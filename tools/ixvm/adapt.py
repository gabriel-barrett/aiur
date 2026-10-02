#!/usr/bin/env python3
"""Reproduce the stage-one source port from a pinned sibling Ix checkout.

Only lexical syntax translation is automatic. The semantic replacements are
explicit below and in Compatibility.aiur; no unconstrained pointer values enter
this program. The retained function set is the ordinary static call closure.
"""
from pathlib import Path
import argparse
import re
import subprocess

ROOT = Path(__file__).resolve().parents[2]
REVISION = 'a1c6badfae6ddbb5e7afff53bb3e67bf3f753b4f'
FILES = ['Core', 'ByteStream', 'Blake3', 'RBTreeMap', 'Ixon', 'IxonSerialize',
         'IxonDeserialize', 'KernelTypes', 'Kernel/Klimbs', 'Kernel/NatPrim',
         'Convert', 'Ingress', 'Kernel/Levels', 'Kernel/Subst', 'Kernel/Whnf',
         'Kernel/InferOnly', 'Kernel/DefEq', 'Kernel/Infer',
         'Kernel/CanonicalCheck', 'Kernel/Check', 'Kernel/Claim']


def uncomments(s):
    # Preserve string contents, including comment-like text in diagnostics.
    out, i, depth = [], 0, 0
    while i < len(s):
        if s[i] == '"':
            j = i + 1
            while j < len(s):
                if s[j] == '\\': j += 2
                elif s[j] == '"': j += 1; break
                else: j += 1
            out.append(s[i:j]); i = j
        elif s.startswith('--', i):
            j = s.find('\n', i)
            if j == -1: break
            out.append('\n'); i = j + 1
        elif s.startswith('/-', i):
            depth = 1; i += 2
            while depth:
                if s.startswith('/-', i): depth += 1; i += 2
                elif s.startswith('-/', i): depth -= 1; i += 2
                else:
                    if s[i] == '\n': out.append('\n')
                    i += 1
        else: out.append(s[i]); i += 1
    return ''.join(out)


def strings(s):
    saved = []
    def hide(m):
        saved.append(m[0]); return f'"STRING_{len(saved)-1}"'
    return re.sub(r'"(?:[^"\\]|\\.)*"', hide, s), saved


def balance_end(s, pos, opening='{', closing='}'):
    depth = 1; i = pos + 1
    while depth:
        if s[i] == opening: depth += 1
        elif s[i] == closing: depth -= 1
        i += 1
    return i


def replace_body(s, name, body):
    m = re.search(r'\bfn ' + name + r'\b[^{}]*\{', s)
    if not m: raise ValueError(f'missing override {name}')
    begin = m.end()-1; end = balance_end(s, begin)
    return s[:begin] + '{\n' + body + '\n  }' + s[end:]


def remove_fast_path(s, name):
    m = re.search(r'\bfn ' + name + r'\b[^{}]*\{', s)
    start = m.end()-1; end = balance_end(s, start)
    body = s[start:end]
    # These two structural equality functions must not call themselves on the
    # same inputs. Discard the outer pointer shortcut; retain its full fallback.
    match = re.search(r'match ptr_val\([^)]*\) - ptr_val\([^)]*\) \{\s*0 => 1,\s*_ =>', body)
    assert match
    opening = body.index('{', match.start())
    close = balance_end(body, opening)
    fallback = body[match.end():close-1].strip().removesuffix(',')
    body = body[:match.start()] + fallback + body[close:]
    return s[:start] + body + s[end:]


def wrap_arms(s):
    # Old Aiur permits a sequence directly after =>. New Aiur has ordinary
    # expression arms, so retain the entire sequence as an explicit block.
    inserts = []
    for m in re.finditer(r'=>', s):
        i = m.end(); j = i; depth = 0
        while j < len(s):
            c = s[j]
            if c in '([{‹': depth += 1
            elif c in ')]}›':
                if depth == 0: break
                depth -= 1
            elif c == ',' and depth == 0: break
            j += 1
        inserts += [(i, ' { '), (j, ' } ')]
    for pos, text in sorted(inserts, reverse=True): s = s[:pos] + text + s[pos:]
    return s


def adapt(s):
    s, saved = strings(uncomments(s))
    for name in ['level_struct_eq', 'kexpr_struct_eq']:
        s = remove_fast_path(s, name)
    s = replace_body(s, 'k_is_def_eq_core', '    k_is_def_eq_ordered(a, b, types)')
    s = replace_body(s, 'canon_cmp_kexpr_ctx',
        '    canon_cmp_kexpr_node_ctx(load(x), load(y), ctx)')
    # Every remaining pointer shortcut compares actual KExpr contents. Address
    # comparisons use the existing bytewise address_eq helper instead.
    s = re.sub(r'ptr_val\((\w+)\) - ptr_val\((\w+)\)',
        lambda m: f'(1 - {"address_eq" if m[1].endswith("addr") else "kexpr_struct_eq"}({m[1]}, {m[2]}))', s)
    s = re.sub(r'assert_eq!\(ptr_val\((\w+)\), ptr_val\((\w+)\),',
        r'assert_eq!(address_eq(\1, \2), 1,', s)
    # Pointer-containing values cannot use assert_eq!. Nil is a refutable
    # pattern; arbitrary limb equality uses the existing structural comparator.
    s = re.sub(r'assert_eq!\(load\((\w+)\), ListNode\.Nil,\s*"STRING_\d+"\)',
        r'let ListNode.Nil = load(\1)', s)
    s = s.replace('assert_eq!(lhs, rhs,', 'assert_eq!(klimbs_eq(lhs, rhs), 1,')
    s = replace_body(s, 'load_constant_hint', '    hint::<Field>((3, load(addr)))')
    s = replace_body(s, 'u32_add', '''
    let (s0, c1) = split_sum(to_field(a[0]) + to_field(b[0]));
    let (s1, c2) = split_sum(to_field(a[1]) + to_field(b[1]) + c1);
    let (s2, c3) = split_sum(to_field(a[2]) + to_field(b[2]) + c2);
    let (s3, _) = split_sum(to_field(a[3]) + to_field(b[3]) + c3);
    [s0, s1, s2, s3]''')
    s = replace_body(s, 'u32_add3', '    u32_add(u32_add(a, b), c)')
    # The old quotient hint contains pointers. Ordinary long division replaces
    # it; Compatibility.aiur supplies it using checked limb arithmetic.
    s = s.replace('unconstrained_big_uint_div_mod(a, b)', 'ordinary_div_mod(a, b)')
    s = replace_body(s, 'read_byte_stream', '''
    match len {
      0 => store(ListNode.Nil),
      _ => let byte = hint::<Field>((channel, idx));
           let tail = read_byte_stream(channel, idx + 1, len - 1);
           store(ListNode.Cons(u8_from_field_unsafe(byte), tail)),
    }''')
    s = re.sub(r'\bset\((\w+), (\d+), ([^()]+?)\)', r'(\1 with { [\2] = \3 })', s)
    s = wrap_arms(s)
    s = s.replace('‹', '<').replace('›', '>')
    s = re.sub(r'\b([A-Z]\w*)\.(\w+)', r'\1::\2', s)
    s = re.sub(r'\bG\b', 'Field', s)
    s = re.sub(r'\b(0x[0-9a-fA-F]+|\d+)u8\b', r'\1', s)
    s = re.sub(r'\b0x[0-9a-fA-F]+\b', lambda m: str(int(m[0], 16)), s)
    s = re.sub(r'([#@])(?=[a-zA-Z_]\w*\()', '', s)
    s = re.sub(r'\bpub fn\b', 'fn', s)
    # Alias declarations in old Aiur are newline-terminated.
    s = re.sub(r'(^[ \t]*type [^\n]+)(?=\n)', lambda m: m[0].rstrip().rstrip(';') + ';', s, flags=re.M)
    # All new function signatures state the unit return type explicitly.
    s = re.sub(r'\bfn [^{}]+\{', lambda m: m[0] if '->' in m[0] else m[0][:-1].rstrip() + ' -> () {', s)
    for i, text in enumerate(saved): s = s.replace(f'"STRING_{i}"', text)
    return re.sub(r'\n\s*\n\s*\n+', '\n\n', s)


def prune(s, roots):
    # Identify top-level definitions, ignoring braces in diagnostic strings.
    hidden, saved = strings(s)
    functions = {}; types = []
    for m in re.finditer(r'(?m)^\s*(?:inline )?(fn|enum|type|table|map) (\w+)', hidden):
        kind, name = m[1], m[2]
        if kind in ('type', 'map'):
            end = m.end(); depth = 0
            while end < len(hidden):
                if hidden[end] in '([': depth += 1
                elif hidden[end] in ')]': depth -= 1
                elif hidden[end] == ';' and depth <= 0: break
                end += 1
            end += 1
        else:
            begin = hidden.index('{', m.end()); end = balance_end(hidden, begin)
        body = hidden[m.start():end]
        if kind == 'fn': functions[name] = body
        else: types.append(body)
    reachable = set(); todo = list(roots)
    while todo:
        name = todo.pop()
        if name in reachable: continue
        if name not in functions: continue
        reachable.add(name)
        todo += re.findall(r'\b(\w+)\s*(?:::<[^>]*>)?\(', functions[name])
    out = 'module IxVM {\n' + '\n'.join(types + [body for name, body in functions.items() if name in reachable]) + '\n}\n'
    for i, text in enumerate(saved): out = out.replace(f'"STRING_{i}"', text)
    return out, reachable


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--ix', type=Path, default=ROOT.parent / 'ix')
    parser.add_argument('--check', action='store_true', help='check generated source without writing')
    args = parser.parse_args()
    revision = subprocess.check_output(['git', '-C', str(args.ix), 'rev-parse', 'HEAD'], text=True).strip()
    if revision != REVISION:
        raise RuntimeError(f'expected Ix {REVISION}, found {revision}; review adapters before updating the pin')
    parts = []
    for name in FILES:
        text = (args.ix / 'Ix/IxVM' / (name + '.lean')).read_text()
        parts.append(text.split('⟦', 1)[1].split('⟧', 1)[0])
    source = adapt('\n'.join(parts))
    source += (ROOT / 'Examples/IxVM/Compatibility.aiur').read_text()
    output, names = prune(source, ['verify_constant', 'verify_transitive', 'verify_serde', 'check_primitives'])
    output = '// Generated by tools/ixvm/adapt.py; see Compatibility.aiur and design/ixvm-stage1.md.\n' + output
    output = '\n'.join(line.rstrip() for line in output.splitlines()) + '\n'
    destination = ROOT / 'Examples/IxVM/Program.aiur'
    if args.check:
        if destination.read_text() != output:
            raise RuntimeError('Program.aiur is stale; run tools/ixvm/adapt.py')
    else:
        destination.write_text(output)
    calls = set(re.findall(r'(?<![:\w])([a-z_]\w*)\(', output))
    maps = set(re.findall(r'\bmap (\w+)', output))
    print(f'{len(names)} functions; unresolved call names: {sorted(calls - names - maps - {"hint"})}')
    if 'ptr_val(' in output or re.search(r'[#@]\w+\(', output):
        raise RuntimeError('port retained a pointer identity or unconstrained operation')


if __name__ == '__main__': main()
