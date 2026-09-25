import Aiur.Generic.PatternLowering
import Aiur.Generic.Engine

namespace Aiur.Generic.PatternLowering

/-- Removing one pointer-pattern layer is exactly an ordinary load, even when
the remaining pattern contains further loads. -/
@[simp] theorem lowerLet_load (env) (pat : Pattern α) (value body : Aiur.Expr α) :
    lowerLet env (.load pat) value body = lowerLet env pat (.load value) body := by
  rw [lowerLet]

@[simp] theorem lowerLet_load_bind (env) (name : String) (value body : Aiur.Expr α) :
    lowerLet env (.load (.bind name)) value body =
      .letValue (.bind name) (.load value) body := by
  simp [lowerLet, Pattern.toCore?]

/-- Read-only execution of a pattern plan. A failed test stops the attempt;
a bad load has no successful derivation and does not select a fallback. Only
temporary bindings have been installed when a test fails. -/
inductive Attempt [DecidableEq F] (heap : Heap F) :
    List (Step F) → Environment F Nat → Bool → Environment F Nat → Prop where
  | done : Attempt heap [] locals true locals
  | testHit
      (lookup : locals.find? (·.1 == input) = some (input, value))
      (matched : pat.bindings value = some bindings)
      (rest : Attempt heap steps (bindings ++ locals) accepted final) :
      Attempt heap (.test pat input :: steps) locals accepted final
  | testMiss
      (lookup : locals.find? (·.1 == input) = some (input, value))
      (missed : pat.bindings value = none) :
      Attempt heap (.test pat input :: steps) locals false locals
  | load
      (lookup : locals.find? (·.1 == input) = some (input, pointer))
      (loaded : loadValue heap pointer = .ok value)
      (rest : Attempt heap steps ((name, value) :: locals) accepted final) :
      Attempt heap (.load name input :: steps) locals accepted final

variable [Field F] [DecidableEq F] {world : Engine.World F}

/-- `let &name = pointer; body` evaluates the pointer once, reads its cell,
and evaluates the body with the contents bound to `name`. -/
theorem load_bind_iff {env} {name : String} {locals : Environment F Nat}
    {pointer body : Aiur.Expr F} {before after : Heap F} {result : SourceValue F} :
    Engine.EvalExpr world locals (lowerLet env (.load (.bind name)) pointer body) before result after ↔
      ∃ address middle value,
        Engine.EvalExpr world locals pointer before address middle ∧
        loadValue middle address = .ok value ∧
        Engine.EvalExpr world ((name, value) :: locals) body middle result after := by
  rw [lowerLet_load_bind]
  constructor
  · intro h
    cases h with
    | letValue value matched body =>
        cases value with
        | load pointer loaded =>
            simp only [Aiur.Pattern.bindings, Option.some.injEq] at matched
            subst_vars
            exact ⟨_, _, _, pointer, loaded, body⟩
  · rintro ⟨address, middle, value, pointer, loaded, body⟩
    exact .letValue (bindings := [(name, value)]) (.load pointer loaded)
      (by simp [Aiur.Pattern.bindings]) body

/-- Let desugaring succeeds exactly when all pattern tests and loads succeed,
followed by evaluation of the body. Pattern steps do not change the heap. -/
theorem letSteps_iff {steps : List (Step F)} {locals : Environment F Nat}
    {body : Aiur.Expr F} {before after : Heap F} {result : SourceValue F} :
    Engine.EvalExpr world locals (letSteps steps body) before result after ↔
      ∃ final, Attempt before steps locals true final ∧
        Engine.EvalExpr world final body before result after := by
  induction steps generalizing locals with
  | nil =>
      constructor
      · intro h; exact ⟨locals, .done, h⟩
      · rintro ⟨_, h, body⟩; cases h; exact body
  | cons step steps ih =>
      cases step with
      | test pat input =>
          constructor
          · intro h
            cases h with
            | letValue value matched body =>
                cases value with
                | var lookup =>
                    obtain ⟨final, rest, body⟩ := ih.mp body
                    exact ⟨final, .testHit lookup matched rest, body⟩
          · rintro ⟨final, h, body⟩
            cases h with
            | testHit lookup matched rest =>
                exact .letValue (.var lookup) matched (ih.mpr ⟨final, rest, body⟩)
      | load name input =>
          constructor
          · intro h
            cases h with
            | letValue value matched body =>
                cases value with
                | load pointer loaded =>
                    cases pointer with
                    | var lookup =>
                        simp only [Aiur.Pattern.bindings, Option.some.injEq] at matched
                        subst_vars
                        obtain ⟨final, rest, body⟩ := ih.mp body
                        exact ⟨final, .load lookup loaded rest, body⟩
          · rintro ⟨final, h, body⟩
            cases h with
            | load lookup loaded rest =>
                exact .letValue (bindings := [(name, _)]) (.load (.var lookup) loaded) (by simp [Aiur.Pattern.bindings]) (ih.mpr ⟨final, rest, body⟩)

/-- The selected continuation of a match attempt; no fallback means a partial
match cannot finish after a failed test. -/
def Continuation (world : Engine.World F) (accepted : Bool) (locals : Environment F Nat)
    (body : Aiur.Expr F) (failure : Option (Aiur.Expr F))
    (before : Heap F) (result : SourceValue F) (after : Heap F) : Prop :=
  if accepted then Engine.EvalExpr world locals body before result after
  else ∃ fallback, failure = some fallback ∧ Engine.EvalExpr world locals fallback before result after

/-- Ordered match desugaring executes exactly the chosen plan continuation.
In particular, a failed earlier test bypasses all subsequent loads. -/
theorem matchSteps_iff {steps : List (Step F)} {locals : Environment F Nat}
    {body : Aiur.Expr F} {failure : Option (Aiur.Expr F)}
    {before after : Heap F} {result : SourceValue F} :
    Engine.EvalExpr world locals (matchSteps steps body failure) before result after ↔
      ∃ accepted final, Attempt before steps locals accepted final ∧
        Continuation world accepted final body failure before result after := by
  induction steps generalizing locals with
  | nil =>
      constructor
      · intro h; exact ⟨true, locals, .done, h⟩
      · rintro ⟨_, _, h, body⟩; cases h; exact body
  | cons step steps ih =>
      cases step with
      | load name input =>
          constructor
          · intro h
            cases h with
            | letValue value matched body =>
                cases value with
                | load pointer loaded =>
                    cases pointer with
                    | var lookup =>
                        simp only [Aiur.Pattern.bindings, Option.some.injEq] at matched
                        subst_vars
                        obtain ⟨accepted, final, rest, body⟩ := ih.mp body
                        exact ⟨accepted, final, .load lookup loaded rest, body⟩
          · rintro ⟨accepted, final, h, body⟩
            cases h with
            | load lookup loaded rest =>
                exact .letValue (bindings := [(name, _)]) (.load (.var lookup) loaded) (by simp [Aiur.Pattern.bindings]) (ih.mpr ⟨accepted, final, rest, body⟩)
      | test pat input =>
          constructor
          · intro h
            cases h with
            | matchValue value selected branch =>
                cases value with
                | var lookup =>
                    rename_i inputValue bindings selectedBody
                    cases matched : pat.bindings inputValue with
                    | some bindings =>
                        simp only [selectArm, matched, Option.some.injEq, Prod.mk.injEq] at selected
                        obtain ⟨rfl, rfl⟩ := selected
                        obtain ⟨accepted, final, rest, body⟩ := ih.mp branch
                        exact ⟨accepted, final, .testHit lookup matched rest, body⟩
                    | none =>
                        cases failure with
                        | none => simp [selectArm, matched] at selected
                        | some fallback =>
                            simp only [selectArm, matched, Option.toList_some, List.map_cons,
                              List.map_nil, Aiur.Pattern.bindings, Option.some.injEq, Prod.mk.injEq] at selected
                            obtain ⟨rfl, rfl⟩ := selected
                            exact ⟨false, _, .testMiss lookup matched, fallback, rfl, branch⟩
          · rintro ⟨accepted, final, h, body⟩
            cases h with
            | testHit lookup matched rest =>
                exact .matchValue (.var lookup) (by simp [selectArm, matched, matchSteps])
                  (ih.mpr ⟨accepted, final, rest, body⟩)
            | testMiss lookup missed =>
                obtain ⟨fallback, rfl, branch⟩ := body
                exact .matchValue (bindings := []) (body := fallback) (.var lookup)
                  (by simp [selectArm, missed, Aiur.Pattern.bindings]) branch

end Aiur.Generic.PatternLowering
