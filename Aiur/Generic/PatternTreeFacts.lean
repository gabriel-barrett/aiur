import Aiur.Generic.PatternBindingsFacts
import Aiur.Generic.PatternStepFacts

namespace Aiur.Generic.PatternLowering
open SourceSemantics

theorem state_bind_run (f : StateM S A) (g : A → StateM S B) (s : S) :
    (f >>= g) s = g (f s).1 (f s).2 := by
  simp only [bind, StateT.bind]
  cases f s; rfl

theorem state_pure_run (value : A) (state : S) : (pure value : StateM S A) state = (value, state) := rfl

theorem state_map_result (f : StateM S A) (g : A → B) (s : S) :
    ((do let x ← f; pure (g x) : StateM S B) s).1 = g (f s).1 := by
  rw [state_bind_run, state_pure_run]

theorem fresh_run (stem : String) (n : Nat) : fresh stem n = (stem ++ toString n, n + 1) := rfl

theorem state_mapM_relation (f : A → StateM S B) (xs : List A) (state : S)
    {R : A → B → Prop} (each : ∀ x ∈ xs, ∀ s, R x (f x s).1) :
    List.Forall₂ R xs (xs.mapM f state).1 := by
  induction xs generalizing state with
  | nil => exact .nil
  | cons x xs ih =>
      simp only [List.mapM_cons, bind, StateT.bind, pure, StateT.pure]
      exact .cons (each x (by simp) state)
        (ih _ (fun x hx s => each x (by simp [hx]) s))

theorem matchList_map [DecidableEq F]
    {run : B → SourceValue F → Except EvalError (Option (Environment F Nat))}
    (f : A → B) (xs : List A) (values : List (SourceValue F)) :
    matchListWith run (xs.map f) values = matchListWith (fun x v => run (f x) v) xs values := by
  induction xs generalizing values with
  | nil => cases values <;> rfl
  | cons x xs ih => cases values <;> simp only [List.map_cons, matchListWith, ih]

private theorem matches_tuple [DecidableEq F] (ps : List (Pattern F)) (value : SourceValue F) :
    matchPatternWith constant depth types heap (.tuple ps) value =
      match value with
      | .tuple values => if ps.length != values.length then .ok none else
          matchListWith (fun p v => matchPatternWith constant depth types heap p v) ps values
      | _ => .ok none := by
  cases value <;> simp only [matchPatternWith, Preparation.matchList_attach, pure, Except.pure, bind, Except.bind]

/-- Naming compiler temporaries does not change a pattern. This theorem covers
nested loads, repeated patterns, nominal constructors and all failed matches.
Const references have already been unfolded by the proved preparation pass. -/
theorem planTree_match [DecidableEq F] (pat : Pattern F)
    (resolved : Consts.dependencies pat = []) (types stem state)
    (constant : String → Ty → Except EvalError (Pattern F)) (depth : Nat)
    (heap : Heap F) (value : SourceValue F) :
    matchPatternWith constant depth types heap pat value =
      matchPatternWith constant depth [] heap ((planTree types stem pat state).1.erase) value := by
  have sub (p : Pattern F) (smaller : sizeOf p < sizeOf pat)
      (resolved : Consts.dependencies p = []) (s : Nat) (v : SourceValue F) :
      matchPatternWith constant depth types heap p v =
        matchPatternWith constant depth [] heap ((planTree types stem p s).1.erase) v :=
    planTree_match p resolved types stem s constant depth heap v
  have children (ps : List (Pattern F))
      (smaller : ∀ p ∈ ps, sizeOf p < sizeOf pat)
      (resolved : ∀ p ∈ ps, Consts.dependencies p = []) (s : Nat) :
      let parts := (ps.mapM (fun p => do
        let n ← fresh stem
        return (n, ← planTree types stem p)) s).1
      List.Forall₂ (fun p part => ∀ v,
        matchPatternWith constant depth types heap p v =
        matchPatternWith constant depth [] heap part.2.erase v) ps parts := by
    apply state_mapM_relation
    intro p hp s v
    simp only [state_bind_run, state_pure_run, fresh_run]
    exact sub p (smaller p hp) (resolved p hp) _ v
  cases pat with
  | literal x | wildcard | bind n =>
      simp only [planTree, pure, StateT.pure, PlanTree.erase, matchPatternWith]
  | global n t => simp [Consts.dependencies] at resolved
  | load p =>
      have hp : Consts.dependencies p = [] := by simpa only [Consts.dependencies] using resolved
      simp only [planTree, state_bind_run, fresh_run, state_pure_run, PlanTree.erase, matchPatternWith]
      cases loaded : loadValue heap value with
      | error e => rfl
      | ok v => exact sub p (by simp_wf <;> omega) hp _ v
  | tuple ps | array ps =>
      have hp : ∀ p ∈ ps, Consts.dependencies p = [] := by
        simpa only [Consts.dependencies, List.flatMap_eq_nil_iff] using resolved
      have rel := children ps (by intros; simp_wf; have := List.sizeOf_lt_of_mem ‹_ ∈ _›; omega) hp state
      have lengths := rel.length_eq
      simp only [planTree, state_map_result, PlanTree.erase]
      cases value <;> simp only [matchPatternWith, Preparation.matchList_attach, pure, Except.pure, bind, Except.bind,
        List.length_map, lengths, matchList_map]
      rename_i vs
      split
      · rfl
      · exact Preparation.matchList_congr rel vs
  | «repeat» p n =>
      have hp : Consts.dependencies p = [] := by simpa only [Consts.dependencies] using resolved
      let parts := ((List.range n).mapM (fun (_ : Nat) => do
        let name ← fresh stem
        return (name, ← planTree types stem p)) state).1
      have rel : List.Forall₂ (fun (_ : Nat) part => ∀ v,
          matchPatternWith constant depth types heap p v =
          matchPatternWith constant depth [] heap part.2.erase v) (List.range n) parts := by
        apply state_mapM_relation
        intro _ _ s v
        simp only [state_bind_run, state_pure_run, fresh_run]
        exact sub p (by simp_wf; omega) hp _ v
      have lengths : n = parts.length := by simpa only [List.length_range] using rel.length_eq
      simp only [planTree, state_map_result, PlanTree.erase]
      change matchPatternWith constant depth types heap (.repeat p n) value =
        matchPatternWith constant depth [] heap (.tuple (parts.map fun part => part.2.erase)) value
      cases value <;> simp only [matchPatternWith, Preparation.matchList_attach, List.length_map,
        pure, Except.pure, bind, Except.bind]
      rename_i vs
      by_cases equal : vs.length = n
      · simp only [← lengths, equal, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, matchList_map]
        have units : (List.range n).map (fun _ => ()) = List.replicate n () := by simp
        rw [← units, matchList_map]
        exact Preparation.matchList_congr rel vs
      · simp [← lengths, equal, Ne.symm equal]
  | construct t c ps | constructAs params t c ps =>
      have hp : ∀ p ∈ ps, Consts.dependencies p = [] := by
        simpa only [Consts.dependencies, List.flatMap_eq_nil_iff] using resolved
      have rel := children ps (by intros; simp_wf; have := List.sizeOf_lt_of_mem ‹_ ∈ _›; omega) hp state
      have lengths := rel.length_eq
      simp only [planTree, state_map_result, PlanTree.erase]
      cases core : (t.subst types).toCore <;>
        simp only [core, PlanTree.erase]
      all_goals cases value <;> simp only [matchPatternWith, Preparation.matchList_attach,
        constructorName, Ty.subst, Ty.toCore, Instance.symbol, List.map_nil, List.isEmpty_nil,
        ↓reduceIte, core, pure, Except.pure, bind, Except.bind, List.length_map, lengths, matchList_map]
      all_goals split
      all_goals first | rfl | exact Preparation.matchList_congr rel _
termination_by sizeOf pat
decreasing_by exact smaller

end Aiur.Generic.PatternLowering
