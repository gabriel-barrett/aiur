import Aiur.Generic.OpenSource
import Aiur.Generic.SourceSimulation

namespace Aiur.Generic.SourceSemantics

/-! Induction over finite evaluation closes an expression-level translation
under ordinary and mutual recursion. Calls remain premises of the expression
lemma; they are discharged here by strictly smaller evaluation derivations. -/

theorem EvalExpr.openCalls [Field F] [DecidableEq F]
    {world : World F} {calls : CallRelation F} {names : List String}
    (closed : ∀ n ∈ names, ∀ args ts ls e, world.prepare n args = .ok (ts, ls, e) →
      inScope names (fun _ => true) ts e = true)
    (step : ∀ n ∈ names, ∀ args ts ls e b v a,
      world.prepare n args = .ok (ts, ls, e) →
      OpenSource.EvalExpr world calls ts ls e b v a → calls n args b v a)
    (ev : EvalExpr world types locals expr before result after) :
    inScope names (fun _ => true) types expr = true → OpenSource.EvalExpr world calls types locals expr before result after := by
  induction ev using EvalExpr.rec
    (motive_2 := fun ts ls es b vs h _ => (∀ e ∈ es, inScope names (fun _ => true) ts e = true) → OpenSource.EvalArgs world calls ts ls es b vs h)
    (motive_3 := fun n xs b v h _ => n ∈ names → calls n xs b v h) with
  | literal => intro _; exact .literal
  | var h => intro _; exact .var h
  | global lookup interpreted _ ih =>
      intro _
      exact .global lookup interpreted
        (ih (const_inScope _ interpreted))
  | tuple _ ih => intro h; exact .tuple (ih (by simpa [inScope] using h))
  | array _ ih => intro h; exact .array (ih (by simpa [inScope] using h))
  | «repeat» _ ih => intro h; exact .repeat (ih (by simpa [inScope] using h))
  | index _ op ih => intro h; exact .index (ih (by simpa [inScope] using h)) op
  | slice _ op ih => intro h; exact .slice (ih (by simpa [inScope] using h)) op
  | constructAs _ ih => intro h; exact .constructAs (ih (by simpa [inScope] using h))
  | construct _ ih => intro h; exact .construct (ih (by simpa [inScope] using h))
  | project _ op ih => intro h; exact .project (ih (by simpa [inScope] using h)) op
  | letValue _ matched _ ih1 ih2 =>
      intro h
      simp only [inScope, Bool.and_eq_true] at h
      exact .letValue (ih1 h.1) matched (ih2 h.2)
  | store _ ih => intro h; exact .store (ih (by simpa [inScope] using h))
  | load _ op ih => intro h; exact .load (ih (by simpa [inScope] using h)) op
  | hint _ typed ih =>
      intro h
      simp only [inScope, Bool.and_eq_true] at h
      exact .hint (ih h.2) typed
  | neg _ op ih => intro h; exact .neg (ih (by simpa [inScope] using h)) op
  | binary _ _ op ih1 ih2 =>
      intro h
      simp only [inScope, Bool.and_eq_true] at h
      exact .binary (ih1 h.1) (ih2 h.2) op
  | call _ _ ih1 ih2 =>
      intro h
      simp only [inScope, Bool.and_eq_true, List.contains_iff_mem, List.all_map, List.all_eq_true, Function.comp_def, id_eq] at h
      exact .call (ih1 h.2) (ih2 h.1)
  | matchValue _ selected _ ih1 ih2 =>
      intro h
      simp only [inScope, Bool.and_eq_true, List.all_map, List.all_eq_true, Function.comp_def, id_eq] at h
      exact .matchValue (ih1 h.1) selected (ih2 (selected_inScope selected h.2))
  | nil => exact .nil
  | cons _ _ ih1 ih2 =>
      rename_i h
      exact .cons (ih1 (h _ (by simp))) (ih2 (fun e he => h e (by simp [he])))
  | intro prepared _ ih =>
      rename_i hn
      exact step _ hn _ _ _ _ _ _ _ prepared (ih (closed _ hn _ _ _ _ prepared))


theorem EvalFn.openCalls [Field F] [DecidableEq F]
    {world : World F} {calls : CallRelation F} {names : List String}
    (closed : ∀ n ∈ names, ∀ args ts ls e, world.prepare n args = .ok (ts, ls, e) →
      inScope names (fun _ => true) ts e = true)
    (step : ∀ n ∈ names, ∀ args ts ls e b v a,
      world.prepare n args = .ok (ts, ls, e) →
      OpenSource.EvalExpr world calls ts ls e b v a → calls n args b v a)
    (ev : EvalFn world name args before result after) (member : name ∈ names) :
    calls name args before result after := by
  cases ev with
  | intro prepared body =>
      exact step _ member _ _ _ _ _ _ _ prepared
        (body.openCalls closed step (closed _ member _ _ _ _ prepared))

end Aiur.Generic.SourceSemantics
