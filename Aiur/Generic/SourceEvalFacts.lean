import Aiur.Generic.SourceSemantics

namespace Aiur.Generic.SourceSemantics

variable {F : Type} {world : World F} {types : Types} {hints : HintProvider world}

private theorem evalArgs_of_mapM [Field F] [DecidableEq F]
    {locals : Environment F Nat} {fuel : Nat}
    (sound : ∀ expr before result after,
      evalExprWith world hints types locals fuel expr before = .ok (result, after) →
        EvalExpr world types locals expr before result after)
    {args : List (Expr F)} {values : List (SourceValue F)} {before after : Heap F}
    (executed : args.mapM (evalExprWith world hints types locals fuel) before = .ok (values, after)) :
    EvalArgs world types locals args before values after := by
  induction args generalizing before values with
  | nil =>
      obtain ⟨rfl, rfl⟩ := Evaluation.pure_ok.mp executed
      exact .nil
  | cons head tail ih =>
      rw [List.mapM_cons] at executed
      obtain ⟨value, middle, headRun, rest⟩ := Evaluation.bind_ok.mp executed
      obtain ⟨results, last, tailRun, finished⟩ := Evaluation.bind_ok.mp rest
      obtain ⟨rfl, rfl⟩ := Evaluation.pure_ok.mp finished
      exact .cons (sound head before value middle headRun) (ih tailRun)

/-- Every successful run, including its final heap, has a fuel-free evaluation proof. -/
theorem evalExpr_spec [Field F] [DecidableEq F]
    {locals : Environment F Nat} {fuel : Nat} {expr : Expr F}
    {before after : Heap F} {result : SourceValue F}
    (executed : evalExprWith world hints types locals fuel expr before = .ok (result, after)) :
    EvalExpr world types locals expr before result after := by
  induction fuel generalizing types locals expr before result after with
  | zero => simp [evalExprWith] at executed
  | succ fuel ih =>
      cases expr with
      | literal value =>
          obtain ⟨rfl, rfl⟩ := Evaluation.pure_ok.mp executed
          exact .literal
      | var name =>
          cases found : locals.find? (·.1 == name) with
          | none => simp [evalExprWith, found, Evaluation.throw_apply] at executed
          | some binding =>
              rcases binding with ⟨key, value⟩
              have same : key = name := by simpa using List.find?_some found
              subst key
              simp only [evalExprWith, found] at executed
              obtain ⟨rfl, rfl⟩ := Evaluation.pure_ok.mp executed
              exact .var found
      | tuple items =>
          simp only [evalExprWith] at executed
          obtain ⟨values, middle, itemsRun, finished⟩ := Evaluation.bind_ok.mp executed
          obtain ⟨rfl, rfl⟩ := Evaluation.pure_ok.mp finished
          exact .tuple (evalArgs_of_mapM (fun _ _ _ _ h => ih h) itemsRun)
      | array items =>
          simp only [evalExprWith] at executed
          obtain ⟨values, middle, itemsRun, finished⟩ := Evaluation.bind_ok.mp executed
          obtain ⟨rfl, rfl⟩ := Evaluation.pure_ok.mp finished
          exact .array (evalArgs_of_mapM (fun _ _ _ _ h => ih h) itemsRun)
      | construct name args ctor items =>
          simp only [evalExprWith] at executed
          obtain ⟨values, middle, itemsRun, finished⟩ := Evaluation.bind_ok.mp executed
          obtain ⟨rfl, rfl⟩ := Evaluation.pure_ok.mp finished
          exact .construct (evalArgs_of_mapM (fun _ _ _ _ h => ih h) itemsRun)
      | constructAs params t ctor items =>
          simp only [evalExprWith] at executed
          obtain ⟨values, middle, itemsRun, finished⟩ := Evaluation.bind_ok.mp executed
          obtain ⟨rfl, rfl⟩ := Evaluation.pure_ok.mp finished
          exact .constructAs (evalArgs_of_mapM (fun _ _ _ _ h => ih h) itemsRun)
      | project value index =>
          simp only [evalExprWith] at executed
          obtain ⟨input, middle, operand, operation⟩ := Evaluation.bind_ok.mp executed
          obtain ⟨projected, rfl⟩ := Evaluation.lift_ok.mp operation
          exact .project (ih operand) projected
      | index value index =>
          simp only [evalExprWith] at executed
          obtain ⟨input, middle, operand, operation⟩ := Evaluation.bind_ok.mp executed
          obtain ⟨projected, rfl⟩ := Evaluation.lift_ok.mp operation
          exact .index (ih operand) projected
      | slice value start stop =>
          simp only [evalExprWith] at executed
          obtain ⟨input, middle, operand, operation⟩ := Evaluation.bind_ok.mp executed
          obtain ⟨projected, rfl⟩ := Evaluation.lift_ok.mp operation
          exact .slice (ih operand) projected
      | «repeat» value length =>
          simp only [evalExprWith] at executed
          obtain ⟨input, middle, operand, finished⟩ := Evaluation.bind_ok.mp executed
          obtain ⟨rfl, rfl⟩ := Evaluation.pure_ok.mp finished
          exact .repeat (ih operand)
      | global name => simp [evalExprWith, Evaluation.throw_apply] at executed
      | hint type key =>
          simp only [evalExprWith] at executed
          obtain ⟨input, middle, keyRun, rest⟩ := Evaluation.bind_ok.mp executed
          obtain ⟨value, last, supplied, finished⟩ := Evaluation.bind_ok.mp rest
          obtain ⟨_, rfl⟩ := Evaluation.lift_ok.mp supplied
          obtain ⟨rfl, rfl⟩ := Evaluation.pure_ok.mp finished
          exact .hint (ih keyRun) value.property
      | neg value =>
          simp only [evalExprWith] at executed
          obtain ⟨input, middle, operand, operation⟩ := Evaluation.bind_ok.mp executed
          obtain ⟨negated, rfl⟩ := Evaluation.lift_ok.mp operation
          exact .neg (ih operand) negated
      | store value =>
          simp only [evalExprWith] at executed
          obtain ⟨input, middle, operand, stored⟩ := Evaluation.bind_ok.mp executed
          have same : (.ptr input.type middle.length, middle ++ [input]) = (result, after) := by
            simpa [bind, StateT.bind, Evaluation.get_apply, set, StateT.set,
              pure, StateT.pure, Except.pure, Except.bind] using stored
          cases same
          exact .store (ih operand)
      | load value =>
          simp only [evalExprWith] at executed
          obtain ⟨input, middle, operand, loaded⟩ := Evaluation.bind_ok.mp executed
          have lifted : (liftM (loadValue middle input) : Evaluation F _) middle = .ok (result, after) := by
            simpa [bind, StateT.bind, Evaluation.get_apply, Except.bind] using loaded
          obtain ⟨loadOK, rfl⟩ := Evaluation.lift_ok.mp lifted
          exact .load (ih operand) loadOK
      | binary op left right =>
          simp only [evalExprWith] at executed
          obtain ⟨leftValue, middle, leftRun, rest⟩ := Evaluation.bind_ok.mp executed
          obtain ⟨rightValue, last, rightRun, operation⟩ := Evaluation.bind_ok.mp rest
          obtain ⟨operationOK, rfl⟩ := Evaluation.lift_ok.mp operation
          exact .binary (ih leftRun) (ih rightRun) operationOK
      | letValue pattern value body =>
          simp only [evalExprWith] at executed
          obtain ⟨input, middle, operand, rest⟩ := Evaluation.bind_ok.mp executed
          have rest' : (do
              let some bindings ← liftM (matchPattern types middle pattern input) | throw EvalError.patternMismatch
              evalExprWith world hints types (bindings ++ locals) fuel body : Evaluation F _) middle = .ok (result, after) := by
            simpa [bind, StateT.bind, Evaluation.get_apply, Except.bind] using rest
          obtain ⟨bindings, last, matched, bodyRun⟩ := Evaluation.bind_ok.mp rest'
          obtain ⟨matchOK, rfl⟩ := (Evaluation.lift_ok (computation := matchPattern types middle pattern input)).mp matched
          cases bindings with
          | none => simp [Evaluation.throw_apply] at bodyRun
          | some bindings => exact .letValue (ih operand) matchOK (ih bodyRun)
      | matchValue scrutinee arms =>
          simp only [evalExprWith] at executed
          obtain ⟨input, middle, operand, rest⟩ := Evaluation.bind_ok.mp executed
          have rest' : (do
              let some (bindings, body) ← liftM (selectArm types middle input arms) | throw EvalError.noMatchingArm
              evalExprWith world hints types (bindings ++ locals) fuel body : Evaluation F _) middle = .ok (result, after) := by
            simpa [bind, StateT.bind, Evaluation.get_apply, Except.bind] using rest
          obtain ⟨selection, last, selected, bodyRun⟩ := Evaluation.bind_ok.mp rest'
          obtain ⟨selectionOK, rfl⟩ := (Evaluation.lift_ok (computation := selectArm types middle input arms)).mp selected
          cases selection with
          | none => simp [Evaluation.throw_apply] at bodyRun
          | some pair =>
              rcases pair with ⟨bindings, body⟩
              exact .matchValue (ih operand) selectionOK (ih bodyRun)
      | call name typeArgs args =>
          simp only [evalExprWith] at executed
          obtain ⟨values, middle, arguments, rest⟩ := Evaluation.bind_ok.mp executed
          obtain ⟨⟨calleeTypes, bindings, body⟩, last, prepared, called⟩ := Evaluation.bind_ok.mp rest
          obtain ⟨prepareOK, rfl⟩ := Evaluation.lift_ok.mp prepared
          exact .call (evalArgs_of_mapM (fun _ _ _ _ h => ih h) arguments) (.intro prepareOK (ih called))

end Aiur.Generic.SourceSemantics
