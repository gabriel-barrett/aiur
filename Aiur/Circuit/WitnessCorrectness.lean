import Aiur.Circuit.ExpressionCorrectness

namespace Aiur.Circuit.Compiler

theorem denote_of_prefix [Field F] {function : String} {initial values : List F}
    (extension : initial.IsPrefix values) {bound : Nat} (size : initial.length = bound)
    {polynomial : ArithExpr F} (bounded : polynomial.inBounds bound = true) :
    polynomial.denote (Row.assignment ⟨function, values⟩) =
      polynomial.denote (Row.assignment ⟨function, initial⟩) :=
  ArithExpr.denote_eq_of_agree
    (fun _ bound => Row.assignment_of_prefix extension (by simpa [size] using bound)) bounded

theorem localsEnvironment_of_prefix [Zero F] {function : String} {initial values : List F}
    (extension : initial.IsPrefix values) {bound : Nat} (size : initial.length = bound)
    {locals : List (String × Var)} (bounded : ∀ binding ∈ locals, binding.2 < bound) :
    localsEnvironment locals (Row.assignment ⟨function, values⟩) =
      localsEnvironment locals (Row.assignment ⟨function, initial⟩) := by
  apply List.map_congr_left
  intro binding member
  rw [Row.assignment_of_prefix (before := ⟨function, initial⟩) extension
    (by simpa [size] using bounded binding member)]

theorem BuildState.WellFormed.fresh {state : BuildState F} (layout : state.WellFormed) :
    { state with nextVar := state.nextVar + 1 }.WellFormed :=
  ⟨fun equation member => ArithExpr.inBounds_mono (Nat.le_succ _) (layout.constraints equation member),
    fun send member => Send.inBounds_mono (Nat.le_succ _) (layout.sends send member)⟩

theorem BuildState.WellFormed.constrain {state : BuildState F} (layout : state.WellFormed)
    {polynomial : ArithExpr F} (bound : polynomial.inBounds state.nextVar = true) :
    { state with constraints := state.constraints.push polynomial }.WellFormed := by
  refine ⟨?_, layout.sends⟩
  intro equation member
  simp only [Array.toList_push, List.mem_append, List.mem_singleton] at member
  rcases member with member | rfl
  · exact layout.constraints equation member
  · exact bound

theorem BuildState.Valid.constrain [Field F] {state : BuildState F} {calls : CallRelation F}
    {assignment : Var → F} (valid : state.Valid calls assignment) {polynomial : ArithExpr F}
    (zero : polynomial.denote assignment = 0) :
    { state with constraints := state.constraints.push polynomial }.Valid calls assignment := by
  refine ⟨?_, valid.calls⟩
  intro equation member
  simp only [Array.toList_push, List.mem_append, List.mem_singleton] at member
  rcases member with member | rfl
  · exact valid.constraints equation member
  · exact zero

theorem BuildState.Valid.of_prefix [Field F] {function : String} {initial values : List F}
    {state : BuildState F} {calls : CallRelation F}
    (valid : state.Valid calls (Row.assignment ⟨function, initial⟩))
    (layout : state.WellFormed) (size : initial.length = state.nextVar)
    (extension : initial.IsPrefix values) :
    state.Valid calls (Row.assignment ⟨function, values⟩) := by
  constructor
  · intro equation member
    rw [denote_of_prefix extension size (layout.constraints equation member)]
    exact valid.constraints equation member
  · intro send member active
    have bounds := layout.sends send member
    simp only [Send.inBounds, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at bounds
    have enable := denote_of_prefix (function := function) extension size bounds.1.2
    rw [enable] at active
    have args : send.args.map (ArithExpr.denote (Row.assignment ⟨function, values⟩)) =
        send.args.map (ArithExpr.denote (Row.assignment ⟨function, initial⟩)) := by
      apply List.map_congr_left
      exact fun arg member => denote_of_prefix extension size (bounds.2 arg member)
    rw [args, Row.assignment_of_prefix (before := ⟨function, initial⟩) extension
      (by simpa [size] using bounds.1.1)]
    exact valid.calls send member active

mutual
  /--
  Expression completeness under an active enable. New variables extend the initial
  assignment, preserving its values and all earlier constraints and call premises.
  This includes providing witnesses for every inactive branch of a compiled match.
  -/
  theorem lowerExpr_complete [Field F] [DecidableEq F]
      {function : String} {locals : List (String × Var)} {enable : ArithExpr F} {expr : Expr F}
      {before after : BuildState F} {polynomial : ArithExpr F}
      (compiled : (lowerExpr function locals enable expr).run before = .ok (polynomial, after))
      (layout : before.WellFormed)
      (localsBound : ∀ binding ∈ locals, binding.2 < before.nextVar)
      (enableBound : enable.inBounds before.nextVar = true)
      {calls : CallRelation F} {initial : List F} (size : initial.length = before.nextVar)
      (valid : before.Valid calls (Row.assignment ⟨function, initial⟩))
      (active : enable.denote (Row.assignment ⟨function, initial⟩) = 1)
      {result : F}
      (body : EvalExprWith calls
        (localsEnvironment locals (Row.assignment ⟨function, initial⟩)) expr result) :
      ∃ values, initial.IsPrefix values ∧ values.length = after.nextVar ∧
        after.WellFormed ∧ polynomial.inBounds after.nextVar = true ∧
        after.Valid calls (Row.assignment ⟨function, values⟩) ∧
        polynomial.denote (Row.assignment ⟨function, values⟩) = result := by
    cases expr with
    | literal value =>
        simp [lowerExpr, StateT.run, StateT.pure, pure, Except.pure] at compiled
        rcases compiled with ⟨rfl, rfl⟩
        cases body
        exact ⟨initial, ⟨[], by simp⟩, size, layout, rfl, valid, rfl⟩
    | var name =>
        cases found : locals.find? (·.1 == name) with
        | none =>
            simp [lowerExpr, found, StateT.run] at compiled
            cases compiled
        | some binding =>
            rcases binding with ⟨bindingName, id⟩
            have same : bindingName = name := by simpa using List.find?_some found
            subst bindingName
            simp [lowerExpr, found, StateT.run, StateT.pure, pure, Except.pure] at compiled
            rcases compiled with ⟨rfl, rfl⟩
            refine ⟨initial, ⟨[], by simp⟩, size, layout, ?_, valid, ?_⟩
            · simpa [ArithExpr.inBounds] using localsBound (name, id) (List.mem_of_find?_eq_some found)
            · cases body with
              | var lookup =>
                  simpa [localsEnvironment, List.find?_map, Function.comp_def, found,
                    ArithExpr.denote] using lookup
    | neg expr =>
        cases lowered : lowerExpr function locals enable expr before with
        | error error =>
            simp [lowerExpr, StateT.run, StateT.bind, bind, Except.bind, lowered] at compiled
        | ok output =>
            rcases output with ⟨inner, state⟩
            simp [lowerExpr, StateT.run, StateT.bind, StateT.pure, bind, pure,
              Except.bind, Except.pure, lowered] at compiled
            rcases compiled with ⟨rfl, rfl⟩
            cases body with
            | neg operand =>
                obtain ⟨values, extension, finalSize, finalLayout, innerBound, finalValid, value⟩ :=
                  lowerExpr_complete lowered layout localsBound enableBound size valid active operand
                refine ⟨values, extension, finalSize, finalLayout, ?_, finalValid, ?_⟩
                · simpa [ArithExpr.inBounds] using innerBound
                · simp [ArithExpr.denote, value]
    | binary op left right =>
        cases leftRun : lowerExpr function locals enable left before with
        | error error =>
            simp [lowerExpr, StateT.run, StateT.bind, bind, Except.bind, leftRun] at compiled
        | ok output =>
            rcases output with ⟨leftPolynomial, middle⟩
            cases rightRun : lowerExpr function locals enable right middle with
            | error error =>
                simp [lowerExpr, StateT.run, StateT.bind, bind, Except.bind, leftRun, rightRun] at compiled
            | ok output =>
                rcases output with ⟨rightPolynomial, state⟩
                have operands {x y : F}
                    (leftEval : EvalExprWith calls
                      (localsEnvironment locals (Row.assignment ⟨function, initial⟩)) left x)
                    (rightEval : EvalExprWith calls
                      (localsEnvironment locals (Row.assignment ⟨function, initial⟩)) right y) :
                    ∃ values, initial.IsPrefix values ∧ values.length = state.nextVar ∧
                      state.WellFormed ∧ leftPolynomial.inBounds state.nextVar = true ∧
                      rightPolynomial.inBounds state.nextVar = true ∧
                      state.Valid calls (Row.assignment ⟨function, values⟩) ∧
                      leftPolynomial.denote (Row.assignment ⟨function, values⟩) = x ∧
                      rightPolynomial.denote (Row.assignment ⟨function, values⟩) = y := by
                  obtain ⟨firstValues, firstExtension, firstSize, firstLayout, leftBound, firstValid, leftValue⟩ :=
                    lowerExpr_complete leftRun layout localsBound enableBound size valid active leftEval
                  have increase : before.nextVar ≤ middle.nextVar := by
                    rw [← size, ← firstSize]
                    exact firstExtension.length_le
                  obtain ⟨values, extension, finalSize, finalLayout, rightBound, finalValid, rightValue⟩ :=
                    lowerExpr_complete rightRun firstLayout
                      (fun binding member => lt_of_lt_of_le (localsBound binding member) increase)
                      (ArithExpr.inBounds_mono increase enableBound) firstSize firstValid
                      (by rw [denote_of_prefix firstExtension size enableBound]; exact active)
                      (by rw [localsEnvironment_of_prefix firstExtension size localsBound]; exact rightEval)
                  have nextIncrease : middle.nextVar ≤ state.nextVar := by
                    rw [← firstSize, ← finalSize]
                    exact extension.length_le
                  refine ⟨values, firstExtension.trans extension, finalSize, finalLayout,
                    ArithExpr.inBounds_mono nextIncrease leftBound, rightBound, finalValid, ?_, rightValue⟩
                  rw [denote_of_prefix extension firstSize leftBound]
                  exact leftValue
                cases body with
                | add leftEval rightEval | sub leftEval rightEval | mul leftEval rightEval =>
                    simp [lowerExpr, StateT.run, StateT.bind, StateT.pure, bind, pure,
                      Except.bind, Except.pure, leftRun, rightRun] at compiled
                    rcases compiled with ⟨rfl, rfl⟩
                    obtain ⟨values, extension, finalSize, finalLayout, leftBound, rightBound,
                      finalValid, leftValue, rightValue⟩ := operands leftEval rightEval
                    refine ⟨values, extension, finalSize, finalLayout, ?_, finalValid, ?_⟩
                    · simp [ArithExpr.inBounds, leftBound, rightBound]
                    · simp [ArithExpr.denote, leftValue, rightValue]
                | div leftEval rightEval nonzero =>
                    rename_i x y
                    simp [lowerExpr, StateT.run, StateT.bind, StateT.pure, bind, pure,
                      Except.bind, Except.pure, leftRun, rightRun] at compiled
                    rcases compiled with ⟨rfl, rfl⟩
                    obtain ⟨values, extension, finalSize, finalLayout, leftBound, rightBound,
                      finalValid, leftValue, rightValue⟩ := operands leftEval rightEval
                    let finished := values ++ [y⁻¹]
                    have extended : values.IsPrefix finished := List.prefix_append _ _
                    have inverse : Row.assignment ⟨function, finished⟩ state.nextVar = y⁻¹ := by
                      simp [Row.assignment, finished, ← finalSize]
                    have increase : before.nextVar ≤ state.nextVar := by
                      rw [← size, ← finalSize]
                      exact extension.length_le
                    have finalEnable := ArithExpr.inBounds_mono increase enableBound
                    have activeFinal : enable.denote (Row.assignment ⟨function, finished⟩) = 1 := by
                      rw [denote_of_prefix (extension.trans extended) size enableBound]
                      exact active
                    have leftFinal : leftPolynomial.denote (Row.assignment ⟨function, finished⟩) = x := by
                      rw [denote_of_prefix extended finalSize leftBound]
                      exact leftValue
                    have rightFinal : rightPolynomial.denote (Row.assignment ⟨function, finished⟩) = y := by
                      rw [denote_of_prefix extended finalSize rightBound]
                      exact rightValue
                    have equationBound :
                        (ArithExpr.mul enable (.sub (.mul rightPolynomial (.var state.nextVar)) (.const 1))).inBounds
                          (state.nextVar + 1) = true := by
                      simp [ArithExpr.inBounds, ArithExpr.inBounds_mono (Nat.le_succ _) finalEnable,
                        ArithExpr.inBounds_mono (Nat.le_succ _) rightBound]
                    have oldValid := finalValid.of_prefix finalLayout finalSize extended
                    have freshValid : { state with nextVar := state.nextVar + 1 }.Valid calls
                        (Row.assignment ⟨function, finished⟩) := ⟨oldValid.constraints, oldValid.calls⟩
                    refine ⟨finished, extension.trans extended, by simp [finished, finalSize],
                      finalLayout.fresh.constrain equationBound, ?_, freshValid.constrain ?_, ?_⟩
                    · simp [ArithExpr.inBounds, ArithExpr.inBounds_mono (Nat.le_succ _) leftBound]
                    · simp [ArithExpr.denote, activeFinal, rightFinal, inverse, nonzero]
                    · simp [ArithExpr.denote, leftFinal, inverse, div_eq_mul_inv]
    | call name args =>
        cases argsRun : lowerArgs function locals enable args before with
        | error error =>
            simp [lowerExpr, StateT.run, StateT.bind, bind, Except.bind, argsRun] at compiled
        | ok output =>
            rcases output with ⟨arguments, state⟩
            simp [lowerExpr, boolean, StateT.run, StateT.bind, StateT.pure, bind, pure,
              Except.bind, Except.pure, argsRun] at compiled
            rcases compiled with ⟨rfl, rfl⟩
            cases body with
            | call argsEval callee =>
                obtain ⟨values, extension, finalSize, finalLayout, argsBound, finalValid, argsValue⟩ :=
                  lowerArgs_complete argsRun layout localsBound enableBound size valid active argsEval
                let finished := values ++ [result]
                have extended : values.IsPrefix finished := List.prefix_append _ _
                have output : Row.assignment ⟨function, finished⟩ state.nextVar = result := by
                  simp [Row.assignment, finished, ← finalSize]
                have increase : before.nextVar ≤ state.nextVar := by
                  rw [← size, ← finalSize]
                  exact extension.length_le
                have finalEnable := ArithExpr.inBounds_mono (Nat.le_succ _)
                  (ArithExpr.inBounds_mono increase enableBound)
                have activeFinal : enable.denote (Row.assignment ⟨function, finished⟩) = 1 := by
                  rw [denote_of_prefix (extension.trans extended) size enableBound]
                  exact active
                have argumentsUnchanged : arguments.map (ArithExpr.denote (Row.assignment ⟨function, finished⟩)) =
                    arguments.map (ArithExpr.denote (Row.assignment ⟨function, values⟩)) := by
                  apply List.map_congr_left
                  exact fun argument member => denote_of_prefix extended finalSize (argsBound argument member)
                have booleanBound : (ArithExpr.mul enable (.sub enable (.const 1))).inBounds
                    (state.nextVar + 1) = true := by simp [ArithExpr.inBounds, finalEnable]
                have sendBound : (⟨name, arguments, state.nextVar, enable⟩ : Send F).inBounds
                    (state.nextVar + 1) = true := by
                  simp only [Send.inBounds, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
                  exact ⟨⟨Nat.lt_succ_self _, finalEnable⟩,
                    fun argument member => ArithExpr.inBounds_mono (Nat.le_succ _) (argsBound argument member)⟩
                have oldValid := finalValid.of_prefix finalLayout finalSize extended
                have freshValid : { state with nextVar := state.nextVar + 1 }.Valid calls
                    (Row.assignment ⟨function, finished⟩) := ⟨oldValid.constraints, oldValid.calls⟩
                have booleanZero : (ArithExpr.mul enable (.sub enable (.const 1))).denote
                    (Row.assignment ⟨function, finished⟩) = 0 := by simp [ArithExpr.denote, activeFinal]
                have withBoolean := finalLayout.fresh.constrain booleanBound
                have withBooleanValid := freshValid.constrain booleanZero
                refine ⟨finished, extension.trans extended, by simp [finished, finalSize],
                  ⟨withBoolean.constraints, ?_⟩, by simp [ArithExpr.inBounds],
                  ⟨withBooleanValid.constraints, ?_⟩, output⟩
                · intro send member
                  simp only [Array.toList_push, List.mem_append, List.mem_singleton] at member
                  rcases member with member | rfl
                  · exact withBoolean.sends send member
                  · exact sendBound
                · intro send member enabled
                  simp only [Array.toList_push, List.mem_append, List.mem_singleton] at member
                  rcases member with member | rfl
                  · exact withBooleanValid.calls send member enabled
                  · change calls name _ _
                    rw [argumentsUnchanged, argsValue, output]
                    exact callee
    | matchValue =>
        -- Remaining obligation: construct selectors, default inverse witnesses, and
        -- satisfying assignments for inactive arms without evaluating their bodies.
        sorry
  termination_by sizeOf expr

  theorem lowerArgs_complete [Field F] [DecidableEq F]
      {function : String} {locals : List (String × Var)} {enable : ArithExpr F} {args : List (Expr F)}
      {before after : BuildState F} {polynomials : List (ArithExpr F)}
      (compiled : (lowerArgs function locals enable args).run before = .ok (polynomials, after))
      (layout : before.WellFormed)
      (localsBound : ∀ binding ∈ locals, binding.2 < before.nextVar)
      (enableBound : enable.inBounds before.nextVar = true)
      {calls : CallRelation F} {initial : List F} (size : initial.length = before.nextVar)
      (valid : before.Valid calls (Row.assignment ⟨function, initial⟩))
      (active : enable.denote (Row.assignment ⟨function, initial⟩) = 1)
      {results : List F}
      (body : EvalArgsWith calls
        (localsEnvironment locals (Row.assignment ⟨function, initial⟩)) args results) :
      ∃ values, initial.IsPrefix values ∧ values.length = after.nextVar ∧
        after.WellFormed ∧ (∀ polynomial ∈ polynomials, polynomial.inBounds after.nextVar = true) ∧
        after.Valid calls (Row.assignment ⟨function, values⟩) ∧
        polynomials.map (ArithExpr.denote (Row.assignment ⟨function, values⟩)) = results := by
    cases args with
    | nil =>
        simp [lowerArgs, StateT.run, StateT.pure, pure, Except.pure] at compiled
        rcases compiled with ⟨rfl, rfl⟩
        cases body
        exact ⟨initial, ⟨[], by simp⟩, size, layout, by simp, valid, rfl⟩
    | cons head tail =>
        cases headRun : lowerExpr function locals enable head before with
        | error error =>
            simp [lowerArgs, StateT.run, StateT.bind, bind, Except.bind, headRun] at compiled
        | ok output =>
            rcases output with ⟨headPolynomial, middle⟩
            cases tailRun : lowerArgs function locals enable tail middle with
            | error error =>
                simp [lowerArgs, StateT.run, StateT.bind, bind, Except.bind, headRun, tailRun] at compiled
            | ok output =>
                rcases output with ⟨tailPolynomials, state⟩
                simp [lowerArgs, StateT.run, StateT.bind, StateT.pure, bind, pure,
                  Except.bind, Except.pure, headRun, tailRun] at compiled
                rcases compiled with ⟨rfl, rfl⟩
                cases body with
                | cons headEval tailEval =>
                    obtain ⟨firstValues, firstExtension, firstSize, firstLayout, headBound, firstValid, headValue⟩ :=
                      lowerExpr_complete headRun layout localsBound enableBound size valid active headEval
                    have increase : before.nextVar ≤ middle.nextVar := by
                      rw [← size, ← firstSize]
                      exact firstExtension.length_le
                    obtain ⟨values, extension, finalSize, finalLayout, tailBounds, finalValid, tailValue⟩ :=
                      lowerArgs_complete tailRun firstLayout
                        (fun binding member => lt_of_lt_of_le (localsBound binding member) increase)
                        (ArithExpr.inBounds_mono increase enableBound) firstSize firstValid
                        (by rw [denote_of_prefix firstExtension size enableBound]; exact active)
                        (by rw [localsEnvironment_of_prefix firstExtension size localsBound]; exact tailEval)
                    have nextIncrease : middle.nextVar ≤ state.nextVar := by
                      rw [← firstSize, ← finalSize]
                      exact extension.length_le
                    refine ⟨values, firstExtension.trans extension, finalSize, finalLayout, ?_, finalValid, ?_⟩
                    · intro polynomial member
                      rcases List.mem_cons.mp member with rfl | member
                      · exact ArithExpr.inBounds_mono nextIncrease headBound
                      · exact tailBounds polynomial member
                    · simp only [List.map_cons, tailValue]
                      rw [denote_of_prefix extension firstSize headBound, headValue]
  termination_by sizeOf args

end

end Aiur.Circuit.Compiler
