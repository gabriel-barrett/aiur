import Aiur.AST

namespace Aiur.Value

@[simp] theorem map_map (f : α → β) (g : β → γ) (value : Value α) :
    (value.map f).map g = value.map (g ∘ f) := by
  cases value with
  | field => simp [Value.map]
  | tuple items =>
      simp only [Value.map, List.map_map, Value.tuple.injEq]
      apply List.map_congr_left
      intro value member
      exact map_map f g value
termination_by sizeOf value
decreasing_by
  simp_wf
  have := List.sizeOf_lt_of_mem ‹_ ∈ _›
  omega

@[simp] theorem type_map (f : α → β) (value : Value α) :
    (value.map f).type = value.type := by
  cases value with
  | field => simp [Value.map, Value.type]
  | tuple items =>
      simp only [Value.map, Value.type, List.map_map, Ty.tuple.injEq]
      apply List.map_congr_left
      intro value member
      exact type_map f value
termination_by sizeOf value
decreasing_by
  simp_wf
  have := List.sizeOf_lt_of_mem ‹_ ∈ _›
  omega

end Aiur.Value
