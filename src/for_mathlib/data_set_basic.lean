import data.set.basic

open set

namespace set
-- near range_id
variables {α : Type*}
@[simp] theorem range_subtype_val {p : α → Prop} : range (@subtype.val α p) = set_of p :=
set.ext $ by simp

-- where?
-- Also, use it in embedding_subtype_val
theorem injective_subtype_val {p : α → Prop} : function.injective (@subtype.val α p) :=
assume a₁ a₂ h, subtype.eq h

end set
