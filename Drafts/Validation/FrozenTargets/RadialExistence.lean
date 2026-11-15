import KEBall.Endpoints

/-! Stage12 SOURCE_DRAFT_UNCOMPILED.
An isolated consumer of exactly the unchanged frozen specification.
No new mathematical assumption or proof mechanism is introduced. -/
set_option autoImplicit false

namespace KEBall.Stage12Targets.RadialExistence

theorem candidate : RadialExistenceStatement := KEBall.radialExistence

#print axioms candidate

end KEBall.Stage12Targets.RadialExistence
