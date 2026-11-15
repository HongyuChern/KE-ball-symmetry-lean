import Drafts.KEBall.ExteriorRecovery
import Drafts.Validation.Stage12Contract

/-! Stage13 SOURCE_DRAFT_UNCOMPILED. Coordinate recovery is an additional
consumer; the seven frozen specifications and original solution remain intact. -/
set_option autoImplicit false

namespace KEBall.Stage13Contract

theorem coordinate_recovery {n : ℕ} (u : E n → ℝ) (x : E n) :
    ∀ i j : Fin n, exteriorCoefficient (d0Exterior u x) i j = complexHessian u x i j :=
  exteriorCoefficient_d0 u x

theorem all_frozen_specifications :
    ClassificationStatement ∧ RadialExistenceStatement ∧ SolutionCountsStatement ∧
    BoundaryIdentitiesStatement ∧ LowerSlopeStatement ∧ LogarithmicFluxStatement ∧
    NormalizedClassificationStatement := Stage12Contract.all_frozen_specifications

#print axioms coordinate_recovery
#print axioms all_frozen_specifications

end KEBall.Stage13Contract
