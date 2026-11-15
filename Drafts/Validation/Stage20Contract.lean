import Drafts.Validation.Stage18Contract
import Drafts.KEBall.CriticalBoundaryDeficit

/-! Stage20 SOURCE_DRAFT_UNCOMPILED. The seven primary specifications remain
unchanged; the critical quantitative estimate is only a supplement. -/
set_option autoImplicit false

namespace KEBall.Stage20Contract

theorem all_frozen_d1_and_critical_deficit :
    ((ClassificationStatement ∧ RadialExistenceStatement ∧ SolutionCountsStatement ∧
      BoundaryIdentitiesStatement ∧ LowerSlopeStatement ∧ LogarithmicFluxStatement ∧
      NormalizedClassificationStatement) ∧ D1NormalizedClassificationStatement) ∧
    CriticalBoundaryDeficitStatement :=
  ⟨Stage18Contract.all_frozen_and_d1, criticalBoundaryDeficit⟩

end KEBall.Stage20Contract
