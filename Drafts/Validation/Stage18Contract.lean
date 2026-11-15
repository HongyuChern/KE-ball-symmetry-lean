import Drafts.KEBall.DOneNormalized
import Drafts.Validation.Stage16Contract

/-! Stage18 SOURCE_DRAFT_UNCOMPILED. The seven frozen goals stay unchanged;
the actual D1 normalized classification is an additional paper convention. -/
set_option autoImplicit false

namespace KEBall.Stage18Contract

theorem all_frozen_and_d1 :
    (ClassificationStatement ∧ RadialExistenceStatement ∧ SolutionCountsStatement ∧
      BoundaryIdentitiesStatement ∧ LowerSlopeStatement ∧ LogarithmicFluxStatement ∧
      NormalizedClassificationStatement) ∧ D1NormalizedClassificationStatement :=
  ⟨Stage16Contract.all_frozen_specifications, d1NormalizedClassification⟩

#print axioms all_frozen_and_d1

end KEBall.Stage18Contract
