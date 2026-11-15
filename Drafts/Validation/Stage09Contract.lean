import Drafts.KEBall.ClassificationEndpoints
import Drafts.KEBall.NormalizedEndpoints
import Drafts.Validation.Stage07Contract
import KEBall.Pohozaev
import KEBall.LowerSlope

/-!
Stage09 SOURCE_DRAFT_UNCOMPILED.
All seven frozen determinant/coordinate specifications are source consumers.
No hypothesis, definition or specification is replaced. This conjunction is
not a kernel receipt, a real Levi-Civita identification, or the D0 form bridge.
-/
set_option autoImplicit false

namespace KEBall.Stage09Contract

theorem all_frozen_specifications :
    ClassificationStatement ∧
    RadialExistenceStatement ∧
    SolutionCountsStatement ∧
    BoundaryIdentitiesStatement ∧
    LowerSlopeStatement ∧
    LogarithmicFluxStatement ∧
    NormalizedClassificationStatement :=
  ⟨Stage09.classification, radialExistence, Stage09.solutionCounts,
    boundaryIdentities, lowerSlopeStatement, Stage07Contract.logarithmicFluxStatement,
    Stage09.normalizedClassification⟩

#print axioms all_frozen_specifications

end KEBall.Stage09Contract
