import Drafts.Validation.FrozenTargets.Classification
import Drafts.Validation.FrozenTargets.RadialExistence
import Drafts.Validation.FrozenTargets.SolutionCounts
import Drafts.Validation.FrozenTargets.BoundaryIdentities
import Drafts.Validation.FrozenTargets.LowerSlope
import Drafts.Validation.FrozenTargets.LogarithmicFlux
import Drafts.Validation.FrozenTargets.NormalizedClassification
import Drafts.Validation.Stage11Contract

/-! Stage12 SOURCE_DRAFT_UNCOMPILED. Individual frozen-goal consumers
are assembled without altering the v4 specification or IsSolution. -/
set_option autoImplicit false

namespace KEBall.Stage12Contract

theorem all_frozen_specifications :
    ClassificationStatement ∧
    RadialExistenceStatement ∧
    SolutionCountsStatement ∧
    BoundaryIdentitiesStatement ∧
    LowerSlopeStatement ∧
    LogarithmicFluxStatement ∧
    NormalizedClassificationStatement :=
  ⟨KEBall.Stage12Targets.Classification.candidate, KEBall.Stage12Targets.RadialExistence.candidate, KEBall.Stage12Targets.SolutionCounts.candidate, KEBall.Stage12Targets.BoundaryIdentities.candidate, KEBall.Stage12Targets.LowerSlope.candidate, KEBall.Stage12Targets.LogarithmicFlux.candidate, KEBall.Stage12Targets.NormalizedClassification.candidate⟩

#print axioms all_frozen_specifications

end KEBall.Stage12Contract
