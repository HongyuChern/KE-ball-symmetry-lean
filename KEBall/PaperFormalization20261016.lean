import KEBall.PaperBridges20261016
import Drafts.Validation.FrozenTargets.RadialExistence
import Drafts.Validation.FrozenTargets.LowerSlope
import Drafts.Validation.FrozenTargets.BoundaryIdentities
import Drafts.Validation.FrozenTargets.LogarithmicFlux
import Drafts.Validation.FrozenTargets.Classification
import Drafts.Validation.FrozenTargets.SolutionCounts
import Drafts.Validation.FrozenTargets.NormalizedClassification

/-! Explicit acceptance endpoints. Frozen results are reused unchanged;
every additional component is separately type-checked and axiom-audited. -/
set_option autoImplicit false

namespace KEBall.Paper20261016

theorem exteriorConventions : ExteriorConventionStatement := by
  refine ⟨normalizedExteriorVolume_measure, ?_, ?_, ?_⟩
  · intro n u x
    exact d0Exterior_top u x
  · intro n μ u hu x hx v w
    exact hu.d0Exterior_evaluates_derivative hx v w
  · intro n u x hu
    exact d1Exterior_half hu

theorem metricConventions : MetricConventionStatement := by
  intro n μ u hu p hp
  obtain ⟨g, D, U, hU, hpU, hUB, hg, hbridge⟩ := hu.exists_local_fixed_metric_bridges hp
  refine ⟨g, D, U, hU, hpU, hUB, hg, ?_, hbridge⟩
  intro x hx v w
  exact hu.retained_ricci_eq_metric D hU hUB hg hx v w

theorem exponentialGeometricRigidity : ExponentialGeometricRigidityStatement := by
  intro n hn μ u hu p hp
  exact hu.exists_local_exponential_geometric_rigidity hn hp

theorem currentPaper : CurrentPaperStatement :=
  ⟨Stage12Targets.RadialExistence.candidate,
    Stage12Targets.LowerSlope.candidate,
    Stage12Targets.BoundaryIdentities.candidate,
    Stage12Targets.LogarithmicFlux.candidate,
    Stage12Targets.Classification.candidate,
    Stage12Targets.SolutionCounts.candidate,
    Stage12Targets.NormalizedClassification.candidate,
    radialSymmetry, meanFieldClassification, normalizationCorrespondence,
    exteriorConventions, metricConventions, exponentialGeometricRigidity,
    d1NormalizedClassification⟩

end KEBall.Paper20261016
