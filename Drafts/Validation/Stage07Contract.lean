import Drafts.KEBall.BoundaryLogarithm
import Drafts.KEBall.LogarithmicEquality

/-!
Stage07 SOURCE_DRAFT_UNCOMPILED.
Consumer of the exact frozen Proposition 3.1 specification, without any
boundary-jet, flux, integrability, or vanishing premise beyond its statement.
This source contract is not an elaboration or kernel-verification receipt.
-/

set_option autoImplicit false

namespace KEBall.Stage07Contract

/-- The four clauses of the unchanged specification, assembled from the
actual-solution source chain. -/
theorem logarithmicFluxStatement : LogarithmicFluxStatement := by
  intro n hn μ u hu
  refine ⟨?_, ?_, hu.logarithmicFlux_identity hn, ?_⟩
  · intro x hx
    exact hu.auxiliaryP_gt_one_closedBall hn hx
  · intro x hx
    exact hu.auxiliaryW_laplacian_nonneg hn hx
  · intro hzero
    exact hu.logarithmicFlux_equality_consequence hn hzero

#print axioms logarithmicFluxStatement

end KEBall.Stage07Contract
