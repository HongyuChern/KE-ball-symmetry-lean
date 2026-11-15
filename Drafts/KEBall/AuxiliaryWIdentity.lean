import Drafts.KEBall.ComplexProductLog
import Drafts.KEBall.AuxiliaryPRegularity

/-!
# The actual logarithmic auxiliary function

SOURCE_DRAFT_UNCOMPILED: no kernel-verification claim is made.
The original solution hypotheses imply both positivity and local regularity
of P-1. The exact logarithmic Laplacian below is therefore an unconditional
consequence of those solution hypotheses; its nonnegativity still requires
the actual differential identity for P and the actual Kato estimate.
-/

set_option autoImplicit false
open scoped ContDiff

namespace KEBall

/-- The actual logarithmic identity holds throughout the closed ball when
the original dimension hypothesis guarantees the strict boundary gap. -/
theorem IsSolution.complexLaplacian_auxiliaryW_closedBall {n : ℕ} (hn : 2 ≤ n)
    {μ : ℝ} {u : E n → ℝ} (hu : IsSolution n μ u) {x : E n}
    (hx : x ∈ closedUnitBall n) :
    complexLaplacian u (auxiliaryW u) x =
      complexLaplacian u (auxiliaryP u) x / (auxiliaryP u x - 1) -
        metricGradientNormSq u (auxiliaryP u) x / (auxiliaryP u x - 1) ^ 2 := by
  exact complexLaplacian_log_sub_const u (hu.auxiliaryP_contDiffAt_closedBall hx) 1
    (hu.auxiliaryP_sub_one_pos_closedBall hn hx)

/-- On the open ball the same differential identity only needs n>0. -/
theorem IsSolution.complexLaplacian_auxiliaryW_unitBall {n : ℕ} (hn : 0 < n)
    {μ : ℝ} {u : E n → ℝ} (hu : IsSolution n μ u) {x : E n}
    (hx : x ∈ unitBall n) :
    complexLaplacian u (auxiliaryW u) x =
      complexLaplacian u (auxiliaryP u) x / (auxiliaryP u x - 1) -
        metricGradientNormSq u (auxiliaryP u) x / (auxiliaryP u x - 1) ^ 2 := by
  exact complexLaplacian_log_sub_const u
    (hu.auxiliaryP_contDiffAt_closedBall (Metric.ball_subset_closedBall hx)) 1
    (sub_pos.mpr (hu.auxiliaryP_gt_one_unitBall hn hx))

#print axioms IsSolution.complexLaplacian_auxiliaryW_closedBall
#print axioms IsSolution.complexLaplacian_auxiliaryW_unitBall

end KEBall
