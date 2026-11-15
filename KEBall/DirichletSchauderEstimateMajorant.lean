import KEBall.DirichletSchauderUniformConstants

/-!
# A source-and-supremum majorant for the frozen Schauder estimate

This bounds the actual imported constant using only the norms of the
coefficient square root and its inverse, the source bounds, and the
supremum norm of the unknown.  In particular it does not depend on an
initial bound for the Hessian of a difference quotient.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open DifferentialGeometry.Analysis.Schauder
open DifferentialGeometry.Analysis.Parabolic.Euclidean
open scoped NNReal

namespace KEBall

theorem dirichlet_heatSupSchauderConst_mono {n : ℕ} {t : ℝ} (ht : 0 < t)
    {u v : BoundedContinuousFunction (E n) ℝ} (huv : ‖u‖ ≤ ‖v‖) :
    heatSupSchauderConst t u ≤ heatSupSchauderConst t v := by
  have hScale : 0 ≤ (heatScale t)⁻¹ := inv_nonneg.mpr (heatScale_pos ht).le
  have htInv : 0 ≤ t⁻¹ := inv_nonneg.mpr ht.le
  have hC1 := heatC1_nonneg (V := E n)
  have hC2 := heatC2_nonneg (V := E n)
  have hC3 := heatC3_nonneg (V := E n)
  unfold heatSupSchauderConst heatSupHessianHolderConst
  apply add_le_add
  · apply Finset.sum_le_sum
    intro j _
    cases j with
    | zero => exact huv
    | succ j =>
      cases j with
      | zero =>
        change Real.toNNReal ((heatScale t)⁻¹ * heatC1 (E n) * ‖u‖) ≤
          Real.toNNReal ((heatScale t)⁻¹ * heatC1 (E n) * ‖v‖)
        exact Real.toNNReal_mono (mul_le_mul_of_nonneg_left huv (mul_nonneg hScale hC1))
      | succ j =>
        change Real.toNNReal (t⁻¹ * heatC2 (E n) * ‖u‖) ≤
          Real.toNNReal (t⁻¹ * heatC2 (E n) * ‖v‖)
        exact Real.toNNReal_mono (mul_le_mul_of_nonneg_left huv (mul_nonneg htInv hC2))
  · apply Finset.sum_le_sum
    intro _ _
    unfold heatD2SupHolderConst
    apply max_le_max
    · exact mul_le_mul_of_nonneg_left
        (Real.toNNReal_mono (mul_le_mul_of_nonneg_left huv (mul_nonneg htInv hC2))) (by norm_num)
    · apply Real.toNNReal_mono
      gcongr

theorem dirichlet_heatSupSchauderConst_le_const {n : ℕ}
    {u : BoundedContinuousFunction (E n) ℝ} {U : ℝ≥0} (hu : ‖u‖₊ ≤ U) :
    heatSupSchauderConst 1 u ≤
      heatSupSchauderConst 1 (BoundedContinuousFunction.const (E n) (U : ℝ)) := by
  apply dirichlet_heatSupSchauderConst_mono zero_lt_one
  simpa only [BoundedContinuousFunction.norm_const_eq, Real.norm_of_nonneg U.coe_nonneg]
    using (show ‖u‖ ≤ (U : ℝ) from hu)

noncomputable def dirichletSchauderEstimateMajorant (n : ℕ)
    (α L R K B U : ℝ≥0) : ℝ≥0 :=
  dirichletSchauderChangeConst α (max 1 R)
    (heatSupSchauderConst 1 (BoundedContinuousFunction.const (E n) (U : ℝ)) +
      heatDuhamelConstSchauderConst (V := E n) α (K * L ^ (α : ℝ)) B 1)

theorem dirichletSchauderConst_le_majorant {n : ℕ}
    (A : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) (hA : A.PosDef)
    {α L R U : ℝ≥0} (hα : α < 1)
    (hL : ‖(spdSqrtEquiv A hA : E n →L[ℝ] E n)‖₊ ≤ L)
    (hR : ‖((spdSqrtEquiv A hA).symm : E n →L[ℝ] E n)‖₊ ≤ R)
    (K B : ℝ≥0) (u : BoundedContinuousFunction (E n) ℝ) (hu : ‖u‖₊ ≤ U) :
    spdLaplacianSchauderConst A hA α K B u ≤
      dirichletSchauderEstimateMajorant n α L R K B U := by
  have hPull : ‖linPullBoundedContinuousFunction (spdSqrtEquiv A hA) u‖₊ ≤ U := by
    change ‖linPullBoundedContinuousFunction (spdSqrtEquiv A hA) u‖ ≤ (U : ℝ)
    rw [norm_linPullBoundedContinuousFunction]
    exact hu
  have hK : K * ‖(spdSqrtEquiv A hA : E n →L[ℝ] E n)‖₊ ^ (α : ℝ) ≤
      K * L ^ (α : ℝ) := by gcongr
  exact dirichletSchauderChangeConst_mono (max_le_max_left 1 hR)
    (add_le_add (dirichlet_heatSupSchauderConst_le_const hPull)
      (dirichlet_heatDuhamelConstSchauderConst_mono hα hK le_rfl))

end KEBall
