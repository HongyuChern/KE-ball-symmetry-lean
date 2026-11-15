import KEBall.DirichletFirstJetEnergy

/-! A genuine rotation difference of a zero-trace C2 function is
controlled in L2 by its own Hessian, uniformly in the nonzero step. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 700000

open Filter InnerProductSpace MeasureTheory Metric Set
open scoped ContDiff Gradient Topology

namespace KEBall

theorem integral_orthogonalFlow_difference_sq_le_smooth_hessian {n : ℕ} (hn : 0 < n)
    {u : E n → ℝ} (hu : SmoothNear (closedUnitBall n) u)
    (hu0 : ∀ x ∈ unitSphere n, u x = 0)
    (S : E n →L[ℝ] E n) (hS : star S = -S) {t : ℝ} (ht : t ≠ 0) :
    (∫ x in unitBall n, (dirichletOrthogonalDifference (orthogonalFlow S hS t) t u x) ^ 2 ∂volume0 n) ≤
      (4 * ‖S‖ ^ 2) * ∫ x in unitBall n, ‖realHessian u x‖ ^ 2 ∂volume0 n := by
  obtain ⟨v, hv, he⟩ := MoserTrudinger.exists_global_contDiff_of_smoothNear hu
  have hv0 (x : E n) (hx : x ∈ unitSphere n) : v x = 0 :=
    (he x (sphere_subset_closedBall hx)).self_of_nhds.trans (hu0 x hx)
  have hGN (x : E n) : ‖∇ v x‖ = ‖fderiv ℝ v x‖ := by
    rw [← toDual_gradient]
    exact ((toDual ℝ (E n)).norm_map (∇ v x)).symm
  have h := integral_sq_smooth_angularDifferenceQuotient_le hn S hS hv ht
  simp only [hGN] at h
  have h' := h.trans (mul_le_mul_of_nonneg_left
    (integral_fderiv_sq_le_four_realHessian_sq hn hv hv0) (sq_nonneg _))
  have hD : (∫ x in unitBall n, (t⁻¹ * (v (orthogonalFlow S hS t x) - v x)) ^ 2 ∂volume0 n) =
      ∫ x in unitBall n, (dirichletOrthogonalDifference (orthogonalFlow S hS t) t u x) ^ 2 ∂volume0 n := by
    apply setIntegral_congr_fun measurableSet_ball
    intro x hx
    have hxc := ball_subset_closedBall hx
    dsimp only
    rw [(he x hxc).self_of_nhds,
      (he _ (orthogonalFlow_mapsTo_closedUnitBall S hS t hxc)).self_of_nhds]
    simp only [dirichletOrthogonalDifference, div_eq_mul_inv, mul_comm]
  have hH : (∫ x in unitBall n, ‖realHessian v x‖ ^ 2 ∂volume0 n) =
      ∫ x in unitBall n, ‖realHessian u x‖ ^ 2 ∂volume0 n := by
    apply setIntegral_congr_fun measurableSet_ball
    intro x hx
    dsimp only
    unfold realHessian
    rw [(he x (ball_subset_closedBall hx)).fderiv.fderiv_eq]
  rw [hD, hH] at h'
  exact h'.trans_eq (by ring)

theorem integral_orthogonalFlow_difference_sq_le_within_hessian {n : ℕ} (hn : 0 < n)
    {u : E n → ℝ} (hu : ContDiffOn ℝ 2 u (closedUnitBall n))
    (huS : ContDiffOn ℝ ∞ u (unitBall n)) (hu0 : ∀ x ∈ unitSphere n, u x = 0)
    (S : E n →L[ℝ] E n) (hS : star S = -S) {t : ℝ} (ht : t ≠ 0) :
    (∫ x in unitBall n, (dirichletOrthogonalDifference (orthogonalFlow S hS t) t u x) ^ 2 ∂volume0 n) ≤
      (4 * ‖S‖ ^ 2) * ∫ x in unitBall n, ‖dirichletWithinRealHessian u x‖ ^ 2 ∂volume0 n := by
  obtain ⟨v, hv, hV, _, hH⟩ := exists_dirichlet_zeroBoundary_smooth_C2_approximation hu huS hu0
  let R := orthogonalFlow S hS t
  have hMaps : closedUnitBall n ⊆ R ⁻¹' closedUnitBall n :=
    orthogonalFlow_mapsTo_closedUnitBall S hS t
  have hVC (j : ℕ) : ContinuousOn (v j) (closedUnitBall n) :=
    fun x hx => ((hv j).1.contDiffAt hx).continuousAt.continuousWithinAt
  have hDiff : TendstoUniformlyOn
      (fun j x => v j (R x) - v j x) (fun x => u (R x) - u x) atTop (closedUnitBall n) :=
    ((hV.comp R).mono hMaps).sub hV
  have hDiffC : ContinuousOn (fun x => u (R x) - u x) (closedUnitBall n) :=
    (hu.continuousOn.comp R.continuous.continuousOn hMaps).sub hu.continuousOn
  have hD := dirichlet_uniform_limit_comp_continuous (isCompact_closedBall _ _)
    hDiffC hDiff (show Continuous (fun z : ℝ => (z / t) ^ 2) from
      (continuous_id.div_const t).pow 2)
  have hDC : ContinuousOn (fun x => (dirichletOrthogonalDifference R t u x) ^ 2) (closedUnitBall n) :=
    (continuousOn_dirichletOrthogonalDifference R t hu.continuousOn).pow 2
  have hDCv (j : ℕ) : ContinuousOn (fun x => (dirichletOrthogonalDifference R t (v j) x) ^ 2)
      (closedUnitBall n) := (continuousOn_dirichletOrthogonalDifference R t (hVC j)).pow 2
  have hDI := tendsto_integral_dirichlet_uniform_limit hn hDC hDCv hD
  have hHC := continuousOn_dirichletWithinRealHessian hu
  have hNormH : Continuous (fun H : E n →L[ℝ] E n →L[ℝ] ℝ => ‖H‖ ^ 2) := continuous_norm.pow 2
  have hHL := dirichlet_uniform_limit_comp_continuous (isCompact_closedBall _ _) hHC hH hNormH
  have hHCv (j : ℕ) : ContinuousOn (realHessian (v j)) (closedUnitBall n) := by
    intro x hx
    exact (realHessian_contDiffAt ((hv j).1.contDiffAt hx)).continuousAt.continuousWithinAt
  have hHI := tendsto_integral_dirichlet_uniform_limit hn (hNormH.comp_continuousOn hHC)
    (fun j => hNormH.comp_continuousOn (hHCv j)) hHL
  exact le_of_tendsto_of_tendsto hDI (hHI.const_mul (4 * ‖S‖ ^ 2))
    (Eventually.of_forall (fun j =>
      integral_orthogonalFlow_difference_sq_le_smooth_hessian hn (hv j).1 (hv j).2 S hS ht))

end KEBall
