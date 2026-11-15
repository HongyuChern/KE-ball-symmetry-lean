import KEBall.DirichletPoincare
import KEBall.DirichletClosedBallHessianCoercivity
import KEBall.DirichletSmoothFlowEnergy
import KEBall.MoserTrudingerSmoothGibbsExtension

/-! First spatial energy is controlled by the full real Hessian for
zero sphere trace. The estimate is passed to actual C2 closed-ball jets. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 800000

open Filter InnerProductSpace MeasureTheory Metric Set
open scoped BigOperators ContDiff Gradient Topology

namespace KEBall

local notation "ν[" n "]" => Measure.restrict (volume0 n) (unitBall n)
local notation "e[" n "]" => EuclideanSpace.basisFun (Fin (2 * n)) ℝ

theorem integral_fderiv_sq_le_four_realHessian_sq {n : ℕ} (hn : 0 < n)
    {u : E n → ℝ} (hu : ContDiff ℝ ∞ u)
    (hu0 : ∀ x ∈ unitSphere n, u x = 0) :
    (∫ x in unitBall n, ‖fderiv ℝ u x‖ ^ 2 ∂volume0 n) ≤
      4 * ∫ x in unitBall n, ‖realHessian u x‖ ^ 2 ∂volume0 n := by
  let T (x : E n) := ∑ i, realHessian u x (e[n] i) (e[n] i)
  let V (x : E n) := u x • ∇ u x
  have hG : ContDiff ℝ ∞ (∇ u) :=
    (toDual ℝ (E n)).symm.toContinuousLinearEquiv.contDiff.comp
      (hu.fderiv_right (m := ∞) (by simp))
  have hV : ContDiff ℝ ∞ V := hu.smul hG
  have hHC : Continuous (realHessian u) :=
    ((hu.fderiv_right (m := ∞) (by simp)).fderiv_right (m := ∞) (by simp)).continuous
  have hTC : Continuous T := continuous_finsetSum _ (fun i _ =>
    (hHC.clm_apply continuous_const).clm_apply continuous_const)
  have hGN (x : E n) : ‖∇ u x‖ = ‖fderiv ℝ u x‖ := by
    rw [← toDual_gradient]
    exact ((toDual ℝ (E n)).norm_map (∇ u x)).symm
  have hDivG (x : E n) : euclideanDivergence (∇ u) x = T x := by
    unfold euclideanDivergence
    apply Finset.sum_congr rfl
    intro i _
    have hcoords (y : E n) : (∇ u y) i = fderiv ℝ u y (e[n] i) := by
      rw [← EuclideanSpace.inner_basisFun_real, inner_gradient_left]
    simp only [hcoords]
    rw [fderiv_clm_apply
      ((hu.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x)
      (differentiableAt_const (e[n] i))]
    simp [realHessian]
  have hDiv (x : E n) : euclideanDivergence V x = u x * T x + ‖fderiv ℝ u x‖ ^ 2 := by
    rw [euclideanDivergence_smul (hu.differentiable (by simp) x)
      (hG.differentiable (by simp) x), hDivG]
    rw [← inner_gradient_left, real_inner_self_eq_norm_sq, hGN]
  have hFlux (θ : Sphere n) : inner ℝ θ.1 (V θ.1) = 0 := by
    simp only [V, hu0 θ.1 θ.2, zero_smul, inner_zero_right]
  have hZ : (∫ x, u x * T x + ‖fderiv ℝ u x‖ ^ 2 ∂ν[n]) = 0 := by
    rw [← show euclideanDivergence V = (fun x => u x * T x + ‖fderiv ℝ u x‖ ^ 2)
      from funext hDiv]
    simpa only [hFlux, integral_zero, mul_zero] using
      integral_unitBall_divergence_normalized hn (hV.of_le (by simp))
  have hInt {f : E n → ℝ} (hf : Continuous f) : Integrable f ν[n] :=
    hf.continuousOn.integrableOn_of_subset_isCompact (isCompact_closedBall _ _)
      measurableSet_ball ball_subset_closedBall
      (by rw [volume0_unitBall n hn]; exact ENNReal.one_ne_top)
  have hdu : Continuous (fderiv ℝ u) := (hu.fderiv_right (m := ∞) (by simp)).continuous
  have huI := hInt (hu.continuous.pow 2)
  have hdI := hInt (hdu.norm.pow 2)
  have hHI := hInt (hHC.norm.pow 2)
  have hTI := hInt (hu.continuous.mul hTC)
  have hAdd := integral_add hTI hdI
  simp only [Pi.mul_apply, Pi.pow_apply] at hAdd
  rw [hAdd] at hZ
  have hTrace (x : E n) : |T x| ≤ (2 * n : ℝ) * ‖realHessian u x‖ := by
    calc
      _ ≤ ∑ i, |realHessian u x (e[n] i) (e[n] i)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin (2 * n), ‖realHessian u x‖ := by
        apply Finset.sum_le_sum
        intro i _
        have h := ((realHessian u x (e[n] i)).le_opNorm (e[n] i)).trans
          (mul_le_mul_of_nonneg_right ((realHessian u x).le_opNorm (e[n] i)) (norm_nonneg _))
        simpa only [Real.norm_eq_abs, (e[n]).orthonormal.norm_eq_one i, mul_one] using h
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat]
  have hPoint (x : E n) : -2 * (u x * T x) ≤ (n : ℝ) ^ 2 * u x ^ 2 + 4 * ‖realHessian u x‖ ^ 2 := by
    have hAbs : |u x * T x| ≤ |u x| * ((2 * n : ℝ) * ‖realHessian u x‖) := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hTrace x) (abs_nonneg _)
    have hDown := (neg_le_neg hAbs).trans (neg_abs_le (u x * T x))
    nlinarith only [hDown, sq_nonneg ((n : ℝ) * |u x| - 2 * ‖realHessian u x‖), sq_abs (u x)]
  have hI := integral_mono (hTI.const_mul (-2))
    ((huI.const_mul ((n : ℝ) ^ 2)).add (hHI.const_mul 4)) hPoint
  have hAddI := integral_add (huI.const_mul ((n : ℝ) ^ 2)) (hHI.const_mul 4)
  simp only [Pi.pow_apply] at hAddI
  simp only [Pi.add_apply, Pi.mul_apply, Pi.pow_apply] at hI
  rw [integral_const_mul, hAddI, integral_const_mul, integral_const_mul] at hI
  have hP := dirichlet_poincare_sq hn ⟨Set.univ, isOpen_univ, subset_univ _, hu.contDiffOn⟩ hu0
  change (n : ℝ) ^ 2 * (∫ x, u x ^ 2 ∂ν[n]) ≤ ∫ x, ‖fderiv ℝ u x‖ ^ 2 ∂ν[n] at hP
  nlinarith only [hI, hZ, hP]

theorem integral_fderiv_sq_le_four_realHessian_sq_of_smoothNear {n : ℕ} (hn : 0 < n)
    {u : E n → ℝ} (hu : SmoothNear (closedUnitBall n) u)
    (hu0 : ∀ x ∈ unitSphere n, u x = 0) :
    (∫ x in unitBall n, ‖fderiv ℝ u x‖ ^ 2 ∂volume0 n) ≤
      4 * ∫ x in unitBall n, ‖realHessian u x‖ ^ 2 ∂volume0 n := by
  obtain ⟨v, hv, he⟩ := MoserTrudinger.exists_global_contDiff_of_smoothNear hu
  have hv0 (x : E n) (hx : x ∈ unitSphere n) : v x = 0 :=
    (he x (sphere_subset_closedBall hx)).self_of_nhds.trans (hu0 x hx)
  have h := integral_fderiv_sq_le_four_realHessian_sq hn hv hv0
  have hD : (∫ x in unitBall n, ‖fderiv ℝ v x‖ ^ 2 ∂volume0 n) =
      ∫ x in unitBall n, ‖fderiv ℝ u x‖ ^ 2 ∂volume0 n := by
    apply setIntegral_congr_fun measurableSet_ball
    intro x hx
    dsimp only
    rw [(he x (ball_subset_closedBall hx)).fderiv_eq]
  have hH : (∫ x in unitBall n, ‖realHessian v x‖ ^ 2 ∂volume0 n) =
      ∫ x in unitBall n, ‖realHessian u x‖ ^ 2 ∂volume0 n := by
    apply setIntegral_congr_fun measurableSet_ball
    intro x hx
    dsimp only
    unfold realHessian
    rw [(he x (ball_subset_closedBall hx)).fderiv.fderiv_eq]
  rwa [hD, hH] at h

theorem integral_withinFirstJet_sq_le_four_withinHessian_sq {n : ℕ} (hn : 0 < n)
    {u : E n → ℝ} (hu : ContDiffOn ℝ 2 u (closedUnitBall n))
    (huS : ContDiffOn ℝ ∞ u (unitBall n))
    (hu0 : ∀ x ∈ unitSphere n, u x = 0) :
    (∫ x in unitBall n, ‖fderivWithin ℝ u (closedUnitBall n) x‖ ^ 2 ∂volume0 n) ≤
      4 * ∫ x in unitBall n, ‖dirichletWithinRealHessian u x‖ ^ 2 ∂volume0 n := by
  obtain ⟨v, hv, _, hD, hH⟩ := exists_dirichlet_zeroBoundary_smooth_C2_approximation hu huS hu0
  have hU : UniqueDiffOn ℝ (closedUnitBall n) :=
    uniqueDiffOn_convex (convex_closedBall (0 : E n) 1)
      ⟨0, mem_interior_iff_mem_nhds.mpr (closedBall_mem_nhds _ (by norm_num))⟩
  have hDC := (hu.fderivWithin (m := 1) hU (by norm_num)).continuousOn
  have hHC := continuousOn_dirichletWithinRealHessian hu
  have hNormD : Continuous (fun L : E n →L[ℝ] ℝ => ‖L‖ ^ 2) := continuous_norm.pow 2
  have hNormH : Continuous (fun H : E n →L[ℝ] E n →L[ℝ] ℝ => ‖H‖ ^ 2) := continuous_norm.pow 2
  have hDL := dirichlet_uniform_limit_comp_continuous (isCompact_closedBall _ _) hDC hD hNormD
  have hHL := dirichlet_uniform_limit_comp_continuous (isCompact_closedBall _ _) hHC hH hNormH
  have hDCv (j : ℕ) : ContinuousOn (fderiv ℝ (v j)) (closedUnitBall n) := by
    intro x hx
    exact (((hv j).1.contDiffAt hx).fderiv_right (m := ∞) (by simp)).continuousAt.continuousWithinAt
  have hHCv (j : ℕ) : ContinuousOn (realHessian (v j)) (closedUnitBall n) := by
    intro x hx
    exact (realHessian_contDiffAt ((hv j).1.contDiffAt hx)).continuousAt.continuousWithinAt
  have hDI := tendsto_integral_dirichlet_uniform_limit hn (hNormD.comp_continuousOn hDC)
    (fun j => hNormD.comp_continuousOn (hDCv j)) hDL
  have hHI := tendsto_integral_dirichlet_uniform_limit hn (hNormH.comp_continuousOn hHC)
    (fun j => hNormH.comp_continuousOn (hHCv j)) hHL
  exact le_of_tendsto_of_tendsto hDI (hHI.const_mul 4) (Eventually.of_forall (fun j =>
    integral_fderiv_sq_le_four_realHessian_sq_of_smoothNear hn (hv j).1 (hv j).2))

end KEBall
