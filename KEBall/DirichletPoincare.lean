import KEBall.EulerFlux

/-! The Dirichlet Poincaré inequality on the real model ball. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Metric Set
open scoped ContDiff

namespace KEBall

/-- Poincaré's inequality on the real model ball for a smooth potential
with zero boundary trace. The radial divergence identity gives the explicit
constant independently of the coefficients of the Dirichlet operator. -/
theorem dirichlet_poincare_sq {n : ℕ} (hn : 0 < n) {u : E n → ℝ}
    (hu : SmoothNear (closedUnitBall n) u) (hu0 : ∀ x ∈ unitSphere n, u x = 0) :
    (n : ℝ) ^ 2 * (∫ x in unitBall n, (u x) ^ 2 ∂volume0 n) ≤
      ∫ x in unitBall n, ‖fderiv ℝ u x‖ ^ 2 ∂volume0 n := by
  obtain ⟨U, hU, hKU, huU⟩ := hu
  let V : E n → E n := fun x => (u x) ^ 2 • x
  let q : E n → ℝ := fun x => (u x) ^ 2
  let r : E n → ℝ := fun x => 2 * u x * fderiv ℝ u x x
  let g : E n → ℝ := fun x => ‖fderiv ℝ u x‖ ^ 2
  let d : E n → ℝ := fun x => (2 * n : ℝ) * q x + r x
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hV : ContDiffOn ℝ 1 V U :=
    ((huU.pow 2).smul contDiffOn_id).of_le (by simp)
  have hDiv (x : E n) (hx : x ∈ unitBall n) : euclideanDivergence V x = d x := by
    have huAt := huU.contDiffAt (hU.mem_nhds (hKU (ball_subset_closedBall hx)))
    have huD := huAt.differentiableAt (by simp)
    change euclideanDivergence (fun y => q y • y) x = _
    rw [euclideanDivergence_scalar_euler (show DifferentiableAt ℝ q x from huD.pow 2),
      show fderiv ℝ q x = _ from fderiv_pow 2 huD]
    simp [d, q, r]
  have hFlux (θ : Sphere n) : inner ℝ θ.1 (V θ.1) = 0 := by
    simp [V, hu0 θ.1 θ.2]
  have hD0 : (∫ x in unitBall n, d x ∂volume0 n) = 0 := by
    rw [← setIntegral_congr_fun (show MeasurableSet (unitBall n) from measurableSet_ball) hDiv,
      integral_unitBall_divergence_normalized_of_contDiffOn hn hU hKU hV]
    simp only [hFlux, integral_zero, mul_zero]
  have hInt (f : E n → ℝ) (hf : ContinuousOn f (closedUnitBall n)) :
      IntegrableOn f (unitBall n) (volume0 n) :=
    hf.integrableOn_of_subset_isCompact (isCompact_closedBall _ _) measurableSet_ball
      ball_subset_closedBall (by rw [volume0_unitBall n hn]; exact ENNReal.one_ne_top)
  have hdu := (huU.fderiv_of_isOpen hU (by simp) (m := 0)).continuousOn
  have hq : ContinuousOn q (closedUnitBall n) := (huU.continuousOn.pow 2).mono hKU
  have hr : ContinuousOn r (closedUnitBall n) :=
    ((continuousOn_const.mul huU.continuousOn).mul (hdu.clm_apply continuousOn_id)).mono hKU
  have hg : ContinuousOn g (closedUnitBall n) := (hdu.norm.pow 2).mono hKU
  have hd : ContinuousOn d (closedUnitBall n) := (continuousOn_const.mul hq).add hr
  have hPoint (x : E n) (hx : x ∈ unitBall n) : (n : ℝ) ^ 2 * q x ≤ (n : ℝ) * d x + g x := by
    have hNorm := (mem_ball_zero_iff.mp hx).le
    have hDer := (fderiv ℝ u x).le_opNorm x
    rw [Real.norm_eq_abs] at hDer
    have hD : |fderiv ℝ u x x| ≤ ‖fderiv ℝ u x‖ :=
      hDer.trans (mul_le_of_le_one_right (norm_nonneg _) hNorm)
    have hAbs : |u x * fderiv ℝ u x x| ≤ |u x| * ‖fderiv ℝ u x‖ := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hD (abs_nonneg _)
    have hDown : -(|u x| * ‖fderiv ℝ u x‖) ≤ u x * fderiv ℝ u x x :=
      (neg_le_neg hAbs).trans (neg_abs_le _)
    have hYoung := sq_nonneg ((n : ℝ) * |u x| - ‖fderiv ℝ u x‖)
    have hCross := mul_le_mul_of_nonneg_left hDown (show 0 ≤ 2 * (n : ℝ) by positivity)
    dsimp [d, q, r, g]
    nlinarith only [hYoung, hCross, sq_abs (u x)]
  have hI := setIntegral_mono_on ((hInt q hq).const_mul ((n : ℝ) ^ 2))
    (((hInt d hd).const_mul (n : ℝ)).add (hInt g hg)) measurableSet_ball hPoint
  change (∫ x in unitBall n, (n : ℝ) ^ 2 * q x ∂volume0 n) ≤
    ∫ x in unitBall n, (n : ℝ) * d x + g x ∂volume0 n at hI
  rw [integral_const_mul, integral_add ((hInt d hd).const_mul _) (hInt g hg),
    integral_const_mul, hD0, mul_zero, zero_add] at hI
  exact hI

end KEBall
