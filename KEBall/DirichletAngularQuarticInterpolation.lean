import KEBall.DirichletAngularIntegrationByParts

/-!
# A boundary-free angular L4 interpolation estimate

The vector field is tangent to the sphere, so no boundary condition on
the scalar field is needed.  The estimate is obtained from the actual
angular integration-by-parts identity, followed by a pointwise square.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Filter MeasureTheory Metric Set
open scoped ContDiff Topology

namespace KEBall

theorem integral_pow_four_le_of_dirichlet_angular_chain {n : ℕ} (hn : 0 < n)
    {U : Set (E n)} (hU : IsOpen U) (hSub : closedUnitBall n ⊆ U)
    {f g h : E n → ℝ} (hf : ContDiffOn ℝ 1 f U) (hg : ContDiffOn ℝ 1 g U)
    (hh : ContinuousOn h U) (T : E n →L[ℝ] E n) (hT : star T = -T)
    (hDf : ∀ x ∈ unitBall n, fderiv ℝ f x (T x) = g x)
    (hDg : ∀ x ∈ unitBall n, fderiv ℝ g x (T x) = h x)
    {B : ℝ} (hB : 0 ≤ B) (hF : ∀ x ∈ unitBall n, |f x| ≤ B) :
    (∫ x in unitBall n, (g x) ^ 4 ∂volume0 n) ≤
      9 * B ^ 2 * ∫ x in unitBall n, (h x) ^ 2 ∂volume0 n := by
  let μ := (volume0 n).restrict (unitBall n)
  have hInt {a : E n → ℝ} (ha : ContinuousOn a U) : Integrable a μ :=
    ((ha.mono hSub).integrableOn_compact (isCompact_closedBall (0 : E n) 1)).mono_set
      ball_subset_closedBall
  have hPow (x : E n) (hx : x ∈ unitBall n) :
      fderiv ℝ (fun y => (g y) ^ 3) x (T x) = 3 * (g x) ^ 2 * h x := by
    have hgD := (hg.contDiffAt (hU.mem_nhds (hSub (ball_subset_closedBall hx)))).differentiableAt
      (by norm_num)
    change fderiv ℝ (g ^ 3) x (T x) = _
    rw [fderiv_pow 3 hgD]
    simp only [smul_apply, smul_eq_mul, hDg x hx]
    norm_num
  have hI : (∫ x, (g x) ^ 4 ∂μ) = ∫ x, -3 * f x * (g x) ^ 2 * h x ∂μ := by
    calc
      _ = ∫ x, fderiv ℝ f x (T x) * (g x) ^ 3 ∂μ := by
        apply setIntegral_congr_fun measurableSet_ball
        intro x hx
        change (g x) ^ 4 = fderiv ℝ f x (T x) * (g x) ^ 3
        rw [hDf x hx]
        ring
      _ = -(∫ x, f x * fderiv ℝ (fun y => (g y) ^ 3) x (T x) ∂μ) :=
        integral_dirichlet_skew_derivative_mul hn hU hSub hf (hg.pow 3) T hT
      _ = _ := by
        rw [← integral_neg]
        apply setIntegral_congr_fun measurableSet_ball
        intro x hx
        change -(f x * fderiv ℝ (fun y => (g y) ^ 3) x (T x)) =
          -3 * f x * (g x) ^ 2 * h x
        rw [hPow x hx]
        ring
  have hPoint (x : E n) (hx : x ∈ unitBall n) :
      -3 * f x * (g x) ^ 2 * h x ≤
        (1 / 2 : ℝ) * (g x) ^ 4 + (9 / 2 * B ^ 2) * (h x) ^ 2 := by
    have hfSq : (f x) ^ 2 ≤ B ^ 2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (f x)) (hF x hx) 2
    have hProduct := mul_le_mul_of_nonneg_right hfSq (sq_nonneg (h x))
    have hSquare := sq_nonneg ((g x) ^ 2 + 3 * f x * h x)
    nlinarith only [hProduct, hSquare]
  have hI₁ := hInt (hf.continuousOn.const_mul (-3) |>.mul (hg.continuousOn.pow 2) |>.mul hh)
  have hI₂ := hInt ((hg.continuousOn.pow 4).const_mul (1 / 2 : ℝ))
  have hI₃ := hInt ((hh.pow 2).const_mul (9 / 2 * B ^ 2))
  have hBound := integral_mono_ae hI₁ (hI₂.add hI₃)
    ((ae_restrict_mem (μ := volume0 n)
      (show MeasurableSet (unitBall n) from measurableSet_ball)).mono hPoint)
  change (∫ x, -3 * f x * (g x) ^ 2 * h x ∂μ) ≤
    ∫ x, (1 / 2 : ℝ) * (g x) ^ 4 + (9 / 2 * B ^ 2) * (h x) ^ 2 ∂μ at hBound
  change Integrable (fun x => (1 / 2 : ℝ) * (g x) ^ 4) μ at hI₂
  change Integrable (fun x => (9 / 2 * B ^ 2) * (h x) ^ 2) μ at hI₃
  rw [← hI, integral_add hI₂ hI₃, integral_const_mul, integral_const_mul] at hBound
  linarith only [hBound]

theorem integral_dirichlet_angular_derivative_pow_four_le {n : ℕ} (hn : 0 < n)
    {U : Set (E n)} (hU : IsOpen U) (hSub : closedUnitBall n ⊆ U)
    {f : E n → ℝ} (hf : ContDiffOn ℝ 2 f U)
    (T : E n →L[ℝ] E n) (hT : star T = -T)
    {B : ℝ} (hB : 0 ≤ B) (hF : ∀ x ∈ unitBall n, |f x| ≤ B) :
    (∫ x in unitBall n, (fderiv ℝ f x (T x)) ^ 4 ∂volume0 n) ≤
      9 * B ^ 2 * ∫ x in unitBall n,
        (fderiv ℝ (fun y => fderiv ℝ f y (T y)) x (T x)) ^ 2 ∂volume0 n := by
  let g (x : E n) := fderiv ℝ f x (T x)
  have hg : ContDiffOn ℝ 1 g U :=
    (hf.fderiv_of_isOpen hU (by norm_num)).clm_apply T.contDiff.contDiffOn
  exact integral_pow_four_le_of_dirichlet_angular_chain hn hU hSub (hf.of_le (by norm_num))
    hg ((hg.continuousOn_fderiv_of_isOpen hU (by norm_num)).clm_apply
      T.continuous.continuousOn) T hT (fun _ _ => rfl) (fun _ _ => rfl) hB hF

end KEBall
