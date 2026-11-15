import KEBall.BedfordTaylorRadialKernelHessian

/-!
# Transferring the Hessian to a compactly supported smooth density
-/

set_option autoImplicit false

open Filter MeasureTheory Metric Set
open scoped ContDiff Convolution Topology

namespace KEBall.BedfordTaylor

open PshLines
open PshLines.FirstPass (ComplexModel)
open PshLines.Regularization.HolomorphicPullback

variable {n : ℕ}

private theorem fderiv_translationPairing_compactDensity
    {u k : ComplexModel n → ℝ} (hu : ContDiff ℝ 1 u) (hU : HasCompactSupport u)
    (hk : Continuous k) (hK : HasCompactSupport k) (x v : ComplexModel n) :
    fderiv ℝ (translationPairing volume u k) x v =
      translationPairing volume (fun y => fderiv ℝ u y v) k x := by
  let g (y : ComplexModel n) := k (-y)
  have hg : LocallyIntegrable g volume :=
    ((hk.comp continuous_neg).integrable_of_hasCompactSupport (hK.comp_homeomorph (Homeomorph.neg _))).locallyIntegrable
  let L := ContinuousLinearMap.mul ℝ ℝ
  have hEq : translationPairing volume u k = g ⋆[L.flip, volume] u := by
    rw [translationPairing_eq_convolution]
    exact (convolution_flip L).symm
  rw [hEq, (hU.hasFDerivAt_convolution_right L.flip hg hu x).fderiv,
    convolution_precompR_apply L.flip hg (hU.fderiv ℝ) (hu.continuous_fderiv one_ne_zero)]
  rw [convolution_flip L, translationPairing_eq_convolution]

/-- If the density is smooth with compact support, differentiating the
translation pairing twice can act on the density. -/
theorem realHessian_translationPairing_compactDensity
    {u k : ComplexModel n → ℝ} (hu : ContDiff ℝ 2 u) (hU : HasCompactSupport u)
    (hk : ContDiff ℝ 2 k) (hK : HasCompactSupport k) (x v w : ComplexModel n) :
    PshLines.realHessian (translationPairing volume u k) x v w =
      translationPairing volume (fun y => PshLines.realHessian u y v w) k x := by
  have hPair : ContDiff ℝ 2 (translationPairing volume u k) :=
    contDiff_translationPairing (hu.continuous.integrable_of_hasCompactSupport hU).locallyIntegrable hK hk
  rw [← fderiv_fderiv_apply_eq_realHessian hPair]
  have he : (fun y => fderiv ℝ (translationPairing volume u k) y w) =
      translationPairing volume (fun y => fderiv ℝ u y w) k :=
    funext fun y => fderiv_translationPairing_compactDensity (hu.of_le (by norm_num)) hU hk.continuous hK y w
  rw [he, fderiv_translationPairing_compactDensity (contDiff_fderiv_apply_of_two hu w)
    (hU.fderiv_apply ℝ w) hk.continuous hK]
  simp only [fderiv_fderiv_apply_eq_realHessian hu]

/-- The Hessian of a smooth compact density with constant Hessian near the
center is unchanged there by sufficiently narrow radial convolution. -/
theorem eventually_realHessian_radialPairing_eq_of_eventually_constant
    (R : ℝ) (hR : 0 < R) {u : ComplexModel n → ℝ} (hu : ContDiff ℝ 2 u)
    (hU : HasCompactSupport u) {x v w : ComplexModel n} {A : ℝ}
    (hA : ∀ᶠ y in 𝓝 x, PshLines.realHessian u y v w = A) :
    ∀ᶠ j : ℕ in atTop, PshLines.realHessian (translationPairing volume u
      (explicitRadialKernel R hR j)) x v w = A := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hA
  let radius (j : ℕ) := R / ((j : ℝ) + 1)
  have hrLim : Tendsto radius atTop (𝓝 0) :=
    (tendsto_atTop_add_const_right atTop (1 : ℝ)
      (tendsto_natCast_atTop_atTop (R := ℝ))).const_div_atTop R
  filter_upwards [hrLim.eventually_lt_const hr] with j hj
  let k : ComplexModel n → ℝ := explicitRadialKernel R hR j
  have hK : HasCompactSupport k := explicitRadialKernel_hasCompactSupport R hR j
  have hk : ContDiff ℝ 2 k := (explicitRadialKernel_contDiff R hR j).of_le
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hmass : (∫ y, k (y - x)) = 1 := by
    have h := integral_add_right_eq_self k (-x) (μ := (volume : Measure (ComplexModel n)))
    rw [show (∫ y, k y) = 1 from explicitRadialKernel_integral_one R hR j] at h
    simpa only [sub_eq_add_neg] using h
  change PshLines.realHessian (translationPairing volume u k) x v w = A
  rw [realHessian_translationPairing_compactDensity hu hU hk hK, translationPairing]
  calc
    _ = ∫ y, A * k (y - x) := by
      apply integral_congr_ae
      apply Eventually.of_forall
      intro y
      by_cases hy : k (y - x) = 0
      · simp only [hy, mul_zero]
      have hs := subset_tsupport k hy
      change y - x ∈ tsupport (explicitRadialKernel R hR j) at hs
      rw [explicitRadialKernel_tsupport, mem_closedBall, dist_zero_right] at hs
      have hy' : y ∈ ball x r := by
        rw [mem_ball, dist_eq_norm]
        exact hs.trans_lt hj
      have he : PshLines.realHessian u y v w = A := hball hy'
      change PshLines.realHessian u y v w * k (y - x) = A * k (y - x)
      rw [he]
    _ = A := by rw [integral_const_mul, hmass, mul_one]

/-- If the density agrees to second order at the center with a smooth
compactly supported model, its convolutions recover the model Hessian. -/
theorem tendsto_realHessian_radialPairing_of_quadratic_model
    (R : ℝ) (hR : 0 < R) {g q : ComplexModel n → ℝ} (hg : LocallyIntegrable g volume)
    (hq : ContDiff ℝ 2 q) (hQ : HasCompactSupport q)
    {x v w : ComplexModel n} {A : ℝ}
    (hrem : ∀ ε : ℝ, 0 < ε → ∀ᶠ h in 𝓝 (0 : ComplexModel n),
      |g (x + h) - q (x + h)| ≤ ε * ‖h‖ ^ 2)
    (hA : ∀ᶠ y in 𝓝 x, PshLines.realHessian q y v w = A) :
    Tendsto (fun j : ℕ => PshLines.realHessian (translationPairing volume g
      (explicitRadialKernel R hR j)) x v w) atTop (𝓝 A) := by
  let k (j : ℕ) : ComplexModel n → ℝ := explicitRadialKernel R hR j
  let H (a : ComplexModel n → ℝ) (j : ℕ) := PshLines.realHessian (translationPairing volume a (k j)) x v w
  have hqL : LocallyIntegrable q volume :=
    (hq.continuous.integrable_of_hasCompactSupport hQ).locallyIntegrable
  have hDiff : Tendsto (H (g - q)) atTop (𝓝 0) :=
    tendsto_realHessian_radialPairing_zero_of_quadratic_remainder R hR (hg.sub hqL) hrem v w
  have hModel : Tendsto (H q) atTop (𝓝 A) := by
    have hconst : Tendsto (fun _ : ℕ => A) atTop (𝓝 A) := tendsto_const_nhds
    have heq : H q =ᶠ[atTop] (fun _ => A) :=
      eventually_realHessian_radialPairing_eq_of_eventually_constant R hR hq hQ hA
    exact hconst.congr' heq.symm
  have he (j : ℕ) : H (g - q) j = H g j - H q j := by
    have hks : HasCompactSupport (k j) := explicitRadialKernel_hasCompactSupport R hR j
    have hkc : ContDiff ℝ 2 (k j) := (explicitRadialKernel_contDiff R hR j).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
    simp only [H, PshLines.realHessian_translationPairing (hg.sub hqL) hks hkc,
      PshLines.realHessian_translationPairing hg hks hkc, PshLines.realHessian_translationPairing hqL hks hkc,
      Pi.sub_apply, sub_mul]
    exact integral_sub (integrable_translationPairing_realHessian hg hks hkc x v w)
      (integrable_translationPairing_realHessian hqL hks hkc x v w)
  have h := hDiff.add hModel
  rw [zero_add] at h
  exact h.congr fun j => calc
    H (g - q) j + H q j = H g j := by rw [he, sub_add_cancel]
    _ = _ := rfl

end KEBall.BedfordTaylor
