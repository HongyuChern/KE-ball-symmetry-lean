import PshLines.Regularization.HolomorphicPullback
import PshLines.TranslationPairing

/-!
# Scaling and support of the Hessian of the radial regularization kernel
-/

set_option autoImplicit false

open Filter MeasureTheory Metric Set
open scoped ContDiff Topology

namespace KEBall.BedfordTaylor

open PshLines
open PshLines.FirstPass (ComplexModel)
open PshLines.Regularization.HolomorphicPullback

variable {n : ℕ}

theorem tsupport_realHessian_subset {f : ComplexModel n → ℝ} (hf : ContDiff ℝ 2 f)
    (v w : ComplexModel n) :
    tsupport (fun x => PshLines.realHessian f x v w) ⊆ tsupport f := by
  simpa only [fderiv_fderiv_apply_eq_realHessian hf] using
    (tsupport_fderiv_apply_subset ℝ (f := fun x => fderiv ℝ f x w) v).trans
      (tsupport_fderiv_apply_subset ℝ w)

theorem realHessian_explicitRadialKernel_scale (R : ℝ) (hR : 0 < R) (j : ℕ)
    (x v w : ComplexModel n) :
    PshLines.realHessian (explicitRadialKernel R hR j) x v w =
      ((j : ℝ) + 1) ^ Module.finrank ℝ (ComplexModel n) * ((j : ℝ) + 1) ^ 2 *
        PshLines.realHessian (explicitRadialKernel R hR 0) (((j : ℝ) + 1) • x) v w := by
  let q := (j : ℝ) + 1
  let d := Module.finrank ℝ (ComplexModel n)
  let k : ComplexModel n → ℝ := explicitRadialKernel R hR 0
  let B : ComplexModel n →L[ℝ] ComplexModel n := q • ContinuousLinearMap.id ℝ (ComplexModel n)
  have hk : ContDiff ℝ 2 k := (explicitRadialKernel_contDiff R hR 0).of_le
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hB (y : ComplexModel n) : B y = q • y := rfl
  have he : explicitRadialKernel R hR j = q ^ d • (fun y => k (0 + B y)) := by
    funext y
    simpa only [Pi.smul_apply, smul_eq_mul, hB, zero_add, q, d, k, Nat.cast_zero, div_one] using
      explicitRadialKernel_scale R hR 0 j y
  have hcont : ContDiff ℝ 2 (fun y => k (0 + B y)) :=
    hk.comp (contDiff_const.add B.contDiff)
  rw [he, PshLines.realHessian_smul hcont.contDiffAt,
    PshLines.realHessian_comp_affine hk B 0 x v w, zero_add, hB x, hB v, hB w,
    PshLines.realHessian_smul_left, PshLines.realHessian_smul_right]
  change q ^ d * (q * (q * _)) = q ^ d * q ^ 2 * _
  ring

/-- The L¹ norm of the kernel Hessian scales quadratically in the inverse
radius. -/
theorem integral_abs_realHessian_explicitRadialKernel (R : ℝ) (hR : 0 < R) (j : ℕ)
    (v w : ComplexModel n) :
    (∫ x, |PshLines.realHessian (explicitRadialKernel R hR j) x v w|) =
      ((j : ℝ) + 1) ^ 2 * ∫ x, |PshLines.realHessian (explicitRadialKernel R hR 0) x v w| := by
  let q := (j : ℝ) + 1
  let d := Module.finrank ℝ (ComplexModel n)
  let f (x : ComplexModel n) := |PshLines.realHessian (explicitRadialKernel R hR 0) x v w|
  have hq : 0 < q := by dsimp only [q]; positivity
  have h := Measure.integral_comp_smul_of_nonneg volume f q (hR := hq.le)
  have hi : (∫ x, f (q • x)) = (q ^ d)⁻¹ * ∫ x, f x := by
    simpa only [d, smul_eq_mul] using h
  have he (x : ComplexModel n) : |PshLines.realHessian (explicitRadialKernel R hR j) x v w| =
      q ^ d * q ^ 2 * f (q • x) := by
    rw [realHessian_explicitRadialKernel_scale R hR j]
    change |q ^ d * q ^ 2 * PshLines.realHessian (explicitRadialKernel R hR 0) (q • x) v w| = _
    simp only [abs_mul, abs_of_nonneg (pow_nonneg hq.le d), abs_of_nonneg (pow_nonneg hq.le 2), f]
  calc
    _ = ∫ x, q ^ d * q ^ 2 * f (q • x) := integral_congr_ae (Eventually.of_forall he)
    _ = _ := by
      rw [integral_const_mul, hi]
      change q ^ d * q ^ 2 * ((q ^ d)⁻¹ * ∫ x, f x) = q ^ 2 * ∫ x, f x
      field_simp [hq.ne']

/-- A remainder that is little-o of the squared displacement contributes
zero to the limit of the Hessian of the radial convolutions at the center. -/
theorem tendsto_realHessian_radialPairing_zero_of_quadratic_remainder
    (R : ℝ) (hR : 0 < R) {g : ComplexModel n → ℝ} (hg : LocallyIntegrable g volume)
    {x : ComplexModel n}
    (hrem : ∀ ε : ℝ, 0 < ε → ∀ᶠ h in 𝓝 (0 : ComplexModel n), |g (x + h)| ≤ ε * ‖h‖ ^ 2)
    (v w : ComplexModel n) :
    Tendsto (fun j : ℕ => PshLines.realHessian (translationPairing volume g
      (explicitRadialKernel R hR j)) x v w) atTop (𝓝 0) := by
  let k (j : ℕ) (y : ComplexModel n) := PshLines.realHessian (explicitRadialKernel R hR j) y v w
  let M := ∫ y, |k 0 y|
  have hM : 0 ≤ M := integral_nonneg fun _ => abs_nonneg _
  have hscale (j : ℕ) : (∫ y, |k j y|) = ((j : ℝ) + 1) ^ 2 * M :=
    integral_abs_realHessian_explicitRadialKernel R hR j v w
  let radius (j : ℕ) := R / ((j : ℝ) + 1)
  have hrLim : Tendsto radius atTop (𝓝 0) :=
    (tendsto_atTop_add_const_right atTop (1 : ℝ)
      (tendsto_natCast_atTop_atTop (R := ℝ))).const_div_atTop R
  have hκ (j : ℕ) : ContDiff ℝ 2 (explicitRadialKernel (n := n) R hR j) :=
    (explicitRadialKernel_contDiff R hR j).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hsup (j : ℕ) : tsupport (k j) ⊆ closedBall 0 (radius j) := by
    have h := tsupport_realHessian_subset (hκ j) v w
    rw [explicitRadialKernel_tsupport] at h
    exact h
  have hkInt (j : ℕ) : Integrable (fun y => |k j y|) volume := by
    have hC : Continuous (k j) := continuous_realHessian (hκ j) v w
    have hS : HasCompactSupport (k j) :=
      (isCompact_closedBall (0 : ComplexModel n) (radius j)).of_isClosed_subset (isClosed_tsupport _) (hsup j)
    exact (hC.integrable_of_hasCompactSupport hS).abs
  rw [Metric.tendsto_nhds]
  intro ε hε
  let c := ε / (1 + R ^ 2 * M)
  have hD : 0 < 1 + R ^ 2 * M := by positivity
  have hc : 0 < c := div_pos hε hD
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hrem c hc)
  filter_upwards [hrLim.eventually_lt_const hr] with j hj
  have hInt : Integrable (fun y => g y * k j (y - x)) volume :=
    integrable_translationPairing_realHessian hg (explicitRadialKernel_hasCompactSupport R hR j) (hκ j) x v w
  have hkShift : Integrable (fun y => |k j (y - x)|) volume := by
    simpa only [sub_eq_add_neg] using (hkInt j).comp_add_right (-x)
  have hle (y : ComplexModel n) :
      |g y * k j (y - x)| ≤ (c * radius j ^ 2) * |k j (y - x)| := by
    rw [abs_mul]
    by_cases hy : k j (y - x) = 0
    · simp only [hy, abs_zero, mul_zero, le_refl]
    have hnorm : ‖y - x‖ ≤ radius j := by
      have hmem := hsup j (subset_tsupport (k j) hy)
      simpa only [mem_closedBall, dist_zero_right] using hmem
    have hnear : y - x ∈ ball (0 : ComplexModel n) r := by
      simpa only [mem_ball, dist_zero_right] using hnorm.trans_lt hj
    have hh : |g y| ≤ c * ‖y - x‖ ^ 2 := by
      have he : |g (x + (y - x))| ≤ c * ‖y - x‖ ^ 2 := hball hnear
      rwa [show x + (y - x) = y by abel] at he
    exact mul_le_mul_of_nonneg_right
      (hh.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hnorm 2) hc.le))
      (abs_nonneg _)
  have hShift : (∫ y, |k j (y - x)|) = ∫ y, |k j y| := by
    simpa only [sub_eq_add_neg] using integral_add_right_eq_self (fun y => |k j y|) (-x)
  rw [Real.dist_eq, sub_zero, PshLines.realHessian_translationPairing hg
    (explicitRadialKernel_hasCompactSupport R hR j) (hκ j)]
  change |∫ y, g y * k j (y - x)| < ε
  calc
    _ ≤ ∫ y, |g y * k j (y - x)| := by
      simpa only [Real.norm_eq_abs] using (norm_integral_le_integral_norm
        (f := fun y => g y * k j (y - x)) (μ := volume))
    _ ≤ ∫ y, (c * radius j ^ 2) * |k j (y - x)| :=
      integral_mono hInt.abs (hkShift.const_mul _) hle
    _ = c * (R ^ 2 * M) := by
      rw [integral_const_mul, hShift, hscale]
      dsimp only [radius]
      field_simp [show ((j : ℝ) + 1) ≠ 0 by positivity]
    _ < ε := by
      dsimp only [c]
      rw [div_mul_eq_mul_div]
      exact (div_lt_iff₀ hD).mpr (by linarith only [hε])

end KEBall.BedfordTaylor
