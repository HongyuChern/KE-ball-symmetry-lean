import KEBall.CegrellQuadratic
import KEBall.BedfordTaylorCommonRegularization

/-!
# Radial mollification of the quadratic boundary barrier
-/

set_option autoImplicit false

open Filter MeasureTheory Metric Set
open scoped ContDiff RealInnerProductSpace Topology

namespace KEBall.Cegrell

open PshLines
open PshLines.FirstPass
open PshLines.Regularization.HolomorphicPullback

variable {n : ℕ}

/-- The constant added to the quadratic by radial averaging. -/
noncomputable def radialKernelSecondMoment (n : ℕ) (R : ℝ) (hR : 0 < R) (j : ℕ) : ℝ :=
  ∫ y : ComplexModel n, ‖y‖ ^ 2 * explicitRadialKernel R hR j y

theorem radialKernelSecondMoment_tendsto (n : ℕ) {R : ℝ} (hR : 0 < R) :
    Tendsto (radialKernelSecondMoment n R hR) atTop (𝓝 0) := by
  have hnonneg (j : ℕ) : 0 ≤ radialKernelSecondMoment n R hR j :=
    integral_nonneg fun y => mul_nonneg (sq_nonneg _) (explicitRadialKernel_nonneg R hR j y)
  let r (j : ℕ) := (shrinkingBump (E := ComplexModel n) R hR j).rOut
  have hle (j : ℕ) : radialKernelSecondMoment n R hR j ≤ r j ^ 2 := by
    let k := explicitRadialKernel (n := n) R hR j
    have hk := integrable_of_integral_eq_one (explicitRadialKernel_integral_one (n := n) R hR j)
    have hi : Integrable (fun y : ComplexModel n => ‖y‖ ^ 2 * k y) volume :=
      ((continuous_norm.pow 2).mul (explicitRadialKernel_contDiff R hR j).continuous).integrable_of_hasCompactSupport
        (explicitRadialKernel_hasCompactSupport R hR j).mul_left
    calc
      _ ≤ ∫ y, r j ^ 2 * k y := by
        apply integral_mono hi (hk.const_mul _)
        intro y
        by_cases hy : y ∈ tsupport k
        · rw [show tsupport k = closedBall (0 : ComplexModel n) (r j) from
            explicitRadialKernel_tsupport R hR j] at hy
          exact mul_le_mul_of_nonneg_right
            (pow_le_pow_left₀ (norm_nonneg _) (mem_closedBall_zero_iff.mp hy) _)
            (explicitRadialKernel_nonneg R hR j y)
        · change ‖y‖ ^ 2 * k y ≤ r j ^ 2 * k y
          rw [image_eq_zero_of_notMem_tsupport hy, mul_zero, mul_zero]
      _ = _ := by rw [integral_const_mul, explicitRadialKernel_integral_one, mul_one]
  refine tendsto_const_nhds.squeeze ?_ hnonneg hle
  simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using
    (tendsto_shrinkingBump_rOut (E := ComplexModel n) R hR).pow 2

/-- Radial averaging preserves a quadratic pulled back by a continuous
real linear map up to a constant independent of the evaluation point. -/
theorem translationPairing_pullbackQuadratic
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (L : ComplexModel n →L[ℝ] V) (c d : ℝ) {R : ℝ} (hR : 0 < R)
    (j : ℕ) (x : ComplexModel n) :
    translationPairing volume (fun y => c * (‖L y‖ ^ 2 - d))
      (explicitRadialKernel R hR j) x =
      c * (‖L x‖ ^ 2 - d + ∫ y, ‖L y‖ ^ 2 * explicitRadialKernel R hR j y) := by
  let k := explicitRadialKernel (n := n) R hR j
  have hk : Integrable k volume := integrable_of_integral_eq_one (explicitRadialKernel_integral_one R hR j)
  have hkS : HasCompactSupport k := explicitRadialKernel_hasCompactSupport R hR j
  have hkC : Continuous k := (explicitRadialKernel_contDiff R hR j).continuous
  let F (y : ComplexModel n) := (‖L (y + x)‖ ^ 2 - d) * k y
  let G (y : ComplexModel n) := (2 * inner ℝ (L y) (L x)) * k y
  have hGI : Integrable G volume :=
    ((continuous_const.mul (L.continuous.inner continuous_const)).mul hkC).integrable_of_hasCompactSupport
      hkS.mul_left
  have hNorm : Integrable (fun y : ComplexModel n => ‖L y‖ ^ 2 * k y) volume :=
    ((L.continuous.norm.pow 2).mul hkC).integrable_of_hasCompactSupport hkS.mul_left
  have hOdd (y : ComplexModel n) : G (-y) = -G y := by
    dsimp [G]
    rw [show k (-y) = k y from explicitRadialKernel_neg R hR j y, map_neg, inner_neg_left]
    ring
  have hzero : (∫ y, G y) = 0 := by
    have he : (∫ y, G (-y)) = ∫ y, G y := integral_neg_eq_self G volume
    simp_rw [hOdd, integral_neg] at he
    linarith
  have hF : (∫ y, F y) = (‖L x‖ ^ 2 - d) + (∫ y, ‖L y‖ ^ 2 * k y) := by
    have he (y : ComplexModel n) :
        F y = ((‖L x‖ ^ 2 - d) * k y + ‖L y‖ ^ 2 * k y) + G y := by
      dsimp [F, G]
      rw [map_add, norm_add_sq_real]
      ring
    simp_rw [he]
    have hi : Integrable (fun y : ComplexModel n => (‖L x‖ ^ 2 - d) * k y + ‖L y‖ ^ 2 * k y) volume :=
      (hk.const_mul ((‖L x‖ ^ 2 - d))).add hNorm
    rw [integral_add hi hGI, integral_add (hk.const_mul ((‖L x‖ ^ 2 - d))) hNorm,
      integral_const_mul, hzero, add_zero]
    change (‖L x‖ ^ 2 - d) * (∫ y, explicitRadialKernel R hR j y) +
      (∫ y, ‖L y‖ ^ 2 * k y) = _
    rw [explicitRadialKernel_integral_one, mul_one]
  simp only [translationPairing, mul_assoc]
  rw [integral_const_mul, ← hF]
  congr 1
  have hTrans : (∫ y, F (y + -x)) = ∫ y, F y := integral_add_right_eq_self F (-x)
  simpa only [F, k, ← sub_eq_add_neg, sub_add_cancel] using hTrans

/-- The quadratic defining function is preserved by the radial mollifier
up to a constant independent of the evaluation point. -/
theorem translationPairing_ballQuadratic (c : ℝ) {R : ℝ} (hR : 0 < R)
    (j : ℕ) (x : ComplexModel n) :
    translationPairing volume (fun y => c * ballQuadratic n y)
      (explicitRadialKernel R hR j) x =
      c * (ballQuadratic n x + radialKernelSecondMoment n R hR j) := by
  exact translationPairing_pullbackQuadratic (ContinuousLinearMap.id ℝ (ComplexModel n)) c 1 hR j x

end KEBall.Cegrell
