import KEBall.BallCutoff
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.PeakFunction

/-!
# The actual derivative kernel concentrating on the unit sphere

The cutoff is differentiated in the radial coordinate. Its negative derivative
has mass one on `[0,2]`, is nonnegative there, and concentrates at radius one.
The limit below is an ordinary Lebesgue integral theorem for this specified
kernel, suitable for applying to the spherical average of a boundary flux.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter Metric
open scoped ContDiff Topology

namespace KEBall

noncomputable def radialBallCutoff (ε r : ℝ) : ℝ :=
  ballCutoffProfile ε (r ^ 2)

noncomputable def ballBoundaryKernel (ε r : ℝ) : ℝ :=
  -deriv (radialBallCutoff ε) r

theorem radialBallCutoff_contDiff (ε : ℝ) : ContDiff ℝ ∞ (radialBallCutoff ε) :=
  (ballCutoffProfile_contDiff ε).comp (contDiff_id.pow 2)

theorem ballBoundaryKernel_continuous (ε : ℝ) : Continuous (ballBoundaryKernel ε) :=
  ((radialBallCutoff_contDiff ε).continuous_deriv (by simp)).neg

theorem ballCutoffProfile_antitone {ε : ℝ} (hε : 0 < ε) :
    Antitone (ballCutoffProfile ε) := by
  intro a b hab
  apply Real.smoothTransition.monotone
  apply (div_le_div_iff_of_pos_right hε).mpr
  linarith

theorem ballBoundaryKernel_eq (ε r : ℝ) :
    ballBoundaryKernel ε r = -2 * r * deriv (ballCutoffProfile ε) (r ^ 2) := by
  have h := (((ballCutoffProfile_contDiff ε).differentiable (by simp)) (r ^ 2)).hasDerivAt.comp r
    ((hasDerivAt_id r).pow 2)
  change HasDerivAt (radialBallCutoff ε) _ r at h
  have hd : deriv (radialBallCutoff ε) r =
      deriv (ballCutoffProfile ε) (r ^ 2) * (2 * r) := by
    simpa using h.deriv
  rw [ballBoundaryKernel, hd]
  ring

theorem ballBoundaryKernel_nonneg {ε r : ℝ} (hε : 0 < ε) (hr : 0 ≤ r) :
    0 ≤ ballBoundaryKernel ε r := by
  rw [ballBoundaryKernel_eq]
  exact mul_nonneg_of_nonpos_of_nonpos (by nlinarith)
    (ballCutoffProfile_antitone hε).deriv_nonpos

theorem ballBoundaryKernel_eq_zero_of_le {ε r : ℝ}
    (hε : 0 < ε) (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    ballBoundaryKernel ε r = 0 := by
  have hval : radialBallCutoff ε r = 1 :=
    ballCutoffProfile_eq_one hε (by nlinarith)
  have hmax : IsLocalMax (radialBallCutoff ε) r := by
    apply Eventually.of_forall
    intro y
    rw [hval]
    exact ballCutoffProfile_le_one ε (y ^ 2)
  simp only [ballBoundaryKernel, hmax.deriv_eq_zero, neg_zero]

theorem ballBoundaryKernel_eq_zero_of_ge {ε r : ℝ}
    (hε : 0 < ε) (hr : 1 + ε ≤ r) :
    ballBoundaryKernel ε r = 0 := by
  have hval : radialBallCutoff ε r = 0 :=
    ballCutoffProfile_eq_zero hε (by nlinarith)
  have hmin : IsLocalMin (radialBallCutoff ε) r := by
    apply Eventually.of_forall
    intro y
    rw [hval]
    exact ballCutoffProfile_nonneg ε (y ^ 2)
  simp only [ballBoundaryKernel, hmin.deriv_eq_zero, neg_zero]

theorem integral_ballBoundaryKernel {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∫ r in Icc (0 : ℝ) 2, ballBoundaryKernel ε r = 1 := by
  have hd : ∫ r in (0 : ℝ)..2, deriv (radialBallCutoff ε) r =
      radialBallCutoff ε 2 - radialBallCutoff ε 0 := by
    apply intervalIntegral.integral_deriv_eq_sub
    · intro x hx
      exact (radialBallCutoff_contDiff ε).differentiable (by simp) x
    · exact ((radialBallCutoff_contDiff ε).continuous_deriv (by simp)).intervalIntegrable _ _
  have hzero : radialBallCutoff ε 0 = 1 :=
    ballCutoffProfile_eq_one hε (by norm_num)
  have htwo : radialBallCutoff ε 2 = 0 :=
    ballCutoffProfile_eq_zero hε (by nlinarith)
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 2)]
  simp only [ballBoundaryKernel, intervalIntegral.integral_neg, hd, hzero, htwo]
  norm_num

theorem ballBoundaryKernel_tendstoUniformlyOn {u : Set ℝ}
    (hu : IsOpen u) (h1 : (1 : ℝ) ∈ u) :
    TendstoUniformlyOn
      (fun k : ℕ => ballBoundaryKernel (1 / ((k : ℝ) + 1))) 0 atTop
      (Icc 0 2 \ u) := by
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (hu.mem_nhds h1)
  have hsmall : ∀ᶠ k : ℕ in atTop, 1 / ((k : ℝ) + 1) < δ :=
    (tendsto_order.1 (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))).2 _ hδ
  refine tendstoUniformlyOn_iff.mpr fun η hη => ?_
  filter_upwards [hsmall] with k hk r hr
  have heq : ballBoundaryKernel (1 / ((k : ℝ) + 1)) r = 0 := by
    by_cases hr1 : r ≤ 1
    · exact ballBoundaryKernel_eq_zero_of_le (by positivity) hr.1.1 hr1
    · apply ballBoundaryKernel_eq_zero_of_ge (by positivity)
      have hnot : ¬ r < 1 + δ := by
        intro hlt
        apply hr.2
        apply hball
        simp only [Metric.mem_ball, Real.dist_eq, abs_of_pos (by linarith : 0 < r - 1)]
        linarith
      linarith
  simpa only [Pi.zero_apply, heq, dist_self] using hη

/-- The true radial derivative kernel evaluates integrable test functions at
radius one when they are continuous there. -/
theorem tendsto_integral_ballBoundaryKernel {g : ℝ → ℝ}
    (hg : IntegrableOn g (Icc 0 2) volume) (hgc : ContinuousWithinAt g (Icc 0 2) 1) :
    Tendsto (fun k : ℕ =>
      ∫ r in Icc (0 : ℝ) 2, ballBoundaryKernel (1 / ((k : ℝ) + 1)) r * g r)
      atTop (𝓝 (g 1)) := by
  have hi : Tendsto (fun k : ℕ =>
      ∫ r in Icc (0 : ℝ) 2, ballBoundaryKernel (1 / ((k : ℝ) + 1)) r)
      atTop (𝓝 1) := by
    apply tendsto_const_nhds.congr
    intro k
    symm
    exact integral_ballBoundaryKernel (by positivity) (by
      apply (div_le_one (by positivity : 0 < (k : ℝ) + 1)).mpr
      linarith [Nat.cast_nonneg (α := ℝ) k])
  have h := tendsto_setIntegral_peak_smul_of_integrableOn_of_tendsto
    (φ := fun k : ℕ => ballBoundaryKernel (1 / ((k : ℝ) + 1))) (l := atTop) (μ := volume)
    measurableSet_Icc measurableSet_Icc (Subset.rfl) self_mem_nhdsWithin
    (isCompact_Icc.measure_lt_top.ne)
    (Eventually.of_forall (fun (k : ℕ) r (hr : r ∈ Icc (0 : ℝ) 2) =>
      ballBoundaryKernel_nonneg (by positivity : 0 < 1 / ((k : ℝ) + 1)) hr.1))
    (fun _ hu h1 => ballBoundaryKernel_tendstoUniformlyOn hu h1) hi
    (Eventually.of_forall (fun (k : ℕ) =>
      (ballBoundaryKernel_continuous (1 / ((k : ℝ) + 1))).aestronglyMeasurable))
    hg hgc
  simpa only [smul_eq_mul] using h

#print axioms ballBoundaryKernel_eq
#print axioms ballBoundaryKernel_nonneg
#print axioms integral_ballBoundaryKernel
#print axioms ballBoundaryKernel_tendstoUniformlyOn
#print axioms tendsto_integral_ballBoundaryKernel

end KEBall
