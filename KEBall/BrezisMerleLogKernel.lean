import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.PolarCoord

/-!
# Exponential integrability for logarithmic potentials in the disc

The exponent is normalized so that the logarithmic pole is
`log ‖z - a‖²`. Jensen's inequality then applies below mass one.
-/

set_option autoImplicit false

open Filter MeasureTheory Metric Set
open scoped ENNReal

namespace KEBall.BrezisMerle

private theorem radial_power_integral {s : ℝ} (hs : -2 < s) :
    (∫⁻ z in ball (0 : ℂ) 2, ENNReal.ofReal (‖z‖ ^ s) ∂volume) =
      ENNReal.ofReal (2 * Real.pi * 2 ^ (s + 2) / (s + 2)) := by
  rw [← lintegral_indicator measurableSet_ball, ← Complex.lintegral_comp_polarCoord_symm,
    polarCoord_target]
  have heq : (∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
      ENNReal.ofReal p.1 • (ball (0 : ℂ) 2).indicator
        (fun z => ENNReal.ofReal (‖z‖ ^ s)) (Complex.polarCoord.symm p) ∂volume) =
      ∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
        (Ioo (0 : ℝ) 2).indicator (fun r => ENNReal.ofReal (r ^ (s + 1))) p.1 ∂volume := by
    apply setLIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo)
    intro p hp
    dsimp only
    have hr : 0 < p.1 := hp.1
    have hnorm : ‖Complex.polarCoord.symm p‖ = p.1 := by
      rw [Complex.norm_polarCoord_symm, abs_of_pos hr]
    have hball : Complex.polarCoord.symm p ∈ ball (0 : ℂ) 2 ↔ p.1 < 2 := by
      rw [mem_ball_zero_iff, hnorm]
    by_cases h : p.1 < 2
    · rw [indicator_of_mem (hball.mpr h), indicator_of_mem (show p.1 ∈ Ioo 0 2 from ⟨hr, h⟩),
        hnorm, smul_eq_mul, ← ENNReal.ofReal_mul hr.le, Real.rpow_add hr, Real.rpow_one, mul_comm]
    · rw [indicator_of_notMem (mt hball.mp h),
        indicator_of_notMem (fun hp' : p.1 ∈ Ioo 0 2 => h hp'.2), smul_zero]
  rw [heq]
  change (∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
    (Ioo (0 : ℝ) 2).indicator (fun r => ENNReal.ofReal (r ^ (s + 1))) p.1
      ∂(volume.prod volume)) = _
  have hm : Measurable ((Ioo (0 : ℝ) 2).indicator (fun r => ENNReal.ofReal (r ^ (s + 1)))) :=
    Measurable.indicator (by fun_prop) measurableSet_Ioo
  rw [setLIntegral_prod (fun p : ℝ × ℝ =>
    (Ioo (0 : ℝ) 2).indicator (fun r => ENNReal.ofReal (r ^ (s + 1))) p.1)
      (hm.comp measurable_fst).aemeasurable]
  simp only [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioo]
  rw [lintegral_mul_const _ hm, lintegral_indicator measurableSet_Ioo,
    Measure.restrict_restrict measurableSet_Ioo, inter_eq_left.mpr (show Ioo (0 : ℝ) 2 ⊆ Ioi 0 from fun _ h => h.1)]
  have hi : IntegrableOn (fun r : ℝ => r ^ (s + 1)) (Ioo 0 2) :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num : (0 : ℝ) < 2)).mpr (by linarith)
  have hn : 0 ≤ᵐ[(volume : Measure ℝ).restrict (Ioo 0 2)] fun r => r ^ (s + 1) := by
    filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioo (a := (0 : ℝ)) (b := 2))]
      with r hr
    exact Real.rpow_nonneg hr.1.le _
  rw [← ofReal_integral_eq_lintegral_ofReal hi hn]
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 2),
    integral_rpow (Or.inl (by linarith : -1 < s + 1))]
  rw [show s + 1 + 1 = s + 2 by ring, Real.zero_rpow (by linarith : s + 2 ≠ 0), sub_zero,
    ← ENNReal.ofReal_mul (div_nonneg (Real.rpow_nonneg (by norm_num) _) (by linarith))]
  congr 1
  ring

/-- A uniform bound in the pole for the exponential of the logarithmic kernel. -/
theorem lintegral_exp_logKernel_le {a : ℂ} (ha : a ∈ ball (0 : ℂ) 1)
    {t : ℝ} (ht : t < 1) :
    (∫⁻ z in ball (0 : ℂ) 1,
      ENNReal.ofReal (Real.exp (-t * (2 * Real.log (‖z - a‖ / 2)))) ∂volume) ≤
        ENNReal.ofReal (4 * Real.pi / (1 - t)) := by
  let s : ℝ := -2 * t
  let f : ℂ → ℝ≥0∞ := fun z => ENNReal.ofReal (‖z‖ ^ s)
  have hs : -2 < s := by dsimp [s]; linarith
  have hne : ∀ᵐ z ∂(volume : Measure ℂ).restrict (ball 0 1), z ≠ a := by
    apply ae_restrict_of_ae
    rw [ae_iff]
    simp
  calc
    _ = ∫⁻ z in ball (0 : ℂ) 1, ENNReal.ofReal ((2 : ℝ) ^ (-s)) * f (z - a) ∂volume := by
      apply lintegral_congr_ae
      filter_upwards [hne] with z hz
      have hd : 0 < ‖z - a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz)
      dsimp [f]
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _),
        Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), Real.rpow_def_of_pos hd,
        ← Real.exp_add, Real.log_div hd.ne' (by norm_num)]
      congr 2
      dsimp [s]
      ring
    _ ≤ ∫⁻ z, (ball (0 : ℂ) 2).indicator
        (fun w => ENNReal.ofReal ((2 : ℝ) ^ (-s)) * f w) (z - a) ∂volume := by
      rw [← lintegral_indicator measurableSet_ball]
      apply lintegral_mono
      intro z
      change (ball (0 : ℂ) 1).indicator _ z ≤
        (ball (0 : ℂ) 2).indicator (fun w => ENNReal.ofReal ((2 : ℝ) ^ (-s)) * f w) (z - a)
      by_cases hz : z ∈ ball (0 : ℂ) 1
      · have hza : z - a ∈ ball (0 : ℂ) 2 := by
          rw [mem_ball_zero_iff] at hz ha ⊢
          exact (norm_sub_le _ _).trans_lt (by linarith)
        rw [indicator_of_mem hz, indicator_of_mem hza]
      · rw [indicator_of_notMem hz]
        exact zero_le
    _ = _ := by
      simp only [sub_eq_add_neg]
      rw [lintegral_add_right_eq_self, lintegral_indicator measurableSet_ball,
        lintegral_const_mul _ (by fun_prop)]
      change ENNReal.ofReal ((2 : ℝ) ^ (-s)) *
        (∫⁻ z in ball (0 : ℂ) 2, ENNReal.ofReal (‖z‖ ^ s) ∂volume) = _
      rw [radial_power_integral hs, ← ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _)]
      congr 1
      rw [← mul_div_assoc, show (2 : ℝ) ^ (-s) * (2 * Real.pi * (2 : ℝ) ^ (s + 2)) =
          (2 * Real.pi) * ((2 : ℝ) ^ (-s) * (2 : ℝ) ^ (s + 2)) by ring,
        ← Real.rpow_add (by norm_num : (0 : ℝ) < 2), show -s + (s + 2) = 2 by ring]
      norm_num
      dsimp [s]
      field_simp
      ring

/-- Jensen and Tonelli turn a uniform kernel estimate into an estimate
for the exponential of any function above its probability average. -/
theorem lintegral_exp_le_of_kernel {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {ν : Measure X} [SFinite ν] {μ : Measure Y} [IsProbabilityMeasure μ]
    {s : Set X} (hs : MeasurableSet s) {L : X → Y → ℝ}
    (hL : Measurable (Function.uncurry L)) {v : X → ℝ} {t : ℝ} (ht : 0 ≤ t)
    (hi : ∀ z ∈ s, Integrable (L z) μ)
    (hv : ∀ z ∈ s, (∫ a, L z a ∂μ) ≤ v z) {C : ℝ≥0∞}
    (hC : ∀ᵐ a ∂μ, (∫⁻ z in s, ENNReal.ofReal (Real.exp (-t * L z a)) ∂ν) ≤ C) :
    (∫⁻ z in s, ENNReal.ofReal (Real.exp (-t * v z)) ∂ν) ≤ C := by
  let k : X → Y → ℝ := fun z a => -t * L z a
  let F : X → Y → ℝ≥0∞ := fun z a => ENNReal.ofReal (Real.exp (k z a))
  have hF : Measurable (Function.uncurry F) :=
    (Real.measurable_exp.comp (hL.const_mul _)).ennreal_ofReal
  calc
    _ ≤ ∫⁻ z in s, ∫⁻ a, F z a ∂μ ∂ν := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem (μ := ν) hs] with z hz
      by_cases hfin : (∫⁻ a, F z a ∂μ) = ⊤
      · rw [hfin]
        exact le_top
      have hki : Integrable (k z) μ := (hi z hz).const_mul _
      have hfm : Measurable (fun a => Real.exp (k z a)) :=
        (Real.measurable_exp.comp (hL.const_mul _)).comp (measurable_const.prodMk measurable_id)
      have hfei : Integrable (fun a => Real.exp (k z a)) μ :=
        (lintegral_ofReal_ne_top_iff_integrable hfm.aestronglyMeasurable
          (Eventually.of_forall fun _ => (Real.exp_pos _).le)).mp hfin
      have hJ := convexOn_exp.map_integral_le Real.continuous_exp.continuousOn isClosed_univ
        (Eventually.of_forall fun _ => mem_univ _) hki hfei
      rw [show (∫ a, k z a ∂μ) = -t * ∫ a, L z a ∂μ by exact integral_const_mul _ _] at hJ
      rw [show (∫⁻ a, F z a ∂μ) = ENNReal.ofReal (∫ a, Real.exp (k z a) ∂μ) from
        (ofReal_integral_eq_lintegral_ofReal hfei
          (Eventually.of_forall fun _ => (Real.exp_pos _).le)).symm]
      exact ENNReal.ofReal_le_ofReal ((Real.exp_le_exp.mpr
        (mul_le_mul_of_nonpos_left (hv z hz) (neg_nonpos.mpr ht))).trans hJ)
    _ = ∫⁻ a, ∫⁻ z in s, F z a ∂ν ∂μ := lintegral_lintegral_swap hF.aemeasurable
    _ ≤ ∫⁻ _, C ∂μ := lintegral_mono_ae hC
    _ = _ := by simp

/-- The exponential estimate for a logarithmic potential of probability mass. -/
theorem lintegral_exp_le_of_logPotential {μ : Measure ℂ} [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ a ∂μ, a ∈ ball (0 : ℂ) 1) {v : ℂ → ℝ} {t : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t < 1)
    (hi : ∀ z ∈ ball (0 : ℂ) 1, Integrable (fun a => 2 * Real.log (‖z - a‖ / 2)) μ)
    (hv : ∀ z ∈ ball (0 : ℂ) 1, (∫ a, 2 * Real.log (‖z - a‖ / 2) ∂μ) ≤ v z) :
    (∫⁻ z in ball (0 : ℂ) 1, ENNReal.ofReal (Real.exp (-t * v z)) ∂volume) ≤
      ENNReal.ofReal (4 * Real.pi / (1 - t)) := by
  apply lintegral_exp_le_of_kernel measurableSet_ball
    (L := fun z a : ℂ => 2 * Real.log (‖z - a‖ / 2)) (by fun_prop)
    ht₀ hi hv
  filter_upwards [hμ] with a ha
  exact lintegral_exp_logKernel_le ha ht₁

end KEBall.BrezisMerle
