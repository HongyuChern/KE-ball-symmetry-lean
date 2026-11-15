import KEBall.CegrellSublevelVolume
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Uniform integrability of finite-energy potentials
-/

set_option autoImplicit false

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace KEBall.Cegrell

open BedfordTaylor PshLines
open PshLines.FirstPass (ComplexModel)

variable {n : ℕ} {u : ComplexModel n → EReal}

private noncomputable def volumeCoefficient (n : ℕ) : ℝ :=
  ((n.factorial : ℝ) / Real.pi ^ n) * ((1 : ℝ) / 4) ^ (n + 1)

private theorem volumeCoefficient_pos (n : ℕ) : 0 < volumeCoefficient n := by
  unfold volumeCoefficient
  positivity

/-- A common bound for the real volume tails of a family with energy at most `M`. -/
noncomputable def volumeTailConstant (n : ℕ) (M : ℝ≥0∞) : ℝ :=
  (M / ENNReal.ofReal (volumeCoefficient n)).toReal

private theorem volumeTailConstant_nonneg (n : ℕ) (M : ℝ≥0∞) :
    0 ≤ volumeTailConstant n M := ENNReal.toReal_nonneg

private theorem volume_sublevel_le_quadratic (hn : 0 < n) (hu : IsE1 (complexUnitBall n) u)
    {M : ℝ≥0∞} (hM : energy hu ≤ M) (hMfin : M < ⊤) {t : ℝ} (ht : 1 ≤ t) :
    (volume : Measure (ComplexModel n)).restrict (complexUnitBall n)
        {x ∈ complexUnitBall n | u x < ((-t : ℝ) : EReal)} ≤
      ENNReal.ofReal (volumeTailConstant n M / t ^ 2) := by
  have ht₀ : 0 < t := zero_lt_one.trans_le ht
  let c := volumeCoefficient n
  have hc := volumeCoefficient_pos n
  have hden : c * t ^ 2 ≤ ((n.factorial : ℝ) / Real.pi ^ n) * (t / 4) ^ (n + 1) := by
    have he : ((n.factorial : ℝ) / Real.pi ^ n) * (t / 4) ^ (n + 1) = c * t ^ (n + 1) := by
      simp only [c, volumeCoefficient, div_eq_mul_inv, one_mul, mul_pow]
      ring
    rw [he]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ht (by omega)) hc.le
  calc
    _ ≤ energy hu / ENNReal.ofReal (((n.factorial : ℝ) / Real.pi ^ n) * (t / 4) ^ (n + 1)) :=
      volume_sublevel_le hn hu ht₀
    _ ≤ M / ENNReal.ofReal (c * t ^ 2) :=
      ENNReal.div_le_div hM (ENNReal.ofReal_le_ofReal hden)
    _ = _ := by
      have hf : M / ENNReal.ofReal c ≠ ⊤ :=
        (ENNReal.div_lt_top hMfin.ne (by positivity)).ne
      rw [volumeTailConstant, ENNReal.ofReal_div_of_pos (by positivity : 0 < t ^ 2),
        ENNReal.ofReal_toReal hf, ENNReal.ofReal_mul hc.le]
      simp only [div_eq_mul_inv, ENNReal.mul_inv (Or.inr ENNReal.ofReal_ne_top)
        (Or.inl ENNReal.ofReal_ne_top), mul_assoc]
      rfl

theorem IsE1.ae_finite (hn : 0 < n) (hu : IsE1 (complexUnitBall n) u) :
    ∀ᵐ x ∂(volume : Measure (ComplexModel n)).restrict (complexUnitBall n),
      u x ≠ ⊤ ∧ u x ≠ ⊥ := by
  let B := complexUnitBall n
  let μ := (volume : Measure (ComplexModel n)).restrict B
  have hdom : ∀ᵐ x ∂μ, x ∈ B := ae_restrict_mem B.isOpen.measurableSet
  have hbot : μ {x | u x = ⊥} = 0 := by
    apply le_antisymm _ bot_le
    let C := volumeTailConstant n (energy hu)
    let t (j : ℕ) : ℝ := (j : ℝ) + 1
    have ht (j : ℕ) : 1 ≤ t j := le_add_of_nonneg_left (Nat.cast_nonneg j)
    have hlim : Tendsto (fun j => ENNReal.ofReal (C / t j ^ 2)) atTop (𝓝 0) := by
      have hTop : Tendsto t atTop atTop :=
        tendsto_atTop_add_const_right atTop (1 : ℝ) (tendsto_natCast_atTop_atTop (R := ℝ))
      have h := ((tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp hTop).const_div_atTop C
      simpa only [ENNReal.ofReal_zero, Function.comp_def] using ENNReal.tendsto_ofReal h
    apply le_of_tendsto_of_tendsto' tendsto_const_nhds hlim
    intro j
    refine (measure_mono_ae ?_).trans (volume_sublevel_le_quadratic hn hu le_rfl (energy_lt_top hn hu) (ht j))
    filter_upwards [hdom] with x hx hux
    exact ⟨hx, hux ▸ bot_lt_iff_ne_bot.mpr (EReal.coe_ne_bot _)⟩
  have hae : ∀ᵐ x ∂μ, u x ≠ ⊥ := ae_iff.mpr (by simpa only [not_ne_iff] using hbot)
  filter_upwards [hdom, hae] with x hx hb
  exact ⟨(hu.1 x hx).ne_top, hb⟩

/-- The nonnegative real function `-u`, extended by zero outside the ball. -/
noncomputable def negativePotential (u : ComplexModel n → EReal) : ComplexModel n → ℝ :=
  (complexUnitBall n : Set (ComplexModel n)).indicator (fun x => -(u x).toReal)

theorem measurable_negativePotential (hu : IsE1 (complexUnitBall n) u) :
    Measurable (negativePotential u) := by
  let B := complexUnitBall n
  let e : B → ComplexModel n := Subtype.val
  have he : MeasurableEmbedding e := MeasurableEmbedding.subtype_coe B.isOpen.measurableSet
  have hsc : UpperSemicontinuous (fun x : B => u x) :=
    upperSemicontinuousOn_univ_iff.mp (hu.1.upperSemicontinuousOn.comp continuous_subtype_val.continuousOn
      (fun x _ => x.property))
  have hfun : negativePotential u = Function.extend e (fun x : B => -(u x).toReal) 0 := by
    funext x
    by_cases hx : x ∈ B
    · have h := he.injective.extend_apply (fun x : B => -(u x).toReal) 0 ⟨x, hx⟩
      exact (indicator_of_mem hx _).trans h.symm
    · rw [Function.extend_apply' _ _ _ (by rintro ⟨y, rfl⟩; exact hx y.property)]
      exact indicator_of_notMem hx _
  rw [hfun]
  exact he.measurable_extend (measurable_ereal_toReal.comp hsc.measurable).neg measurable_const

theorem negativePotential_nonneg (hn : 0 < n) (hu : IsE1 (complexUnitBall n) u) (x : ComplexModel n) :
    0 ≤ negativePotential u x := by
  by_cases hx : x ∈ complexUnitBall n
  · rw [negativePotential, indicator_of_mem hx]
    exact neg_nonneg.mpr (EReal.toReal_nonpos (hu.nonpositive_unitBall hn x hx))
  · rw [negativePotential, indicator_of_notMem hx]

theorem volume_negativePotential_gt_le (hn : 0 < n) (hu : IsE1 (complexUnitBall n) u)
    {M : ℝ≥0∞} (hM : energy hu ≤ M) (hMfin : M < ⊤) {t : ℝ} (ht : 1 ≤ t) :
    volume {x | t < negativePotential u x} ≤ ENNReal.ofReal (volumeTailConstant n M / t ^ 2) := by
  let B := complexUnitBall n
  let A : Set (ComplexModel n) := {x | t < negativePotential u x}
  have hA : MeasurableSet A := measurableSet_lt measurable_const (measurable_negativePotential hu)
  have ht₀ : 0 < t := zero_lt_one.trans_le ht
  have hAB : A ⊆ B := by
    intro x hx
    by_contra hxB
    have h := hx
    change t < negativePotential u x at h
    rw [negativePotential, indicator_of_notMem hxB] at h
    exact ht₀.not_gt h
  have hS : A ⊆ {x ∈ B | u x < ((-t : ℝ) : EReal)} := by
    intro x hx
    have hxB := hAB hx
    refine ⟨hxB, ?_⟩
    have h := hx
    change t < negativePotential u x at h
    rw [negativePotential, indicator_of_mem hxB] at h
    have hb : u x ≠ ⊥ := by
      intro he
      rw [he, EReal.toReal_bot, neg_zero] at h
      exact ht₀.not_gt h
    rw [← EReal.coe_toReal ((hu.1 x hxB).ne_top) hb, EReal.coe_lt_coe_iff]
    linarith
  calc
    _ = (volume : Measure (ComplexModel n)).restrict B A := by
      rw [Measure.restrict_apply hA, inter_eq_left.mpr hAB]
    _ ≤ _ := (measure_mono hS).trans (volume_sublevel_le_quadratic hn hu hM hMfin ht)

private theorem lintegral_Ioi_div_sq (C : ℝ) (hC : 0 ≤ C) {R : ℝ} (hR : 0 < R) :
    (∫⁻ t in Ioi R, ENNReal.ofReal (C / t ^ 2)) = ENNReal.ofReal (C / R) := by
  have he (t : ℝ) (ht : t ∈ Ioi R) : C / t ^ 2 = C * t ^ (-2 : ℝ) := by
    rw [Real.rpow_neg (hR.trans ht).le,
      show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, div_eq_mul_inv]
  have hpow : IntegrableOn (fun t : ℝ => C * t ^ (-2 : ℝ)) (Ioi R) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hR).const_mul C
  have hi : IntegrableOn (fun t : ℝ => C / t ^ 2) (Ioi R) :=
    hpow.congr_fun (fun t ht => (he t ht).symm) measurableSet_Ioi
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioi R)] (fun t => C / t ^ 2) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact div_nonneg hC (sq_nonneg _)
  rw [← ofReal_integral_eq_lintegral_ofReal hi hnonneg,
    setIntegral_congr_fun measurableSet_Ioi he, integral_const_mul,
    integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hR]
  norm_num [Real.rpow_neg_one, div_eq_mul_inv]

/-- The integral on any measurable region is controlled by its volume
and the common quadratic decay of the potential's volume sublevels. -/
theorem lintegral_negativePotential_le (hn : 0 < n) (hu : IsE1 (complexUnitBall n) u)
    {M : ℝ≥0∞} (hM : energy hu ≤ M) (hMfin : M < ⊤)
    {ρ : Measure (ComplexModel n)} (hρ : ρ ≤ volume) {R : ℝ} (hR : 1 ≤ R) :
    (∫⁻ x, ENNReal.ofReal (negativePotential u x) ∂ρ) ≤
      ρ univ * ENNReal.ofReal R + ENNReal.ofReal (volumeTailConstant n M / R) := by
  let C := volumeTailConstant n M
  let f := negativePotential u
  have hR₀ := zero_lt_one.trans_le hR
  have hdis : Disjoint (Ioc (0 : ℝ) R) (Ioi R) :=
    disjoint_left.mpr fun _ h₁ h₂ => (not_lt_of_ge h₁.2) h₂
  rw [lintegral_eq_lintegral_meas_lt ρ (Eventually.of_forall (negativePotential_nonneg hn hu))
    (measurable_negativePotential hu).aemeasurable,
    ← Ioc_union_Ioi_eq_Ioi hR₀.le, lintegral_union measurableSet_Ioi hdis]
  apply add_le_add
  · calc
      _ ≤ ∫⁻ _ in Ioc (0 : ℝ) R, ρ univ :=
        lintegral_mono fun _ => measure_mono (subset_univ _)
      _ = _ := by rw [setLIntegral_const, Real.volume_Ioc, sub_zero]
  · calc
      _ ≤ ∫⁻ t in Ioi R, ENNReal.ofReal (C / t ^ 2) := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact (hρ _).trans (volume_negativePotential_gt_le hn hu hM hMfin (hR.trans ht.le))
      _ = _ := lintegral_Ioi_div_sq C (volumeTailConstant_nonneg _ _) hR₀

theorem integrable_negativePotential (hn : 0 < n) (hu : IsE1 (complexUnitBall n) u) :
    Integrable (negativePotential u) (volume : Measure (ComplexModel n)) := by
  let B := complexUnitBall n
  let μ := (volume : Measure (ComplexModel n)).restrict B
  have hμ : μ univ < ⊤ := by
    rw [Measure.restrict_apply_univ]
    exact (measure_mono subset_closure).trans_lt (isCompact_closure_complexUnitBall n).measure_lt_top
  have hb := lintegral_negativePotential_le hn hu le_rfl (energy_lt_top hn hu)
    (ρ := μ) Measure.restrict_le_self (R := 1) le_rfl
  have he : (B : Set (ComplexModel n)).indicator (fun x => ENNReal.ofReal (negativePotential u x)) =
      fun x => ENNReal.ofReal (negativePotential u x) := by
    funext x
    by_cases hx : x ∈ B
    · rw [indicator_of_mem hx]
    · rw [indicator_of_notMem hx, negativePotential, indicator_of_notMem hx, ENNReal.ofReal_zero]
  rw [← lintegral_indicator B.isOpen.measurableSet, he] at hb
  refine ⟨(measurable_negativePotential hu).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall (negativePotential_nonneg hn hu))]
  exact hb.trans_lt (ENNReal.add_lt_top.mpr
    ⟨ENNReal.mul_lt_top hμ ENNReal.ofReal_lt_top, ENNReal.ofReal_lt_top⟩)

theorem IsE1.integrableOn_toReal (hn : 0 < n) (hu : IsE1 (complexUnitBall n) u) :
    IntegrableOn (fun x => (u x).toReal) (complexUnitBall n) volume := by
  apply (integrable_indicator_iff (complexUnitBall n).isOpen.measurableSet).mp
  have he : (fun x => -negativePotential u x) =
      (complexUnitBall n : Set (ComplexModel n)).indicator (fun x => (u x).toReal) := by
    funext x
    by_cases hx : x ∈ complexUnitBall n <;> simp [negativePotential, hx]
  exact he ▸ (integrable_negativePotential hn hu).neg

end KEBall.Cegrell
