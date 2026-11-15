import KEBall.BedfordTaylorTestMeasure
import PshLines.Regularization.PshRepresentative
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Plurisubharmonic representatives of increasing limits
-/

set_option autoImplicit false

open Filter MeasureTheory Set TopologicalSpace
open scoped ContDiff Distributions Topology

namespace KEBall.BedfordTaylor

open PshLines
open PshLines.FirstPass (ComplexModel)

variable {n : ℕ}

theorem measurable_psh_subtype {Ω : Opens (ComplexModel n)} {u : ComplexModel n → EReal}
    (hu : PlurisubharmonicOn u Ω) :
    Measurable (fun x : Ω => u x) :=
  (upperSemicontinuousOn_univ_iff.mp
    (hu.upperSemicontinuousOn.comp continuous_subtype_val.continuousOn
      (fun x _ => x.property))).measurable

/-- An increasing sequence of nonpositive PSH functions with finite
locally integrable representatives has a PSH representative of its supremum. -/
theorem exists_psh_iSup_of_monotone {B : Opens (ComplexModel n)}
    {p : ℕ → ComplexModel n → EReal} (hp : ∀ j, PlurisubharmonicOn (p j) B)
    (hneg : ∀ j x, x ∈ B → p j x ≤ 0)
    (hInt : ∀ j, IntegrableOn (fun x => (p j x).toReal) B volume)
    (hFin : ∀ j, ∀ᵐ x ∂(volume : Measure (ComplexModel n)).restrict B, p j x ≠ ⊤ ∧ p j x ≠ ⊥)
    (hmono : ∀ x ∈ B, Monotone (fun j => p j x)) :
    ∃ v : ComplexModel n → EReal, PlurisubharmonicOn v B ∧
      ∀ᵐ x ∂(volume : Measure (ComplexModel n)).restrict B,
        v x = ⨆ j, p j x := by
  let μ := (volume : Measure (ComplexModel n)).restrict B
  let s (x : ComplexModel n) := ⨆ j, p j x
  let f (j : ℕ) (x : ComplexModel n) := (p j x).toReal
  let g (x : ComplexModel n) := (s x).toReal
  have hdom : ∀ᵐ x ∂μ, x ∈ B := ae_restrict_mem B.isOpen.measurableSet
  have hfinite (x : ComplexModel n) (hx : x ∈ B) (h0 : p 0 x ≠ ⊥) :
      s x ≠ ⊤ ∧ s x ≠ ⊥ := by
    have hs : s x ≤ 0 := iSup_le fun j => hneg j x hx
    exact ⟨ne_of_lt (hs.trans_lt (by simp)),
      ne_of_gt ((bot_lt_iff_ne_bot.mpr h0).trans_le (le_iSup (fun j => p j x) 0))⟩
  have hsfinite : ∀ᵐ x ∂μ, s x ≠ ⊤ ∧ s x ≠ ⊥ := by
    filter_upwards [hdom, hFin 0] with x hx h0
    exact hfinite x hx h0.2
  have hfi (j : ℕ) : Integrable (f j) μ := hInt j
  have hmeas : AEMeasurable g μ :=
    aemeasurable_restrict_of_measurable_subtype B.isOpen.measurableSet
      (measurable_ereal_toReal.comp (Measurable.iSup fun j => measurable_psh_subtype (hp j)))
  have habs (j : ℕ) : ∀ᵐ x ∂μ, |f j x| ≤ |f 0 x| := by
    filter_upwards [hdom, hFin 0, hFin j] with x hx h0 hj
    change |(p j x).toReal| ≤ |(p 0 x).toReal|
    rw [abs_of_nonpos (EReal.toReal_nonpos (hneg j x hx)),
      abs_of_nonpos (EReal.toReal_nonpos (hneg 0 x hx))]
    exact neg_le_neg (EReal.toReal_le_toReal (hmono x hx (Nat.zero_le _)) h0.2 hj.1)
  have hgbound : ∀ᵐ x ∂μ, |g x| ≤ |f 0 x| := by
    filter_upwards [hdom, hFin 0, hsfinite] with x hx h0 hs
    have hnonpos : s x ≤ 0 := iSup_le fun j => hneg j x hx
    change |(s x).toReal| ≤ |(p 0 x).toReal|
    rw [abs_of_nonpos (EReal.toReal_nonpos hnonpos),
      abs_of_nonpos (EReal.toReal_nonpos (hneg 0 x hx))]
    exact neg_le_neg (EReal.toReal_le_toReal (le_iSup (fun j => p j x) 0) h0.2 hs.1)
  have hg : Integrable g μ := (hfi 0).abs.mono' hmeas.aestronglyMeasurable (by
    simpa only [Real.norm_eq_abs] using hgbound)
  have hconv : ∀ᵐ x ∂μ, Tendsto (fun j => f j x) atTop (𝓝 (g x)) := by
    filter_upwards [hdom, hsfinite] with x hx hs
    exact (EReal.tendsto_toReal hs.1 hs.2).comp (tendsto_atTop_iSup (hmono x hx))
  let L : LocallyIntegrableOn g B volume := IntegrableOn.locallyIntegrableOn hg
  have hLevi : HasNonnegativeDistributionalLevi (regularDistribution volume g L) := by
    intro z χ hχ
    rw [distributionalLeviCLM_regularDistribution_apply]
    let k := fun x => leviForm χ x z
    have hkC : Continuous k := continuous_leviForm (χ.contDiff.of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) z
    have hkS : tsupport k ⊆ tsupport χ := tsupport_leviForm_subset χ z
    have hk0 (x : ComplexModel n) (hx : x ∉ B) : k x = 0 :=
      image_eq_zero_of_notMem_tsupport (f := k) (fun h => hx (χ.tsupport_subset (hkS h)))
    obtain ⟨C, hC⟩ := (χ.hasCompactSupport.image_of_continuousOn hkC.abs.continuousOn).bddAbove
    let D := max 0 C
    have hD (x : ComplexModel n) : |k x| ≤ D := by
      by_cases hx : x ∈ tsupport χ
      · exact (hC ⟨x, hx, rfl⟩).trans (le_max_right _ _)
      · rw [image_eq_zero_of_notMem_tsupport (f := k) (fun h => hx (hkS h)), abs_zero]
        exact le_max_left _ _
    have hrestrict (w : ComplexModel n → ℝ) :
        (∫ x, w x * k x ∂(volume : Measure (ComplexModel n))) = ∫ x, w x * k x ∂μ :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by rw [hk0 x hx, mul_zero])).symm
    have hlim : Tendsto (fun j => ∫ x, f j x * k x ∂μ) atTop (𝓝 (∫ x, g x * k x ∂μ)) := by
      apply tendsto_integral_of_dominated_convergence (fun x => |f 0 x| * D)
      · intro j
        exact (hfi j).aestronglyMeasurable.mul hkC.aestronglyMeasurable
      · exact (hfi 0).abs.mul_const D
      · intro j
        filter_upwards [habs j] with x hx
        simp only [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul hx (hD x) (abs_nonneg _) (abs_nonneg _)
      · filter_upwards [hconv] with x hx
        exact hx.mul_const (k x)
    rw [hrestrict g]
    apply ge_of_tendsto hlim
    filter_upwards with j
    rw [← hrestrict (f j)]
    have hj := (hp j).hasNonnegativeDistributionalLevi_of_locallyIntegrable
      (IntegrableOn.locallyIntegrableOn (hfi j)) (hFin j) z χ hχ
    rw [distributionalLeviCLM_regularDistribution_apply] at hj
    exact hj
  obtain ⟨v, hvP, hvF, hvL, hvT⟩ := Regularization.exists_pshRepresentative volume hLevi
  refine ⟨v, hvP, ?_⟩
  filter_upwards [ae_eq_of_regularDistribution_eq volume L hvL hvT, hvF, hsfinite] with x hx hv hs
  change v x = s x
  rw [← EReal.coe_toReal hv.1 hv.2, ← EReal.coe_toReal hs.1 hs.2]
  exact congrArg (fun r : ℝ => (r : EReal)) hx.symm

end KEBall.BedfordTaylor
