import KEBall.CegrellBoundedEnergy
import KEBall.CegrellScaling

/-!
# Energy along a defining Cegrell approximation
-/

set_option autoImplicit false

open Filter MeasureTheory Set
open scoped Distributions ENNReal Topology

namespace KEBall.Cegrell

open BedfordTaylor
open PshLines.FirstPass (ComplexModel)

variable {n : ℕ} {u : ComplexModel n → EReal}
  {v w : ComplexModel n → ℝ}

private theorem cutoff_tail_le (hn : 0 < n)
    (hv : IsE0 (complexUnitBall n) v) (hw : IsE0 (complexUnitBall n) w)
    {a : ℝ} (ha : 0 < a) {ε : ℝ} (hε : 0 < ε)
    (χ : 𝓓(complexUnitBall n, ℝ)) (hχ : ∀ x, χ x ∈ Icc (0 : ℝ) 1)
    (hχ₁ : ∀ x ∈ complexUnitBall n, v x ≤ -ε → χ x = 1) :
    (∫⁻ x, ENNReal.ofReal ((1 - χ x) * -v x) ∂topMeasure hw.locallyBoundedPsh) ≤
      ENNReal.ofReal ε *
        (topMeasure (hv.const_mul ha).locallyBoundedPsh) univ +
        boundedEnergy hw / ENNReal.ofReal a := by
  let B := complexUnitBall n
  let A : Set (ComplexModel n) := {x ∈ B | a * v x < w x}
  let μ := topMeasure hw.locallyBoundedPsh
  let ρ := topMeasure (hv.const_mul ha).locallyBoundedPsh
  have hA : MeasurableSet A :=
    measurableSet_lt_of_locallyBoundedPsh (hv.const_mul ha).locallyBoundedPsh hw.locallyBoundedPsh
  have hdom : ∀ᵐ x ∂μ, x ∈ B := by
    rw [ae_iff]
    exact topMeasure_compl hw.locallyBoundedPsh
  have hcomp : μ A ≤ ρ A := (hv.const_mul ha).compare (isCompact_closure_complexUnitBall n)
    hw.locallyBoundedPsh (hw.nonpositive_unitBall hn)
  have hin (x : ComplexModel n) (hx : x ∈ B) : (1 - χ x) * -v x ≤ ε := by
    by_cases h : v x ≤ -ε
    · rw [hχ₁ x hx h, sub_self, zero_mul]
      exact hε.le
    · have hneg := neg_nonneg.mpr (hv.nonpositive_unitBall hn x hx)
      exact (mul_le_of_le_one_left hneg (sub_le_self _ (hχ x).1)).trans
        (by linarith [lt_of_not_ge h])
  have hfirst : (∫⁻ x in A, ENNReal.ofReal ((1 - χ x) * -v x) ∂μ) ≤
      ENNReal.ofReal ε * ρ univ := by
    calc
      _ ≤ ∫⁻ _ in A, ENNReal.ofReal ε ∂μ := by
        apply lintegral_mono_ae
        filter_upwards [ae_mono Measure.restrict_le_self hdom] with x hx
        exact ENNReal.ofReal_le_ofReal (hin x hx)
      _ = ENNReal.ofReal ε * μ A := by rw [lintegral_const, Measure.restrict_apply_univ]
      _ ≤ _ := mul_le_mul_right (hcomp.trans (measure_mono (subset_univ _))) _
  have hsecond : (∫⁻ x in Aᶜ, ENNReal.ofReal ((1 - χ x) * -v x) ∂μ) ≤
      boundedEnergy hw / ENNReal.ofReal a := by
    calc
      _ ≤ ∫⁻ x in Aᶜ, ENNReal.ofReal (-w x) * (ENNReal.ofReal a)⁻¹ ∂μ := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem hA.compl, ae_mono Measure.restrict_le_self hdom] with x hxA hxB
        have hx : w x ≤ a * v x := le_of_not_gt fun h => hxA ⟨hxB, h⟩
        rw [← div_eq_mul_inv, ← ENNReal.ofReal_div_of_pos ha]
        apply ENNReal.ofReal_le_ofReal
        apply (mul_le_of_le_one_left (neg_nonneg.mpr (hv.nonpositive_unitBall hn x hxB))
          (sub_le_self _ (hχ x).1)).trans
        exact (le_div_iff₀ ha).mpr (by linarith)
      _ ≤ ∫⁻ x, ENNReal.ofReal (-w x) * (ENNReal.ofReal a)⁻¹ ∂μ :=
        lintegral_mono' Measure.restrict_le_self le_rfl
      _ = _ := by
        rw [lintegral_mul_const' _ _ (ENNReal.inv_ne_top.mpr (by positivity)), ← div_eq_mul_inv]
        rfl
  rw [← lintegral_add_compl _ hA]
  exact add_le_add hfirst hsecond

private theorem crossEnergy_eq_cutoff_add_tail (hn : 0 < n)
    (hv : IsE0 (complexUnitBall n) v) (hw : IsE0 (complexUnitBall n) w)
    (χ : 𝓓(complexUnitBall n, ℝ)) (hχ : ∀ x, χ x ∈ Icc (0 : ℝ) 1) :
    crossEnergy hw v =
      (∫⁻ x, ENNReal.ofReal (χ x * -v x) ∂topMeasure hw.locallyBoundedPsh) +
      (∫⁻ x, ENNReal.ofReal ((1 - χ x) * -v x) ∂topMeasure hw.locallyBoundedPsh) := by
  let μ := topMeasure hw.locallyBoundedPsh
  have hdom : ∀ᵐ x ∂μ, x ∈ complexUnitBall n := by
    rw [ae_iff]
    exact topMeasure_compl hw.locallyBoundedPsh
  have hmeas : AEMeasurable (fun x => ENNReal.ofReal (χ x * -v x)) μ := by
    simpa only [Pi.neg_apply, mul_neg] using
      (integrable_test_mul_topMeasure hv.locallyBoundedPsh hw.locallyBoundedPsh χ).neg.aemeasurable.ennreal_ofReal
  rw [← lintegral_add_left' hmeas]
  apply lintegral_congr_ae
  filter_upwards [hdom] with x hx
  have hneg := neg_nonneg.mpr (hv.nonpositive_unitBall hn x hx)
  rw [← ENNReal.ofReal_add (mul_nonneg (hχ x).1 hneg) (mul_nonneg (sub_nonneg.mpr (hχ x).2) hneg)]
  congr 1
  ring

private theorem tendsto_cutoff_crossEnergy (hn : 0 < n) (hu : IsE1 (complexUnitBall n) u)
    (p : E1Approximation (complexUnitBall n) u) (hv : IsE0 (complexUnitBall n) v)
    (χ : 𝓓(complexUnitBall n, ℝ)) (hχ : ∀ x, 0 ≤ χ x) :
    Tendsto (fun j => ∫⁻ x, ENNReal.ofReal (χ x * -v x) ∂
        topMeasure (p.term_mem j).locallyBoundedPsh) atTop
      (𝓝 (∫⁻ x, ENNReal.ofReal (χ x * -v x) ∂mongeAmpereMeasure hu)) := by
  let μ := mongeAmpereMeasure hu
  have hnonneg (ρ : Measure (ComplexModel n))
      (hρ : ρ (complexUnitBall n : Set (ComplexModel n))ᶜ = 0) :
      0 ≤ᵐ[ρ] fun x => -(χ x * v x) := by
    have hdom : ∀ᵐ x ∂ρ, x ∈ complexUnitBall n := by rwa [ae_iff]
    filter_upwards [hdom] with x hx
    exact neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos (hχ x) (hv.nonpositive_unitBall hn x hx))
  have hval (ρ : Measure (ComplexModel n))
      (hρ : ρ (complexUnitBall n : Set (ComplexModel n))ᶜ = 0)
      (hi : Integrable (fun x => χ x * v x) ρ) :
      (∫⁻ x, ENNReal.ofReal (χ x * -v x) ∂ρ) =
        ENNReal.ofReal (-(∫ x, χ x * v x ∂ρ)) := by
    simpa only [Pi.neg_apply, mul_neg, integral_neg] using
      (ofReal_integral_eq_lintegral_ofReal hi.neg (hnonneg ρ hρ)).symm
  rw [hval μ (mongeAmpereMeasure_compl hu)
    (integrable_test_mul_mongeAmpereMeasure hn hu hv.locallyBoundedPsh χ)]
  apply (ENNReal.tendsto_ofReal (tendsto_weighted_mongeAmpereMeasure hn hu p hv.locallyBoundedPsh χ).neg).congr
  intro j
  exact (hval _ (topMeasure_compl (p.term_mem j).locallyBoundedPsh)
    (integrable_test_mul_topMeasure hv.locallyBoundedPsh (p.term_mem j).locallyBoundedPsh χ)).symm

/-- The integral energy is the supremum of the bounded energies of
any defining decreasing sequence. -/
theorem energy_eq_iSup (hn : 0 < n) (hu : IsE1 (complexUnitBall n) u)
    (p : E1Approximation (complexUnitBall n) u) :
    energy hu = ⨆ j, boundedEnergy (p.term_mem j) := by
  refine le_antisymm (energy_le_iSup hn hu p) (iSup_le fun i => ?_)
  let B := complexUnitBall n
  let v := p.term i
  let hv := p.term_mem i
  let M := ⨆ j, boundedEnergy (p.term_mem j)
  let L := energy hu
  have hb (a : ℝ) (ha : 0 < a) (ε : ℝ) (hε : 0 < ε) :
      boundedEnergy hv ≤ L +
        (ENNReal.ofReal ε * topMeasure (hv.const_mul ha).locallyBoundedPsh univ +
          M / ENNReal.ofReal a) := by
    let K := closure {x ∈ B | v x ≤ -ε}
    have hKB : K ⊆ B := sublevel_closure_subset hv (neg_lt_zero.mpr hε)
    have hK : IsCompact K := (isCompact_closure_complexUnitBall n).of_isClosed_subset
      isClosed_closure (closure_mono fun _ hx => hx.1)
    obtain ⟨χ, hχ, hχK⟩ := exists_testFunction_one_on hK hKB
    have hχ₁ (x : ComplexModel n) (hx : x ∈ B) (hle : v x ≤ -ε) : χ x = 1 :=
      hχK (subset_closure ⟨hx, hle⟩)
    let T (j : ℕ) := ∫⁻ x, ENNReal.ofReal (χ x * -v x) ∂topMeasure (p.term_mem j).locallyBoundedPsh
    let Tlim := ∫⁻ x, ENNReal.ofReal (χ x * -v x) ∂mongeAmpereMeasure hu
    let R := ENNReal.ofReal ε * topMeasure (hv.const_mul ha).locallyBoundedPsh univ +
      M / ENNReal.ofReal a
    have hT : Tendsto T atTop (𝓝 Tlim) :=
      tendsto_cutoff_crossEnergy hn hu p hv χ fun x => (hχ x).1
    have hle : ∀ᶠ j in atTop, boundedEnergy hv ≤ T j + R := by
      filter_upwards [eventually_ge_atTop i] with j hj
      have hE := boundedEnergy_le_crossEnergy hn (p.term_mem j) hv
        (fun x hx => p.antitone x hx hj)
      rw [crossEnergy_eq_cutoff_add_tail hn hv (p.term_mem j) χ hχ] at hE
      have hratio : boundedEnergy (p.term_mem j) / ENNReal.ofReal a ≤
          M / ENNReal.ofReal a :=
        ENNReal.div_le_div_right (le_iSup (fun j => boundedEnergy (p.term_mem j)) j) _
      exact hE.trans (add_le_add le_rfl
        ((cutoff_tail_le hn hv (p.term_mem j) ha hε χ hχ hχ₁).trans (add_le_add le_rfl hratio)))
    have hlim : boundedEnergy hv ≤ Tlim + R :=
      le_of_tendsto_of_tendsto tendsto_const_nhds (hT.add tendsto_const_nhds) hle
    have hTL : Tlim ≤ L := by
      apply lintegral_mono_ae
      have hdom : ∀ᵐ x ∂mongeAmpereMeasure hu, x ∈ B := by
        rw [ae_iff]
        exact mongeAmpereMeasure_compl hu
      filter_upwards [hdom] with x hx
      calc
        _ ≤ ENNReal.ofReal (-v x) := ENNReal.ofReal_le_ofReal
          (mul_le_of_le_one_left (neg_nonneg.mpr (hv.nonpositive_unitBall hn x hx)) (hχ x).2)
        _ = (-((v x : ℝ) : EReal)).toENNReal := by rw [← EReal.coe_neg]; rfl
        _ ≤ _ := EReal.toENNReal_le_toENNReal (EReal.neg_le_neg_iff.mpr (p.le_term i x hx))
    exact hlim.trans (add_le_add hTL le_rfl)
  have hsmall (a : ℝ) (ha : 0 < a) : boundedEnergy hv ≤ L + M / ENNReal.ofReal a := by
    let C := topMeasure (hv.const_mul ha).locallyBoundedPsh univ
    have hC := (hv.const_mul ha).finiteMass.ne
    let ε (j : ℕ) : ℝ := 1 / ((j : ℝ) + 1)
    have hε (j : ℕ) : 0 < ε j := by dsimp [ε]; positivity
    have hεlim : Tendsto ε atTop (𝓝 0) :=
      (tendsto_atTop_add_const_right atTop (1 : ℝ)
        (tendsto_natCast_atTop_atTop (R := ℝ))).const_div_atTop 1
    have hProd : Tendsto (fun j => ENNReal.ofReal (ε j) * C) atTop (𝓝 0) := by
      have he (j : ℕ) : ENNReal.ofReal (ε j * C.toReal) = ENNReal.ofReal (ε j) * C := by
        rw [ENNReal.ofReal_mul (hε j).le, ENNReal.ofReal_toReal hC]
      simpa only [zero_mul, ENNReal.ofReal_zero] using
        (ENNReal.tendsto_ofReal (hεlim.mul_const C.toReal)).congr he
    have hlim : Tendsto (fun j => L + (ENNReal.ofReal (ε j) * C + M / ENNReal.ofReal a))
        atTop (𝓝 (L + M / ENNReal.ofReal a)) := by
      simpa only [zero_add] using (tendsto_const_nhds (x := L)).add
        (hProd.add (tendsto_const_nhds (x := M / ENNReal.ofReal a)))
    exact le_of_tendsto_of_tendsto' tendsto_const_nhds hlim fun j => hb a ha (ε j) (hε j)
  let a (j : ℕ) : ℝ := (j : ℝ) + 1
  have ha (j : ℕ) : 0 < a j := by dsimp [a]; positivity
  have hRatio : Tendsto (fun j => M / ENNReal.ofReal (a j)) atTop (𝓝 0) := by
    have h := (tendsto_atTop_add_const_right atTop (1 : ℝ)
      (tendsto_natCast_atTop_atTop (R := ℝ))).const_div_atTop M.toReal
    have hEq (j : ℕ) : ENNReal.ofReal (M.toReal / a j) = M / ENNReal.ofReal (a j) := by
      rw [ENNReal.ofReal_div_of_pos (ha j), ENNReal.ofReal_toReal p.energyBound.ne]
    simpa only [ENNReal.ofReal_zero] using (ENNReal.tendsto_ofReal h).congr hEq
  have hlim : Tendsto (fun j => L + M / ENNReal.ofReal (a j)) atTop (𝓝 L) := by
    simpa only [add_zero] using (tendsto_const_nhds (x := L)).add hRatio
  exact le_of_tendsto_of_tendsto' tendsto_const_nhds hlim fun j => hsmall (a j) (ha j)

/-- The bounded energies increase to the integral energy. -/
theorem tendsto_boundedEnergy (hn : 0 < n) (hu : IsE1 (complexUnitBall n) u)
    (p : E1Approximation (complexUnitBall n) u) :
    Tendsto (fun j => boundedEnergy (p.term_mem j)) atTop (𝓝 (energy hu)) := by
  rw [energy_eq_iSup hn hu p]
  apply tendsto_atTop_iSup
  intro i j hij
  exact boundedEnergy_le_of_le hn (p.term_mem j) (p.term_mem i)
    (fun x hx => p.antitone x hx hij)

end KEBall.Cegrell
