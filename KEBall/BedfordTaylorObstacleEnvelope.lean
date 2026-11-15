import KEBall.BedfordTaylorMonotoneRepresentative
import KEBall.BedfordTaylorTruncationLocality

/-!
# Bounded plurisubharmonic envelopes
-/

set_option autoImplicit false

open Filter MeasureTheory Set TopologicalSpace
open scoped ENNReal Topology

namespace KEBall.BedfordTaylor

open PshLines
open PshLines.FirstPass (ComplexModel)
open PshLines.FirstPass.MongeAmpere (IsLocallyBoundedPshOn)

variable {n : ℕ} {Ω : Opens (ComplexModel n)}

/-- The greatest locally bounded plurisubharmonic minorant of a bounded
upper semicontinuous obstacle on an open set of finite volume. -/
theorem exists_bounded_psh_envelope {f : ComplexModel n → EReal} {m : ℝ}
    (hf : UpperSemicontinuousOn f Ω)
    (hLower : ∀ x ∈ Ω, (m : EReal) ≤ f x)
    (hUpper : ∀ x ∈ Ω, f x ≤ 0)
    (hΩ : (volume : Measure (ComplexModel n)) Ω < ⊤) :
    ∃ u : ComplexModel n → ℝ,
      IsLocallyBoundedPshOn Ω u ∧ (∀ x ∈ Ω, m ≤ u x ∧ (u x : EReal) ≤ f x) ∧
      ∀ v : ComplexModel n → ℝ, IsLocallyBoundedPshOn Ω v →
        (∀ x ∈ Ω, (v x : EReal) ≤ f x) → ∀ x ∈ Ω, v x ≤ u x := by
  let μ := (volume : Measure (ComplexModel n)).restrict Ω
  let : IsFiniteMeasure μ := ⟨by rw [Measure.restrict_apply_univ]; exact hΩ⟩
  have hdom : ∀ᵐ x ∂μ, x ∈ Ω := ae_restrict_mem Ω.isOpen.measurableSet
  let A (u : ComplexModel n → ℝ) : Prop :=
    IsLocallyBoundedPshOn Ω u ∧ ∀ x ∈ Ω, m ≤ u x ∧ (u x : EReal) ≤ f x
  let J (u : ComplexModel n → ℝ) : ℝ := ∫ x, u x ∂μ
  have hNeg {v : ComplexModel n → ℝ} (hv : A v) (x : ComplexModel n) (hx : x ∈ Ω) : v x ≤ 0 :=
    EReal.coe_le_coe_iff.mp ((hv.2 x hx).2.trans (hUpper x hx))
  have hAbs {v : ComplexModel n → ℝ} (hv : A v) (x : ComplexModel n) (hx : x ∈ Ω) : |v x| ≤ -m := by
    rw [abs_of_nonpos (hNeg hv x hx)]
    exact neg_le_neg (hv.2 x hx).1
  have hInt {v : ComplexModel n → ℝ} (hv : A v) : Integrable v μ := by
    have hmeas : AEMeasurable v μ :=
      aemeasurable_restrict_of_measurable_subtype Ω.isOpen.measurableSet
        (measurable_subtype_of_locallyBoundedPsh hv.1)
    exact Integrable.of_bound hmeas.aestronglyMeasurable (-m) (by
      filter_upwards [hdom] with x hx
      simpa only [Real.norm_eq_abs] using hAbs hv x hx)
  have hMax {u v : ComplexModel n → ℝ} (hu : A u) (hv : A v) : A (fun x => max (u x) (v x)) := by
    refine ⟨locallyBoundedPsh_max hu.1 hv.1, fun x hx => ⟨(hu.2 x hx).1.trans (le_max_left _ _), ?_⟩⟩
    change ((max (u x) (v x) : ℝ) : EReal) ≤ f x
    rcases le_total (u x) (v x) with h | h
    · rw [max_eq_right h]
      exact (hv.2 x hx).2
    · rw [max_eq_left h]
      exact (hu.2 x hx).2
  let S : Set ℝ := {r | ∃ v, A v ∧ r = J v}
  have hS : S.Nonempty :=
    ⟨J (fun _ => m), fun _ => m, ⟨locallyBoundedPsh_const m, fun x hx => ⟨le_rfl, hLower x hx⟩⟩, rfl⟩
  have hSbdd : BddAbove S := ⟨0, by
    rintro r ⟨v, hv, rfl⟩
    exact integral_nonpos_of_ae (hdom.mono fun x hx => hNeg hv x hx)⟩
  let L := sSup S
  let ε (j : ℕ) : ℝ := 1 / ((j : ℝ) + 1)
  have hε (j : ℕ) : 0 < ε j := by dsimp [ε]; positivity
  have hεlim : Tendsto ε atTop (𝓝 0) :=
    (tendsto_atTop_add_const_right atTop (1 : ℝ)
      (tendsto_natCast_atTop_atTop (R := ℝ))).const_div_atTop 1
  have hSeq (j : ℕ) : ∃ v, A v ∧ L - ε j < J v := by
    obtain ⟨r, ⟨v, hv, rfl⟩, hr⟩ := exists_lt_of_lt_csSup hS (sub_lt_self L (hε j))
    exact ⟨v, hv, hr⟩
  choose v hv hvnear using hSeq
  let p (j : ℕ) : ComplexModel n → ℝ := Nat.rec (v 0)
    (fun k w x => max (w x) (v (k + 1) x)) j
  have hp0 : p 0 = v 0 := rfl
  have hpSucc (j : ℕ) (x : ComplexModel n) : p (j + 1) x = max (p j x) (v (j + 1) x) := rfl
  have hp (j : ℕ) : A (p j) := by
    induction j with
    | zero => exact hv 0
    | succ j ih => exact hMax ih (hv (j + 1))
  have hpMono (x : ComplexModel n) : Monotone (fun j => p j x) :=
    monotone_nat_of_le_succ fun j => (le_max_left _ _).trans_eq (hpSucc j x).symm
  have hpAbove (j : ℕ) (x : ComplexModel n) : v j x ≤ p j x := by
    cases j with
    | zero => exact le_rfl
    | succ j => exact (le_max_right _ _).trans_eq (hpSucc j x).symm
  have hpLim : Tendsto (fun j => J (p j)) atTop (𝓝 L) := by
    have h := (tendsto_const_nhds (x := L)).sub hεlim
    rw [sub_zero] at h
    exact h.squeeze tendsto_const_nhds
      (fun j => (hvnear j).le.trans (integral_mono (hInt (hv j)) (hInt (hp j)) (hpAbove j)))
      (fun j => le_csSup hSbdd ⟨p j, hp j, rfl⟩)
  let pE (j : ℕ) (x : ComplexModel n) : EReal := Real.toEReal (p j x)
  obtain ⟨w, hw, hwEq⟩ := exists_psh_iSup_of_monotone (p := pE)
    (fun j => (hp j).1.1)
    (fun j x hx => by
      change (p j x : EReal) ≤ 0
      exact_mod_cast hNeg (hp j) x hx)
    (fun j => by
      change IntegrableOn (fun x => (p j x : EReal).toReal) Ω volume
      simp only [EReal.toReal_coe]
      exact hInt (hp j))
    (fun j => Eventually.of_forall fun x => ⟨EReal.coe_ne_top _, EReal.coe_ne_bot _⟩)
    (fun x _ _ _ h => EReal.coe_le_coe_iff.mpr (hpMono x h))
  have hwLower (x : ComplexModel n) (hx : x ∈ Ω) : (m : EReal) ≤ w x := by
    have hc : PlurisubharmonicOn (fun _ : ComplexModel n => (m : EReal)) Ω :=
      fun x _ => plurisubharmonicAt_const _ (by simp) x
    exact hc.le_of_ae_le Ω.isOpen hw.upperSemicontinuousOn volume (by
      filter_upwards [hwEq, hdom] with y hy hyΩ
      rw [hy]
      exact (EReal.coe_le_coe_iff.mpr ((hp 0).2 y hyΩ).1).trans (le_iSup (fun j => pE j y) 0)) x hx
  have hwUpper (x : ComplexModel n) (hx : x ∈ Ω) : w x ≤ f x :=
    hw.le_of_ae_le Ω.isOpen hf volume (by
      filter_upwards [hwEq, hdom] with y hy hyΩ
      rw [hy]
      exact iSup_le fun j => (hp j).2 y hyΩ |>.2) x hx
  let u (x : ComplexModel n) := (w x).toReal
  have huEq (x : ComplexModel n) (hx : x ∈ Ω) : (u x : EReal) = w x :=
    EReal.coe_toReal ((hw x hx).ne_top)
      (ne_of_gt ((bot_lt_iff_ne_bot.mpr (EReal.coe_ne_bot m)).trans_le (hwLower x hx)))
  have huPsh : PlurisubharmonicOn (fun x => (u x : EReal)) Ω := by
    intro x hx
    apply (hw x hx).congr
    filter_upwards [Ω.isOpen.mem_nhds hx] with y hy
    exact (huEq y hy).symm
  have huOrd (x : ComplexModel n) (hx : x ∈ Ω) : m ≤ u x ∧ (u x : EReal) ≤ f x := by
    rw [← EReal.coe_le_coe_iff, huEq x hx]
    exact ⟨hwLower x hx, hwUpper x hx⟩
  have hu : A u := by
    refine ⟨⟨huPsh, fun x hx => ⟨Ω, hx, le_rfl, -m, fun y hy => ?_⟩⟩, huOrd⟩
    have h := EReal.coe_le_coe_iff.mp ((huOrd y hy).2.trans (hUpper y hy)) 
    rw [abs_of_nonpos h]
    exact neg_le_neg (huOrd y hy).1
  have hJu : J u = L := by
    have hlim : Tendsto (fun j => J (p j)) atTop (𝓝 (J u)) := by
      apply tendsto_integral_of_dominated_convergence (fun _ => -m)
      · exact fun j => (hInt (hp j)).aestronglyMeasurable
      · exact integrable_const _
      · intro j
        filter_upwards [hdom] with x hx
        simpa only [Real.norm_eq_abs] using hAbs (hp j) x hx
      · filter_upwards [hdom, hwEq] with x hx hEq
        have ht := tendsto_atTop_iSup (fun i j hij => EReal.coe_le_coe_iff.mpr (hpMono x hij))
        change Tendsto (fun j => pE j x) atTop (𝓝 (⨆ j, pE j x)) at ht
        rw [← hEq] at ht
        have hn : w x ≠ ⊥ := ne_of_gt
          ((bot_lt_iff_ne_bot.mpr (EReal.coe_ne_bot m)).trans_le (hwLower x hx))
        simpa only [pE, Function.comp_def, EReal.toReal_coe] using
          (EReal.tendsto_toReal ((hw x hx).ne_top) hn).comp ht
    exact tendsto_nhds_unique hlim hpLim
  refine ⟨u, hu.1, hu.2, ?_⟩
  intro z hz hzF
  let a (x : ComplexModel n) := max (z x) m
  have ha : A a := ⟨locallyBoundedPsh_max_const hz m, fun x hx => ⟨le_max_right _ _, by
    rcases le_total (z x) m with h | h
    · rw [show a x = m from max_eq_right h]
      exact hLower x hx
    · rw [show a x = z x from max_eq_left h]
      exact hzF x hx⟩⟩
  let b (x : ComplexModel n) := max (u x) (a x)
  have hb : A b := hMax hu ha
  have hJb : J b ≤ J u := by rw [hJu]; exact le_csSup hSbdd ⟨b, hb, rfl⟩
  have hnonneg : 0 ≤ᵐ[μ] fun x => b x - u x :=
    Eventually.of_forall fun x => sub_nonneg.mpr (le_max_left _ _)
  have hDiff : Integrable (fun x => b x - u x) μ := (hInt hb).sub (hInt hu)
  have hzero : (∫ x, b x - u x ∂μ) = 0 := by
    apply le_antisymm _ (integral_nonneg_of_ae hnonneg)
    rw [integral_sub (hInt hb) (hInt hu)]
    exact sub_nonpos.mpr hJb
  have hAe := (integral_eq_zero_iff_of_nonneg_ae hnonneg hDiff).mp hzero
  have hAu : ∀ x ∈ Ω, a x ≤ u x := by
    intro x hx
    have h := ha.1.1.le_of_ae_le Ω.isOpen huPsh.upperSemicontinuousOn volume (by
      filter_upwards [hAe] with y hy
      have hby : b y = u y := sub_eq_zero.mp hy
      exact EReal.coe_le_coe_iff.mpr ((le_max_right (u y) (a y)).trans_eq hby)) x hx
    exact EReal.coe_le_coe_iff.mp h
  exact fun x hx => (le_max_left _ _).trans (hAu x hx)

end KEBall.BedfordTaylor
