import KEBall.CegrellOrder
import KEBall.CegrellQuadratic

/-!
# Closure of energy sublevels under decreasing limits
-/

set_option autoImplicit false

open Filter MeasureTheory Set
open scoped Distributions ENNReal Topology

namespace KEBall.Cegrell

open BedfordTaylor PshLines
open PshLines.FirstPass (ComplexModel)

variable {n : ℕ}

theorem boundedEnergy_le_of_decreasing (hn : 0 < n)
    {v : ComplexModel n → ℝ} (hv : IsE0 (complexUnitBall n) v)
    {p : ℕ → ComplexModel n → ℝ} (hp : ∀ j, IsE0 (complexUnitBall n) (p j))
    (hanti : ∀ x ∈ complexUnitBall n, Antitone (fun j => p j x))
    (hlim : ∀ x ∈ complexUnitBall n, Tendsto (fun j => p j x) atTop (𝓝 (v x)))
    {M : ℝ≥0∞} (hM : ∀ j, boundedEnergy (hp j) ≤ M) :
    boundedEnergy hv ≤ M := by
  apply lintegral_energy_le_of_cutoff_bound (topMeasure_compl hv.locallyBoundedPsh)
  intro χ hχ
  have hnonneg (x : ComplexModel n) : 0 ≤ χ x := (hχ x).1
  let hP := fun j => (hp j).locallyBoundedPsh
  have h := ENNReal.tendsto_ofReal (tendsto_weightedTopMeasure_of_decreasing
    hv.locallyBoundedPsh hv.locallyBoundedPsh hP hP hanti hanti hlim hlim χ).neg
  rw [lintegral_test_energy_eq_ofReal hv.locallyBoundedPsh (hv.nonpositive_unitBall hn) χ hnonneg]
  apply le_of_tendsto h
  filter_upwards with j
  rw [← lintegral_test_energy_eq_ofReal (hP j) ((hp j).nonpositive_unitBall hn) χ hnonneg]
  refine le_trans ?_ (hM j)
  apply lintegral_mono_ae
  have ha : ∀ᵐ x ∂topMeasure (hP j), x ∈ complexUnitBall n := by
    rw [ae_iff]
    exact topMeasure_compl (hP j)
  filter_upwards [ha] with x hx
  exact ENNReal.ofReal_le_ofReal (mul_le_of_le_one_left
    (neg_nonneg.mpr ((hp j).nonpositive_unitBall hn x hx)) (hχ x).2)

private theorem maxRealPotential_isE0 (hn : 0 < n)
    {p : ComplexModel n → EReal} (hp : PlurisubharmonicOn p (complexUnitBall n))
    (hpNeg : ∀ x ∈ complexUnitBall n, p x ≤ 0)
    {b : ComplexModel n → ℝ} (hb : IsE0 (complexUnitBall n) b) :
    IsE0 (complexUnitBall n) (maxRealPotential p b) := by
  have hbNeg := hb.nonpositive_unitBall hn
  apply hb.of_ge hn (maxRealPotential_locallyBounded hp hpNeg hb.locallyBoundedPsh hbNeg)
  · intro x hx
    rw [← EReal.coe_le_coe_iff, coe_maxRealPotential ((hp x hx).ne_top), EReal.coe_zero]
    exact max_le (hpNeg x hx) (by exact_mod_cast hbNeg x hx)
  · intro x hx
    rw [← EReal.coe_le_coe_iff, coe_maxRealPotential ((hp x hx).ne_top)]
    exact le_max_right _ _

/-- An antitone sequence in the finite-energy class with uniformly bounded
energy has a finite-energy infimum, whose energy is the supremum of the energies. -/
theorem isE1_iInf_of_antitone (hn : 0 < n)
    {p : ℕ → ComplexModel n → EReal} (hp : ∀ j, IsE1 (complexUnitBall n) (p j))
    (hanti : ∀ x ∈ complexUnitBall n, Antitone (fun j => p j x))
    (hfin : (⨆ j, energy (hp j)) < ⊤) :
    ∃ h : IsE1 (complexUnitBall n) (fun x => ⨅ j, p j x), energy h = ⨆ j, energy (hp j) := by
  let B := complexUnitBall n
  let u (x : ComplexModel n) := ⨅ j, p j x
  let M := ⨆ j, energy (hp j)
  have hu : PlurisubharmonicOn u B :=
    DiscPshOn.plurisubharmonicOn_iInf_of_antitone B.isOpen (fun j => (hp j).1.discPshOn) hanti
  have huNeg (x : ComplexModel n) (hx : x ∈ B) : u x ≤ 0 :=
    (iInf_le (fun j => p j x) 0).trans ((hp 0).nonpositive_unitBall hn x hx)
  let c (j : ℕ) : ℝ := (j : ℝ) + 1
  let b (j : ℕ) (x : ComplexModel n) := c j * ballQuadratic n x
  have hc (j : ℕ) : 0 < c j := by dsimp [c]; positivity
  have hb (j : ℕ) : IsE0 B (b j) := (ballQuadratic_isE0 n).const_mul (hc j)
  let v (j : ℕ) := maxRealPotential u (b j)
  let hv (j : ℕ) := maxRealPotential_isE0 hn hu huNeg (hb j)
  have hvEq (j : ℕ) (x : ComplexModel n) (hx : x ∈ B) :
      (v j x : EReal) = max (u x) (b j x : EReal) :=
    coe_maxRealPotential ((hu x hx).ne_top)
  have hvEnergy (j : ℕ) : boundedEnergy (hv j) ≤ M := by
    let w (i : ℕ) := maxRealPotential (p i) (b j)
    let hw (i : ℕ) := maxRealPotential_isE0 hn (hp i).1 ((hp i).nonpositive_unitBall hn) (hb j)
    have hwEq (i : ℕ) (x : ComplexModel n) (hx : x ∈ B) :
        (w i x : EReal) = max (p i x) (b j x : EReal) :=
      coe_maxRealPotential (((hp i).1 x hx).ne_top)
    have hanti' (x : ComplexModel n) (hx : x ∈ B) : Antitone (fun i => w i x) := by
      intro i l hil
      change w l x ≤ w i x
      rw [← EReal.coe_le_coe_iff, hwEq i x hx, hwEq l x hx]
      exact max_le_max_right _ (hanti x hx hil)
    have hlim' (x : ComplexModel n) (hx : x ∈ B) :
        Tendsto (fun i => w i x) atTop (𝓝 (v j x)) := by
      have h := (tendsto_atTop_iInf (hanti x hx)).max
        (tendsto_const_nhds (x := (b j x : EReal)))
      rw [← hvEq j x hx] at h
      apply ((EReal.tendsto_toReal (EReal.coe_ne_top _) (EReal.coe_ne_bot _)).comp h).congr
      intro i
      change (max (p i x) (b j x : EReal)).toReal = w i x
      rw [← hwEq i x hx, EReal.toReal_coe]
    apply boundedEnergy_le_of_decreasing hn (hv j) hw hanti' hlim'
    intro i
    obtain ⟨h, hh⟩ := (hp i).of_ge hn (hw i).psh
      (fun x hx => by exact_mod_cast (hw i).nonpositive_unitBall hn x hx)
      (fun x hx => by rw [hwEq i x hx]; exact le_max_left _ _)
    have he : energy h = boundedEnergy (hw i) := energy_eq_boundedEnergy hn (hw i)
    exact he.ge.trans (hh.trans (le_iSup (fun j => energy (hp j)) i))
  let approx : E1Approximation B u := {
    term := v
    term_mem := hv
    antitone := fun x hx i j hij => by
      change v j x ≤ v i x
      rw [← EReal.coe_le_coe_iff, hvEq i x hx, hvEq j x hx]
      apply max_le_max_left
      apply EReal.coe_le_coe_iff.mpr
      have hcij : c i ≤ c j := by
        dsimp [c]
        exact add_le_add_left (by exact_mod_cast hij) _
      exact mul_le_mul_of_nonpos_right hcij (ballQuadratic_neg n hx).le
    pointwise := fun x hx => by
      have hbLim : Tendsto (fun j => (b j x : EReal)) atTop (𝓝 ⊥) := by
        have hcTop : Tendsto c atTop atTop :=
          tendsto_atTop_add_const_right atTop (1 : ℝ) (tendsto_natCast_atTop_atTop (R := ℝ))
        exact EReal.tendsto_coe_atBot.comp (hcTop.atTop_mul_const_of_neg (ballQuadratic_neg n hx))
      have hLim : Tendsto (fun j => max (u x) (b j x : EReal)) atTop (𝓝 (u x)) := by
        simpa only [max_eq_left bot_le] using (tendsto_const_nhds (x := u x)).max hbLim
      exact hLim.congr fun j => (hvEq j x hx).symm
    energyBound := (iSup_le hvEnergy).trans_lt hfin }
  let h : IsE1 B u := ⟨hu, ⟨approx⟩⟩
  refine ⟨h, le_antisymm ((energy_eq_iSup hn h approx).le.trans (iSup_le hvEnergy)) ?_⟩
  apply iSup_le
  intro j
  obtain ⟨_, he⟩ := h.of_ge hn (hp j).1 ((hp j).nonpositive_unitBall hn)
    (fun x _ => iInf_le (fun i => p i x) j)
  exact he

end KEBall.Cegrell
