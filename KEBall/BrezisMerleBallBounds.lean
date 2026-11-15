import KEBall.BrezisMerleFiberStep
import KEBall.MoserTrudingerFiberBound
import KEBall.MoserTrudingerDiscFiniteEnergy
import KEBall.BedfordTaylorBallDilation

/-!
# Mass bounds obtained from a lower-dimensional functional estimate
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Metric Set TopologicalSpace
open scoped ContDiff ENNReal

namespace KEBall.BrezisMerle

open BedfordTaylor Cegrell MoserTrudinger
open PshLines.FirstPass (ComplexModel)
open PshLines.FirstPass.MongeAmpere (IsSmoothPshOn isSmoothPshOn_of_psh smoothDensity)

private theorem exists_lintegral_exp_smallBall_le_of_fiberFunctionalBound {n : ℕ} (hn : 0 < n)
    {γ C : ℝ} (hγ : 0 < γ)
    (hFiber : ∀ (v : ComplexModel n → EReal) (hv : IsE1 (complexUnitBall n) v),
      finiteEnergyFunctional γ hv ≤ (C : EReal))
    {m : ℝ≥0∞} (hm : ENNReal.ofReal (γ⁻¹ ^ n / (n + 1 : ℝ)) * m < 1) :
    ∃ K : ℝ≥0∞, K ≠ ⊤ ∧
      ∀ (R : ℝ) (u : ComplexModel (n + 1) → ℝ) (hu : IsE0 (ballDomain 0 R) u),
        0 < R → R < 1 → ContDiff ℝ 2 u →
        (∀ x ∈ ball 0 R, u x ≤ 0) → (∀ x ∈ sphere 0 R, u x = 0) →
        topMeasure hu.locallyBoundedPsh univ ≤ m →
        (∫⁻ x in ball 0 R, ENNReal.ofReal (Real.exp (-u x))) ≤ K := by
  let a := γ⁻¹ ^ n
  let D := ENNReal.ofReal ((Real.pi ^ n / (n.factorial : ℝ)) * Real.exp (γ * C))
  let s := ENNReal.ofReal (a / (n + 1 : ℝ)) * m
  have hs : s < 1 := hm
  have hsFin : s ≠ ⊤ := (hs.trans ENNReal.one_lt_top).ne
  have hsR : s.toReal < 1 := by
    simpa only [ENNReal.toReal_one] using (ENNReal.toReal_lt_toReal hsFin ENNReal.one_ne_top).2 hs
  let t := (s.toReal + 1) / 2
  have ht₀ : 0 < t := by dsimp [t]; positivity
  have ht₁ : t < 1 := by dsimp [t]; linarith only [hsR]
  have hst : s ≤ ENNReal.ofReal t := by
    rw [← ENNReal.ofReal_toReal hsFin]
    exact ENNReal.ofReal_le_ofReal (by dsimp [t]; linarith only [hsR])
  refine ⟨D * ENNReal.ofReal (4 * Real.pi / (1 - t)),
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top, ?_⟩
  intro R u hu hR hR₁ hSmooth hneg hBoundary hMass
  apply lintegral_exp_ball_le_of_fiberEnergyBound hn (pow_pos (inv_pos.mpr hγ) _) ENNReal.ofReal_ne_top
    (lintegral_exp_real_le_of_functionalBound hn hγ hFiber) hR hR₁ hu hSmooth hneg hBoundary ht₀ ht₁
  exact (mul_le_mul_right hMass _).trans hst

/-- A subcritical functional estimate in dimension n gives a uniform
mass bound on the smooth unit ball in dimension n+1. -/
theorem exists_lintegral_exp_unitBall_le_of_fiberFunctionalBound {n : ℕ} (hn : 0 < n)
    {γ C : ℝ} (hγ : 0 < γ)
    (hFiber : ∀ (v : ComplexModel n → EReal) (hv : IsE1 (complexUnitBall n) v),
      finiteEnergyFunctional γ hv ≤ (C : EReal))
    {m : ℝ≥0∞} (hm : ENNReal.ofReal (γ⁻¹ ^ n / (n + 1 : ℝ)) * m < 1) :
    ∃ K : ℝ≥0∞, K ≠ ⊤ ∧
      ∀ (u : ComplexModel (n + 1) → ℝ) (hu : IsE0 (complexUnitBall (n + 1)) u),
        ContDiff ℝ ∞ u → (∀ x ∈ sphere 0 1, u x = 0) →
        topMeasure hu.locallyBoundedPsh univ ≤ m →
        (∫⁻ x in complexUnitBall (n + 1), ENNReal.ofReal (Real.exp (-u x))) ≤ K := by
  obtain ⟨D, hD, hSmall⟩ := exists_lintegral_exp_smallBall_le_of_fiberFunctionalBound hn hγ hFiber hm
  let K := ENNReal.ofReal ((2 : ℝ) ^ (2 * (n + 1))) * D
  refine ⟨K, ENNReal.mul_ne_top ENNReal.ofReal_ne_top hD, ?_⟩
  intro u hu hSmooth hBoundary hMass
  let v (x : ComplexModel (n + 1)) := u ((2 : ℝ) • x)
  let U := ballDomain (0 : ComplexModel (n + 1)) (1 / 2)
  have huS : IsSmoothPshOn (ballDomain (0 : ComplexModel (n + 1)) (2 * (1 / 2))) u := by
    rw [show (2 : ℝ) * (1 / 2) = 1 by norm_num]
    exact isSmoothPshOn_of_psh hSmooth.contDiffOn hu.psh
  have hvS : IsSmoothPshOn U v := isSmoothPshOn_ball_dilate hSmooth (by norm_num) huS
  have hvC : ContDiff ℝ ∞ v := hSmooth.comp (contDiff_id.const_smul (2 : ℝ))
  have hvBoundary (x : ComplexModel (n + 1)) (hx : x ∈ sphere 0 (1 / 2)) : v x = 0 := by
    apply hBoundary
    apply mem_sphere_zero_iff_norm.mpr
    rw [norm_smul, Real.norm_of_nonneg (by norm_num : 0 ≤ (2 : ℝ)), mem_sphere_zero_iff_norm.mp hx]
    norm_num
  have hvneg (x : ComplexModel (n + 1)) (hx : x ∈ ball 0 (1 / 2)) : v x ≤ 0 := by
    apply hu.nonpositive_unitBall (by omega : 0 < n + 1)
    apply mem_ball_zero_iff.mpr
    rw [norm_smul, Real.norm_of_nonneg (by norm_num : 0 ≤ (2 : ℝ))]
    have hx' := mem_ball_zero_iff.mp hx
    linarith only [hx']
  have hComp : IsCompact (closure (U : Set (ComplexModel (n + 1)))) := by
    change IsCompact (closure (ball (0 : ComplexModel (n + 1)) (1 / 2)))
    rw [closure_ball _ (by norm_num : (1 / 2 : ℝ) ≠ 0)]
    exact isCompact_closedBall _ _
  have hv : IsE0 U v := isE0_of_smoothOn_closure (W := ⊤) hComp (by simp) hvS hvC.contDiffOn (by
    intro x hx
    change x ∈ frontier (ball (0 : ComplexModel (n + 1)) (1 / 2)) at hx
    rw [frontier_ball _ (by norm_num : (1 / 2 : ℝ) ≠ 0)] at hx
    exact hvBoundary x hx)
  have hvMass : topMeasure hv.locallyBoundedPsh univ ≤ m := by
    have h := topMeasure_univ_ball_dilate hSmooth (by norm_num : 0 < (2 : ℝ)) huS
    rw [topMeasure_univ_eq_lintegral_smoothDensity huS] at h
    change _ = (∫⁻ x in ball (0 : ComplexModel (n + 1)) (2 * (1 / 2)), ENNReal.ofReal (smoothDensity u x)) at h
    rw [show (2 : ℝ) * (1 / 2) = 1 by norm_num] at h
    have huS₁ : IsSmoothPshOn (complexUnitBall (n + 1)) u :=
      isSmoothPshOn_of_psh hSmooth.contDiffOn hu.psh
    exact h.trans_le ((topMeasure_univ_eq_lintegral_smoothDensity huS₁).symm.trans_le hMass)
  have hI := hSmall (1 / 2) v hv (by norm_num) (by norm_num)
    (hvC.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) hvneg hvBoundary hvMass
  have hDil := lintegral_smul_ball (volume : Measure (ComplexModel (n + 1)))
    (fun x => ENNReal.ofReal (Real.exp (-u x))) (R := 1 / 2) (by norm_num : 0 < (2 : ℝ))
  rw [finrank_complexModel_real, show (2 : ℝ) * (1 / 2) = 1 by norm_num] at hDil
  calc
    _ = ENNReal.ofReal ((2 : ℝ) ^ (2 * (n + 1))) *
        ∫⁻ x in ball (0 : ComplexModel (n + 1)) (1 / 2), ENNReal.ofReal (Real.exp (-v x)) := hDil.symm
    _ ≤ K := mul_le_mul_right hI _

/-- The complex two-dimensional mass bound holds below mass four.
The fiber estimate is the proved finite-energy estimate on the disk. -/
theorem exists_lintegral_exp_unitBall_two_le_of_mass_lt_four {m : ℝ≥0∞} (hm : m < 4) :
    ∃ K : ℝ≥0∞, K ≠ ⊤ ∧
      ∀ (u : ComplexModel 2 → ℝ) (hu : IsE0 (complexUnitBall 2) u),
        ContDiff ℝ ∞ u → (∀ x ∈ sphere 0 1, u x = 0) →
        topMeasure hu.locallyBoundedPsh univ ≤ m →
        (∫⁻ x in complexUnitBall 2, ENNReal.ofReal (Real.exp (-u x))) ≤ K := by
  have hmFin : m ≠ ⊤ := (hm.trans ENNReal.ofNat_lt_top).ne
  have hmReal : m.toReal < 4 := by
    simpa only [ENNReal.toReal_ofNat] using (ENNReal.toReal_lt_toReal hmFin ENNReal.ofNat_ne_top).2 hm
  let γ := (m.toReal / 2 + 2) / 2
  have hγ : 0 < γ := by dsimp [γ]; positivity
  have hγ₂ : γ < 2 := by dsimp [γ]; linarith only [hmReal]
  have hT : ENNReal.ofReal (γ⁻¹ ^ (1 : ℕ) / ((1 : ℕ) + 1 : ℝ)) * m < 1 := by
    rw [← ENNReal.ofReal_toReal hmFin, ← ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_lt_one]
    simp only [pow_one, Nat.cast_one, one_add_one_eq_two]
    have he : γ⁻¹ / 2 * m.toReal = m.toReal / (2 * γ) := by field_simp
    rw [he, div_lt_iff₀ (by positivity)]
    dsimp only [γ]
    linarith only [hmReal]
  exact exists_lintegral_exp_unitBall_le_of_fiberFunctionalBound (n := 1) (by decide) hγ
    (fun _ hv => finiteEnergyFunctional_disc_le hγ hγ₂ hv) hT

end KEBall.BrezisMerle
