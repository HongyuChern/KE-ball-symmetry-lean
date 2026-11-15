import KEBall.BedfordTaylorScaling
import KEBall.CegrellMeasure

/-!
# Homogeneity of the Cegrell classes, measures and energy
-/

set_option autoImplicit false

open Filter MeasureTheory Set TopologicalSpace
open scoped Distributions ENNReal Topology

namespace KEBall.Cegrell

open BedfordTaylor
open PshLines.FirstPass (ComplexModel)

variable {n : ℕ} {Ω : Opens (ComplexModel n)} {c : ℝ}

theorem IsE0.const_mul {u : ComplexModel n → ℝ} (hu : IsE0 Ω u) (hc : 0 < c) :
    IsE0 Ω (fun x => c * u x) := by
  have hpsh := locallyBoundedPsh_const_mul hu.locallyBoundedPsh hc
  obtain ⟨C, hC⟩ := hu.bounded
  refine ⟨hpsh.1, ⟨c * C, fun x hx => ?_⟩, ?_, ?_⟩
  · rw [abs_mul, abs_of_pos hc]
    exact mul_le_mul_of_nonneg_left (hC x hx) hc.le
  · intro z hz
    simpa only [mul_zero] using (hu.boundary z hz).const_mul c
  · change topMeasure hpsh univ < ⊤
    rw [topMeasure_const_mul hu.locallyBoundedPsh hc, Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hu.finiteMass

theorem boundedEnergy_const_mul {u : ComplexModel n → ℝ} (hu : IsE0 Ω u) (hc : 0 < c) :
    boundedEnergy (hu.const_mul hc) = ENNReal.ofReal (c ^ (n + 1)) * boundedEnergy hu := by
  unfold boundedEnergy
  have hm : topMeasure (hu.const_mul hc).locallyBoundedPsh =
      ENNReal.ofReal (c ^ n) • topMeasure hu.locallyBoundedPsh :=
    topMeasure_const_mul hu.locallyBoundedPsh hc
  rw [hm, lintegral_smul_measure]
  simp_rw [neg_mul_eq_mul_neg, ENNReal.ofReal_mul hc.le]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, smul_eq_mul, ← mul_assoc,
    ← ENNReal.ofReal_mul (pow_nonneg hc.le _), pow_succ]

private noncomputable def E1Approximation.const_mul
    {u : ComplexModel n → EReal} (p : E1Approximation Ω u) (hc : 0 < c) :
    E1Approximation Ω (fun x => (c : EReal) * u x) where
  term := fun j x => c * p.term j x
  term_mem := fun j => (p.term_mem j).const_mul hc
  antitone := fun x hx _ _ h => mul_le_mul_of_nonneg_left (p.antitone x hx h) hc.le
  pointwise := fun x hx => by
    simp only [EReal.coe_mul]
    exact EReal.Tendsto.const_mul (p.pointwise x hx) (Or.inl (EReal.coe_ne_bot c))
      (Or.inl (EReal.coe_ne_top c))
  energyBound := by
    change (⨆ j, boundedEnergy ((p.term_mem j).const_mul hc)) < ⊤
    have he (j : ℕ) := boundedEnergy_const_mul (p.term_mem j) hc
    simp_rw [he]
    rw [← ENNReal.mul_iSup]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top p.energyBound

theorem IsE1.const_mul {u : ComplexModel n → EReal} (hu : IsE1 Ω u) (hc : 0 < c) :
    IsE1 Ω (fun x => (c : EReal) * u x) := by
  obtain ⟨p⟩ := hu.2
  exact ⟨plurisubharmonicOn_const_mul hu.1 hc, ⟨p.const_mul hc⟩⟩

theorem mongeAmpereMeasure_const_mul (hn : 0 < n)
    {u : ComplexModel n → EReal} (hu : IsE1 (complexUnitBall n) u) (hc : 0 < c) :
    mongeAmpereMeasure (hu.const_mul hc) = ENNReal.ofReal (c ^ n) • mongeAmpereMeasure hu := by
  apply ambientMeasure_eq_of_smooth_test (mongeAmpereMeasure_compl (hu.const_mul hc))
  · rw [Measure.smul_apply, mongeAmpereMeasure_compl hu, smul_eq_mul, mul_zero]
  · exact fun _ => mongeAmpereMeasure_finite_on_compact hn (hu.const_mul hc)
  · intro K hK hKB
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (mongeAmpereMeasure_finite_on_compact hn hu hK hKB)
  · intro φ
    obtain ⟨p⟩ := hu.2
    have h₁ := tendsto_mongeAmpereMeasure hn (hu.const_mul hc) (p.const_mul hc)
      φ.continuous φ.hasCompactSupport φ.tsupport_subset
    have h₂ := (tendsto_mongeAmpereMeasure hn hu p φ.continuous φ.hasCompactSupport
      φ.tsupport_subset).const_mul (c ^ n)
    rw [integral_smul_measure, ENNReal.toReal_ofReal (pow_nonneg hc.le _), smul_eq_mul]
    apply tendsto_nhds_unique h₁
    apply h₂.congr
    intro j
    have hM : topMeasure ((p.const_mul hc).term_mem j).locallyBoundedPsh =
        ENNReal.ofReal (c ^ n) • topMeasure (p.term_mem j).locallyBoundedPsh :=
      topMeasure_const_mul (p.term_mem j).locallyBoundedPsh hc
    rw [hM, integral_smul_measure, ENNReal.toReal_ofReal (pow_nonneg hc.le _), smul_eq_mul]

theorem energy_const_mul (hn : 0 < n)
    {u : ComplexModel n → EReal} (hu : IsE1 (complexUnitBall n) u) (hc : 0 < c) :
    energy (hu.const_mul hc) = ENNReal.ofReal (c ^ (n + 1)) * energy hu := by
  have hcE : 0 ≤ (c : EReal) := by exact_mod_cast hc.le
  rw [energy, mongeAmpereMeasure_const_mul hn hu hc, lintegral_smul_measure]
  have hNeg (a : EReal) : -((c : EReal) * a) = (c : EReal) * (-a) := by
    rw [mul_comm (c : EReal) a, ← EReal.neg_mul, mul_comm]
  simp_rw [hNeg, EReal.toENNReal_mul hcE, EReal.real_coe_toENNReal]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, smul_eq_mul, ← mul_assoc,
    ← ENNReal.ofReal_mul (pow_nonneg hc.le _), pow_succ, energy]

#print axioms mongeAmpereMeasure_const_mul
#print axioms energy_const_mul

end KEBall.Cegrell
