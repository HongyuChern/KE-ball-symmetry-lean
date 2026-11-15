import KEBall.CegrellSmoothFunctional

/-!
# Corollary 1.3 on the actual finite-energy class

The passage from smooth subcritical attainment to the critical
inequality is separated from the variational existence theorem.
Sharpness on the finite-energy class follows from its radial members.
-/

set_option autoImplicit false

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace KEBall.MoserTrudinger

open BedfordTaylor Cegrell
open PshLines.FirstPass (ComplexModel)

variable {n : ℕ}

/-- Smooth attainment of the finite-energy functional in the
subcritical range, in the normalization used by the paper. -/
def SubcriticalSmoothAttainment (n : ℕ) : Prop :=
  ∀ γ ∈ Ioo (0 : ℝ) (n + 1 : ℝ), ∃ v : E n → ℝ,
    ∃ hv : Paper20261016.IsMeanFieldSolution n γ v,
      ∀ {u : ComplexModel n → EReal} (hu : IsE1 (complexUnitBall n) u),
        finiteEnergyFunctional γ hu ≤ finiteEnergyFunctional γ (meanFieldSolution_memE0 hv).isE1

private theorem energy_scaled_toReal (hn : 0 < n) {u : ComplexModel n → EReal}
    (hu : IsE1 (complexUnitBall n) u) :
    (energy (hu.const_mul (c := ((n + 1 : ℝ)⁻¹)) (inv_pos.mpr (by positivity)))).toReal =
      energyCoefficient n * (energy hu).toReal := by
  have hc : 0 < (n + 1 : ℝ)⁻¹ := inv_pos.mpr (by positivity)
  rw [energy_const_mul hn hu hc, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (pow_nonneg hc.le _), energyCoefficient, inv_pow]

/-- Smooth subcritical attainment implies the critical integrability
and inequality for every finite-energy potential. -/
theorem critical_bound_of_subcriticalSmoothAttainment (hn : 2 ≤ n)
    (hmax : SubcriticalSmoothAttainment n)
    {u : ComplexModel n → EReal} (hu : IsE1 (complexUnitBall n) u) :
    exponentialIntegral 1 u < ⊤ ∧
      Real.log (exponentialIntegral 1 u).toReal ≤
        energyCoefficient n * (energy hu).toReal + harmonicConstant n := by
  have hn₀ : 0 < n := by omega
  have hcoef : 0 ≤ energyCoefficient n := by unfold energyCoefficient; positivity
  have hE : 0 ≤ energyCoefficient n * (energy hu).toReal :=
    mul_nonneg hcoef ENNReal.toReal_nonneg
  have h := critical_log_bound_of_meanField_maximizers hn (finiteEnergyWeight u)
    (finiteEnergyWeight_measurable hu) (finiteEnergyWeight_ge_one hn₀ hu) hE ?_
  · simpa only [exponentialIntegral, ENNReal.rpow_one] using h
  · intro t ht
    let γ : ℝ := (n + 1 : ℝ) * t
    have hγ₀ : 0 < γ := mul_pos (by positivity) ht.1
    have hγ₁ : γ < (n + 1 : ℝ) := by
      dsimp [γ]
      exact mul_lt_of_lt_one_right (by positivity) ht.2
    obtain ⟨v, hv, hDom⟩ := hmax γ ⟨hγ₀, hγ₁⟩
    refine ⟨v, hv, ?_⟩
    let c : ℝ := (n + 1 : ℝ)⁻¹
    have hc : 0 < c := inv_pos.mpr (by positivity)
    let q : ComplexModel n → EReal := fun x => (c : EReal) * u x
    let hq : IsE1 (complexUnitBall n) q := hu.const_mul hc
    have hVariational := hDom hq
    rw [finiteEnergyFunctional_realModelPotential hn₀ hv.2.1 (meanFieldSolution_memE0 hv) γ]
      at hVariational
    have hA : exponentialIntegral γ q ≠ ⊤ := by
      intro he
      rw [finiteEnergyFunctional, if_pos he] at hVariational
      exact (EReal.coe_ne_top _ (top_le_iff.mp hVariational)).elim
    rw [finiteEnergyFunctional, if_neg hA, EReal.coe_le_coe_iff] at hVariational
    have hA₀ : 0 < (exponentialIntegral γ q).toReal :=
      ENNReal.toReal_pos (zero_lt_one.trans_le (exponentialIntegral_ge_one hn₀ hq hγ₀.le)).ne' hA
    have hEnergy : (energy hq).toReal = energyCoefficient n * (energy hu).toReal :=
      energy_scaled_toReal hn₀ hu
    have hCγ : c * γ = t := by
      dsimp [c, γ]
      rw [← mul_assoc, inv_mul_cancel₀ (by positivity : (n + 1 : ℝ) ≠ 0), one_mul]
    have hExp : exponentialIntegral γ q = exponentialIntegral t u := by
      rw [show q = (fun x => (c : EReal) * u x) from rfl,
        exponentialIntegral_const_mul u c γ, hCγ]
    have hLog : Real.log (exponentialIntegral γ q).toReal ≤
        t * (energyCoefficient n * (energy hu).toReal) +
          (Real.log (normalizingIntegral γ v) - t * smoothEnergy v) := by
      have heq (a : ℝ) : γ * (a / (n + 1 : ℝ)) = t * a := by
        dsimp [γ]
        field_simp
      have hmul := mul_le_mul_of_nonneg_left hVariational hγ₀.le
      simp only [mul_sub, heq] at hmul
      rw [mul_div_cancel₀ _ hγ₀.ne', mul_div_cancel₀ _ hγ₀.ne', hEnergy] at hmul
      linarith
    change exponentialIntegral t u ≤ _
    rw [← hExp, ← ENNReal.ofReal_toReal hA, ← Real.exp_log hA₀]
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hLog)

private theorem log_exponentialIntegral_one_realModel (hn : 0 < n) {v : E n → ℝ}
    (hv : SmoothNear (closedUnitBall n) v) :
    Real.log (exponentialIntegral 1 (realModelPotential v)).toReal = logIntegral v := by
  rw [exponentialIntegral_realModelPotential hn hv 1]
  simp only [normalizingIntegral, logIntegral, neg_mul, one_mul]
  rw [ENNReal.toReal_ofReal (integral_nonneg fun _ => (Real.exp_pos _).le)]

/-- Any additive constant valid with the stated energy coefficient on
the full finite-energy class is at least the harmonic number. -/
theorem harmonicConstant_le_of_finiteEnergy_bound (hn : 2 ≤ n) {C : ℝ}
    (hbound : ∀ {u : ComplexModel n → EReal} (hu : IsE1 (complexUnitBall n) u),
      Real.log (exponentialIntegral 1 u).toReal ≤
        energyCoefficient n * (energy hu).toReal + C) :
    harmonicConstant n ≤ C := by
  apply harmonicConstant_le_of_bound hn
  intro t ht
  let v := testPotential n t
  have hv := (testPotential_admissible hn ht.1 ht.2).1
  have hE0 := testPotential_isE0 hn ht.1 ht.2
  have h := hbound (u := realModelPotential v) hE0.isE1
  rwa [log_exponentialIntegral_one_realModel (by omega) hv,
    energy_realModelPotential (by omega) hv hE0] at h

/-- Any smaller energy coefficient fails for some finite-energy
potential, for every fixed finite additive constant. -/
theorem finiteEnergy_counterexample_of_lt_energyCoefficient (hn : 2 ≤ n)
    {c : ℝ} (hc : c < energyCoefficient n) (C : ℝ) :
    ∃ u : ComplexModel n → EReal, ∃ hu : IsE1 (complexUnitBall n) u,
      exponentialIntegral 1 u < ⊤ ∧
      c * (energy hu).toReal + C < Real.log (exponentialIntegral 1 u).toReal := by
  obtain ⟨t, ht, hcounter⟩ := exists_test_violating_bound hn hc C
  let v := testPotential n t
  have hv := (testPotential_admissible hn ht.1 ht.2).1
  have hE0 := testPotential_isE0 hn ht.1 ht.2
  refine ⟨realModelPotential v, hE0.isE1, ?_, ?_⟩
  · rw [exponentialIntegral_realModelPotential (by omega) hv 1]
    exact ENNReal.ofReal_lt_top
  · rwa [log_exponentialIntegral_one_realModel (by omega) hv,
      energy_realModelPotential (by omega) hv hE0]

#print axioms critical_bound_of_subcriticalSmoothAttainment
#print axioms harmonicConstant_le_of_finiteEnergy_bound
#print axioms finiteEnergy_counterexample_of_lt_energyCoefficient

end KEBall.MoserTrudinger
