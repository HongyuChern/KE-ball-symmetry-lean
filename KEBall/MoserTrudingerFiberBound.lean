import KEBall.MoserTrudingerSmoothToFiniteEnergy

/-!
# Converting a functional bound to the Euclidean-volume estimate on fibers
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Metric Set
open scoped ENNReal

namespace KEBall.MoserTrudinger

open BedfordTaylor Cegrell
open PshLines.FirstPass (ComplexModel)

theorem exponentialIntegral_real_eq_lintegral_volume {n : ℕ} (γ : ℝ) (u : ComplexModel n → ℝ) :
    exponentialIntegral γ (fun z => (u z : EReal)) =
      ENNReal.ofReal ((n.factorial : ℝ) / Real.pi ^ n) *
        ∫⁻ z in complexUnitBall n, ENNReal.ofReal (Real.exp (-(γ * u z))) := by
  unfold exponentialIntegral volume0
  rw [Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul]
  congr 1
  let e := complexCoordinates n
  let f (z : ComplexModel n) := ENNReal.ofReal (Real.exp (-(γ * u z)))
  calc
    _ = ∫⁻ x in unitBall n, f (e x) := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem (show MeasurableSet (unitBall n) from measurableSet_ball)] with x hx
      rw [finiteEnergyWeight, if_pos hx, ← expNeg_const_mul, ← EReal.coe_mul, expNeg_coe]
    _ = _ := by
      have h := (complexCoordinates_measurePreserving n).setLIntegral_comp_preimage_emb
        e.toHomeomorph.toMeasurableEquiv.measurableEmbedding f (complexUnitBall n : Set (ComplexModel n))
      rw [preimage_complexUnitBall] at h
      exact h

/-- A finite-energy functional bound at parameter γ yields the unscaled
Euclidean-volume bound on every bounded Cegrell potential. -/
theorem lintegral_exp_real_le_of_functionalBound {n : ℕ} (hn : 0 < n) {γ C : ℝ} (hγ : 0 < γ)
    (hBound : ∀ (v : ComplexModel n → EReal) (hv : IsE1 (complexUnitBall n) v),
      finiteEnergyFunctional γ hv ≤ (C : EReal))
    (u : ComplexModel n → ℝ) (hu : IsE0 (complexUnitBall n) u) :
    (∫⁻ z in complexUnitBall n, ENNReal.ofReal (Real.exp (-u z))) ≤
      ENNReal.ofReal ((Real.pi ^ n / (n.factorial : ℝ)) * Real.exp (γ * C)) *
        ENNReal.ofReal (Real.exp (γ⁻¹ ^ n * (boundedEnergy hu).toReal / (n + 1 : ℝ))) := by
  let c := γ⁻¹
  let k := (n.factorial : ℝ) / Real.pi ^ n
  let v (z : ComplexModel n) := c * u z
  have hc : 0 < c := inv_pos.mpr hγ
  have hk : 0 < k := div_pos (by exact_mod_cast Nat.factorial_pos n) (pow_pos Real.pi_pos n)
  let hv : IsE0 (complexUnitBall n) v := hu.const_mul hc
  have hI := (finiteEnergyFunctional_le_iff_exponentialIntegral_le hn hγ hv.isE1).mp
    (hBound _ hv.isE1)
  rw [energy_eq_boundedEnergy hn hv, boundedEnergy_const_mul hu hc, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (pow_nonneg hc.le _)] at hI
  have hPower : γ * c ^ (n + 1) = c ^ n := by
    calc
      _ = (γ * c) * c ^ n := by rw [pow_succ]; ring
      _ = _ := by rw [show γ * c = 1 from mul_inv_cancel₀ hγ.ne', one_mul]
  have hExponent : γ * (C + c ^ (n + 1) * (boundedEnergy hu).toReal / (n + 1 : ℝ)) =
      γ * C + c ^ n * (boundedEnergy hu).toReal / (n + 1 : ℝ) := by
    rw [mul_add, mul_div_assoc, ← mul_assoc, hPower]
    ring
  rw [hExponent, Real.exp_add, ENNReal.ofReal_mul (Real.exp_nonneg _),
    exponentialIntegral_real_eq_lintegral_volume] at hI
  have hInt : (∫⁻ z in complexUnitBall n, ENNReal.ofReal (Real.exp (-(γ * v z)))) =
      ∫⁻ z in complexUnitBall n, ENNReal.ofReal (Real.exp (-u z)) := by
    apply lintegral_congr
    intro z
    change ENNReal.ofReal (Real.exp (-(γ * (c * u z)))) = _
    rw [← mul_assoc, show γ * c = 1 from mul_inv_cancel₀ hγ.ne', one_mul]
  rw [hInt] at hI
  let J := ∫⁻ z in complexUnitBall n, ENNReal.ofReal (Real.exp (-u z))
  have hOne : ENNReal.ofReal k⁻¹ * ENNReal.ofReal k = 1 := by
    rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hk.le), inv_mul_cancel₀ hk.ne', ENNReal.ofReal_one]
  calc
    J = ENNReal.ofReal k⁻¹ * (ENNReal.ofReal k * J) := by rw [← mul_assoc, hOne, one_mul]
    _ ≤ ENNReal.ofReal k⁻¹ *
        (ENNReal.ofReal (Real.exp (γ * C)) * ENNReal.ofReal
          (Real.exp (c ^ n * (boundedEnergy hu).toReal / (n + 1 : ℝ)))) :=
      mul_le_mul_right hI _
    _ = _ := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.mpr hk.le)]
      simp only [k, inv_div, c]

end KEBall.MoserTrudinger
