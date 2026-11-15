import KEBall.CegrellExponentialConvergence

/-!
# Scaling and coercivity of the finite-energy functional
-/

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace KEBall.MoserTrudinger

open BedfordTaylor Cegrell
open PshLines.FirstPass (ComplexModel)

variable {n : ℕ}

/-- A finite uniform upper bound at a larger coupling implies coercivity
at the smaller coupling, with the energy of the actual Cegrell measure. -/
theorem finiteEnergyFunctional_coercive_of_bound (hn : 0 < n) {α β C : ℝ}
    (hα : 0 < α) (hαβ : α < β)
    (hBound : ∀ {v : ComplexModel n → EReal} (hv : IsE1 (complexUnitBall n) v),
      finiteEnergyFunctional β hv ≤ (C : EReal))
    {u : ComplexModel n → EReal} (hu : IsE1 (complexUnitBall n) u) :
    exponentialIntegral α u < ⊤ ∧
      finiteEnergyFunctional α hu ≤
        ((C / (α / β) - (1 - (α / β) ^ n) * ((energy hu).toReal / (n + 1 : ℝ)) : ℝ) : EReal) := by
  have hβ := hα.trans hαβ
  let c := α / β
  have hc : 0 < c := div_pos hα hβ
  let q : ComplexModel n → EReal := fun x => (c : EReal) * u x
  let hq : IsE1 (complexUnitBall n) q := hu.const_mul hc
  have h := hBound hq
  have hCβ : c * β = α := div_mul_cancel₀ _ hβ.ne'
  have hEq : exponentialIntegral β q = exponentialIntegral α u := by
    change exponentialIntegral β (fun x => (c : EReal) * u x) = _
    rw [exponentialIntegral_const_mul u c β, hCβ]
  have hfinite : exponentialIntegral α u ≠ ⊤ := by
    intro htop
    rw [finiteEnergyFunctional, hEq, if_pos htop] at h
    exact (EReal.coe_ne_top C (top_le_iff.mp h)).elim
  refine ⟨hfinite.lt_top, ?_⟩
  have hEn : (energy hq).toReal = c ^ (n + 1) * (energy hu).toReal := by
    rw [energy_const_mul hn hu hc, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (pow_nonneg hc.le _)]
  rw [finiteEnergyFunctional, hEq, if_neg hfinite, EReal.coe_le_coe_iff, hEn] at h
  rw [finiteEnergyFunctional, if_neg hfinite, EReal.coe_le_coe_iff]
  have heq (A B : ℝ) :
      c * (A / α - B / (n + 1 : ℝ)) =
        (A / β - c ^ (n + 1) * B / (n + 1 : ℝ)) -
          c * ((1 - c ^ n) * (B / (n + 1 : ℝ))) := by
    rw [pow_succ]
    dsimp [c]
    field_simp
    ring
  change Real.log (exponentialIntegral α u).toReal / α - (energy hu).toReal / (n + 1 : ℝ) ≤ _
  apply le_of_mul_le_mul_left _ hc
  rw [heq, mul_sub, mul_div_cancel₀ _ hc.ne']
  linarith

theorem coercivity_coefficient_pos (hn : 0 < n) {α β : ℝ}
    (hα : 0 < α) (hαβ : α < β) :
    0 < 1 - (α / β) ^ n := by
  apply sub_pos.mpr
  exact pow_lt_one₀ (div_nonneg hα.le (hα.trans hαβ).le)
    ((div_lt_one (hα.trans hαβ)).mpr hαβ) hn.ne'

end KEBall.MoserTrudinger
