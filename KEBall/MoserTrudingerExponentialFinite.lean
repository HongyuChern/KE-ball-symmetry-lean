import KEBall.MoserTrudingerWeakAttainmentUnconditional

/-! Finite exponential integrals for the entire actual Cegrell E1 class. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped ENNReal
namespace KEBall.MoserTrudinger
open BedfordTaylor Cegrell
open PshLines.FirstPass (ComplexModel)

theorem exponentialIntegral_lt_top_of_E1_unconditional {n : ℕ} (hn : 0<n)
    {u : ComplexModel n → EReal} (hu : IsE1 (complexUnitBall n) u)
    {γ : ℝ} (hγ : 0<γ) : exponentialIntegral γ u < ⊤ := by
  have hOne : (1 : ℝ)<(n+1 : ℝ) := by
    have hnR : (0 : ℝ)<n := by exact_mod_cast hn
    linarith
  obtain ⟨C,hC⟩ := exists_finiteEnergyFunctional_bound_unconditional n hn 1 zero_lt_one hOne
  have h := hC _ (hu.const_mul hγ)
  have hEq : exponentialIntegral 1 (fun x => (γ : EReal)*u x)=exponentialIntegral γ u := by
    rw [exponentialIntegral_const_mul,mul_one]
  apply lt_top_iff_ne_top.mpr
  intro hTop
  rw [finiteEnergyFunctional,hEq,if_pos hTop] at h
  exact EReal.coe_ne_top C (top_le_iff.mp h)

theorem exponentialIntegral_one_lt_top_of_E1_unconditional {n : ℕ} (hn : 0<n)
    {u : ComplexModel n → EReal} (hu : IsE1 (complexUnitBall n) u) :
    exponentialIntegral 1 u < ⊤ :=
  exponentialIntegral_lt_top_of_E1_unconditional hn hu zero_lt_one

end KEBall.MoserTrudinger
