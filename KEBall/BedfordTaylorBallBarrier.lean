import KEBall.BedfordTaylorSmoothMax
import PshLines.DistributionRegularization

/-!
# A common quadratic boundary barrier on a ball
-/

set_option autoImplicit false

open Metric Set TopologicalSpace
open scoped ContDiff

namespace KEBall.BedfordTaylor

open PshLines
open PshLines.FirstPass (ComplexModel)
open PshLines.FirstPass.MongeAmpere (IsSmoothPshOn isSmoothPshOn_of_psh)

def ballDomain {n : ℕ} (z : ComplexModel n) (r : ℝ) : Opens (ComplexModel n) :=
  ⟨ball z r, isOpen_ball⟩

theorem exists_quadratic_boundary_barrier {n : ℕ} (z : ComplexModel n)
    {r₀ r C : ℝ} (hr₀ : 0 ≤ r₀) (hr : r₀ < r) (hC : 0 ≤ C) :
    ∃ b : ComplexModel n → ℝ, IsSmoothPshOn (ballDomain z r) b ∧
      (∀ x ∈ closedBall z r₀, b x ≤ -C - 1) ∧
      ∃ K : Set (ComplexModel n), IsCompact K ∧ K ⊆ ball z r ∧
        ∀ x ∈ ball z r \ K, C + 1 ≤ b x := by
  have hrpos : 0 < r := hr₀.trans_lt hr
  have hdiff : 0 < r ^ 2 - r₀ ^ 2 := by nlinarith
  let A := (2 * C + 4) / (r ^ 2 - r₀ ^ 2)
  have hA : 0 < A := div_pos (by linarith) hdiff
  have hAeq : A * (r ^ 2 - r₀ ^ 2) = 2 * C + 4 := by
    dsimp [A]
    exact div_mul_cancel₀ _ hdiff.ne'
  have hAsq : 1 < A * r ^ 2 := by
    nlinarith [mul_nonneg hA.le (sq_nonneg r₀)]
  let q : ComplexModel n → ℝ := fun x => ‖x - z‖ ^ 2
  let b : ComplexModel n → ℝ := A • q + fun _ => C + 2 - A * r ^ 2
  have hq : ContDiff ℝ ∞ q := (contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)
  have hb : ContDiff ℝ ∞ b := (hq.const_smul A).add contDiff_const
  have hL (x v : ComplexModel n) : 0 ≤ leviForm b x v := by
    have hn : (2 : ℕ∞ω) ≤ ∞ := ENat.natCast_le_of_coe_top_le_withTop le_rfl 2
    have h₁ : ContDiffAt ℝ 2 (A • q) x := ((hq.const_smul A).of_le hn).contDiffAt
    rw [show b = A • q + (fun _ => C + 2 - A * r ^ 2) from rfl,
      leviForm_add h₁ contDiffAt_const, leviForm_smul (hq.of_le hn).contDiffAt,
      show leviForm (fun _ : ComplexModel n => C + 2 - A * r ^ 2) x v = 0 by
        simp [leviForm], add_zero]
    have heq : leviForm q x v = leviForm (fun y : ComplexModel n => ‖y‖ ^ 2) (x - z) v :=
      leviForm_comp_sub (fun y : ComplexModel n => ‖y‖ ^ 2) z x v
    rw [heq]
    exact mul_nonneg hA.le (leviForm_norm_sq_nonneg _ _)
  have hpsh := plurisubharmonicOn_of_levi_nonneg
    (hb.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) (isOpen_ball : IsOpen (ball z r))
    (fun x _ v => hL x v)
  have hbEq (x : ComplexModel n) : b x = A * (dist x z ^ 2 - r ^ 2) + C + 2 := by
    simp only [b, q, Pi.add_apply, Pi.smul_apply, smul_eq_mul, dist_eq_norm]
    ring
  refine ⟨b, isSmoothPshOn_of_psh hb.contDiffOn hpsh, ?_, ?_⟩
  · intro x hx
    have hd : dist x z ≤ r₀ := hx
    have hsq : dist x z ^ 2 ≤ r₀ ^ 2 := by nlinarith [dist_nonneg (x := x) (y := z)]
    rw [hbEq]
    nlinarith [mul_le_mul_of_nonneg_left hsq hA.le]
  · let R := Real.sqrt (r ^ 2 - A⁻¹)
    have hpositive : A⁻¹ < r ^ 2 := by
      rw [← one_div, div_lt_iff₀ hA]
      linarith
    have hR : R ^ 2 = r ^ 2 - A⁻¹ := Real.sq_sqrt (sub_nonneg.mpr hpositive.le)
    have hRnonneg : 0 ≤ R := Real.sqrt_nonneg _
    have hRlt : R < r := by
      nlinarith [inv_pos.mpr hA]
    refine ⟨closedBall z R, isCompact_closedBall _ _, closedBall_subset_ball hRlt, ?_⟩
    intro x hx
    have hRx : R < dist x z := lt_of_not_ge hx.2
    have hsq : R ^ 2 ≤ dist x z ^ 2 := by nlinarith
    rw [hbEq]
    have hmul := mul_le_mul_of_nonneg_left hsq hA.le
    rw [hR, mul_sub, mul_inv_cancel₀ hA.ne'] at hmul
    linarith

end KEBall.BedfordTaylor
