import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# The quadratic expansion from differentiability of the gradient
-/

set_option autoImplicit false

open Filter Metric Set
open scoped Topology

namespace KEBall

/-- Differentiability of the gradient at one point gives a quadratic
expansion of the function there, with no continuity of the second
derivative required. -/
theorem eventually_quadratic_remainder_of_hasFDerivAt_fderiv {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {u : E → ℝ} {W : Set E} {x : E}
    (hW : IsOpen W) (hx : x ∈ W) (hu : ∀ y ∈ W, DifferentiableAt ℝ u y)
    {A : E →L[ℝ] E →L[ℝ] ℝ} (hA : HasFDerivAt (fderiv ℝ u) A x)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ h in 𝓝 (0 : E),
      ‖u (x + h) - u x - fderiv ℝ u x h - A h h / 2‖ ≤ ε * ‖h‖ ^ 2 := by
  have hlin : ∀ᶠ h in 𝓝 (0 : E),
      ‖fderiv ℝ u (x + h) - fderiv ℝ u x - A h‖ ≤ ε * ‖h‖ :=
    (Asymptotics.isLittleO_iff.mp (hasFDerivAt_iff_isLittleO_nhds_zero.mp hA)) hε
  have hdom : ∀ᶠ h : E in 𝓝 0, x + h ∈ W := by
    have hc : Continuous (fun h : E => x + h) := continuous_const.add continuous_id
    have hx' : x + (0 : E) ∈ W := by rwa [add_zero]
    exact hc.continuousAt (x := 0) (hW.mem_nhds hx')
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hdom.and hlin)
  filter_upwards [ball_mem_nhds (0 : E) hr] with h hh
  have hhr : ‖h‖ < r := by simpa only [mem_ball, dist_zero_right] using hh
  let g (t : ℝ) := u (x + t • h) - u x - t * fderiv ℝ u x h - t ^ 2 * (A h h / 2)
  have htb (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : t • h ∈ ball (0 : E) r := by
    rw [mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
    exact (mul_le_of_le_one_left (norm_nonneg h) ht.2).trans_lt hhr
  have hg (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt g ((fderiv ℝ u (x + t • h) - fderiv ℝ u x - A (t • h)) h) t := by
    have hγ : HasDerivAt (fun s : ℝ => x + s • h) h t := by
      simpa only [id_eq, one_smul] using ((hasDerivAt_id t).smul_const h).const_add x
    have hd := (hu _ (hball (htb t ht)).1).hasFDerivAt.comp_hasDerivAt t hγ
    have he := (((hd.sub (hasDerivAt_const t (u x))).sub
      ((hasDerivAt_id t).mul_const (fderiv ℝ u x h))).sub
      (((hasDerivAt_id t).pow 2).mul_const (A h h / 2)))
    change HasDerivAt g ((fderiv ℝ u (x + t • h)) h - 0 - 1 * fderiv ℝ u x h -
      (2 : ℝ) * t ^ (2 - 1 : ℕ) * 1 * (A h h / 2)) t at he
    have heq : (fderiv ℝ u (x + t • h)) h - 0 - 1 * fderiv ℝ u x h -
        (2 : ℝ) * t ^ (2 - 1 : ℕ) * 1 * (A h h / 2) =
      (fderiv ℝ u (x + t • h) - fderiv ℝ u x - A (t • h)) h := by
      simp only [map_smul, sub_apply, smul_apply, smul_eq_mul, Nat.reduceSub, pow_one]
      ring
    rwa [← heq]
  have hgBound (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ‖(fderiv ℝ u (x + t • h) - fderiv ℝ u x - A (t • h)) h‖ ≤ ε * ‖h‖ ^ 2 := by
    have hb := (hball (htb t ht)).2
    have htNorm : ‖t • h‖ ≤ ‖h‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
      exact mul_le_of_le_one_left (norm_nonneg h) ht.2
    calc
      _ ≤ ‖fderiv ℝ u (x + t • h) - fderiv ℝ u x - A (t • h)‖ * ‖h‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ (ε * ‖h‖) * ‖h‖ := mul_le_mul_of_nonneg_right
        (hb.trans (mul_le_mul_of_nonneg_left htNorm hε.le)) (norm_nonneg h)
      _ = _ := by ring
  have hfinal := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun t ht => (hg t ht).hasDerivWithinAt) (fun t ht => hgBound t (Ico_subset_Icc_self ht))
  simpa only [g, one_smul, zero_smul, add_zero, one_mul, mul_one, one_pow,
    zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, sub_self, sub_zero] using hfinal

end KEBall
