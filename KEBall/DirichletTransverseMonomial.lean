import KEBall.DirichletClosedTaylorGlue
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.SmoothSeries

/-! Compactly supported transverse monomials with small lower derivatives. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Metric
open scoped ContDiff Topology

namespace KEBall

private noncomputable def transverseBump : ContDiffBump (0 : ℝ) where
  rIn := 1 / 2
  rOut := 1
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

noncomputable def transverseMonomial (k : ℕ) (a t : ℝ) : ℝ :=
  a ^ k * (a⁻¹ * t) ^ k / k.factorial * transverseBump (a⁻¹ * t)

theorem contDiff_transverseMonomial (k : ℕ) (a : ℝ) :
    ContDiff ℝ ∞ (transverseMonomial k a) := by
  have h : ContDiff ℝ ∞ (fun t : ℝ => a⁻¹ * t) := contDiff_const.mul contDiff_id
  exact ((contDiff_const.mul (h.pow k)).div_const _).mul (transverseBump.contDiff.comp h)

theorem transverseMonomial_eq_zero_of_lt_abs (k : ℕ) {a t : ℝ}
    (ha : a ∈ Ioc (0 : ℝ) 1) (ht : 1 < |t|) :
    transverseMonomial k a t = 0 := by
  have hStrict : 1 < |a⁻¹ * t| := by
    rw [abs_mul, abs_of_pos (inv_pos.mpr ha.1)]
    calc
      1 ≤ a⁻¹ := (one_le_inv₀ ha.1).mpr ha.2
      _ = a⁻¹ * 1 := (mul_one _).symm
      _ < _ := mul_lt_mul_of_pos_left ht (inv_pos.mpr ha.1)
  have hZ : transverseBump (a⁻¹ * t) = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    rw [transverseBump.tsupport_eq]
    intro h
    exact (not_lt_of_ge (by simpa [transverseBump, Real.dist_eq] using h)) hStrict
  simp only [transverseMonomial, hZ, mul_zero]

private theorem transverseMonomial_eventuallyEq (k : ℕ) {a : ℝ} (ha : 0 < a) :
    transverseMonomial k a =ᶠ[𝓝 0] fun t => t ^ k / k.factorial := by
  have hN : ∀ᶠ t : ℝ in 𝓝 0, a⁻¹ * t ∈ ball (0 : ℝ) transverseBump.rIn := by
    have h : Continuous (fun t : ℝ => a⁻¹ * t) := continuous_const.mul continuous_id
    exact h.continuousAt (isOpen_ball.mem_nhds (by
      simpa only [mul_zero] using mem_ball_self transverseBump.rIn_pos))
  filter_upwards [hN] with t ht
  have h1 := (transverseBump.eventuallyEq_one_of_mem_ball ht).eq_of_nhds
  change transverseBump (a⁻¹ * t) = 1 at h1
  rw [transverseMonomial, h1, mul_one, mul_pow, ← mul_assoc, ← mul_pow,
    mul_inv_cancel₀ ha.ne', one_pow, one_mul]

/-- The derivatives at zero are precisely those of a normalized monomial. -/
theorem iteratedDeriv_transverseMonomial_zero (j k : ℕ) {a : ℝ} (ha : 0 < a) :
    iteratedDeriv j (transverseMonomial k a) 0 = if j = k then 1 else 0 := by
  rw [(transverseMonomial_eventuallyEq k ha).iteratedDeriv_eq j,
    iteratedDeriv_div_const, iteratedDeriv_fun_pow_zero]
  by_cases hj : j = k
  · simp [hj, Nat.factorial_ne_zero]
  · simp [hj]

private noncomputable def transverseProfile (k : ℕ) (t : ℝ) :=
  t ^ k / k.factorial * transverseBump t

private theorem contDiff_transverseProfile (k : ℕ) : ContDiff ℝ ∞ (transverseProfile k) :=
  ((contDiff_id.pow k).div_const _).mul transverseBump.contDiff

private theorem hasCompactSupport_transverseProfile (k : ℕ) :
    HasCompactSupport (transverseProfile k) :=
  transverseBump.hasCompactSupport.mul_left

private theorem transverseMonomial_eq_scale (k : ℕ) (a : ℝ) :
    transverseMonomial k a = fun t => a ^ k • transverseProfile k (a⁻¹ • t) := by
  funext t
  simp only [transverseMonomial, transverseProfile, smul_eq_mul]
  ring

/-- Below the monomial order, the uniform derivative bound has a
positive power of the support scale. -/
theorem exists_bound_iteratedFDeriv_transverseMonomial (k j : ℕ) (hj : j ≤ k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ℝ, 0 < a → ∀ t : ℝ,
      ‖iteratedFDeriv ℝ j (transverseMonomial k a) t‖ ≤ C * a ^ (k - j) := by
  have hP := contDiff_transverseProfile k
  have hCts := hP.continuous_iteratedFDeriv
    (show (j : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
  obtain ⟨C, hC⟩ := hCts.norm.bddAbove_range_of_hasCompactSupport
    ((hasCompactSupport_transverseProfile k).iteratedFDeriv j).norm
  have hNon : 0 ≤ C := (norm_nonneg _).trans (hC ⟨0, rfl⟩)
  refine ⟨C, hNon, fun a ha t => ?_⟩
  have hS : ContDiff ℝ ∞ (fun y => transverseProfile k (a⁻¹ • y)) :=
    hP.comp ((contDiff_id (𝕜 := ℝ) (E := ℝ)).const_smul a⁻¹)
  have hOrder : (j : ℕ∞ω) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
  rw [transverseMonomial_eq_scale, iteratedFDeriv_const_smul_apply' ((hS.of_le hOrder).contDiffAt),
    iteratedFDeriv_comp_const_smul a⁻¹ (hP.of_le hOrder), smul_smul, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg (by positivity), inv_pow,
    ← pow_sub₀ a ha.ne' hj, mul_comm (a ^ (k - j))]
  exact mul_le_mul_of_nonneg_right (hC ⟨a⁻¹ • t, rfl⟩) (by positivity)

end KEBall
