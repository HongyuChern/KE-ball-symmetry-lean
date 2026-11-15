import KEBall.DirichletCompactness

/-! Uniform two-point control of the prescribed log-density on the ball. -/

set_option autoImplicit false

open Metric Set
open scoped ContDiff NNReal

noncomputable section

namespace KEBall

theorem exists_dirichlet_logDensity_lipschitz_exp_bound {n : ℕ}
    {g : E n → ℝ} (hg : SmoothNear (closedUnitBall n) g) :
    ∃ (K : ℝ≥0) (D : ℝ), 0 < D ∧ LipschitzOnWith K g (closedUnitBall n) ∧
      ∀ x ∈ closedUnitBall n, Real.exp (g x) ≤ D := by
  obtain ⟨U, hU, hSub, hgU⟩ := hg
  have hDg : ContinuousOn (fderiv ℝ g) U :=
    (hgU.fderiv_of_isOpen hU (m := 0) (by simp)).continuousOn
  obtain ⟨K, hK⟩ := (isCompact_closedBall (0 : E n) 1).exists_bound_of_continuousOn (hDg.mono hSub)
  let k : ℝ≥0 := ⟨|K|, abs_nonneg K⟩
  have hk : LipschitzOnWith k g (closedUnitBall n) := by
    apply Convex.lipschitzOnWith_of_nnnorm_fderiv_le (𝕜 := ℝ) _ _ (convex_closedBall (0 : E n) 1)
    · intro x hx
      exact (hgU.contDiffAt (hU.mem_nhds (hSub hx))).differentiableAt (by simp)
    · intro x hx
      exact_mod_cast (hK x hx).trans (le_abs_self K)
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : E n) 1).exists_bound_of_continuousOn
    (hgU.continuousOn.mono hSub)
  refine ⟨k, Real.exp B, Real.exp_pos B, hk, ?_⟩
  intro x hx
  exact Real.exp_le_exp.mpr ((le_abs_self (g x)).trans (hB x hx))

theorem dirichlet_density_log_twoPoint_bound {n : ℕ}
    {g : E n → ℝ} {K : ℝ≥0} (hLip : LipschitzOnWith K g (closedUnitBall n))
    {D : ℝ} (hD : 0 ≤ D) (hExp : ∀ x ∈ closedUnitBall n, Real.exp (g x) ≤ D)
    {x₀ x y : E n} {R : ℝ} (hR : 0 ≤ R)
    (hBall : closedBall x₀ R ⊆ unitBall n)
    (hx : x ∈ ball x₀ R) (hy : y ∈ ball x₀ R) :
    Real.exp (g x) * (g x - g y) ≤ (2 * D * (K : ℝ)) * R := by
  have hxB := ball_subset_closedBall (hBall (ball_subset_closedBall hx))
  have hyB := ball_subset_closedBall (hBall (ball_subset_closedBall hy))
  have hdist : dist x y ≤ 2 * R := by
    calc
      dist x y ≤ dist x x₀ + dist x₀ y := dist_triangle _ _ _
      _ ≤ R + R := add_le_add (mem_ball.mp hx).le (by simpa only [dist_comm] using (mem_ball.mp hy).le)
      _ = _ := by ring
  have hdiff : g x - g y ≤ (K : ℝ) * (2 * R) := by
    calc
      g x - g y ≤ |g x - g y| := le_abs_self _
      _ = dist (g x) (g y) := Real.dist_eq _ _ |>.symm
      _ ≤ (K : ℝ) * dist x y := hLip.dist_le_mul x hxB y hyB
      _ ≤ _ := mul_le_mul_of_nonneg_left hdist K.coe_nonneg
  calc
    _ ≤ Real.exp (g x) * ((K : ℝ) * (2 * R)) :=
      mul_le_mul_of_nonneg_left hdiff (Real.exp_pos _).le
    _ ≤ D * ((K : ℝ) * (2 * R)) := mul_le_mul_of_nonneg_right (hExp x hxB) (by positivity)
    _ = _ := by ring

end KEBall
