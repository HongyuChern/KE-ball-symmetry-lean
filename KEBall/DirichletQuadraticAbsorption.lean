import KEBall.DirichletAnnularComparison
import KEBall.DirichletGradient

/-! A threshold maximum principle and a quadratic Hessian absorption.
The conclusion is unconditional once the displayed differential inequality
has been checked for the actual functions. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 500000

open Filter InnerProductSpace Metric Set
open scoped ContDiff

namespace KEBall

theorem dirichlet_le_boundary_of_contraction_positive_above
    {n : ℕ} (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n))
    {A : E n → E n →L[ℝ] E n}
    (hA : ∀ x ∈ unitBall n, (A x).IsPositive)
    {w : E n → ℝ} (hw : SmoothNear (closedUnitBall n) w) {C : ℝ}
    (hBoundary : ∀ x ∈ unitSphere n, w x ≤ C)
    (hL : ∀ x ∈ unitBall n, C < w x →
      0 < dirichletBilinearContraction b (A x) (realHessian w x)) :
    ∀ x ∈ closedUnitBall n, w x ≤ C := by
  have hW : ContinuousOn w (closedUnitBall n) :=
    fun x hx => (hw.contDiffAt hx).continuousAt.continuousWithinAt
  have hne : (closedUnitBall n).Nonempty := ⟨0, by simp [closedUnitBall]⟩
  obtain ⟨x, hx, hxmax⟩ := (isCompact_closedBall (0 : E n) 1).exists_isMaxOn hne hW
  have hx' : ‖x‖ ≤ 1 := mem_closedBall_zero_iff.mp hx
  by_cases hWC : w x ≤ C
  · exact fun y hy => (hxmax hy).trans hWC
  have hAbove : C < w x := lt_of_not_ge hWC
  rcases hx'.lt_or_eq with hlt | heq
  · have hxB : x ∈ unitBall n := mem_ball_zero_iff.mpr hlt
    have hMax := hxmax.isLocalMax
      (mem_of_superset (isOpen_ball.mem_nhds hxB) ball_subset_closedBall)
    have hNonpos := dirichletBilinearContraction_nonpos_of_positive b (hA x hxB)
      (realHessian w x) (fun v => realHessian_nonpos_of_isLocalMax (hw.contDiffAt hx) hMax v)
    exact False.elim ((hL x hxB hAbove).not_ge hNonpos)
  · exact False.elim (hWC (hBoundary x (mem_sphere_zero_iff_norm.mpr heq)))

theorem dirichlet_quadratic_absorption
    {n : ℕ} (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n))
    {A : E n → E n →L[ℝ] E n}
    (hA : ∀ x ∈ unitBall n, (A x).IsPositive)
    {H p : E n → ℝ}
    (hW : SmoothNear (closedUnitBall n) (fun x => H x + (p x) ^ 2))
    {c T S C BC : ℝ} (hc : 0 < c) (hT : 0 ≤ T) (hS : 0 ≤ S)
    (hC : 0 < C) (hCS : 2 * S ≤ C) (hTC : 4 * T < c * C)
    (hBC : BC + S ≤ C)
    (hp : ∀ x ∈ closedUnitBall n, (p x) ^ 2 ≤ S)
    (hBoundary : ∀ x ∈ unitSphere n, H x ≤ BC)
    (hL : ∀ x ∈ unitBall n,
      2 * c * (H x) ^ 2 - T * (C + 2 * S) ≤
        dirichletBilinearContraction b (A x)
          (realHessian (fun y => H y + (p y) ^ 2) x)) :
    ∀ x ∈ closedUnitBall n, H x ≤ C := by
  have hBound : ∀ x ∈ closedUnitBall n, H x + (p x) ^ 2 ≤ C := by
    apply dirichlet_le_boundary_of_contraction_positive_above b hA hW
    · intro x hx
      exact (add_le_add (hBoundary x hx) (hp x (sphere_subset_closedBall hx))).trans hBC
    · intro x hx hAbove
      have hpB := hp x (ball_subset_closedBall hx)
      have hHalf : C / 2 < H x := by linarith
      have hH : 0 < H x := lt_trans (by positivity) hHalf
      have hSq : C ^ 2 / 4 < (H x) ^ 2 := by nlinarith
      have hSqC := mul_lt_mul_of_pos_left hSq hc
      have hTC' := mul_lt_mul_of_pos_right hTC hC
      have hSmall := mul_le_mul_of_nonneg_left hCS hT
      have hPositive : 0 < 2 * c * (H x) ^ 2 - T * (C + 2 * S) := by
        nlinarith only [hSqC, hTC', hSmall]
      exact hPositive.trans_le (hL x hx)
  intro x hx
  exact (le_add_of_nonneg_right (sq_nonneg (p x))).trans (hBound x hx)

end KEBall
