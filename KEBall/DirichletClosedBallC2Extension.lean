import KEBall.DirichletFirstJetBoundary
import Mathlib.Topology.ExtendFrom

/-!
# Closed-ball C2 regularity from genuine Hessian limits

Existence of an interior Hessian limit at every sphere point supplies a
continuous extension by `extendFrom`.  The closure derivative theorem is
applied to the first jet, then to the potential.  No exterior second
derivative of the original representative is required.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Filter Metric Set
open scoped ContDiff Topology

namespace KEBall

theorem continuousOn_dirichlet_extendFrom_of_boundary_limits {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] {H : E n → F}
    (hH : ContinuousOn H (unitBall n))
    (hLim : ∀ p ∈ unitSphere n, ∃ C : F, Tendsto H (𝓝[unitBall n] p) (𝓝 C)) :
    ContinuousOn (extendFrom (unitBall n) H) (closedUnitBall n) := by
  have hClosure : closure (unitBall n) = closedUnitBall n :=
    closure_ball (0 : E n) (by norm_num)
  apply continuousOn_extendFrom hClosure.ge
  intro x hx
  by_cases hi : x ∈ unitBall n
  · exact ⟨H x, hH x hi⟩
  · apply hLim x
    apply mem_sphere_zero_iff_norm.mpr
    have hle := mem_closedBall_zero_iff.mp hx
    have hge : 1 ≤ ‖x‖ := le_of_not_gt (fun h => hi (mem_ball_zero_iff.mpr h))
    exact le_antisymm hle hge

theorem hasFDerivWithinAt_dirichlet_closedBall_vector {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {G : E n → F} {H : E n → E n →L[ℝ] F}
    (hG : ContinuousOn G (closedUnitBall n))
    (hH : ContinuousOn H (closedUnitBall n))
    (hD : ∀ x ∈ unitBall n, HasFDerivAt G (H x) x)
    {x : E n} (hx : x ∈ closedUnitBall n) :
    HasFDerivWithinAt G (H x) (closedUnitBall n) x := by
  have hClosure : closure (unitBall n) = closedUnitBall n :=
    closure_ball (0 : E n) (by norm_num)
  rw [← hClosure]
  apply hasFDerivWithinAt_closure_of_tendsto_fderiv
    (fun y hy => (hD y hy).differentiableAt.differentiableWithinAt)
    (convex_ball _ _) isOpen_ball
  · intro y hy
    rw [hClosure] at hy
    exact (hG y hy).mono ball_subset_closedBall
  · apply ((hH x hx).mono ball_subset_closedBall).congr'
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact (hD y hy).fderiv.symm

theorem contDiffOn_two_dirichlet_closedBall_of_hessian_limits {n : ℕ}
    {w : E n → ℝ} {G : E n → E n →L[ℝ] ℝ}
    {H : E n → E n →L[ℝ] E n →L[ℝ] ℝ}
    (hw : ContinuousOn w (closedUnitBall n))
    (hG : ContinuousOn G (closedUnitBall n))
    (hD : ∀ x ∈ unitBall n, HasFDerivAt w (G x) x)
    (hH : ContinuousOn H (unitBall n))
    (hDG : ∀ x ∈ unitBall n, HasFDerivAt G (H x) x)
    (hLim : ∀ p ∈ unitSphere n, ∃ C : E n →L[ℝ] E n →L[ℝ] ℝ,
      Tendsto H (𝓝[unitBall n] p) (𝓝 C)) :
    ContDiffOn ℝ 2 w (closedUnitBall n) := by
  let H' := extendFrom (unitBall n) H
  have hH'C : ContinuousOn H' (closedUnitBall n) :=
    continuousOn_dirichlet_extendFrom_of_boundary_limits hH hLim
  have hEq (x : E n) (hx : x ∈ unitBall n) : H' x = H x := extendFrom_extends hH x hx
  have hDG' (x : E n) (hx : x ∈ unitBall n) : HasFDerivAt G (H' x) x := by
    rw [hEq x hx]
    exact hDG x hx
  have hUnique : UniqueDiffOn ℝ (closedUnitBall n) := by
    apply uniqueDiffOn_convex (convex_closedBall (0 : E n) 1)
    rw [interior_closedBall _ (by norm_num)]
    exact nonempty_ball.mpr (by norm_num)
  have hG1 : ContDiffOn ℝ 1 G (closedUnitBall n) := by
    change ContDiffOn ℝ ((0 : ℕ∞ω) + 1) G (closedUnitBall n)
    apply (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn hUnique).mpr
    exact ⟨by simp, H', contDiffOn_zero.mpr hH'C,
      fun x hx => hasFDerivWithinAt_dirichlet_closedBall_vector hG hH'C hDG' hx⟩
  change ContDiffOn ℝ ((1 : ℕ∞ω) + 1) w (closedUnitBall n)
  apply (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn hUnique).mpr
  exact ⟨by simp, G, hG1, fun x hx => hasFDerivWithinAt_dirichlet_closedBall hw hG hD hx⟩

end KEBall
