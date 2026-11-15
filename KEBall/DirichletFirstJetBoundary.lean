import KEBall.BoundaryHessian
import Mathlib.Analysis.Calculus.FDeriv.Extend

/-!
# The actual first jet at the boundary

Continuity of the first jet upgrades the interior derivative to a derivative
within the closed ball.  Great circles then identify its tangential and
normal components from the genuine zero boundary values.  No exterior
differentiability of the original representative is asserted.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter InnerProductSpace Metric Set
open scoped ContDiff Topology

namespace KEBall

theorem hasFDerivWithinAt_dirichlet_closedBall {n : ℕ}
    {w : E n → ℝ} {G : E n → E n →L[ℝ] ℝ}
    (hw : ContinuousOn w (closedUnitBall n))
    (hG : ContinuousOn G (closedUnitBall n))
    (hD : ∀ x ∈ unitBall n, HasFDerivAt w (G x) x)
    {x : E n} (hx : x ∈ closedUnitBall n) :
    HasFDerivWithinAt w (G x) (closedUnitBall n) x := by
  have hClosure : closure (unitBall n) = closedUnitBall n :=
    closure_ball (0 : E n) (by norm_num)
  rw [← hClosure]
  apply hasFDerivWithinAt_closure_of_tendsto_fderiv
    (fun y hy => (hD y hy).differentiableAt.differentiableWithinAt)
    (convex_ball _ _) isOpen_ball
  · intro y hy
    rw [hClosure] at hy
    exact (hw y hy).mono ball_subset_closedBall
  · apply ((hG x hx).mono ball_subset_closedBall).congr'
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact (hD y hy).fderiv.symm

theorem contDiffOn_one_dirichlet_closedBall {n : ℕ}
    {w : E n → ℝ} {G : E n → E n →L[ℝ] ℝ}
    (hw : ContinuousOn w (closedUnitBall n))
    (hG : ContinuousOn G (closedUnitBall n))
    (hD : ∀ x ∈ unitBall n, HasFDerivAt w (G x) x) :
    ContDiffOn ℝ 1 w (closedUnitBall n) := by
  have hUnique : UniqueDiffOn ℝ (closedUnitBall n) := by
    apply uniqueDiffOn_convex (convex_closedBall (0 : E n) 1)
    rw [interior_closedBall _ (by norm_num)]
    exact nonempty_ball.mpr (by norm_num)
  change ContDiffOn ℝ ((0 : ℕ∞ω) + 1) w (closedUnitBall n)
  apply (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn hUnique).mpr
  exact ⟨by simp, G, contDiffOn_zero.mpr hG,
    fun x hx => hasFDerivWithinAt_dirichlet_closedBall hw hG hD hx⟩

theorem dirichlet_closedBall_firstJet_unit_tangent_zero {n : ℕ}
    {w : E n → ℝ} {G : E n → E n →L[ℝ] ℝ}
    (hD : ∀ x ∈ closedUnitBall n, HasFDerivWithinAt w (G x) (closedUnitBall n) x)
    (hw0 : ∀ x ∈ unitSphere n, w x = 0)
    {x v : E n} (hx : x ∈ unitSphere n) (hv : ‖v‖ = 1)
    (horth : inner ℝ x v = 0) : G x v = 0 := by
  have hd := (hD x (sphere_subset_closedBall hx)).comp_hasDerivAt_of_eq 0
    (greatCircle_hasDerivAt x v 0)
    (Eventually.of_forall fun s => sphere_subset_closedBall (greatCircle_mem_sphere hx hv horth s))
    (greatCircle_zero x v).symm
  have he : w ∘ greatCircle x v = fun _ : ℝ => (0 : ℝ) := by
    funext s
    exact hw0 _ (greatCircle_mem_sphere hx hv horth s)
  rw [he] at hd
  simpa only [greatCircleVelocity_zero, deriv_const] using hd.deriv.symm

theorem dirichlet_closedBall_firstJet_tangent_zero {n : ℕ}
    {w : E n → ℝ} {G : E n → E n →L[ℝ] ℝ}
    (hD : ∀ x ∈ closedUnitBall n, HasFDerivWithinAt w (G x) (closedUnitBall n) x)
    (hw0 : ∀ x ∈ unitSphere n, w x = 0)
    {x v : E n} (hx : x ∈ unitSphere n) (horth : inner ℝ x v = 0) : G x v = 0 := by
  by_cases hv : v = 0
  · simp [hv]
  let z : E n := ‖v‖⁻¹ • v
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  have hz : ‖z‖ = 1 := by
    simp only [z, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg v)]
    exact inv_mul_cancel₀ hn
  have horthz : inner ℝ x z = 0 := by simp [z, real_inner_smul_right, horth]
  have hzero := dirichlet_closedBall_firstJet_unit_tangent_zero hD hw0 hx hz horthz
  have hvz : ‖v‖ • z = v := by simp [z, smul_smul, hn]
  rw [← hvz, map_smul, hzero, smul_zero]

theorem dirichlet_closedBall_firstJet_normal {n : ℕ}
    {w : E n → ℝ} {G : E n → E n →L[ℝ] ℝ}
    (hD : ∀ x ∈ closedUnitBall n, HasFDerivWithinAt w (G x) (closedUnitBall n) x)
    (hw0 : ∀ x ∈ unitSphere n, w x = 0)
    {x : E n} (hx : x ∈ unitSphere n) (v : E n) :
    G x v = G x x * inner ℝ x v := by
  have hxx : inner ℝ x x = 1 := by
    rw [real_inner_self_eq_norm_sq, mem_sphere_zero_iff_norm.mp hx, one_pow]
  have horth : inner ℝ x (v - inner ℝ x v • x) = 0 := by
    rw [inner_sub_right, real_inner_smul_right, hxx, mul_one, sub_self]
  have hz := dirichlet_closedBall_firstJet_tangent_zero hD hw0 hx horth
  rw [map_sub, map_smul, smul_eq_mul] at hz
  linarith

end KEBall
