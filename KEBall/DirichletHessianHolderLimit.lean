import KEBall.DirichletLocalHessianLimit

/-! Retention of the precise interior Hessian modulus at a specified
first-jet limit. Compactness may use a larger norm bound, while the
final Holder constant remains the original one. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 600000

open Filter Metric Set
open scoped ContDiff NNReal Topology

namespace KEBall

theorem hessian_holder_of_uniform_firstJet_limit_on_ball {n : ℕ}
    {u : ℕ → E n → ℝ} (hu : ∀ j, ContDiff ℝ ∞ (u j))
    {w : E n → ℝ} {G : E n → E n →L[ℝ] ℝ}
    {p : E n} {R : ℝ} {α N K : ℝ≥0} (hα : 0 < α)
    (hU : TendstoUniformlyOn u w atTop (ball p R))
    (hG : TendstoUniformlyOn (fun j => fderiv ℝ (u j)) G atTop (ball p R))
    (hBound : ∀ j x, x ∈ ball p R → ‖fderiv ℝ (fderiv ℝ (u j)) x‖ ≤ N)
    (hHolder : ∀ j, HolderOnWith K α (fderiv ℝ (fderiv ℝ (u j))) (ball p R)) :
    HolderOnWith K α (fderiv ℝ (fderiv ℝ w)) (ball p R) := by
  apply dirichlet_holderOnWith_of_norm_bound K.coe_nonneg α.coe_nonneg
  intro x hx y hy
  let d : ℝ := max (dist x p) (dist y p)
  let r : ℝ := (d + R) / 2
  have hd : d < R := max_lt (mem_ball.mp hx) (mem_ball.mp hy)
  have hd0 : 0 ≤ d := le_trans dist_nonneg (le_max_left _ _)
  have hr : 0 < r := by dsimp [r]; linarith
  have hdr : d < r := by dsimp [r]; linarith
  have hrR : r < R := by dsimp [r]; linarith
  have hSub : closedBall p r ⊆ ball p R := closedBall_subset_ball hrR
  have hxr : x ∈ ball p r := mem_ball.mpr ((le_max_left _ _).trans_lt hdr)
  have hyr : y ∈ ball p r := mem_ball.mpr ((le_max_right _ _).trans_lt hdr)
  let J : ℝ≥0 := max N K
  obtain ⟨_, _, _, φ, _, hLim⟩ :=
    local_C2_of_uniform_firstJet_and_hessian_holder hu hα (hU.mono hSub) (hG.mono hSub)
      (fun j z hz => (hBound j z (hSub hz)).trans (by exact_mod_cast le_max_left N K))
      (fun j => ((hHolder j).mono hSub).mono_const (le_max_right N K))
  have h := le_of_tendsto ((hLim.tendsto_at hxr).dist (hLim.tendsto_at hyr))
    (Eventually.of_forall fun j => (hHolder (φ j)).dist_le hx hy)
  simpa only [dist_eq_norm] using h

end KEBall
