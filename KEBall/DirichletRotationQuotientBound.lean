import KEBall.DirichletBoundaryNormalTrace
import KEBall.DirichletBoundaryQuotientBound

/-!
# True rotation quotients from the actual first jet

This estimate applies to the continuous limit first jet as well as to
smooth approximating potentials.  The zero sphere value follows from its
within differential and the tangency of the vector field.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open InnerProductSpace Metric Set
open scoped NNReal

namespace KEBall

theorem lipschitzOnWith_dirichlet_linearFieldTrace {n : ℕ}
    {G : E n → E n →L[ℝ] ℝ} {L : ℝ≥0}
    (hG : LipschitzOnWith L G (closedUnitBall n)) (T : E n →L[ℝ] E n) :
    LipschitzOnWith ((2 * L + ‖G 0‖₊) * ‖T‖₊) (fun x => G x (T x)) (closedUnitBall n) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  have hxy : ‖G x - G y‖ ≤ (L : ℝ) * ‖x - y‖ := by
    simpa only [dist_eq_norm] using hG.dist_le_mul x hx y hy
  have hTx : ‖T x‖ ≤ ‖T‖ := (T.le_opNorm x).trans
    (mul_le_of_le_one_right (norm_nonneg T) (mem_closedBall_zero_iff.mp hx))
  have hGy := norm_dirichlet_firstJet_le hG hy
  have he : G x (T x) - G y (T y) = (G x - G y) (T x) + G y (T (x - y)) := by
    simp only [_root_.sub_apply, map_sub]
    ring
  rw [dist_eq_norm, dist_eq_norm, he]
  calc
    ‖(G x - G y) (T x) + G y (T (x - y))‖ ≤
        ‖(G x - G y) (T x)‖ + ‖G y (T (x - y))‖ := norm_add_le _ _
    _ ≤ ‖G x - G y‖ * ‖T x‖ + ‖G y‖ * ‖T (x - y)‖ :=
      add_le_add ((G x - G y).le_opNorm _) ((G y).le_opNorm _)
    _ ≤ ((L : ℝ) * ‖x - y‖) * ‖T‖ + ((L : ℝ) + ‖G 0‖) * (‖T‖ * ‖x - y‖) := by
      apply add_le_add
      · exact (mul_le_mul_of_nonneg_left hTx (norm_nonneg _)).trans
          (mul_le_mul_of_nonneg_right hxy (norm_nonneg T))
      · exact mul_le_mul hGy (T.le_opNorm _) (norm_nonneg _) (by positivity)
    _ = (((2 * L + ‖G 0‖₊) * ‖T‖₊ : ℝ≥0) : ℝ) * ‖x - y‖ := by
      push_cast
      ring

theorem abs_dirichlet_rotation_firstJet_quotient_le {n : ℕ} (hn : 0 < n)
    {w : E n → ℝ} {G : E n → E n →L[ℝ] ℝ} {L : ℝ≥0}
    (hG : LipschitzOnWith L G (closedUnitBall n))
    (hD : ∀ x ∈ closedUnitBall n, HasFDerivWithinAt w (G x) (closedUnitBall n) x)
    (hw0 : ∀ x ∈ unitSphere n, w x = 0) (T : E n →L[ℝ] E n)
    (hT : ∀ x ∈ unitSphere n, inner ℝ x (T x) = 0)
    {x : E n} (hx : x ∈ unitBall n) :
    |G x (T x) / dirichletBoundaryDistanceProxy x| ≤
      2 * (2 * (L : ℝ) + ‖G 0‖) * ‖T‖ := by
  have h := abs_dirichlet_boundary_quotient_le_of_lipschitz hn
    (lipschitzOnWith_dirichlet_linearFieldTrace hG T)
    (fun y hy => dirichlet_closedBall_firstJet_tangent_zero hD hw0 hy (hT y hy)) hx
  push_cast at h
  nlinarith only [h]

end KEBall
