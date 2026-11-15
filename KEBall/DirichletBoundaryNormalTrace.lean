import KEBall.DirichletFirstJetBoundary

/-!
# Quantitative continuity of the actual boundary normal trace

The first jet is the continuous extension of the interior differential.
Its evaluation on the radial vector has a Lipschitz bound on the closed
ball.  On the sphere this trace determines the entire first jet when the
potential has zero boundary values.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open InnerProductSpace Metric Set
open scoped NNReal

namespace KEBall

theorem norm_dirichlet_firstJet_le {n : ℕ}
    {G : E n → E n →L[ℝ] ℝ} {L : ℝ≥0}
    (hG : LipschitzOnWith L G (closedUnitBall n))
    {x : E n} (hx : x ∈ closedUnitBall n) :
    ‖G x‖ ≤ (L : ℝ) + ‖G 0‖ := by
  have hz : (0 : E n) ∈ closedUnitBall n := by simp [closedUnitBall]
  have hsub : ‖G x - G 0‖ ≤ (L : ℝ) := by
    have h := hG.dist_le_mul x hx 0 hz
    rw [dist_eq_norm, dist_zero_right] at h
    exact h.trans (by simpa using
      mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.mp hx) L.coe_nonneg)
  calc
    ‖G x‖ = ‖(G x - G 0) + G 0‖ := by rw [sub_add_cancel]
    _ ≤ ‖G x - G 0‖ + ‖G 0‖ := norm_add_le _ _
    _ ≤ (L : ℝ) + ‖G 0‖ := add_le_add hsub le_rfl

theorem lipschitzOnWith_dirichlet_normalTrace {n : ℕ}
    {G : E n → E n →L[ℝ] ℝ} {L : ℝ≥0}
    (hG : LipschitzOnWith L G (closedUnitBall n)) :
    LipschitzOnWith (2 * L + ‖G 0‖₊) (fun x => G x x) (closedUnitBall n) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  have hxy : ‖G x - G y‖ ≤ (L : ℝ) * ‖x - y‖ := by
    simpa only [dist_eq_norm] using hG.dist_le_mul x hx y hy
  have hnx : ‖x‖ ≤ 1 := mem_closedBall_zero_iff.mp hx
  have hny := norm_dirichlet_firstJet_le hG hy
  have he : G x x - G y y = (G x - G y) x + G y (x - y) := by
    simp only [_root_.sub_apply, map_sub]
    ring
  rw [dist_eq_norm, dist_eq_norm, he]
  calc
    ‖(G x - G y) x + G y (x - y)‖ ≤ ‖(G x - G y) x‖ + ‖G y (x - y)‖ :=
      norm_add_le _ _
    _ ≤ ‖G x - G y‖ * ‖x‖ + ‖G y‖ * ‖x - y‖ :=
      add_le_add ((G x - G y).le_opNorm x) ((G y).le_opNorm (x - y))
    _ ≤ (L : ℝ) * ‖x - y‖ + ((L : ℝ) + ‖G 0‖) * ‖x - y‖ := by
      apply add_le_add
      · exact (mul_le_mul_of_nonneg_left hnx (norm_nonneg _)).trans (by simpa using hxy)
      · exact mul_le_mul_of_nonneg_right hny (norm_nonneg _)
    _ = ((2 * L + ‖G 0‖₊ : ℝ≥0) : ℝ) * ‖x - y‖ := by
      push_cast
      ring

end KEBall
