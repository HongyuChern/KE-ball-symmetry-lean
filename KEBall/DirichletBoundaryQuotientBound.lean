import KEBall.DirichletTangentBall

/-! A zero-boundary Lipschitz function has a uniformly bounded true quotient. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open InnerProductSpace Metric Set
open scoped NNReal

namespace KEBall

theorem exists_dirichlet_nearest_sphere_point {n : ℕ} (hn : 0 < n)
    {x : E n} (hx : x ∈ closedUnitBall n) :
    ∃ p ∈ unitSphere n, dist x p = 1 - ‖x‖ := by
  by_cases hx0 : x = 0
  · let i : Fin (2 * n) := ⟨0, by omega⟩
    let p : E n := (EuclideanSpace.basisFun (Fin (2 * n)) ℝ) i
    have hp : ‖p‖ = 1 := (EuclideanSpace.basisFun (Fin (2 * n)) ℝ).orthonormal.norm_eq_one i
    refine ⟨p, mem_sphere_zero_iff_norm.mpr hp, ?_⟩
    simp only [hx0, dist_zero_left, norm_zero, sub_zero, hp]
  · have hn0 : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    let p : E n := ‖x‖⁻¹ • x
    have hp : ‖p‖ = 1 := by
      simp only [p, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn0),
        inv_mul_cancel₀ hn0.ne']
    have hRep : x = ‖x‖ • p := by simp [p, smul_smul, hn0.ne']
    have hSub : x - p = (‖x‖ - 1) • p := by rw [sub_smul, one_smul, ← hRep]
    refine ⟨p, mem_sphere_zero_iff_norm.mpr hp, ?_⟩
    rw [dist_eq_norm, hSub, norm_smul, Real.norm_eq_abs,
      abs_of_nonpos (sub_nonpos.mpr (mem_closedBall_zero_iff.mp hx)), neg_sub, hp, mul_one]

theorem abs_dirichlet_boundary_quotient_le_of_lipschitz {n : ℕ} (hn : 0 < n)
    {q : E n → ℝ} {L : ℝ≥0} (hLip : LipschitzOnWith L q (closedUnitBall n))
    (hq0 : ∀ x ∈ unitSphere n, q x = 0) {x : E n} (hx : x ∈ unitBall n) :
    |q x / dirichletBoundaryDistanceProxy x| ≤ 2 * (L : ℝ) := by
  obtain ⟨p, hp, hDist⟩ := exists_dirichlet_nearest_sphere_point hn (ball_subset_closedBall hx)
  have h := hLip.dist_le_mul x (ball_subset_closedBall hx) p (sphere_subset_closedBall hp)
  rw [hq0 p hp, dist_zero_right, Real.norm_eq_abs, hDist] at h
  have hρ := dirichletBoundaryDistanceProxy_pos hx
  have hρLower := mul_le_mul_of_nonneg_left
    (dirichletBoundaryDistanceProxy_bounds (ball_subset_closedBall hx)).1 (L.coe_nonneg)
  rw [abs_div, abs_of_pos hρ]
  apply (div_le_iff₀ hρ).mpr
  nlinarith only [h, hρLower]

end KEBall
