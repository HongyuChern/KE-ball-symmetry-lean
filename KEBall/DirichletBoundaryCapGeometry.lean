import KEBall.DirichletTangentBall

/-!
# A common interior ball for a cap of tangent annuli

All radii are explicit.  The Harnack ball has radius `R/2`; its quarter
ball contains the inner spheres of radius `R/32` for nearby tangent balls.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open InnerProductSpace Metric Set

namespace KEBall

theorem dist_dirichletTangentBallCenter_self {n : ℕ} {p : E n}
    (hp : p ∈ unitSphere n) {R : ℝ} (hR : 0 ≤ R) :
    dist (dirichletTangentBallCenter p R) p = R := by
  have h := dist_dirichlet_radial_point_tangent_center hp (s := 0) hR
  simpa only [sub_zero, one_smul, dist_comm] using h

theorem dirichlet_corkscrew_closedBall_subset {n : ℕ} {p : E n}
    (hp : p ∈ unitSphere n) {R : ℝ} (hR : 0 < R) (hR1 : R ≤ 1) :
    closedBall (dirichletTangentBallCenter p R) (R / 2) ⊆ unitBall n := by
  intro x hx
  apply mem_ball_zero_iff.mpr
  have h := norm_add_le (x - dirichletTangentBallCenter p R) (dirichletTangentBallCenter p R)
  rw [sub_add_cancel, norm_dirichletTangentBallCenter hp hR1] at h
  have hd : ‖x - dirichletTangentBallCenter p R‖ ≤ R / 2 := by
    simpa only [dist_eq_norm] using mem_closedBall.mp hx
  linarith

theorem dirichletBoundaryDistanceProxy_lower_on_corkscrew_quarter {n : ℕ}
    {p : E n} (hp : p ∈ unitSphere n) {R : ℝ} (hR : 0 < R) (hR1 : R ≤ 1)
    {x : E n} (hx : x ∈ closedBall (dirichletTangentBallCenter p R) (R / 8)) :
    R / 4 ≤ dirichletBoundaryDistanceProxy x := by
  have hxBall : x ∈ unitBall n := dirichlet_corkscrew_closedBall_subset hp hR hR1
    (closedBall_subset_closedBall (by linarith) hx)
  have h := norm_add_le (x - dirichletTangentBallCenter p R) (dirichletTangentBallCenter p R)
  rw [sub_add_cancel, norm_dirichletTangentBallCenter hp hR1] at h
  have hd : ‖x - dirichletTangentBallCenter p R‖ ≤ R / 8 := by
    simpa only [dist_eq_norm] using mem_closedBall.mp hx
  have hb := (dirichletBoundaryDistanceProxy_bounds (ball_subset_closedBall hxBall)).1
  linarith

theorem dist_dirichletTangentBallCenter_le {n : ℕ} (p q : E n)
    {R : ℝ} (hR : 0 ≤ R) (hR1 : R ≤ 1) :
    dist (dirichletTangentBallCenter p R) (dirichletTangentBallCenter q R) ≤ dist p q := by
  rw [dist_eq_norm, dirichletTangentBallCenter, dirichletTangentBallCenter,
    ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hR1), dist_eq_norm]
  exact mul_le_of_le_one_left (norm_nonneg _) (by linarith)

theorem dirichlet_inner_sphere_subset_common_quarter {n : ℕ} (p p₀ : E n)
    {R : ℝ} (hR : 0 < R) (hR1 : R ≤ 1) (hp : dist p p₀ ≤ R / 32) :
    sphere (dirichletTangentBallCenter p R) (R / 32) ⊆
      ball (dirichletTangentBallCenter p₀ R) ((R / 2) / 4) := by
  intro x hx
  have h := dist_triangle x (dirichletTangentBallCenter p R) (dirichletTangentBallCenter p₀ R)
  rw [mem_sphere.mp hx] at h
  have hc := dist_dirichletTangentBallCenter_le p p₀ hR.le hR1
  apply mem_ball.mpr
  linarith

theorem dirichlet_tangent_closedBall_subset_cap {n : ℕ}
    {p p₀ : E n} (hp : p ∈ unitSphere n) {R : ℝ} (hR : 0 < R)
    (hDist : dist p p₀ ≤ R / 32) :
    closedBall (dirichletTangentBallCenter p R) R ⊆ ball p₀ (4 * R) := by
  intro x hx
  have h₁ := dist_triangle x (dirichletTangentBallCenter p R) p
  rw [dist_dirichletTangentBallCenter_self hp hR.le] at h₁
  have h₂ := dist_triangle x p p₀
  have hx' := mem_closedBall.mp hx
  apply mem_ball.mpr
  linarith

/-- Every point of the smaller cap lies on one of the inward radii used
in the common-ball comparison, with quantitative control of the footpoint. -/
theorem exists_dirichlet_nearby_boundary_radius {n : ℕ}
    {p₀ x : E n} (hp₀ : p₀ ∈ unitSphere n) {R : ℝ}
    (hR : 0 < R) (hR1 : R ≤ 1) (hx : x ∈ unitBall n)
    (hxCap : x ∈ ball p₀ (R / 64)) :
    ∃ (p : E n) (s : ℝ), p ∈ unitSphere n ∧ 0 < s ∧ s < R / 64 ∧
      dist p p₀ ≤ R / 32 ∧ x = (1 - s) • p := by
  have hxDist : dist x p₀ < R / 64 := mem_ball.mp hxCap
  have hpNorm : ‖p₀‖ = 1 := mem_sphere_zero_iff_norm.mp hp₀
  have hxn : 0 < ‖x‖ := by
    apply norm_pos_iff.mpr
    intro hzero
    rw [hzero, dist_zero_left, hpNorm] at hxDist
    linarith
  let p : E n := ‖x‖⁻¹ • x
  let s : ℝ := 1 - ‖x‖
  have hp : p ∈ unitSphere n := by
    apply mem_sphere_zero_iff_norm.mpr
    simp only [p, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hxn),
      inv_mul_cancel₀ hxn.ne']
  have hs : 0 < s := sub_pos.mpr (mem_ball_zero_iff.mp hx)
  have hRep : x = (1 - s) • p := by
    simp [s, p, smul_smul, hxn.ne']
  have hsDist : s ≤ dist x p₀ := by
    have h := norm_sub_norm_le p₀ x
    rw [hpNorm, ← dist_eq_norm, dist_comm p₀ x] at h
    exact h
  have hpx : dist p x = s := by
    have he : p - x = s • p := by
      calc
        p - x = p - (1 - s) • p := by rw [← hRep]
        _ = (1 - (1 - s)) • p := by simp only [sub_smul, one_smul]
        _ = s • p := by congr 1; ring
    rw [dist_eq_norm, he, norm_smul, Real.norm_eq_abs, abs_of_pos hs,
      mem_sphere_zero_iff_norm.mp hp, mul_one]
  have hpp := dist_triangle p x p₀
  rw [hpx] at hpp
  exact ⟨p, s, hp, hs, hsDist.trans_lt hxDist, by linarith, hRep⟩

end KEBall
