import KEBall.DirichletLogDensitySmooth

/-! The quadratic starting point of the log-density continuity path. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Metric Set
open scoped ComplexOrder ContDiff Matrix Topology

namespace KEBall

private noncomputable def dirichletQuadratic (n : ℕ) (x : E n) : ℝ := ‖x‖ ^ 2 - 1

private theorem contDiff_dirichletQuadratic (n : ℕ) : ContDiff ℝ ∞ (dirichletQuadratic n) :=
  (contDiff_norm_sq ℝ).sub contDiff_const

private theorem complexHessian_dirichletQuadratic {n : ℕ} (x : E n) :
    complexHessian (dirichletQuadratic n) x = 1 := by
  have hρ (t : ℝ) (_ : 0 ≤ t) : HasDerivAt (fun s : ℝ => s - 1) 1 t :=
    (hasDerivAt_id' t).sub_const 1
  have hρ₁ : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 (‖x‖ ^ 2) := hasDerivAt_const _ _
  change complexHessian (fun y : E n => ‖y‖ ^ 2 - 1) x = 1
  simpa using complexHessian_radial_profile hρ (x := x) hρ₁

/-- Smooth positive log-density paths from the quadratic background have
strictly plurisubharmonic zero-boundary solutions of any prescribed finite
regularity for all sufficiently small parameters. -/
theorem eventually_exists_posDef_dirichlet_logDensity_near_zero {n r : ℕ}
    (hn : 0 < n) (hr : 2 ≤ r) {g : E n → ℝ} (hg : ContDiff ℝ ∞ g) :
    ∀ᶠ s in 𝓝 (0 : ℝ), ∃ v : E n → ℝ, ContDiffOn ℝ (r : ℕ∞ω) v (closedUnitBall n) ∧
      (∀ x ∈ unitSphere n, v x = 0) ∧
      (∀ x ∈ unitBall n, (complexHessian v x).PosDef) ∧
      EqOn (fun x => (complexHessian v x).det.re) (fun x => Real.exp (s * g x)) (unitBall n) := by
  apply eventually_exists_closedBall_posDef_dirichlet_logDensity hn hr
    (contDiff_dirichletQuadratic n) hg 0 (a := 1) (l := 1 / 4)
  · intro x hx
    simp [dirichletQuadratic, mem_sphere_zero_iff_norm.mp hx]
  · intro x _
    rw [complexHessian_dirichletQuadratic]
    exact Matrix.PosDef.one
  · intro x _
    simp [complexHessian_dirichletQuadratic]
  · exact zero_lt_one
  · norm_num
  · intro x _
    simp [complexHessian_dirichletQuadratic]
  · intro x _ v
    rw [complexLaplacian_rankOne_quadratic, complexHessian_dirichletQuadratic, inv_one,
      Matrix.one_mulVec, star_star, dotProduct_comm]
    have h := sum_star_complexCoord_mul v
    change star (complexCoord v) ⬝ᵥ complexCoord v = _ at h
    rw [h, Complex.ofReal_re]
    simpa only [div_eq_mul_inv, one_mul] using (mul_comm (1 / 4 : ℝ) (‖v‖ ^ 2)).le

/-- The log-density path starts at a neighborhood of the quadratic
solution with smooth, strictly plurisubharmonic potentials. -/
theorem eventually_exists_posDef_dirichlet_logDensity_smooth_near_zero {n : ℕ}
    (hn : 0 < n) {g : E n → ℝ} (hg : ContDiff ℝ ∞ g) :
    ∀ᶠ s in 𝓝 (0 : ℝ), ∃ v : E n → ℝ, ContDiffOn ℝ ∞ v (closedUnitBall n) ∧
      (∀ x ∈ unitSphere n, v x = 0) ∧
      (∀ x ∈ unitBall n, (complexHessian v x).PosDef) ∧
      EqOn (fun x => (complexHessian v x).det.re) (fun x => Real.exp (s * g x)) (unitBall n) := by
  apply eventually_exists_posDef_dirichlet_logDensity_smooth hn
    (contDiff_dirichletQuadratic n) hg 0 (a := 1) (l := 1 / 4)
  · intro x hx
    simp [dirichletQuadratic, mem_sphere_zero_iff_norm.mp hx]
  · intro x _
    rw [complexHessian_dirichletQuadratic]
    exact Matrix.PosDef.one
  · intro x _
    simp [complexHessian_dirichletQuadratic]
  · exact zero_lt_one
  · norm_num
  · intro x _
    simp [complexHessian_dirichletQuadratic]
  · intro x _ v
    rw [complexLaplacian_rankOne_quadratic, complexHessian_dirichletQuadratic, inv_one,
      Matrix.one_mulVec, star_star, dotProduct_comm]
    have h := sum_star_complexCoord_mul v
    change star (complexCoord v) ⬝ᵥ complexCoord v = _ at h
    rw [h, Complex.ofReal_re]
    simpa only [div_eq_mul_inv, one_mul] using (mul_comm (1 / 4 : ℝ) (‖v‖ ^ 2)).le

end KEBall
