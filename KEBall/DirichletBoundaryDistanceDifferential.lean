import KEBall.DirichletTangentBall
import KEBall.DirichletCofactorSourceCorrection

/-! The actual differential of rho and its contribution to a remainder. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open InnerProductSpace Metric Set
open scoped ContDiff Gradient

namespace KEBall

theorem gradient_dirichletBoundaryDistanceProxy {n : ℕ} (x : E n) :
    ∇ (@dirichletBoundaryDistanceProxy n) x = -x := by
  have he : (@dirichletBoundaryDistanceProxy n) =
      dirichletSourceQuadratic (1 / 2) 1 (0 : E n) := by
    ext y
    simp only [dirichletBoundaryDistanceProxy, dirichletSourceQuadratic, sub_zero, one_pow]
    ring
  rw [he, gradient_dirichletSourceQuadratic]
  norm_num

theorem fderiv_dirichletBoundaryDistanceProxy {n : ℕ} (x : E n) :
    fderiv ℝ (@dirichletBoundaryDistanceProxy n) x = -(innerSL ℝ x) := by
  ext v
  rw [← inner_gradient_left, gradient_dirichletBoundaryDistanceProxy, inner_neg_left]
  rfl

theorem norm_fderiv_dirichletBoundaryDistanceProxy_sub_le {n : ℕ} (x y : E n) :
    ‖fderiv ℝ (@dirichletBoundaryDistanceProxy n) x -
      fderiv ℝ (@dirichletBoundaryDistanceProxy n) y‖ ≤ ‖x - y‖ := by
  rw [fderiv_dirichletBoundaryDistanceProxy, fderiv_dirichletBoundaryDistanceProxy]
  have he : -(innerSL ℝ x) - -(innerSL ℝ y) = -(innerSL ℝ (x - y)) := by
    rw [map_sub]
    abel
  rw [he, norm_neg]
  exact ((innerSL ℝ).le_opNorm (x - y)).trans
    ((mul_le_mul_of_nonneg_right (norm_innerSL_le (𝕜 := ℝ) (E := E n))
      (norm_nonneg (x - y))).trans_eq (one_mul _))

theorem dirichlet_sub_boundaryProxy_derivative_holder {n : ℕ}
    {q : E n → ℝ} {s : Set (E n)}
    (hq : ∀ x ∈ s, DifferentiableAt ℝ q x)
    {H β : ℝ} (hβ1 : β ≤ 1)
    (hHolder : ∀ x ∈ s, ∀ y ∈ s,
      ‖fderiv ℝ q x - fderiv ℝ q y‖ ≤ H * ‖x - y‖ ^ β)
    (hDiam : ∀ x ∈ s, ∀ y ∈ s, ‖x - y‖ ≤ 1) (a : ℝ) :
    ∀ x ∈ s, ∀ y ∈ s,
      ‖fderiv ℝ (fun z => q z - a * dirichletBoundaryDistanceProxy z) x -
        fderiv ℝ (fun z => q z - a * dirichletBoundaryDistanceProxy z) y‖ ≤
        (H + |a|) * ‖x - y‖ ^ β := by
  have hρ (z : E n) :=
    ((contDiff_dirichletBoundaryDistanceProxy (n := n)).differentiable (by simp) z).hasFDerivAt
  have he (z : E n) (hz : z ∈ s) :
      fderiv ℝ (fun z => q z - a * dirichletBoundaryDistanceProxy z) z =
        fderiv ℝ q z - a • fderiv ℝ (@dirichletBoundaryDistanceProxy n) z := by
    exact ((hq z hz).hasFDerivAt.sub ((hρ z).const_mul a)).fderiv
  intro x hx y hy
  rw [he x hx, he y hy]
  have hSub :
      (fderiv ℝ q x - a • fderiv ℝ (@dirichletBoundaryDistanceProxy n) x) -
        (fderiv ℝ q y - a • fderiv ℝ (@dirichletBoundaryDistanceProxy n) y) =
      (fderiv ℝ q x - fderiv ℝ q y) - a •
        (fderiv ℝ (@dirichletBoundaryDistanceProxy n) x -
          fderiv ℝ (@dirichletBoundaryDistanceProxy n) y) := by
    rw [smul_sub]
    abel
  rw [hSub]
  have hPow := Real.self_le_rpow_of_le_one (norm_nonneg (x - y)) (hDiam x hx y hy) hβ1
  calc
    _ ≤ ‖fderiv ℝ q x - fderiv ℝ q y‖ + |a| *
        ‖fderiv ℝ (@dirichletBoundaryDistanceProxy n) x -
          fderiv ℝ (@dirichletBoundaryDistanceProxy n) y‖ := by
      simpa only [norm_smul, Real.norm_eq_abs] using norm_sub_le
        (fderiv ℝ q x - fderiv ℝ q y)
        (a • (fderiv ℝ (@dirichletBoundaryDistanceProxy n) x -
          fderiv ℝ (@dirichletBoundaryDistanceProxy n) y))
    _ ≤ H * ‖x - y‖ ^ β + |a| * ‖x - y‖ ^ β :=
      add_le_add (hHolder x hx y hy)
        (mul_le_mul_of_nonneg_left
          ((norm_fderiv_dirichletBoundaryDistanceProxy_sub_le x y).trans hPow) (abs_nonneg a))
    _ = _ := by ring

end KEBall
