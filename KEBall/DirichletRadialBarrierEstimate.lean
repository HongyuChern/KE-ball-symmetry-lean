import KEBall.DirichletRadialBarrier

/-!
# Uniform elliptic bounds for the exponential annular barrier

The constants use the real dimension `2 * n`, the operator norm bound of
the actual coefficient, and its coercivity constant.  The source term is
not discarded in subsequent comparison arguments.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open InnerProductSpace Metric Set
open scoped BigOperators

namespace KEBall

theorem dirichlet_coefficient_trace_le_norm {n : ℕ}
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n))
    (A : E n →L[ℝ] E n) :
    (∑ i : Fin (2 * n), inner ℝ (A (b i)) (b i)) ≤ (2 * n : ℝ) * ‖A‖ := by
  calc
    _ ≤ ∑ i : Fin (2 * n), ‖A‖ := by
      apply Finset.sum_le_sum
      intro i _
      have hi : ‖b i‖ = 1 := b.orthonormal.norm_eq_one i
      calc
        inner ℝ (A (b i)) (b i) ≤ ‖A (b i)‖ * ‖b i‖ := real_inner_le_norm _ _
        _ ≤ ‖A‖ * ‖b i‖ * ‖b i‖ :=
          mul_le_mul_of_nonneg_right (A.le_opNorm _) (norm_nonneg _)
        _ = ‖A‖ := by rw [hi]; ring
    _ = (2 * n : ℝ) * ‖A‖ := by simp

theorem dirichletBilinearContraction_radialExponential_lower_bound {n : ℕ}
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n))
    {A : E n →L[ℝ] E n} {ell Λ κ : ℝ} (hκ : 0 ≤ κ)
    (hA : ‖A‖ ≤ Λ)
    (hCoer : ∀ v : E n, ell * ‖v‖ ^ 2 ≤ inner ℝ (A v) v)
    (z x : E n) :
    dirichletRadialExponential κ z x *
      (4 * κ ^ 2 * ell * ‖x - z‖ ^ 2 - 2 * κ * (2 * n : ℝ) * Λ) ≤
      dirichletBilinearContraction b A (realHessian (dirichletRadialExponential κ z) x) := by
  rw [dirichletBilinearContraction_radialExponential]
  apply mul_le_mul_of_nonneg_left _ (le_of_lt (Real.exp_pos _))
  have hTrace : (∑ i : Fin (2 * n), inner ℝ (A (b i)) (b i)) ≤ (2 * n : ℝ) * Λ :=
    (dirichlet_coefficient_trace_le_norm b A).trans
      (mul_le_mul_of_nonneg_left hA (by positivity))
  have hFirst := mul_le_mul_of_nonneg_left (hCoer (x - z))
    (by positivity : 0 ≤ 4 * κ ^ 2)
  have hSecond := mul_le_mul_of_nonneg_left hTrace (by positivity : 0 ≤ 2 * κ)
  nlinarith only [hFirst, hSecond]

/-- Strict positivity on an annulus, with an explicit lower bound. -/
theorem dirichletBilinearContraction_radialExponential_pos {n : ℕ}
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n))
    {A : E n →L[ℝ] E n} {ell Λ κ r : ℝ}
    (hell : 0 < ell) (hκ : 0 < κ) (hr : 0 < r)
    (hA : ‖A‖ ≤ Λ)
    (hCoer : ∀ v : E n, ell * ‖v‖ ^ 2 ≤ inner ℝ (A v) v)
    (hScale : (2 * n : ℝ) * Λ ≤ κ * ell * r ^ 2)
    {z x : E n} (hAnnulus : r ≤ ‖x - z‖) :
    0 < dirichletBilinearContraction b A (realHessian (dirichletRadialExponential κ z) x) := by
  apply lt_of_lt_of_le _
    (dirichletBilinearContraction_radialExponential_lower_bound b hκ.le hA hCoer z x)
  apply mul_pos (Real.exp_pos _)
  have hR : r ^ 2 ≤ ‖x - z‖ ^ 2 := sq_le_sq₀ hr.le (norm_nonneg _) |>.mpr hAnnulus
  have h1 := mul_le_mul_of_nonneg_left hScale (by positivity : 0 ≤ 2 * κ)
  have h2 := mul_le_mul_of_nonneg_left hR (by positivity : 0 ≤ 4 * κ ^ 2 * ell)
  have hp : 0 < 2 * κ ^ 2 * ell * r ^ 2 := by positivity
  nlinarith only [h1, h2, hp]

end KEBall
