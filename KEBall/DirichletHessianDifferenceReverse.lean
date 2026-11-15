import KEBall.DirichletIteratedTensorDifferences

/-! The reverse pointwise comparison: actual difference Hessians from spatial tensor differences. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 500000
open Filter Metric Set
open scoped BigOperators ContDiff
namespace KEBall

theorem dirichletWithinHessian_difference_eq_tensor_difference {n : ℕ}
    (R : E n ≃ₗᵢ[ℝ] E n) (t : ℝ) {u : E n → ℝ}
    (hu : ContDiffOn ℝ 2 u (closedUnitBall n)) {x : E n} (hx : x ∈ closedUnitBall n) :
    dirichletWithinRealHessian (dirichletOrthogonalDifference R t u) x =
      dirichletBilinearPullbackCLM R (dirichletFieldDifference R t (dirichletWithinRealHessian u) x) +
      dirichletBilinearPullbackIncrement R t (dirichletWithinRealHessian u x) := by
  rw [dirichletWithinRealHessian_orthogonal_difference R t hu hx]
  simp only [dirichletFieldDifference, map_smul, map_sub, dirichletBilinearPullbackIncrement,
    _root_.smul_apply, _root_.sub_apply, ContinuousLinearMap.id_apply,
    dirichletBilinearPullbackCLM_apply, smul_sub]
  abel

theorem dirichletIteratedFieldDifference_differenceHessian {n : ℕ}
    (R : E n ≃ₗᵢ[ℝ] E n) (t : ℝ) {u : E n → ℝ}
    (hu : ContDiffOn ℝ 2 u (closedUnitBall n)) (k : ℕ)
    {x : E n} (hx : x ∈ closedUnitBall n) :
    dirichletIteratedFieldDifference R t (dirichletWithinRealHessian (dirichletOrthogonalDifference R t u)) k x =
      dirichletBilinearPullbackCLM R
        (dirichletIteratedFieldDifference R t (dirichletWithinRealHessian u) (k+1) x) +
      dirichletBilinearPullbackIncrement R t
        (dirichletIteratedFieldDifference R t (dirichletWithinRealHessian u) k x) := by
  have he := fun y hy => dirichletWithinHessian_difference_eq_tensor_difference R t hu (x := y) hy
  rw [dirichletIteratedFieldDifference_congr_closed R t he k hx,
    dirichletIteratedFieldDifference_add, dirichletIteratedFieldDifference_clm,
    dirichletIteratedFieldDifference_clm, dirichletIteratedFieldDifference_succ_right]

theorem norm_dirichlet_iterated_difference_hessian_le_tensor_differences {n : ℕ}
    {u : E n → ℝ} (hu : ContDiffOn ℝ 2 u (closedUnitBall n))
    (S : E n →L[ℝ] E n) (hS : star S = -S) {t : ℝ} (ht : t ≠ 0)
    (k : ℕ) {x : E n} (hx : x ∈ closedUnitBall n) :
    ‖dirichletWithinRealHessian (dirichletIteratedOrthogonalDifference (orthogonalFlow S hS t) t u k) x‖ ≤
      (1 + 2*‖S‖)^k * ∑ j ∈ Finset.range (k+1),
        ‖dirichletIteratedFieldDifference (orthogonalFlow S hS t) t (dirichletWithinRealHessian u) j x‖ := by
  let R := orthogonalFlow S hS t
  let M : ℝ := 2*‖S‖
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hA : 0 ≤ 1+M := by positivity
  induction k generalizing u with
  | zero => simp [dirichletIteratedOrthogonalDifference, dirichletIteratedFieldDifference]
  | succ k ih =>
    let q := dirichletOrthogonalDifference R t u
    let F (j : ℕ) := ‖dirichletIteratedFieldDifference R t (dirichletWithinRealHessian u) j x‖
    let Z := ∑ j ∈ Finset.range (k+2), F j
    have hC (H : E n →L[ℝ] E n →L[ℝ] ℝ) :
        ‖dirichletBilinearPullbackIncrement R t H‖ ≤ M*‖H‖ :=
      ((dirichletBilinearPullbackIncrement R t).le_opNorm H).trans
        (mul_le_mul_of_nonneg_right (norm_dirichletBilinearPullbackCLM_normalized_increment_le S hS ht)
          (norm_nonneg H))
    have hEach (j : ℕ) :
        ‖dirichletIteratedFieldDifference R t (dirichletWithinRealHessian q) j x‖ ≤ F (j+1)+M*F j := by
      rw [dirichletIteratedFieldDifference_differenceHessian R t hu j hx]
      exact (norm_add_le _ _).trans (add_le_add (norm_dirichletBilinearPullback_le R _) (hC _))
    have hSum0 : (∑ j ∈ Finset.range (k+1), F j) ≤ Z := by
      dsimp only [Z]
      rw [show k+2=k+1+1 by omega, Finset.sum_range_succ F (k+1)]
      exact le_add_of_nonneg_right (show 0 ≤ F (k+1) from norm_nonneg _)
    have hSum1 : (∑ j ∈ Finset.range (k+1), F (j+1)) ≤ Z := by
      dsimp only [Z]
      rw [show k+2=k+1+1 by omega, Finset.sum_range_succ' F (k+1)]
      exact le_add_of_nonneg_right (show 0 ≤ F 0 from norm_nonneg _)
    have hSum : (∑ j ∈ Finset.range (k+1),
        ‖dirichletIteratedFieldDifference R t (dirichletWithinRealHessian q) j x‖) ≤ (1+M)*Z := by
      calc
        _ ≤ ∑ j ∈ Finset.range (k+1), (F (j+1)+M*F j) := Finset.sum_le_sum (fun j _ => hEach j)
        _ = (∑ j ∈ Finset.range (k+1), F (j+1)) + M*(∑ j ∈ Finset.range (k+1), F j) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]
        _ ≤ Z+M*Z := add_le_add hSum1 (mul_le_mul_of_nonneg_left hSum0 hM)
        _ = (1+M)*Z := by ring
    have h := (ih (u := q) (contDiffOn_dirichletOrthogonalDifference R t hu)).trans
      (mul_le_mul_of_nonneg_left hSum (pow_nonneg hA k))
    simpa only [q, R, M, Z, F, dirichletIteratedOrthogonalDifference_succ_right,
      pow_succ, mul_assoc] using h

end KEBall
