import KEBall.DirichletIteratedTensorDifferences

/-!
# The highest actual Hessian in an arbitrary spatial difference

The leading term is the iterated inverse pullback of the highest potential
difference. Every remaining term contains a strictly lower potential difference.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Metric Set
open scoped BigOperators ContDiff

namespace KEBall

theorem norm_dirichletBilinearPullback_iterate_sub_le {n : ℕ}
    (R : E n ≃ₗᵢ[ℝ] E n) (H : E n →L[ℝ] E n →L[ℝ] ℝ) (k : ℕ) :
    ‖(dirichletBilinearPullbackCLM R)^[k] H - H‖ ≤
      (k : ℝ) * ‖dirichletBilinearPullbackCLM R - ContinuousLinearMap.id ℝ _‖ * ‖H‖ := by
  let L := dirichletBilinearPullbackCLM R
  have hL (K : E n →L[ℝ] E n →L[ℝ] ℝ) : ‖L K‖ ≤ ‖K‖ :=
    norm_dirichletBilinearPullback_le R K
  have hDiff : ‖L H - H‖ ≤ ‖L - ContinuousLinearMap.id ℝ _‖ * ‖H‖ :=
    (L - ContinuousLinearMap.id ℝ _).le_opNorm H
  induction k with
  | zero => simp
  | succ k ih =>
    change ‖L^[k + 1] H - H‖ ≤ _
    rw [Function.iterate_succ_apply']
    have he : L (L^[k] H) - H = L (L^[k] H - H) + (L H - H) := by rw [map_sub]; abel
    rw [he]
    calc
      _ ≤ ‖L^[k] H - H‖ + ‖L - ContinuousLinearMap.id ℝ _‖ * ‖H‖ :=
        (norm_add_le _ _).trans (add_le_add (hL _) hDiff)
      _ ≤ (k : ℝ) * ‖L - ContinuousLinearMap.id ℝ _‖ * ‖H‖ +
          ‖L - ContinuousLinearMap.id ℝ _‖ * ‖H‖ := add_le_add ih le_rfl
      _ = _ := by simp only [Nat.cast_add, Nat.cast_one]; ring

theorem norm_dirichletIteratedHessian_lower_remainder_le {n : ℕ}
    {u : E n → ℝ} (hu : ContDiffOn ℝ 2 u (closedUnitBall n))
    (S : E n →L[ℝ] E n) (hS : star S = -S) {t : ℝ} (ht : t ≠ 0)
    (k : ℕ) {x : E n} (hx : x ∈ closedUnitBall n) :
    let R := orthogonalFlow S hS t
    let L := dirichletBilinearPullbackCLM R.symm
    ‖dirichletIteratedFieldDifference R t (dirichletWithinRealHessian u) k x -
      L^[k] (dirichletWithinRealHessian (dirichletIteratedOrthogonalDifference R t u k) x)‖ ≤
      (1 + 2 * ‖S‖) ^ k * ∑ j ∈ Finset.range k,
        ‖dirichletWithinRealHessian (dirichletIteratedOrthogonalDifference R t u j) x‖ := by
  dsimp only
  let R := orthogonalFlow S hS t
  let L := dirichletBilinearPullbackCLM R.symm
  let C := dirichletBilinearPullbackIncrement R.symm t
  let M := 2 * ‖S‖
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hA : 0 ≤ 1 + M := by positivity
  have hL (K : E n →L[ℝ] E n →L[ℝ] ℝ) : ‖L K‖ ≤ ‖K‖ :=
    norm_dirichletBilinearPullback_le R.symm K
  have hC (K : E n →L[ℝ] E n →L[ℝ] ℝ) : ‖C K‖ ≤ M * ‖K‖ :=
    (C.le_opNorm K).trans (mul_le_mul_of_nonneg_right
      (norm_dirichletBilinearPullbackIncrement_flow_symm_le S hS ht) (norm_nonneg K))
  induction k generalizing u with
  | zero => simp [dirichletIteratedFieldDifference, dirichletIteratedOrthogonalDifference]
  | succ k ih =>
    let q := dirichletOrthogonalDifference R t u
    have hq : ContDiffOn ℝ 2 q (closedUnitBall n) := contDiffOn_dirichletOrthogonalDifference R t hu
    let F (j : ℕ) := ‖dirichletWithinRealHessian (dirichletIteratedOrthogonalDifference R t u j) x‖
    let Z := ∑ j ∈ Finset.range (k + 1), F j
    have hSum : (∑ j ∈ Finset.range k, F (j + 1)) ≤ Z := by
      dsimp only [Z]
      rw [Finset.sum_range_succ' F k]
      exact le_add_of_nonneg_right (norm_nonneg (dirichletWithinRealHessian u x))
    have hLow : ‖dirichletIteratedFieldDifference R t (dirichletWithinRealHessian q) k x -
        L^[k] (dirichletWithinRealHessian (dirichletIteratedOrthogonalDifference R t q k) x)‖ ≤
        (1 + M) ^ k * Z := by
      have h := ih hq
      have h' : ‖dirichletIteratedFieldDifference R t (dirichletWithinRealHessian q) k x -
          L^[k] (dirichletWithinRealHessian (dirichletIteratedOrthogonalDifference R t q k) x)‖ ≤
          (1 + M) ^ k * ∑ j ∈ Finset.range k, F (j + 1) := by
        simpa only [q, R, L, M, F, dirichletIteratedOrthogonalDifference_succ_right] using h
      exact h'.trans (mul_le_mul_of_nonneg_left hSum (pow_nonneg hA k))
    have hAll : ‖dirichletIteratedFieldDifference R t (dirichletWithinRealHessian u) k x‖ ≤
        (1 + M) ^ k * Z := norm_dirichletIteratedFieldDifference_withinHessian_le hu S hS ht k hx
    have he : dirichletIteratedFieldDifference R t (dirichletWithinRealHessian u) (k + 1) x -
        L^[k + 1] (dirichletWithinRealHessian (dirichletIteratedOrthogonalDifference R t u (k + 1)) x) =
        L (dirichletIteratedFieldDifference R t (dirichletWithinRealHessian q) k x -
          L^[k] (dirichletWithinRealHessian (dirichletIteratedOrthogonalDifference R t q k) x)) +
        C (dirichletIteratedFieldDifference R t (dirichletWithinRealHessian u) k x) := by
      rw [dirichletIteratedFieldDifference_withinHessian_succ R t hu k hx,
        Function.iterate_succ_apply', map_sub]
      simp only [q, dirichletIteratedOrthogonalDifference_succ_right]
      change L _ + C _ - L _ = L _ - L _ + C _
      abel
    change _ ≤ (1 + M) ^ (k + 1) * Z
    rw [he]
    calc
      _ ≤ ‖dirichletIteratedFieldDifference R t (dirichletWithinRealHessian q) k x -
          L^[k] (dirichletWithinRealHessian (dirichletIteratedOrthogonalDifference R t q k) x)‖ +
          M * ‖dirichletIteratedFieldDifference R t (dirichletWithinRealHessian u) k x‖ :=
        (norm_add_le _ _).trans (add_le_add (hL _) (hC _))
      _ ≤ (1 + M) ^ k * Z + M * ((1 + M) ^ k * Z) :=
        add_le_add hLow (mul_le_mul_of_nonneg_left hAll hM)
      _ = _ := by rw [pow_succ]; ring

theorem norm_dirichletIteratedFieldDifference_sub_highestHessian_le {n : ℕ}
    {u : E n → ℝ} (hu : ContDiffOn ℝ 2 u (closedUnitBall n))
    (S : E n →L[ℝ] E n) (hS : star S = -S) {t : ℝ} (ht : t ≠ 0)
    (k : ℕ) {x : E n} (hx : x ∈ closedUnitBall n) :
    let R := orthogonalFlow S hS t
    ‖dirichletIteratedFieldDifference R t (dirichletWithinRealHessian u) k x -
      dirichletWithinRealHessian (dirichletIteratedOrthogonalDifference R t u k) x‖ ≤
      (1 + 2 * ‖S‖) ^ k * ∑ j ∈ Finset.range k,
        ‖dirichletWithinRealHessian (dirichletIteratedOrthogonalDifference R t u j) x‖ +
      (2 * k * ‖S‖ * |t|) *
        ‖dirichletWithinRealHessian (dirichletIteratedOrthogonalDifference R t u k) x‖ := by
  dsimp only
  let R := orthogonalFlow S hS t
  let L := dirichletBilinearPullbackCLM R.symm
  let H := dirichletWithinRealHessian (dirichletIteratedOrthogonalDifference R t u k) x
  have hInc : ‖L - ContinuousLinearMap.id ℝ _‖ ≤ 2 * ‖S‖ * |t| := by
    simpa only [L, R, orthogonalFlow_symm_eq_neg, abs_neg] using
      norm_dirichletBilinearPullbackCLM_flow_sub_id_le S hS (-t)
  have hMove : ‖L^[k] H - H‖ ≤ (2 * k * ‖S‖ * |t|) * ‖H‖ := by
    have h := norm_dirichletBilinearPullback_iterate_sub_le R.symm H k
    exact h.trans ((mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hInc (Nat.cast_nonneg k)) (norm_nonneg H)).trans_eq (by ring))
  exact (norm_sub_le_norm_sub_add_norm_sub
    (dirichletIteratedFieldDifference R t (dirichletWithinRealHessian u) k x) (L^[k] H) H).trans
      (add_le_add (norm_dirichletIteratedHessian_lower_remainder_le hu S hS ht k hx) hMove)

end KEBall
