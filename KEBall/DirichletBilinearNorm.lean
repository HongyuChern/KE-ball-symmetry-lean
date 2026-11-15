import KEBall.DirichletBilinearReconstruction

/-! Operator-norm bounds from the actual orthonormal Hessian entries. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open InnerProductSpace
open scoped BigOperators

namespace KEBall

local notation "e[" n "]" => EuclideanSpace.basisFun (Fin (2 * n)) ℝ

theorem norm_dirichletBilinearBasis {n : ℕ} (i j : Fin (2 * n)) :
    ‖dirichletBilinearBasis i j‖ = 1 := by
  simp only [dirichletBilinearBasis, ContinuousLinearMap.norm_smulRight_apply,
    innerSL_apply_norm, OrthonormalBasis.norm_eq_one, one_mul]

set_option maxHeartbeats 1000000 in
theorem norm_dirichlet_bilinear_le_sum_entries {n : ℕ}
    (D : E n →L[ℝ] E n →L[ℝ] ℝ) :
    ‖D‖ ≤ ∑ i : Fin (2 * n), ∑ j : Fin (2 * n), |D (e[n] i) (e[n] j)| := by
  letI : NormedAddCommGroup (E n →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
  letI : NormedSpace ℝ (E n →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
  letI : NormedAddCommGroup (E n →L[ℝ] E n →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedAddCommGroup
  letI : NormedSpace ℝ (E n →L[ℝ] E n →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedSpace
  calc
    ‖D‖ = ‖∑ i : Fin (2 * n), ∑ j : Fin (2 * n),
        D (e[n] i) (e[n] j) • dirichletBilinearBasis i j‖ :=
      congrArg norm (dirichletBilinearFromEntries_basis D).symm
    _ ≤ ∑ i : Fin (2 * n), ∑ j : Fin (2 * n),
        ‖D (e[n] i) (e[n] j) • dirichletBilinearBasis i j‖ := by
      let T (i j : Fin (2 * n)) : E n →L[ℝ] E n →L[ℝ] ℝ :=
        D (e[n] i) (e[n] j) • dirichletBilinearBasis i j
      have hi (i : Fin (2 * n)) : ‖∑ j, T i j‖ ≤ ∑ j, ‖T i j‖ :=
        norm_sum_le Finset.univ (fun j : Fin (2 * n) => T i j)
      have ho : ‖∑ i, ∑ j, T i j‖ ≤ ∑ i, ‖∑ j, T i j‖ :=
        norm_sum_le Finset.univ (fun i : Fin (2 * n) => ∑ j, T i j)
      exact ho.trans (Finset.sum_le_sum fun i _ => hi i)
    _ = ∑ i : Fin (2 * n), ∑ j : Fin (2 * n), |D (e[n] i) (e[n] j)| := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [norm_smul, norm_dirichletBilinearBasis, mul_one, Real.norm_eq_abs]

theorem norm_dirichlet_bilinear_le_of_entries {n : ℕ}
    (D : E n →L[ℝ] E n →L[ℝ] ℝ) {B : ℝ}
    (h : ∀ i j : Fin (2 * n), |D (e[n] i) (e[n] j)| ≤ B) :
    ‖D‖ ≤ (2 * n : ℝ) ^ 2 * B := by
  calc
    ‖D‖ ≤ ∑ i : Fin (2 * n), ∑ j : Fin (2 * n), |D (e[n] i) (e[n] j)| :=
      norm_dirichlet_bilinear_le_sum_entries D
    _ ≤ ∑ _ : Fin (2 * n), ∑ _ : Fin (2 * n), B :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h i j
    _ = _ := by simp [nsmul_eq_mul, pow_two, mul_assoc]

end KEBall
