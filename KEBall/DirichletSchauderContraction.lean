import KEBall.DirichletCofactorContraction
import DifferentialGeometry.Analysis.Schauder.Elliptic.VariableCoefficient.Basic

/-!
# Exact coefficient interface for the imported Schauder estimates

The Euclidean matrix entries are taken in the project's real orthonormal
basis.  Contracting this matrix with the real Hessian is exactly the real
cofactor contraction, hence the complex determinant linearization.  No
factor or transpose is absorbed into an unspecified source term.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open InnerProductSpace Metric Set
open scoped BigOperators

namespace KEBall

local notation "e[" n "]" => EuclideanSpace.basisFun (Fin (2 * n)) ℝ

noncomputable def dirichletSchauderMatrix {n : ℕ} (A : E n →L[ℝ] E n) :
    Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ :=
  fun i j => inner ℝ (e[n] i) (A (e[n] j))

theorem dirichlet_schauder_matrixLap_eq_contraction {n : ℕ}
    (A : E n →L[ℝ] E n) (D : E n →L[ℝ] E n →L[ℝ] ℝ) :
    DifferentialGeometry.Analysis.Parabolic.Euclidean.matrixLap (dirichletSchauderMatrix A) D =
      dirichletBilinearContraction e[n] A D := by
  unfold DifferentialGeometry.Analysis.Parabolic.Euclidean.matrixLap
    dirichletSchauderMatrix dirichletBilinearContraction
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  have h := congrArg (fun z : E n => D z (e[n] j)) (e[n].sum_repr' (A (e[n] j)))
  simpa only [map_sum, map_smul, _root_.sum_apply, _root_.smul_apply, smul_eq_mul] using h

theorem dirichlet_schauder_matrixLap_cofactor {n : ℕ}
    (H : Matrix (Fin n) (Fin n) ℂ) (D : E n →L[ℝ] E n →L[ℝ] ℝ) :
    DifferentialGeometry.Analysis.Parabolic.Euclidean.matrixLap
        (dirichletSchauderMatrix (dirichletCofactorOfMatrix H)) D =
      (H.adjugate * complexHessianOfRealBilinear D).trace.re := by
  rw [dirichlet_schauder_matrixLap_eq_contraction, dirichletBilinearContraction_cofactor]

theorem abs_dirichletSchauderMatrix_sub_le {n : ℕ}
    (A B : E n →L[ℝ] E n) (i j : Fin (2 * n)) :
    |dirichletSchauderMatrix A i j - dirichletSchauderMatrix B i j| ≤ ‖A - B‖ := by
  unfold dirichletSchauderMatrix
  rw [← inner_sub_right, ← _root_.sub_apply]
  have h := norm_inner_le_norm (𝕜 := ℝ) (e[n] i) ((A - B) (e[n] j))
  rw [Real.norm_eq_abs, e[n].orthonormal.norm_eq_one i, one_mul] at h
  exact h.trans ((A - B).le_opNorm _ |>.trans_eq (by
    rw [e[n].orthonormal.norm_eq_one j, mul_one]))

theorem dirichletSchauderMatrix_holder_of_operator_holder {n : ℕ}
    {A : E n → E n →L[ℝ] E n} {S : Set (E n)} {K α : ℝ}
    (hA : ∀ x ∈ S, ∀ y ∈ S, ‖A x - A y‖ ≤ K * ‖x - y‖ ^ α)
    (i j : Fin (2 * n)) :
    ∀ x ∈ S, ∀ y ∈ S,
      |dirichletSchauderMatrix (A x) i j - dirichletSchauderMatrix (A y) i j| ≤
        K * ‖x - y‖ ^ α := by
  intro x hx y hy
  exact (abs_dirichletSchauderMatrix_sub_le (A x) (A y) i j).trans (hA x hx y hy)

theorem dirichlet_variableMatrixLap_eq_contraction {n : ℕ}
    (a : Fin (2 * n) → Fin (2 * n) → BoundedContinuousFunction (E n) ℝ)
    (D : BoundedContinuousFunction (E n) (E n →L[ℝ] E n →L[ℝ] ℝ))
    (A : E n →L[ℝ] E n) {x : E n}
    (hA : ∀ i j, a i j x = dirichletSchauderMatrix A i j) :
    DifferentialGeometry.Analysis.Schauder.variableMatrixLap a D x =
      dirichletBilinearContraction e[n] A (D x) := by
  rw [DifferentialGeometry.Analysis.Schauder.variableMatrixLap_apply]
  have he : (fun i j => a i j x) = dirichletSchauderMatrix A := by
    ext i j
    exact hA i j
  rw [he, dirichlet_schauder_matrixLap_eq_contraction]

end KEBall
