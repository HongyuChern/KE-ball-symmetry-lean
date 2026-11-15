import KEBall.DirichletWeakDivergenceLimit
import KEBall.DirichletBilinearContraction

/-!
# Exact real/complex cofactor contraction

The factor `1 / 8` in the real cofactor operator, the factor `2` in
Hermitian realification, and the factor `1 / 4` in the complex Hessian
are retained explicitly.  This identity connects the real directional
frame to the existing positive-Hermitian log-determinant inequality.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open InnerProductSpace Matrix
open scoped BigOperators ComplexOrder

noncomputable section

namespace KEBall

local notation "e[" n "]" => EuclideanSpace.basisFun (Fin (2 * n)) ℝ

def dirichletRieszOfBilinear {n : ℕ} (D : E n →L[ℝ] E n →L[ℝ] ℝ) : E n →L[ℝ] E n :=
  (InnerProductSpace.toDual ℝ (E n)).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp D

theorem dirichletRieszOfBilinear_coordinateProduct {n : ℕ} (i j : Fin (2 * n)) :
    dirichletRieszOfBilinear (coordinateProduct i j) = rankOne ℝ (e[n] j) (e[n] i) := by
  ext v : 1
  apply ext_inner_right ℝ
  intro w
  have h : inner ℝ ((InnerProductSpace.toDual ℝ (E n)).symm (coordinateProduct i j v)) w =
      coordinateProduct i j v w :=
    congrArg (fun f : E n →L[ℝ] ℝ => f w)
      ((InnerProductSpace.toDual ℝ (E n)).apply_symm_apply (coordinateProduct i j v))
  change inner ℝ ((InnerProductSpace.toDual ℝ (E n)).symm (coordinateProduct i j v)) w = _
  rw [h]
  simp only [coordinateProduct_apply, rankOne_apply, EuclideanSpace.basisFun_apply,
    real_inner_smul_left, EuclideanSpace.inner_single_left, map_one, one_mul]

/-- Real bilinear contraction is exactly the complex determinant
linearization.  The equality holds for every real bilinear form. -/
theorem dirichletBilinearContraction_cofactor {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (D : E n →L[ℝ] E n →L[ℝ] ℝ) :
    dirichletBilinearContraction e[n] (dirichletCofactorOfMatrix A) D =
      (A.adjugate * complexHessianOfRealBilinear D).trace.re := by
  let R := (InnerProductSpace.toDual ℝ (E n)).symm.toContinuousLinearEquiv.toContinuousLinearMap
  let L := ContinuousLinearMap.compL ℝ (E n) (E n →L[ℝ] ℝ) (E n) R
  let F : (E n →L[ℝ] E n →L[ℝ] ℝ) →ₗ[ℝ] ℝ :=
    (dirichletBilinearContractionLinearMap e[n] D).comp L.toLinearMap
  have hF (i j : Fin (2 * n)) : F (coordinateProduct i j) = D (e[n] j) (e[n] i) := by
    change dirichletBilinearContraction e[n] (dirichletRieszOfBilinear (coordinateProduct i j)) D = _
    rw [dirichletRieszOfBilinear_coordinateProduct, dirichletBilinearContraction_rankOne_general]
  have hFsub (P Q : E n →L[ℝ] E n →L[ℝ] ℝ) : F (P - Q) = F P - F Q := by
    have he : P - Q = P + (-1 : ℝ) • Q := by module
    rw [he, map_add, map_smul]
    simp only [smul_eq_mul, neg_one_mul]
    ring
  let S : ℝ := ∑ i : Fin n, ∑ j : Fin n,
    ((A.adjugate i j).re * (D (realDirection j) (realDirection i) + D (imagDirection j) (imagDirection i)) +
      (A.adjugate i j).im * (D (imagDirection j) (realDirection i) - D (realDirection j) (imagDirection i)))
  have hReal : F (hermitianRealification A.adjugate) = 2 * S := by
    simp only [hermitianRealification, map_smul, map_sum, map_add, hFsub, hF, smul_eq_mul]
    simp only [S, EuclideanSpace.basisFun_apply, realDirection, imagDirection]
  have hTrace : (A.adjugate * complexHessianOfRealBilinear D).trace.re = (1 / 4 : ℝ) * S := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Complex.re_sum, S, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    norm_num [complexHessianOfRealBilinear, Complex.mul_re, Complex.mul_im]
    ring
  rw [hTrace]
  calc
    _ = (1 / 8 : ℝ) * F (hermitianRealification A.adjugate) := by
      change (dirichletBilinearContractionLinearMap e[n] D)
        ((8 : ℝ)⁻¹ • L (hermitianRealification A.adjugate)) = _
      rw [map_smul]
      simp only [smul_eq_mul, one_div]
      rfl
    _ = (1 / 4 : ℝ) * S := by rw [hReal]; ring

end KEBall
