import Drafts.KEBall.ExteriorEvaluation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
Stage13 SOURCE_DRAFT_UNCOMPILED.
Recover every complex matrix coefficient from the actual real-coordinate
evaluation of its D0 exterior representative. All complex matrices are
allowed; Hermitian symmetry is only needed for the real bilinear consumer.
This is a source-level proof candidate, not a kernel success receipt.
-/
set_option autoImplicit false
open scoped BigOperators

namespace KEBall

theorem hermitianPairing_real_real {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (i j : Fin n) :
    hermitianPairing A (realDirection i) (realDirection j) = A i j := by
  classical
  simp [hermitianPairing, complexCoord_realDirection, eq_comm, mul_ite, ite_mul]

theorem hermitianPairing_real_imag {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (i j : Fin n) :
    hermitianPairing A (realDirection i) (imagDirection j) = A i j * (-Complex.I) := by
  classical
  simp [hermitianPairing, complexCoord_realDirection, complexCoord_imagDirection,
    Complex.star_def, eq_comm, mul_ite, ite_mul, apply_ite]

theorem hermitianPairing_imag_real {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (i j : Fin n) :
    hermitianPairing A (imagDirection i) (realDirection j) = A i j * Complex.I := by
  classical
  simp [hermitianPairing, complexCoord_realDirection, complexCoord_imagDirection,
    eq_comm, mul_ite, ite_mul]

theorem exteriorEvaluation_matrixDZero_real_real {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    exteriorEvaluation ![realDirection i, realDirection j] (matrixDZeroExterior A) =
      Complex.I / (2 * (Real.pi : ℂ)) * (A i j - A j i) := by
  rw [exteriorEvaluation_matrixDZero, hermitianPairing_real_real,
    hermitianPairing_real_real]

theorem exteriorEvaluation_matrixDZero_real_imag {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    exteriorEvaluation ![realDirection i, imagDirection j] (matrixDZeroExterior A) =
      (A i j + A j i) / (2 * (Real.pi : ℂ)) := by
  rw [exteriorEvaluation_matrixDZero, hermitianPairing_real_imag,
    hermitianPairing_imag_real]
  calc
    _ = -(Complex.I * Complex.I) * ((A i j + A j i) / (2 * (Real.pi : ℂ))) := by
      simp only [div_eq_mul_inv]
      ring
    _ = _ := by rw [Complex.I_mul_I]; ring

/-- Reconstruct the ordered coefficient A_ij, including its antisymmetric part. -/
noncomputable def exteriorCoefficient {n : ℕ} (F : CovectorExterior n) (i j : Fin n) : ℂ :=
  (Real.pi : ℂ) *
    (exteriorEvaluation ![realDirection i, imagDirection j] F -
      Complex.I * exteriorEvaluation ![realDirection i, realDirection j] F)

theorem exteriorCoefficient_matrixDZero {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    exteriorCoefficient (matrixDZeroExterior A) i j = A i j := by
  rw [exteriorCoefficient, exteriorEvaluation_matrixDZero_real_imag,
    exteriorEvaluation_matrixDZero_real_real]
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  calc
    _ = ((A i j + A j i) - (Complex.I * Complex.I) * (A i j - A j i)) / 2 := by
      field_simp [hp]
    _ = A i j := by rw [Complex.I_mul_I]; ring

theorem matrixDZeroExterior_injective {n : ℕ} :
    Function.Injective (matrixDZeroExterior (n := n)) := by
  intro A B h
  ext i j
  calc
    A i j = exteriorCoefficient (matrixDZeroExterior A) i j :=
      (exteriorCoefficient_matrixDZero A i j).symm
    _ = exteriorCoefficient (matrixDZeroExterior B) i j := by rw [h]
    _ = B i j := exteriorCoefficient_matrixDZero B i j

theorem matrixDZeroExterior_eq_iff {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℂ) :
    matrixDZeroExterior A = matrixDZeroExterior B ↔ A = B :=
  ⟨fun h => matrixDZeroExterior_injective h, congrArg matrixDZeroExterior⟩

theorem matrixDZeroExterior_transpose_eq_iff {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) :
    matrixDZeroExterior A.transpose = matrixDZeroExterior A ↔ A.transpose = A :=
  matrixDZeroExterior_eq_iff _ _

theorem matrixDZeroExterior_zero_iff {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) : matrixDZeroExterior A = 0 ↔ A = 0 := by
  have hz : matrixDZeroExterior (0 : Matrix (Fin n) (Fin n) ℂ) = 0 := by
    simp [matrixDZeroExterior]
  rw [← hz, matrixDZeroExterior_eq_iff]

theorem exteriorCoefficient_d0 {n : ℕ} (u : E n → ℝ) (x : E n) (i j : Fin n) :
    exteriorCoefficient (d0Exterior u x) i j = complexHessian u x i j :=
  exteriorCoefficient_matrixDZero _ i j

theorem d0Exterior_eq_iff_hessian {n : ℕ} (u v : E n → ℝ) (x y : E n) :
    d0Exterior u x = d0Exterior v y ↔ complexHessian u x = complexHessian v y :=
  matrixDZeroExterior_eq_iff _ _

/-- Recover the complex Hessian from the actual real degree-two form. -/
theorem complexHessian_eq_of_d0BilinearForm_eq {n : ℕ}
    {u v : E n → ℝ} {x y : E n}
    (hHu : (complexHessian u x).IsHermitian)
    (hHv : (complexHessian v y).IsHermitian)
    (hform : ∀ a b : E n, d0BilinearForm u x a b = d0BilinearForm v y a b) :
    complexHessian u x = complexHessian v y := by
  ext i j
  have hxy : exteriorEvaluation ![realDirection i, imagDirection j] (d0Exterior u x) =
      exteriorEvaluation ![realDirection i, imagDirection j] (d0Exterior v y) := by
    rw [exteriorEvaluation_d0 hHu, exteriorEvaluation_d0 hHv,
      hform (realDirection i) (imagDirection j)]
  have hxx : exteriorEvaluation ![realDirection i, realDirection j] (d0Exterior u x) =
      exteriorEvaluation ![realDirection i, realDirection j] (d0Exterior v y) := by
    rw [exteriorEvaluation_d0 hHu, exteriorEvaluation_d0 hHv,
      hform (realDirection i) (realDirection j)]
  calc
    complexHessian u x i j = exteriorCoefficient (d0Exterior u x) i j :=
      (exteriorCoefficient_d0 u x i j).symm
    _ = exteriorCoefficient (d0Exterior v y) i j := by
      unfold exteriorCoefficient
      rw [hxy, hxx]
    _ = complexHessian v y i j := exteriorCoefficient_d0 v y i j

/-- Original solutions discharge the Hermitian premises on the closed ball. -/
theorem IsSolution.hessian_eq_of_d0BilinearForm_eq {n : ℕ} {μ ν : ℝ} {u v : E n → ℝ}
    (hu : IsSolution n μ u) (hv : IsSolution n ν v) {x y : E n}
    (hx : x ∈ closedUnitBall n) (hy : y ∈ closedUnitBall n)
    (hform : ∀ a b : E n, d0BilinearForm u x a b = d0BilinearForm v y a b) :
    complexHessian u x = complexHessian v y :=
  complexHessian_eq_of_d0BilinearForm_eq
    (hu.hessian_isHermitian_closedBall hx) (hv.hessian_isHermitian_closedBall hy) hform

#print axioms exteriorCoefficient_matrixDZero
#print axioms matrixDZeroExterior_injective
#print axioms IsSolution.hessian_eq_of_d0BilinearForm_eq

end KEBall
