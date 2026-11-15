import Drafts.KEBall.ExteriorPairAlgebra
import Drafts.KEBall.DZeroTwoForm
import KEBall.ComplexMaximum
import Mathlib.Tactic.Module

/-!
Stage11 SOURCE_DRAFT_UNCOMPILED.
The coefficient module consists of actual complex-valued real covectors.
Products are mathlib ExteriorAlgebra multiplication. The top identity is
proved from the independent exterior-product lemma, not defined by det.
-/
set_option autoImplicit false
open scoped BigOperators ContDiff

namespace KEBall

abbrev ComplexCovector (n : ℕ) := E n →ₗ[ℝ] ℂ
abbrev CovectorExterior (n : ℕ) := ExteriorAlgebra ℂ (ComplexCovector n)

noncomputable def realCovector {n : ℕ} (i : Fin n) : ComplexCovector n :=
  Complex.ofRealCLM.toLinearMap.comp (EuclideanSpace.proj (realIndex i)).toLinearMap

noncomputable def imagCovector {n : ℕ} (i : Fin n) : ComplexCovector n :=
  Complex.ofRealCLM.toLinearMap.comp (EuclideanSpace.proj (imagIndex i)).toLinearMap

noncomputable def dzCovector {n : ℕ} (i : Fin n) : ComplexCovector n :=
  realCovector i + Complex.I • imagCovector i

noncomputable def dbarCovector {n : ℕ} (i : Fin n) : ComplexCovector n :=
  realCovector i - Complex.I • imagCovector i

@[simp] theorem realCovector_apply {n : ℕ} (i : Fin n) (v : E n) :
    realCovector i v = (v (realIndex i) : ℂ) := rfl

@[simp] theorem imagCovector_apply {n : ℕ} (i : Fin n) (v : E n) :
    imagCovector i v = (v (imagIndex i) : ℂ) := rfl

@[simp] theorem dzCovector_apply {n : ℕ} (i : Fin n) (v : E n) :
    dzCovector i v = complexCoord v i := by
  simp [dzCovector, complexCoord, mul_comm]

@[simp] theorem dbarCovector_apply {n : ℕ} (i : Fin n) (v : E n) :
    dbarCovector i v = star (complexCoord v i) := by
  simp [dbarCovector, complexCoord, sub_eq_add_neg]

/-- Ordered dx_1 wedge dy_1 wedge ... wedge dx_n wedge dy_n. -/
noncomputable def euclideanExteriorVolume (n : ℕ) : CovectorExterior n :=
  ExteriorPair.pairProd n realCovector imagCovector

/-- The explicit exterior volume with the manuscript's n!/pi^n normalization. -/
noncomputable def normalizedExteriorVolume (n : ℕ) : CovectorExterior n :=
  n.factorial • (((Real.pi : ℂ) ^ n)⁻¹ • euclideanExteriorVolume n)

noncomputable def matrixDZeroExterior {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    CovectorExterior n :=
  (Complex.I / (2 * (Real.pi : ℂ))) •
    ∑ i, ExteriorAlgebra.ι ℂ (dzCovector i) *
      ExteriorAlgebra.ι ℂ (∑ j, A i j • dbarCovector j)

noncomputable def d0Exterior {n : ℕ} (u : E n → ℝ) (x : E n) : CovectorExterior n :=
  matrixDZeroExterior (complexHessian u x)

theorem dz_dbar_exterior_pair {n : ℕ} (i : Fin n) :
    ExteriorAlgebra.ι ℂ (dzCovector i) * ExteriorAlgebra.ι ℂ (dbarCovector i) =
      (-2 * Complex.I) •
        (ExteriorAlgebra.ι ℂ (realCovector i) * ExteriorAlgebra.ι ℂ (imagCovector i)) := by
  have hswap : ExteriorAlgebra.ι ℂ (imagCovector i) *
      ExteriorAlgebra.ι ℂ (realCovector i) =
      -(ExteriorAlgebra.ι ℂ (realCovector i) * ExteriorAlgebra.ι ℂ (imagCovector i)) :=
    eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap _ _)
  simp only [dzCovector, dbarCovector, map_add, map_sub, map_smul, add_mul,
    sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, smul_smul,
    ExteriorAlgebra.ι_sq_zero, smul_zero, hswap]
  module

theorem dz_dbar_exterior_volume (n : ℕ) :
    ExteriorPair.pairProd n dzCovector dbarCovector =
      (-2 * Complex.I) ^ n • euclideanExteriorVolume n :=
  ExteriorPair.pairProd_of_pair_eq _ _ _ _ _ dz_dbar_exterior_pair

theorem d0_pair_coefficient :
    Complex.I / (2 * (Real.pi : ℂ)) * (-2 * Complex.I) = (Real.pi : ℂ)⁻¹ := by
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  calc
    _ = -(Complex.I * Complex.I) / (Real.pi : ℂ) := by field_simp [hp] <;> ring
    _ = _ := by rw [Complex.I_mul_I]; ring

/-- Exact determinant density in the genuine exterior algebra, in every n. -/
theorem matrixDZeroExterior_top {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    matrixDZeroExterior A ^ n = A.det • normalizedExteriorVolume n := by
  rw [matrixDZeroExterior, smul_pow, ExteriorPair.sum_pairs_matrix_pow,
    dz_dbar_exterior_volume]
  have hc : (Complex.I / (2 * (Real.pi : ℂ))) ^ n * (-2 * Complex.I) ^ n =
      ((Real.pi : ℂ) ^ n)⁻¹ := by
    rw [← mul_pow, d0_pair_coefficient, inv_pow]
  rw [smul_comm ((Complex.I / (2 * (Real.pi : ℂ))) ^ n) (n.factorial : ℕ),
    smul_comm ((Complex.I / (2 * (Real.pi : ℂ))) ^ n) A.det,
    smul_comm (n.factorial : ℕ) A.det, smul_smul, hc]
  rfl

theorem d0Exterior_top {n : ℕ} (u : E n → ℝ) (x : E n) :
    d0Exterior u x ^ n = (complexHessian u x).det • normalizedExteriorVolume n :=
  matrixDZeroExterior_top _

theorem matrixDZeroExterior_smul {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) :
    matrixDZeroExterior (c • A) = c • matrixDZeroExterior A := by
  unfold matrixDZeroExterior
  simp only [Matrix.smul_apply, smul_eq_mul, mul_smul, ← Finset.smul_sum,
    map_smul, mul_smul_comm]
  rw [smul_comm]

theorem d0Exterior_const_mul {n : ℕ} {u : E n → ℝ} {x : E n}
    (hu : ContDiffAt ℝ ∞ u x) (c : ℝ) :
    d0Exterior (fun y => c * u y) x = (c : ℂ) • d0Exterior u x := by
  unfold d0Exterior
  rw [complexHessian_const_mul_at hu, matrixDZeroExterior_smul]

noncomputable def d1Exterior {n : ℕ} (u : E n → ℝ) (x : E n) : CovectorExterior n :=
  (2 : ℂ) • d0Exterior u x

theorem d1Exterior_half {n : ℕ} {u : E n → ℝ} {x : E n}
    (hu : ContDiffAt ℝ ∞ u x) :
    d1Exterior (fun y => u y / 2) x = d0Exterior u x := by
  have heq : (fun y => u y / 2) = (fun y => (1 / 2 : ℝ) * u y) := by
    funext y
    ring
  rw [heq, d1Exterior, d0Exterior_const_mul hu, smul_smul]
  norm_num

#print axioms matrixDZeroExterior_top
#print axioms d0Exterior_top
#print axioms d1Exterior_half

end KEBall
