import Drafts.KEBall.DZeroExterior
import KEBall.BoundaryRegularity
import Mathlib.LinearAlgebra.ExteriorAlgebra.OfAlternating
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
Stage14 SOURCE_REPAIR_CANDIDATE_UNCOMPILED.
The matrix evaluation proof now separates pair evaluation from sum expansion.
Evaluation is induced by the determinant alternating map on actual covectors.
The degree-two bridge is proved for Hermitian matrices, then consumed using
the original IsSolution hypotheses. The volume evaluation uses the actual
interleaved coordinate covectors and standard real Euclidean frame.
-/
set_option autoImplicit false
open scoped BigOperators ContDiff

namespace KEBall

noncomputable def covectorValues {n d : ℕ} (v : Fin d → E n) :
    ComplexCovector n →ₗ[ℂ] (Fin d → ℂ) where
  toFun a i := a (v i)
  map_add' a b := by ext i; rfl
  map_smul' c a := by ext i; rfl

noncomputable def covectorDet {n d : ℕ} (v : Fin d → E n) :
    ComplexCovector n [⋀^Fin d]→ₗ[ℂ] ℂ :=
  Matrix.detRowAlternating.compLinearMap (covectorValues v)

/-- The degree-d evaluation; other homogeneous degrees are sent to zero. -/
noncomputable def exteriorEvaluation {n d : ℕ} (v : Fin d → E n) :
    CovectorExterior n →ₗ[ℂ] ℂ :=
  ExteriorAlgebra.liftAlternating (fun k =>
    if h : k = d then h.symm ▸ covectorDet v else 0)

theorem exteriorEvaluation_multi {n d : ℕ} (v : Fin d → E n)
    (a : Fin d → ComplexCovector n) :
    exteriorEvaluation v (ExteriorAlgebra.ιMulti ℂ d a) =
      Matrix.det (fun i j => a i (v j)) := by
  simp only [exteriorEvaluation, ExteriorAlgebra.liftAlternating_apply_ιMulti,
    dif_pos rfl]
  rfl

theorem exteriorEvaluation_pair {n : ℕ} (v w : E n) (a b : ComplexCovector n) :
    exteriorEvaluation ![v, w] (ExteriorAlgebra.ι ℂ a * ExteriorAlgebra.ι ℂ b) =
      a v * b w - a w * b v := by
  have h := exteriorEvaluation_multi ![v, w] ![a, b]
  have hd := Matrix.det_fin_two (fun i j : Fin 2 => ![a, b] i (![v, w] j))
  simpa [ExteriorAlgebra.ιMulti_succ_apply, Matrix.vecTail] using h.trans hd

noncomputable def hermitianPairing {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (v w : E n) : ℂ :=
  ∑ i, ∑ j, A i j * complexCoord v i * star (complexCoord w j)

theorem hermitianPairing_star {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.IsHermitian) (v w : E n) :
    star (hermitianPairing A v w) = hermitianPairing A w v := by
  unfold hermitianPairing
  simp only [star_sum, star_mul, star_star]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hA.apply i j]
  ring

theorem hermitianPairing_J {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (v w : E n) :
    hermitianPairing A (J v) w = Complex.I * hermitianPairing A v w := by
  unfold hermitianPairing
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [complexCoord_J]
  ring

theorem exteriorEvaluation_matrixDZero {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (v w : E n) :
    exteriorEvaluation ![v, w] (matrixDZeroExterior A) =
      Complex.I / (2 * (Real.pi : ℂ)) *
        (hermitianPairing A v w - hermitianPairing A w v) := by
  -- Evaluate the pair before expanding its second generator.
  have hrow (i : Fin n) :
      exteriorEvaluation ![v, w]
        (ExteriorAlgebra.ι ℂ (dzCovector i) *
          ExteriorAlgebra.ι ℂ (∑ j, A i j • dbarCovector j)) =
        ∑ j, (A i j * complexCoord v i * star (complexCoord w j) -
          A i j * complexCoord w i * star (complexCoord v j)) := by
    rw [exteriorEvaluation_pair, dzCovector_apply, dzCovector_apply]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, dbarCovector_apply,
      smul_eq_mul]
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  calc
    _ = Complex.I / (2 * (Real.pi : ℂ)) *
        (∑ i, ∑ j, (A i j * complexCoord v i * star (complexCoord w j) -
          A i j * complexCoord w i * star (complexCoord v j))) := by
      rw [matrixDZeroExterior, map_smul, map_sum, smul_eq_mul]
      exact congrArg (fun z : ℂ => Complex.I / (2 * (Real.pi : ℂ)) * z)
        (Finset.sum_congr rfl (fun i _ => hrow i))
    _ = _ := by
      congr 1
      simp only [hermitianPairing, ← Finset.sum_sub_distrib]

theorem d0_scalar_real (z : ℂ) :
    Complex.I / (2 * (Real.pi : ℂ)) * (z - star z) =
      ((2 * Real.pi)⁻¹ * (2 * (Complex.I * z).re) : ℝ) := by
  apply Complex.ext
  · simp [Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im]
    field_simp [Real.pi_ne_zero]
    ring
  · simp [Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im]

/-- Identification with the degree-two form, with Hermitian symmetry explicit. -/
theorem exteriorEvaluation_d0 {n : ℕ} {u : E n → ℝ} {x : E n}
    (hH : (complexHessian u x).IsHermitian) (v w : E n) :
    exteriorEvaluation ![v, w] (d0Exterior u x) = (d0BilinearForm u x v w : ℂ) := by
  rw [d0Exterior, exteriorEvaluation_matrixDZero, ← hermitianPairing_star hH v w,
    d0_scalar_real, d0BilinearForm_apply]
  change (((2 * Real.pi)⁻¹ * (2 * (Complex.I *
      hermitianPairing (complexHessian u x) v w).re) : ℝ) : ℂ) =
    (((2 * Real.pi)⁻¹ * (2 * (hermitianPairing (complexHessian u x) (J v) w).re) : ℝ) : ℂ)
  rw [hermitianPairing_J]

/-- The actual exterior algebra representative evaluates to d(dc0 u). -/
theorem IsSolution.d0Exterior_evaluates_derivative {n : ℕ} {μ : ℝ} {u : E n → ℝ}
    (hu : IsSolution n μ u) {x : E n} (hx : x ∈ closedUnitBall n) (v w : E n) :
    exteriorEvaluation ![v, w] (d0Exterior u x) =
      ((fderiv ℝ (fun y => dcZeroForm u y w) x v -
        fderiv ℝ (fun y => dcZeroForm u y v) x w : ℝ) : ℂ) := by
  rw [exteriorEvaluation_d0 (hu.hessian_isHermitian_closedBall hx),
    d0BilinearForm_eq_exteriorDerivative (hu.2.1.contDiffAt hx)]

noncomputable def coordinateCovector {n : ℕ} (k : Fin (2 * n)) : ComplexCovector n :=
  Complex.ofRealCLM.toLinearMap.comp (EuclideanSpace.proj k).toLinearMap

@[simp] theorem coordinateCovector_apply {n : ℕ} (k : Fin (2 * n)) (v : E n) :
    coordinateCovector k v = (v k : ℂ) := rfl

/-- This identity records the interleaved orientation, including n=0. -/
theorem euclideanExteriorVolume_eq_multi (n : ℕ) :
    euclideanExteriorVolume n = ExteriorAlgebra.ιMulti ℂ (2 * n) coordinateCovector := by
  rw [euclideanExteriorVolume, ExteriorPair.pairProd_eq_list,
    ExteriorAlgebra.ιMulti_apply, List.ofFn_mul', List.prod_flatten, List.map_ofFn]
  congr 1
  apply congrArg List.ofFn
  funext i
  simp [List.ofFn_succ, realCovector, imagCovector, coordinateCovector,
    realIndex, imagIndex]

theorem exteriorEvaluation_volume {n : ℕ} (v : Fin (2 * n) → E n) :
    exteriorEvaluation v (euclideanExteriorVolume n) =
      Matrix.det (fun i j => (v j i : ℂ)) := by
  rw [euclideanExteriorVolume_eq_multi, exteriorEvaluation_multi]
  rfl

noncomputable def euclideanFrame (n : ℕ) (k : Fin (2 * n)) : E n :=
  EuclideanSpace.single k 1

theorem exteriorEvaluation_standard_volume (n : ℕ) :
    exteriorEvaluation (euclideanFrame n) (euclideanExteriorVolume n) = 1 := by
  rw [exteriorEvaluation_volume]
  have h : (fun i j => (euclideanFrame n j i : ℂ)) =
      (1 : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ) := by
    ext i j
    by_cases hij : i = j <;> simp [euclideanFrame, Matrix.one_apply, hij, eq_comm]
  rw [h, Matrix.det_one]

theorem exteriorEvaluation_normalized_volume (n : ℕ) :
    exteriorEvaluation (euclideanFrame n) (normalizedExteriorVolume n) =
      (((n.factorial : ℝ) / Real.pi ^ n : ℝ) : ℂ) := by
  unfold normalizedExteriorVolume
  rw [map_nsmul, map_smul, exteriorEvaluation_standard_volume]
  simp [nsmul_eq_mul, div_eq_mul_inv]

theorem exteriorEvaluation_d0_top {n : ℕ} (u : E n → ℝ) (x : E n) :
    exteriorEvaluation (euclideanFrame n) (d0Exterior u x ^ n) =
      (complexHessian u x).det * (((n.factorial : ℝ) / Real.pi ^ n : ℝ) : ℂ) := by
  rw [d0Exterior_top, map_smul, exteriorEvaluation_normalized_volume, smul_eq_mul]

#print axioms IsSolution.d0Exterior_evaluates_derivative
#print axioms exteriorEvaluation_standard_volume
#print axioms exteriorEvaluation_d0_top

end KEBall
