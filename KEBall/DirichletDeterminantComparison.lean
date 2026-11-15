import KEBall.BedfordTaylorQuadraticDeterminant
import KEBall.LogDetConcavity
import Mathlib.Analysis.Matrix.Order

set_option autoImplicit false
open scoped Matrix ComplexOrder MatrixOrder

namespace KEBall.BedfordTaylor

/-- Adding a positive semidefinite matrix to a positive definite matrix
increases the determinant by at least the determinant of the added matrix. -/
theorem det_re_add_ge {n : ℕ} (hn : 0 < n) {A B : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.PosSemidef) (hB : B.PosDef) :
    A.det.re + B.det.re ≤ (A + B).det.re := by
  let S := CFC.sqrt B
  have hS : S.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg B)
  have hSq : S * S = B := by
    rw [← sq]
    change CFC.sqrt B ^ 2 = B
    exact CFC.sq_sqrt B hB.posSemidef.nonneg
  have hSD : S.det * S.det = B.det := by rw [← Matrix.det_mul, hSq]
  have hSdet : S.det ≠ 0 := by
    intro h
    rw [h, zero_mul] at hSD
    exact ((Matrix.isUnit_iff_isUnit_det _).mp hB.isUnit).ne_zero hSD.symm
  have hSunit : IsUnit S.det := isUnit_iff_ne_zero.mpr hSdet
  have hSP : S.PosDef := hS.posDef_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det _).mpr hSunit)
  let T := S⁻¹
  have hT : T.PosDef := hSP.inv
  have hTB : T * B * T = 1 := by
    rw [← hSq, ← mul_assoc, show T * S = 1 from Matrix.nonsing_inv_mul _ hSunit,
      one_mul, show S * T = 1 from Matrix.mul_nonsing_inv _ hSunit]
  let C := T * A * T
  have hC : C.PosSemidef := by
    simpa only [hT.isHermitian.eq] using hA.mul_mul_conjTranspose_same T
  have hM : T * (A + B) * T = C + 1 := by
    rw [Matrix.mul_add, Matrix.add_mul, hTB]
  have hDet (M : Matrix (Fin n) (Fin n) ℂ) : (T * M * T).det.re = T.det.re ^ 2 * M.det.re := by
    rw [Matrix.det_mul, Matrix.det_mul, posDef_det_eq_ofReal_re hT]
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hB1 : T.det.re ^ 2 * B.det.re = 1 := by
    rw [← hDet, hTB, Matrix.det_one, Complex.one_re]
  have hA1 : T.det.re ^ 2 * A.det.re = C.det.re := (hDet A).symm
  have hAB : T.det.re ^ 2 * (A + B).det.re = (C + 1).det.re := by rw [← hDet, hM]
  have h := det_re_add_scalar_one_ge hn hC zero_le_one
  simp only [one_pow, Complex.ofReal_one, one_smul] at h
  apply le_of_mul_le_mul_left _ (pow_pos (posDef_det_re_pos hT) 2)
  rwa [mul_add, hA1, hB1, hAB]

end KEBall.BedfordTaylor
