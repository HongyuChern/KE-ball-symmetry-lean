import PoincareLib.Analysis.Matrix.Determinant
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Complex.Basic

/-! Extension of the real-matrix Jacobi formula in
`PoincareLib.Analysis.Matrix.Determinant` to complex matrices differentiated
over the real scalars. The multilinear/adjugate proof follows that upstream
module, pinned at 62db01af9388dc1d9b56b66d6674f4c09b2318a2.
The index type is arbitrary finite; this is not limited to dimension two. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Matrix.Norms.Elementwise

namespace KEBallProbe
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private noncomputable def complexDetMultilinear :
    ContinuousMultilinearMap ℂ (fun _ : ι => ι → ℂ) ℂ where
  toMultilinearMap := Matrix.detRowAlternating.toMultilinearMap
  cont := continuous_id.matrix_det

private theorem complexDetMultilinear_linearDeriv (A B : Matrix ι ι ℂ) :
    (complexDetMultilinear.linearDeriv A) B = Matrix.trace (Matrix.adjugate A * B) := by
  change (complexDetMultilinear.linearDeriv (fun i j => A i j)) (fun i j => B i j) = _
  rw [ContinuousMultilinearMap.linearDeriv_apply]
  change (∑ i, (A.updateRow i (B i)).det) = _
  trans ∑ i, ∑ j, A.adjugate j i * B i j
  · apply Finset.sum_congr rfl
    intro i _
    rw [← Matrix.cramer_transpose_apply, Matrix.cramer_eq_adjugate_mulVec,
      ← Matrix.adjugate_transpose]
    rfl
  · rw [Finset.sum_comm]
    rfl

theorem fderiv_real_complex_det (A B : Matrix ι ι ℂ) :
    fderiv ℝ Matrix.det A B = Matrix.trace (Matrix.adjugate A * B) := by
  have h := (complexDetMultilinear.hasFDerivAt A).restrictScalars ℝ
  change HasFDerivAt (fun a : Matrix ι ι ℂ => a.det)
    ((complexDetMultilinear.linearDeriv A).restrictScalars ℝ) A at h
  rw [h.fderiv]
  exact complexDetMultilinear_linearDeriv A B

theorem fderiv_real_complex_det_invertible (A B : Matrix ι ι ℂ)
    (hA : IsUnit A.det) :
    fderiv ℝ Matrix.det A B = A.det * Matrix.trace (A⁻¹ * B) := by
  rw [fderiv_real_complex_det]
  have hadj : Matrix.adjugate A = A.det • A⁻¹ := by
    rw [Matrix.inv_def, smul_smul, Ring.mul_inverse_cancel _ hA, one_smul]
  rw [hadj, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]

#print axioms fderiv_real_complex_det
#print axioms fderiv_real_complex_det_invertible
end KEBallProbe
