import KEBall.DirichletC3DifferentiatedEquation
import KEBall.DirichletRotations
import KEBall.DirichletUnitaryFieldMatrix

/-!
# The actual rotation equation with interior smoothness only

No smoothness at the sphere is used in the differentiation.  The source
is the directional derivative of the prescribed determinant, with the
real cofactor normalization already fixed by the contraction theorem.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Filter InnerProductSpace Matrix Metric Set
open scoped ComplexOrder ContDiff Matrix.Norms.Elementwise Topology

namespace KEBall

theorem dirichlet_complexHessian_linearField_on_open {n : ℕ}
    {U : Set (E n)} (hU : IsOpen U) {u : E n → ℝ}
    (hu : ContDiffOn ℝ ∞ u U) {x : E n} (hx : x ∈ U)
    (T : E n →L[ℝ] E n) (hTJ : ∀ y, T (J y) = J (T y))
    (M : Matrix (Fin n) (Fin n) ℂ)
    (hM : ∀ y, complexCoord (T y) = M *ᵥ complexCoord y) :
    complexHessian (fun y => fderiv ℝ u y (T y)) x =
      complexHessian (fun y => fderiv ℝ u y (T x)) x +
        (Mᵀ * complexHessian u x + complexHessian u x * Mᴴᵀ) := by
  apply hermitianRealification_injective
  ext v w : 2
  rw [← realMetricForm_eq, realMetricForm_linearFieldDerivative hU hu hx T hTJ]
  simp only [realMetricForm_eq, hermitianRealification_eq_re_dotProduct, hM]
  simp only [Matrix.add_mulVec, dotProduct_add, Complex.add_re]
  rw [Matrix.star_mulVec, Matrix.mulVec_vecMul]
  simp only [Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec]
  ring

theorem dirichlet_cofactor_rotation_equation_on_open {n : ℕ}
    {U : Set (E n)} (hU : IsOpen U) {u f : E n → ℝ}
    (hu : ContDiffOn ℝ ∞ u U)
    (hEq : ∀ x ∈ U, (complexHessian u x).det.re = f x)
    (T : E n →L[ℝ] E n) (hT : star T = -T)
    (hTJ : ∀ y, T (J y) = J (T y)) {x : E n} (hx : x ∈ U) :
    dirichletContractionCLM n (dirichletCofactorOfMatrix (complexHessian u x))
      (realHessian (fun y => fderiv ℝ u y (T y)) x) = fderiv ℝ f x (T x) := by
  obtain ⟨M, hTM, hM⟩ := exists_dirichlet_skewHermitian_matrix_of_field T hT hTJ
  have huAt := hu.contDiffAt (hU.mem_nhds hx)
  have h2 : (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω) :=
    ENat.natCast_le_of_coe_top_le_withTop le_rfl 2
  have h3 : (3 : ℕ∞ω) ≤ (∞ : ℕ∞ω) :=
    ENat.natCast_le_of_coe_top_le_withTop le_rfl 3
  have hRot := ((huAt.fderiv_right (m := ∞) (by simp)).clm_apply T.contDiff.contDiffAt)
  have hConst := ((huAt.fderiv_right (m := ∞) (by simp)).clm_apply
    (g := fun _ => T x) contDiffAt_const)
  have hNear : (fun y => (complexHessian u y).det.re) =ᶠ[𝓝 x] f := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact hEq y hy
  have hDir := dirichlet_cofactor_directional_equation_of_C3
    (huAt.of_le h3) hNear (T x)
  have hTrace : ((complexHessian u x).adjugate *
      (Mᵀ * complexHessian u x + complexHessian u x * Mᴴᵀ)).trace = 0 := by
    rw [Matrix.mul_add, Matrix.trace_add,
      Matrix.trace_mul_cycle' (complexHessian u x).adjugate Mᵀ (complexHessian u x),
      ← Matrix.mul_assoc (complexHessian u x) (complexHessian u x).adjugate,
      ← Matrix.mul_assoc (complexHessian u x).adjugate (complexHessian u x),
      Matrix.mul_adjugate, Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul,
      Matrix.smul_mul, Matrix.one_mul, hM, smul_neg, Matrix.trace_neg, add_neg_cancel]
  rw [dirichletContractionCLM_apply, dirichletBilinearContraction_cofactor,
    complexHessianOfRealBilinear_eq (hRot.of_le h2),
    dirichlet_complexHessian_linearField_on_open hU hu hx T hTJ M hTM,
    Matrix.mul_add, Matrix.trace_add, Complex.add_re, hTrace, Complex.zero_re, add_zero]
  rw [dirichletContractionCLM_apply, dirichletBilinearContraction_cofactor] at hDir
  change ((complexHessian u x).adjugate * complexHessianOfRealBilinear
    (realHessian (fun y => fderiv ℝ u y (T x)) x)).trace.re = fderiv ℝ f x (T x) at hDir
  rw [complexHessianOfRealBilinear_eq (hConst.of_le h2)] at hDir
  exact hDir

end KEBall
