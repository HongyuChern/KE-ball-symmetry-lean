import KEBall.DirichletDifferenceQuotientCoefficients
import KEBall.DirichletSchauderLocalC2

/-!
# Holder control of the actual complex Hessian from the actual real jets

The conversion is a fixed real continuous linear map with the existing
factor 1/4.  The resulting coefficient family is the one in the exact
determinant difference-quotient equation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Matrix Metric Set
open DifferentialGeometry.Analysis.Schauder
open scoped ComplexOrder Matrix.Norms.Elementwise NNReal

namespace KEBall

noncomputable def dirichletComplexHessianLinearMap {n : ℕ} :
    (E n →L[ℝ] E n →L[ℝ] ℝ) →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ where
  toFun := complexHessianOfRealBilinear
  map_add' B D := by
    ext i j
    simp only [complexHessianOfRealBilinear, Matrix.add_apply, _root_.add_apply, Complex.ofReal_add]
    ring
  map_smul' c B := by
    ext i j
    simp only [complexHessianOfRealBilinear, Matrix.smul_apply, _root_.smul_apply,
      smul_eq_mul, Complex.ofReal_mul, Complex.real_smul, RingHom.id_apply]
    ring

noncomputable def dirichletComplexHessianCLM {n : ℕ} :
    (E n →L[ℝ] E n →L[ℝ] ℝ) →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
  dirichletComplexHessianLinearMap.toContinuousLinearMap

theorem dirichletComplexHessianCLM_apply {n : ℕ} (B : E n →L[ℝ] E n →L[ℝ] ℝ) :
    dirichletComplexHessianCLM B = complexHessianOfRealBilinear B := rfl

theorem dirichlet_complexHessian_eq_of_bounded_jets {n : ℕ}
    (u : BoundedContinuousFunction (E n) ℝ)
    (Du : BoundedContinuousFunction (E n) (E n →L[ℝ] ℝ))
    (Hu : BoundedContinuousFunction (E n) (E n →L[ℝ] E n →L[ℝ] ℝ))
    (hu : ∀ x, HasFDerivAt (u : E n → ℝ) (Du x) x)
    (hDu : ∀ x, HasFDerivAt (Du : E n → E n →L[ℝ] ℝ) (Hu x) x) (x : E n) :
    complexHessian (u : E n → ℝ) x = dirichletComplexHessianCLM (Hu x) := by
  have hC := contDiff_two_of_hasFDerivAt u Du Hu hu hDu
  have hFirst : fderiv ℝ (u : E n → ℝ) = (Du : E n → E n →L[ℝ] ℝ) := funext fun y => (hu y).fderiv
  rw [← complexHessianOfRealBilinear_eq (hC.contDiffAt (x := x)),
    realHessian, hFirst, (hDu x).fderiv]
  rfl

theorem holderWith_dirichlet_complexHessian_of_bounded_jets {n : ℕ}
    (u : BoundedContinuousFunction (E n) ℝ)
    (Du : BoundedContinuousFunction (E n) (E n →L[ℝ] ℝ))
    (Hu : BoundedContinuousFunction (E n) (E n →L[ℝ] E n →L[ℝ] ℝ))
    (hu : ∀ x, HasFDerivAt (u : E n → ℝ) (Du x) x)
    (hDu : ∀ x, HasFDerivAt (Du : E n → E n →L[ℝ] ℝ) (Hu x) x)
    {K α : ℝ≥0} (hH : HolderWith K α (Hu : E n → E n →L[ℝ] E n →L[ℝ] ℝ)) :
    HolderWith (‖(@dirichletComplexHessianCLM n)‖₊ * K) α (complexHessian (u : E n → ℝ)) := by
  have h := (@dirichletComplexHessianCLM n).lipschitz.holderWith.comp hH
  have he : complexHessian (u : E n → ℝ) = dirichletComplexHessianCLM ∘ (Hu : E n → _) :=
    funext fun x => dirichlet_complexHessian_eq_of_bounded_jets u Du Hu hu hDu x
  rw [he]
  simpa only [NNReal.coe_one, NNReal.rpow_one, one_mul] using! h

end KEBall
