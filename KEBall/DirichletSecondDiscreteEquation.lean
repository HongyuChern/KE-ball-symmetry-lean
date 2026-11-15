import KEBall.DirichletDiscreteCofactorEquation
import KEBall.DirichletAveragedCofactorBounds
import KEBall.DirichletBoundedBilinear

/-!
# The exact second unitary-difference equation

The two averaged coefficients use the three actual pulled-back Hessians.
The error term is the increment of the averaged coefficient contracted
with the pulled-back Hessian of the first difference.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Matrix Metric Set
open scoped BigOperators ComplexOrder ContDiff

namespace KEBall

theorem dirichletOrthogonalDifference_comp {n : ℕ}
    (R : E n ≃ₗᵢ[ℝ] E n) (τ : ℝ) (f : E n → ℝ) :
    dirichletOrthogonalDifference R τ (f ∘ R) =
      (dirichletOrthogonalDifference R τ f) ∘ R := rfl

theorem dirichletContraction_second_difference {n : ℕ}
    (A B : E n →L[ℝ] E n)
    (H₀ H₁ : E n →L[ℝ] E n →L[ℝ] ℝ)
    (τ g₀ g₁ : ℝ)
    (h₀ : dirichletContractionCLM n A H₀ = g₀)
    (h₁ : dirichletContractionCLM n B H₁ = g₁) :
    dirichletContractionCLM n A (τ⁻¹ • (H₁ - H₀)) =
      τ⁻¹ * (g₁ - g₀) -
        τ⁻¹ * dirichletContractionCLM n (B - A) H₁ := by
  simp only [map_smul, map_sub, _root_.sub_apply, smul_eq_mul]
  rw [h₀, h₁]
  ring

theorem dirichlet_unitary_second_difference_determinant_equation {n : ℕ}
    (R : E n ≃ₗᵢ[ℝ] E n) (hJ : ∀ y, R (J y) = J (R y)) (τ : ℝ)
    {u f : E n → ℝ} (hu : ContDiffOn ℝ 2 u (closedUnitBall n))
    (hEq : ∀ y ∈ unitBall n, (complexHessian u y).det.re = f y)
    {x : E n} (hx : x ∈ unitBall n) :
    dirichletContractionCLM n
      (dirichletMeanCofactor (complexHessian u x) (complexHessian (u ∘ R) x))
      (realHessian
        (dirichletOrthogonalDifference R τ (dirichletOrthogonalDifference R τ u)) x) =
      dirichletOrthogonalDifference R τ (dirichletOrthogonalDifference R τ f) x -
      τ⁻¹ * dirichletContractionCLM n
        (dirichletMeanCofactor (complexHessian (u ∘ R) x)
            (complexHessian ((u ∘ R) ∘ R) x) -
          dirichletMeanCofactor (complexHessian u x) (complexHessian (u ∘ R) x))
        (realHessian ((dirichletOrthogonalDifference R τ u) ∘ R) x) := by
  have hMaps : MapsTo R (closedUnitBall n) (closedUnitBall n) := by
    intro y hy
    simpa only [closedUnitBall, mem_closedBall_zero_iff, R.norm_map] using hy
  have hMapsB : MapsTo R (unitBall n) (unitBall n) := by
    intro y hy
    simpa only [unitBall, mem_ball_zero_iff, R.norm_map] using hy
  have huR : ContDiffOn ℝ 2 (u ∘ R) (closedUnitBall n) :=
    hu.comp R.toContinuousLinearEquiv.contDiff.contDiffOn hMaps
  have hEqR : ∀ y ∈ unitBall n,
      (complexHessian (u ∘ R) y).det.re = (f ∘ R) y := by
    intro y hy
    have huAt := (hu.mono ball_subset_closedBall).contDiffAt
      (isOpen_ball.mem_nhds (hMapsB hy))
    rw [(complexHessian_posDef_and_det_comp_unitary R hJ huAt).2]
    exact hEq _ (hMapsB hy)
  let q := dirichletOrthogonalDifference R τ u
  have hq : ContDiffOn ℝ 2 q (closedUnitBall n) :=
    contDiffOn_dirichletOrthogonalDifference R τ hu
  have hqAt := (hq.mono ball_subset_closedBall).contDiffAt (isOpen_ball.mem_nhds hx)
  have hqRAt := (hq.mono ball_subset_closedBall).contDiffAt
    (isOpen_ball.mem_nhds (hMapsB hx))
  have h₀ := dirichlet_unitary_difference_determinant_equation R hJ τ hu hEq hx
  have h₁ := dirichlet_unitary_difference_determinant_equation R hJ τ huR hEqR hx
  rw [← dirichletContractionCLM_apply] at h₀ h₁
  rw [dirichletOrthogonalDifference_comp] at h₁
  have hAlgebra := dirichletContraction_second_difference
    (dirichletMeanCofactor (complexHessian u x) (complexHessian (u ∘ R) x))
    (dirichletMeanCofactor (complexHessian (u ∘ R) x)
      (complexHessian ((u ∘ R) ∘ R) x))
    (realHessian q x) (realHessian (q ∘ R) x) τ
    (dirichletOrthogonalDifference R τ f x)
    (dirichletOrthogonalDifference R τ (f ∘ R) x) h₀ h₁
  rw [realHessian_dirichletOrthogonalDifference R τ hqAt hqRAt]
  convert hAlgebra using 1
  simp only [dirichletOrthogonalDifference, Function.comp_apply, div_eq_mul_inv]
  ring

end KEBall
