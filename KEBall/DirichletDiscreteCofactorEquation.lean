import KEBall.DirichletDiscreteDifferences
import KEBall.DirichletDifferenceQuotientEquation
import KEBall.DirichletUnitaryHessian

/-!
# The exact cofactor equation for normalized unitary differences

The coefficient averages the two actual complex Hessians, including the
pullback of the Hessian at the rotated point. Only closed-ball C2 regularity
is required. No smooth extension across the sphere is introduced.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Matrix Metric Set
open scoped BigOperators ComplexOrder ContDiff

namespace KEBall

theorem contDiffOn_dirichletOrthogonalDifference_ball {n : ℕ} {m : ℕ∞ω}
    (R : E n ≃ₗᵢ[ℝ] E n) (τ : ℝ) {u : E n → ℝ}
    (hu : ContDiffOn ℝ m u (unitBall n)) :
    ContDiffOn ℝ m (dirichletOrthogonalDifference R τ u) (unitBall n) := by
  have hMaps : MapsTo R (unitBall n) (unitBall n) := by
    intro x hx
    simpa only [unitBall, mem_ball_zero_iff, R.norm_map] using hx
  exact ((hu.comp R.toContinuousLinearEquiv.contDiff.contDiffOn hMaps).sub hu).div_const τ

theorem realHessian_dirichletOrthogonalDifference {n : ℕ}
    (R : E n ≃ₗᵢ[ℝ] E n) (τ : ℝ) {u : E n → ℝ} {x : E n}
    (hx : ContDiffAt ℝ 2 u x) (hxR : ContDiffAt ℝ 2 u (R x)) :
    realHessian (dirichletOrthogonalDifference R τ u) x =
      τ⁻¹ • (realHessian (u ∘ R) x - realHessian u x) := by
  have huR : ContDiffAt ℝ 2 (u ∘ R) x :=
    hxR.comp x R.toContinuousLinearEquiv.contDiff.contDiffAt
  have hFun : dirichletOrthogonalDifference R τ u = τ⁻¹ • ((u ∘ R) - u) := by
    funext y
    simp only [dirichletOrthogonalDifference, Pi.smul_apply, Pi.sub_apply,
      Function.comp_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
  rw [hFun, dirichlet_realHessian_smul_C2 (u := (u ∘ R) - u) (huR.sub hx),
    dirichlet_realHessian_sub_C2 (u := u ∘ R) (v := u) huR hx]

theorem dirichlet_orthogonal_difference_det_linearization {n : ℕ}
    (R : E n ≃ₗᵢ[ℝ] E n) (τ : ℝ) {u : E n → ℝ} {x : E n}
    (hx : ContDiffAt ℝ 2 u x) (hxR : ContDiffAt ℝ 2 u (R x)) :
    dirichletBilinearContraction (EuclideanSpace.basisFun (Fin (2 * n)) ℝ)
      (dirichletMeanCofactor (complexHessian u x) (complexHessian (u ∘ R) x))
      (realHessian (dirichletOrthogonalDifference R τ u) x) =
      τ⁻¹ * ((complexHessian (u ∘ R) x).det.re - (complexHessian u x).det.re) := by
  rw [realHessian_dirichletOrthogonalDifference R τ hx hxR,
    dirichletBilinearContraction_smul_right]
  congr 1
  apply dirichletBilinearContraction_meanCofactor
  rw [complexHessianOfRealBilinear_sub,
    complexHessianOfRealBilinear_eq
      (hxR.comp x R.toContinuousLinearEquiv.contDiff.contDiffAt),
    complexHessianOfRealBilinear_eq hx]

theorem dirichlet_unitary_difference_determinant_equation {n : ℕ}
    (R : E n ≃ₗᵢ[ℝ] E n) (hJ : ∀ y, R (J y) = J (R y)) (τ : ℝ)
    {u f : E n → ℝ} (hu : ContDiffOn ℝ 2 u (closedUnitBall n))
    (hEq : ∀ y ∈ unitBall n, (complexHessian u y).det.re = f y)
    {x : E n} (hx : x ∈ unitBall n) :
    dirichletBilinearContraction (EuclideanSpace.basisFun (Fin (2 * n)) ℝ)
      (dirichletMeanCofactor (complexHessian u x) (complexHessian (u ∘ R) x))
      (realHessian (dirichletOrthogonalDifference R τ u) x) =
      dirichletOrthogonalDifference R τ f x := by
  have hxR : R x ∈ unitBall n := by
    simpa only [unitBall, mem_ball_zero_iff, R.norm_map] using hx
  have huB : ContDiffOn ℝ 2 u (unitBall n) := hu.mono ball_subset_closedBall
  have huAt := huB.contDiffAt (isOpen_ball.mem_nhds hx)
  have huRAt := huB.contDiffAt (isOpen_ball.mem_nhds hxR)
  rw [dirichlet_orthogonal_difference_det_linearization R τ huAt huRAt,
    (complexHessian_posDef_and_det_comp_unitary R hJ huRAt).2,
    hEq _ hxR, hEq _ hx]
  simp only [dirichletOrthogonalDifference, div_eq_mul_inv, mul_comm]

theorem dirichlet_unitary_difference_meanCofactor_pos {n : ℕ}
    (R : E n ≃ₗᵢ[ℝ] E n) (hJ : ∀ y, R (J y) = J (R y))
    {u : E n → ℝ} (hu : ContDiffOn ℝ 2 u (closedUnitBall n))
    (hPos : ∀ y ∈ unitBall n, (complexHessian u y).PosDef)
    {x : E n} (hx : x ∈ unitBall n) {v : E n} (hv : v ≠ 0) :
    0 < inner ℝ
      (dirichletMeanCofactor (complexHessian u x) (complexHessian (u ∘ R) x) v) v := by
  have hxR : R x ∈ unitBall n := by
    simpa only [unitBall, mem_ball_zero_iff, R.norm_map] using hx
  have huAt : ContDiffAt ℝ 2 u (R x) :=
    (hu.mono ball_subset_closedBall).contDiffAt (isOpen_ball.mem_nhds hxR)
  exact dirichletMeanCofactor_pos (hPos x hx)
    ((complexHessian_posDef_and_det_comp_unitary R hJ huAt).1.mpr (hPos _ hxR)) hv

theorem dirichlet_unitary_difference_meanCofactor_symmetric {n : ℕ}
    (R : E n ≃ₗᵢ[ℝ] E n) (hJ : ∀ y, R (J y) = J (R y))
    {u : E n → ℝ} (hu : ContDiffOn ℝ 2 u (closedUnitBall n))
    (hPos : ∀ y ∈ unitBall n, (complexHessian u y).PosDef)
    {x : E n} (hx : x ∈ unitBall n) (v z : E n) :
    inner ℝ
      (dirichletMeanCofactor (complexHessian u x) (complexHessian (u ∘ R) x) v) z =
    inner ℝ
      (dirichletMeanCofactor (complexHessian u x) (complexHessian (u ∘ R) x) z) v := by
  have hxR : R x ∈ unitBall n := by
    simpa only [unitBall, mem_ball_zero_iff, R.norm_map] using hx
  have huAt : ContDiffAt ℝ 2 u (R x) :=
    (hu.mono ball_subset_closedBall).contDiffAt (isOpen_ball.mem_nhds hxR)
  exact dirichletMeanCofactor_symmetric (hPos x hx)
    ((complexHessian_posDef_and_det_comp_unitary R hJ huAt).1.mpr (hPos _ hxR)) v z

end KEBall
