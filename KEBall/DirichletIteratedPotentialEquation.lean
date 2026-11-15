import KEBall.DirichletDeterminantLeadingLimit
import KEBall.DirichletIteratedHessianRemainder

/-!
# An arbitrary-order equation for the actual potential difference

The error contains the exact polynomial remainder and the exact Hessian
pullback remainder. The equation is for the given C2 potential itself.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Matrix Metric Set
open scoped BigOperators ContDiff Matrix.Norms.Elementwise

namespace KEBall

theorem dirichletIteratedFieldDifference_congr_ball {n : ℕ} {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (R : E n ≃ₗᵢ[ℝ] E n) (τ : ℝ) {F G : E n → V}
    (h : EqOn F G (unitBall n)) (k : ℕ) :
    EqOn (dirichletIteratedFieldDifference R τ F k)
      (dirichletIteratedFieldDifference R τ G k) (unitBall n) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    intro x hx
    have hxR : R x ∈ unitBall n := by
      simpa only [unitBall, mem_ball_zero_iff, R.norm_map] using hx
    simp only [dirichletIteratedFieldDifference, dirichletFieldDifference, ih hx, ih hxR]

noncomputable def dirichletIteratedPotentialLeadingField {n : ℕ}
    (R : E n ≃ₗᵢ[ℝ] E n) (u : E n → ℝ) (k : ℕ) (x : E n) :
    (E n →L[ℝ] E n →L[ℝ] ℝ) →L[ℝ] ℝ :=
  dirichletRealDeterminantDifferenceCLM
    (dirichletWithinComplexHessian u (R^[k] x))
    (dirichletWithinComplexHessian u (R^[k + 1] x))

noncomputable def dirichletIteratedPotentialDeterminantError {n : ℕ}
    (R : E n ≃ₗᵢ[ℝ] E n) (τ : ℝ) (u : E n → ℝ) (k : ℕ) (x : E n) : ℝ :=
  (dirichletDeterminantDifferenceRemainder R τ (dirichletWithinComplexHessian u) k x).re +
    dirichletIteratedPotentialLeadingField R u k x
      (dirichletIteratedFieldDifference R τ (dirichletWithinRealHessian u) (k + 1) x -
        dirichletWithinRealHessian (dirichletIteratedOrthogonalDifference R τ u (k + 1)) x)

theorem dirichlet_iterated_potential_determinant_equation {n : ℕ}
    (R : E n ≃ₗᵢ[ℝ] E n) (τ : ℝ) {u f : E n → ℝ}
    (hu : ContDiffOn ℝ 2 u (closedUnitBall n))
    (hEq : ∀ x ∈ unitBall n, (complexHessian u x).det.re = f x)
    (k : ℕ) {x : E n} (hx : x ∈ unitBall n) :
    dirichletIteratedPotentialLeadingField R u k x
      (dirichletWithinRealHessian (dirichletIteratedOrthogonalDifference R τ u (k + 1)) x) =
      dirichletIteratedOrthogonalDifference R τ f (k + 1) x -
        dirichletIteratedPotentialDeterminantError R τ u k x := by
  have hEqWithin : EqOn (fun y => (dirichletWithinComplexHessian u y).det.re) f (unitBall n) := by
    intro y hy
    change (dirichletWithinComplexHessian u y).det.re = f y
    rw [dirichletWithinComplexHessian_eq_on_ball_of_C2 hu hy, hEq y hy]
  have hF := dirichletIteratedFieldDifference_congr_ball R τ hEqWithin (k + 1) hx
  have hReal := congrArg (fun F => F x)
    (dirichletIteratedFieldDifference_clm R τ Complex.reCLM
      (fun y => (dirichletWithinComplexHessian u y).det) (k + 1))
  simp only [Complex.reCLM_apply] at hReal
  have hComplex := congrArg (fun F => F x)
    (dirichletIteratedFieldDifference_clm R τ dirichletComplexHessianCLM
      (dirichletWithinRealHessian u) (k + 1))
  have hDet := congrArg Complex.re
    (dirichletIteratedFieldDifference_determinant_eq R τ (dirichletWithinComplexHessian u) k x)
  rw [Complex.add_re] at hDet
  have hLin : dirichletIteratedPotentialLeadingField R u k x
      (dirichletIteratedFieldDifference R τ (dirichletWithinRealHessian u) (k + 1) x) +
      (dirichletDeterminantDifferenceRemainder R τ (dirichletWithinComplexHessian u) k x).re =
      dirichletIteratedOrthogonalDifference R τ f (k + 1) x := by
    rw [← dirichletIteratedFieldDifference_real]
    rw [← hF, hReal, hDet]
    congr 1
    dsimp only [dirichletIteratedPotentialLeadingField, dirichletRealDeterminantDifferenceCLM,
      ContinuousLinearMap.comp_apply, Complex.reCLM_apply]
    exact congrArg (fun B =>
      (dirichletDeterminantDifferenceCLM
        (dirichletWithinComplexHessian u (R^[k] x))
        (dirichletWithinComplexHessian u (R^[k + 1] x)) B).re) hComplex.symm
  unfold dirichletIteratedPotentialDeterminantError
  rw [map_sub]
  linarith only [hLin]

theorem continuousOn_dirichletIteratedPotentialLeadingField {n : ℕ}
    (R : E n ≃ₗᵢ[ℝ] E n) {u : E n → ℝ}
    (hu : ContDiffOn ℝ 2 u (closedUnitBall n)) (k : ℕ) :
    ContinuousOn (dirichletIteratedPotentialLeadingField R u k) (closedUnitBall n) := by
  convert! (continuous_dirichletRealDeterminantDifferenceCLM (n := n)).comp_continuousOn
    ((continuousOn_dirichlet_orthogonal_iterate_comp R
      (continuousOn_dirichletWithinComplexHessian_of_C2 hu) k).prodMk
    (continuousOn_dirichlet_orthogonal_iterate_comp R
      (continuousOn_dirichletWithinComplexHessian_of_C2 hu) (k + 1))) using 1

theorem continuousOn_dirichletIteratedPotentialDeterminantError {n : ℕ}
    (R : E n ≃ₗᵢ[ℝ] E n) (τ : ℝ) {u : E n → ℝ}
    (hu : ContDiffOn ℝ 2 u (closedUnitBall n)) (k : ℕ) :
    ContinuousOn (dirichletIteratedPotentialDeterminantError R τ u k) (closedUnitBall n) := by
  have hM := continuousOn_dirichletWithinComplexHessian_of_C2 hu
  have hRem : ContinuousOn
      (dirichletDeterminantDifferenceRemainder R τ (dirichletWithinComplexHessian u) k)
      (closedUnitBall n) :=
    continuousOn_finsetSum _ (fun σ _ =>
      (continuousOn_dirichletProductDifferenceRemainder R τ Finset.univ
        (fun i y => dirichletWithinComplexHessian u y (σ i) i)
        (fun i _ => (continuous_apply i).comp_continuousOn
          ((continuous_apply (σ i)).comp_continuousOn hM)) k).const_mul _)
  exact (Complex.continuous_re.comp_continuousOn hRem).add
    ((continuousOn_dirichletIteratedPotentialLeadingField R hu k).clm_apply
      ((continuousOn_dirichletIteratedFieldDifference R τ
        (continuousOn_dirichletWithinRealHessian hu) (k + 1)).sub
      (continuousOn_dirichletWithinRealHessian
        (contDiffOn_dirichletIteratedOrthogonalDifference R τ hu (k + 1)))))

end KEBall
