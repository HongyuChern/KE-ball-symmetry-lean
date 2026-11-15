import KEBall.DirichletDiscreteCofactorEquation
import KEBall.DirichletAveragedCofactorBounds
import KEBall.DirichletComplexHessianHolder
import KEBall.DirichletBoundedBilinear

/-!
# The coefficient increment in the second difference equation

All three Hessians are Hessians of the actual pulled-back potentials.
The bounds here retain the explicit matrix-ball hypotheses; choosing that
ball uniformly in the step is a separate compactness/norm argument.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Matrix Metric Set
open scoped BigOperators ComplexOrder ContDiff Matrix.Norms.Elementwise NNReal

namespace KEBall

theorem complexHessian_comp_sub_eq_smul_discreteHessian {n : ℕ}
    (R : E n ≃ₗᵢ[ℝ] E n) {τ : ℝ} (hτ : τ ≠ 0)
    {u : E n → ℝ} {x : E n}
    (hu : ContDiffAt ℝ 2 u x) (huR : ContDiffAt ℝ 2 u (R x)) :
    complexHessian (u ∘ R) x - complexHessian u x =
      τ • dirichletComplexHessianCLM
        (realHessian (dirichletOrthogonalDifference R τ u) x) := by
  rw [realHessian_dirichletOrthogonalDifference R τ hu huR, map_smul, map_sub,
    dirichletComplexHessianCLM_apply, dirichletComplexHessianCLM_apply,
    complexHessianOfRealBilinear_eq
      (huR.comp x R.toContinuousLinearEquiv.contDiff.contDiffAt),
    complexHessianOfRealBilinear_eq hu, smul_smul, mul_inv_cancel₀ hτ, one_smul]

theorem norm_complexHessian_comp_sub_le_discreteHessian {n : ℕ}
    (R : E n ≃ₗᵢ[ℝ] E n) {τ : ℝ} (hτ : τ ≠ 0)
    {u : E n → ℝ} {x : E n}
    (hu : ContDiffAt ℝ 2 u x) (huR : ContDiffAt ℝ 2 u (R x)) :
    ‖complexHessian (u ∘ R) x - complexHessian u x‖ ≤
      |τ| * ‖(@dirichletComplexHessianCLM n)‖ *
        ‖realHessian (dirichletOrthogonalDifference R τ u) x‖ := by
  rw [complexHessian_comp_sub_eq_smul_discreteHessian R hτ hu huR,
    norm_smul, Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left
    ((@dirichletComplexHessianCLM n).le_opNorm _) (abs_nonneg τ)).trans_eq
      (mul_assoc _ _ _).symm

theorem norm_dirichlet_second_difference_cofactor_increment_le {n : ℕ}
    (R : E n ≃ₗᵢ[ℝ] E n) {τ : ℝ} (hτ : τ ≠ 0)
    {u : E n → ℝ} (hu : ContDiffOn ℝ 2 u (closedUnitBall n))
    {x : E n} (hx : x ∈ unitBall n)
    {r : ℝ} {K : ℝ≥0}
    (hLip : LipschitzOnWith K (@dirichletCofactorOfMatrix n) (closedBall 0 r))
    (h₀ : ‖complexHessian u x‖ ≤ r)
    (h₁ : ‖complexHessian (u ∘ R) x‖ ≤ r)
    (h₂ : ‖complexHessian ((u ∘ R) ∘ R) x‖ ≤ r) :
    ‖dirichletMeanCofactor (complexHessian (u ∘ R) x)
        (complexHessian ((u ∘ R) ∘ R) x) -
      dirichletMeanCofactor (complexHessian u x) (complexHessian (u ∘ R) x)‖ ≤
      (K : ℝ) * (|τ| * ‖(@dirichletComplexHessianCLM n)‖ *
        (‖realHessian (dirichletOrthogonalDifference R τ u) x‖ +
          ‖realHessian ((dirichletOrthogonalDifference R τ u) ∘ R) x‖)) := by
  have hMaps : MapsTo R (unitBall n) (unitBall n) := by
    intro y hy
    simpa only [unitBall, mem_ball_zero_iff, R.norm_map] using hy
  have hC2 (y : E n) (hy : y ∈ unitBall n) : ContDiffAt ℝ 2 u y :=
    (hu.mono ball_subset_closedBall).contDiffAt (isOpen_ball.mem_nhds hy)
  have hA := norm_complexHessian_comp_sub_le_discreteHessian R hτ
    (hC2 x hx) (hC2 _ (hMaps hx))
  have hB := norm_complexHessian_comp_sub_le_discreteHessian R hτ
    ((hC2 _ (hMaps hx)).comp x R.toContinuousLinearEquiv.contDiff.contDiffAt)
    ((hC2 _ (hMaps (hMaps hx))).comp (R x) R.toContinuousLinearEquiv.contDiff.contDiffAt)
  have hComm : dirichletOrthogonalDifference R τ (u ∘ R) =
      (dirichletOrthogonalDifference R τ u) ∘ R := rfl
  rw [hComm] at hB
  let T := |τ| * ‖(@dirichletComplexHessianCLM n)‖
  have hT : 0 ≤ T := mul_nonneg (abs_nonneg τ) (norm_nonneg _)
  apply norm_dirichletMeanCofactor_sub_le_of_lipschitz hLip h₁ h₂ h₀ h₁
  · exact hA.trans (mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_right (norm_nonneg _)) hT)
  · exact hB.trans (mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_left (norm_nonneg _)) hT)

end KEBall
