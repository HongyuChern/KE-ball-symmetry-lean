import KEBall.DirichletBilinearPullback
import KEBall.DirichletDiscreteCofactorIncrement
import KEBall.DirichletDiscreteHessianEstimate

/-!
# Uniform coefficient bounds for second unitary differences

A compactness bound for the actual within Hessian controls every
orthogonal pullback, uniformly in the rotation and in the nonzero step.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Matrix Metric Set
open scoped BigOperators ComplexOrder ContDiff Matrix.Norms.Elementwise NNReal

namespace KEBall

theorem dirichletWithinRealHessian_comp_orthogonal {n : ℕ}
    (R : E n ≃ₗᵢ[ℝ] E n) {u : E n → ℝ}
    (hu : ContDiffOn ℝ 2 u (closedUnitBall n)) {x : E n}
    (hx : x ∈ closedUnitBall n) :
    dirichletWithinRealHessian (u ∘ R) x =
      dirichletBilinearPullback R (dirichletWithinRealHessian u (R x)) := by
  have hMaps : MapsTo R (closedUnitBall n) (closedUnitBall n) := by
    intro y hy
    simpa only [closedUnitBall, mem_closedBall_zero_iff, R.norm_map] using hy
  have hMapsB : MapsTo R (unitBall n) (unitBall n) := by
    intro y hy
    simpa only [unitBall, mem_ball_zero_iff, R.norm_map] using hy
  have huR : ContDiffOn ℝ 2 (u ∘ R) (closedUnitBall n) :=
    hu.comp R.toContinuousLinearEquiv.contDiff.contDiffOn hMaps
  have hLeft := continuousOn_dirichletWithinRealHessian huR
  have hRight := (dirichletBilinearPullbackCLM R).continuous.comp_continuousOn
    ((continuousOn_dirichletWithinRealHessian hu).comp R.continuous.continuousOn hMaps)
  have hEq : EqOn (dirichletWithinRealHessian (u ∘ R))
      (fun y => dirichletBilinearPullback R (dirichletWithinRealHessian u (R y)))
      (unitBall n) := by
    intro y hy
    change dirichletWithinRealHessian (u ∘ R) y =
      dirichletBilinearPullback R (dirichletWithinRealHessian u (R y))
    rw [dirichletWithinRealHessian_eq_on_ball _ hy,
      dirichletWithinRealHessian_eq_on_ball u (hMapsB hy),
      realHessian_comp_eq_dirichletBilinearPullback]
  exact hEq.of_subset_closure hLeft hRight ball_subset_closedBall
    (by rw [unitBall, closedUnitBall, closure_ball _ (by norm_num : (1 : ℝ) ≠ 0)]) hx

theorem dirichletWithinComplexHessian_comp_orthogonal {n : ℕ}
    (R : E n ≃ₗᵢ[ℝ] E n) {u : E n → ℝ}
    (hu : ContDiffOn ℝ 2 u (closedUnitBall n)) {x : E n}
    (hx : x ∈ closedUnitBall n) :
    dirichletWithinComplexHessian (u ∘ R) x =
      dirichletComplexHessianCLM
        (dirichletBilinearPullback R (dirichletWithinRealHessian u (R x))) := by
  change complexHessianOfRealBilinear (dirichletWithinRealHessian (u ∘ R) x) =
    complexHessianOfRealBilinear
      (dirichletBilinearPullback R (dirichletWithinRealHessian u (R x)))
  rw [dirichletWithinRealHessian_comp_orthogonal R hu hx]

theorem exists_uniform_withinComplexHessian_orthogonal_bound_of_C2 {n : ℕ}
    {u : E n → ℝ} (hu : ContDiffOn ℝ 2 u (closedUnitBall n)) :
    ∃ r ≥ (0 : ℝ), ∀ R : E n ≃ₗᵢ[ℝ] E n, ∀ x ∈ closedUnitBall n,
      ‖dirichletWithinComplexHessian (u ∘ R) x‖ ≤ r := by
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : E n) 1).exists_bound_of_continuousOn
    (continuousOn_dirichletWithinRealHessian hu)
  refine ⟨‖(@dirichletComplexHessianCLM n)‖ * max M 0, by positivity, ?_⟩
  intro R x hx
  have hRx : R x ∈ closedUnitBall n := by
    simpa only [closedUnitBall, mem_closedBall_zero_iff, R.norm_map] using hx
  rw [dirichletWithinComplexHessian_comp_orthogonal R hu hx]
  calc
    _ ≤ ‖(@dirichletComplexHessianCLM n)‖ *
        ‖dirichletBilinearPullback R (dirichletWithinRealHessian u (R x))‖ :=
      (@dirichletComplexHessianCLM n).le_opNorm _
    _ = ‖(@dirichletComplexHessianCLM n)‖ *
        ‖dirichletWithinRealHessian u (R x)‖ := by rw [norm_dirichletBilinearPullback]
    _ ≤ ‖(@dirichletComplexHessianCLM n)‖ * max M 0 :=
      mul_le_mul_of_nonneg_left ((hM _ hRx).trans (le_max_left M 0)) (norm_nonneg _)

theorem exists_uniform_dirichlet_second_cofactor_increment_bound {n : ℕ}
    {u : E n → ℝ} (hu : ContDiffOn ℝ 2 u (closedUnitBall n)) :
    ∃ C ≥ (0 : ℝ), ∀ R : E n ≃ₗᵢ[ℝ] E n, ∀ τ : ℝ, τ ≠ 0 →
      ∀ x ∈ unitBall n,
        ‖dirichletMeanCofactor (complexHessian (u ∘ R) x)
            (complexHessian ((u ∘ R) ∘ R) x) -
          dirichletMeanCofactor (complexHessian u x) (complexHessian (u ∘ R) x)‖ ≤
          |τ| * C * (‖realHessian (dirichletOrthogonalDifference R τ u) x‖ +
            ‖realHessian ((dirichletOrthogonalDifference R τ u) ∘ R) x‖) := by
  obtain ⟨r, _, hBound⟩ := exists_uniform_withinComplexHessian_orthogonal_bound_of_C2 hu
  obtain ⟨K, hLip⟩ := exists_dirichlet_cofactor_lipschitz_on_matrix_ball (n := n) r
  have hClassical (R : E n ≃ₗᵢ[ℝ] E n) (x : E n) (hx : x ∈ unitBall n) :
      ‖complexHessian (u ∘ R) x‖ ≤ r := by
    have hMaps : MapsTo R (closedUnitBall n) (closedUnitBall n) := by
      intro y hy
      simpa only [closedUnitBall, mem_closedBall_zero_iff, R.norm_map] using hy
    have huR : ContDiffOn ℝ 2 (u ∘ R) (closedUnitBall n) :=
      hu.comp R.toContinuousLinearEquiv.contDiff.contDiffOn hMaps
    rw [← dirichletWithinComplexHessian_eq_on_ball_of_C2 huR hx]
    exact hBound R x (ball_subset_closedBall hx)
  refine ⟨(K : ℝ) * ‖(@dirichletComplexHessianCLM n)‖, by positivity, ?_⟩
  intro R τ hτ x hx
  have h₀ : ‖complexHessian u x‖ ≤ r := by
    simpa using hClassical (LinearIsometryEquiv.refl ℝ (E n)) x hx
  have h₁ := hClassical R x hx
  have h₂ := hClassical (R.trans R) x hx
  change ‖complexHessian ((u ∘ R) ∘ R) x‖ ≤ r at h₂
  exact (norm_dirichlet_second_difference_cofactor_increment_le
    R hτ hu hx hLip h₀ h₁ h₂).trans_eq (by ring)

theorem exists_uniform_dirichlet_second_cofactor_error_bound {n : ℕ}
    {u : E n → ℝ} (hu : ContDiffOn ℝ 2 u (closedUnitBall n)) :
    ∃ C ≥ (0 : ℝ), ∀ R : E n ≃ₗᵢ[ℝ] E n, ∀ τ : ℝ, τ ≠ 0 →
      ∀ x ∈ unitBall n,
        |τ⁻¹ * dirichletContractionCLM n
          (dirichletMeanCofactor (complexHessian (u ∘ R) x)
              (complexHessian ((u ∘ R) ∘ R) x) -
            dirichletMeanCofactor (complexHessian u x) (complexHessian (u ∘ R) x))
          (realHessian ((dirichletOrthogonalDifference R τ u) ∘ R) x)| ≤
        C * (‖realHessian (dirichletOrthogonalDifference R τ u) x‖ +
          ‖realHessian ((dirichletOrthogonalDifference R τ u) ∘ R) x‖) *
          ‖realHessian ((dirichletOrthogonalDifference R τ u) ∘ R) x‖ := by
  obtain ⟨K, hK, hInc⟩ := exists_uniform_dirichlet_second_cofactor_increment_bound hu
  let L := dirichletContractionCLM n
  refine ⟨‖L‖ * K, by positivity, ?_⟩
  intro R τ hτ x hx
  let A := dirichletMeanCofactor (complexHessian u x) (complexHessian (u ∘ R) x)
  let B := dirichletMeanCofactor (complexHessian (u ∘ R) x)
    (complexHessian ((u ∘ R) ∘ R) x)
  let H₀ := realHessian (dirichletOrthogonalDifference R τ u) x
  let H₁ := realHessian ((dirichletOrthogonalDifference R τ u) ∘ R) x
  have hI : ‖B - A‖ ≤ |τ| * K * (‖H₀‖ + ‖H₁‖) := hInc R τ hτ x hx
  have hL : ‖L (B - A) H₁‖ ≤ ‖L‖ * (|τ| * K * (‖H₀‖ + ‖H₁‖)) * ‖H₁‖ :=
    (L.le_opNorm₂ _ _).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hI (norm_nonneg L)) (norm_nonneg H₁))
  change |τ⁻¹ * L (B - A) H₁| ≤ (‖L‖ * K) * (‖H₀‖ + ‖H₁‖) * ‖H₁‖
  calc
    _ = |τ|⁻¹ * ‖L (B - A) H₁‖ := by rw [abs_mul, abs_inv, Real.norm_eq_abs]
    _ ≤ |τ|⁻¹ * (‖L‖ * (|τ| * K * (‖H₀‖ + ‖H₁‖)) * ‖H₁‖) :=
      mul_le_mul_of_nonneg_left hL (inv_nonneg.mpr (abs_nonneg τ))
    _ = _ := by field_simp

end KEBall
