import KEBall.DirichletUniformDiscreteCofactor
import KEBall.DirichletSecondDiscreteEquation

/-!
# The actual second-difference error on the closed ball

The error is defined using the within Hessians of the same potential and
its actual rotations. Its L2 norm is controlled by the fourth-power
integral of the Hessian of the first difference.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Filter Matrix MeasureTheory Metric Set
open scoped BigOperators ComplexOrder ContDiff Matrix.Norms.Elementwise Topology

namespace KEBall

private theorem contDiffOn_comp_orthogonal_closed {n : ℕ} {m : ℕ∞ω}
    (R : E n ≃ₗᵢ[ℝ] E n) {u : E n → ℝ}
    (hu : ContDiffOn ℝ m u (closedUnitBall n)) :
    ContDiffOn ℝ m (u ∘ R) (closedUnitBall n) := by
  have hMaps : MapsTo R (closedUnitBall n) (closedUnitBall n) := by
    intro x hx
    simpa only [closedUnitBall, mem_closedBall_zero_iff, R.norm_map] using hx
  exact hu.comp R.toContinuousLinearEquiv.contDiff.contDiffOn hMaps

noncomputable def dirichletSecondDiscreteCofactorError {n : ℕ}
    (R : E n ≃ₗᵢ[ℝ] E n) (τ : ℝ) (u : E n → ℝ) (x : E n) : ℝ :=
  τ⁻¹ * dirichletContractionCLM n
    (dirichletMeanCofactor (dirichletWithinComplexHessian (u ∘ R) x)
        (dirichletWithinComplexHessian ((u ∘ R) ∘ R) x) -
      dirichletMeanCofactor (dirichletWithinComplexHessian u x)
        (dirichletWithinComplexHessian (u ∘ R) x))
    (dirichletWithinRealHessian ((dirichletOrthogonalDifference R τ u) ∘ R) x)

theorem continuousOn_dirichletSecondDiscreteCofactorError {n : ℕ}
    (R : E n ≃ₗᵢ[ℝ] E n) (τ : ℝ) {u : E n → ℝ}
    (hu : ContDiffOn ℝ 2 u (closedUnitBall n)) :
    ContinuousOn (dirichletSecondDiscreteCofactorError R τ u) (closedUnitBall n) := by
  have huR := contDiffOn_comp_orthogonal_closed R hu
  have huRR := contDiffOn_comp_orthogonal_closed R huR
  have hqR := contDiffOn_comp_orthogonal_closed R (contDiffOn_dirichletOrthogonalDifference R τ hu)
  have hU := continuousOn_dirichletWithinComplexHessian_of_C2 hu
  have hUR := continuousOn_dirichletWithinComplexHessian_of_C2 huR
  have hURR := continuousOn_dirichletWithinComplexHessian_of_C2 huRR
  have hA := (continuous_dirichletMeanCofactor (n := n)).comp_continuousOn (hU.prodMk hUR)
  have hB := (continuous_dirichletMeanCofactor (n := n)).comp_continuousOn (hUR.prodMk hURR)
  have hH := continuousOn_dirichletWithinRealHessian hqR
  have hE := (((dirichletContractionCLM n).continuous.comp_continuousOn
    (hB.sub hA)).clm_apply hH).const_mul τ⁻¹
  exact hE

theorem dirichletSecondDiscreteCofactorError_eq_on_ball {n : ℕ}
    (R : E n ≃ₗᵢ[ℝ] E n) (τ : ℝ) {u : E n → ℝ}
    (hu : ContDiffOn ℝ 2 u (closedUnitBall n)) {x : E n} (hx : x ∈ unitBall n) :
    dirichletSecondDiscreteCofactorError R τ u x =
      τ⁻¹ * dirichletContractionCLM n
        (dirichletMeanCofactor (complexHessian (u ∘ R) x)
            (complexHessian ((u ∘ R) ∘ R) x) -
          dirichletMeanCofactor (complexHessian u x) (complexHessian (u ∘ R) x))
        (realHessian ((dirichletOrthogonalDifference R τ u) ∘ R) x) := by
  have huR := contDiffOn_comp_orthogonal_closed R hu
  have huRR := contDiffOn_comp_orthogonal_closed R huR
  unfold dirichletSecondDiscreteCofactorError
  rw [dirichletWithinComplexHessian_eq_on_ball_of_C2 huR hx,
    dirichletWithinComplexHessian_eq_on_ball_of_C2 huRR hx,
    dirichletWithinComplexHessian_eq_on_ball_of_C2 hu hx,
    dirichletWithinRealHessian_eq_on_ball _ hx]

private theorem square_sum_mul_sq_le_fourth (a b : ℝ) :
    (a + b) ^ 2 * b ^ 2 ≤ a ^ 4 + 3 * b ^ 4 := by
  nlinarith only [sq_nonneg (a * b - b ^ 2), sq_nonneg (a ^ 2 - b ^ 2)]

theorem exists_dirichlet_second_error_sq_bound {n : ℕ}
    {u : E n → ℝ} (hu : ContDiffOn ℝ 2 u (closedUnitBall n)) :
    ∃ C ≥ (0 : ℝ), ∀ R : E n ≃ₗᵢ[ℝ] E n, ∀ τ : ℝ, τ ≠ 0 →
      ∀ x ∈ unitBall n,
        (dirichletSecondDiscreteCofactorError R τ u x) ^ 2 ≤ C *
          (‖dirichletWithinRealHessian (dirichletOrthogonalDifference R τ u) x‖ ^ 4 +
            3 * ‖dirichletWithinRealHessian
              ((dirichletOrthogonalDifference R τ u) ∘ R) x‖ ^ 4) := by
  obtain ⟨K, _, hK⟩ := exists_uniform_dirichlet_second_cofactor_error_bound hu
  refine ⟨K ^ 2, sq_nonneg K, ?_⟩
  intro R τ hτ x hx
  rw [dirichletSecondDiscreteCofactorError_eq_on_ball R τ hu hx,
    dirichletWithinRealHessian_eq_on_ball _ hx,
    dirichletWithinRealHessian_eq_on_ball _ hx]
  let e := τ⁻¹ * dirichletContractionCLM n
    (dirichletMeanCofactor (complexHessian (u ∘ R) x)
        (complexHessian ((u ∘ R) ∘ R) x) -
      dirichletMeanCofactor (complexHessian u x) (complexHessian (u ∘ R) x))
    (realHessian ((dirichletOrthogonalDifference R τ u) ∘ R) x)
  let a := ‖realHessian (dirichletOrthogonalDifference R τ u) x‖
  let b := ‖realHessian ((dirichletOrthogonalDifference R τ u) ∘ R) x‖
  have hBound : |e| ≤ K * (a + b) * b := hK R τ hτ x hx
  have hSq := pow_le_pow_left₀ (abs_nonneg e) hBound 2
  rw [sq_abs] at hSq
  calc
    e ^ 2 ≤ (K * (a + b) * b) ^ 2 := hSq
    _ = K ^ 2 * ((a + b) ^ 2 * b ^ 2) := by ring
    _ ≤ K ^ 2 * (a ^ 4 + 3 * b ^ 4) :=
      mul_le_mul_of_nonneg_left (square_sum_mul_sq_le_fourth a b) (sq_nonneg K)

theorem integral_dirichletWithinRealHessian_comp_norm_pow_four {n : ℕ}
    (R : E n ≃ₗᵢ[ℝ] E n) {q : E n → ℝ}
    (hq : ContDiffOn ℝ 2 q (closedUnitBall n)) :
    (∫ x in unitBall n, ‖dirichletWithinRealHessian (q ∘ R) x‖ ^ 4 ∂volume0 n) =
      ∫ x in unitBall n, ‖dirichletWithinRealHessian q x‖ ^ 4 ∂volume0 n := by
  calc
    _ = ∫ x in unitBall n, ‖dirichletWithinRealHessian q (R x)‖ ^ 4 ∂volume0 n := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem (μ := volume0 n)
        (show MeasurableSet (unitBall n) from measurableSet_ball)] with x hx
      rw [dirichletWithinRealHessian_comp_orthogonal R hq (ball_subset_closedBall hx),
        norm_dirichletBilinearPullback]
    _ = _ := integral_dirichlet_orthogonal_comp R
      (fun x => ‖dirichletWithinRealHessian q x‖ ^ 4)

theorem exists_integral_dirichlet_second_error_sq_bound {n : ℕ} (hn : 0 < n)
    {u : E n → ℝ} (hu : ContDiffOn ℝ 2 u (closedUnitBall n)) :
    ∃ C ≥ (0 : ℝ), ∀ R : E n ≃ₗᵢ[ℝ] E n, ∀ τ : ℝ, τ ≠ 0 →
      (∫ x in unitBall n, (dirichletSecondDiscreteCofactorError R τ u x) ^ 2 ∂volume0 n) ≤
        C * ∫ x in unitBall n,
          ‖dirichletWithinRealHessian (dirichletOrthogonalDifference R τ u) x‖ ^ 4 ∂volume0 n := by
  obtain ⟨C, hC, hPoint⟩ := exists_dirichlet_second_error_sq_bound hu
  refine ⟨4 * C, by positivity, ?_⟩
  intro R τ hτ
  let q := dirichletOrthogonalDifference R τ u
  let a (x : E n) := ‖dirichletWithinRealHessian q x‖ ^ 4
  let b (x : E n) := ‖dirichletWithinRealHessian (q ∘ R) x‖ ^ 4
  have hq : ContDiffOn ℝ 2 q (closedUnitBall n) := contDiffOn_dirichletOrthogonalDifference R τ hu
  have ha : ContinuousOn a (closedUnitBall n) :=
    (continuousOn_dirichletWithinRealHessian hq).norm.pow 4
  have hb : ContinuousOn b (closedUnitBall n) :=
    (continuousOn_dirichletWithinRealHessian (contDiffOn_comp_orthogonal_closed R hq)).norm.pow 4
  have he : ContinuousOn (dirichletSecondDiscreteCofactorError R τ u) (closedUnitBall n) :=
    continuousOn_dirichletSecondDiscreteCofactorError R τ hu
  letI : NeZero n := ⟨hn.ne'⟩
  letI : IsProbabilityMeasure ((volume0 n).restrict (unitBall n)) :=
    volume0_restrict_isProbability n
  have hInt {f : E n → ℝ} (hf : ContinuousOn f (closedUnitBall n)) :
      IntegrableOn f (unitBall n) (volume0 n) :=
    (dirichlet_memLp_of_continuousOn hn hf 1).integrable le_rfl
  have hSum :
      (∫ x in unitBall n, (a x + 3 * b x) ∂volume0 n) =
        (∫ x in unitBall n, a x ∂volume0 n) + 3 * ∫ x in unitBall n, b x ∂volume0 n := by
    have h := integral_add (hInt ha) ((hInt hb).const_mul 3)
    change (∫ x in unitBall n, a x + 3 * b x ∂volume0 n) =
      (∫ x in unitBall n, a x ∂volume0 n) +
        ∫ x in unitBall n, 3 * b x ∂volume0 n at h
    rw [integral_const_mul] at h
    exact h
  have hRot : (∫ x in unitBall n, b x ∂volume0 n) =
      ∫ x in unitBall n, a x ∂volume0 n :=
    integral_dirichletWithinRealHessian_comp_norm_pow_four R hq
  have h := setIntegral_mono_on (hInt (he.pow 2))
    (hInt ((ha.add (hb.const_mul 3)).const_mul C)) measurableSet_ball
    (hPoint R τ hτ)
  change (∫ x in unitBall n, (dirichletSecondDiscreteCofactorError R τ u x) ^ 2 ∂volume0 n) ≤
    ∫ x in unitBall n, C * (a x + 3 * b x) ∂volume0 n at h
  rw [integral_const_mul, hSum, hRot] at h
  convert h using 1 <;> ring

end KEBall
