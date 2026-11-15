import KEBall.DirichletBoundaryAverageHarnack
import KEBall.DirichletBoundaryCapPropagation
import KEBall.DirichletBoundaryGainConstants

/-!
# Uniform boundary improvement for the actual cofactor equation

Two nonnegative defects whose sum is `osc * rho` cannot both remain small
in the common interior ball.  One fixed defect therefore gains a definite
multiple of `osc` throughout the smaller boundary cap.  The bounded source
contributes exactly an error of order `S * R` after division by `rho`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Filter InnerProductSpace MeasureTheory Metric Set
open scoped ComplexOrder ContDiff Topology

namespace KEBall

local notation "e[" n "]" => EuclideanSpace.basisFun (Fin (2 * n)) ℝ

theorem exists_uniform_dirichlet_boundary_defect_improvement {n : ℕ} (hn : 2 ≤ n)
    {c K : ℝ} (hc : 0 < c) (hK : 0 ≤ K) :
    ∃ δ loss : ℝ, 0 < δ ∧ δ < 1 ∧ 0 ≤ loss ∧
      ∀ (u : E n → ℝ), SmoothNear (closedUnitBall n) u →
        (∀ x ∈ unitBall n, (complexHessian u x).PosDef) →
        (∀ x ∈ unitBall n, ‖dirichletCofactorOperator u x‖ ≤ K) →
        (∀ x ∈ unitBall n, ∀ v : E n,
          c * ‖v‖ ^ 2 ≤ inner ℝ (dirichletCofactorOperator u x v) v) →
      ∀ (w₁ w₂ : E n → ℝ), SmoothNear (closedUnitBall n) w₁ →
        SmoothNear (closedUnitBall n) w₂ → ∀ S osc : ℝ, 0 ≤ S → 0 ≤ osc →
        (∀ x ∈ unitBall n,
          dirichletBilinearContraction e[n] (dirichletCofactorOperator u x) (realHessian w₁ x) ≤ S) →
        (∀ x ∈ unitBall n,
          dirichletBilinearContraction e[n] (dirichletCofactorOperator u x) (realHessian w₂ x) ≤ S) →
        ∀ p₀ ∈ unitSphere n, ∀ R : ℝ, 0 < R → R ≤ 1 →
          (∀ x ∈ closedUnitBall n, x ∈ ball p₀ (4 * R) → 0 ≤ w₁ x) →
          (∀ x ∈ closedUnitBall n, x ∈ ball p₀ (4 * R) → 0 ≤ w₂ x) →
          (∀ x ∈ closedUnitBall n, x ∈ ball p₀ (4 * R) →
            w₁ x + w₂ x = osc * dirichletBoundaryDistanceProxy x) →
          (∀ x ∈ unitBall n, x ∈ ball p₀ (R / 64) →
            δ * osc - loss * S * R ≤ w₁ x / dirichletBoundaryDistanceProxy x) ∨
          (∀ x ∈ unitBall n, x ∈ ball p₀ (R / 64) →
            δ * osc - loss * S * R ≤ w₂ x / dirichletBoundaryDistanceProxy x) := by
  obtain ⟨H, hH1, hHarnack⟩ := exists_uniform_smooth_cofactor_source_average_harnack hn hc hK
  have hH : 0 < H := lt_of_lt_of_le zero_lt_one hH1
  let τ : ℝ := dirichletBoundaryBarrierScale n c K
  let δ : ℝ := min (1 / 2) (dirichletBoundaryGain H τ)
  let loss : ℝ := dirichletBoundaryLoss n c τ
  have hτ : 0 < τ := dirichletBoundaryBarrierScale_pos n hc hK
  have hδ : 0 < δ := lt_min (by norm_num) (dirichletBoundaryGain_pos hH hτ)
  have hδ1 : δ < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hLoss : 0 ≤ loss := dirichletBoundaryLoss_nonneg n hc hτ.le
  refine ⟨δ, loss, hδ, hδ1, hLoss, ?_⟩
  intro u hu huP hNorm hEll w₁ w₂ hw₁ hw₂ S osc hS hosc hL₁ hL₂ p₀ hp₀ R hR hR1 hPos₁ hPos₂ hSum
  let z : KEBall.E n := dirichletTangentBallCenter p₀ R
  let μ : Measure (KEBall.E n) := dirichletBallProbability z ((R / 2) / 4)
  let a : ℝ := S / (4 * n * c)
  let m : ℝ := max 0 (osc * R / (8 * H) - a * R ^ 2 / 4)
  have ha : 0 ≤ a := div_nonneg hS (by positivity)
  have hm : 0 ≤ m := le_max_left _ _
  have hM : osc * R / (8 * H) - a * R ^ 2 / 4 ≤ m := le_max_right _ _
  have hLarge : closedBall z (R / 2) ⊆ unitBall n :=
    dirichlet_corkscrew_closedBall_subset hp₀ hR hR1
  have hCap : closedBall z (R / 2) ⊆ ball p₀ (4 * R) :=
    (closedBall_subset_closedBall (by linarith : R / 2 ≤ R)).trans
      (dirichlet_tangent_closedBall_subset_cap hp₀ hR (by rw [dist_self]; positivity))
  have hSmall : ball z ((R / 2) / 4) ⊆ closedBall z (R / 2) :=
    ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith))
  have hSmoothC (w : KEBall.E n → ℝ) (hw : SmoothNear (closedUnitBall n) w) :
      ContinuousOn w (closedUnitBall n) := by
    intro x hx
    exact (hw.contDiffAt hx).continuousAt.continuousWithinAt
  have hSmooth2 (w : KEBall.E n → ℝ) (hw : SmoothNear (closedUnitBall n) w) :
      ContDiffOn ℝ 2 w (unitBall n) := by
    obtain ⟨U, hU, hSub, hwU⟩ := hw
    exact (hwU.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).mono
      (ball_subset_closedBall.trans hSub)
  have hInt (w : KEBall.E n → ℝ) (hw : SmoothNear (closedUnitBall n) w) : Integrable w μ := by
    apply (integrable_dirichletBallProbability_iff (by positivity)).mpr
    exact (((hSmoothC w hw).mono (hLarge.trans ball_subset_closedBall)).integrableOn_compact
      (isCompact_closedBall z (R / 2))).mono_set hSmall
  have hOuter₁ (x : KEBall.E n) (hx : x ∈ ball z (R / 2)) : 0 ≤ w₁ x :=
    hPos₁ x (ball_subset_closedBall (hLarge (ball_subset_closedBall hx))) (hCap (ball_subset_closedBall hx))
  have hOuter₂ (x : KEBall.E n) (hx : x ∈ ball z (R / 2)) : 0 ≤ w₂ x :=
    hPos₂ x (ball_subset_closedBall (hLarge (ball_subset_closedBall hx))) (hCap (ball_subset_closedBall hx))
  have hH₁ (y : KEBall.E n) (hy : y ∈ ball z ((R / 2) / 4)) :
      (∫ x, w₁ x ∂μ) ≤ H * (w₁ y + a * R ^ 2 / 4) := by
    have h := hHarnack u hu huP hNorm hEll w₁ hw₁ S hS hL₁ z (R / 2)
      (by positivity) hLarge hOuter₁ y hy
    have he : S / (4 * n * c) * (R / 2) ^ 2 = a * R ^ 2 / 4 := by dsimp [a]; ring
    rw [he] at h
    exact h
  have hH₂ (y : KEBall.E n) (hy : y ∈ ball z ((R / 2) / 4)) :
      (∫ x, w₂ x ∂μ) ≤ H * (w₂ y + a * R ^ 2 / 4) := by
    have h := hHarnack u hu huP hNorm hEll w₂ hw₂ S hS hL₂ z (R / 2)
      (by positivity) hLarge hOuter₂ y hy
    have he : S / (4 * n * c) * (R / 2) ^ 2 = a * R ^ 2 / 4 := by dsimp [a]; ring
    rw [he] at h
    exact h
  have hSumAe : ∀ᵐ x ∂μ, osc * R / 4 ≤ w₁ x + w₂ x := by
    apply ae_dirichletBallProbability_iff.mpr
    filter_upwards [ae_restrict_mem (μ := (volume : Measure (KEBall.E n))) measurableSet_ball] with x hx
    rw [hSum x (ball_subset_closedBall (hLarge (hSmall hx))) (hCap (hSmall hx))]
    have hρ := dirichletBoundaryDistanceProxy_lower_on_corkscrew_quarter hp₀ hR hR1
      (show x ∈ closedBall (dirichletTangentBallCenter p₀ R) (R / 8) from by
        simpa only [show (R / 2) / 4 = R / 8 by ring] using ball_subset_closedBall hx)
    nlinarith only [mul_le_mul_of_nonneg_left hρ hosc]
  haveI : IsProbabilityMeasure μ := isProbabilityMeasure_dirichletBallProbability z (by positivity)
  have hTwo := dirichlet_two_defects_common_lower (hInt w₁ hw₁) (hInt w₂ hw₂) hH hSumAe
    (fun y hy => hOuter₁ y (ball_subset_ball (by linarith) hy))
    (fun y hy => hOuter₂ y (ball_subset_ball (by linarith) hy)) hH₁ hH₂
  have hSym (x : KEBall.E n) (hx : x ∈ unitBall n) :
      (dirichletCofactorOperator u x).toLinearMap.IsSymmetric := by
    rw [← dirichletCofactorOfMatrix_complexHessian]
    intro v w
    exact (dirichletCofactorOfMatrix_symmetric (huP x hx).isHermitian v w).trans (real_inner_comm _ _)
  have hGain := dirichlet_boundary_gain_from_inner_lower (by omega : 0 < n) hc hH hτ hR hM
  have hδGain : δ * osc - loss * S * R ≤
      dirichletBoundaryGain H τ * osc - dirichletBoundaryLoss n c τ * S * R := by
    have h := mul_le_mul_of_nonneg_right (min_le_right (1 / 2) (dirichletBoundaryGain H τ)) hosc
    dsimp [δ, loss]
    linarith only [h]
  have hProp (w : KEBall.E n → ℝ) (hw : SmoothNear (closedUnitBall n) w)
      (hL : ∀ x ∈ unitBall n,
        dirichletBilinearContraction e[n] (dirichletCofactorOperator u x) (realHessian w x) ≤ S)
      (hPos : ∀ x ∈ closedUnitBall n, x ∈ ball p₀ (4 * R) → 0 ≤ w x)
      (hInner : ∀ x ∈ ball z ((R / 2) / 4), m ≤ w x) :
      ∀ x ∈ unitBall n, x ∈ ball p₀ (R / 64) →
        δ * osc - loss * S * R ≤ w x / dirichletBoundaryDistanceProxy x := by
    have hBound := dirichlet_boundary_quotient_lower_on_cap e[n] hp₀ hR hR1 hc
      (by positivity : 0 < τ / R ^ 2) hm ha
      (dirichletBoundaryBarrierScale_elliptic hc hR)
      (le_of_eq (dirichlet_source_coefficient_scale (by omega : 0 < n) hc).symm)
      hSym hNorm hEll (hSmoothC w hw) (hSmooth2 w hw) hL hPos hInner
    intro x hx hxCap
    exact hδGain.trans (hGain.trans (hBound x hx hxCap))
  rcases hTwo with h₁ | h₂
  · exact Or.inl (hProp w₁ hw₁ hL₁ hPos₁ h₁)
  · exact Or.inr (hProp w₂ hw₂ hL₂ hPos₂ h₂)

end KEBall
