import Drafts.KEBall.AuxiliaryPLaplacian
import Drafts.KEBall.AuxiliaryWIdentity

/-!
Explicit original-hypothesis consumers of the Stage06 source chain.
SOURCE_DRAFT_UNCOMPILED. This same-author contract is not a Comparator
challenge or a proof of the complete LogarithmicFluxStatement.
-/

set_option autoImplicit false
open scoped BigOperators

namespace KEBall.Stage06Contract

theorem q_differential_from_original_hypotheses {n : ℕ} {μ : ℝ}
    {u : E n → ℝ} (hu : IsSolution n μ u) {x : E n}
    (hx : x ∈ unitBall n) (j : Fin n) :
    partialZ j (fun y => (gradientNormSq u y : ℂ)) x =
      partialZ j (fun y => (u y : ℂ)) x +
        ∑ i : Fin n, ∑ l : Fin n, inverseCoefficient u x i l *
          covariantHessian20 u x j i * partialBar l (fun y => (u y : ℂ)) x :=
  hu.partialZ_gradientNormSq hx j

theorem p_differential_from_original_hypotheses {n : ℕ} {μ : ℝ}
    {u : E n → ℝ} (hu : IsSolution n μ u) {x : E n}
    (hx : x ∈ unitBall n) (j : Fin n) :
    partialZ j (fun y => (auxiliaryP u y : ℂ)) x =
      (expWeight u x / (n + 1 : ℝ) : ℂ) *
        hermitianTensorContract (inverseCoefficient u x) (auxiliaryDefectTensor u x)
          (fun i => partialZ i (fun y => (u y : ℂ)) x) j :=
  hu.partialZ_auxiliaryP_defect hx j

theorem p_laplacian_from_original_hypotheses {n : ℕ} {μ : ℝ}
    {u : E n → ℝ} (hu : IsSolution n μ u) {x : E n}
    (hx : x ∈ unitBall n) :
    complexLaplacian u (auxiliaryP u) x =
      expWeight u x / (n + 1 : ℝ) *
        complexTensorNormSq u x (auxiliaryDefectTensor u x) :=
  hu.auxiliaryP_laplacian hx

theorem kato_from_original_hypotheses {n : ℕ} {μ : ℝ}
    {u : E n → ℝ} (hu : IsSolution n μ u) {x : E n}
    (hx : x ∈ unitBall n) :
    metricGradientNormSq u (auxiliaryP u) x ≤
      (auxiliaryP u x - expWeight u x) * complexLaplacian u (auxiliaryP u) x :=
  hu.auxiliaryP_kato hx

theorem w_chain_from_original_hypotheses {n : ℕ} (hn : 2 ≤ n) {μ : ℝ}
    {u : E n → ℝ} (hu : IsSolution n μ u) {x : E n}
    (hx : x ∈ closedUnitBall n) :
    complexLaplacian u (auxiliaryW u) x =
      complexLaplacian u (auxiliaryP u) x / (auxiliaryP u x - 1) -
        metricGradientNormSq u (auxiliaryP u) x / (auxiliaryP u x - 1) ^ 2 :=
  hu.complexLaplacian_auxiliaryW_closedBall hn hx

/-- Exactly the first two conjuncts, not the full flux/equality specification. -/
theorem logarithmic_flux_local_components {n : ℕ} (hn : 2 ≤ n) {μ : ℝ}
    {u : E n → ℝ} (hu : IsSolution n μ u) :
    (∀ x ∈ closedUnitBall n, 1 < auxiliaryP u x) ∧
      (∀ x ∈ unitBall n, 0 ≤ complexLaplacian u (auxiliaryW u) x) := by
  exact ⟨fun _ hx => hu.auxiliaryP_gt_one_closedBall hn hx,
    fun _ hx => hu.auxiliaryW_laplacian_nonneg hn hx⟩

theorem neighbourhood_regularity_and_gap {n : ℕ} (hn : 2 ≤ n) {μ : ℝ}
    {u : E n → ℝ} (hu : IsSolution n μ u) :
    SmoothNear (closedUnitBall n) (gradientNormSq u) ∧
      SmoothNear (closedUnitBall n) (auxiliaryP u) ∧
      SmoothNear (closedUnitBall n) (auxiliaryW u) ∧
      ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ closedUnitBall n, δ ≤ auxiliaryP u x - 1 := by
  exact ⟨hu.gradientNormSq_smoothNear, hu.auxiliaryP_smoothNear,
    hu.auxiliaryW_smoothNear hn, hu.auxiliaryP_uniform_gap hn⟩

end KEBall.Stage06Contract
