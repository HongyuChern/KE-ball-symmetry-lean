import Drafts.KEBall.FixedMetricHessian
import Drafts.KEBall.DZeroTwoForm
import Drafts.KEBall.NormalizedMass
import Drafts.Validation.Stage09Contract

/-!
Stage10 SOURCE_DRAFT_UNCOMPILED.
The same local metric realizes the fixed-background Hessian, gradient, and
degree-two D0 form. The inherited seven frozen specifications stay intact.
This consumer does not assert the n-fold wedge / determinant-density bridge.
-/
set_option autoImplicit false
open Set
open scoped ContDiff

namespace KEBall.Stage10Contract

/-- Geometric identities in one actual local Riemannian realization. -/
theorem local_geometry {n : ℕ} (hn : 2 ≤ n) {μ : ℝ} {u : E n → ℝ}
    (hu : IsSolution n μ u) {p : E n} (hp : p ∈ unitBall n) :
    ∃ (t₀ : ℝ) (g : PoincareMT.RiemannianMetric (2 * n) (E n))
      (D : PoincareMT.LeviCivitaData g) (U : Set (E n)),
      0 < t₀ ∧ t₀ < (n + 1 : ℝ) ∧ boundaryPolynomial n t₀ = μ ∧
      IsOpen U ∧ p ∈ U ∧ U ⊆ unitBall n ∧
      (∀ x ∈ U, ∀ v w : E n, g.inner x v w = realMetricForm u x v w) ∧
      (∀ x ∈ U, ∀ i j : Fin n, complexify20 (D.hessian (expWeight u) x) i j = 0) ∧
      (∀ x ∈ U, D.gradient (expWeight u) x = (-1 / ((n + 1 : ℝ) - t₀)) • x) ∧
      (∀ x ∈ U, ∀ v w : E n,
        d0BilinearForm u x v w = (2 * Real.pi)⁻¹ * g.inner x (J v) w) ∧
      (∀ x ∈ U, ∀ v w : E n,
        d0BilinearForm u x v w =
          fderiv ℝ (fun y => dcZeroForm u y w) x v -
            fderiv ℝ (fun y => dcZeroForm u y v) x w) := by
  obtain ⟨t₀, g, D, U, ht, htk, hF, hU, hpU, hUB, hg, hH, hV⟩ :=
    hu.exists_local_exponential_geometric_rigidity hn hp
  refine ⟨t₀, g, D, U, ht, htk, hF, hU, hpU, hUB, hg, hH, hV, ?_, ?_⟩
  · intro x hx v w
    exact d0BilinearForm_eq_metric (hg x hx) v w
  · intro x hx v w
    exact d0BilinearForm_eq_exteriorDerivative
      (hu.2.1.contDiffAt (Metric.ball_subset_closedBall (hUB hx))) v w

theorem normalized_constants {n : ℕ} (hn : 2 ≤ n) {γ : ℝ} {φ : E n → ℝ}
    (hφ : IsNormalizedSolution n γ φ) :
    γ < (n + 1 : ℝ) ∧
      normalizingIntegral γ φ = (1 - γ / (n + 1 : ℝ))⁻¹ ∧
      (∀ x ∈ unitBall n, (complexHessian φ x).det =
        (((1 - γ / (n + 1 : ℝ)) * Real.exp (-γ * φ x) : ℝ) : ℂ)) :=
  ⟨(hφ.boundaryPolynomial_parameter hn).1, hφ.normalizingIntegral_eq hn,
    fun _ hx => hφ.det_eq_explicit_coefficient hn hx⟩

theorem all_frozen_specifications :
    ClassificationStatement ∧ RadialExistenceStatement ∧ SolutionCountsStatement ∧
    BoundaryIdentitiesStatement ∧ LowerSlopeStatement ∧ LogarithmicFluxStatement ∧
    NormalizedClassificationStatement := Stage09Contract.all_frozen_specifications

#print axioms local_geometry
#print axioms normalized_constants
#print axioms all_frozen_specifications

end KEBall.Stage10Contract
