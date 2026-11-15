import Drafts.KEBall.ExponentialRigidityPrelude

/-!
Stage08 SOURCE_DRAFT_UNCOMPILED.
An explicit consumer of the original IsSolution assumptions. The integrated
zero, constant sphere slope, rank-one Hessian and fixed-metric exponential
Hessian are conclusions, not premises. The vector identity remains a sphere
identity; neither interior holomorphic uniqueness nor classification is
claimed by this contract. This file is not a kernel-verification receipt.
-/
set_option autoImplicit false
open MeasureTheory Set
open scoped ContDiff

namespace KEBall.Stage08Contract

theorem boundary_and_tensor_rigidity {n : ℕ} (hn : 2 ≤ n)
    {μ : ℝ} {u : E n → ℝ} (hu : IsSolution n μ u) :
    (((∫ x in unitBall n, complexLaplacian u (auxiliaryW u) x *
        (complexHessian u x).det.re ∂volume0 n) = 0) ∧
      ((∫ x : Sphere n,
        (boundaryPolynomial n (boundarySlope u x.1) - μ) / boundarySlope u x.1
          ∂sphere0 n) = 0) ∧
      ((∫ x : Sphere n, horizontalFluxWeight n (boundarySlope u x.1) *
        ‖horizontalGradient (boundarySlope u) x.1‖ ^ 2 ∂sphere0 n) = 0)) ∧
    (∃ t₀ : ℝ, 0 < t₀ ∧ t₀ < (n + 1 : ℝ) ∧ boundaryPolynomial n t₀ = μ ∧
      (∀ x ∈ unitSphere n, boundarySlope u x = t₀) ∧
      (∀ x ∈ unitSphere n, ∀ i : Fin n,
        exponentialGradient u x i = (-1 / ((n + 1 : ℝ) - t₀) : ℝ) * complexCoord x i)) ∧
    (∀ x ∈ unitBall n, ∀ i j : Fin n,
      covariantHessian20 u x i j = (n + 1 : ℂ)⁻¹ *
        partialZ i (fun y => (u y : ℂ)) x * partialZ j (fun y => (u y : ℂ)) x) ∧
    (∀ x ∈ unitBall n, ∀ i j : Fin n,
      metricCovariantHessian20 u (expWeight u) x i j = 0) ∧
    (∀ x ∈ unitSphere n, horizontalGradient (boundarySlope u) x = 0) ∧
    (∀ i : Fin n, ContDiffOn ℝ ∞ (fun x => exponentialGradient u x i)
      (closedUnitBall n)) := by
  refine ⟨hu.logarithmicFlux_all_integrals_zero hn,
    hu.exists_exponentialGradient_boundary_data hn, ?_, ?_, ?_, ?_⟩
  · intro x hx i j
    exact hu.covariantHessian20_eq_rank_one hn hx i j
  · intro x hx i j
    exact hu.metricCovariantHessian20_expWeight_eq_zero hn hx i j
  · intro x hx
    exact hu.horizontalGradient_boundarySlope_eq_zero hn hx
  · intro i
    exact hu.exponentialGradient_contDiffOn_closedBall i

#print axioms boundary_and_tensor_rigidity

end KEBall.Stage08Contract
