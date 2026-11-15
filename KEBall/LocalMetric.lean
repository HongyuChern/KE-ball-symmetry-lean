import KEBall.HermitianRealification
import PoincareLib.Geometry.Riemannian.Metric.LocalExtension

/-!
# A constructed Levi-Civita realization of the actual complex Hessian

Only local positivity of the complex Hessian is used. The existing Poincare
construction extends the real bilinear metric by a cutoff and constructs its
torsion-free, compatible connection. There is no assumed Bochner normalization,
Ricci identification, or global positivity of the original potential.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff Manifold ComplexOrder

namespace KEBall

/-- Actual matrix-to-metric realization near any point of an open set. -/
theorem exists_local_hermitian_metric {n : ℕ} {U : Set (E n)} (hU : IsOpen U)
    {p : E n} (hp : p ∈ U) {A : E n → Matrix (Fin n) (Fin n) ℂ}
    (hA : ∀ i j, ContDiffOn ℝ ∞ (fun x => A x i j) U)
    (hpos : ∀ x ∈ U, (A x).PosDef) :
    ∃ (g : PoincareMT.RiemannianMetric (2 * n) (E n))
      (_D : PoincareMT.LeviCivitaData g) (V : Set (E n)),
      IsOpen V ∧ p ∈ V ∧ V ⊆ U ∧
        ∀ x ∈ V, g.euclideanCoefficients x = hermitianRealification (A x) := by
  exact PoincareMT.RiemannianMetric.exists_local_realization hU hp
    (fun x => hermitianRealification (A x))
    (hermitianRealification_contDiffOn hA)
    (fun x hx v w => hermitianRealification_symm (hpos x hx).isHermitian v w)
    (fun x hx v hv => hermitianRealification_pos (hpos x hx) v hv)

/-- This theorem constructs the metric and connection from an actual potential
satisfying the original equation, without adding any geometric bridge fields. -/
theorem IsSolution.exists_local_metric {n : ℕ} {μ : ℝ} {u : E n → ℝ}
    (hu : IsSolution n μ u) {p : E n} (hp : p ∈ unitBall n) :
    ∃ (g : PoincareMT.RiemannianMetric (2 * n) (E n))
      (_D : PoincareMT.LeviCivitaData g) (V : Set (E n)),
      IsOpen V ∧ p ∈ V ∧ V ⊆ unitBall n ∧
        ∀ x ∈ V, ∀ v w : E n, g.inner x v w = realMetricForm u x v w := by
  have huB : ContDiffOn ℝ ∞ u (unitBall n) := by
    intro x hx
    exact (hu.2.1.contDiffAt (Metric.ball_subset_closedBall hx)).contDiffWithinAt
  obtain ⟨g, D, V, hV, hpV, hVU, heq⟩ :=
    exists_local_hermitian_metric (n := n) Metric.isOpen_ball hp
      (complexHessian_contDiffOn Metric.isOpen_ball huB) hu.2.2.1
  refine ⟨g, D, V, hV, hpV, hVU, ?_⟩
  intro x hx v w
  change g.euclideanCoefficients x v w = realMetricForm u x v w
  rw [heq x hx, realMetricForm_eq]

end KEBall
