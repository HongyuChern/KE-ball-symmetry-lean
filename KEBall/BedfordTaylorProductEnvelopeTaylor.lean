import KEBall.BedfordTaylorProductEnvelopeApproximation
import KEBall.SecondOrderExpansion
import Mathlib.Analysis.Calculus.Rademacher

/-!
# Almost-everywhere quadratic expansion of a product-ball envelope
-/

set_option autoImplicit false

open Filter MeasureTheory Metric Set TopologicalSpace
open scoped ContDiff Topology

namespace KEBall.BedfordTaylor

open PshLines.FirstPass (ComplexModel)
open PshLines.FirstPass.MongeAmpere (IsLocallyBoundedPshOn RelativelyCompactIn)

/-- The envelope of a zero-extended smooth potential admits a genuine
second-order Taylor expansion almost everywhere in the interior. -/
theorem ae_quadratic_remainder_of_productEnvelope {n m : ℕ} {R : ℝ}
    {u v : ComplexModel (n + m) → ℝ} (hu : ContDiff ℝ 2 u)
    (hu₀ : ∀ x ∈ ball 0 R, u x ≤ 0) (huBoundary : ∀ x ∈ sphere 0 R, u x = 0)
    (hv : IsLocallyBoundedPshOn (complexProductBall n m) v)
    (hvf : ∀ x ∈ complexProductBall n m, v x ≤ (ball (0 : ComplexModel (n + m)) R).indicator u x)
    (hgreatest : ∀ w : ComplexModel (n + m) → ℝ, IsLocallyBoundedPshOn (complexProductBall n m) w →
      (∀ x ∈ complexProductBall n m, w x ≤ (ball (0 : ComplexModel (n + m)) R).indicator u x) →
        ∀ x ∈ complexProductBall n m, w x ≤ v x)
    {a : ComplexModel (n + m)} (ha : a ∈ complexProductBall n m) :
    ∃ W : Opens (ComplexModel (n + m)), a ∈ W ∧ RelativelyCompactIn W (complexProductBall n m) ∧
      ∀ᵐ x ∂volume.restrict (W : Set (ComplexModel (n + m))),
        HasFDerivAt (fderiv ℝ v) (fderiv ℝ (fderiv ℝ v) x) x ∧
        ∀ ε : ℝ, 0 < ε → ∀ᶠ h in 𝓝 (0 : ComplexModel (n + m)),
          ‖v (x + h) - v x - fderiv ℝ v x h - fderiv ℝ (fderiv ℝ v) x h h / 2‖ ≤ ε * ‖h‖ ^ 2 := by
  obtain ⟨W, haW, hrel, hdiff, C, hLip⟩ := exists_lipschitz_fderiv_productEnvelope hu hu₀ huBoundary hv hvf hgreatest ha
  refine ⟨W, haW, hrel, ?_⟩
  have hdiff' (x : ComplexModel (n + m)) (hx : x ∈ W) : DifferentiableAt ℝ v x :=
    (hdiff x hx).differentiableAt (W.isOpen.mem_nhds hx)
  filter_upwards [hLip.ae_differentiableWithinAt (μ := volume) W.isOpen.measurableSet,
    ae_restrict_mem W.isOpen.measurableSet] with x hgrad hx
  have hD := (hgrad.differentiableAt (W.isOpen.mem_nhds hx)).hasFDerivAt
  exact ⟨hD, fun ε hε => eventually_quadratic_remainder_of_hasFDerivAt_fderiv W.isOpen hx hdiff' hD hε⟩

end KEBall.BedfordTaylor
