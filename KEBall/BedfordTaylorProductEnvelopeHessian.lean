import KEBall.BedfordTaylorProductEnvelopeApproximation
import KEBall.BedfordTaylorHessianModelLimit
import KEBall.SecondOrderExpansion
import Mathlib.Analysis.Calculus.Rademacher

/-!
# The almost-everywhere Hessian limit of the product-ball regularization
-/

set_option autoImplicit false

open Filter MeasureTheory Metric Set TopologicalSpace
open scoped ContDiff Topology

namespace KEBall.BedfordTaylor

open PshLines (integrable_indicator_of_locallyIntegrableOn_isCompact)
open PshLines.FirstPass (ComplexModel)
open PshLines.FirstPass.MongeAmpere
  (IsLocallyBoundedPshOn IsDecreasingApproximation RelativelyCompactIn
    locallyIntegrableOn_of_plurisubharmonicOn_real)

local notation "modelHessian" => PshLines.FirstPass.MongeAmpere.complexHessian

/-- The quadratic polynomial with the value and the first two derivatives
of the potential at its center. -/
noncomputable def potentialTaylorModel {n : ℕ} (u : ComplexModel n → ℝ) (x : ComplexModel n) :
    ComplexModel n → ℝ :=
  quadraticTaylorModel x (u x) (fderiv ℝ u x) (fderiv ℝ (fderiv ℝ u) x)

set_option maxHeartbeats 800000 in
/-- On each interior neighborhood, the very same radial sequence used for
the Bedford–Taylor limit converges in its complex Hessians almost everywhere. -/
theorem exists_ae_hessianApproximation_productEnvelope {n m : ℕ} {R : ℝ}
    {u v : ComplexModel (n + m) → ℝ} (hu : ContDiff ℝ 2 u)
    (hu₀ : ∀ x ∈ ball 0 R, u x ≤ 0) (huBoundary : ∀ x ∈ sphere 0 R, u x = 0)
    (hv : IsLocallyBoundedPshOn (complexProductBall n m) v)
    (hvf : ∀ x ∈ complexProductBall n m, v x ≤ (ball (0 : ComplexModel (n + m)) R).indicator u x)
    (hgreatest : ∀ w : ComplexModel (n + m) → ℝ, IsLocallyBoundedPshOn (complexProductBall n m) w →
      (∀ x ∈ complexProductBall n m, w x ≤ (ball (0 : ComplexModel (n + m)) R).indicator u x) →
        ∀ x ∈ complexProductBall n m, w x ≤ v x)
    {a : ComplexModel (n + m)} (ha : a ∈ complexProductBall n m) :
    ∃ W : Opens (ComplexModel (n + m)), a ∈ W ∧ RelativelyCompactIn W (complexProductBall n m) ∧
      ∃ q : ℕ → ComplexModel (n + m) → ℝ, IsDecreasingApproximation W v q ∧
      (∃ C : ℝ, 0 ≤ C ∧ ∀ j x, x ∈ W → ‖fderiv ℝ (fderiv ℝ (q j)) x‖ ≤ C) ∧
      ∀ᵐ x ∂volume.restrict (W : Set (ComplexModel (n + m))),
        Tendsto (fun j => modelHessian (q j) x) atTop (𝓝 (modelHessian (potentialTaylorModel v x) x)) ∧
        ∀ ε : ℝ, 0 < ε → ∀ᶠ h in 𝓝 (0 : ComplexModel (n + m)),
          |v (x + h) - potentialTaylorModel v x (x + h)| ≤ ε * ‖h‖ ^ 2 := by
  obtain ⟨W, haW, hrel, hW, q, hq, ⟨C, hC, hess⟩, ρ, hρ, K, hK, hKP, hWK, hformula⟩ :=
    exists_boundedHessianApproximation_productEnvelope hu hu₀ huBoundary hv hvf hgreatest ha
  have hWle : W ≤ complexProductBall n m := subset_closure.trans hrel.2
  obtain ⟨hdiff, hLip⟩ := differentiableOn_lipschitz_fderiv_of_boundedHessian
    (IsLocallyBoundedPshOn.mono hv hWle) hW hq hC hess
  have hdiff' (x : ComplexModel (n + m)) (hx : x ∈ W) : DifferentiableAt ℝ v x :=
    (hdiff x hx).differentiableAt (W.isOpen.mem_nhds hx)
  have hg : LocallyIntegrable (K.indicator v) volume :=
    (integrable_indicator_of_locallyIntegrableOn_isCompact
      (locallyIntegrableOn_of_plurisubharmonicOn_real hv.1) hK hKP).locallyIntegrable
  refine ⟨W, haW, hrel, q, hq, ⟨C, hC, hess⟩, ?_⟩
  filter_upwards [hLip.ae_differentiableWithinAt (μ := volume) W.isOpen.measurableSet,
    ae_restrict_mem W.isOpen.measurableSet] with x hgrad hx
  have hD := (hgrad.differentiableAt (W.isOpen.mem_nhds hx)).hasFDerivAt
  have ht (ε : ℝ) (hε : 0 < ε) : ∀ᶠ h in 𝓝 (0 : ComplexModel (n + m)),
      |v (x + h) - v x - fderiv ℝ v x h - fderiv ℝ (fderiv ℝ v) x h h / 2| ≤ ε * ‖h‖ ^ 2 := by
    simpa only [Real.norm_eq_abs] using
      eventually_quadratic_remainder_of_hasFDerivAt_fderiv W.isOpen hx hdiff' hD hε
  have hShift : ∀ᶠ h : ComplexModel (n + m) in 𝓝 0, x + h ∈ K := by
    have hc : Continuous (fun h : ComplexModel (n + m) => x + h) := continuous_const.add continuous_id
    have hx' : x + (0 : ComplexModel (n + m)) ∈ interior K := by rw [add_zero]; exact hWK hx
    have hnear : ∀ᶠ h : ComplexModel (n + m) in 𝓝 0, x + h ∈ interior K :=
      hc.continuousAt (x := 0) (isOpen_interior.mem_nhds hx')
    exact hnear.mono fun _ h => interior_subset h
  have hgrem (ε : ℝ) (hε : 0 < ε) : ∀ᶠ h in 𝓝 (0 : ComplexModel (n + m)),
      |K.indicator v (x + h) - v x - fderiv ℝ v x h - fderiv ℝ (fderiv ℝ v) x h h / 2| ≤ ε * ‖h‖ ^ 2 := by
    filter_upwards [ht ε hε, hShift] with h hsmall hh
    rwa [indicator_of_mem hh]
  refine ⟨?_, ?_⟩
  · simpa only [hformula, potentialTaylorModel] using
      tendsto_complexHessian_radialPairing_of_quadratic_expansion ρ hρ hg x (v x)
        (fderiv ℝ v x) (fderiv ℝ (fderiv ℝ v) x) hgrem
  · intro ε hε
    filter_upwards [ht ε hε] with h hh
    have he : v (x + h) - potentialTaylorModel v x (x + h) =
        v (x + h) - v x - fderiv ℝ v x h - fderiv ℝ (fderiv ℝ v) x h h / 2 := by
      simp only [potentialTaylorModel, quadraticTaylorModel, add_sub_cancel_left]
      ring
    rwa [he]

end KEBall.BedfordTaylor
