import KEBall.BedfordTaylorMixedPositivity
import KEBall.BedfordTaylorMixedLocality

/-!
# The second mixed measure in a tuple of complex directions

Successive smooth approximation gives positivity of the diagonal
coefficient. This coefficient is represented by a positive Radon measure.
-/

set_option autoImplicit false

open Filter MeasureTheory Set TopologicalSpace
open scoped Distributions Topology

namespace KEBall.BedfordTaylor

open PshLines
open PshLines.FirstPass (ComplexModel)
open PshLines.FirstPass.MongeAmpere (IsLocallyBoundedPshOn RelativelyCompactIn)
open PshLines.Regularization.HolomorphicPullback (exists_decreasingMollifierApproximation)

variable {n : ℕ} {Ω : Opens (ComplexModel n)} {u p : ComplexModel n → ℝ}

set_option maxHeartbeats 600000 in
theorem positive_secondMixedHessian (hu : IsLocallyBoundedPshOn Ω u)
    (hp : IsLocallyBoundedPshOn Ω p) (v : Fin 2 → ComplexModel n) :
    PositiveDistribution (Distribution.mapCLM Complex.reCLM (secondMixedHessian hu hp v v)) := by
  intro φ hφ
  obtain ⟨V, hVo, hφV, hVΩ, hVc⟩ :=
    exists_open_between_and_isCompact_closure φ.hasCompactSupport Ω.isOpen φ.tsupport_subset
  let W : Opens (ComplexModel n) := ⟨V, hVo⟩
  have hrel : RelativelyCompactIn W Ω := ⟨hVc, hVΩ⟩
  have hWΩ : W ≤ Ω := subset_closure.trans hVΩ
  let ψ : 𝓓(W, ℝ) := ⟨φ, φ.contDiff, φ.hasCompactSupport, hφV⟩
  have hψ : ∀ x, 0 ≤ ψ x := hφ
  have hφeq : extendTest hWΩ ψ = φ := TestFunction.ext fun _ => rfl
  let huW := IsLocallyBoundedPshOn.mono hu hWΩ
  let hpW := IsLocallyBoundedPshOn.mono hp hWΩ
  rw [Distribution.mapCLM_apply, Complex.reCLM_apply, ← hφeq,
    secondMixedHessian_extendTest hu hp hWΩ]
  change 0 ≤ (secondMixedHessian huW hpW v v ψ).re
  obtain ⟨uApprox, huApprox⟩ := exists_decreasingMollifierApproximation hu hrel
  obtain ⟨pApprox, hpApprox⟩ := exists_decreasingMollifierApproximation hp hrel
  let huL := fun j => isLocallyBoundedPshOn_of_isSmoothPshOn (huApprox.1 j)
  let hpL := fun j => isLocallyBoundedPshOn_of_isSmoothPshOn (hpApprox.1 j)
  have hpos (j : ℕ) : 0 ≤ (secondMixedHessian (huL j) hpW v v ψ).re := by
    apply ge_of_tendsto ((Complex.continuous_re.tendsto _).comp
      (tendsto_secondMixedHessian_potential_test (huApprox.1 j) hpW hpL
        hpApprox.2.1 hpApprox.2.2 v v ψ))
    exact Eventually.of_forall fun m =>
      positive_secondMixedHessian_of_isSmoothPshOn (huApprox.1 j) (hpApprox.1 m) v ψ hψ
  exact ge_of_tendsto ((Complex.continuous_re.tendsto _).comp
    (tendsto_secondMixedHessian_weight_test huW hpW huL huApprox.2.1 huApprox.2.2 v v ψ))
      (Eventually.of_forall hpos)

theorem existsUnique_secondMixedMeasure (hu : IsLocallyBoundedPshOn Ω u)
    (hp : IsLocallyBoundedPshOn Ω p) (v : Fin 2 → ComplexModel n) :
    ∃! μ : Measure Ω, μ.Regular ∧
      ∀ φ : 𝓓(Ω, ℝ), (∫ x : Ω, φ x ∂μ) = (secondMixedHessian hu hp v v φ).re := by
  obtain ⟨μ, hμ, _, hpair⟩ := (positive_secondMixedHessian hu hp v).exists_regular_measure
  refine ⟨μ, ⟨hμ, hpair⟩, ?_⟩
  rintro ν ⟨hν, htest⟩
  let : μ.Regular := hμ
  let : ν.Regular := hν
  exact measure_eq_of_smooth_test fun φ => (htest φ).trans (hpair φ).symm

/-- The positive measure representing the diagonal coefficient of the
second mixed Hessian, before the `ddᶜ` normalization. -/
noncomputable def secondMixedMeasure (hu : IsLocallyBoundedPshOn Ω u)
    (hp : IsLocallyBoundedPshOn Ω p) (v : Fin 2 → ComplexModel n) : Measure Ω :=
  (existsUnique_secondMixedMeasure hu hp v).exists.choose

theorem secondMixedMeasure_regular (hu : IsLocallyBoundedPshOn Ω u)
    (hp : IsLocallyBoundedPshOn Ω p) (v : Fin 2 → ComplexModel n) :
    (secondMixedMeasure hu hp v).Regular :=
  (existsUnique_secondMixedMeasure hu hp v).exists.choose_spec.1

theorem integral_secondMixedMeasure (hu : IsLocallyBoundedPshOn Ω u)
    (hp : IsLocallyBoundedPshOn Ω p) (v : Fin 2 → ComplexModel n) (φ : 𝓓(Ω, ℝ)) :
    (∫ x : Ω, φ x ∂secondMixedMeasure hu hp v) = (secondMixedHessian hu hp v v φ).re :=
  (existsUnique_secondMixedMeasure hu hp v).exists.choose_spec.2 φ

#print axioms positive_secondMixedHessian
#print axioms integral_secondMixedMeasure

end KEBall.BedfordTaylor
