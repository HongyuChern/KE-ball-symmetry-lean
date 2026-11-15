import KEBall.BedfordTaylorSmoothCoefficients

/-!
# Upper bound in the joint weighted Levi limit

On a nonnegative test, decreasing smooth weights can be bounded by
one fixed approximant. First-degree weak convergence then controls
the upper limit even when the limiting weight is discontinuous.
-/

set_option autoImplicit false

open Filter MeasureTheory TopologicalSpace
open scoped Distributions Topology

namespace KEBall.BedfordTaylor

open PshLines
open PshLines.FirstPass (ComplexModel)
open PshLines.FirstPass.MongeAmpere (IsLocallyBoundedPshOn IsSmoothPshOn)

variable {n : ℕ} {Ω : Opens (ComplexModel n)} {u p : ComplexModel n → ℝ}
  {u' p' : ℕ → ComplexModel n → ℝ}

theorem eventually_weightedLeviDistribution_lt_add
    (hu : IsLocallyBoundedPshOn Ω u) (hp : IsLocallyBoundedPshOn Ω p)
    (hu' : ∀ j, IsSmoothPshOn Ω (u' j)) (hp' : ∀ j, IsLocallyBoundedPshOn Ω (p' j))
    (huanti : ∀ x ∈ Ω, Antitone (fun j => u' j x))
    (hulim : ∀ x ∈ Ω, Tendsto (fun j => u' j x) atTop (𝓝 (u x)))
    (hpanti : ∀ x ∈ Ω, Antitone (fun j => p' j x))
    (hplim : ∀ x ∈ Ω, Tendsto (fun j => p' j x) atTop (𝓝 (p x)))
    (v : ComplexModel n) (φ : 𝓓(Ω, ℝ)) (hφ : ∀ x, 0 ≤ φ x)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ j in atTop,
      weightedLeviDistribution (isLocallyBoundedPshOn_of_isSmoothPshOn (hu' j)) (hp' j) v φ <
        weightedLeviDistribution hu hp v φ + ε := by
  let μ := directionalLeviMeasure hp v
  let : μ.Regular := directionalLeviMeasure_regular hp v
  let a := ∫ x : Ω, φ x * u x ∂μ
  let huL := fun j => isLocallyBoundedPshOn_of_isSmoothPshOn (hu' j)
  have hfix := tendsto_integral_psh_weight_of_antitone hu huL huanti hulim μ φ
  have hhalf : a < a + ε / 2 := lt_add_of_pos_right a (half_pos hε)
  obtain ⟨m, hm⟩ := (hfix.eventually_lt_const hhalf).exists
  let ψ := multiplySmoothTest φ (hu' m).1
  have hcont := tendsto_directionalLeviMeasure_test hp hp' hpanti hplim v ψ
  have hlt : (∫ x : Ω, ψ x ∂μ) < a + ε := hm.trans (by linarith)
  simp_rw [weightedLeviDistribution_apply]
  filter_upwards [eventually_ge_atTop m, hcont.eventually_lt_const hlt] with j hj hupper
  let ν := directionalLeviMeasure (hp' j) v
  let : ν.Regular := directionalLeviMeasure_regular (hp' j) v
  have hleft : Integrable (fun x : Ω => φ x * u' j x) ν :=
    (testFunctionToCompactlySupportedLM Ω (multiplySmoothTest φ (hu' j).1)).integrable
  have hright : Integrable (fun x : Ω => ψ x) ν :=
    (testFunctionToCompactlySupportedLM Ω ψ).integrable
  exact (integral_mono hleft hright fun x =>
    mul_le_mul_of_nonneg_left (huanti x x.property hj) (hφ x)).trans_lt hupper

end KEBall.BedfordTaylor
