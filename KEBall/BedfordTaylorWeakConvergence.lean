import KEBall.BedfordTaylorLeviMeasure
import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox

/-!
# Continuous tests for convergence of Levi measures

Smooth test convergence for positive measures controls the local mass
through a cutoff. Smooth approximation then gives continuous test convergence.
-/

set_option autoImplicit false

open Filter MeasureTheory Set TopologicalSpace
open scoped ContDiff Distributions Topology

namespace KEBall.BedfordTaylor

open PshLines.FirstPass (ComplexModel)
open PshLines.FirstPass.MongeAmpere (IsLocallyBoundedPshOn)

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
  [MeasurableSpace H] [BorelSpace H] {Ω : Opens H}

omit [NormedSpace ℝ H] [FiniteDimensional ℝ H] in
private theorem integral_dist_le_on_compact {μ : Measure Ω} [IsFiniteMeasureOnCompacts μ]
    {K : Set Ω} (hK : IsCompact K) {f g : Ω → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hf₀ : ∀ x ∉ K, f x = 0) (hg₀ : ∀ x ∉ K, g x = 0)
    {δ : ℝ} (hδ : ∀ x, dist (f x) (g x) ≤ δ) :
    dist (∫ x, f x ∂μ) (∫ x, g x ∂μ) ≤ δ * μ.real K := by
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hf₀,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero hg₀, dist_eq_norm,
    ← integral_sub (hf.continuousOn.integrableOn_compact hK)
      (hg.continuousOn.integrableOn_compact hK)]
  apply norm_setIntegral_le_of_norm_le_const_ae hK.measure_lt_top
  filter_upwards with x using (dist_eq_norm (f x) (g x)) ▸ hδ x

/-- For positive measures on an open domain, convergence on smooth compact
tests implies convergence on continuous compact tests supported in the domain. -/
theorem tendsto_integral_of_tendsto_smooth_tests {μ : ℕ → Measure Ω} {ν : Measure Ω}
    [∀ j, (μ j).Regular] [ν.Regular]
    (h : ∀ φ : 𝓓(Ω, ℝ),
      Tendsto (fun j => ∫ z : Ω, φ z ∂μ j) atTop (𝓝 (∫ z : Ω, φ z ∂ν)))
    {f : H → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f) (hfΩ : tsupport f ⊆ Ω) :
    Tendsto (fun j => ∫ z : Ω, f z ∂μ j) atTop (𝓝 (∫ z : Ω, f z ∂ν)) := by
  obtain ⟨χ, hχ, hχf⟩ := exists_testFunction_one_on hfc hfΩ
  let K := (Subtype.val : Ω → H) ⁻¹' tsupport χ
  have hK : IsCompact K :=
    Topology.IsEmbedding.subtypeVal.isInducing.isCompact_preimage' χ.hasCompactSupport (by
      intro z hz
      exact ⟨⟨z, χ.tsupport_subset hz⟩, rfl⟩)
  obtain ⟨ψ, hψ, hψχ⟩ := exists_testFunction_one_on χ.hasCompactSupport χ.tsupport_subset
  have hmass (ρ : Measure Ω) [ρ.Regular] : ρ.real K ≤ ∫ z : Ω, ψ z ∂ρ := by
    rw [← integral_indicator_one hK.measurableSet]
    apply integral_mono
      ((continuousOn_const.integrableOn_compact hK).integrable_indicator hK.measurableSet)
      (PshLines.testFunctionToCompactlySupportedLM Ω ψ).integrable
    intro z
    by_cases hz : z ∈ K
    · rw [indicator_of_mem hz]
      exact (hψχ hz).ge
    · rw [indicator_of_notMem hz]
      exact (hψ z).1
  let M := (∫ z : Ω, ψ z ∂ν) + 1
  have hνM : ν.real K ≤ M := (hmass ν).trans (le_add_of_nonneg_right zero_le_one)
  have hM : 0 < M := by
    have hpos : 0 ≤ ∫ z : Ω, ψ z ∂ν :=
      integral_nonneg (f := fun z : Ω => ψ z) (fun z => (hψ z).1)
    dsimp [M]
    linarith
  have hμM : ∀ᶠ j in atTop, (μ j).real K ≤ M :=
    ((h ψ).eventually_lt_const (show (∫ z : Ω, ψ z ∂ν) < M by simp [M])).mono
      (fun j hj => (hmass (μ j)).trans hj.le)
  rw [Metric.tendsto_nhds]
  intro ε hε
  let δ := ε / (4 * M)
  have hδ : 0 < δ := div_pos hε (by positivity)
  obtain ⟨g, hg, hgf⟩ := (hfc.uniformContinuous_of_continuous hf).exists_contDiff_dist_le hδ
  let G : H → ℝ := fun x => χ x * g x
  have hG : tsupport G ⊆ tsupport χ := tsupport_mul_subset_left
  let η : 𝓓(Ω, ℝ) :=
    ⟨G, χ.contDiff.mul hg, χ.hasCompactSupport.of_isClosed_subset isClosed_closure hG,
      hG.trans χ.tsupport_subset⟩
  have hηf (x : H) : dist (η x) (f x) ≤ δ := by
    have heq : χ x * f x = f x := by
      by_cases hx : x ∈ tsupport f
      · rw [hχf hx, Pi.one_apply, one_mul]
      · rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]
    change dist (χ x * g x) (f x) ≤ δ
    rw [← heq, Real.dist_eq, ← mul_sub, abs_mul, abs_of_nonneg (hχ x).1, ← Real.dist_eq]
    exact (mul_le_mul_of_nonneg_right (hχ x).2 dist_nonneg).trans (by simpa using (hgf x).le)
  have hdist (ρ : Measure Ω) [ρ.Regular] :
      dist (∫ z : Ω, η z ∂ρ) (∫ z : Ω, f z ∂ρ) ≤ δ * ρ.real K :=
    integral_dist_le_on_compact hK (η.continuous.comp continuous_subtype_val)
      (hf.comp continuous_subtype_val)
      (fun z hz => show G (z : H) = 0 from image_eq_zero_of_notMem_tsupport (fun hz' => hz (hG hz')))
      (fun z hz => show f (z : H) = 0 from image_eq_zero_of_notMem_tsupport (by
        intro hfz
        apply hz (subset_tsupport χ _)
        change χ (z : H) ≠ 0
        rw [hχf hfz, Pi.one_apply]
        exact one_ne_zero))
      (fun z => hηf z)
  have hsmall : δ * M = ε / 4 := by dsimp [δ]; field_simp
  filter_upwards [hμM, Metric.tendsto_nhds.mp (h η) (ε / 2) (half_pos hε)] with j hj hη
  have hj' := (hdist (μ j)).trans (mul_le_mul_of_nonneg_left hj hδ.le)
  have hν' := (hdist ν).trans (mul_le_mul_of_nonneg_left hνM hδ.le)
  rw [hsmall, dist_comm] at hj'
  rw [hsmall] at hν'
  apply (dist_triangle4 _ (∫ z : Ω, η z ∂μ j) (∫ z : Ω, η z ∂ν) _).trans_lt
  linarith

theorem tendsto_directionalLeviMeasure_continuous_test {n : ℕ} {U : Opens (ComplexModel n)}
    {u : ComplexModel n → ℝ} (hu : IsLocallyBoundedPshOn U u)
    {p : ℕ → ComplexModel n → ℝ} (hp : ∀ j, IsLocallyBoundedPshOn U (p j))
    (hanti : ∀ x ∈ U, Antitone (fun j => p j x))
    (hlim : ∀ x ∈ U, Tendsto (fun j => p j x) atTop (𝓝 (u x)))
    (v : ComplexModel n) {f : ComplexModel n → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) (hfU : tsupport f ⊆ U) :
    Tendsto (fun j => ∫ z : U, f z ∂directionalLeviMeasure (hp j) v) atTop
      (𝓝 (∫ z : U, f z ∂directionalLeviMeasure hu v)) := by
  let : ∀ j, (directionalLeviMeasure (hp j) v).Regular :=
    fun j => directionalLeviMeasure_regular (hp j) v
  let : (directionalLeviMeasure hu v).Regular := directionalLeviMeasure_regular hu v
  exact tendsto_integral_of_tendsto_smooth_tests
    (tendsto_directionalLeviMeasure_test hu hp hanti hlim v) hf hfc hfU

#print axioms tendsto_directionalLeviMeasure_continuous_test

end KEBall.BedfordTaylor
