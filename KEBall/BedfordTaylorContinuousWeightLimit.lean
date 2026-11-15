import KEBall.BedfordTaylorMixedConvergence
import Mathlib.Topology.UniformSpace.Dini

/-!
# Joint convergence with a continuous limiting weight

Dini's theorem controls the varying weight on compact sets. The local
mass estimate then reduces the joint limit to convergence against a
fixed continuous compactly supported function.
-/

set_option autoImplicit false

open Filter MeasureTheory Set TopologicalSpace
open scoped Distributions Topology

namespace KEBall.BedfordTaylor

open PshLines
open PshLines.FirstPass (ComplexModel)
open PshLines.FirstPass.MongeAmpere (IsLocallyBoundedPshOn)

variable {n : ℕ} {Ω : Opens (ComplexModel n)} {u p : ComplexModel n → ℝ}
  {u' p' : ℕ → ComplexModel n → ℝ}

private theorem continuous_test_mul_of_continuousOn (φ : 𝓓(Ω, ℝ))
    {f : ComplexModel n → ℝ} (hf : ContinuousOn f Ω) :
    Continuous (fun x => φ x * f x) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x ∈ Ω
  · exact φ.continuous.continuousAt.mul (hf.continuousAt (Ω.isOpen.mem_nhds hx))
  · apply (continuousAt_const (y := (0 : ℝ))).congr
    have hx' : x ∈ (tsupport φ)ᶜ := fun h => hx (φ.tsupport_subset h)
    filter_upwards [(isClosed_tsupport φ).isOpen_compl.mem_nhds hx'] with y hy
    simp only [image_eq_zero_of_notMem_tsupport hy, zero_mul]

theorem tendsto_weightedLeviDistribution_of_continuous_limit
    (hu : IsLocallyBoundedPshOn Ω u) (hp : IsLocallyBoundedPshOn Ω p)
    (hu' : ∀ j, IsLocallyBoundedPshOn Ω (u' j)) (hp' : ∀ j, IsLocallyBoundedPshOn Ω (p' j))
    (huc : ContinuousOn u Ω) (hu'c : ∀ j, ContinuousOn (u' j) Ω)
    (huanti : ∀ x ∈ Ω, Antitone (fun j => u' j x))
    (hulim : ∀ x ∈ Ω, Tendsto (fun j => u' j x) atTop (𝓝 (u x)))
    (hpanti : ∀ x ∈ Ω, Antitone (fun j => p' j x))
    (hplim : ∀ x ∈ Ω, Tendsto (fun j => p' j x) atTop (𝓝 (p x)))
    (v : ComplexModel n) (φ : 𝓓(Ω, ℝ)) :
    Tendsto (fun j => weightedLeviDistribution (hu' j) (hp' j) v φ) atTop
      (𝓝 (weightedLeviDistribution hu hp v φ)) := by
  let μ := fun j => directionalLeviMeasure (hp' j) v
  let K := (Subtype.val : Ω → ComplexModel n) ⁻¹' tsupport φ
  let : ∀ j, (μ j).Regular := fun j => directionalLeviMeasure_regular (hp' j) v
  have hK : IsCompact K :=
    Topology.IsEmbedding.subtypeVal.isInducing.isCompact_preimage' φ.hasCompactSupport (by
      intro x hx
      exact ⟨⟨x, φ.tsupport_subset hx⟩, rfl⟩)
  obtain ⟨χ, hχ, hχK⟩ := exists_testFunction_one_on φ.hasCompactSupport φ.tsupport_subset
  obtain ⟨B, _, hB⟩ :=
    exists_compact_abs_bound_of_antitone hp hp' hpanti hplim χ.hasCompactSupport χ.tsupport_subset
  let M := B * ∫ x, |leviForm χ x v|
  have hμM (j : ℕ) : (μ j).real K ≤ M :=
    directionalLeviMeasure_mass_le_of_cutoff (hp' j) v hK χ (fun x => (hχ x).1)
      (fun x hx => (hχK hx).ge) (hB j)
  have hM : 0 ≤ M := (measureReal_nonneg (μ := μ 0) (s := K)).trans (hμM 0)
  obtain ⟨C₀, hC₀⟩ :=
    (φ.hasCompactSupport.image_of_continuousOn φ.continuous.abs.continuousOn).bddAbove
  let C := max C₀ 1
  have hC (x : ComplexModel n) (hx : x ∈ tsupport φ) : |φ x| ≤ C :=
    (hC₀ ⟨x, hx, rfl⟩).trans (le_max_left _ _)
  have hCpos : 0 < C := zero_lt_one.trans_le (le_max_right _ _)
  have hf : Continuous (fun x => φ x * u x) := continuous_test_mul_of_continuousOn φ huc
  have hts : tsupport (fun x => φ x * u x) ⊆ tsupport φ := tsupport_mul_subset_left
  have hfixed := tendsto_directionalLeviMeasure_continuous_test hp hp' hpanti hplim v hf
    (φ.hasCompactSupport.of_isClosed_subset isClosed_closure hts) (hts.trans φ.tsupport_subset)
  have hf' (j : ℕ) : Continuous (fun x => φ x * u' j x) :=
    continuous_test_mul_of_continuousOn φ (hu'c j)
  have hz (x : Ω) (hx : x ∉ K) : φ x = 0 := image_eq_zero_of_notMem_tsupport hx
  have hint {f : ComplexModel n → ℝ} (hf : Continuous (fun x => φ x * f x)) (j : ℕ) :
      Integrable (fun x : Ω => φ x * f x) (μ j) := by
    rw [← integrableOn_iff_integrable_of_support_subset (s := K)]
    · exact (hf.comp continuous_subtype_val).continuousOn.integrableOn_compact hK
    · intro x hx
      by_contra h
      exact hx (by simp [hz x h])
  have hunif := Antitone.tendstoUniformlyOn_of_forall_tendsto φ.hasCompactSupport
    (fun j => (hu'c j).mono φ.tsupport_subset) (fun x hx => huanti x (φ.tsupport_subset hx))
    (huc.mono φ.tsupport_subset) (fun x hx => hulim x (φ.tsupport_subset hx))
  have hdiff : Tendsto
      (fun j => (∫ x : Ω, φ x * u' j x ∂μ j) - ∫ x : Ω, φ x * u x ∂μ j)
        atTop (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    let δ := ε / (C * M + 1)
    have hdenom : 0 < C * M + 1 := by positivity
    have hδ : 0 < δ := div_pos hε hdenom
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hunif δ hδ] with j hj
    rw [dist_zero_right, ← integral_sub (hint (hf' j) j) (hint hf j)]
    have hzero (x : Ω) (hx : x ∉ K) : φ x * u' j x - φ x * u x = 0 := by
      rw [hz x hx, zero_mul, zero_mul, sub_self]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
    refine (norm_setIntegral_le_of_norm_le_const_ae (C := C * δ) hK.measure_lt_top ?_).trans_lt ?_
    · filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
      change ‖φ x * u' j x - φ x * u x‖ ≤ C * δ
      rw [← mul_sub, Real.norm_eq_abs, abs_mul]
      apply mul_le_mul (hC x hx) _ (abs_nonneg _) hCpos.le
      simpa only [Real.dist_eq, abs_sub_comm] using (hj x hx).le
    · have hmul := mul_le_mul_of_nonneg_left (hμM j) (mul_nonneg hCpos.le hδ.le)
      refine hmul.trans_lt ?_
      rw [show C * δ * M = C * M * δ by ring]
      dsimp [δ]
      rw [← mul_div_assoc, div_lt_iff₀ hdenom]
      nlinarith
  simp_rw [weightedLeviDistribution_apply]
  simpa only [μ, sub_add_cancel, zero_add] using hdiff.add hfixed

/-- Joint test convergence of second mixed Hessians when the weight and
its approximants are continuous on the open domain. -/
theorem tendsto_secondMixedHessian_of_continuous_limit
    (hu : IsLocallyBoundedPshOn Ω u) (hp : IsLocallyBoundedPshOn Ω p)
    (hu' : ∀ j, IsLocallyBoundedPshOn Ω (u' j)) (hp' : ∀ j, IsLocallyBoundedPshOn Ω (p' j))
    (huc : ContinuousOn u Ω) (hu'c : ∀ j, ContinuousOn (u' j) Ω)
    (huanti : ∀ x ∈ Ω, Antitone (fun j => u' j x))
    (hulim : ∀ x ∈ Ω, Tendsto (fun j => u' j x) atTop (𝓝 (u x)))
    (hpanti : ∀ x ∈ Ω, Antitone (fun j => p' j x))
    (hplim : ∀ x ∈ Ω, Tendsto (fun j => p' j x) atTop (𝓝 (p x)))
    (v w : Fin 2 → ComplexModel n) (φ : 𝓓(Ω, ℝ)) :
    Tendsto (fun j => secondMixedHessian (hu' j) (hp' j) v w φ) atTop
      (𝓝 (secondMixedHessian hu hp v w φ)) := by
  apply tendsto_secondMixedHessian_of_weightedComplexHessian_test _ v w φ
  intro a b ψ
  simp only [weightedComplexHessian]
  exact tendsto_polarizedLeviDistribution_test
    (tendsto_weightedLeviDistribution_of_continuous_limit hu hp hu' hp' huc hu'c
      huanti hulim hpanti hplim) a b ψ

end KEBall.BedfordTaylor
