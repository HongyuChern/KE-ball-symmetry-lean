import KEBall.BedfordTaylorBoundaryPairing
import KEBall.BedfordTaylorWeightedOrderLimit

/-!
# Weighted convergence with a common boundary potential

The smooth integration-by-parts identity controls the total weighted
integrals. Comparing a test with a sufficiently large cutoff then
localizes the lower bound.
-/

set_option autoImplicit false

open Filter MeasureTheory Set TopologicalSpace
open scoped Distributions Topology

namespace KEBall.BedfordTaylor

open PshLines
open PshLines.FirstPass (ComplexModel)
open PshLines.FirstPass.MongeAmpere (IsLocallyBoundedPshOn IsSmoothPshOn)

variable {n : ℕ} {Ω : Opens (ComplexModel n)} {u p : ComplexModel n → ℝ}
  {u' p' : ℕ → ComplexModel n → ℝ}

private theorem tendsto_weightedLeviDistribution_cutoff
    (hu : IsLocallyBoundedPshOn Ω u) (hp : IsLocallyBoundedPshOn Ω p)
    (hu' : ∀ j, IsSmoothPshOn Ω (u' j)) (hp' : ∀ j, IsSmoothPshOn Ω (p' j))
    (huanti : ∀ x ∈ Ω, Antitone (fun j => u' j x))
    (hulim : ∀ x ∈ Ω, Tendsto (fun j => u' j x) atTop (𝓝 (u x)))
    (hpanti : ∀ x ∈ Ω, Antitone (fun j => p' j x))
    (hplim : ∀ x ∈ Ω, Tendsto (fun j => p' j x) atTop (𝓝 (p x)))
    {K : Set (ComplexModel n)} (hK : IsCompact K)
    (heq : ∀ j m, EqOn (u' j) (p' m) ((Ω : Set (ComplexModel n)) \ K))
    (χ : 𝓓(Ω, ℝ)) (hχ₀ : ∀ x, 0 ≤ χ x) (hχ₁ : ∀ x ∈ K, (χ : ComplexModel n → ℝ) =ᶠ[𝓝 x] 1)
    (v : ComplexModel n) :
    Tendsto (fun j => weightedLeviDistribution (isLocallyBoundedPshOn_of_isSmoothPshOn (hu' j))
      (isLocallyBoundedPshOn_of_isSmoothPshOn (hp' j)) v χ) atTop
      (𝓝 (weightedLeviDistribution hu hp v χ)) := by
  let huL := fun j => isLocallyBoundedPshOn_of_isSmoothPshOn (hu' j)
  let hpL := fun j => isLocallyBoundedPshOn_of_isSmoothPshOn (hp' j)
  let μ := directionalLeviMeasure hp v
  let μu := fun j => directionalLeviMeasure (huL j) v
  let μp := fun j => directionalLeviMeasure (hpL j) v
  let : μ.Regular := directionalLeviMeasure_regular hp v
  let : ∀ j, (μu j).Regular := fun j => directionalLeviMeasure_regular (huL j) v
  have hswap (j : ℕ) : (∫ x : Ω, χ x * u' j x ∂μ) = ∫ x : Ω, χ x * p x ∂μu j := by
    have hL := tendsto_directionalLeviMeasure_test hp hpL hpanti hplim v
      (multiplySmoothTest χ (hu' j).1)
    have hR := tendsto_integral_psh_weight_of_antitone hp hpL hpanti hplim (μu j) χ
    exact tendsto_nhds_unique hL (hR.congr' (Eventually.of_forall fun m =>
      (integral_mul_directionalLeviMeasure_swap (hu' j) (hp' m) hK (heq j m) χ hχ₁ v).symm))
  have hlow (j : ℕ) :
      (∫ x : Ω, χ x * u x ∂μ) ≤ ∫ x : Ω, χ x * u' j x ∂μp j := calc
    _ ≤ ∫ x : Ω, χ x * u' j x ∂μ :=
      integral_mono (integrable_test_mul_psh hu μ χ) (integrable_test_mul_psh (huL j) μ χ)
        (fun x => mul_le_mul_of_nonneg_left
          (le_of_tendsto (hulim x x.property)
            ((eventually_ge_atTop j).mono fun m hm => huanti x x.property hm)) (hχ₀ x))
    _ = ∫ x : Ω, χ x * p x ∂μu j := hswap j
    _ ≤ ∫ x : Ω, χ x * p' j x ∂μu j :=
      integral_mono (integrable_test_mul_psh hp (μu j) χ) (integrable_test_mul_psh (hpL j) (μu j) χ)
        (fun x => mul_le_mul_of_nonneg_left
          (le_of_tendsto (hplim x x.property)
            ((eventually_ge_atTop j).mono fun m hm => hpanti x x.property hm)) (hχ₀ x))
    _ = _ := (integral_mul_directionalLeviMeasure_swap (hu' j) (hp' j) hK (heq j j) χ hχ₁ v).symm
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Eventually.of_forall fun j =>
      ha.trans_le (by simpa only [weightedLeviDistribution_apply] using hlow j)
  · intro a ha
    have h := eventually_weightedLeviDistribution_lt_add hu hp hu' hpL
      huanti hulim hpanti hplim v χ hχ₀ (sub_pos.mpr ha)
    simpa only [add_sub_cancel] using h

theorem tendsto_of_upper_of_dominating_test {T : ℕ → 𝓓'(Ω, ℝ)} {S : 𝓓'(Ω, ℝ)}
    (hupper : ∀ ψ : 𝓓(Ω, ℝ), (∀ x, 0 ≤ ψ x) → ∀ ε > 0,
      ∀ᶠ j in atTop, T j ψ < S ψ + ε)
    (χ φ : 𝓓(Ω, ℝ)) (hχ : ∀ x, |φ x| ≤ χ x)
    (hχlim : Tendsto (fun j => T j χ) atTop (𝓝 (S χ))) :
    Tendsto (fun j => T j φ) atTop (𝓝 (S φ)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have h₁ : ∀ x, 0 ≤ (χ + φ) x := fun x => by
    rw [add_apply]
    linarith [(abs_le.mp (hχ x)).1]
  have h₂ : ∀ x, 0 ≤ (χ - φ) x := fun x =>
    sub_nonneg.mpr ((le_abs_self _).trans (hχ x))
  filter_upwards [Metric.tendsto_nhds.mp hχlim (ε / 2) (half_pos hε),
    hupper (χ + φ) h₁ (ε / 2) (half_pos hε),
    hupper (χ - φ) h₂ (ε / 2) (half_pos hε)] with j hj hplus hminus
  simp only [map_add, map_sub] at hplus hminus
  rw [Real.dist_eq, abs_lt] at hj ⊢
  constructor <;> linarith

/-- Joint weighted convergence when all approximants have a common
boundary potential off a compact subset of the domain. -/
theorem tendsto_weightedLeviDistribution_of_eq_off_compact
    (hu : IsLocallyBoundedPshOn Ω u) (hp : IsLocallyBoundedPshOn Ω p)
    (hu' : ∀ j, IsSmoothPshOn Ω (u' j)) (hp' : ∀ j, IsSmoothPshOn Ω (p' j))
    (huanti : ∀ x ∈ Ω, Antitone (fun j => u' j x))
    (hulim : ∀ x ∈ Ω, Tendsto (fun j => u' j x) atTop (𝓝 (u x)))
    (hpanti : ∀ x ∈ Ω, Antitone (fun j => p' j x))
    (hplim : ∀ x ∈ Ω, Tendsto (fun j => p' j x) atTop (𝓝 (p x)))
    {K : Set (ComplexModel n)} (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (heq : ∀ j m, EqOn (u' j) (p' m) ((Ω : Set (ComplexModel n)) \ K))
    (v : ComplexModel n) (φ : 𝓓(Ω, ℝ)) :
    Tendsto (fun j => weightedLeviDistribution (isLocallyBoundedPshOn_of_isSmoothPshOn (hu' j))
      (isLocallyBoundedPshOn_of_isSmoothPshOn (hp' j)) v φ) atTop
      (𝓝 (weightedLeviDistribution hu hp v φ)) := by
  obtain ⟨W, hWo, hKW, hWΩ, hWc⟩ := exists_open_between_and_isCompact_closure
    (hK.union φ.hasCompactSupport) Ω.isOpen (union_subset hKΩ φ.tsupport_subset)
  obtain ⟨χ, hχ, hχW⟩ := exists_testFunction_one_on hWc hWΩ
  have hχ₁ (x : ComplexModel n) (hx : x ∈ K) : (χ : ComplexModel n → ℝ) =ᶠ[𝓝 x] 1 := by
    filter_upwards [hWo.mem_nhds (hKW (Or.inl hx))] with y hy
    exact hχW (subset_closure hy)
  have hχlim := tendsto_weightedLeviDistribution_cutoff hu hp hu' hp'
    huanti hulim hpanti hplim hK heq χ (fun x => (hχ x).1) hχ₁ v
  obtain ⟨C₀, hC₀⟩ :=
    (φ.hasCompactSupport.image_of_continuousOn φ.continuous.abs.continuousOn).bddAbove
  let C := max 0 C₀
  have hC (x : ComplexModel n) : |φ x| ≤ (C • χ) x := by
    by_cases hx : x ∈ tsupport φ
    · rw [smul_apply, hχW (subset_closure (hKW (Or.inr hx))), Pi.one_apply, smul_eq_mul, mul_one]
      exact (hC₀ ⟨x, hx, rfl⟩).trans (le_max_right _ _)
    · simp only [image_eq_zero_of_notMem_tsupport hx, abs_zero, smul_apply, smul_eq_mul]
      exact mul_nonneg (le_max_left _ _) (hχ x).1
  apply tendsto_of_upper_of_dominating_test
    (fun ψ hψ _ hε => eventually_weightedLeviDistribution_lt_add hu hp hu'
      (fun j => isLocallyBoundedPshOn_of_isSmoothPshOn (hp' j))
      huanti hulim hpanti hplim v ψ hψ hε) (C • χ) φ hC
  simpa only [map_smul, smul_eq_mul] using hχlim.const_mul C

end KEBall.BedfordTaylor
