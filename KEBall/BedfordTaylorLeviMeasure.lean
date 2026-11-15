import KEBall.BedfordTaylorTestMeasure
import PshLines.Regularization.HolomorphicPullback
import PshLines.TestLeviPairing
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The first derivative measure for bounded PSH potentials

Testing the first `ddᶜ` against a constant complex direction gives a positive
Levi distribution. Its representing measure is unique on the open domain.
-/

set_option autoImplicit false

open Set Filter MeasureTheory TopologicalSpace
open scoped Distributions Topology

namespace KEBall.BedfordTaylor

open PshLines
open PshLines.FirstPass (ComplexModel)
open PshLines.FirstPass.MongeAmpere
  (IsLocallyBoundedPshOn locallyIntegrableOn_of_plurisubharmonicOn_real
   hasNonnegativeDistributionalLevi_of_plurisubharmonicOn_real)

variable {n : ℕ} {Ω : Opens (ComplexModel n)} {u : ComplexModel n → ℝ}

/-- The positive measure representing one constant-direction coefficient of
the distributional Levi form. The quarter in `leviForm` is fixed by the
Wirtinger convention. -/
theorem existsUnique_directionalLeviMeasure (hu : IsLocallyBoundedPshOn Ω u)
    (v : ComplexModel n) :
    ∃! μ : Measure Ω, μ.Regular ∧
      ∀ φ : 𝓓(Ω, ℝ), (∫ x : Ω, φ x ∂μ) = ∫ x, u x * leviForm φ x v := by
  have hpos := hasNonnegativeDistributionalLevi_of_plurisubharmonicOn_real hu.1 v
  obtain ⟨μ, hμ, _, hμtest⟩ := hpos.exists_regular_measure
  have hpair (φ : 𝓓(Ω, ℝ)) :
      (∫ x : Ω, φ x ∂μ) = ∫ x, u x * leviForm φ x v :=
    (hμtest φ).trans (distributionalLeviCLM_regularDistribution_apply
      (locallyIntegrableOn_of_plurisubharmonicOn_real hu.1) φ v)
  refine ⟨μ, ⟨hμ, hpair⟩, ?_⟩
  rintro ν ⟨hν, hνtest⟩
  let : μ.Regular := hμ
  let : ν.Regular := hν
  exact measure_eq_of_smooth_test fun φ => (hνtest φ).trans (hpair φ).symm

noncomputable def directionalLeviMeasure (hu : IsLocallyBoundedPshOn Ω u)
    (v : ComplexModel n) : Measure Ω :=
  (existsUnique_directionalLeviMeasure hu v).exists.choose

theorem directionalLeviMeasure_regular (hu : IsLocallyBoundedPshOn Ω u)
    (v : ComplexModel n) : (directionalLeviMeasure hu v).Regular :=
  (existsUnique_directionalLeviMeasure hu v).exists.choose_spec.1

theorem integral_directionalLeviMeasure (hu : IsLocallyBoundedPshOn Ω u)
    (v : ComplexModel n) (φ : 𝓓(Ω, ℝ)) :
    (∫ x : Ω, φ x ∂directionalLeviMeasure hu v) = ∫ x, u x * leviForm φ x v :=
  (existsUnique_directionalLeviMeasure hu v).exists.choose_spec.2 φ

/-- The local mass estimate for the first `ddᶜ` factor. A compact cutoff
bounds its measure on a compact set by the local bound on the potential
times the integral of the absolute Levi derivative of the cutoff. -/
theorem directionalLeviMeasure_mass_le_of_cutoff (hu : IsLocallyBoundedPshOn Ω u)
    (v : ComplexModel n) {K : Set Ω} (hK : IsCompact K)
    (χ : 𝓓(Ω, ℝ)) (hχ₀ : ∀ x, 0 ≤ χ x) (hχ₁ : ∀ x ∈ K, 1 ≤ χ (x : Ω))
    {C : ℝ} (huC : ∀ x ∈ tsupport χ, |u x| ≤ C) :
    (directionalLeviMeasure hu v).real K ≤ C * ∫ x, |leviForm χ x v| := by
  let μ := directionalLeviMeasure hu v
  let : μ.Regular := directionalLeviMeasure_regular hu v
  have hKint : Integrable (K.indicator (1 : Ω → ℝ)) μ :=
    (continuousOn_const.integrableOn_compact hK).integrable_indicator hK.measurableSet
  have hχint : Integrable (fun x : Ω => χ x) μ :=
    (testFunctionToCompactlySupportedLM Ω χ).integrable
  have hKχ (x : Ω) : K.indicator (1 : Ω → ℝ) x ≤ χ x := by
    by_cases hx : x ∈ K
    · rw [indicator_of_mem hx]
      exact hχ₁ x hx
    · rw [indicator_of_notMem hx]
      exact hχ₀ x
  have hsup (x : ComplexModel n) : u x * leviForm χ x v ≤ C * |leviForm χ x v| := by
    by_cases hx : x ∈ tsupport χ
    · exact (le_abs_self _).trans (by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (huC x hx) (abs_nonneg _))
    · simp only [leviForm_eq_zero_of_notMem_tsupport hx v, mul_zero, abs_zero, le_refl]
  have hd : HasCompactSupport (fun x => leviForm χ x v) :=
    χ.hasCompactSupport.of_isClosed_subset isClosed_closure (tsupport_leviForm_subset χ v)
  have hdcont : Continuous (fun x => leviForm χ x v) :=
    continuous_leviForm (χ.contDiff.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) v
  calc
    μ.real K = ∫ x, K.indicator (1 : Ω → ℝ) x ∂μ :=
      (integral_indicator_one hK.measurableSet).symm
    _ ≤ ∫ x : Ω, χ x ∂μ := integral_mono hKint hχint hKχ
    _ = ∫ x, u x * leviForm χ x v := integral_directionalLeviMeasure hu v χ
    _ ≤ ∫ x, C * |leviForm χ x v| := integral_mono
      (integrable_mul_leviForm_testFunction (locallyIntegrableOn_of_plurisubharmonicOn_real hu.1) χ v)
      ((hdcont.integrable_of_hasCompactSupport hd).abs.const_mul C) hsup
    _ = C * ∫ x, |leviForm χ x v| := integral_const_mul _ _

/-- A decreasing PSH approximation has a common bound on each compact
subset of the domain, given by the first potential and the limit. -/
theorem exists_compact_abs_bound_of_antitone (hu : IsLocallyBoundedPshOn Ω u)
    {p : ℕ → ComplexModel n → ℝ} (hp : ∀ j, IsLocallyBoundedPshOn Ω (p j))
    (hanti : ∀ x ∈ Ω, Antitone (fun j => p j x))
    (hlim : ∀ x ∈ Ω, Tendsto (fun j => p j x) atTop (𝓝 (u x)))
    {K : Set (ComplexModel n)} (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j x, x ∈ K → |p j x| ≤ C := by
  obtain ⟨C₁, hC₁, huK⟩ := hu.exists_compact_abs_bound hK hKΩ
  obtain ⟨C₂, _, hpK⟩ := (hp 0).exists_compact_abs_bound hK hKΩ
  refine ⟨max C₁ C₂, hC₁.trans (le_max_left _ _), fun j x hx => ?_⟩
  have hxΩ := hKΩ hx
  have hlow : u x ≤ p j x := le_of_tendsto (hlim x hxΩ)
    ((eventually_ge_atTop j).mono fun k hjk => hanti x hxΩ hjk)
  exact abs_le.mpr ⟨
    (neg_le_neg (le_max_left C₁ C₂)).trans ((abs_le.mp (huK x hx)).1.trans hlow),
    (hanti x hxΩ (Nat.zero_le j)).trans ((abs_le.mp (hpK x hx)).2.trans (le_max_right C₁ C₂))⟩

/-- The first-degree measures converge on smooth compactly supported tests
under the pointwise decreasing convergence used in the Bedford–Taylor theorem. -/
theorem tendsto_directionalLeviMeasure_test (hu : IsLocallyBoundedPshOn Ω u)
    {p : ℕ → ComplexModel n → ℝ} (hp : ∀ j, IsLocallyBoundedPshOn Ω (p j))
    (hanti : ∀ x ∈ Ω, Antitone (fun j => p j x))
    (hlim : ∀ x ∈ Ω, Tendsto (fun j => p j x) atTop (𝓝 (u x)))
    (v : ComplexModel n) (φ : 𝓓(Ω, ℝ)) :
    Tendsto (fun j => ∫ x : Ω, φ x ∂directionalLeviMeasure (hp j) v) atTop
      (𝓝 (∫ x : Ω, φ x ∂directionalLeviMeasure hu v)) := by
  simp_rw [integral_directionalLeviMeasure]
  obtain ⟨C, _, hsup⟩ :=
    exists_compact_abs_bound_of_antitone hu hp hanti hlim φ.hasCompactSupport φ.tsupport_subset
  have hd : HasCompactSupport (fun x => leviForm φ x v) :=
    φ.hasCompactSupport.of_isClosed_subset isClosed_closure (tsupport_leviForm_subset φ v)
  have hdcont : Continuous (fun x => leviForm φ x v) :=
    continuous_leviForm (φ.contDiff.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) v
  apply tendsto_integral_of_dominated_convergence (fun x => C * |leviForm φ x v|)
  · intro j
    exact (integrable_mul_leviForm_testFunction
      (locallyIntegrableOn_of_plurisubharmonicOn_real (hp j).1) φ v).aestronglyMeasurable
  · exact (hdcont.integrable_of_hasCompactSupport hd).abs.const_mul C
  · intro j
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_mul]
    by_cases hx : x ∈ tsupport φ
    · exact mul_le_mul_of_nonneg_right (hsup j x hx) (abs_nonneg _)
    · simp [leviForm_eq_zero_of_notMem_tsupport hx v]
  · filter_upwards with x
    by_cases hx : x ∈ Ω
    · exact (hlim x hx).mul tendsto_const_nhds
    · have hz := leviForm_eq_zero_of_notMem_tsupport (fun hk => hx (φ.tsupport_subset hk)) v
      simpa only [hz, mul_zero] using (tendsto_const_nhds (x := (0 : ℝ)))

#print axioms existsUnique_directionalLeviMeasure
#print axioms tendsto_directionalLeviMeasure_test
#print axioms directionalLeviMeasure_mass_le_of_cutoff

end KEBall.BedfordTaylor
