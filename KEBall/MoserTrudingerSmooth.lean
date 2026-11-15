import Drafts.KEBall.NormalizedExterior
import Drafts.KEBall.NormalizedMass
import KEBall.MoserTrudingerRadialIntegral
import KEBall.MoserTrudingerRadialMeasure
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# The smooth radial family in Corollary 1.3

The energy in this file uses the existing top exterior form measure.
-/

set_option autoImplicit false

open Filter MeasureTheory Set
open scoped ComplexOrder ContDiff ENNReal Interval Topology

namespace KEBall.MoserTrudinger

noncomputable def smoothEnergy {n : ℕ} (u : E n → ℝ) : ℝ :=
  ∫ x in unitBall n, -u x ∂d0TopMeasure u

private theorem topMeasure_restrict_const_mul {n : ℕ} {u : E n → ℝ}
    (hu : SmoothNear (closedUnitBall n) u) {c : ℝ} (hc : 0 ≤ c) :
    (d0TopMeasure (fun x => c * u x)).restrict (unitBall n) =
      ENNReal.ofReal (c ^ n) • (d0TopMeasure u).restrict (unitBall n) := by
  have hB : MeasurableSet (unitBall n) := Metric.isOpen_ball.measurableSet
  rw [d0TopMeasure_eq_density, d0TopMeasure_eq_density,
    restrict_withDensity hB, restrict_withDensity hB,
    ← withDensity_smul' _ _ ENNReal.ofReal_ne_top]
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem hB] with x hx
  have hs := hu.contDiffAt (Metric.ball_subset_closedBall hx)
  rw [complexHessian_const_mul_at hs, Matrix.det_smul, Fintype.card_fin]
  simp only [Pi.smul_apply, smul_eq_mul, ← ENNReal.ofReal_mul (pow_nonneg hc _),
    ← Complex.ofReal_pow, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]

private theorem smoothEnergy_const_mul {n : ℕ} {u : E n → ℝ}
    (hu : SmoothNear (closedUnitBall n) u) {c : ℝ} (hc : 0 ≤ c) :
    smoothEnergy (fun x => c * u x) = c ^ (n + 1) * smoothEnergy u := by
  unfold smoothEnergy
  rw [topMeasure_restrict_const_mul hu hc, integral_smul_measure,
    ENNReal.toReal_ofReal (pow_nonneg hc _), smul_eq_mul]
  simp_rw [neg_mul_eq_mul_neg]
  rw [integral_const_mul, pow_succ, mul_assoc]

/-- Parameter `t` is the coupling divided by `n+1`. -/
noncomputable def profile (n : ℕ) (t : ℝ) : E n → ℝ :=
  normalizedPotential n ((n + 1 : ℝ) * t)

private theorem coupling_pos (n : ℕ) {t : ℝ} (ht : 0 < t) :
    0 < (n + 1 : ℝ) * t := by positivity

private theorem coupling_lt (n : ℕ) {t : ℝ} (ht : t < 1) :
    (n + 1 : ℝ) * t < (n + 1 : ℝ) := by
  simpa using mul_lt_mul_of_pos_left ht (show (0 : ℝ) < n + 1 by positivity)

private theorem t_mul_profile (n : ℕ) {t : ℝ} (ht : 0 < t) (x : E n) :
    t * profile n t x = Real.log (1 - t + t * ‖x‖ ^ 2) := by
  unfold profile normalizedPotential
  have hκ : (n + 1 : ℝ) ≠ 0 := by positivity
  rw [mul_div_cancel_left₀ _ hκ]
  field_simp [ht.ne', hκ]

private theorem density_formula (n : ℕ) {t : ℝ} (ht₀ : 0 < t) (ht₁ : t < 1)
    (x : E n) :
    Real.exp (-((n + 1 : ℝ) * t) * profile n t x) =
      ((1 - t + t * ‖x‖ ^ 2) ^ (n + 1))⁻¹ := by
  have hd : 0 < 1 - t + t * ‖x‖ ^ 2 :=
    add_pos_of_pos_of_nonneg (sub_pos.mpr ht₁) (by positivity)
  rw [show -((n + 1 : ℝ) * t) * profile n t x =
      -((n + 1 : ℝ) * (t * profile n t x)) by ring, t_mul_profile n ht₀,
      Real.exp_neg, ← Nat.cast_succ, Real.exp_nat_mul, Real.exp_log hd]

/-- The normalized exponential integral already computed by the classification proof. -/
theorem subcritical_integral_profile {n : ℕ} (hn : 2 ≤ n) {t : ℝ}
    (ht₀ : 0 < t) (ht₁ : t < 1) :
    (∫ x in unitBall n, Real.exp (-((n + 1 : ℝ) * t) * profile n t x) ∂volume0 n) =
      (1 - t)⁻¹ := by
  change normalizingIntegral ((n + 1 : ℝ) * t) (profile n t) = _
  unfold profile
  rw [normalizedPotential_normalizingIntegral hn (coupling_pos n ht₀) (coupling_lt n ht₁)]
  rw [mul_div_cancel_left₀ _ (by positivity : (n + 1 : ℝ) ≠ 0)]

/-- Equality with the scalar radial energy identity, using the actual measure. -/
theorem energy_profile {n : ℕ} (hn : 2 ≤ n) {t : ℝ}
    (ht₀ : 0 < t) (ht₁ : t < 1) :
    t * smoothEnergy (profile n t) = -Real.log (1 - t) - radialValue n t := by
  let φ := profile n t
  let γ : ℝ := (n + 1 : ℝ) * t
  have hφ : IsNormalizedSolution n γ φ :=
    normalizedPotential_isNormalizedSolution hn (coupling_pos n ht₀) (coupling_lt n ht₁)
  let g : ℝ → ℝ := fun s =>
    (1 - t) / (1 - t + t * s) ^ (n + 1) * (-Real.log (1 - t + t * s))
  have hgc : ContinuousOn g (Icc 0 1) := by
    have hd (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) : 0 < 1 - t + t * s :=
      add_pos_of_pos_of_nonneg (sub_pos.mpr ht₁) (mul_nonneg ht₀.le hs.1)
    have hc : ContinuousOn (fun s : ℝ => 1 - t + t * s) (Icc 0 1) := by fun_prop
    exact (continuousOn_const.div (hc.pow _) (fun s hs => pow_ne_zero _ (hd s hs).ne')).mul
      (hc.log (fun s hs => (hd s hs).ne')).neg
  have hB : MeasurableSet (unitBall n) := Metric.isOpen_ball.measurableSet
  have hdens_nonneg (x : E n) : 0 ≤ Real.exp (-γ * φ x) / normalizingIntegral γ φ :=
    div_nonneg (Real.exp_pos _).le hφ.normalizingIntegral_pos.le
  have hdens_meas : AEMeasurable
      (fun x => ENNReal.ofReal (Real.exp (-γ * φ x) / normalizingIntegral γ φ))
      ((volume0 n).restrict (unitBall n)) :=
    hφ.normalized_density_integrableOn.aestronglyMeasurable.aemeasurable.ennreal_ofReal
  change t * smoothEnergy φ = _
  unfold smoothEnergy
  rw [hφ.d0TopMeasure_normalized, integral_withDensity_eq_integral_toReal_smul₀ hdens_meas
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) _, ← integral_const_mul]
  have hnorm : normalizingIntegral γ φ = (1 - t)⁻¹ :=
    subcritical_integral_profile hn ht₀ ht₁
  have heq :
      (∫ x in unitBall n,
        t * ((ENNReal.ofReal (Real.exp (-γ * φ x) / normalizingIntegral γ φ)).toReal •
          -φ x) ∂volume0 n) =
        ∫ x in unitBall n, g (‖x‖ ^ 2) ∂volume0 n := by
    apply setIntegral_congr_fun hB
    intro x _
    dsimp only
    rw [ENNReal.toReal_ofReal (hdens_nonneg x), smul_eq_mul, hnorm,
      div_inv_eq_mul, show Real.exp (-γ * φ x) = ((1 - t + t * ‖x‖ ^ 2) ^ (n + 1))⁻¹
        from density_formula n ht₀ ht₁ x]
    unfold g
    rw [← t_mul_profile n ht₀ x]
    dsimp [φ]
    ring
  rw [heq, integral_volume0_sqNorm (by omega : 0 < n) g hgc]
  rw [← integral_radial_energy n (by omega) ht₀.le ht₁]
  apply intervalIntegral.integral_congr
  intro x _
  dsimp [g]
  ring

/-- Smooth tests for both optimal constants in Corollary 1.3. -/
noncomputable def testPotential (n : ℕ) (t : ℝ) : E n → ℝ :=
  fun x => (n + 1 : ℝ) * profile n t x

noncomputable def energyCoefficient (n : ℕ) : ℝ :=
  ((n + 1 : ℝ) ^ (n + 1))⁻¹

noncomputable def logIntegral {n : ℕ} (u : E n → ℝ) : ℝ :=
  Real.log (∫ x in unitBall n, Real.exp (-u x) ∂volume0 n)

theorem testPotential_admissible {n : ℕ} (hn : 2 ≤ n) {t : ℝ}
    (ht₀ : 0 < t) (ht₁ : t < 1) :
    SmoothNear (closedUnitBall n) (testPotential n t) ∧
    (∀ x ∈ unitBall n, (complexHessian (testPotential n t) x).PosDef) ∧
    (∀ x ∈ unitSphere n, testPotential n t x = 0) := by
  have hφ : IsNormalizedSolution n ((n + 1 : ℝ) * t) (profile n t) :=
    normalizedPotential_isNormalizedSolution hn (coupling_pos n ht₀) (coupling_lt n ht₁)
  refine ⟨?_, ?_, ?_⟩
  · exact smoothNear_const_mul hφ.2.1 _
  · intro x hx
    unfold testPotential
    rw [complexHessian_const_mul_at (hφ.2.1.contDiffAt (Metric.ball_subset_closedBall hx))]
    apply (hφ.2.2.1 x hx).smul
    exact_mod_cast (show 0 < (n + 1 : ℝ) by positivity)
  · intro x hx
    simp [testPotential, hφ.2.2.2.1 x hx]

theorem testPotential_finite_energy {n : ℕ} (hn : 2 ≤ n) {t : ℝ}
    (ht₀ : 0 < t) (ht₁ : t < 1) :
    d0TopMeasure (testPotential n t) (unitBall n) = ENNReal.ofReal ((n + 1 : ℝ) ^ n) ∧
    IntegrableOn (fun x => -testPotential n t x) (unitBall n) (d0TopMeasure (testPotential n t)) ∧
    IntegrableOn (fun x => Real.exp (-testPotential n t x)) (unitBall n) (volume0 n) := by
  have hφ : IsNormalizedSolution n ((n + 1 : ℝ) * t) (profile n t) :=
    normalizedPotential_isNormalizedSolution hn (coupling_pos n ht₀) (coupling_lt n ht₁)
  have hscale := topMeasure_restrict_const_mul hφ.2.1 (show (0 : ℝ) ≤ n + 1 by positivity)
  have hm : d0TopMeasure (testPotential n t) (unitBall n) = ENNReal.ofReal ((n + 1 : ℝ) ^ n) := by
    unfold testPotential
    rw [← Measure.restrict_apply_univ, hscale, Measure.smul_apply,
      hφ.d0TopMeasure_total_mass, smul_eq_mul, mul_one]
  obtain ⟨U, _, hBU, hdiff⟩ := (testPotential_admissible hn ht₀ ht₁).1
  have hcont := (hdiff.continuousOn.mono hBU).neg
  have hK : IsCompact (closedUnitBall n) := isCompact_closedBall _ _
  have hB : MeasurableSet (unitBall n) := Metric.isOpen_ball.measurableSet
  have hsubset : unitBall n ⊆ closedUnitBall n := Metric.ball_subset_closedBall
  have henergy := hcont.integrableOn_of_subset_isCompact hK hB hsubset
    (hm.symm ▸ ENNReal.ofReal_ne_top : d0TopMeasure (testPotential n t) (unitBall n) ≠ (⊤ : ℝ≥0∞))
  have hexp := (Real.continuous_exp.comp_continuousOn hcont).integrableOn_of_subset_isCompact
    hK hB hsubset (by rw [volume0_unitBall n (by omega)]; exact ENNReal.one_ne_top)
  exact ⟨hm, henergy, hexp⟩

private theorem energy_testPotential {n : ℕ} (hn : 2 ≤ n) {t : ℝ}
    (ht₀ : 0 < t) (ht₁ : t < 1) :
    smoothEnergy (testPotential n t) = (n + 1 : ℝ) ^ (n + 1) * smoothEnergy (profile n t) := by
  have hφ : IsNormalizedSolution n ((n + 1 : ℝ) * t) (profile n t) :=
    normalizedPotential_isNormalizedSolution hn (coupling_pos n ht₀) (coupling_lt n ht₁)
  exact smoothEnergy_const_mul hφ.2.1 (by positivity)

private theorem log_integral_testPotential {n : ℕ} (hn : 2 ≤ n) {t : ℝ}
    (ht₀ : 0 < t) (ht₁ : t < 1) :
    -Real.log (1 - t) ≤ t * logIntegral (testPotential n t) := by
  let φ := profile n t
  let γ : ℝ := (n + 1 : ℝ) * t
  let p : ℝ := t⁻¹
  let f : E n → ℝ := fun x => Real.exp (-γ * φ x)
  let F : E n → ℝ := fun x => Real.exp (-testPotential n t x)
  let : NeZero n := ⟨by omega⟩
  have hp : 1 ≤ p := by dsimp [p]; exact (one_le_inv₀ ht₀).mpr ht₁.le
  have hφ : IsNormalizedSolution n γ φ :=
    normalizedPotential_isNormalizedSolution hn (coupling_pos n ht₀) (coupling_lt n ht₁)
  have hF : (fun y : ℝ => y ^ p) ∘ f = F := by
    funext x
    dsimp [f, F, γ, p, testPotential, φ]
    rw [← Real.exp_mul]
    congr 1
    field_simp
  have hfInt : IntegrableOn f (unitBall n) (volume0 n) := hφ.exponential_integrableOn
  have hFInt : IntegrableOn F (unitBall n) (volume0 n) :=
    (testPotential_finite_energy hn ht₀ ht₁).2.2
  have h := (convexOn_rpow hp).map_integral_le
    (μ := (volume0 n).restrict (unitBall n))
    (Real.continuous_rpow_const (le_trans zero_le_one hp)).continuousOn isClosed_Ici
    (Eventually.of_forall fun x => (Real.exp_pos (-γ * φ x)).le) hfInt
    (hF ▸ hFInt : Integrable ((fun y : ℝ => y ^ p) ∘ f) ((volume0 n).restrict (unitBall n)))
  change (∫ x in unitBall n, f x ∂volume0 n) ^ p ≤
    ∫ x in unitBall n, ((fun y : ℝ => y ^ p) ∘ f) x ∂volume0 n at h
  rw [hF, show (∫ x in unitBall n, f x ∂volume0 n) = (1 - t)⁻¹ from
    subcritical_integral_profile hn ht₀ ht₁] at h
  have hleft : 0 < ((1 - t)⁻¹ : ℝ) ^ p := Real.rpow_pos_of_pos (by positivity) _
  have hlog := Real.log_le_log hleft h
  rw [Real.log_rpow (by positivity), Real.log_inv] at hlog
  change p * (-Real.log (1 - t)) ≤ logIntegral (testPotential n t) at hlog
  have hmul := mul_le_mul_of_nonneg_left hlog ht₀.le
  rwa [← mul_assoc, show t * p = 1 by exact mul_inv_cancel₀ ht₀.ne', one_mul] at hmul

/-- On the smooth radial tests, the critical deficit dominates the
subcritical radial value that converges to the harmonic number. -/
theorem radialValue_le_test_deficit {n : ℕ} (hn : 2 ≤ n) {t : ℝ}
    (ht₀ : 0 < t) (ht₁ : t < 1) :
    radialValue n t ≤
      logIntegral (testPotential n t) -
        energyCoefficient n * smoothEnergy (testPotential n t) := by
  rw [energy_testPotential hn ht₀ ht₁, energyCoefficient,
    ← mul_assoc, inv_mul_cancel₀ (by positivity : (n + 1 : ℝ) ^ (n + 1) ≠ 0), one_mul]
  have hlog := log_integral_testPotential hn ht₀ ht₁
  have hen := energy_profile hn ht₀ ht₁
  have hrad := radialValue_eq_integral n ht₀.le ht₁
  have hnonneg : 0 ≤ radialValue n t := by
    rw [hrad]
    apply intervalIntegral.integral_nonneg zero_le_one
    intro x hx
    have htX : t * x ≤ t := by simpa using mul_le_mul_of_nonneg_left hx.2 ht₀.le
    exact div_nonneg (mul_nonneg ht₀.le (sub_nonneg.mpr (pow_le_one₀ hx.1 hx.2)))
      (by linarith)
  apply (le_of_mul_le_mul_left _ ht₀)
  nlinarith [mul_nonneg (sub_nonneg.mpr ht₁.le) hnonneg]

private theorem eventually_subcritical :
    ∀ᶠ t : ℝ in 𝓝[<] (1 : ℝ), 0 < t ∧ t < 1 := by
  filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num)),
    self_mem_nhdsWithin (a := (1 : ℝ)) (s := Iio 1)] with t h₀ h₁
  exact ⟨h₀, h₁⟩

theorem tendsto_energy_testPotential {n : ℕ} (hn : 2 ≤ n) :
    Tendsto (fun t => smoothEnergy (testPotential n t)) (𝓝[<] (1 : ℝ)) atTop := by
  have h1t : Tendsto (fun t : ℝ => 1 - t) (𝓝[<] (1 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, eventually_subcritical.mono fun t ht => sub_pos.mpr ht.2⟩
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub (tendsto_id.mono_left
      (nhdsWithin_le_nhds : 𝓝[<] (1 : ℝ) ≤ 𝓝 (1 : ℝ)))
  have hlog : Tendsto (fun t : ℝ => -Real.log (1 - t)) (𝓝[<] (1 : ℝ)) atTop :=
    tendsto_neg_atBot_atTop.comp (Real.tendsto_log_nhdsGT_zero.comp h1t)
  have hsub : Tendsto (fun t : ℝ => -Real.log (1 - t) - radialValue n t)
      (𝓝[<] (1 : ℝ)) atTop :=
    hlog.atTop_add (tendsto_radialValue n).neg
  have henergy : Tendsto (fun t => t * smoothEnergy (profile n t))
      (𝓝[<] (1 : ℝ)) atTop :=
    hsub.congr' (eventually_subcritical.mono fun t ht => (energy_profile hn ht.1 ht.2).symm)
  have hprofile : Tendsto (fun t => smoothEnergy (profile n t)) (𝓝[<] (1 : ℝ)) atTop := by
    apply tendsto_atTop.mpr
    intro A
    filter_upwards [eventually_subcritical, (tendsto_atTop.mp henergy) (max A 0)] with t ht hA
    have hE : 0 ≤ smoothEnergy (profile n t) := by
      have h0 := (le_max_right A 0).trans hA
      exact nonneg_of_mul_nonneg_right h0 ht.1
    exact (le_max_left A 0).trans (hA.trans
      (by simpa using mul_le_mul_of_nonneg_right ht.2.le hE))
  exact (hprofile.const_mul_atTop (by positivity : 0 < (n + 1 : ℝ) ^ (n + 1))).congr'
    (eventually_subcritical.mono fun _ ht => (energy_testPotential hn ht.1 ht.2).symm)

/-- Any bound with the stated coefficient, even on these smooth tests alone,
needs an additive constant at least the harmonic number. -/
theorem harmonicConstant_le_of_bound {n : ℕ} (hn : 2 ≤ n) {C : ℝ}
    (hbound : ∀ t ∈ Ioo (0 : ℝ) 1,
      logIntegral (testPotential n t) ≤ energyCoefficient n * smoothEnergy (testPotential n t) + C) :
    harmonicConstant n ≤ C := by
  apply le_of_tendsto_of_tendsto (tendsto_radialValue n) tendsto_const_nhds
  filter_upwards [eventually_subcritical] with t ht
  linarith [radialValue_le_test_deficit hn ht.1 ht.2, hbound t ht]

/-- A strictly smaller energy coefficient cannot give any finite additive
bound, already on the smooth radial tests. -/
theorem exists_test_violating_bound {n : ℕ} (hn : 2 ≤ n)
    {c : ℝ} (hc : c < energyCoefficient n) (C : ℝ) :
    ∃ t ∈ Ioo (0 : ℝ) 1,
      c * smoothEnergy (testPotential n t) + C < logIntegral (testPotential n t) := by
  have hE := (tendsto_energy_testPotential hn).const_mul_atTop (sub_pos.mpr hc)
  have hsum := hE.atTop_add (tendsto_radialValue n)
  have hex : ∀ᶠ t : ℝ in 𝓝[<] (1 : ℝ),
      0 < t ∧ t < 1 ∧ C < (energyCoefficient n - c) * smoothEnergy (testPotential n t) +
        radialValue n t := by
    filter_upwards [eventually_subcritical, hsum.eventually (eventually_gt_atTop C)] with t ht hC
    exact ⟨ht.1, ht.2, hC⟩
  obtain ⟨t, ht₀, ht₁, hC⟩ := hex.exists
  refine ⟨t, ⟨ht₀, ht₁⟩, ?_⟩
  linarith [radialValue_le_test_deficit hn ht₀ ht₁]

#print axioms energy_profile
#print axioms testPotential_admissible
#print axioms testPotential_finite_energy
#print axioms harmonicConstant_le_of_bound
#print axioms exists_test_violating_bound

end KEBall.MoserTrudinger
