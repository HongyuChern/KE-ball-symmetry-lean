import KEBall.BrezisMerleDiscGreen
import KEBall.BrezisMerleLogKernel

/-!
# The smooth Brezis–Merle estimate on the unit disc

The smooth logarithmic test in Green's formula provides a lower bound
for the convolution by the regularized Laplacian. Jensen and Tonelli
bound its exponential uniformly, and Fatou gives the disc estimate.
-/

set_option autoImplicit false

open Filter MeasureTheory Metric Set
open scoped ContDiff ENNReal Laplacian Topology

namespace KEBall.BrezisMerle

private noncomputable def discCoordinates : E 1 ≃ₗᵢ[ℝ] ℂ :=
  Complex.orthonormalBasisOneI.repr.symm

set_option backward.isDefEq.respectTransparency false in
private theorem lintegral_exp_regularizedLog_le {a : E 1} (ha : a ∈ unitBall 1)
    {ε t : ℝ} (hε : 0 < ε) (ht₀ : 0 ≤ t) (ht₁ : t < 1) :
    (∫⁻ z in unitBall 1, ENNReal.ofReal (Real.exp (-t * regularizedLog ε z a)) ∂volume) ≤
      ENNReal.ofReal (4 * Real.pi / (1 - t)) := by
  let e := discCoordinates
  have hB : e ⁻¹' ball (0 : ℂ) 1 = unitBall 1 := by
    rw [e.preimage_ball, e.symm.map_zero]
    rfl
  have hae : ∀ᵐ z ∂(volume : Measure (E 1)).restrict (unitBall 1), z ≠ a := by
    apply ae_restrict_of_ae
    rw [ae_iff]
    simp
  have ht : ∀ᵐ z ∂(volume : Measure (E 1)).restrict (unitBall 1),
      2 * Real.log (‖e z - e a‖ / 2) ≤ regularizedLog ε z a := by
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_ball, hae] with z hz hza
    have hd : 0 < ‖a - z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hza.symm)
    have hb : ‖a - z‖ ≤ 2 := by
      refine (norm_sub_le _ _).trans ?_
      have h₁ : ‖a‖ < 1 := mem_ball_zero_iff.mp ha
      have h₂ : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
      linarith
    have hlog : 2 * Real.log (‖a - z‖ / 2) = Real.log (‖a - z‖ ^ 2 / 4) := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, ← div_pow, Real.log_pow]
      norm_num
    rw [← e.map_sub, e.norm_map, norm_sub_rev, hlog, regularizedLog,
      ← Real.log_div (by positivity) (by positivity)]
    apply Real.log_le_log (by positivity)
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 4) (by positivity)).mpr
    nlinarith [mul_nonneg (show 0 ≤ 4 - ‖a - z‖ ^ 2 by nlinarith) hε.le]
  calc
    _ ≤ ∫⁻ z in unitBall 1, ENNReal.ofReal (Real.exp (-t * (2 * Real.log (‖e z - e a‖ / 2)))) ∂volume := by
      apply lintegral_mono_ae
      filter_upwards [ht] with z hz
      exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonpos_left hz (neg_nonpos.mpr ht₀)))
    _ = ∫⁻ z in ball (0 : ℂ) 1, ENNReal.ofReal (Real.exp (-t * (2 * Real.log (‖z - e a‖ / 2)))) ∂volume := by
      rw [← hB]
      exact (e.measurePreserving.restrict_preimage
        (measurableSet_ball (x := (0 : ℂ)) (ε := 1))).lintegral_comp_emb
        e.toMeasurableEquiv.measurableEmbedding
          (fun z => ENNReal.ofReal (Real.exp (-t * (2 * Real.log (‖z - e a‖ / 2)))))
    _ ≤ _ := lintegral_exp_logKernel_le (by rwa [← mem_preimage, hB]) ht₁

/-- The total mass in the `ddᶜ = (i / 2π) ∂∂̄` normalization. -/
noncomputable def discMass (u : E 1 → ℝ) : ℝ :=
  (∫ x in unitBall 1, Δ u x) / (4 * Real.pi)

private theorem laplacian_div_mass_integrable {u : E 1 → ℝ} (hu : ContDiff ℝ 2 u)
    (t : ℝ) : IntegrableOn (fun x => Δ u x / (4 * Real.pi * t)) (unitBall 1) :=
  ((continuous_laplacian hu).div_const _ |>.continuousOn.integrableOn_compact
    (isCompact_closedBall (0 : E 1) 1)).mono_set ball_subset_closedBall

set_option maxHeartbeats 800000 in
/-- The smooth disk estimate with a uniform lower bound on the boundary. -/
theorem lintegral_exp_addBoundary_le_of_discMass {u : E 1 → ℝ} (hu : ContDiff ℝ 2 u)
    {δ : ℝ} (hBoundary : ∀ x ∈ unitSphere 1, -δ ≤ u x)
    (hΔ : ∀ x ∈ unitBall 1, 0 ≤ Δ u x)
    (ht₀ : 0 < discMass u) (ht₁ : discMass u < 1) :
    (∫⁻ z in unitBall 1, ENNReal.ofReal (Real.exp (-(u z + δ))) ∂volume) ≤
      ENNReal.ofReal (4 * Real.pi / (1 - discMass u)) := by
  let t := discMass u
  let ρ : E 1 → ℝ := fun x => Δ u x / (4 * Real.pi * t)
  let ν : Measure (E 1) := volume.restrict (unitBall 1)
  let μ : Measure (E 1) := ν.withDensity (fun x => ENNReal.ofReal (ρ x))
  have ht : 0 < t := ht₀
  have hρ : Continuous ρ := (continuous_laplacian hu).div_const _
  have hν : ∀ᵐ x ∂ν, x ∈ unitBall 1 := ae_restrict_mem measurableSet_ball
  have hρ₀ : 0 ≤ᵐ[ν] ρ := hν.mono fun x hx => div_nonneg (hΔ x hx) (by positivity)
  have hρi : Integrable ρ ν := laplacian_div_mass_integrable hu t
  have hρmass : (∫ x, ρ x ∂ν) = 1 := by
    change (∫ x in unitBall 1, Δ u x / (4 * Real.pi * t)) = 1
    rw [integral_div]
    have heq : (∫ x in unitBall 1, Δ u x) = (4 * Real.pi) * t := by
      dsimp only [t, discMass]
      have hp := Real.pi_pos
      field_simp
    rw [heq, div_self (by positivity)]
  have : IsProbabilityMeasure μ := ⟨by
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hρi hρ₀, hρmass, ENNReal.ofReal_one]⟩
  have hμ : ∀ᵐ x ∂μ, x ∈ unitBall 1 :=
    (withDensity_absolutelyContinuous ν _).ae_le hν
  let ε : ℕ → ℝ := fun k => ((k : ℝ) + 1)⁻¹
  have hε (k : ℕ) : 0 < ε k := inv_pos.mpr (by positivity : 0 < (k : ℝ) + 1)
  have hε₀ : Tendsto ε atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ 1 (tendsto_natCast_atTop_atTop (R := ℝ)))
  let v (k : ℕ) (z : E 1) : ℝ :=
    ∫ x in unitBall 1, (Δ (regularizedDiscGreen (ε k) z) x / (4 * Real.pi)) * (u x + δ)
  have hv (k : ℕ) : Measurable (v k) := by
    have h : Measurable (fun p : E 1 × E 1 =>
        (Δ (regularizedDiscGreen (ε k) p.1) p.2 / (4 * Real.pi)) * (u p.2 + δ)) :=
      ((measurable_laplacian_regularizedDiscGreen (hε k)).div_const _).mul
        ((hu.continuous.measurable.comp measurable_snd).add_const δ)
    exact h.stronglyMeasurable.integral_prod_right' (ν := ν) |>.measurable
  have hbound (k : ℕ) :
      (∫⁻ z in unitBall 1, ENNReal.ofReal (Real.exp (-v k z)) ∂volume) ≤
        ENNReal.ofReal (4 * Real.pi / (1 - t)) := by
    let L := regularizedLog (ε k)
    have hL : Continuous (Function.uncurry L) := by
      have hk := hε k
      have h : Continuous (fun p : E 1 × E 1 => ‖p.2 - p.1‖ ^ 2 + ε k) := by fun_prop
      exact (h.log fun p => ne_of_gt (by positivity)).sub continuous_const
    have hLρ (z : E 1) : Integrable (fun x => ρ x * L z x) ν := by
      have h : Continuous (fun x => ρ x * L z x) :=
        hρ.mul (regularizedLog_smooth (hε k) z).continuous
      exact (h.continuousOn.integrableOn_compact
        (isCompact_closedBall (0 : E 1) 1)).mono_set ball_subset_closedBall
    have hA (z : E 1) : (fun x => (ENNReal.ofReal (ρ x)).toReal • L z x) =ᵐ[ν]
        fun x => ρ x * L z x := hρ₀.mono fun x hx => by
      dsimp only
      rw [ENNReal.toReal_ofReal hx, smul_eq_mul]
    have hLi (z : E 1) : Integrable (L z) μ := by
      change Integrable (L z) (ν.withDensity fun x => ENNReal.ofReal (ρ x))
      rw [integrable_withDensity_iff_integrable_smul' (μ := ν) (g := L z)
        hρ.measurable.ennreal_ofReal (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
      exact (hLρ z).congr (hA z).symm
    have hdom (z : E 1) (hz : z ∈ unitBall 1) : (∫ a, L z a ∂μ) ≤ v k z / t := by
      let G := regularizedDiscGreen (ε k) z
      have hg := integral_regularizedDiscGreen_mul_laplacian_le hu (hε k) hBoundary
        (ball_subset_closedBall hz)
      have hLG : (∫ x in unitBall 1, L z x * Δ u x) ≤ ∫ x in unitBall 1, G x * Δ u x := by
        have hI (f : E 1 → ℝ) (hf : Continuous f) :
            IntegrableOn (fun x => f x * Δ u x) (unitBall 1) :=
          ((hf.mul (continuous_laplacian hu)).continuousOn.integrableOn_compact
            (isCompact_closedBall (0 : E 1) 1)).mono_set ball_subset_closedBall
        apply integral_mono_ae (hI _ ((regularizedLog_smooth (hε k) z).continuous))
          (hI _ ((regularizedDiscGreen_contDiff (hε k) z).continuous))
        filter_upwards [hν] with x hx
        exact mul_le_mul_of_nonneg_right
          (regularizedLog_le_regularizedDiscGreen (hε k) (ball_subset_closedBall hz) (ball_subset_closedBall hx))
          (hΔ x hx)
      rw [integral_withDensity_eq_integral_toReal_smul hρ.measurable.ennreal_ofReal
        (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top), integral_congr_ae (hA z)]
      have hleft : (∫ x, ρ x * L z x ∂ν) =
          (∫ x in unitBall 1, L z x * Δ u x) / (4 * Real.pi * t) := by
        rw [← integral_div]
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by dsimp [ρ]; ring
      rw [hleft]
      have hright : v k z / t = (∫ x in unitBall 1, (u x + δ) * Δ G x) / (4 * Real.pi * t) := by
        have hEq (x : E 1) : (Δ G x / (4 * Real.pi)) * (u x + δ) =
            ((u x + δ) * Δ G x) / (4 * Real.pi) := by ring
        change (∫ x in unitBall 1, (Δ G x / (4 * Real.pi)) * (u x + δ)) / t = _
        simp_rw [hEq, integral_div]
        ring
      rw [hright]
      exact div_le_div_of_nonneg_right (hLG.trans hg) (by positivity)
    have h := lintegral_exp_le_of_kernel (ν := volume) (μ := μ) (s := unitBall 1) measurableSet_ball
      hL.measurable ht.le (fun z _ => hLi z) hdom
      (C := ENNReal.ofReal (4 * Real.pi / (1 - t))) (hμ.mono fun a ha =>
        lintegral_exp_regularizedLog_le ha (hε k) ht.le ht₁)
    have hcancel (z : E 1) : -t * (v k z / t) = -v k z := by field_simp
    simpa only [hcancel] using h
  let F (k : ℕ) (z : E 1) := ENNReal.ofReal (Real.exp (-v k z))
  have hF (k : ℕ) : Measurable (F k) := (Real.measurable_exp.comp (hv k).neg).ennreal_ofReal
  have hconv (z : E 1) (hz : z ∈ unitBall 1) :
      Tendsto (fun k => F k z) atTop (𝓝 (ENNReal.ofReal (Real.exp (-(u z + δ))))) := by
    exact (ENNReal.continuous_ofReal.tendsto _).comp
      ((Real.continuous_exp.tendsto _).comp
        (tendsto_integral_laplacian_regularizedDiscGreen (hu.continuous.add continuous_const) hz hε hε₀).neg)
  calc
    _ = ∫⁻ z in unitBall 1, liminf (fun k => F k z) atTop ∂volume := by
      apply lintegral_congr_ae
      filter_upwards [hν] with z hz
      exact (hconv z hz).liminf_eq.symm
    _ ≤ liminf (fun k => ∫⁻ z in unitBall 1, F k z ∂volume) atTop := lintegral_liminf_le hF
    _ ≤ _ := liminf_le_of_le (h := fun b hb => by
      obtain ⟨k, hk⟩ := hb.exists
      exact hk.trans (hbound k))

set_option linter.unusedVariables false in
/-- The smooth disk estimate for zero boundary data. -/
theorem lintegral_exp_le_of_discMass {u : E 1 → ℝ} (hu : ContDiff ℝ 2 u)
    (hneg : ∀ x ∈ closedUnitBall 1, u x ≤ 0) (hzero : ∀ x ∈ unitSphere 1, u x = 0)
    (hΔ : ∀ x ∈ unitBall 1, 0 ≤ Δ u x)
    (ht₀ : 0 < discMass u) (ht₁ : discMass u < 1) :
    (∫⁻ z in unitBall 1, ENNReal.ofReal (Real.exp (-u z)) ∂volume) ≤
      ENNReal.ofReal (4 * Real.pi / (1 - discMass u)) := by
  simpa only [add_zero] using lintegral_exp_addBoundary_le_of_discMass hu (δ := 0)
    (fun x hx => by rw [hzero x hx, neg_zero]) hΔ ht₀ ht₁

end KEBall.BrezisMerle
