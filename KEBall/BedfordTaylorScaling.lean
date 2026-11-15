import KEBall.BedfordTaylorMonotone
import KEBall.BedfordTaylorSmoothCriterion

/-!
# Positive scaling of potentials and their Monge–Ampère measures
-/

set_option autoImplicit false

open Filter MeasureTheory Set TopologicalSpace
open scoped ComplexOrder ContDiff Distributions ENNReal Topology

namespace KEBall.BedfordTaylor

open PshLines
open PshLines.FirstPass (ComplexModel)
open PshLines.FirstPass.MongeAmpere
  (IsLocallyBoundedPshOn IsSmoothPshOn smoothDensity smoothMeasure RelativelyCompactIn)
open PshLines.Regularization.HolomorphicPullback (exists_decreasingMollifierApproximation)

variable {n : ℕ} {Ω : Opens (ComplexModel n)}

theorem continuous_ereal_const_mul (c : ℝ) :
    Continuous (fun a : EReal => (c : EReal) * a) := by
  rw [continuous_iff_continuousAt]
  intro a
  exact EReal.Tendsto.const_mul tendsto_id (Or.inl (EReal.coe_ne_bot c))
    (Or.inl (EReal.coe_ne_top c))

/-- Positive multiplication preserves the disc submean criterion, including
potentials with poles. -/
theorem plurisubharmonicOn_const_mul {u : ComplexModel n → EReal}
    (hu : PlurisubharmonicOn u Ω) {c : ℝ} (hc : 0 < c) :
    PlurisubharmonicOn (fun x => (c : EReal) * u x) Ω := by
  have hcE : 0 ≤ (c : EReal) := by exact_mod_cast hc.le
  have hd := hu.discPshOn
  have hD : DiscPshOn (fun x => (c : EReal) * u x) Ω := by
    refine ⟨fun x hx => (EReal.mul_ne_top (c : EReal) (u x)).mpr
      ⟨Or.inl (EReal.coe_ne_bot c), Or.inl hcE, Or.inl (EReal.coe_ne_top c), Or.inr (hd.ne_top x hx)⟩,
      (continuous_ereal_const_mul c).comp_upperSemicontinuousOn
        hd.upperSemicontinuousOn (fun _ _ hab => mul_le_mul_of_nonneg_left hab hcE), ?_⟩
    intro x v r hr hdisc C hbound
    have hC (y : ComplexModel n) (hy : y ∈ affineClosedDisc x v r) :
        u y ≤ ((C / c : ℝ) : EReal) := by
      by_cases hb : u y = ⊥
      · rw [hb]
        exact bot_le
      · have hfin : u y ≠ ⊤ := hd.ne_top y (hdisc hy)
        lift u y to ℝ using ⟨hfin, hb⟩ with z hz
        have hzle := hbound y hy
        rw [← hz, ← EReal.coe_mul, EReal.coe_le_coe_iff] at hzle
        rw [EReal.coe_le_coe_iff]
        exact (le_div_iff₀ hc).mpr (by simpa only [mul_comm] using hzle)
    have hid (b : EReal) : ((C : EReal) - (c : EReal) * b).toENNReal =
        ENNReal.ofReal c * (((C / c : ℝ) : EReal) - b).toENNReal := by
      rw [← EReal.real_coe_toENNReal c, ← EReal.toENNReal_mul hcE,
        EReal.mul_sub_of_nonneg_of_ne_top hcE (EReal.coe_ne_top c),
        ← EReal.coe_mul, show c * (C / c) = C by field_simp [hc.ne']]
    have he : circleDeficit (fun y => (c : EReal) * u y) x v r C =
        ENNReal.ofReal c * circleDeficit u x v r (C / c) := by
      unfold circleDeficit
      simp_rw [hid]
      exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    rw [he, hid, ← mul_assoc, mul_comm (ENNReal.ofReal (2 * Real.pi)), mul_assoc]
    exact mul_le_mul_right (hd.submean x v r hr hdisc (C / c) hC) _
  exact hD.plurisubharmonicOn Ω.isOpen

theorem locallyBoundedPsh_const_mul {u : ComplexModel n → ℝ} (hu : IsLocallyBoundedPshOn Ω u)
    {c : ℝ} (hc : 0 < c) : IsLocallyBoundedPshOn Ω (fun x => c * u x) := by
  refine ⟨?_, ?_⟩
  · simp only [EReal.coe_mul]
    exact plurisubharmonicOn_const_mul hu.1 hc
  · intro x hx
    obtain ⟨V, hxV, hVΩ, C, hC⟩ := hu.2 x hx
    refine ⟨V, hxV, hVΩ, c * C, fun y hy => ?_⟩
    rw [abs_mul, abs_of_pos hc]
    exact mul_le_mul_of_nonneg_left (hC y hy) hc.le

theorem smoothPsh_const_mul {u : ComplexModel n → ℝ} (hu : IsSmoothPshOn Ω u)
    {c : ℝ} (hc : 0 < c) : IsSmoothPshOn Ω (fun x => c * u x) := by
  apply isSmoothPshOn_of_coordinateHessian (contDiffOn_const.mul hu.1)
  intro x hx
  change (PshLines.FirstPass.MongeAmpere.complexHessian (c • u) x).PosSemidef
  rw [PshLines.FirstPass.MongeAmpere.complexHessian_smul
    ((hu.1.contDiffAt (Ω.isOpen.mem_nhds hx)).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) c]
  exact (hu.2.2 x hx).smul (by exact_mod_cast hc.le)

private theorem smoothMeasure_const_mul {u : ComplexModel n → ℝ}
    (hu : IsSmoothPshOn Ω u) {c : ℝ} (hc : 0 < c) :
    smoothMeasure Ω (fun x => c * u x) (smoothPsh_const_mul hu hc) =
      ENNReal.ofReal (c ^ n) • smoothMeasure Ω u hu := by
  unfold smoothMeasure
  rw [← withDensity_smul' _ _ ENNReal.ofReal_ne_top]
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem Ω.isOpen.measurableSet] with x hx
  change ENNReal.ofReal (smoothDensity (c • u) x) =
    ENNReal.ofReal (c ^ n) * ENNReal.ofReal (smoothDensity u x)
  rw [← ENNReal.ofReal_mul (pow_nonneg hc.le n), smoothDensity, smoothDensity,
    PshLines.FirstPass.MongeAmpere.complexHessian_smul
      ((hu.1.contDiffAt (Ω.isOpen.mem_nhds hx)).of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) c,
    Matrix.det_smul, Fintype.card_fin]
  simp only [← Complex.ofReal_pow, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  ring_nf

/-- Scaling a locally bounded potential by a positive constant scales
its top measure by the dimension-th power of that constant. -/
theorem topMeasure_const_mul {u : ComplexModel n → ℝ}
    (hu : IsLocallyBoundedPshOn Ω u) {c : ℝ} (hc : 0 < c) :
    topMeasure (locallyBoundedPsh_const_mul hu hc) =
      ENNReal.ofReal (c ^ n) • topMeasure hu := by
  apply ambientMeasure_eq_of_smooth_test (topMeasure_compl (locallyBoundedPsh_const_mul hu hc))
  · rw [Measure.smul_apply, topMeasure_compl hu, smul_eq_mul, mul_zero]
  · intro K hK hKΩ
    exact topMeasure_finite_on_compact _ hK hKΩ
  · intro K hK hKΩ
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (topMeasure_finite_on_compact hu hK hKΩ)
  · intro φ
    obtain ⟨V, hVo, hφV, hVΩ, hVc⟩ :=
      exists_open_between_and_isCompact_closure φ.hasCompactSupport Ω.isOpen φ.tsupport_subset
    let W : Opens (ComplexModel n) := ⟨V, hVo⟩
    have hrel : RelativelyCompactIn W Ω := ⟨hVc, hVΩ⟩
    rw [integral_smul_measure, ENNReal.toReal_ofReal (pow_nonneg hc.le _), smul_eq_mul]
    obtain ⟨p, hp⟩ := exists_decreasingMollifierApproximation hu hrel
    let hs := fun j => smoothPsh_const_mul (hp.1 j) hc
    have hanti (x : ComplexModel n) (hx : x ∈ W) : Antitone (fun j => c * p j x) :=
      fun _ _ hm => mul_le_mul_of_nonneg_left (hp.2.1 x hx hm) hc.le
    have hlim (x : ComplexModel n) (hx : x ∈ W) :
        Tendsto (fun j => c * p j x) atTop (𝓝 (c * u x)) := (hp.2.2 x hx).const_mul c
    have h₁ := (isLocalBedfordTaylorMeasure_top (locallyBoundedPsh_const_mul hu hc)).2.2.2 W hrel
    have h₂ := (isLocalBedfordTaylorMeasure_top hu).2.2.2 W hrel
    have h₁' := h₁.2 (fun j x => c * p j x) ⟨hs, hanti, hlim⟩
      φ φ.continuous φ.hasCompactSupport hφV
    have h₂' := (h₂.2 p hp φ φ.continuous φ.hasCompactSupport hφV).const_mul (c ^ n)
    have heq (j : ℕ) : (∫ x, φ x ∂smoothMeasure W (p j) (hp.1 j)) * c ^ n =
        ∫ x, φ x ∂smoothMeasure W (fun x => c * p j x) (hs j) := by
      rw [smoothMeasure_const_mul (hp.1 j) hc, integral_smul_measure,
        ENNReal.toReal_ofReal (pow_nonneg hc.le _), smul_eq_mul, mul_comm]
    exact tendsto_nhds_unique h₁' (h₂'.congr fun j => by simpa only [mul_comm] using heq j)

end KEBall.BedfordTaylor
