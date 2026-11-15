import KEBall.BrezisMerleDiscWeak
import KEBall.CegrellFiberCurvature

/-!
# From an energy inequality on the fibers to a mass inequality on the ball
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Metric Set TopologicalSpace
open scoped ContDiff ENNReal Laplacian Topology

namespace KEBall.BrezisMerle

open BedfordTaylor Cegrell
open PshLines.FirstPass (ComplexModel)

private theorem lintegral_productBall_slices {n : ℕ} {v : ComplexModel (n + 1) → ℝ}
    (hv : ContinuousOn v (complexProductBall n 1)) :
    (∫⁻ x in complexProductBall n 1, ENNReal.ofReal (Real.exp (-v x))) =
      ∫⁻ w in unitBall 1, ∫⁻ z in complexUnitBall n,
        ENNReal.ofReal (Real.exp (-complexFiberSlice v (complexCoordinates 1 w) z)) := by
  let e := complexProductCoordinates n 1
  let c := complexCoordinates 1
  let A := (complexUnitBall n : Set (ComplexModel n))
  let B : Set (ComplexModel 1) := ball 0 1
  let P := (complexProductBall n 1 : Set (ComplexModel (n + 1)))
  let f (p : ComplexModel n × ComplexModel 1) := ENNReal.ofReal (Real.exp (-v (e.symm p)))
  have hA : MeasurableSet A := measurableSet_ball
  have hB : MeasurableSet B := measurableSet_ball
  have hP : e ⁻¹' (A ×ˢ B) = P := rfl
  have hf : ContinuousOn f (A ×ˢ B) := ENNReal.continuous_ofReal.comp_continuousOn
    (Real.continuous_exp.comp_continuousOn
      ((hv.comp e.symm.continuous.continuousOn (fun x hx => by
        change e (e.symm x) ∈ A ×ˢ B
        rwa [e.apply_symm_apply])).neg))
  have hf' : AEMeasurable f (((volume : Measure (ComplexModel n)).restrict A).prod
      ((volume : Measure (ComplexModel 1)).restrict B)) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact hf.aemeasurable (hA.prod hB)
  have he : MeasurePreserving e := measurePreserving_complexProductCoordinates n 1
  have hL := he.setLIntegral_comp_preimage_emb
    e.toHomeomorph.toMeasurableEquiv.measurableEmbedding f (A ×ˢ B)
  have hL' : (∫⁻ x in P, ENNReal.ofReal (Real.exp (-v x))) = ∫⁻ p in A ×ˢ B, f p := by
    simpa only [← hP, f, e.symm_apply_apply] using hL
  have hL'' : (∫⁻ p in A ×ˢ B, f p) = ∫⁻ w in B, ∫⁻ z in A, f (z, w) := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
    exact lintegral_prod_symm _ hf'
  have hcPre : c ⁻¹' B = unitBall 1 := by
    ext w
    simp only [B, unitBall, mem_preimage, mem_ball_zero_iff, c.norm_map]
  have hC := (complexCoordinates_measurePreserving 1).setLIntegral_comp_preimage_emb
    c.toHomeomorph.toMeasurableEquiv.measurableEmbedding (fun w => ∫⁻ z in A, f (z, w)) B
  rw [show (complexCoordinates 1) ⁻¹' B = unitBall 1 from hcPre] at hC
  exact hL'.trans (hL''.trans hC.symm)

set_option maxHeartbeats 900000 in
/-- The lower-dimensional energy bound gives the higher-dimensional mass
bound by subextension, slicing, and the weak disk estimate. -/
theorem lintegral_exp_ball_le_of_fiberEnergyBound {n : ℕ} (hn : 0 < n)
    {a : ℝ} (ha : 0 < a) {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (hFiber : ∀ (q : ComplexModel n → ℝ) (hq : IsE0 (complexUnitBall n) q),
      (∫⁻ z in complexUnitBall n, ENNReal.ofReal (Real.exp (-q z))) ≤
        C * ENNReal.ofReal (Real.exp (a * (boundedEnergy hq).toReal / (n + 1 : ℝ))))
    {R : ℝ} (hR : 0 < R) (hR₁ : R < 1)
    {u : ComplexModel (n + 1) → ℝ} (hu : IsE0 (ballDomain 0 R) u)
    (huSmooth : ContDiff ℝ 2 u) (hu₀ : ∀ x ∈ ball 0 R, u x ≤ 0)
    (huBoundary : ∀ x ∈ sphere 0 R, u x = 0)
    {t : ℝ} (ht₀ : 0 < t) (ht₁ : t < 1)
    (hMass : ENNReal.ofReal (a / (n + 1 : ℝ)) * topMeasure hu.locallyBoundedPsh univ ≤ ENNReal.ofReal t) :
    (∫⁻ x in ball 0 R, ENNReal.ofReal (Real.exp (-u x))) ≤
      C * ENNReal.ofReal (4 * Real.pi / (1 - t)) := by
  obtain ⟨v, hv, hvu, hvCont, μ, _, hμ, hWeak, M, hM, hSlice⟩ :=
    exists_productBall_subextension_withFiberCurvature hn hR hR₁ hu huSmooth hu₀ huBoundary
  let E₀ := bedfordTaylorFiberEnergy (R := 1) (ρ := 1) hv.locallyBoundedPsh
  let F (w : E 1) := a * E₀ w
  let ν := ENNReal.ofReal a • μ
  have hZero (w : E 1) (hw : w ∉ unitBall 1) : F w = 0 := by
    have h := fun h : ‖complexCoordinates 1 w‖ < 1 =>
      hw (mem_ball_zero_iff.mpr (by simpa only [LinearIsometryEquiv.norm_map] using h))
    change a * bedfordTaylorFiberEnergy (R := 1) (ρ := 1) hv.locallyBoundedPsh w = 0
    rw [bedfordTaylorFiberEnergy, dif_neg h, mul_zero]
  have hBound (w : E 1) (hw : w ∈ unitBall 1) : -(a * M * (1 - ‖w‖ ^ 2)) ≤ F w ∧ F w ≤ 0 := by
    obtain ⟨hq, heq, hlo, hhi⟩ := hSlice w hw
    refine ⟨?_, mul_nonpos_of_nonneg_of_nonpos ha.le hhi⟩
    simpa only [mul_neg, ← mul_assoc] using mul_le_mul_of_nonneg_left hlo ha.le
  have hν : ν univ ≤ ENNReal.ofReal t := by
    change (ENNReal.ofReal a • μ) univ ≤ _
    rw [Measure.smul_apply, smul_eq_mul]
    refine (mul_le_mul_right hμ _).trans ?_
    rw [← mul_assoc, ← ENNReal.ofReal_mul ha.le, ← div_eq_mul_inv]
    exact hMass
  have hWeak' (φ : E 1 → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
      (hs : tsupport φ ⊆ unitBall 1) :
      Integrable (fun w => F w * Δ φ w) ∧ (∫ w, F w * Δ φ w) = (4 * Real.pi) * ∫ w, φ w ∂ν := by
    obtain ⟨hI, hE⟩ := hWeak φ hφ hc hs
    refine ⟨by simpa only [F, E₀, mul_assoc] using hI.const_mul a, ?_⟩
    change (∫ w, (a * E₀ w) * Δ φ w) = (4 * Real.pi) * ∫ w, φ w ∂(ENNReal.ofReal a • μ)
    simp_rw [mul_assoc, integral_const_mul]
    rw [show (∫ w, E₀ w * Δ φ w) = (4 * Real.pi) * ∫ w, φ w ∂μ from hE,
      integral_smul_measure, ENNReal.toReal_ofReal ha.le, smul_eq_mul]
    ring
  have hDisc := lintegral_exp_le_of_weakDiscMass hWeak' hZero (mul_nonneg ha.le hM) hBound ht₀ ht₁ hν
  have hRP : ball (0 : ComplexModel (n + 1)) R ⊆ complexProductBall n 1 := by
    intro x hx
    have hx₁ : ‖x‖ < 1 := (mem_ball_zero_iff.mp hx).trans hR₁
    exact mem_complexProductBall.mpr
      ⟨(norm_fst_complexProductCoordinates_le x).trans_lt hx₁,
        (norm_snd_complexProductCoordinates_le x).trans_lt hx₁⟩
  calc
    _ ≤ ∫⁻ x in ball (0 : ComplexModel (n + 1)) R, ENNReal.ofReal (Real.exp (-v x)) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
      exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (neg_le_neg (hvu x hx)))
    _ ≤ ∫⁻ x in complexProductBall n 1, ENNReal.ofReal (Real.exp (-v x)) := lintegral_mono_set hRP
    _ = ∫⁻ w in unitBall 1, ∫⁻ z in complexUnitBall n,
        ENNReal.ofReal (Real.exp (-complexFiberSlice v (complexCoordinates 1 w) z)) :=
      lintegral_productBall_slices hvCont
    _ ≤ ∫⁻ w in unitBall 1, C * ENNReal.ofReal (Real.exp (-F w)) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem (show MeasurableSet (unitBall 1) from measurableSet_ball)] with w hw
      obtain ⟨hq, heq, _, _⟩ := hSlice w hw
      have he : -F w = a * (boundedEnergy hq).toReal / (n + 1 : ℝ) := by
        change -(a * E₀ w) = _
        rw [show E₀ w = -(boundedEnergy hq).toReal / (n + 1 : ℝ) from heq]
        ring
      simpa only [he] using hFiber _ hq
    _ = C * ∫⁻ w in unitBall 1, ENNReal.ofReal (Real.exp (-F w)) := lintegral_const_mul' _ _ hC
    _ ≤ _ := mul_le_mul_right hDisc _

end KEBall.BrezisMerle
