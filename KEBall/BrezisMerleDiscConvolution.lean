import KEBall.BrezisMerleDiscMass
import PshLines.TranslationPairing
import Mathlib.MeasureTheory.Integral.Prod

/-!
# The Laplacian of a compactly mollified weak disk potential
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Metric Set
open scoped ContDiff Laplacian Topology

namespace KEBall.BrezisMerle

open PshLines (translationPairing)

theorem laplacian_translationPairing_disc {f k : E 1 → ℝ} (hf : LocallyIntegrable f volume)
    (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k) (z : E 1) :
    Δ (translationPairing volume f k) z = ∫ x, f x * Δ k (x - z) := by
  have hH (u : E 1 → ℝ) (x a b : E 1) :
      KEBall.realHessian u x a b = PshLines.realHessian u x a b :=
    (PshLines.realHessian_eq_fderiv u x a b).symm
  rw [laplacian_eq_realHessian_disc]
  simp only [hH, PshLines.realHessian_translationPairing hf hkc hk]
  rw [← integral_add (PshLines.integrable_translationPairing_realHessian hf hkc hk z _ _)
    (PshLines.integrable_translationPairing_realHessian hf hkc hk z _ _)]
  apply integral_congr_ae
  filter_upwards with x
  change f x * PshLines.realHessian k (x - z) (realDirection 0) (realDirection 0) +
    f x * PshLines.realHessian k (x - z) (imagDirection 0) (imagDirection 0) = _
  rw [laplacian_eq_realHessian_disc, hH, hH, mul_add]

theorem laplacian_comp_sub_right_disc {k : E 1 → ℝ} (hk : ContDiff ℝ 2 k) (z x : E 1) :
    Δ (fun y => k (y - z)) x = Δ k (x - z) := by
  have hH (u : E 1 → ℝ) (x a b : E 1) :
      KEBall.realHessian u x a b = PshLines.realHessian u x a b :=
    (PshLines.realHessian_eq_fderiv u x a b).symm
  have he (a : E 1) : PshLines.realHessian (fun y => k (y - z)) x a a =
      PshLines.realHessian k (x - z) a a := by
    have h := PshLines.realHessian_comp_affine hk (ContinuousLinearMap.id ℝ (E 1)) (-z) x a a
    simpa only [ContinuousLinearMap.id_apply, neg_add_eq_sub] using h
  simp only [laplacian_eq_realHessian_disc, hH, he]

/-- On balls where the translated test is supported in the unit disk,
differentiating the mollified potential mollifies the actual measure. -/
theorem laplacian_translationPairing_eq_measure_integral {f k : E 1 → ℝ}
    (hf : LocallyIntegrable f volume) {μ : Measure (E 1)}
    (hWeak : ∀ φ : E 1 → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ unitBall 1 →
      (∫ x, f x * Δ φ x) = (4 * Real.pi) * ∫ x, φ x ∂μ)
    (hk : ContDiff ℝ ∞ k) (hkc : HasCompactSupport k)
    {s : ℝ} (hks : tsupport k ⊆ closedBall 0 s) {z : E 1} (hz : ‖z‖ + s < 1) :
    Δ (translationPairing volume f k) z = (4 * Real.pi) * ∫ x, k (x - z) ∂μ := by
  let φ (x : E 1) := k (x - z)
  have hφ : ContDiff ℝ ∞ φ := hk.comp (contDiff_id.sub contDiff_const)
  have hφc : HasCompactSupport φ := hkc.comp_homeomorph (Homeomorph.addRight (-z))
  have hφs : tsupport φ ⊆ unitBall 1 := by
    have hs : tsupport φ ⊆ closedBall z s := by
      apply closure_minimal _ isClosed_closedBall
      intro x hx
      have hkx : x - z ∈ tsupport k := subset_tsupport k hx
      rw [mem_closedBall, dist_eq_norm]
      exact mem_closedBall_zero_iff.mp (hks hkx)
    intro x hx
    have hxd : ‖x - z‖ ≤ s := by simpa only [mem_closedBall, dist_eq_norm] using hs hx
    apply mem_ball_zero_iff.mpr
    have he : ‖x‖ ≤ ‖x - z‖ + ‖z‖ := by
      simpa only [sub_add_cancel] using norm_add_le (x - z) z
    linarith only [he, hxd, hz]
  have hk₂ := hk.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  calc
    _ = ∫ x, f x * Δ k (x - z) := laplacian_translationPairing_disc hf hk₂ hkc z
    _ = ∫ x, f x * Δ φ x := by
      apply integral_congr_ae
      filter_upwards with x
      rw [show Δ φ x = Δ k (x - z) from laplacian_comp_sub_right_disc hk₂ z x]
    _ = _ := hWeak φ hφ hφc hφs

/-- A nonnegative normalized compact kernel cannot increase the total
mass of a finite measure on a subdisk. -/
theorem setIntegral_measure_translation_le_mass {k : E 1 → ℝ} (hk : Continuous k)
    (hkc : HasCompactSupport k) (hk₀ : ∀ x, 0 ≤ k x) (hk₁ : (∫ x, k x) = 1)
    (μ : Measure (E 1)) [IsFiniteMeasure μ] (r : ℝ) :
    (∫ z in ball (0 : E 1) r, ∫ x, k (x - z) ∂μ) ≤ (μ univ).toReal := by
  let B := ball (0 : E 1) r
  let ν := (volume : Measure (E 1)).restrict B
  let : IsFiniteMeasure ν := ⟨by
    rw [show ν = volume.restrict B from rfl, Measure.restrict_apply_univ]
    exact measure_ball_lt_top⟩
  let K (p : E 1 × E 1) := k (p.2 - p.1)
  obtain ⟨C, hC⟩ := (hkc.image_of_continuousOn hk.norm.continuousOn).bddAbove
  have hbound (x : E 1) : ‖k x‖ ≤ max C 0 := by
    by_cases hx : x ∈ tsupport k
    · exact (hC ⟨x, hx, rfl⟩).trans (le_max_left _ _)
    · rw [image_eq_zero_of_notMem_tsupport hx, norm_zero]
      exact le_max_right _ _
  have hI : Integrable K (ν.prod μ) :=
    Integrable.of_bound (hk.comp (continuous_snd.sub continuous_fst)).aestronglyMeasurable
      (max C 0) (Eventually.of_forall fun p => hbound (p.2 - p.1))
  have hK (x : E 1) : (∫ z, k (x - z)) = 1 := by
    calc
      _ = ∫ z, k (x + z) := by
        simpa only [sub_eq_add_neg] using integral_neg_eq_self (fun z => k (x + z)) volume
      _ = _ := (integral_add_left_eq_self (μ := volume) k x).trans hk₁
  have hB (x : E 1) : (∫ z, k (x - z) ∂ν) ≤ 1 := by
    have hcont : Continuous (fun z => k (x - z)) := hk.comp (continuous_const.sub continuous_id)
    have hs : HasCompactSupport (fun z => k (x - z)) := by
      have h := hkc.comp_homeomorph ((Homeomorph.neg (E 1)).trans (Homeomorph.addLeft x))
      change HasCompactSupport (fun z : E 1 => k (x + -z)) at h
      simpa only [sub_eq_add_neg] using h
    rw [← hK x]
    exact setIntegral_le_integral (hcont.integrable_of_hasCompactSupport hs)
      (Eventually.of_forall fun z => hk₀ (x - z))
  change (∫ z, ∫ x, K (z, x) ∂μ ∂ν) ≤ _
  rw [← integral_prod K hI, integral_prod_symm K hI]
  apply (integral_mono_ae hI.integral_prod_right (integrable_const (1 : ℝ))
    (Eventually.of_forall hB)).trans_eq
  simp only [integral_const, measureReal_def, smul_eq_mul, mul_one]

end KEBall.BrezisMerle
