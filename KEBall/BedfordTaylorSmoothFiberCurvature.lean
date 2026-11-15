import KEBall.BedfordTaylorSmoothFiberEnergy
import KEBall.FiberEnergyCurvature
import KEBall.SmoothLaplacianTesting
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Weak curvature of smooth fiber energy in the Bedford–Taylor normalization
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Metric Set TopologicalSpace
open scoped ComplexOrder ContDiff ENNReal Laplacian Topology

namespace KEBall.BedfordTaylor

open MoserTrudinger
open PshLines.FirstPass (ComplexModel)
open PshLines.FirstPass.MongeAmpere (IsSmoothPshOn smoothDensity)

local notation "modelHessian" => PshLines.FirstPass.MongeAmpere.complexHessian

/-- The cylinder with separately prescribed fiber and base radii. -/
noncomputable def fiberEnergyCylinder (n : ℕ) (R ρ : ℝ) : Opens (ComplexModel (n + 1)) :=
  ⟨(complexProductCoordinates n 1) ⁻¹' (ball 0 R ×ˢ ball 0 ρ),
    (isOpen_ball.prod isOpen_ball).preimage (complexProductCoordinates n 1).continuous⟩

/-- Integrating the base Laplacian against the smooth fiber energy gives the
projection of the full Bedford–Taylor measure, with Euclidean base volume. -/
theorem integral_fiberEnergy_mul_laplacian {n : ℕ} (hn : 0 < n) {R ρ : ℝ} (hR : 0 < R)
    {q : ComplexModel (n + 1) → ℝ} (hq : ContDiff ℝ ∞ q)
    (hs : IsSmoothPshOn (fiberEnergyCylinder n R ρ) q)
    (h0 : ∀ w z, z ∈ unitSphere n → q (fiberDilationCoordinates n R (z, w)) = 0)
    (hP : ∀ w ∈ ball (0 : E 1) ρ, ∀ z ∈ unitBall n,
      (KEBall.complexHessian (fun y => q (fiberDilationCoordinates n R (y, w))) z).PosDef)
    {φ : E 1 → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφs : tsupport φ ⊆ ball (0 : E 1) ρ) :
    (∫ w, fiberEnergy (q ∘ fiberDilationCoordinates n R) w * Δ φ w) =
      (4 * Real.pi / (n + 1 : ℝ)) *
        ∫ x, φ ((complexCoordinates 1).symm ((complexProductCoordinates n 1 x).2))
          ∂topMeasure (isLocallyBoundedPshOn_of_isSmoothPshOn hs) := by
  let e := complexProductCoordinates n 1
  let c := complexCoordinates 1
  let u := q ∘ fiberDilationCoordinates n R
  let det (x : ComplexModel (n + 1)) := (modelHessian q x).det.re
  let A : Set (ComplexModel n) := ball 0 R
  let B : Set (ComplexModel 1) := ball 0 ρ
  let B' : Set (E 1) := ball 0 ρ
  let F (p : ComplexModel n × ComplexModel 1) := det (e.symm p) * φ (c.symm p.2)
  have hu : ContDiff ℝ ∞ u := hq.comp (fiberDilationCoordinates n R).contDiff
  have hφ0 (w : E 1) (hw : w ∉ B') : φ w = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hw (hφs h))
  have hLap (w : E 1) (hw : w ∈ B') :
      Δ (fiberEnergy u) w = 4 * (((n.factorial : ℝ) / Real.pi ^ n) *
        ∫ z in A, det (e.symm (z, c w))) := by
    have hU : B' ∈ 𝓝 w := isOpen_ball.mem_nhds hw
    rw [laplacian_fiberEnergy_of_eventually_posDef hn hu h0
      ((show ∀ᶠ v in 𝓝 w, v ∈ B' from hU).mono hP)]
    congr 1
    have h := setIntegral_volume0_dilation_coordinates (fun z => det (e.symm (z, c w))) hR
    simpa only [u, productComplexHessian_det_fiberDilationCoordinates hq, det,
      fiberDilationCoordinates_apply, e, c, A] using h
  have hInt : IntegrableOn F (A ×ˢ B) := by
    have hDet : Continuous det := by
      have h := continuousOn_smoothDensity (U := (⊤ : Opens (ComplexModel (n + 1))))
        hq.contDiffOn
      have h' : Continuous (smoothDensity q) := continuousOn_univ.mp h
      have hcoef : ((n + 1).factorial : ℝ) / Real.pi ^ (n + 1) ≠ 0 :=
        ne_of_gt (div_pos (by exact_mod_cast Nat.factorial_pos _) (pow_pos Real.pi_pos _))
      have heq : det = fun x => ( ((n + 1).factorial : ℝ) / Real.pi ^ (n + 1))⁻¹ *
          smoothDensity q x := by
        funext x
        change det x = _ * (_ * det x)
        rw [← mul_assoc, inv_mul_cancel₀ hcoef, one_mul]
      rw [heq]
      exact continuous_const.mul h'
    have hF : Continuous F :=
      (hDet.comp e.symm.continuous).mul (hφ.continuous.comp (c.symm.continuous.comp continuous_snd))
    have hK := (isCompact_closedBall (0 : ComplexModel n) R).prod
      (isCompact_closedBall (0 : ComplexModel 1) ρ)
    have hAB : A ×ˢ B ⊆ closedBall (0 : ComplexModel n) R ×ˢ closedBall (0 : ComplexModel 1) ρ :=
      Set.prod_mono ball_subset_closedBall ball_subset_closedBall
    exact hF.continuousOn.integrableOn_of_subset_isCompact hK
      (measurableSet_ball.prod measurableSet_ball) hAB
      (measure_ne_top_of_subset hAB hK.measure_lt_top.ne)
  have hB : c ⁻¹' B = B' := by
    ext w
    simp only [B, B', mem_preimage, mem_ball_zero_iff, LinearIsometryEquiv.norm_map]
  have hFubini :
      (∫ w in B', ∫ z in A, F (z, c w)) = ∫ p in A ×ˢ B, F p := by
    rw [← hB, (complexCoordinates_measurePreserving 1).setIntegral_preimage_emb
      c.toHomeomorph.toMeasurableEquiv.measurableEmbedding (fun w => ∫ z in A, F (z, w)) B]
    have hInt' : Integrable F ((volume.restrict A).prod (volume.restrict B)) := by
      rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
      exact hInt
    rw [← integral_prod_symm F hInt', Measure.prod_restrict, ← Measure.volume_eq_prod]
  have hFull :
      (∫ p in A ×ˢ B, F p) =
        ∫ x in (fiberEnergyCylinder n R ρ : Set (ComplexModel (n + 1))),
          det x * φ (c.symm (e x).2) := by
    have he : MeasurePreserving e := measurePreserving_complexProductCoordinates n 1
    have h := he.setIntegral_preimage_emb
      e.toHomeomorph.toMeasurableEquiv.measurableEmbedding F (A ×ˢ B)
    change (∫ p in A ×ˢ B, F p) = ∫ x in e ⁻¹' (A ×ˢ B), det x * φ (c.symm (e x).2)
    simpa only [Function.comp_apply, F, ContinuousLinearEquiv.symm_apply_apply] using h.symm
  calc
    _ = ∫ w, Δ (fiberEnergy u) w * φ w :=
      integral_mul_laplacian_eq_of_compact_test (fiberEnergy_contDiff hn hu) hφ hφc
    _ = ∫ w in B', Δ (fiberEnergy u) w * φ w := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro w hw
      rw [hφ0 w hw, mul_zero]
    _ = (4 * ((n.factorial : ℝ) / Real.pi ^ n)) *
        ∫ w in B', ∫ z in A, F (z, c w) := by
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_ball
      intro w hw
      change Δ (fiberEnergy u) w * φ w =
        (4 * ((n.factorial : ℝ) / Real.pi ^ n)) * ∫ z in A, F (z, c w)
      rw [hLap w hw]
      simp only [F, LinearIsometryEquiv.symm_apply_apply, integral_mul_const]
      ring
    _ = _ := by
      rw [hFubini, hFull, integral_topMeasure_eq_setIntegral_density hs, ← integral_const_mul,
        ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      change 4 * ((n.factorial : ℝ) / Real.pi ^ n) * (det x * φ (c.symm (e x).2)) =
        (4 * Real.pi / (n + 1 : ℝ)) *
          ((((n + 1).factorial : ℝ) / Real.pi ^ (n + 1) * det x) * φ (c.symm (e x).2))
      have hn1 : (n + 1 : ℝ) ≠ 0 := by positivity
      rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
      field_simp [hn1, Real.pi_ne_zero]

end KEBall.BedfordTaylor
