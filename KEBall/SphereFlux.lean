import KEBall.BallBoundaryKernel
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Polar integration and spherical flux averages

The Euclidean polar product is split using Fubini only after proving
integrability by the actual measure-preserving polar equivalence.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace KEBall

theorem integrable_polar (n : ℕ) {f : E n → ℝ}
    (hf : Integrable f volume) :
    Integrable (fun p : Sphere n × Ioi (0 : ℝ) => f (p.2.1 • p.1.1))
      ((sphereMeasure n).prod (Measure.volumeIoiPow (2 * n - 1))) := by
  have hsub : Integrable (fun x : ({(0 : E n)}ᶜ : Set (E n)) => f x.1)
      ((volume : Measure (E n)).comap Subtype.val) :=
    (integrableOn_iff_comap_subtypeVal (measurableSet_singleton _).compl).mp hf.integrableOn
  have h := (polar_measurePreserving n).integrable_comp_emb
    (g := fun p => f ((homeomorphUnitSphereProd (E n)).symm p).1)
    (Homeomorph.measurableEmbedding (homeomorphUnitSphereProd (E n)))
  have h' := h.mp (by simpa only [Function.comp_def, Homeomorph.symm_apply_apply] using hsub)
  simpa only [homeomorphUnitSphereProd_symm_apply_coe, Sphere, unitSphere] using h'

theorem integral_volumeIoiPow (d : ℕ) (f : ℝ → ℝ) :
    (∫ r : Ioi (0 : ℝ), f r.1 ∂Measure.volumeIoiPow d) =
      ∫ r in Ioi (0 : ℝ), r ^ d * f r := by
  simp only [Measure.volumeIoiPow, ENNReal.ofReal]
  rw [integral_withDensity_eq_integral_smul,
    integral_subtype_comap measurableSet_Ioi (fun r : ℝ => Real.toNNReal (r ^ d) • f r)]
  · apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    change Real.toNNReal (r ^ d) • f r = r ^ d * f r
    rw [NNReal.smul_def, Real.coe_toNNReal _ (pow_nonneg hr.le _), smul_eq_mul]
  · exact (measurable_subtype_coe.pow_const d).real_toNNReal

theorem integral_polar_iterated (n : ℕ) (hn : 0 < n) {f : E n → ℝ}
    (hf : Integrable f volume) :
    (∫ x, f x) =
      ∫ r in Ioi (0 : ℝ), r ^ (2 * n - 1) *
        ∫ θ : Sphere n, f (r • θ.1) ∂sphereMeasure n := by
  rw [integral_polar n hn, integral_prod_symm _ (integrable_polar n hf)]
  exact integral_volumeIoiPow (2 * n - 1)
    (fun r => ∫ θ : Sphere n, f (r • θ.1) ∂sphereMeasure n)

noncomputable def radialFlux (n : ℕ) (V : E n → E n) (r : ℝ) : ℝ :=
  ∫ θ : Sphere n, inner ℝ θ.1 (V (r • θ.1)) ∂sphereMeasure n

theorem radialFlux_continuous (n : ℕ) {V : E n → E n} (hV : Continuous V) :
    Continuous (radialFlux n V) := by
  have hc : Continuous (fun p : ℝ × Sphere n => inner ℝ p.2.1 (V (p.1 • p.2.1))) :=
    (continuous_subtype_val.comp continuous_snd).inner
      (hV.comp (continuous_fst.smul (continuous_subtype_val.comp continuous_snd)))
  have h := continuous_parametric_integral_of_continuous
    (f := fun r (θ : Sphere n) => inner ℝ θ.1 (V (r • θ.1)))
    (μ := sphereMeasure n) hc (s := univ) isCompact_univ
  change Continuous (fun r => ∫ θ : Sphere n, inner ℝ θ.1 (V (r • θ.1)) ∂sphereMeasure n)
  simpa only [Measure.restrict_univ] using h

theorem tendsto_integral_ballBoundaryKernel_radialFlux (n : ℕ)
    {V : E n → E n} (hV : Continuous V) :
    Tendsto (fun k : ℕ =>
      ∫ r in Icc (0 : ℝ) 2,
        ballBoundaryKernel (1 / ((k : ℝ) + 1)) r *
          (r ^ (2 * n - 1) * radialFlux n V r))
      atTop (𝓝 (∫ θ : Sphere n, inner ℝ θ.1 (V θ.1) ∂sphereMeasure n)) := by
  have hc : Continuous (fun r : ℝ => r ^ (2 * n - 1) * radialFlux n V r) :=
    (continuous_id.pow _).mul (radialFlux_continuous n hV)
  have h := tendsto_integral_ballBoundaryKernel
    (hc.continuousOn.integrableOn_compact isCompact_Icc) hc.continuousWithinAt
  simpa only [one_pow, one_mul, radialFlux, one_smul] using h

#print axioms integrable_polar
#print axioms integral_polar_iterated
#print axioms radialFlux_continuous
#print axioms tendsto_integral_ballBoundaryKernel_radialFlux

end KEBall
