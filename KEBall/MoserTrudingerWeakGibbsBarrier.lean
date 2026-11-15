import KEBall.MoserTrudingerWeakGibbsLimit
import KEBall.CegrellDirichletBarrier

/-!
# Quadratic comparison for a continuous weak Gibbs solution
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Metric Set
open scoped ENNReal Topology

namespace KEBall.MoserTrudinger

open BedfordTaylor Cegrell
open PshLines.FirstPass (ComplexModel)

variable {n : ℕ}

private theorem topMeasure_scaled_ballQuadratic_eq_mapped_volume {c : ℝ} (hc : 0 < c) :
    topMeasure ((ballQuadratic_isE0 n).const_mul hc).locallyBoundedPsh =
      Measure.map (complexCoordinates n) (ENNReal.ofReal (c ^ n) • (volume0 n).restrict (unitBall n)) := by
  let e := (complexCoordinates n).toHomeomorph.toMeasurableEquiv
  let B := (complexUnitBall n : Set (ComplexModel n))
  have hEq : Measure.map (complexCoordinates n) ((volume0 n).restrict (unitBall n)) =
      ENNReal.ofReal ((n.factorial : ℝ) / Real.pi ^ n) • (volume : Measure (ComplexModel n)).restrict B := by
    have he : e ⁻¹' B = unitBall n := preimage_complexUnitBall n
    have hVol : Measure.map e (volume : Measure (E n)) = volume :=
      (complexCoordinates_measurePreserving n).map_eq
    rw [volume0, Measure.restrict_smul, Measure.map_smul]
    congr 1
    change Measure.map e (volume.restrict (unitBall n)) = volume.restrict B
    rw [← he, ← e.restrict_map, hVol]
  rw [topMeasure_const_mul_ballQuadratic hc, Measure.map_smul, hEq, smul_smul,
    ← ENNReal.ofReal_mul (by positivity), mul_comm (c ^ n)]

/-- Bounds on the positive Gibbs density trap the weak potential between
quadratic barriers with zero boundary values. -/
theorem IsWeakGibbsSolution.quadratic_bounds (hn : 0 < n)
    {γ : ℝ} {v : E n → ℝ} (hv : IsWeakGibbsSolution n γ v)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hDensity : ∀ x ∈ unitBall n, a ^ n ≤ gibbsDensity γ v x ∧ gibbsDensity γ v x ≤ b ^ n) :
    ∀ x ∈ closedUnitBall n, b * (‖x‖ ^ 2 - 1) ≤ v x ∧ v x ≤ a * (‖x‖ ^ 2 - 1) := by
  let e := complexCoordinates n
  let ρ := (volume0 n).restrict (unitBall n)
  let p := fun x => ENNReal.ofReal (gibbsDensity γ v x)
  have hp : ∀ᵐ x ∂ρ, ENNReal.ofReal (a ^ n) ≤ p x ∧ p x ≤ ENNReal.ofReal (b ^ n) := by
    filter_upwards [ae_restrict_mem (μ := volume0 n) (show MeasurableSet (unitBall n) from measurableSet_ball)]
      with x hx
    exact ⟨ENNReal.ofReal_le_ofReal (hDensity x hx).1, ENNReal.ofReal_le_ofReal (hDensity x hx).2⟩
  have hLow : topMeasure ((ballQuadratic_isE0 n).const_mul ha).locallyBoundedPsh ≤
      topMeasure hv.memE0.locallyBoundedPsh := by
    rw [topMeasure_scaled_ballQuadratic_eq_mapped_volume ha, hv.measure_eq]
    apply Measure.map_mono _ e.continuous.measurable
    rw [← withDensity_const]
    exact withDensity_mono (hp.mono fun _ hx => hx.1)
  have hHigh : topMeasure hv.memE0.locallyBoundedPsh ≤
      topMeasure ((ballQuadratic_isE0 n).const_mul hb).locallyBoundedPsh := by
    rw [topMeasure_scaled_ballQuadratic_eq_mapped_volume hb, hv.measure_eq]
    apply Measure.map_mono _ e.continuous.measurable
    rw [← withDensity_const]
    exact withDensity_mono (hp.mono fun _ hx => hx.2)
  intro x hx
  rcases (mem_closedBall_zero_iff.mp hx).lt_or_eq with hlt | heq
  · have hx' : e x ∈ complexUnitBall n := by
      change x ∈ e ⁻¹' (complexUnitBall n : Set (ComplexModel n))
      rw [preimage_complexUnitBall]
      exact mem_ball_zero_iff.mpr hlt
    have h₁ := ((ballQuadratic_isE0 n).const_mul hb).le_of_topMeasure_le_unitBall hn hv.memE0 hHigh (e x) hx'
    have h₂ := hv.memE0.le_of_topMeasure_le_unitBall hn ((ballQuadratic_isE0 n).const_mul ha) hLow (e x) hx'
    change b * (‖e x‖ ^ 2 - 1) ≤ v (e.symm (e x)) at h₁
    change v (e.symm (e x)) ≤ a * (‖e x‖ ^ 2 - 1) at h₂
    simpa only [e.norm_map, e.symm_apply_apply] using And.intro h₁ h₂
  · have hx' : x ∈ unitSphere n := mem_sphere_zero_iff_norm.mpr heq
    simp only [heq, hv.zero_on_sphere x hx', one_pow, sub_self, mul_zero, le_refl, and_self]

end KEBall.MoserTrudinger
