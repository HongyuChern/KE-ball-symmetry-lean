import KEBall.BedfordTaylorFiberEnvelopeCurvature
import KEBall.CegrellFiberEnergyBoundary
import KEBall.CegrellProductBallSubextension

/-!
# Subextension with the disk measure of the fiber energy
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Metric Set TopologicalSpace
open scoped ContDiff ENNReal Laplacian Topology

namespace KEBall.Cegrell

open BedfordTaylor
open PshLines.FirstPass (ComplexModel)

/-- The product subextension has bounded Cegrell fibers. Its signed fiber
energy has zero base trace and its disk Monge–Ampère mass is bounded by the
original mass divided by the ambient complex dimension. -/
theorem exists_productBall_subextension_withFiberCurvature {n : ℕ} (hn : 0 < n)
    {R : ℝ} (hR : 0 < R) (hR₁ : R < 1)
    {u : ComplexModel (n + 1) → ℝ} (hu : IsE0 (ballDomain 0 R) u)
    (huSmooth : ContDiff ℝ 2 u) (hu₀ : ∀ x ∈ ball 0 R, u x ≤ 0)
    (huBoundary : ∀ x ∈ sphere 0 R, u x = 0) :
    ∃ v : ComplexModel (n + 1) → ℝ, ∃ hv : IsE0 (complexProductBall n 1) v,
      (∀ x ∈ ball 0 R, v x ≤ u x) ∧ ContinuousOn v (complexProductBall n 1) ∧
      ∃ μ : Measure (E 1),
        μ (unitBall 1)ᶜ = 0 ∧
        μ univ ≤ ENNReal.ofReal ((n + 1 : ℝ)⁻¹) * topMeasure hu.locallyBoundedPsh univ ∧
        (∀ φ : E 1 → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ unitBall 1 →
          Integrable (fun w => bedfordTaylorFiberEnergy (R := 1) (ρ := 1) hv.locallyBoundedPsh w * Δ φ w) ∧
            (∫ w, bedfordTaylorFiberEnergy (R := 1) (ρ := 1) hv.locallyBoundedPsh w * Δ φ w) =
              (4 * Real.pi) * ∫ w, φ w ∂μ) ∧
        ∃ M : ℝ, 0 ≤ M ∧ ∀ w ∈ unitBall 1,
          ∃ hE : IsE0 (complexUnitBall n) (complexFiberSlice v (complexCoordinates 1 w)),
            bedfordTaylorFiberEnergy (R := 1) (ρ := 1) hv.locallyBoundedPsh w =
              -(boundedEnergy hE).toReal / (n + 1 : ℝ) ∧
            -(M * (1 - ‖w‖ ^ 2)) ≤ bedfordTaylorFiberEnergy (R := 1) (ρ := 1) hv.locallyBoundedPsh w ∧
            bedfordTaylorFiberEnergy (R := 1) (ρ := 1) hv.locallyBoundedPsh w ≤ 0 := by
  obtain ⟨v, hv, hμ, hle, hCont, hv₀, hvf, hGreatest, A, hA, hBarrier⟩ :=
    exists_productBall_subextension_withEnvelope (n := n) (m := 1) (by omega) hR hR₁ hu huSmooth hu₀ huBoundary
  let e := complexProductCoordinates n 1
  let c := complexCoordinates 1
  let P := complexProductBall n 1
  let g (x : ComplexModel (n + 1)) := c.symm (e x).2
  let k := (n + 1 : ℝ)⁻¹
  let ν := topMeasure hv.locallyBoundedPsh
  let μ := ENNReal.ofReal k • Measure.map g ν
  have hg : Continuous g := c.symm.continuous.comp e.continuous.snd
  have hvLower (x : ComplexModel (n + 1)) (hx : x ∈ P) : A * productFiberQuadratic n 1 x ≤ v x :=
    (mul_le_mul_of_nonneg_left (le_max_left _ _) hA.le).trans (hBarrier x hx)
  refine ⟨v, hv, hle, hCont, μ, ?_, ?_, ?_, ?_⟩
  · have hpre : g ⁻¹' (unitBall 1)ᶜ ⊆ (P : Set (ComplexModel (n + 1)))ᶜ := by
      intro x hx hxP
      have hbase : ‖(e x).2‖ < 1 := (mem_complexProductBall.mp hxP).2
      apply hx
      apply mem_ball_zero_iff.mpr
      change ‖c.symm (e x).2‖ < 1
      rw [c.symm.norm_map]
      exact hbase
    have h0 : ν (g ⁻¹' (unitBall 1)ᶜ) = 0 :=
      le_antisymm ((measure_mono hpre).trans_eq (topMeasure_compl hv.locallyBoundedPsh)) bot_le
    rw [show μ = ENNReal.ofReal k • Measure.map g ν from rfl,
      Measure.smul_apply, Measure.map_apply hg.measurable
        (show MeasurableSet (unitBall 1)ᶜ from measurableSet_ball.compl), h0, smul_zero]
  · change (ENNReal.ofReal k • Measure.map g ν) univ ≤ _
    rw [Measure.smul_apply, Measure.map_apply hg.measurable MeasurableSet.univ,
      preimage_univ, smul_eq_mul]
    exact mul_le_mul_right (hμ univ) _
  · intro φ hφ hφc hφs
    obtain ⟨hInt, hEq⟩ := integral_bedfordTaylorFiberEnergy_mul_laplacian_productEnvelope hn hR hR₁
      huSmooth hu₀ huBoundary hv.locallyBoundedPsh hvf hGreatest hA hvLower hφ hφc hφs
    refine ⟨hInt, hEq.trans ?_⟩
    change (4 * Real.pi / (n + 1 : ℝ)) * (∫ x, φ (g x) ∂ν) =
      (4 * Real.pi) * ∫ w, φ w ∂(ENNReal.ofReal k • Measure.map g ν)
    rw [integral_smul_measure, ENNReal.toReal_ofReal (by dsimp [k]; positivity), smul_eq_mul,
      integral_map hg.measurable.aemeasurable hφ.continuous.aestronglyMeasurable]
    dsimp only [k]
    ring
  · obtain ⟨M, hM, hb⟩ := exists_isE0_complexFiberSlice_and_energy_bound
      hv.locallyBoundedPsh hv₀ hA hBarrier
    exact ⟨M, hM, fun w hw => ⟨(hb w hw).1,
      bedfordTaylorFiberEnergy_eq_neg_boundedEnergy hn hv.locallyBoundedPsh hw (hb w hw).1,
      (hb w hw).2⟩⟩

end KEBall.Cegrell
