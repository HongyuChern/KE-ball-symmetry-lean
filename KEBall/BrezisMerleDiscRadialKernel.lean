import KEBall.BrezisMerleDiscConvolution
import KEBall.BedfordTaylorCoordinates
import PshLines.Regularization.HolomorphicPullback

/-!
# Compact radial mollifiers on the real model of the complex disk
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Metric Set
open scoped ContDiff Topology

namespace KEBall.BrezisMerle

open PshLines (translationPairing)
open PshLines.FirstPass (ComplexModel)
open PshLines.Regularization.HolomorphicPullback

/-- The fixed normalized radial kernel pulled back by the Euclidean coordinates. -/
noncomputable def discMollifier (j : ℕ) (x : E 1) : ℝ :=
  explicitRadialKernel 1 one_pos j (complexCoordinates 1 x)

theorem discMollifier_contDiff (j : ℕ) : ContDiff ℝ ∞ (discMollifier j) :=
  (explicitRadialKernel_contDiff 1 one_pos j).comp (complexCoordinates 1).toContinuousLinearEquiv.contDiff

theorem discMollifier_nonneg (j : ℕ) (x : E 1) : 0 ≤ discMollifier j x :=
  explicitRadialKernel_nonneg 1 one_pos j (complexCoordinates 1 x)

theorem discMollifier_integral_one (j : ℕ) : (∫ x, discMollifier j x) = 1 := by
  let c := complexCoordinates 1
  have hc := (complexCoordinates_measurePreserving 1).integral_comp
    c.toHomeomorph.toMeasurableEquiv.measurableEmbedding (explicitRadialKernel (n := 1) 1 one_pos j)
  exact hc.trans (explicitRadialKernel_integral_one 1 one_pos j)

theorem discMollifier_tsupport_subset (j : ℕ) :
    tsupport (discMollifier j) ⊆ closedBall 0 (1 / ((j : ℝ) + 1)) := by
  apply closure_minimal _ isClosed_closedBall
  intro x hx
  have h : complexCoordinates 1 x ∈ tsupport (explicitRadialKernel (n := 1) 1 one_pos j) :=
    subset_tsupport _ hx
  rw [explicitRadialKernel_tsupport] at h
  have hn := mem_closedBall_zero_iff.mp h
  exact mem_closedBall_zero_iff.mpr (by simpa only [LinearIsometryEquiv.norm_map] using hn)

theorem discMollifier_hasCompactSupport (j : ℕ) : HasCompactSupport (discMollifier j) :=
  (isCompact_closedBall _ _).of_isClosed_subset (isClosed_tsupport _) (discMollifier_tsupport_subset j)

theorem ae_tendsto_translationPairing_discMollifier {u : E 1 → ℝ} (hu : Integrable u) :
    ∀ᵐ z ∂(volume : Measure (E 1)),
      Tendsto (fun j => translationPairing volume u (discMollifier j) z) atTop (𝓝 (u z)) := by
  let c := complexCoordinates 1
  let ce := c.toHomeomorph.toMeasurableEquiv
  have hc : MeasurePreserving c := complexCoordinates_measurePreserving 1
  have hci : MeasurePreserving c.symm := MeasurePreserving.symm ce hc
  let v : ComplexModel 1 → ℝ := u ∘ c.symm
  have hv : Integrable v := Integrable.comp_measurable (hci.map_eq.symm ▸ hu) hci.measurable
  have h := ae_tendsto_translationPairing_explicitRadialKernel hv.locallyIntegrable 1 one_pos
  have hEq (j : ℕ) (z : E 1) :
      translationPairing volume u (discMollifier j) z =
        translationPairing volume v (explicitRadialKernel 1 one_pos j) (c z) := by
    have he := hc.integral_comp ce.measurableEmbedding
      (fun x => v x * explicitRadialKernel 1 one_pos j (x - c z))
    simpa only [translationPairing, v, Function.comp_apply, LinearIsometryEquiv.symm_apply_apply,
      ← map_sub, c, discMollifier] using he
  filter_upwards [hc.quasiMeasurePreserving.ae h] with z hz
  simp_rw [hEq]
  simpa only [v, Function.comp_apply, LinearIsometryEquiv.symm_apply_apply] using hz

end KEBall.BrezisMerle
