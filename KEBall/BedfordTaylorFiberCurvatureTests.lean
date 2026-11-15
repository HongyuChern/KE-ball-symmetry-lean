import KEBall.BedfordTaylorProductFiberMeasure
import KEBall.BedfordTaylorSmoothLocalCurvature

/-!
# Compact tests of the projection of the cylinder measure
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Metric Set TopologicalSpace
open scoped ContDiff Topology

namespace KEBall.BedfordTaylor

open PshLines.FirstPass (ComplexModel)
open PshLines.FirstPass.MongeAmpere (IsLocallyBoundedPshOn)

/-- A quadratic collar constant in the base direction carries no ambient mass. -/
theorem topMeasure_fiberNorm_gt_eq_zero {n : ℕ} {W : Opens (ComplexModel (n + 1))}
    (hW : W ≤ complexProductCylinder n 1) {q : ComplexModel (n + 1) → ℝ}
    (hq : IsLocallyBoundedPshOn W q) {r A D : ℝ} (hA : 0 < A)
    (he : ∀ x ∈ W, r < ‖(complexProductCoordinates n 1 x).1‖ →
      q x = A * ‖(complexProductCoordinates n 1 x).1‖ ^ 2 + D) :
    topMeasure hq {x | r < ‖(complexProductCoordinates n 1 x).1‖} = 0 := by
  let e := complexProductCoordinates n 1
  let b (x : ComplexModel (n + 1)) := A * productFiberQuadratic n 1 x
  let b' (x : ComplexModel (n + 1)) := b x + (D + A)
  let E : Set (ComplexModel (n + 1)) := {x | r < ‖(e x).1‖}
  let V : Opens (ComplexModel (n + 1)) :=
    ⟨(W : Set (ComplexModel (n + 1))) ∩ E, W.isOpen.inter (isOpen_lt continuous_const e.continuous.fst.norm)⟩
  have hVW : V ≤ W := inter_subset_left
  have hVO : V ≤ complexProductCylinder n 1 := hVW.trans hW
  have hb : IsLocallyBoundedPshOn (complexProductCylinder n 1) b :=
    locallyBoundedPsh_const_mul (locallyBoundedPsh_productFiberQuadratic n 1) hA
  have hb' : IsLocallyBoundedPshOn (complexProductCylinder n 1) b' :=
    locallyBoundedPsh_add_const hb (D + A)
  have hb'0 : topMeasure hb' = 0 := by
    rw [topMeasure_add_const hb, topMeasure_const_mul_productFiberQuadratic_eq_zero hA]
  have hEq : EqOn q b' (V : Set (ComplexModel (n + 1))) := by
    intro x hx
    have hx' : x ∈ (W : Set (ComplexModel (n + 1))) ∩ E := hx
    rw [he x hx'.1 hx'.2]
    unfold b' b productFiberQuadratic
    ring
  have hres : (topMeasure hq).restrict (V : Set (ComplexModel (n + 1))) = 0 := by
    rw [topMeasure_restrict hq hVW,
      topMeasure_congr _ (IsLocallyBoundedPshOn.mono hb' hVO) hEq, ← topMeasure_restrict hb' hVO,
      hb'0, Measure.restrict_zero]
  have hdom : (topMeasure hq).restrict (W : Set (ComplexModel (n + 1))) = topMeasure hq :=
    Measure.restrict_eq_self_of_ae_mem (by rw [ae_iff]; exact topMeasure_compl hq)
  have hE : MeasurableSet E := (isOpen_lt continuous_const e.continuous.fst.norm).measurableSet
  change topMeasure hq E = 0
  calc
    topMeasure hq E = ((topMeasure hq).restrict W) E := by rw [hdom]
    _ = ((topMeasure hq).restrict (V : Set (ComplexModel (n + 1)))) univ := by
      rw [Measure.restrict_apply hE, Measure.restrict_apply_univ]
      change topMeasure hq (E ∩ (W : Set (ComplexModel (n + 1)))) = topMeasure hq (W ∩ E)
      rw [inter_comm]
    _ = 0 := by rw [hres]; simp

/-- A base test times a compactly supported fiber cutoff is compactly
supported in the product cylinder. -/
theorem hasCompactSupport_fiberBaseTest {n : ℕ} {R ρ : ℝ}
    {χ : ComplexModel n → ℝ} {φ : E 1 → ℝ}
    (hχ : HasCompactSupport χ) (hχR : tsupport χ ⊆ ball (0 : ComplexModel n) R)
    (hφ : HasCompactSupport φ) (hφρ : tsupport φ ⊆ ball (0 : E 1) ρ) :
    let f (x : ComplexModel (n + 1)) :=
      χ (complexProductCoordinates n 1 x).1 *
        φ ((complexCoordinates 1).symm (complexProductCoordinates n 1 x).2)
    HasCompactSupport f ∧ tsupport f ⊆ fiberEnergyCylinder n R ρ := by
  let e := complexProductCoordinates n 1
  let c := complexCoordinates 1
  let ψ := φ ∘ c.symm
  let f (x : ComplexModel (n + 1)) := χ (e x).1 * ψ (e x).2
  let K := e ⁻¹' (tsupport χ ×ˢ (c '' tsupport φ))
  have hK : IsCompact K := e.toHomeomorph.isCompact_preimage.mpr
    (hχ.prod (hφ.image c.continuous))
  have hfK : tsupport f ⊆ K := by
    apply closure_minimal _ hK.isClosed
    intro x hx
    have h₁ : χ (e x).1 ≠ 0 := fun h => hx (by change χ (e x).1 * ψ (e x).2 = 0; rw [h, zero_mul])
    have h₂ : φ (c.symm (e x).2) ≠ 0 := fun h => hx (by
      change χ (e x).1 * φ (c.symm (e x).2) = 0
      rw [h, mul_zero])
    exact ⟨subset_tsupport χ h₁, ⟨c.symm (e x).2, subset_tsupport φ h₂, c.apply_symm_apply _⟩⟩
  refine ⟨hK.of_isClosed_subset isClosed_closure hfK, hfK.trans ?_⟩
  intro x hx
  have hx' : e x ∈ tsupport χ ×ˢ (c '' tsupport φ) := hx
  obtain ⟨w, hw, hew⟩ := hx'.2
  apply mem_fiberEnergyCylinder.mpr
  refine ⟨mem_ball_zero_iff.mp (hχR hx'.1), ?_⟩
  rw [← hew, LinearIsometryEquiv.norm_map]
  exact mem_ball_zero_iff.mp (hφρ hw)

/-- The cutoff can be inserted in a base test whenever it is one on the
fiber support of the top measure. -/
theorem integral_topMeasure_baseTest_eq_fiberCutoff {n : ℕ} {r R ρ : ℝ}
    {W : Opens (ComplexModel (n + 1))} {q : ComplexModel (n + 1) → ℝ}
    (hU : fiberEnergyCylinder n R ρ ≤ W) (hq : IsLocallyBoundedPshOn W q)
    (hr : r < R) (hMass : topMeasure hq {x | r < ‖(complexProductCoordinates n 1 x).1‖} = 0)
    {χ : ComplexModel n → ℝ} (hχ : ∀ z, ‖z‖ ≤ r → χ z = 1)
    {φ : E 1 → ℝ} (hφρ : tsupport φ ⊆ ball (0 : E 1) ρ) :
    (∫ x, φ ((complexCoordinates 1).symm (complexProductCoordinates n 1 x).2)
      ∂topMeasure (IsLocallyBoundedPshOn.mono hq hU)) =
      ∫ x, χ (complexProductCoordinates n 1 x).1 *
        φ ((complexCoordinates 1).symm (complexProductCoordinates n 1 x).2) ∂topMeasure hq := by
  let e := complexProductCoordinates n 1
  let c := complexCoordinates 1
  let U := fiberEnergyCylinder n R ρ
  let g (x : ComplexModel (n + 1)) := φ (c.symm (e x).2)
  change (∫ x, g x ∂topMeasure (IsLocallyBoundedPshOn.mono hq hU)) = ∫ x, χ (e x).1 * g x ∂topMeasure hq
  rw [← topMeasure_restrict hq hU, ← integral_indicator U.isOpen.measurableSet]
  have hAE : ∀ᵐ x ∂topMeasure hq, ‖(e x).1‖ ≤ r := by
    simpa only [ae_iff, not_le, e] using hMass
  apply integral_congr_ae
  filter_upwards [hAE] with x hx
  rw [hχ (e x).1 hx, one_mul]
  by_cases hxU : x ∈ U
  · rw [indicator_of_mem hxU]
  · rw [indicator_of_notMem hxU]
    change 0 = φ (c.symm (e x).2)
    symm
    apply image_eq_zero_of_notMem_tsupport
    intro hxφ
    have h := mem_ball_zero_iff.mp (hφρ hxφ)
    have hNorm : ‖c.symm (e x).2‖ = ‖(e x).2‖ := c.symm.norm_map _
    rw [hNorm] at h
    exact hxU (mem_fiberEnergyCylinder.mpr ⟨hx.trans_lt hr, h⟩)

end KEBall.BedfordTaylor
