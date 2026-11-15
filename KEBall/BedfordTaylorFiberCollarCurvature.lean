import KEBall.BedfordTaylorFiberEnergyLimit
import KEBall.BedfordTaylorFiberCurvatureTests

/-!
# The curvature identity with the smooth quadratic collar in place
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Metric Set TopologicalSpace
open scoped ComplexOrder ContDiff ENNReal Laplacian SchwartzMap Topology

namespace KEBall.BedfordTaylor

open MoserTrudinger
open PshLines.FirstPass (ComplexModel)
open PshLines.FirstPass.MongeAmpere (IsLocallyBoundedPshOn IsSmoothPshOn isSmoothPshOn_of_psh)

set_option maxHeartbeats 750000 in
/-- Subtracting the fiber boundary constant contributes a base-independent
term because the collar fixes the vertical Monge–Ampère mass. -/
theorem integral_fiberEnergy_mul_laplacian_of_quadratic_collar {n : ℕ} (hn : 0 < n)
    {r ρ A D : ℝ} (hrρ : r < ρ) (hA : 0 < A)
    {q : ComplexModel (n + 1) → ℝ} (hq : ContDiff ℝ ∞ q)
    (hs : IsSmoothPshOn (fiberEnergyCylinder n 3 ρ) q)
    (hEq : ∀ x ∈ fiberEnergyCylinder n 3 ρ,
      (3 / 2 : ℝ) < ‖(complexProductCoordinates n 1 x).1‖ →
      q x = A * ‖(complexProductCoordinates n 1 x).1‖ ^ 2 + D)
    (hP : ∀ c w, w ∈ ball (0 : E 1) ρ → ∀ z ∈ unitBall n,
      (KEBall.complexHessian (fun y => q (fiberDilationCoordinates n 2 (y, w)) - c) z).PosDef)
    {φ : E 1 → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφs : tsupport φ ⊆ ball (0 : E 1) r) :
    (∫ w, fiberEnergy (q ∘ fiberDilationCoordinates n 2) w * Δ φ w) =
      (4 * Real.pi / (n + 1 : ℝ)) *
        ∫ x, φ ((complexCoordinates 1).symm (complexProductCoordinates n 1 x).2)
          ∂topMeasure (IsLocallyBoundedPshOn.mono (isLocallyBoundedPshOn_of_isSmoothPshOn hs)
            (fiberEnergyCylinder_mono (by norm_num : (2 : ℝ) ≤ 3) hrρ.le)) := by
  let e := complexProductCoordinates n 1
  let c := complexCoordinates 1
  let W := fiberEnergyCylinder n 3 ρ
  let U := fiberEnergyCylinder n 2 r
  let B : Opens (ComplexModel n) := ballDomain 0 2
  let L := fiberDilationCoordinates n 2
  let C := A * (2 : ℝ) ^ 2 + D
  let q' (x : ComplexModel (n + 1)) := q x - C
  let hUW : U ≤ W := fiberEnergyCylinder_mono (by norm_num) hrρ.le
  let hQU : IsSmoothPshOn U q :=
    ⟨hs.1.mono hUW, hs.2.1.mono hUW, fun x hx => hs.2.2 x (hUW hx)⟩
  have hBoundary (z : ComplexModel n) (w : ComplexModel 1)
      (hz : ‖z‖ = 2) (hw : ‖w‖ < ρ) : q (e.symm (z, w)) = C := by
    have hX : e.symm (z, w) ∈ W := by
      apply mem_fiberEnergyCylinder.mpr
      change ‖(e (e.symm (z, w))).1‖ < 3 ∧ ‖(e (e.symm (z, w))).2‖ < ρ
      rw [e.apply_symm_apply]
      exact ⟨by rw [hz]; norm_num, hw⟩
    have h := hEq (e.symm (z, w)) hX
    rw [e.apply_symm_apply, hz] at h
    exact h (by norm_num)
  have hP' (w : E 1) (hw : w ∈ ball (0 : E 1) r) (z : E n) (hz : z ∈ unitBall n) :
      (KEBall.complexHessian (fun y => q (L (y, w)) - C) z).PosDef :=
    hP C w (ball_subset_ball hrρ.le hw) z hz
  have hShifted := integral_fiberEnergy_sub_const_mul_laplacian hn (by norm_num : (0 : ℝ) < 2)
    hrρ hq hQU hBoundary hP' hφ hφc hφs
  let mass := (ENNReal.ofReal (A ^ n) *
    (ENNReal.ofReal ((n.factorial : ℝ) / Real.pi ^ n) *
      (volume : Measure (ComplexModel n)) (ball 0 2))).toReal
  have hPoint (w : E 1) (hw : w ∈ ball (0 : E 1) r) :
      fiberEnergy (q ∘ L) w = fiberEnergy (q' ∘ L) w + C * mass / (n + 1 : ℝ) := by
    have hc : ‖c w‖ < r := (c.norm_map w).trans_lt (mem_ball_zero_iff.mp hw)
    let v := complexFiberSlice q (c w)
    have hv := locallyBoundedPsh_complexFiberSlice
      (isLocallyBoundedPshOn_of_isSmoothPshOn hQU) hc
    have hvS : IsSmoothPshOn B v := isSmoothPshOn_of_psh
      (contDiff_complexFiberSlice hq (c w)).contDiffOn hv.1
    have hv'S : IsSmoothPshOn B (complexFiberSlice q' (c w)) :=
      isSmoothPshOn_of_psh (contDiff_complexFiberSlice (hq.sub contDiff_const) (c w)).contDiffOn
        (locallyBoundedPsh_add_const hv (-C)).1
    have hVE (z : ComplexModel n) (hz : z ∈ ball (0 : ComplexModel n) 2)
        (hz' : (3 / 2 : ℝ) < ‖z‖) : v z = A * ‖z‖ ^ 2 + D := by
      have hX : e.symm (z, c w) ∈ W := by
        apply mem_fiberEnergyCylinder.mpr
        change ‖(e (e.symm (z, c w))).1‖ < 3 ∧ ‖(e (e.symm (z, c w))).2‖ < ρ
        rw [e.apply_symm_apply]
        exact ⟨(mem_ball_zero_iff.mp hz).trans (by norm_num), hc.trans hrρ⟩
      have h := hEq (e.symm (z, c w)) hX
      rw [e.apply_symm_apply] at h
      exact h hz'
    have hMass := topMeasure_univ_eq_of_quadratic_collar (by norm_num : (3 / 2 : ℝ) < 2)
      hA hv hVE
    have hFin := topMeasure_univ_lt_top_of_quadratic_collar (by norm_num : (3 / 2 : ℝ) < 2)
      hA hv hVE
    obtain ⟨B₀, hB₀⟩ := ((isCompact_closedBall (0 : ComplexModel n) 2).image
      (contDiff_complexFiberSlice hq (c w)).continuous.norm).bddAbove
    have hInt : Integrable v (topMeasure hv) :=
      integrable_topMeasure_of_bounded hv hv hFin
        (fun z hz => hB₀ ⟨z, ball_subset_closedBall hz, rfl⟩)
    have hshift := integral_topMeasure_sub_const hv C hFin hInt
    rw [fiberEnergy_fiberDilationCoordinates hq (by norm_num) w hvS,
      fiberEnergy_fiberDilationCoordinates (show ContDiff ℝ ∞ q' from hq.sub contDiff_const)
        (by norm_num) w hv'S]
    change (∫ z, v z ∂topMeasure hv) / (n + 1 : ℝ) =
      (∫ z, v z + -C ∂topMeasure (locallyBoundedPsh_add_const hv (-C))) / (n + 1 : ℝ) +
        C * mass / (n + 1 : ℝ)
    rw [hshift, hMass]
    change _ = ((∫ z, v z ∂topMeasure hv) - C * mass) / (n + 1 : ℝ) + C * mass / (n + 1 : ℝ)
    ring
  have hΔ : HasCompactSupport (Δ φ) :=
    hφc.of_isClosed_subset (isClosed_tsupport _) (tsupport_laplacian_subset φ)
  have hΔC : Continuous (Δ φ) := by
    let f := hφc.toSchwartzMap hφ
    have hf : ((Δ f : 𝓢(E 1, ℝ)) : E 1 → ℝ) = Δ φ :=
      funext fun w => SchwartzMap.laplacian_apply f w
    rw [← hf]
    exact (Δ f).continuous
  have hF : ContDiff ℝ ∞ (fiberEnergy (q' ∘ L)) :=
    fiberEnergy_contDiff hn ((hq.sub contDiff_const).comp L.contDiff)
  have hIntegrable : Integrable (fun w => fiberEnergy (q' ∘ L) w * Δ φ w) :=
    (hF.continuous.mul hΔC).integrable_of_hasCompactSupport hΔ.mul_left
  have hIntEq : (∫ w, fiberEnergy (q ∘ L) w * Δ φ w) =
      ∫ w, fiberEnergy (q' ∘ L) w * Δ φ w + (C * mass / (n + 1 : ℝ)) * Δ φ w := by
    apply integral_congr_ae
    filter_upwards with w
    by_cases hw : w ∈ ball (0 : E 1) r
    · rw [hPoint w hw, add_mul]
    · have hz : Δ φ w = 0 := image_eq_zero_of_notMem_tsupport
        (fun h => hw (hφs (tsupport_laplacian_subset φ h)))
      simp only [hz, mul_zero, add_zero]
  rw [hIntEq, integral_add hIntegrable ((integrable_laplacian_of_compactSupport hφ hφc).const_mul _),
    integral_const_mul, integral_laplacian_eq_zero_of_compactSupport hφ hφc, mul_zero, add_zero]
  exact hShifted

end KEBall.BedfordTaylor
