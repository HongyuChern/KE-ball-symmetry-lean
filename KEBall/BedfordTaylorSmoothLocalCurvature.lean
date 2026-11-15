import KEBall.BedfordTaylorFiberBoundaryNormalization
import KEBall.BedfordTaylorTruncationLocality

/-!
# Smooth curvature for a locally constant fiber boundary value
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Metric Set TopologicalSpace
open scoped ComplexOrder ContDiff Laplacian Topology

namespace KEBall.BedfordTaylor

open MoserTrudinger
open PshLines
open PshLines.FirstPass (ComplexModel)
open PshLines.FirstPass.MongeAmpere (IsLocallyBoundedPshOn IsSmoothPshOn isSmoothPshOn_of_psh)

theorem mem_fiberEnergyCylinder {n : ℕ} {R ρ : ℝ} {x : ComplexModel (n + 1)} :
    x ∈ fiberEnergyCylinder n R ρ ↔
      ‖(complexProductCoordinates n 1 x).1‖ < R ∧
      ‖(complexProductCoordinates n 1 x).2‖ < ρ := by
  change complexProductCoordinates n 1 x ∈ ball 0 R ×ˢ ball 0 ρ ↔ _
  simp only [mem_prod, mem_ball_zero_iff]

/-- The smooth weak curvature identity only needs the constant fiber boundary
value on a neighborhood of the support of the base test. -/
theorem integral_fiberEnergy_sub_const_mul_laplacian {n : ℕ} (hn : 0 < n)
    {R ρ r c : ℝ} (hR : 0 < R) (hrρ : r < ρ)
    {q : ComplexModel (n + 1) → ℝ} (hq : ContDiff ℝ ∞ q)
    (hs : IsSmoothPshOn (fiberEnergyCylinder n R r) q)
    (hBoundary : ∀ (z : ComplexModel n) (w : ComplexModel 1), ‖z‖ = R → ‖w‖ < ρ →
      q ((complexProductCoordinates n 1).symm (z, w)) = c)
    (hP : ∀ w ∈ ball (0 : E 1) r, ∀ z ∈ unitBall n,
      (KEBall.complexHessian (fun y => q (fiberDilationCoordinates n R (y, w)) - c) z).PosDef)
    {φ : E 1 → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφs : tsupport φ ⊆ ball (0 : E 1) r) :
    (∫ w, fiberEnergy ((fun x => q x - c) ∘ fiberDilationCoordinates n R) w * Δ φ w) =
      (4 * Real.pi / (n + 1 : ℝ)) *
        ∫ x, φ ((complexCoordinates 1).symm ((complexProductCoordinates n 1 x).2))
          ∂topMeasure (isLocallyBoundedPshOn_of_isSmoothPshOn hs) := by
  let e := complexProductCoordinates n 1
  let U := fiberEnergyCylinder n R r
  let q' (x : ComplexModel (n + 1)) := q x - c
  let L := fiberDilationCoordinates n R
  obtain ⟨Q, hQ, hQ0, hEq⟩ := exists_smooth_zeroFiberBoundary hR hrρ hq hBoundary
  have hq' : IsLocallyBoundedPshOn U q' := by
    simpa only [q', sub_eq_add_neg] using
      locallyBoundedPsh_add_const (isLocallyBoundedPshOn_of_isSmoothPshOn hs) (-c)
  have hUeq : EqOn Q q' (U : Set (ComplexModel (n + 1))) :=
    fun x hx => hEq x (mem_fiberEnergyCylinder.mp hx).2.le
  have hQP : IsSmoothPshOn U Q := isSmoothPshOn_of_psh hQ.contDiffOn (by
    intro x hx
    have hE : (fun y => (q' y : EReal)) =ᶠ[𝓝 x] (fun y => (Q y : EReal)) := by
      filter_upwards [U.isOpen.mem_nhds hx] with y hy
      rw [hUeq hy]
    exact (hq'.1 x hx).congr hE)
  have hMeas : topMeasure (isLocallyBoundedPshOn_of_isSmoothPshOn hQP) =
      topMeasure (isLocallyBoundedPshOn_of_isSmoothPshOn hs) := by
    rw [topMeasure_congr _ hq' hUeq]
    exact topMeasure_add_const (isLocallyBoundedPshOn_of_isSmoothPshOn hs) (-c)
  have hFiber (w : E 1) (hw : w ∈ ball (0 : E 1) r) :
      (fun y => Q (L (y, w))) = fun y => q' (L (y, w)) := by
    funext z
    apply hEq
    have hL : e (L (z, w)) = (R • complexCoordinates n z, complexCoordinates 1 w) :=
      e.apply_symm_apply _
    rw [hL, LinearIsometryEquiv.norm_map]
    exact (mem_ball_zero_iff.mp hw).le
  have hQP' (w : E 1) (hw : w ∈ ball (0 : E 1) r) (z : E n) (hz : z ∈ unitBall n) :
      (KEBall.complexHessian (fun y => Q (L (y, w))) z).PosDef := by
    rw [hFiber w hw]
    exact hP w hw z hz
  rw [← hMeas, ← integral_fiberEnergy_mul_laplacian hn hR hQ hQP hQ0 hQP' hφ hφc hφs]
  apply integral_congr_ae
  filter_upwards with w
  by_cases hw : w ∈ ball (0 : E 1) r
  · unfold fiberEnergy
    change signedSmoothEnergy (fun z => q' (L (z, w))) * Δ φ w =
      signedSmoothEnergy (fun z => Q (L (z, w))) * Δ φ w
    rw [hFiber w hw]
  · have hzero : Δ φ w = 0 := image_eq_zero_of_notMem_tsupport
      (fun h => hw (hφs (tsupport_laplacian_subset φ h)))
    rw [hzero, mul_zero, mul_zero]

end KEBall.BedfordTaylor
