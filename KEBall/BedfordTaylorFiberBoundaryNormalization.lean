import KEBall.BedfordTaylorProductFiberCollar
import KEBall.BedfordTaylorSmoothFiberCurvature

/-!
# Boundary normalization for the smooth approximation on a larger fiber
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Metric Set TopologicalSpace
open scoped ContDiff Topology

namespace KEBall.BedfordTaylor

open PshLines.FirstPass (ComplexModel)
open PshLines.Regularization.HolomorphicPullback

theorem tendsto_productFiberKernelSecondMoment (n m : ℕ) {s : ℝ} (hs : 0 < s) :
    Tendsto (productFiberKernelSecondMoment n m s hs) atTop (𝓝 0) := by
  refine tendsto_const_nhds.squeeze (Cegrell.radialKernelSecondMoment_tendsto (n + m) hs) ?_ ?_
  · intro j
    exact integral_nonneg fun t => mul_nonneg (sq_nonneg _)
      (explicitRadialKernel_nonneg s hs j t)
  · intro j
    let k := explicitRadialKernel (n := n + m) s hs j
    have hc := (explicitRadialKernel_contDiff (n := n + m) s hs j).continuous
    have hk := explicitRadialKernel_hasCompactSupport (n := n + m) s hs j
    have h₁ : Integrable (fun t : ComplexModel (n + m) => ‖(complexProductCoordinates n m t).1‖ ^ 2 * k t) :=
      (((complexProductCoordinates n m).continuous.fst.norm.pow 2).mul hc).integrable_of_hasCompactSupport
        hk.mul_left
    have h₂ : Integrable (fun t : ComplexModel (n + m) => ‖t‖ ^ 2 * k t) :=
      ((continuous_norm.pow 2).mul hc).integrable_of_hasCompactSupport hk.mul_left
    exact integral_mono h₁ h₂ fun t => mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (norm_nonneg _) (norm_fst_complexProductCoordinates_le t) _)
      (explicitRadialKernel_nonneg s hs j t)

/-- On the interior where the base cutoff is one, normalize by subtracting
the fiber boundary value. Outside its support the family is zero. -/
theorem exists_smooth_zeroFiberBoundary {n : ℕ} {R ρ r c : ℝ} (hR : 0 < R)
    (hrρ : r < ρ) {q : ComplexModel (n + 1) → ℝ} (hq : ContDiff ℝ ∞ q)
    (hBoundary : ∀ (z : ComplexModel n) (w : ComplexModel 1), ‖z‖ = R → ‖w‖ < ρ →
      q ((complexProductCoordinates n 1).symm (z, w)) = c) :
    ∃ Q : ComplexModel (n + 1) → ℝ, ContDiff ℝ ∞ Q ∧
      (∀ w z, z ∈ unitSphere n → Q (fiberDilationCoordinates n R (z, w)) = 0) ∧
      (∀ x, ‖(complexProductCoordinates n 1 x).2‖ ≤ r → Q x = q x - c) := by
  let e := complexProductCoordinates n 1
  let B : Opens (ComplexModel 1) := ⟨ball 0 ρ, isOpen_ball⟩
  obtain ⟨χ, _, hχ⟩ := exists_testFunction_one_on (U := B) (isCompact_closedBall (0 : ComplexModel 1) r)
    (closedBall_subset_ball hrρ)
  let Q (x : ComplexModel (n + 1)) := χ (e x).2 * (q x - c)
  let er := e.toContinuousLinearMap.restrictScalars ℝ
  have hχQ : ContDiff ℝ ∞ (fun x => χ (e x).2) := χ.contDiff.comp er.contDiff.snd
  refine ⟨Q, hχQ.mul (hq.sub contDiff_const), ?_, ?_⟩
  · intro w z hz
    have hZ : ‖z‖ = 1 := by
      simpa only [unitSphere, mem_sphere, dist_zero_right] using hz
    rw [fiberDilationCoordinates_apply]
    dsimp only [Q]
    rw [show complexProductCoordinates n 1 = e from rfl, e.apply_symm_apply]
    by_cases hw : ‖complexCoordinates 1 w‖ < ρ
    · have hzR : ‖R • complexCoordinates n z‖ = R := by
        rw [norm_smul, Real.norm_of_nonneg hR.le, LinearIsometryEquiv.norm_map, hZ, mul_one]
      rw [hBoundary _ _ hzR hw, sub_self, mul_zero]
    · have hwB : complexCoordinates 1 w ∉ (B : Set (ComplexModel 1)) :=
        fun h => hw (mem_ball_zero_iff.mp h)
      rw [image_eq_zero_of_notMem_tsupport (fun h => hwB (χ.tsupport_subset h)), zero_mul]
  · intro x hx
    change χ (e x).2 * (q x - c) = _
    rw [hχ (mem_closedBall_zero_iff.mpr hx), Pi.one_apply, one_mul]

end KEBall.BedfordTaylor
