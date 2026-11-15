import KEBall.BedfordTaylorFiberCollarCurvature
import KEBall.BedfordTaylorLocallyBoundedMonotone

/-!
# Distributional curvature of the energy of the extended fibers
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Metric Set TopologicalSpace
open scoped ContDiff Laplacian Topology

namespace KEBall.BedfordTaylor

open MoserTrudinger
open PshLines
open PshLines.FirstPass (ComplexModel)
open PshLines.FirstPass.MongeAmpere (IsLocallyBoundedPshOn)

/-- The actual Bedford–Taylor energy of the extended fibers has the
projected cylinder measure as its base Laplacian. -/
theorem integral_bedfordTaylorFiberEnergy_mul_laplacian_productFiberExtension
    {n : ℕ} (hn : 0 < n) {A : ℝ} (hA : 0 < A)
    {v : ComplexModel (n + 1) → ℝ}
    (hp : IsLocallyBoundedPshOn (complexProductCylinder n 1)
      (gluedMax (complexProductBall n 1 : Set (ComplexModel (n + 1))) v
        (fun x => A * productFiberQuadratic n 1 x)))
    {r : ℝ} (hr : r < 1)
    {φ : E 1 → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφs : tsupport φ ⊆ ball (0 : E 1) r) :
    Integrable (fun w => bedfordTaylorFiberEnergy
      (IsLocallyBoundedPshOn.mono hp (fiberEnergyCylinder_le_complexProductCylinder 2 le_rfl)) w *
        Δ φ w) ∧
    (∫ w, bedfordTaylorFiberEnergy
        (IsLocallyBoundedPshOn.mono hp (fiberEnergyCylinder_le_complexProductCylinder 2 le_rfl)) w *
      Δ φ w) =
      (4 * Real.pi / (n + 1 : ℝ)) *
        ∫ x, φ ((complexCoordinates 1).symm (complexProductCoordinates n 1 x).2)
          ∂topMeasure hp := by
  classical
  let e := complexProductCoordinates n 1
  let c := complexCoordinates 1
  let Ω := complexProductCylinder n 1
  let P := complexProductBall n 1
  let p := gluedMax (P : Set (ComplexModel (n + 1))) v (fun x => A * productFiberQuadratic n 1 x)
  obtain ⟨ρ, hrρ, hρ⟩ := exists_between hr
  let W := fiberEnergyCylinder n 3 ρ
  let U := fiberEnergyCylinder n 2 r
  let hWΩ : W ≤ Ω := fiberEnergyCylinder_le_complexProductCylinder 3 hρ.le
  let hUW : U ≤ W := fiberEnergyCylinder_mono (by norm_num) hrρ.le
  let hpW := IsLocallyBoundedPshOn.mono hp hWΩ
  let g (x : ComplexModel (n + 1)) := φ (c.symm (e x).2)
  have hpEq (x : ComplexModel (n + 1)) (hx : 1 < ‖(e x).1‖) :
      p x = A * ‖(e x).1‖ ^ 2 + -A := by
    have hxP : x ∉ (P : Set (ComplexModel (n + 1))) :=
      fun h => (not_lt_of_ge hx.le) (mem_complexProductBall.mp h).1
    simp only [p, gluedMax, if_neg hxP, productFiberQuadratic, e]
    ring
  obtain ⟨q, a, d, hApp, hq, ha, haLim, hdLim, hEq, hP⟩ :=
    exists_productFiber_curvatureApproximation hρ hA hp
  let hqW (j : ℕ) := isLocallyBoundedPshOn_of_isSmoothPshOn (hApp.1 j)
  have hpE (x : ComplexModel (n + 1)) (_ : x ∈ W) (hx : (3 / 2 : ℝ) < ‖(e x).1‖) :
      p x = A * ‖(e x).1‖ ^ 2 + -A := hpEq x ((by norm_num : (1 : ℝ) < 3 / 2).trans hx)
  have hqE (j : ℕ) (x : ComplexModel (n + 1)) (hx : x ∈ W) (hx' : (3 / 2 : ℝ) < ‖(e x).1‖) :
      q j x = a j * ‖(e x).1‖ ^ 2 + d j := hEq j x hx hx'.le
  have hLeft := tendsto_integral_fiberEnergy_mul_of_quadratic_collar hn hrρ hρ.le hA hp
    hApp hq hpE ha haLim hdLim hqE (integrable_laplacian_of_compactSupport hφ hφc)
    (fun w hw => image_eq_zero_of_notMem_tsupport
      (fun h => hw (hφs (tsupport_laplacian_subset φ h))))
  let B : Opens (ComplexModel n) := ballDomain 0 2
  obtain ⟨χ, _, hχ⟩ := exists_testFunction_one_on (U := B)
    (isCompact_closedBall (0 : ComplexModel n) (3 / 2)) (closedBall_subset_ball (by norm_num))
  have hχ1 (z : ComplexModel n) (hz : ‖z‖ ≤ 3 / 2) : χ z = 1 :=
    hχ (mem_closedBall_zero_iff.mpr hz)
  let f (x : ComplexModel (n + 1)) := χ (e x).1 * g x
  have hfC : Continuous f := (χ.continuous.comp e.continuous.fst).mul
    (hφ.continuous.comp (c.symm.continuous.comp e.continuous.snd))
  obtain ⟨hf, hfU⟩ := hasCompactSupport_fiberBaseTest χ.hasCompactSupport χ.tsupport_subset hφc hφs
  have hfW : tsupport f ⊆ W := hfU.trans hUW
  have hRight := tendsto_topMeasure_of_decreasing hpW hqW hApp.2.1 hApp.2.2 f hfC hf hfW
  have hStep (j : ℕ) : (∫ w, fiberEnergy (q j ∘ fiberDilationCoordinates n 2) w * Δ φ w) =
      (4 * Real.pi / (n + 1 : ℝ)) * ∫ x, f x ∂topMeasure (hqW j) := by
    have h := integral_fiberEnergy_mul_laplacian_of_quadratic_collar hn hrρ (ha j).1
      (hq j) (hApp.1 j) (hqE j) (hP j) hφ hφc hφs
    rw [integral_topMeasure_baseTest_eq_fiberCutoff hUW (hqW j) (by norm_num)
      (topMeasure_fiberNorm_gt_eq_zero hWΩ (hqW j) (ha j).1 (hqE j)) hχ1 hφs] at h
    exact h
  have hpMass : topMeasure hp {x | 1 < ‖(e x).1‖} = 0 :=
    topMeasure_fiberNorm_gt_eq_zero le_rfl hp hA (fun x _ hx => hpEq x hx)
  have hpAE : ∀ᵐ x ∂topMeasure hp, ‖(e x).1‖ ≤ 1 := by
    simpa only [ae_iff, not_le] using hpMass
  have hFinal : (∫ x, f x ∂topMeasure hpW) = ∫ x, g x ∂topMeasure hp := by
    rw [← topMeasure_restrict hp hWΩ, ← integral_indicator W.isOpen.measurableSet]
    apply integral_congr_ae
    filter_upwards [hpAE] with x hx
    have hχx : χ (e x).1 = 1 := hχ1 _ (hx.trans (by norm_num))
    by_cases hxW : x ∈ W
    · rw [indicator_of_mem hxW]
      simp only [f, hχx, one_mul]
    · rw [indicator_of_notMem hxW]
      change 0 = φ (c.symm (e x).2)
      symm
      apply image_eq_zero_of_notMem_tsupport
      intro hxφ
      have hBase := mem_ball_zero_iff.mp (hφs hxφ)
      have hNorm : ‖c.symm (e x).2‖ = ‖(e x).2‖ := c.symm.norm_map _
      rw [hNorm] at hBase
      exact hxW (mem_fiberEnergyCylinder.mpr ⟨hx.trans_lt (by norm_num), hBase.trans hrρ⟩)
  rw [hFinal] at hRight
  exact ⟨hLeft.1, tendsto_nhds_unique hLeft.2 ((hRight.const_mul (4 * Real.pi / (n + 1 : ℝ))).congr'
    (Eventually.of_forall fun j => (hStep j).symm))⟩

end KEBall.BedfordTaylor
