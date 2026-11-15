import KEBall.BedfordTaylorProductFiberMollification
import KEBall.CegrellQuadraticMollifier

/-!
# The quadratic collar of the mollified fiber extension
-/

set_option autoImplicit false

open MeasureTheory Metric Set
open scoped Topology

namespace KEBall.BedfordTaylor

open PshLines
open PshLines.FirstPass (ComplexModel)
open PshLines.Regularization.HolomorphicPullback

/-- Second moment of the kernel in the fiber variables. -/
noncomputable def productFiberKernelSecondMoment (n m : ℕ) (s : ℝ) (hs : 0 < s) (j : ℕ) : ℝ :=
  ∫ t : ComplexModel (n + m),
    ‖(complexProductCoordinates n m t).1‖ ^ 2 * explicitRadialKernel s hs j t

/-- Outside the unit fiber ball by at least the kernel radius, the
smoothed extension is a fiberwise quadratic plus a constant. -/
theorem translationPairing_gluedMax_fiberQuadratic_eq {n m : ℕ}
    {v : ComplexModel (n + m) → ℝ} {A s : ℝ} (hs : 0 < s) (j : ℕ)
    {K : Set (ComplexModel (n + m))} {x : ComplexModel (n + m)}
    (hK : closedBall x s ⊆ K)
    (hx : 1 + s / ((j : ℝ) + 1) ≤ ‖(complexProductCoordinates n m x).1‖) :
    let b := fun y => A * productFiberQuadratic n m y
    let p := gluedMax (complexProductBall n m : Set (ComplexModel (n + m))) v b
    translationPairing volume (K.indicator p) (explicitRadialKernel s hs j) x =
      A * (productFiberQuadratic n m x + productFiberKernelSecondMoment n m s hs j) := by
  classical
  let e := complexProductCoordinates n m
  let b := fun y => A * productFiberQuadratic n m y
  let p := gluedMax (complexProductBall n m : Set (ComplexModel (n + m))) v b
  let k : ComplexModel (n + m) → ℝ := explicitRadialKernel s hs j
  have heq : translationPairing volume (K.indicator p) k x = translationPairing volume b k x := by
    unfold translationPairing
    apply integral_congr_ae
    filter_upwards with y
    by_cases hy : k (y - x) = 0
    · simp only [hy, mul_zero]
    have hS : y - x ∈ tsupport k := subset_tsupport k hy
    have hr : ‖y - x‖ ≤ s / ((j : ℝ) + 1) := by
      simpa only [k, explicitRadialKernel_tsupport, mem_closedBall, dist_zero_right] using hS
    have hyK : y ∈ K := hK (by
      rw [mem_closedBall, dist_eq_norm]
      exact hr.trans (div_le_self hs.le (le_add_of_nonneg_left (Nat.cast_nonneg j))))
    have hyNorm : ‖(e x).1‖ ≤ ‖(e y).1‖ + s / ((j : ℝ) + 1) := by
      have hsub := norm_sub_le (e y).1 (e (y - x)).1
      rw [map_sub, Prod.fst_sub, sub_sub_cancel] at hsub
      have hd : ‖(e (y - x)).1‖ ≤ s / ((j : ℝ) + 1) :=
        (norm_fst_complexProductCoordinates_le (n := n) (m := m) (y - x)).trans hr
      exact hsub.trans (add_le_add le_rfl hd)
    have hyP : y ∉ (complexProductBall n m : Set (ComplexModel (n + m))) := by
      intro hyP
      have h := (mem_complexProductBall.mp hyP).1
      change 1 + s / ((j : ℝ) + 1) ≤ ‖(e x).1‖ at hx
      linarith only [hyNorm, hx, h]
    rw [indicator_of_mem hyK]
    simp only [p, gluedMax, if_neg hyP]
  change translationPairing volume (K.indicator p) k x =
    A * (productFiberQuadratic n m x + productFiberKernelSecondMoment n m s hs j)
  rw [heq]
  let L : ComplexModel (n + m) →L[ℝ] ComplexModel n :=
    (ContinuousLinearMap.fst ℝ (ComplexModel n) (ComplexModel m)).comp
      (e.toContinuousLinearMap.restrictScalars ℝ)
  exact Cegrell.translationPairing_pullbackQuadratic L A 1 hs j x

end KEBall.BedfordTaylor
