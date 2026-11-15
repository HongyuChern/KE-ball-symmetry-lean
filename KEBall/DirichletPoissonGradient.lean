import DifferentialGeometry.Analysis.Parabolic.Euclidean.Duhamel.Frozen
import DifferentialGeometry.Analysis.Parabolic.Euclidean.HeatPotential.Estimate
import DifferentialGeometry.Analysis.Schauder.Holder.Basic
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Topology.ContinuousMap.BoundedCompactlySupported

/-!
# A radius-dependent Poisson gradient estimate

The heat representation gives the gradient estimate using only the size of the
function and its actual Euclidean Laplacian.  No real Hessian bound appears on
the right hand side.  Compact support supplies bounded derivatives for the
representation identity; their bounds do not enter the resulting constant.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 500000

open Filter MeasureTheory Metric Set
open scoped ContDiff Laplacian NNReal Topology

noncomputable section

namespace KEBall

open DifferentialGeometry.Analysis.Parabolic.Euclidean
open DifferentialGeometry.Analysis.Schauder

section RealPoisson

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Nontrivial V]

private def poissonBoundedOfCompactSupport {W : Type*} [NormedAddCommGroup W]
    (f : V → W) (hf : Continuous f) (hc : HasCompactSupport f) :
    BoundedContinuousFunction V W :=
  BoundedContinuousFunction.ofNormedAddCommGroup f hf
    (Classical.choose (hf.bounded_above_of_compact_support hc))
    (Classical.choose_spec (hf.bounded_above_of_compact_support hc))

/-- The heat primitive yields a scale-explicit estimate for an actual bounded
twice differentiable function.  The derivative witnesses are identified by
`HasFDerivAt`, rather than independent tensors. -/
theorem norm_fderiv_le_of_bounded_poisson
    (u : BoundedContinuousFunction V ℝ)
    (du : BoundedContinuousFunction V (V →L[ℝ] ℝ))
    (d2u : BoundedContinuousFunction V (V →L[ℝ] V →L[ℝ] ℝ))
    (hu : ∀ x, HasFDerivAt (u : V → ℝ) (du x) x)
    (hdu : ∀ x, HasFDerivAt (du : V → V →L[ℝ] ℝ) (d2u x) x)
    {A L r : ℝ} (hA : 0 ≤ A) (hL : 0 ≤ L) (hr : 0 < r)
    (hAmp : ‖u‖ ≤ A) (hLap : ‖coreLap d2u‖ ≤ L) (x : V) :
    ‖fderiv ℝ (u : V → ℝ) x‖ ≤ heatC1 V * (A / r + 2 * r * L) := by
  let t : ℝ := r ^ 2
  have ht : 0 < t := sq_pos_of_pos hr
  let B : ℝ≥0 := ⟨L, hL⟩
  let f : ℝ → BoundedContinuousFunction V ℝ := fun _ => coreLap d2u
  have hbound : ∀ s ∈ Icc (0 : ℝ) t, ‖f s‖ ≤ B := fun _ _ => hLap
  have hsource : ContinuousOn (fun p : ℝ × V => f p.1 p.2)
      (Ioo (0 : ℝ) t ×ˢ (univ : Set V)) :=
    ((coreLap d2u).continuous.comp continuous_snd).continuousOn
  have hm0 := fun z => heatSup_timeSource_aestronglyMeasurable_of_continuousOn
    ht.le f hsource z
  have hm1 := fun z => heatSupGradient_timeSource_aestronglyMeasurable_of_continuousOn
    ht.le f hsource z
  have hulip : LipschitzWith ‖du‖₊ (u : V → ℝ) := by
    apply lipschitzWith_of_nnnorm_fderiv_le (𝕜 := ℝ)
    · exact fun y => (hu y).differentiableAt
    · intro y
      rw [(hu y).fderiv]
      exact_mod_cast du.norm_coe_le_norm y
  have huzero : HolderWith (2 * ‖u‖₊) 0 (u : V → ℝ) :=
    holderWith_zero_of_norm_le u.norm_coe_le_norm
  have huhalf : HolderWith (max (2 * ‖u‖₊) ‖du‖₊) (1 / 2 : ℝ≥0) (u : V → ℝ) :=
    huzero.of_le_of_le hulip.holderWith (by positivity) (by norm_num)
  have hrep : (u : V → ℝ) = (fun y => heatSup t u y) - heatDuhamel t f := by
    funext y
    rw [Pi.sub_apply, heatDuhamel_const_eq_integral_heatSup]
    rw [heatSup_primitive ht u du d2u hu hdu huhalf y]
    ring
  have hd := (heatSup_hasFDerivAt ht u x).sub
    (heatDuhamel_hasFDerivAt ht f hbound hm0 hm1 x)
  rw [← hrep] at hd
  rw [hd.fderiv]
  have hheat := heatSupGradient_norm_le ht u x
  have hpot := heatDuhamelGradientMap_norm_le ht f hbound x (hm1 x)
  have hscale : heatScale t = r := by exact Real.sqrt_sq hr.le
  have hsqrt : Real.sqrt t = r := Real.sqrt_sq hr.le
  rw [hscale] at hheat
  rw [hsqrt] at hpot
  have hC : 0 ≤ heatC1 V := heatC1_nonneg
  calc
    _ ≤ ‖heatSupGradient t u x‖ + ‖heatDuhamelGradientMap t f x‖ := norm_sub_le _ _
    _ ≤ r⁻¹ * heatC1 V * A + 2 * L * heatC1 V * r := by
      exact add_le_add (hheat.trans (mul_le_mul_of_nonneg_left hAmp (by positivity))) hpot
    _ = _ := by ring

/-- The genuine Euclidean Laplacian, for smooth compactly supported real
functions, controls the gradient at every positive scale. -/
theorem norm_fderiv_le_of_compactSupport_laplacian_bound
    {u : V → ℝ} (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u)
    {A L r : ℝ} (hA : 0 ≤ A) (hL : 0 ≤ L) (hr : 0 < r)
    (hAmp : ∀ y, ‖u y‖ ≤ A) (hLap : ∀ y, ‖Δ u y‖ ≤ L) (x : V) :
    ‖fderiv ℝ u x‖ ≤ heatC1 V * (A / r + 2 * r * L) := by
  have hu1 : ContDiff ℝ ∞ (fderiv ℝ u) := hu.fderiv_right (by simp)
  have hu2 : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ u)) := hu1.fderiv_right (by simp)
  let u0 := poissonBoundedOfCompactSupport u hu.continuous hc
  let u1 := poissonBoundedOfCompactSupport (fderiv ℝ u)
    hu1.continuous (hc.fderiv ℝ)
  let u2 := poissonBoundedOfCompactSupport (fderiv ℝ (fderiv ℝ u))
    hu2.continuous ((hc.fderiv ℝ).fderiv ℝ)
  have hEq (y : V) : coreLap u2 y = Δ u y := by
    rw [coreLap_apply, InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
    simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    rfl
  have h0 : ‖u0‖ ≤ A := (BoundedContinuousFunction.norm_le hA).mpr hAmp
  have h2 : ‖coreLap u2‖ ≤ L := (BoundedContinuousFunction.norm_le hL).mpr
    (fun y => (hEq y).symm ▸ hLap y)
  exact norm_fderiv_le_of_bounded_poisson u0 u1 u2
    (fun y => (hu.differentiable (by simp) y).hasFDerivAt)
    (fun y => (hu1.differentiable (by simp) y).hasFDerivAt)
    hA hL hr h0 h2 x

end RealPoisson

end KEBall
