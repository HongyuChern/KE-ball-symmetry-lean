import KEBall.ComplexMaximum
import KEBall.MetricConnection
import KEBall.SphereMeasure
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.MeasureTheory.Function.Jacobian

/-!
# The real gradient-image estimate on the unit ball
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Metric Set
open scoped ContDiff ENNReal Gradient Topology

namespace KEBall

/-- Points in the open ball where the real Hessian is positive semidefinite. -/
def nonnegHessianSet {n : ℕ} (u : E n → ℝ) : Set (E n) :=
  {x ∈ unitBall n | ∀ v, 0 ≤ realHessian u x v v}

theorem measurableSet_nonnegHessianSet {n : ℕ} {u : E n → ℝ}
    (hu : SmoothNear (closedUnitBall n) u) : MeasurableSet (nonnegHessianSet u) := by
  have hOpen : IsOpen (⋃ v : E n, unitBall n ∩
      (fun x => realHessian u x v v) ⁻¹' Iio 0) := by
    apply isOpen_iUnion
    intro v
    have hC : ContinuousOn (fun x => realHessian u x v v) (unitBall n) := by
      intro x hx
      exact (((realHessian_contDiffAt (hu.contDiffAt (ball_subset_closedBall hx))).clm_apply
        contDiffAt_const).clm_apply contDiffAt_const).continuousAt.continuousWithinAt
    exact hC.isOpen_inter_preimage isOpen_ball isOpen_Iio
  have hS : nonnegHessianSet u = unitBall n \
      (⋃ v : E n, unitBall n ∩ (fun x => realHessian u x v v) ⁻¹' Iio 0) := by
    ext x
    simp only [nonnegHessianSet, mem_ofPred_eq, Set.mem_sdiff, mem_iUnion, mem_inter_iff, mem_preimage,
      mem_Iio, not_exists, not_and, not_lt]
    exact ⟨fun hx => ⟨hx.1, fun v _ => hx.2 v⟩, fun hx => ⟨hx.1, fun v => hx.2 v hx.1⟩⟩
  rw [hS]
  exact measurableSet_ball.diff hOpen.measurableSet

private theorem ball_subset_gradient_image {n : ℕ} {u : E n → ℝ}
    (hu : SmoothNear (closedUnitBall n) u) (hu0 : ∀ x ∈ unitSphere n, u x = 0)
    {x : E n} (hx : x ∈ closedUnitBall n) :
    ball (0 : E n) (-u x / 2) ⊆ (∇ u) '' nonnegHessianSet u := by
  intro q hq
  let L := InnerProductSpace.toDual ℝ (E n) q
  let w (y : E n) := L y - u y
  have hC : ContinuousOn w (closedUnitBall n) := L.continuous.continuousOn.sub
    (fun y hy => (hu.contDiffAt hy).continuousAt.continuousWithinAt)
  have hne : (closedUnitBall n).Nonempty := ⟨x, hx⟩
  obtain ⟨z, hz, hzMax⟩ := (isCompact_closedBall (0 : E n) 1).exists_isMaxOn hne hC
  have hzB : z ∈ unitBall n := by
    have hzNorm : ‖z‖ ≤ 1 := mem_closedBall_zero_iff.mp hz
    rcases hzNorm.lt_or_eq with hlt | heq
    · exact mem_ball_zero_iff.mpr hlt
    have hzS : z ∈ unitSphere n := mem_sphere_zero_iff_norm.mpr heq
    have h := hzMax hx
    change L x - u x ≤ L z - u z at h
    rw [hu0 z hzS, sub_zero] at h
    have hDist : ‖z - x‖ ≤ 2 := (norm_sub_le z x).trans
      (by linarith only [hzNorm, mem_closedBall_zero_iff.mp hx])
    have hLp : L (z - x) ≤ ‖q‖ * 2 := by
      change inner ℝ q (z - x) ≤ _
      exact (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left hDist (norm_nonneg q))
    rw [map_sub] at hLp
    have hq' := mem_ball_zero_iff.mp hq
    linarith only [h, hLp, hq']
  have hLoc := hzMax.isLocalMax
    (mem_of_superset (isOpen_ball.mem_nhds hzB) ball_subset_closedBall)
  have huAt := hu.contDiffAt hz
  have huDiff := huAt.differentiableAt (by simp)
  have hw := (L.contDiff.contDiffAt.sub huAt : ContDiffAt ℝ ∞ w z)
  have hwDeriv : fderiv ℝ w z = L - fderiv ℝ u z :=
    (L.hasFDerivAt.sub huDiff.hasFDerivAt).fderiv
  have hzDeriv : L = fderiv ℝ u z := sub_eq_zero.mp (hwDeriv.symm.trans hLoc.fderiv_eq_zero)
  refine ⟨z, ⟨hzB, fun v => ?_⟩, ?_⟩
  · have he : fderiv ℝ w =ᶠ[𝓝 z] fun y => L - fderiv ℝ u y := by
      filter_upwards [(huAt.of_le (m := 1) (by simp)).eventually (by simp)] with y hy
      exact (L.hasFDerivAt.sub (hy.differentiableAt one_ne_zero).hasFDerivAt).fderiv
    have hNeg := realHessian_nonpos_of_isLocalMax hw hLoc v
    have hD := (huAt.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
    unfold realHessian at hNeg ⊢
    rw [he.fderiv_eq, (hD.hasFDerivAt.const_sub L).fderiv] at hNeg
    simpa only [neg_apply, neg_nonpos] using hNeg
  · change (InnerProductSpace.toDual ℝ (E n)).symm (fderiv ℝ u z) = q
    rw [← hzDeriv]
    exact (InnerProductSpace.toDual ℝ (E n)).symm_apply_apply q

/-- The ball of supporting slopes is bounded in volume by the real Hessian
Jacobian on the positive-semidefinite locus. -/
theorem volume_ball_le_lintegral_det_gradient {n : ℕ} {u : E n → ℝ}
    (hu : SmoothNear (closedUnitBall n) u) (hu0 : ∀ x ∈ unitSphere n, u x = 0)
    {x : E n} (hx : x ∈ closedUnitBall n) :
    volume (ball (0 : E n) (-u x / 2)) ≤
      ∫⁻ y in nonnegHessianSet u, ENNReal.ofReal |(fderiv ℝ (∇ u) y).det| := by
  refine (measure_mono (ball_subset_gradient_image hu hu0 hx)).trans ?_
  apply addHaar_image_le_lintegral_abs_det_fderiv volume (measurableSet_nonnegHessianSet hu)
  intro y hy
  have huAt := hu.contDiffAt (ball_subset_closedBall hy.1)
  have hD := (huAt.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  have hG : DifferentiableAt ℝ (∇ u) y :=
    (InnerProductSpace.toDual ℝ (E n)).symm.toContinuousLinearEquiv.differentiableAt.comp y hD
  exact hG.hasFDerivAt.hasFDerivWithinAt

end KEBall
