import KEBall.RealHessian
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Tangential and mixed Hessians from the actual zero sphere boundary value

The sphere identities are derived by differentiating genuine great circles.
They are then extended from unit tangent vectors by homogeneity and polarization.
No tangent Hessian formula or second fundamental form is an input hypothesis.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped ContDiff Topology

namespace KEBall

noncomputable def greatCircle {n : ℕ} (x v : E n) (s : ℝ) : E n :=
  Real.cos s • x + Real.sin s • v

noncomputable def greatCircleVelocity {n : ℕ} (x v : E n) (s : ℝ) : E n :=
  (-Real.sin s) • x + Real.cos s • v

@[simp] theorem greatCircle_zero {n : ℕ} (x v : E n) : greatCircle x v 0 = x := by
  simp [greatCircle]

@[simp] theorem greatCircleVelocity_zero {n : ℕ} (x v : E n) :
    greatCircleVelocity x v 0 = v := by
  simp [greatCircleVelocity]

theorem greatCircle_mem_sphere {n : ℕ} {x v : E n} (hx : x ∈ unitSphere n)
    (hv : ‖v‖ = 1) (horth : inner ℝ x v = 0) (s : ℝ) :
    greatCircle x v s ∈ unitSphere n := by
  have hxn : ‖x‖ = 1 := by
    simpa only [unitSphere, Metric.mem_sphere, dist_zero_right] using hx
  have hsq : ‖greatCircle x v s‖ ^ 2 = 1 := by
    rw [greatCircle, norm_add_sq_real]
    simp only [norm_smul, Real.norm_eq_abs, hxn, hv, mul_one, sq_abs,
      real_inner_smul_left, real_inner_smul_right, horth, mul_zero, add_zero]
    exact Real.cos_sq_add_sin_sq s
  have hn : ‖greatCircle x v s‖ = 1 := by
    nlinarith [norm_nonneg (greatCircle x v s)]
  simpa only [unitSphere, Metric.mem_sphere, dist_zero_right] using hn

theorem greatCircle_hasDerivAt {n : ℕ} (x v : E n) (s : ℝ) :
    HasDerivAt (greatCircle x v) (greatCircleVelocity x v s) s :=
  ((Real.hasDerivAt_cos s).smul_const x).add ((Real.hasDerivAt_sin s).smul_const v)

theorem greatCircleVelocity_hasDerivAt {n : ℕ} (x v : E n) (s : ℝ) :
    HasDerivAt (greatCircleVelocity x v) (-greatCircle x v s) s := by
  have h := ((Real.hasDerivAt_sin s).neg.smul_const x).add
    ((Real.hasDerivAt_cos s).smul_const v)
  change HasDerivAt (greatCircleVelocity x v) ((-Real.cos s) • x + (-Real.sin s) • v) s at h
  convert h using 1
  simp only [greatCircle, neg_add, neg_smul]

theorem greatCircle_potential_derivative_zero {n : ℕ} {u : E n → ℝ}
    (hu : SmoothNear (closedUnitBall n) u) (hzero : ∀ y ∈ unitSphere n, u y = 0)
    {x v : E n} (hx : x ∈ unitSphere n) (hv : ‖v‖ = 1)
    (horth : inner ℝ x v = 0) (s : ℝ) :
    fderiv ℝ u (greatCircle x v s) (greatCircleVelocity x v s) = 0 := by
  have hpoint := greatCircle_mem_sphere hx hv horth s
  have hud := (hu.contDiffAt (Metric.sphere_subset_closedBall hpoint)).differentiableAt (by simp)
  have h := hud.hasFDerivAt.comp_hasDerivAt s (greatCircle_hasDerivAt x v s)
  have heq : u ∘ greatCircle x v = fun _ : ℝ => (0 : ℝ) := by
    funext r
    exact hzero _ (greatCircle_mem_sphere hx hv horth r)
  rw [heq] at h
  simpa only [deriv_const] using h.deriv.symm

theorem sphere_unit_tangent_deriv_zero {n : ℕ} {u : E n → ℝ}
    (hu : SmoothNear (closedUnitBall n) u) (hzero : ∀ y ∈ unitSphere n, u y = 0)
    {x v : E n} (hx : x ∈ unitSphere n) (hv : ‖v‖ = 1)
    (horth : inner ℝ x v = 0) : fderiv ℝ u x v = 0 := by
  simpa only [greatCircle_zero, greatCircleVelocity_zero] using
    greatCircle_potential_derivative_zero hu hzero hx hv horth 0

theorem sphere_unit_tangent_hessian {n : ℕ} {u : E n → ℝ}
    (hu : SmoothNear (closedUnitBall n) u) (hzero : ∀ y ∈ unitSphere n, u y = 0)
    {x v : E n} (hx : x ∈ unitSphere n) (hv : ‖v‖ = 1)
    (horth : inner ℝ x v = 0) : realHessian u x v v = fderiv ℝ u x x := by
  have hux := hu.contDiffAt (Metric.sphere_subset_closedBall hx)
  have hdf : HasFDerivAt (fderiv ℝ u) (realHessian u x) x :=
    ((hux.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)).hasFDerivAt
  have hdcurve : HasDerivAt (fun s => fderiv ℝ u (greatCircle x v s))
      (realHessian u x v) 0 := by
    have h := hdf.comp_hasDerivAt_of_eq 0 (greatCircle_hasDerivAt x v 0)
      (greatCircle_zero x v).symm
    simpa only [Function.comp_def, greatCircleVelocity_zero] using h
  have haccel : HasDerivAt (greatCircleVelocity x v) (-x) 0 := by
    simpa only [greatCircle_zero] using greatCircleVelocity_hasDerivAt x v 0
  have hsecond := hdcurve.clm_apply haccel
  have heq : (fun s => fderiv ℝ u (greatCircle x v s) (greatCircleVelocity x v s)) =
      fun _ : ℝ => (0 : ℝ) := by
    funext s
    exact greatCircle_potential_derivative_zero hu hzero hx hv horth s
  rw [heq] at hsecond
  have hh := hsecond.deriv
  simp only [greatCircleVelocity_zero, greatCircle_zero, map_neg, deriv_const] at hh
  linarith

theorem sphere_tangent_deriv_zero {n : ℕ} {u : E n → ℝ}
    (hu : SmoothNear (closedUnitBall n) u) (hzero : ∀ y ∈ unitSphere n, u y = 0)
    {x X : E n} (hx : x ∈ unitSphere n) (horth : inner ℝ x X = 0) :
    fderiv ℝ u x X = 0 := by
  by_cases hX : X = 0
  · simp [hX]
  · let v : E n := ‖X‖⁻¹ • X
    have hnorm : ‖X‖ ≠ 0 := norm_ne_zero_iff.mpr hX
    have hv : ‖v‖ = 1 := by
      simp only [v, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg X)]
      exact inv_mul_cancel₀ hnorm
    have horthv : inner ℝ x v = 0 := by
      simp only [v, real_inner_smul_right, horth, mul_zero]
    have hre : ‖X‖ • v = X := by
      simp only [v, smul_smul, mul_inv_cancel₀ hnorm, one_smul]
    have hz := sphere_unit_tangent_deriv_zero hu hzero hx hv horthv
    rw [← hre, map_smul, hz, smul_zero]

theorem sphere_tangent_hessian_self {n : ℕ} {u : E n → ℝ}
    (hu : SmoothNear (closedUnitBall n) u) (hzero : ∀ y ∈ unitSphere n, u y = 0)
    {x X : E n} (hx : x ∈ unitSphere n) (horth : inner ℝ x X = 0) :
    realHessian u x X X = fderiv ℝ u x x * ‖X‖ ^ 2 := by
  by_cases hX : X = 0
  · simp [hX]
  · let v : E n := ‖X‖⁻¹ • X
    have hnorm : ‖X‖ ≠ 0 := norm_ne_zero_iff.mpr hX
    have hv : ‖v‖ = 1 := by
      simp only [v, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg X)]
      exact inv_mul_cancel₀ hnorm
    have horthv : inner ℝ x v = 0 := by
      simp only [v, real_inner_smul_right, horth, mul_zero]
    have hre : ‖X‖ • v = X := by
      simp only [v, smul_smul, mul_inv_cancel₀ hnorm, one_smul]
    have hh := sphere_unit_tangent_hessian hu hzero hx hv horthv
    conv_lhs => rw [← hre]
    simp only [map_smul, smul_apply, smul_eq_mul, hh]
    ring

/-- The genuine tangent Hessian identity used to determine the horizontal
complex Hessian block at every sphere point. -/
theorem sphere_tangent_hessian {n : ℕ} {u : E n → ℝ}
    (hu : SmoothNear (closedUnitBall n) u) (hzero : ∀ y ∈ unitSphere n, u y = 0)
    {x X Y : E n} (hx : x ∈ unitSphere n)
    (hX : inner ℝ x X = 0) (hY : inner ℝ x Y = 0) :
    realHessian u x X Y = 2 * boundarySlope u x * inner ℝ X Y := by
  have hsum : inner ℝ x (X + Y) = 0 := by rw [inner_add_right, hX, hY, zero_add]
  have hXX := sphere_tangent_hessian_self hu hzero hx hX
  have hYY := sphere_tangent_hessian_self hu hzero hx hY
  have hsumH := sphere_tangent_hessian_self hu hzero hx hsum
  simp only [map_add, add_apply, norm_add_sq_real] at hsumH
  rw [realHessian_symm (hu.contDiffAt (Metric.sphere_subset_closedBall hx)) Y X] at hsumH
  unfold boundarySlope
  nlinarith

theorem fderiv_boundarySlope {n : ℕ} {u : E n → ℝ} {x : E n}
    (hu : ContDiffAt ℝ ∞ u x) (X : E n) :
    fderiv ℝ (boundarySlope u) x X =
      (realHessian u x X x + fderiv ℝ u x X) / 2 := by
  have hdf : HasFDerivAt (fderiv ℝ u) (realHessian u x) x :=
    ((hu.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)).hasFDerivAt
  have hpair := hdf.clm_apply (hasFDerivAt_id x)
  have ht := hpair.mul_const ((2 : ℝ)⁻¹)
  change HasFDerivAt (boundarySlope u) _ x at ht
  rw [ht.fderiv]
  simp only [smul_apply, smul_eq_mul, add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.id_apply, id_eq]
  ring

/-- The mixed normal/tangent Hessian identity, from differentiating the
actual extension `t(y) = Du_y(y)/2` and the proved tangent first derivative. -/
theorem sphere_mixed_hessian {n : ℕ} {u : E n → ℝ}
    (hu : SmoothNear (closedUnitBall n) u) (hzero : ∀ y ∈ unitSphere n, u y = 0)
    {x X : E n} (hx : x ∈ unitSphere n) (hX : inner ℝ x X = 0) :
    realHessian u x X x = 2 * fderiv ℝ (boundarySlope u) x X := by
  rw [fderiv_boundarySlope (hu.contDiffAt (Metric.sphere_subset_closedBall hx)),
    sphere_tangent_deriv_zero hu hzero hx hX]
  ring

theorem sphere_fderiv_normal {n : ℕ} {u : E n → ℝ}
    (hu : SmoothNear (closedUnitBall n) u) (hzero : ∀ y ∈ unitSphere n, u y = 0)
    {x : E n} (hx : x ∈ unitSphere n) (X : E n) :
    fderiv ℝ u x X = 2 * boundarySlope u x * inner ℝ x X := by
  have hnorm : ‖x‖ = 1 := by
    simpa only [unitSphere, Metric.mem_sphere, dist_zero_right] using hx
  have hxx : inner ℝ x x = 1 := by rw [real_inner_self_eq_norm_sq, hnorm, one_pow]
  have horth : inner ℝ x (X - inner ℝ x X • x) = 0 := by
    rw [inner_sub_right, real_inner_smul_right, hxx, mul_one, sub_self]
  have h := sphere_tangent_deriv_zero hu hzero hx horth
  rw [map_sub, map_smul, smul_eq_mul] at h
  unfold boundarySlope
  nlinarith

theorem sphere_partialZ {n : ℕ} {u : E n → ℝ}
    (hu : SmoothNear (closedUnitBall n) u) (hzero : ∀ y ∈ unitSphere n, u y = 0)
    {x : E n} (hx : x ∈ unitSphere n) (i : Fin n) :
    partialZ i (fun y => (u y : ℂ)) x =
      (boundarySlope u x : ℂ) * star (complexCoord x i) := by
  rw [partialZ_ofReal ((hu.contDiffAt (Metric.sphere_subset_closedBall hx)).differentiableAt (by simp)),
    sphere_fderiv_normal hu hzero hx, sphere_fderiv_normal hu hzero hx]
  simp only [realDirection, imagDirection, EuclideanSpace.inner_single_right,
    conj_trivial, one_mul, complexCoord, star_add, star_mul, Complex.star_def,
    Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

theorem sphere_partialBar {n : ℕ} {u : E n → ℝ}
    (hu : SmoothNear (closedUnitBall n) u) (hzero : ∀ y ∈ unitSphere n, u y = 0)
    {x : E n} (hx : x ∈ unitSphere n) (i : Fin n) :
    partialBar i (fun y => (u y : ℂ)) x =
      (boundarySlope u x : ℂ) * complexCoord x i := by
  rw [partialBar_ofReal ((hu.contDiffAt (Metric.sphere_subset_closedBall hx)).differentiableAt (by simp)),
    sphere_partialZ hu hzero hx]
  simp

#print axioms greatCircle_mem_sphere
#print axioms sphere_tangent_deriv_zero
#print axioms sphere_tangent_hessian
#print axioms fderiv_boundarySlope
#print axioms sphere_mixed_hessian
#print axioms sphere_fderiv_normal
#print axioms sphere_partialZ
#print axioms sphere_partialBar

end KEBall
