import KEBall.DirichletAngularSecondHessianL2
import KEBall.DirichletRotations

/-!
# The Hessian of the actual twice angular differentiated potential

The moving arguments of the Hessian are retained in the orbit derivative.
Only interior smoothness is used to identify the pointwise limit.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Filter Matrix MeasureTheory Metric Set
open scoped BigOperators ComplexOrder ContDiff Topology

namespace KEBall

local notation "e[" n "]" => EuclideanSpace.basisFun (Fin (2 * n)) ℝ

theorem hasDerivAt_dirichlet_rotated_realHessian {n : ℕ} {u : E n → ℝ}
    (hu : ContDiffOn ℝ ∞ u (unitBall n))
    (S : E n →L[ℝ] E n) (hS : star S = -S)
    {x : E n} (hx : x ∈ unitBall n) (a b : E n) (t : ℝ) :
    HasDerivAt (fun s => realHessian (u ∘ orthogonalFlow S hS s) x a b)
      (realHessian ((fun y => fderiv ℝ u y (S y)) ∘ orthogonalFlow S hS t) x a b) t := by
  let R := orthogonalFlow S hS
  have hMaps : R t x ∈ unitBall n := by
    simpa only [unitBall, mem_ball_zero_iff, LinearIsometryEquiv.norm_map] using hx
  have huAt := hu.contDiffAt (isOpen_ball.mem_nhds hMaps)
  have hH : HasFDerivAt (realHessian u) (fderiv ℝ (realHessian u) (R t x)) (R t x) :=
    ((realHessian_contDiffAt huAt).differentiableAt (by simp)).hasFDerivAt
  have h₁ : HasDerivAt (fun s : ℝ => realHessian u (R s x))
      (realThirdDerivative u (R t x) (R t (S x))) t :=
    HasFDerivAt.comp_hasDerivAt (F := E n) (E := E n →L[ℝ] E n →L[ℝ] ℝ)
      (f := fun s => R s x) t hH (hasDerivAt_orthogonalFlow_apply S hS x t)
  have h := (h₁.clm_apply (hasDerivAt_orthogonalFlow_apply S hS a t)).clm_apply
    (hasDerivAt_orthogonalFlow_apply S hS b t)
  simp_rw [realHessian_comp_linearIsometryEquiv]
  rw [realHessian_linearFieldDerivative isOpen_ball hu hMaps S]
  simpa only [R, realThirdDerivative, _root_.add_apply, orthogonalFlow_apply_generator] using h

theorem realHessian_secondOrthogonalDifference_flow_eq {n : ℕ} {u : E n → ℝ}
    (hu : ContDiffOn ℝ ∞ u (unitBall n))
    (S : E n →L[ℝ] E n) (hS : star S = -S)
    {x : E n} (hx : x ∈ unitBall n) (a b : E n) (t : ℝ) :
    realHessian
      (dirichletOrthogonalDifference (orthogonalFlow S hS t) t
        (dirichletOrthogonalDifference (orthogonalFlow S hS t) t u)) x a b =
      (t ^ 2)⁻¹ * (realHessian (u ∘ orthogonalFlow S hS (2 * t)) x a b -
        2 * realHessian (u ∘ orthogonalFlow S hS t) x a b + realHessian u x a b) := by
  let R := orthogonalFlow S hS t
  have hMaps : MapsTo R (unitBall n) (unitBall n) := by
    intro y hy
    simpa only [unitBall, mem_ball_zero_iff, LinearIsometryEquiv.norm_map] using hy
  have hu2 : ContDiffOn ℝ 2 u (unitBall n) :=
    hu.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have huR : ContDiffOn ℝ 2 (u ∘ R) (unitBall n) :=
    hu2.comp R.toContinuousLinearEquiv.contDiff.contDiffOn hMaps
  have hq := contDiffOn_dirichletOrthogonalDifference_ball R t hu2
  rw [realHessian_dirichletOrthogonalDifference R t
    (hq.contDiffAt (isOpen_ball.mem_nhds hx))
    (hq.contDiffAt (isOpen_ball.mem_nhds (hMaps hx)))]
  rw [← dirichletOrthogonalDifference_comp R t u]
  rw [realHessian_dirichletOrthogonalDifference R t
    (huR.contDiffAt (isOpen_ball.mem_nhds hx))
    (huR.contDiffAt (isOpen_ball.mem_nhds (hMaps hx))),
    realHessian_dirichletOrthogonalDifference R t
      (hu2.contDiffAt (isOpen_ball.mem_nhds hx))
      (hu2.contDiffAt (isOpen_ball.mem_nhds (hMaps hx)))]
  have hRR : (u ∘ R) ∘ R = u ∘ orthogonalFlow S hS (2 * t) := by
    funext y
    simp only [Function.comp_apply, R, ← orthogonalFlow_add_apply, ← two_mul]
  rw [hRR]
  simp only [_root_.smul_apply, _root_.sub_apply, smul_eq_mul]
  dsimp only [R]
  rw [← inv_pow]
  ring

theorem tendsto_realHessian_secondOrthogonalDifference_flow_entry {n : ℕ}
    {u : E n → ℝ} (hu : ContDiffOn ℝ ∞ u (unitBall n))
    (S : E n →L[ℝ] E n) (hS : star S = -S)
    {x : E n} (hx : x ∈ unitBall n) (a b : E n) :
    Tendsto (fun t : ℝ => realHessian
      (dirichletOrthogonalDifference (orthogonalFlow S hS t) t
        (dirichletOrthogonalDifference (orthogonalFlow S hS t) t u)) x a b)
      (𝓝[≠] 0) (𝓝 (realHessian
        (fun y => fderiv ℝ (fun z => fderiv ℝ u z (S z)) y (S y)) x a b)) := by
  let R := orthogonalFlow S hS
  let q (y : E n) := fderiv ℝ u y (S y)
  let F (t : ℝ) := realHessian (u ∘ R t) x a b
  have hq : ContDiffOn ℝ ∞ q (unitBall n) :=
    (hu.fderiv_of_isOpen isOpen_ball (m := ∞) (by simp)).clm_apply S.contDiff.contDiffOn
  have hMaps (t : ℝ) : R t x ∈ unitBall n := by
    simpa only [unitBall, mem_ball_zero_iff, LinearIsometryEquiv.norm_map] using hx
  have hFlow (y : E n) : ContDiff ℝ ∞ (fun t : ℝ => R t y) :=
    (contDiff_orthogonalFlow_apply S hS).comp (contDiff_id.prodMk contDiff_const)
  have hF : ContDiff ℝ ∞ F := by
    apply contDiff_iff_contDiffAt.mpr
    intro t
    have hH := (realHessian_contDiffAt (hu.contDiffAt (isOpen_ball.mem_nhds (hMaps t)))).comp t
      (hFlow x).contDiffAt
    simp only [F, realHessian_comp_linearIsometryEquiv]
    convert! ((hH.clm_apply (hFlow a).contDiffAt).clm_apply (hFlow b).contDiffAt) using 1
  have hF' : deriv F = fun t => realHessian (q ∘ R t) x a b :=
    funext (fun t => (hasDerivAt_dirichlet_rotated_realHessian hu S hS hx a b t).deriv)
  have hF'' : iteratedDeriv 2 F 0 =
      realHessian (fun y => fderiv ℝ q y (S y)) x a b := by
    rw [iteratedDeriv_succ (n := 1), iteratedDeriv_one, hF']
    have h := (hasDerivAt_dirichlet_rotated_realHessian hq S hS hx a b 0).deriv
    have hZero : (fun y => fderiv ℝ q y (S y)) ∘ R 0 =
        (fun y => fderiv ℝ q y (S y)) := by
      funext y
      simp only [Function.comp_apply, R, orthogonalFlow_zero_apply]
    simpa only [R, hZero] using h
  have h := tendsto_dirichlet_second_forward_quotient
    (hF.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
  rw [hF''] at h
  have hZero : u ∘ R 0 = u := by
    funext y
    simp only [Function.comp_apply, R, orthogonalFlow_zero_apply]
  simpa only [realHessian_secondOrthogonalDifference_flow_eq hu S hS hx, F, hZero,
    R, q, smul_eq_mul] using h

theorem tendsto_realHessian_firstOrthogonalDifference_flow_entry {n : ℕ}
    {u : E n → ℝ} (hu : ContDiffOn ℝ ∞ u (unitBall n))
    (S : E n →L[ℝ] E n) (hS : star S = -S)
    {x : E n} (hx : x ∈ unitBall n) (a b : E n) :
    Tendsto (fun t : ℝ => realHessian
      (dirichletOrthogonalDifference (orthogonalFlow S hS t) t u) x a b)
      (𝓝[≠] 0) (𝓝 (realHessian (fun y => fderiv ℝ u y (S y)) x a b)) := by
  have h := (hasDerivAt_dirichlet_rotated_realHessian hu S hS hx a b 0).tendsto_slope_zero
  have hZero (v : E n → ℝ) : v ∘ orthogonalFlow S hS 0 = v := by
    funext y
    simp only [Function.comp_apply, orthogonalFlow_zero_apply]
  simp only [hZero, zero_add, smul_eq_mul] at h
  apply h.congr'
  filter_upwards [] with t
  have hMaps : orthogonalFlow S hS t x ∈ unitBall n := by
    simpa only [unitBall, mem_ball_zero_iff, LinearIsometryEquiv.norm_map] using hx
  have hu2 : ContDiffOn ℝ 2 u (unitBall n) :=
    hu.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  rw [realHessian_dirichletOrthogonalDifference _ _
    (hu2.contDiffAt (isOpen_ball.mem_nhds hx))
    (hu2.contDiffAt (isOpen_ball.mem_nhds hMaps))]
  simp only [_root_.smul_apply, _root_.sub_apply, smul_eq_mul]

end KEBall
