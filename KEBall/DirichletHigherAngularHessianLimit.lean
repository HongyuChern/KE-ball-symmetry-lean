import KEBall.DirichletHigherForwardLimit
import KEBall.DirichletAngularPotentialHessian
import KEBall.DirichletIteratedPotentialEnergy

/-! Identification of every actual potential-difference Hessian with the corresponding angular Hessian. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 500000

open Filter Metric Set
open scoped BigOperators ContDiff Topology

namespace KEBall

noncomputable def dirichletInteriorAngularIterate {n : ℕ}
    (S : E n →L[ℝ] E n) (u : E n → ℝ) : ℕ → E n → ℝ
  | 0 => u
  | k + 1 => fun x => fderiv ℝ (dirichletInteriorAngularIterate S u k) x (S x)

theorem contDiffOn_dirichletInteriorAngularIterate {n : ℕ} {u : E n → ℝ}
    (hu : ContDiffOn ℝ ∞ u (unitBall n)) (S : E n →L[ℝ] E n) (k : ℕ) :
    ContDiffOn ℝ ∞ (dirichletInteriorAngularIterate S u k) (unitBall n) := by
  induction k with
  | zero => exact hu
  | succ k ih =>
    exact (ih.fderiv_of_isOpen isOpen_ball (m := ∞) (by simp)).clm_apply S.contDiff.contDiffOn

theorem dirichletOrthogonalDifference_comp_flow {n : ℕ}
    (S : E n →L[ℝ] E n) (hS : star S = -S) (t s : ℝ) (u : E n → ℝ) :
    (dirichletOrthogonalDifference (orthogonalFlow S hS t) t u) ∘ orthogonalFlow S hS s =
      dirichletOrthogonalDifference (orthogonalFlow S hS t) t (u ∘ orthogonalFlow S hS s) := by
  funext x
  simp only [dirichletOrthogonalDifference, Function.comp_apply, ← orthogonalFlow_add_apply, add_comm t s]

theorem realHessian_iteratedDifference_comp_flow_eq {n : ℕ} {u : E n → ℝ}
    (hu : ContDiffOn ℝ ∞ u (unitBall n))
    (S : E n →L[ℝ] E n) (hS : star S = -S)
    {x : E n} (hx : x ∈ unitBall n) (a b : E n) (t : ℝ) (k : ℕ) (s : ℝ) :
    realHessian
      ((dirichletIteratedOrthogonalDifference (orthogonalFlow S hS t) t u k) ∘ orthogonalFlow S hS s) x a b =
      (t ^ k)⁻¹ * ((fwdDiff t)^[k] (fun r => realHessian (u ∘ orthogonalFlow S hS r) x a b)) s := by
  let R := orthogonalFlow S hS
  have hMaps (r : ℝ) : MapsTo (R r) (unitBall n) (unitBall n) := by
    intro y hy
    simpa only [unitBall, mem_ball_zero_iff, LinearIsometryEquiv.norm_map] using hy
  induction k generalizing s with
  | zero => simp only [dirichletIteratedOrthogonalDifference, pow_zero, inv_one, one_mul, Function.iterate_zero, id_eq]
  | succ k ih =>
    let q := dirichletIteratedOrthogonalDifference (R t) t u k
    have hq : ContDiffOn ℝ ∞ q (unitBall n) := contDiffOn_dirichletIteratedOrthogonalDifference_ball (R t) t hu k
    have hV : ContDiffOn ℝ 2 (q ∘ R s) (unitBall n) :=
      (hq.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).comp
        (R s).toContinuousLinearEquiv.contDiff.contDiffOn (hMaps s)
    change realHessian ((dirichletOrthogonalDifference (R t) t q) ∘ R s) x a b = _
    rw [dirichletOrthogonalDifference_comp_flow S hS t s q]
    rw [realHessian_dirichletOrthogonalDifference (R t) t
      (hV.contDiffAt (isOpen_ball.mem_nhds hx)) (hV.contDiffAt (isOpen_ball.mem_nhds (hMaps t hx)))]
    have hComp : (q ∘ R s) ∘ R t = q ∘ R (s + t) := by
      funext y
      simp only [Function.comp_apply, R, orthogonalFlow_add_apply]
    rw [hComp]
    simp only [_root_.smul_apply, _root_.sub_apply, smul_eq_mul]
    rw [ih (s + t), ih s, Function.iterate_succ_apply']
    simp only [fwdDiff, pow_succ, mul_inv_rev]
    ring

theorem realHessian_iteratedDifference_flow_eq_sum {n : ℕ} {u : E n → ℝ}
    (hu : ContDiffOn ℝ ∞ u (unitBall n))
    (S : E n →L[ℝ] E n) (hS : star S = -S)
    {x : E n} (hx : x ∈ unitBall n) (a b : E n) (t : ℝ) (k : ℕ) :
    realHessian (dirichletIteratedOrthogonalDifference (orthogonalFlow S hS t) t u k) x a b =
      (t ^ k)⁻¹ * ∑ i ∈ Finset.range (k + 1), dirichletForwardWeight k i *
        realHessian (u ∘ orthogonalFlow S hS (i * t)) x a b := by
  have h := realHessian_iteratedDifference_comp_flow_eq hu S hS hx a b t k 0
  have hZero (v : E n → ℝ) : v ∘ orthogonalFlow S hS 0 = v := by
    funext y
    simp only [Function.comp_apply, orthogonalFlow_zero_apply]
  rw [hZero, fwdDiff_iter_eq_sum_shift] at h
  simpa only [zero_add, nsmul_eq_mul, zsmul_eq_mul, Int.cast_mul, Int.cast_pow,
    Int.cast_neg, Int.cast_one, Int.cast_natCast, dirichletForwardWeight] using h

theorem iteratedDeriv_rotated_realHessian {n : ℕ} {u : E n → ℝ}
    (hu : ContDiffOn ℝ ∞ u (unitBall n))
    (S : E n →L[ℝ] E n) (hS : star S = -S)
    {x : E n} (hx : x ∈ unitBall n) (a b : E n) (k : ℕ) :
    iteratedDeriv k (fun t => realHessian (u ∘ orthogonalFlow S hS t) x a b) =
      fun t => realHessian ((dirichletInteriorAngularIterate S u k) ∘ orthogonalFlow S hS t) x a b := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    exact (hasDerivAt_dirichlet_rotated_realHessian
      (contDiffOn_dirichletInteriorAngularIterate hu S k) S hS hx a b t).deriv

theorem tendsto_realHessian_iteratedOrthogonalDifference_flow_entry {n : ℕ}
    {u : E n → ℝ} (hu : ContDiffOn ℝ ∞ u (unitBall n))
    (S : E n →L[ℝ] E n) (hS : star S = -S)
    {x : E n} (hx : x ∈ unitBall n) (a b : E n) (k : ℕ) :
    Tendsto (fun t : ℝ => realHessian
      (dirichletIteratedOrthogonalDifference (orthogonalFlow S hS t) t u k) x a b)
      (𝓝[≠] 0) (𝓝 (realHessian (dirichletInteriorAngularIterate S u k) x a b)) := by
  let R := orthogonalFlow S hS
  let F (t : ℝ) := realHessian (u ∘ R t) x a b
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
  have h := tendsto_dirichlet_higher_forward_quotient k
    (hF.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl k))
  have hD : iteratedDeriv k F 0 = realHessian (dirichletInteriorAngularIterate S u k) x a b := by
    have he : dirichletInteriorAngularIterate S u k ∘ R 0 = dirichletInteriorAngularIterate S u k := by
      funext y
      simp only [Function.comp_apply, R, orthogonalFlow_zero_apply]
    rw [iteratedDeriv_rotated_realHessian hu S hS hx a b k]
    change realHessian (dirichletInteriorAngularIterate S u k ∘ R 0) x a b = _
    rw [he]
  rw [hD] at h
  simpa only [realHessian_iteratedDifference_flow_eq_sum hu S hS hx, F, R, smul_eq_mul] using h

end KEBall
