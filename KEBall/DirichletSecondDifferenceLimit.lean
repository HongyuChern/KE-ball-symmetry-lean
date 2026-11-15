import KEBall.DirichletSmoothFieldDifferences
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Tactic.Module

/-! Second forward differences and their genuine interior derivative limit. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Filter Metric Set
open scoped ContDiff Topology

namespace KEBall

theorem tendsto_dirichlet_second_forward_quotient {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {F : ℝ → V} (hF : ContDiff ℝ 2 F) :
    Tendsto (fun t : ℝ => (t ^ 2)⁻¹ • (F (2 * t) - (2 : ℝ) • F t + F 0))
      (𝓝[≠] 0) (𝓝 (iteratedDeriv 2 F 0)) := by
  let P (t : ℝ) := F 0 + t • deriv F 0 + ((1 / 2 : ℝ) * t ^ 2) • iteratedDeriv 2 F 0
  let r (t : ℝ) := (t ^ 2)⁻¹ • (F t - P t)
  have hP (t : ℝ) : taylorWithinEval F 2 univ 0 t = P t := by
    simp [taylorWithinEval_succ, taylor_within_zero_eval, iteratedDerivWithin_univ, P]
    norm_num
  have hr : Tendsto r (𝓝 (0 : ℝ)) (𝓝 0) := by
    have h := taylor_tendsto (f := F) (n := 2) convex_univ (mem_univ (0 : ℝ)) hF.contDiffOn
    simpa only [nhdsWithin_univ, sub_zero, hP, r] using h
  have hDouble : Tendsto (fun t : ℝ => 2 * t) (𝓝 (0 : ℝ)) (𝓝 0) := by
    simpa only [mul_zero, id_eq] using (tendsto_const_nhds.mul (tendsto_id : Tendsto (fun t : ℝ => t) (𝓝 0) (𝓝 0)))
  have hLimit : Tendsto (fun t : ℝ => (4 : ℝ) • r (2 * t) - (2 : ℝ) • r t + iteratedDeriv 2 F 0)
      (𝓝[≠] 0) (𝓝 (iteratedDeriv 2 F 0)) := by
    have h := (((hr.comp hDouble).const_smul (4 : ℝ)).sub
      (hr.const_smul (2 : ℝ))).add_const (iteratedDeriv 2 F 0)
    simpa only [Function.comp_def, smul_zero, sub_zero, zero_add] using h.mono_left nhdsWithin_le_nhds
  apply hLimit.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : t ≠ 0 := ht
  dsimp only [r, P]
  match_scalars <;> field_simp [ht0] <;> ring

theorem orthogonalFlow_add_apply {n : ℕ}
    (S : E n →L[ℝ] E n) (hS : star S = -S) (t s : ℝ) (x : E n) :
    orthogonalFlow S hS (t + s) x = orthogonalFlow S hS t (orthogonalFlow S hS s x) := by
  change NormedSpace.exp ((t + s) • S) x =
    NormedSpace.exp (t • S) (NormedSpace.exp (s • S) x)
  letI : NormedAlgebra ℚ (E n →L[ℝ] E n) :=
    NormedAlgebra.restrictScalars ℚ ℝ (E n →L[ℝ] E n)
  have hComm : Commute (t • S) (s • S) := ((Commute.refl S).smul_left t).smul_right s
  have hExp : NormedSpace.exp (t • S + s • S) =
      NormedSpace.exp (t • S) * NormedSpace.exp (s • S) :=
    NormedSpace.exp_add_of_commute hComm
  simpa only [add_smul, ContinuousLinearMap.mul_apply] using congrArg (fun L : E n →L[ℝ] E n => L x) hExp

theorem dirichletFieldSecondDifference_flow_eq {n : ℕ} {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (S : E n →L[ℝ] E n) (hS : star S = -S) (t : ℝ) (F : E n → V) (x : E n) :
    dirichletFieldDifference (orthogonalFlow S hS t) t
      (dirichletFieldDifference (orthogonalFlow S hS t) t F) x =
      (t ^ 2)⁻¹ • (F (orthogonalFlow S hS (2 * t) x) -
        (2 : ℝ) • F (orthogonalFlow S hS t x) + F x) := by
  simp only [dirichletFieldDifference, ← orthogonalFlow_add_apply, ← two_mul, inv_pow]
  module

theorem tendsto_dirichletFieldSecondDifference_flow {n : ℕ} {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {F : E n → V} (hF : ContDiffOn ℝ ∞ F (unitBall n))
    (S : E n →L[ℝ] E n) (hS : star S = -S)
    {x : E n} (hx : x ∈ unitBall n) :
    Tendsto (fun t : ℝ => dirichletFieldDifference (orthogonalFlow S hS t) t
      (dirichletFieldDifference (orthogonalFlow S hS t) t F) x)
      (𝓝[≠] 0) (𝓝 (fderiv ℝ (fun y => fderiv ℝ F y (S y)) x (S x))) := by
  let R := orthogonalFlow S hS
  let g (t : ℝ) := F (R t x)
  let G (y : E n) := fderiv ℝ F y (S y)
  have hMaps (t : ℝ) : R t x ∈ unitBall n := by
    simpa only [unitBall, mem_ball_zero_iff, LinearIsometryEquiv.norm_map] using hx
  have hFAt (t : ℝ) := hF.contDiffAt (isOpen_ball.mem_nhds (hMaps t))
  have hFlow : ContDiff ℝ ∞ (fun t : ℝ => R t x) :=
    (contDiff_orthogonalFlow_apply S hS).comp (contDiff_id.prodMk contDiff_const)
  have hg : ContDiff ℝ ∞ g := contDiff_iff_contDiffAt.mpr
    (fun t => (hFAt t).comp t hFlow.contDiffAt)
  have hDeriv (t : ℝ) : HasDerivAt g (G (R t x)) t := by
    have h := ((hFAt t).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t
      (hasDerivAt_orthogonalFlow_apply S hS x t)
    simpa only [g, G, R, Function.comp_def, orthogonalFlow_apply_generator] using h
  have hg' : deriv g = fun t => G (R t x) := funext (fun t => (hDeriv t).deriv)
  have hGAt : ContDiffAt ℝ ∞ G x :=
    ((hF.contDiffAt (isOpen_ball.mem_nhds hx)).fderiv_right (m := ∞) (by simp)).clm_apply
      S.contDiff.contDiffAt
  have hGAt0 : HasFDerivAt G (fderiv ℝ G x) (R 0 x) := by
    rw [orthogonalFlow_zero_apply]
    exact (hGAt.differentiableAt (by simp)).hasFDerivAt
  have hg'' : iteratedDeriv 2 g 0 = fderiv ℝ G x (S x) := by
    rw [iteratedDeriv_succ (n := 1), iteratedDeriv_one, hg']
    exact (hGAt0.comp_hasDerivAt 0 (hasDerivAt_orthogonalFlow_apply_zero S hS x)).deriv
  have hLim := tendsto_dirichlet_second_forward_quotient
    (hg.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
  rw [hg''] at hLim
  simpa only [dirichletFieldSecondDifference_flow_eq, g, R,
    orthogonalFlow_zero_apply, G] using hLim

end KEBall
