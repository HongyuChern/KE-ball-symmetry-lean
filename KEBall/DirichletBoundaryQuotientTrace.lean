import KEBall.DirichletBoundaryOscillation
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Identifying the boundary quotient with the actual normal derivative

The sign is fixed by the inward radius and rho=(1-|x|^2)/2.  The quotient
converges to minus the outward normal derivative.  Oscillation estimates
therefore control that derivative without changing its representative.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Filter Metric Set
open scoped Topology

namespace KEBall

theorem dirichletBoundaryDistanceProxy_radial {n : ℕ} {p : E n}
    (hp : p ∈ unitSphere n) (s : ℝ) :
    dirichletBoundaryDistanceProxy ((1 - s) • p) = s * (1 - s / 2) := by
  unfold dirichletBoundaryDistanceProxy
  rw [norm_smul, Real.norm_eq_abs, mem_sphere_zero_iff_norm.mp hp, mul_one, sq_abs]
  ring

theorem tendsto_dirichlet_boundary_quotient_radial {n : ℕ} {q : E n → ℝ}
    {p : E n} (hp : p ∈ unitSphere n) {Q : E n →L[ℝ] ℝ}
    (hD : HasFDerivAt q Q p) (hq0 : q p = 0) :
    Tendsto (fun s : ℝ => q ((1 - s) • p) /
      dirichletBoundaryDistanceProxy ((1 - s) • p)) (𝓝[>] (0 : ℝ)) (𝓝 (-Q p)) := by
  have hLine : HasDerivAt (fun s : ℝ => (1 - s) • p) (-p) 0 := by
    simpa only [Pi.sub_apply, Function.id_def, sub_self, one_smul, sub_zero, zero_sub,
      neg_one_smul] using!
      (((hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub (hasDerivAt_id (0 : ℝ))).smul_const p)
  have hD' : HasFDerivAt q Q ((1 - (0 : ℝ)) • p) := by simpa using hD
  have hComp : HasDerivAt (fun s : ℝ => q ((1 - s) • p)) (-Q p) 0 := by
    simpa only [Function.comp_def, map_neg] using! hD'.comp_hasDerivAt 0 hLine
  have hSlope : Tendsto (fun s : ℝ => q ((1 - s) • p) / s)
      (𝓝[>] (0 : ℝ)) (𝓝 (-Q p)) := by
    simpa only [zero_add, sub_zero, one_smul, hq0, smul_eq_mul, div_eq_mul_inv, mul_comm]
      using hComp.tendsto_slope_zero_right
  have hId : Tendsto (fun s : ℝ => s) (𝓝[>] (0 : ℝ)) (𝓝 0) := nhdsWithin_le_nhds
  have hDen : Tendsto (fun s : ℝ => 1 - s / 2) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    simpa only [zero_div, sub_zero] using tendsto_const_nhds.sub (hId.div_const 2)
  have h := hSlope.div hDen (by norm_num : (1 : ℝ) ≠ 0)
  change Tendsto (fun s : ℝ => (q ((1 - s) • p) / s) / (1 - s / 2))
    (𝓝[>] (0 : ℝ)) (𝓝 ((-Q p) / 1)) at h
  simpa only [div_one, dirichletBoundaryDistanceProxy_radial hp, div_div] using h

theorem eventually_dirichlet_radial_in_boundary_cap {n : ℕ} {p : E n}
    (hp : p ∈ unitSphere n) {r : ℝ} (hr : 0 < r) :
    ∀ᶠ s : ℝ in 𝓝[>] (0 : ℝ), (1 - s) • p ∈ dirichletBoundaryCap p r := by
  filter_upwards [Ioo_mem_nhdsGT (lt_min zero_lt_one hr)] with s hs
  refine ⟨mem_ball_zero_iff.mpr ?_, mem_ball.mpr ?_⟩
  · rw [norm_dirichlet_radial_point hp (hs.2.trans_le (min_le_left _ _)).le]
    linarith [hs.1]
  · change dist (dirichletTangentBallCenter p s) p < r
    rw [dist_dirichletTangentBallCenter_self hp hs.1.le]
    exact hs.2.trans_le (min_le_right _ _)

theorem abs_dirichlet_quotient_add_normal_le_oscillation {n : ℕ} {q : E n → ℝ}
    {p : E n} (hp : p ∈ unitSphere n) {Q : E n →L[ℝ] ℝ}
    (hD : HasFDerivAt q Q p) (hq0 : q p = 0) {B : ℝ}
    (hB : ∀ x ∈ unitBall n, |q x / dirichletBoundaryDistanceProxy x| ≤ B)
    {r : ℝ} (hr : 0 < r) {x : E n} (hx : x ∈ dirichletBoundaryCap p r) :
    |q x / dirichletBoundaryDistanceProxy x + Q p| ≤
      dirichletBoundaryOscillation (fun y => q y / dirichletBoundaryDistanceProxy y) p r := by
  have hT := ((tendsto_const_nhds (x := q x / dirichletBoundaryDistanceProxy x)).sub
    (tendsto_dirichlet_boundary_quotient_radial hp hD hq0)).abs
  have hEv : ∀ᶠ s : ℝ in 𝓝[>] (0 : ℝ),
      |q x / dirichletBoundaryDistanceProxy x -
        q ((1 - s) • p) / dirichletBoundaryDistanceProxy ((1 - s) • p)| ≤
      dirichletBoundaryOscillation (fun y => q y / dirichletBoundaryDistanceProxy y) p r := by
    filter_upwards [eventually_dirichlet_radial_in_boundary_cap hp hr] with s hs
    exact abs_sub_le_dirichletBoundaryOscillation _ hp hr
      (fun y hy => abs_le.mp (hB y hy.1)) hx hs
  simpa only [sub_neg_eq_add] using le_of_tendsto hT hEv

theorem abs_dirichlet_boundary_normal_sub_le_of_power {n : ℕ} {q : E n → ℝ}
    {Q : E n → E n →L[ℝ] ℝ}
    (hD : ∀ p ∈ unitSphere n, HasFDerivAt q (Q p) p)
    (hq0 : ∀ p ∈ unitSphere n, q p = 0) {B C α : ℝ} (hC : 0 ≤ C)
    (hB : ∀ x ∈ unitBall n, |q x / dirichletBoundaryDistanceProxy x| ≤ B)
    (hPower : ∀ p ∈ unitSphere n, ∀ r : ℝ, 0 < r → r ≤ 1 →
      dirichletBoundaryOscillation (fun x => q x / dirichletBoundaryDistanceProxy x) p r ≤ C * r ^ α)
    {p p' : E n} (hp : p ∈ unitSphere n) (hp' : p' ∈ unitSphere n)
    (hDist : dist p p' ≤ 1 / 2) :
    |Q p p - Q p' p'| ≤ C * (2 * dist p p') ^ α := by
  by_cases he : p = p'
  · subst p'
    simp only [sub_self, abs_zero, dist_self, mul_zero]
    exact mul_nonneg hC (Real.rpow_nonneg (by norm_num) _)
  have hd : 0 < dist p p' := dist_pos.mpr he
  have hT := ((tendsto_dirichlet_boundary_quotient_radial hp' (hD p' hp') (hq0 p' hp')).add_const (Q p p)).abs
  have hEv : ∀ᶠ s : ℝ in 𝓝[>] (0 : ℝ),
      |q ((1 - s) • p') / dirichletBoundaryDistanceProxy ((1 - s) • p') + Q p p| ≤
        C * (2 * dist p p') ^ α := by
    filter_upwards [eventually_dirichlet_radial_in_boundary_cap hp' hd] with s hs
    have hcap : (1 - s) • p' ∈ dirichletBoundaryCap p (2 * dist p p') := by
      refine ⟨hs.1, mem_ball.mpr ?_⟩
      have h := dist_triangle ((1 - s) • p') p' p
      rw [dist_comm p' p] at h
      have hh := mem_ball.mp hs.2
      linarith
    exact (abs_dirichlet_quotient_add_normal_le_oscillation hp (hD p hp) (hq0 p hp) hB
      (by positivity) hcap).trans (hPower p hp _ (by positivity) (by linarith))
  have h := le_of_tendsto hT hEv
  simpa only [neg_add_eq_sub] using h

end KEBall
