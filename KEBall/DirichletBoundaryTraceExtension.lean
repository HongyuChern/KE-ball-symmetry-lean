import KEBall.DirichletBoundaryOscillation
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.MetricSpace.Cauchy

/-!
# Boundary traces from pointwise cap oscillation decay

The trace is constructed by completeness of the real numbers.  No boundary
differentiability or previously chosen boundary representative is assumed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Filter Metric Set
open scoped Topology

namespace KEBall

theorem dirichletBoundaryCap_mem_nhdsWithin {n : ℕ} {p : E n}
    {r : ℝ} (hr : 0 < r) : dirichletBoundaryCap p r ∈ 𝓝[unitBall n] p :=
  inter_mem self_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds (ball_mem_nhds p hr))

theorem exists_dirichlet_boundary_trace_of_oscillation {n : ℕ}
    {f : E n → ℝ} {B C α : ℝ} (hα : 0 < α)
    (hB : ∀ x ∈ unitBall n, |f x| ≤ B)
    {p : E n} (hp : p ∈ unitSphere n)
    (hPower : ∀ r : ℝ, 0 < r → r ≤ 1 →
      dirichletBoundaryOscillation f p r ≤ C * r ^ α) :
    ∃ a : ℝ, Tendsto f (𝓝[unitBall n] p) (𝓝 a) := by
  have hpCl : p ∈ closure (unitBall n) := by
    rw [unitBall, closure_ball (0 : E n) (by norm_num : (1 : ℝ) ≠ 0)]
    exact sphere_subset_closedBall hp
  letI : NeBot (𝓝[unitBall n] p) := mem_closure_iff_nhdsWithin_neBot.mp hpCl
  apply cauchy_map_iff_exists_tendsto.mp
  apply Metric.cauchy_iff.mpr
  refine ⟨inferInstance, ?_⟩
  intro ε hε
  have hId : Tendsto (fun r : ℝ => r) (𝓝[>] (0 : ℝ)) (𝓝 0) := nhdsWithin_le_nhds
  have hSmall : Tendsto (fun r : ℝ => C * r ^ α) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [mul_zero] using (hId.rpow_const_nhds_zero hα).const_mul C
  have hInterval : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ), r ∈ Ioo (0 : ℝ) 1 :=
    Ioo_mem_nhdsGT zero_lt_one
  obtain ⟨r, hr, hCr⟩ := (hInterval.and
    (hSmall.eventually (gt_mem_nhds hε))).exists
  refine ⟨f '' dirichletBoundaryCap p r, ?_, ?_⟩
  · change f ⁻¹' (f '' dirichletBoundaryCap p r) ∈ 𝓝[unitBall n] p
    filter_upwards [dirichletBoundaryCap_mem_nhdsWithin hr.1] with x hx
    exact mem_image_of_mem f hx
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [Real.dist_eq]
    exact ((abs_sub_le_dirichletBoundaryOscillation f hp hr.1
      (fun z hz => abs_le.mp (hB z hz.1)) hx hy).trans (hPower r hr.1 hr.2.le)).trans_lt hCr

theorem abs_sub_dirichlet_boundary_trace_le_oscillation {n : ℕ}
    {f : E n → ℝ} {B : ℝ} (hB : ∀ x ∈ unitBall n, |f x| ≤ B)
    {p : E n} (hp : p ∈ unitSphere n) {a : ℝ}
    (hTrace : Tendsto f (𝓝[unitBall n] p) (𝓝 a))
    {r : ℝ} (hr : 0 < r) {x : E n} (hx : x ∈ dirichletBoundaryCap p r) :
    |f x - a| ≤ dirichletBoundaryOscillation f p r := by
  have hpCl : p ∈ closure (unitBall n) := by
    rw [unitBall, closure_ball (0 : E n) (by norm_num : (1 : ℝ) ≠ 0)]
    exact sphere_subset_closedBall hp
  letI : NeBot (𝓝[unitBall n] p) := mem_closure_iff_nhdsWithin_neBot.mp hpCl
  apply le_of_tendsto ((tendsto_const_nhds (x := f x)).sub hTrace).abs
  filter_upwards [dirichletBoundaryCap_mem_nhdsWithin hr] with y hy
  exact abs_sub_le_dirichletBoundaryOscillation f hp hr
    (fun z hz => abs_le.mp (hB z hz.1)) hx hy

theorem abs_sub_dirichlet_boundary_traces_le_of_power {n : ℕ}
    {f a : E n → ℝ} {B C α : ℝ} (hC : 0 ≤ C)
    (hB : ∀ x ∈ unitBall n, |f x| ≤ B)
    (hTrace : ∀ p ∈ unitSphere n, Tendsto f (𝓝[unitBall n] p) (𝓝 (a p)))
    (hPower : ∀ p ∈ unitSphere n, ∀ r : ℝ, 0 < r → r ≤ 1 →
      dirichletBoundaryOscillation f p r ≤ C * r ^ α)
    {p p' : E n} (hp : p ∈ unitSphere n) (hp' : p' ∈ unitSphere n)
    (hDist : dist p p' ≤ 1 / 2) :
    |a p - a p'| ≤ C * (2 * dist p p') ^ α := by
  by_cases he : p = p'
  · subst p'
    simp only [sub_self, abs_zero, dist_self, mul_zero]
    exact mul_nonneg hC (Real.rpow_nonneg (by norm_num) _)
  have hd : 0 < dist p p' := dist_pos.mpr he
  have hpCl : p' ∈ closure (unitBall n) := by
    rw [unitBall, closure_ball (0 : E n) (by norm_num : (1 : ℝ) ≠ 0)]
    exact sphere_subset_closedBall hp'
  letI : NeBot (𝓝[unitBall n] p') := mem_closure_iff_nhdsWithin_neBot.mp hpCl
  apply le_of_tendsto ((tendsto_const_nhds (x := a p)).sub (hTrace p' hp')).abs
  have hBall : ball p (2 * dist p p') ∈ 𝓝[unitBall n] p' := by
    apply mem_nhdsWithin_of_mem_nhds
    apply isOpen_ball.mem_nhds
    rw [mem_ball, dist_comm p' p]
    linarith
  filter_upwards [self_mem_nhdsWithin, hBall] with x hx hxBall
  rw [abs_sub_comm]
  exact (abs_sub_dirichlet_boundary_trace_le_oscillation hB hp (hTrace p hp)
    (by positivity) ⟨hx, hxBall⟩).trans
    (hPower p hp _ (by positivity) (by linarith))

theorem exists_dirichlet_boundary_trace_with_power_control {n : ℕ}
    {f : E n → ℝ} {B C α : ℝ} (hα : 0 < α) (hC : 0 ≤ C)
    (hB : ∀ x ∈ unitBall n, |f x| ≤ B)
    (hPower : ∀ p ∈ unitSphere n, ∀ r : ℝ, 0 < r → r ≤ 1 →
      dirichletBoundaryOscillation f p r ≤ C * r ^ α) :
    ∃ a : E n → ℝ,
      (∀ p ∈ unitSphere n, Tendsto f (𝓝[unitBall n] p) (𝓝 (a p))) ∧
      (∀ p ∈ unitSphere n, ∀ r : ℝ, 0 < r → r ≤ 1 →
        ∀ x ∈ dirichletBoundaryCap p r, |f x - a p| ≤ C * r ^ α) ∧
      ∀ p ∈ unitSphere n, ∀ p' ∈ unitSphere n, dist p p' ≤ 1 / 2 →
        |a p - a p'| ≤ C * (2 * dist p p') ^ α := by
  classical
  have hExists (p : E n) (hp : p ∈ unitSphere n) :=
    exists_dirichlet_boundary_trace_of_oscillation hα hB hp (hPower p hp)
  let a (p : E n) : ℝ := if hp : p ∈ unitSphere n then (hExists p hp).choose else 0
  have hTrace (p : E n) (hp : p ∈ unitSphere n) :
      Tendsto f (𝓝[unitBall n] p) (𝓝 (a p)) := by
    simpa only [a, dif_pos hp] using (hExists p hp).choose_spec
  refine ⟨a, hTrace, ?_, ?_⟩
  · intro p hp r hr hr1 x hx
    exact (abs_sub_dirichlet_boundary_trace_le_oscillation hB hp (hTrace p hp) hr hx).trans
      (hPower p hp r hr hr1)
  · intro p hp p' hp' hDist
    exact abs_sub_dirichlet_boundary_traces_le_of_power hC hB hTrace hPower hp hp' hDist

end KEBall
