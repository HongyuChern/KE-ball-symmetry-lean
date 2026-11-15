import KEBall.DirichletBoundaryTraceExtension
import KEBall.DirichletHolderContinuity

/-! Boundedness and continuity of the boundary trace chosen from cap decay. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Filter Metric Set
open scoped Topology

namespace KEBall

theorem abs_dirichlet_boundary_trace_le {n : ℕ} {f : E n → ℝ} {B a : ℝ}
    (hB : ∀ x ∈ unitBall n, |f x| ≤ B) {p : E n} (hp : p ∈ unitSphere n)
    (hTrace : Tendsto f (𝓝[unitBall n] p) (𝓝 a)) : |a| ≤ B := by
  have hpCl : p ∈ closure (unitBall n) := by
    rw [unitBall, closure_ball (0 : E n) (by norm_num : (1 : ℝ) ≠ 0)]
    exact sphere_subset_closedBall hp
  letI : NeBot (𝓝[unitBall n] p) := mem_closure_iff_nhdsWithin_neBot.mp hpCl
  apply le_of_tendsto hTrace.abs
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact hB x hx

theorem abs_dirichlet_boundary_trace_sub_le_global {n : ℕ} {a : E n → ℝ}
    {B C α : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C) (hα : 0 ≤ α)
    (hBound : ∀ p ∈ unitSphere n, |a p| ≤ B)
    (hLocal : ∀ p ∈ unitSphere n, ∀ p' ∈ unitSphere n, dist p p' ≤ 1 / 2 →
      |a p - a p'| ≤ C * (2 * dist p p') ^ α) :
    ∀ p ∈ unitSphere n, ∀ p' ∈ unitSphere n,
      |a p - a p'| ≤ ((C + 2 * B) * (2 : ℝ) ^ α) * ‖p - p'‖ ^ α := by
  intro p hp p' hp'
  have hMain : |a p - a p'| ≤ (C + 2 * B) * (2 * dist p p') ^ α := by
    by_cases hNear : dist p p' ≤ 1 / 2
    · exact (hLocal p hp p' hp' hNear).trans
        (mul_le_mul_of_nonneg_right (by linarith : C ≤ C + 2 * B)
          (Real.rpow_nonneg (by positivity) _))
    · have hFar : 1 ≤ (2 * dist p p') ^ α := Real.one_le_rpow (by linarith) hα
      calc
        |a p - a p'| ≤ |a p| + |a p'| := abs_sub _ _
        _ ≤ 2 * B := by linarith [hBound p hp, hBound p' hp']
        _ ≤ C + 2 * B := by linarith
        _ ≤ (C + 2 * B) * (2 * dist p p') ^ α :=
          le_mul_of_one_le_right (by positivity) hFar
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (dist_nonneg : 0 ≤ dist p p')] at hMain
  simpa only [dist_eq_norm, mul_assoc] using hMain

theorem continuousOn_dirichlet_boundary_trace {n : ℕ} {f a : E n → ℝ}
    {B C α : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C) (hα : 0 < α)
    (hBound : ∀ x ∈ unitBall n, |f x| ≤ B)
    (hTrace : ∀ p ∈ unitSphere n, Tendsto f (𝓝[unitBall n] p) (𝓝 (a p)))
    (hPower : ∀ p ∈ unitSphere n, ∀ r : ℝ, 0 < r → r ≤ 1 →
      dirichletBoundaryOscillation f p r ≤ C * r ^ α) :
    ContinuousOn a (unitSphere n) := by
  apply continuousOn_of_dirichlet_holder_bound hα
  exact abs_dirichlet_boundary_trace_sub_le_global hB hC hα.le
    (fun p hp => abs_dirichlet_boundary_trace_le hBound hp (hTrace p hp))
    (fun p hp p' hp' hd => abs_sub_dirichlet_boundary_traces_le_of_power
      hC hBound hTrace hPower hp hp' hd)

end KEBall
