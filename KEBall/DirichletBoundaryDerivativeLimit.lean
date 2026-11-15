import KEBall.DirichletBoundaryRemainderDerivative
import KEBall.DirichletBoundaryTraceContinuity
import KEBall.DirichletBoundaryQuotientBound

/-!
# Boundary convergence of the actual derivative from quotient decay

At each interior point a nearest sphere point supplies the trace in the
remainder estimate.  Its distance to a fixed boundary point tends to zero.
The remainder derivative tends to zero at the proved interpolation scale.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Filter InnerProductSpace Metric Set
open scoped ContDiff Topology

namespace KEBall

theorem tendsto_dirichlet_boundary_fderiv_of_quotient_and_scaled_holder {n : ℕ} (hn : 0 < n)
    {q a : E n → ℝ} {B C H α β : ℝ}
    (hB : 0 ≤ B) (hC : 0 ≤ C) (hH : 0 ≤ H)
    (hα : 0 < α) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hq : ∀ x ∈ unitBall n, DifferentiableAt ℝ q x)
    (hBound : ∀ p ∈ unitSphere n, |a p| ≤ B)
    (hCont : ContinuousOn a (unitSphere n))
    (hTrace : ∀ p ∈ unitSphere n, ∀ r : ℝ, 0 < r → r ≤ 1 →
      ∀ x ∈ dirichletBoundaryCap p r,
        |q x / dirichletBoundaryDistanceProxy x - a p| ≤ C * r ^ α)
    (hHolder : ∀ x ∈ unitBall n, ∀ r : ℝ, r = 1 - ‖x‖ → r ≤ 1 / 2 →
      ∀ y ∈ ball x (r / 8), ∀ z ∈ ball x (r / 8),
        ‖fderiv ℝ q y - fderiv ℝ q z‖ ≤ (H / r ^ β) * ‖y - z‖ ^ β)
    {p₀ : E n} (hp₀ : p₀ ∈ unitSphere n) :
    Tendsto (fderiv ℝ q) (𝓝[unitBall n] p₀)
      (𝓝 (a p₀ • fderiv ℝ (@dirichletBoundaryDistanceProxy n) p₀)) := by
  classical
  have hNearest (x : E n) (hx : x ∈ unitBall n) :=
    exists_dirichlet_nearest_sphere_point hn (ball_subset_closedBall hx)
  let p (x : E n) : E n := if hx : x ∈ unitBall n then (hNearest x hx).choose else p₀
  have hP (x : E n) (hx : x ∈ unitBall n) :
      p x ∈ unitSphere n ∧ dist x (p x) = 1 - ‖x‖ := by
    simpa only [p, dif_pos hx] using (hNearest x hx).choose_spec
  have hMarginLe (x : E n) : 1 - ‖x‖ ≤ dist x p₀ := by
    have h := norm_sub_norm_le p₀ x
    rwa [mem_sphere_zero_iff_norm.mp hp₀, ← dist_eq_norm, dist_comm p₀ x] at h
  have hPT : Tendsto p (𝓝[unitBall n] p₀) (𝓝 p₀) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    have hNear : ∀ᶠ x in 𝓝[unitBall n] p₀, dist x p₀ < ε / 2 :=
      mem_nhdsWithin_of_mem_nhds (ball_mem_nhds p₀ (half_pos hε))
    filter_upwards [self_mem_nhdsWithin, hNear] with x hx hxNear
    have h := dist_triangle (p x) x p₀
    rw [dist_comm (p x) x, (hP x hx).2] at h
    linarith [hMarginLe x]
  have hPWithin : Tendsto p (𝓝[unitBall n] p₀) (𝓝[unitSphere n] p₀) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hPT, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (hP x hx).1
  have hAT : Tendsto (fun x => a (p x)) (𝓝[unitBall n] p₀) (𝓝 (a p₀)) :=
    (hCont p₀ hp₀).tendsto.comp hPWithin
  have hρC : Continuous (fun x : E n => fderiv ℝ (@dirichletBoundaryDistanceProxy n) x) := by
    simpa only [fderiv_dirichletBoundaryDistanceProxy] using! (innerSL ℝ (E := E n)).continuous.neg
  have hApprox : Tendsto (fun x => a (p x) • fderiv ℝ (@dirichletBoundaryDistanceProxy n) x)
      (𝓝[unitBall n] p₀) (𝓝 (a p₀ • fderiv ℝ (@dirichletBoundaryDistanceProxy n) p₀)) :=
    hAT.smul ((hρC.tendsto p₀).mono_left nhdsWithin_le_nhds)
  have hId : Tendsto (fun x : E n => x) (𝓝[unitBall n] p₀) (𝓝 p₀) := nhdsWithin_le_nhds
  have hR : Tendsto (fun x : E n => 1 - ‖x‖) (𝓝[unitBall n] p₀) (𝓝 (0 : ℝ)) := by
    simpa only [mem_sphere_zero_iff_norm.mp hp₀, sub_self] using hId.norm.const_sub 1
  have hRpos : ∀ᶠ x in 𝓝[unitBall n] p₀, 0 < 1 - ‖x‖ := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact sub_pos.mpr (mem_ball_zero_iff.mp hx)
  have hRGT : Tendsto (fun x : E n => 1 - ‖x‖) (𝓝[unitBall n] p₀) (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hR, hRpos⟩
  have hSmall : ∀ᶠ x in 𝓝[unitBall n] p₀, 1 - ‖x‖ < 1 / 2 :=
    hR.eventually_lt_const (by norm_num)
  have hError := (tendsto_dirichlet_boundary_interpolation_error
    (A := C * (2 : ℝ) ^ (1 + α)) (H := H + B) hα hβ).comp hRGT
  have hDiff : Tendsto
      (fun x => fderiv ℝ q x - a (p x) • fderiv ℝ (@dirichletBoundaryDistanceProxy n) x)
      (𝓝[unitBall n] p₀) (𝓝 0) := by
    apply squeeze_zero_norm' _ hError
    filter_upwards [self_mem_nhdsWithin, hSmall] with x hx hxSmall
    let r : ℝ := 1 - ‖x‖
    have hr : 0 < r := sub_pos.mpr (mem_ball_zero_iff.mp hx)
    have hInside : closedBall x (r / 2) ⊆ unitBall n :=
      closedBall_subset_dirichlet_unitBall_of_margin (by dsimp [r] at *; linarith)
    have hSub : ball x (r / 8) ⊆ unitBall n :=
      ball_subset_closedBall.trans ((closedBall_subset_closedBall (by linarith)).trans hInside)
    exact norm_dirichlet_boundary_remainder_fderiv_le hC hH hB hα hβ hβ1
      (hBound (p x) (hP x hx).1) (hP x hx).1 hr hxSmall.le hInside (hP x hx).2.le
      (fun y hy => hq y (hSub hy)) (hHolder x hx r rfl hxSmall.le)
      (hTrace (p x) (hP x hx).1 (2 * r) (by positivity) (by dsimp [r]; linarith))
  simpa only [Pi.add_apply, sub_add_cancel, zero_add] using hDiff.add hApprox

end KEBall
