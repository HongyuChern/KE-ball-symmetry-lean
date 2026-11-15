import KEBall.DirichletDensityStability
import KEBall.DirichletLogDensityPath

/-! Quantitative stability along the smooth part of the log-density path. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Metric Set
open scoped ComplexOrder ContDiff

namespace KEBall

private theorem exists_logDensityPath_abs_sub_le {n : ℕ}
    {g : E n → ℝ} (hg : SmoothNear (closedUnitBall n) g) :
    ∃ L ≥ (0 : ℝ), ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      ∀ x ∈ closedUnitBall n, |Real.exp (t * g x) - Real.exp (s * g x)| ≤ L * |t - s| := by
  obtain ⟨R₀, hR₀⟩ := (isCompact_closedBall (0 : E n) 1).exists_bound_of_continuousOn
    (show ContinuousOn g (closedUnitBall n) from fun x hx =>
      (hg.contDiffAt hx).continuousAt.continuousWithinAt)
  let R := max R₀ 0
  have hR : 0 ≤ R := le_max_right _ _
  refine ⟨Real.exp R * R, mul_nonneg (Real.exp_pos _).le hR, ?_⟩
  intro s hs t ht x hx
  have hG : |g x| ≤ R := by
    rw [← Real.norm_eq_abs]
    exact (hR₀ x hx).trans (le_max_left _ _)
  have hDer (r : ℝ) : HasDerivAt (fun q => Real.exp (q * g x)) (Real.exp (r * g x) * g x) r := by
    simpa only [id_eq, one_mul] using (((hasDerivAt_id r).mul_const (g x)).exp)
  simp only [← Real.norm_eq_abs]
  refine Convex.norm_image_sub_le_of_norm_deriv_le
    (fun r _ => (hDer r).differentiableAt) (fun r hr => ?_) (convex_Icc 0 1) hs ht
  rw [(hDer r).deriv, norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.norm_eq_abs]
  apply mul_le_mul _ hG (abs_nonneg _) (Real.exp_pos _).le
  apply Real.exp_le_exp.mpr
  exact (le_abs_self _).trans (by
    rw [abs_mul, abs_of_nonneg hr.1]
    exact (mul_le_mul_of_nonneg_right hr.2 (abs_nonneg _)).trans (by rwa [one_mul]))

/-- The squared (L^2) complex Hessian difference of two smooth solutions on the
log-density path is bounded by a constant times the squared parameter difference. -/
theorem exists_integral_sq_complexHessian_sub_le_of_logDensityPath {n : ℕ} (hn : 0 < n)
    {g : E n → ℝ} (hg : SmoothNear (closedUnitBall n) g) :
    ∃ C ≥ (0 : ℝ), ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      ∀ {u v : E n → ℝ},
      SmoothNear (closedUnitBall n) u → SmoothNear (closedUnitBall n) v →
      (∀ x ∈ unitSphere n, u x = 0) → (∀ x ∈ unitSphere n, v x = 0) →
      (∀ x ∈ unitBall n, (complexHessian u x).PosDef) →
      (∀ x ∈ unitBall n, (complexHessian v x).PosDef) →
      (∀ x ∈ unitBall n, (complexHessian u x).det.re = Real.exp (s * g x)) →
      (∀ x ∈ unitBall n, (complexHessian v x).det.re = Real.exp (t * g x)) →
      (∫ x in unitBall n, ∑ i, ∑ j, ‖(complexHessian v x - complexHessian u x) i j‖ ^ 2 ∂volume0 n) ≤
        C * (t - s) ^ 2 := by
  have : NeZero n := ⟨hn.ne'⟩
  let f (t : ℝ) (x : E n) := Real.exp (t * g x)
  have hSmooth (r : ℝ) : SmoothNear (closedUnitBall n) (f r) := by
    obtain ⟨U, hU, hSub, hgU⟩ := hg
    exact ⟨U, hU, hSub, (contDiffOn_const.mul hgU).exp⟩
  obtain ⟨a, b, K, M, ha, hb, hK, hM, hBounds⟩ := exists_logDensityPath_bounds hn hg
  obtain ⟨L, hL, hLip⟩ := exists_logDensityPath_abs_sub_le hg
  let d := (3 * K + 1) / (n : ℝ)
  let B := 2 * b + 4 * b * d +
    (2 * b + 4 * (b ^ n / a ^ (n - 1) + (b * d) ^ 2 / (4 * a)))
  let D := B + ((M + 1) / (n : ℝ)) * b
  have hD : 0 < D := by dsimp [D, B, d]; positivity
  obtain ⟨C, hC, hStability⟩ := exists_integral_sq_complexHessian_sub_le_of_dirichlet_data hn ha hb hD
  refine ⟨C * L ^ 2, by positivity, ?_⟩
  intro s hs t ht u v hu hv hu0 hv0 huP hvP huEq hvEq
  have hDen {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) (x : E n) (hx : x ∈ unitBall n) :
      a ^ n ≤ f r x ∧ f r x ≤ b ^ n := (hBounds r hr).1 x (ball_subset_closedBall hx)
  have hHess {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) {w : E n → ℝ}
      (hw : SmoothNear (closedUnitBall n) w) (hw0 : ∀ x ∈ unitSphere n, w x = 0)
      (hwP : ∀ x ∈ unitBall n, (complexHessian w x).PosDef)
      (hwEq : ∀ x ∈ unitBall n, (complexHessian w x).det.re = f r x) :
      ∀ x ∈ closedUnitBall n, ∀ z : E n, ‖z‖ = 1 → |realHessian w x z z| ≤ D :=
    abs_realHessian_self_le_of_dirichlet_det hn hw (hSmooth r) hw0 hwP hwEq
      ha hb hM (hDen hr)
      (fun y hy z hz => abs_realHessian_self_le_on_sphere_of_dirichlet_det hn hw (hSmooth r)
        hw0 hwP hwEq ha hb hK (hDen hr) (fun x hx => (hBounds r hr).2.1 x (ball_subset_closedBall hx))
        hy hz)
      (fun x hx => (hBounds r hr).2.2 x (ball_subset_closedBall hx))
  have hS := hStability hu hv (hSmooth s) (hSmooth t) hu0 hv0 huP hvP huEq hvEq (hDen hs) (hDen ht)
    (hHess hs hu hu0 huP huEq) (hHess ht hv hv0 hvP hvEq)
  let μ := (volume0 n).restrict (unitBall n)
  have hF (r : ℝ) : ContinuousOn (f r) (closedUnitBall n) :=
    fun x hx => ((hSmooth r).contDiffAt hx).continuousAt.continuousWithinAt
  have hInt : Integrable (fun x => (f t x - f s x) ^ 2) μ := by
    have hCont : ContinuousOn (fun x => (f t x - f s x) ^ 2) (closedUnitBall n) :=
      ((hF t).sub (hF s)).pow 2
    exact hCont.integrableOn_of_subset_isCompact (isCompact_closedBall _ _) measurableSet_ball
      ball_subset_closedBall (by rw [volume0_unitBall n hn]; exact ENNReal.one_ne_top)
  have hPoint : (fun x => (f t x - f s x) ^ 2) ≤ᵐ[μ] fun _ => L ^ 2 * (t - s) ^ 2 := by
    filter_upwards [ae_restrict_mem (μ := volume0 n) (show MeasurableSet (unitBall n) from measurableSet_ball)]
      with x hx
    have h := pow_le_pow_left₀ (abs_nonneg _) (hLip s hs t ht x (ball_subset_closedBall hx)) 2
    simpa only [sq_abs, mul_pow] using h
  have hIntLe := integral_mono_ae hInt (integrable_const (L ^ 2 * (t - s) ^ 2)) hPoint
  rw [integral_const, probReal_univ, one_smul] at hIntLe
  exact hS.trans ((mul_le_mul_of_nonneg_left hIntLe hC).trans_eq (mul_assoc _ _ _).symm)

end KEBall
