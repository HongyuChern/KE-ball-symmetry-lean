import KEBall.DirichletCenterTranslation
import KEBall.DirichletRealHessianStability

/-! Full real Hessian difference-quotient estimates for interior translations. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter InnerProductSpace MeasureTheory Metric Set
open scoped ComplexOrder ContDiff Topology

namespace KEBall

local notation "e[" n "]" => EuclideanSpace.basisFun (Fin (2 * n)) ℝ

private theorem realHessian_eventuallyEq {n : ℕ} {u v : E n → ℝ} {x : E n}
    (h : u =ᶠ[𝓝 x] v) : realHessian u x = realHessian v x :=
  h.fderiv.fderiv_eq

private theorem realHessian_add_right {n : ℕ} (u : E n → ℝ) (p x : E n) (a b : E n) :
    realHessian (fun y => u (y + p)) x a b = realHessian u (x + p) a b := by
  simpa only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one, realHessian] using
    congrFun (congrArg DFunLike.coe (iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := u) 2 p x)) ![a, b]

/-- Near the center, the real Hessian of the cutoff pullback equals the
translated Hessian, including both real coordinate slots. -/
theorem realHessian_comp_centerTranslation_of_mem_ball {n : ℕ}
    (u : E n → ℝ) {p x : E n} (hx : x ∈ ball 0 (1 / 4)) (a b : E n) :
    realHessian (u ∘ dirichletCenterTranslation p) x a b = realHessian u (x + p) a b := by
  have h : (u ∘ dirichletCenterTranslation p) =ᶠ[𝓝 x] fun y => u (y + p) := by
    filter_upwards [isOpen_ball.mem_nhds hx] with y hy
    exact congrArg u (dirichletCenterTranslation_eq_add_of_mem_ball hy)
  rw [realHessian_eventuallyEq h, realHessian_add_right]

/-- Differences of real Hessians at nearby points near the center are
controlled in (L²) uniformly by the size of the translation. -/
theorem exists_integral_sq_realHessian_centerTranslation_le {n : ℕ} (hn : 0 < n)
    {d b D B L : ℝ} (hd : 0 < d) (hD : 0 < D) (hB : 0 ≤ B) (hL : 0 ≤ L) :
    ∃ ε > (0 : ℝ), ∃ C ≥ (0 : ℝ), ∀ {u f : E n → ℝ},
      SmoothNear (closedUnitBall n) u → SmoothNear (closedUnitBall n) f →
      (∀ x ∈ unitSphere n, u x = 0) →
      (∀ x ∈ unitBall n, (complexHessian u x).PosDef) →
      (∀ x ∈ unitBall n, (complexHessian u x).det.re = f x) →
      (∀ x ∈ unitBall n, d ≤ f x ∧ f x ≤ b) →
      (∀ x ∈ closedUnitBall n, ‖fderiv ℝ u x‖ ≤ B) →
      (∀ x ∈ closedUnitBall n, ‖fderiv ℝ f x‖ ≤ L) →
      (∀ x ∈ closedUnitBall n, ‖realHessian u x‖ ≤ D) →
      ∀ p : E n, ‖p‖ < ε →
      (∫ x in ball 0 (1 / 4), ∑ i, ∑ j,
        ((realHessian u (x + p) - realHessian u x) (e[n] i) (e[n] j)) ^ 2 ∂volume0 n) ≤ C * ‖p‖ ^ 2 := by
  have : NeZero n := ⟨hn.ne'⟩
  obtain ⟨ε, hε, K, hK, M, hM, hTrans⟩ :=
    exists_centerTranslation_density_stability (n := n) (b := b) hd hD hB hL
  let a := (d / 2) ^ (n : ℝ)⁻¹
  let c := max (b + K) 1 ^ (n : ℝ)⁻¹
  let N := max D M
  have ha : 0 < a := Real.rpow_pos_of_pos (half_pos hd) _
  have hc₀ : 0 < max (b + K) 1 := zero_lt_one.trans_le (le_max_right _ _)
  have hc : 0 < c := Real.rpow_pos_of_pos hc₀ _
  have hN : 0 < N := hD.trans_le (le_max_left _ _)
  have ha' : a ^ n = d / 2 := Real.rpow_inv_natCast_pow (half_pos hd).le hn.ne'
  have hc' : c ^ n = max (b + K) 1 := Real.rpow_inv_natCast_pow hc₀.le hn.ne'
  obtain ⟨C, hC, hStab⟩ := exists_integral_sq_complexHessian_sub_le_of_dirichlet_data hn ha hc hN
  refine ⟨ε, hε, (16 * n : ℝ) * C * K ^ 2, by positivity, ?_⟩
  intro u f hu hf hu0 huP huEq hDen hGrad hGradF hHess p hp
  let v := u ∘ dirichletCenterTranslation p
  let g (x : E n) := (complexHessian v x).det.re
  obtain ⟨hv, hg, hv0, hvP, hgDen, hDiff, hHv⟩ := hTrans hu hf hu0 huP huEq hDen hGrad hGradF hHess p hp
  have hfDen (x : E n) (hx : x ∈ unitBall n) : a ^ n ≤ f x ∧ f x ≤ c ^ n := by
    rw [ha', hc']
    exact ⟨(half_le_self hd.le).trans (hDen x hx).1,
      ((hDen x hx).2.trans (le_add_of_nonneg_right hK)).trans (le_max_left _ _)⟩
  have hgDen' (x : E n) (hx : x ∈ unitBall n) : a ^ n ≤ g x ∧ g x ≤ c ^ n := by
    rw [ha', hc']
    exact ⟨(hgDen x hx).1, (hgDen x hx).2.trans (le_max_left _ _)⟩
  have huH (x : E n) (hx : x ∈ closedUnitBall n) (w : E n) (hw : ‖w‖ = 1) :
      |realHessian u x w w| ≤ N := by
    rw [← Real.norm_eq_abs]
    exact ((realHessian u x w).le_opNorm w).trans (by
      rw [hw, mul_one]
      exact ((realHessian u x).le_opNorm w).trans (by
        rw [hw, mul_one]
        exact (hHess x hx).trans (le_max_left _ _)))
  have hCx := hStab hu hv hf hg hu0 hv0 huP hvP huEq (fun _ _ => rfl) hfDen hgDen' huH
    (fun x hx w hw => (hHv x hx w hw).trans (le_max_right _ _))
  let μ := (volume0 n).restrict (unitBall n)
  have hI {F : E n → ℝ} (hF : ContinuousOn F (closedUnitBall n)) : Integrable F μ :=
    hF.integrableOn_of_subset_isCompact (isCompact_closedBall _ _) measurableSet_ball
      ball_subset_closedBall (by rw [volume0_unitBall n hn]; exact ENNReal.one_ne_top)
  have hCont {F : E n → ℝ} (hF : SmoothNear (closedUnitBall n) F) :
      ContinuousOn F (closedUnitBall n) := fun x hx => (hF.contDiffAt hx).continuousAt.continuousWithinAt
  have hDInt : (∫ x, (g x - f x) ^ 2 ∂μ) ≤ K ^ 2 * ‖p‖ ^ 2 := by
    have hPt : (fun x => (g x - f x) ^ 2) ≤ᵐ[μ] fun _ => K ^ 2 * ‖p‖ ^ 2 := by
      filter_upwards [ae_restrict_mem (μ := volume0 n) (show MeasurableSet (unitBall n) from measurableSet_ball)]
        with x hx
      simpa only [sq_abs, mul_pow] using pow_le_pow_left₀ (abs_nonneg _) (hDiff x hx) 2
    have h := integral_mono_ae (hI (((hCont hg).sub (hCont hf)).pow 2)) (integrable_const _) hPt
    rwa [integral_const, probReal_univ, one_smul] at h
  have hReal := (integral_sq_realHessian_sub_le_complex hn hu hv hu0 hv0).trans
    (mul_le_mul_of_nonneg_left (hCx.trans (mul_le_mul_of_nonneg_left hDInt hC)) (by positivity))
  let H (x : E n) := ∑ i, ∑ j, ((realHessian v x - realHessian u x) (e[n] i) (e[n] j)) ^ 2
  have hHC : ContinuousOn H (closedUnitBall n) := by
    apply continuousOn_finsetSum
    intro i _
    apply continuousOn_finsetSum
    intro j _
    have h (w : E n → ℝ) (hw : SmoothNear (closedUnitBall n) w) :
        ContinuousOn (fun x => realHessian w x (e[n] i) (e[n] j)) (closedUnitBall n) := fun x hx =>
      (((realHessian_contDiffAt (hw.contDiffAt hx)).clm_apply contDiffAt_const).clm_apply
        contDiffAt_const).continuousAt.continuousWithinAt
    exact (((h v hv).sub (h u hu)).pow 2).congr fun x _ => by
      rfl
  have hSub : ball (0 : E n) (1 / 4) ⊆ unitBall n := ball_subset_ball (by norm_num)
  have hRestr := setIntegral_mono_set (hI hHC) (Eventually.of_forall fun x => by dsimp [H]; positivity)
    (Eventually.of_forall hSub)
  have he : (∫ x in ball 0 (1 / 4), H x ∂volume0 n) =
      ∫ x in ball 0 (1 / 4), ∑ i, ∑ j,
        ((realHessian u (x + p) - realHessian u x) (e[n] i) (e[n] j)) ^ 2 ∂volume0 n := by
    apply setIntegral_congr_fun measurableSet_ball
    intro x hx
    simp only [H, v, _root_.sub_apply, realHessian_comp_centerTranslation_of_mem_ball u hx]
  rw [← he]
  exact hRestr.trans (hReal.trans_eq (by ring))

end KEBall
