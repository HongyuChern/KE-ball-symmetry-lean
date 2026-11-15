import KEBall.DirichletCenterHessianStability
import KEBall.DirichletNonlinearAnnularEstimate
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! Uniform square integrability of all third derivatives for smooth Dirichlet solutions. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8

open Filter InnerProductSpace MeasureTheory Metric Set
open scoped ComplexOrder ContDiff Topology

namespace KEBall

local notation "e[" n "]" => EuclideanSpace.basisFun (Fin (2 * n)) ℝ

private theorem integral_le_of_ae_tendsto_nonneg {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {F : ℕ → α → ℝ} {G : α → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hF : ∀ k, Integrable (F k) μ) (hG : Integrable G μ)
    (hF₀ : ∀ k, 0 ≤ᵐ[μ] F k) (hG₀ : 0 ≤ᵐ[μ] G)
    (hLim : ∀ᵐ x ∂μ, Tendsto (fun k => F k x) atTop (𝓝 (G x)))
    (hBound : ∀ᶠ k in atTop, (∫ x, F k x ∂μ) ≤ C) :
    (∫ x, G x ∂μ) ≤ C := by
  have h := lintegral_liminf_le' (u := atTop) (fun k => (hF k).aemeasurable.ennreal_ofReal)
  have he : (∫⁻ x, liminf (fun k => ENNReal.ofReal (F k x)) atTop ∂μ) =
      ∫⁻ x, ENNReal.ofReal (G x) ∂μ := by
    apply lintegral_congr_ae
    filter_upwards [hLim] with x hx
    exact ((ENNReal.continuous_ofReal.continuousAt.tendsto.comp hx) :
      Tendsto (fun k => ENNReal.ofReal (F k x)) atTop (𝓝 (ENNReal.ofReal (G x)))).liminf_eq
  have hL : ∀ᶠ k in atTop, (∫⁻ x, ENNReal.ofReal (F k x) ∂μ) ≤ ENNReal.ofReal C := by
    filter_upwards [hBound] with k hk
    rw [← ofReal_integral_eq_lintegral_ofReal (hF k) (hF₀ k)]
    exact ENNReal.ofReal_le_ofReal hk
  have hL' : liminf (fun k => ∫⁻ x, ENNReal.ofReal (F k x) ∂μ) atTop ≤ ENNReal.ofReal C := by
    obtain ⟨N, hN⟩ := eventually_atTop.mp hL
    rw [Filter.liminf_eq_iSup_iInf_of_nat]
    exact iSup_le fun k => iInf_le_of_le (max k N) (iInf_le_of_le (le_max_left _ _) (hN _ (le_max_right _ _)))
  rw [he, ← ofReal_integral_eq_lintegral_ofReal hG hG₀] at h
  exact (ENNReal.ofReal_le_ofReal_iff hC).mp (h.trans hL')

private theorem exists_integral_sq_realThirdDerivative_center_le {n : ℕ} (hn : 0 < n)
    {d b D B L : ℝ} (hd : 0 < d) (hD : 0 < D) (hB : 0 ≤ B) (hL : 0 ≤ L) :
    ∃ C ≥ (0 : ℝ), ∀ {u f : E n → ℝ},
      SmoothNear (closedUnitBall n) u → SmoothNear (closedUnitBall n) f →
      (∀ x ∈ unitSphere n, u x = 0) →
      (∀ x ∈ unitBall n, (complexHessian u x).PosDef) →
      (∀ x ∈ unitBall n, (complexHessian u x).det.re = f x) →
      (∀ x ∈ unitBall n, d ≤ f x ∧ f x ≤ b) →
      (∀ x ∈ closedUnitBall n, ‖fderiv ℝ u x‖ ≤ B) →
      (∀ x ∈ closedUnitBall n, ‖fderiv ℝ f x‖ ≤ L) →
      (∀ x ∈ closedUnitBall n, ‖realHessian u x‖ ≤ D) →
      ∀ i : Fin (2 * n),
      (∫ x in ball 0 (1 / 4), ∑ j, ∑ k,
        (realThirdDerivative u x (e[n] i) (e[n] j) (e[n] k)) ^ 2 ∂volume0 n) ≤ C := by
  obtain ⟨ε, hε, C, hC, hEst⟩ := exists_integral_sq_realHessian_centerTranslation_le hn hd hD hB hL
  refine ⟨C, hC, ?_⟩
  intro u f hu hf hu0 huP huEq hDen hGrad hGradF hHess i
  let Ω := ball (0 : E n) (1 / 4)
  let μ := (volume0 n).restrict Ω
  let t (m : ℕ) : ℝ := min (ε / 2) (1 / 4) / ((m : ℝ) + 1)
  let p (m : ℕ) := t m • e[n] i
  let F (m : ℕ) (x : E n) := ∑ j, ∑ k, ((t m)⁻¹ *
    (realHessian u (x + p m) (e[n] j) (e[n] k) - realHessian u x (e[n] j) (e[n] k))) ^ 2
  let G (x : E n) := ∑ j, ∑ k, (realThirdDerivative u x (e[n] i) (e[n] j) (e[n] k)) ^ 2
  have hCap : 0 < min (ε / 2) (1 / 4 : ℝ) := lt_min (half_pos hε) (by norm_num)
  have ht (m : ℕ) : 0 < t m := by dsimp only [t]; positivity
  have htB (m : ℕ) : t m ≤ min (ε / 2) (1 / 4 : ℝ) := by
    dsimp only [t]
    exact div_le_self hCap.le (by simp)
  have hp (m : ℕ) : ‖p m‖ = t m := by
    rw [show p m = t m • e[n] i from rfl, norm_smul, (e[n]).orthonormal.norm_eq_one i, mul_one,
      Real.norm_of_nonneg (ht m).le]
  have htLim : Tendsto t atTop (𝓝[≠] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, Eventually.of_forall fun m => (ht m).ne'⟩
    simpa only [t, mul_zero, div_eq_mul_inv, one_mul] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (min (ε / 2) (1 / 4))
  have hSub : Ω ⊆ unitBall n := ball_subset_ball (by norm_num)
  let S := closedBall (0 : E n) (1 / 4)
  have hSB : S ⊆ closedUnitBall n := closedBall_subset_closedBall (by norm_num)
  have hShift (m : ℕ) : MapsTo (fun x => x + p m) S (closedUnitBall n) := by
    intro x hx
    apply mem_closedBall_zero_iff.mpr
    exact (norm_add_le _ _).trans ((add_le_add (mem_closedBall_zero_iff.mp hx)
      ((hp m).trans_le ((htB m).trans (min_le_right _ _)))).trans (by norm_num))
  have hI {h : E n → ℝ} (hh : ContinuousOn h S) : Integrable h μ :=
    hh.integrableOn_of_subset_isCompact (isCompact_closedBall _ _) measurableSet_ball ball_subset_closedBall
      ((measure_mono hSub).trans_lt (by rw [volume0_unitBall n hn]; exact ENNReal.one_lt_top)).ne
  have hHC (j k : Fin (2 * n)) :
      ContinuousOn (fun x => realHessian u x (e[n] j) (e[n] k)) (closedUnitBall n) :=
    fun x hx => (((realHessian_contDiffAt (hu.contDiffAt hx)).clm_apply contDiffAt_const).clm_apply
      contDiffAt_const).continuousAt.continuousWithinAt
  have hFC (m : ℕ) : ContinuousOn (F m) S := continuousOn_finsetSum Finset.univ fun j _ =>
    continuousOn_finsetSum Finset.univ fun k _ =>
      (continuousOn_const.mul (((hHC j k).comp
        (continuous_id.add continuous_const).continuousOn (hShift m)).sub ((hHC j k).mono hSB))).pow 2
  have hGC : ContinuousOn G S := by
    obtain ⟨U, hU, hKU, huU⟩ := hu
    have hD₁ := huU.fderiv_of_isOpen hU (m := ∞) (by simp)
    have hD₂ := hD₁.fderiv_of_isOpen hU (m := ∞) (by simp)
    have hT : ContDiffOn ℝ ∞ (realThirdDerivative u) U := hD₂.fderiv_of_isOpen hU (m := ∞) (by simp)
    exact continuousOn_finsetSum Finset.univ fun j _ => continuousOn_finsetSum Finset.univ fun k _ =>
      (((((hT.continuousOn.clm_apply continuousOn_const).clm_apply continuousOn_const).clm_apply
        continuousOn_const).pow 2).mono (hSB.trans hKU))
  have hLim : ∀ᵐ x ∂μ, Tendsto (fun m => F m x) atTop (𝓝 (G x)) := by
    filter_upwards [ae_restrict_mem (μ := volume0 n) (show MeasurableSet Ω from measurableSet_ball)]
      with x hx
    have huAt := hu.contDiffAt (ball_subset_closedBall (hSub hx))
    apply tendsto_finsetSum
    intro j _
    apply tendsto_finsetSum
    intro k _
    let H (x : E n) := realHessian u x (e[n] j) (e[n] k)
    have hLine (s : ℝ) : HasDerivAt (fun r : ℝ => x + r • e[n] i) (e[n] i) s := by
      simpa only [id_eq, one_smul] using ((hasDerivAt_id s).smul_const (e[n] i)).const_add x
    have hD : HasFDerivAt H (fderiv ℝ H x) (x + (0 : ℝ) • e[n] i) := by
      rw [zero_smul, add_zero]
      exact (((realHessian_contDiffAt huAt).clm_apply contDiffAt_const).clm_apply
        contDiffAt_const).differentiableAt (by simp) |>.hasFDerivAt
    have h := HasFDerivAt.comp_hasDerivAt (F := E n) (E := ℝ) (0 : ℝ) hD (hLine 0)
    have hR : fderiv ℝ H x (e[n] i) = realThirdDerivative u x (e[n] i) (e[n] j) (e[n] k) :=
      fderiv_realHessian_apply huAt _ _ _
    have he := (h.tendsto_slope_zero.comp htLim).pow 2
    simpa only [Function.comp_def, zero_add, zero_smul, add_zero, smul_eq_mul, hR, H, p] using he
  have hBound' (m : ℕ) : (∫ x, F m x ∂μ) ≤ C := by
    have hSmall : ‖p m‖ < ε := (hp m).trans_lt (((htB m).trans (min_le_left _ _)).trans_lt (half_lt_self hε))
    have h := hEst hu hf hu0 huP huEq hDen hGrad hGradF hHess (p m) hSmall
    have he : (∫ x, F m x ∂μ) =
        (t m)⁻¹ ^ 2 * ∫ x, ∑ j, ∑ k,
          ((realHessian u (x + p m) - realHessian u x) (e[n] j) (e[n] k)) ^ 2 ∂μ := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [F, mul_pow, Finset.mul_sum, _root_.sub_apply]
    rw [he]
    refine (mul_le_mul_of_nonneg_left h (sq_nonneg _)).trans_eq ?_
    rw [hp, ← mul_assoc, mul_comm ((t m)⁻¹ ^ 2), mul_assoc, ← mul_pow, inv_mul_cancel₀ (ht m).ne',
      one_pow, mul_one]
  exact integral_le_of_ae_tendsto_nonneg hC (fun m => hI (hFC m)) (hI hGC)
    (fun m => Eventually.of_forall fun x => by dsimp [F]; positivity)
    (Eventually.of_forall fun x => by dsimp [G]; positivity) hLim (Eventually.of_forall hBound')


/-- With the uniform first and second derivative bounds, every real third
derivative of a smooth positive Dirichlet solution is uniformly in (L²). -/
theorem exists_integral_sq_realThirdDerivative_le_of_dirichlet_data {n : ℕ} (hn : 0 < n)
    {a b D B L : ℝ} (ha : 0 < a) (hb : 0 < b) (hD : 0 < D) (hB : 0 ≤ B) (hL : 0 ≤ L) :
    ∃ C ≥ (0 : ℝ), ∀ {u f : E n → ℝ},
      SmoothNear (closedUnitBall n) u → SmoothNear (closedUnitBall n) f →
      (∀ x ∈ unitSphere n, u x = 0) →
      (∀ x ∈ unitBall n, (complexHessian u x).PosDef) →
      (∀ x ∈ unitBall n, (complexHessian u x).det.re = f x) →
      (∀ x ∈ unitBall n, a ^ n ≤ f x ∧ f x ≤ b ^ n) →
      (∀ x ∈ closedUnitBall n, ‖fderiv ℝ u x‖ ≤ B) →
      (∀ x ∈ closedUnitBall n, ‖fderiv ℝ f x‖ ≤ L) →
      (∀ x ∈ closedUnitBall n, ‖realHessian u x‖ ≤ D) →
      (∫ x in unitBall n, ∑ i, ∑ j, ∑ k,
        (realThirdDerivative u x (e[n] i) (e[n] j) (e[n] k)) ^ 2 ∂volume0 n) ≤ C := by
  obtain ⟨C, hC, hCenter⟩ := exists_integral_sq_realThirdDerivative_center_le hn
    (b := b ^ n) (pow_pos ha n) hD hB hL
  obtain ⟨A, hA, hAnnulus⟩ := exists_integral_sq_realThirdDerivative_le_on_annulus hn
    ha hb hD hL (r := 1 / 4) (by norm_num)
  refine ⟨(2 * n : ℝ) * C + A, by positivity, ?_⟩
  intro u f hu hf hu0 huP huEq hDen hGrad hGradF hHess
  let Ω := ball (0 : E n) (1 / 4)
  let S := unitBall n ∩ {x | (1 : ℝ) / 4 ≤ ‖x‖}
  let q (i : Fin (2 * n)) (x : E n) := ∑ j, ∑ k,
    (realThirdDerivative u x (e[n] i) (e[n] j) (e[n] k)) ^ 2
  let Q (x : E n) := ∑ i, q i x
  have hΩ : Ω ⊆ unitBall n := ball_subset_ball (by norm_num)
  have hS : S ⊆ unitBall n := inter_subset_left
  have hSM : MeasurableSet S := measurableSet_ball.inter
    (isClosed_le continuous_const continuous_norm).measurableSet
  have hUnion : Ω ∪ S = unitBall n := by
    ext x
    constructor
    · exact fun hx => hx.elim (fun hy => hΩ hy) (fun hy => hS hy)
    · intro hx
      exact (lt_or_ge ‖x‖ (1 / 4)).imp (mem_ball_zero_iff.mpr) (fun hr => ⟨hx, hr⟩)
  have hDisj : Disjoint Ω S := by
    apply disjoint_left.mpr
    intro x hx hx'
    exact (not_le_of_gt (mem_ball_zero_iff.mp hx)) hx'.2
  obtain ⟨U, hU, hSub, huU⟩ := hu
  have hu : SmoothNear (closedUnitBall n) u := ⟨U, hU, hSub, huU⟩
  have hD₁ := huU.fderiv_of_isOpen hU (m := ∞) (by simp)
  have hD₂ := hD₁.fderiv_of_isOpen hU (m := ∞) (by simp)
  have hT : ContDiffOn ℝ ∞ (realThirdDerivative u) U := hD₂.fderiv_of_isOpen hU (m := ∞) (by simp)
  have hq (i : Fin (2 * n)) : ContinuousOn (q i) U := continuousOn_finsetSum Finset.univ fun j _ =>
    continuousOn_finsetSum Finset.univ fun k _ =>
      (((hT.continuousOn.clm_apply continuousOn_const).clm_apply continuousOn_const).clm_apply
        continuousOn_const).pow 2
  have hQC : ContinuousOn Q U := continuousOn_finsetSum Finset.univ fun i _ => hq i
  have hI {g : E n → ℝ} (hg : ContinuousOn g U) : IntegrableOn g (unitBall n) (volume0 n) :=
    (hg.mono hSub).integrableOn_of_subset_isCompact (isCompact_closedBall _ _)
      measurableSet_ball ball_subset_closedBall (by rw [volume0_unitBall n hn]; exact ENNReal.one_ne_top)
  have hCI : (∫ x in Ω, Q x ∂volume0 n) ≤ (2 * n : ℝ) * C := by
    unfold Q
    rw [integral_finsetSum _ (fun i _ => (hI (hq i)).mono_set hΩ)]
    exact (Finset.sum_le_sum fun i _ => hCenter hu hf hu0 huP huEq hDen hGrad hGradF hHess i).trans_eq
      (by simp [Nat.cast_mul])
  have hAI : (∫ x in S, Q x ∂volume0 n) ≤ A := hAnnulus hu hf hu0 huP huEq hDen hGradF
    (fun x hx w hw => by
      rw [← Real.norm_eq_abs]
      exact ((realHessian u x w).le_opNorm w).trans (by
        rw [hw, mul_one]
        exact ((realHessian u x).le_opNorm w).trans (by rw [hw, mul_one]; exact hHess x hx)))
  change (∫ x in unitBall n, Q x ∂volume0 n) ≤ _
  rw [← hUnion, setIntegral_union hDisj hSM ((hI hQC).mono_set hΩ) ((hI hQC).mono_set hS)]
  exact add_le_add hCI hAI


/-- Smooth solutions along a fixed log-density path have a single uniform
closed-ball third-derivative square-integral bound. -/
theorem exists_integral_sq_realThirdDerivative_le_of_logDensityPath {n : ℕ} (hn : 0 < n)
    {g : E n → ℝ} (hg : SmoothNear (closedUnitBall n) g) :
    ∃ C ≥ (0 : ℝ), ∀ t ∈ Icc (0 : ℝ) 1, ∀ {u : E n → ℝ},
      SmoothNear (closedUnitBall n) u → (∀ x ∈ unitSphere n, u x = 0) →
      (∀ x ∈ unitBall n, (complexHessian u x).PosDef) →
      (∀ x ∈ unitBall n, (complexHessian u x).det.re = Real.exp (t * g x)) →
      (∫ x in unitBall n, ∑ i, ∑ j, ∑ k,
        (realThirdDerivative u x (e[n] i) (e[n] j) (e[n] k)) ^ 2 ∂volume0 n) ≤ C := by
  obtain ⟨a, b, K, M, ha, hb, hK, hM, hBounds⟩ := exists_logDensityPath_bounds hn hg
  let d := (3 * K + 1) / (n : ℝ)
  let C := 2 * b + 4 * b * d +
    (2 * b + 4 * (b ^ n / a ^ (n - 1) + (b * d) ^ 2 / (4 * a)))
  let D := C + ((M + 1) / (n : ℝ)) * b
  let B := 2 * b + ((K + 1) / (n : ℝ)) * b
  let L := b ^ n * K
  have hD : 0 < D := by dsimp [D, C, d]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hL : 0 ≤ L := by dsimp [L]; positivity
  obtain ⟨A, hA, hEst⟩ := exists_integral_sq_realThirdDerivative_le_of_dirichlet_data hn ha hb hD hB hL
  refine ⟨A, hA, ?_⟩
  intro t ht u hu hu0 huP hEq
  let f (x : E n) := Real.exp (t * g x)
  have hf : SmoothNear (closedUnitBall n) f := by
    obtain ⟨U, hU, hSub, hgU⟩ := hg
    exact ⟨U, hU, hSub, (contDiffOn_const.mul hgU).exp⟩
  have hDen (x : E n) (hx : x ∈ unitBall n) : a ^ n ≤ f x ∧ f x ≤ b ^ n :=
    (hBounds t ht).1 x (ball_subset_closedBall hx)
  have hLog (x : E n) (hx : x ∈ unitBall n) : ‖fderiv ℝ (fun y => Real.log (f y)) x‖ ≤ K :=
    (hBounds t ht).2.1 x (ball_subset_closedBall hx)
  have hF (x : E n) (hx : x ∈ closedUnitBall n) : ‖fderiv ℝ f x‖ ≤ L := by
    have hArg : DifferentiableAt ℝ (fun y => t * g y) x :=
      ((contDiffAt_const.mul (hg.contDiffAt hx)).differentiableAt (by simp))
    have h := hArg.hasFDerivAt.exp.fderiv
    change fderiv ℝ f x = _ at h
    rw [h, norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
    have hLogEq : (fun y => Real.log (f y)) = (fun y => t * g y) := by
      funext y
      exact Real.log_exp _
    have hLog' := (hBounds t ht).2.1 x hx
    change ‖fderiv ℝ (fun y => Real.log (f y)) x‖ ≤ K at hLog'
    rw [hLogEq] at hLog'
    exact mul_le_mul ((hBounds t ht).1 x hx).2 hLog' (norm_nonneg _) (by positivity)
  have hH (x : E n) (hx : x ∈ closedUnitBall n) (w : E n) (hw : ‖w‖ = 1) :
      |realHessian u x w w| ≤ D :=
    abs_realHessian_self_le_of_dirichlet_det hn hu hf hu0 huP hEq ha hb hM hDen
      (fun y hy v hv => abs_realHessian_self_le_on_sphere_of_dirichlet_det hn hu hf hu0 huP hEq ha hb hK hDen hLog hy hv)
      (fun y hy => (hBounds t ht).2.2 y (ball_subset_closedBall hy)) x hx w hw
  exact hEst hu hf hu0 huP hEq hDen
    (norm_fderiv_le_of_dirichlet_det hn hu hf hu0 huP hEq ha hb hK hDen hLog) hF
    (fun x hx => norm_realHessian_le_of_unit_test (hu.contDiffAt hx) hD.le (hH x hx))

end KEBall
