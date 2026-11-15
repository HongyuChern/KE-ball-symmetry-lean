import KEBall.DirichletABP
import KEBall.DirichletABPDeterminant
import KEBall.DirichletDeterminantComparison

/-!
# A squared-density bound for the complex Dirichlet problem
-/

set_option autoImplicit false

open Filter MeasureTheory Metric Set
open scoped ComplexOrder ContDiff ENNReal Gradient Topology

namespace KEBall

private theorem dirichlet_abp_of_jacobian_bound {n : ℕ} (hn : 0 < n) {u f : E n → ℝ}
    (hu : SmoothNear (closedUnitBall n) u) (hf : ContinuousOn f (closedUnitBall n))
    (hu0 : ∀ x ∈ unitSphere n, u x = 0)
    (hJac : ∀ x ∈ nonnegHessianSet u, |(fderiv ℝ (∇ u) x).det| ≤ (4 : ℝ) ^ (2 * n) * f x ^ 2)
    {x : E n} (hx : x ∈ closedUnitBall n) (hxu : u x ≤ 0) :
    (-u x / 2) ^ (2 * n) ≤ (4 : ℝ) ^ (2 * n) * ∫ y in unitBall n, f y ^ 2 ∂volume0 n := by
  let r := -u x / 2
  let C : ℝ := 4 ^ (2 * n)
  have hr : 0 ≤ r := div_nonneg (neg_nonneg.mpr hxu) (by norm_num)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hI : IntegrableOn (fun y => f y ^ 2) (unitBall n) (volume0 n) :=
    (hf.pow 2).integrableOn_of_subset_isCompact (isCompact_closedBall _ _) measurableSet_ball
      ball_subset_closedBall (by rw [volume0_unitBall n hn]; exact ENNReal.one_ne_top)
  have hI' : IntegrableOn (fun y => C * f y ^ 2) (unitBall n) (volume0 n) := hI.const_mul C
  have hL : (volume : Measure (E n)) (ball 0 r) ≤
      ∫⁻ y in unitBall n, ENNReal.ofReal (C * f y ^ 2) := by
    apply (volume_ball_le_lintegral_det_gradient hu hu0 hx).trans
    have hS : MeasurableSet (nonnegHessianSet u) := measurableSet_nonnegHessianSet hu
    refine (lintegral_mono_ae ?_).trans (lintegral_mono_set (fun y hy => hy.1))
    filter_upwards [ae_restrict_mem (μ := volume) hS] with y hy
    exact ENNReal.ofReal_le_ofReal (hJac y hy)
  let c : ℝ := (n.factorial : ℝ) / Real.pi ^ n
  have hc : 0 < c := by dsimp [c]; positivity
  have hVol : ENNReal.ofReal c * (volume : Measure (E n)) (ball 0 r) =
      ENNReal.ofReal (r ^ (2 * n)) := by
    let : Nontrivial (E n) := Module.nontrivial_of_finrank_pos (R := ℝ)
      (by rw [finrank_E]; omega)
    rw [InnerProductSpace.volume_ball_of_dim_even (finrank_E n), finrank_E,
      ← ENNReal.ofReal_pow hr, ← ENNReal.ofReal_mul (pow_nonneg hr _), ← ENNReal.ofReal_mul hc.le]
    congr 1
    dsimp [c]
    field_simp
  have h := mul_le_mul_right hL (ENNReal.ofReal c)
  rw [hVol] at h
  change _ ≤ ENNReal.ofReal c • (∫⁻ y in unitBall n, ENNReal.ofReal (C * f y ^ 2)) at h
  rw [← lintegral_smul_measure, ← Measure.restrict_smul] at h
  change ENNReal.ofReal (r ^ (2 * n)) ≤
    ∫⁻ y in unitBall n, ENNReal.ofReal (C * f y ^ 2) ∂volume0 n at h
  rw [← ofReal_integral_eq_lintegral_ofReal hI' (Eventually.of_forall fun y => mul_nonneg hC (sq_nonneg _)),
    integral_const_mul] at h
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hC (integral_nonneg fun y => sq_nonneg _))).mp h

/-- The smooth Dirichlet solution has a zeroth-order estimate in terms of
the squared density integral with respect to normalized volume. -/
theorem dirichlet_abp {n : ℕ} (hn : 0 < n) {u f : E n → ℝ}
    (hu : SmoothNear (closedUnitBall n) u) (hf : ContinuousOn f (closedUnitBall n))
    (hu0 : ∀ x ∈ unitSphere n, u x = 0)
    (huP : ∀ x ∈ unitBall n, (complexHessian u x).PosDef)
    (hEq : ∀ x ∈ unitBall n, (complexHessian u x).det.re = f x)
    {x : E n} (hx : x ∈ closedUnitBall n) (hxu : u x ≤ 0) :
    (-u x / 2) ^ (2 * n) ≤ (4 : ℝ) ^ (2 * n) * ∫ y in unitBall n, f y ^ 2 ∂volume0 n := by
  apply dirichlet_abp_of_jacobian_bound hn hu hf hu0 _ hx hxu
  intro y hy
  have hyB : y ∈ unitBall n := hy.1
  simpa only [hEq y hyB] using abs_det_gradient_le_complexDet_sq
    (hu.contDiffAt (ball_subset_closedBall hyB)) (huP y hyB).posSemidef hy.2

private theorem dirichlet_abp_difference_lower {n : ℕ} (hn : 0 < n)
    {u v f g : E n → ℝ} (hu : SmoothNear (closedUnitBall n) u) (hv : SmoothNear (closedUnitBall n) v)
    (hf : ContinuousOn f (closedUnitBall n)) (hg : ContinuousOn g (closedUnitBall n))
    (hu0 : ∀ x ∈ unitSphere n, u x = 0) (hv0 : ∀ x ∈ unitSphere n, v x = 0)
    (hvP : ∀ x ∈ unitBall n, (complexHessian v x).PosDef)
    (hEqU : ∀ x ∈ unitBall n, (complexHessian u x).det.re = f x)
    (hEqV : ∀ x ∈ unitBall n, (complexHessian v x).det.re = g x)
    {x : E n} (hx : x ∈ closedUnitBall n) (hxu : u x ≤ v x) :
    ((v x - u x) / 2) ^ (2 * n) ≤
      (4 : ℝ) ^ (2 * n) * ∫ y in unitBall n, (f y - g y) ^ 2 ∂volume0 n := by
  let w (y : E n) := u y - v y
  have hw : SmoothNear (closedUnitBall n) w := by
    obtain ⟨U, hU, hSU, huU⟩ := hu
    obtain ⟨V, hV, hSV, hvV⟩ := hv
    exact ⟨U ∩ V, hU.inter hV, subset_inter hSU hSV, (huU.mono inter_subset_left).sub
      (hvV.mono inter_subset_right)⟩
  have hw0 (y : E n) (hy : y ∈ unitSphere n) : w y = 0 := by simp [w, hu0 y hy, hv0 y hy]
  have hj (y : E n) (hy : y ∈ nonnegHessianSet w) :
      |(fderiv ℝ (∇ w) y).det| ≤ (4 : ℝ) ^ (2 * n) * (f y - g y) ^ 2 := by
    have hyB : y ∈ unitBall n := hy.1
    have hyC := ball_subset_closedBall hyB
    have hA := complexHessian_posSemidef_of_realHessian_nonneg (hw.contDiffAt hyC) hy.2
    have hd := BedfordTaylor.det_re_add_ge hn hA (hvP y hyB)
    have hSum : complexHessian w y + complexHessian v y = complexHessian u y := by
      rw [show complexHessian w y = complexHessian u y - complexHessian v y from
        complexHessian_sub_at (hu.contDiffAt hyC) (hv.contDiffAt hyC), sub_add_cancel]
    rw [hSum, hEqU y hyB, hEqV y hyB, ← le_sub_iff_add_le] at hd
    have hD : 0 ≤ (complexHessian w y).det.re := (RCLike.nonneg_iff.mp hA.det_nonneg).1
    exact (abs_det_gradient_le_complexDet_sq (hw.contDiffAt hyC) hA hy.2).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hD hd 2) (by positivity))
  simpa only [w, neg_sub, Pi.sub_apply] using
    dirichlet_abp_of_jacobian_bound hn hw (hf.sub hg) hw0 hj hx (sub_nonpos.mpr hxu)

/-- The real gradient-image estimate controls the uniform difference of two
smooth zero-boundary solutions by the squared difference of their densities. -/
theorem dirichlet_abp_difference {n : ℕ} (hn : 0 < n)
    {u v f g : E n → ℝ} (hu : SmoothNear (closedUnitBall n) u) (hv : SmoothNear (closedUnitBall n) v)
    (hf : ContinuousOn f (closedUnitBall n)) (hg : ContinuousOn g (closedUnitBall n))
    (hu0 : ∀ x ∈ unitSphere n, u x = 0) (hv0 : ∀ x ∈ unitSphere n, v x = 0)
    (huP : ∀ x ∈ unitBall n, (complexHessian u x).PosDef)
    (hvP : ∀ x ∈ unitBall n, (complexHessian v x).PosDef)
    (hEqU : ∀ x ∈ unitBall n, (complexHessian u x).det.re = f x)
    (hEqV : ∀ x ∈ unitBall n, (complexHessian v x).det.re = g x)
    {x : E n} (hx : x ∈ closedUnitBall n) :
    (|u x - v x| / 2) ^ (2 * n) ≤
      (4 : ℝ) ^ (2 * n) * ∫ y in unitBall n, (f y - g y) ^ 2 ∂volume0 n := by
  rcases le_total (u x) (v x) with h | h
  · rw [abs_of_nonpos (sub_nonpos.mpr h), neg_sub]
    exact dirichlet_abp_difference_lower hn hu hv hf hg hu0 hv0 hvP hEqU hEqV hx h
  · rw [abs_of_nonneg (sub_nonneg.mpr h)]
    have hI : (fun y => (g y - f y) ^ 2) = fun y => (f y - g y) ^ 2 := by
      funext y
      ring
    simpa only [hI] using dirichlet_abp_difference_lower hn hv hu hg hf hv0 hu0 huP hEqV hEqU hx h

/-- Smooth zero-boundary solutions with Cauchy densities in L² converge
uniformly on the closed ball. -/
theorem exists_uniform_limit_of_dirichlet_density_cauchy {n : ℕ} (hn : 0 < n)
    {u f : ℕ → E n → ℝ}
    (hu : ∀ j, SmoothNear (closedUnitBall n) (u j))
    (hf : ∀ j, ContinuousOn (f j) (closedUnitBall n))
    (hu0 : ∀ j x, x ∈ unitSphere n → u j x = 0)
    (huP : ∀ j x, x ∈ unitBall n → (complexHessian (u j) x).PosDef)
    (hEq : ∀ j x, x ∈ unitBall n → (complexHessian (u j) x).det.re = f j x)
    (hCauchy : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ j ≥ N, ∀ k ≥ N,
      (∫ y in unitBall n, (f j y - f k y) ^ 2 ∂volume0 n) < ε) :
    ∃ v : E n → ℝ, TendstoUniformlyOn u v atTop (closedUnitBall n) ∧
      ContinuousOn v (closedUnitBall n) := by
  have hUC : UniformCauchySeqOn u atTop (closedUnitBall n) := by
    apply Metric.uniformCauchySeqOn_iff.mpr
    intro ε hε
    let C := (4 : ℝ) ^ (2 * n)
    have hC : 0 < C := by dsimp [C]; positivity
    obtain ⟨N, hN⟩ := hCauchy ((ε / 2) ^ (2 * n) / C) (by positivity)
    refine ⟨N, fun j hj k hk x hx => ?_⟩
    have h := dirichlet_abp_difference hn (hu j) (hu k) (hf j) (hf k)
      (hu0 j) (hu0 k) (huP j) (huP k) (hEq j) (hEq k) hx
    have h' := h.trans_lt ((lt_div_iff₀' hC).mp (hN j hj k hk))
    rw [Real.dist_eq]
    by_contra! hOpp
    exact h'.not_ge (pow_le_pow_left₀ (by positivity : 0 ≤ ε / 2)
      (div_le_div_of_nonneg_right hOpp (by norm_num)) _)
  have hPoint (x : E n) : ∃ v : ℝ, x ∈ closedUnitBall n → Tendsto (fun j => u j x) atTop (𝓝 v) := by
    by_cases hx : x ∈ closedUnitBall n
    · have hC : CauchySeq (fun j => u j x) := by
        apply Metric.cauchySeq_iff.mpr
        intro ε hε
        obtain ⟨N, hN⟩ := Metric.uniformCauchySeqOn_iff.mp hUC ε hε
        exact ⟨N, fun j hj k hk => hN j hj k hk x hx⟩
      obtain ⟨v, hv⟩ := cauchySeq_tendsto_of_complete hC
      exact ⟨v, fun _ => hv⟩
    · exact ⟨0, fun h => (hx h).elim⟩
  choose v hv using hPoint
  have hU := hUC.tendstoUniformlyOn_of_tendsto hv
  have hCont : ∀ᶠ j in atTop, ContinuousOn (u j) (closedUnitBall n) :=
    Eventually.of_forall fun j _ hx => ((hu j).contDiffAt hx).continuousAt.continuousWithinAt
  exact ⟨v, hU, hU.continuousOn hCont.frequently⟩

end KEBall
