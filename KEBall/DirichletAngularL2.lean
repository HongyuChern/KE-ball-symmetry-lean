import KEBall.DirichletAngularDerivative
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Mul

/-! The derivative formula for angular difference quotients along the actual flow. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Function MeasureTheory Metric Set TopologicalSpace
open scoped ContDiff Distributions Gradient Interval NNReal Topology

namespace KEBall

local notation "ν[" n "]" => Measure.restrict (volume0 n) (unitBall n)

theorem hasDerivAt_orthogonalFlow_apply {n : ℕ} (S : E n →L[ℝ] E n)
    (hS : star S = -S) (x : E n) (t : ℝ) :
    HasDerivAt (fun s => orthogonalFlow S hS s x) (orthogonalFlow S hS t (S x)) t :=
  (ContinuousLinearMap.apply ℝ (E n) x).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_exp_smul_const S t)

theorem sub_orthogonalFlow_eq_integral_fderiv {n : ℕ} (S : E n →L[ℝ] E n)
    (hS : star S = -S) {ψ : E n → ℝ} (hψ : ContDiff ℝ ∞ ψ) (x : E n) (t : ℝ) :
    ψ (orthogonalFlow S hS t x) - ψ x =
      t * ∫ s in (0 : ℝ)..1,
        fderiv ℝ ψ (orthogonalFlow S hS (s * t) x) (orthogonalFlow S hS (s * t) (S x)) := by
  let R := orthogonalFlow S hS
  let D (s : ℝ) := fderiv ℝ ψ (R (s * t) x) (R (s * t) (S x))
  have hR (y : E n) : Continuous (fun s => R s y) :=
    continuous_iff_continuousAt.mpr fun s => (hasDerivAt_orthogonalFlow_apply S hS y s).continuousAt
  have hD : Continuous D := by
    have hd : Continuous (fderiv ℝ ψ) := (hψ.fderiv_right (m := ∞) (by simp)).continuous
    have ht : Continuous (fun s : ℝ => s * t) := continuous_id.mul continuous_const
    exact (hd.comp ((hR x).comp ht)).clm_apply ((hR (S x)).comp ht)
  have hDeriv (s : ℝ) : HasDerivAt (fun k : ℝ => ψ (R (k * t) x)) (t * D s) s := by
    have hShift : HasDerivAt (fun k : ℝ => k * t) t s := by
      simpa only [id_eq, one_mul] using (hasDerivAt_id s).mul_const t
    have hPath : HasDerivAt (fun k : ℝ => R (k * t) x) (t • R (s * t) (S x)) s := by
      simpa only [Function.comp_def, R] using
        (hasDerivAt_orthogonalFlow_apply S hS x (s * t)).scomp s hShift
    have h := (hψ.differentiable (by simp) (R (s * t) x)).hasFDerivAt.comp_hasDerivAt s hPath
    simpa only [Function.comp_def, map_smul, smul_eq_mul, D] using h
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hDeriv s)
    ((continuous_const.mul hD).intervalIntegrable 0 1)
  rw [intervalIntegral.integral_const_mul] at he
  simpa only [one_mul, zero_mul, R, orthogonalFlow_zero_apply, D] using he.symm

private theorem integral_sq_angularDifferenceQuotient_le {n : ℕ} (hn : 0 < n)
    (S : E n →L[ℝ] E n) (hS : star S = -S)
    (φ : 𝓓(dirichletBallOpens n, ℝ)) {t : ℝ} (ht : t ≠ 0) :
    (∫ x, (t⁻¹ * (φ (orthogonalFlow S hS t x) - φ x)) ^ 2 ∂ν[n]) ≤
      ‖S‖ ^ 2 * ∫ x, ‖∇ (φ : E n → ℝ) x‖ ^ 2 ∂ν[n] := by
  have : NeZero n := ⟨hn.ne'⟩
  have : IsProbabilityMeasure ν[n] := volume0_restrict_isProbability n
  let μ : Measure ℝ := volume.restrict (Ioc 0 1)
  have : IsProbabilityMeasure μ := ⟨by simp [μ, Real.volume_Ioc]⟩
  let R := orthogonalFlow S hS
  let D (x : E n) (s : ℝ) := fderiv ℝ (φ : E n → ℝ) (R (s * t) x) (R (s * t) (S x))
  have hd : Continuous (fderiv ℝ (φ : E n → ℝ)) :=
    (φ.contDiff.fderiv_right (m := ∞) (by simp)).continuous
  have hFlow : Continuous (fun p : E n × ℝ => R (p.2 * t) p.1) := by
    have hT : Continuous (fun s : ℝ => NormedSpace.exp (s • S)) :=
      continuous_iff_continuousAt.mpr fun s => (hasDerivAt_exp_smul_const S s).continuousAt
    exact (hT.comp (continuous_snd.mul continuous_const)).clm_apply continuous_fst
  have hFlowS : Continuous (fun p : E n × ℝ => R (p.2 * t) (S p.1)) :=
    hFlow.comp ((S.continuous.comp continuous_fst).prodMk continuous_snd)
  have hD : Continuous (fun p : E n × ℝ => D p.1 p.2) := (hd.comp hFlow).clm_apply hFlowS
  have hDb (x : E n) (hx : x ∈ unitBall n) (s : ℝ) :
      ‖D x s‖ ≤ ‖∇ (φ : E n → ℝ) (R (s * t) x)‖ * ‖S‖ := by
    have hSx : ‖R (s * t) (S x)‖ ≤ ‖S‖ := by
      rw [LinearIsometryEquiv.norm_map]
      exact (S.le_opNorm x).trans
        (mul_le_of_le_one_right (norm_nonneg _) (mem_ball_zero_iff.mp hx).le)
    rw [show D x s = inner ℝ (∇ (φ : E n → ℝ) (R (s * t) x)) (R (s * t) (S x)) from
      inner_gradient_left.symm]
    exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left hSx (norm_nonneg _))
  have hAE := ae_restrict_mem (μ := volume0 n)
    (show MeasurableSet (unitBall n) from measurableSet_ball)
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : E n) 1).exists_bound_of_continuousOn
    (by
      have hG : Continuous (∇ (φ : E n → ℝ)) :=
        (InnerProductSpace.toDual ℝ (E n)).symm.continuous.comp hd
      exact hG.continuousOn)
  have hProd : Integrable (fun p : E n × ℝ => (D p.1 p.2) ^ 2) (ν[n].prod μ) := by
    have hP : ∀ᵐ p : E n × ℝ ∂ν[n].prod μ, p.1 ∈ unitBall n :=
      (Measure.quasiMeasurePreserving_fst (μ := ν[n]) (ν := μ)).tendsto_ae.eventually hAE
    have hMeas : AEStronglyMeasurable (fun p : E n × ℝ => (D p.1 p.2) ^ 2) (ν[n].prod μ) :=
      (hD.pow 2).aestronglyMeasurable
    refine (memLp_top_of_bound hMeas ((C * ‖S‖) ^ 2) ?_).integrable (by simp)
    filter_upwards [hP] with p hp
    have hBall : R (p.2 * t) p.1 ∈ closedUnitBall n := by
      apply ball_subset_closedBall
      apply mem_ball_zero_iff.mpr
      rw [(R (p.2 * t)).norm_map]
      exact mem_ball_zero_iff.mp hp
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _)
      ((hDb p.1 hp p.2).trans (mul_le_mul_of_nonneg_right (hC _ hBall) (norm_nonneg _))) 2
  have hI (x : E n) : (t⁻¹ * (φ (R t x) - φ x)) ^ 2 ≤ ∫ s, (D x s) ^ 2 ∂μ := by
    have hDx : Continuous (D x) := hD.comp (continuous_const.prodMk continuous_id)
    have h1 : Integrable (D x) μ := (hDx.intervalIntegrable 0 1).1
    have h2 : Integrable (fun s => (D x s) ^ 2) μ := ((hDx.pow 2).intervalIntegrable 0 1).1
    have hj := ((by decide : Even (2 : ℕ)).convexOn_pow (𝕜 := ℝ)).map_integral_le
      (continuous_id.pow 2).continuousOn isClosed_univ
      (Eventually.of_forall fun _ => mem_univ _) h1 h2
    have he : t⁻¹ * (φ (R t x) - φ x) = ∫ s, D x s ∂μ := by
      rw [sub_orthogonalFlow_eq_integral_fderiv S hS φ.contDiff, ← mul_assoc,
        inv_mul_cancel₀ ht, one_mul, intervalIntegral.integral_of_le zero_le_one]
    rw [he]
    exact hj
  have hLeft : Integrable (fun x => (t⁻¹ * (φ (R t x) - φ x)) ^ 2) ν[n] := by
    let f (x : E n) := t⁻¹ * (φ (R t x) - φ x)
    have hC : Continuous f :=
      continuous_const.mul ((φ.continuous.comp (R t).continuous).sub φ.continuous)
    have hSupp : HasCompactSupport f := HasCompactSupport.mul_left (f := fun _ => t⁻¹)
      ((φ.hasCompactSupport.comp_homeomorph (R t).toHomeomorph).sub φ.hasCompactSupport)
    exact (hC.pow 2).integrable_of_hasCompactSupport (by
      simpa only [pow_two] using hSupp.mul_right (f' := f))
  let J (x : E n) := ‖∇ (φ : E n → ℝ) x‖ ^ 2
  have hJ : Integrable J ν[n] := by
    let g := dirichletTestGradientToL2 n φ
    have hI' : Integrable (fun x => ‖g x‖ ^ 2) ν[n] := by
      simpa only [real_inner_self_eq_norm_sq] using MeasureTheory.L2.integrable_inner (𝕜 := ℝ) g g
    exact hI'.congr ((dirichletTestGradientToL2_ae φ).mono fun x hx => by change g x = _ at hx; simp [J, hx])
  have hInner (s : ℝ) : (∫ x, (D x s) ^ 2 ∂ν[n]) ≤ ‖S‖ ^ 2 * ∫ x, J x ∂ν[n] := by
    have hDR : Integrable (fun x => (D x s) ^ 2) ν[n] := by
      have hCont : Continuous (fun x => (D x s) ^ 2) :=
        (hD.comp (continuous_id.prodMk continuous_const)).pow 2
      refine (memLp_top_of_bound hCont.aestronglyMeasurable ((C * ‖S‖) ^ 2) ?_).integrable (by simp)
      filter_upwards [hAE] with x hx
      have hxR : R (s * t) x ∈ closedUnitBall n := by
        apply ball_subset_closedBall
        apply mem_ball_zero_iff.mpr
        rw [(R (s * t)).norm_map]
        exact mem_ball_zero_iff.mp hx
      rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _)
        ((hDb x hx s).trans (mul_le_mul_of_nonneg_right (hC _ hxR) (norm_nonneg _))) 2
    have hMP := orthogonal_measurePreserving_dirichletBall (R (s * t))
    have hIJ := hMP.integrable_comp_of_integrable hJ
    have hEq : (∫ x, J (R (s * t) x) ∂ν[n]) = ∫ x, J x ∂ν[n] :=
      hMP.integral_comp (R (s * t)).toHomeomorph.toMeasurableEquiv.measurableEmbedding J
    rw [← hEq, ← integral_const_mul]
    refine integral_mono_ae hDR (hIJ.const_mul _) ?_
    filter_upwards [hAE] with x hx
    change D x s ^ 2 ≤ ‖S‖ ^ 2 * ‖∇ (φ : E n → ℝ) (R (s * t) x)‖ ^ 2
    rw [← sq_abs (D x s), ← Real.norm_eq_abs, ← mul_pow, mul_comm ‖S‖]
    exact pow_le_pow_left₀ (norm_nonneg _) (hDb x hx s) 2
  calc
    _ ≤ ∫ x, ∫ s, (D x s) ^ 2 ∂μ ∂ν[n] := integral_mono hLeft hProd.integral_prod_left hI
    _ = ∫ s, ∫ x, (D x s) ^ 2 ∂ν[n] ∂μ := integral_integral_swap hProd
    _ ≤ ∫ _, (‖S‖ ^ 2 * ∫ x, J x ∂ν[n]) ∂μ :=
      integral_mono hProd.integral_prod_right (integrable_const _) hInner
    _ = _ := by simp [J]

private theorem dirichletL2_norm_sq {n : ℕ} {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (f : DirichletBallL2 n F) : ‖f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂ν[n] := by
  rw [← real_inner_self_eq_norm_sq f, MeasureTheory.L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

private theorem norm_dirichletTest_angularDifferenceQuotient_value_le {n : ℕ} (hn : 0 < n)
    (φ : 𝓓(dirichletBallOpens n, ℝ)) (S : E n →L[ℝ] E n) (hS : star S = -S)
    {t : ℝ} (ht : t ≠ 0) :
    ‖t⁻¹ • (dirichletL2Pullback (orthogonalFlow S hS t) (dirichletTestToL2 φ) -
      dirichletTestToL2 φ)‖ ≤ ‖S‖ * ‖dirichletTestGradientToL2 n φ‖ := by
  let R := orthogonalFlow S hS t
  let f := dirichletTestToL2 φ
  let g := dirichletTestGradientToL2 n φ
  let fR := dirichletL2Pullback R f
  change ‖t⁻¹ • (fR - f)‖ ≤ ‖S‖ * ‖g‖
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow, dirichletL2_norm_sq, dirichletL2_norm_sq g]
  have hEq :
      (∫ x, ‖(t⁻¹ • (fR - f)) x‖ ^ 2 ∂ν[n]) = ∫ x, (t⁻¹ * (φ (R x) - φ x)) ^ 2 ∂ν[n] := by
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_smul t⁻¹ (fR - f), Lp.coeFn_sub fR f, dirichletL2Pullback_ae R f,
      (orthogonal_measurePreserving_dirichletBall R).quasiMeasurePreserving.tendsto_ae.eventually
        (dirichletTestToL2_ae φ), dirichletTestToL2_ae φ] with x hs hsub hr hrp hp
    change fR x = f (R x) at hr
    change f (R x) = φ (R x) at hrp
    change f x = φ x at hp
    simp only [hs, hsub, hr, hrp, hp, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Real.norm_eq_abs, sq_abs]
  have hGrad : (∫ x, ‖g x‖ ^ 2 ∂ν[n]) = ∫ x, ‖∇ (φ : E n → ℝ) x‖ ^ 2 ∂ν[n] :=
    integral_congr_ae ((dirichletTestGradientToL2_ae φ).mono fun x hx => by
      change g x = _ at hx
      change ‖g x‖ ^ 2 = ‖∇ (φ : E n → ℝ) x‖ ^ 2
      rw [hx])
  rw [hEq, hGrad]
  exact integral_sq_angularDifferenceQuotient_le hn S hS φ ht

/-- The scalar angular difference quotient is bounded by the gradient
on the whole zero-boundary graph. -/
theorem norm_dirichletAngularDifferenceQuotient_value_le {n : ℕ} (hn : 0 < n)
    (u : DirichletSobolev n) (S : E n →L[ℝ] E n) (hS : star S = -S)
    {t : ℝ} (ht : t ≠ 0) :
    ‖((t⁻¹ • (dirichletSobolevPullback (orthogonalFlow S hS t) u - u) : DirichletSobolev n) :
      DirichletBallL2Pair n).fst‖ ≤ ‖S‖ * ‖(u : DirichletBallL2Pair n).snd‖ := by
  let R := orthogonalFlow S hS t
  let P : Set (DirichletBallL2Pair n) :=
    {z | ‖t⁻¹ • (dirichletL2Pullback R z.fst - z.fst)‖ ≤ ‖S‖ * ‖z.snd‖}
  have hClosed : IsClosed P := isClosed_le (by fun_prop) (by fun_prop)
  have hRange : ((dirichletTestL2Graph n).range : Set (DirichletBallL2Pair n)) ⊆ P := by
    rintro _ ⟨φ, rfl⟩
    exact norm_dirichletTest_angularDifferenceQuotient_value_le hn φ S hS ht
  exact closure_minimal hRange hClosed u.property

theorem dirichletL2Pullback_inner {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (R : E n ≃ₗᵢ[ℝ] E n) (f g : DirichletBallL2 n F) :
    inner ℝ (dirichletL2Pullback R f) g = inner ℝ f (dirichletL2Pullback R.symm g) := by
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  calc
    _ = ∫ x, inner ℝ (f (R x)) (g x) ∂ν[n] := by
      apply integral_congr_ae
      filter_upwards [dirichletL2Pullback_ae R f] with x hx
      rw [hx]
    _ = ∫ x, inner ℝ (f x) (g (R.symm x)) ∂ν[n] := by
      have h := (orthogonal_measurePreserving_dirichletBall R).integral_comp
        R.toHomeomorph.toMeasurableEquiv.measurableEmbedding
        (fun x => inner ℝ (f x) (g (R.symm x)))
      simpa only [LinearIsometryEquiv.symm_apply_apply] using h
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [dirichletL2Pullback_ae R.symm g] with x hx
      rw [hx]

/-- An L² forcing gives a uniform bound on the angular gradient difference
quotients. Move the rotated forcing to the test before applying Cauchy–Schwarz. -/
theorem norm_dirichletGradient_angular_differenceQuotient_le_L2 {n : ℕ} (hn : 0 < n)
    {A : E n → E n →L[ℝ] E n} (hA : MemLp A ⊤ ν[n])
    {l : ℝ} (hE : ∀ᵐ x ∂ν[n], ∀ v : E n, l * ‖v‖ ^ 2 ≤ inner ℝ (A x v) v)
    {K : ℝ≥0} (hLipA : LipschitzOnWith K A (closedUnitBall n))
    {M : ℝ} (hM₀ : 0 ≤ M) (hM : ∀ x ∈ closedUnitBall n, ‖A x‖ ≤ M)
    {g : DirichletBallL2 n ℝ} {u : DirichletSobolev n} (hu : IsDirichletWeakSolution A g u)
    (S : E n →L[ℝ] E n) (hS : star S = -S) {t : ℝ} (ht : t ≠ 0) :
    l * ‖((t⁻¹ • (dirichletSobolevPullback (orthogonalFlow S hS t) u - u) :
      DirichletSobolev n) : DirichletBallL2Pair n).snd‖ ≤
      (‖g‖ + ((K : ℝ) + 2 * M) * ‖(u : DirichletBallL2Pair n).snd‖) * ‖S‖ := by
  let R := orthogonalFlow S hS t
  let B := orthogonalPullbackDirichletField R A
  let w := dirichletSobolevPullback R u
  let z := w - u
  let p := (z : DirichletBallL2Pair n).fst
  let Z := (z : DirichletBallL2Pair n).snd
  let δ := ((K : ℝ) + 2 * M) * (‖S‖ * |t|)
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have hB : MemLp B ⊤ ν[n] := memLp_orthogonalPullbackDirichletField R hLipA.continuousOn
  have hDiff : ∀ᵐ x ∂ν[n], ‖A x - B x‖ ≤ δ := by
    filter_upwards [ae_restrict_mem (μ := volume0 n)
      (show MeasurableSet (unitBall n) from measurableSet_ball)] with x hx
    exact (norm_orthogonalPullbackDirichletField_sub_le R hLipA hM hx).trans
      (mul_le_mul_of_nonneg_left (norm_orthogonalFlow_sub_id_le S hS t) (by positivity))
  have hNorm : ‖dirichletL2Pullback R.symm p - p‖ ≤ |t| * (‖S‖ * ‖Z‖) := by
    have hq := norm_dirichletAngularDifferenceQuotient_value_le hn z S hS (neg_ne_zero.mpr ht)
    change ‖(-t)⁻¹ • (dirichletL2Pullback (orthogonalFlow S hS (-t)) p - p)‖ ≤ _ at hq
    rw [← orthogonalFlow_symm_eq_neg S hS t] at hq
    have he (f : DirichletBallL2 n ℝ) : ‖f‖ = |t| * ‖(-t)⁻¹ • f‖ := by
      calc
        _ = ‖(-t) • ((-t)⁻¹ • f)‖ := by
          rw [smul_smul, mul_inv_cancel₀ (neg_ne_zero.mpr ht), one_smul]
        _ = _ := by rw [norm_smul, norm_neg, Real.norm_eq_abs]
    rw [he]
    exact mul_le_mul_of_nonneg_left hq (abs_nonneg _)
  have hWork : inner ℝ (dirichletL2Pullback R g - g) p ≤ (‖g‖ * ‖S‖ * |t|) * ‖Z‖ := by
    rw [inner_sub_left, dirichletL2Pullback_inner, ← inner_sub_right]
    exact (real_inner_le_norm _ _).trans ((mul_le_mul_of_nonneg_left hNorm (norm_nonneg _)).trans_eq
      (by ring))
  have h := norm_dirichletGradient_sub_le_of_weakSolutions_pairing hA hB hδ (by positivity)
    hE hDiff hu (hu.orthogonalPullback R) hWork
  rw [norm_dirichletSobolevPullback_gradient] at h
  change l * ‖t⁻¹ • Z‖ ≤ _
  rw [norm_smul, Real.norm_eq_abs, abs_inv]
  calc
    _ = |t|⁻¹ * (l * ‖Z‖) := by ring
    _ ≤ |t|⁻¹ * (‖g‖ * ‖S‖ * |t| + δ * ‖(u : DirichletBallL2Pair n).snd‖) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by
      dsimp [δ]
      field_simp [abs_ne_zero.mpr ht]

/-- A weak solution with Lipschitz coefficients and square-integrable
forcing has a zero-trace angular weak derivative. -/
theorem exists_dirichletSobolev_angularDerivative_L2 {n : ℕ} (hn : 0 < n)
    {A : E n → E n →L[ℝ] E n} (hA : MemLp A ⊤ ν[n]) {l : ℝ} (hl : 0 < l)
    (hE : ∀ᵐ x ∂ν[n], ∀ v : E n, l * ‖v‖ ^ 2 ≤ inner ℝ (A x v) v)
    {K : ℝ≥0} (hLipA : LipschitzOnWith K A (closedUnitBall n))
    {M : ℝ} (hM₀ : 0 ≤ M) (hM : ∀ x ∈ closedUnitBall n, ‖A x‖ ≤ M)
    {g : DirichletBallL2 n ℝ} {u : DirichletSobolev n} (hu : IsDirichletWeakSolution A g u)
    (S : E n →L[ℝ] E n) (hS : star S = -S) :
    ∃ v : DirichletSobolev n, ∀ ψ : 𝓓(dirichletBallOpens n, ℝ),
      (∫ x, ψ x * (v : DirichletBallL2Pair n).fst x ∂ν[n]) =
        -(∫ x, fderiv ℝ (ψ : E n → ℝ) x (S x) * (u : DirichletBallL2Pair n).fst x ∂ν[n]) := by
  let C := ((‖g‖ + ((K : ℝ) + 2 * M) * ‖(u : DirichletBallL2Pair n).snd‖) * ‖S‖) / l
  have hC : 0 ≤ C := by dsimp [C]; positivity
  apply exists_dirichletSobolev_angularDerivative_of_bound hn u S hS hC
  intro t ht
  apply (le_div_iff₀ hl).mpr
  rw [mul_comm]
  exact norm_dirichletGradient_angular_differenceQuotient_le_L2 hn hA hE hLipA hM₀ hM hu S hS ht

end KEBall
