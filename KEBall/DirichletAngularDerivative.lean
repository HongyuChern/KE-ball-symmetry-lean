import KEBall.DirichletAngularFlow
import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Angular weak derivatives in the zero-boundary Dirichlet space

The weak limit of bounded angular difference quotients is identified by
moving the orthogonal pullback to a smooth test function.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Bornology Filter MeasureTheory Metric Set
open scoped ContDiff Distributions NNReal Topology

namespace KEBall

private theorem realHilbert_weakBidual_surjective {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] :
    Function.Surjective (NormedSpace.inclusionInDoubleDualWeak ℝ H) := by
  intro b
  let D : StrongDual ℝ (StrongDual ℝ H) := StrongDual.toWeakDual.symm b
  let J := InnerProductSpace.toDual ℝ H
  let R : StrongDual ℝ H := D.comp J.toContinuousLinearEquiv.toContinuousLinearMap
  let x := J.symm R
  have hx (y : H) : inner ℝ x y = D (J y) := by
    exact congrArg (fun F : StrongDual ℝ H => F y) (J.apply_symm_apply R)
  refine ⟨toWeakSpace ℝ H x, ?_⟩
  apply StrongDual.toWeakDual.symm.injective
  ext d
  obtain ⟨y, rfl⟩ := J.surjective d
  change inner ℝ y x = D (J y)
  rw [real_inner_comm x y]
  exact hx y

/-- A norm-bounded sequence in a real Hilbert space has a cluster point
for the weak topology. -/
theorem realHilbert_exists_weakClusterPoint_of_bound {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {u : ℕ → H} {C : ℝ} (hC : ∀ j, ‖u j‖ ≤ C) :
    ∃ w : H, MapClusterPt (toWeakSpace ℝ H w) atTop (fun j => toWeakSpace ℝ H (u j)) := by
  let J := toWeakSpace ℝ H
  let S := J '' closedBall (0 : H) C
  have hb : IsBounded (J ⁻¹' S) := by
    rw [show J ⁻¹' S = closedBall (0 : H) C from preimage_image_eq _ J.injective]
    exact isBounded_closedBall
  have hRange : Set.range (NormedSpace.inclusionInDoubleDualWeak ℝ H) = univ :=
    Set.range_eq_univ.mpr realHilbert_weakBidual_surjective
  have hComp : IsCompact (closure S) :=
    NormedSpace.isCompact_closure_of_isBounded ℝ H S hb (by rw [hRange]; exact subset_univ _)
  have hMem : ∀ᶠ j in atTop, J (u j) ∈ closure S :=
    Eventually.of_forall fun j => subset_closure ⟨u j, mem_closedBall_zero_iff.mpr (hC j), rfl⟩
  obtain ⟨y, _, hy⟩ := hComp.exists_mapClusterPt (f := atTop) (u := fun j => J (u j))
    (Filter.le_principal_iff.mpr hMem)
  refine ⟨J.symm y, ?_⟩
  change MapClusterPt (J (J.symm y)) atTop (fun j => J (u j))
  rw [J.apply_symm_apply]
  exact hy

local notation "ν[" n "]" => Measure.restrict (volume0 n) (unitBall n)

private theorem test_angular_increment_le {n : ℕ} (S : E n →L[ℝ] E n)
    (hS : star S = -S) (ψ : E n → ℝ) {K : ℝ≥0}
    (hψ : LipschitzOnWith K ψ (closedUnitBall n)) (t : ℝ)
    {x : E n} (hx : x ∈ unitBall n) :
    ‖ψ ((orthogonalFlow S hS t).symm x) - ψ x‖ ≤ (K : ℝ) * (‖S‖ * |t|) := by
  let R := orthogonalFlow S hS (-t)
  let P := R.toContinuousLinearEquiv.toContinuousLinearMap - ContinuousLinearMap.id ℝ (E n)
  have hxR : R x ∈ unitBall n :=
    mem_ball_zero_iff.mpr (R.norm_map x ▸ mem_ball_zero_iff.mp hx)
  have hMove : dist (R x) x ≤ ‖S‖ * |t| := by
    calc
      dist (R x) x = ‖P x‖ := by rw [dist_eq_norm]; rfl
      _ ≤ ‖P‖ * ‖x‖ := P.le_opNorm x
      _ ≤ ‖P‖ := mul_le_of_le_one_right (norm_nonneg _) (mem_ball_zero_iff.mp hx).le
      _ ≤ ‖S‖ * |t| := by simpa only [P, R, abs_neg] using norm_orthogonalFlow_sub_id_le S hS (-t)
  rw [orthogonalFlow_symm_eq_neg S hS t, ← dist_eq_norm]
  exact (hψ.dist_le_mul (R x) (ball_subset_closedBall hxR) x (ball_subset_closedBall hx)).trans
    (mul_le_mul_of_nonneg_left hMove K.coe_nonneg)

private theorem tendsto_angular_test_integral {n : ℕ} (hn : 0 < n)
    (S : E n →L[ℝ] E n) (hS : star S = -S) (ψ : 𝓓(dirichletBallOpens n, ℝ))
    (f : DirichletBallL2 n ℝ) {t : ℕ → ℝ}
    (ht : Tendsto t atTop (𝓝[≠] 0)) (ht₀ : ∀ j, t j ≠ 0) :
    Tendsto (fun j => ∫ x, ((t j)⁻¹ * (ψ ((orthogonalFlow S hS (t j)).symm x) - ψ x)) * f x ∂ν[n])
      atTop (𝓝 (-(∫ x, fderiv ℝ (ψ : E n → ℝ) x (S x) * f x ∂ν[n]))) := by
  have : NeZero n := ⟨hn.ne'⟩
  have : IsProbabilityMeasure ν[n] := volume0_restrict_isProbability n
  have hf := (Lp.memLp f).integrable (by norm_num)
  have hc := (ψ.contDiff.fderiv_right (m := 0) (by simp)).continuous
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : E n) 1).exists_bound_of_continuousOn hc.continuousOn
  let K : ℝ≥0 := ⟨max 0 B, le_max_left _ _⟩
  have hK : LipschitzOnWith K (ψ : E n → ℝ) (closedUnitBall n) := by
    apply Convex.lipschitzOnWith_of_nnnorm_fderiv_le (𝕜 := ℝ) _ _ (convex_closedBall (0 : E n) 1)
    · exact fun x _ => ψ.contDiff.differentiable (by simp) x
    · intro x hx
      have he : ‖fderiv ℝ (ψ : E n → ℝ) x‖ ≤ (K : ℝ) := (hB x hx).trans (le_max_right _ _)
      exact_mod_cast he
  rw [← integral_neg]
  apply tendsto_integral_of_dominated_convergence (fun x => (K : ℝ) * ‖S‖ * ‖f x‖)
  · intro j
    have he : Continuous (fun x => (t j)⁻¹ *
        (ψ ((orthogonalFlow S hS (t j)).symm x) - ψ x)) :=
      continuous_const.mul ((ψ.continuous.comp (orthogonalFlow S hS (t j)).symm.continuous).sub
        ψ.continuous)
    exact he.aestronglyMeasurable.mul (Lp.aestronglyMeasurable f)
  · exact hf.norm.const_mul _
  · intro j
    filter_upwards [ae_restrict_mem (μ := volume0 n)
      (show MeasurableSet (unitBall n) from measurableSet_ball)] with x hx
    rw [norm_mul, norm_mul, Real.norm_eq_abs ((t j)⁻¹), abs_inv]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    calc
      _ ≤ |t j|⁻¹ * ((K : ℝ) * (‖S‖ * |t j|)) :=
        mul_le_mul_of_nonneg_left (test_angular_increment_le S hS (ψ : E n → ℝ) hK (t j) hx)
          (by positivity)
      _ = _ := by field_simp [abs_ne_zero.mpr (ht₀ j)]
  · filter_upwards with x
    have hP := hasDerivAt_test_orthogonalFlow_zero S hS (ψ.contDiff.differentiable (by simp) x)
    have hN : HasDerivAt (fun s => ψ ((orthogonalFlow S hS s).symm x))
        (-(fderiv ℝ (ψ : E n → ℝ) x (S x))) 0 := by
      have hP' : HasDerivAt (fun s => ψ (orthogonalFlow S hS s x))
          (fderiv ℝ (ψ : E n → ℝ) x (S x)) (-(0 : ℝ)) := by
        simpa only [neg_zero] using hP
      have hd : HasDerivAt (fun s => ψ (orthogonalFlow S hS (-s) x))
          ((fderiv ℝ (ψ : E n → ℝ) x (S x)) * (-1)) 0 :=
        HasDerivAt.comp (0 : ℝ) (h := fun s : ℝ => -s) hP' (hasDerivAt_neg' (0 : ℝ))
      simpa only [orthogonalFlow_symm_eq_neg, mul_neg, mul_one] using hd
    have hSlope := (hasDerivAt_iff_tendsto_slope_zero.mp hN).comp ht
    have hZero : ψ ((orthogonalFlow S hS 0).symm x) = ψ x := by
      rw [orthogonalFlow_symm_eq_neg, neg_zero, orthogonalFlow_zero_apply]
    have hLim : Tendsto (fun j => (t j)⁻¹ * (ψ ((orthogonalFlow S hS (t j)).symm x) - ψ x))
        atTop (𝓝 (-(fderiv ℝ (ψ : E n → ℝ) x (S x)))) := by
      simpa only [Function.comp_def, zero_add, smul_eq_mul, hZero] using hSlope
    simpa only [neg_mul] using hLim.mul_const (f x)

private theorem angular_differenceQuotient_test_integral {n : ℕ} (hn : 0 < n)
    (S : E n →L[ℝ] E n) (hS : star S = -S) (ψ : 𝓓(dirichletBallOpens n, ℝ))
    (u : DirichletSobolev n) (t : ℝ) :
    let q := t⁻¹ • (dirichletSobolevPullback (orthogonalFlow S hS t) u - u)
    (∫ x, ψ x * ((q : DirichletSobolev n) : DirichletBallL2Pair n).fst x ∂ν[n]) =
      ∫ x, (t⁻¹ * (ψ ((orthogonalFlow S hS t).symm x) - ψ x)) *
        (u : DirichletBallL2Pair n).fst x ∂ν[n] := by
  have : NeZero n := ⟨hn.ne'⟩
  have : IsProbabilityMeasure ν[n] := volume0_restrict_isProbability n
  let R := orthogonalFlow S hS t
  let f := (u : DirichletBallL2Pair n).fst
  let fR := (dirichletSobolevPullback R u : DirichletBallL2Pair n).fst
  have hf := (Lp.memLp f).integrable (by norm_num)
  have hfR := (Lp.memLp fR).integrable (by norm_num)
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : E n) 1).exists_bound_of_continuousOn
    ψ.continuous.continuousOn
  have hAE := ae_restrict_mem (μ := volume0 n) (show MeasurableSet (unitBall n) from measurableSet_ball)
  have hψ : ∀ᵐ x ∂ν[n], ‖ψ x‖ ≤ C := hAE.mono fun x hx => hC x (ball_subset_closedBall hx)
  have hψR : ∀ᵐ x ∂ν[n], ‖ψ (R.symm x)‖ ≤ C :=
    (orthogonal_measurePreserving_dirichletBall R.symm).quasiMeasurePreserving.tendsto_ae.eventually hψ
  have hi := hf.bdd_mul ψ.aestronglyMeasurable hψ
  have hiR := hfR.bdd_mul ψ.aestronglyMeasurable hψ
  have hi' : Integrable (fun x => ψ (R.symm x) * f x) ν[n] :=
    hf.bdd_mul (ψ.continuous.comp R.symm.continuous).aestronglyMeasurable hψR
  have hPush : (∫ x, ψ x * fR x ∂ν[n]) = ∫ x, ψ (R.symm x) * f x ∂ν[n] := by
    calc
      _ = ∫ x, ψ x * f (R x) ∂ν[n] := by
        apply integral_congr_ae
        filter_upwards [dirichletSobolevPullback_value_ae R u] with x hx
        change fR x = f (R x) at hx
        rw [hx]
      _ = _ := by
        have h := (orthogonal_measurePreserving_dirichletBall R).integral_comp
          R.toHomeomorph.toMeasurableEquiv.measurableEmbedding (fun x => ψ (R.symm x) * f x)
        simpa only [LinearIsometryEquiv.symm_apply_apply] using h
  change (∫ x, ψ x * (t⁻¹ • (fR - f)) x ∂ν[n]) =
    ∫ x, (t⁻¹ * (ψ (R.symm x) - ψ x)) * f x ∂ν[n]
  calc
    _ = t⁻¹ * ((∫ x, ψ x * fR x ∂ν[n]) - ∫ x, ψ x * f x ∂ν[n]) := by
      rw [← integral_sub hiR hi, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_smul t⁻¹ (fR - f), Lp.coeFn_sub fR f] with x hx hy
      simp only [hx, hy, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      ring
    _ = t⁻¹ * ((∫ x, ψ (R.symm x) * f x ∂ν[n]) - ∫ x, ψ x * f x ∂ν[n]) := by rw [hPush]
    _ = _ := by
      rw [← integral_sub hi' hi, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      ring

/-- Uniform gradient bounds on the angular difference quotients give a
zero-trace angular weak derivative. -/
theorem exists_dirichletSobolev_angularDerivative_of_bound {n : ℕ} (hn : 0 < n)
    (u : DirichletSobolev n) (S : E n →L[ℝ] E n) (hS : star S = -S)
    {C : ℝ} (hC : 0 ≤ C)
    (hBound : ∀ {t : ℝ}, t ≠ 0 →
      ‖((t⁻¹ • (dirichletSobolevPullback (orthogonalFlow S hS t) u - u) :
        DirichletSobolev n) : DirichletBallL2Pair n).snd‖ ≤ C) :
    ∃ v : DirichletSobolev n, ∀ ψ : 𝓓(dirichletBallOpens n, ℝ),
      (∫ x, ψ x * (v : DirichletBallL2Pair n).fst x ∂ν[n]) =
        -(∫ x, fderiv ℝ (ψ : E n → ℝ) x (S x) * (u : DirichletBallL2Pair n).fst x ∂ν[n]) := by
  let t (j : ℕ) := 1 / ((j : ℝ) + 1)
  have ht₀ (j : ℕ) : t j ≠ 0 := by dsimp [t]; positivity
  have ht : Tendsto t atTop (𝓝[≠] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨tendsto_one_div_add_atTop_nhds_zero_nat, Eventually.of_forall fun j => ht₀ j⟩
  let q (j : ℕ) : DirichletSobolev n := (t j)⁻¹ • (dirichletSobolevPullback (orthogonalFlow S hS (t j)) u - u)
  have hQ (j : ℕ) : ‖q j‖ ≤ 2 * C := by
    have he : ‖(q j : DirichletBallL2Pair n).snd‖ ≤ C := hBound (ht₀ j)
    have hp := dirichletSobolev_poincare hn (q j)
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hnSq : 1 ≤ (n : ℝ) ^ 2 := by nlinarith only [hnR]
    have hP := (mul_le_mul_of_nonneg_right hnSq (sq_nonneg ‖(q j : DirichletBallL2Pair n).fst‖)).trans hp
    have hP' : ‖(q j : DirichletBallL2Pair n).fst‖ ≤ ‖(q j : DirichletBallL2Pair n).snd‖ :=
      (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (by simpa only [one_mul] using hP)
    change ‖(q j : DirichletBallL2Pair n)‖ ≤ 2 * C
    have heq := WithLp.prod_norm_sq_eq_of_L2 (q j : DirichletBallL2Pair n)
    have hs₁ := pow_le_pow_left₀ (norm_nonneg _) (hP'.trans he) 2
    have hs₂ := pow_le_pow_left₀ (norm_nonneg _) he 2
    nlinarith only [heq, hs₁, hs₂, norm_nonneg (q j : DirichletBallL2Pair n), hC]
  obtain ⟨v, hv⟩ := realHilbert_exists_weakClusterPoint_of_bound hQ
  refine ⟨v, fun ψ => ?_⟩
  let F : DirichletSobolev n →L[ℝ] ℝ :=
    (innerSL ℝ (dirichletTestToL2 ψ)).comp
      ((WithLp.fstL 2 ℝ _ _).comp (dirichletSobolevSubmodule n).subtypeL)
  have hF (w : DirichletSobolev n) :
      F w = ∫ x, ψ x * (w : DirichletBallL2Pair n).fst x ∂ν[n] := by
    change inner ℝ (dirichletTestToL2 ψ) (w : DirichletBallL2Pair n).fst = _
    rw [MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    filter_upwards [dirichletTestToL2_ae ψ] with x hx
    rw [hx, Real.inner_apply]
  have hFc : Continuous (fun z : WeakSpace ℝ (DirichletSobolev n) => F ((toWeakSpace ℝ (DirichletSobolev n)).symm z)) :=
    WeakBilin.eval_continuous (topDualPairing ℝ (DirichletSobolev n)).flip F
  have hv' : MapClusterPt (F v) atTop (fun j => F (q j)) :=
    MapClusterPt.continuousAt_comp (X := WeakSpace ℝ (DirichletSobolev n))
      hFc.continuousAt hv
  have hLim : Tendsto (fun j => F (q j)) atTop
      (𝓝 (-(∫ x, fderiv ℝ (ψ : E n → ℝ) x (S x) * (u : DirichletBallL2Pair n).fst x ∂ν[n]))) := by
    apply (tendsto_angular_test_integral hn S hS ψ (u : DirichletBallL2Pair n).fst ht ht₀).congr
    intro j
    rw [hF]
    exact (angular_differenceQuotient_test_integral hn S hS ψ u (t j)).symm
  obtain ⟨φ, hφ, hSub⟩ := hv'.tendsto_subseq
  exact (hF v).symm.trans (tendsto_nhds_unique hSub (hLim.comp hφ.tendsto_atTop))

/-- A weak solution with Lipschitz coefficients and right-hand side has a
zero-trace angular weak derivative in the Dirichlet graph space. -/
theorem exists_dirichletSobolev_angularDerivative {n : ℕ} (hn : 0 < n)
    {A : E n → E n →L[ℝ] E n} (hA : MemLp A ⊤ ν[n]) {l : ℝ} (hl : 0 < l)
    (hE : ∀ᵐ x ∂ν[n], ∀ v : E n, l * ‖v‖ ^ 2 ≤ inner ℝ (A x v) v)
    {K L : ℝ≥0} (hLipA : LipschitzOnWith K A (closedUnitBall n))
    {M : ℝ} (hM₀ : 0 ≤ M) (hM : ∀ x ∈ closedUnitBall n, ‖A x‖ ≤ M)
    {g : DirichletBallL2 n ℝ} {G : E n → ℝ} (hRep : g =ᵐ[ν[n]] G)
    (hLipG : LipschitzOnWith L G (closedUnitBall n))
    {u : DirichletSobolev n} (hu : IsDirichletWeakSolution A g u)
    (S : E n →L[ℝ] E n) (hS : star S = -S) :
    ∃ v : DirichletSobolev n, ∀ ψ : 𝓓(dirichletBallOpens n, ℝ),
      (∫ x, ψ x * (v : DirichletBallL2Pair n).fst x ∂ν[n]) =
        -(∫ x, fderiv ℝ (ψ : E n → ℝ) x (S x) * (u : DirichletBallL2Pair n).fst x ∂ν[n]) := by
  let C := (((L : ℝ) / n + ((K : ℝ) + 2 * M) * ‖(u : DirichletBallL2Pair n).snd‖) * ‖S‖) / l
  have hC : 0 ≤ C := by dsimp [C]; positivity
  apply exists_dirichletSobolev_angularDerivative_of_bound hn u S hS hC
  intro t ht
  apply (le_div_iff₀ hl).mpr
  rw [mul_comm]
  exact norm_dirichletGradient_angular_differenceQuotient_le hn hA hE hLipA hM₀ hM hRep hLipG hu S hS ht

end KEBall
