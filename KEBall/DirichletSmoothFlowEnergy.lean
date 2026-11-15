import KEBall.DirichletAngularL2
import KEBall.DirichletIteratedTensorDifferences

/-! Actual scalar flow differences satisfy an L2 estimate by the first
spatial jet. No compact support or zero boundary condition is required. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 700000

open Filter MeasureTheory Metric Set
open scoped ContDiff Gradient Interval Topology

namespace KEBall

local notation "ν[" n "]" => Measure.restrict (volume0 n) (unitBall n)

theorem integral_sq_smooth_angularDifferenceQuotient_le {n : ℕ} (hn : 0 < n)
    (S : E n →L[ℝ] E n) (hS : star S = -S)
    {φ : E n → ℝ} (hφ : ContDiff ℝ ∞ φ) {t : ℝ} (ht : t ≠ 0) :
    (∫ x, (t⁻¹ * (φ (orthogonalFlow S hS t x) - φ x)) ^ 2 ∂ν[n]) ≤
      ‖S‖ ^ 2 * ∫ x, ‖∇ φ x‖ ^ 2 ∂ν[n] := by
  have : NeZero n := ⟨hn.ne'⟩
  have : IsProbabilityMeasure ν[n] := volume0_restrict_isProbability n
  let μ : Measure ℝ := volume.restrict (Ioc 0 1)
  have : IsProbabilityMeasure μ := ⟨by simp [μ, Real.volume_Ioc]⟩
  let R := orthogonalFlow S hS
  let D (x : E n) (s : ℝ) := fderiv ℝ φ (R (s * t) x) (R (s * t) (S x))
  have hd : Continuous (fderiv ℝ φ) :=
    (hφ.fderiv_right (m := ∞) (by simp)).continuous
  have hFlow : Continuous (fun p : E n × ℝ => R (p.2 * t) p.1) := by
    have hT : Continuous (fun s : ℝ => NormedSpace.exp (s • S)) :=
      continuous_iff_continuousAt.mpr fun s => (hasDerivAt_exp_smul_const S s).continuousAt
    exact (hT.comp (continuous_snd.mul continuous_const)).clm_apply continuous_fst
  have hFlowS : Continuous (fun p : E n × ℝ => R (p.2 * t) (S p.1)) :=
    hFlow.comp ((S.continuous.comp continuous_fst).prodMk continuous_snd)
  have hD : Continuous (fun p : E n × ℝ => D p.1 p.2) := (hd.comp hFlow).clm_apply hFlowS
  have hDb (x : E n) (hx : x ∈ unitBall n) (s : ℝ) :
      ‖D x s‖ ≤ ‖∇ φ (R (s * t) x)‖ * ‖S‖ := by
    have hSx : ‖R (s * t) (S x)‖ ≤ ‖S‖ := by
      rw [LinearIsometryEquiv.norm_map]
      exact (S.le_opNorm x).trans
        (mul_le_of_le_one_right (norm_nonneg _) (mem_ball_zero_iff.mp hx).le)
    rw [show D x s = inner ℝ (∇ φ (R (s * t) x)) (R (s * t) (S x)) from
      inner_gradient_left.symm]
    exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left hSx (norm_nonneg _))
  have hAE := ae_restrict_mem (μ := volume0 n)
    (show MeasurableSet (unitBall n) from measurableSet_ball)
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : E n) 1).exists_bound_of_continuousOn
    (by
      have hG : Continuous (∇ φ) :=
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
      rw [sub_orthogonalFlow_eq_integral_fderiv S hS hφ, ← mul_assoc,
        inv_mul_cancel₀ ht, one_mul, intervalIntegral.integral_of_le zero_le_one]
    rw [he]
    exact hj
  have hInt {f : E n → ℝ} (hf : Continuous f) : Integrable f ν[n] :=
    hf.continuousOn.integrableOn_of_subset_isCompact (isCompact_closedBall _ _)
      measurableSet_ball ball_subset_closedBall
      (by rw [volume0_unitBall n hn]; exact ENNReal.one_ne_top)
  have hLeft : Integrable (fun x => (t⁻¹ * (φ (R t x) - φ x)) ^ 2) ν[n] :=
    hInt ((continuous_const.mul ((hφ.continuous.comp (R t).continuous).sub hφ.continuous)).pow 2)
  let J (x : E n) := ‖∇ φ x‖ ^ 2
  have hJ : Integrable J ν[n] := hInt
    (((InnerProductSpace.toDual ℝ (E n)).symm.continuous.comp hd).norm.pow 2)
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
    change D x s ^ 2 ≤ ‖S‖ ^ 2 * ‖∇ φ (R (s * t) x)‖ ^ 2
    rw [← sq_abs (D x s), ← Real.norm_eq_abs, ← mul_pow, mul_comm ‖S‖]
    exact pow_le_pow_left₀ (norm_nonneg _) (hDb x hx s) 2
  calc
    _ ≤ ∫ x, ∫ s, (D x s) ^ 2 ∂μ ∂ν[n] := integral_mono hLeft hProd.integral_prod_left hI
    _ = ∫ s, ∫ x, (D x s) ^ 2 ∂ν[n] ∂μ := integral_integral_swap hProd
    _ ≤ ∫ _, (‖S‖ ^ 2 * ∫ x, J x ∂ν[n]) ∂μ :=
      integral_mono hProd.integral_prod_right (integrable_const _) hInner
    _ = _ := by simp [J]


end KEBall
