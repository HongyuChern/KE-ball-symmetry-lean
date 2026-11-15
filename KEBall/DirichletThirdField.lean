import KEBall.DirichletThirdDerivative

/-! Testing weak derivatives along smooth vector fields on the unit ball. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Metric Set
open scoped ContDiff Distributions

namespace KEBall

local notation "ν[" n "]" => Measure.restrict (volume0 n) (unitBall n)

/-- Expanding a smooth vector field in an orthonormal basis gives the
coordinate product rule for the divergence of a scalar test times the field. -/
theorem sum_dirichletTestFieldDerivative_mul_eq {n : ℕ}
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n))
    (ψ : 𝓓(dirichletBallOpens n, ℝ)) {X : E n → E n} (hX : ContDiff ℝ ∞ X)
    (x : E n) :
    (∑ i, dirichletTestFieldDerivative
      (dirichletTestMul ψ ((innerSL ℝ (b i)).contDiff.comp hX))
        (fun _ => b i) contDiff_const x) =
      fderiv ℝ (ψ : E n → ℝ) x (X x) + ψ x * dirichletVectorDivergence b X x := by
  let c (i : Fin (2 * n)) (y : E n) := inner ℝ (b i) (X y)
  have hc (i : Fin (2 * n)) : ContDiff ℝ ∞ (c i) := (innerSL ℝ (b i)).contDiff.comp hX
  let τ (i : Fin (2 * n)) := dirichletTestMul ψ (hc i)
  let D (i : Fin (2 * n)) := dirichletTestFieldDerivative (τ i) (fun _ => b i) contDiff_const
  change (∑ i, D i x) = _
  have hProduct (i : Fin (2 * n)) (x : E n) :
      D i x = c i x * fderiv ℝ (ψ : E n → ℝ) x (b i) + ψ x * fderiv ℝ (c i) x (b i) := by
    change fderiv ℝ (fun y => ψ y * c i y) x (b i) = _
    rw [fderiv_fun_mul (ψ.contDiff.differentiable (by simp) x) ((hc i).differentiable (by simp) x)]
    simp [add_comm]
  simp_rw [hProduct, Finset.sum_add_distrib]
  rw [← Finset.mul_sum]
  congr 1
  calc
    _ = fderiv ℝ (ψ : E n → ℝ) x (∑ i, c i x • b i) := by
      simp only [map_sum, map_smul, smul_eq_mul]
    _ = _ := congrArg (fderiv ℝ (ψ : E n → ℝ) x) (b.sum_repr' (X x))

theorem sum_dirichletThirdDerivativeEntry_eq_field {n : ℕ} (hn : 0 < n)
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)) (u : DirichletSobolev n)
    (ψ : 𝓓(dirichletBallOpens n, ℝ)) (e w : E n)
    {X : E n → E n} (hX : ContDiff ℝ ∞ X) {F : E n → ℝ} (hF : MemLp F 2 ν[n])
    (heF : ∀ τ : 𝓓(dirichletBallOpens n, ℝ), dirichletHessianEntry u τ e w = ∫ x, τ x * F x ∂ν[n]) :
    (∑ i, dirichletThirdDerivativeEntry u
      (dirichletTestMul ψ ((innerSL ℝ (b i)).contDiff.comp hX)) (b i) e w) =
      -(∫ x, (fderiv ℝ (ψ : E n → ℝ) x (X x) + ψ x * dirichletVectorDivergence b X x) *
        F x ∂ν[n]) := by
  have : NeZero n := ⟨hn.ne'⟩
  have : IsProbabilityMeasure ν[n] := volume0_restrict_isProbability n
  let c (i : Fin (2 * n)) (x : E n) := inner ℝ (b i) (X x)
  have hc (i : Fin (2 * n)) : ContDiff ℝ ∞ (c i) := (innerSL ℝ (b i)).contDiff.comp hX
  let τ (i : Fin (2 * n)) := dirichletTestMul ψ (hc i)
  let D (i : Fin (2 * n)) := dirichletTestFieldDerivative (τ i) (fun _ => b i) contDiff_const
  have hInt (i : Fin (2 * n)) : Integrable (fun x => D i x * F x) ν[n] :=
    (D i).integrable_bilin (ContinuousLinearMap.lsmul ℝ ℝ)
      ((hF.integrable (by norm_num)).locallyIntegrable.locallyIntegrableOn (unitBall n))
  change (∑ i, dirichletThirdDerivativeEntry u (τ i) (b i) e w) = _
  simp_rw [dirichletThirdDerivativeEntry_eq_integral u e w heF]
  change (∑ i, -(∫ x, D i x * F x ∂ν[n])) = _
  rw [Finset.sum_neg_distrib, ← integral_finsetSum _ (fun i _ => hInt i)]
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    change (∑ i, D i x * F x) = _
    rw [← Finset.sum_mul]
    exact congrArg (fun t : ℝ => t * F x) (sum_dirichletTestFieldDerivative_mul_eq b ψ hX x)

theorem dirichletVectorDivergence_basisFun_eq_euclideanDivergence {n : ℕ}
    (X : E n → E n) (x : E n) :
    dirichletVectorDivergence (EuclideanSpace.basisFun (Fin (2 * n)) ℝ) X x =
      euclideanDivergence X x := by
  simp only [dirichletVectorDivergence, euclideanDivergence, EuclideanSpace.basisFun_inner]

theorem integral_dirichletTest_fieldDerivative_mul_smooth {n : ℕ} (hn : 0 < n)
    (ψ : 𝓓(dirichletBallOpens n, ℝ)) {G : E n → ℝ} (hG : ContDiff ℝ ∞ G)
    {X : E n → E n} (hX : ContDiff ℝ ∞ X) :
    let b := EuclideanSpace.basisFun (Fin (2 * n)) ℝ
    (∫ x, (fderiv ℝ (ψ : E n → ℝ) x (X x) + ψ x * dirichletVectorDivergence b X x) * G x ∂ν[n]) =
      -(∫ x, ψ x * fderiv ℝ G x (X x) ∂ν[n]) := by
  let b := EuclideanSpace.basisFun (Fin (2 * n)) ℝ
  let H (x : E n) := ψ x * G x
  let V (x : E n) := H x • X x
  let L (x : E n) := (fderiv ℝ (ψ : E n → ℝ) x (X x) + ψ x * dirichletVectorDivergence b X x) * G x
  let R (x : E n) := ψ x * fderiv ℝ G x (X x)
  have hH : ContDiff ℝ ∞ H := ψ.contDiff.mul hG
  have hV : ContDiff ℝ ∞ V := hH.smul hX
  have he (x : E n) : euclideanDivergence V x = L x + R x := by
    change euclideanDivergence (fun y => H y • X y) x = _
    rw [euclideanDivergence_smul (hH.differentiable (by simp) x) (hX.differentiable (by simp) x)]
    change H x * euclideanDivergence X x + fderiv ℝ (fun y => ψ y * G y) x (X x) = _
    rw [fderiv_fun_mul (ψ.contDiff.differentiable (by simp) x) (hG.differentiable (by simp) x)]
    simp only [L, R, H, b, dirichletVectorDivergence_basisFun_eq_euclideanDivergence,
      add_apply, smul_apply, smul_eq_mul]
    ring
  have hBoundary (θ : Sphere n) : inner ℝ θ.1 (V θ.1) = 0 := by
    have hz : ψ θ.1 = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hs
      have hb : θ.1 ∈ unitBall n := ψ.tsupport_subset hs
      exact (lt_irrefl _ ((mem_sphere_zero_iff_norm.mp θ.2) ▸ mem_ball_zero_iff.mp hb)).elim
    simp [V, H, hz]
  have hZero : (∫ x, euclideanDivergence V x ∂ν[n]) = 0 := by
    have hz := integral_unitBall_divergence_normalized hn (hV.of_le (by simp))
    simpa only [hBoundary, integral_zero, mul_zero] using hz
  have hLC : Continuous L :=
    ((((ψ.contDiff.fderiv_right (m := ∞) (by simp)).continuous.clm_apply hX.continuous).add
      (ψ.continuous.mul (contDiff_dirichletVectorDivergence b hX).continuous))).mul hG.continuous
  have hRC : Continuous R :=
    ψ.continuous.mul ((hG.fderiv_right (m := ∞) (by simp)).continuous.clm_apply hX.continuous)
  have hL : Integrable L ν[n] :=
    (hLC.continuousOn.integrableOn_compact (isCompact_closedBall (0 : E n) 1)).mono_set ball_subset_closedBall
  have hR : Integrable R ν[n] :=
    (hRC.continuousOn.integrableOn_compact (isCompact_closedBall (0 : E n) 1)).mono_set ball_subset_closedBall
  simp_rw [he, integral_add hL hR] at hZero
  change (∫ x, L x ∂ν[n]) = -(∫ x, R x ∂ν[n])
  linarith only [hZero]

end KEBall
