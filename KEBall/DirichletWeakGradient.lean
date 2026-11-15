import KEBall.DirichletSobolev
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-! The second component of the Dirichlet graph is the weak gradient. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Metric Set
open scoped ContDiff Distributions Gradient Topology

namespace KEBall

private noncomputable def dirichletTestDerivative {n : ℕ}
    (φ : 𝓓(dirichletBallOpens n, ℝ)) (v : E n) : 𝓓(dirichletBallOpens n, ℝ) :=
  TestFunction.lineDerivCLM ℝ v φ

private theorem dirichletTestDerivative_apply {n : ℕ}
    (φ : 𝓓(dirichletBallOpens n, ℝ)) (v x : E n) :
    dirichletTestDerivative φ v x = fderiv ℝ (φ : E n → ℝ) x v := by
  rw [dirichletTestDerivative, TestFunction.lineDerivCLM_apply_of_le (by simp)]
  exact (φ.contDiff.differentiable (by simp) x).lineDeriv_eq_fderiv

private theorem test_eq_zero_off_ball {n : ℕ} (φ : 𝓓(dirichletBallOpens n, ℝ))
    {x : E n} (hx : x ∉ unitBall n) : φ x = 0 :=
  image_eq_zero_of_notMem_tsupport (fun h => hx (φ.tsupport_subset h))

private theorem dirichletTest_integral_derivative {n : ℕ}
    (φ ψ : 𝓓(dirichletBallOpens n, ℝ)) (v : E n) :
    (∫ x in unitBall n, ψ x * dirichletTestDerivative φ v x ∂volume0 n) =
      -(∫ x in unitBall n, dirichletTestDerivative ψ v x * φ x ∂volume0 n) := by
  have hInt (f g : 𝓓(dirichletBallOpens n, ℝ)) : Integrable (fun x => f x * g x) := by
    exact (f.contDiff.continuous.mul g.contDiff.continuous).integrable_of_hasCompactSupport
      f.hasCompactSupport.mul_right
  have hi₁ := hInt (dirichletTestDerivative ψ v) φ
  have hi₂ := hInt ψ (dirichletTestDerivative φ v)
  simp only [dirichletTestDerivative_apply] at hi₁ hi₂
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    hi₁ hi₂ (hInt ψ φ)
    (fun x _ => ψ.contDiff.differentiable (by simp) x)
    (fun x _ => φ.contDiff.differentiable (by simp) x)
  have hL : (∫ x in unitBall n, ψ x * dirichletTestDerivative φ v x) =
      ∫ x, ψ x * dirichletTestDerivative φ v x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [test_eq_zero_off_ball ψ hx, zero_mul]
  have hR : (∫ x in unitBall n, dirichletTestDerivative ψ v x * φ x) =
      ∫ x, dirichletTestDerivative ψ v x * φ x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [test_eq_zero_off_ball φ hx, mul_zero]
  rw [setIntegral_volume0, setIntegral_volume0, hL, hR]
  simp only [dirichletTestDerivative_apply]
  rw [h, mul_neg]

/-- The gradient component in the Dirichlet closure satisfies the
distributional differentiation identity in every fixed real direction. -/
theorem dirichletSobolev_integral_weakGradient {n : ℕ} (w : DirichletSobolev n)
    (ψ : 𝓓(dirichletBallOpens n, ℝ)) (v : E n) :
    (∫ x in unitBall n, ψ x * inner ℝ v ((w : DirichletBallL2Pair n).snd x) ∂volume0 n) =
      -(∫ x in unitBall n, fderiv ℝ (ψ : E n → ℝ) x v *
        ((w : DirichletBallL2Pair n).fst x) ∂volume0 n) := by
  let μ := (volume0 n).restrict (unitBall n)
  let eval : E n →L[ℝ] ℝ := innerSL ℝ v
  let evalLp := ContinuousLinearMap.compLpL 2 μ eval
  let ψd := dirichletTestDerivative ψ v
  let L : DirichletBallL2Pair n →L[ℝ] ℝ :=
    (innerSL ℝ (dirichletTestToL2 ψ)).comp (evalLp.comp (WithLp.sndL 2 ℝ _ _))
  let R : DirichletBallL2Pair n →L[ℝ] ℝ :=
    (innerSL ℝ (dirichletTestToL2 ψd)).comp (WithLp.fstL 2 ℝ _ _)
  have hL (z : DirichletBallL2Pair n) :
      L z = ∫ x in unitBall n, ψ x * inner ℝ v (z.snd x) ∂volume0 n := by
    change inner ℝ (dirichletTestToL2 ψ) (evalLp z.snd) = _
    rw [MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    filter_upwards [dirichletTestToL2_ae ψ, eval.coeFn_compLp z.snd] with x hψ hx
    change inner ℝ (dirichletTestToL2 ψ x) (eval.compLp z.snd x) = _
    rw [hψ, hx, Real.inner_apply]
    rfl
  have hR (z : DirichletBallL2Pair n) :
      R z = ∫ x in unitBall n, ψd x * z.fst x ∂volume0 n := by
    change inner ℝ (dirichletTestToL2 ψd) z.fst = _
    rw [MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    filter_upwards [dirichletTestToL2_ae ψd] with x hx
    rw [Real.inner_apply, hx]
  let S : Set (DirichletBallL2Pair n) := {z | L z = -R z}
  have hClosed : IsClosed S := isClosed_eq L.continuous R.continuous.neg
  have hRange : ((dirichletTestL2Graph n).range : Set (DirichletBallL2Pair n)) ⊆ S := by
    rintro _ ⟨φ, rfl⟩
    change L (dirichletTestL2Graph n φ) = -R (dirichletTestL2Graph n φ)
    rw [hL, hR]
    change (∫ x in unitBall n, ψ x * inner ℝ v (dirichletTestGradientToL2 n φ x) ∂volume0 n) =
      -(∫ x in unitBall n, ψd x * dirichletTestToL2 φ x ∂volume0 n)
    have hLeft : (∫ x in unitBall n, ψ x * inner ℝ v (dirichletTestGradientToL2 n φ x) ∂volume0 n) =
        ∫ x in unitBall n, ψ x * dirichletTestDerivative φ v x ∂volume0 n := by
      apply integral_congr_ae
      filter_upwards [dirichletTestGradientToL2_ae φ] with x hx
      rw [hx, dirichletTestDerivative_apply, real_inner_comm _ v, inner_gradient_left]
    have hRight : (∫ x in unitBall n, ψd x * dirichletTestToL2 φ x ∂volume0 n) =
        ∫ x in unitBall n, ψd x * φ x ∂volume0 n := by
      apply integral_congr_ae
      filter_upwards [dirichletTestToL2_ae φ] with x hx
      rw [hx]
    rw [hLeft, hRight]
    exact dirichletTest_integral_derivative φ ψ v
  have hw : (w : DirichletBallL2Pair n) ∈ S := closure_minimal hRange hClosed w.property
  change L w = -R w at hw
  simpa only [hL, hR, ψd, dirichletTestDerivative_apply] using hw

private theorem dirichletSobolev_snd_eq_zero_of_fst_eq_zero {n : ℕ} (hn : 0 < n)
    (w : DirichletSobolev n) (hw : (w : DirichletBallL2Pair n).fst = 0) :
    (w : DirichletBallL2Pair n).snd = 0 := by
  let μ := (volume0 n).restrict (unitBall n)
  have : NeZero n := ⟨hn.ne'⟩
  have : IsProbabilityMeasure μ := volume0_restrict_isProbability n
  let g := (w : DirichletBallL2Pair n).snd
  have hg : LocallyIntegrableOn (g : E n → E n) (unitBall n) μ :=
    ((Lp.memLp g).integrable (by norm_num)).locallyIntegrable.locallyIntegrableOn (unitBall n)
  have hz : ∀ᵐ x ∂μ, x ∈ unitBall n → g x = 0 := by
    apply (show IsOpen (unitBall n) from isOpen_ball).ae_eq_zero_of_integral_contDiff_smul_eq_zero hg
    intro ψ hψ hs hsub
    let φ : 𝓓(dirichletBallOpens n, ℝ) := ⟨ψ, hψ, hs, hsub⟩
    have hInt : Integrable (fun x => ψ x • g x) μ :=
      φ.integrable_bilin (ContinuousLinearMap.lsmul ℝ ℝ) hg
    apply integral_eq_zero_of_forall_integral_inner_eq_zero ℝ _ hInt
    intro v
    simp only [real_inner_smul_right]
    have he := dirichletSobolev_integral_weakGradient w φ v
    have hRight : (∫ x in unitBall n, fderiv ℝ (φ : E n → ℝ) x v *
        ((w : DirichletBallL2Pair n).fst x) ∂volume0 n) = 0 := by
      rw [hw]
      apply integral_eq_zero_of_ae
      filter_upwards [Lp.coeFn_zero (E := ℝ) (p := 2) (μ := μ)] with x hx
      simp only [hx, Pi.zero_apply, mul_zero]
    rw [hRight, neg_zero] at he
    exact he
  apply Lp.ext
  filter_upwards [hz, ae_restrict_mem (μ := volume0 n)
    (show MeasurableSet (unitBall n) from measurableSet_ball),
    Lp.coeFn_zero (E := E n) (p := 2) (μ := μ)] with x hx hmem hzero
  exact (hx hmem).trans hzero.symm

/-- A Dirichlet graph element is determined by its scalar (L^2) component. -/
theorem dirichletSobolev_fst_injective {n : ℕ} (hn : 0 < n) :
    Function.Injective (fun w : DirichletSobolev n => (w : DirichletBallL2Pair n).fst) := by
  intro w z he
  have hf : ((w - z : DirichletSobolev n) : DirichletBallL2Pair n).fst = 0 :=
    sub_eq_zero.mpr he
  have hg := dirichletSobolev_snd_eq_zero_of_fst_eq_zero hn (w - z) hf
  apply sub_eq_zero.mp
  apply Subtype.ext
  apply (WithLp.equiv 2 (DirichletBallL2 n ℝ × DirichletBallL2 n (E n))).injective
  exact Prod.ext hf hg

end KEBall
