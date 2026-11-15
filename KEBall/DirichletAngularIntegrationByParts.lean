import KEBall.DirichletAngularEquation
import KEBall.DirichletUnitaryFieldMatrix

/-!
# Angular integration by parts without a boundary value assumption

A skew linear field is tangent to every centered sphere and has zero
divergence.  The boundary flux therefore vanishes for arbitrary C1 scalar
fields near the closed ball.  This applies to Hessian entries as well as
to functions with zero Dirichlet data.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Filter InnerProductSpace MeasureTheory Metric Set
open scoped ContDiff Topology

namespace KEBall

theorem integral_dirichlet_skew_derivative_eq_zero {n : ℕ} (hn : 0 < n)
    {U : Set (E n)} (hU : IsOpen U) (hSub : closedUnitBall n ⊆ U)
    {f : E n → ℝ} (hf : ContDiffOn ℝ 1 f U)
    (T : E n →L[ℝ] E n) (hT : star T = -T) :
    (∫ x in unitBall n, fderiv ℝ f x (T x) ∂volume0 n) = 0 := by
  let V (x : E n) := f x • T x
  have hV : ContDiffOn ℝ 1 V U := hf.smul T.contDiff.contDiffOn
  have hDiv (x : E n) (hx : x ∈ unitBall n) :
      euclideanDivergence V x = fderiv ℝ f x (T x) := by
    have h := euclideanDivergence_smul
      ((hf.contDiffAt (hU.mem_nhds (hSub (ball_subset_closedBall hx)))).differentiableAt
        (by norm_num)) T.differentiableAt
    simpa only [euclideanDivergence_skew_field T hT, mul_zero, zero_add] using h
  have hBoundary (θ : Sphere n) : inner ℝ θ.1 (V θ.1) = 0 := by
    simp only [V, inner_smul_right, inner_dirichlet_skew_field_self T hT, mul_zero]
  have h := integral_unitBall_divergence_normalized_of_contDiffOn hn hU hSub hV
  calc
    _ = ∫ x in unitBall n, euclideanDivergence V x ∂volume0 n :=
      setIntegral_congr_fun (show MeasurableSet (unitBall n) from measurableSet_ball)
        (fun x hx => (hDiv x hx).symm)
    _ = (2 * n : ℝ) * ∫ θ : Sphere n, inner ℝ θ.1 (V θ.1) ∂sphere0 n := h
    _ = 0 := by simp only [hBoundary, integral_zero, mul_zero]

theorem integral_dirichlet_skew_derivative_mul {n : ℕ} (hn : 0 < n)
    {U : Set (E n)} (hU : IsOpen U) (hSub : closedUnitBall n ⊆ U)
    {f g : E n → ℝ} (hf : ContDiffOn ℝ 1 f U) (hg : ContDiffOn ℝ 1 g U)
    (T : E n →L[ℝ] E n) (hT : star T = -T) :
    (∫ x in unitBall n, fderiv ℝ f x (T x) * g x ∂volume0 n) =
      -(∫ x in unitBall n, f x * fderiv ℝ g x (T x) ∂volume0 n) := by
  have hDf : ContinuousOn (fun x => fderiv ℝ f x (T x)) U :=
    (hf.continuousOn_fderiv_of_isOpen hU (by norm_num)).clm_apply T.continuous.continuousOn
  have hDg : ContinuousOn (fun x => fderiv ℝ g x (T x)) U :=
    (hg.continuousOn_fderiv_of_isOpen hU (by norm_num)).clm_apply T.continuous.continuousOn
  have hInt₁ : IntegrableOn (fun x => fderiv ℝ f x (T x) * g x)
      (unitBall n) (volume0 n) :=
    (((hDf.mul hg.continuousOn).mono hSub).integrableOn_compact
      (isCompact_closedBall (0 : E n) 1)).mono_set ball_subset_closedBall
  have hInt₂ : IntegrableOn (fun x => f x * fderiv ℝ g x (T x))
      (unitBall n) (volume0 n) :=
    (((hf.continuousOn.mul hDg).mono hSub).integrableOn_compact
      (isCompact_closedBall (0 : E n) 1)).mono_set ball_subset_closedBall
  have h := integral_dirichlet_skew_derivative_eq_zero hn hU hSub (hf.mul hg) T hT
  have hPoint (x : E n) (hx : x ∈ unitBall n) :
      fderiv ℝ (fun y => f y * g y) x (T x) =
        fderiv ℝ f x (T x) * g x + f x * fderiv ℝ g x (T x) := by
    have hN := hU.mem_nhds (hSub (ball_subset_closedBall hx))
    rw [fderiv_fun_mul ((hf.contDiffAt hN).differentiableAt (by norm_num))
      ((hg.contDiffAt hN).differentiableAt (by norm_num))]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  have hSum : (∫ x in unitBall n,
      fderiv ℝ f x (T x) * g x + f x * fderiv ℝ g x (T x) ∂volume0 n) = 0 := by
    calc
      _ = ∫ x in unitBall n, fderiv ℝ (fun y => f y * g y) x (T x) ∂volume0 n :=
        setIntegral_congr_fun (show MeasurableSet (unitBall n) from measurableSet_ball)
          (fun x hx => (hPoint x hx).symm)
      _ = 0 := h
  have hSeparate : (∫ x in unitBall n, fderiv ℝ f x (T x) * g x ∂volume0 n) +
      (∫ x in unitBall n, f x * fderiv ℝ g x (T x) ∂volume0 n) = 0 :=
    (integral_add hInt₁ hInt₂).symm.trans hSum
  exact eq_neg_of_add_eq_zero_left hSeparate

end KEBall
