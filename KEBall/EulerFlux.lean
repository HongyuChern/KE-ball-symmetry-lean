import KEBall.ComplexFlux
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# The Euler-field flux identity in Lemma 2.1

The vector field is the actual field `μ exp(-u(x)) x`. Its divergence is
computed from Frechet derivatives, and the nonzero sphere flux is evaluated
using the original boundary condition. No scaling variation is assumed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped ContDiff Topology BigOperators

namespace KEBall

noncomputable def eulerDerivative {n : ℕ} (u : E n → ℝ) (x : E n) : ℝ :=
  fderiv ℝ u x x

noncomputable def equationDensity {n : ℕ} (μ : ℝ) (u : E n → ℝ) (x : E n) : ℝ :=
  μ * Real.exp (-u x)

theorem euclideanDivergence_scalar_euler {n : ℕ} {f : E n → ℝ} {x : E n}
    (hf : DifferentiableAt ℝ f x) :
    euclideanDivergence (fun y => f y • y) x =
      (2 * n : ℝ) * f x + fderiv ℝ f x x := by
  have hcoord (i : Fin (2 * n)) :
      fderiv ℝ (fun y : E n => (f y • y) i) x
        (EuclideanSpace.basisFun (Fin (2 * n)) ℝ i) =
      f x + x i * fderiv ℝ f x (EuclideanSpace.basisFun (Fin (2 * n)) ℝ i) := by
    change fderiv ℝ (fun y : E n => f y * y i) x _ = _
    have hi : fderiv ℝ (fun y : E n => y i) x = EuclideanSpace.proj i :=
      (EuclideanSpace.proj i : E n →L[ℝ] ℝ).hasFDerivAt.fderiv
    have hdi : DifferentiableAt ℝ (fun y : E n => y i) x :=
      (EuclideanSpace.proj i : E n →L[ℝ] ℝ).differentiableAt
    rw [fderiv_fun_mul hf hdi, hi]
    simp [EuclideanSpace.basisFun_apply]
  have hrepr : (∑ i : Fin (2 * n),
      x i • EuclideanSpace.basisFun (Fin (2 * n)) ℝ i) = x := by
    simpa only [EuclideanSpace.basisFun_repr] using
      (EuclideanSpace.basisFun (Fin (2 * n)) ℝ).sum_repr x
  have hsum : (∑ i : Fin (2 * n),
      x i * fderiv ℝ f x (EuclideanSpace.basisFun (Fin (2 * n)) ℝ i)) =
      fderiv ℝ f x x := by
    simpa only [map_sum, map_smul, smul_eq_mul] using congrArg (fderiv ℝ f x) hrepr
  simp only [euclideanDivergence, hcoord, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hsum, Nat.cast_mul, Nat.cast_ofNat]

theorem equationDensity_contDiffOn {n : ℕ} {u : E n → ℝ} {U : Set (E n)}
    (μ : ℝ) (hu : ContDiffOn ℝ ∞ u U) :
    ContDiffOn ℝ ∞ (equationDensity μ u) U :=
  contDiffOn_const.mul (Real.contDiff_exp.comp_contDiffOn hu.neg)

theorem eulerDerivative_equationDensity {n : ℕ} {u : E n → ℝ} {x : E n}
    (μ : ℝ) (hu : DifferentiableAt ℝ u x) :
    fderiv ℝ (equationDensity μ u) x x =
      - (eulerDerivative u x * equationDensity μ u x) := by
  have h := (hu.hasFDerivAt.neg.exp).const_mul μ
  change HasFDerivAt (equationDensity μ u) _ x at h
  rw [h.fderiv]
  simp only [smul_apply, smul_eq_mul, neg_apply, Pi.neg_apply, equationDensity, eulerDerivative]
  ring

theorem IsSolution.eulerFlux_density {n : ℕ} (hn : 0 < n) {μ : ℝ} {u : E n → ℝ}
    (hu : IsSolution n μ u) :
    (∫ x in unitBall n, eulerDerivative u x * equationDensity μ u x ∂volume0 n) =
      (2 * n : ℝ) * ((∫ x in unitBall n, equationDensity μ u x ∂volume0 n) - μ) := by
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  obtain ⟨U, hU, hKU, huU⟩ := hu.2.1
  have hwU := equationDensity_contDiffOn μ huU
  have hRU : ContDiffOn ℝ ∞ (eulerDerivative u) U :=
    (huU.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_id
  have hw : IntegrableOn (equationDensity μ u) (unitBall n) (volume0 n) := by
    have h := (hwU.continuousOn.mono hKU).integrableOn_compact
      (μ := (volume : Measure (E n))) (isCompact_closedBall (0 : E n) 1)
    have hb := h.mono_set (Metric.ball_subset_closedBall : unitBall n ⊆ closedUnitBall n)
    change Integrable (equationDensity μ u) ((volume0 n).restrict (unitBall n))
    rw [volume0, Measure.restrict_smul]
    exact hb.smul_measure ENNReal.ofReal_ne_top
  have hRw : IntegrableOn (fun x => eulerDerivative u x * equationDensity μ u x)
      (unitBall n) (volume0 n) := by
    have h := ((hRU.mul hwU).continuousOn.mono hKU).integrableOn_compact
      (μ := (volume : Measure (E n))) (isCompact_closedBall (0 : E n) 1)
    have hb := h.mono_set (Metric.ball_subset_closedBall : unitBall n ⊆ closedUnitBall n)
    change Integrable _ ((volume0 n).restrict (unitBall n))
    rw [volume0, Measure.restrict_smul]
    exact hb.smul_measure ENNReal.ofReal_ne_top
  have hV : ContDiffOn ℝ 1 (fun x : E n => equationDensity μ u x • x) U :=
    (hwU.smul contDiffOn_id).of_le (by simp)
  have hGreen := integral_unitBall_divergence_normalized_of_contDiffOn hn hU hKU hV
  have hvol :
      (∫ x in unitBall n, euclideanDivergence (fun y => equationDensity μ u y • y) x ∂volume0 n) =
      (2 * n : ℝ) * (∫ x in unitBall n, equationDensity μ u x ∂volume0 n) -
        ∫ x in unitBall n, eulerDerivative u x * equationDensity μ u x ∂volume0 n := by
    calc
      _ = ∫ x in unitBall n,
          ((2 * n : ℝ) * equationDensity μ u x -
            eulerDerivative u x * equationDensity μ u x) ∂volume0 n := by
        apply setIntegral_congr_fun Metric.isOpen_ball.measurableSet
        intro x hx
        have hxU : x ∈ U := hKU (Metric.ball_subset_closedBall hx)
        rw [euclideanDivergence_scalar_euler
          ((hwU.contDiffAt (hU.mem_nhds hxU)).differentiableAt (by simp)),
          eulerDerivative_equationDensity μ
            ((huU.contDiffAt (hU.mem_nhds hxU)).differentiableAt (by simp))]
        rfl
      _ = _ := by rw [integral_sub (hw.const_mul _) hRw, integral_const_mul]
  have hsurf :
      (∫ θ : Sphere n, inner ℝ θ.1 (equationDensity μ u θ.1 • θ.1) ∂sphere0 n) = μ := by
    have hpoint (θ : Sphere n) : inner ℝ θ.1 (equationDensity μ u θ.1 • θ.1) = μ := by
      have hnorm : ‖θ.1‖ = 1 := by
        simpa only [unitSphere, Metric.mem_sphere, dist_zero_right] using θ.2
      rw [real_inner_smul_right, real_inner_self_eq_norm_sq, hnorm, one_pow, mul_one,
        equationDensity, hu.2.2.2.2 θ.1 θ.2]
      simp
    rw [integral_congr_ae (Eventually.of_forall hpoint)]
    simp
  rw [hvol, hsurf] at hGreen
  linarith

/-- The exact determinant-weighted Euler identity used in the manuscript's
Pohozaev argument. The coefficient and all boundary data come from `IsSolution`. -/
theorem IsSolution.eulerFlux {n : ℕ} (hn : 0 < n) {μ : ℝ} {u : E n → ℝ}
    (hu : IsSolution n μ u) :
    (∫ x in unitBall n, eulerDerivative u x * (complexHessian u x).det.re ∂volume0 n) =
      (2 * n : ℝ) * ((∫ x in unitBall n, (complexHessian u x).det.re ∂volume0 n) - μ) := by
  have heq (x : E n) (hx : x ∈ unitBall n) :
      (complexHessian u x).det.re = equationDensity μ u x := by
    rw [hu.2.2.2.1 x hx]
    simp only [equationDensity, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
  have hdet : (∫ x in unitBall n, (complexHessian u x).det.re ∂volume0 n) =
      ∫ x in unitBall n, equationDensity μ u x ∂volume0 n :=
    setIntegral_congr_fun Metric.isOpen_ball.measurableSet heq
  have hweighted :
      (∫ x in unitBall n, eulerDerivative u x * (complexHessian u x).det.re ∂volume0 n) =
      ∫ x in unitBall n, eulerDerivative u x * equationDensity μ u x ∂volume0 n :=
    setIntegral_congr_fun Metric.isOpen_ball.measurableSet
      (fun x hx => congrArg (fun z => eulerDerivative u x * z) (heq x hx))
  rw [hdet, hweighted]
  exact hu.eulerFlux_density hn

#print axioms euclideanDivergence_scalar_euler
#print axioms eulerDerivative_equationDensity
#print axioms IsSolution.eulerFlux_density
#print axioms IsSolution.eulerFlux

end KEBall
