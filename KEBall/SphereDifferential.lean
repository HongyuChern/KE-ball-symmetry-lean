import KEBall.SecondGreen
import KEBall.EulerLaplacian

/-!
# The actual horizontal differential operator

The ambient polynomial projection is tangent to every concentric sphere.
On the unit sphere it is exactly the horizontal gradient from the fixed
specification. Its actual Euclidean divergence is the trace of the ambient
Hessian minus the normal and Hopf terms, including the spherical curvature
correction. All derivatives below are Frechet derivatives.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped ContDiff Topology BigOperators RealInnerProductSpace

namespace KEBall

@[simp] theorem JCLM_coe (n : ℕ) : (JCLM n : E n → E n) = J :=
  funext fun x => JCLM_apply x

noncomputable def horizontalLaplacian {n : ℕ} (h : E n → ℝ) (x : E n) : ℝ :=
  (∑ i : Fin (2 * n), realHessian h x
      (EuclideanSpace.basisFun (Fin (2 * n)) ℝ i)
      (EuclideanSpace.basisFun (Fin (2 * n)) ℝ i)) -
    realHessian h x x x - realHessian h x (J x) (J x) -
      (2 * n - 2 : ℝ) * fderiv ℝ h x x

noncomputable def scaledHorizontalGradient {n : ℕ} (h : E n → ℝ) (x : E n) : E n :=
  ‖x‖ ^ 2 • euclideanGradient h x -
    fderiv ℝ h x x • x - fderiv ℝ h x (J x) • J x

theorem scaledHorizontalGradient_tangent {n : ℕ} (h : E n → ℝ) (x : E n) :
    inner ℝ x (scaledHorizontalGradient h x) = 0 := by
  have hg : inner ℝ x (euclideanGradient h x) = fderiv ℝ h x x := by
    rw [real_inner_comm, inner_euclideanGradient]
  simp only [scaledHorizontalGradient, inner_sub_right, real_inner_smul_right,
    hg, real_inner_self_eq_norm_sq, inner_J_self_zero, mul_zero, sub_zero]
  ring

theorem scaledHorizontalGradient_on_sphere {n : ℕ} (h : E n → ℝ)
    {x : E n} (hx : x ∈ unitSphere n) :
    scaledHorizontalGradient h x = horizontalGradient h x := by
  have hnorm : ‖x‖ = 1 := by
    simpa only [unitSphere, Metric.mem_sphere, dist_zero_right] using hx
  simp only [scaledHorizontalGradient, horizontalGradient, hnorm, one_pow, one_smul,
    inner_euclideanGradient]

theorem euclideanGradient_contDiff {n : ℕ} {h : E n → ℝ} (hh : ContDiff ℝ ∞ h) :
    ContDiff ℝ ∞ (euclideanGradient h) := by
  apply ContDiff.sum
  intro i hi
  exact (((contDiff_infty_iff_fderiv.mp hh).2).clm_apply contDiff_const).smul contDiff_const

theorem euclideanGradient_contDiffAt {n : ℕ} {h : E n → ℝ} {x : E n}
    (hh : ContDiffAt ℝ ∞ h x) : ContDiffAt ℝ ∞ (euclideanGradient h) x := by
  apply ContDiffAt.sum
  intro i hi
  exact ((hh.fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const).smul contDiffAt_const

theorem euclideanGradient_coord {n : ℕ} (h : E n → ℝ) (x : E n) (i : Fin (2 * n)) :
    euclideanGradient h x i =
      fderiv ℝ h x (EuclideanSpace.basisFun (Fin (2 * n)) ℝ i) := by
  simpa only [EuclideanSpace.inner_basisFun_real] using
    inner_euclideanGradient h x (EuclideanSpace.basisFun (Fin (2 * n)) ℝ i)

theorem euclideanDivergence_euclideanGradient {n : ℕ} {h : E n → ℝ} {x : E n}
    (hh : ContDiffAt ℝ ∞ h x) :
    euclideanDivergence (euclideanGradient h) x =
      ∑ i : Fin (2 * n), realHessian h x
        (EuclideanSpace.basisFun (Fin (2 * n)) ℝ i)
        (EuclideanSpace.basisFun (Fin (2 * n)) ℝ i) := by
  simp only [euclideanDivergence, euclideanGradient_coord]
  apply Finset.sum_congr rfl
  intro i hi
  exact fderiv_firstDerivative_apply hh _ _

theorem euclideanDivergence_J {n : ℕ} (x : E n) : euclideanDivergence J x = 0 := by
  have he (i : Fin (2 * n)) : fderiv ℝ (fun y : E n => J y i) x =
      (EuclideanSpace.proj i).comp (JCLM n) := by
    have h := (EuclideanSpace.proj i : E n →L[ℝ] ℝ).hasFDerivAt.comp x
      (JCLM n).hasFDerivAt
    simpa only [Function.comp_def, JCLM_apply, EuclideanSpace.coe_proj] using h.fderiv
  have hz (i : Fin (2 * n)) :
      ((EuclideanSpace.proj i).comp (JCLM n))
        (EuclideanSpace.basisFun (Fin (2 * n)) ℝ i) = 0 := by
    simp only [ContinuousLinearMap.comp_apply, JCLM_apply, EuclideanSpace.coe_proj]
    have hj := inner_J_self_zero (EuclideanSpace.basisFun (Fin (2 * n)) ℝ i)
    rw [real_inner_comm] at hj
    simpa only [EuclideanSpace.inner_basisFun_real] using hj
  simp only [euclideanDivergence, he, hz, Finset.sum_const_zero]

theorem fderiv_hopfDerivative {n : ℕ} {h : E n → ℝ} {x : E n}
    (hh : ContDiffAt ℝ ∞ h x) (v : E n) :
    fderiv ℝ (fun y => fderiv ℝ h y (J y)) x v =
      realHessian h x v (J x) + fderiv ℝ h x (J v) := by
  have hd := ((hh.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)).hasFDerivAt
  have ht := hd.clm_apply ((JCLM n).hasFDerivAt (x := x))
  simp only [JCLM_apply, JCLM_coe] at ht
  rw [ht.fderiv]
  simp only [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    JCLM_apply, realHessian]
  ring

theorem scaledHorizontalGradient_contDiff {n : ℕ} {h : E n → ℝ}
    (hh : ContDiff ℝ ∞ h) : ContDiff ℝ ∞ (scaledHorizontalGradient h) := by
  have hd := (contDiff_infty_iff_fderiv.mp hh).2
  have hJ : ContDiff ℝ ∞ (J (n := n)) := by
    simpa only [JCLM_coe] using (JCLM n).contDiff (n := ∞)
  exact ((contDiff_norm_sq ℝ).smul (euclideanGradient_contDiff hh)).sub
    ((hd.clm_apply contDiff_id).smul contDiff_id) |>.sub
      ((hd.clm_apply hJ).smul hJ)

theorem scaledHorizontalGradient_divergence {n : ℕ} {h : E n → ℝ} {x : E n}
    (hh : ContDiffAt ℝ ∞ h x) :
    euclideanDivergence (scaledHorizontalGradient h) x =
      ‖x‖ ^ 2 * (∑ i : Fin (2 * n), realHessian h x
        (EuclideanSpace.basisFun (Fin (2 * n)) ℝ i)
        (EuclideanSpace.basisFun (Fin (2 * n)) ℝ i)) -
      realHessian h x x x - realHessian h x (J x) (J x) -
        (2 * n - 2 : ℝ) * fderiv ℝ h x x := by
  have hd := (hh.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  have hg := (euclideanGradient_contDiffAt hh).differentiableAt (by simp)
  have hJ : DifferentiableAt ℝ (J (n := n)) x := by
    simpa only [JCLM_coe] using (JCLM n).differentiableAt (x := x)
  have hr : DifferentiableAt ℝ (eulerDerivative h) x := hd.clm_apply differentiableAt_id
  have hj : DifferentiableAt ℝ (fun y => fderiv ℝ h y (J y)) x :=
    hd.clm_apply hJ
  have hn : DifferentiableAt ℝ (fun y : E n => ‖y‖ ^ 2) x :=
    (hasStrictFDerivAt_norm_sq x).hasFDerivAt.differentiableAt
  change euclideanDivergence
    (fun y => (‖y‖ ^ 2 • euclideanGradient h y - eulerDerivative h y • y) -
      fderiv ℝ h y (J y) • J y) x = _
  rw [euclideanDivergence_sub
      (V := fun y => ‖y‖ ^ 2 • euclideanGradient h y - eulerDerivative h y • y)
      (W := fun y => fderiv ℝ h y (J y) • J y)
      ((hn.smul hg).sub (hr.smul differentiableAt_id))
      (hj.smul hJ),
    euclideanDivergence_sub
      (V := fun y => ‖y‖ ^ 2 • euclideanGradient h y)
      (W := fun y => eulerDerivative h y • y)
      (hn.smul hg) (hr.smul differentiableAt_id),
    euclideanDivergence_smul hn hg,
    euclideanDivergence_scalar_euler hr,
    euclideanDivergence_smul hj hJ,
    euclideanDivergence_euclideanGradient hh, euclideanDivergence_J,
    fderiv_eulerDerivative hh, fderiv_hopfDerivative hh]
  rw [(hasStrictFDerivAt_norm_sq x).hasFDerivAt.fderiv]
  simp only [smul_apply, smul_eq_mul, innerSL_apply_apply,
    J_sq, map_neg, eulerDerivative, mul_zero]
  have hgx : inner ℝ x (euclideanGradient h x) = fderiv ℝ h x x := by
    rw [real_inner_comm, inner_euclideanGradient]
  rw [hgx]
  ring

theorem scaledHorizontalGradient_divergence_on_sphere {n : ℕ} {h : E n → ℝ}
    {x : E n} (hh : ContDiffAt ℝ ∞ h x) (hx : x ∈ unitSphere n) :
    euclideanDivergence (scaledHorizontalGradient h) x = horizontalLaplacian h x := by
  have hnorm : ‖x‖ = 1 := by
    simpa only [unitSphere, Metric.mem_sphere, dist_zero_right] using hx
  simpa only [horizontalLaplacian, hnorm, one_pow, one_mul] using
    scaledHorizontalGradient_divergence hh

#print axioms scaledHorizontalGradient_tangent
#print axioms euclideanDivergence_J
#print axioms scaledHorizontalGradient_divergence_on_sphere

end KEBall
