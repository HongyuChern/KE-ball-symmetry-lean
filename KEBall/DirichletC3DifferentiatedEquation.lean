import KEBall.DirichletBoundedBilinear
import KEBall.DirichletComplexHessianHolder

/-!
# Differentiating the actual equation at C3 regularity

The Hessian of a directional derivative equals the directional derivative
of the Hessian by the finite-order Schwarz theorem.  No smoothness premise
is used to justify the first step of the regularity bootstrap.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Filter Matrix Metric Set
open scoped ContDiff Matrix.Norms.Elementwise Topology

namespace KEBall

open KEBallProbe

theorem dirichlet_hessian_directionalDerivative_of_C3 {n : ℕ} {u : E n → ℝ} {x : E n}
    (hu : ContDiffAt ℝ 3 u x) (v : E n) :
    fderiv ℝ (fderiv ℝ (fun y => fderiv ℝ u y v)) x =
      fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x v := by
  let H := fderiv ℝ (fderiv ℝ u)
  have hFirst : fderiv ℝ (fun y => fderiv ℝ u y v) =ᶠ[𝓝 x] fun y => H y v := by
    filter_upwards [hu.eventually (by simp)] with y hy
    have hD : HasFDerivAt (fderiv ℝ u) (H y) y :=
      ((hy.fderiv_right (m := 2) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
    have hE := (ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt.comp y hD
    change HasFDerivAt (fun z => fderiv ℝ u z v) _ y at hE
    rw [hE.fderiv]
    ext z
    change H y z v = H y v z
    exact (hy.isSymmSndFDerivAt (by norm_num)).eq z v
  have hDu : ContDiffAt ℝ 2 (fderiv ℝ u) x := hu.fderiv_right (by norm_num)
  have hH : HasFDerivAt H (fderiv ℝ H x) x :=
    ((hDu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hE := (ContinuousLinearMap.apply ℝ (E n →L[ℝ] ℝ) v).hasFDerivAt.comp x hH
  change HasFDerivAt (fun y => H y v) _ x at hE
  rw [hFirst.fderiv_eq, hE.fderiv]
  ext a b
  change fderiv ℝ H x a v b = fderiv ℝ H x v a b
  exact congrArg (fun L : E n →L[ℝ] ℝ => L b)
    ((hDu.isSymmSndFDerivAt (by norm_num)).eq a v)

theorem dirichlet_linear_directional_equation_of_C3 {n : ℕ}
    {u f : E n → ℝ} {A : E n → E n →L[ℝ] E n} {x : E n}
    (hu : ContDiffAt ℝ 3 u x) (hA : DifferentiableAt ℝ A x)
    (hEq : (fun y => dirichletContractionCLM n (A y) (fderiv ℝ (fderiv ℝ u) y)) =ᶠ[𝓝 x] f)
    (v : E n) :
    dirichletContractionCLM n (A x) (fderiv ℝ (fderiv ℝ (fun y => fderiv ℝ u y v)) x) =
      fderiv ℝ f x v -
        dirichletContractionCLM n (fderiv ℝ A x v) (fderiv ℝ (fderiv ℝ u) x) := by
  let H := fderiv ℝ (fderiv ℝ u)
  have hH : HasFDerivAt H (fderiv ℝ H x) x :=
    (((hu.fderiv_right (m := 2) (by norm_num)).fderiv_right (m := 1)
      (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hL := (dirichletContractionCLM n).hasFDerivAt.comp x hA.hasFDerivAt
  have hP := hL.clm_apply hH
  change HasFDerivAt (fun y => dirichletContractionCLM n (A y) (fderiv ℝ (fderiv ℝ u) y)) _ x at hP
  rw [dirichlet_hessian_directionalDerivative_of_C3 hu v, ← hEq.fderiv_eq, hP.fderiv]
  simp only [_root_.add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply, Function.comp_apply]
  ring

theorem dirichlet_cofactor_directional_equation_of_C3 {n : ℕ}
    {u f : E n → ℝ} {x : E n} (hu : ContDiffAt ℝ 3 u x)
    (hEq : (fun y => (complexHessian u y).det.re) =ᶠ[𝓝 x] f) (v : E n) :
    dirichletContractionCLM n (dirichletCofactorOfMatrix (complexHessian u x))
      (fderiv ℝ (fderiv ℝ (fun y => fderiv ℝ u y v)) x) = fderiv ℝ f x v := by
  let H := fderiv ℝ (fderiv ℝ u)
  let C := @dirichletComplexHessianCLM n
  have hH : HasFDerivAt H (fderiv ℝ H x) x :=
    (((hu.fderiv_right (m := 2) (by norm_num)).fderiv_right (m := 1)
      (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hCH : complexHessian u =ᶠ[𝓝 x] C ∘ H := by
    filter_upwards [hu.eventually (by simp)] with y hy
    exact (complexHessianOfRealBilinear_eq (hy.of_le (by norm_num))).symm
  have hDet := (complex_det_differentiableAt (C (H x))).hasFDerivAt.comp x
    (C.hasFDerivAt.comp x hH)
  have hF := Complex.reCLM.hasFDerivAt.comp x hDet
  change HasFDerivAt (fun y => (C (H y)).det.re) _ x at hF
  have hEq' : (fun y => (C (H y)).det.re) =ᶠ[𝓝 x] f := by
    filter_upwards [hCH, hEq] with y hy hfy
    change complexHessian u y = C (H y) at hy
    rwa [← hy]
  rw [dirichlet_hessian_directionalDerivative_of_C3 hu v,
    dirichletContractionCLM_apply, dirichletBilinearContraction_cofactor,
    hCH.self_of_nhds, ← hEq'.fderiv_eq, hF.fderiv]
  simp only [ContinuousLinearMap.comp_apply, Function.comp_apply, fderiv_real_complex_det]
  rfl

end KEBall
