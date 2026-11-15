import KEBall.DirichletLinearHolderBootstrap
import KEBall.DirichletNonlinearHolderGain

/-!
# All-order interior regularity for the positive determinant equation

The source hypothesis is a preservation property for actual local jets.
It is discharged below for a smooth density and for an exponential of the
potential.  The first C2,alpha jet is an explicit premise of these local
regularity theorems; no weak solution is silently assumed to have it.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Filter Matrix Metric Set
open scoped ComplexOrder ContDiff Matrix.Norms.Elementwise NNReal Topology

namespace KEBall

theorem hasDirichletHolderAt_all_of_positive_determinant {n : ℕ} (hn : 0 < n)
    {S : Set (E n)} (hS : IsOpen S) {p : E n} (hp : p ∈ S)
    {u f : E n → ℝ} {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1)
    (hu : HasDirichletHolderAt 2 α u p)
    (hPos : ∀ x ∈ S, (complexHessian u x).PosDef)
    (hEq : ∀ x ∈ S, (complexHessian u x).det.re = f x)
    (hSource : ∀ k : ℕ, HasDirichletHolderAt k α u p → HasDirichletHolderAt k α f p) :
    ∀ k : ℕ, HasDirichletHolderAt k α u p := by
  have hu3 := hasDirichletHolderAt_three_of_positive_determinant hn hS hp hα hα1 hu
    (hSource 2 hu) hPos hEq
  let A (x : E n) := dirichletCofactorOfMatrix (complexHessian u x)
  obtain ⟨hAP, l, hl, hEll⟩ := exists_dirichlet_point_cofactor_ellipticity hn (hPos p hp)
  have hInd : ∀ j : ℕ, HasDirichletHolderAt (j + 3) α u p := by
    intro j
    induction j with
    | zero => exact hu3
    | succ j hj =>
        have hA : HasDirichletHolderAt (j + 1) α A p :=
          hasDirichletHolderAt_cofactor_of_hessian hα hα1.le hj
        have hf : HasDirichletHolderAt (j + 3) α f p := hSource (j + 3) hj
        have hDir (v : E n) : HasDirichletHolderAt (j + 3) α (fun x => fderiv ℝ u x v) p := by
          have hv : HasDirichletHolderAt 2 α (fun x => fderiv ℝ u x v) p :=
            (hj.derivative.of_order_le (by omega) hα1.le).clm hα hα1.le
              (ContinuousLinearMap.apply ℝ ℝ v)
          have hfv : HasDirichletHolderAt (j + 1) α (fun x => fderiv ℝ f x v) p :=
            (hf.derivative.of_order_le (by omega) hα1.le).clm hα hα1.le
              (ContinuousLinearMap.apply ℝ ℝ v)
          have hNear : ∀ᶠ x in 𝓝 p,
              dirichletContractionCLM n (A x)
                (fderiv ℝ (fderiv ℝ (fun y => fderiv ℝ u y v)) x) = fderiv ℝ f x v := by
            filter_upwards [hu3.contDiffAt.eventually (by simp), hS.mem_nhds hp] with x hux hxS
            apply dirichlet_cofactor_directional_equation_of_C3 hux
            filter_upwards [hS.mem_nhds hxS] with y hy
            exact hEq y hy
          obtain ⟨ρ, hρ, hPDE⟩ := Metric.mem_nhds_iff.mp hNear
          exact hasDirichletHolderAt_of_linear_elliptic_equation hn hα hα1 (j + 1)
            isOpen_ball (mem_ball_self hρ) hv hfv hA hAP hl hEll (fun x hx => hPDE hx)
        obtain ⟨R, hR, huC, K, huH⟩ := hj
        exact HasDirichletHolderAt.of_directions hR (huC.of_le (by norm_cast; omega))
          (fun i => hDir (EuclideanSpace.basisFun (Fin (2 * n)) ℝ i))
  intro k
  exact (hInd k).of_order_le (by omega) hα1.le

theorem contDiffAt_infty_of_positive_determinant_and_holder_source {n : ℕ} (hn : 0 < n)
    {S : Set (E n)} (hS : IsOpen S) {p : E n} (hp : p ∈ S)
    {u f : E n → ℝ} {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1)
    (hu : HasDirichletHolderAt 2 α u p)
    (hPos : ∀ x ∈ S, (complexHessian u x).PosDef)
    (hEq : ∀ x ∈ S, (complexHessian u x).det.re = f x)
    (hSource : ∀ k : ℕ, HasDirichletHolderAt k α u p → HasDirichletHolderAt k α f p) :
    ContDiffAt ℝ ∞ u p := by
  apply contDiffAt_infty.mpr
  intro k
  exact (hasDirichletHolderAt_all_of_positive_determinant hn hS hp hα hα1 hu hPos hEq hSource k).contDiffAt

theorem contDiffAt_infty_of_positive_determinant_smooth_density {n : ℕ} (hn : 0 < n)
    {S : Set (E n)} (hS : IsOpen S) {p : E n} (hp : p ∈ S)
    {u f : E n → ℝ} {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1)
    (hu : HasDirichletHolderAt 2 α u p) (hf : ContDiffAt ℝ ∞ f p)
    (hPos : ∀ x ∈ S, (complexHessian u x).PosDef)
    (hEq : ∀ x ∈ S, (complexHessian u x).det.re = f x) :
    ContDiffAt ℝ ∞ u p := by
  apply contDiffAt_infty_of_positive_determinant_and_holder_source hn hS hp hα hα1 hu hPos hEq
  intro k _
  exact hasDirichletHolderAt_of_contDiffAt_succ
    (hf.of_le (WithTop.coe_le_coe.mpr le_top)) hα1.le

theorem contDiffAt_infty_of_positive_determinant_exponential {n : ℕ} (hn : 0 < n)
    {S : Set (E n)} (hS : IsOpen S) {p : E n} (hp : p ∈ S)
    {u : E n → ℝ} {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1)
    (hu : HasDirichletHolderAt 2 α u p) (c a : ℝ)
    (hPos : ∀ x ∈ S, (complexHessian u x).PosDef)
    (hEq : ∀ x ∈ S, (complexHessian u x).det.re = c * Real.exp (a * u x)) :
    ContDiffAt ℝ ∞ u p := by
  apply contDiffAt_infty_of_positive_determinant_and_holder_source hn hS hp hα hα1 hu hPos hEq
  intro k huk
  exact huk.comp_smooth hα hα1.le (contDiff_const.mul (contDiff_const.mul contDiff_id).exp)

end KEBall
