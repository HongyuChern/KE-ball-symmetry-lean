import KEBall.RealHessian
import PoincareLib.Geometry.Riemannian.Connection.Euclidean

/-! Constant-frame connection identities derived from the actual Hessian
metric and the retained Koszul formula. -/

set_option autoImplicit false
set_option maxSynthPendingDepth 10
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped ContDiff Manifold Topology

namespace KEBall

noncomputable def realThirdDerivative {n : ℕ} (u : E n → ℝ) (x : E n) :
    E n →L[ℝ] E n →L[ℝ] E n →L[ℝ] ℝ := fderiv ℝ (realHessian u) x

theorem realHessian_contDiffAt {n : ℕ} {u : E n → ℝ} {x : E n}
    (hu : ContDiffAt ℝ ∞ u x) : ContDiffAt ℝ ∞ (realHessian u) x :=
  (hu.fderiv_right (m := ∞) (by simp)).fderiv_right (m := ∞) (by simp)

theorem fderiv_realHessian_apply {n : ℕ} {u : E n → ℝ} {x : E n}
    (hu : ContDiffAt ℝ ∞ u x) (a v w : E n) :
    fderiv ℝ (fun y => realHessian u y v w) x a = realThirdDerivative u x a v w := by
  have hd := ((realHessian_contDiffAt hu).differentiableAt (by simp)).hasFDerivAt
  have h := (hd.clm_apply (hasFDerivAt_const v x)).clm_apply (hasFDerivAt_const w x)
  rw [h.fderiv]
  simp [realThirdDerivative]

theorem realThirdDerivative_symm12 {n : ℕ} {u : E n → ℝ} {x : E n}
    (hu : ContDiffAt ℝ ∞ u x) (a b c : E n) :
    realThirdDerivative u x a b c = realThirdDerivative u x b a c := by
  have hs := ((hu.fderiv_right (m := ∞) (by simp)).isSymmSndFDerivAt
    (by simp; norm_cast)).eq a b
  exact congrArg (fun L : E n →L[ℝ] ℝ => L c) hs

theorem realThirdDerivative_symm23 {n : ℕ} {u : E n → ℝ} {U : Set (E n)}
    (hU : IsOpen U) (hu : ContDiffOn ℝ ∞ u U) {x : E n} (hx : x ∈ U)
    (a b c : E n) :
    realThirdDerivative u x a b c = realThirdDerivative u x a c b := by
  have huAt := hu.contDiffAt (hU.mem_nhds hx)
  have heq : (fun y => realHessian u y b c) =ᶠ[𝓝 x]
      (fun y => realHessian u y c b) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact realHessian_symm (hu.contDiffAt (hU.mem_nhds hy)) b c
  rw [← fderiv_realHessian_apply huAt, heq.fderiv_eq, fderiv_realHessian_apply huAt]

theorem fderiv_realMetricForm {n : ℕ} {u : E n → ℝ} {U : Set (E n)}
    (hU : IsOpen U) (hu : ContDiffOn ℝ ∞ u U) {x : E n} (hx : x ∈ U)
    (a v w : E n) :
    fderiv ℝ (fun y => realMetricForm u y v w) x a =
      (realThirdDerivative u x a v w + realThirdDerivative u x a (J v) (J w)) / 2 := by
  have huAt := hu.contDiffAt (hU.mem_nhds hx)
  have heq : (fun y => realMetricForm u y v w) =ᶠ[𝓝 x]
      (fun y => (2 : ℝ)⁻¹ *
        (realHessian u y v w + realHessian u y (J v) (J w))) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    rw [realMetricForm_eq_average_hessian (hu.contDiffAt (hU.mem_nhds hy))]
    ring
  have hb (v w : E n) : DifferentiableAt ℝ (fun y => realHessian u y v w) x :=
    (((realHessian_contDiffAt huAt).clm_apply contDiffAt_const).clm_apply
      contDiffAt_const).differentiableAt (by simp)
  have hsum : DifferentiableAt ℝ
      (fun y => realHessian u y v w + realHessian u y (J v) (J w)) x :=
    (hb v w).add (hb (J v) (J w))
  rw [heq.fderiv_eq, fderiv_const_mul hsum,
    fderiv_fun_add (hb v w) (hb (J v) (J w))]
  simp only [smul_apply, smul_eq_mul, add_apply, fderiv_realHessian_apply huAt]
  ring

/-- This is the vanishing of the mixed complex Christoffel part, obtained
from the upstream Koszul identity for the actual selected connection. -/
theorem connection_J_pair_eq_zero {n : ℕ}
    {g : PoincareMT.RiemannianMetric (2 * n) (E n)}
    (D : PoincareMT.LeviCivitaData g) {u : E n → ℝ} {U : Set (E n)}
    (hU : IsOpen U) (hu : ContDiffOn ℝ ∞ u U)
    (hg : ∀ y ∈ U, ∀ v w : E n, g.inner y v w = realMetricForm u y v w)
    {x : E n} (hx : x ∈ U) (v w : E n) :
    D.connection (fun _ : E n => w) x v +
      D.connection (fun _ : E n => J w) x (J v) = 0 := by
  have huAt := hu.contDiffAt (hU.mem_nhds hx)
  have hd (a b c : E n) :
      fderiv ℝ (fun y => g.inner y b c) x a =
        (realThirdDerivative u x a b c + realThirdDerivative u x a (J b) (J c)) / 2 := by
    have heq : (fun y => g.inner y b c) =ᶠ[𝓝 x] (fun y => realMetricForm u y b c) := by
      filter_upwards [hU.mem_nhds hx] with y hy
      exact hg y hy b c
    rw [heq.fderiv_eq]
    exact fderiv_realMetricForm hU hu hx a b c
  apply (g.inner_isInvertible x).injective
  ext z
  simp only [map_add, add_apply, map_zero, zero_apply]
  have h1 := D.inner_connection_const x v w z
  have h2 := D.inner_connection_const x (J v) (J w) z
  simp only [hd] at h1 h2
  simp only [J_sq, map_neg, neg_apply] at h2
  simp only [realThirdDerivative_symm12 huAt, realThirdDerivative_symm23 hU hu hx] at h1 h2
  linarith

end KEBall
