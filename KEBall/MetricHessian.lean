import KEBall.MetricConnection
import PoincareLib.Geometry.Riemannian.ScalarOperators.Hessian.Coordinates

/-! The actual covariant Hessian and the complex structure of the potential
metric. The Christoffel cancellation is derived from the selected Levi-Civita
connection; it is not an extra geometric assumption. -/

set_option autoImplicit false
set_option maxSynthPendingDepth 10
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped ContDiff Manifold Topology

namespace KEBall

theorem realMetricForm_J_J {n : ℕ} {u : E n → ℝ} {x : E n}
    (hu : ContDiffAt ℝ ∞ u x) (v w : E n) :
    realMetricForm u x (J v) (J w) = realMetricForm u x v w := by
  rw [realMetricForm_eq_average_hessian hu, realMetricForm_eq_average_hessian hu]
  simp only [J_sq, map_neg, neg_apply, neg_neg]
  ring

theorem realMetricForm_J_skew {n : ℕ} {u : E n → ℝ} {x : E n}
    (hu : ContDiffAt ℝ ∞ u x) (v w : E n) :
    realMetricForm u x (J v) w = -realMetricForm u x v (J w) := by
  have h := realMetricForm_J_J hu v (J w)
  rw [J_sq, realMetricForm_eq, map_neg] at h
  rw [realMetricForm_eq] at ⊢
  linarith

theorem hessian_eq_realHessian_sub_connection {n : ℕ}
    {g : PoincareMT.RiemannianMetric (2 * n) (E n)}
    (D : PoincareMT.LeviCivitaData g) {h : E n → ℝ} {x : E n}
    (hh : ContDiffAt ℝ ∞ h x) (v w : E n) :
    D.hessian h x v w = realHessian h x v w -
      fderiv ℝ h x (D.connection (fun _ : E n => w) x v) := by
  rw [D.hessian_eq_fderiv_sub_christoffel hh, D.connection_const_eq_inverse]
  rfl

theorem hessian_J_pair {n : ℕ}
    {g : PoincareMT.RiemannianMetric (2 * n) (E n)}
    (D : PoincareMT.LeviCivitaData g) {u h : E n → ℝ} {U : Set (E n)}
    (hU : IsOpen U) (hu : ContDiffOn ℝ ∞ u U)
    (hg : ∀ y ∈ U, ∀ v w : E n, g.inner y v w = realMetricForm u y v w)
    {x : E n} (hx : x ∈ U) (hh : ContDiffAt ℝ ∞ h x) (v w : E n) :
    D.hessian h x v w + D.hessian h x (J v) (J w) =
      realHessian h x v w + realHessian h x (J v) (J w) := by
  rw [hessian_eq_realHessian_sub_connection D hh,
    hessian_eq_realHessian_sub_connection D hh]
  have hz := congrArg (fderiv ℝ h x) (connection_J_pair_eq_zero D hU hu hg hx v w)
  simp only [map_add, map_zero] at hz
  linarith

theorem hessian_J_pair_eq_twice_realMetricForm {n : ℕ}
    {g : PoincareMT.RiemannianMetric (2 * n) (E n)}
    (D : PoincareMT.LeviCivitaData g) {u h : E n → ℝ} {U : Set (E n)}
    (hU : IsOpen U) (hu : ContDiffOn ℝ ∞ u U)
    (hg : ∀ y ∈ U, ∀ v w : E n, g.inner y v w = realMetricForm u y v w)
    {x : E n} (hx : x ∈ U) (hh : ContDiffAt ℝ ∞ h x) (v w : E n) :
    D.hessian h x v w + D.hessian h x (J v) (J w) =
      2 * realMetricForm h x v w := by
  rw [hessian_J_pair D hU hu hg hx hh, realMetricForm_eq_average_hessian hh]
  ring

theorem potential_hessian_J_pair {n : ℕ}
    {g : PoincareMT.RiemannianMetric (2 * n) (E n)}
    (D : PoincareMT.LeviCivitaData g) {u : E n → ℝ} {U : Set (E n)}
    (hU : IsOpen U) (hu : ContDiffOn ℝ ∞ u U)
    (hg : ∀ y ∈ U, ∀ v w : E n, g.inner y v w = realMetricForm u y v w)
    {x : E n} (hx : x ∈ U) (v w : E n) :
    D.hessian u x v w + D.hessian u x (J v) (J w) = 2 * g.inner x v w := by
  rw [hessian_J_pair_eq_twice_realMetricForm D hU hu hg hx
    (hu.contDiffAt (hU.mem_nhds hx)), hg x hx]

end KEBall
