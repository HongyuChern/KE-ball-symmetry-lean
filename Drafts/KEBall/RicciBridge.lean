import Drafts.KEBall.LoweredConnectionDerivative
import Drafts.KEBall.RicciContractionAlgebra
import Drafts.KEBall.MetricFrameMoments

/-!
# Retained real Ricci from actual constant-frame connection derivatives

Stage04 DRAFT; no kernel receipt. Uses the pinned upstream curvature formula
and its exact Ricci slot convention. No Chern-Ricci formula is postulated.
The pointwise real orthonormal basis is kept fixed during differentiation.
-/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped ContDiff Manifold Topology BigOperators

namespace KEBall
open KEBallProbe

/-- Upstream retained curvature in complex coordinates, including both
quadratic connection terms and both derivative terms. -/
theorem retained_curvature_complex_coordinates {n : ℕ}
    {g : PoincareMT.RiemannianMetric (2 * n) (E n)}
    (D : PoincareMT.LeviCivitaData g) {u : E n → ℝ} {U : Set (E n)}
    (hU : IsOpen U) (hu : ContDiffOn ℝ ∞ u U)
    (hg : ∀ y ∈ U, ∀ v w : E n, g.inner y v w = realMetricForm u y v w)
    {x : E n} (hx : x ∈ U) (v w z : E n) (k : Fin n) :
    complexCoord (D.curvature x v w z) k =
      CurvatureCoordinateAlgebra.curvature (complexConnectionCoeff D x)
        (fun j i l k => partialZ j (fun y => complexConnectionCoeff D y i l k) x)
        (fun j i l k => partialBar j (fun y => complexConnectionCoeff D y i l k) x)
        (complexCoord v) (complexCoord w) (complexCoord z) k := by
  let A := complexConnectionCoeff D x
  let P := fun j i l k => partialZ j (fun y => complexConnectionCoeff D y i l k) x
  let Q := fun j i l k => partialBar j (fun y => complexConnectionCoeff D y i l k) x
  have hc (a b : E n) (l : Fin n) :
      complexCoord (D.euclideanConnection a b x) l =
        CurvatureCoordinateAlgebra.conn A (complexCoord a) (complexCoord b) l :=
    euclideanConnection_complex_coordinates D hU hu hg hx a b l
  have hd (a b c : E n) (l : Fin n) :
      complexCoord (fderiv ℝ (D.euclideanConnection b c) x a) l =
        CurvatureCoordinateAlgebra.dconn P Q
          (complexCoord a) (complexCoord b) (complexCoord c) l := by
    rw [rd_euclideanConnection_coordinates D hU hu hg hx]
    simp_rw [rd_eq_full_wirtinger]
    rfl
  have hn (a b c : E n) (l : Fin n) :
      complexCoord (D.euclideanConnection a (D.euclideanConnection b c x) x) l =
        CurvatureCoordinateAlgebra.conn A (complexCoord a)
          (CurvatureCoordinateAlgebra.conn A (complexCoord b) (complexCoord c)) l := by
    rw [hc]
    have he : complexCoord (D.euclideanConnection b c x) =
        CurvatureCoordinateAlgebra.conn A (complexCoord b) (complexCoord c) := by
      funext r
      exact hc b c r
    rw [he]
  rw [D.curvature_eq_euclideanConnection]
  change (complexCoordCLM k) (_ + _ - (_ + _)) = _
  simp only [map_sub, map_add, complexCoordCLM_apply]
  rw [hd, hd, hn, hn]
  rfl

/-- Trace the two actual real frame slots before pairing with the metric. -/
theorem retained_curvature_frame_sum {n : ℕ}
    {g : PoincareMT.RiemannianMetric (2 * n) (E n)}
    (D : PoincareMT.LeviCivitaData g) {u : E n → ℝ} {U : Set (E n)}
    (hU : IsOpen U) (hu : ContDiffOn ℝ ∞ u U)
    (hg : ∀ y ∈ U, ∀ v w : E n, g.inner y v w = realMetricForm u y v w)
    {x : E n} (hx : x ∈ U) (hdet : IsUnit (complexHessian u x).det)
    (v : E n) (k : Fin n) :
    (∑ a, complexCoord (D.curvature x v
      (g.orthonormalBasis x a) (g.orthonormalBasis x a)) k) =
      -(∑ i : Fin n, ∑ l : Fin n, ∑ j : Fin n,
        partialBar j (fun y => complexConnectionCoeff D y i l k) x *
          complexCoord v i * inverseCoefficient u x l j) := by
  classical
  have huAt := hu.contDiffAt (hU.mem_nhds hx)
  simp_rw [retained_curvature_complex_coordinates D hU hu hg hx]
  exact CurvatureCoordinateAlgebra.curvature_frame_trace
    (fun a => complexCoord (g.orthonormalBasis x a)) (inverseCoefficient u x)
    (metric_frame_holomorphic_moment huAt hdet (hg x hx))
    (metric_frame_complex_moment huAt hdet (hg x hx)) _ _ _ _ _

/-- Actual retained Ricci equals the realification of minus the derivative
of the actual connection trace. No PDE has been used in this theorem. -/
theorem retained_ricci_eq_connection_trace {n : ℕ}
    {g : PoincareMT.RiemannianMetric (2 * n) (E n)}
    (D : PoincareMT.LeviCivitaData g) {u : E n → ℝ} {U : Set (E n)}
    (hU : IsOpen U) (hu : ContDiffOn ℝ ∞ u U)
    (hg : ∀ y ∈ U, ∀ v w : E n, g.inner y v w = realMetricForm u y v w)
    {x : E n} (hx : x ∈ U) (hdet : IsUnit (complexHessian u x).det)
    (v w : E n) :
    D.ricci x v w = -2 * (∑ i : Fin n, ∑ s : Fin n,
      partialBar s (fun y => complexConnectionTrace D y i) x *
        complexCoord v i * star (complexCoord w s)).re := by
  classical
  let Q := fun j i l k => partialBar j (fun y => complexConnectionCoeff D y i l k) x
  have hinv (k l : Fin n) :
      (∑ j : Fin n, complexHessian u x k j * inverseCoefficient u x l j) =
        if k = l then 1 else 0 := by
    have h := congrFun (congrFun (Matrix.mul_nonsing_inv (complexHessian u x) hdet) k) l
    simpa only [Matrix.mul_apply, Matrix.one_apply, inverseCoefficient] using h
  have hsym (i l j s : Fin n) :
      (∑ k : Fin n, complexHessian u x k s * Q j i l k) =
        ∑ k : Fin n, complexHessian u x k j * Q s i l k :=
    lowered_connection_derivative_swap D hU hu hg hx i l j s
  have hcontract := CurvatureCoordinateAlgebra.ricci_coefficient_sum
    (complexHessian u x) (inverseCoefficient u x) Q hinv hsym
    (complexCoord v) (complexCoord w)
  have htrace (k : Fin n) := retained_curvature_frame_sum D hU hu hg hx hdet v k
  calc
    D.ricci x v w = 2 * (∑ a, ∑ k : Fin n, ∑ s : Fin n,
        complexHessian u x k s * complexCoord (D.curvature x v
          (g.orthonormalBasis x a) (g.orthonormalBasis x a)) k *
            star (complexCoord w s)).re := by
      simp only [PoincareMT.LeviCivitaData.ricci,
        PoincareMT.LeviCivitaData.curvatureTensor, hg x hx, realMetricForm,
        Complex.re_sum, Finset.mul_sum]
    _ = 2 * (∑ k : Fin n, ∑ s : Fin n, complexHessian u x k s *
        (∑ a, complexCoord (D.curvature x v
          (g.orthonormalBasis x a) (g.orthonormalBasis x a)) k) *
            star (complexCoord w s)).re := by
      congr 2
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum, Finset.sum_mul]
    _ = -2 * (∑ k : Fin n, ∑ s : Fin n, complexHessian u x k s *
        (∑ i : Fin n, ∑ l : Fin n, ∑ j : Fin n,
          Q j i l k * complexCoord v i * inverseCoefficient u x l j) *
            star (complexCoord w s)).re := by
      simp only [htrace, Q, mul_neg, neg_mul, Finset.sum_neg_distrib, Complex.neg_re]
    _ = -2 * (∑ i : Fin n, ∑ s : Fin n,
        (∑ k : Fin n, Q s i k k) * complexCoord v i * star (complexCoord w s)).re := by
      rw [hcontract]
    _ = _ := by
      simp only [Q, ← partialBar_connectionTrace_eq_sum]

/-- The equation is used only now: the previously derived actual trace
identity implies Ric_G = G for this same metric and this same connection. -/
theorem IsSolution.retained_ricci_eq_metric {n : ℕ} {μ : ℝ} {u : E n → ℝ}
    (hu : IsSolution n μ u)
    {g : PoincareMT.RiemannianMetric (2 * n) (E n)}
    (D : PoincareMT.LeviCivitaData g) {V : Set (E n)}
    (hV : IsOpen V) (hVB : V ⊆ unitBall n)
    (hg : ∀ y ∈ V, ∀ v w : E n, g.inner y v w = realMetricForm u y v w)
    {x : E n} (hx : x ∈ V) (v w : E n) : D.ricci x v w = g.inner x v w := by
  rw [retained_ricci_eq_connection_trace D hV (hu.contDiffOn_ball.mono hVB) hg hx
    (hu.det_isUnit_closedBall (Metric.ball_subset_closedBall (hVB hx)))]
  simp_rw [hu.partialBar_complexConnectionTrace D hV hVB hg hx]
  rw [hg x hx]
  simp only [realMetricForm, neg_mul, Finset.sum_neg_distrib, Complex.neg_re]
  ring

/-- Original solution assumptions alone construct the local Einstein objects. -/
theorem IsSolution.exists_local_einstein_metric {n : ℕ} {μ : ℝ}
    {u : E n → ℝ} (hu : IsSolution n μ u) {p : E n} (hp : p ∈ unitBall n) :
    ∃ (g : PoincareMT.RiemannianMetric (2 * n) (E n))
      (D : PoincareMT.LeviCivitaData g) (V : Set (E n)),
      IsOpen V ∧ p ∈ V ∧ V ⊆ unitBall n ∧
      (∀ x ∈ V, ∀ v w : E n, g.inner x v w = realMetricForm u x v w) ∧
      (∀ x ∈ V, ∀ v w : E n, D.ricci x v w = g.inner x v w) := by
  obtain ⟨g, D, V, hV, hpV, hVB, hg⟩ := hu.exists_local_metric hp
  refine ⟨g, D, V, hV, hpV, hVB, hg, ?_⟩
  intro x hx v w
  exact hu.retained_ricci_eq_metric D hV hVB hg hx v w

end KEBall
