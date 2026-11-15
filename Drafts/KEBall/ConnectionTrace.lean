import Drafts.KEBall.Hessian20Bridge
import KEBall.EulerLaplacian

/-!
# The actual complex connection trace of a KE potential

Stage03 source draft; no Lean kernel receipt in the current environment.
The selected Levi-Civita connection is not replaced by a formal Chern
connection. The trace is computed from its action on actual constant fields.
This file stops BEFORE identifying that derivative with retained real Ricci.
-/

set_option autoImplicit false
set_option maxSynthPendingDepth 10
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped ContDiff Manifold Topology BigOperators

namespace KEBall
open KEBallProbe

theorem fderiv_equationDensity_apply {n : ℕ} {u : E n → ℝ} {x : E n}
    (μ : ℝ) (hu : DifferentiableAt ℝ u x) (v : E n) :
    fderiv ℝ (equationDensity μ u) x v =
      -(fderiv ℝ u x v * equationDensity μ u x) := by
  have h := (hu.hasFDerivAt.neg.exp).const_mul μ
  change HasFDerivAt (equationDensity μ u) _ x at h
  rw [h.fderiv]
  simp only [smul_apply, smul_eq_mul, neg_apply, Pi.neg_apply, equationDensity]
  ring

/-- Jacobi's formula in an arbitrary REAL direction, with the inverse
transpose from the unchanged Domain layer. -/
theorem IsSolution.directional_hessian_contraction {n : ℕ} {μ : ℝ}
    {u : E n → ℝ} (hu : IsSolution n μ u) {x : E n}
    (hx : x ∈ unitBall n) (v : E n) :
    (∑ k : Fin n, ∑ l : Fin n, inverseCoefficient u x k l *
      rd v (fun y => complexHessian u y k l) x) = -(fderiv ℝ u x v : ℂ) := by
  obtain ⟨U, hU, hKU, huU⟩ := hu.2.1
  have hxU := hKU (Metric.ball_subset_closedBall hx)
  have huAt := huU.contDiffAt (hU.mem_nhds hxU)
  have hG (k l : Fin n) : DifferentiableAt ℝ
      (fun y => complexHessian u y k l) x :=
    ((complexHessian_contDiffOn hU huU k l).contDiffAt
      (hU.mem_nhds hxU)).differentiableAt (by simp)
  have heq : (fun y => (complexHessian u y).det) =ᶠ[𝓝 x]
      (fun y => (equationDensity μ u y : ℂ)) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hx] with y hy
    simpa only [equationDensity, Complex.ofReal_mul] using hu.2.2.2.1 y hy
  have hw : DifferentiableAt ℝ (equationDensity μ u) x :=
    ((equationDensity_contDiffOn μ huU).contDiffAt
      (hU.mem_nhds hxU)).differentiableAt (by simp)
  have hrd : rd v (fun y => (complexHessian u y).det) x =
      -(fderiv ℝ u x v : ℂ) * (complexHessian u x).det := by
    change fderiv ℝ (fun y => (complexHessian u y).det) x v = _
    rw [heq.fderiv_eq]
    change rd v (fun y => (equationDensity μ u y : ℂ)) x = _
    rw [rd_ofReal hw,
      fderiv_equationDensity_apply μ (huAt.differentiableAt (by simp)),
      hu.2.2.2.1 x hx]
    simp only [equationDensity]
    push_cast
    ring
  have hunit := hu.det_isUnit_closedBall (Metric.ball_subset_closedBall hx)
  have hc := adjugate_contraction_eq_det_mul (complexHessian u x)
    (fun k l => rd v (fun y => complexHessian u y k l) x) hunit
  rw [← rd_det_field hG v, hrd] at hc
  apply mul_left_cancel₀ (isUnit_iff_ne_zero.mp hunit)
  exact hc.symm.trans (mul_comm _ _)

/-- The original equation implies tr(g^{-1} partial_i g) = -partial_i u. -/
theorem IsSolution.partialZ_hessian_contraction {n : ℕ} {μ : ℝ}
    {u : E n → ℝ} (hu : IsSolution n μ u) {x : E n}
    (hx : x ∈ unitBall n) (i : Fin n) :
    (∑ k : Fin n, ∑ l : Fin n, inverseCoefficient u x k l *
      partialZ i (fun y => complexHessian u y k l) x) =
      -partialZ i (fun y => (u y : ℂ)) x := by
  have hr := hu.directional_hessian_contraction hx (realDirection i)
  have hi := hu.directional_hessian_contraction hx (imagDirection i)
  have huAt := hu.2.1.contDiffAt (Metric.ball_subset_closedBall hx)
  calc
    _ = (2 : ℂ)⁻¹ *
        ((∑ k : Fin n, ∑ l : Fin n, inverseCoefficient u x k l *
          rd (realDirection i) (fun y => complexHessian u y k l) x) -
         Complex.I * (∑ k : Fin n, ∑ l : Fin n, inverseCoefficient u x k l *
          rd (imagDirection i) (fun y => complexHessian u y k l) x)) := by
      simp only [partialZ, dz, Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro l _
      ring
    _ = _ := by
      rw [hr, hi, partialZ_ofReal (huAt.differentiableAt (by simp))]
      ring

/-- The trace of the actual connection in the fixed complex frame.
This definition contains no assumed curvature or Einstein identity. -/
noncomputable def complexConnectionTrace {n : ℕ}
    {g : PoincareMT.RiemannianMetric (2 * n) (E n)}
    (D : PoincareMT.LeviCivitaData g) (x : E n) (i : Fin n) : ℂ :=
  ∑ k : Fin n, complexCoord
    (D.connection (fun _ : E n => realDirection k) x (realDirection i)) k

/-- An identity for the actual retained connection, not an auxiliary matrix. -/
theorem IsSolution.complexConnectionTrace_eq {n : ℕ} {μ : ℝ}
    {u : E n → ℝ} (hu : IsSolution n μ u)
    {g : PoincareMT.RiemannianMetric (2 * n) (E n)}
    (D : PoincareMT.LeviCivitaData g) {V : Set (E n)}
    (hV : IsOpen V) (hVB : V ⊆ unitBall n)
    (hg : ∀ y ∈ V, ∀ v w : E n, g.inner y v w = realMetricForm u y v w)
    {x : E n} (hx : x ∈ V) (i : Fin n) :
    complexConnectionTrace D x i = -partialZ i (fun y => (u y : ℂ)) x := by
  unfold complexConnectionTrace
  simp_rw [connection_const_complex_coordinates D hV
    (hu.contDiffOn_ball.mono hVB) hg hx
    (hu.det_isUnit_closedBall (Metric.ball_subset_closedBall (hVB hx)))]
  exact hu.partialZ_hessian_contraction (hVB hx) i

/-- Its antiholomorphic derivative is -g_{i bar j}. This is not yet a theorem
identifying retained REAL Ricci with a connection-trace derivative. -/
theorem IsSolution.partialBar_complexConnectionTrace {n : ℕ} {μ : ℝ}
    {u : E n → ℝ} (hu : IsSolution n μ u)
    {g : PoincareMT.RiemannianMetric (2 * n) (E n)}
    (D : PoincareMT.LeviCivitaData g) {V : Set (E n)}
    (hV : IsOpen V) (hVB : V ⊆ unitBall n)
    (hg : ∀ y ∈ V, ∀ v w : E n, g.inner y v w = realMetricForm u y v w)
    {x : E n} (hx : x ∈ V) (i j : Fin n) :
    partialBar j (fun y => complexConnectionTrace D y i) x =
      -complexHessian u x i j := by
  have heq : (fun y => complexConnectionTrace D y i) =ᶠ[𝓝 x]
      (fun y => -partialZ i (fun z => (u z : ℂ)) y) := by
    filter_upwards [hV.mem_nhds hx] with y hy
    exact hu.complexConnectionTrace_eq D hV hVB hg hy i
  have huAt := hu.2.1.contDiffAt (Metric.ball_subset_closedBall (hVB hx))
  have hc : ContDiffAt ℝ ∞ (fun y => (u y : ℂ)) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x huAt
  change (2 : ℂ)⁻¹ *
    (fderiv ℝ (fun y => complexConnectionTrace D y i) x (realDirection j) -
      Complex.I * fderiv ℝ (fun y => complexConnectionTrace D y i) x
        (-imagDirection j)) = _
  simp only [heq.fderiv_eq, fderiv_fun_neg, neg_apply]
  have hcomm := dz_comm_at hc (realDirection j) (-imagDirection j)
    (realDirection i) (imagDirection i)
  change partialBar j (partialZ i (fun y => (u y : ℂ))) x =
    complexHessian u x i j at hcomm
  calc
    _ = -partialBar j (partialZ i (fun y => (u y : ℂ))) x := by
      simp only [partialBar, dz, rd]
      ring
    _ = _ := congrArg Neg.neg hcomm

end KEBall
