import Drafts.KEBall.ExponentialRigidityPrelude
import Drafts.KEBall.WirtingerConjugation

/-!
Stage09 SOURCE_DRAFT_UNCOMPILED.
The actual exponential gradient satisfies the Cauchy--Riemann equations.
The inverse-transpose convention is derived by matrix multiplication.
Metric compatibility is proved by differentiating the actual dual identity;
no holomorphicity, connection identity or inverse derivative is assumed.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped ContDiff Topology BigOperators ComplexOrder

namespace KEBall
open KEBallProbe

/-- The defining gradient is genuinely dual to dE for the original metric. -/
theorem IsSolution.exponentialGradient_dual {n : ℕ} {μ : ℝ} {u : E n → ℝ}
    (hu : IsSolution n μ u) {x : E n} (hx : x ∈ closedUnitBall n) (j : Fin n) :
    (∑ i : Fin n, complexHessian u x i j * exponentialGradient u x i) =
      partialBar j (fun y => (expWeight u y : ℂ)) x := by
  let A := complexHessian u x
  let p : Fin n → ℂ := fun k => partialBar k (fun y => (expWeight u y : ℂ)) x
  change (A.transpose.mulVec (A⁻¹.transpose.mulVec p)) j = p j
  rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul,
    Matrix.nonsing_inv_mul A (hu.det_isUnit_closedBall hx),
    Matrix.transpose_one, Matrix.one_mulVec]

/-- Invertibility of the same row pairing, used after differentiation. -/
theorem complexHessian_row_zero {n : ℕ} {u : E n → ℝ} {x : E n}
    (hdet : IsUnit (complexHessian u x).det) (w : Fin n → ℂ)
    (hw : ∀ j : Fin n, (∑ i : Fin n, complexHessian u x i j * w i) = 0) : w = 0 := by
  let A := complexHessian u x
  have hrow : A.transpose.mulVec w = 0 := by funext j; exact hw j
  have h := congrArg (A⁻¹.transpose.mulVec) hrow
  rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul,
    Matrix.mul_nonsing_inv A hdet, Matrix.transpose_one, Matrix.one_mulVec,
    Matrix.mulVec_zero] at h
  exact h

theorem IsSolution.star_partialZ_metric {n : ℕ} {μ : ℝ} {u : E n → ℝ}
    (hu : IsSolution n μ u) {x : E n} (hx : x ∈ unitBall n) (k j l : Fin n) :
    star (partialZ k (fun y => complexHessian u y j l) x) =
      partialBar k (fun y => complexHessian u y l j) x := by
  have huC := Complex.ofRealCLM.contDiff.contDiffAt.comp x
    (hu.2.1.contDiffAt (Metric.ball_subset_closedBall hx))
  have hg : ContDiffAt ℝ ∞ (fun y => complexHessian u y j l) x :=
    smoothAt_dz (smoothAt_dz huC (realDirection l) (-imagDirection l))
      (realDirection j) (imagDirection j)
  have heq : (fun y => star (complexHessian u y j l)) =ᶠ[𝓝 x]
      (fun y => complexHessian u y l j) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hx] with y hy
    exact (hu.2.2.1 y hy).isHermitian.apply l j
  rw [← partialBar_star (hg.differentiableAt (by simp))]
  exact partialBar_congr_nhds heq k

/-- The conjugate of the fixed-metric (2,0) identity, with all indices exposed. -/
theorem IsSolution.expWeight_bar_bar_eq_metric_derivative {n : ℕ}
    (hn : 2 ≤ n) {μ : ℝ} {u : E n → ℝ} (hu : IsSolution n μ u)
    {x : E n} (hx : x ∈ unitBall n) (k j : Fin n) :
    partialBar k (partialBar j (fun y => (expWeight u y : ℂ))) x =
      ∑ i : Fin n, partialBar k (fun y => complexHessian u y i j) x *
        exponentialGradient u x i := by
  have hE := contDiffAt_expWeight (hu.2.1.contDiffAt (Metric.ball_subset_closedBall hx))
  have hInv := (hu.2.2.1 x hx).inv.isHermitian
  have hc (a b : Fin n) : star (inverseCoefficient u x a b) =
      inverseCoefficient u x b a := hInv.apply a b
  have hs := congrArg star (hu.metricCovariantHessian20_expWeight_eq_zero hn hx k j)
  simp only [metricCovariantHessian20, star_sub, star_sum, star_mul, star_zero] at hs
  rw [← partialBar_partialBar_ofReal hE] at hs
  simp_rw [hc, hu.star_partialZ_metric hx,
    ← partialBar_ofReal (hE.differentiableAt (by simp))] at hs
  have hsum : (∑ a : Fin n, ∑ b : Fin n,
      partialBar a (fun y => (expWeight u y : ℂ)) x *
        (partialBar k (fun y => complexHessian u y b j) x *
          inverseCoefficient u x b a)) =
      ∑ i : Fin n, partialBar k (fun y => complexHessian u y i j) x *
        exponentialGradient u x i := by
    rw [Finset.sum_comm]
    unfold exponentialGradient
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro a _
    ring
  rw [hsum] at hs
  exact sub_eq_zero.mp hs

/-- Differentiate the genuine metric-duality equation on an open ball. -/
theorem IsSolution.exponentialGradient_lowered_partialBar {n : ℕ}
    {μ : ℝ} {u : E n → ℝ} (hu : IsSolution n μ u)
    {x : E n} (hx : x ∈ unitBall n) (k j : Fin n) :
    (∑ i : Fin n, complexHessian u x i j *
      partialBar k (fun y => exponentialGradient u y i) x) =
      partialBar k (partialBar j (fun y => (expWeight u y : ℂ))) x -
        ∑ i : Fin n, partialBar k (fun y => complexHessian u y i j) x *
          exponentialGradient u x i := by
  have huC := Complex.ofRealCLM.contDiff.contDiffAt.comp x
    (hu.2.1.contDiffAt (Metric.ball_subset_closedBall hx))
  have hM (i : Fin n) : DifferentiableAt ℝ (fun y => complexHessian u y i j) x :=
    (smoothAt_dz (smoothAt_dz huC (realDirection j) (-imagDirection j))
      (realDirection i) (imagDirection i)).differentiableAt (by simp)
  have hV (i : Fin n) : DifferentiableAt ℝ (fun y => exponentialGradient u y i) x :=
    (((hu.exponentialGradient_contDiffOn_closedBall i).mono Metric.ball_subset_closedBall).contDiffAt
      (Metric.isOpen_ball.mem_nhds hx)).differentiableAt (by simp)
  have heq : (fun y => ∑ i : Fin n, complexHessian u y i j *
      exponentialGradient u y i) =ᶠ[𝓝 x] partialBar j (fun y => (expWeight u y : ℂ)) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hx] with y hy
    exact hu.exponentialGradient_dual (Metric.ball_subset_closedBall hy) j
  have hd := partialBar_congr_nhds heq k
  change dz (realDirection k) (-imagDirection k) _ x = _ at hd
  have hMV (i : Fin n) : DifferentiableAt ℝ
      (fun y => complexHessian u y i j * exponentialGradient u y i) x :=
    (hM i).mul (hV i)
  rw [dz_sum_differentiableAt hMV] at hd
  have hp (i : Fin n) := dz_mul_differentiableAt (hM i) (hV i)
    (realDirection k) (-imagDirection k)
  simp only [hp, Finset.sum_add_distrib] at hd
  apply eq_sub_iff_add_eq.mpr
  rw [add_comm]
  exact hd

/-- Every component of the actual exponential gradient satisfies CR.
This is a conclusion from the original solution; it is never an input. -/
theorem IsSolution.partialBar_exponentialGradient_eq_zero {n : ℕ}
    (hn : 2 ≤ n) {μ : ℝ} {u : E n → ℝ} (hu : IsSolution n μ u)
    {x : E n} (hx : x ∈ unitBall n) (k i : Fin n) :
    partialBar k (fun y => exponentialGradient u y i) x = 0 := by
  have hrow (j : Fin n) : (∑ a : Fin n, complexHessian u x a j *
      partialBar k (fun y => exponentialGradient u y a) x) = 0 := by
    rw [hu.exponentialGradient_lowered_partialBar hx,
      hu.expWeight_bar_bar_eq_metric_derivative hn hx, sub_self]
  have hz := complexHessian_row_zero (hu.det_isUnit_closedBall
    (Metric.ball_subset_closedBall hx))
    (fun a => partialBar k (fun y => exponentialGradient u y a) x) hrow
  exact congrFun hz i

#print axioms IsSolution.partialBar_exponentialGradient_eq_zero

end KEBall
