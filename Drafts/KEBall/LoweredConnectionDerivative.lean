import Drafts.KEBall.ConnectionCoordinates

/-!
# Actual connection derivative after lowering its output

Stage04 DRAFT, not kernel checked. Symmetry is obtained by differentiating
an equality on the open neighbourhood. It is not a curvature assumption.
-/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped ContDiff Manifold Topology BigOperators

namespace KEBall
open KEBallProbe

/-- Differentiate g_{k bar s} Gamma^k_il = partial_i g_{l bar s}. -/
theorem lowered_connection_derivative {n : ℕ}
    {g : PoincareMT.RiemannianMetric (2 * n) (E n)}
    (D : PoincareMT.LeviCivitaData g) {u : E n → ℝ} {U : Set (E n)}
    (hU : IsOpen U) (hu : ContDiffOn ℝ ∞ u U)
    (hg : ∀ y ∈ U, ∀ v w : E n, g.inner y v w = realMetricForm u y v w)
    {x : E n} (hx : x ∈ U) (i l j s : Fin n) :
    (∑ k : Fin n, complexHessian u x k s *
      partialBar j (fun y => complexConnectionCoeff D y i l k) x) =
      partialBar j (partialZ i (fun y => complexHessian u y l s)) x -
        ∑ k : Fin n, partialBar j (fun y => complexHessian u y k s) x *
          complexConnectionCoeff D x i l k := by
  have hM (k : Fin n) := ((complexHessian_contDiffOn hU hu k s).contDiffAt
    (hU.mem_nhds hx)).differentiableAt (by simp)
  have hA (k : Fin n) := (complexConnectionCoeff_smoothAt D x i l k).differentiableAt
    (by simp)
  have heq : (fun y => ∑ k : Fin n,
      complexHessian u y k s * complexConnectionCoeff D y i l k) =ᶠ[𝓝 x]
      partialZ i (fun y => complexHessian u y l s) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact connection_const_complex_row D hU hu hg hy i l s
  have hd := partialBar_congr_nhds heq j
  change dz (realDirection j) (-imagDirection j) _ x = _ at hd
  have hMA (k : Fin n) : DifferentiableAt ℝ
      (fun y => complexHessian u y k s * complexConnectionCoeff D y i l k) x :=
    (hM k).mul (hA k)
  rw [dz_sum_differentiableAt hMA] at hd
  have hp (k : Fin n) := dz_mul_differentiableAt (hM k) (hA k)
    (realDirection j) (-imagDirection j)
  simp only [hp, Finset.sum_add_distrib] at hd
  change (∑ k : Fin n, partialBar j (fun y => complexHessian u y k s) x *
    complexConnectionCoeff D x i l k) +
    (∑ k : Fin n, complexHessian u x k s *
      partialBar j (fun y => complexConnectionCoeff D y i l k) x) = _ at hd
  apply eq_sub_iff_add_eq.mpr
  rw [add_comm]
  exact hd

/-- Both antiholomorphic slots become symmetric after lowering the output. -/
theorem lowered_connection_derivative_swap {n : ℕ}
    {g : PoincareMT.RiemannianMetric (2 * n) (E n)}
    (D : PoincareMT.LeviCivitaData g) {u : E n → ℝ} {U : Set (E n)}
    (hU : IsOpen U) (hu : ContDiffOn ℝ ∞ u U)
    (hg : ∀ y ∈ U, ∀ v w : E n, g.inner y v w = realMetricForm u y v w)
    {x : E n} (hx : x ∈ U) (i l j s : Fin n) :
    (∑ k : Fin n, complexHessian u x k s *
      partialBar j (fun y => complexConnectionCoeff D y i l k) x) =
    ∑ k : Fin n, complexHessian u x k j *
      partialBar s (fun y => complexConnectionCoeff D y i l k) x := by
  rw [lowered_connection_derivative D hU hu hg hx,
    lowered_connection_derivative D hU hu hg hx,
    partialBar_partialZ_metric_swap hU hu hx i l j s]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [partialBar_metric_swap hU hu hx k j s]

/-- The previously defined connection trace is the coefficient trace; this
records the interface rather than replacing the old definition. -/
theorem complexConnectionTrace_eq_sum_coeff {n : ℕ}
    {g : PoincareMT.RiemannianMetric (2 * n) (E n)}
    (D : PoincareMT.LeviCivitaData g) (x : E n) (i : Fin n) :
    complexConnectionTrace D x i = ∑ k : Fin n, complexConnectionCoeff D x i k k := rfl

theorem partialBar_connectionTrace_eq_sum {n : ℕ}
    {g : PoincareMT.RiemannianMetric (2 * n) (E n)}
    (D : PoincareMT.LeviCivitaData g) (x : E n) (i j : Fin n) :
    partialBar j (fun y => complexConnectionTrace D y i) x =
      ∑ k : Fin n, partialBar j (fun y => complexConnectionCoeff D y i k k) x := by
  simp only [complexConnectionTrace_eq_sum_coeff]
  exact dz_sum_differentiableAt
    (fun k => (complexConnectionCoeff_smoothAt D x i k k).differentiableAt (by simp)) _ _

end KEBall
