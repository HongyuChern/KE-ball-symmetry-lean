import Drafts.KEBall.InteriorGradientRigidity

/-!
Stage10 SOURCE_DRAFT_UNCOMPILED.
The metric potential u and test function h are independent arguments. Every
connection and gradient below is the actual Poincare LeviCivitaData object.
The inherited self-Hessian bridge already treats h=u; it is not reproved here.
-/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped ContDiff Manifold Topology BigOperators

namespace KEBall

theorem hessian_complexify20_test_eq_second_sub_connection {n : ℕ}
    {g : PoincareMT.RiemannianMetric (2 * n) (E n)}
    (D : PoincareMT.LeviCivitaData g) {u h : E n → ℝ} {U : Set (E n)}
    (hU : IsOpen U) (hu : ContDiffOn ℝ ∞ u U)
    (hg : ∀ y ∈ U, ∀ v w : E n, g.inner y v w = realMetricForm u y v w)
    {x : E n} (hx : x ∈ U) (hh : ContDiffAt ℝ ∞ h x) (i j : Fin n) :
    complexify20 (D.hessian h x) i j =
      partialZ i (partialZ j (fun y => (h y : ℂ))) x -
        ∑ k : Fin n, partialZ k (fun y => (h y : ℂ)) x *
          complexCoord (D.connection (fun _ : E n => realDirection j) x
            (realDirection i)) k := by
  let C := D.connection (fun _ : E n => realDirection j) x (realDirection i)
  have hri : D.connection (fun _ : E n => imagDirection j) x (realDirection i) =
      J C := by
    rw [← J_realDirection_eq_imag, connection_const_J_right D hU hu hg hx]
  have hir : D.connection (fun _ : E n => realDirection j) x (imagDirection i) =
      J C := by
    rw [← J_realDirection_eq_imag, connection_const_J_left D hU hu hg hx]
  have hii : D.connection (fun _ : E n => imagDirection j) x (imagDirection i) =
      -C := by
    rw [← J_realDirection_eq_imag, connection_const_J_right D hU hu hg hx, hir, J_sq]
  rw [partialZ_partialZ_eq_complexify20 hh,
    wirtinger_covector_apply (hh.differentiableAt (by simp))]
  simp only [complexify20, hessian_eq_realHessian_sub_connection D hh,
    hri, hir, hii, map_neg]
  dsimp only [C]
  push_cast
  ring

/-- Identification in g_u of the actual Hessian of an arbitrary smooth h. -/
theorem metricCovariantHessian20_eq_hessian_complexification {n : ℕ}
    {g : PoincareMT.RiemannianMetric (2 * n) (E n)}
    (D : PoincareMT.LeviCivitaData g) {u h : E n → ℝ} {U : Set (E n)}
    (hU : IsOpen U) (hu : ContDiffOn ℝ ∞ u U)
    (hg : ∀ y ∈ U, ∀ v w : E n, g.inner y v w = realMetricForm u y v w)
    {x : E n} (hx : x ∈ U) (hh : ContDiffAt ℝ ∞ h x)
    (hdet : IsUnit (complexHessian u x).det) (i j : Fin n) :
    metricCovariantHessian20 u h x i j = complexify20 (D.hessian h x) i j := by
  rw [hessian_complexify20_test_eq_second_sub_connection D hU hu hg hx hh]
  unfold metricCovariantHessian20
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [connection_const_complex_coordinates D hU hu hg hx hdet, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  ring

/-- Real gradient coordinates for a test function in the fixed metric g_u. -/
theorem gradient_complex_coordinates_fixed_metric {n : ℕ}
    {g : PoincareMT.RiemannianMetric (2 * n) (E n)}
    (D : PoincareMT.LeviCivitaData g) {u h : E n → ℝ} {x : E n}
    (hh : DifferentiableAt ℝ h x) (hdet : IsUnit (complexHessian u x).det)
    (hg : ∀ v w : E n, g.inner x v w = realMetricForm u x v w) (i : Fin n) :
    complexCoord (D.gradient h x) i =
      ∑ j : Fin n, inverseCoefficient u x i j *
        partialBar j (fun y => (h y : ℂ)) x := by
  have hd (v : E n) : g.inner x (D.gradient h x) v = fderiv ℝ h x v := by
    rw [D.inner_gradient]
    simp only [mvfderiv, mfderiv_eq_fderiv]
    rfl
  have hdual (v : E n) : hermitianRealification (complexHessian u x)
      (D.gradient h x) v =
      2 * (∑ j : Fin n, partialZ j (fun y => (h y : ℂ)) x * complexCoord v j).re := by
    rw [← realMetricForm_eq, ← hg, hd, fderiv_eq_wirtinger hh]
  let A := complexHessian u x
  let p : Fin n → ℂ := fun j => partialBar j (fun y => (h y : ℂ)) x
  have hrow : A.transpose.mulVec (complexCoord (D.gradient h x)) = p := by
    funext j
    rw [show p j = star (partialZ j (fun y => (h y : ℂ)) x) from partialBar_ofReal hh j]
    exact hermitianRealification_dual_coordinates A
      (fun j => partialZ j (fun y => (h y : ℂ)) x) (D.gradient h x) hdual j
  have hcoord : complexCoord (D.gradient h x) = A⁻¹.transpose.mulVec p := by
    have hz := congrArg (A⁻¹.transpose.mulVec) hrow
    rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul,
      Matrix.mul_nonsing_inv A hdet, Matrix.transpose_one, Matrix.one_mulVec] at hz
    exact hz
  have hz := congrFun hcoord i
  simpa only [A, p, Matrix.mulVec, dotProduct, Matrix.transpose_apply,
    inverseCoefficient] using hz

/-- One local geometric realization works for every smooth test function. -/
theorem IsSolution.exists_local_fixed_metric_bridges {n : ℕ} {μ : ℝ}
    {u : E n → ℝ} (hu : IsSolution n μ u) {p : E n} (hp : p ∈ unitBall n) :
    ∃ (g : PoincareMT.RiemannianMetric (2 * n) (E n))
      (D : PoincareMT.LeviCivitaData g) (U : Set (E n)),
      IsOpen U ∧ p ∈ U ∧ U ⊆ unitBall n ∧
      (∀ x ∈ U, ∀ v w : E n, g.inner x v w = realMetricForm u x v w) ∧
      (∀ x ∈ U, ∀ h : E n → ℝ, ContDiffAt ℝ ∞ h x →
        (∀ i j : Fin n, metricCovariantHessian20 u h x i j =
          complexify20 (D.hessian h x) i j) ∧
        (∀ i : Fin n, complexCoord (D.gradient h x) i =
          ∑ j : Fin n, inverseCoefficient u x i j *
            partialBar j (fun y => (h y : ℂ)) x)) := by
  obtain ⟨g, D, U, hU, hpU, hUB, hg⟩ := hu.exists_local_metric hp
  refine ⟨g, D, U, hU, hpU, hUB, hg, ?_⟩
  intro x hx h hh
  have hdet := hu.det_isUnit_closedBall (Metric.ball_subset_closedBall (hUB hx))
  constructor
  · intro i j
    exact metricCovariantHessian20_eq_hessian_complexification D hU
      (hu.contDiffOn_ball.mono hUB) hg hx hh hdet i j
  · intro i
    exact gradient_complex_coordinates_fixed_metric D
      (hh.differentiableAt (by simp)) hdet (hg x hx) i

/-- The equality rigidity is now stated for an actual local metric and
connection. Neither E's Hessian metric nor a formal replacement connection
is used. This is a (2,0) statement, not vanishing of the whole real Hessian. -/
theorem IsSolution.exists_local_exponential_geometric_rigidity {n : ℕ}
    (hn : 2 ≤ n) {μ : ℝ} {u : E n → ℝ} (hu : IsSolution n μ u)
    {p : E n} (hp : p ∈ unitBall n) :
    ∃ (t₀ : ℝ) (g : PoincareMT.RiemannianMetric (2 * n) (E n))
      (D : PoincareMT.LeviCivitaData g) (U : Set (E n)),
      0 < t₀ ∧ t₀ < (n + 1 : ℝ) ∧ boundaryPolynomial n t₀ = μ ∧
      IsOpen U ∧ p ∈ U ∧ U ⊆ unitBall n ∧
      (∀ x ∈ U, ∀ v w : E n, g.inner x v w = realMetricForm u x v w) ∧
      (∀ x ∈ U, ∀ i j : Fin n, complexify20 (D.hessian (expWeight u) x) i j = 0) ∧
      (∀ x ∈ U, D.gradient (expWeight u) x = (-1 / ((n + 1 : ℝ) - t₀)) • x) := by
  obtain ⟨t₀, ht, htk, hF, _, hV⟩ := hu.exists_exponentialGradient_closedBall_data hn
  obtain ⟨g, D, U, hU, hpU, hUB, hg, hbridge⟩ := hu.exists_local_fixed_metric_bridges hp
  refine ⟨t₀, g, D, U, ht, htk, hF, hU, hpU, hUB, hg, ?_, ?_⟩
  · intro x hx i j
    have hE := contDiffAt_expWeight (hu.2.1.contDiffAt (Metric.ball_subset_closedBall (hUB hx)))
    rw [← (hbridge x hx (expWeight u) hE).1 i j]
    exact hu.metricCovariantHessian20_expWeight_eq_zero hn (hUB hx) i j
  · intro x hx
    apply complexCoord_injective
    funext i
    have hE := contDiffAt_expWeight (hu.2.1.contDiffAt (Metric.ball_subset_closedBall (hUB hx)))
    rw [(hbridge x hx (expWeight u) hE).2 i]
    change exponentialGradient u x i = _
    rw [hV x (Metric.ball_subset_closedBall (hUB hx)) i]
    change _ = (complexCoordCLM i) ((-1 / ((n + 1 : ℝ) - t₀)) • x)
    rw [map_smul, Complex.real_smul, complexCoordCLM_apply]

#print axioms metricCovariantHessian20_eq_hessian_complexification
#print axioms IsSolution.exists_local_fixed_metric_bridges
#print axioms IsSolution.exists_local_exponential_geometric_rigidity

end KEBall
