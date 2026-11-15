import Drafts.KEBall.GradientNormDifferential
import Drafts.KEBall.BoundaryThirdJet
import Drafts.KEBall.BoundaryInverseSplit
import KEBall.HorizontalPower

/-!
# The actual ambient normal derivative of q

SOURCE_DRAFT_UNCOMPILED. The normal derivative is obtained in the open ball
from metric compatibility, and extended continuously to the closed ball.
No equality restricted to the sphere is differentiated transversely.
-/

set_option autoImplicit false
set_option maxSynthPendingDepth 10
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped ContDiff Manifold Topology BigOperators RealInnerProductSpace

namespace KEBall

/-- The actual inverse metric dual of du, in real coordinates. -/
noncomputable def inverseGradientVector {n : ℕ} (u : E n → ℝ) (x : E n) : E n :=
  complexVectorReal (fun i => ∑ j : Fin n, inverseCoefficient u x i j *
    partialBar j (fun y => (u y : ℂ)) x)

theorem inverseGradientVector_eq_metric_gradient {n : ℕ}
    {g : PoincareMT.RiemannianMetric (2 * n) (E n)}
    (D : PoincareMT.LeviCivitaData g) {u : E n → ℝ} {x : E n}
    (hu : DifferentiableAt ℝ u x) (hd : IsUnit (complexHessian u x).det)
    (hg : ∀ v w : E n, g.inner x v w = realMetricForm u x v w) :
    inverseGradientVector u x = D.gradient u x := by
  apply complexCoord_injective
  rw [inverseGradientVector, complexCoord_complexVectorReal]
  funext i
  exact (metric_gradient_complex_coordinates D hu hd hg i).symm

theorem IsSolution.inverseGradientVector_contDiffOn_closedBall {n : ℕ} {μ : ℝ}
    {u : E n → ℝ} (hu : IsSolution n μ u) :
    ContDiffOn ℝ ∞ (inverseGradientVector u) (closedUnitBall n) := by
  obtain ⟨U, hU, hKU, huU⟩ := hu.2.1
  have huC : ContDiffOn ℝ ∞ (fun y => (u y : ℂ)) U :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn huU
  have hInv (i j : Fin n) : ContDiffOn ℝ ∞
      (fun y => inverseCoefficient u y i j) (closedUnitBall n) :=
    AuxiliaryPRegularity.matrixField_inverse_entry_contDiffOn
      (fun i j => (complexHessian_contDiffOn hU huU i j).mono hKU)
      (fun y hy => isUnit_iff_ne_zero.mp (hu.det_isUnit_closedBall hy)) j i
  apply complexVectorReal_contDiffOn
  intro i
  apply ContDiffOn.sum
  intro j _
  exact (hInv i j).mul
    ((smoothOn_dz hU huC (realDirection j) (-imagDirection j)).mono hKU)

/-- In a local metric, Koszul cancels the two equal off-diagonal terms.
This retains both derivatives of the covector in the dual norm. -/
theorem fderiv_gradientNormSq_eq_realHessian_metricJet_local {n : ℕ} {μ : ℝ}
    {u : E n → ℝ} (hu : IsSolution n μ u)
    {g : PoincareMT.RiemannianMetric (2 * n) (E n)}
    (D : PoincareMT.LeviCivitaData g) {U : Set (E n)}
    (hU : IsOpen U) (hUB : U ⊆ unitBall n)
    (hg : ∀ y ∈ U, ∀ v w : E n, g.inner y v w = realMetricForm u y v w)
    {x : E n} (hx : x ∈ U) (a : E n) :
    fderiv ℝ (gradientNormSq u) x a =
      realHessian u x a (inverseGradientVector u x) -
        fderiv ℝ (fun y => realMetricForm u y
          (inverseGradientVector u x) (inverseGradientVector u x)) x a / 2 := by
  have huAt := hu.2.1.contDiffAt (Metric.ball_subset_closedBall (hUB hx))
  have hV := inverseGradientVector_eq_metric_gradient D
    (huAt.differentiableAt (by simp))
    (hu.det_isUnit_closedBall (Metric.ball_subset_closedBall (hUB hx))) (hg x hx)
  rw [hV, fderiv_gradientNormSq_eq_hessian hu D hU hUB hg hx,
    hessian_eq_realHessian_sub_connection D huAt]
  have hk := D.inner_connection_const x a (D.gradient u x) (D.gradient u x)
  have heq : (fun y => g.inner y (D.gradient u x) a) =
      (fun y => g.inner y a (D.gradient u x)) := by
    funext y
    exact g.symm y _ _
  rw [heq] at hk
  have hdu (w : E n) : fderiv ℝ u x w = g.inner x w (D.gradient u x) := by
    rw [g.symm x, D.inner_gradient]
    simp only [mvfderiv, mfderiv_eq_fderiv]
    rfl
  have hmetric : (fun y => g.inner y (D.gradient u x) (D.gradient u x)) =ᶠ[𝓝 x]
      (fun y => realMetricForm u y (D.gradient u x) (D.gradient u x)) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact hg y hy _ _
  rw [hmetric.fderiv_eq] at hk
  rw [hdu]
  linarith

theorem IsSolution.fderiv_gradientNormSq_eq_realThirdDerivative {n : ℕ} {μ : ℝ}
    {u : E n → ℝ} (hu : IsSolution n μ u) {x : E n}
    (hx : x ∈ unitBall n) (a : E n) :
    fderiv ℝ (gradientNormSq u) x a =
      realHessian u x a (inverseGradientVector u x) -
        (realThirdDerivative u x a (inverseGradientVector u x) (inverseGradientVector u x) +
          realThirdDerivative u x a (J (inverseGradientVector u x))
            (J (inverseGradientVector u x))) / 4 := by
  obtain ⟨g, D, U, hU, hxU, hUB, hg⟩ := hu.exists_local_metric hx
  rw [fderiv_gradientNormSq_eq_realHessian_metricJet_local hu D hU hUB hg hxU,
    fderiv_realMetricForm hU (hu.contDiffOn_ball.mono hUB) hxU]
  ring

/-- Continuity is applied to the ambient differentiated identity, not to a
normal derivative of the boundary restriction q=t^(n+1)/μ. -/
theorem IsSolution.fderiv_gradientNormSq_eq_realThirdDerivative_closedBall
    {n : ℕ} {μ : ℝ} {u : E n → ℝ} (hu : IsSolution n μ u) {x : E n}
    (hx : x ∈ closedUnitBall n) (a : E n) :
    fderiv ℝ (gradientNormSq u) x a =
      realHessian u x a (inverseGradientVector u x) -
        (realThirdDerivative u x a (inverseGradientVector u x) (inverseGradientVector u x) +
          realThirdDerivative u x a (J (inverseGradientVector u x))
            (J (inverseGradientVector u x))) / 4 := by
  obtain ⟨U, hU, hKU, huU⟩ := hu.2.1
  obtain ⟨V, hV, hKV, hqV⟩ := hu.gradientNormSq_smoothNear
  have hleft : ContinuousOn (fun y => fderiv ℝ (gradientNormSq u) y a)
      (closedUnitBall n) :=
    (((hqV.fderiv_of_isOpen (m := 0) hV (by simp)).clm_apply contDiffOn_const).mono hKV).continuousOn
  have hH : ContDiffOn ℝ ∞ (realHessian u) (closedUnitBall n) :=
    (((huU.fderiv_of_isOpen (m := ∞) hU (by simp)).fderiv_of_isOpen (m := ∞) hU (by simp)).mono hKU)
  have hT : ContDiffOn ℝ ∞ (realThirdDerivative u) (closedUnitBall n) :=
    ((((huU.fderiv_of_isOpen (m := ∞) hU (by simp)).fderiv_of_isOpen (m := ∞) hU (by simp)).fderiv_of_isOpen (m := ∞) hU (by simp)).mono hKU)
  have hW := hu.inverseGradientVector_contDiffOn_closedBall
  have hJW : ContDiffOn ℝ ∞ (fun y => J (inverseGradientVector u y))
      (closedUnitBall n) := by
    simpa only [Function.comp_def, JCLM_apply] using (JCLM n).contDiff.comp_contDiffOn hW
  have hTa : ContDiffOn ℝ ∞ (fun y => realThirdDerivative u y a)
      (closedUnitBall n) := hT.clm_apply contDiffOn_const
  have hquad := (((hTa.clm_apply hW).clm_apply hW).add
    ((hTa.clm_apply hJW).clm_apply hJW)).div_const 4
  have hright : ContinuousOn (fun y =>
      realHessian u y a (inverseGradientVector u y) -
        (realThirdDerivative u y a (inverseGradientVector u y) (inverseGradientVector u y) +
          realThirdDerivative u y a (J (inverseGradientVector u y))
            (J (inverseGradientVector u y))) / 4) (closedUnitBall n) :=
    (((hH.clm_apply contDiffOn_const).clm_apply hW).sub hquad).continuousOn
  have heq : EqOn (fun y => fderiv ℝ (gradientNormSq u) y a)
      (fun y => realHessian u y a (inverseGradientVector u y) -
        (realThirdDerivative u y a (inverseGradientVector u y) (inverseGradientVector u y) +
          realThirdDerivative u y a (J (inverseGradientVector u y))
            (J (inverseGradientVector u y))) / 4) (unitBall n) := by
    intro y hy
    exact hu.fderiv_gradientNormSq_eq_realThirdDerivative hy a
  apply heq.of_subset_closure hleft hright Metric.ball_subset_closedBall ?_ hx
  rw [unitBall, closure_ball (0 : E n) (by norm_num : (1 : ℝ) ≠ 0)]
  exact Set.Subset.rfl

theorem IsSolution.fderiv_gradientNormSq_eq_metricJet_closedBall
    {n : ℕ} {μ : ℝ} {u : E n → ℝ} (hu : IsSolution n μ u) {x : E n}
    (hx : x ∈ closedUnitBall n) (a : E n) :
    fderiv ℝ (gradientNormSq u) x a =
      realHessian u x a (inverseGradientVector u x) -
        fderiv ℝ (fun y => realMetricForm u y
          (inverseGradientVector u x) (inverseGradientVector u x)) x a / 2 := by
  obtain ⟨U, hU, hKU, huU⟩ := hu.2.1
  rw [hu.fderiv_gradientNormSq_eq_realThirdDerivative_closedBall hx,
    fderiv_realMetricForm hU huU (hKU hx)]
  ring

theorem IsSolution.inverseGradientVector_normSq_closedBall
    {n : ℕ} {μ : ℝ} {u : E n → ℝ} (hu : IsSolution n μ u) {x : E n}
    (hx : x ∈ closedUnitBall n) :
    realMetricForm u x (inverseGradientVector u x) (inverseGradientVector u x) =
      2 * gradientNormSq u x := by
  obtain ⟨U, hU, hKU, huU⟩ := hu.2.1
  have hW := hu.inverseGradientVector_contDiffOn_closedBall
  have hG : ContDiffOn ℝ ∞
      (fun y => hermitianRealification (complexHessian u y)) (closedUnitBall n) :=
    (hermitianRealification_contDiffOn (complexHessian_contDiffOn hU huU)).mono hKU
  have hleft : ContinuousOn (fun y => realMetricForm u y
      (inverseGradientVector u y) (inverseGradientVector u y)) (closedUnitBall n) := by
    simpa only [realMetricForm_eq] using ((hG.clm_apply hW).clm_apply hW).continuousOn
  have hright : ContinuousOn (fun y => 2 * gradientNormSq u y) (closedUnitBall n) :=
    continuousOn_const.mul (fun y hy =>
      (hu.gradientNormSq_contDiffAt_closedBall hy).continuousAt.continuousWithinAt)
  have heq : EqOn (fun y => realMetricForm u y
      (inverseGradientVector u y) (inverseGradientVector u y))
      (fun y => 2 * gradientNormSq u y) (unitBall n) := by
    intro y hy
    obtain ⟨g, D, V, hV, hyV, hVB, hg⟩ := hu.exists_local_metric hy
    have hdiff := (hu.2.1.contDiffAt (Metric.ball_subset_closedBall hy)).differentiableAt
      (by simp)
    have hdet := hu.det_isUnit_closedBall (Metric.ball_subset_closedBall hy)
    dsimp only
    rw [inverseGradientVector_eq_metric_gradient D hdiff hdet (hg y hyV),
      ← hg y hyV]
    exact gradient_normSq_eq_twice_complex D hdiff hdet (hg y hyV)
  apply heq.of_subset_closure hleft hright Metric.ball_subset_closedBall ?_ hx
  rw [unitBall, closure_ball (0 : E n) (by norm_num : (1 : ℝ) ≠ 0)]
  exact Set.Subset.rfl

theorem IsSolution.inverseGradientVector_on_sphere {n : ℕ} (hn : 2 ≤ n)
    {μ : ℝ} {u : E n → ℝ} (hu : IsSolution n μ u) {x : E n}
    (hx : x ∈ unitSphere n) :
    inverseGradientVector u x = boundaryInverseDirection u μ x := by
  apply complexCoord_injective
  rw [inverseGradientVector, complexCoord_complexVectorReal]
  funext i
  exact hu.boundary_inverseCoefficient_partialBar hn hx i

theorem IsSolution.gradientNormSq_on_sphere_schur {n : ℕ} (hn : 2 ≤ n)
    {μ : ℝ} {u : E n → ℝ} (hu : IsSolution n μ u) {x : E n}
    (hx : x ∈ unitSphere n) :
    gradientNormSq u x = boundarySlope u x ^ 2 /
      (μ / boundarySlope u x ^ (n - 1)) := by
  have ht : boundarySlope u x ≠ 0 := ne_of_gt (hu.boundarySlope_pos hn hx)
  have hp : boundarySlope u x ^ (n + 1) =
      boundarySlope u x ^ 2 * boundarySlope u x ^ (n - 1) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hu.gradientNormSq_on_sphere hn hx, hp]
  field_simp [ht, ne_of_gt hu.1]

/-- The first two covector derivatives contribute together. In particular,
the horizontal square term is present before the Schur cancellation. -/
theorem IsSolution.boundary_realHessian_inverseGradient_cancel
    {n : ℕ} (hn : 2 ≤ n) {μ : ℝ} {u : E n → ℝ} (hu : IsSolution n μ u)
    {x : E n} (hx : x ∈ unitSphere n) :
    realHessian u x x (boundaryInverseDirection u μ x) + 2 * gradientNormSq u x =
      4 * boundarySlope u x := by
  let t := boundarySlope u x
  let σ := μ / t ^ (n - 1)
  let G := ‖horizontalGradient (boundarySlope u) x‖ ^ 2
  let d := fderiv ℝ (boundarySlope u) x x
  have ht : t ≠ 0 := ne_of_gt (hu.boundarySlope_pos hn hx)
  have hσ : σ ≠ 0 := div_ne_zero (ne_of_gt hu.1) (pow_ne_zero _ ht)
  have hD : fderiv ℝ (boundarySlope u) x
      (horizontalGradient (boundarySlope u) x) = G := by
    rw [← inner_horizontalGradient (boundarySlope u)
      (horizontalGradient_inner_normal _ hx) (horizontalGradient_inner_hopf _ hx),
      real_inner_self_eq_norm_sq]
  have hSlope := fderiv_boundarySlope
    (hu.2.1.contDiffAt (Metric.sphere_subset_closedBall hx)) (boundaryInverseDirection u μ x)
  rw [realHessian_symm (hu.2.1.contDiffAt (Metric.sphere_subset_closedBall hx)),
    sphere_fderiv_normal hu.2.1 hu.2.2.2.2 hx] at hSlope
  have hScalar : σ⁻¹ * (t * d - (1 / 2 : ℝ) * G) =
      (realHessian u x x (boundaryInverseDirection u μ x) + 2 * t * (σ⁻¹ * t)) / 2 := by
    simpa only [boundaryInverseDirection, map_smul, map_sub, smul_eq_mul,
      inner_sub_right, real_inner_smul_right, sphere_inner_self hx,
      horizontalGradient_inner_normal _ hx, mul_zero, mul_one, sub_zero,
      hD, t, σ, d] using hSlope
  have hSchur : d / 2 - G / (4 * t) = σ := hu.boundary_schur_complement hn hx
  rw [hu.gradientNormSq_on_sphere_schur hn hx]
  change realHessian u x x (boundaryInverseDirection u μ x) + 2 * (t ^ 2 / σ) = 4 * t
  field_simp [hσ] at hScalar ⊢
  field_simp [ht] at hSchur
  nlinarith [hScalar, hSchur]

/-- The remaining normal derivative is a genuine metric quadratic of t.
This identity is prior to using the differentiated PDE. -/
theorem IsSolution.fderiv_gradientNormSq_normal_eq_metric
    {n : ℕ} (hn : 2 ≤ n) {μ : ℝ} {u : E n → ℝ} (hu : IsSolution n μ u)
    {x : E n} (hx : x ∈ unitSphere n) :
    fderiv ℝ (gradientNormSq u) x x = 4 * boundarySlope u x -
      realMetricForm (boundarySlope u) x (boundaryInverseDirection u μ x)
        (boundaryInverseDirection u μ x) := by
  obtain ⟨U, hU, hKU, huU⟩ := hu.2.1
  have hxK := Metric.sphere_subset_closedBall hx
  have hq := hu.fderiv_gradientNormSq_eq_metricJet_closedBall hxK x
  rw [fderiv_realMetricForm_radial_eq_boundarySlope hU huU (hKU hxK),
    hu.inverseGradientVector_normSq_closedBall hxK,
    hu.inverseGradientVector_on_sphere hn hx] at hq
  have hc := hu.boundary_realHessian_inverseGradient_cancel hn hx
  linarith

/-- The complete ambient normal derivative, under exactly the original
solution assumptions. The PDE trace is taken in the open ball and extended
to the boundary before its use here. -/
theorem IsSolution.fderiv_gradientNormSq_normal
    {n : ℕ} (hn : 2 ≤ n) {μ : ℝ} {u : E n → ℝ} (hu : IsSolution n μ u)
    {x : E n} (hx : x ∈ unitSphere n) :
    fderiv ℝ (gradientNormSq u) x x =
      2 * ((n : ℝ) + 1) * boundarySlope u x +
      2 * boundarySlope u x ^ 2 * (boundarySlope u x - n) /
        (μ / boundarySlope u x ^ (n - 1)) +
      boundarySlope u x / (2 * (μ / boundarySlope u x ^ (n - 1))) *
        horizontalLaplacian (boundarySlope u) x +
      ((n : ℝ) - 1) / (2 * (μ / boundarySlope u x ^ (n - 1))) *
        ‖horizontalGradient (boundarySlope u) x‖ ^ 2 := by
  let t := boundarySlope u x
  let σ := μ / t ^ (n - 1)
  let G := ‖horizontalGradient (boundarySlope u) x‖ ^ 2
  let δ := horizontalLaplacian (boundarySlope u) x
  let d := fderiv ℝ (boundarySlope u) x x
  let M := realMetricForm (boundarySlope u) x (boundaryInverseDirection u μ x)
    (boundaryInverseDirection u μ x)
  have ht : t ≠ 0 := ne_of_gt (hu.boundarySlope_pos hn hx)
  have hσ : σ ≠ 0 := div_ne_zero (ne_of_gt hu.1) (pow_ne_zero _ ht)
  have hSchur : d / 2 - G / (4 * t) = σ := hu.boundary_schur_complement hn hx
  have hd : d = 2 * σ + G / (2 * t) := by
    field_simp [ht] at hSchur ⊢
    nlinarith [hSchur]
  have htrace := frozenHorizontalComplexTrace_self
    ((hu.2.1.boundarySlope).contDiffAt (Metric.sphere_subset_closedBall hx))
  have hL := hu.boundary_complexLaplacian_split hn hx (boundarySlope u)
  rw [hu.complexLaplacian_boundarySlope_closedBall (Metric.sphere_subset_closedBall hx),
    htrace] at hL
  change (n : ℝ) - t = (δ / 4 + ((n : ℝ) - 1) / 2 * d) / t +
    σ / (2 * t ^ 2) * M at hL
  rw [hd] at hL
  rw [hu.fderiv_gradientNormSq_normal_eq_metric hn hx]
  change 4 * t - M = 2 * ((n : ℝ) + 1) * t +
    2 * t ^ 2 * (t - n) / σ + t / (2 * σ) * δ + ((n : ℝ) - 1) / (2 * σ) * G
  field_simp [ht, hσ] at hL ⊢
  nlinarith [hL]

#print axioms IsSolution.fderiv_gradientNormSq_eq_metricJet_closedBall
#print axioms IsSolution.fderiv_gradientNormSq_normal

end KEBall
