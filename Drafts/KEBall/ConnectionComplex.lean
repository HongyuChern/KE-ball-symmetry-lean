import KEBall.MetricHessian
import KEBall.LocalMetric
import KEBall.EquationBasics
import PoincareLib.Geometry.Riemannian.Curvature.Euclidean

/-!
# The constructed Levi-Civita connection preserves the complex structure

Stage02 source draft: no current Lean kernel receipt.
The metric and connection are the actual objects used by the retained
Poincare library. Their compatibility with J is derived from Koszul's
formula and third derivatives of u. It is not a field supplied by a caller.
The final theorem constructs the objects from IsSolution on a neighbourhood.
-/

set_option autoImplicit false
set_option maxSynthPendingDepth 10
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped ContDiff Manifold Topology BigOperators

namespace KEBall

/-- Coordinate action of the fixed complex structure; independent of the
unreplayed scalar-Laplacian module. -/
theorem J_realDirection_eq_imag {n : ℕ} (i : Fin n) :
    J (realDirection i) = imagDirection i := by
  apply complexCoord_injective
  funext j
  simp [complexCoord_J, complexCoord_realDirection, complexCoord_imagDirection,
    mul_ite]

theorem J_imagDirection_eq_neg {n : ℕ} (i : Fin n) :
    J (imagDirection i) = -realDirection i := by
  rw [← J_realDirection_eq_imag, J_sq]

/-- The metric derivative at a point where the actual metric agrees locally
with the realification of the complex Hessian. -/
theorem metric_derivative_eq_third_average {n : ℕ}
    {g : PoincareMT.RiemannianMetric (2 * n) (E n)}
    {u : E n → ℝ} {U : Set (E n)} (hU : IsOpen U)
    (hu : ContDiffOn ℝ ∞ u U)
    (hg : ∀ y ∈ U, ∀ v w : E n, g.inner y v w = realMetricForm u y v w)
    {x : E n} (hx : x ∈ U) (a v w : E n) :
    fderiv ℝ (fun y => g.inner y v w) x a =
      (realThirdDerivative u x a v w +
        realThirdDerivative u x a (J v) (J w)) / 2 := by
  have heq : (fun y => g.inner y v w) =ᶠ[𝓝 x]
      (fun y => realMetricForm u y v w) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact hg y hy v w
  rw [heq.fderiv_eq]
  exact fderiv_realMetricForm hU hu hx a v w

/-- The full constant-frame Koszul expression, including every third-jet term. -/
theorem inner_connection_const_eq_third {n : ℕ}
    {g : PoincareMT.RiemannianMetric (2 * n) (E n)}
    (D : PoincareMT.LeviCivitaData g) {u : E n → ℝ} {U : Set (E n)}
    (hU : IsOpen U) (hu : ContDiffOn ℝ ∞ u U)
    (hg : ∀ y ∈ U, ∀ v w : E n, g.inner y v w = realMetricForm u y v w)
    {x : E n} (hx : x ∈ U) (v w z : E n) :
    g.inner x (D.connection (fun _ : E n => w) x v) z =
      (realThirdDerivative u x v w z +
       realThirdDerivative u x v (J w) (J z) +
       realThirdDerivative u x w (J v) (J z) -
       realThirdDerivative u x z (J v) (J w)) / 4 := by
  have huAt := hu.contDiffAt (hU.mem_nhds hx)
  have h := D.inner_connection_const x v w z
  simp only [metric_derivative_eq_third_average hU hu hg hx] at h
  simp only [realThirdDerivative_symm12 huAt,
    realThirdDerivative_symm23 hU hu hx] at h ⊢
  linarith

/-- Complex linearity in the vector being differentiated, in a constant frame. -/
theorem connection_const_J_right {n : ℕ}
    {g : PoincareMT.RiemannianMetric (2 * n) (E n)}
    (D : PoincareMT.LeviCivitaData g) {u : E n → ℝ} {U : Set (E n)}
    (hU : IsOpen U) (hu : ContDiffOn ℝ ∞ u U)
    (hg : ∀ y ∈ U, ∀ v w : E n, g.inner y v w = realMetricForm u y v w)
    {x : E n} (hx : x ∈ U) (v w : E n) :
    D.connection (fun _ : E n => J w) x v =
      J (D.connection (fun _ : E n => w) x v) := by
  have huAt := hu.contDiffAt (hU.mem_nhds hx)
  apply (g.inner_isInvertible x).injective
  ext z
  change g.inner x (D.connection (fun _ : E n => J w) x v) z =
    g.inner x (J (D.connection (fun _ : E n => w) x v)) z
  have hskew : g.inner x (J (D.connection (fun _ : E n => w) x v)) z =
      -g.inner x (D.connection (fun _ : E n => w) x v) (J z) := by
    rw [hg x hx, realMetricForm_J_skew huAt, ← hg x hx]
  rw [hskew]
  rw [inner_connection_const_eq_third D hU hu hg hx,
    inner_connection_const_eq_third D hU hu hg hx]
  simp only [J_sq, map_neg, neg_apply]
  simp only [realThirdDerivative_symm12 huAt,
    realThirdDerivative_symm23 hU hu hx]
  ring

/-- Symmetry in a constant frame is derived here directly from Koszul. -/
theorem connection_const_swap {n : ℕ}
    {g : PoincareMT.RiemannianMetric (2 * n) (E n)}
    (D : PoincareMT.LeviCivitaData g) {u : E n → ℝ} {U : Set (E n)}
    (hU : IsOpen U) (hu : ContDiffOn ℝ ∞ u U)
    (hg : ∀ y ∈ U, ∀ v w : E n, g.inner y v w = realMetricForm u y v w)
    {x : E n} (hx : x ∈ U) (v w : E n) :
    D.connection (fun _ : E n => w) x v =
      D.connection (fun _ : E n => v) x w := by
  have huAt := hu.contDiffAt (hU.mem_nhds hx)
  apply (g.inner_isInvertible x).injective
  ext z
  change g.inner x (D.connection (fun _ : E n => w) x v) z =
    g.inner x (D.connection (fun _ : E n => v) x w) z
  rw [inner_connection_const_eq_third D hU hu hg hx,
    inner_connection_const_eq_third D hU hu hg hx]
  simp only [realThirdDerivative_symm12 huAt,
    realThirdDerivative_symm23 hU hu hx]
  ring

/-- Complex linearity in the differentiating direction for constant fields. -/
theorem connection_const_J_left {n : ℕ}
    {g : PoincareMT.RiemannianMetric (2 * n) (E n)}
    (D : PoincareMT.LeviCivitaData g) {u : E n → ℝ} {U : Set (E n)}
    (hU : IsOpen U) (hu : ContDiffOn ℝ ∞ u U)
    (hg : ∀ y ∈ U, ∀ v w : E n, g.inner y v w = realMetricForm u y v w)
    {x : E n} (hx : x ∈ U) (v w : E n) :
    D.connection (fun _ : E n => w) x (J v) =
      J (D.connection (fun _ : E n => w) x v) := by
  rw [connection_const_swap D hU hu hg hx (J v) w,
    connection_const_J_right D hU hu hg hx w v,
    connection_const_swap D hU hu hg hx w v]

/-- Parallelness of J on actual differentiable fields, not just constant ones. -/
theorem connection_J_field {n : ℕ}
    {g : PoincareMT.RiemannianMetric (2 * n) (E n)}
    (D : PoincareMT.LeviCivitaData g) {u : E n → ℝ} {U : Set (E n)}
    (hU : IsOpen U) (hu : ContDiffOn ℝ ∞ u U)
    (hg : ∀ y ∈ U, ∀ v w : E n, g.inner y v w = realMetricForm u y v w)
    {x : E n} (hx : x ∈ U) {Y : E n → E n}
    (hY : DifferentiableAt ℝ Y x) (v : E n) :
    D.connection (fun y => J (Y y)) x v = J (D.connection Y x v) := by
  have hJY : DifferentiableAt ℝ (fun y => J (Y y)) x := by
    simpa only [Function.comp_def, JCLM_apply] using (JCLM n).differentiableAt.comp x hY
  have hd : fderiv ℝ (fun y => J (Y y)) x v =
      J (fderiv ℝ Y x v) := by
    have h := (JCLM n).hasFDerivAt.comp x hY.hasFDerivAt
    have h' : HasFDerivAt (fun y => J (Y y))
        ((JCLM n).comp (fderiv ℝ Y x)) x := by
      simpa only [Function.comp_def, JCLM_apply] using h
    rw [h'.fderiv]
    simp only [ContinuousLinearMap.comp_apply, JCLM_apply]
  have hsumY : (D.connection Y x v : E n) =
      fderiv ℝ Y x v + D.euclideanConnection v (Y x) x := by
    exact D.connection_eq_fderiv_add hY v
  have hsumJY : (D.connection (fun y => J (Y y)) x v : E n) =
      fderiv ℝ (fun y => J (Y y)) x v +
        D.euclideanConnection v (J (Y x)) x := by
    exact D.connection_eq_fderiv_add hJY v
  have hconstJ : D.euclideanConnection v (J (Y x)) x =
      J (D.euclideanConnection v (Y x) x) := by
    exact connection_const_J_right D hU hu hg hx v (Y x)
  rw [hsumJY, hsumY, hd]
  rw [hconstJ]
  simpa only [JCLM_apply] using
    ((JCLM n).map_add (fderiv ℝ Y x v) (D.euclideanConnection v (Y x) x)).symm

/-- A caller supplies only the original solution and an interior point. -/
theorem IsSolution.exists_local_parallel_complex_structure {n : ℕ} {μ : ℝ}
    {u : E n → ℝ} (hu : IsSolution n μ u) {p : E n} (hp : p ∈ unitBall n) :
    ∃ (g : PoincareMT.RiemannianMetric (2 * n) (E n))
      (D : PoincareMT.LeviCivitaData g) (V : Set (E n)),
      IsOpen V ∧ p ∈ V ∧ V ⊆ unitBall n ∧
      (∀ x ∈ V, ∀ v w : E n, g.inner x v w = realMetricForm u x v w) ∧
      (∀ x ∈ V, ∀ Y : E n → E n, DifferentiableAt ℝ Y x →
        ∀ v : E n, D.connection (fun y => J (Y y)) x v =
          J (D.connection Y x v)) := by
  obtain ⟨g, D, V, hV, hpV, hVB, hg⟩ := hu.exists_local_metric hp
  refine ⟨g, D, V, hV, hpV, hVB, hg, ?_⟩
  intro x hx Y hY v
  exact connection_J_field D hV (hu.contDiffOn_ball.mono hVB) hg hx hY v

end KEBall
