import KEBall.EulerLaplacian
import KEBall.SecondGreen
import KEBall.BoundaryMass

/-!
# The exact Pohozaev identity for the actual solution

The proof combines the second Green identity for `u` and `Ru` with
ordinary divergence of the local vector field `u μ exp(-u) x`.
All integral linearity uses integrability proved from smoothness near the
compact closed ball. No global integrability or moving-domain derivative
is assumed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped ContDiff Topology BigOperators

namespace KEBall

theorem integrableOn_unitBall_of_contDiffOn {n : ℕ} {U : Set (E n)}
    {f : E n → ℝ} (hsub : closedUnitBall n ⊆ U) (hf : ContDiffOn ℝ ∞ f U) :
    IntegrableOn f (unitBall n) (volume0 n) := by
  have h := (hf.continuousOn.mono hsub).integrableOn_compact
    (μ := (volume : Measure (E n))) (isCompact_closedBall (0 : E n) 1)
  have hb := h.mono_set (Metric.ball_subset_closedBall : unitBall n ⊆ closedUnitBall n)
  change Integrable f ((volume0 n).restrict (unitBall n))
  rw [volume0, Measure.restrict_smul]
  exact hb.smul_measure ENNReal.ofReal_ne_top

theorem boundarySlope_contDiffOn {n : ℕ} {u : E n → ℝ} {U : Set (E n)}
    (hU : IsOpen U) (hu : ContDiffOn ℝ ∞ u U) :
    ContDiffOn ℝ ∞ (boundarySlope u) U := by
  change ContDiffOn ℝ ∞ (fun x => eulerDerivative u x * (2 : ℝ)⁻¹) U
  exact (eulerDerivative_contDiffOn hU hu).mul contDiffOn_const

theorem SmoothNear.boundarySlope_continuous_sphere {n : ℕ} {u : E n → ℝ}
    (hu : SmoothNear (closedUnitBall n) u) :
    Continuous (fun x : Sphere n => boundarySlope u x.1) := by
  obtain ⟨U, hU, hKU, huU⟩ := hu
  exact (boundarySlope_contDiffOn hU huU).continuousOn.comp_continuous
    continuous_subtype_val (fun x => hKU (Metric.sphere_subset_closedBall x.2))

theorem IsSolution.weightedEulerFlux_density {n : ℕ} (hn : 0 < n) {μ : ℝ}
    {u : E n → ℝ} (hu : IsSolution n μ u) :
    (∫ x in unitBall n, u x * eulerDerivative u x * equationDensity μ u x ∂volume0 n) =
      (2 * n : ℝ) * (∫ x in unitBall n, u x * equationDensity μ u x ∂volume0 n) +
        ∫ x in unitBall n, eulerDerivative u x * equationDensity μ u x ∂volume0 n := by
  obtain ⟨U, hU, hKU, huU⟩ := hu.2.1
  have hfU := equationDensity_contDiffOn μ huU
  have hRuU := eulerDerivative_contDiffOn hU huU
  have huf := integrableOn_unitBall_of_contDiffOn hKU (huU.mul hfU)
  have hRuf := integrableOn_unitBall_of_contDiffOn hKU (hRuU.mul hfU)
  have huRuf := integrableOn_unitBall_of_contDiffOn hKU ((huU.mul hRuU).mul hfU)
  have hV : ContDiffOn ℝ 1 (fun x : E n => (u x * equationDensity μ u x) • x) U :=
    ((huU.mul hfU).smul contDiffOn_id).of_le (by simp)
  have hG := integral_unitBall_divergence_normalized_of_contDiffOn hn hU hKU hV
  have hdiv (x : E n) (hx : x ∈ unitBall n) :
      euclideanDivergence (fun y : E n => (u y * equationDensity μ u y) • y) x =
        (2 * n : ℝ) * (u x * equationDensity μ u x) +
          eulerDerivative u x * equationDensity μ u x -
            u x * eulerDerivative u x * equationDensity μ u x := by
    have hxU := hKU (Metric.ball_subset_closedBall hx)
    have hud := (huU.contDiffAt (hU.mem_nhds hxU)).differentiableAt (by simp)
    have hfd := (hfU.contDiffAt (hU.mem_nhds hxU)).differentiableAt (by simp)
    rw [euclideanDivergence_scalar_euler (hud.fun_mul hfd), fderiv_fun_mul hud hfd]
    simp only [add_apply, smul_apply, smul_eq_mul]
    rw [eulerDerivative_equationDensity μ hud]
    change (2 * n : ℝ) * (u x * equationDensity μ u x) +
      (u x * -(eulerDerivative u x * equationDensity μ u x) +
        equationDensity μ u x * eulerDerivative u x) = _
    ring
  have hvol : (∫ x in unitBall n,
      euclideanDivergence (fun y : E n => (u y * equationDensity μ u y) • y) x ∂volume0 n) =
      (2 * n : ℝ) * (∫ x in unitBall n, u x * equationDensity μ u x ∂volume0 n) +
        (∫ x in unitBall n, eulerDerivative u x * equationDensity μ u x ∂volume0 n) -
          ∫ x in unitBall n, u x * eulerDerivative u x * equationDensity μ u x ∂volume0 n := by
    calc
      _ = ∫ x in unitBall n,
          ((2 * n : ℝ) * (u x * equationDensity μ u x) +
            eulerDerivative u x * equationDensity μ u x -
              u x * eulerDerivative u x * equationDensity μ u x) ∂volume0 n := by
        apply setIntegral_congr_fun Metric.isOpen_ball.measurableSet
        exact hdiv
      _ = _ := by
        rw [integral_sub
          (f := fun x => (2 * n : ℝ) * (u x * equationDensity μ u x) +
            eulerDerivative u x * equationDensity μ u x)
          (((huf.const_mul (2 * n : ℝ)).add hRuf)) huRuf,
          integral_add (huf.const_mul (2 * n : ℝ)) hRuf, integral_const_mul]
  have hsurf : (∫ x : Sphere n,
      inner ℝ x.1 ((u x.1 * equationDensity μ u x.1) • x.1) ∂sphere0 n) = 0 := by
    calc
      _ = ∫ x : Sphere n, (0 : ℝ) ∂sphere0 n := by
        apply integral_congr_ae
        apply Eventually.of_forall
        intro x
        simp only [hu.2.2.2.2 x.1 x.2, zero_mul, zero_smul, inner_zero_right]
      _ = 0 := by simp
  rw [hvol, hsurf, mul_zero] at hG
  linarith

theorem IsSolution.pohozaev_euler_density {n : ℕ} (hn : 2 ≤ n) {μ : ℝ}
    {u : E n → ℝ} (hu : IsSolution n μ u) :
    (n + 1 : ℝ) * (∫ x in unitBall n,
      eulerDerivative u x * equationDensity μ u x ∂volume0 n) =
      (2 * n : ℝ) * ∫ x : Sphere n, boundarySlope u x.1 ^ (n + 1) ∂sphere0 n := by
  have hG := hu.secondGreen hn hu.2.1 hu.2.1.eulerDerivative
  obtain ⟨U, hU, hKU, huU⟩ := hu.2.1
  have hfU := equationDensity_contDiffOn μ huU
  have hRuU := eulerDerivative_contDiffOn hU huU
  have huf := integrableOn_unitBall_of_contDiffOn hKU (huU.mul hfU)
  have hRuf := integrableOn_unitBall_of_contDiffOn hKU (hRuU.mul hfU)
  have huRuf := integrableOn_unitBall_of_contDiffOn hKU ((huU.mul hRuU).mul hfU)
  have hleft : (∫ x in unitBall n,
      (u x * complexLaplacian u (eulerDerivative u) x -
        eulerDerivative u x * complexLaplacian u u x) * (complexHessian u x).det.re ∂volume0 n) =
      (2 * n : ℝ) * (∫ x in unitBall n, u x * equationDensity μ u x ∂volume0 n) -
        (∫ x in unitBall n, u x * eulerDerivative u x * equationDensity μ u x ∂volume0 n) -
          (n : ℝ) * ∫ x in unitBall n, eulerDerivative u x * equationDensity μ u x ∂volume0 n := by
    calc
      _ = ∫ x in unitBall n,
          ((2 * n : ℝ) * (u x * equationDensity μ u x) -
            u x * eulerDerivative u x * equationDensity μ u x -
              (n : ℝ) * (eulerDerivative u x * equationDensity μ u x)) ∂volume0 n := by
        apply setIntegral_congr_fun Metric.isOpen_ball.measurableSet
        intro x hx
        dsimp only
        rw [hu.complexLaplacian_eulerDerivative hx,
          hu.complexLaplacian_self (Metric.ball_subset_closedBall hx), hu.2.2.2.1 x hx]
        simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
          sub_zero, equationDensity]
        ring
      _ = _ := by
        rw [integral_sub
          (f := fun x => (2 * n : ℝ) * (u x * equationDensity μ u x) -
            u x * eulerDerivative u x * equationDensity μ u x)
          ((huf.const_mul (2 * n : ℝ)).sub huRuf) (hRuf.const_mul (n : ℝ)),
          integral_sub (huf.const_mul (2 * n : ℝ)) huRuf,
          integral_const_mul, integral_const_mul]
  have hright : (∫ x : Sphere n, boundarySlope u x.1 ^ (n - 1) *
      (u x.1 * conormalDerivative u (eulerDerivative u) x.1 -
        eulerDerivative u x.1 * conormalDerivative u u x.1) ∂sphere0 n) =
      -4 * ∫ x : Sphere n, boundarySlope u x.1 ^ (n + 1) ∂sphere0 n := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    apply Eventually.of_forall
    intro x
    dsimp only
    rw [hu.2.2.2.2 x.1 x.2, sphere_conormal_self hu.2.1 hu.2.2.2.2 x.2]
    have he : eulerDerivative u x.1 = 2 * boundarySlope u x.1 := by
      unfold eulerDerivative boundarySlope
      ring
    rw [he, zero_mul, zero_sub]
    calc
      _ = -4 * (boundarySlope u x.1 ^ (n - 1) * boundarySlope u x.1 ^ 2) := by ring
      _ = _ := by
        rw [← pow_add]
        congr 2
        omega
  rw [hleft, hright] at hG
  have hE := hu.weightedEulerFlux_density (by omega)
  nlinarith [hG, hE]

theorem IsSolution.pohozaev_identity {n : ℕ} (hn : 2 ≤ n) {μ : ℝ}
    {u : E n → ℝ} (hu : IsSolution n μ u) :
    (∫ x : Sphere n, boundaryPolynomial n (boundarySlope u x.1) ∂sphere0 n) = μ := by
  letI : NeZero n := ⟨by omega⟩
  have hP := hu.pohozaev_euler_density hn
  have hE := hu.eulerFlux_density (by omega)
  have hmass : (∫ x in unitBall n, equationDensity μ u x ∂volume0 n) =
      ∫ x : Sphere n, boundarySlope u x.1 ^ n ∂sphere0 n := by
    rw [← hu.mass_identity hn]
    apply setIntegral_congr_fun Metric.isOpen_ball.measurableSet
    intro x hx
    dsimp only
    rw [hu.2.2.2.1 x hx]
    simp only [equationDensity, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
  rw [hmass] at hE
  have hc := hu.2.1.boundarySlope_continuous_sphere
  have hi (k : ℕ) : Integrable (fun x : Sphere n => boundarySlope u x.1 ^ k) (sphere0 n) :=
    (hc.pow k).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hF : (∫ x : Sphere n, boundaryPolynomial n (boundarySlope u x.1) ∂sphere0 n) =
      (∫ x : Sphere n, boundarySlope u x.1 ^ n ∂sphere0 n) -
        (n + 1 : ℝ)⁻¹ * ∫ x : Sphere n, boundarySlope u x.1 ^ (n + 1) ∂sphere0 n := by
    calc
      _ = ∫ x : Sphere n, (boundarySlope u x.1 ^ n -
          (n + 1 : ℝ)⁻¹ * boundarySlope u x.1 ^ (n + 1)) ∂sphere0 n := by
        apply integral_congr_ae
        apply Eventually.of_forall
        intro x
        dsimp only
        unfold boundaryPolynomial
        rw [pow_succ]
        ring
      _ = _ := by rw [integral_sub (hi n) ((hi (n + 1)).const_mul _), integral_const_mul]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hkR : (n + 1 : ℝ) ≠ 0 := by positivity
  have hmoment : (n + 1 : ℝ) *
      ((∫ x : Sphere n, boundarySlope u x.1 ^ n ∂sphere0 n) - μ) =
        ∫ x : Sphere n, boundarySlope u x.1 ^ (n + 1) ∂sphere0 n := by
    apply mul_left_cancel₀ (show (2 * n : ℝ) ≠ 0 by exact mul_ne_zero (by norm_num) hnR)
    nlinarith [hP, hE]
  rw [hF, ← hmoment]
  field_simp
  ring

/-- All three exact identities of manuscript Lemma 2.1, discharged from the
original `IsSolution` and actual probability normalizations. -/
theorem boundaryIdentities : BoundaryIdentitiesStatement := by
  intro n hn μ u hu
  exact ⟨hu.mass_identity hn, hu.pohozaev_identity hn,
    fun h hh => hu.conormalGreen hn hh⟩

#print axioms IsSolution.weightedEulerFlux_density
#print axioms IsSolution.pohozaev_euler_density
#print axioms IsSolution.pohozaev_identity
#print axioms boundaryIdentities

end KEBall
