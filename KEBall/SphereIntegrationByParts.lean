import KEBall.SphereDifferential
import KEBall.SphereDivergence

/-!
# Horizontal integration by parts for the actual normalized sphere measure

The proof applies the genuine sphere divergence theorem to the globally
radially tangent polynomial projection field. Smooth functions defined
only near the closed ball are treated using the proved compact extension,
with equality of actual first and second derivatives on the sphere.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped ContDiff Topology BigOperators RealInnerProductSpace

namespace KEBall

theorem horizontalGradient_continuous_sphere {n : ℕ} {h : E n → ℝ}
    (hh : ContDiff ℝ ∞ h) : Continuous (fun x : Sphere n => horizontalGradient h x.1) := by
  have hc : Continuous (fun x : Sphere n => scaledHorizontalGradient h x.1) :=
    (scaledHorizontalGradient_contDiff hh).continuous.comp continuous_subtype_val
  exact hc.congr (fun x => scaledHorizontalGradient_on_sphere h x.2)

theorem horizontalLaplacian_continuous_sphere {n : ℕ} {h : E n → ℝ}
    (hh : ContDiff ℝ ∞ h) : Continuous (fun x : Sphere n => horizontalLaplacian h x.1) := by
  have hc : Continuous (fun x : Sphere n =>
      euclideanDivergence (scaledHorizontalGradient h) x.1) := (euclideanDivergence_continuous
    ((scaledHorizontalGradient_contDiff hh).of_le (by simp))).comp continuous_subtype_val
  exact hc.congr (fun x => scaledHorizontalGradient_divergence_on_sphere hh.contDiffAt x.2)

theorem integral_horizontalLaplacian_mul {n : ℕ} (hn : 0 < n)
    {a b : E n → ℝ} (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) :
    (∫ x : Sphere n, a x.1 * horizontalLaplacian b x.1 ∂sphere0 n) =
      - ∫ x : Sphere n,
          inner ℝ (horizontalGradient a x.1) (horizontalGradient b x.1) ∂sphere0 n := by
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  have hV : ContDiff ℝ 1 (fun y => a y • scaledHorizontalGradient b y) :=
    (ha.smul (scaledHorizontalGradient_contDiff hb)).of_le (by simp)
  have ht : ∀ y, inner ℝ y (a y • scaledHorizontalGradient b y) = 0 := by
    intro y
    rw [real_inner_smul_right, scaledHorizontalGradient_tangent, mul_zero]
  have hzero := integral_sphere0_divergence_eq_zero hn hV ht
  have he (x : Sphere n) :
      euclideanDivergence (fun y => a y • scaledHorizontalGradient b y) x.1 =
        a x.1 * horizontalLaplacian b x.1 +
          inner ℝ (horizontalGradient a x.1) (horizontalGradient b x.1) := by
    rw [euclideanDivergence_smul (ha.differentiable (by simp) x.1)
      ((scaledHorizontalGradient_contDiff hb).differentiable (by simp) x.1),
      scaledHorizontalGradient_divergence_on_sphere hb.contDiffAt x.2,
      scaledHorizontalGradient_on_sphere b x.2,
      ← inner_horizontalGradient a (horizontalGradient_inner_normal b x.2)
        (horizontalGradient_inner_hopf b x.2)]
  have hc1 : Continuous (fun x : Sphere n => a x.1 * horizontalLaplacian b x.1) :=
    (ha.continuous.comp continuous_subtype_val).mul
    (horizontalLaplacian_continuous_sphere hb)
  have hc2 : Continuous (fun x : Sphere n =>
      inner ℝ (horizontalGradient a x.1) (horizontalGradient b x.1)) :=
    (horizontalGradient_continuous_sphere ha).inner
    (horizontalGradient_continuous_sphere hb)
  have hi1 := hc1.integrable_of_hasCompactSupport (μ := sphere0 n) (HasCompactSupport.of_compactSpace _)
  have hi2 := hc2.integrable_of_hasCompactSupport (μ := sphere0 n) (HasCompactSupport.of_compactSpace _)
  have hz : (∫ x : Sphere n,
      a x.1 * horizontalLaplacian b x.1 +
        inner ℝ (horizontalGradient a x.1) (horizontalGradient b x.1) ∂sphere0 n) = 0 := by
    calc
      _ = ∫ x : Sphere n,
          euclideanDivergence (fun y => a y • scaledHorizontalGradient b y) x.1 ∂sphere0 n :=
        integral_congr_ae (Eventually.of_forall (fun x => (he x).symm))
      _ = 0 := hzero
  rw [integral_add hi1 hi2] at hz
  linarith

theorem horizontalGradient_eq_of_eventuallyEq {n : ℕ} {a b : E n → ℝ} {x : E n}
    (he : a =ᶠ[𝓝 x] b) : horizontalGradient a x = horizontalGradient b x := by
  simp only [horizontalGradient, euclideanGradient, he.fderiv_eq]

theorem horizontalLaplacian_eq_of_eventuallyEq {n : ℕ} {a b : E n → ℝ} {x : E n}
    (he : a =ᶠ[𝓝 x] b) : horizontalLaplacian a x = horizontalLaplacian b x := by
  have hD : fderiv ℝ (fderiv ℝ a) x = fderiv ℝ (fderiv ℝ b) x := he.fderiv.fderiv_eq
  simp only [horizontalLaplacian, realHessian, he.fderiv_eq, hD]

/-- The true horizontal Green identity with only original-neighborhood
smoothness. Neither test function is required to vanish on the sphere. -/
theorem integral_horizontalLaplacian_mul_of_smoothNear {n : ℕ} (hn : 0 < n)
    {a b : E n → ℝ} (ha : SmoothNear (closedUnitBall n) a)
    (hb : SmoothNear (closedUnitBall n) b) :
    (∫ x : Sphere n, a x.1 * horizontalLaplacian b x.1 ∂sphere0 n) =
      - ∫ x : Sphere n,
          inner ℝ (horizontalGradient a x.1) (horizontalGradient b x.1) ∂sphere0 n := by
  obtain ⟨U, hU, hKU, haU⟩ := ha
  obtain ⟨V, hV, hKV, hbV⟩ := hb
  obtain ⟨A, _, hA, hAa⟩ := exists_contDiff_extension_closedUnitBall (⊤ : ℕ∞) hU hKU haU
  obtain ⟨B, _, hB, hBb⟩ := exists_contDiff_extension_closedUnitBall (⊤ : ℕ∞) hV hKV hbV
  have heA (x : Sphere n) := hAa x.1 (Metric.sphere_subset_closedBall x.2)
  have heB (x : Sphere n) := hBb x.1 (Metric.sphere_subset_closedBall x.2)
  calc
    _ = ∫ x : Sphere n, A x.1 * horizontalLaplacian B x.1 ∂sphere0 n := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [(heA x).eq_of_nhds, horizontalLaplacian_eq_of_eventuallyEq (heB x)]
    _ = - ∫ x : Sphere n,
          inner ℝ (horizontalGradient A x.1) (horizontalGradient B x.1) ∂sphere0 n :=
      integral_horizontalLaplacian_mul hn hA hB
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [] with x
      rw [horizontalGradient_eq_of_eventuallyEq (heA x),
        horizontalGradient_eq_of_eventuallyEq (heB x)]

#print axioms integral_horizontalLaplacian_mul
#print axioms integral_horizontalLaplacian_mul_of_smoothNear

end KEBall
