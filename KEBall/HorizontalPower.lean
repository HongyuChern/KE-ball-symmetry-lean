import KEBall.SphereIntegrationByParts
import KEBall.Pohozaev

/-!
# The exact horizontal power identity, including complex dimension two

The coefficient is represented as `t^(n-1)/t^2`; hence the dimension-two
weight is the genuine reciprocal slope, rather than a truncated natural
power. Positive sphere slope and compactness justify every integral.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped ContDiff Topology BigOperators RealInnerProductSpace

namespace KEBall

theorem euclideanGradient_pow {n : ℕ} {h : E n → ℝ} {x : E n}
    (hh : DifferentiableAt ℝ h x) (k : ℕ) :
    euclideanGradient (fun y => h y ^ k) x =
      ((k : ℝ) * h x ^ (k - 1)) • euclideanGradient h x := by
  have hd := (hh.hasFDerivAt.pow k).fderiv
  simp only [euclideanGradient, hd, smul_apply, smul_eq_mul, Finset.smul_sum,
    smul_smul, nsmul_eq_mul]

theorem horizontalGradient_pow {n : ℕ} {h : E n → ℝ} {x : E n}
    (hh : DifferentiableAt ℝ h x) (k : ℕ) :
    horizontalGradient (fun y => h y ^ k) x =
      ((k : ℝ) * h x ^ (k - 1)) • horizontalGradient h x := by
  simp only [horizontalGradient, euclideanGradient_pow hh k,
    real_inner_smul_left, smul_sub, smul_smul]

theorem SmoothNear.pow {n : ℕ} {h : E n → ℝ} {K : Set (E n)}
    (hh : SmoothNear K h) (k : ℕ) : SmoothNear K (fun x => h x ^ k) := by
  obtain ⟨U, hU, hKU, hhu⟩ := hh
  exact ⟨U, hU, hKU, hhu.pow k⟩

theorem SmoothNear.horizontalGradient_continuous_sphere {n : ℕ} {h : E n → ℝ}
    (hh : SmoothNear (closedUnitBall n) h) :
    Continuous (fun x : Sphere n => horizontalGradient h x.1) := by
  obtain ⟨U, hU, hKU, hhU⟩ := hh
  obtain ⟨H, _, hH, hHh⟩ := exists_contDiff_extension_closedUnitBall (⊤ : ℕ∞) hU hKU hhU
  exact (KEBall.horizontalGradient_continuous_sphere hH).congr (fun x =>
    horizontalGradient_eq_of_eventuallyEq (hHh x.1 (Metric.sphere_subset_closedBall x.2)))

theorem SmoothNear.horizontalLaplacian_continuous_sphere {n : ℕ} {h : E n → ℝ}
    (hh : SmoothNear (closedUnitBall n) h) :
    Continuous (fun x : Sphere n => horizontalLaplacian h x.1) := by
  obtain ⟨U, hU, hKU, hhU⟩ := hh
  obtain ⟨H, _, hH, hHh⟩ := exists_contDiff_extension_closedUnitBall (⊤ : ℕ∞) hU hKU hhU
  exact (KEBall.horizontalLaplacian_continuous_sphere hH).congr (fun x =>
    horizontalLaplacian_eq_of_eventuallyEq (hHh x.1 (Metric.sphere_subset_closedBall x.2)))

theorem SmoothNear.boundarySlope {n : ℕ} {u : E n → ℝ} {K : Set (E n)}
    (hu : SmoothNear K u) : SmoothNear K (KEBall.boundarySlope u) := by
  obtain ⟨U, hU, hKU, huU⟩ := hu
  exact ⟨U, hU, hKU, boundarySlope_contDiffOn hU huU⟩

theorem integral_horizontalLaplacian_power {n : ℕ} (hn : 0 < n)
    {h : E n → ℝ} (hh : SmoothNear (closedUnitBall n) h) (k : ℕ) :
    (∫ x : Sphere n, h x.1 ^ k * horizontalLaplacian h x.1 ∂sphere0 n) =
      -(k : ℝ) * ∫ x : Sphere n,
        h x.1 ^ (k - 1) * ‖horizontalGradient h x.1‖ ^ 2 ∂sphere0 n := by
  rw [integral_horizontalLaplacian_mul_of_smoothNear hn (hh.pow k) hh]
  have he (x : Sphere n) :
      inner ℝ (horizontalGradient (fun y => h y ^ k) x.1) (horizontalGradient h x.1) =
        (k : ℝ) * (h x.1 ^ (k - 1) * ‖horizontalGradient h x.1‖ ^ 2) := by
    rw [horizontalGradient_pow
      ((hh.contDiffAt (Metric.sphere_subset_closedBall x.2)).differentiableAt (by simp)),
      real_inner_smul_left, real_inner_self_eq_norm_sq]
    ring
  simp_rw [he]
  rw [integral_const_mul, neg_mul]

theorem IsSolution.horizontal_power_identity {n : ℕ} (hn : 2 ≤ n) {μ : ℝ}
    {u : E n → ℝ} (hu : IsSolution n μ u) :
    (∫ x : Sphere n, boundarySlope u x.1 ^ (n - 2) *
        horizontalLaplacian (boundarySlope u) x.1 ∂sphere0 n) =
      -(n - 2 : ℝ) * ∫ x : Sphere n,
        (boundarySlope u x.1 ^ (n - 1) / boundarySlope u x.1 ^ 2) *
          ‖horizontalGradient (boundarySlope u) x.1‖ ^ 2 ∂sphere0 n := by
  have hi := integral_horizontalLaplacian_power (by omega : 0 < n)
    hu.2.1.boundarySlope (n - 2)
  rw [hi]
  by_cases htwo : n = 2
  · subst n
    norm_num
  · have hthree : 3 ≤ n := by omega
    have hk : ((n - 2 : ℕ) : ℝ) = (n - 2 : ℝ) := by
      rw [Nat.cast_sub (by omega : 2 ≤ n)]
      norm_num
    rw [hk]
    congr 1
    apply integral_congr_ae
    filter_upwards [] with x
    have ht := ne_of_gt (hu.boundarySlope_pos hn x.2)
    have hp : n - 1 = (n - 2 - 1) + 2 := by omega
    rw [hp, pow_add, mul_div_cancel_right₀ _ (pow_ne_zero _ ht)]

#print axioms integral_horizontalLaplacian_power
#print axioms IsSolution.horizontal_power_identity

end KEBall
