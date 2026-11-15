import KEBall.DirichletAffineHolderRegularity
import KEBall.DirichletNonlinearC3Jets

/-!
# Retaining the Holder bound of the third directional jet

The derivative-limit theorem supplies both differentiability and the
Holder bound of the derivative.  Neither part is discarded when the
spatial normalization is inverted.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Filter Metric Set
open DifferentialGeometry.Analysis.Schauder
open scoped ComplexOrder Matrix.Norms.Elementwise NNReal Topology

namespace KEBall

theorem dirichlet_C1_holder_normalized_directional_hessian_of_schauder_bound {n : ℕ}
    (u : BoundedContinuousFunction (E n) ℝ)
    (Du : BoundedContinuousFunction (E n) (E n →L[ℝ] ℝ))
    (Hu : BoundedContinuousFunction (E n) (E n →L[ℝ] E n →L[ℝ] ℝ))
    (hu : ∀ x, HasFDerivAt (u : E n → ℝ) (Du x) x)
    (hDu : ∀ x, HasFDerivAt (Du : E n → E n →L[ℝ] ℝ) (Hu x) x)
    {KH α C : ℝ≥0} (hα : 0 < α)
    (hH : HolderWith KH α (Hu : E n → E n →L[ℝ] E n →L[ℝ] ℝ))
    (p v : E n) (r : ℝ≥0) {h : ℕ → ℝ}
    (hh : ∀ i, h i ≠ 0) (hlim : Tendsto h atTop (𝓝 0))
    (hGauge : ∀ i, eContDiffHolderGaugeOn 2 α (closedBall (0 : E n) (1 / 2))
      (dirichletBoundedScaledJet (dirichletBoundedDifferenceQuotient u v (h i)) p r 0 : E n → ℝ) ≤ C) :
    ContDiffOn ℝ 1 (fun x => (r : ℝ) • Hu (p + (r : ℝ) • x) v) (ball (0 : E n) (1 / 4)) ∧
      HolderOnWith C α (fderiv ℝ (fun x => (r : ℝ) • Hu (p + (r : ℝ) • x) v))
        (ball (0 : E n) (1 / 4)) := by
  let q₁ (i : ℕ) := dirichletBoundedScaledJet (dirichletBoundedDifferenceQuotient Du v (h i)) p r 1
  let q₂ (i : ℕ) := dirichletBoundedScaledJet (dirichletBoundedDifferenceQuotient Hu v (h i)) p r 2
  have hq₀ (i : ℕ) (x : E n) :
      HasFDerivAt (dirichletBoundedScaledJet (dirichletBoundedDifferenceQuotient u v (h i)) p r 0 : E n → ℝ)
        (q₁ i x) x :=
    hasFDerivAt_dirichletBoundedScaledJet (hasFDerivAt_dirichletBoundedDifferenceQuotient hu v (h i)) p r 0 x
  have hq₁ (i : ℕ) (x : E n) : HasFDerivAt (q₁ i : E n → E n →L[ℝ] ℝ) (q₂ i x) x :=
    hasFDerivAt_dirichletBoundedScaledJet (hasFDerivAt_dirichletBoundedDifferenceQuotient hDu v (h i)) p r 1 x
  have hqH (i : ℕ) : HolderOnWith C α (fderiv ℝ (q₁ i : E n → E n →L[ℝ] ℝ))
      (ball (0 : E n) (1 / 2)) := by
    have he : fderiv ℝ (q₁ i : E n → E n →L[ℝ] ℝ) = q₂ i := funext fun x => (hq₁ i x).fderiv
    rw [he]
    exact (dirichlet_actual_second_jet_holderOnWith_of_schauder_gauge
      (hq₀ i) (hq₁ i) (hGauge i)).mono ball_subset_closedBall
  have ht : TendstoUniformlyOn (fun i => (q₁ i : E n → E n →L[ℝ] ℝ))
      (fun x => (r : ℝ) ^ 1 • Hu (p + (r : ℝ) • x) v) atTop (ball (0 : E n) (1 / 2)) :=
    (tendstoUniformly_dirichlet_scaled_quotient hDu hH hα p v r 1 hh hlim).tendstoUniformlyOn
  simpa only [pow_one] using!
    dirichlet_C1_limit_of_uniform_holder_derivatives (l := atTop)
      (f := fun i => (q₁ i : E n → E n →L[ℝ] ℝ))
      (g := fun x => (r : ℝ) ^ 1 • Hu (p + (r : ℝ) • x) v)
      (by norm_num : (1 / 4 : ℝ) < 1 / 2) hα
      (fun i x _ => (hq₁ i x).differentiableAt) hqH ht

theorem exists_dirichlet_local_holder_directional_third_jet {n : ℕ} (hn : 0 < n)
    (u : BoundedContinuousFunction (E n) ℝ)
    (Du : BoundedContinuousFunction (E n) (E n →L[ℝ] ℝ))
    (Hu : BoundedContinuousFunction (E n) (E n →L[ℝ] E n →L[ℝ] ℝ))
    (f : BoundedContinuousFunction (E n) ℝ)
    (Df : BoundedContinuousFunction (E n) (E n →L[ℝ] ℝ))
    (hu : ∀ x, HasFDerivAt (u : E n → ℝ) (Du x) x)
    (hDu : ∀ x, HasFDerivAt (Du : E n → E n →L[ℝ] ℝ) (Hu x) x)
    (hf : ∀ x, HasFDerivAt (f : E n → ℝ) (Df x) x)
    {KDu KH KDf α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1)
    (hDuH : HolderWith KDu α (Du : E n → E n →L[ℝ] ℝ))
    (hHH : HolderWith KH α (Hu : E n → E n →L[ℝ] E n →L[ℝ] ℝ))
    (hDfH : HolderWith KDf α (Df : E n → E n →L[ℝ] ℝ))
    (p v : E n) (R : ℝ≥0) (hR : 0 < R)
    (hPos : ∀ x ∈ closedBall p (2 * R), (complexHessian (u : E n → ℝ) x).PosDef)
    (hEq : ∀ x ∈ closedBall p (2 * R), (complexHessian (u : E n → ℝ) x).det.re = f x) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ K : ℝ≥0,
      ContDiffOn ℝ 1 (fun x => Hu x v) (ball p δ) ∧
      HolderOnWith K α (fderiv ℝ (fun x => Hu x v)) (ball p δ) := by
  obtain ⟨r, hr, _, C, hBound⟩ :=
    exists_dirichlet_uniform_normalized_quotient_schauder_bound hn u Du Hu f Df hu hDu hf
      hα hα1 hDuH hHH hDfH p v R hR hPos hEq
  obtain ⟨h, hh, hlim, hStep⟩ := exists_dirichlet_admissible_quotient_sequence v R hR
  obtain ⟨hC1, hHolder⟩ := dirichlet_C1_holder_normalized_directional_hessian_of_schauder_bound
    u Du Hu hu hDu hα hHH p v r hh hlim (fun i => hBound (h i) (hh i) (hStep i))
  have hr' : (0 : ℝ) < r := hr
  exact ⟨(r : ℝ) * (1 / 4), by positivity, _,
    dirichlet_C1_holder_of_affine_normalization (fun x => Hu x v) p hr' hr'.ne' hC1 hHolder⟩

end KEBall
