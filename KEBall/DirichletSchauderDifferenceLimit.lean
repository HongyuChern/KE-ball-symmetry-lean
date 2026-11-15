import KEBall.DirichletDifferenceQuotientSchauder
import KEBall.DirichletDifferenceQuotientRegularity

/-!
# The actual directional Hessian limit after spatial normalization

Uniform estimates are passed to the first-jet quotients.  The affine
change of variables is then inverted, so the resulting C1 assertion is
about the original Hessian, at the original physical point.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Filter Function Metric Module Set
open DifferentialGeometry.Analysis.Schauder
open scoped NNReal Topology

namespace KEBall

theorem dirichlet_contDiffAt_clm_apply {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {k : WithTop ℕ∞} {f : E n → E n →L[ℝ] F} {p : E n} :
    ContDiffAt ℝ k f p ↔ ∀ v, ContDiffAt ℝ k (fun x => f x v) p := by
  refine ⟨fun h v => h.clm_apply contDiffAt_const, fun h => ?_⟩
  let d := finrank ℝ (E n)
  have hd : d = finrank ℝ (Fin d → ℝ) := (finrank_fin_fun ℝ).symm
  let e₁ := ContinuousLinearEquiv.ofFinrankEq hd
  let e₂ := (e₁.arrowCongr (1 : F ≃L[ℝ] F)).trans (ContinuousLinearEquiv.piRing (Fin d))
  rw [← id_comp f, ← e₂.symm_comp_self]
  exact e₂.symm.contDiff.contDiffAt.comp p (contDiffAt_pi.mpr fun i => h _)

theorem exists_dirichlet_admissible_quotient_sequence {n : ℕ} (v : E n)
    (R : ℝ≥0) (hR : 0 < R) :
    ∃ h : ℕ → ℝ, (∀ i, h i ≠ 0) ∧ Tendsto h atTop (𝓝 0) ∧
      ∀ i, |h i| * ‖v‖ ≤ R := by
  let a : ℝ := R / (‖v‖ + 1)
  have hd : 0 < ‖v‖ + 1 := by positivity
  have ha : 0 < a := div_pos hR hd
  have haR : a * (‖v‖ + 1) = R := div_mul_cancel₀ _ hd.ne'
  have haBound : a * ‖v‖ ≤ R := by nlinarith
  let h (i : ℕ) : ℝ := a / ((i : ℝ) + 1)
  have hpos (i : ℕ) : 0 < h i := div_pos ha (by positivity)
  refine ⟨h, fun i => (hpos i).ne', ?_, ?_⟩
  · have ht := (tendsto_const_div_atTop_nhds_zero_nat a).comp (tendsto_add_atTop_nat 1)
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one, h] using! ht
  · intro i
    rw [abs_of_pos (hpos i)]
    exact (mul_le_mul_of_nonneg_right
      (div_le_self ha.le (by have := Nat.cast_nonneg (α := ℝ) i; linarith))
      (norm_nonneg v)).trans haBound

theorem tendstoUniformly_dirichlet_scaled_quotient {n : ℕ} {F I : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : BoundedContinuousFunction (E n) F}
    {D : BoundedContinuousFunction (E n) (E n →L[ℝ] F)} {K α : ℝ≥0}
    (hD : ∀ x, HasFDerivAt (f : E n → F) (D x) x)
    (hH : HolderWith K α (D : E n → E n →L[ℝ] F)) (hα : 0 < α)
    (p v : E n) (r : ℝ≥0) (k : ℕ) {l : Filter I} {h : I → ℝ}
    (hh : ∀ i, h i ≠ 0) (hlim : Tendsto h l (𝓝 0)) :
    TendstoUniformly
      (fun i => (dirichletBoundedScaledJet
        (dirichletBoundedDifferenceQuotient f v (h i)) p r k : E n → F))
      (fun x => (r : ℝ) ^ k • D (p + (r : ℝ) • x) v) l := by
  have ht := (tendstoUniformly_dirichletDifferenceQuotient hD hH hα v hh hlim).comp
    (fun x : E n => p + (r : ℝ) • x)
  have hs := (lipschitzWith_smul ((r : ℝ) ^ k) (β := F)).uniformContinuous.comp_tendstoUniformly ht
  simpa only [Function.comp_def, dirichletBoundedScaledJet_apply,
    dirichletBoundedDifferenceQuotient_apply] using! hs

theorem dirichlet_C1_directional_hessian_of_normalized_schauder_bound {n : ℕ}
    (u : BoundedContinuousFunction (E n) ℝ)
    (Du : BoundedContinuousFunction (E n) (E n →L[ℝ] ℝ))
    (Hu : BoundedContinuousFunction (E n) (E n →L[ℝ] E n →L[ℝ] ℝ))
    (hu : ∀ x, HasFDerivAt (u : E n → ℝ) (Du x) x)
    (hDu : ∀ x, HasFDerivAt (Du : E n → E n →L[ℝ] ℝ) (Hu x) x)
    {KH α C : ℝ≥0} (hα : 0 < α)
    (hH : HolderWith KH α (Hu : E n → E n →L[ℝ] E n →L[ℝ] ℝ))
    (p v : E n) (r : ℝ≥0) (hr : 0 < r) {h : ℕ → ℝ}
    (hh : ∀ i, h i ≠ 0) (hlim : Tendsto h atTop (𝓝 0))
    (hGauge : ∀ i, eContDiffHolderGaugeOn 2 α (closedBall (0 : E n) (1 / 2))
      (dirichletBoundedScaledJet (dirichletBoundedDifferenceQuotient u v (h i)) p r 0 : E n → ℝ) ≤ C) :
    ContDiffAt ℝ 1 (fun x => Hu x v) p := by
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
  have hC1 := (dirichlet_C1_limit_of_uniform_holder_derivatives (l := atTop)
    (f := fun i => (q₁ i : E n → E n →L[ℝ] ℝ))
    (g := fun x => (r : ℝ) ^ 1 • Hu (p + (r : ℝ) • x) v)
    (by norm_num : (1 / 4 : ℝ) < 1 / 2) hα
    (fun i x _ => (hq₁ i x).differentiableAt) hqH ht).1
  have hAt : ContDiffAt ℝ 1 (fun x => (r : ℝ) • Hu (p + (r : ℝ) • x) v) (0 : E n) := by
    simpa only [pow_one] using hC1.contDiffAt (ball_mem_nhds _ (by norm_num : (0 : ℝ) < 1 / 4))
  have hInv : ContDiffAt ℝ 1 (fun x : E n => (r : ℝ)⁻¹ • (x - p)) p := by fun_prop
  have hAt' : ContDiffAt ℝ 1 (fun x => (r : ℝ) • Hu (p + (r : ℝ) • x) v)
      ((r : ℝ)⁻¹ • (p - p)) := by simpa only [sub_self, smul_zero] using hAt
  have hs := (hAt'.comp p hInv).const_smul ((r : ℝ)⁻¹)
  have hr0 : (r : ℝ) ≠ 0 := (show (0 : ℝ) < r from hr).ne'
  simpa only [Function.comp_def, smul_smul, mul_inv_cancel₀ hr0,
    inv_mul_cancel₀ hr0, one_smul, ← add_sub_assoc, add_sub_cancel_left] using! hs

end KEBall
