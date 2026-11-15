import KEBall.DirichletHessianDefectEstimate
import KEBall.DirichletBallAverages

/-! Local integrability and essential bounds of the original Hessian entries. -/

set_option autoImplicit false

open Filter MeasureTheory Metric Set
open scoped NNReal

noncomputable section

namespace KEBall

theorem boundedUnder_dirichlet_hessianEntry_ball {n : ℕ}
    {G : E n → E n →L[ℝ] ℝ} {L : ℝ≥0}
    (hG : LipschitzOnWith L G (closedUnitBall n)) (v : E n)
    {x₀ : E n} {R : ℝ} (hBall : ball x₀ R ⊆ unitBall n) :
    IsBoundedUnder (· ≥ ·) (ae (volume.restrict (ball x₀ R)))
        (fun x => fderiv ℝ G x v v) ∧
      IsBoundedUnder (· ≤ ·) (ae (volume.restrict (ball x₀ R)))
        (fun x => fderiv ℝ G x v v) := by
  let K : ℝ := (L : ℝ) * ‖v‖ * ‖v‖
  have h : ∀ᵐ x ∂(volume : Measure (E n)).restrict (ball x₀ R),
      -K ≤ fderiv ℝ G x v v ∧ fderiv ℝ G x v v ≤ K := by
    filter_upwards [ae_restrict_mem (μ := (volume : Measure (E n))) measurableSet_ball] with x hx
    exact abs_le.mp (norm_dirichlet_hessianEntry_le hG (hBall hx) v v)
  exact ⟨⟨-K, h.mono fun _ hx => hx.1⟩, ⟨K, h.mono fun _ hx => hx.2⟩⟩

theorem integrableOn_dirichlet_hessianEntry_ball {n : ℕ}
    {G : E n → E n →L[ℝ] ℝ} {L : ℝ≥0}
    (hG : LipschitzOnWith L G (closedUnitBall n)) (v : E n)
    {x₀ : E n} {R : ℝ} (hBall : ball x₀ R ⊆ unitBall n) :
    IntegrableOn (fun x => fderiv ℝ G x v v) (ball x₀ R) volume := by
  let μ : Measure (E n) := volume.restrict (ball x₀ R)
  haveI : IsFiniteMeasure μ := ⟨by
    simpa only [μ, Measure.restrict_apply_univ] using
      (measure_ball_lt_top (μ := (volume : Measure (E n))) (x := x₀) (r := R))⟩
  have hm : Measurable (fun x => fderiv ℝ G x v v) :=
    (ContinuousLinearMap.measurable_apply v).comp (measurable_fderiv_apply_const ℝ G v)
  apply (integrable_const ((L : ℝ) * ‖v‖ * ‖v‖)).mono' hm.aestronglyMeasurable
  filter_upwards [ae_restrict_mem (μ := (volume : Measure (E n))) measurableSet_ball] with x hx
  exact norm_dirichlet_hessianEntry_le hG (hBall hx) v v

theorem ae_dirichlet_hessianEntry_between_essential_bounds {n : ℕ}
    {G : E n → E n →L[ℝ] ℝ} {L : ℝ≥0}
    (hG : LipschitzOnWith L G (closedUnitBall n)) (v : E n)
    {x₀ : E n} {R : ℝ} (hBall : ball x₀ R ⊆ unitBall n) :
    ∀ᵐ x ∂(volume : Measure (E n)).restrict (ball x₀ R),
      essInf (fun y => fderiv ℝ G y v v) (volume.restrict (ball x₀ R)) ≤ fderiv ℝ G x v v ∧
        fderiv ℝ G x v v ≤ essSup (fun y => fderiv ℝ G y v v) (volume.restrict (ball x₀ R)) := by
  obtain ⟨hLo, hHi⟩ := boundedUnder_dirichlet_hessianEntry_ball hG v hBall
  exact (ae_essInf_le hLo).and (ae_le_essSup hHi)

end KEBall
