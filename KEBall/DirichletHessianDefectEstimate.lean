import KEBall.DirichletHessianWeakHarnack
import KEBall.DirichletHarnackDefect

/-!
# Upper-defect estimate for the actual bounded Hessian

The quadratic source correction and the strict positivity parameter are
removed from the integral side.  The remaining error has order R².  The
essential supremum is still written in the affine coordinates of the
verified weak Harnack theorem.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Metric Set
open scoped NNReal

noncomputable section

namespace KEBall

/-- The essential supremum in the verified scaled Harnack theorem is the
essential supremum on the physical ball.  No continuity of the function
and no pointwise representative are needed. -/
theorem dirichlet_essSup_affine_pullback {n : ℕ} (f : E n → ℝ)
    {x₀ : E n} {R ρ : ℝ} (hR : 0 < R) :
    essSup (fun z : E n => f (x₀ + R • z))
        (volume.restrict (ball (0 : E n) ρ)) =
      essSup f (volume.restrict (ball x₀ (R * ρ))) := by
  let T : E n → E n := fun z => x₀ + R • z
  have hT : MeasurableEmbedding T :=
    (MeasurableEquiv.addLeft x₀).measurableEmbedding.comp
      (Homeomorph.smulOfNeZero R hR.ne').toMeasurableEquiv.measurableEmbedding
  have he : essSup (f ∘ T) (volume.restrict (ball (0 : E n) ρ)) =
      essSup f (Measure.map T (volume.restrict (ball (0 : E n) ρ))) := by
    rw [essSup_eq_sInf, essSup_eq_sInf]
    congr 1
    ext b
    change ((volume.restrict (ball (0 : E n) ρ)) {x | b < (f ∘ T) x} = 0) ↔
      ((Measure.map T (volume.restrict (ball (0 : E n) ρ))) {x | b < f x} = 0)
    rw [hT.map_apply]
    rfl
  change essSup (f ∘ T) _ = _
  rw [he]
  change essSup f (Measure.map (fun z : E n => x₀ + R • z) _) = _
  rw [DeGiorgi.affine_map_restrict_ball_radius hR,
    essSup_ennreal_smul_measure (DeGiorgi.affine_scale_measure_ne_zero (d := 2 * n) hR)]

theorem norm_dirichlet_hessianEntry_le {n : ℕ}
    {G : E n → E n →L[ℝ] ℝ} {L : ℝ≥0}
    (hG : LipschitzOnWith L G (closedUnitBall n))
    {x : E n} (hx : x ∈ unitBall n) (v w : E n) :
    ‖fderiv ℝ G x v w‖ ≤ (L : ℝ) * ‖v‖ * ‖w‖ := by
  have hNorm : ‖fderiv ℝ G x‖ ≤ L :=
    norm_fderiv_le_of_lipschitzOn ℝ
      (mem_of_superset (isOpen_ball.mem_nhds hx) ball_subset_closedBall) hG
  exact ((fderiv ℝ G x v).le_opNorm w).trans
    (mul_le_mul_of_nonneg_right (((fderiv ℝ G x).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right hNorm (norm_nonneg _))) (norm_nonneg _))

theorem exists_dirichlet_hessian_upper_defect_estimate {n : ℕ} (hn : 0 < n)
    {G : E n → E n →L[ℝ] ℝ} {L : ℝ≥0}
    (hG : LipschitzOnWith L G (closedUnitBall n))
    {c : ℝ} (hc : 0 < c) (hH : HasDirichletHessianWeakHarnack G c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : E n, ∃ a : ℝ, 0 ≤ a ∧
      ∀ (M R : ℝ) (x₀ : E n), 0 < R → closedBall x₀ R ⊆ unitBall n →
        (∀ᵐ x ∂(volume0 n).restrict (ball x₀ R), fderiv ℝ G x v v ≤ M) →
        (R ^ (2 * n))⁻¹ * (∫ x in ball x₀ (R / 4), M - fderiv ℝ G x v v) ≤
          C * (M - essSup (fun z : E n => fderiv ℝ G (x₀ + R • z) v v)
            (volume.restrict (ball (0 : E n) (1 / 4 : ℝ))) + a * R ^ 2) := by
  obtain ⟨C, hC, hHV⟩ := hH
  refine ⟨C, hC, ?_⟩
  intro v
  obtain ⟨B, hB, hHB⟩ := hHV v
  let a : ℝ := B / (4 * n * c)
  have ha : 0 ≤ a := div_nonneg hB (by positivity)
  refine ⟨a, ha, ?_⟩
  intro M R x₀ hR hBall hM
  let q : E n → ℝ := fun x => fderiv ℝ G x v v
  let s : E n → ℝ := dirichletSourceQuadratic a R x₀
  let μ : Measure (E n) := volume.restrict (ball x₀ (R / 4))
  let ν : Measure (E n) := volume.restrict (ball (0 : E n) (1 / 4 : ℝ))
  let K : ℝ := (L : ℝ) * ‖v‖ * ‖v‖
  have hSub : ball x₀ (R / 4) ⊆ closedBall x₀ R :=
    ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith))
  have hqMeas : Measurable q :=
    (ContinuousLinearMap.measurable_apply v).comp (measurable_fderiv_apply_const ℝ G v)
  have hqBound : ∀ᵐ x ∂μ, ‖q x‖ ≤ K := by
    filter_upwards [ae_restrict_mem (μ := (volume : Measure (E n))) measurableSet_ball] with x hx
    exact norm_dirichlet_hessianEntry_le hG (hBall (hSub hx)) v v
  have hqBounds : ∀ᵐ x ∂μ, -K ≤ q x ∧ q x ≤ K := by
    filter_upwards [hqBound] with x hx
    exact abs_le.mp hx
  have hsBounds : ∀ᵐ x ∂μ, 0 ≤ s x ∧ s x ≤ a * R ^ 2 := by
    filter_upwards [ae_restrict_mem (μ := (volume : Measure (E n))) measurableSet_ball] with x hx
    exact dirichletSourceQuadratic_bounds ha hR.le (hSub hx)
  have hqPull : ∀ᵐ z ∂ν, -K ≤ q (x₀ + R • z) ∧ q (x₀ + R • z) ≤ K := by
    apply ae_dirichlet_affine_pullback (n := n) (x₀ := x₀) (ρ := (1 / 4 : ℝ))
      (P := fun x => -K ≤ q x ∧ q x ≤ K) hR
    rw [show R * (1 / 4 : ℝ) = R / 4 by ring]
    exact hqBounds
  have hsPull : ∀ᵐ z ∂ν, 0 ≤ s (x₀ + R • z) ∧ s (x₀ + R • z) ≤ a * R ^ 2 := by
    apply ae_dirichlet_affine_pullback (n := n) (x₀ := x₀) (ρ := (1 / 4 : ℝ))
      (P := fun x => 0 ≤ s x ∧ s x ≤ a * R ^ 2) hR
    rw [show R * (1 / 4 : ℝ) = R / 4 by ring]
    exact hsBounds
  have hν : ν ≠ 0 := by
    intro hzero
    have hz := congrArg (fun m : Measure (E n) => m univ) hzero
    have hp := measure_ball_pos (volume : Measure (E n)) (0 : E n)
      (show (0 : ℝ) < 1 / 4 by norm_num)
    have hz' : (volume : Measure (E n)) (ball (0 : E n) (1 / 4 : ℝ)) = 0 := by
      simpa [ν] using hz
    exact hp.ne' hz'
  haveI : IsFiniteMeasure μ := ⟨by
    change (volume.restrict (ball x₀ (R / 4))) univ < ⊤
    simpa only [Measure.restrict_apply_univ] using
      (measure_ball_lt_top (μ := (volume : Measure (E n))) (x := x₀) (r := R / 4))⟩
  have hqInt : Integrable q μ := (integrable_const K).mono' hqMeas.aestronglyMeasurable hqBound
  have hsInt : Integrable s μ :=
    ((contDiff_dirichletSourceQuadratic a R x₀).continuous.continuousOn.integrableOn_compact
      (isCompact_closedBall x₀ (R / 4))).mono_set ball_subset_closedBall
  apply dirichlet_defect_bound_of_corrected_harnack hν hC hqPull hsPull
  intro ε hε
  have hfInt : Integrable (fun x => M + ε - q x + s x) μ :=
    ((integrable_const _).sub hqInt).add hsInt
  have hle : (fun x => M - q x) ≤ᵐ[μ] (fun x => |M + ε - q x + s x|) := by
    filter_upwards [hsBounds] with x hx
    exact (by linarith [hx.1] : M - q x ≤ M + ε - q x + s x).trans (le_abs_self _)
  have hi := integral_mono_ae ((integrable_const M).sub hqInt) hfInt.abs hle
  have hw := mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr (pow_nonneg hR.le (2 * n)))
  exact hw.trans (hHB M R ε x₀ hR hBall hε hM)

/-- The same estimate in physical-ball coordinates. -/
theorem exists_dirichlet_hessian_upper_defect_estimate_on_ball {n : ℕ} (hn : 0 < n)
    {G : E n → E n →L[ℝ] ℝ} {L : ℝ≥0}
    (hG : LipschitzOnWith L G (closedUnitBall n))
    {c : ℝ} (hc : 0 < c) (hH : HasDirichletHessianWeakHarnack G c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : E n, ∃ a : ℝ, 0 ≤ a ∧
      ∀ (M R : ℝ) (x₀ : E n), 0 < R → closedBall x₀ R ⊆ unitBall n →
        (∀ᵐ x ∂(volume0 n).restrict (ball x₀ R), fderiv ℝ G x v v ≤ M) →
        (R ^ (2 * n))⁻¹ * (∫ x in ball x₀ (R / 4), M - fderiv ℝ G x v v) ≤
          C * (M - essSup (fun x : E n => fderiv ℝ G x v v)
            (volume.restrict (ball x₀ (R / 4))) + a * R ^ 2) := by
  obtain ⟨C, hC, hv⟩ := exists_dirichlet_hessian_upper_defect_estimate hn hG hc hH
  refine ⟨C, hC, ?_⟩
  intro v
  obtain ⟨a, ha, hEst⟩ := hv v
  refine ⟨a, ha, ?_⟩
  intro M R x₀ hR hBall hM
  have h := hEst M R x₀ hR hBall hM
  rw [dirichlet_essSup_affine_pullback (fun x : E n => fderiv ℝ G x v v)
      (x₀ := x₀) (ρ := (1 / 4 : ℝ)) hR,
    show R * (1 / 4 : ℝ) = R / 4 by ring] at h
  exact h

end KEBall
