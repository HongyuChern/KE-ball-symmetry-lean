import KEBall.DirichletFiniteLpJetAlgebra

/-! Reciprocal closure of actual finite Lp jets with a bounded reciprocal. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 500000
open Filter MeasureTheory Metric Set
open scoped BigOperators ContDiff ENNReal Topology
namespace KEBall

theorem HasDirichletFiniteLpJets.inv {n k : ℕ} {U : Set (E n)} {μ : Measure (E n)}
    [IsFiniteMeasure μ] (hU : IsOpen U) (hμ : ∀ᵐ x ∂μ, x ∈ U)
    {f : E n → ℝ} (hf : HasDirichletFiniteLpJets U μ k f)
    (h₀ : ∀ x ∈ U, f x ≠ 0) {C : ℝ} (hC : ∀ x ∈ U, ‖(f x)⁻¹‖ ≤ C) :
    HasDirichletFiniteLpJets U μ k (fun x => (f x)⁻¹) := by
  have hSmooth := hf.contDiffOn.inv h₀
  have hMeas : AEStronglyMeasurable (fun x => (f x)⁻¹) μ := by
    have h := hSmooth.continuousOn.aestronglyMeasurable (μ := μ) hU.measurableSet
    rwa [Measure.restrict_eq_self_of_ae_mem hμ] at h
  have hBase : HasDirichletFiniteLpJets U μ 0 (fun x => (f x)⁻¹) :=
    ⟨hSmooth,fun p _ => (memLp_const C).mono' hMeas (hμ.mono (fun x hx => hC x hx))⟩
  induction k with
  | zero => exact hBase
  | succ k ih =>
    have hInv := ih (hf.of_le (Nat.le_succ k))
    refine ⟨hBase,fun d => ?_⟩
    have hSquare := hInv.mul hU hμ hInv
    have hNeg : HasDirichletFiniteLpJets U μ k (fun x => -1 * (fderiv ℝ f x d * ((f x)⁻¹*(f x)⁻¹))) :=
      (HasDirichletFiniteLpJets.const k (-1)).mul hU hμ ((hf.2 d).mul hU hμ hSquare)
    refine hNeg.congr hU hμ ?_
    intro x hx
    have hd := (hf.contDiffOn.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
    change -1 * (fderiv ℝ f x d * ((f x)⁻¹*(f x)⁻¹)) = fderiv ℝ (Inv.inv ∘ f) x d
    rw [fderiv_comp x (differentiableAt_inv (h₀ x hx)) hd, fderiv_inv,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul]
    simp only [inv_pow,pow_two]
    ring

theorem HasDirichletFiniteLpJets.div {n k : ℕ} {U : Set (E n)} {μ : Measure (E n)}
    [IsFiniteMeasure μ] (hU : IsOpen U) (hμ : ∀ᵐ x ∂μ, x ∈ U)
    {f g : E n → ℝ} (hf : HasDirichletFiniteLpJets U μ k f)
    (hg : HasDirichletFiniteLpJets U μ k g)
    (h₀ : ∀ x ∈ U, g x ≠ 0) {C : ℝ} (hC : ∀ x ∈ U, ‖(g x)⁻¹‖ ≤ C) :
    HasDirichletFiniteLpJets U μ k (fun x => f x/g x) := by
  simpa only [div_eq_mul_inv] using hf.mul hU hμ (hg.inv hU hμ h₀ hC)

end KEBall
