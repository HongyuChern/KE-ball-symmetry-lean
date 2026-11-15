import KEBall.DirichletHessianOscillationStep
import KEBall.DirichletOscillationGeometric

/-!
# Geometric decay of the original directional Hessian oscillations

The constants are uniform in the centre and the admissible initial radius.
Essential extrema are taken with respect to actual Euclidean volume.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Metric Set
open scoped BigOperators NNReal Topology

noncomputable section

namespace KEBall

theorem dirichletHessianOscillation_nonneg_le {n m : ℕ}
    {G : E n → E n →L[ℝ] ℝ} {L : ℝ≥0}
    (hG : LipschitzOnWith L G (closedUnitBall n)) (v : Fin m → E n)
    {x₀ : E n} {R : ℝ} (hR : 0 < R) (hBall : ball x₀ R ⊆ unitBall n) :
    0 ≤ dirichletHessianOscillation G v x₀ R ∧
      dirichletHessianOscillation G v x₀ R ≤
        ∑ i : Fin m, 2 * ((L : ℝ) * ‖v i‖ * ‖v i‖) := by
  let μ := dirichletBallProbability x₀ R
  haveI : IsProbabilityMeasure μ := isProbabilityMeasure_dirichletBallProbability x₀ hR
  have hEach (i : Fin m) :
      0 ≤ essSup (fun x => fderiv ℝ G x (v i) (v i)) μ -
        essInf (fun x => fderiv ℝ G x (v i) (v i)) μ ∧
      essSup (fun x => fderiv ℝ G x (v i) (v i)) μ -
        essInf (fun x => fderiv ℝ G x (v i) (v i)) μ ≤
          2 * ((L : ℝ) * ‖v i‖ * ‖v i‖) := by
    let q : E n → ℝ := fun x => fderiv ℝ G x (v i) (v i)
    let K : ℝ := (L : ℝ) * ‖v i‖ * ‖v i‖
    have hBounds : ∀ᵐ x ∂μ, -K ≤ q x ∧ q x ≤ K := by
      apply ae_dirichletBallProbability_iff.mpr
      filter_upwards [ae_restrict_mem (μ := (volume : Measure (E n))) measurableSet_ball] with x hx
      exact abs_le.mp (norm_dirichlet_hessianEntry_le hG (hBall hx) (v i) (v i))
    have hLo : IsBoundedUnder (· ≥ ·) (ae μ) q := ⟨-K, hBounds.mono fun _ h => h.1⟩
    have hHi : IsBoundedUnder (· ≤ ·) (ae μ) q := ⟨K, hBounds.mono fun _ h => h.2⟩
    have hSup : essSup q μ ≤ K :=
      essSup_le_of_ae_le _ (hBounds.mono fun _ h => h.2) hLo.isCoboundedUnder_le
    have hInf : -K ≤ essInf q μ :=
      le_essInf_of_ae_le _ (hBounds.mono fun _ h => h.1) hHi.isCoboundedUnder_ge
    obtain ⟨x, hxInf, hxSup⟩ := ((ae_essInf_le hLo).and (ae_le_essSup hHi)).exists
    exact ⟨sub_nonneg.mpr (hxInf.trans hxSup), by change essSup q μ - essInf q μ ≤ 2 * K; linarith⟩
  have hNonneg := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => (hEach i).1)
  have hUpper := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => (hEach i).2)
  simpa only [μ, essSup_dirichletBallProbability, essInf_dirichletBallProbability,
    dirichletHessianOscillation] using And.intro hNonneg hUpper

theorem exists_dirichlet_hessian_geometric_decay {n m : ℕ}
    {G : E n → E n →L[ℝ] ℝ} {L : ℝ≥0}
    (hG : LipschitzOnWith L G (closedUnitBall n)) (v : Fin m → E n)
    {θ C : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hC : 0 ≤ C)
    (hStep : ∀ (x₀ : E n) (R : ℝ), 0 < R → R ≤ 1 → closedBall x₀ R ⊆ unitBall n →
      dirichletHessianOscillation G v x₀ (R / 4) ≤
        θ * dirichletHessianOscillation G v x₀ R + C * R) :
    ∃ τ D : ℝ, 0 < τ ∧ τ < 1 ∧ 0 ≤ D ∧
      ∀ (x₀ : E n) (R₀ : ℝ), 0 < R₀ → R₀ ≤ 1 → closedBall x₀ R₀ ⊆ unitBall n →
        ∀ k : ℕ, 0 ≤ dirichletHessianOscillation G v x₀ (R₀ * (1 / 4 : ℝ) ^ k) ∧
          dirichletHessianOscillation G v x₀ (R₀ * (1 / 4 : ℝ) ^ k) ≤ D * τ ^ k := by
  let M : ℝ := ∑ i : Fin m, 2 * ((L : ℝ) * ‖v i‖ * ‖v i‖)
  have hM : 0 ≤ M := Finset.sum_nonneg fun i _ => by positivity
  obtain ⟨τ, D, hτ0, hτ1, hD, hBound⟩ :=
    exists_dirichlet_oscillation_geometric_budget hθ0 hθ1 hC hM
  refine ⟨τ, D, hτ0, hτ1, hD, ?_⟩
  intro x₀ R₀ hR₀ hR₀1 hBall
  let r : ℕ → ℝ := fun k => R₀ * (1 / 4 : ℝ) ^ k
  let o : ℕ → ℝ := fun k => dirichletHessianOscillation G v x₀ (r k)
  have hrPos (k : ℕ) : 0 < r k := mul_pos hR₀ (pow_pos (by norm_num) _)
  have hrLe (k : ℕ) : r k ≤ R₀ := by
    exact mul_le_of_le_one_right hR₀.le (pow_le_one₀ (by norm_num) (by norm_num))
  have hrBall (k : ℕ) : closedBall x₀ (r k) ⊆ unitBall n :=
    (closedBall_subset_closedBall (hrLe k)).trans hBall
  have hInitial : o 0 ≤ M := by
    simpa only [o, r, pow_zero, mul_one] using
      (dirichletHessianOscillation_nonneg_le hG v hR₀ (ball_subset_closedBall.trans hBall)).2
  have hRec (k : ℕ) : o (k + 1) ≤ θ * o k + C * (1 / 4 : ℝ) ^ k := by
    have hRadius : r (k + 1) = r k / 4 := by dsimp only [r]; rw [pow_succ]; ring
    have h := hStep x₀ (r k) (hrPos k) ((hrLe k).trans hR₀1) (hrBall k)
    change dirichletHessianOscillation G v x₀ (r (k + 1)) ≤ _
    rw [hRadius]
    apply h.trans
    apply add_le_add le_rfl
    apply mul_le_mul_of_nonneg_left _ hC
    exact mul_le_of_le_one_left (pow_nonneg (by norm_num) _) hR₀1
  have hDecay := hBound o hInitial hRec
  intro k
  exact ⟨(dirichletHessianOscillation_nonneg_le hG v (hrPos k)
    (ball_subset_closedBall.trans (hrBall k))).1, hDecay k⟩

end KEBall
