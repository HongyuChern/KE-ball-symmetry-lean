import KEBall.DirichletHessianCrossTerms
import KEBall.DirichletProductResidualBound

/-! Arbitrarily small highest-order coefficient for proper products of the actual Hessian. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 400000

open MeasureTheory Metric Set
open scoped BigOperators ContDiff

namespace KEBall

theorem exists_dirichlet_hessian_proper_product_tame_bound {n k : ℕ}
    (hn : 0 < n) (hk : 2 ≤ k) {ι : Type*} [LinearOrder ι] (s : Finset ι)
    (j : ι → ℕ) (hj : ∀ i ∈ s, 0 < j i) (hjk : ∀ i ∈ s, j i < k)
    (hSum : ∑ i ∈ s, j i = k) {u : E n → ℝ}
    (hu : ContDiffOn ℝ 2 u (closedUnitBall n)) (huS : ContDiffOn ℝ ∞ u (unitBall n))
    (hu0 : ∀ x ∈ unitSphere n, u x = 0)
    (S : E n →L[ℝ] E n) (hS : star S = -S) {Λ ε : ℝ} (hΛ : 0 ≤ Λ) (hε : 0 < ε) :
    ∃ C ≥ (0 : ℝ), ∀ t : ℝ, t ≠ 0 →
      ∀ (Q : ι → E n ≃ₗᵢ[ℝ] E n)
        (L : ι → (E n →L[ℝ] E n →L[ℝ] ℝ) →L[ℝ] ℝ), (∀ i ∈ s, ‖L i‖ ≤ Λ) →
      let R := orthogonalFlow S hS t
      (∫ x in unitBall n, ∏ i ∈ s,
        (L i (dirichletIteratedFieldDifference R t (dirichletWithinRealHessian u)
          (j i) (Q i x))) ^ 2 ∂volume0 n) ≤
        ε * (∫ x in unitBall n,
          ‖dirichletWithinRealHessian (dirichletIteratedOrthogonalDifference R t u k) x‖ ^ 2 ∂volume0 n) +
        C * (∑ m ∈ Finset.range k, ∫ x in unitBall n,
          ‖dirichletWithinRealHessian (dirichletIteratedOrthogonalDifference R t u m) x‖ ^ 2 ∂volume0 n) + C := by
  classical
  obtain ⟨v, hv, hv0, hApprox, C₀, hC₀, hResidual⟩ :=
    exists_dirichlet_hessian_linearForm_reference_absorption hn hk s j hj hjk hSum hu huS hu0
      S hS hΛ (half_pos hε)
  let H := dirichletWithinRealHessian u
  let V := realHessian v
  let Z (x : E n) := H x - V x
  have hV (x : E n) (hx : x ∈ closedUnitBall n) : ContDiffAt ℝ ∞ V x :=
    realHessian_contDiffAt (hv.contDiffAt hx)
  let Energy (t : ℝ) (m : ℕ) := ∫ x in unitBall n,
    ‖dirichletWithinRealHessian
      (dirichletIteratedOrthogonalDifference (orthogonalFlow S hS t) t u m) x‖ ^ 2 ∂volume0 n
  let Low (t : ℝ) := ∑ m ∈ Finset.range k, Energy t m
  let Cross (t : ℝ) (Q : ι → E n ≃ₗᵢ[ℝ] E n)
      (L : ι → (E n →L[ℝ] E n →L[ℝ] ℝ) →L[ℝ] ℝ) (i : ι) :=
    ∫ x in unitBall n,
      (L i (dirichletIteratedFieldDifference (orthogonalFlow S hS t) t V (j i) (Q i x))) ^ 2 *
      ∏ l ∈ s.erase i,
        (if l < i then L l (dirichletIteratedFieldDifference (orthogonalFlow S hS t) t H (j l) (Q l x))
          else L l (dirichletIteratedFieldDifference (orthogonalFlow S hS t) t Z (j l) (Q l x))) ^ 2 ∂volume0 n
  have hCrossAll (i : ι) : ∃ D ≥ (0 : ℝ), ∀ t : ℝ, t ≠ 0 → i ∈ s →
      ∀ (Q : ι → E n ≃ₗᵢ[ℝ] E n)
        (L : ι → (E n →L[ℝ] E n →L[ℝ] ℝ) →L[ℝ] ℝ), (∀ l ∈ s, ‖L l‖ ≤ Λ) →
        Cross t Q L i ≤ D * Low t + D := by
    by_cases hi : i ∈ s
    · obtain ⟨D, hD, hBound⟩ := exists_dirichlet_hessian_reference_cross_term_bound hn s j hj hjk hSum hu hV S hS hΛ i hi
      exact ⟨D, hD, fun t ht _ Q L hL => hBound t ht Q L hL⟩
    · refine ⟨0, le_rfl, ?_⟩
      intro t ht his
      exact (hi his).elim
  choose D hD hCross using hCrossAll
  let Dsum := ∑ i ∈ s, D i
  have hDsum : 0 ≤ Dsum := Finset.sum_nonneg (fun i _ => hD i)
  let C := ε + 2 * C₀ + 2 * (s.card : ℝ) * Dsum
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro t ht Q L hL
  dsimp only
  let R := orthogonalFlow S hS t
  let A (i : ι) (x : E n) := L i (dirichletIteratedFieldDifference R t Z (j i) (Q i x))
  let B (i : ι) (x : E n) := L i (dirichletIteratedFieldDifference R t V (j i) (Q i x))
  have hHC : ContinuousOn H (closedUnitBall n) := continuousOn_dirichletWithinRealHessian hu
  have hVC : ContinuousOn V (closedUnitBall n) :=
    fun x hx => (hV x hx).continuousAt.continuousWithinAt
  have hZC : ContinuousOn Z (closedUnitBall n) := hHC.sub hVC
  have hAC (i : ι) : ContinuousOn (A i) (closedUnitBall n) := (L i).continuous.comp_continuousOn
    (continuousOn_dirichlet_orthogonal_comp (continuousOn_dirichletIteratedFieldDifference R t hZC (j i)) (Q i))
  have hBC (i : ι) : ContinuousOn (B i) (closedUnitBall n) := (L i).continuous.comp_continuousOn
    (continuousOn_dirichlet_orthogonal_comp (continuousOn_dirichletIteratedFieldDifference R t hVC (j i)) (Q i))
  have hAB (i : ι) (x : E n) : A i x + B i x =
      L i (dirichletIteratedFieldDifference R t H (j i) (Q i x)) := by
    simp only [A, B, Z, dirichletIteratedFieldDifference_sub, map_sub, sub_add_cancel]
  have hSplit := integral_dirichlet_product_add_sq_le hn s A B (fun i _ => hAC i) (fun i _ => hBC i)
  simp only [hAB] at hSplit
  have hRes : (∫ x in unitBall n, ∏ i ∈ s, A i x ^ 2 ∂volume0 n) ≤
      ε / 2 * (Low t + Energy t k) + C₀ := by
    have h := hResidual t ht Q L hL
    dsimp only at h
    rw [Finset.sum_range_succ] at h
    exact h
  have hSumCross : ∑ i ∈ s, Cross t Q L i ≤ Dsum * Low t + Dsum := by
    calc
      _ ≤ ∑ i ∈ s, (D i * Low t + D i) := Finset.sum_le_sum (fun i hi => hCross i t ht hi Q L hL)
      _ = _ := by rw [Finset.sum_add_distrib, ← Finset.sum_mul]
  have hLow0 : 0 ≤ Low t := Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => sq_nonneg _))
  have hCombine : (∫ x in unitBall n, ∏ i ∈ s,
      (L i (dirichletIteratedFieldDifference R t H (j i) (Q i x))) ^ 2 ∂volume0 n) ≤
      2 * (ε / 2 * (Low t + Energy t k) + C₀) +
        2 * s.card * (Dsum * Low t + Dsum) := by
    exact hSplit.trans (add_le_add (mul_le_mul_of_nonneg_left hRes (by positivity))
      (mul_le_mul_of_nonneg_left hSumCross (by positivity)))
  refine hCombine.trans ?_
  change _ ≤ ε * Energy t k + C * Low t + C
  dsimp only [C]
  nlinarith only [hε.le, hC₀, mul_nonneg hC₀ hLow0]

end KEBall
