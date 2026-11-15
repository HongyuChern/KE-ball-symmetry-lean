import KEBall.DirichletFieldProductInterpolation
import KEBall.DirichletHessianPairEnergy

/-! Uniform lower-order product bounds mixing the Hessian and its reference residual. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open MeasureTheory Metric Set
open scoped BigOperators ContDiff

namespace KEBall

noncomputable def dirichletPairSelectCLM {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] (L : V →L[ℝ] ℝ) (p : Bool) :
    (V × V) →L[ℝ] ℝ :=
  if p then L.comp (ContinuousLinearMap.fst ℝ V V) else L.comp (ContinuousLinearMap.snd ℝ V V)

theorem norm_dirichletPairSelectCLM_le {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] (L : V →L[ℝ] ℝ) (p : Bool) :
    ‖dirichletPairSelectCLM L p‖ ≤ ‖L‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg L)
  intro v
  cases p with
  | false =>
    exact (L.le_opNorm v.2).trans (mul_le_mul_of_nonneg_left (norm_snd_le v) (norm_nonneg L))
  | true =>
    exact (L.le_opNorm v.1).trans (mul_le_mul_of_nonneg_left (norm_fst_le v) (norm_nonneg L))

theorem exists_dirichlet_hessian_pair_product_lower_bound {n k m : ℕ}
    (hn : 0 < n) (hm0 : 0 < m) (hm : m < k) {ι : Type*} (s : Finset ι)
    (j : ι → ℕ) (hj : ∀ i ∈ s, 0 < j i) (hjm : ∀ i ∈ s, j i ≤ m)
    (hSum : ∑ i ∈ s, j i = m) {u : E n → ℝ}
    (hu : ContDiffOn ℝ 2 u (closedUnitBall n))
    {V : E n → E n →L[ℝ] E n →L[ℝ] ℝ}
    (hV : ∀ x ∈ closedUnitBall n, ContDiffAt ℝ ∞ V x)
    (S : E n →L[ℝ] E n) (hS : star S = -S) {Λ : ℝ} (hΛ : 0 ≤ Λ) :
    ∃ C ≥ (0 : ℝ), ∀ t : ℝ, t ≠ 0 →
      ∀ (Q : ι → E n ≃ₗᵢ[ℝ] E n)
        (L : ι → ((E n →L[ℝ] E n →L[ℝ] ℝ) × (E n →L[ℝ] E n →L[ℝ] ℝ)) →L[ℝ] ℝ),
      (∀ i ∈ s, ‖L i‖ ≤ Λ) →
      let R := orthogonalFlow S hS t
      (∫ x in unitBall n, ∏ i ∈ s,
        (L i (dirichletIteratedFieldDifference R t
          (fun y => (dirichletWithinRealHessian u y, dirichletWithinRealHessian u y - V y))
          (j i) (Q i x))) ^ 2 ∂volume0 n) ≤
        C * (∑ l ∈ Finset.range k, ∫ x in unitBall n,
          ‖dirichletWithinRealHessian (dirichletIteratedOrthogonalDifference R t u l) x‖ ^ 2 ∂volume0 n) + C := by
  let W (x : E n) := (dirichletWithinRealHessian u x, dirichletWithinRealHessian u x - V x)
  have hH := continuousOn_dirichletWithinRealHessian hu
  have hW : ContinuousOn W (closedUnitBall n) :=
    hH.prodMk (hH.sub (fun x hx => (hV x hx).continuousAt.continuousWithinAt))
  obtain ⟨B₀, hB₀⟩ := (isCompact_closedBall (0 : E n) 1).exists_bound_of_continuousOn hW
  let B := max B₀ 0
  have hB : 0 ≤ B := le_max_right _ _
  obtain ⟨C, hC, hEnergy⟩ := exists_dirichlet_hessian_pair_lower_energy_bound hn hm hu hV S hS
  let A : ℝ := (((4 * (m : ℝ)) ^ (m ^ 3)) ^ s.card * (Λ * B) ^ (s.card - 1) * Λ) ^ 2
  have hA : 0 ≤ A := sq_nonneg _
  refine ⟨A * C, mul_nonneg hA hC, ?_⟩
  intro t ht Q L hL
  dsimp only
  have hProd := integral_dirichlet_linearForm_product_sq_le hn hm0 s (orthogonalFlow S hS t) ht
    hW j hj hjm hSum Q L hΛ hB hL
    (fun x hx => (hB₀ x (ball_subset_closedBall hx)).trans (le_max_left _ _))
  exact hProd.trans ((mul_le_mul_of_nonneg_left (hEnergy t ht) hA).trans_eq (by ring))

theorem exists_dirichlet_hessian_mixed_product_lower_bound {n k m : ℕ}
    (hn : 0 < n) (hm0 : 0 < m) (hm : m < k) {ι : Type*} (s : Finset ι)
    (j : ι → ℕ) (hj : ∀ i ∈ s, 0 < j i) (hjm : ∀ i ∈ s, j i ≤ m)
    (hSum : ∑ i ∈ s, j i = m) {u : E n → ℝ}
    (hu : ContDiffOn ℝ 2 u (closedUnitBall n))
    {V : E n → E n →L[ℝ] E n →L[ℝ] ℝ}
    (hV : ∀ x ∈ closedUnitBall n, ContDiffAt ℝ ∞ V x)
    (S : E n →L[ℝ] E n) (hS : star S = -S) {Λ : ℝ} (hΛ : 0 ≤ Λ) :
    ∃ C ≥ (0 : ℝ), ∀ t : ℝ, t ≠ 0 →
      ∀ (Q : ι → E n ≃ₗᵢ[ℝ] E n)
        (L : ι → (E n →L[ℝ] E n →L[ℝ] ℝ) →L[ℝ] ℝ), (∀ i ∈ s, ‖L i‖ ≤ Λ) →
      ∀ p : ι → Bool,
      let R := orthogonalFlow S hS t
      (∫ x in unitBall n, ∏ i ∈ s,
        (if p i then L i (dirichletIteratedFieldDifference R t (dirichletWithinRealHessian u) (j i) (Q i x))
          else L i (dirichletIteratedFieldDifference R t
            (fun y => dirichletWithinRealHessian u y - V y) (j i) (Q i x))) ^ 2 ∂volume0 n) ≤
        C * (∑ l ∈ Finset.range k, ∫ x in unitBall n,
          ‖dirichletWithinRealHessian (dirichletIteratedOrthogonalDifference R t u l) x‖ ^ 2 ∂volume0 n) + C := by
  obtain ⟨C, hC, hBound⟩ := exists_dirichlet_hessian_pair_product_lower_bound hn hm0 hm s j hj hjm hSum hu hV S hS hΛ
  refine ⟨C, hC, ?_⟩
  intro t ht Q L hL p
  have h := hBound t ht Q (fun i => dirichletPairSelectCLM (L i) (p i))
    (fun i hi => (norm_dirichletPairSelectCLM_le (L i) (p i)).trans (hL i hi))
  have hEval (l : (E n →L[ℝ] E n →L[ℝ] ℝ) →L[ℝ] ℝ) (p : Bool)
      (a b : E n →L[ℝ] E n →L[ℝ] ℝ) :
      dirichletPairSelectCLM l p (a, b) = if p then l a else l b := by
    cases p <;> rfl
  simpa only [dirichletIteratedFieldDifference_prod, hEval] using h

end KEBall
