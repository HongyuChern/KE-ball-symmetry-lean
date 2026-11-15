import KEBall.DirichletIteratedPotentialEnergy

/-! Separating and absorbing the small-step highest Hessian in the exact error. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Filter Matrix MeasureTheory Metric Set
open scoped BigOperators ComplexOrder ContDiff Matrix.Norms.Elementwise Topology

namespace KEBall

local notation "e[" n "]" => EuclideanSpace.basisFun (Fin (2 * n)) ℝ

theorem continuousOn_dirichletDeterminantDifferenceRemainder {n m : ℕ}
    (R : E n ≃ₗᵢ[ℝ] E n) (τ : ℝ) {F : E n → Matrix (Fin m) (Fin m) ℂ}
    (hF : ContinuousOn F (closedUnitBall n)) (k : ℕ) :
    ContinuousOn (dirichletDeterminantDifferenceRemainder R τ F k) (closedUnitBall n) :=
  continuousOn_finsetSum _ (fun σ _ =>
    (continuousOn_dirichletProductDifferenceRemainder R τ Finset.univ
      (fun i y => F y (σ i) i) (fun i _ => (continuous_apply i).comp_continuousOn
        ((continuous_apply (σ i)).comp_continuousOn hF)) k).const_mul _)

theorem exists_dirichlet_iterated_leading_field_uniform_bound {n : ℕ} {u : E n → ℝ}
    (hu : ContDiffOn ℝ 2 u (closedUnitBall n))
    (S : E n →L[ℝ] E n) (hS : star S = -S) (k : ℕ) :
    ∃ δ > (0 : ℝ), ∃ M ≥ (0 : ℝ), ∀ t : ℝ, |t| < δ → ∀ x ∈ closedUnitBall n,
      ‖dirichletIteratedPotentialLeadingField (orthogonalFlow S hS t) u k x‖ ≤ M := by
  let A (x : E n) := dirichletContractionCLM n
    (dirichletCofactorOfMatrix (dirichletWithinComplexHessian u x))
  have hAC : ContinuousOn A (closedUnitBall n) :=
    (dirichletContractionCLM n).continuous.comp_continuousOn
      (contDiff_dirichletCofactorOfMatrix.continuous.comp_continuousOn
        (continuousOn_dirichletWithinComplexHessian_of_C2 hu))
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : E n) 1).exists_bound_of_continuousOn hAC
  obtain ⟨δ, hδ, hNear⟩ := Metric.eventually_nhds_iff.mp
    (eventually_dirichletDeterminantLeadingField_close hu S hS k (by norm_num : (0 : ℝ) < 1))
  refine ⟨δ, hδ, max M 0 + 1, by positivity, ?_⟩
  intro t ht x hx
  have h := hNear (show dist t 0 < δ by simpa only [dist_zero_right, Real.norm_eq_abs] using ht) x hx
  let L := dirichletIteratedPotentialLeadingField (orthogonalFlow S hS t) u k x
  have hDiff : ‖L - A x‖ < 1 := by
    rw [norm_sub_rev]
    exact h
  calc
    ‖L‖ = ‖(L - A x) + A x‖ := by rw [sub_add_cancel]
    _ ≤ ‖L - A x‖ + ‖A x‖ := norm_add_le _ _
    _ ≤ 1 + max M 0 := add_le_add hDiff.le ((hM x hx).trans (le_max_left _ _))
    _ = _ := by ring

private theorem sq_three_sum_le (a b c : ℝ) :
    (a + b + c) ^ 2 ≤ 3 * a ^ 2 + 3 * b ^ 2 + 3 * c ^ 2 := by
  nlinarith only [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]

theorem dirichlet_iterated_potential_error_sq_le {n : ℕ} {u : E n → ℝ}
    (hu : ContDiffOn ℝ 2 u (closedUnitBall n))
    (S : E n →L[ℝ] E n) (hS : star S = -S) (k : ℕ)
    {M t : ℝ} (hM : 0 ≤ M) (ht : t ≠ 0) {x : E n} (hx : x ∈ closedUnitBall n)
    (hBound : ‖dirichletIteratedPotentialLeadingField (orthogonalFlow S hS t) u k x‖ ≤ M) :
    let R := orthogonalFlow S hS t
    (dirichletIteratedPotentialDeterminantError R t u k x) ^ 2 ≤
      3 * ((dirichletDeterminantDifferenceRemainder R t (dirichletWithinComplexHessian u) k x).re) ^ 2 +
      (3 * (M * (1 + 2 * ‖S‖) ^ (k + 1)) ^ 2 * (k + 1 : ℝ)) *
        (∑ j ∈ Finset.range (k + 1),
          ‖dirichletWithinRealHessian (dirichletIteratedOrthogonalDifference R t u j) x‖ ^ 2) +
      (3 * (M * (2 * (k + 1 : ℝ) * ‖S‖)) ^ 2 * (2 * n : ℝ) ^ 2) * t ^ 2 *
        (∑ i, ∑ j,
          (dirichletWithinRealHessian (dirichletIteratedOrthogonalDifference R t u (k + 1)) x
            (e[n] i) (e[n] j)) ^ 2) := by
  dsimp only
  let R := orthogonalFlow S hS t
  let B : ℝ := (1 + 2 * ‖S‖) ^ (k + 1)
  let N : ℝ := 2 * (k + 1 : ℝ) * ‖S‖
  let H := dirichletWithinRealHessian (dirichletIteratedOrthogonalDifference R t u (k + 1)) x
  let Z (j : ℕ) := ‖dirichletWithinRealHessian (dirichletIteratedOrthogonalDifference R t u j) x‖
  let L := dirichletIteratedPotentialLeadingField R u k x
  let W := dirichletIteratedFieldDifference R t (dirichletWithinRealHessian u) (k + 1) x - H
  let r := (dirichletDeterminantDifferenceRemainder R t (dirichletWithinComplexHessian u) k x).re
  have hW : ‖W‖ ≤ B * (∑ j ∈ Finset.range (k + 1), Z j) + (N * |t|) * ‖H‖ := by
    simpa only [R, B, N, Nat.cast_add, Nat.cast_one] using
      norm_dirichletIteratedFieldDifference_sub_highestHessian_le hu S hS ht (k + 1) hx
  have hLW : |L W| ≤ M * (B * (∑ j ∈ Finset.range (k + 1), Z j) + (N * |t|) * ‖H‖) := by
    have h := L.le_opNorm W
    rw [Real.norm_eq_abs] at h
    exact h.trans ((mul_le_mul_of_nonneg_right hBound (norm_nonneg W)).trans
      (mul_le_mul_of_nonneg_left hW hM))
  have hE : |dirichletIteratedPotentialDeterminantError R t u k x| ≤
      |r| + (M * B) * (∑ j ∈ Finset.range (k + 1), Z j) + (M * N) * |t| * ‖H‖ := by
    have h := (abs_add_le r (L W)).trans (add_le_add le_rfl hLW)
    exact h.trans_eq (by ring)
  have hSq := pow_le_pow_left₀ (abs_nonneg _) hE 2
  rw [sq_abs] at hSq
  have hThree := sq_three_sum_le |r|
    ((M * B) * (∑ j ∈ Finset.range (k + 1), Z j)) ((M * N) * |t| * ‖H‖)
  rw [sq_abs] at hThree
  have hSum := sq_sum_le_card_mul_sum_sq (s := Finset.range (k + 1)) (f := Z)
  simp only [Finset.card_range, Nat.cast_add, Nat.cast_one] at hSum
  have hSumMul := mul_le_mul_of_nonneg_left hSum (by positivity : 0 ≤ 3 * (M * B) ^ 2)
  have hH := mul_le_mul_of_nonneg_left (norm_dirichlet_bilinear_sq_le_sum_entries H)
    (by positivity : 0 ≤ 3 * (M * N) ^ 2 * |t| ^ 2)
  rw [sq_abs] at hH
  simp only [mul_pow, sq_abs] at hThree
  change _ ≤ 3 * r ^ 2 + (3 * (M * B) ^ 2 * (k + 1 : ℝ)) *
    (∑ j ∈ Finset.range (k + 1), Z j ^ 2) +
    (3 * (M * N) ^ 2 * (2 * n : ℝ) ^ 2) * t ^ 2 *
      (∑ i, ∑ j, (H (e[n] i) (e[n] j)) ^ 2)
  nlinarith only [hSq, hThree, hSumMul, hH]

theorem integral_dirichlet_iterated_potential_error_sq_le {n : ℕ}
    (hn : 0 < n) {u : E n → ℝ} (hu : ContDiffOn ℝ 2 u (closedUnitBall n))
    (S : E n →L[ℝ] E n) (hS : star S = -S) (k : ℕ)
    {M t : ℝ} (hM : 0 ≤ M) (ht : t ≠ 0)
    (hBound : ∀ x ∈ closedUnitBall n,
      ‖dirichletIteratedPotentialLeadingField (orthogonalFlow S hS t) u k x‖ ≤ M) :
    let R := orthogonalFlow S hS t
    (∫ x in unitBall n, (dirichletIteratedPotentialDeterminantError R t u k x) ^ 2 ∂volume0 n) ≤
      3 * (∫ x in unitBall n,
        ((dirichletDeterminantDifferenceRemainder R t (dirichletWithinComplexHessian u) k x).re) ^ 2 ∂volume0 n) +
      (3 * (M * (1 + 2 * ‖S‖) ^ (k + 1)) ^ 2 * (k + 1 : ℝ)) *
        (∑ j ∈ Finset.range (k + 1), ∫ x in unitBall n,
          ‖dirichletWithinRealHessian (dirichletIteratedOrthogonalDifference R t u j) x‖ ^ 2 ∂volume0 n) +
      (3 * (M * (2 * (k + 1 : ℝ) * ‖S‖)) ^ 2 * (2 * n : ℝ) ^ 2) * t ^ 2 *
        (∫ x in unitBall n, ∑ i, ∑ j,
          (dirichletWithinRealHessian (dirichletIteratedOrthogonalDifference R t u (k + 1)) x
            (e[n] i) (e[n] j)) ^ 2 ∂volume0 n) := by
  dsimp only
  let R := orthogonalFlow S hS t
  let r (x : E n) := (dirichletDeterminantDifferenceRemainder R t (dirichletWithinComplexHessian u) k x).re
  let e := dirichletIteratedPotentialDeterminantError R t u k
  let H (j : ℕ) := dirichletWithinRealHessian (dirichletIteratedOrthogonalDifference R t u j)
  let l (x : E n) := ∑ j ∈ Finset.range (k + 1), ‖H j x‖ ^ 2
  let z (x : E n) := ∑ i, ∑ j, (H (k + 1) x (e[n] i) (e[n] j)) ^ 2
  let K : ℝ := 3 * (M * (1 + 2 * ‖S‖) ^ (k + 1)) ^ 2 * (k + 1 : ℝ)
  let T : ℝ := 3 * (M * (2 * (k + 1 : ℝ) * ‖S‖)) ^ 2 * (2 * n : ℝ) ^ 2 * t ^ 2
  have hH (j : ℕ) : ContinuousOn (H j) (closedUnitBall n) :=
    continuousOn_dirichletWithinRealHessian (contDiffOn_dirichletIteratedOrthogonalDifference R t hu j)
  have hr : ContinuousOn r (closedUnitBall n) := Complex.continuous_re.comp_continuousOn
    (continuousOn_dirichletDeterminantDifferenceRemainder R t
      (continuousOn_dirichletWithinComplexHessian_of_C2 hu) k)
  have he : ContinuousOn e (closedUnitBall n) := continuousOn_dirichletIteratedPotentialDeterminantError R t hu k
  have hl : ContinuousOn l (closedUnitBall n) :=
    continuousOn_finsetSum _ (fun j _ => (hH j).norm.pow 2)
  have hz : ContinuousOn z (closedUnitBall n) :=
    continuousOn_finsetSum _ (fun i _ => continuousOn_finsetSum _ (fun j _ =>
      (((hH (k + 1)).clm_apply continuousOn_const).clm_apply continuousOn_const).pow 2))
  letI : NeZero n := ⟨hn.ne'⟩
  letI : IsProbabilityMeasure ((volume0 n).restrict (unitBall n)) := volume0_restrict_isProbability n
  have hInt {F : E n → ℝ} (hF : ContinuousOn F (closedUnitBall n)) :
      IntegrableOn F (unitBall n) (volume0 n) :=
    (dirichlet_memLp_of_continuousOn hn hF 1).integrable le_rfl
  have hPoint (x : E n) (hx : x ∈ unitBall n) : e x ^ 2 ≤ 3 * r x ^ 2 + K * l x + T * z x :=
    dirichlet_iterated_potential_error_sq_le hu S hS k hM ht (ball_subset_closedBall hx)
      (hBound x (ball_subset_closedBall hx))
  have h := setIntegral_mono_on (hInt (he.pow 2))
    (hInt ((((hr.pow 2).const_mul 3).add (hl.const_mul K)).add (hz.const_mul T)))
    measurableSet_ball hPoint
  have hAdd₁ := integral_add ((hInt (hr.pow 2)).const_mul 3) ((hInt hl).const_mul K)
  have hAdd₂ := integral_add (((hInt (hr.pow 2)).const_mul 3).add ((hInt hl).const_mul K))
    ((hInt hz).const_mul T)
  have hSwap : (∫ x in unitBall n, l x ∂volume0 n) =
      ∑ j ∈ Finset.range (k + 1), ∫ x in unitBall n, ‖H j x‖ ^ 2 ∂volume0 n := by
    simpa only [Pi.pow_apply] using integral_finset_sum (Finset.range (k + 1))
      (fun j _ => hInt ((hH j).norm.pow 2))
  simp only [Pi.add_apply, Pi.pow_apply] at h hAdd₁ hAdd₂
  rw [hAdd₂, hAdd₁, integral_const_mul, integral_const_mul, integral_const_mul, hSwap] at h
  exact h

theorem exists_dirichlet_iterated_polynomial_remainder_energy_bound {n : ℕ}
    (hn : 0 < n) {u f : E n → ℝ}
    (hu : ContDiffOn ℝ 2 u (closedUnitBall n)) (huS : ContDiffOn ℝ ∞ u (unitBall n))
    (hu0 : ∀ x ∈ unitSphere n, u x = 0)
    (hPos : ∀ x ∈ closedUnitBall n, (dirichletWithinComplexHessian u x).PosDef)
    (hf : SmoothNear (closedUnitBall n) f)
    (hEq : ∀ x ∈ unitBall n, (complexHessian u x).det.re = f x)
    (S : E n →L[ℝ] E n) (hS : star S = -S) (k : ℕ) :
    ∃ δ > (0 : ℝ), ∃ C ≥ (0 : ℝ), ∀ t : ℝ, t ≠ 0 → |t| < δ →
      let R := orthogonalFlow S hS t
      (∫ x in unitBall n, ∑ i, ∑ j,
        (dirichletWithinRealHessian (dirichletIteratedOrthogonalDifference R t u (k + 1)) x
          (e[n] i) (e[n] j)) ^ 2 ∂volume0 n) ≤
        C * (∫ x in unitBall n,
          ((dirichletDeterminantDifferenceRemainder R t (dirichletWithinComplexHessian u) k x).re) ^ 2 ∂volume0 n) +
        C * (∑ j ∈ Finset.range (k + 1), ∫ x in unitBall n,
          ‖dirichletWithinRealHessian (dirichletIteratedOrthogonalDifference R t u j) x‖ ^ 2 ∂volume0 n) + C := by
  obtain ⟨δ₀, hδ₀, A, hA, hEnergy⟩ :=
    exists_dirichlet_iterated_potential_error_energy_bound hn hu huS hu0 hPos hf hEq S hS k
  obtain ⟨δ₁, hδ₁, M, hM, hLeading⟩ := exists_dirichlet_iterated_leading_field_uniform_bound hu S hS k
  let K : ℝ := 3 * (M * (1 + 2 * ‖S‖) ^ (k + 1)) ^ 2 * (k + 1 : ℝ)
  let T : ℝ := 3 * (M * (2 * (k + 1 : ℝ) * ‖S‖)) ^ 2 * (2 * n : ℝ) ^ 2
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hc : ContinuousAt (fun t : ℝ => A * T * t ^ 2) 0 := by fun_prop
  have hsmall : ∀ᶠ t : ℝ in 𝓝 0, A * T * t ^ 2 < 1 / 2 :=
    hc.eventually (gt_mem_nhds (by norm_num : A * T * (0 : ℝ) ^ 2 < 1 / 2))
  obtain ⟨δ₂, hδ₂, hTime⟩ := Metric.eventually_nhds_iff.mp hsmall
  let C : ℝ := 8 * A + 2 * A * K
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨min δ₀ (min δ₁ δ₂), lt_min hδ₀ (lt_min hδ₁ hδ₂), C, hC, ?_⟩
  intro t ht htδ
  dsimp only
  have ht₀ : |t| < δ₀ := htδ.trans_le (min_le_left _ _)
  have ht₁ : |t| < δ₁ := htδ.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have ht₂ : |t| < δ₂ := htδ.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  let R := orthogonalFlow S hS t
  let E := ∫ x in unitBall n, ∑ i, ∑ j,
    (dirichletWithinRealHessian (dirichletIteratedOrthogonalDifference R t u (k + 1)) x
      (e[n] i) (e[n] j)) ^ 2 ∂volume0 n
  let P := ∫ x in unitBall n,
    ((dirichletDeterminantDifferenceRemainder R t (dirichletWithinComplexHessian u) k x).re) ^ 2 ∂volume0 n
  let L := ∑ j ∈ Finset.range (k + 1), ∫ x in unitBall n,
    ‖dirichletWithinRealHessian (dirichletIteratedOrthogonalDifference R t u j) x‖ ^ 2 ∂volume0 n
  have hE0 : 0 ≤ E := integral_nonneg (fun _ => Finset.sum_nonneg (fun _ _ =>
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
  have hP0 : 0 ≤ P := integral_nonneg (fun _ => sq_nonneg _)
  have hL0 : 0 ≤ L := Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => sq_nonneg _))
  have hErr := integral_dirichlet_iterated_potential_error_sq_le hn hu S hS k hM ht (hLeading t ht₁)
  have hE := (hEnergy t ht ht₀).trans (add_le_add
    (mul_le_mul_of_nonneg_left hErr hA) le_rfl)
  have hs : A * T * t ^ 2 ≤ 1 / 2 :=
    (hTime (show dist t 0 < δ₂ by simpa only [dist_zero_right, Real.norm_eq_abs] using ht₂)).le
  have hsE := mul_le_mul_of_nonneg_right hs hE0
  have hp : 6 * A * P ≤ C * P := mul_le_mul_of_nonneg_right
    (show 6 * A ≤ C by dsimp [C]; nlinarith only [hA, mul_nonneg hA hK]) hP0
  have hl : 2 * A * K * L ≤ C * L := mul_le_mul_of_nonneg_right
    (show 2 * A * K ≤ C by dsimp [C]; linarith) hL0
  have hb : 2 * A ≤ C := by dsimp [C]; nlinarith only [hA, mul_nonneg hA hK]
  change E ≤ C * P + C * L + C
  change E ≤ A * (3 * P + K * L + T * t ^ 2 * E) + A at hE
  nlinarith only [hE, hsE, hp, hl, hb]

end KEBall
