import KEBall.DirichletSmoothFieldDifferences
import KEBall.DirichletTensorQuartic

/-!
# An arbitrarily small quartic coefficient at the actual C2 Hessian

A fixed smooth approximation is used only to split the continuous Hessian
into a uniformly small remainder and a reference with bounded differences.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Filter MeasureTheory Metric Set
open scoped ContDiff Topology

namespace KEBall

theorem dirichletFieldDifference_sub {n : ℕ} {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (R : E n ≃ₗᵢ[ℝ] E n) (τ : ℝ) (F G : E n → V) :
    dirichletFieldDifference R τ (fun x => F x - G x) =
      fun x => dirichletFieldDifference R τ F x - dirichletFieldDifference R τ G x := by
  funext x
  simp only [dirichletFieldDifference, smul_sub]
  abel

theorem dirichletWithinRealHessian_difference_eq_spatial {n : ℕ}
    (R : E n ≃ₗᵢ[ℝ] E n) (τ : ℝ) {u : E n → ℝ}
    (hu : ContDiffOn ℝ 2 u (closedUnitBall n)) {x : E n}
    (hx : x ∈ closedUnitBall n) :
    dirichletWithinRealHessian (dirichletOrthogonalDifference R τ u) x =
      dirichletBilinearPullbackCLM R
        (dirichletFieldDifference R τ (dirichletWithinRealHessian u) x) +
      dirichletBilinearPullbackIncrement R τ (dirichletWithinRealHessian u x) := by
  rw [dirichletWithinRealHessian_orthogonal_difference R τ hu hx]
  simp only [dirichletFieldDifference, map_smul, map_sub,
    dirichletBilinearPullbackIncrement, _root_.smul_apply, _root_.sub_apply,
    ContinuousLinearMap.id_apply, dirichletBilinearPullbackCLM_apply, smul_sub]
  abel

private theorem exists_small_quartic_scale (K : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ η > (0 : ℝ), 24 * K * η ^ 2 ≤ ε := by
  have hc : ContinuousAt (fun η : ℝ => 24 * K * η ^ 2) 0 := by fun_prop
  have he : ∀ᶠ η in 𝓝 (0 : ℝ), 24 * K * η ^ 2 < ε := by
    have h₀ : 24 * K * (0 : ℝ) ^ 2 < ε := by simpa using hε
    exact hc.eventually (gt_mem_nhds h₀)
  obtain ⟨δ, hδ, hδb⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨δ / 2, by positivity, (hδb ?_).le⟩
  rw [dist_zero_right, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < δ / 2)]
  linarith

private theorem sq_three_terms_le (a b c : ℝ) :
    (a + b + c) ^ 2 ≤ 3 * a ^ 2 + 3 * b ^ 2 + 3 * c ^ 2 := by
  nlinarith only [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]

theorem exists_dirichlet_discrete_hessian_quartic_small_coefficient {n : ℕ}
    (hn : 0 < n) {u : E n → ℝ}
    (hu : ContDiffOn ℝ 2 u (closedUnitBall n))
    (huS : ContDiffOn ℝ ∞ u (unitBall n))
    (hu0 : ∀ x ∈ unitSphere n, u x = 0)
    (S : E n →L[ℝ] E n) (hS : star S = -S) {ε : ℝ} (hε : 0 < ε) :
    ∃ C ≥ (0 : ℝ), ∀ t : ℝ, t ≠ 0 →
      (∫ x in unitBall n,
        ‖dirichletWithinRealHessian
          (dirichletOrthogonalDifference (orthogonalFlow S hS t) t u) x‖ ^ 4 ∂volume0 n) ≤
      ε * (∫ x in unitBall n,
        ‖dirichletWithinRealHessian
          (dirichletOrthogonalDifference (orthogonalFlow S hS t) t
            (dirichletOrthogonalDifference (orthogonalFlow S hS t) t u)) x‖ ^ 2 ∂volume0 n) +
      C * (∫ x in unitBall n,
        ‖dirichletWithinRealHessian
          (dirichletOrthogonalDifference (orthogonalFlow S hS t) t u) x‖ ^ 2 ∂volume0 n) + C := by
  let K : ℝ := 36 * (2 * n : ℝ) ^ 8
  have hK : 0 ≤ K := by positivity
  obtain ⟨η, hη, hSmall⟩ := exists_small_quartic_scale K hε
  obtain ⟨v, hv, _, hApprox, _⟩ :=
    exists_dirichlet_smooth_zeroBoundary_reference_close_hessian hu huS hu0 hη
  let H := dirichletWithinRealHessian u
  let V := realHessian v
  let Z (x : E n) := H x - V x
  have hH : ContinuousOn H (closedUnitBall n) := continuousOn_dirichletWithinRealHessian hu
  have hVAt (x : E n) (hx : x ∈ closedUnitBall n) : ContDiffAt ℝ ∞ V x :=
    realHessian_contDiffAt (hv.contDiffAt hx)
  have hV : ContinuousOn V (closedUnitBall n) :=
    fun x hx => (hVAt x hx).continuousAt.continuousWithinAt
  have hZ : ContinuousOn Z (closedUnitBall n) := hH.sub hV
  obtain ⟨M₀, hM₀⟩ := (isCompact_closedBall (0 : E n) 1).exists_bound_of_continuousOn hH
  let M := max M₀ 0
  have hM : 0 ≤ M := le_max_right _ _
  have hBoundH (x : E n) (hx : x ∈ closedUnitBall n) : ‖H x‖ ≤ M :=
    (hM₀ x hx).trans (le_max_left _ _)
  obtain ⟨A, hA, B, hB, hRef⟩ := exists_dirichlet_smooth_field_difference_bounds hVAt S hS
  let T := A + 2 * ‖S‖ * M
  let W := 4 * ‖S‖ ^ 2 * M + B
  let C₁ := 384 * K * η ^ 2 * ‖S‖ ^ 2
  let C₂ := 24 * K * η ^ 2 * W ^ 2 + 8 * T ^ 4
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hC₁ : 0 ≤ C₁ := by dsimp [C₁]; positivity
  have hC₂ : 0 ≤ C₂ := by dsimp [C₂]; positivity
  refine ⟨C₁ + C₂, add_nonneg hC₁ hC₂, ?_⟩
  intro t ht
  let R := orthogonalFlow S hS t
  let q := dirichletOrthogonalDifference R t u
  let p := dirichletOrthogonalDifference R t q
  let H₁ := dirichletWithinRealHessian q
  let H₂ := dirichletWithinRealHessian p
  let DZ := dirichletFieldDifference R t Z
  let DDZ := dirichletFieldDifference R t DZ
  have hH₁ : ContinuousOn H₁ (closedUnitBall n) :=
    continuousOn_dirichletWithinRealHessian (contDiffOn_dirichletOrthogonalDifference R t hu)
  have hH₂ : ContinuousOn H₂ (closedUnitBall n) :=
    continuousOn_dirichletWithinRealHessian (contDiffOn_dirichletOrthogonalDifference R t
      (contDiffOn_dirichletOrthogonalDifference R t hu))
  have hDZ := continuousOn_dirichletFieldDifference R t hZ
  have hDDZ := continuousOn_dirichletFieldDifference R t hDZ
  have hFirst (x : E n) (hx : x ∈ closedUnitBall n) : ‖H₁ x‖ ≤ ‖DZ x‖ + T := by
    have hSplit : dirichletFieldDifference R t H x =
        DZ x + dirichletFieldDifference R t V x := by
      dsimp only [DZ, Z]
      rw [dirichletFieldDifference_sub]
      simp only [sub_add_cancel]
    have hInc (Y : E n →L[ℝ] E n →L[ℝ] ℝ) :
        ‖dirichletBilinearPullbackIncrement R t Y‖ ≤ 2 * ‖S‖ * ‖Y‖ :=
      ((dirichletBilinearPullbackIncrement R t).le_opNorm Y).trans
        (mul_le_mul_of_nonneg_right
          (norm_dirichletBilinearPullbackCLM_normalized_increment_le S hS ht) (norm_nonneg Y))
    have he : H₁ x = dirichletBilinearPullbackCLM R
        (dirichletFieldDifference R t H x) + dirichletBilinearPullbackIncrement R t (H x) :=
      dirichletWithinRealHessian_difference_eq_spatial R t hu hx
    rw [he]
    calc
      _ ≤ ‖dirichletBilinearPullbackCLM R (dirichletFieldDifference R t H x)‖ +
          ‖dirichletBilinearPullbackIncrement R t (H x)‖ := norm_add_le _ _
      _ ≤ ‖dirichletFieldDifference R t H x‖ + 2 * ‖S‖ * ‖H x‖ :=
        add_le_add (norm_dirichletBilinearPullback_le R _) (hInc _)
      _ ≤ (‖DZ x‖ + A) + 2 * ‖S‖ * M := by
        apply add_le_add
        · rw [hSplit]
          exact (norm_add_le _ _).trans (add_le_add le_rfl (hRef t ht x hx).1)
        · exact mul_le_mul_of_nonneg_left (hBoundH x hx) (by positivity)
      _ = _ := by dsimp [T]; ring
  have hSecond (x : E n) (hx : x ∈ closedUnitBall n) :
      ‖DDZ x‖ ≤ ‖H₂ x‖ + 4 * ‖S‖ * ‖H₁ x‖ + W := by
    have he : DDZ x = dirichletFieldDifference R t (dirichletFieldDifference R t H) x -
        dirichletFieldDifference R t (dirichletFieldDifference R t V) x := by
      dsimp only [DDZ, DZ, Z]
      rw [dirichletFieldDifference_sub, dirichletFieldDifference_sub]
    rw [he]
    calc
      _ ≤ ‖dirichletFieldDifference R t (dirichletFieldDifference R t H) x‖ +
          ‖dirichletFieldDifference R t (dirichletFieldDifference R t V) x‖ := norm_sub_le _ _
      _ ≤ (‖H₂ x‖ + 4 * ‖S‖ * ‖H₁ x‖ + 4 * ‖S‖ ^ 2 * ‖H x‖) + B :=
        add_le_add (norm_dirichletFieldSecondDifference_withinHessian_le hu S hS ht hx)
          (hRef t ht x hx).2
      _ ≤ (‖H₂ x‖ + 4 * ‖S‖ * ‖H₁ x‖ + 4 * ‖S‖ ^ 2 * M) + B := by
        gcongr
        exact hBoundH x hx
      _ = _ := by dsimp [W]; ring
  letI : NeZero n := ⟨hn.ne'⟩
  letI : IsProbabilityMeasure ((volume0 n).restrict (unitBall n)) :=
    volume0_restrict_isProbability n
  have hInt {f : E n → ℝ} (hf : ContinuousOn f (closedUnitBall n)) :
      IntegrableOn f (unitBall n) (volume0 n) :=
    (dirichlet_memLp_of_continuousOn hn hf 1).integrable le_rfl
  have hFourPoint (x : E n) (hx : x ∈ unitBall n) :
      ‖H₁ x‖ ^ 4 ≤ 8 * ‖DZ x‖ ^ 4 + 8 * T ^ 4 := by
    have h₀ := pow_le_pow_left₀ (norm_nonneg (H₁ x)) (hFirst x (ball_subset_closedBall hx)) 4
    have h₁ := add_pow_le (norm_nonneg (DZ x)) hT 4
    norm_num only at h₁
    nlinarith only [h₀, h₁]
  have hSquarePoint (x : E n) (hx : x ∈ unitBall n) :
      ‖DDZ x‖ ^ 2 ≤ 3 * ‖H₂ x‖ ^ 2 + 48 * ‖S‖ ^ 2 * ‖H₁ x‖ ^ 2 + 3 * W ^ 2 := by
    have h₀ := pow_le_pow_left₀ (norm_nonneg (DDZ x)) (hSecond x (ball_subset_closedBall hx)) 2
    have h₁ := sq_three_terms_le ‖H₂ x‖ (4 * ‖S‖ * ‖H₁ x‖) W
    nlinarith only [h₀, h₁]
  have hFour : (∫ x in unitBall n, ‖H₁ x‖ ^ 4 ∂volume0 n) ≤
      8 * (∫ x in unitBall n, ‖DZ x‖ ^ 4 ∂volume0 n) + 8 * T ^ 4 := by
    have h := setIntegral_mono_on (hInt (hH₁.norm.pow 4))
      (hInt (((hDZ.norm.pow 4).const_mul 8).add continuousOn_const))
      measurableSet_ball hFourPoint
    simp only [Pi.add_apply, Pi.pow_apply] at h
    have hAdd := integral_add ((hInt (hDZ.norm.pow 4)).const_mul 8) (integrable_const (8 * T ^ 4))
    simp only [Pi.add_apply, Pi.pow_apply] at hAdd
    rw [hAdd, integral_const_mul, integral_const, probReal_univ, one_smul] at h
    exact h
  have hSquare : (∫ x in unitBall n, ‖DDZ x‖ ^ 2 ∂volume0 n) ≤
      3 * (∫ x in unitBall n, ‖H₂ x‖ ^ 2 ∂volume0 n) +
        48 * ‖S‖ ^ 2 * (∫ x in unitBall n, ‖H₁ x‖ ^ 2 ∂volume0 n) + 3 * W ^ 2 := by
    have h := setIntegral_mono_on (hInt (hDDZ.norm.pow 2))
      (hInt ((((hH₂.norm.pow 2).const_mul 3).add
        ((hH₁.norm.pow 2).const_mul (48 * ‖S‖ ^ 2))).add continuousOn_const))
      measurableSet_ball hSquarePoint
    simp only [Pi.add_apply, Pi.pow_apply] at h
    have hAdd₀ := integral_add (((hInt (hH₂.norm.pow 2)).const_mul 3).add
      ((hInt (hH₁.norm.pow 2)).const_mul (48 * ‖S‖ ^ 2))) (integrable_const (3 * W ^ 2))
    have hAdd₁ := integral_add ((hInt (hH₂.norm.pow 2)).const_mul 3)
      ((hInt (hH₁.norm.pow 2)).const_mul (48 * ‖S‖ ^ 2))
    simp only [Pi.add_apply, Pi.pow_apply] at hAdd₀ hAdd₁
    rw [hAdd₀, hAdd₁, integral_const_mul, integral_const_mul, integral_const,
      probReal_univ, one_smul] at h
    exact h
  have hQ : (∫ x in unitBall n, ‖DZ x‖ ^ 4 ∂volume0 n) ≤
      K * η ^ 2 * ∫ x in unitBall n, ‖DDZ x‖ ^ 2 ∂volume0 n :=
    integral_dirichletFieldDifference_norm_pow_four_le hn R ht hZ hη.le
      (fun x hx => (hApprox x (ball_subset_closedBall hx)).le)
  let E₁ := ∫ x in unitBall n, ‖H₁ x‖ ^ 2 ∂volume0 n
  let E₂ := ∫ x in unitBall n, ‖H₂ x‖ ^ 2 ∂volume0 n
  have hE₁ : 0 ≤ E₁ := integral_nonneg (fun _ => sq_nonneg _)
  have hE₂ : 0 ≤ E₂ := integral_nonneg (fun _ => sq_nonneg _)
  have hQ₀ := mul_le_mul_of_nonneg_left hQ (by norm_num : (0 : ℝ) ≤ 8)
  have hSq₀ := mul_le_mul_of_nonneg_left hSquare
    (by positivity : 0 ≤ 8 * K * η ^ 2)
  have hSm := mul_le_mul_of_nonneg_right hSmall hE₂
  have hCE := mul_le_mul_of_nonneg_right (show C₁ ≤ C₁ + C₂ from le_add_of_nonneg_right hC₂) hE₁
  change (∫ x in unitBall n, ‖H₁ x‖ ^ 4 ∂volume0 n) ≤
    ε * E₂ + (C₁ + C₂) * E₁ + (C₁ + C₂)
  dsimp only [C₁, C₂] at hCE ⊢
  change (∫ x in unitBall n, ‖H₁ x‖ ^ 4 ∂volume0 n) ≤
    8 * (∫ x in unitBall n, ‖DZ x‖ ^ 4 ∂volume0 n) + 8 * T ^ 4 at hFour
  dsimp only [E₁, E₂] at hSm hCE
  nlinarith only [hFour, hQ₀, hSq₀, hSm, hCE, hC₁]

end KEBall
