import KEBall.DirichletSecondDiscreteHessianEstimate

/-!
# Iterated spatial tensor differences and actual Hessian pullbacks

The recurrence holds for every order at the actual closed-ball C2 level.
The norm constant is independent of the nonzero rotation step.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Filter MeasureTheory Metric Set
open scoped BigOperators ContDiff

namespace KEBall

noncomputable def dirichletIteratedFieldDifference {n : ℕ} {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (R : E n ≃ₗᵢ[ℝ] E n) (τ : ℝ) (F : E n → V) : ℕ → E n → V
  | 0 => F
  | k + 1 => dirichletFieldDifference R τ (dirichletIteratedFieldDifference R τ F k)

theorem dirichletIteratedFieldDifference_succ_right {n : ℕ} {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (R : E n ≃ₗᵢ[ℝ] E n) (τ : ℝ) (F : E n → V) (k : ℕ) :
    dirichletIteratedFieldDifference R τ (dirichletFieldDifference R τ F) k =
      dirichletIteratedFieldDifference R τ F (k + 1) := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [dirichletIteratedFieldDifference, ih]

theorem dirichletIteratedFieldDifference_add {n : ℕ} {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (R : E n ≃ₗᵢ[ℝ] E n) (τ : ℝ) (F G : E n → V) (k : ℕ) :
    dirichletIteratedFieldDifference R τ (fun x => F x + G x) k =
      fun x => dirichletIteratedFieldDifference R τ F k x +
        dirichletIteratedFieldDifference R τ G k x := by
  induction k with
  | zero => rfl
  | succ k ih => rw [dirichletIteratedFieldDifference, ih, dirichletFieldDifference_add]; rfl

theorem dirichletIteratedFieldDifference_clm {n : ℕ} {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (R : E n ≃ₗᵢ[ℝ] E n) (τ : ℝ) (L : V →L[ℝ] W) (F : E n → V) (k : ℕ) :
    dirichletIteratedFieldDifference R τ (fun x => L (F x)) k =
      fun x => L (dirichletIteratedFieldDifference R τ F k x) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [dirichletIteratedFieldDifference, ih, dirichletFieldDifference_clm]; rfl

theorem dirichletIteratedFieldDifference_congr_closed {n : ℕ} {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (R : E n ≃ₗᵢ[ℝ] E n) (τ : ℝ) {F G : E n → V}
    (h : EqOn F G (closedUnitBall n)) (k : ℕ) :
    EqOn (dirichletIteratedFieldDifference R τ F k)
      (dirichletIteratedFieldDifference R τ G k) (closedUnitBall n) := by
  induction k with
  | zero => exact h
  | succ k ih => exact dirichletFieldDifference_congr_closed R τ ih

theorem continuousOn_dirichletIteratedFieldDifference {n : ℕ} {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (R : E n ≃ₗᵢ[ℝ] E n) (τ : ℝ) {F : E n → V}
    (hF : ContinuousOn F (closedUnitBall n)) (k : ℕ) :
    ContinuousOn (dirichletIteratedFieldDifference R τ F k) (closedUnitBall n) := by
  induction k with
  | zero => exact hF
  | succ k ih => exact continuousOn_dirichletFieldDifference R τ ih

theorem dirichletIteratedFieldDifference_real {n : ℕ}
    (R : E n ≃ₗᵢ[ℝ] E n) (τ : ℝ) (F : E n → ℝ) (k : ℕ) :
    dirichletIteratedFieldDifference R τ F k = dirichletIteratedOrthogonalDifference R τ F k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [dirichletIteratedFieldDifference, ih, dirichletFieldDifference_real]
    rfl

theorem dirichletIteratedOrthogonalDifference_succ_right {n : ℕ}
    (R : E n ≃ₗᵢ[ℝ] E n) (τ : ℝ) (F : E n → ℝ) (k : ℕ) :
    dirichletIteratedOrthogonalDifference R τ (dirichletOrthogonalDifference R τ F) k =
      dirichletIteratedOrthogonalDifference R τ F (k + 1) := by
  simpa only [dirichletFieldDifference_real, dirichletIteratedFieldDifference_real] using
    dirichletIteratedFieldDifference_succ_right R τ F k

theorem dirichletIteratedFieldDifference_bilinear_apply {n : ℕ}
    (R : E n ≃ₗᵢ[ℝ] E n) (τ : ℝ)
    (H : E n → E n →L[ℝ] E n →L[ℝ] ℝ) (k : ℕ) (x a b : E n) :
    dirichletIteratedFieldDifference R τ H k x a b =
      dirichletIteratedOrthogonalDifference R τ (fun y => H y a b) k x := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    simp only [dirichletIteratedFieldDifference, dirichletFieldDifference_bilinear_apply,
      dirichletIteratedOrthogonalDifference]
    congr 1
    funext y
    exact ih y

theorem dirichletIteratedFieldDifference_withinHessian_succ {n : ℕ}
    (R : E n ≃ₗᵢ[ℝ] E n) (τ : ℝ) {u : E n → ℝ}
    (hu : ContDiffOn ℝ 2 u (closedUnitBall n)) (k : ℕ) {x : E n}
    (hx : x ∈ closedUnitBall n) :
    dirichletIteratedFieldDifference R τ (dirichletWithinRealHessian u) (k + 1) x =
      dirichletBilinearPullbackCLM R.symm
        (dirichletIteratedFieldDifference R τ
          (dirichletWithinRealHessian (dirichletOrthogonalDifference R τ u)) k x) +
      dirichletBilinearPullbackIncrement R.symm τ
        (dirichletIteratedFieldDifference R τ (dirichletWithinRealHessian u) k x) := by
  rw [← dirichletIteratedFieldDifference_succ_right]
  have he := fun y hy => dirichletFieldDifference_withinHessian R τ hu (x := y) hy
  rw [dirichletIteratedFieldDifference_congr_closed R τ he k hx,
    dirichletIteratedFieldDifference_add, dirichletIteratedFieldDifference_clm,
    dirichletIteratedFieldDifference_clm]

theorem norm_dirichletIteratedFieldDifference_withinHessian_le {n : ℕ}
    {u : E n → ℝ} (hu : ContDiffOn ℝ 2 u (closedUnitBall n))
    (S : E n →L[ℝ] E n) (hS : star S = -S) {t : ℝ} (ht : t ≠ 0)
    (k : ℕ) {x : E n} (hx : x ∈ closedUnitBall n) :
    ‖dirichletIteratedFieldDifference (orthogonalFlow S hS t) t
      (dirichletWithinRealHessian u) k x‖ ≤
      (1 + 2 * ‖S‖) ^ k * ∑ j ∈ Finset.range (k + 1),
        ‖dirichletWithinRealHessian
          (dirichletIteratedOrthogonalDifference (orthogonalFlow S hS t) t u j) x‖ := by
  let R := orthogonalFlow S hS t
  let M := 2 * ‖S‖
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hA : 0 ≤ 1 + M := by positivity
  induction k generalizing u with
  | zero => simp [dirichletIteratedFieldDifference, dirichletIteratedOrthogonalDifference]
  | succ k ih =>
    let q := dirichletOrthogonalDifference R t u
    let L := dirichletBilinearPullbackCLM R.symm
    let C := dirichletBilinearPullbackIncrement R.symm t
    have hq := contDiffOn_dirichletOrthogonalDifference R t hu
    have hL (H : E n →L[ℝ] E n →L[ℝ] ℝ) : ‖L H‖ ≤ ‖H‖ :=
      norm_dirichletBilinearPullback_le R.symm H
    have hC (H : E n →L[ℝ] E n →L[ℝ] ℝ) : ‖C H‖ ≤ M * ‖H‖ :=
      (C.le_opNorm H).trans (mul_le_mul_of_nonneg_right
        (norm_dirichletBilinearPullbackIncrement_flow_symm_le S hS ht) (norm_nonneg H))
    let F (j : ℕ) := ‖dirichletWithinRealHessian (dirichletIteratedOrthogonalDifference R t u j) x‖
    let Z := ∑ j ∈ Finset.range (k + 1 + 1), F j
    have hSum₀ : (∑ j ∈ Finset.range (k + 1), F j) ≤ Z := by
      dsimp only [Z]
      rw [Finset.sum_range_succ F (k + 1)]
      exact le_add_of_nonneg_right (norm_nonneg (dirichletWithinRealHessian
        (dirichletIteratedOrthogonalDifference R t u (k + 1)) x))
    have hSum₁ : (∑ j ∈ Finset.range (k + 1), F (j + 1)) ≤ Z := by
      dsimp only [Z]
      rw [Finset.sum_range_succ' F (k + 1)]
      exact le_add_of_nonneg_right (norm_nonneg (dirichletWithinRealHessian u x))
    have h₀ := (ih hu).trans (mul_le_mul_of_nonneg_left hSum₀ (pow_nonneg hA k))
    have h₁ : ‖dirichletIteratedFieldDifference R t (dirichletWithinRealHessian q) k x‖ ≤
        (1 + M) ^ k * ∑ j ∈ Finset.range (k + 1), F (j + 1) := by
      simpa only [q, R, M, F, dirichletIteratedOrthogonalDifference_succ_right] using ih (u := q) hq
    have h₁' : ‖dirichletIteratedFieldDifference R t (dirichletWithinRealHessian q) k x‖ ≤
        (1 + M) ^ k * Z :=
      h₁.trans (mul_le_mul_of_nonneg_left hSum₁ (pow_nonneg hA k))
    rw [dirichletIteratedFieldDifference_withinHessian_succ _ _ hu k hx]
    change ‖L (dirichletIteratedFieldDifference R t (dirichletWithinRealHessian q) k x) +
      C (dirichletIteratedFieldDifference R t (dirichletWithinRealHessian u) k x)‖ ≤ (1 + M) ^ (k + 1) * Z
    calc
      _ ≤ ‖dirichletIteratedFieldDifference R t (dirichletWithinRealHessian q) k x‖ +
          M * ‖dirichletIteratedFieldDifference R t (dirichletWithinRealHessian u) k x‖ :=
        (norm_add_le _ _).trans (add_le_add (hL _) (hC _))
      _ ≤ (1 + M) ^ k * Z + M * ((1 + M) ^ k * Z) :=
        add_le_add h₁' (mul_le_mul_of_nonneg_left h₀ hM)
      _ = _ := by rw [pow_succ]; ring

theorem contDiffAt_dirichletIteratedFieldDifference_closed {n : ℕ} {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] {m : ℕ∞ω}
    (R : E n ≃ₗᵢ[ℝ] E n) (τ : ℝ) {F : E n → V}
    (hF : ∀ x ∈ closedUnitBall n, ContDiffAt ℝ m F x) (k : ℕ)
    {x : E n} (hx : x ∈ closedUnitBall n) :
    ContDiffAt ℝ m (dirichletIteratedFieldDifference R τ F k) x := by
  induction k generalizing x with
  | zero => exact hF x hx
  | succ k ih =>
    have hxR : R x ∈ closedUnitBall n := by
      simpa only [closedUnitBall, mem_closedBall_zero_iff, R.norm_map] using hx
    exact (((ih hxR).comp x R.toContinuousLinearEquiv.contDiff.contDiffAt).sub (ih hx)).const_smul τ⁻¹

theorem dirichletFieldDifference_angular_flow {n : ℕ} {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] {F : E n → V}
    (hF : ∀ x ∈ closedUnitBall n, ContDiffAt ℝ ∞ F x)
    (S : E n →L[ℝ] E n) (hS : star S = -S) (t : ℝ)
    {x : E n} (hx : x ∈ closedUnitBall n) :
    fderiv ℝ (dirichletFieldDifference (orthogonalFlow S hS t) t F) x (S x) =
      dirichletFieldDifference (orthogonalFlow S hS t) t
        (fun y => fderiv ℝ F y (S y)) x := by
  let R := orthogonalFlow S hS t
  let Q := t⁻¹ • ((fderiv ℝ F (R x)).comp R.toContinuousLinearEquiv.toContinuousLinearMap -
    fderiv ℝ F x)
  have hD : HasFDerivAt (dirichletFieldDifference R t F) Q x := by
    have h₀ := ((hF x hx).differentiableAt (by simp)).hasFDerivAt
    have h₁ := (((hF (R x) (orthogonalFlow_mapsTo_closedUnitBall S hS t hx)).differentiableAt
      (by simp)).hasFDerivAt.comp x R.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt)
    convert! (h₁.sub h₀).const_smul t⁻¹ using 1
  rw [hD.fderiv]
  change t⁻¹ • (fderiv ℝ F (R x) (R (S x)) - fderiv ℝ F x (S x)) =
    t⁻¹ • (fderiv ℝ F (R x) (S (R x)) - fderiv ℝ F x (S x))
  rw [orthogonalFlow_apply_generator]

theorem dirichletIteratedFieldDifference_angular_flow {n : ℕ} {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] {F : E n → V}
    (hF : ∀ x ∈ closedUnitBall n, ContDiffAt ℝ ∞ F x)
    (S : E n →L[ℝ] E n) (hS : star S = -S) (t : ℝ) (k : ℕ)
    {x : E n} (hx : x ∈ closedUnitBall n) :
    fderiv ℝ (dirichletIteratedFieldDifference (orthogonalFlow S hS t) t F k) x (S x) =
      dirichletIteratedFieldDifference (orthogonalFlow S hS t) t
        (fun y => fderiv ℝ F y (S y)) k x := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    change fderiv ℝ (dirichletFieldDifference _ _ (dirichletIteratedFieldDifference _ _ F k)) x (S x) =
      dirichletFieldDifference _ _ (dirichletIteratedFieldDifference _ _ (fun y => fderiv ℝ F y (S y)) k) x
    rw [dirichletFieldDifference_angular_flow
      (fun y hy => contDiffAt_dirichletIteratedFieldDifference_closed _ _ hF k hy) S hS t hx]
    exact dirichletFieldDifference_congr_closed _ _ (fun y hy => ih hy) hx

theorem exists_dirichlet_smooth_field_iterated_difference_bound {n : ℕ} {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] {F : E n → V}
    (hF : ∀ x ∈ closedUnitBall n, ContDiffAt ℝ ∞ F x)
    (S : E n →L[ℝ] E n) (hS : star S = -S) (k : ℕ) :
    ∃ C ≥ (0 : ℝ), ∀ t : ℝ, t ≠ 0 → ∀ x ∈ closedUnitBall n,
      ‖dirichletIteratedFieldDifference (orthogonalFlow S hS t) t F k x‖ ≤ C := by
  induction k generalizing F with
  | zero =>
    have hFC : ContinuousOn F (closedUnitBall n) :=
      fun x hx => (hF x hx).continuousAt.continuousWithinAt
    obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : E n) 1).exists_bound_of_continuousOn hFC
    refine ⟨max C 0, le_max_right _ _, fun t ht x hx => ?_⟩
    exact (hC x hx).trans (le_max_left _ _)
  | succ k ih =>
    let G (y : E n) := fderiv ℝ F y (S y)
    have hG (y : E n) (hy : y ∈ closedUnitBall n) : ContDiffAt ℝ ∞ G y :=
      ((hF y hy).fderiv_right (m := ∞) (by simp)).clm_apply S.contDiff.contDiffAt
    obtain ⟨C, hC, hBound⟩ := ih hG
    refine ⟨C, hC, ?_⟩
    intro t ht x hx
    have hD (y : E n) (hy : y ∈ closedUnitBall n) :=
      ((contDiffAt_dirichletIteratedFieldDifference_closed (orthogonalFlow S hS t) t hF k hy).differentiableAt
        (by simp)).hasFDerivAt
    apply norm_dirichletFieldDifference_flow_le_of_angular_bound hD S hS ?_ ht hx
    intro y hy
    rw [dirichletIteratedFieldDifference_angular_flow hF S hS t k hy]
    exact hBound t ht y hy

theorem exists_integral_dirichlet_smooth_field_iterated_difference_sq_bound {n : ℕ}
    (hn : 0 < n) {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {F : E n → V}
    (hF : ∀ x ∈ closedUnitBall n, ContDiffAt ℝ ∞ F x)
    (S : E n →L[ℝ] E n) (hS : star S = -S) (k : ℕ) :
    ∃ C ≥ (0 : ℝ), ∀ t : ℝ, t ≠ 0 →
      (∫ x in unitBall n,
        ‖dirichletIteratedFieldDifference (orthogonalFlow S hS t) t F k x‖ ^ 2 ∂volume0 n) ≤ C := by
  obtain ⟨C, hC, hBound⟩ := exists_dirichlet_smooth_field_iterated_difference_bound hF S hS k
  refine ⟨C ^ 2, sq_nonneg _, ?_⟩
  intro t ht
  have hFC : ContinuousOn F (closedUnitBall n) :=
    fun x hx => (hF x hx).continuousAt.continuousWithinAt
  have hPC := (continuousOn_dirichletIteratedFieldDifference (orthogonalFlow S hS t) t hFC k).norm.pow 2
  let : NeZero n := ⟨hn.ne'⟩
  let : IsProbabilityMeasure ((volume0 n).restrict (unitBall n)) := volume0_restrict_isProbability n
  have hInt := (dirichlet_memLp_of_continuousOn hn hPC 1).integrable le_rfl
  have h := setIntegral_mono_on hInt (integrable_const (C ^ 2)) measurableSet_ball
    (fun x hx => pow_le_pow_left₀ (norm_nonneg _)
      (hBound t ht x (ball_subset_closedBall hx)) 2)
  simpa only [Pi.pow_apply, integral_const, probReal_univ, one_smul] using h

end KEBall
