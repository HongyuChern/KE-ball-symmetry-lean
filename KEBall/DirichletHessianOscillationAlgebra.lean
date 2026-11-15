import KEBall.DirichletFinitePositiveFrame

/-!
# Finite-direction algebra for Hessian oscillation

These are the finite-sum and recurrence steps of the oscillation argument.
The log-determinant comparison and weak Harnack integral estimates must still
be supplied for the actual directional Hessian functions.  None of the
lemmas below asserts that those analytic hypotheses hold automatically.
-/

set_option autoImplicit false

open scoped BigOperators

namespace KEBall

/-- Positive directional coefficients turn the two-point linearized
inequality into control by the sum of upper Hessian defects. -/
theorem dirichlet_directional_defect_comparison {ι : Type*} [Fintype ι]
    (p q M β : ι → ℝ) {l u ε : ℝ} (hl : 0 < l) (hε : 0 ≤ ε)
    (hβ : ∀ i, l ≤ β i ∧ β i ≤ u)
    (hp : ∀ i, p i ≤ M i) (hq : ∀ i, q i ≤ M i)
    (hLinear : (∑ i, β i * (p i - q i)) ≤ ε) (j : ι) :
    l * (p j - q j) ≤ u * (∑ i, (M i - p i)) + ε := by
  have hβ₀ (i : ι) : 0 ≤ β i := hl.le.trans (hβ i).1
  have hu : 0 ≤ u := (hβ₀ j).trans (hβ j).2
  have hS₀ : 0 ≤ ∑ i, (M i - p i) := Finset.sum_nonneg fun i _ => sub_nonneg.mpr (hp i)
  by_cases hdiff : 0 ≤ p j - q j
  · calc
      _ ≤ β j * (p j - q j) := mul_le_mul_of_nonneg_right (hβ j).1 hdiff
      _ ≤ β j * (M j - q j) := mul_le_mul_of_nonneg_left (sub_le_sub_right (hp j) _) (hβ₀ j)
      _ ≤ ∑ i, β i * (M i - q i) :=
        Finset.single_le_sum (fun i _ => mul_nonneg (hβ₀ i) (sub_nonneg.mpr (hq i))) (Finset.mem_univ j)
      _ = (∑ i, β i * (p i - q i)) + ∑ i, β i * (M i - p i) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ ≤ ε + ∑ i, u * (M i - p i) := add_le_add hLinear
        (Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hβ i).2 (sub_nonneg.mpr (hp i)))
      _ = _ := by rw [← Finset.mul_sum]; ring
  · exact (mul_nonpos_of_nonneg_of_nonpos hl.le (le_of_not_ge hdiff)).trans
      (add_nonneg (mul_nonneg hu hS₀) hε)

/-- Absorbing the drop of the outer upper bounds gives a strict
contraction factor whenever the weak Harnack comparison constant is finite. -/
theorem dirichlet_oscillation_absorb {O o D K E : ℝ} (hK : 0 ≤ K)
    (hDrop : D ≤ O - o) (hEstimate : o ≤ K * D + E) :
    o ≤ K / (1 + K) * O + E / (1 + K) := by
  have hDen : 0 < 1 + K := by positivity
  have h := hEstimate.trans (add_le_add (mul_le_mul_of_nonneg_left hDrop hK) le_rfl)
  calc
    o ≤ (K * O + E) / (1 + K) := (le_div_iff₀ hDen).mpr (by nlinarith only [h])
    _ = K / (1 + K) * O + E / (1 + K) := by ring

theorem dirichlet_oscillation_factor {K : ℝ} (hK : 0 ≤ K) :
    0 ≤ K / (1 + K) ∧ K / (1 + K) < 1 := by
  have hDen : 0 < 1 + K := by positivity
  exact ⟨div_nonneg hK hDen.le, (div_lt_one hDen).mpr (by linarith)⟩

/-- An explicit geometric majorant for an oscillation recurrence with
geometrically decaying forcing. -/
theorem dirichlet_oscillation_geometric_bound
    (o : ℕ → ℝ) {θ σ τ E D : ℝ}
    (hθ : 0 ≤ θ) (hσ : 0 ≤ σ) (hστ : σ ≤ τ) (hE : 0 ≤ E)
    (hInitial : o 0 ≤ D) (hBudget : θ * D + E ≤ D * τ)
    (hStep : ∀ k : ℕ, o (k + 1) ≤ θ * o k + E * σ ^ k) :
    ∀ k : ℕ, o k ≤ D * τ ^ k := by
  intro k
  induction k with
  | zero => simpa only [pow_zero, mul_one] using hInitial
  | succ k ih =>
    calc
      o (k + 1) ≤ θ * o k + E * σ ^ k := hStep k
      _ ≤ θ * (D * τ ^ k) + E * τ ^ k := add_le_add
        (mul_le_mul_of_nonneg_left ih hθ)
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hσ hστ k) hE)
      _ = (θ * D + E) * τ ^ k := by ring
      _ ≤ (D * τ) * τ ^ k := mul_le_mul_of_nonneg_right hBudget (pow_nonneg (hσ.trans hστ) k)
      _ = D * τ ^ (k + 1) := by rw [pow_succ]; ring

end KEBall
