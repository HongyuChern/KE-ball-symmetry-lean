import KEBall.BedfordTaylorSeparateMatrixLimit

/-!
# Upper bound on a weighted positive quadratic coefficient
-/

set_option autoImplicit false

open Filter MeasureTheory TopologicalSpace
open scoped Distributions Topology

namespace KEBall.BedfordTaylor

open PshLines
open PshLines.FirstPass (ComplexModel)
open PshLines.FirstPass.MongeAmpere (IsLocallyBoundedPshOn IsSmoothPshOn)

variable {n k : ℕ} {Ω : Opens (ComplexModel n)}
  {u : ComplexModel n → ℝ} {q : ℕ → ComplexModel n → ℝ}

theorem WeakMatrixLimit.integral_quadraticMeasure {T : ℕ → CoordinateDistributions Ω k k}
    {S : CoordinateDistributions Ω k k} (h : WeakMatrixLimit T S)
    (hT : ∀ j, IsPositiveMatrixDistribution (T j)) (hS : IsPositiveMatrixDistribution S)
    (v : CoordinateTuple n k → ℂ) (φ : 𝓓(Ω, ℝ)) :
    Tendsto (fun j => ∫ x : Ω, φ x ∂quadraticMeasure (hT j) v) atTop
      (𝓝 (∫ x : Ω, φ x ∂quadraticMeasure hS v)) := by
  simp_rw [KEBall.BedfordTaylor.integral_quadraticMeasure]
  exact (Complex.continuous_re.tendsto _).comp (h.quadratic v φ)

theorem eventually_weightedQuadraticIntegral_lt_add
    {T : ℕ → CoordinateDistributions Ω k k} {S : CoordinateDistributions Ω k k}
    (h : WeakMatrixLimit T S) (hT : ∀ j, IsPositiveMatrixDistribution (T j))
    (hS : IsPositiveMatrixDistribution S)
    (hu : IsLocallyBoundedPshOn Ω u) (hq : ∀ j, IsSmoothPshOn Ω (q j))
    (hanti : ∀ x ∈ Ω, Antitone (fun j => q j x))
    (hlim : ∀ x ∈ Ω, Tendsto (fun j => q j x) atTop (𝓝 (u x)))
    (v : CoordinateTuple n k → ℂ) (φ : 𝓓(Ω, ℝ)) (hφ : ∀ x, 0 ≤ φ x)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ j in atTop,
      (∫ x : Ω, φ x * q j x ∂quadraticMeasure (hT j) v) <
        (∫ x : Ω, φ x * u x ∂quadraticMeasure hS v) + ε := by
  let μ := quadraticMeasure hS v
  let : μ.Regular := quadraticMeasure_regular hS v
  let a := ∫ x : Ω, φ x * u x ∂μ
  let hqL := fun j => isLocallyBoundedPshOn_of_isSmoothPshOn (hq j)
  have hfix := tendsto_integral_psh_weight_of_antitone hu hqL hanti hlim μ φ
  obtain ⟨m, hm⟩ := (hfix.eventually_lt_const (lt_add_of_pos_right a (half_pos hε))).exists
  let ψ := multiplySmoothTest φ (hq m).1
  have hcont := h.integral_quadraticMeasure hT hS v ψ
  have hlt : (∫ x : Ω, ψ x ∂μ) < a + ε := hm.trans (by linarith)
  filter_upwards [eventually_ge_atTop m, hcont.eventually_lt_const hlt] with j hj hupper
  let ν := quadraticMeasure (hT j) v
  let : ν.Regular := quadraticMeasure_regular (hT j) v
  have hleft : Integrable (fun x : Ω => φ x * q j x) ν :=
    integrable_test_mul_psh (hqL j) ν φ
  have hright : Integrable (fun x : Ω => ψ x) ν :=
    (testFunctionToCompactlySupportedLM Ω ψ).integrable
  exact (integral_mono hleft hright fun x =>
    mul_le_mul_of_nonneg_left (hanti x x.property hj) (hφ x)).trans_lt hupper

end KEBall.BedfordTaylor
