import Drafts.KEBall.NormalizedExterior

/-!
Stage18 SOURCE_DRAFT_UNCOMPILED.
The independent mass-one equation for D1 is stated in the actual exterior
algebra. Its solutions are transported in both directions; the original D0
predicate is unchanged. No additional mass/integrability assumption is used.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped ContDiff ComplexOrder

namespace KEBall

def IsD1NormalizedSolution (n : ℕ) (γ : ℝ) (ψ : E n → ℝ) : Prop :=
  0 < γ ∧ SmoothNear (closedUnitBall n) ψ ∧
  (∀ x ∈ unitBall n, (complexHessian ψ x).PosDef) ∧
  (∀ x ∈ unitSphere n, ψ x = 0) ∧
  (∀ x ∈ unitBall n, d1Exterior ψ x ^ n =
    ((Real.exp (-γ * ψ x) / normalizingIntegral γ ψ : ℝ) : ℂ) •
      normalizedExteriorVolume n)

noncomputable def d1NormalizedPotential (n : ℕ) (γ : ℝ) (x : E n) : ℝ :=
  normalizedPotential n (γ / 2) x / 2

def d1NormalizedSolutionSet (n : ℕ) (γ : ℝ) : Set (ClosedBall n → ℝ) :=
  {v | ∃ ψ : E n → ℝ, IsD1NormalizedSolution n γ ψ ∧ restrictClosedBall ψ = v}

def D1NormalizedClassificationStatement : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∀ γ : ℝ, 0 < γ →
    (γ < 2 * (n + 1 : ℝ) →
      IsD1NormalizedSolution n γ (d1NormalizedPotential n γ) ∧
      d1NormalizedSolutionSet n γ = {restrictClosedBall (d1NormalizedPotential n γ)}) ∧
    (2 * (n + 1 : ℝ) ≤ γ → d1NormalizedSolutionSet n γ = ∅)

theorem d0Exterior_double {n : ℕ} {ψ : E n → ℝ} {x : E n}
    (hψ : ContDiffAt ℝ ∞ ψ x) :
    d0Exterior (fun y => 2 * ψ y) x = d1Exterior ψ x := by
  rw [d0Exterior_const_mul hψ]
  rfl

theorem normalizingIntegral_half_double {n : ℕ} (γ : ℝ) (ψ : E n → ℝ) :
    normalizingIntegral (γ / 2) (fun x => 2 * ψ x) =
      normalizingIntegral γ ψ := by
  unfold normalizingIntegral
  apply setIntegral_congr_fun Metric.isOpen_ball.measurableSet
  intro x _
  congr 1
  ring

/-- An independent D1 solution supplies an original D0 solution. -/
theorem IsD1NormalizedSolution.double_isNormalized {n : ℕ} {γ : ℝ}
    {ψ : E n → ℝ} (hψ : IsD1NormalizedSolution n γ ψ) :
    IsNormalizedSolution n (γ / 2) (fun x => 2 * ψ x) := by
  have he (x : E n) : Real.exp (-(γ / 2) * (2 * ψ x)) =
      Real.exp (-γ * ψ x) := by
    congr 1
    ring
  have htop : ∀ x ∈ unitBall n,
      exteriorEvaluation (euclideanFrame n)
        (d0Exterior (fun y => 2 * ψ y) x ^ n) =
      (((Real.exp (-(γ / 2) * (2 * ψ x)) /
        normalizingIntegral (γ / 2) (fun y => 2 * ψ y)) *
          ((n.factorial : ℝ) / Real.pi ^ n) : ℝ) : ℂ) := by
    intro x hx
    rw [d0Exterior_double (hψ.2.1.contDiffAt (Metric.ball_subset_closedBall hx))]
    have h := congrArg (exteriorEvaluation (euclideanFrame n)) (hψ.2.2.2.2 x hx)
    rw [map_smul, exteriorEvaluation_normalized_volume, smul_eq_mul] at h
    simpa only [normalizingIntegral_half_double, he, Complex.ofReal_mul,
      Complex.ofReal_div, Complex.ofReal_pow] using h
  apply (isNormalizedSolution_iff_real_density n (γ / 2) (fun x => 2 * ψ x)).2
  refine ⟨div_pos hψ.1 (by norm_num), smoothNear_const_mul hψ.2.1 2, ?_, ?_,
    (normalized_equation_iff_top_evaluation (γ / 2) (fun x => 2 * ψ x)).mpr htop⟩
  · intro x hx
    rw [complexHessian_const_mul_at (hψ.2.1.contDiffAt (Metric.ball_subset_closedBall hx))]
    apply (hψ.2.2.1 x hx).smul
    exact_mod_cast (show (0 : ℝ) < 2 by norm_num)
  · intro x hx
    rw [hψ.2.2.2.1 x hx, mul_zero]

/-- The D0 half-potential satisfies the full D1 exterior equation. -/
theorem IsNormalizedSolution.half_isD1Normalized {n : ℕ} {γ : ℝ}
    {φ : E n → ℝ} (hφ : IsNormalizedSolution n γ φ) :
    IsD1NormalizedSolution n (2 * γ) (fun x => φ x / 2) := by
  have hfun : (fun x => φ x / 2) = (fun x => (1 / 2 : ℝ) * φ x) := by
    funext x
    ring
  have hs : SmoothNear (closedUnitBall n) (fun x => φ x / 2) := by
    rw [hfun]
    exact smoothNear_const_mul hφ.2.1 _
  have he (x : E n) : Real.exp (-(2 * γ) * (φ x / 2)) =
      Real.exp (-γ * φ x) := by
    congr 1
    ring
  refine ⟨mul_pos (by norm_num) hφ.1, hs, ?_, ?_, ?_⟩
  · intro x hx
    rw [hfun, complexHessian_const_mul_at (hφ.2.1.contDiffAt (Metric.ball_subset_closedBall hx))]
    apply (hφ.2.2.1 x hx).smul
    exact_mod_cast (show (0 : ℝ) < 1 / 2 by norm_num)
  · intro x hx
    change φ x / 2 = 0
    rw [hφ.2.2.2.1 x hx, zero_div]
  · intro x hx
    rw [d1Exterior_half (hφ.2.1.contDiffAt (Metric.ball_subset_closedBall hx)),
      d0Exterior_top, hφ.det_eq_real_density hx]
    simp only [normalizingIntegral_double_half, he]

theorem isD1NormalizedSolution_iff_double {n : ℕ} (γ : ℝ) (ψ : E n → ℝ) :
    IsD1NormalizedSolution n γ ψ ↔
      IsNormalizedSolution n (γ / 2) (fun x => 2 * ψ x) := by
  constructor
  · exact IsD1NormalizedSolution.double_isNormalized
  · intro h
    have hfun : (fun x => (2 * ψ x) / 2) = ψ := by
      funext x
      ring
    have hγ : 2 * (γ / 2) = γ := by ring
    simpa only [hfun, hγ] using h.half_isD1Normalized

theorem IsD1NormalizedSolution.eqOn_d1NormalizedPotential {n : ℕ} (hn : 2 ≤ n)
    {γ : ℝ} {ψ : E n → ℝ} (hψ : IsD1NormalizedSolution n γ ψ) :
    γ < 2 * (n + 1 : ℝ) ∧
      EqOn ψ (d1NormalizedPotential n γ) (closedUnitBall n) := by
  obtain ⟨hγκ, heq⟩ := hψ.double_isNormalized.eqOn_normalizedPotential hn
  refine ⟨by linarith, ?_⟩
  intro x hx
  have h := heq hx
  change 2 * ψ x = normalizedPotential n (γ / 2) x at h
  unfold d1NormalizedPotential
  linarith

theorem d1NormalizedPotential_isD1NormalizedSolution {n : ℕ} (hn : 2 ≤ n)
    {γ : ℝ} (hγ : 0 < γ) (hγκ : γ < 2 * (n + 1 : ℝ)) :
    IsD1NormalizedSolution n γ (d1NormalizedPotential n γ) := by
  have hhalf : 0 < γ / 2 := div_pos hγ (by norm_num)
  have hhalfκ : γ / 2 < (n + 1 : ℝ) := by linarith
  have h := (normalizedPotential_isNormalizedSolution hn hhalf hhalfκ).half_isD1Normalized
  have he : 2 * (γ / 2) = γ := by ring
  change IsD1NormalizedSolution n γ (fun x => normalizedPotential n (γ / 2) x / 2)
  simpa only [he] using h

theorem d1NormalizedPotential_explicit {n : ℕ} {γ : ℝ} (hγ : 0 < γ) (x : E n) :
    d1NormalizedPotential n γ x = (n + 1 : ℝ) / γ *
      Real.log (1 - γ / (2 * (n + 1 : ℝ)) +
        γ / (2 * (n + 1 : ℝ)) * ‖x‖ ^ 2) := by
  have hk : (n + 1 : ℝ) ≠ 0 := by positivity
  have ha : (γ / 2) / (n + 1 : ℝ) = γ / (2 * (n + 1 : ℝ)) := by
    field_simp [hk] <;> ring
  have hc : ((n + 1 : ℝ) / (γ / 2)) / 2 = (n + 1 : ℝ) / γ := by
    field_simp [ne_of_gt hγ] <;> ring
  unfold d1NormalizedPotential normalizedPotential
  rw [ha]
  calc
    _ = (((n + 1 : ℝ) / (γ / 2)) / 2) *
      Real.log (1 - γ / (2 * (n + 1 : ℝ)) +
        γ / (2 * (n + 1 : ℝ)) * ‖x‖ ^ 2) := by ring
    _ = _ := by rw [hc]

theorem IsD1NormalizedSolution.d1TopMeasure_isProbability {n : ℕ} {γ : ℝ}
    {ψ : E n → ℝ} (hψ : IsD1NormalizedSolution n γ ψ) :
    IsProbabilityMeasure ((d1TopMeasure ψ).restrict (unitBall n)) := by
  have h := hψ.double_isNormalized
  have hfun : (fun x => (2 * ψ x) / 2) = ψ := by funext x; ring
  have hμ : (d1TopMeasure ψ).restrict (unitBall n) =
      (d0TopMeasure (fun x => 2 * ψ x)).restrict (unitBall n) := by
    simpa only [hfun] using h.d1TopMeasure_half
  rw [hμ]
  exact h.d0TopMeasure_isProbability

theorem d1NormalizedClassification : D1NormalizedClassificationStatement := by
  intro n hn γ hγ
  refine ⟨?_, ?_⟩
  · intro hγκ
    have hex := d1NormalizedPotential_isD1NormalizedSolution hn hγ hγκ
    refine ⟨hex, ?_⟩
    ext v
    constructor
    · rintro ⟨ψ, hψ, hv⟩
      have heq := (hψ.eqOn_d1NormalizedPotential hn).2
      apply Set.mem_singleton_iff.mpr
      exact hv.symm.trans (restrictClosedBall_eq_iff.mpr heq)
    · intro hv
      have hv' := Set.mem_singleton_iff.mp hv
      exact ⟨d1NormalizedPotential n γ, hex, hv'.symm⟩
  · intro hκγ
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro v ⟨ψ, hψ, _⟩
    exact (not_lt_of_ge hκγ) (hψ.eqOn_d1NormalizedPotential hn).1

#print axioms isD1NormalizedSolution_iff_double
#print axioms d1NormalizedClassification
#print axioms IsD1NormalizedSolution.d1TopMeasure_isProbability

end KEBall
