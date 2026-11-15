import Drafts.KEBall.InteriorGradientRigidity
import KEBall.BoundaryMass
import KEBall.ScalarBranches
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
Stage17 SOURCE_DRAFT_UNCOMPILED.
Actual determinant-level normalization, using u = gamma * phi and the
existing mass identity. The frozen complex-integral expression is converted
explicitly to the real density before positivity or scaling. Still uncompiled.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped ContDiff ComplexOrder

namespace KEBall

noncomputable def normalizingIntegral {n : ℕ} (γ : ℝ) (φ : E n → ℝ) : ℝ :=
  ∫ x in unitBall n, Real.exp (-γ * φ x) ∂volume0 n

/-- Convert the frozen equation without assuming a definitional equality
between a complex integral and the coercion of a real integral. -/
theorem normalized_equation_iff_real_density {n : ℕ} (γ : ℝ) (φ : E n → ℝ) :
    (∀ x ∈ unitBall n, (complexHessian φ x).det =
      (Real.exp (-γ * φ x) /
        (∫ y in unitBall n, Real.exp (-γ * φ y) ∂volume0 n) : ℂ)) ↔
    (∀ x ∈ unitBall n, (complexHessian φ x).det =
      ((Real.exp (-γ * φ x) / normalizingIntegral γ φ : ℝ) : ℂ)) := by
  simp only [normalizingIntegral, Complex.ofReal_div, integral_complex_ofReal]

theorem isNormalizedSolution_iff_real_density (n : ℕ) (γ : ℝ) (φ : E n → ℝ) :
    IsNormalizedSolution n γ φ ↔
      0 < γ ∧ SmoothNear (closedUnitBall n) φ ∧
      (∀ x ∈ unitBall n, (complexHessian φ x).PosDef) ∧
      (∀ x ∈ unitSphere n, φ x = 0) ∧
      (∀ x ∈ unitBall n, (complexHessian φ x).det =
        ((Real.exp (-γ * φ x) / normalizingIntegral γ φ : ℝ) : ℂ)) := by
  unfold IsNormalizedSolution
  rw [normalized_equation_iff_real_density]

theorem IsNormalizedSolution.det_eq_real_density {n : ℕ} {γ : ℝ}
    {φ : E n → ℝ} (hφ : IsNormalizedSolution n γ φ)
    {x : E n} (hx : x ∈ unitBall n) :
    (complexHessian φ x).det =
      ((Real.exp (-γ * φ x) / normalizingIntegral γ φ : ℝ) : ℂ) := by
  simpa only [normalizingIntegral, Complex.ofReal_div, integral_complex_ofReal]
    using hφ.2.2.2.2 x hx

theorem smoothNear_const_mul {n : ℕ} {u : E n → ℝ}
    (hu : SmoothNear (closedUnitBall n) u) (c : ℝ) :
    SmoothNear (closedUnitBall n) (fun x => c * u x) := by
  obtain ⟨U, hU, hKU, hs⟩ := hu
  exact ⟨U, hU, hKU, contDiffOn_const.mul hs⟩

/-- Positivity is forced by the actual equation at the origin. In particular,
the totalized integral cannot be zero for a normalized solution. -/
theorem IsNormalizedSolution.normalizingIntegral_pos {n : ℕ} {γ : ℝ}
    {φ : E n → ℝ} (hφ : IsNormalizedSolution n γ φ) :
    0 < normalizingIntegral γ φ := by
  have h0 : (0 : E n) ∈ unitBall n := by simp [unitBall]
  have hd := posDef_det_re_pos (hφ.2.2.1 0 h0)
  have heq := congrArg Complex.re (hφ.det_eq_real_density h0)
  simp only [Complex.ofReal_re] at heq
  rw [heq] at hd
  rcases (div_pos_iff.mp hd) with h | h
  · exact h.2
  · exact False.elim ((not_lt_of_gt (Real.exp_pos _)) h.1)

theorem IsNormalizedSolution.rescale {n : ℕ} {γ : ℝ}
    {φ : E n → ℝ} (hφ : IsNormalizedSolution n γ φ) :
    IsSolution n (γ ^ n / normalizingIntegral γ φ) (fun x => γ * φ x) := by
  refine ⟨div_pos (pow_pos hφ.1 _) hφ.normalizingIntegral_pos,
    smoothNear_const_mul hφ.2.1 γ, ?_, ?_, ?_⟩
  · intro x hx
    rw [complexHessian_const_mul_at (hφ.2.1.contDiffAt (Metric.ball_subset_closedBall hx))]
    apply (hφ.2.2.1 x hx).smul
    exact_mod_cast hφ.1
  · intro x hx
    rw [complexHessian_const_mul_at (hφ.2.1.contDiffAt (Metric.ball_subset_closedBall hx)),
      Matrix.det_smul, Fintype.card_fin, hφ.det_eq_real_density hx]
    have hsign : -(γ * φ x) = -γ * φ x := by ring
    have hreal : γ ^ n * (Real.exp (-γ * φ x) / normalizingIntegral γ φ) =
        (γ ^ n / normalizingIntegral γ φ) * Real.exp (-γ * φ x) := by ring
    simpa only [Complex.ofReal_mul, Complex.ofReal_pow, hsign]
      using congrArg (fun t : ℝ => (t : ℂ)) hreal
  · intro x hx
    change γ * φ x = 0
    rw [hφ.2.2.2.1 x hx, mul_zero]

/-- The concrete mass of an original solution with constant sphere slope. -/
theorem IsSolution.exponential_mass_of_constant_slope {n : ℕ} (hn : 2 ≤ n)
    {μ a : ℝ} {u : E n → ℝ} (hu : IsSolution n μ u)
    (ht : ∀ x ∈ unitSphere n, boundarySlope u x = a) :
    μ * (∫ x in unitBall n, Real.exp (-u x) ∂volume0 n) = a ^ n := by
  letI : NeZero n := ⟨by omega⟩
  have hL : (∫ x in unitBall n, (complexHessian u x).det.re ∂volume0 n) =
      μ * (∫ x in unitBall n, Real.exp (-u x) ∂volume0 n) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun Metric.isOpen_ball.measurableSet
    intro x hx
    change (complexHessian u x).det.re = μ * Real.exp (-u x)
    rw [hu.2.2.2.1 x hx]
    simp only [← Complex.ofReal_mul, Complex.ofReal_re]
  have hR : (∫ x : Sphere n, boundarySlope u x.1 ^ n ∂sphere0 n) = a ^ n := by
    simp_rw [ht _ (Subtype.property _)]
    simp
  have h := hu.mass_identity hn
  rwa [hL, hR] at h

theorem IsNormalizedSolution.parameter_and_rescaled_eqOn {n : ℕ} (hn : 2 ≤ n)
    {γ : ℝ} {φ : E n → ℝ} (hφ : IsNormalizedSolution n γ φ) :
    γ < (n + 1 : ℝ) ∧
      EqOn (fun x => γ * φ x)
        (radialPotential n (γ / ((n + 1 : ℝ) - γ))) (closedUnitBall n) := by
  let u : E n → ℝ := fun x => γ * φ x
  have hu : IsSolution n (γ ^ n / normalizingIntegral γ φ) u := hφ.rescale
  obtain ⟨t₀, ht, htk, _, hSlope, hV⟩ := hu.exists_exponentialGradient_closedBall_data hn
  have hmass := hu.exponential_mass_of_constant_slope hn hSlope
  have hI : (∫ x in unitBall n, Real.exp (-u x) ∂volume0 n) =
      normalizingIntegral γ φ := by
    apply setIntegral_congr_fun Metric.isOpen_ball.measurableSet
    intro x _
    congr 1
    dsimp [u]
    ring
  rw [hI, div_mul_cancel₀ _ (ne_of_gt hφ.normalizingIntegral_pos)] at hmass
  have htg : t₀ = γ :=
    (pow_left_inj₀ ht.le hφ.1.le (by omega : n ≠ 0)).mp hmass.symm
  subst t₀
  have hZ := hu.complexEuler_eq_expWeight hn htk hSlope hV
  have hEuler : ∀ x ∈ unitBall n, fderiv ℝ u x x =
      2 * ((n + 1 : ℝ) - ((n + 1 : ℝ) - γ) * expWeight u x) := by
    intro x hx
    rw [fderiv_eq_wirtinger
      ((hu.2.1.contDiffAt (Metric.ball_subset_closedBall hx)).differentiableAt (by simp))]
    change 2 * (complexEuler u x).re = _
    rw [hZ x (Metric.ball_subset_closedBall hx), Complex.ofReal_re]
  exact ⟨htk, eq_radial_of_euler_identity hu.2.1 hu.2.2.2.2 hφ.1 htk hEuler⟩

/-- Converse scaling uses mass, rather than assuming the normalized PDE. -/
theorem IsSolution.normalized_rescale_of_slope {n : ℕ} (hn : 2 ≤ n)
    {μ γ : ℝ} {u : E n → ℝ} (hu : IsSolution n μ u) (hγ : 0 < γ)
    (ht : ∀ x ∈ unitSphere n, boundarySlope u x = γ) :
    IsNormalizedSolution n γ (fun x => γ⁻¹ * u x) := by
  let I : ℝ := ∫ x in unitBall n, Real.exp (-u x) ∂volume0 n
  have hmass : μ * I = γ ^ n := hu.exponential_mass_of_constant_slope hn ht
  have hIpos : 0 < I := by
    by_contra h
    have hnonpos : I ≤ 0 := le_of_not_gt h
    have : μ * I ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hu.1.le hnonpos
    linarith [pow_pos hγ n]
  have hI : I ≠ 0 := ne_of_gt hIpos
  have hγne : γ ≠ 0 := ne_of_gt hγ
  have hsign (x : E n) : -γ * (γ⁻¹ * u x) = -u x := by
    field_simp [hγne]
  have hnormal : normalizingIntegral γ (fun x => γ⁻¹ * u x) = I := by
    unfold normalizingIntegral
    simp_rw [hsign]
    rfl
  have hcoef : (γ⁻¹) ^ n * μ = I⁻¹ := by
    apply mul_right_cancel₀ hI
    calc
      (γ⁻¹ ^ n * μ) * I = γ⁻¹ ^ n * (μ * I) := by ring
      _ = γ⁻¹ ^ n * γ ^ n := by rw [hmass]
      _ = 1 := by rw [← mul_pow, inv_mul_cancel₀ hγne, one_pow]
      _ = I⁻¹ * I := (inv_mul_cancel₀ hI).symm
  apply (isNormalizedSolution_iff_real_density n γ (fun x => γ⁻¹ * u x)).2
  refine ⟨hγ, smoothNear_const_mul hu.2.1 γ⁻¹, ?_, ?_, ?_⟩
  · intro x hx
    rw [complexHessian_const_mul_at (hu.2.1.contDiffAt (Metric.ball_subset_closedBall hx))]
    apply (hu.2.2.1 x hx).smul
    exact_mod_cast (inv_pos.mpr hγ)
  · intro x hx
    rw [hu.2.2.2.2 x hx, mul_zero]
  · intro x hx
    calc
      (complexHessian (fun y => γ⁻¹ * u y) x).det =
          (((γ⁻¹) ^ n * (μ * Real.exp (-u x)) : ℝ) : ℂ) := by
        rw [complexHessian_const_mul_at (hu.2.1.contDiffAt (Metric.ball_subset_closedBall hx)),
          Matrix.det_smul, Fintype.card_fin, hu.2.2.2.1 x hx]
        push_cast <;> ring
      _ = ((Real.exp (-γ * (γ⁻¹ * u x)) /
          normalizingIntegral γ (fun y => γ⁻¹ * u y) : ℝ) : ℂ) := by
        congr 1
        rw [hsign, hnormal, div_eq_mul_inv, ← hcoef]
        ring

theorem radial_scaled_eq_normalized {n : ℕ} {γ : ℝ} (hγ : 0 < γ)
    (hγκ : γ < (n + 1 : ℝ)) :
    (fun x => γ⁻¹ * radialPotential n (γ / ((n + 1 : ℝ) - γ)) x) =
      normalizedPotential n γ := by
  have hk : (n + 1 : ℝ) ≠ 0 := by positivity
  have hd : (n + 1 : ℝ) - γ ≠ 0 := ne_of_gt (sub_pos.mpr hγκ)
  have harg (x : E n) :
      (1 + (γ / ((n + 1 : ℝ) - γ)) * ‖x‖ ^ 2) /
        (1 + γ / ((n + 1 : ℝ) - γ)) =
      1 - γ / (n + 1 : ℝ) + γ / (n + 1 : ℝ) * ‖x‖ ^ 2 := by
    field_simp [hk, hd]
    ring
  funext x
  unfold radialPotential normalizedPotential
  rw [harg]
  ring

theorem IsNormalizedSolution.eqOn_normalizedPotential {n : ℕ} (hn : 2 ≤ n)
    {γ : ℝ} {φ : E n → ℝ} (hφ : IsNormalizedSolution n γ φ) :
    γ < (n + 1 : ℝ) ∧ EqOn φ (normalizedPotential n γ) (closedUnitBall n) := by
  obtain ⟨hγκ, heq⟩ := hφ.parameter_and_rescaled_eqOn hn
  refine ⟨hγκ, ?_⟩
  intro x hx
  calc
    φ x = γ⁻¹ * (γ * φ x) := by rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hφ.1), one_mul]
    _ = γ⁻¹ * radialPotential n (γ / ((n + 1 : ℝ) - γ)) x := by
      have heqx : γ * φ x = radialPotential n (γ / ((n + 1 : ℝ) - γ)) x := heq hx
      rw [heqx]
    _ = normalizedPotential n γ x := congrFun (radial_scaled_eq_normalized hφ.1 hγκ) x

theorem normalizedPotential_isNormalizedSolution {n : ℕ} (hn : 2 ≤ n)
    {γ : ℝ} (hγ : 0 < γ) (hγκ : γ < (n + 1 : ℝ)) :
    IsNormalizedSolution n γ (normalizedPotential n γ) := by
  have hb : 0 < γ / ((n + 1 : ℝ) - γ) := div_pos hγ (sub_pos.mpr hγκ)
  have ht : ∀ x ∈ unitSphere n,
      boundarySlope (radialPotential n (γ / ((n + 1 : ℝ) - γ))) x = γ := by
    intro x hx
    rw [radial_boundarySlope n hb hx, radialBoundaryParameter_inverse n ⟨hγ, hγκ⟩]
  have h := (radial_isSolution n hb).normalized_rescale_of_slope hn hγ ht
  rwa [radial_scaled_eq_normalized hγ hγκ] at h

#print axioms IsNormalizedSolution.rescale
#print axioms IsNormalizedSolution.parameter_and_rescaled_eqOn
#print axioms IsSolution.normalized_rescale_of_slope
#print axioms normalizedPotential_isNormalizedSolution

end KEBall
