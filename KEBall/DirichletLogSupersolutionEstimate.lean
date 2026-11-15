import KEBall.DirichletWeakDivergenceLimit

/-! A logarithmic energy bound for positive elliptic supersolutions. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter InnerProductSpace MeasureTheory Metric Set
open scoped ContDiff Distributions Gradient Topology

namespace KEBall

local notation "ν[" n "]" => Measure.restrict (volume0 n) (unitBall n)
local notation "𝓓B[" n "]" => 𝓓(dirichletBallOpens n, ℝ)

private theorem gradient_test_sq_mul_inv {n : ℕ} {h η : E n → ℝ} {x : E n}
    (hh : DifferentiableAt ℝ h x) (h₀ : h x ≠ 0) (hη : DifferentiableAt ℝ η x) :
    ∇ (fun y => (η y) ^ 2 * (h y)⁻¹) x =
      (2 * η x * (h x)⁻¹) • ∇ η x - ((η x) ^ 2 * ((h x) ^ 2)⁻¹) • ∇ h x := by
  have hD := ((hη.hasFDerivAt.pow 2).mul ((hasDerivAt_inv h₀).comp_hasFDerivAt x hh.hasFDerivAt))
  change HasFDerivAt (fun y => (η y) ^ 2 * (h y)⁻¹) _ x at hD
  rw [gradient, hD.fderiv]
  simp only [Nat.reduceSubDiff, pow_one, map_add, map_neg, map_smul, gradient,
    neg_smul, smul_neg, sub_eq_add_neg, smul_smul, nsmul_eq_mul, Function.comp_apply]
  rw [add_comm]
  congr 2
  ring

private theorem gradient_log_eq {n : ℕ} {h : E n → ℝ} {x : E n}
    (hh : DifferentiableAt ℝ h x) (h₀ : h x ≠ 0) :
    ∇ (fun y => Real.log (h y)) x = (h x)⁻¹ • ∇ h x := by
  rw [gradient, hh.hasFDerivAt.log h₀ |>.fderiv, map_smul]
  rfl

private theorem cofactor_logEnergy_pointwise {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] {A : V →L[ℝ] V} {c C : ℝ} (hc : 0 < c) (hC : ‖A‖ ≤ C)
    {v : V} (hEll : c * ‖v‖ ^ 2 ≤ inner ℝ (A v) v) (w : V) (η : ℝ) :
    (c / 2) * (η ^ 2 * ‖v‖ ^ 2) ≤
      (2 * C ^ 2 / c) * ‖w‖ ^ 2 + (η ^ 2 * inner ℝ (A v) v - 2 * η * inner ℝ (A v) w) := by
  have h₀ : 0 ≤ C := (norm_nonneg _).trans hC
  have hPair : |inner ℝ (A v) w| ≤ C * ‖v‖ * ‖w‖ := by
    rw [← Real.norm_eq_abs]
    exact (norm_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right ((A.le_opNorm v).trans (mul_le_mul_of_nonneg_right hC (norm_nonneg _)))
        (norm_nonneg _))
  have hMixed : 2 * η * inner ℝ (A v) w ≤ 2 * (|η| * ‖v‖) * (C * ‖w‖) := by
    calc
      _ ≤ |2 * η * inner ℝ (A v) w| := le_abs_self _
      _ = 2 * |η| * |inner ℝ (A v) w| := by rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : 0 ≤ (2 : ℝ))]
      _ ≤ 2 * |η| * (C * ‖v‖ * ‖w‖) := mul_le_mul_of_nonneg_left hPair (by positivity)
      _ = _ := by ring
  have hYoung : 2 * (|η| * ‖v‖) * (C * ‖w‖) ≤
      (c / 2) * (η ^ 2 * ‖v‖ ^ 2) + (2 * C ^ 2 / c) * ‖w‖ ^ 2 := by
    apply (le_of_mul_le_mul_right · hc)
    have h := sq_nonneg (c * (|η| * ‖v‖) - 2 * (C * ‖w‖))
    have hSq : (|η| * ‖v‖) ^ 2 = η ^ 2 * ‖v‖ ^ 2 := by rw [mul_pow, sq_abs]
    have hCancel : (2 * C ^ 2 / c) * c = 2 * C ^ 2 := div_mul_cancel₀ _ hc.ne'
    calc
      (2 * (|η| * ‖v‖) * (C * ‖w‖)) * c ≤
          c ^ 2 / 2 * (|η| * ‖v‖) ^ 2 + 2 * (C * ‖w‖) ^ 2 := by nlinarith only [h]
      _ = ((c / 2) * (η ^ 2 * ‖v‖ ^ 2) + (2 * C ^ 2 / c) * ‖w‖ ^ 2) * c := by
        rw [hSq, mul_pow, add_mul, mul_right_comm (2 * C ^ 2 / c), hCancel]
        ring
  have hLower := mul_le_mul_of_nonneg_left hEll (sq_nonneg η)
  nlinarith only [hLower, hMixed.trans hYoung]

private theorem cofactor_logEnergy_integrand_eq {n : ℕ} {h η : E n → ℝ} {x : E n}
    {A : E n →L[ℝ] E n} (hh : DifferentiableAt ℝ h x) (h₀ : h x ≠ 0)
    (hη : DifferentiableAt ℝ η x) :
    inner ℝ (A (∇ h x)) (∇ (fun y => (η y) ^ 2 * (h y)⁻¹) x) =
      2 * η x * inner ℝ (A (∇ (fun y => Real.log (h y)) x)) (∇ η x) -
        η x ^ 2 * inner ℝ (A (∇ (fun y => Real.log (h y)) x)) (∇ (fun y => Real.log (h y)) x) := by
  rw [gradient_test_sq_mul_inv hh h₀ hη, gradient_log_eq hh h₀]
  simp only [inner_sub_right, map_smul, real_inner_smul_left, real_inner_smul_right]
  ring

/-- Testing a smooth positive supersolution by the squared cutoff divided by
the supersolution controls the energy of its logarithm. -/
theorem integral_log_gradient_sq_le_of_supersolution {n : ℕ} (hn : 0 < n)
    {h : E n → ℝ} (hh : ContDiff ℝ ∞ h) (hPos : ∀ x, 0 < h x)
    {A : E n → E n →L[ℝ] E n} (hA : ContinuousOn A (closedUnitBall n))
    {c C : ℝ} (hc : 0 < c)
    (hEll : ∀ x ∈ unitBall n, ∀ v : E n, c * ‖v‖ ^ 2 ≤ inner ℝ (A x v) v)
    (hNorm : ∀ x ∈ unitBall n, ‖A x‖ ≤ C)
    {f : E n → ℝ}
    (hSup : ∀ ψ : 𝓓B[n], (∀ x ∈ unitBall n, 0 ≤ ψ x) →
      -(∫ x, ψ x * f x ∂ν[n]) ≤ ∫ x, inner ℝ (A x (∇ h x)) (∇ (ψ : E n → ℝ) x) ∂ν[n])
    (η : 𝓓B[n]) :
    (c / 2) * (∫ x, η x ^ 2 * ‖∇ (fun y => Real.log (h y)) x‖ ^ 2 ∂ν[n]) ≤
      (2 * C ^ 2 / c) * (∫ x, ‖∇ (η : E n → ℝ) x‖ ^ 2 ∂ν[n]) +
        ∫ x, η x ^ 2 * (h x)⁻¹ * f x ∂ν[n] := by
  have : NeZero n := ⟨hn.ne'⟩
  let φ : 𝓓B[n] := dirichletTestMul η (η.contDiff.mul (hh.inv (fun x => (hPos x).ne')))
  have hφ (x : E n) : φ x = η x ^ 2 * (h x)⁻¹ := by
    simp only [φ, dirichletTestMul_apply, Pi.inv_apply]
    ring
  have hψ := hSup φ (fun x _ => by
    rw [hφ]
    exact mul_nonneg (sq_nonneg _) (inv_nonneg.mpr (hPos x).le))
  let U (x : E n) := ∇ (fun y => Real.log (h y)) x
  let V := ∇ (η : E n → ℝ)
  let E₀ (x : E n) := η x ^ 2 * ‖U x‖ ^ 2
  let E₁ (x : E n) := ‖V x‖ ^ 2
  let F (x : E n) := inner ℝ (A x (∇ h x)) (∇ (φ : E n → ℝ) x)
  have hD (x : E n) : F x =
      2 * η x * inner ℝ (A x (U x)) (V x) - η x ^ 2 * inner ℝ (A x (U x)) (U x) := by
    have he : (φ : E n → ℝ) = fun y => η y ^ 2 * (h y)⁻¹ := funext hφ
    dsimp only [F, U, V]
    rw [he]
    exact cofactor_logEnergy_integrand_eq (hh.differentiable (by simp) x) (hPos x).ne'
      (η.contDiff.differentiable (by simp) x)
  have hGrad {p : E n → ℝ} (hp : ContDiff ℝ ∞ p) : Continuous (∇ p) :=
    (InnerProductSpace.toDual ℝ (E n)).symm.continuous.comp
      (hp.fderiv_right (m := ∞) (by simp)).continuous
  have hI {w : E n → ℝ} (hw : ContinuousOn w (closedUnitBall n)) : Integrable w ν[n] :=
    (memLp_continuousOn_dirichletBall hn hw).integrable (by norm_num)
  have hI₀ : Integrable E₀ ν[n] :=
    hI ((η.continuous.pow 2).mul ((hGrad (hh.log (fun x => (hPos x).ne'))).norm.pow 2)).continuousOn
  have hI₁ : Integrable E₁ ν[n] := hI (((hGrad η.contDiff).norm.pow 2).continuousOn)
  have hIF : Integrable F ν[n] :=
    hI ((hA.clm_apply (hGrad hh).continuousOn).inner (hGrad φ.contDiff).continuousOn)
  have hPoint : (fun x => (c / 2) * E₀ x) ≤ᵐ[ν[n]] fun x => (2 * C ^ 2 / c) * E₁ x - F x := by
    filter_upwards [ae_restrict_mem (μ := volume0 n) (show MeasurableSet (unitBall n) from measurableSet_ball)]
      with x hx
    rw [hD]
    have h := cofactor_logEnergy_pointwise hc (hNorm x hx) (hEll x hx (U x)) (V x) (η x)
    dsimp only [E₀, E₁]
    linarith only [h]
  have hEnergy := integral_mono_ae (hI₀.const_mul _) ((hI₁.const_mul _).sub hIF) hPoint
  simp only [Pi.sub_apply] at hEnergy
  rw [integral_sub (hI₁.const_mul _) hIF, integral_const_mul, integral_const_mul] at hEnergy
  have hSrc : (∫ x, φ x * f x ∂ν[n]) = ∫ x, η x ^ 2 * (h x)⁻¹ * f x ∂ν[n] := by
    apply integral_congr_ae
    exact Eventually.of_forall fun x => congrArg (fun a => a * f x) (hφ x)
  change -(∫ x, φ x * f x ∂ν[n]) ≤ ∫ x, F x ∂ν[n] at hψ
  rw [hSrc] at hψ
  change _ ≤ (2 * C ^ 2 / c) * (∫ x, E₁ x ∂ν[n]) + ∫ x, η x ^ 2 * (h x)⁻¹ * f x ∂ν[n]
  exact hEnergy.trans (by linarith only [hψ])

end KEBall
