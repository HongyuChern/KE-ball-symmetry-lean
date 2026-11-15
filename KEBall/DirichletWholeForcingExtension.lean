import KEBall.DirichletWholeThirdDerivative
import KEBall.DirichletThirdTrace

/-! Transferring the derivative of localized forcing to the whole space. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter InnerProductSpace MeasureTheory Set TopologicalSpace
open scoped ContDiff Distributions NNReal

namespace KEBall

local notation "ν[" n "]" => Measure.restrict (volume0 n) (unitBall n)
local notation "𝓓E[" n "]" => 𝓓((⊤ : Opens (E n)), ℝ)

theorem integral_mul_dirichletL2ZeroExtension {n : ℕ}
    (u : DirichletBallL2 n ℝ) (p : E n → ℝ) :
    (∫ x, p x * dirichletL2ZeroExtension u x ∂volume0 n) =
      ∫ x, p x * u x ∂ν[n] := by
  rw [← integral_indicator (show MeasurableSet (unitBall n) from measurableSet_ball)]
  apply integral_congr_ae
  filter_upwards [dirichletL2ZeroExtension_ae u] with x hx
  rw [hx]
  by_cases h : x ∈ unitBall n
  · rw [indicator_of_mem h, indicator_of_mem h]
  · rw [indicator_of_notMem h, indicator_of_notMem h, mul_zero]

/-- A compactly localized forcing with a square-integrable directional
derivative on the ball has one after extension by zero to the whole space. -/
theorem euclideanWeakDerivative_dirichletZeroExtension_mul {n : ℕ}
    (d : E n) (f : DirichletBallL2 n ℝ) {F : E n → ℝ} (hF : MemLp F 2 ν[n])
    (hWeak : ∀ ψ : 𝓓(dirichletBallOpens n, ℝ),
      (∫ x, ψ x * F x ∂ν[n]) = -(∫ x, fderiv ℝ (ψ : E n → ℝ) x d * f x ∂ν[n]))
    (η : 𝓓(dirichletBallOpens n, ℝ))
    (hη : ∀ᵐ x ∂ν[n], f x ≠ 0 → η x = 1 ∧ fderiv ℝ (η : E n → ℝ) x d = 0) :
    let q (x : E n) := η x * F x
    let hq : MemLp q 2 ν[n] :=
      memLp_dirichlet_mul_of_continuousOn η.continuous.continuousOn hF
    ∀ ψ : 𝓓E[n],
      (∫ x, ψ x * dirichletL2ZeroExtension (hq.toLp q) x ∂volume0 n) =
        -(∫ x, fderiv ℝ (ψ : E n → ℝ) x d * dirichletL2ZeroExtension f x ∂volume0 n) := by
  let q (x : E n) := η x * F x
  have hq : MemLp q 2 ν[n] := memLp_dirichlet_mul_of_continuousOn η.continuous.continuousOn hF
  change ∀ ψ : 𝓓E[n],
    (∫ x, ψ x * dirichletL2ZeroExtension (hq.toLp q) x ∂volume0 n) =
      -(∫ x, fderiv ℝ (ψ : E n → ℝ) x d * dirichletL2ZeroExtension f x ∂volume0 n)
  intro ψ
  rw [integral_mul_dirichletL2ZeroExtension (hq.toLp q) (ψ : E n → ℝ),
    integral_mul_dirichletL2ZeroExtension f (fun x => fderiv ℝ (ψ : E n → ℝ) x d)]
  let τ := dirichletTestMul η ψ.contDiff
  have he : (∫ x, ψ x * hq.toLp q x ∂ν[n]) = ∫ x, τ x * F x ∂ν[n] := by
    apply integral_congr_ae
    filter_upwards [MemLp.coeFn_toLp hq] with x hx
    change ψ x * hq.toLp q x = (η x * ψ x) * F x
    rw [hx]
    dsimp only [q]
    ring
  rw [he, hWeak τ]
  congr 1
  apply integral_congr_ae
  filter_upwards [hη] with x hx
  by_cases hf : f x = 0
  · simp [hf]
  · obtain ⟨h₀, h₁⟩ := hx hf
    change fderiv ℝ (fun y => η y * ψ y) x d * f x = _
    rw [fderiv_fun_mul (η.contDiff.differentiable (by simp) x) (ψ.contDiff.differentiable (by simp) x)]
    simp only [add_apply, smul_apply, smul_eq_mul, h₀, h₁, one_mul, mul_zero, add_zero]

/-- A compactly localized forcing with a square-integrable directional
derivative on the ball has one after extension by zero to the whole space. -/
theorem exists_euclideanWeakDerivative_of_dirichletZeroExtension {n : ℕ}
    (d : E n) (f : DirichletBallL2 n ℝ) {F : E n → ℝ} (hF : MemLp F 2 ν[n])
    (hWeak : ∀ ψ : 𝓓(dirichletBallOpens n, ℝ),
      (∫ x, ψ x * F x ∂ν[n]) = -(∫ x, fderiv ℝ (ψ : E n → ℝ) x d * f x ∂ν[n]))
    (η : 𝓓(dirichletBallOpens n, ℝ))
    (hη : ∀ᵐ x ∂ν[n], f x ≠ 0 → η x = 1 ∧ fderiv ℝ (η : E n → ℝ) x d = 0) :
    ∃ g : EuclideanL2 n ℝ, ∀ ψ : 𝓓E[n],
      (∫ x, ψ x * g x ∂volume0 n) =
        -(∫ x, fderiv ℝ (ψ : E n → ℝ) x d * dirichletL2ZeroExtension f x ∂volume0 n) := by
  let q (x : E n) := η x * F x
  have hq : MemLp q 2 ν[n] := memLp_dirichlet_mul_of_continuousOn η.continuous.continuousOn hF
  exact ⟨dirichletL2ZeroExtension (hq.toLp q),
    euclideanWeakDerivative_dirichletZeroExtension_mul d f hF hWeak η hη⟩

/-- The localized forcing has an L² directional weak derivative whenever
its scalar forcing term has one and the solution has an L² Hessian. -/
theorem dirichletLocalizedForcing_weakDerivative_of {n : ℕ} (hn : 0 < n)
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)) (d : E n) (u : DirichletSobolev n)
    {S C ds : E n → ℝ} (hS : MemLp S 2 ν[n]) (hS₁ : MemLp ds 2 ν[n])
    (heS : ∀ ψ : 𝓓(dirichletBallOpens n, ℝ), (∫ x, ψ x * ds x ∂ν[n]) =
      -(∫ x, fderiv ℝ (ψ : E n → ℝ) x d * S x ∂ν[n]))
    (hC : ContDiff ℝ ∞ C)
    {Y : E n → E n} (hY : ContDiff ℝ ∞ Y) (D : DirichletBallL2 n ℝ)
    (hD : ∀ ψ : 𝓓(dirichletBallOpens n, ℝ),
      (∫ x, fderiv ℝ (ψ : E n → ℝ) x
        (rankOne ℝ d (Y x) ((u : DirichletBallL2Pair n).snd x)) ∂ν[n]) =
        -(∫ x, ψ x * D x ∂ν[n])) :
    let f (x : E n) := S x - 2 * inner ℝ (Y x) ((u : DirichletBallL2Pair n).snd x) -
      C x * (u : DirichletBallL2Pair n).fst x
    let F (x : E n) := ds x - 2 * D x -
      (C x * inner ℝ d ((u : DirichletBallL2Pair n).snd x) +
        fderiv ℝ C x d * (u : DirichletBallL2Pair n).fst x)
    MemLp F 2 ν[n] ∧ ∀ ψ : 𝓓(dirichletBallOpens n, ℝ),
      (∫ x, ψ x * F x ∂ν[n]) =
        -(∫ x, fderiv ℝ (ψ : E n → ℝ) x d * f x ∂ν[n]) := by
  have : NeZero n := ⟨hn.ne'⟩
  have : IsProbabilityMeasure ν[n] := volume0_restrict_isProbability n
  let U := (u : DirichletBallL2Pair n).snd
  let V := (u : DirichletBallL2Pair n).fst
  let W (x : E n) := inner ℝ (Y x) (U x)
  have hW : MemLp W 2 ν[n] := by
    let a (i : Fin (2 * n)) (x : E n) := inner ℝ (b i) (Y x)
    have he (x : E n) : (∑ i, a i x * inner ℝ (b i) (U x)) = W x := by
      change _ = inner ℝ (Y x) (U x)
      rw [← b.sum_repr' (Y x), sum_inner]
      simp only [real_inner_smul_left, a]
    refine MemLp.ae_eq (Eventually.of_forall he)
      (memLp_finsetSum Finset.univ fun i (_ : i ∈ Finset.univ) => ?_)
    exact memLp_dirichlet_mul_of_continuousOn ((innerSL ℝ (b i)).continuous.comp
      hY.continuous).continuousOn ((Lp.memLp U).const_inner (b i))
  let dc (x : E n) := fderiv ℝ C x d
  let G (x : E n) := inner ℝ d (U x)
  have hdc : ContDiff ℝ ∞ dc := (hC.fderiv_right (by simp)).clm_apply contDiff_const
  have hG : MemLp G 2 ν[n] := (Lp.memLp U).const_inner d
  have hV₀ : MemLp (fun x => C x * G x) 2 ν[n] :=
    memLp_dirichlet_mul_of_continuousOn hC.continuous.continuousOn hG
  have hV₁ : MemLp (fun x => dc x * V x) 2 ν[n] :=
    memLp_dirichlet_mul_of_continuousOn hdc.continuous.continuousOn (Lp.memLp V)
  have hV₂ : MemLp (fun x => C x * V x) 2 ν[n] :=
    memLp_dirichlet_mul_of_continuousOn hC.continuous.continuousOn (Lp.memLp V)
  refine ⟨(hS₁.sub ((Lp.memLp D).const_smul (2 : ℝ))).sub (hV₀.add hV₁), fun ψ => ?_⟩
  let τ := dirichletTestFieldDerivative ψ (fun _ => d) contDiff_const
  have hI (φ : 𝓓(dirichletBallOpens n, ℝ)) {f : E n → ℝ} (hf : MemLp f 2 ν[n]) :
      Integrable (fun x => φ x * f x) ν[n] :=
    (memLp_dirichlet_mul_of_continuousOn φ.continuous.continuousOn hf).integrable (by norm_num)
  have hS_eq : (∫ x, τ x * S x ∂ν[n]) = -(∫ x, ψ x * ds x ∂ν[n]) := by
    have h := heS ψ
    change (∫ x, ψ x * ds x ∂ν[n]) = -(∫ x, τ x * S x ∂ν[n]) at h
    linarith only [h]
  have hD_eq : (∫ x, τ x * W x ∂ν[n]) = -(∫ x, ψ x * D x ∂ν[n]) := by
    have he := hD ψ
    change (∫ x, fderiv ℝ (ψ : E n → ℝ) x (rankOne ℝ d (Y x) (U x)) ∂ν[n]) = _ at he
    change (∫ x, fderiv ℝ (ψ : E n → ℝ) x d * inner ℝ (Y x) (U x) ∂ν[n]) = _
    simpa only [rankOne_apply, map_smul, smul_eq_mul, mul_comm (inner ℝ (Y _) (U _))]
      using he
  have hV_eq : (∫ x, τ x * (C x * V x) ∂ν[n]) =
      -(∫ x, ψ x * (C x * G x) ∂ν[n]) - ∫ x, ψ x * (dc x * V x) ∂ν[n] := by
    let σ := dirichletTestMul ψ hC
    have he := dirichletSobolev_integral_weakGradient u σ d
    change (∫ x, σ x * G x ∂ν[n]) = -(∫ x, fderiv ℝ (σ : E n → ℝ) x d * V x ∂ν[n]) at he
    have hσ (x : E n) : fderiv ℝ (σ : E n → ℝ) x d * V x =
        τ x * (C x * V x) + ψ x * (dc x * V x) := by
      change fderiv ℝ (fun y => ψ y * C y) x d * V x = _
      rw [fderiv_fun_mul (ψ.contDiff.differentiable (by simp) x) (hC.differentiable (by simp) x)]
      change _ = fderiv ℝ (ψ : E n → ℝ) x d * (C x * V x) + ψ x * (dc x * V x)
      simp only [add_apply, smul_apply, smul_eq_mul, dc]
      ring
    simp_rw [hσ, integral_add (hI τ hV₂) (hI ψ hV₁)] at he
    simp only [σ, dirichletTestMul_apply, mul_assoc] at he
    linarith only [he]
  change (∫ x, ψ x * (ds x - 2 * D x - (C x * G x + dc x * V x)) ∂ν[n]) =
    -(∫ x, τ x * (S x - 2 * W x - C x * V x) ∂ν[n])
  have hI₁ : Integrable (fun x => ψ x * ds x - 2 * (ψ x * D x)) ν[n] :=
    (hI ψ hS₁).sub ((hI ψ (Lp.memLp D)).const_mul 2)
  have hI₂ : Integrable (fun x => τ x * S x - 2 * (τ x * W x)) ν[n] :=
    (hI τ hS).sub ((hI τ hW).const_mul 2)
  have hI₃ : Integrable (fun x => ψ x * (C x * G x + dc x * V x)) ν[n] :=
    hI ψ (hV₀.add hV₁)
  simp only [mul_sub, mul_left_comm (ψ _) 2, mul_left_comm (τ _) 2]
  rw [integral_sub hI₁ hI₃, integral_sub hI₂ (hI τ hV₂),
    integral_sub (hI ψ hS₁) ((hI ψ (Lp.memLp D)).const_mul 2),
    integral_sub (hI τ hS) ((hI τ hW).const_mul 2), integral_const_mul, integral_const_mul,
    hS_eq, hD_eq, hV_eq]
  simp_rw [mul_add, integral_add (hI ψ hV₀) (hI ψ hV₁)]
  ring

/-- The localized forcing has an L² directional weak derivative whenever
its scalar forcing term has one and the solution has an L² Hessian. -/
theorem exists_dirichletLocalizedForcing_weakDerivative {n : ℕ} (hn : 0 < n)
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)) (d : E n) (u : DirichletSobolev n)
    (hH : HasDirichletHessianEntriesL2 b u)
    {S C : E n → ℝ} (hS : MemLp S 2 ν[n]) (hSWeak : HasDirichletWeakGradientL2 S)
    (hC : ContDiff ℝ ∞ C)
    {Y : E n → E n} (hY : ContDiff ℝ ∞ Y) :
    let f (x : E n) := S x - 2 * inner ℝ (Y x) ((u : DirichletBallL2Pair n).snd x) -
      C x * (u : DirichletBallL2Pair n).fst x
    ∃ F : E n → ℝ, MemLp F 2 ν[n] ∧ ∀ ψ : 𝓓(dirichletBallOpens n, ℝ),
      (∫ x, ψ x * F x ∂ν[n]) =
        -(∫ x, fderiv ℝ (ψ : E n → ℝ) x d * f x ∂ν[n]) := by
  obtain ⟨ds, hds, heS⟩ := hSWeak d
  obtain ⟨D, hD⟩ := exists_dirichletGradientDivergence_L2 hn b u hH
    (contDiff_rankOne_real (contDiff_const (c := d)) hY)
  exact ⟨_, dirichletLocalizedForcing_weakDerivative_of hn b d u hS hds heS hC hY D hD⟩

end KEBall
