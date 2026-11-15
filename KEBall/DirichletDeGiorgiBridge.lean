import KEBall.DirichletHessianHarnackInput
import KEBall.DirichletDeGiorgiCoefficients
import DifferentialGeometry.External.DeGiorgi.SobolevSpace.PositiveTestDensity
import DifferentialGeometry.External.DeGiorgi.ScaledBallEstimates

/-!
# From the actual Dirichlet weak gradient to the De Giorgi interface

The normalization change is by the positive scalar `n! / π^n` on both
sides of every weak identity.  The explicit weak-gradient witness is
retained when passing from bundled compactly supported tests to the
De Giorgi Sobolev class.  No continuity of the Hessian is assumed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter InnerProductSpace MeasureTheory Metric Set
open scoped ContDiff Distributions ENNReal Gradient Topology

noncomputable section

namespace KEBall

local notation "ν[" n "]" => Measure.restrict (volume0 n) (unitBall n)
local notation "μ[" n "]" => Measure.restrict (volume : Measure (E n)) (unitBall n)
local notation "e[" n "]" => EuclideanSpace.basisFun (Fin (2 * n)) ℝ
local notation "𝓓B[" n "]" => 𝓓(dirichletBallOpens n, ℝ)

/-- The S053/S055 bundled-test identity is the literal coordinate weak
derivative used by the pinned De Giorgi development. -/
theorem IsDirichletWeakGradient.hasWeakGrad {n : ℕ} [NeZero n]
    {f : E n → ℝ} {F : E n → E n}
    (h : IsDirichletWeakGradient f F) :
    DeGiorgi.HasWeakGrad F f (unitBall n) := by
  intro i φ hφ hCompact hSupport
  let ψ : 𝓓B[n] := ⟨φ, hφ, hCompact, hSupport⟩
  have hEq := h i ψ
  simp only [EuclideanSpace.basisFun_apply,
    EuclideanSpace.inner_single_left, map_one, one_mul] at hEq
  change (∫ x in unitBall n, φ x * F x i ∂volume0 n) =
    -(∫ x in unitBall n, fderiv ℝ φ x (EuclideanSpace.single i 1) * f x ∂volume0 n) at hEq
  rw [setIntegral_volume0, setIntegral_volume0, ← mul_neg] at hEq
  have hc : (n.factorial : ℝ) / Real.pi ^ n ≠ 0 := by positivity
  have hEq' := mul_left_cancel₀ hc hEq
  have hFlip : (∫ x in unitBall n, fderiv ℝ φ x (EuclideanSpace.single i 1) * f x) =
      -(∫ x in unitBall n, φ x * F x i) := by
    linarith only [hEq']
  simpa only [mul_comm] using hFlip

/-- A Sobolev witness with exactly the gradient supplied by the path limit. -/
def dirichletDeGiorgiWitness {n : ℕ} [NeZero n]
    {f : E n → ℝ} {F : E n → E n}
    (hf : MemLp f 2 ν[n]) (hF : MemLp F 2 ν[n])
    (hWeak : IsDirichletWeakGradient f F) :
    DeGiorgi.MemW1pWitness 2 f (unitBall n) where
  memLp := memLp_volume0_restrict_iff.mp hf
  weakGrad := F
  weakGrad_component_memLp := by
    intro i
    have hFV : MemLp F 2 μ[n] := memLp_volume0_restrict_iff.mp hF
    simpa only [EuclideanSpace.inner_single_left, map_one, one_mul] using
      hFV.const_inner (𝕜 := ℝ) (c := EuclideanSpace.single i (1 : ℝ))
  isWeakGrad := hWeak.hasWeakGrad

/-- The external smooth gradient is the existing Euclidean gradient,
without a further factor from the complex-coordinate conventions. -/
theorem deGiorgi_smoothGradField_eq_gradient {n : ℕ} (f : E n → ℝ) :
    DeGiorgi.smoothGradField f = ∇ f := by
  funext x
  apply PiLp.ext
  intro i
  change fderiv ℝ f x (EuclideanSpace.single i 1) = (∇ f x) i
  rw [← inner_gradient_left, real_inner_comm, EuclideanSpace.inner_single_left]
  simp

/-- The actual weak supersolution is accepted by all Sobolev tests after
the positive-test density theorem.  `hAB` records the exact coefficient
action, so the normalization factor cannot be silently changed. -/
theorem isDeGiorgiSupersolution_of_dirichlet_weak {n : ℕ} [NeZero n]
    {f : E n → ℝ} {F : E n → E n}
    (hf : MemLp f 2 ν[n]) (hF : MemLp F 2 ν[n])
    (hWeak : IsDirichletWeakGradient f F)
    {B : E n → E n →L[ℝ] E n}
    (hSuper : ∀ ψ : 𝓓B[n], (∀ x ∈ unitBall n, 0 ≤ ψ x) →
      0 ≤ ∫ x, inner ℝ (B x (F x)) (∇ (ψ : E n → ℝ) x) ∂ν[n])
    (A : DeGiorgi.EllipticCoeff (2 * n) (unitBall n))
    {κ : ℝ} (hκ : 0 ≤ κ)
    (hAB : ∀ᵐ x ∂μ[n], ∀ v : E n,
      DeGiorgi.matMulE (A.a x) v = κ • B x v) :
    DeGiorgi.IsSupersolution A f := by
  let w := dirichletDeGiorgiWitness hf hF hWeak
  apply DeGiorgi.IsSupersolution.of_nonnegative_smooth_tests isOpen_ball A w.memW1p
  intro u ψ hψ hψnonneg
  let φ : 𝓓B[n] := ⟨ψ, hψ.1, hψ.2.1, hψ.2.2⟩
  have hGrad : u.weakGrad =ᵐ[μ[n]] F :=
    DeGiorgi.MemW1pWitness.ae_eq isOpen_ball u w
  have hEq : DeGiorgi.bilinFormOfCoeff A u
      (DeGiorgi.smoothTestWitness isOpen_ball hψ) =
      κ * ∫ x in unitBall n, inner ℝ (B x (F x)) (∇ ψ x) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [hGrad, hAB] with x hx hBx
    change inner ℝ (DeGiorgi.matMulE (A.a x) (u.weakGrad x))
      (DeGiorgi.smoothGradField ψ x) = _
    rw [hx, hBx, deGiorgi_smoothGradField_eq_gradient, real_inner_smul_left]
  have h := hSuper φ (fun x _ => hψnonneg x)
  change 0 ≤ ∫ x in unitBall n, inner ℝ (B x (F x)) (∇ ψ x) ∂volume0 n at h
  rw [setIntegral_volume0] at h
  have hc : 0 < (n.factorial : ℝ) / Real.pi ^ n := by positivity
  rw [hEq]
  exact mul_nonneg hκ (nonneg_of_mul_nonneg_right h hc)

end KEBall
