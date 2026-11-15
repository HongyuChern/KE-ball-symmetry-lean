import KEBall.DirichletWeakHarnack

/-!
# Weak Harnack on a single actual log-density path limit

The conclusion keeps the same potential, first jet, Hessian, and cofactor
field as the established limit theorem.  A common Harnack constant is chosen
before the real direction.  The forcing amplitude is allowed to depend on
that direction, as the differentiated log-density equation requires.

This is a path-limit estimate.  It does not assert continuity of the Hessian,
smooth closed-ball extension, or unconditional Dirichlet solvability.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter InnerProductSpace MeasureTheory Metric Set
open scoped ComplexOrder ContDiff Distributions ENNReal Gradient NNReal Topology

noncomputable section

namespace KEBall

local notation "ν[" n "]" => Measure.restrict (volume0 n) (unitBall n)
local notation "𝓓B[" n "]" => 𝓓(dirichletBallOpens n, ℝ)

/-- Uniform local L¹ weak Harnack for all actual directional Hessian
defects, with the explicit quadratic source correction. -/
def HasDirichletHessianWeakHarnack {n : ℕ}
    (G : E n → E n →L[ℝ] ℝ) (c : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ v : E n, ∃ B : ℝ, 0 ≤ B ∧
    ∀ (M R ε : ℝ) (x₀ : E n),
      0 < R → closedBall x₀ R ⊆ unitBall n → 0 < ε →
      (∀ᵐ x ∂(volume0 n).restrict (ball x₀ R), fderiv ℝ G x v v ≤ M) →
      (R ^ (2 * n))⁻¹ * (∫ x in ball x₀ (R / 4),
        |dirichletCorrectedHessianDefect G v (M + ε) (B / (4 * n * c)) R x₀ x|) ≤
        C * essInf (fun z : E n =>
          dirichletCorrectedHessianDefect G v (M + ε) (B / (4 * n * c)) R x₀
            (x₀ + R • z)) (volume.restrict (ball (0 : E n) (1 / 4 : ℝ)))

/-- The bounded smooth log-density path has a single limit satisfying its
actual determinant equation, uniform cofactor ellipticity, distributional
column-divergence identity, and the proved local weak Harnack estimate. -/
theorem exists_dirichlet_limit_with_weakHarnack_of_logDensityPath {n : ℕ} (hn : 2 ≤ n)
    {g : E n → ℝ} (hg : SmoothNear (closedUnitBall n) g)
    {t : ℕ → ℝ} {t₀ : ℝ} (ht : ∀ m, t m ∈ Icc (0 : ℝ) 1)
    (hT : Tendsto t atTop (𝓝 t₀))
    {u : ℕ → E n → ℝ} (hu : ∀ m, SmoothNear (closedUnitBall n) (u m))
    (hu0 : ∀ m x, x ∈ unitSphere n → u m x = 0)
    (huP : ∀ m x, x ∈ unitBall n → (complexHessian (u m) x).PosDef)
    (hEq : ∀ m x, x ∈ unitBall n →
      (complexHessian (u m) x).det.re = Real.exp (t m * g x)) :
    ∃ (w : E n → ℝ) (G : E n → E n →L[ℝ] ℝ) (L : ℝ≥0),
      ContinuousOn w (closedUnitBall n) ∧
      (∀ x ∈ unitBall n, HasFDerivAt w (G x) x) ∧
      LipschitzOnWith L G (closedUnitBall n) ∧
      (∀ x ∈ unitSphere n, w x = 0) ∧
      (∀ᵐ x ∂ν[n], (complexHessianOfRealBilinear (fderiv ℝ G x)).PosDef ∧
        (complexHessianOfRealBilinear (fderiv ℝ G x)).det.re = Real.exp (t₀ * g x)) ∧
      let A (x : E n) := dirichletCofactorOfMatrix (complexHessianOfRealBilinear (fderiv ℝ G x))
      MemLp A ⊤ ν[n] ∧
      ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
        (∀ᵐ x ∂ν[n], ∀ v : E n,
          c * ‖v‖ ^ 2 ≤ inner ℝ (A x v) v ∧ inner ℝ (A x v) v ≤ C * ‖v‖ ^ 2) ∧
        (∀ (v : E n) (ψ : 𝓓B[n]),
          (∫ x, inner ℝ (A x v) (∇ (ψ : E n → ℝ) x) ∂ν[n]) = 0) ∧
        HasDirichletHessianWeakHarnack G c := by
  obtain ⟨w, G, L, hwC, hD, hLip, hw0, hH, hA, hEllData, hDiv, _, hSecond⟩ :=
    exists_dirichlet_limit_with_divergence_free_cofactor_of_logDensityPath
      (by omega : 0 < n) hg ht hT hu hu0 huP hEq
  obtain ⟨c, C, hc, hC, hEll⟩ := hEllData
  refine ⟨w, G, L, hwC, hD, hLip, hw0, hH, hA, c, C, hc, hC, hEll, hDiv, ?_⟩
  obtain ⟨H, hH₀, hHarnack⟩ := exists_correctedHessian_weakHarnack hn hg t₀ hLip hA hDiv hc
    (hEll.mono fun x hx v => (hx v).1)
  refine ⟨H, hH₀, fun v => ?_⟩
  obtain ⟨F, hWeak, hSub⟩ := hSecond v
  exact hHarnack v F (Lp.memLp F) hWeak hSub

end KEBall
