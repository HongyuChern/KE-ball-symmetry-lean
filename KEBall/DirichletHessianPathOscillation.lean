import KEBall.DirichletHessianOscillationStep
import KEBall.DirichletHessianDirectionalFrame

/-!
# Interior Hessian oscillation contraction for the actual path limit

The finite direction family contains every coordinate vector and pair sum.
The conclusion is derived from the original smooth path sequence; the
oscillation or Harnack estimates are not hypotheses of the path-limit theorem.
It does not yet assert a continuous Hessian representative or boundary regularity.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter InnerProductSpace MeasureTheory Metric Set
open scoped BigOperators ComplexOrder ContDiff ENNReal NNReal Topology

noncomputable section

namespace KEBall

local notation "ν[" n "]" => Measure.restrict (volume0 n) (unitBall n)
local notation "e[" n "]" => EuclideanSpace.basisFun (Fin (2 * n)) ℝ

def HasDirichletHessianOscillationDecay {n : ℕ}
    (G : E n → E n →L[ℝ] ℝ) : Prop :=
  ∃ (m : ℕ) (v : Fin m → E n) (θ C : ℝ),
    0 ≤ θ ∧ θ < 1 ∧ 0 ≤ C ∧
    (∀ i : Fin (2 * n), ∃ k : Fin m, v k = e[n] i) ∧
    (∀ i j : Fin (2 * n), ∃ k : Fin m, v k = e[n] i + e[n] j) ∧
    ∀ (x₀ : E n) (R : ℝ), 0 < R → R ≤ 1 → closedBall x₀ R ⊆ unitBall n →
      dirichletHessianOscillation G v x₀ (R / 4) ≤
        θ * dirichletHessianOscillation G v x₀ R + C * R

theorem hasDirichletHessianOscillationDecay_of_cofactor {n : ℕ} (hn : 0 < n)
    {G : E n → E n →L[ℝ] ℝ} {L : ℝ≥0}
    (hG : LipschitzOnWith L G (closedUnitBall n))
    {g : E n → ℝ} (hg : SmoothNear (closedUnitBall n) g)
    (hPos : ∀ᵐ x ∂ν[n], (complexHessianOfRealBilinear (fderiv ℝ G x)).PosDef)
    (hDet : ∀ᵐ x ∂ν[n], (complexHessianOfRealBilinear (fderiv ℝ G x)).det.re = Real.exp (g x))
    (hA : MemLp (fun x => dirichletCofactorOfMatrix
      (complexHessianOfRealBilinear (fderiv ℝ G x))) ⊤ ν[n])
    {c : ℝ} (hc : 0 < c)
    (hEll : ∀ᵐ x ∂ν[n], ∀ v : E n, c * ‖v‖ ^ 2 ≤
      inner ℝ (dirichletCofactorOfMatrix (complexHessianOfRealBilinear (fderiv ℝ G x)) v) v)
    (hH : HasDirichletHessianWeakHarnack G c) :
    HasDirichletHessianOscillationDecay G := by
  obtain ⟨m, v, l, U, hl, hU, hBasis, hPairs, hFrame⟩ :=
    hasUniformDirichletDirectionalFrame_cofactor hn hPos hA hc hEll
  obtain ⟨θ, C, hθ0, hθ1, hC, hStep⟩ :=
    exists_dirichlet_hessian_oscillation_step_of_frame hn hG hg hPos hDet hc hH v hl hU.le hFrame
  exact ⟨m, v, θ, C, hθ0, hθ1, hC, hBasis, hPairs, hStep⟩

theorem exists_dirichlet_limit_with_hessian_oscillation_of_logDensityPath {n : ℕ} (hn : 2 ≤ n)
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
      HasDirichletHessianOscillationDecay G := by
  obtain ⟨w, G, L, hwC, hD, hLip, hw0, hH, hA, c, C, hc, hC, hEll, hDiv, hHarnack⟩ :=
    exists_dirichlet_limit_with_weakHarnack_of_logDensityPath hn hg ht hT hu hu0 huP hEq
  refine ⟨w, G, L, hwC, hD, hLip, hw0, hH, ?_⟩
  have hg' : SmoothNear (closedUnitBall n) (fun x => t₀ * g x) := by
    obtain ⟨U, hU, hSub, hgU⟩ := hg
    exact ⟨U, hU, hSub, contDiffOn_const.mul hgU⟩
  exact hasDirichletHessianOscillationDecay_of_cofactor (by omega) hLip hg'
    (hH.mono fun _ hx => hx.1) (hH.mono fun _ hx => hx.2) hA hc
    (hEll.mono fun _ hx v => (hx v).1) hHarnack

end KEBall
