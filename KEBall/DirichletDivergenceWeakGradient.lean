import KEBall.DirichletGlobalWeakThirdDerivative

/-! The first weak derivatives of the divergence correction. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Set
open scoped ContDiff Distributions NNReal

namespace KEBall

local notation "ν[" n "]" => Measure.restrict (volume0 n) (unitBall n)
local notation "b[" n "]" => EuclideanSpace.basisFun (Fin (2 * n)) ℝ

/-- The third weak coordinate derivatives admit square-integrable representatives. -/
def HasDirichletThirdDerivativeEntriesL2 {n : ℕ}
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)) (u : DirichletSobolev n) : Prop :=
  ∀ i j k : Fin (2 * n), ∃ F : E n → ℝ, MemLp F 2 ν[n] ∧
    ∀ ψ : 𝓓(dirichletBallOpens n, ℝ),
      dirichletThirdDerivativeEntry u ψ (b k) (b j) (b i) = ∫ x, ψ x * F x ∂ν[n]

/-- When the third derivatives of the potential are in L², each L² Hessian
representative has an L² weak gradient. -/
theorem hasDirichletWeakGradientL2_of_hessianEntry {n : ℕ} (hn : 0 < n)
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)) (u : DirichletSobolev n)
    (hThird : HasDirichletThirdDerivativeEntriesL2 b u)
    (i j : Fin (2 * n)) {F : E n → ℝ} (hF : MemLp F 2 ν[n])
    (heF : ∀ ψ : 𝓓(dirichletBallOpens n, ℝ),
      dirichletHessianEntry u ψ (b j) (b i) = ∫ x, ψ x * F x ∂ν[n]) :
    HasDirichletWeakGradientL2 F := by
  apply HasDirichletWeakGradientL2.of_basis hn b hF
  intro k
  obtain ⟨G, hG, heG⟩ := hThird i j k
  refine ⟨G, hG, fun ψ => ?_⟩
  rw [← heG ψ, dirichletThirdDerivativeEntry_eq_integral u (b j) (b i) heF]

/-- The coordinate gradient of the potential has its weak gradient in L²
when the Hessian entries are in L². -/
theorem hasDirichletWeakGradientL2_of_gradientEntry {n : ℕ} (hn : 0 < n)
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)) (u : DirichletSobolev n)
    (hH : HasDirichletHessianEntriesL2 b u) (i : Fin (2 * n)) :
    HasDirichletWeakGradientL2 (fun x => inner ℝ (b i) ((u : DirichletBallL2Pair n).snd x)) := by
  apply HasDirichletWeakGradientL2.of_basis hn b ((Lp.memLp _).const_inner (b i))
  intro j
  obtain ⟨F, hF, heF⟩ := hH i j
  exact ⟨F, hF, fun ψ => (heF ψ).symm⟩

/-- The divergence of a smooth matrix times the weak gradient belongs to
the first-order L² Sobolev space when the potential has third derivatives in L². -/
theorem exists_dirichletGradientDivergence_with_weakGradient {n : ℕ} (hn : 0 < n)
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)) (u : DirichletSobolev n)
    (hH : HasDirichletHessianEntriesL2 b u) (hThird : HasDirichletThirdDerivativeEntriesL2 b u)
    {B : E n → E n →L[ℝ] E n} (hB : ContDiff ℝ ∞ B) :
    ∃ d : DirichletBallL2 n ℝ, HasDirichletWeakGradientL2 (d : E n → ℝ) ∧
      ∀ ψ : 𝓓(dirichletBallOpens n, ℝ),
        (∫ x, fderiv ℝ (ψ : E n → ℝ) x (B x ((u : DirichletBallL2Pair n).snd x)) ∂ν[n]) =
          -(∫ x, ψ x * d x ∂ν[n]) := by
  unfold HasDirichletHessianEntriesL2 at hH
  choose F hF heF using hH
  let c (i j : Fin (2 * n)) (x : E n) := inner ℝ (b j) (B x (b i))
  have hc (i j : Fin (2 * n)) : ContDiff ℝ ∞ (c i j) :=
    contDiff_dirichletCoefficientEntry hB (b i) (b j)
  let T (i j : Fin (2 * n)) (x : E n) := c i j x * F i j x
  have hT (i j : Fin (2 * n)) : MemLp (T i j) 2 ν[n] :=
    memLp_dirichlet_mul_of_continuousOn (hc i j).continuous.continuousOn (hF i j)
  have hWT (i j : Fin (2 * n)) : HasDirichletWeakGradientL2 (T i j) :=
    (hasDirichletWeakGradientL2_of_hessianEntry hn b u hThird i j (hF i j) (heF i j)).mul_smooth
      hn (hF i j) (hc i j)
  let P (i : Fin (2 * n)) (x : E n) := ∑ j, T i j x
  have hP (i : Fin (2 * n)) : MemLp (P i) 2 ν[n] :=
    memLp_finsetSum Finset.univ fun j _ => hT i j
  have hWP (i : Fin (2 * n)) : HasDirichletWeakGradientL2 (P i) :=
    HasDirichletWeakGradientL2.finsetSum hn Finset.univ (fun j _ => hT i j) (fun j _ => hWT i j)
  let R (x : E n) := ∑ i, P i x
  have hR : MemLp R 2 ν[n] := memLp_finsetSum Finset.univ fun i _ => hP i
  have hWR : HasDirichletWeakGradientL2 R :=
    HasDirichletWeakGradientL2.finsetSum hn Finset.univ (fun i _ => hP i) (fun i _ => hWP i)
  let D (i : Fin (2 * n)) (x : E n) := dirichletColumnDivergence b B (b i) x
  have hD (i : Fin (2 * n)) : ContDiff ℝ ∞ (D i) :=
    contDiff_dirichletVectorDivergence b (hB.clm_apply contDiff_const)
  let U := (u : DirichletBallL2Pair n).snd
  let V (i : Fin (2 * n)) (x : E n) := D i x * inner ℝ (b i) (U x)
  have hV (i : Fin (2 * n)) : MemLp (V i) 2 ν[n] :=
    memLp_dirichlet_mul_of_continuousOn (hD i).continuous.continuousOn ((Lp.memLp U).const_inner (b i))
  have hWV (i : Fin (2 * n)) : HasDirichletWeakGradientL2 (V i) :=
    (hasDirichletWeakGradientL2_of_gradientEntry hn b u (fun i j => ⟨F i j, hF i j, heF i j⟩) i).mul_smooth
      hn ((Lp.memLp U).const_inner (b i)) (hD i)
  let C := dirichletDivergenceGradientCorrection b u B
  have hC : MemLp C 2 ν[n] := memLp_finsetSum Finset.univ fun i _ => hV i
  have hWC : HasDirichletWeakGradientL2 C :=
    HasDirichletWeakGradientL2.finsetSum hn Finset.univ (fun i _ => hV i) (fun i _ => hWV i)
  obtain ⟨d, hd, he⟩ := exists_dirichletGradientDivergence_L2_of_trace hn b u hB hR
    (dirichletHessianTrace_eq_integral_of_entries hn b u hB F hF heF)
  exact ⟨d, (hWR.add hn hR hC hWC).congr hd.symm, he⟩

end KEBall
