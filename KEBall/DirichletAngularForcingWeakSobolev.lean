import KEBall.DirichletFluxWeakSobolev
import KEBall.DirichletAngularWeakSobolev

/-! The differentiated angular equation with forcing of arbitrary finite weak order. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Set
open scoped ContDiff Distributions NNReal

namespace KEBall

local notation "ν[" n "]" => Measure.restrict (volume0 n) (unitBall n)
local notation "𝓓B[" n "]" => 𝓓(dirichletBallOpens n, ℝ)

/-- Angular differentiation of a forcing loses one order of L² weak regularity. -/
theorem exists_dirichletAngularForcing_with_weakDerivatives {n : ℕ} (hn : 0 < n)
    (g : DirichletBallL2 n ℝ) (k : ℕ)
    (hg : HasDirichletWeakDerivativesL2 (g : E n → ℝ) (k + 1))
    (S : E n →L[ℝ] E n) (hS : star S = -S) :
    ∃ gS : DirichletBallL2 n ℝ, HasDirichletWeakDerivativesL2 (gS : E n → ℝ) k ∧
      ∀ ψ : 𝓓B[n], (∫ x, ψ x * gS x ∂ν[n]) =
        -(∫ x, fderiv ℝ (ψ : E n → ℝ) x (S x) * g x ∂ν[n]) := by
  let b := EuclideanSpace.basisFun (Fin (2 * n)) ℝ
  have he (i : Fin (2 * n)) := (hasDirichletWeakDerivativesL2_succ_iff.mp hg).2 (b i)
  choose F hF heF using he
  let c (i : Fin (2 * n)) (x : E n) := inner ℝ (b i) (S x)
  have hc (i : Fin (2 * n)) : ContDiff ℝ ∞ (c i) := (innerSL ℝ (b i)).contDiff.comp S.contDiff
  let R (x : E n) := ∑ i, c i x * F i x
  have hR : HasDirichletWeakDerivativesL2 R k :=
    HasDirichletWeakDerivativesL2.finsetSum hn Finset.univ fun i _ => (hF i).mul_smooth hn (hc i)
  have heR := (dirichletWeakFieldDerivative_of_basis hn b (Lp.memLp g) F
    (fun i => (hF i).1) heF S.contDiff).2
  let gS := hR.1.toLp R
  refine ⟨gS, hR.congr (MemLp.coeFn_toLp hR.1).symm, fun ψ => ?_⟩
  have hLp : (∫ x, ψ x * gS x ∂ν[n]) = ∫ x, ψ x * R x ∂ν[n] := by
    apply integral_congr_ae
    filter_upwards [MemLp.coeFn_toLp hR.1] with x hx
    change ψ x * hR.1.toLp R x = _
    rw [hx]
  have hDiv (x : E n) : dirichletVectorDivergence b (S : E n → E n) x = 0 :=
    (dirichletVectorDivergence_basisFun_eq_euclideanDivergence S x).trans
      (euclideanDivergence_skew_field S hS x)
  rw [hLp]
  have h := heR ψ
  change (∫ x, ψ x * R x ∂ν[n]) =
    -(∫ x, (fderiv ℝ (ψ : E n → ℝ) x (S x) + ψ x * dirichletVectorDivergence b S x) *
      g x ∂ν[n]) at h
  simpa only [hDiv, mul_zero, add_zero] using h

/-- The differentiated angular Dirichlet equation has forcing of order k
when the original forcing has order k+1 and the potential has order k+2. -/
theorem IsDirichletWeakSolution.exists_angularDerivative_with_weakForcing
    {n : ℕ} (hn : 0 < n) (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n))
    {A : E n → E n →L[ℝ] E n} (hA : MemLp A ⊤ ν[n]) (hAc : ContDiff ℝ ∞ A)
    {l : ℝ} (hl : 0 < l)
    (hE : ∀ x ∈ unitBall n, ∀ v : E n, l * ‖v‖ ^ 2 ≤ inner ℝ (A x v) v)
    {K : ℝ≥0} (hLipA : LipschitzOnWith K A (closedUnitBall n))
    {M : ℝ} (hM₀ : 0 ≤ M) (hM : ∀ x ∈ closedUnitBall n, ‖A x‖ ≤ M)
    {g : DirichletBallL2 n ℝ} {u : DirichletSobolev n} (hu : IsDirichletWeakSolution A g u)
    (k : ℕ) (hU : HasDirichletWeakDerivativesL2 ((u : DirichletBallL2Pair n).fst : E n → ℝ) (k + 2))
    (hg : HasDirichletWeakDerivativesL2 (g : E n → ℝ) (k + 1))
    (S : E n →L[ℝ] E n) (hS : star S = -S) :
    ∃ (v : DirichletSobolev n) (g' : DirichletBallL2 n ℝ),
      HasDirichletWeakDerivativesL2 (g' : E n → ℝ) k ∧
      IsDirichletWeakSolution A g' v ∧
      ∀ ψ : 𝓓B[n], (∫ x, ψ x * (v : DirichletBallL2Pair n).fst x ∂ν[n]) =
        -(∫ x, fderiv ℝ (ψ : E n → ℝ) x (S x) * (u : DirichletBallL2Pair n).fst x ∂ν[n]) := by
  have hAE := (ae_restrict_mem (μ := volume0 n)
    (show MeasurableSet (unitBall n) from measurableSet_ball)).mono hE
  obtain ⟨v, hv⟩ :=
    exists_dirichletSobolev_angularDerivative_L2 hn hA hl hAE hLipA hM₀ hM hu S hS
  obtain ⟨gS, hGS, heGS⟩ := exists_dirichletAngularForcing_with_weakDerivatives hn g k hg S hS
  obtain ⟨D, hD, heD⟩ := exists_dirichletGradientDivergence_with_weakDerivatives hn b u k hU
    (contDiff_dirichletAngularCoefficient hAc S)
  exact ⟨v, gS + D, ((hGS.add hn hD).congr (Lp.coeFn_add gS D).symm),
    hu.angularDerivative_of_forcing hn b hA hAc S hS heGS v hv heD, hv⟩

end KEBall
