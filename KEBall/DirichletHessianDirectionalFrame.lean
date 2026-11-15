import KEBall.DirichletHessianWeakHarnack
import KEBall.DirichletFinitePositiveFrame

/-!
# Uniform finite directions for the actual rough cofactor field

The representation below is almost everywhere and uses the original
coefficient field.  It assumes no continuity or differentiability of that
field.  All coefficient bounds and directions are selected uniformly before
the spatial point.  No measurable choice of the individual weights is needed
for the pointwise inequalities used in the oscillation argument.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter InnerProductSpace MeasureTheory Metric Set
open scoped ComplexOrder ENNReal NNReal BigOperators

noncomputable section

namespace KEBall

local notation "ν[" n "]" => Measure.restrict (volume0 n) (unitBall n)
local notation "e[" n "]" => EuclideanSpace.basisFun (Fin (2 * n)) ℝ

def HasUniformDirichletDirectionalFrame {n : ℕ}
    (A : E n → E n →L[ℝ] E n) : Prop :=
  ∃ (m : ℕ) (v : Fin m → E n) (c C : ℝ), 0 < c ∧ 0 < C ∧
    (∀ i : Fin (2 * n), ∃ k : Fin m, v k = e[n] i) ∧
    (∀ i j : Fin (2 * n), ∃ k : Fin m, v k = e[n] i + e[n] j) ∧
    ∀ᵐ x ∂ν[n], ∃ β : Fin m → ℝ, (∀ k, c ≤ β k ∧ β k ≤ C) ∧
      A x = ∑ k : Fin m, β k • rankOne ℝ (v k) (v k)

theorem hasUniformDirichletDirectionalFrame_of_memLp {n : ℕ} (hn : 0 < n)
    {A : E n → E n →L[ℝ] E n} (hA : MemLp A ⊤ ν[n])
    (hSym : ∀ᵐ x ∂ν[n], (A x).toLinearMap.IsSymmetric)
    {c : ℝ} (hc : 0 < c)
    (hEll : ∀ᵐ x ∂ν[n], ∀ v : E n, c * ‖v‖ ^ 2 ≤ inner ℝ (A x v) v) :
    HasUniformDirichletDirectionalFrame A := by
  have : NeZero (2 * n) := ⟨by omega⟩
  have hTop : eLpNormEssSup A ν[n] < ⊤ := by
    simpa only [eLpNorm_exponent_top] using hA.2
  obtain ⟨K, hK⟩ := eLpNormEssSup_lt_top_iff_isBoundedUnder.mp hTop
  obtain ⟨m, v, l, u, hl, hu, hBasis, hPairs, hRep⟩ :=
    exists_dirichlet_uniform_positive_frame e[n] (B := (K : ℝ)) hc
  refine ⟨m, v, l, u, hl, hu, hBasis, hPairs, ?_⟩
  filter_upwards [hK, hSym, hEll] with x hx hxs hxe
  apply hRep (A x)
  refine ⟨hxs, hxe, ?_⟩
  exact_mod_cast hx

/-- The actual complex Hessian cofactor inherits a single finite positive
real frame from the already proved a.e. ellipticity and L∞ bound. -/
theorem hasUniformDirichletDirectionalFrame_cofactor {n : ℕ} (hn : 0 < n)
    {H : E n → Matrix (Fin n) (Fin n) ℂ}
    (hH : ∀ᵐ x ∂ν[n], (H x).PosDef)
    (hA : MemLp (fun x => dirichletCofactorOfMatrix (H x)) ⊤ ν[n])
    {c : ℝ} (hc : 0 < c)
    (hEll : ∀ᵐ x ∂ν[n], ∀ v : E n,
      c * ‖v‖ ^ 2 ≤ inner ℝ (dirichletCofactorOfMatrix (H x) v) v) :
    HasUniformDirichletDirectionalFrame (fun x => dirichletCofactorOfMatrix (H x)) := by
  apply hasUniformDirichletDirectionalFrame_of_memLp hn hA ?_ hc hEll
  filter_upwards [hH] with x hx
  intro v w
  exact (dirichletCofactorOfMatrix_symmetric hx.isHermitian v w).trans (real_inner_comm _ _)

end KEBall
