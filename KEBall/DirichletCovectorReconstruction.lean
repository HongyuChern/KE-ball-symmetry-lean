import KEBall.Domain
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.InnerProductSpace.Dual

/-! Reconstruct a covector and its derivative from an orthonormal basis. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open InnerProductSpace
open scoped BigOperators

noncomputable section

namespace KEBall

local notation "e[" n "]" => EuclideanSpace.basisFun (Fin (2 * n)) ℝ

def dirichletCovectorFromEntries (n : ℕ) :
    (Fin (2 * n) → ℝ) →L[ℝ] (E n →L[ℝ] ℝ) :=
  ∑ i : Fin (2 * n), (ContinuousLinearMap.proj i).smulRight (innerSL ℝ (e[n] i))

theorem dirichletCovectorFromEntries_basis {n : ℕ} (D : E n →L[ℝ] ℝ) :
    dirichletCovectorFromEntries n (fun i => D (e[n] i)) = D := by
  ext v
  simp only [dirichletCovectorFromEntries, _root_.sum_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply,
    _root_.smul_apply, innerSL_apply_apply, smul_eq_mul]
  have hv := (e[n]).sum_repr' v
  conv_rhs => rw [← hv]
  simp only [map_sum, map_smul, smul_eq_mul, mul_comm]

theorem hasFDerivAt_dirichlet_covector_of_basis {n : ℕ}
    {G : E n → E n →L[ℝ] ℝ} {D : E n →L[ℝ] E n →L[ℝ] ℝ} {x : E n}
    (h : ∀ i : Fin (2 * n), HasFDerivAt (fun y => G y (e[n] i))
      ((ContinuousLinearMap.apply ℝ ℝ (e[n] i)).comp D) x) :
    HasFDerivAt G D x := by
  let Q : E n → Fin (2 * n) → ℝ := fun y i => G y (e[n] i)
  let P : E n →L[ℝ] (Fin (2 * n) → ℝ) :=
    ContinuousLinearMap.pi fun i => (ContinuousLinearMap.apply ℝ ℝ (e[n] i)).comp D
  have hQ : HasFDerivAt Q P x := hasFDerivAt_pi.mpr h
  have hC := (dirichletCovectorFromEntries n).hasFDerivAt.comp x hQ
  have hFun : dirichletCovectorFromEntries n ∘ Q = G :=
    funext fun y => dirichletCovectorFromEntries_basis (G y)
  have hDer : (dirichletCovectorFromEntries n).comp P = D := by
    ext v : 1
    change dirichletCovectorFromEntries n (fun i => D v (e[n] i)) = D v
    exact dirichletCovectorFromEntries_basis (D v)
  rw [hFun, hDer] at hC
  exact hC

end KEBall
