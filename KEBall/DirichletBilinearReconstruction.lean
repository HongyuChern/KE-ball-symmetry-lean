import KEBall.Domain

/-! Reconstruction of a real bilinear form from its actual basis entries. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open InnerProductSpace
open scoped BigOperators

noncomputable section

namespace KEBall

local notation "e[" n "]" => EuclideanSpace.basisFun (Fin (2 * n)) ℝ

def dirichletBilinearBasis {n : ℕ} (i j : Fin (2 * n)) :
    E n →L[ℝ] E n →L[ℝ] ℝ :=
  (innerSL ℝ (e[n] i)).smulRight (innerSL ℝ (e[n] j))

def dirichletBilinearFromEntries {n : ℕ} (a : Fin (2 * n) → Fin (2 * n) → ℝ) :
    E n →L[ℝ] E n →L[ℝ] ℝ :=
  ∑ i : Fin (2 * n), ∑ j : Fin (2 * n), a i j • dirichletBilinearBasis i j

theorem dirichletBilinearFromEntries_basis {n : ℕ} (D : E n →L[ℝ] E n →L[ℝ] ℝ) :
    dirichletBilinearFromEntries (fun i j => D (e[n] i) (e[n] j)) = D := by
  ext x y
  simp only [dirichletBilinearFromEntries, dirichletBilinearBasis, _root_.sum_apply,
    _root_.smul_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, smul_eq_mul]
  have hx := (e[n]).sum_repr' x
  have hy := (e[n]).sum_repr' y
  conv_rhs => rw [← hx, ← hy]
  simp only [map_sum, map_smul, _root_.sum_apply, _root_.smul_apply, smul_eq_mul]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm (f := fun k j => ⟪e[n] k, y⟫_ℝ * (⟪e[n] j, x⟫_ℝ * D (e[n] j) (e[n] k)))]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem continuousOn_dirichletBilinearFromEntries {n : ℕ} {s : Set (E n)}
    {a : E n → Fin (2 * n) → Fin (2 * n) → ℝ}
    (ha : ∀ i j, ContinuousOn (fun x => a x i j) s) :
    ContinuousOn (fun x => dirichletBilinearFromEntries (a x)) s := by
  letI : ContinuousAdd (E n →L[ℝ] E n →L[ℝ] ℝ) :=
    (ContinuousLinearMap.topologicalAddGroup :
      IsTopologicalAddGroup (E n →L[ℝ] E n →L[ℝ] ℝ)).toContinuousAdd
  unfold dirichletBilinearFromEntries
  apply continuousOn_finsetSum
  intro i _
  apply continuousOn_finsetSum
  intro j _
  exact (ha i j).smul continuousOn_const

end KEBall
