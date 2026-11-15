import KEBall.DirichletSchauderContraction

/-!
# Positive definiteness in the Schauder coordinates

The real matrix used by the imported estimates represents the actual
continuous linear operator in the project's orthonormal basis.  Its
quadratic form is the original quadratic form, with no normalization
change.  Thus symmetry and coercivity pass to precisely this matrix.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open InnerProductSpace Matrix
open scoped BigOperators

namespace KEBall

local notation "e[" n "]" => EuclideanSpace.basisFun (Fin (2 * n)) ℝ

theorem dirichletSchauderMatrix_eq_toMatrix {n : ℕ} (A : E n →L[ℝ] E n) :
    dirichletSchauderMatrix A = LinearMap.toMatrix e[n].toBasis e[n].toBasis A.toLinearMap := by
  ext i j
  rw [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply]
  exact (e[n].repr_apply_apply (A (e[n] j)) i).symm

theorem dirichletSchauderMatrix_quadratic {n : ℕ} (A : E n →L[ℝ] E n)
    (z : Fin (2 * n) → ℝ) :
    star z ⬝ᵥ (dirichletSchauderMatrix A *ᵥ z) =
      inner ℝ (A (WithLp.toLp 2 z)) (WithLp.toLp 2 z) := by
  let b := e[n].toBasis
  let v : E n := WithLp.toLp 2 z
  have hrepr (w : E n) : ⇑(b.repr w) = w.ofLp := by
    funext i
    rw [show b = e[n].toBasis from rfl,
      OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr]
  have h := LinearMap.toMatrix_mulVec_repr b b A.toLinearMap v
  rw [hrepr, hrepr] at h
  change LinearMap.toMatrix b b A.toLinearMap *ᵥ z = (A v).ofLp at h
  rw [dirichletSchauderMatrix_eq_toMatrix, h, dotProduct_comm,
    ← EuclideanSpace.inner_eq_star_dotProduct]
  exact real_inner_comm _ _

theorem dirichletSchauderMatrix_isHermitian {n : ℕ} {A : E n →L[ℝ] E n}
    (hA : ∀ v z : E n, inner ℝ (A v) z = inner ℝ (A z) v) :
    (dirichletSchauderMatrix A).IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply, star_trivial, dirichletSchauderMatrix]
  calc
    inner ℝ (e[n] j) (A (e[n] i)) = inner ℝ (A (e[n] i)) (e[n] j) := real_inner_comm _ _
    _ = inner ℝ (A (e[n] j)) (e[n] i) := hA _ _
    _ = inner ℝ (e[n] i) (A (e[n] j)) := real_inner_comm _ _

theorem dirichletSchauderMatrix_posDef {n : ℕ} {A : E n →L[ℝ] E n}
    (hSym : ∀ v z : E n, inner ℝ (A v) z = inner ℝ (A z) v)
    (hPos : ∀ v : E n, v ≠ 0 → 0 < inner ℝ (A v) v) :
    (dirichletSchauderMatrix A).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (dirichletSchauderMatrix_isHermitian hSym)
  intro z hz
  rw [dirichletSchauderMatrix_quadratic]
  apply hPos
  intro h
  exact hz (congrArg WithLp.ofLp h)

theorem dirichletSchauderMatrix_posDef_of_coercive {n : ℕ} {A : E n →L[ℝ] E n}
    (hSym : ∀ v z : E n, inner ℝ (A v) z = inner ℝ (A z) v)
    {l : ℝ} (hl : 0 < l)
    (hE : ∀ v : E n, l * ‖v‖ ^ 2 ≤ inner ℝ (A v) v) :
    (dirichletSchauderMatrix A).PosDef := by
  apply dirichletSchauderMatrix_posDef hSym
  intro v hv
  exact (mul_pos hl (sq_pos_of_pos (norm_pos_iff.mpr hv))).trans_le (hE v)

end KEBall
