import KEBall.DirichletFiniteDirections

/-! Bilinear Hessian contraction in a genuine orthonormal basis. -/

set_option autoImplicit false

open InnerProductSpace
open scoped BigOperators

noncomputable section

namespace KEBall

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {ι : Type*} [Fintype ι]

def dirichletBilinearContraction (b : OrthonormalBasis ι ℝ V)
    (A : V →L[ℝ] V) (D : V →L[ℝ] V →L[ℝ] ℝ) : ℝ :=
  ∑ i : ι, D (A (b i)) (b i)

def dirichletBilinearContractionLinearMap (b : OrthonormalBasis ι ℝ V)
    (D : V →L[ℝ] V →L[ℝ] ℝ) : (V →L[ℝ] V) →ₗ[ℝ] ℝ where
  toFun A := dirichletBilinearContraction b A D
  map_add' A B := by simp only [dirichletBilinearContraction, add_apply, map_add, Finset.sum_add_distrib]
  map_smul' c A := by
    simp only [dirichletBilinearContraction, smul_apply, map_smul, smul_eq_mul,
      RingHom.id_apply, Finset.mul_sum]

theorem dirichletBilinearContraction_rankOne_general (b : OrthonormalBasis ι ℝ V)
    (D : V →L[ℝ] V →L[ℝ] ℝ) (v w : V) :
    dirichletBilinearContraction b (rankOne ℝ v w) D = D v w := by
  unfold dirichletBilinearContraction
  simp only [rankOne_apply, map_smul, smul_apply, smul_eq_mul]
  calc
    _ = D v (∑ i : ι, inner ℝ (b i) w • b i) := by
      simp only [map_sum, map_smul, smul_eq_mul, real_inner_comm w]
    _ = D v w := by rw [b.sum_repr']

theorem dirichletBilinearContraction_rankOne (b : OrthonormalBasis ι ℝ V)
    (D : V →L[ℝ] V →L[ℝ] ℝ) (v : V) :
    dirichletBilinearContraction b (rankOne ℝ v v) D = D v v := by
  unfold dirichletBilinearContraction
  simp only [rankOne_apply, map_smul, smul_apply, smul_eq_mul]
  calc
    _ = D v (∑ i : ι, inner ℝ (b i) v • b i) := by
      simp only [map_sum, map_smul, smul_eq_mul, real_inner_comm v]
    _ = D v v := by rw [b.sum_repr']

theorem dirichletBilinearContraction_sum {κ : Type*} [Fintype κ]
    (b : OrthonormalBasis ι ℝ V) (D : V →L[ℝ] V →L[ℝ] ℝ)
    (a : κ → ℝ) (A : κ → V →L[ℝ] V) :
    dirichletBilinearContraction b (∑ k : κ, a k • A k) D =
      ∑ k : κ, a k * dirichletBilinearContraction b (A k) D := by
  simp only [dirichletBilinearContraction, _root_.sum_apply, smul_apply,
    map_sum, map_smul, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_comm

/-- The directional values are exactly those of the original bilinear
Hessian, with no replacement scalar family. -/
theorem dirichletBilinearContraction_of_frame {κ : Type*} [Fintype κ]
    (b : OrthonormalBasis ι ℝ V) (D : V →L[ℝ] V →L[ℝ] ℝ)
    {A : V →L[ℝ] V} (a : κ → ℝ) (v : κ → V)
    (hA : A = ∑ k : κ, a k • rankOne ℝ (v k) (v k)) :
    dirichletBilinearContraction b A D = ∑ k : κ, a k * D (v k) (v k) := by
  rw [hA, dirichletBilinearContraction_sum]
  simp only [dirichletBilinearContraction_rankOne]

end KEBall
