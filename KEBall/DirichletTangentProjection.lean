import KEBall.DirichletAngularGradient

/-! A finite set of rotational directions recovers the projection to the
tangent space of each centered sphere. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open InnerProductSpace

namespace KEBall

/-- The skew generator associated to two fixed vectors. -/
noncomputable def dirichletPlaneRotation {n : ℕ} (v w : E n) : E n →L[ℝ] E n :=
  rankOne ℝ v w - rankOne ℝ w v

theorem dirichletPlaneRotation_apply {n : ℕ} (v w x : E n) :
    dirichletPlaneRotation v w x = inner ℝ w x • v - inner ℝ v x • w := by
  simp only [dirichletPlaneRotation, sub_apply, rankOne_apply]

theorem dirichletPlaneRotation_star {n : ℕ} (v w : E n) :
    star (dirichletPlaneRotation v w) = -dirichletPlaneRotation v w := by
  simp only [ContinuousLinearMap.star_eq_adjoint, dirichletPlaneRotation, map_sub, adjoint_rankOne,
    neg_sub]

/-- Multiplying each rotation by the corresponding coordinate gives the
tangential component of a constant direction, scaled by the squared radius. -/
theorem sum_dirichletPlaneRotation_eq_tangentProjection {n : ℕ}
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)) (v x : E n) :
    (∑ i, inner ℝ (b i) x • dirichletPlaneRotation v (b i) x) =
      ‖x‖ ^ 2 • v - inner ℝ v x • x := by
  simp only [dirichletPlaneRotation_apply, smul_sub, smul_smul, Finset.sum_sub_distrib]
  rw [← Finset.sum_smul]
  simp_rw [← pow_two]
  rw [b.sum_sq_inner_right]
  congr 1
  calc
    _ = inner ℝ v x • ∑ i, inner ℝ (b i) x • b i := by
      rw [Finset.smul_sum]
      simp only [smul_smul, mul_comm]
    _ = _ := by rw [b.sum_repr']

/-- The coefficient in the remaining radial direction stays uniformly
positive on any annulus bounded away from the origin. -/
theorem dirichlet_radialCoefficient_ge {n : ℕ} {A : E n →L[ℝ] E n} {l r : ℝ}
    (hl : 0 ≤ l) (hr : 0 ≤ r) (x : E n) (hx : r ≤ ‖x‖)
    (hE : ∀ v : E n, l * ‖v‖ ^ 2 ≤ inner ℝ (A v) v) :
    l * r ^ 2 ≤ inner ℝ (A x) x :=
  (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr hx 2) hl).trans (hE x)

/-- The divergence of the weighted sum of rotation generators. -/
theorem sum_inner_dirichletPlaneRotation {n : ℕ}
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)) (v x : E n) :
    (∑ i, inner ℝ (b i) (dirichletPlaneRotation v (b i) x)) =
      (1 - (2 : ℝ) * n) * inner ℝ v x := by
  have hDiag (i : Fin (2 * n)) : inner ℝ (b i) (b i) = 1 := by
    rw [real_inner_self_eq_norm_sq, b.orthonormal.1 i]
    norm_num
  simp only [dirichletPlaneRotation_apply, inner_sub_right, real_inner_smul_right,
    hDiag, mul_one, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat]
  have hSum : (∑ i, inner ℝ (b i) x * inner ℝ (b i) v) = inner ℝ v x := by
    calc
      _ = ∑ i, inner ℝ v (b i) * inner ℝ (b i) x := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [real_inner_comm v (b i), mul_comm]
      _ = _ := b.sum_inner_mul_inner v x
  rw [hSum]
  ring


end KEBall
