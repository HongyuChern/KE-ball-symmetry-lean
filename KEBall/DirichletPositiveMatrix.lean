import KEBall.DirichletSobolevClassical

/-! Stability of positive definiteness in the Hermitian subspace. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Metric Set
open scoped ComplexOrder ContDiff Matrix Topology

namespace KEBall

/-- All Hermitian matrices in an open neighborhood of a positive-definite
matrix are positive definite. -/
theorem exists_isOpen_hermitian_posDef_nhds {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.PosDef) :
    ∃ U : Set (Matrix (Fin n) (Fin n) ℂ), IsOpen U ∧ A ∈ U ∧
      ∀ B ∈ U, B.IsHermitian → B.PosDef := by
  let E := EuclideanSpace ℂ (Fin n)
  let q (p : Matrix (Fin n) (Fin n) ℂ × E) :=
    (star p.2.ofLp ⬝ᵥ (p.1 *ᵥ p.2.ofLp)).re
  have hCoord (i : Fin n) : Continuous (fun p : Matrix (Fin n) (Fin n) ℂ × E => p.2.ofLp i) :=
    (EuclideanSpace.proj i).continuous.comp continuous_snd
  have hEntry (i j : Fin n) : Continuous (fun p : Matrix (Fin n) (Fin n) ℂ × E => p.1 i j) := by
    exact (continuous_apply j).comp ((continuous_apply i).comp continuous_fst)
  have hC : Continuous q := by
    unfold q
    apply Complex.continuous_re.comp
    simp only [dotProduct, Matrix.mulVec]
    exact continuous_finsetSum _ fun i _ => ((continuous_star.comp (hCoord i))).mul
      (continuous_finsetSum _ fun j _ => (hEntry i j).mul (hCoord j))
  let O := {p | 0 < q p}
  have hO : IsOpen O := isOpen_lt continuous_const hC
  let S := sphere (0 : E) 1
  have hS : IsCompact S := isCompact_sphere _ _
  have hAO : ({A} : Set (Matrix (Fin n) (Fin n) ℂ)) ×ˢ S ⊆ O := by
    rintro ⟨B, z⟩ ⟨hB, hz⟩
    have he : B = A := hB
    subst B
    have hz1 : ‖z‖ = 1 := mem_sphere_zero_iff_norm.mp hz
    have hz0 : z.ofLp ≠ 0 := by
      intro h
      have : z = 0 := WithLp.ofLp_injective 2 h
      simp [this] at hz1
    have hp := hA.dotProduct_mulVec_pos hz0
    exact (RCLike.pos_iff.mp hp).1
  obtain ⟨U, V, hU, _, hAU, hSV, hUV⟩ := generalized_tube_lemma isCompact_singleton hS hO hAO
  refine ⟨U, hU, hAU (mem_singleton A), fun B hB hH => ?_⟩
  apply Matrix.PosDef.of_dotProduct_mulVec_pos hH
  intro z hz
  let v : E := WithLp.toLp 2 z
  have hv0 : v ≠ 0 := fun h => hz (WithLp.toLp_injective 2 h)
  let a := ‖v‖
  have ha : 0 < a := norm_pos_iff.mpr hv0
  let w := a⁻¹ • v
  have hw : w ∈ S := by
    apply mem_sphere_zero_iff_norm.mpr
    rw [show ‖w‖ = ‖a⁻¹‖ * a from norm_smul _ _, Real.norm_of_nonneg (inv_nonneg.mpr ha.le),
      inv_mul_cancel₀ ha.ne']
  have hpos : 0 < q (B, w) := hUV ⟨hB, hSV hw⟩
  have hwEq : w.ofLp = (a⁻¹ : ℂ) • z := by
    ext i
    change a⁻¹ • z i = (a⁻¹ : ℂ) • z i
    rw [Complex.real_smul, smul_eq_mul, Complex.ofReal_inv]
  rw [show q (B, w) = (star w.ofLp ⬝ᵥ (B *ᵥ w.ofLp)).re from rfl,
    hwEq, star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct] at hpos
  simp only [smul_eq_mul, ← Complex.ofReal_inv, Complex.star_def, Complex.conj_ofReal, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero] at hpos
  have hRe : 0 < (star z ⬝ᵥ (B *ᵥ z)).re :=
    pos_of_mul_pos_right (pos_of_mul_pos_right hpos (inv_nonneg.mpr ha.le)) (inv_nonneg.mpr ha.le)
  exact RCLike.pos_iff.mpr ⟨hRe, hH.im_star_dotProduct_mulVec_self z⟩

theorem complexHessian_isHermitian_of_C2 {n : ℕ} {u : E n → ℝ} {x : E n}
    (hu : ContDiffAt ℝ 2 u x) : (complexHessian u x).IsHermitian := by
  have hSym (a b : E n) : realHessian u x a b = realHessian u x b a :=
    (hu.isSymmSndFDerivAt (by simp)).eq a b
  have he (i j : Fin n) : complexHessian u x i j =
      ((1 / 4 : ℝ) : ℂ) *
        ((realHessian u x (realDirection i) (realDirection j) : ℝ) +
         (realHessian u x (imagDirection i) (imagDirection j) : ℝ) +
         Complex.I * ((realHessian u x (realDirection i) (imagDirection j) : ℝ) -
           (realHessian u x (imagDirection i) (realDirection j) : ℝ))) := by
    rw [complexHessian_real_entry_C2 hu]
    norm_num
  ext i j
  change star (complexHessian u x j i) = complexHessian u x i j
  rw [he j i, he i j, Complex.star_def]
  simp only [map_mul, map_add, map_sub, Complex.conj_ofReal, Complex.conj_I]
  rw [hSym (realDirection j) (realDirection i),
    hSym (imagDirection j) (imagDirection i),
    hSym (realDirection j) (imagDirection i),
    hSym (imagDirection j) (realDirection i)]
  ring

end KEBall
