import KEBall.DirichletPositiveMatrix
import KEBall.DirichletRankOneRecovery
import Mathlib.Topology.MetricSpace.Thickening

/-! Uniform positive-definiteness and determinant bounds for small Hessian perturbations. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8

open Filter InnerProductSpace Matrix Metric Set
open scoped ComplexOrder ContDiff MatrixOrder Matrix.Norms.Elementwise Topology

namespace KEBall

private theorem isClosed_setOf_posSemidef {n : ℕ} :
    IsClosed {A : Matrix (Fin n) (Fin n) ℂ | A.PosSemidef} := by
  let M := Matrix (Fin n) (Fin n) ℂ
  let s : Set M := {A | Aᴴ = A} ∩ ⋂ z : Fin n → ℂ, {A | 0 ≤ (star z ⬝ᵥ (A *ᵥ z)).re}
  have he : {A : M | A.PosSemidef} = s := by
    ext A
    constructor
    · intro h
      exact ⟨h.isHermitian.eq, mem_iInter.mpr fun z => h.re_dotProduct_nonneg z⟩
    · intro h
      have hH : A.IsHermitian := h.1
      exact Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hH fun z =>
        RCLike.nonneg_iff.mpr ⟨mem_iInter.mp h.2 z, hH.im_star_dotProduct_mulVec_self z⟩
  rw [he]
  apply IsClosed.inter
  · apply isClosed_eq _ continuous_id
    exact continuous_pi fun i => continuous_pi fun j =>
      continuous_star.comp ((continuous_apply i).comp (continuous_apply j))
  · apply isClosed_iInter
    intro z
    apply isClosed_le continuous_const
    apply Complex.continuous_re.comp
    simp only [dotProduct, Matrix.mulVec]
    have hEntry (i j : Fin n) : Continuous (fun A : M => A i j) :=
      (continuous_apply j).comp (continuous_apply i)
    exact continuous_finsetSum _ fun i _ => continuous_const.mul
      (continuous_finsetSum _ fun j _ => (hEntry i j).mul continuous_const)

/-- Compactness gives a uniform perturbation radius for all bounded
positive Hessians with determinant bounded away from zero. -/
theorem exists_posDef_det_re_of_norm_sub_lt {n : ℕ} {a D : ℝ} (ha : 0 < a) :
    ∃ δ > (0 : ℝ), ∀ A B : Matrix (Fin n) (Fin n) ℂ,
      A.PosSemidef → ‖A‖ ≤ D → a ≤ A.det.re → B.IsHermitian → ‖B - A‖ < δ →
        B.PosDef ∧ a / 2 < B.det.re := by
  let M := Matrix (Fin n) (Fin n) ℂ
  let S : Set M := closedBall 0 D ∩ ({A | A.PosSemidef} ∩ {A | a ≤ A.det.re})
  let O : Set M := (⋃₀ {U | IsOpen U ∧ ∀ B ∈ U, B.IsHermitian → B.PosDef}) ∩
    {B | a / 2 < B.det.re}
  have hDet : Continuous (fun A : M => A.det.re) :=
    Complex.continuous_re.comp continuous_id.matrix_det
  have hS : IsCompact S := (isCompact_closedBall _ _).inter_right
    (isClosed_setOf_posSemidef.inter (isClosed_le continuous_const hDet))
  have hO : IsOpen O :=
    (isOpen_sUnion fun _ h => h.1).inter (isOpen_lt continuous_const hDet)
  have hSub : S ⊆ O := by
    intro A hA
    have hd : a ≤ A.det.re := hA.2.2
    have hNZ : A.det ≠ 0 := by
      intro h
      rw [h, Complex.zero_re] at hd
      exact ha.not_ge hd
    have hp := (show A.PosSemidef from hA.2.1).posDef_iff_det_ne_zero.mpr hNZ
    obtain ⟨W, hW, hAW, hWP⟩ := exists_isOpen_hermitian_posDef_nhds hp
    exact ⟨mem_sUnion.mpr ⟨W, ⟨hW, hWP⟩, hAW⟩, (half_lt_self ha).trans_le hd⟩
  obtain ⟨δ, hδ, hU⟩ := hS.exists_thickening_subset_open hO hSub
  refine ⟨δ, hδ, fun A B hAp hAN hAd hBh hAB => ?_⟩
  have hA : A ∈ S := ⟨mem_closedBall_zero_iff.mpr hAN, hAp, hAd⟩
  have hB := hU (mem_thickening_iff.mpr ⟨A, hA, by rwa [dist_eq_norm]⟩)
  obtain ⟨W, hW, hBW⟩ := mem_sUnion.mp hB.1
  exact ⟨hW.2 B hBW hBh, hB.2⟩

/-- The real determinant is Lipschitz on each bounded matrix ball. -/
theorem exists_abs_det_re_sub_le_mul_norm_sub {n : ℕ} (D : ℝ) :
    ∃ C ≥ (0 : ℝ), ∀ A B : Matrix (Fin n) (Fin n) ℂ, ‖A‖ ≤ D → ‖B‖ ≤ D →
      |B.det.re - A.det.re| ≤ C * ‖B - A‖ := by
  let M := Matrix (Fin n) (Fin n) ℂ
  let g (A : M) := A.det.re
  let S : Set M := closedBall 0 D
  have hC : ContDiff ℝ ∞ g := by
    rw [← contDiffOn_univ]
    apply Complex.reCLM.contDiff.comp_contDiffOn
    exact contDiffOn_det_of_contDiffOn_entries (A := id) fun i j =>
      (contDiff_pi.mp (contDiff_pi.mp (contDiff_id (𝕜 := ℝ) (E := M)) i) j).contDiffOn
  obtain ⟨C, hC'⟩ := (isCompact_closedBall (0 : M) D).exists_bound_of_continuousOn
    (hC.continuous_fderiv (by simp)).continuousOn
  refine ⟨max C 0, le_max_right _ _, fun A B hA hB => ?_⟩
  rw [← Real.norm_eq_abs]
  exact Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun x _ => hC.differentiable (by simp) x) (fun x hx => (hC' x hx).trans (le_max_left _ _))
    (convex_closedBall (0 : M) D) (mem_closedBall_zero_iff.mpr hA) (mem_closedBall_zero_iff.mpr hB)

end KEBall
