import KEBall.DirichletBoundaryHessianUniqueness
import Mathlib.Topology.Compactness.Compact

/-!
# A boundary Hessian limit from compactness and tangent traces

Every cluster form is symmetric and positive, with the prescribed positive
determinant.  Its tangent entries have unique limits.  The radial rank-one
uniqueness lemma therefore makes the whole bounded Hessian converge.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Filter InnerProductSpace Metric Set
open scoped ComplexOrder ContDiff Matrix Topology

namespace KEBall

theorem continuous_dirichlet_complexHessianOfRealBilinear (n : ℕ) :
    Continuous (@complexHessianOfRealBilinear n) := by
  apply continuous_matrix
  intro i j
  unfold complexHessianOfRealBilinear
  fun_prop

theorem dirichlet_posSemidef_of_tendsto_matrix {n : ℕ} {ι : Type*}
    {l : Filter ι} [NeBot l] {A : ι → Matrix (Fin n) (Fin n) ℂ}
    {C : Matrix (Fin n) (Fin n) ℂ}
    (hT : Tendsto A l (𝓝 C)) (hP : ∀ᶠ j in l, (A j).PosSemidef) : C.PosSemidef := by
  have hHerm : C.IsHermitian := by
    have hCont : Continuous (fun D : Matrix (Fin n) (Fin n) ℂ => Dᴴ) :=
      continuous_id.matrix_conjTranspose
    apply tendsto_nhds_unique ((hCont.tendsto C).comp hT)
    apply hT.congr'
    filter_upwards [hP] with j hj
    exact hj.isHermitian.eq.symm
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hHerm
  intro v
  let F (D : Matrix (Fin n) (Fin n) ℂ) := star v ⬝ᵥ (D *ᵥ v)
  have hCont : Continuous F :=
    continuous_const.dotProduct (continuous_id.matrix_mulVec continuous_const)
  apply isClosed_Ici.mem_of_tendsto ((hCont.tendsto C).comp hT)
  filter_upwards [hP] with j hj
  exact hj.dotProduct_mulVec_nonneg v

theorem dirichlet_boundary_hessian_cluster_data {n : ℕ}
    {B : E n → E n →L[ℝ] E n →L[ℝ] ℝ} {p : E n}
    {f : E n → ℝ} {f₀ : ℝ} (hf₀ : 0 < f₀)
    (hF : Tendsto f (𝓝[unitBall n] p) (𝓝 f₀))
    (hSym : ∀ x ∈ unitBall n, ∀ v w, B x v w = B x w v)
    (hPos : ∀ x ∈ unitBall n, (complexHessianOfRealBilinear (B x)).PosDef)
    (hDet : ∀ x ∈ unitBall n, (complexHessianOfRealBilinear (B x)).det.re = f x)
    {C : E n →L[ℝ] E n →L[ℝ] ℝ}
    (hCluster : MapClusterPt C (𝓝[unitBall n] p) B) :
    (∀ v w, C v w = C w v) ∧ (complexHessianOfRealBilinear C).PosDef ∧
      (complexHessianOfRealBilinear C).det.re = f₀ ∧
      ∀ (T : E n →L[ℝ] E n) (Q : E n →L[ℝ] ℝ),
        Tendsto (fun x => B x (T x)) (𝓝[unitBall n] p) (𝓝 Q) → C (T p) = Q := by
  let l := comap B (𝓝 C) ⊓ 𝓝[unitBall n] p
  letI : NeBot l := neBot_inf_comap_iff_map'.mpr hCluster
  have hB : Tendsto B l (𝓝 C) := tendsto_comap.mono_left inf_le_left
  have hX : Tendsto (fun x : E n => x) l (𝓝 p) :=
    nhdsWithin_le_nhds.trans' inf_le_right
  have hMem : ∀ᶠ x in l, x ∈ unitBall n := by
    have hMem₀ : ∀ᶠ x in 𝓝[unitBall n] p, x ∈ unitBall n := self_mem_nhdsWithin
    exact hMem₀.filter_mono inf_le_right
  have hCMatrix := (continuous_dirichlet_complexHessianOfRealBilinear n).tendsto C |>.comp hB
  have hSemi : (complexHessianOfRealBilinear C).PosSemidef :=
    dirichlet_posSemidef_of_tendsto_matrix hCMatrix (by
      filter_upwards [hMem] with x hx
      exact (hPos x hx).posSemidef)
  have hCDet : (complexHessianOfRealBilinear C).det.re = f₀ := by
    apply tendsto_nhds_unique
      ((Complex.continuous_re.comp continuous_id.matrix_det).tendsto _ |>.comp hCMatrix)
    apply (hF.mono_left inf_le_right).congr'
    filter_upwards [hMem] with x hx
    exact (hDet x hx).symm
  have hCPos : (complexHessianOfRealBilinear C).PosDef :=
    hSemi.posDef_iff_det_ne_zero.mpr (by
      intro he
      have hz := hCDet
      rw [he, Complex.zero_re] at hz
      exact hf₀.ne' hz.symm)
  refine ⟨?_, hCPos, hCDet, ?_⟩
  · intro v w
    have hEval (a b : E n) : Continuous
        (fun D : E n →L[ℝ] E n →L[ℝ] ℝ => D a b) := by fun_prop
    have h₁ := (hEval v w).tendsto C |>.comp hB
    have h₂ := (hEval w v).tendsto C |>.comp hB
    apply tendsto_nhds_unique h₁
    apply h₂.congr'
    filter_upwards [hMem] with x hx
    exact (hSym x hx v w).symm
  · intro T Q hQ
    have hEval : Continuous
        (fun z : (E n →L[ℝ] E n →L[ℝ] ℝ) × E n => z.1 z.2) :=
      continuous_fst.clm_apply continuous_snd
    exact tendsto_nhds_unique ((hEval.tendsto (C, T p)).comp
      (hB.prodMk_nhds (T.continuous.tendsto p |>.comp hX))) (hQ.mono_left inf_le_right)

theorem exists_dirichlet_boundary_hessian_limit {n : ℕ}
    {B : E n → E n →L[ℝ] E n →L[ℝ] ℝ} {p : E n} (hp : p ∈ unitSphere n)
    {L : ℝ} (hBound : ∀ x ∈ unitBall n, ‖B x‖ ≤ L)
    {f : E n → ℝ} {f₀ : ℝ} (hf₀ : 0 < f₀)
    (hF : Tendsto f (𝓝[unitBall n] p) (𝓝 f₀))
    (hSym : ∀ x ∈ unitBall n, ∀ v w, B x v w = B x w v)
    (hPos : ∀ x ∈ unitBall n, (complexHessianOfRealBilinear (B x)).PosDef)
    (hDet : ∀ x ∈ unitBall n, (complexHessianOfRealBilinear (B x)).det.re = f x)
    (hTan : ∀ v : E n, ‖v‖ = 1 → inner ℝ p v = 0 →
      ∃ (T : E n →L[ℝ] E n) (Q : E n →L[ℝ] ℝ), T p = v ∧
        Tendsto (fun x => B x (T x)) (𝓝[unitBall n] p) (𝓝 Q)) :
    ∃ C : E n →L[ℝ] E n →L[ℝ] ℝ,
      Tendsto B (𝓝[unitBall n] p) (𝓝 C) ∧
      (∀ v w, C v w = C w v) ∧ (complexHessianOfRealBilinear C).PosDef ∧
        (complexHessianOfRealBilinear C).det.re = f₀ := by
  have hpCl : p ∈ closure (unitBall n) := by
    rw [unitBall, closure_ball (0 : E n) (by norm_num : (1 : ℝ) ≠ 0)]
    exact sphere_subset_closedBall hp
  letI : NeBot (𝓝[unitBall n] p) := mem_closure_iff_nhdsWithin_neBot.mp hpCl
  let K := closedBall (0 : E n →L[ℝ] E n →L[ℝ] ℝ) L
  have hK : IsCompact K := isCompact_closedBall _ _
  have hMem : ∀ᶠ x in 𝓝[unitBall n] p, B x ∈ K := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact mem_closedBall_zero_iff.mpr (hBound x hx)
  obtain ⟨C, hCK, hCC⟩ := hK.exists_mapClusterPt (u := B) (f := 𝓝[unitBall n] p)
    (le_principal_iff.mpr hMem)
  have hC := dirichlet_boundary_hessian_cluster_data hf₀ hF hSym hPos hDet hCC
  refine ⟨C, ?_, hC.1, hC.2.1, hC.2.2.1⟩
  apply hK.tendsto_nhds_of_unique_mapClusterPt hMem
  intro D hDK hDC
  have hD := dirichlet_boundary_hessian_cluster_data hf₀ hF hSym hPos hDet hDC
  apply dirichlet_symmetric_bilinear_eq_of_tangent_det hp hD.1 hC.1
    (dirichlet_bilinear_tangent_eq_of_unit_tangent_eq ?_) hC.2.1
    (hD.2.2.1.trans hC.2.2.1.symm)
  intro v hv hOrth
  obtain ⟨T, Q, hTp, hQ⟩ := hTan v hv hOrth
  rw [← hTp]
  exact (hD.2.2.2 T Q hQ).trans (hC.2.2.2 T Q hQ).symm

end KEBall
