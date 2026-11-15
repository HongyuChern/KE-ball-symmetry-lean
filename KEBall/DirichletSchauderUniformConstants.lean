import KEBall.DirichletSchauderAbsorptionScale

/-!
# Schauder constants uniform over an elliptic coefficient family

The square root and its inverse are bounded by the actual quadratic-form
ellipticity constants.  Monotonicity of the imported heat-potential
constant then gives a bound independent of a difference-quotient step.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Filter InnerProductSpace Matrix Metric Set
open DifferentialGeometry.Analysis.Schauder
open DifferentialGeometry.Analysis.Parabolic.Euclidean
open scoped NNReal Topology

namespace KEBall

theorem dirichletSchauderMatrix_toEuclidean_quadratic {n : ℕ}
    (A : E n →L[ℝ] E n) (v : E n) :
    inner ℝ v (Matrix.toEuclideanCLM (n := Fin (2 * n)) (𝕜 := ℝ) (dirichletSchauderMatrix A) v) =
      inner ℝ (A v) v := by
  rw [Matrix.inner_toEuclideanCLM]
  simpa only [star_trivial, WithLp.toLp_ofLp] using
    dirichletSchauderMatrix_quadratic A v.ofLp

theorem norm_dirichletSchauderSqrt_le {n : ℕ} {A : E n →L[ℝ] E n}
    (hA : (dirichletSchauderMatrix A).PosDef) {M : ℝ} (hM : 0 ≤ M)
    (hNorm : ‖A‖ ≤ M) :
    ‖(spdSqrtEquiv (dirichletSchauderMatrix A) hA : E n →L[ℝ] E n)‖ ≤ Real.sqrt M := by
  apply spdSqrt_norm_le _ hA hM
  intro v
  rw [dirichletSchauderMatrix_toEuclidean_quadratic]
  calc
    inner ℝ (A v) v ≤ ‖A v‖ * ‖v‖ := real_inner_le_norm _ _
    _ ≤ (M * ‖v‖) * ‖v‖ :=
      mul_le_mul_of_nonneg_right
        ((A.le_opNorm v).trans (mul_le_mul_of_nonneg_right hNorm (norm_nonneg _)))
        (norm_nonneg _)
    _ = M * ‖v‖ ^ 2 := by ring

theorem norm_dirichletSchauderSqrt_symm_le {n : ℕ} {A : E n →L[ℝ] E n}
    (hA : (dirichletSchauderMatrix A).PosDef) {l : ℝ} (hl : 0 < l)
    (hEll : ∀ v : E n, l * ‖v‖ ^ 2 ≤ inner ℝ (A v) v) :
    ‖((spdSqrtEquiv (dirichletSchauderMatrix A) hA).symm : E n →L[ℝ] E n)‖ ≤
      (Real.sqrt l)⁻¹ := by
  apply spdSqrt_inv_le _ hA hl
  intro v
  rw [dirichletSchauderMatrix_toEuclidean_quadratic]
  exact hEll v

theorem dirichlet_heatDuhamelConstSchauderConst_mono {n : ℕ}
    {α K K' B B' : ℝ≥0} (hα : α < 1) (hK : K ≤ K') (hB : B ≤ B') :
    heatDuhamelConstSchauderConst (V := E n) α K B 1 ≤
      heatDuhamelConstSchauderConst (V := E n) α K' B' 1 := by
  obtain ⟨k, rfl⟩ := exists_add_of_le hK
  obtain ⟨b, rfl⟩ := exists_add_of_le hB
  rw [heatDuhamelConstSchauderConst_add hα K k B b (by norm_num)]
  exact le_add_of_nonneg_right (bot_le : (0 : ℝ≥0) ≤ _)

noncomputable def dirichletSchauderChangeConst (α R C : ℝ≥0) : ℝ≥0 :=
  C + R * C + R ^ 2 * C + R ^ 2 * (C * R ^ (α : ℝ))

theorem dirichletSchauderChangeConst_mono {α R R' C C' : ℝ≥0}
    (hR : R ≤ R') (hC : C ≤ C') :
    dirichletSchauderChangeConst α R C ≤ dirichletSchauderChangeConst α R' C' := by
  unfold dirichletSchauderChangeConst
  gcongr

noncomputable def dirichletSchauderDefectMajorant (n : ℕ)
    (α L R K B : ℝ≥0) : ℝ≥0 :=
  dirichletSchauderChangeConst α (max 1 R)
    (heatDuhamelConstSchauderConst (V := E n) α (K * L ^ (α : ℝ)) B 1)

theorem dirichletSchauderDefectConst_le_majorant {n : ℕ}
    (A : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) (hA : A.PosDef)
    {α L R : ℝ≥0} (hα : α < 1)
    (hL : ‖(spdSqrtEquiv A hA : E n →L[ℝ] E n)‖₊ ≤ L)
    (hR : ‖((spdSqrtEquiv A hA).symm : E n →L[ℝ] E n)‖₊ ≤ R)
    (K B : ℝ≥0) :
    spdLaplacianSchauderDefectConst A hA α K B ≤
      dirichletSchauderDefectMajorant n α L R K B := by
  have hK : K * ‖(spdSqrtEquiv A hA : E n →L[ℝ] E n)‖₊ ^ (α : ℝ) ≤
      K * L ^ (α : ℝ) := by gcongr
  exact dirichletSchauderChangeConst_mono (max_le_max_left 1 hR)
    (dirichlet_heatDuhamelConstSchauderConst_mono hα hK le_rfl)

theorem dirichletSchauderDefectMajorant_smul (n : ℕ) (α L R c K B : ℝ≥0) :
    dirichletSchauderDefectMajorant n α L R (c * K) (c * B) =
      c * dirichletSchauderDefectMajorant n α L R K B := by
  unfold dirichletSchauderDefectMajorant
  rw [show (c * K) * L ^ (α : ℝ) = c * (K * L ^ (α : ℝ)) by ring,
    heatDuhamelConstSchauderConst_nnreal_mul]
  unfold dirichletSchauderChangeConst
  ring

theorem exists_dirichlet_uniform_schauder_absorption_scale (n : ℕ)
    (α L R K B radius : ℝ≥0) (hα : 0 < α) (hRadius : 0 < radius) :
    ∃ r : ℝ≥0, 0 < r ∧ r < radius ∧
      dirichletSchauderDefectMajorant n α L R
        (r ^ (α : ℝ) * K) (r ^ (α : ℝ) * B) < 1 / 2 := by
  let D := dirichletSchauderDefectMajorant n α L R K B
  have hlim : Tendsto (fun r : ℝ≥0 => r ^ (α : ℝ) * D) (𝓝[>] 0) (𝓝 0) := by
    simpa only [NNReal.zero_rpow (show (α : ℝ) ≠ 0 from ne_of_gt hα), zero_mul] using
      (((NNReal.continuous_rpow_const α.coe_nonneg).mul_const D).continuousAt
        (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
  have hlt : ∀ᶠ r : ℝ≥0 in 𝓝[>] 0, r < radius :=
    (tendsto_id.mono_left nhdsWithin_le_nhds).eventually_lt_const hRadius
  obtain ⟨r, hr, hsmall, hrR⟩ :=
    (eventually_mem_nhdsWithin.and
      ((hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ≥0) < 1 / 2))).and hlt)).exists
  refine ⟨r, hr, hrR, ?_⟩
  rw [dirichletSchauderDefectMajorant_smul]
  exact hsmall

end KEBall
