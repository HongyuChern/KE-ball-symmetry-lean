import KEBall.DirichletAveragedCofactorBounds

/-!
# Uniform ellipticity of the full family of averaged cofactors

Compactness is applied before choosing the two Hessian points.  Therefore
the resulting ellipticity and norm constants are uniform over every
translation quotient whose two arguments remain in the compact set.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open InnerProductSpace Matrix Metric Set
open scoped ComplexOrder Matrix.Norms.Elementwise NNReal

namespace KEBall

theorem lipschitzOnWith_dirichletMeanCofactor_pair {n : ℕ} {R : ℝ} {K : ℝ≥0}
    (hLip : LipschitzOnWith K (@dirichletCofactorOfMatrix n) (closedBall 0 R)) :
    LipschitzOnWith K
      (fun P : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ =>
        dirichletMeanCofactor P.1 P.2) (closedBall 0 R) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro P hP Q hQ
  have hPn := mem_closedBall_zero_iff.mp hP
  have hQn := mem_closedBall_zero_iff.mp hQ
  rw [dist_eq_norm, dist_eq_norm]
  exact norm_dirichletMeanCofactor_sub_le_of_lipschitz hLip
    ((norm_fst_le P).trans hPn) ((norm_snd_le P).trans hPn)
    ((norm_fst_le Q).trans hQn) ((norm_snd_le Q).trans hQn)
    (norm_fst_le (P - Q)) (norm_snd_le (P - Q))

theorem continuous_dirichletMeanCofactor_pair {n : ℕ} :
    Continuous (fun P : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ =>
      dirichletMeanCofactor P.1 P.2) := by
  apply continuous_iff_continuousAt.mpr
  intro P
  obtain ⟨K, hK⟩ := exists_dirichlet_cofactor_lipschitz_on_matrix_ball (n := n) (‖P‖ + 1)
  apply (lipschitzOnWith_dirichletMeanCofactor_pair hK).continuousOn.continuousAt
  exact Filter.mem_of_superset (isOpen_ball.mem_nhds
    (mem_ball_zero_iff.mpr (by linarith : ‖P‖ < ‖P‖ + 1))) ball_subset_closedBall

theorem exists_uniform_ellipticity_of_continuous_compact_operator_family {n : ℕ}
    {X : Type*} [TopologicalSpace X] {S : Set X} (hS : IsCompact S)
    {A : X → E n →L[ℝ] E n} (hA : ContinuousOn A S)
    (hPos : ∀ x ∈ S, ∀ v : E n, v ≠ 0 → 0 < inner ℝ (A x v) v) :
    ∃ l M : ℝ, 0 < l ∧ 0 < M ∧
      (∀ x ∈ S, ‖A x‖ ≤ M) ∧
      ∀ x ∈ S, ∀ v : E n, l * ‖v‖ ^ 2 ≤ inner ℝ (A x v) v := by
  let Q (z : X × E n) := inner ℝ (A z.1 z.2) z.2
  have hQ : ContinuousOn Q (S ×ˢ unitSphere n) :=
    ((hA.comp continuousOn_fst (fun _ hz => hz.1)).clm_apply continuousOn_snd).inner
      continuousOn_snd
  obtain ⟨l, hl, hMin⟩ := (hS.prod (isCompact_sphere (0 : E n) 1)).exists_forall_le' hQ (by
    intro z hz
    apply hPos z.1 hz.1 z.2
    intro he
    have hn := mem_sphere_zero_iff_norm.mp hz.2
    rw [he, norm_zero] at hn
    norm_num at hn)
  obtain ⟨B, hB⟩ := hS.exists_bound_of_continuousOn hA
  refine ⟨l, max B 1, hl, lt_of_lt_of_le zero_lt_one (le_max_right _ _),
    fun x hx => (hB x hx).trans (le_max_left _ _), ?_⟩
  intro x hx v
  by_cases hv : v = 0
  · simp [hv]
  have hvNorm : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  let z : E n := ‖v‖⁻¹ • v
  have hz : z ∈ unitSphere n := by
    apply mem_sphere_zero_iff_norm.mpr
    simp only [z, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg v)),
      inv_mul_cancel₀ hvNorm]
  calc
    l * ‖v‖ ^ 2 = ‖v‖ ^ 2 * l := mul_comm _ _
    _ ≤ ‖v‖ ^ 2 * Q (x, z) :=
      mul_le_mul_of_nonneg_left (hMin (x, z) ⟨hx, hz⟩) (sq_nonneg _)
    _ = inner ℝ (A x v) v := by
      simp only [Q, z, map_smul, real_inner_smul_left, real_inner_smul_right]
      field_simp

theorem exists_uniform_dirichletMeanCofactor_bounds_on_compact {n : ℕ}
    {X : Type*} [TopologicalSpace X] {S : Set X} (hS : IsCompact S)
    {H : X → Matrix (Fin n) (Fin n) ℂ} (hH : ContinuousOn H S)
    (hPos : ∀ x ∈ S, (H x).PosDef) :
    ∃ l M : ℝ, 0 < l ∧ 0 < M ∧
      (∀ x ∈ S, ∀ y ∈ S, ‖dirichletMeanCofactor (H x) (H y)‖ ≤ M) ∧
      ∀ x ∈ S, ∀ y ∈ S, ∀ v : E n,
        l * ‖v‖ ^ 2 ≤ inner ℝ (dirichletMeanCofactor (H x) (H y) v) v := by
  have hPair : ContinuousOn (fun p : X × X => (H p.1, H p.2)) (S ×ˢ S) :=
    (hH.comp continuousOn_fst (fun _ hp => hp.1)).prodMk
      (hH.comp continuousOn_snd (fun _ hp => hp.2))
  have hCont : ContinuousOn (fun p : X × X => dirichletMeanCofactor (H p.1) (H p.2)) (S ×ˢ S) := by
    simpa only [Function.comp_def] using!
      (continuous_dirichletMeanCofactor_pair (n := n)).comp_continuousOn hPair
  obtain ⟨l, M, hl, hM, hNorm, hEll⟩ :=
    exists_uniform_ellipticity_of_continuous_compact_operator_family (hS.prod hS) hCont
      (fun p hp v hv => dirichletMeanCofactor_pos (hPos p.1 hp.1) (hPos p.2 hp.2) hv)
  exact ⟨l, M, hl, hM, fun x hx y hy => hNorm (x, y) ⟨hx, hy⟩,
    fun x hx y hy v => hEll (x, y) ⟨hx, hy⟩ v⟩

end KEBall
