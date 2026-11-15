import KEBall.DirichletFiniteLpJetComposition

/-! Finite-basis evaluation of actual multilinear differentials in all finite Lp. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 800000
open Filter InnerProductSpace MeasureTheory Metric Set
open scoped BigOperators ContDiff ENNReal Topology
namespace KEBall

theorem hasDirichletFiniteLpJets_multilinear_apply {n k m : ℕ} {ι F : Type*}
    [Fintype ι] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (b : Module.Basis ι ℝ F) {U : Set (E n)} {μ : Measure (E n)} [IsFiniteMeasure μ]
    (hU : IsOpen U) (hμ : ∀ᵐ x ∂μ, x ∈ U)
    {M : E n → ContinuousMultilinearMap ℝ (fun _ : Fin m => F) ℝ}
    (hM : ∀ r : Fin m → ι, HasDirichletFiniteLpJets U μ k (fun x => M x (fun i => b (r i))))
    {v : Fin m → E n → F}
    (hv : ∀ i j, HasDirichletFiniteLpJets U μ k (fun x => b.repr (v i x) j)) :
    HasDirichletFiniteLpJets U μ k (fun x => M x (fun i => v i x)) := by
  classical
  have hSum := HasDirichletFiniteLpJets.finsetSum hU hμ (Finset.univ : Finset (Fin m → ι))
    (fun r _ => (HasDirichletFiniteLpJets.finsetProd hU hμ Finset.univ
      (fun i _ => hv i (r i))).mul hU hμ (hM r))
  refine hSum.congr hU hμ ?_
  intro x _
  have he : (fun i => v i x)=(fun i => ∑ j, b.repr (v i x) j • b j) := by
    funext i
    exact (b.sum_repr (v i x)).symm
  change (∑ r : Fin m → ι, (∏ i, b.repr (v i x) (r i))*M x (fun i => b (r i))) =
    M x (fun i => v i x)
  rw [he,(M x).map_sum]
  simp only [ContinuousMultilinearMap.map_smul_univ,smul_eq_mul]

theorem hasDirichletFiniteLpJets_iteratedFDeriv_comp_apply {n k m : ℕ} {ι F : Type*}
    [Fintype ι] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (b : Module.Basis ι ℝ F) {U : Set (E n)} {μ : Measure (E n)} [IsFiniteMeasure μ]
    (hU : IsOpen U) (hμ : ∀ᵐ x ∂μ, x ∈ U)
    {A : E n → F} (hAS : ContDiffOn ℝ ∞ A U)
    (hA : ∀ i, HasDirichletFiniteLpJets U μ k (fun x => b.repr (A x) i))
    {K : Set F} (hK : IsCompact K) (hRange : MapsTo A U K)
    {H : F → ℝ} (hH : ContDiff ℝ ∞ H) {v : Fin m → E n → F}
    (hv : ∀ i j, HasDirichletFiniteLpJets U μ k (fun x => b.repr (v i x) j)) :
    HasDirichletFiniteLpJets U μ k
      (fun x => iteratedFDeriv ℝ m H (A x) (fun i => v i x)) := by
  apply hasDirichletFiniteLpJets_multilinear_apply b hU hμ _ hv
  intro r
  apply hasDirichletFiniteLpJets_compact_comp b hU hμ hAS hA hK hRange
    (H := fun y => iteratedFDeriv ℝ m H y (fun i => b (r i)))
  have hOrder (j : ℕ) : (∞ : ℕ∞ω)+j ≤ (∞ : ℕ∞ω) := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [Nat.cast_succ,← add_assoc]
      exact (add_le_add_right ih (1 : ℕ∞ω)).trans
        (show (∞ : ℕ∞ω)+1 ≤ (∞ : ℕ∞ω) by rw [ENat.coe_top_add_one])
  exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin m => F) ℝ (fun i => b (r i))).contDiff.comp
    (hH.iteratedFDeriv_right (m := ∞) (hOrder m))

end KEBall
