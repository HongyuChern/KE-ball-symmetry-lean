import KEBall.DirichletFiniteLpJetOperations

/-! Smooth composition of genuine finite Lp jets on a compact range. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 700000
open Filter InnerProductSpace MeasureTheory Metric Set
open scoped BigOperators ContDiff ENNReal Topology
namespace KEBall

theorem hasDirichletFiniteLpJets_compact_comp {n k : ℕ} {ι F : Type*}
    [Fintype ι] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (b : Module.Basis ι ℝ F) {U : Set (E n)} {μ : Measure (E n)} [IsFiniteMeasure μ]
    (hU : IsOpen U) (hμ : ∀ᵐ x ∂μ, x ∈ U)
    {f : E n → F} (hf : ContDiffOn ℝ ∞ f U)
    (hJet : ∀ i, HasDirichletFiniteLpJets U μ k (fun x => b.repr (f x) i))
    {K : Set F} (hK : IsCompact K) (hRange : MapsTo f U K)
    {H : F → ℝ} (hH : ContDiff ℝ ∞ H) :
    HasDirichletFiniteLpJets U μ k (fun x => H (f x)) := by
  classical
  have hBase {G : F → ℝ} (hG : ContDiff ℝ ∞ G) :
      HasDirichletFiniteLpJets U μ 0 (fun x => G (f x)) := by
    have hC := hG.comp_contDiffOn hf
    obtain ⟨C,hCbound⟩ := hK.exists_bound_of_continuousOn hG.continuous.continuousOn
    have hMeas := hC.continuousOn.aestronglyMeasurable (μ := μ) hU.measurableSet
    rw [Measure.restrict_eq_self_of_ae_mem hμ] at hMeas
    exact ⟨hC,fun p _ => (memLp_const C).mono' hMeas (hμ.mono (fun x hx => hCbound (f x) (hRange hx)))⟩
  induction k generalizing H with
  | zero => exact hBase hH
  | succ k ih =>
    refine ⟨hBase hH,fun d => ?_⟩
    have hCoef (i : ι) : HasDirichletFiniteLpJets U μ k (fun x => fderiv ℝ H (f x) (b i)) :=
      ih (fun j => (hJet j).of_le (Nat.le_succ k))
        ((hH.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const)
    have hSum := HasDirichletFiniteLpJets.finsetSum hU hμ Finset.univ
      (fun i _ => (hCoef i).mul hU hμ ((hJet i).2 d))
    refine hSum.congr hU hμ ?_
    intro x hx
    have hdf := (hf.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
    have hcoord (i : ι) : fderiv ℝ (fun y => b.repr (f y) i) x d =
        b.repr (fderiv ℝ f x d) i := by
      have h := ((b.coord i).toContinuousLinearMap).hasFDerivAt.comp x hdf.hasFDerivAt
      change HasFDerivAt (fun y => b.repr (f y) i) _ x at h
      rw [h.fderiv]
      rfl
    change (∑ i, fderiv ℝ H (f x) (b i) * fderiv ℝ (fun y => b.repr (f y) i) x d) =
      fderiv ℝ (H ∘ f) x d
    simp_rw [hcoord]
    rw [fderiv_comp x (hH.differentiable (by simp) (f x)) hdf,ContinuousLinearMap.comp_apply]
    calc
      _ = fderiv ℝ H (f x) (∑ i, b.repr (fderiv ℝ f x d) i • b i) := by
        simp only [map_sum,map_smul,smul_eq_mul]
        exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
      _ = _ := by rw [b.sum_repr]

end KEBall
