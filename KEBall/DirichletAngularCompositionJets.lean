import KEBall.DirichletMultilinearFiniteLpJets
import KEBall.DirichletInteriorAngularWordEquation

/-! The actual ordered angular chain rule and compact-range composition
in the algebra of all angular finite Lp jets. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 1200000

open Filter MeasureTheory Metric Set
open scoped BigOperators ContDiff Topology

namespace KEBall

theorem dirichletAngularWord_comp_smooth_on_ball {n m : ℕ}
    {u : E n → ℝ} (hu : ContDiffOn ℝ ∞ u (unitBall n))
    {H : ℝ → ℝ} (hH : ContDiff ℝ ∞ H)
    (R : Fin m → DirichletUnitaryField n) {x : E n} (hx : x ∈ unitBall n) :
    dirichletAngularWord R (H ∘ u) x =
      ∑ c : OrderedFinpartition m, iteratedFDeriv ℝ c.length H (u x)
        (fun i => dirichletAngularWord (R ∘ c.emb i) u x) := by
  classical
  obtain ⟨v, hv, he⟩ := exists_dirichlet_local_smooth_extension isOpen_ball hu hx
  let X : ClosedBall n := ⟨x, ball_subset_closedBall hx⟩
  let M (t : Fin m → ℝ) := v (dirichletUnitaryOrbit R t x)
  let d (i : Fin m) : Fin m → ℝ := Pi.single i 1
  have hM : ContDiff ℝ ∞ M :=
    hv.comp ((contDiff_dirichletUnitaryOrbit_apply R).comp (contDiff_id.prodMk contDiff_const))
  have hAngV (j : ℕ) (Q : Fin j → DirichletUnitaryField n) :
      ContDiffOn ℝ 1 (dirichletAngularWord Q v) (closedUnitBall n) :=
    (contDiffOn_dirichletAngularWord hv.contDiffOn Q).of_le (by simp)
  have hBlock {j : ℕ} (e : Fin j → Fin m) (he' : StrictMono e) :
      iteratedFDeriv ℝ j M 0 (d ∘ e) = dirichletAngularWord (R ∘ e) v x := by
    exact eval_iteratedFDeriv_eq_angularWord_of_suborbit (ContinuousLinearMap.id ℝ ℝ)
      R e he' hAngV X (Eventually.of_forall (fun t => ⟨hM.contDiffAt, rfl⟩))
  have hTop : iteratedFDeriv ℝ m (H ∘ M) 0 d = dirichletAngularWord R (H ∘ v) x := by
    apply eval_iteratedFDeriv_eq_angularWord_of_orbit (ContinuousLinearMap.id ℝ ℝ) R
      (fun j Q => (contDiffOn_dirichletAngularWord (hH.comp hv).contDiffOn Q).of_le (by simp)) X
    exact Eventually.of_forall (fun t => ⟨(hH.comp hM).contDiffAt, rfl⟩)
  have hChain := congrArg (fun L => L d) (iteratedFDeriv_comp (x := (0 : Fin m → ℝ)) hH.contDiffAt hM.contDiffAt
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl m))
  simp only [ftaylorSeries, FormalMultilinearSeries.taylorComp, sum_apply,
    FormalMultilinearSeries.compAlongOrderedFinpartition_apply,
    OrderedFinpartition.applyOrderedFinpartition_apply] at hChain
  have hM0 : M 0 = v x := by simp only [M, dirichletUnitaryOrbit_zero_apply]
  have hHv : H ∘ v =ᶠ[𝓝 x] H ∘ u := he.mono (fun y hy => congrArg H hy)
  calc
    _ = dirichletAngularWord R (H ∘ v) x :=
      (dirichletAngularWord_eventuallyEq hx hHv R).self_of_nhds.symm
    _ = iteratedFDeriv ℝ m (H ∘ M) 0 d := hTop.symm
    _ = ∑ c : OrderedFinpartition m, iteratedFDeriv ℝ c.length H (v x)
        (fun i => dirichletAngularWord (R ∘ c.emb i) v x) := by
      rw [hChain, hM0]
      apply Finset.sum_congr rfl
      intro c _
      congr 1
      funext i
      exact hBlock (c.emb i) (c.emb_strictMono i)
    _ = _ := by
      rw [he.self_of_nhds]
      apply Finset.sum_congr rfl
      intro c _
      congr 1
      funext i
      exact (dirichletAngularWord_eventuallyEq hx he (R ∘ c.emb i)).self_of_nhds

theorem hasDirichletFiniteLpJets_all_angularWords_compact_comp {n k : ℕ}
    {U K : Set (E n)} {μ : Measure (E n)} [IsFiniteMeasure μ]
    (hU : IsOpen U) (hμ : ∀ᵐ x ∂μ, x ∈ U) (hK : IsCompact K)
    (hUK : U ⊆ K) (hUB : U ⊆ unitBall n)
    {u : E n → ℝ} (hu : ContDiffOn ℝ ∞ u (unitBall n)) (huK : ContinuousOn u K)
    (hAll : ∀ m, ∀ R : Fin m → DirichletUnitaryField n,
      HasDirichletFiniteLpJets U μ k (dirichletAngularWord R u))
    {H : ℝ → ℝ} (hH : ContDiff ℝ ∞ H)
    (m : ℕ) (R : Fin m → DirichletUnitaryField n) :
    HasDirichletFiniteLpJets U μ k (dirichletAngularWord R (H ∘ u)) := by
  classical
  let b := Module.Basis.singleton Unit ℝ
  have hImage : IsCompact (u '' K) := hK.image_of_continuousOn huK
  have hRange : MapsTo u U (u '' K) := fun x hx => ⟨x, hUK hx, rfl⟩
  have hA (j : Unit) : HasDirichletFiniteLpJets U μ k (fun x => b.repr (u x) j) := by
    simpa only [b, Module.Basis.singleton_repr, dirichletAngularWord] using hAll 0 (fun i => i.elim0)
  have hTerms (c : OrderedFinpartition m) :
      HasDirichletFiniteLpJets U μ k (fun x => iteratedFDeriv ℝ c.length H (u x)
        (fun i => dirichletAngularWord (R ∘ c.emb i) u x)) := by
    apply hasDirichletFiniteLpJets_iteratedFDeriv_comp_apply b hU hμ (hu.mono hUB)
      hA hImage hRange hH
    intro i j
    simpa only [b, Module.Basis.singleton_repr] using hAll (c.partSize i) (R ∘ c.emb i)
  have hSum := HasDirichletFiniteLpJets.finsetSum hU hμ Finset.univ (fun c _ => hTerms c)
  exact hSum.congr hU hμ (fun x hx =>
    (dirichletAngularWord_comp_smooth_on_ball hu hH R (hUB hx)).symm)

end KEBall
