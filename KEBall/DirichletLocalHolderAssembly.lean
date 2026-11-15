import KEBall.DirichletLocalHolder

/-! Finite-dimensional assembly and elementary operations on local Holder jets. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Filter Metric Set
open DifferentialGeometry.Analysis DifferentialGeometry.Analysis.Schauder
open scoped ContDiff NNReal Topology

namespace KEBall

theorem exists_dirichlet_holder_iterated_clm_of_basis {n k : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {S : Set (E n)} (hS : IsOpen S) {f : E n → E n →L[ℝ] F}
    (hf : ContDiffOn ℝ k f S) {α : ℝ≥0}
    (hH : ∀ i : Fin (2 * n), ∃ K : ℝ≥0,
      HolderOnWith K α (iteratedFDeriv ℝ k
        (fun x => f x (EuclideanSpace.basisFun (Fin (2 * n)) ℝ i))) S) :
    ∃ K : ℝ≥0, HolderOnWith K α (iteratedFDeriv ℝ k f) S := by
  let b := (EuclideanSpace.basisFun (Fin (2 * n)) ℝ).toBasis
  apply exists_holderOnWith_continuousMultilinearMap_of_basis b
  intro a
  apply dirichlet_exists_holderOnWith_clm_of_basis
  intro i
  obtain ⟨K, hK⟩ := hH i
  obtain ⟨C, hC⟩ := exists_holderOnWith_clm_comp hK
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => E n) F (fun j => b (a j)))
  have he (x : E n) (hx : x ∈ S) :
      iteratedFDeriv ℝ k (fun y => f y (b i)) x (fun j => b (a j)) =
        iteratedFDeriv ℝ k f x (fun j => b (a j)) (b i) := by
    have ht := (ContinuousLinearMap.apply ℝ F (b i)).iteratedFDeriv_comp_left
      (hf.contDiffAt (hS.mem_nhds hx)) le_rfl
    exact congrArg (fun T => T (fun j => b (a j))) ht
  refine ⟨C, ?_⟩
  intro x hx y hy
  have hh := hC x hx y hy
  change edist (iteratedFDeriv ℝ k (fun z => f z (b i)) x (fun j => b (a j)))
    (iteratedFDeriv ℝ k (fun z => f z (b i)) y (fun j => b (a j))) ≤ _ at hh
  rwa [he x hx, he y hy] at hh

theorem hasDirichletHolderAt_clm_of_basis {n k : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E n → E n →L[ℝ] F} {p : E n} {α : ℝ≥0}
    (hf : ∀ i : Fin (2 * n), HasDirichletHolderAt k α
      (fun x => f x (EuclideanSpace.basisFun (Fin (2 * n)) ℝ i)) p) :
    HasDirichletHolderAt k α f p := by
  classical
  choose R hR hC K hH using hf
  have hN : (⋂ i : Fin (2 * n), ball p (R i)) ∈ 𝓝 p :=
    Filter.iInter_mem.mpr fun i => isOpen_ball.mem_nhds (mem_ball_self (hR i))
  obtain ⟨δ, hδ, hSub⟩ := Metric.mem_nhds_iff.mp hN
  have hSub' (i : Fin (2 * n)) : ball p δ ⊆ ball p (R i) :=
    fun x hx => mem_iInter.mp (hSub hx) i
  have hfC : ContDiffOn ℝ k f (ball p δ) :=
    dirichlet_contDiffOn_clm_of_basis fun i => (hC i).mono (hSub' i)
  obtain ⟨C, hCH⟩ := exists_dirichlet_holder_iterated_clm_of_basis isOpen_ball hfC
    (fun i => ⟨K i, (hH i).mono (hSub' i)⟩)
  exact ⟨δ, hδ, hfC, C, hCH⟩

namespace HasDirichletHolderAt

variable {n k : ℕ} {F G V : Type*}
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {α : ℝ≥0} {f : E n → F} {p : E n}

theorem eventually (hf : HasDirichletHolderAt k α f p) :
    ∀ᶠ q in 𝓝 p, HasDirichletHolderAt k α f q := by
  obtain ⟨R, hR, hC, K, hH⟩ := hf
  filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hR)] with q hq
  obtain ⟨r, hr, hSub⟩ := Metric.mem_nhds_iff.mp (isOpen_ball.mem_nhds hq)
  exact ⟨r, hr, hC.mono hSub, K, hH.mono hSub⟩

theorem bilinear (hf : HasDirichletHolderAt k α f p) {g : E n → G}
    (hg : HasDirichletHolderAt k α g p) (hα : 0 < α) (hα1 : α ≤ 1)
    (L : F →L[ℝ] G →L[ℝ] V) : HasDirichletHolderAt k α (fun x => L (f x) (g x)) p :=
  (hf.prodMk hg).comp_smooth hα hα1 ((L.contDiff.comp contDiff_fst).clm_apply contDiff_snd)

theorem of_directions {R : ℝ} (hR : 0 < R) (hC1 : ContDiffOn ℝ 1 f (ball p R))
    (hf : ∀ i : Fin (2 * n), HasDirichletHolderAt k α
      (fun x => fderiv ℝ f x (EuclideanSpace.basisFun (Fin (2 * n)) ℝ i)) p) :
    HasDirichletHolderAt (k + 1) α f p :=
  of_fderiv hR hC1 (hasDirichletHolderAt_clm_of_basis hf)

theorem congr_of_eventuallyEq (hf : HasDirichletHolderAt k α f p) {g : E n → F}
    (he : g =ᶠ[𝓝 p] f) : HasDirichletHolderAt k α g p := by
  obtain ⟨R, hR, hC, K, hH⟩ := hf
  obtain ⟨Q, hQ, hEq⟩ := Metric.mem_nhds_iff.mp he
  let r := min R Q
  have hSubR : ball p r ⊆ ball p R := ball_subset_ball (min_le_left _ _)
  have hSubQ : ball p r ⊆ ball p Q := ball_subset_ball (min_le_right _ _)
  have hNear (x : E n) (hx : x ∈ ball p r) : g =ᶠ[𝓝 x] f := by
    filter_upwards [isOpen_ball.mem_nhds hx] with y hy
    exact hEq (hSubQ hy)
  refine ⟨r, lt_min hR hQ, ?_, K, ?_⟩
  · intro x hx
    exact ((hC.contDiffAt (isOpen_ball.mem_nhds (hSubR hx))).congr_of_eventuallyEq
      (hNear x hx)).contDiffWithinAt
  · intro x hx y hy
    rw [(hNear x hx).iteratedFDeriv ℝ k |>.self_of_nhds,
      (hNear y hy).iteratedFDeriv ℝ k |>.self_of_nhds]
    exact hH x (hSubR hx) y (hSubR hy)

end HasDirichletHolderAt

theorem hasDirichletHolderAt_of_contDiffAt_succ {n k : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E n → F} {p : E n}
    (hf : ContDiffAt ℝ (k + 1 : ℕ) f p) {α : ℝ≥0} (hα1 : α ≤ 1) :
    HasDirichletHolderAt k α f p := by
  obtain ⟨R, hR, hSub⟩ := Metric.mem_nhds_iff.mp (hf.eventually (by simp))
  have hBall : closedBall p (R / 2) ⊆ ball p R := closedBall_subset_ball (by linarith)
  have hC : ContDiffOn ℝ (k + 1 : ℕ) f (ball p R) := by
    intro x hx
    have hxC := hSub hx
    change ContDiffAt ℝ (k + 1 : ℕ) f x at hxC
    exact hxC.contDiffWithinAt
  have hjC : ContDiffOn ℝ 1 (iteratedFDeriv ℝ k f) (closedBall p (R / 2)) := by
    intro x hx
    have hxC := hSub (hBall hx)
    change ContDiffAt ℝ (k + 1 : ℕ) f x at hxC
    exact (hxC.iteratedFDeriv_right (by norm_cast; omega)).contDiffWithinAt
  obtain ⟨K, hK⟩ := exists_holderWith_restrict_of_contDiffOn_isCompact
    (isCompact_closedBall p (R / 2)) (convex_closedBall p (R / 2)) hjC hα1
  exact ⟨R / 2, by positivity, (hC.of_le (by norm_cast; omega)).mono
    (ball_subset_closedBall.trans hBall), K,
    (HolderWith.restrict_iff.mp hK).mono ball_subset_closedBall⟩

end KEBall
