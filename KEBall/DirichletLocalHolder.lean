import KEBall.DirichletLocalLinearC3Holder
import DifferentialGeometry.Analysis.Schauder.Holder.IteratedDerivative

/-!
# Local finite-order Holder jets

This predicate uses a uniform two-point Holder estimate on a neighborhood,
not merely a pointwise Holder estimate with one endpoint fixed.  The jet
is the actual iterated Frechet derivative.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Filter Metric Set
open DifferentialGeometry.Analysis DifferentialGeometry.Analysis.Schauder
open scoped ContDiff NNReal Topology

namespace KEBall

def HasDirichletHolderAt {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (k : ℕ) (α : ℝ≥0) (f : E n → F) (p : E n) : Prop :=
  ∃ R : ℝ, 0 < R ∧ ContDiffOn ℝ k f (ball p R) ∧
    ∃ K : ℝ≥0, HolderOnWith K α (iteratedFDeriv ℝ k f) (ball p R)

theorem dirichlet_holderOn_iterated_succ_iff {n k : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E n → F} {S : Set (E n)} {K α : ℝ≥0} :
    HolderOnWith K α (iteratedFDeriv ℝ (k + 1) f) S ↔
      HolderOnWith K α (iteratedFDeriv ℝ k (fderiv ℝ f)) S := by
  have he (x y : E n) :
      edist (iteratedFDeriv ℝ (k + 1) f x) (iteratedFDeriv ℝ (k + 1) f y) =
        edist (iteratedFDeriv ℝ k (fderiv ℝ f) x) (iteratedFDeriv ℝ k (fderiv ℝ f) y) := by
    rw [iteratedFDeriv_succ_eq_comp_right, iteratedFDeriv_succ_eq_comp_right,
      Function.comp_apply, Function.comp_apply, LinearIsometryEquiv.edist_map]
  constructor <;> intro h x hx y hy
  · rw [← he x y]
    exact h x hx y hy
  · rw [he x y]
    exact h x hx y hy

theorem dirichlet_holderOn_iterated_zero_iff {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E n → F} {S : Set (E n)} {K α : ℝ≥0} :
    HolderOnWith K α (iteratedFDeriv ℝ 0 f) S ↔ HolderOnWith K α f S := by
  have he (x y : E n) : edist (iteratedFDeriv ℝ 0 f x) (iteratedFDeriv ℝ 0 f y) =
      edist (f x) (f y) := by
    rw [iteratedFDeriv_zero_eq_comp]
    exact (continuousMultilinearCurryFin0 ℝ (E n) F).symm.edist_map _ _
  constructor <;> intro h x hx y hy
  · rw [← he x y]
    exact h x hx y hy
  · rw [he x y]
    exact h x hx y hy

theorem dirichlet_holderOn_iterated_one_iff {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E n → F} {S : Set (E n)} {K α : ℝ≥0} :
    HolderOnWith K α (iteratedFDeriv ℝ 1 f) S ↔ HolderOnWith K α (fderiv ℝ f) S :=
  dirichlet_holderOn_iterated_succ_iff.trans dirichlet_holderOn_iterated_zero_iff

theorem dirichlet_holderOn_iterated_two_iff {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E n → F} {S : Set (E n)} {K α : ℝ≥0} :
    HolderOnWith K α (iteratedFDeriv ℝ 2 f) S ↔
      HolderOnWith K α (fderiv ℝ (fderiv ℝ f)) S :=
  dirichlet_holderOn_iterated_succ_iff.trans dirichlet_holderOn_iterated_one_iff

theorem dirichlet_holderOn_iterated_three_iff {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E n → F} {S : Set (E n)} {K α : ℝ≥0} :
    HolderOnWith K α (iteratedFDeriv ℝ 3 f) S ↔
      HolderOnWith K α (fderiv ℝ (fderiv ℝ (fderiv ℝ f))) S :=
  dirichlet_holderOn_iterated_succ_iff.trans dirichlet_holderOn_iterated_two_iff

namespace HasDirichletHolderAt

variable {n k : ℕ} {F G : Type*}
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  {α : ℝ≥0} {f : E n → F} {p : E n}

theorem contDiffAt (hf : HasDirichletHolderAt k α f p) : ContDiffAt ℝ k f p := by
  obtain ⟨R, hR, hC, K, hK⟩ := hf
  exact hC.contDiffAt (isOpen_ball.mem_nhds (mem_ball_self hR))

theorem derivative (hf : HasDirichletHolderAt (k + 1) α f p) :
    HasDirichletHolderAt k α (fderiv ℝ f) p := by
  obtain ⟨R, hR, hC, K, hK⟩ := hf
  refine ⟨R, hR, hC.fderiv_of_isOpen isOpen_ball ?_, K,
    dirichlet_holderOn_iterated_succ_iff.mp hK⟩
  norm_cast

theorem of_order_le (hf : HasDirichletHolderAt k α f p) {j : ℕ}
    (hjk : j ≤ k) (hα1 : α ≤ 1) : HasDirichletHolderAt j α f p := by
  by_cases he : j = k
  · exact he ▸ hf
  obtain ⟨R, hR, hC, K, hK⟩ := hf
  have hr : 0 < R / 2 := by positivity
  have hSub : closedBall p (R / 2) ⊆ ball p R := closedBall_subset_ball (by linarith)
  have hjC : ContDiffOn ℝ 1 (iteratedFDeriv ℝ j f) (closedBall p (R / 2)) := by
    intro x hx
    apply ContDiffAt.contDiffWithinAt
    apply (hC.contDiffAt (isOpen_ball.mem_nhds (hSub hx))).iteratedFDeriv_right
    norm_cast
    omega
  obtain ⟨C, hCH⟩ := exists_holderWith_restrict_of_contDiffOn_isCompact
    (isCompact_closedBall p (R / 2)) (convex_closedBall p (R / 2)) hjC hα1
  refine ⟨R / 2, hr, (hC.of_le (by exact_mod_cast hjk)).mono
    (ball_subset_closedBall.trans hSub), C, ?_⟩
  exact (HolderWith.restrict_iff.mp hCH).mono ball_subset_closedBall

theorem of_fderiv {R : ℝ} (hR : 0 < R) (hC1 : ContDiffOn ℝ 1 f (ball p R))
    (hf : HasDirichletHolderAt k α (fderiv ℝ f) p) :
    HasDirichletHolderAt (k + 1) α f p := by
  obtain ⟨Q, hQ, hD, K, hKH⟩ := hf
  let r := min R Q
  have hSubR : ball p r ⊆ ball p R := ball_subset_ball (min_le_left _ _)
  have hSubQ : ball p r ⊆ ball p Q := ball_subset_ball (min_le_right _ _)
  refine ⟨r, lt_min hR hQ, ?_, K, dirichlet_holderOn_iterated_succ_iff.mpr (hKH.mono hSubQ)⟩
  apply (contDiffOn_succ_iff_fderiv_of_isOpen (n := k) isOpen_ball).mpr
  refine ⟨?_, by simp, hD.mono hSubQ⟩
  intro x hx
  exact ((hC1.contDiffAt (isOpen_ball.mem_nhds (hSubR hx))).differentiableAt
    (by norm_num)).differentiableWithinAt

theorem prodMk (hf : HasDirichletHolderAt k α f p) {g : E n → G}
    (hg : HasDirichletHolderAt k α g p) :
    HasDirichletHolderAt k α (fun x => (f x, g x)) p := by
  obtain ⟨R, hR, hF, K, hFK⟩ := hf
  obtain ⟨Q, hQ, hG, L, hGL⟩ := hg
  let r := min R Q
  have hSubR : ball p r ⊆ ball p R := ball_subset_ball (min_le_left _ _)
  have hSubQ : ball p r ⊆ ball p Q := ball_subset_ball (min_le_right _ _)
  have hfC := hF.mono hSubR
  have hgC := hG.mono hSubQ
  refine ⟨r, lt_min hR hQ, hfC.prodMk hgC, max K L, ?_⟩
  intro x hx y hy
  rw [iteratedFDeriv_prodMk (hfC.contDiffAt (isOpen_ball.mem_nhds hx))
    (hgC.contDiffAt (isOpen_ball.mem_nhds hx)) le_rfl,
    iteratedFDeriv_prodMk (hfC.contDiffAt (isOpen_ball.mem_nhds hy))
      (hgC.contDiffAt (isOpen_ball.mem_nhds hy)) le_rfl]
  change edist (ContinuousMultilinearMap.prodL ℝ (fun _ : Fin k => E n) F G (_, _))
    (ContinuousMultilinearMap.prodL ℝ (fun _ : Fin k => E n) F G (_, _)) ≤ _
  rw [LinearIsometryEquiv.edist_map]
  exact holderOnWith_prodMk (hFK.mono hSubR) (hGL.mono hSubQ) x hx y hy

theorem comp_smooth (hf : HasDirichletHolderAt k α f p) (hα : 0 < α) (hα1 : α ≤ 1)
    {g : F → G} (hg : ContDiff ℝ ∞ g) : HasDirichletHolderAt k α (g ∘ f) p := by
  obtain ⟨R, hR, hC, K, hKH⟩ := hf
  have hr : 0 < R / 2 := by positivity
  have hSub : closedBall p (R / 2) ⊆ ball p R := closedBall_subset_ball (by linarith)
  have hD : UniqueDiffOn ℝ (closedBall p (R / 2)) :=
    uniqueDiffOn_convex (convex_closedBall p (R / 2))
      ⟨p, mem_interior_iff_mem_nhds.mpr (closedBall_mem_nhds p hr)⟩
  have hJ : HolderOnWith K α (iteratedFDerivWithin ℝ k f (closedBall p (R / 2)))
      (closedBall p (R / 2)) := by
    intro x hx y hy
    rw [iteratedFDerivWithin_eq_iteratedFDeriv hD (hC.contDiffAt (isOpen_ball.mem_nhds (hSub hx))) hx,
      iteratedFDerivWithin_eq_iteratedFDeriv hD (hC.contDiffAt (isOpen_ball.mem_nhds (hSub hy))) hy]
    exact hKH x (hSub hx) y (hSub hy)
  have hgk : ContDiffOn ℝ (k + 1 : ℕ) g univ :=
    (hg.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffOn
  obtain ⟨C, hCH⟩ := exists_holderOnWith_iteratedFDerivWithin_comp_of_convex
    (isCompact_closedBall p (R / 2)) (convex_closedBall p (R / 2)) hD (hC.mono hSub)
    hα hα1 hJ isOpen_univ (mapsTo_univ _ _) hgk
  have hgC : ContDiffOn ℝ k (g ∘ f) (ball p R) :=
    (hg.of_le (WithTop.coe_le_coe.mpr le_top)).comp_contDiffOn hC
  refine ⟨R / 2, hr, hgC.mono (ball_subset_closedBall.trans hSub), C, ?_⟩
  intro x hx y hy
  have hx' := ball_subset_closedBall hx
  have hy' := ball_subset_closedBall hy
  have he := hCH x hx' y hy'
  rw [iteratedFDerivWithin_eq_iteratedFDeriv hD (hgC.contDiffAt (isOpen_ball.mem_nhds (hSub hx'))) hx',
    iteratedFDerivWithin_eq_iteratedFDeriv hD (hgC.contDiffAt (isOpen_ball.mem_nhds (hSub hy'))) hy'] at he
  exact he

theorem clm (hf : HasDirichletHolderAt k α f p) (hα : 0 < α) (hα1 : α ≤ 1)
    (L : F →L[ℝ] G) : HasDirichletHolderAt k α (fun x => L (f x)) p :=
  hf.comp_smooth hα hα1 L.contDiff

theorem sub (hf : HasDirichletHolderAt k α f p) {g : E n → F}
    (hg : HasDirichletHolderAt k α g p) (hα : 0 < α) (hα1 : α ≤ 1) :
    HasDirichletHolderAt k α (fun x => f x - g x) p :=
  (hf.prodMk hg).comp_smooth hα hα1 (contDiff_fst.sub contDiff_snd)

end HasDirichletHolderAt

end KEBall
