import DifferentialGeometry.Analysis.Schauder.Holder.CompactRegularity
import KEBall.DirichletLocalHolderLinearMap

/-! Holder calculus on compact sets, retaining the common exponent. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Function Metric Set
open DifferentialGeometry.Analysis.Schauder
open scoped ContDiff NNReal

namespace KEBall

def HasDirichletHolderOn {X F : Type*} [PseudoEMetricSpace X] [PseudoEMetricSpace F]
    (α : ℝ≥0) (f : X → F) (S : Set X) : Prop :=
  ∃ K : ℝ≥0, HolderOnWith K α f S

namespace HasDirichletHolderOn

variable {X F G H : Type*} [PseudoMetricSpace X]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  {α : ℝ≥0} {S T : Set X} {f : X → F}

theorem mono (hf : HasDirichletHolderOn α f S) (hT : T ⊆ S) :
    HasDirichletHolderOn α f T := by
  obtain ⟨K, hK⟩ := hf
  exact ⟨K, hK.mono hT⟩

theorem congr (hf : HasDirichletHolderOn α f S) {g : X → F} (he : EqOn g f S) :
    HasDirichletHolderOn α g S := by
  obtain ⟨K, hK⟩ := hf
  refine ⟨K, fun x hx y hy => ?_⟩
  rw [he hx, he hy]
  exact hK x hx y hy

theorem continuousOn (hf : HasDirichletHolderOn α f S) (hα : 0 < α) :
    ContinuousOn f S := by
  obtain ⟨K, hK⟩ := hf
  exact hK.continuousOn hα

theorem prodMk (hf : HasDirichletHolderOn α f S) {g : X → G}
    (hg : HasDirichletHolderOn α g S) :
    HasDirichletHolderOn α (fun x => (f x, g x)) S := by
  obtain ⟨K, hK⟩ := hf
  obtain ⟨L, hL⟩ := hg
  exact ⟨max K L, holderOnWith_prodMk hK hL⟩

theorem comp_contDiffOn (hf : HasDirichletHolderOn α f S)
    (hS : IsCompact S) (hα : 0 < α) {U : Set F} (hU : IsOpen U)
    {g : F → G} (hg : ContDiffOn ℝ 1 g U) (hMaps : MapsTo f S U) :
    HasDirichletHolderOn α (g ∘ f) S := by
  obtain ⟨K, hK⟩ := hf
  exact exists_holderOnWith_comp_of_contDiffOn_isCompact hS hU hK hα hMaps hg

theorem comp_smooth (hf : HasDirichletHolderOn α f S)
    (hS : IsCompact S) (hα : 0 < α) {g : F → G} (hg : ContDiff ℝ ∞ g) :
    HasDirichletHolderOn α (g ∘ f) S :=
  hf.comp_contDiffOn hS hα isOpen_univ
    (hg.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffOn (mapsTo_univ _ _)

theorem clm (hf : HasDirichletHolderOn α f S) (L : F →L[ℝ] G) :
    HasDirichletHolderOn α (fun x => L (f x)) S := by
  obtain ⟨K, hK⟩ := hf
  refine ⟨‖L‖₊ * K, ?_⟩
  have h := L.lipschitz.holderWith.comp_holderOnWith hK
  simpa only [Function.comp_def, one_mul, NNReal.coe_one, NNReal.rpow_one] using h

theorem add (hf : HasDirichletHolderOn α f S) {g : X → F}
    (hg : HasDirichletHolderOn α g S) (hS : IsCompact S) (hα : 0 < α) :
    HasDirichletHolderOn α (fun x => f x + g x) S :=
  (hf.prodMk hg).comp_smooth hS hα (contDiff_fst.add contDiff_snd)

theorem sub (hf : HasDirichletHolderOn α f S) {g : X → F}
    (hg : HasDirichletHolderOn α g S) (hS : IsCompact S) (hα : 0 < α) :
    HasDirichletHolderOn α (fun x => f x - g x) S :=
  (hf.prodMk hg).comp_smooth hS hα (contDiff_fst.sub contDiff_snd)

theorem smul {a : X → ℝ} (ha : HasDirichletHolderOn α a S)
    (hf : HasDirichletHolderOn α f S) (hS : IsCompact S) (hα : 0 < α) :
    HasDirichletHolderOn α (fun x => a x • f x) S :=
  (ha.prodMk hf).comp_smooth hS hα (contDiff_fst.smul contDiff_snd)

theorem clm_comp {A : X → G →L[ℝ] H} {B : X → F →L[ℝ] G}
    (hA : HasDirichletHolderOn α A S) (hB : HasDirichletHolderOn α B S)
    (hS : IsCompact S) (hα : 0 < α) :
    HasDirichletHolderOn α (fun x => (A x).comp (B x)) S :=
  (hA.prodMk hB).comp_smooth hS hα (contDiff_fst.clm_comp contDiff_snd)

theorem clm_apply {A : X → F →L[ℝ] G}
    (hA : HasDirichletHolderOn α A S) (hf : HasDirichletHolderOn α f S)
    (hS : IsCompact S) (hα : 0 < α) :
    HasDirichletHolderOn α (fun x => A x (f x)) S :=
  (hA.prodMk hf).comp_smooth hS hα (contDiff_fst.clm_apply contDiff_snd)

theorem pi {ι : Type*} [Fintype ι] {g : X → ι → F}
    (hg : ∀ i, HasDirichletHolderOn α (fun x => g x i) S) :
    HasDirichletHolderOn α g S := by
  classical
  choose K hK using hg
  refine ⟨∑ i, K i, fun x hx y hy => ?_⟩
  apply edist_pi_le_iff.mpr
  intro i
  apply (hK i x hx y hy).trans
  gcongr
  exact Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_univ i)

theorem sum {ι : Type*} [Fintype ι] {g : ι → X → F}
    (hg : ∀ i, HasDirichletHolderOn α (g i) S) (hS : IsCompact S) (hα : 0 < α) :
    HasDirichletHolderOn α (fun x => ∑ i, g i x) S :=
  (pi hg).comp_smooth hS hα (ContDiff.sum fun i _ => contDiff_apply ℝ F i)

theorem const (c : F) : HasDirichletHolderOn α (fun _ : X => c) S := by
  refine ⟨0, fun x hx y hy => ?_⟩
  simp

theorem inv {f : X → ℝ} (hf : HasDirichletHolderOn α f S)
    (hS : IsCompact S) (hα : 0 < α) (h0 : ∀ x ∈ S, f x ≠ 0) :
    HasDirichletHolderOn α (fun x => (f x)⁻¹) S := by
  apply hf.comp_contDiffOn hS hα (U := {y : ℝ | y ≠ 0})
    isClosed_singleton.isOpen_compl
  · exact contDiffOn_id.inv (fun _ hy => hy)
  · exact h0

end HasDirichletHolderOn

theorem hasDirichletHolderOn_of_contDiffOn {V F : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {S : Set V} (hS : IsCompact S) (hConv : Convex ℝ S)
    {f : V → F} (hf : ContDiffOn ℝ 1 f S) {α : ℝ≥0} (hα1 : α ≤ 1) :
    HasDirichletHolderOn α f S := by
  obtain ⟨K, hK⟩ := exists_holderWith_restrict_of_contDiffOn_isCompact hS hConv hf hα1
  exact ⟨K, fun x hx y hy => hK ⟨x, hx⟩ ⟨y, hy⟩⟩

end KEBall
