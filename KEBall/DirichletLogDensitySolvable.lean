import KEBall.DirichletLogDensityOpen
import KEBall.DirichletLogDensitySmoothLimit
import Mathlib.Topology.Connected.Clopen

/-! The actual smooth log-density path is both open and closed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 900000
open Filter MeasureTheory Metric Set
open scoped ComplexOrder ContDiff Topology
namespace KEBall

theorem exists_smoothNear_dirichlet_logDensity {n : ℕ} (hn : 2≤n)
    {g : E n → ℝ} (hg : ContDiff ℝ ∞ g) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ∃ v : E n → ℝ, SmoothNear (closedUnitBall n) v ∧
      (∀ x ∈ unitSphere n, v x=0) ∧
      (∀ x ∈ unitBall n, (complexHessian v x).PosDef) ∧
      (∀ x ∈ unitBall n, (complexHessian v x).det.re=Real.exp (t*g x)) := by
  classical
  let I := Icc (0 : ℝ) 1
  let P (t : I) : Prop := ∃ v : E n → ℝ, SmoothNear (closedUnitBall n) v ∧
    (∀ x ∈ unitSphere n, v x=0) ∧
    (∀ x ∈ unitBall n, (complexHessian v x).PosDef) ∧
    (∀ x ∈ unitBall n, (complexHessian v x).det.re=Real.exp (t.val*g x))
  let S : Set I := {t | P t}
  have hOpen : IsOpen S := by
    apply isOpen_iff_mem_nhds.mpr
    intro t ht
    obtain ⟨u,hu,hu0,huP,huEq⟩ := ht
    have h := eventually_exists_smoothNear_dirichlet_logDensity (by omega) hg t.property hu hu0 huP huEq
    exact continuous_subtype_val.continuousAt.tendsto.eventually h
  have hClosed : IsClosed S := by
    apply IsSeqClosed.isClosed
    intro s t hs hT
    choose u hu hu0 huP huEq using hs
    have hTR : Tendsto (fun j => (s j).val) atTop (𝓝 t.val) :=
      continuous_subtype_val.continuousAt.tendsto.comp hT
    have hgN : SmoothNear (closedUnitBall n) g := ⟨univ,isOpen_univ,subset_univ _,hg.contDiffOn⟩
    obtain ⟨v,_,hv,hv0,hvP,hvEq⟩ := exists_dirichlet_smoothNear_limit_of_logDensityPath
      hn hgN (fun j => (s j).property) hTR hu hu0 huP huEq
    exact ⟨v,hv,hv0,hvP,hvEq⟩
  have hNonempty : S.Nonempty := by
    refine ⟨⟨0,by constructor <;> norm_num⟩,?_⟩
    exact exists_smoothNear_dirichlet_logDensity_zero (by omega) hg
  letI : PreconnectedSpace I := Subtype.preconnectedSpace isPreconnected_Icc
  have hAll : S=univ := IsClopen.eq_univ ⟨hClosed,hOpen⟩ hNonempty
  have h := (show (⟨t,ht⟩ : I) ∈ S by rw [hAll]; trivial)
  exact h

end KEBall
