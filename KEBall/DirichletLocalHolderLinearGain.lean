import KEBall.DirichletLocalHolderAssembly

/-! The proved linear gain expressed in actual local finite-order jets. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Filter Metric Set
open scoped ContDiff NNReal Topology

namespace KEBall

theorem hasDirichletHolderAt_three_of_linear_elliptic_equation {n : ℕ} (hn : 0 < n)
    {S : Set (E n)} (hS : IsOpen S) {p : E n} (hp : p ∈ S)
    {u f : E n → ℝ} {A : E n → E n →L[ℝ] E n} {α : ℝ≥0}
    (hα : 0 < α) (hα1 : α < 1)
    (hu : HasDirichletHolderAt 2 α u p)
    (hf : HasDirichletHolderAt 1 α f p)
    (hA : HasDirichletHolderAt 1 α A p)
    (hPos : (dirichletSchauderMatrix (A p)).PosDef)
    {l : ℝ} (hl : 0 < l) (hEll : ∀ z, l * ‖z‖ ^ 2 ≤ inner ℝ (A p z) z)
    (hEq : ∀ x ∈ S, dirichletContractionCLM n (A x) (fderiv ℝ (fderiv ℝ u) x) = f x) :
    HasDirichletHolderAt 3 α u p := by
  obtain ⟨Ru, hRu, huC, Ku, huH⟩ := hu
  obtain ⟨Rf, hRf, hfC, Kf, hfH⟩ := hf
  obtain ⟨Ra, hRa, hAC, Ka, hAH⟩ := hA
  let W := S ∩ ball p Ru ∩ ball p Rf ∩ ball p Ra
  have hW : IsOpen W := ((hS.inter isOpen_ball).inter isOpen_ball).inter isOpen_ball
  have hpW : p ∈ W := ⟨⟨⟨hp, mem_ball_self hRu⟩, mem_ball_self hRf⟩, mem_ball_self hRa⟩
  obtain ⟨Q, hQ, hQSub⟩ := Metric.mem_nhds_iff.mp (hW.mem_nhds hpW)
  let R : ℝ≥0 := ⟨Q / 2, by positivity⟩
  have hR : 0 < R := by change (0 : ℝ) < Q / 2; positivity
  have hSub : closedBall p (R : ℝ) ⊆ W :=
    (closedBall_subset_ball (by change Q / 2 < Q; linarith)).trans hQSub
  have huW : ContDiffOn ℝ 2 u W := huC.mono (fun _ hx => hx.1.1.2)
  have hfW : ContDiffOn ℝ 1 f W := hfC.mono (fun _ hx => hx.1.2)
  have hAW : ContDiffOn ℝ 1 A W := hAC.mono (fun _ hx => hx.2)
  have hHu : HolderOnWith Ku α (fderiv ℝ (fderiv ℝ u)) (closedBall p R) :=
    (dirichlet_holderOn_iterated_two_iff.mp huH).mono (fun _ hx => (hSub hx).1.1.2)
  have hDf : HolderOnWith Kf α (fderiv ℝ f) (closedBall p R) :=
    (dirichlet_holderOn_iterated_one_iff.mp hfH).mono (fun _ hx => (hSub hx).1.2)
  have hDA : HolderOnWith Ka α (fderiv ℝ A) (closedBall p R) :=
    (dirichlet_holderOn_iterated_one_iff.mp hAH).mono (fun _ hx => (hSub hx).2)
  obtain ⟨δ, hδ, _, K, hC3, hH3⟩ := exists_dirichlet_local_C3_holder_of_linear_elliptic_equation
    hn hW huW hfW hAW p R α Ku Kf Ka hR hα hα1 hSub hHu hDf hDA hPos hl hEll
      (fun x hx => hEq x hx.1.1.1)
  exact ⟨δ, hδ, hC3, K, dirichlet_holderOn_iterated_three_iff.mpr hH3⟩

end KEBall
