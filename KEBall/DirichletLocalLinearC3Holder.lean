import KEBall.DirichletLinearC3Holder
import KEBall.DirichletSchauderLocalC1

/-!
# Local linear C3,alpha regularity with C1,alpha coefficients and source

Only the data on a compact ball are extended.  The equation, the Hessian
and the third derivative in the conclusion refer to the original function.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Filter Metric Set
open scoped NNReal Topology

namespace KEBall

theorem exists_dirichlet_local_C3_holder_of_linear_elliptic_equation {n : ℕ}
    (hn : 0 < n) {S : Set (E n)} (hS : IsOpen S) {u f : E n → ℝ}
    {A : E n → E n →L[ℝ] E n}
    (hu : ContDiffOn ℝ 2 u S) (hf : ContDiffOn ℝ 1 f S) (hA : ContDiffOn ℝ 1 A S)
    (p : E n) (R α KH KDf KDA : ℝ≥0) (hR : 0 < R) (hα : 0 < α) (hα1 : α < 1)
    (hSub : closedBall p (R : ℝ) ⊆ S)
    (hHH : HolderOnWith KH α (fderiv ℝ (fderiv ℝ u)) (closedBall p R))
    (hDfH : HolderOnWith KDf α (fderiv ℝ f) (closedBall p R))
    (hDAH : HolderOnWith KDA α (fderiv ℝ A) (closedBall p R))
    (hPos : (dirichletSchauderMatrix (A p)).PosDef)
    {l : ℝ} (hl : 0 < l) (hEll : ∀ z, l * ‖z‖ ^ 2 ≤ inner ℝ (A p z) z)
    (hEq : ∀ x ∈ S, dirichletContractionCLM n (A x) (fderiv ℝ (fderiv ℝ u) x) = f x) :
    ∃ δ : ℝ, 0 < δ ∧ ball p δ ⊆ S ∧ ∃ K : ℝ≥0,
      ContDiffOn ℝ 3 u (ball p δ) ∧
      HolderOnWith K α (fderiv ℝ (fderiv ℝ (fderiv ℝ u))) (ball p δ) := by
  have hhalf : R / 2 < R := div_lt_self hR (by norm_num)
  obtain ⟨w, Dw, Hw, Kw, KDw, KHw, hwEq, hwDer, hDwDer, hwH, hDwH, hHwH⟩ :=
    exists_dirichlet_actual_C2_holder_extension p (R / 2) R α KH hhalf hα hα1.le
      hS hSub hu hHH
  obtain ⟨Kf, hfH⟩ := exists_dirichlet_holderOnWith_of_C1_closedBall p R α hα1.le (hf.mono hSub)
  obtain ⟨KA, hAH⟩ := exists_dirichlet_holderOnWith_of_C1_closedBall p R α hα1.le (hA.mono hSub)
  obtain ⟨g, Dg, Kg, KDg, hgEq, hgDer, hgH, hDgH⟩ :=
    exists_dirichlet_C1_holder_jet_extension p (R / 2) R α Kf KDf hhalf hα hα1.le
      (fun x hx => ((hf.contDiffAt (hS.mem_nhds (hSub (ball_subset_closedBall hx)))).differentiableAt
        (by norm_num)).hasFDerivAt) hfH hDfH
  obtain ⟨B, DB, KB, KDB, hBEq, hBDer, hBH, hDBH⟩ :=
    exists_dirichlet_C1_holder_jet_extension p (R / 2) R α KA KDA hhalf hα hα1.le
      (fun x hx => ((hA.contDiffAt (hS.mem_nhds (hSub (ball_subset_closedBall hx)))).differentiableAt
        (by norm_num)).hasFDerivAt) hAH hDAH
  have hNear (x : E n) (hx : x ∈ ball p ((R / 2 : ℝ≥0) : ℝ)) :
      (w : E n → ℝ) =ᶠ[𝓝 x] u := by
    filter_upwards [isOpen_ball.mem_nhds hx] with y hy
    exact hwEq (ball_subset_closedBall hy)
  have hSmall : closedBall p (2 * ((R / 8 : ℝ≥0) : ℝ)) ⊆ ball p ((R / 2 : ℝ≥0) : ℝ) := by
    apply closedBall_subset_ball
    push_cast
    have hR' : (0 : ℝ) < R := hR
    linarith
  have hBallSub : ball p ((R / 2 : ℝ≥0) : ℝ) ⊆ S :=
    (ball_subset_closedBall.trans (closedBall_subset_closedBall
      (by exact_mod_cast hhalf.le))).trans hSub
  have hSecond : fderiv ℝ (fderiv ℝ (w : E n → ℝ)) = Hw := by
    rw [show fderiv ℝ (w : E n → ℝ) = Dw from funext fun x => (hwDer x).fderiv]
    exact funext fun x => (hDwDer x).fderiv
  have hHwEq (x : E n) (hx : x ∈ ball p ((R / 2 : ℝ≥0) : ℝ)) :
      Hw x = fderiv ℝ (fderiv ℝ u) x := by
    rw [← hSecond]
    exact (hNear x hx).fderiv.fderiv_eq
  have hBp : B p = A p := hBEq (mem_closedBall_self (by positivity))
  have hPosB : (dirichletSchauderMatrix (B p)).PosDef := by rwa [hBp]
  have hEllB (z : E n) : l * ‖z‖ ^ 2 ≤ inner ℝ (B p z) z := by rw [hBp]; exact hEll z
  have hEqW (x : E n) (hx : x ∈ closedBall p (2 * ((R / 8 : ℝ≥0) : ℝ))) :
      dirichletContractionCLM n (B x) (Hw x) = g x := by
    rw [hBEq (ball_subset_closedBall (hSmall hx)), hHwEq x (hSmall hx),
      hEq x (hBallSub (hSmall hx)), hgEq (ball_subset_closedBall (hSmall hx))]
  obtain ⟨δ, hδ, K, hwC3, hThird⟩ := exists_dirichlet_local_C3_holder_of_linear_elliptic_jets
    hn w Dw Hw g Dg B DB hwDer hDwDer hgDer hBDer hα hα1 hDwH hHwH hDgH hBH hDBH p (R / 8)
      (div_pos hR (by norm_num)) hPosB hl hEllB hEqW
  let ε : ℝ := min δ ((R : ℝ) / 4)
  have hε : 0 < ε := lt_min hδ (by exact div_pos hR (by norm_num))
  have hεδ : ball p ε ⊆ ball p δ := ball_subset_ball (min_le_left _ _)
  have hεhalf : ball p ε ⊆ ball p ((R / 2 : ℝ≥0) : ℝ) := by
    apply ball_subset_ball
    have hR' : (0 : ℝ) < R := hR
    calc
      ε ≤ (R : ℝ) / 4 := min_le_right _ _
      _ ≤ ((R / 2 : ℝ≥0) : ℝ) := by push_cast; linarith
  have hThirdEq (x : E n) (hx : x ∈ ball p ε) :
      fderiv ℝ (Hw : E n → E n →L[ℝ] E n →L[ℝ] ℝ) x =
        fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x := by
    rw [← hSecond]
    exact ((hNear x (hεhalf hx)).fderiv.fderiv).fderiv_eq
  refine ⟨ε, hε, hεhalf.trans hBallSub, K, ?_, ?_⟩
  · intro x hx
    exact ((hwC3.contDiffAt (isOpen_ball.mem_nhds (hεδ hx))).congr_of_eventuallyEq
      (hNear x (hεhalf hx)).symm).contDiffWithinAt
  · intro x hx y hy
    rw [← hThirdEq x hx, ← hThirdEq y hy]
    exact hThird x (hεδ hx) y (hεδ hy)

end KEBall
