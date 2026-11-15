import KEBall.DirichletLocalHolderAssembly
import KEBall.DirichletLocalNonlinearC3Holder
import KEBall.DirichletClosedBallEllipticity

/-! Actual local nonlinear jets and ellipticity of their cofactor. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Filter Matrix Metric Set
open scoped ComplexOrder ContDiff Matrix.Norms.Elementwise NNReal Topology

namespace KEBall

theorem hasDirichletHolderAt_three_of_positive_determinant {n : ℕ} (hn : 0 < n)
    {S : Set (E n)} (hS : IsOpen S) {p : E n} (hp : p ∈ S)
    {u f : E n → ℝ} {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1)
    (hu : HasDirichletHolderAt 2 α u p) (hf : HasDirichletHolderAt 2 α f p)
    (hPos : ∀ x ∈ S, (complexHessian u x).PosDef)
    (hEq : ∀ x ∈ S, (complexHessian u x).det.re = f x) :
    HasDirichletHolderAt 3 α u p := by
  obtain ⟨Ru, hRu, huC, Ku, huH⟩ := hu
  obtain ⟨Rf, hRf, hfC, Kf, hfH⟩ := hf
  let W := S ∩ ball p Ru ∩ ball p Rf
  have hW : IsOpen W := (hS.inter isOpen_ball).inter isOpen_ball
  have hpW : p ∈ W := ⟨⟨hp, mem_ball_self hRu⟩, mem_ball_self hRf⟩
  obtain ⟨Q, hQ, hQSub⟩ := Metric.mem_nhds_iff.mp (hW.mem_nhds hpW)
  let R : ℝ≥0 := ⟨Q / 2, by positivity⟩
  have hR : 0 < R := by change (0 : ℝ) < Q / 2; positivity
  have hSub : closedBall p (R : ℝ) ⊆ W :=
    (closedBall_subset_ball (by change Q / 2 < Q; linarith)).trans hQSub
  have huW : ContDiffOn ℝ 2 u W := huC.mono (fun _ hx => hx.1.2)
  have hfW : ContDiffOn ℝ 2 f W := hfC.mono (fun _ hx => hx.2)
  have hHu : HolderOnWith Ku α (fderiv ℝ (fderiv ℝ u)) (closedBall p R) :=
    (dirichlet_holderOn_iterated_two_iff.mp huH).mono (fun _ hx => (hSub hx).1.2)
  obtain ⟨δ, hδ, _, K, hC3, hH3⟩ := exists_dirichlet_local_C3_holder_of_positive_determinant
    hn hW huW hfW (fun x hx => hPos x hx.1.1) (fun x hx => hEq x hx.1.1)
      p R α Ku hR hα hα1 hSub hHu
  exact ⟨δ, hδ, hC3, K, dirichlet_holderOn_iterated_three_iff.mpr hH3⟩

theorem hasDirichletHolderAt_cofactor_of_hessian {n k : ℕ} {u : E n → ℝ} {p : E n}
    {α : ℝ≥0} (hα : 0 < α) (hα1 : α ≤ 1)
    (hu : HasDirichletHolderAt (k + 2) α u p) :
    HasDirichletHolderAt k α (fun x => dirichletCofactorOfMatrix (complexHessian u x)) p := by
  have hH : HasDirichletHolderAt k α (fderiv ℝ (fderiv ℝ u)) p := hu.derivative.derivative
  have hC := (hH.clm hα hα1 (@dirichletComplexHessianCLM n)).comp_smooth
    hα hα1 contDiff_dirichletCofactorOfMatrix
  apply hC.congr_of_eventuallyEq
  have hu2 := (hu.of_order_le (by omega : 2 ≤ k + 2) hα1).contDiffAt
  filter_upwards [hu2.eventually (by simp)] with x hx
  change dirichletCofactorOfMatrix (complexHessian u x) =
    dirichletCofactorOfMatrix (complexHessianOfRealBilinear (fderiv ℝ (fderiv ℝ u) x))
  exact congrArg dirichletCofactorOfMatrix (complexHessianOfRealBilinear_eq hx).symm

theorem exists_dirichlet_point_cofactor_ellipticity {n : ℕ} (hn : 0 < n)
    {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.PosDef) :
    (dirichletSchauderMatrix (dirichletCofactorOfMatrix H)).PosDef ∧
      ∃ l : ℝ, 0 < l ∧ ∀ v : E n,
        l * ‖v‖ ^ 2 ≤ inner ℝ (dirichletCofactorOfMatrix H v) v := by
  obtain ⟨l, M, hl, hM, hNorm, hEll⟩ :=
    exists_uniform_ellipticity_of_continuous_closedBall_operator hn
      (A := fun _ : E n => dirichletCofactorOfMatrix H) continuousOn_const
      (fun _ _ v hv => dirichletCofactorOfMatrix_pos hH hv)
  have hE : ∀ v : E n, l * ‖v‖ ^ 2 ≤ inner ℝ (dirichletCofactorOfMatrix H v) v :=
    hEll 0 (by simp [closedUnitBall])
  exact ⟨dirichletSchauderMatrix_posDef_of_coercive
    (dirichletCofactorOfMatrix_symmetric hH.isHermitian) hl hE, l, hl, hE⟩

end KEBall
