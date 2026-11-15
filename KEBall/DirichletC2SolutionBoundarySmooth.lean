import KEBall.DirichletAllOrderCartesianJets
import KEBall.DirichletSmoothRepresentative
import KEBall.DirichletClosedBallExtension

/-! Closing the high-order boundary regularity gap for the same C2 Dirichlet potential. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 900000
open Filter MeasureTheory Metric Set
open scoped BigOperators ComplexOrder ContDiff ENNReal Topology
namespace KEBall

theorem contDiffOn_closedUnitBall_of_C2_dirichlet_solution {n : ℕ}
    (hn : 0<n) {u f : E n → ℝ} (hu : ContDiffOn ℝ 2 u (closedUnitBall n))
    (huS : ContDiffOn ℝ ∞ u (unitBall n)) (hu0 : ∀ x ∈ unitSphere n, u x=0)
    (hPos : ∀ x ∈ closedUnitBall n, (dirichletWithinComplexHessian u x).PosDef)
    (hf : SmoothNear (closedUnitBall n) f)
    (hEq : ∀ x ∈ unitBall n, (complexHessian u x).det.re=f x) :
    ContDiffOn ℝ ∞ u (closedUnitBall n) := by
  have hWeak (k : ℕ) : HasDirichletWeakDerivativesL2 u k :=
    hasDirichletWeakDerivativesL2_all_angularWords_of_C2_solution hn hu huS hu0 hPos hf hEq k
      (fun i : Fin 0 => i.elim0)
  obtain ⟨g,hg,he⟩ := HasDirichletWeakDerivativesL2.exists_contDiffOn_closedUnitBall hn hWeak
  have heB := (volume0 n).eqOn_open_of_ae_eq he isOpen_ball
    (hg.continuousOn.mono ball_subset_closedBall) (hu.continuousOn.mono ball_subset_closedBall)
  have hClosure : closure (unitBall n)=closedUnitBall n := closure_ball _ (by norm_num)
  have heK : EqOn g u (closedUnitBall n) := heB.of_subset_closure
    hg.continuousOn hu.continuousOn ball_subset_closedBall (by rw [hClosure])
  exact hg.congr (fun x hx => (heK hx).symm)

theorem contDiffOn_closedUnitBall_angularWords_of_C2_dirichlet_solution {n : ℕ}
    (hn : 0<n) {u f : E n → ℝ} (hu : ContDiffOn ℝ 2 u (closedUnitBall n))
    (huS : ContDiffOn ℝ ∞ u (unitBall n)) (hu0 : ∀ x ∈ unitSphere n, u x=0)
    (hPos : ∀ x ∈ closedUnitBall n, (dirichletWithinComplexHessian u x).PosDef)
    (hf : SmoothNear (closedUnitBall n) f)
    (hEq : ∀ x ∈ unitBall n, (complexHessian u x).det.re=f x)
    {m : ℕ} (R : Fin m → DirichletUnitaryField n) :
    ContDiffOn ℝ ∞ (dirichletAngularWord R u) (closedUnitBall n) :=
  contDiffOn_dirichletAngularWord
    (contDiffOn_closedUnitBall_of_C2_dirichlet_solution hn hu huS hu0 hPos hf hEq) R

theorem exists_smoothNear_representative_of_C2_dirichlet_solution {n : ℕ}
    (hn : 0<n) {u f : E n → ℝ} (hu : ContDiffOn ℝ 2 u (closedUnitBall n))
    (huS : ContDiffOn ℝ ∞ u (unitBall n)) (hu0 : ∀ x ∈ unitSphere n, u x=0)
    (hPos : ∀ x ∈ closedUnitBall n, (dirichletWithinComplexHessian u x).PosDef)
    (hf : SmoothNear (closedUnitBall n) f)
    (hEq : ∀ x ∈ unitBall n, (complexHessian u x).det.re=f x) :
    ∃ v : E n → ℝ, SmoothNear (closedUnitBall n) v ∧ EqOn v u (closedUnitBall n) :=
  exists_smoothNear_closedUnitBall_of_contDiffOn
    (contDiffOn_closedUnitBall_of_C2_dirichlet_solution hn hu huS hu0 hPos hf hEq)

end KEBall
