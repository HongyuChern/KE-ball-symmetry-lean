import KEBall.DirichletAngularWordEquation
import KEBall.DirichletSobolevParameter
import KEBall.DirichletSobolevTrace

/-!
# The actual higher angular determinant equation for smooth potentials

The Sobolev orbit required by the previously proved chain rule is constructed
directly from the given smooth potential.  No inverse for the nonlinear
Dirichlet operator is assumed.  This supplies the equation for the smooth
members of a continuity path before estimating its proper-partition terms.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Filter Matrix MeasureTheory Metric Set
open scoped ContDiff Matrix.Norms.Elementwise Topology

namespace KEBall

local notation "ν[" n "]" => MeasureTheory.Measure.restrict (volume0 n) (unitBall n)

local instance (n : ℕ) : CompactSpace (ClosedBall n) :=
  isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : E n) 1)

theorem closedBall_angularWord_eq_linearized_det_of_contDiff {n m : ℕ}
    (hn : 0 < n) {u : E n → ℝ} (hu : ContDiff ℝ ∞ u)
    (R : Fin (m + 1) → DirichletUnitaryField n) :
    ∀ x ∈ closedUnitBall n,
      ((dirichletWithinComplexHessian u x).adjugate *
        dirichletWithinComplexHessian (dirichletAngularWord R u) x).trace.re +
        dirichletAngularDetLowerTerms R dirichletWithinComplexHessian u x =
          dirichletAngularWord R (fun y => (complexHessian u y).det.re) x := by
  let k : ℕ := 2 * (2 * n + 1)
  let b := EuclideanSpace.basisFun (Fin (2 * n)) ℝ
  have hk : 2 * (2 * n + 1) ≤ k := le_rfl
  obtain ⟨T, hT⟩ := exists_dirichletSobolevJetGraph_toContinuousMap
    (k := k + 2) hn b (by omega)
  let F (p : (Fin (m + 1) → ℝ) × E n) := u (dirichletUnitaryOrbit R p.1 p.2)
  have hF : ContDiff ℝ ∞ F := hu.comp (contDiff_dirichletUnitaryOrbit_apply R)
  have hSlice (t : Fin (m + 1) → ℝ) : ContDiff ℝ ∞ (fun x => F (t, x)) :=
    hF.comp (contDiff_const.prodMk contDiff_id)
  let W (t : Fin (m + 1) → ℝ) :=
    dirichletSobolevJetOfSmooth (k := k + 2) hn b (hSlice t)
  have hW : ContDiff ℝ ∞ W :=
    contDiff_dirichletSobolevJetOfSmooth_family hn b hF hSlice
  have hRep (t : Fin (m + 1) → ℝ) (x : ClosedBall n) :
      T (W t) x = u (dirichletUnitaryOrbit R t x) := by
    exact hT (W t) (fun y => F (t, y)) (hSlice t).continuous.continuousOn
      (dirichletSobolevJetOfSmooth_fst_ae (k := k + 2) hn b (hSlice t)).symm x
  have hf : ContDiff ℝ ∞ (fun y => (complexHessian u y).det.re) := by
    apply contDiffOn_univ.mp
    exact Complex.reCLM.contDiff.comp_contDiffOn
      (matrixField_det_contDiffOn (complexHessian_contDiffOn isOpen_univ hu.contDiffOn))
  exact closedBall_angularWord_eq_linearized_det_of_sobolev_orbit hn hk T hT
    (hu.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).contDiffOn hf
    (fun _ _ => rfl)
    (fun j R' => (contDiffOn_dirichletAngularWord hu.contDiffOn R').of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) R
    (Eventually.of_forall fun t => ⟨hW.contDiffAt, hRep t⟩)

end KEBall
