import KEBall.DirichletDiscreteCofactorEquation
import KEBall.DirichletClosedBallCofactorPerturbation
import KEBall.DirichletAveragedCofactorBounds
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Uniform convergence of the actual unitary-difference coefficients

The tensor at the rotated point is pulled back in both arguments. Its
closed-ball representative uses the actual within Hessian. Continuity on
the compact closed ball gives uniform convergence as the rotation tends
to the identity, without differentiating the Hessian.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Filter InnerProductSpace Matrix MeasureTheory Metric Set
open scoped ComplexOrder ContDiff Matrix.Norms.Elementwise Topology

namespace KEBall

theorem continuous_dirichletMeanCofactor {n : ℕ} :
    Continuous (fun p : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ =>
      dirichletMeanCofactor p.1 p.2) := by
  let F (p : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :=
    dirichletCofactorOfMatrix (p.1 + t • (p.2 - p.1))
  have hF : Continuous F.uncurry :=
    contDiff_dirichletCofactorOfMatrix.continuous.comp
      ((continuous_fst.fst).add (continuous_snd.smul (continuous_fst.snd.sub continuous_fst.fst)))
  have h := continuous_parametric_integral_of_continuous (μ := volume) hF
    (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1))
  simpa only [F, dirichletMeanCofactor, intervalIntegral.integral_of_le zero_le_one,
    integral_Icc_eq_integral_Ioc] using h

noncomputable def dirichletUnitaryPulledHessian {n : ℕ} (u : E n → ℝ)
    (S : E n →L[ℝ] E n) (hS : star S = -S) (t : ℝ) (x : E n) :
    Matrix (Fin n) (Fin n) ℂ :=
  complexHessianOfRealBilinear
    ((dirichletWithinRealHessian u (orthogonalFlow S hS t x)).bilinearComp
      (NormedSpace.exp (t • S)) (NormedSpace.exp (t • S)))

theorem dirichletUnitaryPulledHessian_zero {n : ℕ} (u : E n → ℝ)
    (S : E n →L[ℝ] E n) (hS : star S = -S) (x : E n) :
    dirichletUnitaryPulledHessian u S hS 0 x = dirichletWithinComplexHessian u x := by
  unfold dirichletUnitaryPulledHessian dirichletWithinComplexHessian dirichletWithinRealHessian
  rw [orthogonalFlow_zero_apply, zero_smul, NormedSpace.exp_zero]
  congr 1

theorem dirichletUnitaryPulledHessian_eq_on_ball {n : ℕ} {u : E n → ℝ}
    (hu : ContDiffOn ℝ 2 u (closedUnitBall n))
    (S : E n →L[ℝ] E n) (hS : star S = -S) (t : ℝ) {x : E n}
    (hx : x ∈ unitBall n) :
    dirichletUnitaryPulledHessian u S hS t x =
      complexHessian (u ∘ orthogonalFlow S hS t) x := by
  let R := orthogonalFlow S hS t
  have hxR : R x ∈ unitBall n := by
    simpa only [R, unitBall, mem_ball_zero_iff, LinearIsometryEquiv.norm_map] using hx
  have huR : ContDiffAt ℝ 2 (u ∘ R) x :=
    ((hu.mono ball_subset_closedBall).contDiffAt (isOpen_ball.mem_nhds hxR)).comp x
      R.toContinuousLinearEquiv.contDiff.contDiffAt
  unfold dirichletUnitaryPulledHessian
  rw [dirichletWithinRealHessian_eq_on_ball u hxR]
  have hH : (realHessian u (R x)).bilinearComp
      (NormedSpace.exp (t • S)) (NormedSpace.exp (t • S)) = realHessian (u ∘ R) x := by
    ext a b
    exact (realHessian_comp_linearIsometryEquiv u R x a b).symm
  rw [hH, complexHessianOfRealBilinear_eq huR]

theorem continuous_dirichletUnitaryPulledHessian {n : ℕ} {u : E n → ℝ}
    (hu : ContDiffOn ℝ 2 u (closedUnitBall n))
    (S : E n →L[ℝ] E n) (hS : star S = -S) :
    Continuous (fun p : ℝ × closedUnitBall n =>
      dirichletUnitaryPulledHessian u S hS p.1 p.2) := by
  let H := dirichletWithinRealHessian u
  let L (p : ℝ × closedUnitBall n) := NormedSpace.exp (p.1 • S)
  have hLt : Continuous (fun t : ℝ => NormedSpace.exp (t • S)) :=
    continuous_iff_continuousAt.mpr fun t => (hasDerivAt_exp_smul_const S t).continuousAt
  have hL : Continuous L := hLt.comp continuous_fst
  have hOrbit : Continuous (fun p : ℝ × closedUnitBall n => orthogonalFlow S hS p.1 p.2) :=
    hL.clm_apply (continuous_subtype_val.comp continuous_snd)
  have hH : Continuous (fun p : ℝ × closedUnitBall n =>
      H (orthogonalFlow S hS p.1 p.2)) := by
    exact (continuousOn_dirichletWithinRealHessian hu).domRestrict.comp
      (hOrbit.subtype_mk fun p => orthogonalFlow_mapsTo_closedUnitBall S hS p.1 p.2.property)
  have hFlip : Continuous (ContinuousLinearMap.flip :
      (E n →L[ℝ] E n →L[ℝ] ℝ) → E n →L[ℝ] E n →L[ℝ] ℝ) :=
    (ContinuousLinearMap.flipₗᵢ ℝ (E n) (E n) ℝ).continuous
  exact (continuous_dirichlet_complexHessianOfRealBilinear n).comp
    (hFlip.comp ((hFlip.comp (hH.clm_comp hL)).clm_comp hL))

set_option backward.isDefEq.respectTransparency true in
set_option maxHeartbeats 100000 in
theorem eventually_dirichlet_unitary_meanCofactor_close {n : ℕ} {u : E n → ℝ}
    (hu : ContDiffOn ℝ 2 u (closedUnitBall n))
    (S : E n →L[ℝ] E n) (hS : star S = -S) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t : ℝ in 𝓝 0, ∀ x ∈ closedUnitBall n,
      ‖dirichletCofactorOfMatrix (dirichletWithinComplexHessian u x) -
        dirichletMeanCofactor (dirichletWithinComplexHessian u x)
          (dirichletUnitaryPulledHessian u S hS t x)‖ < ε := by
  let : CompactSpace (closedUnitBall n) := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  let F (t : ℝ) (x : closedUnitBall n) :=
    dirichletMeanCofactor (dirichletWithinComplexHessian u x)
      (dirichletUnitaryPulledHessian u S hS t x)
  have hA : Continuous (fun p : ℝ × closedUnitBall n =>
      dirichletWithinComplexHessian u p.2) :=
    (continuousOn_dirichletWithinComplexHessian_of_C2 hu).domRestrict.comp continuous_snd
  have hPair := hA.prodMk (continuous_dirichletUnitaryPulledHessian hu S hS)
  have hRaw := (continuous_dirichletMeanCofactor (n := n)).comp hPair
  have hF : Continuous F.uncurry := hRaw
  have hT : TendstoUniformly F (F 0) (𝓝 (0 : ℝ)) := Continuous.tendstoUniformly F hF 0
  filter_upwards [Metric.tendstoUniformly_iff.mp hT ε hε] with t ht x hx
  have h := ht (⟨x, hx⟩ : closedUnitBall n)
  simpa only [F, dirichletUnitaryPulledHessian_zero, dirichletMeanCofactor_same, dist_eq_norm] using h

end KEBall

