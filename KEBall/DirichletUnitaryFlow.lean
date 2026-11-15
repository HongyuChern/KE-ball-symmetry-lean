import KEBall.DirichletUnitaryTangents
import KEBall.DirichletAngularFlow

/-! A skew-adjoint field commuting with the complex structure generates a
smooth unitary orbit of the centered ball. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open InnerProductSpace Metric Set
open scoped ContDiff

namespace KEBall

theorem orthogonalFlow_apply_J {n : ℕ} (R : E n →L[ℝ] E n) (hR : star R = -R)
    (hJ : ∀ x, R (J x) = J (R x)) (t : ℝ) (x : E n) :
    orthogonalFlow R hR t (J x) = J (orthogonalFlow R hR t x) := by
  have h : Commute (t • R) (JCLM n) := by
    show (t • R) * JCLM n = JCLM n * (t • R)
    ext1 y
    change t • R (JCLM n y) = JCLM n (t • R y)
    simpa only [map_smul, JCLM_apply] using congrArg (t • ·) (hJ y)
  have he := h.exp_left
  have he' := DFunLike.congr_fun he.eq x
  change NormedSpace.exp (t • R) (JCLM n x) =
    JCLM n (NormedSpace.exp (t • R) x) at he'
  change ((orthogonalFlow R hR t).toContinuousLinearEquiv.toContinuousLinearMap) (J x) =
    J (((orthogonalFlow R hR t).toContinuousLinearEquiv.toContinuousLinearMap) x)
  rw [orthogonalFlow_CLM]
  simpa only [JCLM_apply] using he'

theorem contDiff_orthogonalFlow_apply {n : ℕ} {r : ℕ∞ω}
    (R : E n →L[ℝ] E n) (hR : star R = -R) :
    ContDiff ℝ r (fun p : ℝ × E n => orthogonalFlow R hR p.1 p.2) := by
  have hExp : ContDiff ℝ r (NormedSpace.exp : (E n →L[ℝ] E n) → E n →L[ℝ] E n) := by
    apply ContDiff.of_le (n := ω)
    · exact contDiff_omega_iff_analyticOnNhd.mpr fun x _ =>
        NormedSpace.exp_analytic (𝕂 := ℝ) x
    · exact le_top
  have hCLM : ContDiff ℝ r (fun p : ℝ × E n => NormedSpace.exp (p.1 • R)) :=
    hExp.comp (contDiff_fst.smul contDiff_const)
  exact hCLM.clm_apply contDiff_snd

theorem orthogonalFlow_mapsTo_closedUnitBall {n : ℕ}
    (R : E n →L[ℝ] E n) (hR : star R = -R) (t : ℝ) :
    MapsTo (orthogonalFlow R hR t) (closedUnitBall n) (closedUnitBall n) := by
  intro x hx
  simpa only [closedUnitBall, mem_closedBall, dist_zero_right, LinearIsometryEquiv.norm_map] using hx

theorem orthogonalFlow_mapsTo_unitSphere {n : ℕ}
    (R : E n →L[ℝ] E n) (hR : star R = -R) (t : ℝ) :
    MapsTo (orthogonalFlow R hR t) (unitSphere n) (unitSphere n) := by
  intro x hx
  simpa only [unitSphere, mem_sphere, dist_zero_right, LinearIsometryEquiv.norm_map] using hx

end KEBall
