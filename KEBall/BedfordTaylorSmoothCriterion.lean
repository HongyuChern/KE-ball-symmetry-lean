import KEBall.BedfordTaylorSmoothMeasure
import PshLines.FirstPass.SmoothPshHessian

/-!
# The smooth coordinate Hessian criterion
-/

set_option autoImplicit false

open Filter Set TopologicalSpace
open scoped ComplexOrder ContDiff Topology

namespace KEBall.BedfordTaylor

open PshLines
open PshLines.FirstPass
open PshLines.FirstPass.MongeAmpere (IsSmoothPshOn coordinateVector)

variable {n : ℕ} {Ω : Opens (ComplexModel n)} {u : ComplexModel n → ℝ}

private theorem leviForm_nonneg_of_coordinateHessian {z : ComplexModel n} {v : ComplexModel n}
    (hu : ContDiffAt ℝ 2 u z)
    (hH : (PshLines.FirstPass.MongeAmpere.complexHessian u z).PosSemidef) :
    0 ≤ PshLines.leviForm u z v := by
  let a : Fin n → ℂ := fun j => star (v j)
  have h := complexHessian_dotProduct_mulVec_eq_leviForm hu a
  let w : ComplexModel n := ∑ j, ((a j).re • coordinateVector j -
    (a j).im • (Complex.I • coordinateVector j))
  change star a ⬝ᵥ ((PshLines.FirstPass.MongeAmpere.complexHessian u z).mulVec a) =
    (PshLines.leviForm u z w : ℂ) at h
  have hw : w = v := by
    ext i
    simp [w, a, coordinateVector, Pi.single_apply, mul_ite, Complex.real_smul]
  have hnonneg := hH.dotProduct_mulVec_nonneg a
  rw [h, hw] at hnonneg
  simpa only [Complex.ofReal_re] using (Complex.nonneg_iff.mp hnonneg).1

/-- A smooth real potential with positive semidefinite coordinate Hessian
is plurisubharmonic on the open domain. -/
theorem isSmoothPshOn_of_coordinateHessian
    (hu : ContDiffOn ℝ ∞ u Ω)
    (hH : ∀ z ∈ Ω, (PshLines.FirstPass.MongeAmpere.complexHessian u z).PosSemidef) :
    IsSmoothPshOn Ω u := by
  refine ⟨hu, ?_, hH⟩
  intro x hx
  obtain ⟨g, hg, heq⟩ := exists_contDiff_eventuallyEq_of_contDiffOn Ω.isOpen hu hx
  have hmem : {y | u y = g y} ∩ (Ω : Set (ComplexModel n)) ∈ 𝓝 x :=
    inter_mem heq (Ω.isOpen.mem_nhds hx)
  obtain ⟨V, hVsub, hV, hxV⟩ := _root_.mem_nhds_iff.mp hmem
  have hlevi (y : ComplexModel n) (hy : y ∈ V) (v : ComplexModel n) :
      0 ≤ PshLines.leviForm g y v := by
    have he : u =ᶠ[𝓝 y] g := by
      filter_upwards [hV.mem_nhds hy] with t ht
      exact (hVsub ht).1
    have h2 : ContDiffAt ℝ 2 u y := ((hu y (hVsub hy).2).contDiffAt
      (Ω.isOpen.mem_nhds (hVsub hy).2)).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
    have hn := leviForm_nonneg_of_coordinateHessian (v := v) h2 (hH y (hVsub hy).2)
    simpa only [PshLines.leviForm, PshLines.realHessian_eq_fderiv, he.fderiv.fderiv_eq] using hn
  have hgP : PlurisubharmonicOn (fun y => (g y : EReal)) V :=
    plurisubharmonicOn_of_levi_nonneg (hg.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) hV hlevi
  exact (hgP x hxV).congr (heq.symm.fun_comp (fun t : ℝ => (t : EReal)))

end KEBall.BedfordTaylor
