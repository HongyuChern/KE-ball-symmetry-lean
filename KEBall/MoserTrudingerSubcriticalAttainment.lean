import KEBall.MoserTrudingerGibbsBoundarySmooth
import KEBall.MoserTrudingerSmoothToFiniteEnergy

/-! Attainment over the entire actual Cegrell E1 class. Smooth inverse
iteration, boundary regularity and classification bound each smooth
competitor by the same canonical potential, followed by E1 approximation. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 900000

open Filter MeasureTheory Metric Set TopologicalSpace
open scoped ComplexOrder ContDiff ENNReal Topology

namespace KEBall.MoserTrudinger
open BedfordTaylor Cegrell
open PshLines.FirstPass (ComplexModel)

theorem subcriticalSmoothAttainment_unconditional {n : ℕ} (hn : 2 ≤ n) :
    SubcriticalSmoothAttainment n := by
  intro γ hγ
  have hn0 : 0 < n := by omega
  let w := normalizedPotential n γ
  have hw : Paper20261016.IsMeanFieldSolution n γ w :=
    (Paper20261016.meanField_iff_normalized n γ w).mpr
      (normalizedPotential_isNormalizedSolution hn hγ.1 hγ.2)
  let hE := meanFieldSolution_memE0 hw
  let C : ℝ := Real.log (normalizingIntegral γ w) / γ - smoothEnergy w / (n + 1 : ℝ)
  have hCF : finiteEnergyFunctional γ hE.isE1 = (C : EReal) :=
    finiteEnergyFunctional_realModelPotential hn0 hw.2.1 hE γ
  refine ⟨w, hw, ?_⟩
  intro u hu
  refine (finiteEnergyFunctional_le_of_smooth_bound hn0 hγ.1 ?_ hu).trans_eq hCF.symm
  intro q hq hqC hqP
  let e := complexCoordinates n
  let p := q ∘ e
  have hpC : ContDiff ℝ ∞ p := hqC.comp e.toContinuousLinearEquiv.contDiff
  have hp0 (x : E n) (hx : x ∈ unitSphere n) : p x = 0 := by
    let B := (complexUnitBall n : Set (ComplexModel n))
    have hz : e x ∈ frontier B := by
      change e x ∈ frontier (ball (0 : ComplexModel n) 1)
      rw [frontier_ball _ one_ne_zero, mem_sphere_zero_iff_norm, e.norm_map]
      exact mem_sphere_zero_iff_norm.mp hx
    let : NeBot (𝓝[B] e x) := mem_closure_iff_nhdsWithin_neBot.mp (frontier_subset_closure hz)
    exact tendsto_nhds_unique (hqC.continuous.continuousWithinAt (s := B) (x := e x)) (hq.boundary _ hz)
  have hqEq : p ∘ e.symm = q := by
    funext x
    simp only [p, Function.comp_apply, LinearIsometryEquiv.apply_symm_apply]
  have hpP (x : E n) (hx : x ∈ unitBall n) : (complexHessian p x).PosDef := by
    have hx' : e x ∈ complexUnitBall n := by
      change x ∈ e ⁻¹' (complexUnitBall n : Set (ComplexModel n))
      simpa only [e, preimage_complexUnitBall] using hx
    rw [← complexHessian_coordinates hpC.contDiffAt, hqEq]
    exact hqP _ hx'
  have hBound := smoothFunctional_le_normalized_subcritical hn hγ.1 hγ.2 hpC hp0 hpP
  change (smoothFunctional γ p : EReal) ≤ finiteEnergyFunctional γ hE.isE1 at hBound
  rw [hCF] at hBound
  have hpNear : SmoothNear (closedUnitBall n) p := ⟨univ, isOpen_univ, subset_univ _, hpC.contDiffOn⟩
  have hpE0 : IsE0 (complexUnitBall n) (p ∘ e.symm) := hqEq.symm ▸ hq
  have hEqF : finiteEnergyFunctional γ hq.isE1 = finiteEnergyFunctional γ hpE0.isE1 := by
    congr 1
    exact congrArg (fun v : ComplexModel n → ℝ => fun x => (v x : EReal)) hqEq.symm
  rw [hEqF, finiteEnergyFunctional_realModelPotential hn0 hpNear hpE0 γ]
  rw [smoothFunctional, signedSmoothEnergy_eq isOpen_univ hpC.contDiffOn (subset_univ _) hpP] at hBound
  simpa only [neg_div, sub_eq_add_neg, add_comm] using hBound

end KEBall.MoserTrudinger
