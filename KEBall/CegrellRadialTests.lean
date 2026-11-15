import KEBall.BedfordTaylorSmoothCriterion
import KEBall.CegrellBallBoundary
import KEBall.MoserTrudingerSmooth

/-!
# The paper's radial tests belong to Cegrell's finite-energy class
-/

set_option autoImplicit false

open Filter MeasureTheory Metric Set TopologicalSpace
open scoped ComplexOrder ContDiff ENNReal Topology

namespace KEBall.MoserTrudinger

open BedfordTaylor Cegrell
open PshLines.FirstPass (ComplexModel)
open PshLines.FirstPass.MongeAmpere (IsSmoothPshOn)

variable {n : ℕ}

theorem isE0_onBall_of_smooth_real_model {u : E n → ℝ}
    (hS : SmoothNear (closedUnitBall n) u)
    (hH : ∀ x ∈ unitBall n, (KEBall.complexHessian u x).PosSemidef)
    (hB : ∀ x ∈ unitSphere n, u x = 0) :
    IsE0 (complexUnitBall n) (u ∘ (complexCoordinates n).symm) := by
  obtain ⟨U, hU, hCU, hSu⟩ := hS
  let e := (complexCoordinates n).symm
  let W : Opens (ComplexModel n) := ⟨e ⁻¹' U, hU.preimage e.continuous⟩
  have hcl : closure (complexUnitBall n : Set (ComplexModel n)) =
      closedBall (0 : ComplexModel n) 1 := closure_ball _ one_ne_zero
  have hW : closure (complexUnitBall n : Set (ComplexModel n)) ⊆ W := by
    rw [hcl]
    intro z hz
    apply hCU
    change dist (e z) 0 ≤ 1
    rw [dist_zero_right, e.norm_map]
    exact mem_closedBall_zero_iff.mp hz
  have hW' : complexUnitBall n ≤ W := subset_closure.trans hW
  have hs : ContDiffOn ℝ ∞ (u ∘ (complexCoordinates n).symm) W :=
    hSu.comp e.toContinuousLinearEquiv.contDiff.contDiffOn (fun _ hx => hx)
  have hpsh : IsSmoothPshOn (complexUnitBall n) (u ∘ (complexCoordinates n).symm) := by
    apply isSmoothPshOn_of_coordinateHessian (hs.mono hW')
    intro z hz
    have hx : e z ∈ unitBall n := by
      change dist (e z) 0 < 1
      rw [dist_zero_right, e.norm_map]
      exact mem_ball_zero_iff.mp hz
    have he : complexCoordinates n (e z) = z := LinearIsometryEquiv.apply_symm_apply _ _
    rw [← he, complexHessian_coordinates (show ContDiffAt ℝ ∞ u (e z) from
      hSu.contDiffAt (hU.mem_nhds (hCU (ball_subset_closedBall hx))))]
    exact hH (e z) hx
  apply isE0_of_smoothOn_closure (hcl.symm ▸ isCompact_closedBall _ _) hW hpsh hs
  intro z hz
  apply hB
  change dist (e z) 0 = 1
  rw [dist_zero_right, e.norm_map]
  change z ∈ frontier (ball (0 : ComplexModel n) 1) at hz
  rw [frontier_ball _ one_ne_zero] at hz
  exact mem_sphere_zero_iff_norm.mp hz

/-- The radial test family for Corollary 1.3 lies in the actual
bounded Bedford–Taylor energy class. -/
theorem testPotential_isE0 (hn : 2 ≤ n) {t : ℝ} (ht₀ : 0 < t) (ht₁ : t < 1) :
    IsE0 (complexUnitBall n) (testPotential n t ∘ (complexCoordinates n).symm) := by
  obtain ⟨hS, hH, hB⟩ := testPotential_admissible hn ht₀ ht₁
  exact isE0_onBall_of_smooth_real_model hS (fun x hx => (hH x hx).posSemidef) hB

theorem testPotential_isE1 (hn : 2 ≤ n) {t : ℝ} (ht₀ : 0 < t) (ht₁ : t < 1) :
    IsE1 (complexUnitBall n) (fun z => (testPotential n t ((complexCoordinates n).symm z) : EReal)) :=
  (testPotential_isE0 hn ht₀ ht₁).isE1

#print axioms testPotential_isE1

end KEBall.MoserTrudinger
