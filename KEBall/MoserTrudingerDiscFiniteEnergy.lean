import KEBall.MoserTrudingerDisc
import KEBall.MoserTrudingerSmoothToFiniteEnergy
import KEBall.MoserTrudingerFiniteEnergyAttainment
import KEBall.CegrellSmoothFunctional

/-!
# Subcritical Moser–Trudinger on the finite-energy disc
-/

set_option autoImplicit false

open Filter Metric Set
open scoped ComplexOrder ContDiff Topology

namespace KEBall.MoserTrudinger

open BedfordTaylor Cegrell
open PshLines.FirstPass (ComplexModel)

private theorem finiteEnergyFunctional_congr_fun {n : ℕ} {u v : ComplexModel n → EReal}
    (he : u = v) (hu : IsE1 (complexUnitBall n) u) (hv : IsE1 (complexUnitBall n) v)
    (γ : ℝ) : finiteEnergyFunctional γ hu = finiteEnergyFunctional γ hv := by
  subst v
  rfl

theorem finiteEnergyFunctional_disc_le {γ : ℝ} (hγ : 0 < γ) (hγ₂ : γ < 2)
    {u : ComplexModel 1 → EReal} (hu : IsE1 (complexUnitBall 1) u) :
    finiteEnergyFunctional γ hu ≤ ((Real.log (16 / (1 - γ / 2)) / γ : ℝ) : EReal) := by
  apply finiteEnergyFunctional_le_of_smooth_bound (by decide : 0 < (1 : ℕ)) hγ _ hu
  intro q hq hqC hqH
  let e := complexCoordinates 1
  let v : E 1 → ℝ := q ∘ e
  have hv : ContDiff ℝ ∞ v := hqC.comp e.toContinuousLinearEquiv.contDiff
  have hvS : SmoothNear (closedUnitBall 1) v :=
    ⟨univ, isOpen_univ, subset_univ _, hv.contDiffOn⟩
  have hEq : v ∘ e.symm = q := by
    funext z
    simp only [v, Function.comp_apply, LinearIsometryEquiv.apply_symm_apply]
  have hvE : IsE0 (complexUnitBall 1) (v ∘ e.symm) := hEq.symm ▸ hq
  have hvH (x : E 1) (hx : x ∈ unitBall 1) : (complexHessian v x).PosDef := by
    have hz : e x ∈ complexUnitBall 1 := by
      change x ∈ e ⁻¹' (complexUnitBall 1 : Set (ComplexModel 1))
      simpa only [e, preimage_complexUnitBall] using hx
    rw [← complexHessian_coordinates hv.contDiffAt, hEq]
    exact hqH _ hz
  have hvZero (x : E 1) (hx : x ∈ unitSphere 1) : v x = 0 := by
    let B := (complexUnitBall 1 : Set (ComplexModel 1))
    have hz : e x ∈ frontier B := by
      change e x ∈ frontier (ball (0 : ComplexModel 1) 1)
      rw [frontier_ball _ one_ne_zero, mem_sphere_zero_iff_norm, e.norm_map]
      exact mem_sphere_zero_iff_norm.mp hx
    let : NeBot (𝓝[B] e x) := mem_closure_iff_nhdsWithin_neBot.mp (frontier_subset_closure hz)
    exact tendsto_nhds_unique (hqC.continuous.continuousWithinAt (s := B) (x := e x))
      (hq.boundary _ hz)
  have hs := smoothFunctional_disc_le isOpen_univ (subset_univ _) hv.contDiffOn hvZero hvH hγ hγ₂
  have he : (fun x => (q x : EReal)) = realModelPotential v := by
    funext x
    exact congrArg (fun a : ℝ => (a : EReal)) (congrFun hEq x).symm
  rw [finiteEnergyFunctional_congr_fun he hq.isE1 hvE.isE1,
    finiteEnergyFunctional_realModelPotential (by decide : 0 < (1 : ℕ)) hvS hvE γ,
    EReal.coe_le_coe_iff]
  rw [smoothFunctional, signedSmoothEnergy_eq isOpen_univ hv.contDiffOn (subset_univ _) hvH,
    neg_div] at hs
  exact (by simpa only [sub_eq_add_neg, add_comm, Nat.cast_one] using hs)

theorem exists_finiteEnergyFunctional_disc_maximizer {γ : ℝ} (hγ : 0 < γ) (hγ₂ : γ < 2) :
    ∃ (v : ComplexModel 1 → EReal) (hv : IsE1 (complexUnitBall 1) v),
      ∀ {u : ComplexModel 1 → EReal} (hu : IsE1 (complexUnitBall 1) u),
        finiteEnergyFunctional γ hu ≤ finiteEnergyFunctional γ hv := by
  let β := (γ + 2) / 2
  have hγβ : γ < β := by dsimp [β]; linarith
  have hβ₂ : β < 2 := by dsimp [β]; linarith
  exact exists_finiteEnergyFunctional_maximizer_of_bound (by decide : 0 < (1 : ℕ)) hγ hγβ
    (fun hu => finiteEnergyFunctional_disc_le (hγ.trans hγβ) hβ₂ hu)

end KEBall.MoserTrudinger
