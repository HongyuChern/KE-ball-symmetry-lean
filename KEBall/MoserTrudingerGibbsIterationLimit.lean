import KEBall.MoserTrudingerGibbsIteration
import Mathlib.Topology.Order.MonotoneConvergence

/-! Finite convergence of the original functional along actual Gibbs iterates. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
open Filter MeasureTheory Metric Set
open scoped ComplexOrder ContDiff ENNReal Topology
namespace KEBall.MoserTrudinger
open BedfordTaylor Cegrell

theorem finiteEnergyFunctional_eq_smoothFunctional {n : ℕ} (hn : 0<n) (γ : ℝ)
    {u : E n → ℝ} (hu : ContDiff ℝ ∞ u)
    (huP : ∀ x∈unitBall n, (complexHessian u x).PosDef)
    (hE : IsE0 (complexUnitBall n) (u ∘ (complexCoordinates n).symm)) :
    finiteEnergyFunctional γ hE.isE1=(smoothFunctional γ u : EReal) := by
  have hNear : SmoothNear (closedUnitBall n) u :=
    ⟨univ,isOpen_univ,subset_univ _,hu.contDiffOn⟩
  rw [finiteEnergyFunctional_realModelPotential hn hNear hE,smoothFunctional,
    signedSmoothEnergy_eq isOpen_univ hu.contDiffOn (subset_univ _) huP,neg_div]
  congr 1
  ring

theorem exists_smoothFunctional_limit_of_gibbsIteration {n : ℕ} (hn : 0<n)
    {γ : ℝ} (hγ : 0<γ) (hγn : γ<(n+1 : ℝ))
    {u : ℕ → E n → ℝ} (hu : ∀ j, ContDiff ℝ ∞ (u j))
    (hu0 : ∀ j x, x∈unitSphere n → u j x=0)
    (huP : ∀ j x, x∈unitBall n → (complexHessian (u j) x).PosDef)
    (hEq : ∀ j x, x∈unitBall n →
      (complexHessian (u (j+1)) x).det.re=gibbsDensity γ (u j) x) :
    ∃ m : ℝ, Tendsto (fun j => smoothFunctional γ (u j)) atTop (𝓝 m) ∧
      (∀ j, smoothFunctional γ (u j)≤m) ∧
      Tendsto (fun j => smoothFunctional γ (u (j+1))-smoothFunctional γ (u j))
        atTop (𝓝 0) := by
  have hMono : Monotone (fun j => smoothFunctional γ (u j)) :=
    monotone_nat_of_le_succ fun j => smoothFunctional_le_of_gibbs_step hn
      isOpen_univ (subset_univ _) (hu j).contDiffOn (hu (j+1)).contDiffOn
      (hu0 j) (hu0 (j+1)) (huP j) (huP (j+1)) hγ (hEq j)
  obtain ⟨C,hC⟩ := exists_finiteEnergyFunctional_bound_unconditional n hn γ hγ hγn
  have hUpper (j : ℕ) : smoothFunctional γ (u j)≤C := by
    have hNear : SmoothNear (closedUnitBall n) (u j) :=
      ⟨univ,isOpen_univ,subset_univ _,(hu j).contDiffOn⟩
    have hE := isE0_onBall_of_smooth_real_model hNear
      (fun x hx => (huP j x hx).posSemidef) (hu0 j)
    have h := hC _ hE.isE1
    rw [finiteEnergyFunctional_eq_smoothFunctional hn γ (hu j) (huP j) hE,
      EReal.coe_le_coe_iff] at h
    exact h
  have hBdd : BddAbove (range (fun j => smoothFunctional γ (u j))) :=
    ⟨C,fun _ ⟨j,hj⟩ => hj ▸ hUpper j⟩
  let m := ⨆ j, smoothFunctional γ (u j)
  have hLim : Tendsto (fun j => smoothFunctional γ (u j)) atTop (𝓝 m) :=
    tendsto_atTop_ciSup hMono hBdd
  refine ⟨m,hLim,fun j => le_ciSup hBdd j,?_⟩
  have hSucc := hLim.comp (tendsto_add_atTop_nat 1)
  simpa only [Function.comp_apply,sub_self] using hSucc.sub hLim

end KEBall.MoserTrudinger
