import KEBall.DirichletPrescribedDensitySolvable
import KEBall.MoserTrudingerWeakGibbsExtension

/-! Unconditional variational bounds and an actual continuous weak Gibbs maximizer. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 900000
open Filter MeasureTheory Metric Set
open scoped ENNReal Topology
namespace KEBall.MoserTrudinger
open BedfordTaylor Cegrell
open PshLines.FirstPass (ComplexModel)

theorem exists_finiteEnergyFunctional_bound_unconditional
    (n : ℕ) (hn : 0<n) (γ : ℝ) (hγ : 0<γ) (hγn : γ<(n+1 : ℝ)) :
    ∃ C : ℝ, ∀ (u : ComplexModel n → EReal) (hu : IsE1 (complexUnitBall n) u),
      finiteEnergyFunctional γ hu ≤ (C : EReal) :=
  exists_finiteEnergyFunctional_bound_of_smoothGibbs
    (fun d α hd _ _ => smoothGibbsDirichletSolvable_unconditional (by omega) α)
    n hn γ hγ hγn

theorem exists_finiteEnergyFunctional_maximizer_unconditional {n : ℕ} (hn : 0<n)
    {γ : ℝ} (hγ : 0<γ) (hγn : γ<(n+1 : ℝ)) :
    ∃ (v : ComplexModel n → EReal) (hv : IsE1 (complexUnitBall n) v),
      ∀ {u : ComplexModel n → EReal} (hu : IsE1 (complexUnitBall n) u),
        finiteEnergyFunctional γ hu ≤ finiteEnergyFunctional γ hv :=
  exists_finiteEnergyFunctional_maximizer_of_smoothGibbs hn hγ hγn
    (fun d α hd _ _ => smoothGibbsDirichletSolvable_unconditional (by omega) α)

theorem exists_weakGibbs_maximizer_unconditional {n : ℕ} (hn : 2≤n)
    {γ : ℝ} (hγ : 0<γ) (hγn : γ<(n+1 : ℝ)) :
    ∃ v : E n → ℝ, ∃ hv : IsWeakGibbsSolution n γ v,
      ∀ {u : ComplexModel n → EReal} (hu : IsE1 (complexUnitBall n) u),
        finiteEnergyFunctional γ hu ≤ finiteEnergyFunctional γ hv.memE0.isE1 := by
  let β := (γ+(n+1 : ℝ))/2
  have hγβ : γ<β := by dsimp [β]; linarith only [hγn]
  have hβn : β<(n+1 : ℝ) := by dsimp [β]; linarith only [hγn]
  obtain ⟨C,hC⟩ := exists_finiteEnergyFunctional_bound_unconditional n (by omega) β
    (hγ.trans hγβ) hβn
  exact exists_weakGibbs_maximizer_of_smoothGibbs (by omega) hγ hγβ
    (fun hu => hC _ hu) (smoothGibbsDirichletSolvable_unconditional hn γ)

end KEBall.MoserTrudinger
