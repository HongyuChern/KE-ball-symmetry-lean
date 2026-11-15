import KEBallComparator.Statements
import KEBall.PaperFormalization20261016
import KEBall.MoserTrudingerFiniteEnergy
import KEBall.MoserTrudingerSubcriticalAttainment

/-! Bind the independent challenge propositions to the kernel-checked proofs. -/

set_option autoImplicit false

namespace KEBallComparator.Targets

open KEBall KEBall.BedfordTaylor KEBall.MoserTrudinger

theorem smoothPaper : Paper20261016.CurrentPaperStatement :=
  Paper20261016.currentPaper

theorem positiveRoots : PositiveRootsStatement := by
  intro n hn
  have hn₁ : 1 ≤ n := by omega
  refine ⟨fun s hs => ⟨boundaryPolynomial_le_critical_of_nonneg hn₁ hs.le,
    boundaryPolynomial_critical hn₁ hs⟩, ?_⟩
  intro μ hμ hμc
  exact ⟨boundaryPolynomial_subcritical hn₁ hμ hμc, radialCoefficient_subcritical hn₁ hμ hμc⟩

theorem smoothCompatibility : SmoothCompatibilityStatement :=
  fun _ _ hu => topMeasure_eq_map_d0TopMeasure_unitBall hu

theorem optimalEnergyCoefficient : OptimalEnergyCoefficientStatement :=
  fun _ hn _ hc C => finiteEnergy_counterexample_of_lt_energyCoefficient hn hc C

theorem optimalAdditiveConstant : OptimalAdditiveConstantStatement :=
  fun _ hn _ h => harmonicConstant_le_of_finiteEnergy_bound hn (fun hu => (h _ hu).2)

theorem subcriticalAttainment : SubcriticalAttainmentStatement := by
  intro n hn γ hγ
  obtain ⟨v, hv, hMax⟩ := subcriticalSmoothAttainment_unconditional hn γ hγ
  exact ⟨v, hv, (meanFieldSolution_memE0 hv).isE1, fun _ hu => hMax hu⟩

theorem criticalInequality : CriticalInequalityStatement := by
  intro n hn u hu
  exact critical_bound_of_subcriticalSmoothAttainment hn
    (subcriticalSmoothAttainment_unconditional hn) hu

end KEBallComparator.Targets
