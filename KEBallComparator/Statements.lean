import KEBall.PaperSpecification20261016
import KEBall.CegrellExponential

/-!
# Comparator propositions for the final manuscript

This module fixes the manuscript statements independently of the endpoint
proofs. In particular the inequality and attainment quantify over the
actual Cegrell class and use its Bedford–Taylor energy.
-/

set_option autoImplicit false

open MeasureTheory Set TopologicalSpace
open scoped ENNReal

namespace KEBallComparator

open KEBall KEBall.BedfordTaylor KEBall.Cegrell KEBall.MoserTrudinger
open PshLines.FirstPass (ComplexModel)
open PshLines.FirstPass.MongeAmpere (IsSmoothPshOn)

def PositiveRootsStatement : Prop :=
  ∀ n : ℕ, 2 ≤ n →
    (∀ s : ℝ, 0 < s →
      boundaryPolynomial n s ≤ criticalCoefficient n ∧
      (boundaryPolynomial n s = criticalCoefficient n ↔ s = (n : ℝ))) ∧
    ∀ μ : ℝ, 0 < μ → μ < criticalCoefficient n →
      (∃ a c : ℝ, 0 < a ∧ a < (n : ℝ) ∧ (n : ℝ) < c ∧ c < (n + 1 : ℝ) ∧
        boundaryPolynomial n a = μ ∧ boundaryPolynomial n c = μ ∧
        ∀ s : ℝ, 0 < s → (boundaryPolynomial n s = μ ↔ s = a ∨ s = c)) ∧
      (∃ b d : ℝ, 0 < b ∧ b < (n : ℝ) ∧ (n : ℝ) < d ∧
        radialCoefficient n b = μ ∧ radialCoefficient n d = μ ∧
        ∀ t : ℝ, 0 < t → (radialCoefficient n t = μ ↔ t = b ∨ t = d))

def SmoothCompatibilityStatement : Prop :=
  ∀ (n : ℕ) (u : E n → ℝ)
    (hu : IsSmoothPshOn (complexUnitBall n) (u ∘ (complexCoordinates n).symm)),
    topMeasure (isLocallyBoundedPshOn_of_isSmoothPshOn hu) =
      Measure.map (complexCoordinates n) ((d0TopMeasure u).restrict (unitBall n))

noncomputable def criticalEnergyCoefficient (n : ℕ) : ℝ :=
  ((n + 1 : ℝ) ^ (n + 1))⁻¹

noncomputable def harmonicNumber (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range n, (1 : ℝ) / (j + 1)

def SubcriticalAttainmentStatement : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ γ ∈ Ioo (0 : ℝ) (n + 1 : ℝ),
    ∃ v : E n → ℝ, Paper20261016.IsMeanFieldSolution n γ v ∧
      ∃ hv : IsE1 (complexUnitBall n) (fun x => (v ((complexCoordinates n).symm x) : EReal)),
        ∀ (u : ComplexModel n → EReal) (hu : IsE1 (complexUnitBall n) u),
          finiteEnergyFunctional γ hu ≤ finiteEnergyFunctional γ hv

def CriticalInequalityStatement : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∀ (u : ComplexModel n → EReal) (hu : IsE1 (complexUnitBall n) u),
    exponentialIntegral 1 u < ⊤ ∧
    Real.log (exponentialIntegral 1 u).toReal ≤
      criticalEnergyCoefficient n * (energy hu).toReal + harmonicNumber n

def OptimalEnergyCoefficientStatement : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ c : ℝ, c < criticalEnergyCoefficient n → ∀ C : ℝ,
    ∃ u : ComplexModel n → EReal, ∃ hu : IsE1 (complexUnitBall n) u,
      exponentialIntegral 1 u < ⊤ ∧
        c * (energy hu).toReal + C < Real.log (exponentialIntegral 1 u).toReal

def OptimalAdditiveConstantStatement : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ C : ℝ,
    (∀ (u : ComplexModel n → EReal) (hu : IsE1 (complexUnitBall n) u),
      exponentialIntegral 1 u < ⊤ ∧
      Real.log (exponentialIntegral 1 u).toReal ≤
        criticalEnergyCoefficient n * (energy hu).toReal + C) →
    harmonicNumber n ≤ C

end KEBallComparator
