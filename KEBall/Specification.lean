import KEBall.Domain
import KEBall.SphereMeasure

/-!
# Frozen whole-paper specifications

These are propositions to be proved, not assumed theorems. Defining or
compiling a specification does not prove it. No implementation imports a
proof of a specification, and there are no axioms or admitted proofs here.

All objects below are defined from the concrete derivatives, Euclidean
metric, and actual normalized measures. Counting is on closed-ball
restrictions. The differential-form identification for D0 is a separate
obligation: the normalized specification here is the determinant equation.
-/

set_option autoImplicit false
open MeasureTheory Set
open scoped ContDiff BigOperators ComplexOrder

namespace KEBall

noncomputable def euclideanGradient {n : ℕ} (h : E n → ℝ) (x : E n) : E n :=
  ∑ i : Fin (2 * n),
    (fderiv ℝ h x (EuclideanSpace.single i 1)) • EuclideanSpace.single i 1

noncomputable def horizontalGradient {n : ℕ} (h : E n → ℝ) (x : E n) : E n :=
  euclideanGradient h x -
    (inner ℝ (euclideanGradient h x) x) • x -
    (inner ℝ (euclideanGradient h x) (J x)) • J x

noncomputable def conormalDerivative {n : ℕ} (u h : E n → ℝ) (x : E n) : ℝ :=
  fderiv ℝ h x x -
    inner ℝ (horizontalGradient (boundarySlope u) x) (horizontalGradient h x) /
      (2 * boundarySlope u x)

noncomputable def expWeight {n : ℕ} (u : E n → ℝ) (x : E n) : ℝ :=
  Real.exp (-u x / (n + 1 : ℝ))

noncomputable def auxiliaryP {n : ℕ} (u : E n → ℝ) (x : E n) : ℝ :=
  expWeight u x * (1 + gradientNormSq u x / (n + 1 : ℝ))

noncomputable def auxiliaryW {n : ℕ} (u : E n → ℝ) (x : E n) : ℝ :=
  Real.log (auxiliaryP u x - 1)

/-- Coordinate formula for the (2,0) covariant Hessian. Its identification
with the constructed real Levi-Civita connection remains a proof obligation. -/
noncomputable def covariantHessian20 {n : ℕ} (u : E n → ℝ) (x : E n)
    (i j : Fin n) : ℂ :=
  partialZ i (partialZ j (fun y => (u y : ℂ))) x -
    ∑ k : Fin n, ∑ l : Fin n, inverseCoefficient u x k l *
      partialZ i (fun y => complexHessian u y j l) x *
      partialZ k (fun y => (u y : ℂ)) x

/-- Theorem 1.1, forward classification. -/
def ClassificationStatement : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∀ (μ : ℝ) (u : E n → ℝ), IsSolution n μ u →
    ∃ b : ℝ, 0 < b ∧ Set.EqOn u (radialPotential n b) (closedUnitBall n) ∧
      μ = radialCoefficient n b

/-- Theorem 1.1, the necessary converse. -/
def RadialExistenceStatement : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∀ b : ℝ, 0 < b →
    IsSolution n (radialCoefficient n b) (radialPotential n b)

/-- Theorem 1.1, all three exact counting branches. -/
def SolutionCountsStatement : Prop :=
  ∀ (n : ℕ), 2 ≤ n →
    (∀ μ : ℝ, 0 < μ → μ < criticalCoefficient n →
      ∃ v w : ClosedBall n → ℝ, v ≠ w ∧ solutionSet n μ = {v, w}) ∧
    (∃! v : ClosedBall n → ℝ, v ∈ solutionSet n (criticalCoefficient n)) ∧
    (∀ μ : ℝ, criticalCoefficient n < μ → solutionSet n μ = ∅)

/-- Lemma 2.1, including the nonzero boundary flux for every smooth test. -/
def BoundaryIdentitiesStatement : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∀ (μ : ℝ) (u : E n → ℝ), IsSolution n μ u →
    ((∫ x in unitBall n, (complexHessian u x).det.re ∂volume0 n) =
      ∫ x : Sphere n, (boundarySlope u x.1) ^ n ∂sphere0 n) ∧
    ((∫ x : Sphere n, boundaryPolynomial n (boundarySlope u x.1) ∂sphere0 n) = μ) ∧
    (∀ h : E n → ℝ, SmoothNear (closedUnitBall n) h →
      (∫ x in unitBall n, complexLaplacian u h x * (complexHessian u x).det.re
        ∂volume0 n) =
      (n : ℝ) / 2 * ∫ x : Sphere n,
        (boundarySlope u x.1) ^ (n - 1) * conormalDerivative u h x.1 ∂sphere0 n)

/-- Lemma 2.2, with the smaller scalar root explicitly characterized. -/
def LowerSlopeStatement : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∀ (μ a : ℝ) (u : E n → ℝ),
    IsSolution n μ u → μ < criticalCoefficient n →
    0 < a → a < (n : ℝ) → boundaryPolynomial n a = μ →
    ∀ x ∈ unitSphere n, a ≤ boundarySlope u x

/-- Proposition 3.1, positivity, exact flux and its equality consequence. -/
def LogarithmicFluxStatement : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∀ (μ : ℝ) (u : E n → ℝ), IsSolution n μ u →
    (∀ x ∈ closedUnitBall n, 1 < auxiliaryP u x) ∧
    (∀ x ∈ unitBall n, 0 ≤ complexLaplacian u (auxiliaryW u) x) ∧
    ((∫ x in unitBall n, complexLaplacian u (auxiliaryW u) x *
        (complexHessian u x).det.re ∂volume0 n) =
      -(n : ℝ) ^ 2 *
        ((∫ x : Sphere n,
            (boundaryPolynomial n (boundarySlope u x.1) - μ) / boundarySlope u x.1
              ∂sphere0 n) +
         1 / 4 * ∫ x : Sphere n,
            horizontalFluxWeight n (boundarySlope u x.1) *
              ‖horizontalGradient (boundarySlope u) x.1‖ ^ 2 ∂sphere0 n)) ∧
    (((∫ x in unitBall n, complexLaplacian u (auxiliaryW u) x *
        (complexHessian u x).det.re ∂volume0 n) = 0) →
      ∀ x ∈ unitBall n, ∀ i j : Fin n,
        covariantHessian20 u x i j = (n + 1 : ℂ)⁻¹ *
          partialZ i (fun y => (u y : ℂ)) x * partialZ j (fun y => (u y : ℂ)) x)

def IsNormalizedSolution (n : ℕ) (γ : ℝ) (φ : E n → ℝ) : Prop :=
  0 < γ ∧ SmoothNear (closedUnitBall n) φ ∧
  (∀ x ∈ unitBall n, (complexHessian φ x).PosDef) ∧
  (∀ x ∈ unitSphere n, φ x = 0) ∧
  (∀ x ∈ unitBall n, (complexHessian φ x).det =
    (Real.exp (-γ * φ x) /
      (∫ y in unitBall n, Real.exp (-γ * φ y) ∂volume0 n) : ℂ))

def normalizedSolutionSet (n : ℕ) (γ : ℝ) : Set (ClosedBall n → ℝ) :=
  {v | ∃ φ : E n → ℝ, IsNormalizedSolution n γ φ ∧ restrictClosedBall φ = v}

noncomputable def normalizedPotential (n : ℕ) (γ : ℝ) (x : E n) : ℝ :=
  (n + 1 : ℝ) / γ *
    Real.log (1 - γ / (n + 1 : ℝ) + γ / (n + 1 : ℝ) * ‖x‖ ^ 2)

/-- Corollary 4.1 at determinant level, with explicit existence and uniqueness. -/
def NormalizedClassificationStatement : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∀ γ : ℝ, 0 < γ →
    (γ < (n + 1 : ℝ) →
      IsNormalizedSolution n γ (normalizedPotential n γ) ∧
      normalizedSolutionSet n γ = {restrictClosedBall (normalizedPotential n γ)}) ∧
    ((n + 1 : ℝ) ≤ γ → normalizedSolutionSet n γ = ∅)

end KEBall
