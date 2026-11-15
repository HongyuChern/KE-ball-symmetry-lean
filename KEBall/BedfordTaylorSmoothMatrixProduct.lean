import KEBall.BedfordTaylorMatrixProductRule
import KEBall.BedfordTaylorAffineHessian

/-!
# Smooth mixed products in all dimensions
-/

set_option autoImplicit false

open Set TopologicalSpace
open scoped ContDiff Distributions

namespace KEBall.BedfordTaylor

open KEBallProbe
open PshLines.FirstPass (ComplexModel)
open PshLines.FirstPass.MongeAmpere (complexHessian coordinateVector IsLocallyBoundedPshOn IsSmoothPshOn)

variable {n k : ℕ} {Ω : Opens (ComplexModel n)}

theorem classicalComplexHessianEntry_coordinate_eq {u : ComplexModel n → ℝ}
    {x : ComplexModel n} (hu : ContDiffAt ℝ ∞ u x) (i j : Fin n) :
    classicalComplexHessianEntry u (coordinateVector i) (coordinateVector j) x =
      complexHessian u x i j := by
  rw [classicalComplexHessianEntry_eq_realHessian hu]
  rfl

/-- Densities of the classical mixed product, with separate ordered
row and column tuples. -/
noncomputable def smoothMixedDensities (n : ℕ) :
    (k : ℕ) → (Fin k → ComplexModel n → ℝ) → CoordinateDensities n k k
  | 0, _ => Matrix.of fun _ _ _ => 1
  | k + 1, u => smoothHessianWedge (u 0) (smoothMixedDensities n k (Fin.tail u))

theorem contDiffOn_smoothMixedDensities (u : Fin k → ComplexModel n → ℝ)
    (hu : ∀ r, ContDiffOn ℝ ∞ (u r) Ω) (I J : CoordinateTuple n k) :
    ContDiffOn ℝ ∞ (smoothMixedDensities n k u I J) Ω := by
  induction k with
  | zero => exact contDiffOn_const
  | succ k ih =>
    exact contDiffOn_smoothHessianWedge _ (fun I J => ih (Fin.tail u)
      (fun r => hu r.succ) I J) (hu 0) I J

theorem smoothMixedDensities_eq_mixedMinor (u : Fin k → ComplexModel n → ℝ)
    (I J : CoordinateTuple n k) (x : ComplexModel n) :
    smoothMixedDensities n k u I J x = mixedMinorMatrix k
      (fun r => Matrix.of fun i j =>
        classicalComplexHessianEntry (u r) (coordinateVector i) (coordinateVector j) x) I J := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [smoothMixedDensities, smoothHessianWedge, Matrix.of_apply, mixedMinorMatrix_succ,
      ih (Fin.tail u), Fin.tail]
    rfl

theorem smoothMixedDensities_isPositive (u : Fin k → ComplexModel n → ℝ)
    (hu : ∀ r, IsSmoothPshOn Ω (u r)) :
    IsPositiveMatrixDistribution
      (matrixOfDensities (smoothMixedDensities n k u)
        (contDiffOn_smoothMixedDensities u (fun r => (hu r).1))) := by
  apply matrixOfDensities_isPositive
  intro x hx
  have heq : (Matrix.of fun I J => smoothMixedDensities n k u I J x) = mixedMinorMatrix k
      (fun r => Matrix.of fun i j =>
        classicalComplexHessianEntry (u r) (coordinateVector i) (coordinateVector j) x) := by
    ext I J : 1
    exact smoothMixedDensities_eq_mixedMinor u I J x
  rw [heq]
  exact mixedMinorMatrix_posSemidef (fun r =>
    posSemidef_classicalComplexHessianEntry (hu r) hx coordinateVector)

/-- One Bedford–Taylor recursion step on a positive coefficient
matrix. The result is closed by commutation of distribution derivatives. -/
noncomputable def mixedProductStep {u : ComplexModel n → ℝ}
    (hu : IsLocallyBoundedPshOn Ω u)
    {T : CoordinateDistributions Ω k k} (hT : IsPositiveMatrixDistribution T) :
    CoordinateDistributions Ω (k + 1) (k + 1) :=
  coordinateRowDerivative (coordinateColumnDerivative (weightPositiveMatrixDistribution hu hT))

theorem mixedProductStep_rowClosed {u : ComplexModel n → ℝ}
    (hu : IsLocallyBoundedPshOn Ω u)
    {T : CoordinateDistributions Ω k k} (hT : IsPositiveMatrixDistribution T) :
    coordinateRowDerivative (mixedProductStep hu hT) = 0 :=
  coordinateRowDerivative_sq _

theorem mixedProductStep_colClosed {u : ComplexModel n → ℝ}
    (hu : IsLocallyBoundedPshOn Ω u)
    {T : CoordinateDistributions Ω k k} (hT : IsPositiveMatrixDistribution T) :
    coordinateColumnDerivative (mixedProductStep hu hT) = 0 := by
  rw [mixedProductStep, ← coordinateExteriorDerivatives_comm,
    coordinateColumnDerivative_sq, coordinateRowDerivative_zero]

theorem mixedProductStep_eq_smooth (u : Fin (k + 1) → ComplexModel n → ℝ)
    (hu : ∀ r, IsSmoothPshOn Ω (u r))
    (hr : coordinateRowDerivative (matrixOfDensities (smoothMixedDensities n k (Fin.tail u))
      (contDiffOn_smoothMixedDensities (Fin.tail u) (fun r => (hu r.succ).1))) = 0)
    (hc : coordinateColumnDerivative (matrixOfDensities (smoothMixedDensities n k (Fin.tail u))
      (contDiffOn_smoothMixedDensities (Fin.tail u) (fun r => (hu r.succ).1))) = 0) :
    mixedProductStep (isLocallyBoundedPshOn_of_isSmoothPshOn (hu 0))
        (smoothMixedDensities_isPositive (Fin.tail u) (fun r => hu r.succ)) =
      matrixOfDensities (smoothMixedDensities n (k + 1) u)
        (contDiffOn_smoothMixedDensities u (fun r => (hu r).1)) := by
  let g := smoothMixedDensities n k (Fin.tail u)
  have hg : ∀ I J, ContDiffOn ℝ ∞ (g I J) Ω :=
    contDiffOn_smoothMixedDensities (Fin.tail u) (fun r => (hu r.succ).1)
  have hrow : ∀ I J, EqOn (coordinateRowDensity g I J) 0 Ω := by
    have hr' : coordinateRowDerivative (matrixOfDensities g hg) = 0 := hr
    rw [coordinateRowDerivative_of_densities, ← matrixOfDensities_zero] at hr'
    exact matrixOfDensities_eqOn_of_eq _ _ hr'
  have hcol : ∀ I J, EqOn (coordinateColumnDensity g I J) 0 Ω := by
    have hc' : coordinateColumnDerivative (matrixOfDensities g hg) = 0 := hc
    rw [coordinateColumnDerivative_of_densities, ← matrixOfDensities_zero] at hc'
    exact matrixOfDensities_eqOn_of_eq _ _ hc'
  let w : CoordinateDensities n k k := Matrix.of fun I J x => (u 0 x : ℂ) * g I J x
  have hw : ∀ I J, ContDiffOn ℝ ∞ (w I J) Ω :=
    fun I J => (Complex.ofRealCLM.contDiff.comp_contDiffOn (hu 0).1).mul (hg I J)
  unfold mixedProductStep
  rw [weightPositiveMatrixDistribution_of_densities (hu 0) g hg,
    coordinateColumnDerivative_of_densities w hw,
    coordinateRowDerivative_of_densities (coordinateColumnDensity w)
      (contDiffOn_coordinateColumnDensity w hw)]
  exact matrixOfDensities_congr _ _ (coordinateRowColumnDensity_mul_eqOn_wedge g hg (hu 0).1 hrow hcol)

theorem smoothMixedDensities_closed (u : Fin k → ComplexModel n → ℝ)
    (hu : ∀ r, IsSmoothPshOn Ω (u r)) :
    let T := matrixOfDensities (smoothMixedDensities n k u)
        (contDiffOn_smoothMixedDensities u (fun r => (hu r).1))
    coordinateRowDerivative T = 0 ∧ coordinateColumnDerivative T = 0 := by
  induction k with
  | zero =>
    dsimp only
    constructor
    · rw [coordinateRowDerivative_of_densities, ← matrixOfDensities_zero]
      apply matrixOfDensities_congr
      intro I J x hx
      simp [coordinateRowDensity, smoothMixedDensities, dz, rd]
    · rw [coordinateColumnDerivative_of_densities, ← matrixOfDensities_zero]
      apply matrixOfDensities_congr
      intro I J x hx
      simp [coordinateColumnDensity, smoothMixedDensities, dz, rd]
  | succ k ih =>
    dsimp only
    have h := ih (Fin.tail u) (fun r => hu r.succ)
    rw [← mixedProductStep_eq_smooth u hu h.1 h.2]
    exact ⟨mixedProductStep_rowClosed _ _, mixedProductStep_colClosed _ _⟩

end KEBall.BedfordTaylor
