import KEBall.BedfordTaylorExteriorDerivative
import KEBall.BedfordTaylorMixedMinors

/-!
# Exterior derivatives of coordinate coefficient matrices
-/

set_option autoImplicit false

open TopologicalSpace
open scoped Distributions

namespace KEBall.BedfordTaylor

open PshLines.FirstPass (ComplexModel)
open PshLines.FirstPass.MongeAmpere (coordinateVector)

variable {n k l : ℕ} {Ω : Opens (ComplexModel n)}

abbrev CoordinateDistributions (Ω : Opens (ComplexModel n)) (k l : ℕ) :=
  Matrix (CoordinateTuple n k) (CoordinateTuple n l) 𝓓'(Ω, ℂ)

/-- Differentiate the holomorphic row indices of a coordinate matrix. -/
noncomputable def coordinateRowDerivative (T : CoordinateDistributions Ω k l) :
    CoordinateDistributions Ω (k + 1) l :=
  Matrix.of fun I J => alternatingDerivative
    (fun i : Fin n => wirtingerDerivative (coordinateVector i) (Complex.I • coordinateVector i))
    (fun I' => T I' J) I

/-- Differentiate the antiholomorphic column indices of a coordinate matrix. -/
noncomputable def coordinateColumnDerivative (T : CoordinateDistributions Ω k l) :
    CoordinateDistributions Ω k (l + 1) :=
  Matrix.of fun I J => alternatingDerivative
    (fun j : Fin n => wirtingerDerivative (coordinateVector j) (-(Complex.I • coordinateVector j)))
    (T I) J

theorem coordinateRowDerivative_sq (T : CoordinateDistributions Ω k l) :
    coordinateRowDerivative (coordinateRowDerivative T) = 0 := by
  ext I J : 1
  simp only [coordinateRowDerivative, Matrix.of_apply, Matrix.zero_apply]
  exact alternatingDerivative_sq
    (fun i : Fin n => wirtingerDerivative (coordinateVector i) (Complex.I • coordinateVector i))
    (fun i j S => wirtingerDerivative_comm (coordinateVector i) (Complex.I • coordinateVector i)
      (coordinateVector j) (Complex.I • coordinateVector j) S) (fun I' => T I' J) I

theorem coordinateColumnDerivative_sq (T : CoordinateDistributions Ω k l) :
    coordinateColumnDerivative (coordinateColumnDerivative T) = 0 := by
  ext I J : 1
  simp only [coordinateColumnDerivative, Matrix.of_apply, Matrix.zero_apply]
  exact alternatingDerivative_sq
    (fun i : Fin n => wirtingerDerivative (coordinateVector i) (-(Complex.I • coordinateVector i)))
    (fun i j S => wirtingerDerivative_comm (coordinateVector i) (-(Complex.I • coordinateVector i))
      (coordinateVector j) (-(Complex.I • coordinateVector j)) S) (T I) J

theorem coordinateExteriorDerivatives_comm (T : CoordinateDistributions Ω k l) :
    coordinateRowDerivative (coordinateColumnDerivative T) =
      coordinateColumnDerivative (coordinateRowDerivative T) := by
  ext I J : 1
  simp only [coordinateRowDerivative, coordinateColumnDerivative, alternatingDerivative,
    Matrix.of_apply, map_sum, map_zsmul, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rw [smul_comm, wirtingerDerivative_comm]

theorem coordinateRowDerivative_zero :
    coordinateRowDerivative (0 : CoordinateDistributions Ω k l) = 0 := by
  ext I J : 1
  simp [coordinateRowDerivative, alternatingDerivative]

theorem coordinateColumnDerivative_zero :
    coordinateColumnDerivative (0 : CoordinateDistributions Ω k l) = 0 := by
  ext I J : 1
  simp [coordinateColumnDerivative, alternatingDerivative]

end KEBall.BedfordTaylor
