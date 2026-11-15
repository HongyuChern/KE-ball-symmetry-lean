import KEBall.LocalWirtinger
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The concrete domain and differential operators of the KE ball problem

`E n` is real Euclidean space of dimension `2*n`, with interleaved real and
imaginary coordinates. In particular its unit ball is an l2 ball.
Potentials are represented by total real functions smooth on an open
neighbourhood of the closed ball. All endpoint comparisons and solution
counts use their restrictions to the closed ball.

There are no assumed analytic conclusions in these definitions.
-/

set_option autoImplicit false
open scoped ContDiff BigOperators ComplexOrder

namespace KEBall

abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin (2 * n))

def unitBall (n : ℕ) : Set (E n) := Metric.ball 0 1
def closedUnitBall (n : ℕ) : Set (E n) := Metric.closedBall 0 1
def unitSphere (n : ℕ) : Set (E n) := Metric.sphere 0 1

abbrev ClosedBall (n : ℕ) := ↥(closedUnitBall n)
abbrev Sphere (n : ℕ) := ↥(unitSphere n)

def realIndex {n : ℕ} (i : Fin n) : Fin (2 * n) :=
  ⟨2 * i.val, by omega⟩

def imagIndex {n : ℕ} (i : Fin n) : Fin (2 * n) :=
  ⟨2 * i.val + 1, by omega⟩

noncomputable def realDirection {n : ℕ} (i : Fin n) : E n :=
  EuclideanSpace.single (realIndex i) 1

noncomputable def imagDirection {n : ℕ} (i : Fin n) : E n :=
  EuclideanSpace.single (imagIndex i) 1

noncomputable def complexCoord {n : ℕ} (x : E n) (i : Fin n) : ℂ :=
  (x (realIndex i) : ℂ) + Complex.I * (x (imagIndex i) : ℂ)

noncomputable def J {n : ℕ} (x : E n) : E n :=
  ∑ i : Fin n, ((-x (imagIndex i)) • realDirection i +
    (x (realIndex i)) • imagDirection i)

/-- The closed-ball smoothness convention is an actual open-neighbourhood
condition, not global smoothness of the representing total function. -/
def SmoothNear {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (K : Set X) (u : X → ℝ) : Prop :=
  ∃ U : Set X, IsOpen U ∧ K ⊆ U ∧ ContDiffOn ℝ ∞ u U

noncomputable def partialZ {n : ℕ} (i : Fin n) (f : E n → ℂ) : E n → ℂ :=
  KEBallProbe.dz (realDirection i) (imagDirection i) f

noncomputable def partialBar {n : ℕ} (i : Fin n) (f : E n → ℂ) : E n → ℂ :=
  KEBallProbe.dz (realDirection i) (-imagDirection i) f

noncomputable def complexHessian {n : ℕ} (u : E n → ℝ) (x : E n) :
    Matrix (Fin n) (Fin n) ℂ :=
  fun i j => partialZ i (partialBar j (fun y => (u y : ℂ))) x

/-- In the manuscript, `g^{i bar j}` is inverse-matrix entry `(j,i)`. -/
noncomputable def inverseCoefficient {n : ℕ} (u : E n → ℝ) (x : E n)
    (i j : Fin n) : ℂ := (complexHessian u x)⁻¹ j i

noncomputable def complexLaplacian {n : ℕ} (u h : E n → ℝ) (x : E n) : ℝ :=
  (∑ i : Fin n, ∑ j : Fin n,
    inverseCoefficient u x i j * complexHessian h x i j).re

noncomputable def gradientNormSq {n : ℕ} (u : E n → ℝ) (x : E n) : ℝ :=
  (∑ i : Fin n, ∑ j : Fin n, inverseCoefficient u x i j *
    partialZ i (fun y => (u y : ℂ)) x *
    partialBar j (fun y => (u y : ℂ)) x).re

/-- Evaluated on the unit sphere, `x` is the outward unit normal. -/
noncomputable def boundarySlope {n : ℕ} (u : E n → ℝ) (x : E n) : ℝ :=
  fderiv ℝ u x x / 2

/-- This real form has blocks `2 [[Re H, Im H], [-Im H, Re H]]`
in grouped real/imaginary coordinates. The use of `v_i * conj(w_j)` follows
the manuscript's complex Hessian convention. -/
noncomputable def realMetricForm {n : ℕ} (u : E n → ℝ) (x v w : E n) : ℝ :=
  2 * (∑ i : Fin n, ∑ j : Fin n, complexHessian u x i j *
    complexCoord v i * star (complexCoord w j)).re

/-- Exactly the differential equation, local smoothness, interior positivity
and boundary condition of the fixed manuscript. -/
def IsSolution (n : ℕ) (μ : ℝ) (u : E n → ℝ) : Prop :=
  0 < μ ∧
  SmoothNear (closedUnitBall n) u ∧
  (∀ x ∈ unitBall n, (complexHessian u x).PosDef) ∧
  (∀ x ∈ unitBall n, (complexHessian u x).det = (μ * Real.exp (-u x) : ℂ)) ∧
  (∀ x ∈ unitSphere n, u x = 0)

def restrictClosedBall {n : ℕ} (u : E n → ℝ) : ClosedBall n → ℝ :=
  fun x => u x.1

/-- Counts are on the closed-ball functions, not on arbitrary extensions. -/
def solutionSet (n : ℕ) (μ : ℝ) : Set (ClosedBall n → ℝ) :=
  {v | ∃ u : E n → ℝ, IsSolution n μ u ∧ restrictClosedBall u = v}

noncomputable def radialPotential (n : ℕ) (b : ℝ) (x : E n) : ℝ :=
  (n + 1 : ℝ) * Real.log ((1 + b * ‖x‖ ^ 2) / (1 + b))

noncomputable def radialCoefficient (n : ℕ) (b : ℝ) : ℝ :=
  (n + 1 : ℝ) ^ n * b ^ n / (1 + b) ^ (n + 1)

noncomputable def criticalCoefficient (n : ℕ) : ℝ := (n : ℝ) ^ n / (n + 1 : ℝ)

noncomputable def boundaryPolynomial (n : ℕ) (t : ℝ) : ℝ :=
  t ^ n * (1 - t / (n + 1 : ℝ))

/-- This equals `t^(n-3)` for `n ≥ 2` and `t > 0`, including `1/t`
in complex dimension two. Natural subtraction cannot erase the negative power. -/
noncomputable def horizontalFluxWeight (n : ℕ) (t : ℝ) : ℝ :=
  t ^ (n - 1) / t ^ 2

theorem SmoothNear.contDiffAt {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {K : Set X} {u : X → ℝ} (hu : SmoothNear K u) {x : X} (hx : x ∈ K) :
    ContDiffAt ℝ ∞ u x := by
  obtain ⟨U, hU, hKU, huU⟩ := hu
  exact huU.contDiffAt (hU.mem_nhds (hKU hx))

theorem restrictClosedBall_eq_iff {n : ℕ} {u v : E n → ℝ} :
    restrictClosedBall u = restrictClosedBall v ↔ Set.EqOn u v (closedUnitBall n) := by
  constructor
  · intro h x hx
    exact congrFun h ⟨x, hx⟩
  · intro h
    funext x
    exact h x.property

end KEBall
