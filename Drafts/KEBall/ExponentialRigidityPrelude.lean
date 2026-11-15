import Drafts.KEBall.BoundarySlopeRigidity

/-!
Stage08 SOURCE_DRAFT_UNCOMPILED.
The exponential is differentiated in the ORIGINAL Hessian metric of u.
The tensor below has separate metric-potential and test-function arguments.
It must not be confused with covariantHessian20 (expWeight u), whose
background metric would be different.
-/
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped BigOperators ContDiff Topology

namespace KEBall
open KEBallProbe

/-- (2,0) Hessian of h with the fixed connection coefficients of g_u. -/
noncomputable def metricCovariantHessian20 {n : ℕ} (u h : E n → ℝ) (x : E n)
    (i j : Fin n) : ℂ :=
  partialZ i (partialZ j (fun y => (h y : ℂ))) x -
    ∑ k : Fin n, ∑ l : Fin n, inverseCoefficient u x k l *
      partialZ i (fun y => complexHessian u y j l) x *
      partialZ k (fun y => (h y : ℂ)) x

@[simp] theorem metricCovariantHessian20_self {n : ℕ} (u : E n → ℝ)
    (x : E n) (i j : Fin n) :
    metricCovariantHessian20 u u x i j = covariantHessian20 u x i j := rfl

/-- The full exponential chain rule in the original metric. It is derived
from actual second Wirtinger derivatives before the connection contraction. -/
theorem metricCovariantHessian20_exp_const_mul {n : ℕ} {u : E n → ℝ}
    {x : E n} (hu : ContDiffAt ℝ ∞ u x) (r : ℝ) (i j : Fin n) :
    metricCovariantHessian20 u (fun y => Real.exp (r * u y)) x i j =
      (Real.exp (r * u x) : ℂ) *
        ((r : ℂ) * covariantHessian20 u x i j +
          (r : ℂ) ^ 2 * partialZ i (fun y => (u y : ℂ)) x *
            partialZ j (fun y => (u y : ℂ)) x) := by
  have hfirst (k : Fin n) :
      partialZ k (fun y => (Real.exp (r * u y) : ℂ)) x =
        (r : ℂ) * (Real.exp (r * u x) : ℂ) * partialZ k (fun y => (u y : ℂ)) x :=
    AuxiliaryPDifferential.dz_ofReal_exp_const_mul (hu.differentiableAt (by simp)) r
      (realDirection k) (imagDirection k)
  have hsecond := AuxiliaryPDifferential.dz_dz_ofReal_exp_const_mul hu r
    (realDirection i) (imagDirection i) (realDirection j) (imagDirection j)
  change partialZ i (partialZ j (fun y => (Real.exp (r * u y) : ℂ))) x =
    (Real.exp (r * u x) : ℂ) *
      ((r : ℂ) * partialZ i (partialZ j (fun y => (u y : ℂ))) x +
        (r : ℂ) ^ 2 * partialZ i (fun y => (u y : ℂ)) x *
          partialZ j (fun y => (u y : ℂ)) x) at hsecond
  have hsum : (∑ k : Fin n, ∑ l : Fin n, inverseCoefficient u x k l *
      partialZ i (fun y => complexHessian u y j l) x *
      partialZ k (fun y => (Real.exp (r * u y) : ℂ)) x) =
      (Real.exp (r * u x) : ℂ) * (r : ℂ) *
        (∑ k : Fin n, ∑ l : Fin n, inverseCoefficient u x k l *
          partialZ i (fun y => complexHessian u y j l) x *
          partialZ k (fun y => (u y : ℂ)) x) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    rw [hfirst]
    ring
  unfold metricCovariantHessian20 covariantHessian20
  rw [hsecond, hsum]
  ring

/-- The original rank-one Hessian identity forces the weighted Hessian to
vanish in g_u, without any additional integral or symmetry premise. -/
theorem IsSolution.metricCovariantHessian20_expWeight_eq_zero {n : ℕ}
    (hn : 2 ≤ n) {μ : ℝ} {u : E n → ℝ} (hu : IsSolution n μ u)
    {x : E n} (hx : x ∈ unitBall n) (i j : Fin n) :
    metricCovariantHessian20 u (expWeight u) x i j = 0 := by
  have huAt := hu.2.1.contDiffAt (Metric.ball_subset_closedBall hx)
  rw [AuxiliaryPDifferential.expWeight_eq_exp_const_mul,
    metricCovariantHessian20_exp_const_mul huAt,
    hu.covariantHessian20_eq_rank_one hn hx]
  push_cast
  ring

/-- Coordinate definition of the actual (1,0) gradient of E in g_u. -/
noncomputable def exponentialGradient {n : ℕ} (u : E n → ℝ) (x : E n)
    (i : Fin n) : ℂ :=
  ∑ j : Fin n, inverseCoefficient u x i j *
    partialBar j (fun y => (expWeight u y : ℂ)) x

theorem exponentialGradient_eq_scaled_inverseGradient {n : ℕ} {u : E n → ℝ}
    {x : E n} (hu : DifferentiableAt ℝ u x) (i : Fin n) :
    exponentialGradient u x i =
      -((expWeight u x : ℂ) / (n + 1 : ℂ)) * complexCoord (inverseGradientVector u x) i := by
  unfold exponentialGradient inverseGradientVector
  rw [complexCoord_complexVectorReal]
  simp only [partialBar_expWeight hu, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Actual regularity of each component up to the boundary. -/
theorem IsSolution.exponentialGradient_contDiffOn_closedBall {n : ℕ}
    {μ : ℝ} {u : E n → ℝ} (hu : IsSolution n μ u) (i : Fin n) :
    ContDiffOn ℝ ∞ (fun x => exponentialGradient u x i) (closedUnitBall n) := by
  have hE : ContDiffOn ℝ ∞ (fun x => (expWeight u x : ℂ)) (closedUnitBall n) := by
    apply Complex.ofRealCLM.contDiff.comp_contDiffOn
    intro x hx
    exact (contDiffAt_expWeight (hu.2.1.contDiffAt hx)).contDiffWithinAt
  have hV : ContDiffOn ℝ ∞ (fun x => complexCoord (inverseGradientVector u x) i)
      (closedUnitBall n) :=
    (complexCoordCLM i).contDiff.comp_contDiffOn hu.inverseGradientVector_contDiffOn_closedBall
  apply ((hE.div_const (n + 1 : ℂ)).neg.mul hV).congr
  intro x hx
  exact exponentialGradient_eq_scaled_inverseGradient
    ((hu.2.1.contDiffAt hx).differentiableAt (by simp)) i

/-- Actual boundary gradient. The mixed block disappears because the
horizontal slope gradient has been proved zero for every solution. -/
theorem IsSolution.exponentialGradient_on_sphere {n : ℕ} (hn : 2 ≤ n)
    {μ : ℝ} {u : E n → ℝ} (hu : IsSolution n μ u) {x : E n}
    (hx : x ∈ unitSphere n) (i : Fin n) :
    exponentialGradient u x i =
      (-(boundarySlope u x ^ n / ((n + 1 : ℝ) * μ)) : ℝ) * complexCoord x i := by
  rw [exponentialGradient_eq_scaled_inverseGradient
    ((hu.2.1.contDiffAt (Metric.sphere_subset_closedBall hx)).differentiableAt (by simp)),
    hu.inverseGradientVector_on_sphere hn hx]
  have hE : expWeight u x = 1 := by simp [expWeight, hu.2.2.2.2 x hx]
  rw [hE, boundaryInverseDirection, hu.horizontalGradient_boundarySlope_eq_zero hn hx]
  simp only [smul_zero, sub_zero, smul_smul,
    BoundaryInverseSplitAux.complexCoord_smul, Pi.smul_apply, smul_eq_mul]
  have ht : boundarySlope u x ≠ 0 := ne_of_gt (hu.boundarySlope_pos hn hx)
  have hμ : μ ≠ 0 := ne_of_gt hu.1
  have hk : (n + 1 : ℝ) ≠ 0 := by positivity
  have hp : boundarySlope u x ^ n = boundarySlope u x ^ (n - 1) * boundarySlope u x := by
    rw [← pow_succ]
    congr 1
    omega
  rw [hp]
  have htC : (boundarySlope u x : ℂ) ≠ 0 := by exact_mod_cast ht
  have hμC : (μ : ℂ) ≠ 0 := by exact_mod_cast hμ
  have hkC : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast hk
  push_cast
  field_simp [htC, hμC, hkC]
  <;> ring

/-- Pohozaev's root relation simplifies the scalar in the boundary vector. -/
theorem boundary_exponential_gradient_coefficient {n : ℕ} {μ t : ℝ}
    (ht : 0 < t) (htk : t < (n + 1 : ℝ))
    (hF : boundaryPolynomial n t = μ) :
    -(t ^ n / ((n + 1 : ℝ) * μ)) = -1 / ((n + 1 : ℝ) - t) := by
  have htn : t ^ n ≠ 0 := pow_ne_zero _ (ne_of_gt ht)
  have hk : (n + 1 : ℝ) ≠ 0 := by positivity
  have hkt : (n + 1 : ℝ) - t ≠ 0 := ne_of_gt (sub_pos.mpr htk)
  have hfactor : (n + 1 : ℝ) * μ = t ^ n * ((n + 1 : ℝ) - t) := by
    rw [← hF]
    unfold boundaryPolynomial
    field_simp [hk]
    <;> ring
  rw [hfactor]
  field_simp [htn, hkt]
  <;> ring

/-- Concrete boundary data for the next holomorphic uniqueness step. The
conclusion remains restricted to the sphere; no interior extension is claimed. -/
theorem IsSolution.exists_exponentialGradient_boundary_data {n : ℕ} (hn : 2 ≤ n)
    {μ : ℝ} {u : E n → ℝ} (hu : IsSolution n μ u) :
    ∃ t₀ : ℝ, 0 < t₀ ∧ t₀ < (n + 1 : ℝ) ∧ boundaryPolynomial n t₀ = μ ∧
      (∀ x ∈ unitSphere n, boundarySlope u x = t₀) ∧
      (∀ x ∈ unitSphere n, ∀ i : Fin n,
        exponentialGradient u x i = (-1 / ((n + 1 : ℝ) - t₀) : ℝ) * complexCoord x i) := by
  obtain ⟨t₀, ht₀, htk, hF, ht⟩ := hu.exists_constant_boundarySlope hn
  refine ⟨t₀, ht₀, htk, hF, ht, ?_⟩
  intro x hx i
  rw [hu.exponentialGradient_on_sphere hn hx i, ht x hx,
    boundary_exponential_gradient_coefficient ht₀ htk hF]

#print axioms IsSolution.metricCovariantHessian20_expWeight_eq_zero
#print axioms IsSolution.exists_exponentialGradient_boundary_data

end KEBall
