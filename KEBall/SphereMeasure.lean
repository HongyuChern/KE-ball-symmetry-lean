import KEBall.Domain
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The actual volume and surface measures in the KE ball normalization

`volume0` is `(n! / pi^n)` times Euclidean volume. `sphereMeasure` is
the actual polar surface measure provided by `Measure.toSphere`; `sphere0`
normalizes that measure to mass one in positive complex dimension.

In particular, no abstract probability measure is substituted for the sphere.
The real dimension is `2*n` throughout.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped ENNReal

namespace KEBall

noncomputable def volume0 (n : ℕ) : Measure (E n) :=
  ENNReal.ofReal ((n.factorial : ℝ) / Real.pi ^ n) • volume

noncomputable def sphereMeasure (n : ℕ) : Measure (Sphere n) :=
  (volume : Measure (E n)).toSphere

noncomputable def sphere0 (n : ℕ) : Measure (Sphere n) :=
  (sphereMeasure n univ)⁻¹ • sphereMeasure n

theorem finrank_E (n : ℕ) : Module.finrank ℝ (E n) = 2 * n := by
  simp [E]

theorem volume_unitBall (n : ℕ) (hn : 0 < n) :
    (volume : Measure (E n)) (unitBall n) =
      ENNReal.ofReal (Real.pi ^ n / (n.factorial : ℝ)) := by
  letI : Nontrivial (E n) := Module.nontrivial_of_finrank_pos (R := ℝ)
    (by rw [finrank_E]; omega)
  simpa [unitBall] using
    (InnerProductSpace.volume_ball_of_dim_even (E := E n)
      (k := n) (finrank_E n) (0 : E n) (1 : ℝ))

theorem volume_closedUnitBall (n : ℕ) (hn : 0 < n) :
    (volume : Measure (E n)) (closedUnitBall n) =
      ENNReal.ofReal (Real.pi ^ n / (n.factorial : ℝ)) := by
  letI : Nontrivial (E n) := Module.nontrivial_of_finrank_pos (R := ℝ)
    (by rw [finrank_E]; omega)
  simpa [closedUnitBall] using
    (InnerProductSpace.volume_closedBall_of_dim_even (E := E n)
      (k := n) (finrank_E n) (0 : E n) (1 : ℝ))

theorem volume0_unitBall (n : ℕ) (hn : 0 < n) :
    volume0 n (unitBall n) = 1 := by
  rw [volume0, Measure.smul_apply, smul_eq_mul, volume_unitBall n hn,
    ← ENNReal.ofReal_mul (by positivity)]
  have h : (n.factorial : ℝ) / Real.pi ^ n *
      (Real.pi ^ n / (n.factorial : ℝ)) = 1 := by
    field_simp
  rw [h, ENNReal.ofReal_one]

theorem volume0_closedUnitBall (n : ℕ) (hn : 0 < n) :
    volume0 n (closedUnitBall n) = 1 := by
  rw [volume0, Measure.smul_apply, smul_eq_mul, volume_closedUnitBall n hn,
    ← ENNReal.ofReal_mul (by positivity)]
  have h : (n.factorial : ℝ) / Real.pi ^ n *
      (Real.pi ^ n / (n.factorial : ℝ)) = 1 := by
    field_simp
  rw [h, ENNReal.ofReal_one]

instance sphereMeasure_isFinite (n : ℕ) : IsFiniteMeasure (sphereMeasure n) := by
  change IsFiniteMeasure ((volume : Measure (E n)).toSphere)
  infer_instance

instance sphereMeasure_isOpenPos (n : ℕ) : (sphereMeasure n).IsOpenPosMeasure := by
  change ((volume : Measure (E n)).toSphere).IsOpenPosMeasure
  infer_instance

instance sphere_compactSpace (n : ℕ) : CompactSpace (Sphere n) := by
  change CompactSpace ↥(Metric.sphere (0 : E n) 1)
  infer_instance

theorem sphereMeasure_univ (n : ℕ) (hn : 0 < n) :
    sphereMeasure n univ =
      ENNReal.ofReal ((2 * n : ℝ) * Real.pi ^ n / (n.factorial : ℝ)) := by
  change (volume : Measure (E n)).toSphere univ = _
  rw [Measure.toSphere_apply_univ, finrank_E]
  change (2 * n : ℕ) * (volume : Measure (E n)) (unitBall n) = _
  rw [volume_unitBall n hn]
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  push_cast
  ring

theorem sphereMeasure_univ_ne_zero (n : ℕ) (hn : 0 < n) :
    sphereMeasure n univ ≠ 0 := by
  rw [sphereMeasure_univ n hn]
  apply ne_of_gt
  exact ENNReal.ofReal_pos.mpr (by positivity)

theorem sphere0_univ (n : ℕ) (hn : 0 < n) : sphere0 n univ = 1 := by
  rw [sphere0, Measure.smul_apply, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (sphereMeasure_univ_ne_zero n hn) (measure_ne_top _ _)

theorem sphere0_eq_explicit_smul (n : ℕ) (hn : 0 < n) :
    sphere0 n = ENNReal.ofReal
      ((n.factorial : ℝ) / ((2 * n : ℝ) * Real.pi ^ n)) • sphereMeasure n := by
  rw [sphere0, sphereMeasure_univ n hn,
    ← ENNReal.ofReal_inv_of_pos (by positivity)]
  congr 2
  exact inv_div _ _

instance sphere0_isProbability (n : ℕ) [NeZero n] : IsProbabilityMeasure (sphere0 n) :=
  ⟨sphere0_univ n (Nat.pos_of_ne_zero (NeZero.ne n))⟩

instance volume0_restrict_isProbability (n : ℕ) [NeZero n] :
    IsProbabilityMeasure ((volume0 n).restrict (unitBall n)) := by
  constructor
  rw [Measure.restrict_apply_univ, volume0_unitBall n (Nat.pos_of_ne_zero (NeZero.ne n))]

instance volume0_isOpenPos (n : ℕ) : (volume0 n).IsOpenPosMeasure := by
  unfold volume0
  exact Measure.isOpenPosMeasure_smul (volume : Measure (E n)) (by positivity)

instance sphere0_isOpenPos (n : ℕ) : (sphere0 n).IsOpenPosMeasure := by
  unfold sphere0
  apply Measure.isOpenPosMeasure_smul
  exact ENNReal.inv_ne_zero.mpr (measure_ne_top _ _)

theorem integral_volume0 (n : ℕ) (f : E n → ℝ) :
    (∫ x, f x ∂volume0 n) =
      ((n.factorial : ℝ) / Real.pi ^ n) * ∫ x, f x := by
  rw [volume0, integral_smul_measure, ENNReal.toReal_ofReal (by positivity), smul_eq_mul]

theorem setIntegral_volume0 (n : ℕ) (s : Set (E n)) (f : E n → ℝ) :
    (∫ x in s, f x ∂volume0 n) =
      ((n.factorial : ℝ) / Real.pi ^ n) * ∫ x in s, f x := by
  rw [volume0, Measure.restrict_smul, integral_smul_measure,
    ENNReal.toReal_ofReal (by positivity), smul_eq_mul]

theorem integral_sphere0 (n : ℕ) (hn : 0 < n) (f : Sphere n → ℝ) :
    (∫ x, f x ∂sphere0 n) =
      ((n.factorial : ℝ) / ((2 * n : ℝ) * Real.pi ^ n)) *
        ∫ x, f x ∂sphereMeasure n := by
  rw [sphere0_eq_explicit_smul n hn, integral_smul_measure,
    ENNReal.toReal_ofReal (by positivity), smul_eq_mul]

/-- A continuous nonnegative integrand on the actual sphere vanishes
pointwise if its normalized surface integral is zero. -/
theorem sphere_eq_zero_of_integral_eq_zero (n : ℕ) (hn : 0 < n)
    (f : Sphere n → ℝ) (hf : Continuous f) (hnonneg : 0 ≤ f)
    (hzero : (∫ x, f x ∂sphere0 n) = 0) : f = 0 := by
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  have hfi : Integrable f (sphere0 n) :=
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)
  exact (hf.ae_eq_iff_eq (sphere0 n) continuous_zero).mp
    ((integral_eq_zero_iff_of_nonneg hnonneg hfi).mp hzero)

/-- The fixed polar map uses the actual Euclidean dimension `2*n`. -/
theorem polar_measurePreserving (n : ℕ) :
    MeasurePreserving (homeomorphUnitSphereProd (E n))
      ((volume : Measure (E n)).comap
        (Subtype.val : ({(0 : E n)}ᶜ : Set (E n)) → E n))
      ((sphereMeasure n).prod (Measure.volumeIoiPow (2 * n - 1))) := by
  simpa only [sphereMeasure, finrank_E] using
    (volume : Measure (E n)).measurePreserving_homeomorphUnitSphereProd

/-- Actual polar change of variables, before splitting the product integral.
It is stated without an integrability hypothesis because both sides use
the same totalized Bochner integral under a measurable equivalence. -/
theorem integral_polar (n : ℕ) (hn : 0 < n) (f : E n → ℝ) :
    (∫ x, f x) =
      ∫ p : Sphere n × Ioi (0 : ℝ), f (p.2.1 • p.1.1)
        ∂((sphereMeasure n).prod (Measure.volumeIoiPow (2 * n - 1))) := by
  letI : Nontrivial (E n) := Module.nontrivial_of_finrank_pos (R := ℝ)
    (by rw [finrank_E]; omega)
  calc
    (∫ x, f x) =
        ∫ x : ({(0 : E n)}ᶜ : Set (E n)), f x.1
          ∂((volume : Measure (E n)).comap Subtype.val) := by
      rw [integral_subtype_comap (measurableSet_singleton _).compl,
        restrict_compl_singleton]
    _ = _ := by
      have h := (polar_measurePreserving n).integral_comp
        (Homeomorph.measurableEmbedding (homeomorphUnitSphereProd (E n)))
        (fun p => f ((homeomorphUnitSphereProd (E n)).symm p).1)
      simpa only [Homeomorph.symm_apply_apply,
        homeomorphUnitSphereProd_symm_apply_coe, Sphere, unitSphere] using h

/-- The normalization converts the usual polar surface measure to the
probability surface measure, with the exact real-dimension factor `2*n`. -/
theorem integral_volume0_polar (n : ℕ) (hn : 0 < n) (f : E n → ℝ) :
    (∫ x, f x ∂volume0 n) = (2 * n : ℝ) *
      ∫ p : Sphere n × Ioi (0 : ℝ), f (p.2.1 • p.1.1)
        ∂((sphere0 n).prod (Measure.volumeIoiPow (2 * n - 1))) := by
  rw [integral_volume0, integral_polar n hn, sphere0_eq_explicit_smul n hn,
    Measure.prod_smul_left, integral_smul_measure,
    ENNReal.toReal_ofReal (by positivity), smul_eq_mul]
  have h : (n.factorial : ℝ) / Real.pi ^ n = (2 * n : ℝ) *
      ((n.factorial : ℝ) / ((2 * n : ℝ) * Real.pi ^ n)) := by
    field_simp
  rw [h, mul_assoc]

#print axioms volume0_unitBall
#print axioms volume0_closedUnitBall
#print axioms sphereMeasure_univ
#print axioms sphere0_univ
#print axioms sphere0_eq_explicit_smul
#print axioms integral_volume0
#print axioms integral_sphere0
#print axioms sphere_eq_zero_of_integral_eq_zero
#print axioms integral_polar
#print axioms integral_volume0_polar

end KEBall
