import KEBall.BallGreenLocal

/-!
An independent, non-KE consumer of the local ball Green theorem.
The actual vector field is V(x)=x; it does not vanish on the unit sphere.
Its normalized outward flux and its normalized volume divergence are 2*n.
No complex Hessian, Monge--Ampere equation, or solution hypothesis is used.
-/

set_option autoImplicit false
open MeasureTheory Set
open scoped ContDiff

namespace KEBallValidationExamples
open KEBall

theorem divergence_identity_field {n : ℕ} (x : E n) :
    euclideanDivergence (fun y : E n => y) x = (2 * n : ℝ) := by
  have hi (i : Fin (2 * n)) :
      fderiv ℝ (fun y : E n => y i) x = EuclideanSpace.proj i :=
    (EuclideanSpace.proj i : E n →L[ℝ] ℝ).fderiv
  simp [euclideanDivergence, hi, EuclideanSpace.basisFun_apply]

/-- This is a use of the proved local nonzero-boundary Green theorem,
not an integral calculation assuming the desired flux identity. -/
theorem normalized_identity_field_green (n : ℕ) (hn : 0 < n) :
    (∫ x in unitBall n, euclideanDivergence (fun y : E n => y) x ∂volume0 n) =
      (2 * n : ℝ) := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  have h := integral_unitBall_divergence_normalized_of_contDiffOn hn
    (U := univ) isOpen_univ (subset_univ _) (V := fun y : E n => y)
    contDiffOn_id
  have hinner (θ : Sphere n) : inner ℝ θ.1 θ.1 = 1 := by
    have hnθ : ‖θ.1‖ = 1 := by
      simpa only [unitSphere, Metric.mem_sphere, dist_zero_right] using θ.2
    rw [real_inner_self_eq_norm_sq, hnθ]
    norm_num
  simpa only [hinner, integral_const, probReal_univ, one_smul, mul_one] using h

#print axioms divergence_identity_field
#print axioms normalized_identity_field_green

end KEBallValidationExamples
