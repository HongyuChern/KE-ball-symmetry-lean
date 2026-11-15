import PshLines.TestLeviPairing
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Wirtinger derivatives of distributions

Constant-direction derivatives act on distributions with real test functions
and complex values. Commutation follows from the symmetry of the real
Hessian of the test function.
-/

set_option autoImplicit false

open TopologicalSpace
open scoped ContDiff Distributions

namespace KEBall.BedfordTaylor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {U : Opens E}

/-- The distributional derivative in a fixed real direction. -/
noncomputable abbrev directionalDerivative {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (v : E) : 𝓓'(U, F) →L[ℝ] 𝓓'(U, F) :=
  Distribution.lineDerivCLM v

theorem directionalDerivative_comm {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (v w : E) (T : 𝓓'(U, F)) :
    directionalDerivative v (directionalDerivative w T) =
      directionalDerivative w (directionalDerivative v T) := by
  ext φ
  simp only [directionalDerivative, Distribution.lineDerivCLM_apply, neg_neg]
  congr 1
  ext x
  simp only [PshLines.testFunction_lineDerivCLM_lineDerivCLM_apply,
    PshLines.realHessian_eq_fderiv]
  have hφ : ContDiffAt ℝ ∞ φ x := φ.contDiff.contDiffAt
  exact (hφ.isSymmSndFDerivAt (by simp; norm_cast)).eq _ _

theorem directionalDerivative_neg {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (v : E) (T : 𝓓'(U, F)) :
    directionalDerivative (-v) T = -directionalDerivative v T := by
  change Distribution.lineDerivCLM (-v) T = -Distribution.lineDerivCLM v T
  rw [← neg_one_smul ℝ v, Distribution.lineDerivCLM_smul, neg_one_smul, neg_apply]

theorem directionalDerivative_mapCLM {F G : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (v : E) (A : F →L[ℝ] G) (T : 𝓓'(U, F)) :
    directionalDerivative v (Distribution.mapCLM A T) =
      Distribution.mapCLM A (directionalDerivative v T) := by
  ext φ
  simp only [directionalDerivative, Distribution.lineDerivCLM_apply, Distribution.mapCLM_apply,
    map_neg]

/-- The distributional operator `(D_a - i D_b)/2`.
Taking `b = I • a` gives the holomorphic derivative. Replacing `b` by its
negative gives the antiholomorphic derivative. -/
noncomputable def wirtingerDerivative (a b : E) : 𝓓'(U, ℂ) →L[ℝ] 𝓓'(U, ℂ) :=
  (1 / 2 : ℂ) • (directionalDerivative a - Complex.I • directionalDerivative b)

theorem directionalDerivative_wirtingerDerivative (v a b : E) (T : 𝓓'(U, ℂ)) :
    directionalDerivative v (wirtingerDerivative a b T) =
      (1 / 2 : ℂ) •
        (directionalDerivative v (directionalDerivative a T) -
          Complex.I • directionalDerivative v (directionalDerivative b T)) := by
  ext φ
  simp only [wirtingerDerivative, directionalDerivative, Distribution.lineDerivCLM_apply,
    smul_apply, sub_apply, smul_eq_mul, neg_neg]
  ring

/-- Any two constant-coefficient Wirtinger derivatives commute, including
holomorphic-antiholomorphic pairs. -/
theorem wirtingerDerivative_comm (a b c d : E) (T : 𝓓'(U, ℂ)) :
    wirtingerDerivative a b (wirtingerDerivative c d T) =
      wirtingerDerivative c d (wirtingerDerivative a b T) := by
  change (1 / 2 : ℂ) • (directionalDerivative a (wirtingerDerivative c d T) -
      Complex.I • directionalDerivative b (wirtingerDerivative c d T)) =
    (1 / 2 : ℂ) • (directionalDerivative c (wirtingerDerivative a b T) -
      Complex.I • directionalDerivative d (wirtingerDerivative a b T))
  simp only [directionalDerivative_wirtingerDerivative]
  rw [directionalDerivative_comm a c, directionalDerivative_comm a d,
    directionalDerivative_comm b c, directionalDerivative_comm b d]
  ext φ
  simp only [smul_apply, sub_apply, smul_eq_mul]
  ring

variable [NormedSpace ℂ E]

/-- The `(v, w)` coefficient of `∂∂̄ T`, in the Hessian normalization used
by `smoothMeasure`. -/
noncomputable def distributionalComplexHessian (T : 𝓓'(U, ℝ)) (v w : E) : 𝓓'(U, ℂ) :=
  wirtingerDerivative v (Complex.I • v)
    (wirtingerDerivative w (-(Complex.I • w)) (Distribution.mapCLM Complex.ofRealCLM T))

/-- The row derivatives of the Hessian commute. -/
theorem distributionalComplexHessian_row_closed (T : 𝓓'(U, ℝ)) (a v w : E) :
    wirtingerDerivative a (Complex.I • a) (distributionalComplexHessian T v w) =
      wirtingerDerivative v (Complex.I • v) (distributionalComplexHessian T a w) :=
  wirtingerDerivative_comm _ _ _ _ _

/-- The column derivatives of the Hessian commute. -/
theorem distributionalComplexHessian_column_closed (T : 𝓓'(U, ℝ)) (a v w : E) :
    wirtingerDerivative a (-(Complex.I • a)) (distributionalComplexHessian T v w) =
      wirtingerDerivative w (-(Complex.I • w)) (distributionalComplexHessian T v a) := by
  unfold distributionalComplexHessian
  rw [wirtingerDerivative_comm a (-(Complex.I • a)) v (Complex.I • v),
    wirtingerDerivative_comm a (-(Complex.I • a)) w (-(Complex.I • w)),
    wirtingerDerivative_comm v (Complex.I • v) w (-(Complex.I • w))]

end KEBall.BedfordTaylor
