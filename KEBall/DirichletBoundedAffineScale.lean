import KEBall.DirichletBoundedDifferenceQuotient

/-!
# Affine spatial rescaling of bounded jets

The value, first and second jets acquire respectively the factors 1, r
and r^2.  Holder constants acquire the additional factor r^alpha.  These
are the factors used when an interior physical ball is normalized to the
unit ball in the actual difference-quotient equation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open scoped NNReal

namespace KEBall

noncomputable def dirichletBoundedAffinePull {n : ℕ} {F : Type*} [NormedAddCommGroup F]
    (f : BoundedContinuousFunction (E n) F) (p : E n) (r : ℝ≥0) :
    BoundedContinuousFunction (E n) F :=
  f.compContinuous ⟨fun x => p + (r : ℝ) • x, by fun_prop⟩

theorem dirichletBoundedAffinePull_apply {n : ℕ} {F : Type*} [NormedAddCommGroup F]
    (f : BoundedContinuousFunction (E n) F) (p : E n) (r : ℝ≥0) (x : E n) :
    dirichletBoundedAffinePull f p r x = f (p + (r : ℝ) • x) := rfl

theorem nnnorm_dirichletBoundedAffinePull_le {n : ℕ} {F : Type*} [NormedAddCommGroup F]
    (f : BoundedContinuousFunction (E n) F) (p : E n) (r : ℝ≥0) :
    ‖dirichletBoundedAffinePull f p r‖₊ ≤ ‖f‖₊ := f.norm_compContinuous_le _

theorem lipschitzWith_dirichlet_affineScale {n : ℕ} (p : E n) (r : ℝ≥0) :
    LipschitzWith r (fun x : E n => p + (r : ℝ) • x) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [dist_eq_norm, add_sub_add_left_eq_sub, ← smul_sub, norm_smul,
    Real.norm_of_nonneg r.coe_nonneg]
  exact le_rfl

theorem holderWith_dirichletBoundedAffinePull {n : ℕ} {F : Type*} [NormedAddCommGroup F]
    {f : BoundedContinuousFunction (E n) F} {K α : ℝ≥0}
    (hf : HolderWith K α (f : E n → F)) (p : E n) (r : ℝ≥0) :
    HolderWith (K * r ^ (α : ℝ)) α (dirichletBoundedAffinePull f p r : E n → F) := by
  simpa only [mul_one] using! hf.comp (lipschitzWith_dirichlet_affineScale p r).holderWith

theorem hasFDerivAt_dirichletBoundedAffinePull {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : BoundedContinuousFunction (E n) F}
    {D : BoundedContinuousFunction (E n) (E n →L[ℝ] F)}
    (hD : ∀ x, HasFDerivAt (f : E n → F) (D x) x)
    (p : E n) (r : ℝ≥0) (x : E n) :
    HasFDerivAt (dirichletBoundedAffinePull f p r : E n → F)
      ((r : ℝ) • dirichletBoundedAffinePull D p r x) x := by
  have hLin : HasFDerivAt (fun y : E n => p + (r : ℝ) • y)
      ((r : ℝ) • ContinuousLinearMap.id ℝ (E n)) x := by
    simpa only [zero_add, Pi.add_apply, Pi.smul_apply, id_eq] using!
      (hasFDerivAt_const p x).add ((hasFDerivAt_id x).const_smul (r : ℝ))
  have ht := (hD (p + (r : ℝ) • x)).comp x hLin
  have he : (D (p + (r : ℝ) • x)).comp ((r : ℝ) • ContinuousLinearMap.id ℝ (E n)) =
      (r : ℝ) • D (p + (r : ℝ) • x) := by
    ext y
    simp only [ContinuousLinearMap.comp_apply, smul_apply, ContinuousLinearMap.id_apply, map_smul]
  rw [he] at ht
  exact ht

noncomputable def dirichletBoundedScaledJet {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : BoundedContinuousFunction (E n) F) (p : E n) (r : ℝ≥0) (k : ℕ) :
    BoundedContinuousFunction (E n) F :=
  (r : ℝ) ^ k • dirichletBoundedAffinePull f p r

theorem dirichletBoundedScaledJet_apply {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : BoundedContinuousFunction (E n) F) (p : E n) (r : ℝ≥0) (k : ℕ) (x : E n) :
    dirichletBoundedScaledJet f p r k x = (r : ℝ) ^ k • f (p + (r : ℝ) • x) := rfl

theorem hasFDerivAt_dirichletBoundedScaledJet {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : BoundedContinuousFunction (E n) F}
    {D : BoundedContinuousFunction (E n) (E n →L[ℝ] F)}
    (hD : ∀ x, HasFDerivAt (f : E n → F) (D x) x)
    (p : E n) (r : ℝ≥0) (k : ℕ) (x : E n) :
    HasFDerivAt (dirichletBoundedScaledJet f p r k : E n → F)
      (dirichletBoundedScaledJet D p r (k + 1) x) x := by
  simpa only [dirichletBoundedScaledJet, BoundedContinuousFunction.smul_apply, smul_smul,
    pow_succ] using! (hasFDerivAt_dirichletBoundedAffinePull hD p r x).const_smul ((r : ℝ) ^ k)

theorem nnnorm_dirichletBoundedScaledJet_le {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : BoundedContinuousFunction (E n) F) (p : E n) (r : ℝ≥0) (k : ℕ) :
    ‖dirichletBoundedScaledJet f p r k‖₊ ≤ r ^ k * ‖f‖₊ := by
  have hNorm : ‖(r : ℝ) ^ k‖₊ = r ^ k := by
    apply NNReal.eq
    simp only [coe_nnnorm, Real.norm_of_nonneg (pow_nonneg r.coe_nonneg k), NNReal.coe_pow]
  rw [dirichletBoundedScaledJet, nnnorm_smul, hNorm]
  exact mul_le_mul_of_nonneg_left (nnnorm_dirichletBoundedAffinePull_le f p r) (bot_le : (0 : ℝ≥0) ≤ _)

theorem holderWith_dirichletBoundedScaledJet {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : BoundedContinuousFunction (E n) F} {K α : ℝ≥0}
    (hf : HolderWith K α (f : E n → F)) (p : E n) (r : ℝ≥0) (k : ℕ) :
    HolderWith (r ^ k * (K * r ^ (α : ℝ))) α (dirichletBoundedScaledJet f p r k : E n → F) := by
  have h := (lipschitzWith_smul ((r : ℝ) ^ k) (β := F)).holderWith.comp
    (holderWith_dirichletBoundedAffinePull hf p r)
  have hNorm : ‖(r : ℝ) ^ k‖₊ = r ^ k := by
    apply NNReal.eq
    simp only [coe_nnnorm, Real.norm_of_nonneg (pow_nonneg r.coe_nonneg k), NNReal.coe_pow]
  simpa only [NNReal.coe_one, NNReal.rpow_one, one_mul, hNorm, Function.comp_def,
    dirichletBoundedScaledJet, BoundedContinuousFunction.smul_apply] using! h

end KEBall
