import KEBall.DirichletCofactorMonotonicity
import KEBall.DirichletClassicalEquation

/-! Pairing the Hessian difference of two solutions with the cofactor difference. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter InnerProductSpace Matrix MeasureTheory Metric Set
open scoped ComplexOrder ContDiff Gradient Matrix MatrixOrder Matrix.Norms.Elementwise Topology

namespace KEBall

private theorem cofactorContraction_eq_trace {n : ℕ} (u h : E n → ℝ) (x : E n) :
    MoserTrudinger.cofactorContraction u h x =
      ((complexHessian u x).adjugate * complexHessian h x).trace.re := by
  unfold MoserTrudinger.cofactorContraction
  congr 1
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  exact Finset.sum_comm

/-- The cofactor pairing of two Hessian differences is a boundary
flux of the gradient difference. -/
theorem integral_cofactor_difference_eq_boundary {n : ℕ} (hn : 0 < n)
    {U : Set (E n)} (hU : IsOpen U) (hSub : closedUnitBall n ⊆ U)
    {u v : E n → ℝ} (hu : ContDiffOn ℝ ∞ u U) (hv : ContDiffOn ℝ ∞ v U)
    (huP : ∀ x ∈ unitBall n, (complexHessian u x).PosDef)
    (hvP : ∀ x ∈ unitBall n, (complexHessian v x).PosDef) :
    (∫ x in unitBall n, (((complexHessian u x).adjugate - (complexHessian v x).adjugate) *
        (complexHessian v x - complexHessian u x)).trace.re ∂volume0 n) =
      (n : ℝ) * ∫ θ : Sphere n, inner ℝ θ.val
        ((cofactorRealField u (v - u) θ.val - cofactorRealField v (v - u) θ.val)) ∂sphere0 n := by
  let h := v - u
  let F (x : E n) := cofactorRealField u h x - cofactorRealField v h x
  have hh : ContDiffOn ℝ ∞ h U := hv.sub hu
  have hF₁ := cofactorRealField_contDiffOn hU hu hh
  have hF₂ := cofactorRealField_contDiffOn hU hv hh
  have hGreen := integral_unitBall_divergence_normalized_of_contDiffOn hn hU hSub
    ((hF₁.sub hF₂).of_le (show (1 : ℕ∞ω) ≤ ∞ by simp))
  have hDiv {w : E n → ℝ} (hw : ContDiffOn ℝ ∞ w U)
      (hwP : ∀ x ∈ unitBall n, (complexHessian w x).PosDef) {x : E n} (hx : x ∈ unitBall n) :
      euclideanDivergence (cofactorRealField w h) x =
        2 * ((complexHessian w x).adjugate * complexHessian h x).trace.re := by
    have hN := hU.mem_nhds (hSub (ball_subset_closedBall hx))
    rw [← cofactorContraction_eq_trace]
    apply cofactorRealField_divergence_of_piola (hw.contDiffAt hN) (hh.contDiffAt hN)
    intro j
    have hWC : ContDiffAt ℝ ∞ (fun y => (w y : ℂ)) x :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp x (hw.contDiffAt hN)
    exact cofactor_divergence_at hWC realDirection imagDirection
      ((Matrix.isUnit_iff_isUnit_det _).mp (hwP x hx).isUnit) j
  have hVol :
      (∫ x in unitBall n, euclideanDivergence F x ∂volume0 n) =
        2 * ∫ x in unitBall n, (((complexHessian u x).adjugate - (complexHessian v x).adjugate) *
          (complexHessian v x - complexHessian u x)).trace.re ∂volume0 n := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_ball
    intro x hx
    have hN := hU.mem_nhds (hSub (ball_subset_closedBall hx))
    change euclideanDivergence (fun x => cofactorRealField u h x - cofactorRealField v h x) x = _
    rw [euclideanDivergence_sub ((hF₁.contDiffAt hN).differentiableAt (by simp))
      ((hF₂.contDiffAt hN).differentiableAt (by simp)),
      hDiv hu huP hx, hDiv hv hvP hx]
    dsimp only
    rw [Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re]
    have he : complexHessian h x = complexHessian v x - complexHessian u x :=
      complexHessian_sub_at (hv.contDiffAt hN) (hu.contDiffAt hN)
    rw [he]
    ring
  change (∫ x in unitBall n, euclideanDivergence F x ∂volume0 n) =
    (2 * n : ℝ) * ∫ θ : Sphere n, inner ℝ θ.val (F θ.val) ∂sphere0 n at hGreen
  rw [hVol] at hGreen
  linarith only [hGreen]


/-- Uniform cofactor bounds reduce the flux to the uniform gradient
difference on the sphere. -/
theorem abs_integral_cofactor_difference_le_of_gradient_bound {n : ℕ} (hn : 0 < n)
    {U : Set (E n)} (hU : IsOpen U) (hSub : closedUnitBall n ⊆ U)
    {u v : E n → ℝ} (hu : ContDiffOn ℝ ∞ u U) (hv : ContDiffOn ℝ ∞ v U)
    (huP : ∀ x ∈ unitBall n, (complexHessian u x).PosDef)
    (hvP : ∀ x ∈ unitBall n, (complexHessian v x).PosDef)
    {M ε : ℝ} (hM : 0 ≤ M)
    (hOp : ∀ x ∈ unitSphere n, ‖dirichletCofactorOperator u x‖ ≤ M ∧
      ‖dirichletCofactorOperator v x‖ ≤ M)
    (hD : ∀ x ∈ unitSphere n, ‖fderiv ℝ v x - fderiv ℝ u x‖ ≤ ε) :
    |∫ x in unitBall n, (((complexHessian u x).adjugate - (complexHessian v x).adjugate) *
        (complexHessian v x - complexHessian u x)).trace.re ∂volume0 n| ≤
      (4 * n : ℝ) * M * ε := by
  let h := v - u
  let F (x : E n) := cofactorRealField u h x - cofactorRealField v h x
  let g (θ : Sphere n) := inner ℝ θ.val (F θ.val)
  have hh : ContDiffOn ℝ ∞ h U := hv.sub hu
  have hBound (θ : Sphere n) : ‖g θ‖ ≤ 4 * M * ε := by
    have hN := hU.mem_nhds (hSub (sphere_subset_closedBall θ.property))
    have hd := (hh.contDiffAt hN).differentiableAt (by simp)
    have hgrad : ‖∇ h θ.val‖ ≤ ε := by
      have he : ‖∇ h θ.val‖ = ‖fderiv ℝ h θ.val‖ := by
        rw [← (InnerProductSpace.toDual ℝ (E n)).norm_map, toDual_gradient]
      rw [he]
      change ‖fderiv ℝ (v - u) θ.val‖ ≤ ε
      rw [fderiv_sub ((hv.contDiffAt hN).differentiableAt (by simp))
        ((hu.contDiffAt hN).differentiableAt (by simp))]
      exact hD θ.val θ.property
    have hF (w : E n → ℝ) (hw : ‖dirichletCofactorOperator w θ.val‖ ≤ M) :
        ‖cofactorRealField w h θ.val‖ ≤ 2 * M * ε := by
      rw [cofactorRealField_eq_two_smul_operator hd, norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
        mul_assoc]
      exact mul_le_mul_of_nonneg_left (((dirichletCofactorOperator w θ.val).le_opNorm _).trans
        (mul_le_mul hw hgrad (norm_nonneg _) hM)) (by norm_num)
    calc
      ‖g θ‖ ≤ ‖θ.val‖ * ‖F θ.val‖ := norm_inner_le_norm _ _
      _ = ‖F θ.val‖ := by rw [mem_sphere_zero_iff_norm.mp θ.property, one_mul]
      _ ≤ 2 * M * ε + 2 * M * ε :=
        (norm_sub_le _ _).trans (add_le_add (hF u (hOp θ.val θ.property).1) (hF v (hOp θ.val θ.property).2))
      _ = 4 * M * ε := by ring
  have : NeZero n := ⟨hn.ne'⟩
  have hI : ‖∫ θ, g θ ∂sphere0 n‖ ≤ 4 * M * ε := by
    simpa [measureReal_def, sphere0_univ n hn] using
      norm_integral_le_of_norm_le_const (μ := sphere0 n) (Eventually.of_forall hBound)
  rw [integral_cofactor_difference_eq_boundary hn hU hSub hu hv huP hvP, abs_mul,
    abs_of_nonneg (Nat.cast_nonneg n), ← Real.norm_eq_abs]
  change (n : ℝ) * ‖∫ θ, g θ ∂sphere0 n‖ ≤ _
  exact (mul_le_mul_of_nonneg_left hI (Nat.cast_nonneg _)).trans_eq (by ring)


/-- Under uniform coefficient and inverse-Hessian bounds, the squared
(L^2) distance of two complex Hessians is controlled by their density
difference and their boundary gradient difference. -/
theorem integral_sq_complexHessian_sub_le_of_density_and_gradient_bound {n : ℕ} (hn : 0 < n)
    {U : Set (E n)} (hU : IsOpen U) (hSub : closedUnitBall n ⊆ U)
    {u v : E n → ℝ} (hu : ContDiffOn ℝ ∞ u U) (hv : ContDiffOn ℝ ∞ v U)
    (huP : ∀ x ∈ unitBall n, (complexHessian u x).PosDef)
    (hvP : ∀ x ∈ unitBall n, (complexHessian v x).PosDef)
    {a d M K ε δ : ℝ} (ha : 0 ≤ a) (hM : 0 ≤ M) (hδ : 0 ≤ δ)
    (hDen : ∀ x ∈ unitBall n, d ≤ (complexHessian u x).det.re)
    (hInv : ∀ x ∈ unitBall n,
      (a : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) ≤ (complexHessian u x)⁻¹ ∧
      (a : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) ≤ (complexHessian v x)⁻¹)
    (hOp : ∀ x ∈ unitSphere n, ‖dirichletCofactorOperator u x‖ ≤ M ∧
      ‖dirichletCofactorOperator v x‖ ≤ M)
    (hGrad : ∀ x ∈ unitSphere n, ‖fderiv ℝ v x - fderiv ℝ u x‖ ≤ ε)
    (hDensityDiff : ∀ x ∈ unitBall n,
      |(complexHessian v x).det.re - (complexHessian u x).det.re| ≤ δ)
    (hTrace : ∀ x ∈ unitBall n,
      |((complexHessian v x)⁻¹ * (complexHessian v x - complexHessian u x)).trace.re| ≤ K) :
    d * a ^ 2 * (∫ x in unitBall n, ∑ i, ∑ j,
      ‖(complexHessian v x - complexHessian u x) i j‖ ^ 2 ∂volume0 n) ≤
      (4 * n : ℝ) * M * ε + δ * K := by
  have : NeZero n := ⟨hn.ne'⟩
  let μ := (volume0 n).restrict (unitBall n)
  let A := complexHessian u
  let B := complexHessian v
  let q (x : E n) : ℝ := ∑ i, ∑ j, ‖(B x - A x) i j‖ ^ 2
  let p (x : E n) : ℝ := (((A x).adjugate - (B x).adjugate) * (B x - A x)).trace.re
  have hA : ContinuousOn A U := continuousOn_pi.mpr fun i =>
    continuousOn_pi.mpr fun j => (complexHessian_contDiffOn hU hu i j).continuousOn
  have hB : ContinuousOn B U := continuousOn_pi.mpr fun i =>
    continuousOn_pi.mpr fun j => (complexHessian_contDiffOn hU hv i j).continuousOn
  have hQ : ContinuousOn q U := by
    apply continuousOn_finsetSum
    intro i _
    apply continuousOn_finsetSum
    intro j _
    exact ((continuousOn_pi.mp (continuousOn_pi.mp (hB.sub hA) i) j).norm).pow 2
  have hP : ContinuousOn p U := by
    apply Complex.continuous_re.comp_continuousOn
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    apply continuousOn_finsetSum
    intro i _
    apply continuousOn_finsetSum
    intro j _
    exact (((matrixField_adjugate_contDiffOn (complexHessian_contDiffOn hU hu) i j).continuousOn).sub
      ((matrixField_adjugate_contDiffOn (complexHessian_contDiffOn hU hv) i j).continuousOn)).mul
        (continuousOn_pi.mp (continuousOn_pi.mp (hB.sub hA) j) i)
  have hI {g : E n → ℝ} (hg : ContinuousOn g U) : Integrable g μ :=
    (hg.mono hSub).integrableOn_of_subset_isCompact (isCompact_closedBall _ _)
      measurableSet_ball ball_subset_closedBall (by rw [volume0_unitBall n hn]; exact ENNReal.one_ne_top)
  have hMono : (fun x => (d * a ^ 2) * q x) ≤ᵐ[μ] fun x => p x + δ * K := by
    filter_upwards [ae_restrict_mem (μ := volume0 n) (show MeasurableSet (unitBall n) from measurableSet_ball)]
      with x hx
    have hq₀ : 0 ≤ q x := by dsimp [q]; positivity
    have he := posDef_cofactor_difference_trace_ge (huP x hx) (hvP x hx)
      ha (hInv x hx).1 (hInv x hx).2
    calc
      d * a ^ 2 * q x ≤ (A x).det.re * a ^ 2 * q x :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hDen x hx) (sq_nonneg _)) hq₀
      _ ≤ p x + ((B x).det.re - (A x).det.re) * ((B x)⁻¹ * (B x - A x)).trace.re := he
      _ ≤ p x + δ * K := by
        apply add_le_add_right
        exact (le_abs_self _).trans (by
          rw [abs_mul]
          exact mul_le_mul (hDensityDiff x hx) (hTrace x hx) (abs_nonneg _) hδ)
  have h := integral_mono_ae ((hI hQ).const_mul (d * a ^ 2))
    ((hI hP).add (integrable_const (δ * K))) hMono
  change (∫ x, (d * a ^ 2) * q x ∂μ) ≤ (∫ x, p x + δ * K ∂μ) at h
  rw [integral_const_mul, integral_add (hI hP) (integrable_const (δ * K)),
    integral_const, probReal_univ, one_smul] at h
  exact h.trans (add_le_add_left ((le_abs_self _).trans
    (abs_integral_cofactor_difference_le_of_gradient_bound hn hU hSub hu hv huP hvP hM hOp hGrad)) _)

end KEBall
