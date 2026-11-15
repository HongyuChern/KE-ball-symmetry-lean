import KEBall.DirichletUnitaryCofactorLimit

/-!
# Step-uniform Hessian bounds for genuine C2 determinant solutions

The normalized differences are formed from the original potential.
The proof combines the exact averaged-cofactor equation with the
perturbation estimate at that same potential.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Filter InnerProductSpace Matrix MeasureTheory Metric Set
open scoped BigOperators ComplexOrder ContDiff NNReal Topology

namespace KEBall

local notation "e[" n "]" => EuclideanSpace.basisFun (Fin (2 * n)) ℝ

theorem dirichletWithinComplexHessian_eq_on_ball_of_C2 {n : ℕ} {u : E n → ℝ}
    (hu : ContDiffOn ℝ 2 u (closedUnitBall n)) {x : E n} (hx : x ∈ unitBall n) :
    dirichletWithinComplexHessian u x = complexHessian u x := by
  change complexHessianOfRealBilinear (dirichletWithinRealHessian u x) = _
  rw [dirichletWithinRealHessian_eq_on_ball u hx]
  exact complexHessianOfRealBilinear_eq
    ((hu.mono ball_subset_closedBall).contDiffAt (isOpen_ball.mem_nhds hx))

theorem exists_dirichlet_unitary_difference_hessian_estimate {n : ℕ}
    (hn : 0 < n) {u f : E n → ℝ}
    (hu : ContDiffOn ℝ 2 u (closedUnitBall n))
    (huS : ContDiffOn ℝ ∞ u (unitBall n))
    (hu0 : ∀ x ∈ unitSphere n, u x = 0)
    (hPos : ∀ x ∈ closedUnitBall n, (dirichletWithinComplexHessian u x).PosDef)
    (hf : ContinuousOn f (closedUnitBall n))
    (hEq : ∀ x ∈ unitBall n, (complexHessian u x).det.re = f x)
    (S : E n →L[ℝ] E n) (hS : star S = -S) (hJ : ∀ x, S (J x) = J (S x)) :
    ∃ δ > (0 : ℝ), ∃ C ≥ (0 : ℝ), ∀ t : ℝ, t ≠ 0 → |t| < δ →
      (∫ x in unitBall n, ∑ i, ∑ j,
        (dirichletWithinRealHessian
          (dirichletOrthogonalDifference (orthogonalFlow S hS t) t u) x
            (e[n] i) (e[n] j)) ^ 2 ∂volume0 n) ≤
        C * ∫ x in unitBall n,
          (dirichletOrthogonalDifference (orthogonalFlow S hS t) t f x) ^ 2 ∂volume0 n := by
  obtain ⟨ε, hε, C, hC, hEstimate⟩ :=
    exists_dirichlet_closedBall_cofactor_perturbation_estimate hn hu huS hu0 hPos
  obtain ⟨δ, hδ, hClose⟩ := Metric.eventually_nhds_iff.mp
    (eventually_dirichlet_unitary_meanCofactor_close hu S hS hε)
  refine ⟨δ, hδ, C, hC, ?_⟩
  intro t _ ht
  let R := orthogonalFlow S hS t
  let q := dirichletOrthogonalDifference R t u
  let g := dirichletOrthogonalDifference R t f
  let a (x : E n) := dirichletMeanCofactor (dirichletWithinComplexHessian u x)
    (dirichletUnitaryPulledHessian u S hS t x)
  have hNear := hClose (show dist t 0 < δ by simpa only [dist_zero_right, Real.norm_eq_abs] using ht)
  apply hEstimate (a := a)
    (contDiffOn_dirichletOrthogonalDifference R t hu)
    (contDiffOn_dirichletOrthogonalDifference_ball R t huS)
  · intro x hx
    have hRx := orthogonalFlow_mapsTo_unitSphere S hS t hx
    simp only [dirichletOrthogonalDifference, hu0 x hx, hu0 (R x) hRx, sub_self, zero_div]
  · exact continuousOn_dirichletOrthogonalDifference R t hf
  · intro x hx
    exact (hNear x (ball_subset_closedBall hx)).le
  · intro x hx
    dsimp only [a]
    rw [dirichletContractionCLM_apply, dirichletWithinRealHessian_eq_on_ball _ hx,
      dirichletWithinComplexHessian_eq_on_ball_of_C2 hu hx,
      dirichletUnitaryPulledHessian_eq_on_ball hu S hS t hx]
    exact dirichlet_unitary_difference_determinant_equation R
      (orthogonalFlow_apply_J S hS hJ t) t hu hEq hx

theorem abs_dirichletOrthogonalDifference_flow_le {n : ℕ} {f : E n → ℝ} {K : ℝ≥0}
    (hf : LipschitzOnWith K f (closedUnitBall n))
    (S : E n →L[ℝ] E n) (hS : star S = -S) {t : ℝ} (ht : t ≠ 0)
    {x : E n} (hx : x ∈ closedUnitBall n) :
    |dirichletOrthogonalDifference (orthogonalFlow S hS t) t f x| ≤ (K : ℝ) * ‖S‖ := by
  let R := orthogonalFlow S hS t
  let L := R.toContinuousLinearEquiv.toContinuousLinearMap
  have hMove : dist (R x) x ≤ ‖S‖ * |t| := by
    change ‖(L - ContinuousLinearMap.id ℝ (E n)) x‖ ≤ _
    exact ((L - ContinuousLinearMap.id ℝ (E n)).le_opNorm x).trans
      ((mul_le_of_le_one_right (norm_nonneg _) (mem_closedBall_zero_iff.mp hx)).trans
        (norm_orthogonalFlow_sub_id_le S hS t))
  have hLip := hf.dist_le_mul _ (orthogonalFlow_mapsTo_closedUnitBall S hS t hx) _ hx
  have hBound : |f (R x) - f x| ≤ (K : ℝ) * (‖S‖ * |t|) := by
    simpa only [Real.dist_eq] using hLip.trans (mul_le_mul_of_nonneg_left hMove K.coe_nonneg)
  rw [dirichletOrthogonalDifference, abs_div]
  apply (div_le_iff₀ (abs_pos.mpr ht)).mpr
  exact hBound.trans_eq (mul_assoc _ _ _).symm

theorem exists_dirichlet_unitary_difference_uniform_hessian_bound {n : ℕ}
    (hn : 0 < n) {u f : E n → ℝ}
    (hu : ContDiffOn ℝ 2 u (closedUnitBall n))
    (huS : ContDiffOn ℝ ∞ u (unitBall n))
    (hu0 : ∀ x ∈ unitSphere n, u x = 0)
    (hPos : ∀ x ∈ closedUnitBall n, (dirichletWithinComplexHessian u x).PosDef)
    {K : ℝ≥0} (hf : LipschitzOnWith K f (closedUnitBall n))
    (hEq : ∀ x ∈ unitBall n, (complexHessian u x).det.re = f x)
    (S : E n →L[ℝ] E n) (hS : star S = -S) (hJ : ∀ x, S (J x) = J (S x)) :
    ∃ δ > (0 : ℝ), ∃ C ≥ (0 : ℝ), ∀ t : ℝ, t ≠ 0 → |t| < δ →
      (∫ x in unitBall n, ∑ i, ∑ j,
        (dirichletWithinRealHessian
          (dirichletOrthogonalDifference (orthogonalFlow S hS t) t u) x
            (e[n] i) (e[n] j)) ^ 2 ∂volume0 n) ≤ C := by
  obtain ⟨δ, hδ, C, hC, hEstimate⟩ := exists_dirichlet_unitary_difference_hessian_estimate
    hn hu huS hu0 hPos hf.continuousOn hEq S hS hJ
  refine ⟨δ, hδ, C * ((K : ℝ) * ‖S‖) ^ 2, by positivity, ?_⟩
  intro t ht hSmall
  apply (hEstimate t ht hSmall).trans
  apply mul_le_mul_of_nonneg_left _ hC
  let μ := (volume0 n).restrict (unitBall n)
  let g := dirichletOrthogonalDifference (orthogonalFlow S hS t) t f
  have hg : ContinuousOn g (closedUnitBall n) :=
    continuousOn_dirichletOrthogonalDifference _ t hf.continuousOn
  letI : NeZero n := ⟨hn.ne'⟩
  letI : IsProbabilityMeasure μ := volume0_restrict_isProbability n
  have hgInt : Integrable (fun x => (g x) ^ 2) μ :=
    (dirichlet_memLp_of_continuousOn hn (hg.pow 2) 1).integrable le_rfl
  have h := integral_mono_ae hgInt (integrable_const (((K : ℝ) * ‖S‖) ^ 2)) (by
    filter_upwards [ae_restrict_mem (μ := volume0 n)
      (show MeasurableSet (unitBall n) from measurableSet_ball)] with x hx
    have hBound := pow_le_pow_left₀ (abs_nonneg (g x))
      (abs_dirichletOrthogonalDifference_flow_le hf S hS ht (ball_subset_closedBall hx)) 2
    simpa only [sq_abs] using hBound)
  simpa only [integral_const, probReal_univ, one_smul] using h

/-- A C1 prescribed density supplies the Lipschitz hypothesis on the actual
closed ball; no extension of the C2 potential is required. -/
theorem exists_dirichlet_unitary_difference_uniform_hessian_bound_of_C1_density {n : ℕ}
    (hn : 0 < n) {u f : E n → ℝ}
    (hu : ContDiffOn ℝ 2 u (closedUnitBall n))
    (huS : ContDiffOn ℝ ∞ u (unitBall n))
    (hu0 : ∀ x ∈ unitSphere n, u x = 0)
    (hPos : ∀ x ∈ closedUnitBall n, (dirichletWithinComplexHessian u x).PosDef)
    (hf : ContDiffOn ℝ 1 f (closedUnitBall n))
    (hEq : ∀ x ∈ unitBall n, (complexHessian u x).det.re = f x)
    (S : E n →L[ℝ] E n) (hS : star S = -S) (hJ : ∀ x, S (J x) = J (S x)) :
    ∃ δ > (0 : ℝ), ∃ C ≥ (0 : ℝ), ∀ t : ℝ, t ≠ 0 → |t| < δ →
      (∫ x in unitBall n, ∑ i, ∑ j,
        (dirichletWithinRealHessian
          (dirichletOrthogonalDifference (orthogonalFlow S hS t) t u) x
            (e[n] i) (e[n] j)) ^ 2 ∂volume0 n) ≤ C := by
  obtain ⟨K, hK⟩ := hf.exists_lipschitzOnWith (by norm_num)
    (convex_closedBall _ _) (isCompact_closedBall _ _)
  exact exists_dirichlet_unitary_difference_uniform_hessian_bound
    hn hu huS hu0 hPos hK hEq S hS hJ

end KEBall

