import KEBall.DirichletAngularPotentialHessian

/-!
# L2 Hessian bounds for the twice angular differentiated actual potential

The finite energy of the actual interior derivative is obtained from Fatou,
not assumed when interpreting the limiting real integral.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Filter Matrix MeasureTheory Metric Set
open scoped BigOperators ComplexOrder ContDiff Topology

namespace KEBall

local notation "e[" n "]" => EuclideanSpace.basisFun (Fin (2 * n)) ℝ

theorem memLp_realHessian_of_dirichlet_discrete_energy_limit {n : ℕ} (hn : 0 < n)
    {w : E n → ℝ} (hw : ContDiffOn ℝ ∞ w (unitBall n))
    {v : ℕ → E n → ℝ} (hv : ∀ m, ContDiffOn ℝ 2 (v m) (closedUnitBall n))
    (hLim : ∀ x ∈ unitBall n, ∀ i j : Fin (2 * n),
      Tendsto (fun m => dirichletWithinRealHessian (v m) x (e[n] i) (e[n] j)) atTop
        (𝓝 (realHessian w x (e[n] i) (e[n] j))))
    {C : ℝ} (hC : 0 ≤ C)
    (hBound : ∀ᶠ m in atTop, (∫ x in unitBall n, ∑ i, ∑ j,
      (dirichletWithinRealHessian (v m) x (e[n] i) (e[n] j)) ^ 2 ∂volume0 n) ≤ C) :
    MemLp (realHessian w) 2 ((volume0 n).restrict (unitBall n)) ∧
      (∫ x in unitBall n, ∑ i, ∑ j,
        (realHessian w x (e[n] i) (e[n] j)) ^ 2 ∂volume0 n) ≤ C := by
  let P (m : ℕ) (x : E n) := ∑ i, ∑ j,
    (dirichletWithinRealHessian (v m) x (e[n] i) (e[n] j)) ^ 2
  let G (x : E n) := ∑ i, ∑ j, (realHessian w x (e[n] i) (e[n] j)) ^ 2
  have hHC : ContinuousOn (realHessian w) (unitBall n) :=
    fun x hx => (realHessian_contDiffAt (hw.contDiffAt (isOpen_ball.mem_nhds hx))).continuousAt.continuousWithinAt
  have hGC : ContinuousOn G (unitBall n) := by
    apply continuousOn_finsetSum
    intro i _
    apply continuousOn_finsetSum
    intro j _
    exact ((hHC.clm_apply continuousOn_const).clm_apply continuousOn_const).pow 2
  have hPC (m : ℕ) : ContinuousOn (P m) (closedUnitBall n) := by
    apply continuousOn_finsetSum
    intro i _
    apply continuousOn_finsetSum
    intro j _
    exact (((continuousOn_dirichletWithinRealHessian (hv m)).clm_apply
      continuousOn_const).clm_apply continuousOn_const).pow 2
  letI : NeZero n := ⟨hn.ne'⟩
  letI : IsProbabilityMeasure ((volume0 n).restrict (unitBall n)) :=
    volume0_restrict_isProbability n
  have hInt (m : ℕ) : IntegrableOn (P m) (unitBall n) (volume0 n) :=
    (dirichlet_memLp_of_continuousOn hn (hPC m) 1).integrable le_rfl
  have hP0 (m : ℕ) (x : E n) : 0 ≤ P m x := by dsimp [P]; positivity
  have hG0 (x : E n) : 0 ≤ G x := by dsimp [G]; positivity
  have hPLim : ∀ᵐ x ∂(volume0 n).restrict (unitBall n),
      Tendsto (fun m => P m x) atTop (𝓝 (G x)) := by
    filter_upwards [ae_restrict_mem (μ := volume0 n) measurableSet_ball] with x hx
    exact tendsto_finsetSum _ (fun i _ => tendsto_finsetSum _ (fun j _ => (hLim x hx i j).pow 2))
  have hE := dirichlet_integrable_and_integral_le_of_ae_tendsto_nonneg hC hInt
    (hGC.aestronglyMeasurable measurableSet_ball)
    (fun m => Eventually.of_forall (hP0 m)) (Eventually.of_forall hG0) hPLim hBound
  have hH : AEStronglyMeasurable (realHessian w) ((volume0 n).restrict (unitBall n)) :=
    hHC.aestronglyMeasurable measurableSet_ball
  have hNorm : IntegrableOn (fun x => ‖realHessian w x‖ ^ 2) (unitBall n) (volume0 n) := by
    apply (hE.1.const_mul ((2 * n : ℝ) ^ 2)).mono' (hH.norm.pow 2)
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact norm_dirichlet_bilinear_sq_le_sum_entries (realHessian w x)
  exact ⟨(memLp_two_iff_integrable_sq_norm hH).mpr hNorm, hE.2⟩

theorem memLp_realHessian_secondAngularDerivative_of_C2_solution {n : ℕ}
    (hn : 0 < n) {u f : E n → ℝ}
    (hu : ContDiffOn ℝ 2 u (closedUnitBall n))
    (huS : ContDiffOn ℝ ∞ u (unitBall n))
    (hu0 : ∀ x ∈ unitSphere n, u x = 0)
    (hPos : ∀ x ∈ closedUnitBall n, (dirichletWithinComplexHessian u x).PosDef)
    (hf : SmoothNear (closedUnitBall n) f)
    (hEq : ∀ x ∈ unitBall n, (complexHessian u x).det.re = f x)
    (S : E n →L[ℝ] E n) (hS : star S = -S) (hJ : ∀ x, S (J x) = J (S x)) :
    MemLp (realHessian (fun y => fderiv ℝ (fun z => fderiv ℝ u z (S z)) y (S y)))
      2 ((volume0 n).restrict (unitBall n)) := by
  obtain ⟨δ, hδ, C, hC, hBound⟩ :=
    exists_dirichlet_unitary_second_difference_uniform_hessian_bound hn hu huS hu0 hPos hf hEq S hS hJ
  let t (m : ℕ) : ℝ := 1 / ((m : ℝ) + 1)
  let v (m : ℕ) := dirichletOrthogonalDifference (orthogonalFlow S hS (t m)) (t m)
    (dirichletOrthogonalDifference (orthogonalFlow S hS (t m)) (t m) u)
  have htPos (m : ℕ) : 0 < t m := by dsimp [t]; positivity
  have ht : Tendsto t atTop (𝓝 (0 : ℝ)) := tendsto_one_div_add_atTop_nhds_zero_nat
  have htPunct : Tendsto t atTop (𝓝[≠] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨ht, Eventually.of_forall (fun m => (htPos m).ne')⟩
  have hSmall : ∀ᶠ m in atTop, |t m| < δ :=
    ht.abs.eventually_lt_const (show |(0 : ℝ)| < δ by simpa using hδ)
  have hw : ContDiffOn ℝ ∞
      (fun y => fderiv ℝ (fun z => fderiv ℝ u z (S z)) y (S y)) (unitBall n) :=
    (((huS.fderiv_of_isOpen isOpen_ball (m := ∞) (by simp)).clm_apply
      S.contDiff.contDiffOn).fderiv_of_isOpen isOpen_ball (m := ∞) (by simp)).clm_apply
        S.contDiff.contDiffOn
  have hv (m : ℕ) : ContDiffOn ℝ 2 (v m) (closedUnitBall n) :=
    contDiffOn_dirichletOrthogonalDifference _ _ (contDiffOn_dirichletOrthogonalDifference _ _ hu)
  have hLimit (x : E n) (hx : x ∈ unitBall n) (i j : Fin (2 * n)) :
      Tendsto (fun m => dirichletWithinRealHessian (v m) x (e[n] i) (e[n] j)) atTop
        (𝓝 (realHessian (fun y => fderiv ℝ (fun z => fderiv ℝ u z (S z)) y (S y))
          x (e[n] i) (e[n] j))) := by
    simp_rw [dirichletWithinRealHessian_eq_on_ball _ hx]
    exact (tendsto_realHessian_secondOrthogonalDifference_flow_entry huS S hS hx (e[n] i) (e[n] j)).comp htPunct
  apply (memLp_realHessian_of_dirichlet_discrete_energy_limit hn hw hv hLimit hC ?_).1
  filter_upwards [hSmall] with m hm
  exact hBound (t m) (htPos m).ne' hm

theorem memLp_realHessian_firstAngularDerivative_of_C2_solution {n : ℕ}
    (hn : 0 < n) {u f : E n → ℝ}
    (hu : ContDiffOn ℝ 2 u (closedUnitBall n))
    (huS : ContDiffOn ℝ ∞ u (unitBall n))
    (hu0 : ∀ x ∈ unitSphere n, u x = 0)
    (hPos : ∀ x ∈ closedUnitBall n, (dirichletWithinComplexHessian u x).PosDef)
    (hf : SmoothNear (closedUnitBall n) f)
    (hEq : ∀ x ∈ unitBall n, (complexHessian u x).det.re = f x)
    (S : E n →L[ℝ] E n) (hS : star S = -S) (hJ : ∀ x, S (J x) = J (S x)) :
    MemLp (realHessian (fun y => fderiv ℝ u y (S y)))
      2 ((volume0 n).restrict (unitBall n)) := by
  have hf1 : ContDiffOn ℝ 1 f (closedUnitBall n) := by
    intro x hx
    exact ((hf.contDiffAt hx).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1)).contDiffWithinAt
  obtain ⟨δ, hδ, C, hC, hBound⟩ :=
    exists_dirichlet_unitary_difference_uniform_hessian_bound_of_C1_density
      hn hu huS hu0 hPos hf1 hEq S hS hJ
  let t (m : ℕ) : ℝ := 1 / ((m : ℝ) + 1)
  let v (m : ℕ) := dirichletOrthogonalDifference (orthogonalFlow S hS (t m)) (t m) u
  have htPos (m : ℕ) : 0 < t m := by dsimp [t]; positivity
  have ht : Tendsto t atTop (𝓝 (0 : ℝ)) := tendsto_one_div_add_atTop_nhds_zero_nat
  have htPunct : Tendsto t atTop (𝓝[≠] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨ht, Eventually.of_forall (fun m => (htPos m).ne')⟩
  have hSmall : ∀ᶠ m in atTop, |t m| < δ :=
    ht.abs.eventually_lt_const (show |(0 : ℝ)| < δ by simpa using hδ)
  have hw : ContDiffOn ℝ ∞ (fun y => fderiv ℝ u y (S y)) (unitBall n) :=
    (huS.fderiv_of_isOpen isOpen_ball (m := ∞) (by simp)).clm_apply S.contDiff.contDiffOn
  have hv (m : ℕ) : ContDiffOn ℝ 2 (v m) (closedUnitBall n) :=
    contDiffOn_dirichletOrthogonalDifference _ _ hu
  have hLimit (x : E n) (hx : x ∈ unitBall n) (i j : Fin (2 * n)) :
      Tendsto (fun m => dirichletWithinRealHessian (v m) x (e[n] i) (e[n] j)) atTop
        (𝓝 (realHessian (fun y => fderiv ℝ u y (S y)) x (e[n] i) (e[n] j))) := by
    simp_rw [dirichletWithinRealHessian_eq_on_ball _ hx]
    exact (tendsto_realHessian_firstOrthogonalDifference_flow_entry huS S hS hx (e[n] i) (e[n] j)).comp htPunct
  apply (memLp_realHessian_of_dirichlet_discrete_energy_limit hn hw hv hLimit hC ?_).1
  filter_upwards [hSmall] with m hm
  exact hBound (t m) (htPos m).ne' hm

end KEBall
