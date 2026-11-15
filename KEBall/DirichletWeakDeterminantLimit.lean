import KEBall.DirichletWeakThirdPath
import KEBall.DirichletThirdDetEquation

/-! Differentiating the determinant in the distributional limit. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8

open Filter InnerProductSpace Matrix MeasureTheory Metric Set
open scoped ComplexOrder ContDiff Distributions Matrix.Norms.Elementwise NNReal Topology

namespace KEBall

local notation "ν[" n "]" => Measure.restrict (volume0 n) (unitBall n)
local notation "e[" n "]" => EuclideanSpace.basisFun (Fin (2 * n)) ℝ
local notation "𝓓B[" n "]" => 𝓓(dirichletBallOpens n, ℝ)

/-- The (L^2) weak cluster limit of a bounded sequence can be paired with
strongly convergent coefficients in the same Hilbert space. -/
private theorem tendsto_inner_of_tendsto_and_weak {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {u v : ℕ → H} {x y : H} {C : ℝ}
    (hu : ∀ m, ‖u m‖ ≤ C)
    (hWeak : Tendsto (fun m => inner ℝ y (u m)) atTop (𝓝 (inner ℝ y x)))
    (hStrong : Tendsto v atTop (𝓝 y)) :
    Tendsto (fun m => inner ℝ (v m) (u m)) atTop (𝓝 (inner ℝ y x)) := by
  have hD : Tendsto (fun m => inner ℝ (v m - y) (u m)) atTop (𝓝 (0 : ℝ)) := by
    apply squeeze_zero_norm'
    · filter_upwards [] with m
      exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (hu m) (norm_nonneg _))
    · simpa only [sub_self, norm_zero, zero_mul] using (hStrong.sub_const y).norm.mul_const C
  have h := hD.add hWeak
  simp only [zero_add, inner_sub_left, sub_add_cancel] at h
  exact h

/-- Weak clustering commutes with taking a strong limit of the left factor
in a bounded real Hilbert pairing. -/
theorem MapClusterPt.inner_of_tendsto_weak {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {u v : ℕ → H} {x y : H} {C : ℝ}
    (hu : ∀ m, ‖u m‖ ≤ C)
    (hWeak : MapClusterPt (toWeakSpace ℝ H x) atTop (fun m => toWeakSpace ℝ H (u m)))
    (hStrong : Tendsto v atTop (𝓝 y)) :
    MapClusterPt (inner ℝ y x) atTop (fun m => inner ℝ (v m) (u m)) := by
  let E : H →L[ℝ] ℝ := innerSL ℝ y
  have hE : Continuous (fun z : WeakSpace ℝ H => E ((toWeakSpace ℝ H).symm z)) :=
    WeakBilin.eval_continuous (topDualPairing ℝ H).flip E
  have h := MapClusterPt.continuousAt_comp (X := WeakSpace ℝ H) hE.continuousAt hWeak
  change MapClusterPt (E ((toWeakSpace ℝ H).symm (toWeakSpace ℝ H x))) atTop
    (fun m => E ((toWeakSpace ℝ H).symm (toWeakSpace ℝ H (u m)))) at h
  simp only [LinearEquiv.symm_apply_apply] at h
  obtain ⟨φ, hφ, hT⟩ := h.tendsto_subseq
  have hPair := tendsto_inner_of_tendsto_and_weak (fun m => hu (φ m))
    (show Tendsto (fun m => inner ℝ y (u (φ m))) atTop (𝓝 (inner ℝ y x)) from hT)
    (hStrong.comp hφ.tendsto_atTop)
  exact (hPair.mapClusterPt).of_comp hφ.tendsto_atTop

abbrev DirichletBilinearCoordinates (n : ℕ) :=
  EuclideanSpace ℝ (Fin (2 * n) × Fin (2 * n))

/-- Real bilinear forms in orthonormal coordinates. -/
noncomputable def dirichletBilinearCoordinates {n : ℕ} (B : E n →L[ℝ] E n →L[ℝ] ℝ) :
    DirichletBilinearCoordinates n :=
  WithLp.toLp 2 fun jk => B (e[n] jk.1) (e[n] jk.2)

private noncomputable def realBilinearBasis {n : ℕ} (jk : Fin (2 * n) × Fin (2 * n)) :
    E n →L[ℝ] E n →L[ℝ] ℝ :=
  (innerSL ℝ (e[n] jk.1)).smulRight (innerSL ℝ (e[n] jk.2))

private theorem sum_realBilinearBasis {n : ℕ} (B : E n →L[ℝ] E n →L[ℝ] ℝ) :
    ∑ jk : Fin (2 * n) × Fin (2 * n), dirichletBilinearCoordinates B jk • realBilinearBasis jk =
      B := by
  ext x y
  simp only [_root_.sum_apply, _root_.smul_apply, smul_eq_mul,
    Fintype.sum_prod_type, dirichletBilinearCoordinates,
    realBilinearBasis, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]
  have hx := (e[n]).sum_repr' x
  have hy := (e[n]).sum_repr' y
  conv_rhs => rw [← hx, ← hy]
  simp only [map_sum, map_smul, _root_.sum_apply, _root_.smul_apply,
    smul_eq_mul]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm (f := fun k j => ⟪e[n] k, y⟫_ℝ * (⟪e[n] j, x⟫_ℝ * B (e[n] j) (e[n] k)))]
  congr 1
  ext j
  apply Finset.sum_congr rfl
  intro k _
  ring

private noncomputable def cofactorBilinearLinearMap {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    (E n →L[ℝ] E n →L[ℝ] ℝ) →ₗ[ℝ] ℝ where
  toFun B := (A.adjugate * complexHessianOfRealBilinear B).trace.re
  map_add' B D := by
    have h : complexHessianOfRealBilinear (B + D) =
        complexHessianOfRealBilinear B + complexHessianOfRealBilinear D := by
      ext i j
      simp only [complexHessianOfRealBilinear, Matrix.add_apply, _root_.add_apply,
        Complex.ofReal_add]
      ring
    rw [h, mul_add, Matrix.trace_add, Complex.add_re]
  map_smul' c B := by
    have h : complexHessianOfRealBilinear (c • B) = c • complexHessianOfRealBilinear B := by
      ext i j
      simp only [complexHessianOfRealBilinear, Matrix.smul_apply, _root_.smul_apply,
        smul_eq_mul, Complex.ofReal_mul, Complex.real_smul]
      ring
    rw [h, Matrix.mul_smul, Matrix.trace_smul, Complex.smul_re]
    rfl

/-- Coordinates of the derivative of the real determinant as a functional on real Hessians. -/
noncomputable def dirichletCofactorCoordinates {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    DirichletBilinearCoordinates n :=
  WithLp.toLp 2 fun jk => cofactorBilinearLinearMap A (realBilinearBasis jk)

theorem inner_dirichletCofactorCoordinates {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (B : E n →L[ℝ] E n →L[ℝ] ℝ) :
    inner ℝ (dirichletCofactorCoordinates A) (dirichletBilinearCoordinates B) =
      (A.adjugate * complexHessianOfRealBilinear B).trace.re := by
  change _ = cofactorBilinearLinearMap A B
  conv_rhs => rw [← sum_realBilinearBasis B, map_sum]
  simp only [PiLp.inner_apply, Real.inner_apply, dirichletCofactorCoordinates,
    map_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro jk _
  exact mul_comm _ _

theorem continuous_dirichletCofactorCoordinates {n : ℕ} :
    Continuous (@dirichletCofactorCoordinates n) := by
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro jk
  change Continuous (fun A : Matrix (Fin n) (Fin n) ℂ =>
    (A.adjugate * complexHessianOfRealBilinear (realBilinearBasis jk)).trace.re)
  apply Complex.continuous_re.comp
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    (continuous_id.matrix_adjugate.matrix_elem i j).mul continuous_const

private theorem l2_norm_sq_eq_integral {n : ℕ} {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (F : DirichletBallL2 n V) :
    ‖F‖ ^ 2 = ∫ x, ‖F x‖ ^ 2 ∂ν[n] := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

theorem tendsto_dirichletBallL2_of_ae_tendsto_of_bound {n : ℕ} (hn : 0 < n)
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    {U : ℕ → DirichletBallL2 n V} {F : DirichletBallL2 n V} {C : ℝ}
    (hU : ∀ m, ∀ᵐ x ∂ν[n], ‖U m x‖ ≤ C)
    (hAe : ∀ᵐ x ∂ν[n], Tendsto (fun m => U m x) atTop (𝓝 (F x))) :
    Tendsto U atTop (𝓝 F) := by
  have : NeZero n := ⟨hn.ne'⟩
  have hCountable := ae_all_iff.mpr hU
  have hF : ∀ᵐ x ∂ν[n], ‖F x‖ ≤ C := by
    filter_upwards [hCountable, hAe] with x hx hLim
    exact le_of_tendsto' hLim.norm hx
  have hInt : Tendsto (fun m => ∫ x, ‖U m x - F x‖ ^ 2 ∂ν[n]) atTop (𝓝 (0 : ℝ)) := by
    rw [show (0 : ℝ) = ∫ _ : E n, (0 : ℝ) ∂ν[n] from (integral_zero (μ := ν[n]) (G := ℝ)).symm]
    apply tendsto_integral_filter_of_norm_le_const
    · exact Eventually.of_forall fun m => (((Lp.aestronglyMeasurable (U m)).sub
        (Lp.aestronglyMeasurable F)).norm.pow 2)
    · refine ⟨(C + C) ^ 2, Eventually.of_forall fun m => ?_⟩
      filter_upwards [hU m, hF] with x hx hy
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _)
        ((norm_sub_le _ _).trans (add_le_add hx hy)) 2
    · filter_upwards [hAe] with x hx
      simpa only [sub_self, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)] using
        (hx.sub_const (F x)).norm.pow 2
  have hEq (m : ℕ) : (∫ x, ‖U m x - F x‖ ^ 2 ∂ν[n]) = ‖U m - F‖ ^ 2 := by
    rw [l2_norm_sq_eq_integral]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (U m) F] with x hx
    change (U m - F) x = U m x - F x at hx
    rw [hx]
  have hNorm := ((hInt.congr hEq).sqrt : Tendsto (fun m => Real.sqrt (‖U m - F‖ ^ 2)) atTop
    (𝓝 (Real.sqrt 0)))
  have hN : Tendsto (fun m => ‖U m - F‖) atTop (𝓝 0) := by
    simpa only [Real.sqrt_zero, Real.sqrt_sq (norm_nonneg _)] using hNorm
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hN

/-- The third derivatives in a fixed direction admit one weak cluster point
for all the Hessian coordinates together. -/
theorem exists_weakCluster_realThirdDerivative_of_direction {n : ℕ} (hn : 0 < n)
    {u : ℕ → E n → ℝ} (hu : ∀ m, SmoothNear (closedUnitBall n) (u m)) {C : ℝ}
    (hBound : ∀ m, (∫ x, ∑ i, ∑ j, ∑ k,
      (realThirdDerivative (u m) x (e[n] i) (e[n] j) (e[n] k)) ^ 2 ∂ν[n]) ≤ C)
    (v : E n) :
    ∃ (F : DirichletBallL2 n (DirichletBilinearCoordinates n))
      (Q : ℕ → DirichletBallL2 n (DirichletBilinearCoordinates n)),
      (∀ m, Q m =ᵐ[ν[n]] fun x => dirichletBilinearCoordinates (realThirdDerivative (u m) x v)) ∧
      (∀ m, ‖Q m‖ ≤ Real.sqrt (‖v‖ ^ 2 * C)) ∧
      MapClusterPt (toWeakSpace ℝ _ F) atTop (fun m => toWeakSpace ℝ _ (Q m)) := by
  have : NeZero n := ⟨hn.ne'⟩
  let g (m : ℕ) (x : E n) := dirichletBilinearCoordinates (realThirdDerivative (u m) x v)
  have hC (m : ℕ) (a : E n) (j k : Fin (2 * n)) : ContinuousOn
      (fun x => realThirdDerivative (u m) x a (e[n] j) (e[n] k)) (closedUnitBall n) := by
    obtain ⟨U, hU, hSub, huU⟩ := hu m
    have h₁ := huU.fderiv_of_isOpen hU (m := ∞) (by simp)
    have h₂ := h₁.fderiv_of_isOpen hU (m := ∞) (by simp)
    have h₃ := h₂.fderiv_of_isOpen hU (m := ∞) (by simp)
    exact ((((h₃.clm_apply contDiffOn_const).clm_apply contDiffOn_const).clm_apply
      contDiffOn_const).continuousOn).mono hSub
  have hGC (m : ℕ) : ContinuousOn (g m) (closedUnitBall n) :=
    (PiLp.continuous_toLp 2 _).comp_continuousOn (continuousOn_pi.mpr fun jk => hC m v jk.1 jk.2)
  let Q (m : ℕ) := (memLp_continuousOn_dirichletBall hn (hGC m)).toLp (g m)
  have hRep (m : ℕ) : Q m =ᵐ[ν[n]] g m := MemLp.coeFn_toLp _
  have hNorm (m : ℕ) : ‖Q m‖ ≤ Real.sqrt (‖v‖ ^ 2 * C) := by
    have he : ‖Q m‖ ^ 2 = ∫ x, ‖g m x‖ ^ 2 ∂ν[n] := by
      rw [l2_norm_sq_eq_integral]
      exact integral_congr_ae ((hRep m).mono fun x hx => congrArg (fun z => ‖z‖ ^ 2) hx)
    let p (x : E n) := ∑ a, ∑ j, ∑ k, (realThirdDerivative (u m) x (e[n] a) (e[n] j) (e[n] k)) ^ 2
    have hP : ContinuousOn p (closedUnitBall n) :=
      continuousOn_finsetSum Finset.univ fun a _ => continuousOn_finsetSum Finset.univ fun j _ =>
        continuousOn_finsetSum Finset.univ fun k _ => (hC m (e[n] a) j k).pow 2
    have hInt {w : E n → ℝ} (hw : ContinuousOn w (closedUnitBall n)) : Integrable w ν[n] :=
      hw.integrableOn_of_subset_isCompact (isCompact_closedBall _ _) measurableSet_ball
        ball_subset_closedBall (by rw [volume0_unitBall n hn]; exact ENNReal.one_ne_top)
    have hP' (x : E n) : ‖g m x‖ ^ 2 ≤ ‖v‖ ^ 2 * p x := by
      rw [EuclideanSpace.real_norm_sq_eq, Fintype.sum_prod_type]
      have hv : (∑ a, (inner ℝ (e[n] a) v) ^ 2) = ‖v‖ ^ 2 := by
        simpa only [Real.norm_eq_abs, sq_abs] using (e[n]).sum_sq_norm_inner_right v
      have hEntry (j k : Fin (2 * n)) :
          (realThirdDerivative (u m) x v (e[n] j) (e[n] k)) ^ 2 ≤
            ‖v‖ ^ 2 * ∑ a, (realThirdDerivative (u m) x (e[n] a) (e[n] j) (e[n] k)) ^ 2 := by
        have hRep : realThirdDerivative (u m) x v (e[n] j) (e[n] k) =
            ∑ a, inner ℝ (e[n] a) v * realThirdDerivative (u m) x (e[n] a) (e[n] j) (e[n] k) := by
          conv_lhs => rw [← (e[n]).sum_repr' v]
          simp only [map_sum, map_smul, _root_.sum_apply, _root_.smul_apply, smul_eq_mul]
        rw [hRep, ← hv]
        exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _
      calc
        _ ≤ ∑ j, ∑ k, ‖v‖ ^ 2 * ∑ a, (realThirdDerivative (u m) x (e[n] a) (e[n] j) (e[n] k)) ^ 2 :=
          Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => hEntry j k
        _ = _ := by
          simp only [p, Finset.mul_sum]
          let T (j k a : Fin (2 * n)) := ‖v‖ ^ 2 *
            (realThirdDerivative (u m) x (e[n] a) (e[n] j) (e[n] k)) ^ 2
          change (∑ j, ∑ k, ∑ a, T j k a) = ∑ a, ∑ j, ∑ k, T j k a
          calc
            _ = ∑ j, ∑ a, ∑ k, T j k a := by
              apply Finset.sum_congr rfl
              intro j _
              exact Finset.sum_comm
            _ = _ := Finset.sum_comm
    have hMul : Integrable (fun x => ‖v‖ ^ 2 * p x) ν[n] := (hInt hP).const_mul _
    apply Real.le_sqrt_of_sq_le
    rw [he]
    refine (integral_mono (hInt ((hGC m).norm.pow 2)) hMul hP').trans ?_
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left (hBound m) (sq_nonneg _)
  obtain ⟨F, hF⟩ := realHilbert_exists_weakClusterPoint_of_bound hNorm
  exact ⟨F, Q, hRep, hNorm, hF⟩

/-- The third derivatives in a fixed direction admit one weak cluster point
for all the Hessian coordinates together. -/
theorem exists_weakCluster_realThirdDerivative {n : ℕ} (hn : 0 < n)
    {u : ℕ → E n → ℝ} (hu : ∀ m, SmoothNear (closedUnitBall n) (u m)) {C : ℝ}
    (hBound : ∀ m, (∫ x, ∑ i, ∑ j, ∑ k,
      (realThirdDerivative (u m) x (e[n] i) (e[n] j) (e[n] k)) ^ 2 ∂ν[n]) ≤ C)
    (i : Fin (2 * n)) :
    ∃ (F : DirichletBallL2 n (DirichletBilinearCoordinates n))
      (Q : ℕ → DirichletBallL2 n (DirichletBilinearCoordinates n)),
      (∀ m, Q m =ᵐ[ν[n]] fun x => dirichletBilinearCoordinates (realThirdDerivative (u m) x (e[n] i))) ∧
      (∀ m, ‖Q m‖ ≤ Real.sqrt C) ∧
      MapClusterPt (toWeakSpace ℝ _ F) atTop (fun m => toWeakSpace ℝ _ (Q m)) := by
  simpa only [OrthonormalBasis.norm_eq_one, one_pow, one_mul] using
    exists_weakCluster_realThirdDerivative_of_direction hn hu hBound (e[n] i)

/-- A bounded family of matrices converging almost everywhere has strongly
convergent cofactor coefficients after multiplication by a test function. -/
private theorem exists_tendsto_dirichletCofactorCoordinates_test {n : ℕ} (hn : 0 < n)
    {A : ℕ → E n → Matrix (Fin n) (Fin n) ℂ} {B : E n → Matrix (Fin n) (Fin n) ℂ}
    (hA : ∀ m, AEStronglyMeasurable (A m) ν[n]) (hB : AEStronglyMeasurable B ν[n])
    {D : ℝ} (hBound : ∀ m, ∀ᵐ x ∂ν[n], ‖A m x‖ ≤ D)
    (hLim : ∀ᵐ x ∂ν[n], Tendsto (fun m => A m x) atTop (𝓝 (B x)))
    (ψ : 𝓓B[n]) :
    ∃ (P : ℕ → DirichletBallL2 n (DirichletBilinearCoordinates n))
      (p : DirichletBallL2 n (DirichletBilinearCoordinates n)),
      Tendsto P atTop (𝓝 p) ∧
      (∀ m, P m =ᵐ[ν[n]] fun x => ψ x • dirichletCofactorCoordinates (A m x)) ∧
      p =ᵐ[ν[n]] fun x => ψ x • dirichletCofactorCoordinates (B x) := by
  have : NeZero n := ⟨hn.ne'⟩
  have hC := continuous_dirichletCofactorCoordinates (n := n)
  have hF : Continuous (fun p : E n × Matrix (Fin n) (Fin n) ℂ =>
      ψ p.1 • dirichletCofactorCoordinates p.2) :=
    (ψ.continuous.comp continuous_fst).smul (hC.comp continuous_snd)
  obtain ⟨C, hC⟩ := ((isCompact_closedBall (0 : E n) 1).prod
    (isCompact_closedBall (0 : Matrix (Fin n) (Fin n) ℂ) D)).exists_bound_of_continuousOn hF.continuousOn
  have hBall := ae_restrict_mem (μ := volume0 n) (show MeasurableSet (unitBall n) from measurableSet_ball)
  have hBBound : ∀ᵐ x ∂ν[n], ‖B x‖ ≤ D := by
    filter_upwards [ae_all_iff.mpr hBound, hLim] with x hx hL
    exact le_of_tendsto' hL.norm hx
  have hM {M : E n → Matrix (Fin n) (Fin n) ℂ}
      (hM : AEStronglyMeasurable M ν[n]) (hNorm : ∀ᵐ x ∂ν[n], ‖M x‖ ≤ D) :
      MemLp (fun x => ψ x • dirichletCofactorCoordinates (M x)) 2 ν[n] := by
    apply MemLp.of_bound (hF.comp_aestronglyMeasurable
      (continuous_id.aestronglyMeasurable.prodMk hM)) C
    filter_upwards [hBall, hNorm] with x hx hy
    exact hC (x, M x) ⟨ball_subset_closedBall hx, mem_closedBall_zero_iff.mpr hy⟩
  let P (m : ℕ) := (hM (hA m) (hBound m)).toLp (fun x => ψ x • dirichletCofactorCoordinates (A m x))
  let p := (hM hB hBBound).toLp (fun x => ψ x • dirichletCofactorCoordinates (B x))
  have hRep (m : ℕ) : P m =ᵐ[ν[n]] fun x => ψ x • dirichletCofactorCoordinates (A m x) := MemLp.coeFn_toLp _
  have hp : p =ᵐ[ν[n]] fun x => ψ x • dirichletCofactorCoordinates (B x) := MemLp.coeFn_toLp _
  refine ⟨P, p, ?_, hRep, hp⟩
  apply tendsto_dirichletBallL2_of_ae_tendsto_of_bound hn (C := C)
  · intro m
    filter_upwards [hBall, hBound m, hRep m] with x hx hy he
    rw [he]
    exact hC (x, A m x) ⟨ball_subset_closedBall hx, mem_closedBall_zero_iff.mpr hy⟩
  · filter_upwards [ae_all_iff.mpr hRep, hp, hLim] with x hx hy hL
    rw [hy]
    exact (tendsto_const_nhds.smul (continuous_dirichletCofactorCoordinates.continuousAt.tendsto.comp hL)).congr
      (fun m => (hx m).symm)

/-- The differentiated determinant equation passes to a weak third derivative
cluster point when the complex Hessians converge almost everywhere with a uniform bound. -/
theorem integral_test_cofactor_eq_of_weakThirdCluster {n : ℕ} (hn : 0 < n)
    {u f : ℕ → E n → ℝ} {B : E n → Matrix (Fin n) (Fin n) ℂ}
    (hu : ∀ m, SmoothNear (closedUnitBall n) (u m))
    (hEq : ∀ m x, x ∈ unitBall n → (complexHessian (u m) x).det.re = f m x)
    (hB : AEStronglyMeasurable B ν[n])
    {D : ℝ} (hBound : ∀ m x, x ∈ unitBall n → ‖complexHessian (u m) x‖ ≤ D)
    (hLim : ∀ᵐ x ∂ν[n], Tendsto (fun m => complexHessian (u m) x) atTop (𝓝 (B x)))
    (i : Fin (2 * n)) {Q : ℕ → DirichletBallL2 n (DirichletBilinearCoordinates n)}
    {F : DirichletBallL2 n (DirichletBilinearCoordinates n)} {C : ℝ}
    (hQ : ∀ m, Q m =ᵐ[ν[n]] fun x => dirichletBilinearCoordinates (realThirdDerivative (u m) x (e[n] i)))
    (hNorm : ∀ m, ‖Q m‖ ≤ C)
    (hWeak : MapClusterPt (toWeakSpace ℝ _ F) atTop (fun m => toWeakSpace ℝ _ (Q m)))
    (ψ : 𝓓B[n]) {I : ℝ}
    (hRhs : Tendsto (fun m => ∫ x, ψ x * fderiv ℝ (f m) x (e[n] i) ∂ν[n]) atTop (𝓝 I)) :
    (∫ x, ψ x * inner ℝ (dirichletCofactorCoordinates (B x)) (F x) ∂ν[n]) = I := by
  have hBall := ae_restrict_mem (μ := volume0 n) (show MeasurableSet (unitBall n) from measurableSet_ball)
  have hMeas (m : ℕ) : AEStronglyMeasurable (complexHessian (u m)) ν[n] := by
    obtain ⟨U, hU, hSub, huU⟩ := hu m
    have hC : ContinuousOn (complexHessian (u m)) U :=
      continuousOn_pi.mpr fun j => continuousOn_pi.mpr fun k =>
        (complexHessian_contDiffOn hU huU j k).continuousOn
    exact (hC.mono (ball_subset_closedBall.trans hSub)).aestronglyMeasurable measurableSet_ball
  obtain ⟨P, p, hT, hP, hp⟩ := exists_tendsto_dirichletCofactorCoordinates_test hn hMeas hB
    (fun m => hBall.mono fun x hx => hBound m x hx) hLim ψ
  have hLeft : inner ℝ p F =
      ∫ x, ψ x * inner ℝ (dirichletCofactorCoordinates (B x)) (F x) ∂ν[n] := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hp] with x hx
    rw [hx, real_inner_smul_left]
  have hRight (m : ℕ) : inner ℝ (P m) (Q m) = ∫ x, ψ x * fderiv ℝ (f m) x (e[n] i) ∂ν[n] := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hP m, hQ m, hBall] with x hx hy hz
    rw [hx, hy, real_inner_smul_left, inner_dirichletCofactorCoordinates,
      cofactorTrace_realThirdDerivative_eq_fderiv (hu m) (hEq m) hz]
  have h := MapClusterPt.inner_of_tendsto_weak hNorm hWeak hT
  obtain ⟨φ, hφ, hS⟩ := h.tendsto_subseq
  have hR := (hRhs.comp hφ.tendsto_atTop).congr (fun m => (hRight (φ m)).symm)
  exact hLeft.symm.trans (tendsto_nhds_unique hS hR)

/-- Every component of the common weak cluster point is a distributional
derivative of the corresponding strong Hessian limit. -/
theorem integral_test_weakThirdCluster_eq {n : ℕ} (hn : 0 < n)
    {u : ℕ → E n → ℝ} (hu : ∀ m, SmoothNear (closedUnitBall n) (u m))
    (i j k : Fin (2 * n)) {Q : ℕ → DirichletBallL2 n (DirichletBilinearCoordinates n)}
    {F : DirichletBallL2 n (DirichletBilinearCoordinates n)} {C : ℝ}
    (hQ : ∀ m, Q m =ᵐ[ν[n]] fun x => dirichletBilinearCoordinates (realThirdDerivative (u m) x (e[n] i)))
    (hNorm : ∀ m, ‖Q m‖ ≤ C)
    (hWeak : MapClusterPt (toWeakSpace ℝ _ F) atTop (fun m => toWeakSpace ℝ _ (Q m)))
    {H : DirichletBallL2 n ℝ} {R : ℕ → DirichletBallL2 n ℝ}
    (hH : Tendsto R atTop (𝓝 H))
    (hR : ∀ m, R m =ᵐ[ν[n]] fun x => realHessian (u m) x (e[n] j) (e[n] k))
    (ψ : 𝓓B[n]) :
    (∫ x, ψ x * F x (j, k) ∂ν[n]) =
      -(∫ x, fderiv ℝ (ψ : E n → ℝ) x (e[n] i) * H x ∂ν[n]) := by
  have : NeZero n := ⟨hn.ne'⟩
  let p (x : E n) := EuclideanSpace.single (j, k) (ψ x)
  have hP : Continuous p := by
    apply (PiLp.continuous_toLp 2 _).comp
    exact continuous_pi fun l => by
      by_cases h : l = (j, k)
      · subst l
        simpa [Pi.single_apply] using ψ.continuous
      · have hZero : Continuous (fun _ : E n => (0 : ℝ)) := continuous_const
        simpa [Pi.single_apply, h] using hZero
  have hp : MemLp p 2 ν[n] := memLp_continuousOn_dirichletBall hn hP.continuousOn
  let P := hp.toLp p
  have hPRep : P =ᵐ[ν[n]] p := MemLp.coeFn_toLp hp
  have hInner (V : DirichletBallL2 n (DirichletBilinearCoordinates n)) :
      inner ℝ P V = ∫ x, ψ x * V x (j, k) ∂ν[n] := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hPRep] with x hx
    rw [hx, EuclideanSpace.inner_single_left]
    rfl
  let χ := dirichletTestLineDerivative (e[n] i) ψ
  let K : DirichletBallL2 n ℝ →L[ℝ] ℝ := innerSL ℝ (dirichletTestToL2 χ)
  have hK (V : DirichletBallL2 n ℝ) :
      K V = ∫ x, fderiv ℝ (ψ : E n → ℝ) x (e[n] i) * V x ∂ν[n] := by
    change inner ℝ (dirichletTestToL2 χ) V = _
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [dirichletTestToL2_ae χ] with x hx
    rw [hx, Real.inner_apply]
    rfl
  have hEq (m : ℕ) : -(K (R m)) = inner ℝ P (Q m) := by
    rw [hK, hInner]
    calc
      _ = -(∫ x, fderiv ℝ (ψ : E n → ℝ) x (e[n] i) * realHessian (u m) x (e[n] j) (e[n] k) ∂ν[n]) := by
        congr 1
        apply integral_congr_ae
        filter_upwards [hR m] with x hx
        rw [hx]
      _ = ∫ x, ψ x * realThirdDerivative (u m) x (e[n] i) (e[n] j) (e[n] k) ∂ν[n] :=
        (smooth_integral_test_realThirdDerivative hn (hu m) ψ _ _ _).symm
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [hQ m] with x hx
        rw [hx]
        rfl
  have hWeakPair := MapClusterPt.inner_of_tendsto_weak hNorm hWeak
    (tendsto_const_nhds (x := P) (f := (atTop : Filter ℕ)))
  obtain ⟨φ, hφ, hSub⟩ := hWeakPair.tendsto_subseq
  have hStrongPair := ((K.continuous.continuousAt.tendsto.comp (hH.comp hφ.tendsto_atTop)).neg).congr
    (fun m => hEq (φ m))
  rw [← hInner, ← hK]
  exact tendsto_nhds_unique hSub hStrongPair

theorem exists_norm_complexHessian_le_of_logDensityPath {n : ℕ} (hn : 0 < n)
    {g : E n → ℝ} (hg : SmoothNear (closedUnitBall n) g) :
    ∃ D : ℝ, ∀ t ∈ Icc (0 : ℝ) 1, ∀ {u : E n → ℝ},
      SmoothNear (closedUnitBall n) u → (∀ x ∈ unitSphere n, u x = 0) →
      (∀ x ∈ unitBall n, (complexHessian u x).PosDef) →
      (∀ x ∈ unitBall n, (complexHessian u x).det.re = Real.exp (t * g x)) →
      ∀ x ∈ unitBall n, ‖complexHessian u x‖ ≤ D := by
  obtain ⟨a, b, K, M, ha, hb, hK, hM, hBounds⟩ := exists_logDensityPath_bounds hn hg
  let d := (3 * K + 1) / (n : ℝ)
  let C := 2 * b + 4 * b * d +
    (2 * b + 4 * (b ^ n / a ^ (n - 1) + (b * d) ^ 2 / (4 * a)))
  let D := C + ((M + 1) / (n : ℝ)) * b
  have hD : 0 ≤ D := by dsimp [D, C, d]; positivity
  refine ⟨D, fun t ht u hu hu0 huP hEq x hx => ?_⟩
  let f (y : E n) := Real.exp (t * g y)
  have hf : SmoothNear (closedUnitBall n) f := by
    obtain ⟨U, hU, hSub, hgU⟩ := hg
    exact ⟨U, hU, hSub, (contDiffOn_const.mul hgU).exp⟩
  have hDen (y : E n) (hy : y ∈ unitBall n) : a ^ n ≤ f y ∧ f y ≤ b ^ n :=
    (hBounds t ht).1 y (ball_subset_closedBall hy)
  have hLog (y : E n) (hy : y ∈ unitBall n) : ‖fderiv ℝ (fun z => Real.log (f z)) y‖ ≤ K :=
    (hBounds t ht).2.1 y (ball_subset_closedBall hy)
  have hH := abs_realHessian_self_le_of_dirichlet_det hn hu hf hu0 huP hEq ha hb hM hDen
    (fun y hy z hz => abs_realHessian_self_le_on_sphere_of_dirichlet_det hn hu hf hu0 huP hEq
      ha hb hK hDen hLog hy hz)
    (fun y hy => (hBounds t ht).2.2 y (ball_subset_closedBall hy)) x (ball_subset_closedBall hx)
  exact norm_complexHessian_le_of_unit_bound (hu.contDiffAt (ball_subset_closedBall hx)) hD hH

theorem integral_test_fderiv_logDensityPath_tendsto {n : ℕ} (hn : 0 < n)
    {g : E n → ℝ} (hg : SmoothNear (closedUnitBall n) g)
    {t : ℕ → ℝ} {t₀ : ℝ} (ht : ∀ m, t m ∈ Icc (0 : ℝ) 1) (hT : Tendsto t atTop (𝓝 t₀))
    (ψ : 𝓓B[n]) (v : E n) :
    Tendsto (fun m => ∫ x, ψ x * fderiv ℝ (fun y => Real.exp (t m * g y)) x v ∂ν[n]) atTop
      (𝓝 (∫ x, ψ x * fderiv ℝ (fun y => Real.exp (t₀ * g y)) x v ∂ν[n])) := by
  have : NeZero n := ⟨hn.ne'⟩
  obtain ⟨U, hU, hSub, hgU⟩ := hg
  let J (p : ℝ × E n) := ψ p.2 * (Real.exp (p.1 * g p.2) * (p.1 * fderiv ℝ g p.2 v))
  have hJ : ContinuousOn J ((univ : Set ℝ) ×ˢ U) := by
    have hG := hgU.continuousOn.comp (continuousOn_snd : ContinuousOn Prod.snd ((univ : Set ℝ) ×ˢ U))
      (show MapsTo Prod.snd ((univ : Set ℝ) ×ˢ U) U from fun _ hx => hx.2)
    have hDG := ((hgU.fderiv_of_isOpen hU (m := ∞) (by simp)).clm_apply (contDiffOn_const (c := v))).continuousOn.comp
      continuousOn_snd (show MapsTo Prod.snd ((univ : Set ℝ) ×ˢ U) U from fun _ hx => hx.2)
    exact (ψ.continuous.comp continuous_snd).continuousOn.mul
      ((Real.continuous_exp.comp_continuousOn (continuousOn_fst.mul hG)).mul
        (continuousOn_fst.mul hDG))
  have hJ' (r : ℝ) : ContinuousOn (fun x => J (r, x)) (closedUnitBall n) :=
    hJ.comp (continuousOn_const.prodMk continuousOn_id) fun x hx => ⟨mem_univ _, hSub hx⟩
  have hF (r : ℝ) :
      (∫ x, ψ x * fderiv ℝ (fun y => Real.exp (r * g y)) x v ∂ν[n]) =
        ∫ x, J (r, x) ∂ν[n] := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem (μ := volume0 n) (show MeasurableSet (unitBall n) from measurableSet_ball)]
      with x hx
    have h := (hgU.contDiffAt (hU.mem_nhds (hSub (ball_subset_closedBall hx)))).differentiableAt (by simp)
    have hd := (h.hasFDerivAt.const_smul r).exp.fderiv
    change fderiv ℝ (fun y => Real.exp (r * g y)) x = _ at hd
    simp only [hd, J, Pi.smul_apply, smul_eq_mul, _root_.smul_apply]
  simp only [hF]
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod (isCompact_closedBall (0 : E n) 1)).exists_bound_of_continuousOn
    (hJ.mono (show Icc (0 : ℝ) 1 ×ˢ closedUnitBall n ⊆ (univ : Set ℝ) ×ˢ U from prod_mono (subset_univ _) hSub))
  apply tendsto_integral_filter_of_norm_le_const
  · exact Eventually.of_forall fun m => ((hJ' (t m)).mono ball_subset_closedBall).aestronglyMeasurable measurableSet_ball
  · refine ⟨C, Eventually.of_forall fun m => ?_⟩
    filter_upwards [ae_restrict_mem (μ := volume0 n) (show MeasurableSet (unitBall n) from measurableSet_ball)]
      with x hx
    exact hC (t m, x) ⟨ht m, ball_subset_closedBall hx⟩
  · exact Eventually.of_forall fun x =>
      tendsto_const_nhds.mul (((Real.continuous_exp.tendsto _).comp (hT.mul_const (g x))).mul (hT.mul_const (fderiv ℝ g x v)))

/-- The Lipschitz-gradient limit along the log-density path satisfies the
linearized Monge–Ampère equation almost everywhere. The tensor in that equation is the weak derivative of its
actual almost-everywhere real Hessian. -/
theorem exists_dirichlet_limit_with_linearized_det_of_logDensityPath {n : ℕ} (hn : 0 < n)
    {g : E n → ℝ} (hg : SmoothNear (closedUnitBall n) g)
    {t : ℕ → ℝ} {t₀ : ℝ} (ht : ∀ m, t m ∈ Icc (0 : ℝ) 1) (hT : Tendsto t atTop (𝓝 t₀))
    {u : ℕ → E n → ℝ} (hu : ∀ m, SmoothNear (closedUnitBall n) (u m))
    (hu0 : ∀ m x, x ∈ unitSphere n → u m x = 0)
    (huP : ∀ m x, x ∈ unitBall n → (complexHessian (u m) x).PosDef)
    (hEq : ∀ m x, x ∈ unitBall n → (complexHessian (u m) x).det.re = Real.exp (t m * g x)) :
    ∃ (w : E n → ℝ) (G : E n → E n →L[ℝ] ℝ) (L : ℝ≥0),
      (∀ x ∈ unitBall n, HasFDerivAt w (G x) x) ∧ LipschitzOnWith L G (closedUnitBall n) ∧
      (∀ x ∈ unitSphere n, w x = 0) ∧
      (∀ᵐ x ∂ν[n], (complexHessianOfRealBilinear (fderiv ℝ G x)).PosDef ∧
        (complexHessianOfRealBilinear (fderiv ℝ G x)).det.re = Real.exp (t₀ * g x)) ∧
      ∃ F : Fin (2 * n) → DirichletBallL2 n (DirichletBilinearCoordinates n),
        (∀ (i j k : Fin (2 * n)) (η : 𝓓B[n]),
          (∫ x, η x * F i x (j, k) ∂ν[n]) =
            -(∫ x, fderiv ℝ (η : E n → ℝ) x (e[n] i) * fderiv ℝ G x (e[n] j) (e[n] k) ∂ν[n])) ∧
        ∀ i : Fin (2 * n),
          (fun x => inner ℝ (dirichletCofactorCoordinates
            (complexHessianOfRealBilinear (fderiv ℝ G x))) (F i x)) =ᵐ[ν[n]]
              fun x => fderiv ℝ (fun y => Real.exp (t₀ * g y)) x (e[n] i) := by
  have : NeZero n := ⟨hn.ne'⟩
  obtain ⟨φ, w, G, L, hφ, _, hGrad, hD, hLip, hw0, _, _, A, _, ⟨ψ, hψ, hAe⟩, _, hEqA⟩ :=
    exists_dirichlet_C1_and_complexHessian_L2_limit_of_logDensityPath hn hg ht hT hu hu0 huP hEq
  let r (m : ℕ) := φ (ψ m)
  have hr := hφ.comp hψ
  let B (x : E n) := dirichletHessianMatrix (A x)
  have hCont : Continuous (dirichletHessianMatrix (n := n)) :=
    continuous_matrix fun j k => (EuclideanSpace.proj (j, k)).continuous
  have hB : AEStronglyMeasurable B ν[n] := hCont.comp_aestronglyMeasurable (Lp.aestronglyMeasurable A)
  have hLim : ∀ᵐ x ∂ν[n], Tendsto (fun m => complexHessian (u (r m)) x) atTop (𝓝 (B x)) := by
    filter_upwards [hAe] with x hx
    exact ((hCont.tendsto (A x)).comp hx.1).congr (fun m =>
      dirichletHessianMatrix_coordinates (complexHessian (u (r m)) x))
  have hGradient : TendstoUniformlyOn (fun m => fderiv ℝ (u (r m))) G atTop (closedUnitBall n) :=
    fun U hU => hψ.tendsto_atTop.eventually (hGrad U hU)
  obtain ⟨D, hDBound⟩ := exists_norm_complexHessian_le_of_logDensityPath hn hg
  obtain ⟨C, _, hThird⟩ := exists_integral_sq_realThirdDerivative_le_of_logDensityPath hn hg
  obtain ⟨H, R, hH, hR⟩ := exists_realHessian_L2_limit_of_logDensityPath hn hg
    (fun m => ht (r m)) (hT.comp hr.tendsto_atTop) (fun m => hu (r m)) (fun m => hu0 (r m))
    (fun m => huP (r m)) (fun m => hEq (r m))
  choose F Q hQ hNorm hWeak using exists_weakCluster_realThirdDerivative hn (fun m => hu (r m))
    (fun m => hThird (t (r m)) (ht (r m)) (hu (r m)) (hu0 (r m)) (huP (r m)) (hEq (r m)))
  refine ⟨w, G, L, hD, hLip, hw0, ?_, F, ?_, ?_⟩
  · filter_upwards [hAe, hEqA] with x hx he
    change dirichletHessianMatrix (A x) = complexHessianOfRealBilinear (fderiv ℝ G x) at he
    rw [← he]
    exact hx.2
  · intro i j k η
    have hEqH := ae_realHessian_eq_of_uniform_gradient hn (fun m => hu (r m)) hGradient hLip
      (e[n] j) (e[n] k) (H j k) (fun m => R m j k) (hH j k) (fun m => hR m j k)
    rw [integral_test_weakThirdCluster_eq hn (fun m => hu (r m)) i j k (hQ i) (hNorm i)
      (hWeak i) (hH j k) (fun m => hR m j k) η]
    congr 1
    apply integral_congr_ae
    filter_upwards [hEqH] with x hx
    rw [hx]
  · intro i
    have hBound (m : ℕ) (x : E n) (hx : x ∈ unitBall n) : ‖complexHessian (u (r m)) x‖ ≤ D :=
      hDBound (t (r m)) (ht (r m)) (hu (r m)) (hu0 (r m)) (huP (r m)) (hEq (r m)) x hx
    have hBNorm : ∀ᵐ x ∂ν[n], ‖B x‖ ≤ D := by
      filter_upwards [hLim, ae_restrict_mem (μ := volume0 n)
        (show MeasurableSet (unitBall n) from measurableSet_ball)] with x hx hy
      exact le_of_tendsto' hx.norm (fun m => hBound m x hy)
    obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : Matrix (Fin n) (Fin n) ℂ) D).exists_bound_of_continuousOn
      continuous_dirichletCofactorCoordinates.continuousOn
    let T (x : E n) := inner ℝ (dirichletCofactorCoordinates (B x)) (F i x)
    have hTInt : Integrable T ν[n] := by
      apply (((Lp.memLp (F i)).integrable (by norm_num)).norm.const_mul M).mono'
        ((continuous_dirichletCofactorCoordinates.comp_aestronglyMeasurable hB).inner
          (Lp.aestronglyMeasurable (F i)))
      filter_upwards [hBNorm] with x hx
      exact (norm_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_right (hM (B x) (mem_closedBall_zero_iff.mpr hx)) (norm_nonneg _))
    have hRInt : Integrable (fun x => fderiv ℝ (fun y => Real.exp (t₀ * g y)) x (e[n] i)) ν[n] := by
      obtain ⟨U, hU, hSub, hgU⟩ := hg
      have hExp : ContDiffOn ℝ ∞ (fun y => Real.exp (t₀ * g y)) U := (contDiffOn_const.mul hgU).exp
      exact (memLp_continuousOn_dirichletBall hn
        (((hExp.fderiv_of_isOpen hU (m := ∞) (by simp)).clm_apply
          (contDiffOn_const (c := e[n] i))).continuousOn.mono hSub)).integrable (by norm_num)
    refine EventuallyEq.trans ?_ (ae_eq_on_unitBall_of_tests
      (hTInt.locallyIntegrable.locallyIntegrableOn _) (hRInt.locallyIntegrable.locallyIntegrableOn _) ?_)
    · filter_upwards [hEqA] with x hx
      change B x = complexHessianOfRealBilinear (fderiv ℝ G x) at hx
      dsimp only [T]
      rw [hx]
    intro η
    exact integral_test_cofactor_eq_of_weakThirdCluster hn (fun m => hu (r m))
      (fun m => hEq (r m)) hB hBound hLim i (hQ i) (hNorm i) (hWeak i) η
      (integral_test_fderiv_logDensityPath_tendsto hn hg (fun m => ht (r m))
        (hT.comp hr.tendsto_atTop) η (e[n] i))

end KEBall
