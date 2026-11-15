import KEBall.DirichletWeakDeterminantLimit
import KEBall.DirichletClassicalEquation

/-! Weak divergence equations for the first derivatives of a Dirichlet path limit. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8

open Filter InnerProductSpace MeasureTheory Metric Set
open scoped ComplexOrder ContDiff Distributions Gradient Matrix.Norms.Elementwise NNReal Topology

namespace KEBall

local notation "ν[" n "]" => Measure.restrict (volume0 n) (unitBall n)
local notation "e[" n "]" => EuclideanSpace.basisFun (Fin (2 * n)) ℝ
local notation "𝓓B[" n "]" => 𝓓(dirichletBallOpens n, ℝ)

/-- The real coefficient operator associated with a complex Hessian matrix. -/
noncomputable def dirichletCofactorOfMatrix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    E n →L[ℝ] E n :=
  (8 : ℝ)⁻¹ •
    ((InnerProductSpace.toDual ℝ (E n)).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
      (hermitianRealification A.adjugate))

theorem dirichletCofactorOfMatrix_complexHessian {n : ℕ} (u : E n → ℝ) (x : E n) :
    dirichletCofactorOfMatrix (complexHessian u x) = dirichletCofactorOperator u x := rfl

theorem continuous_dirichletCofactorOfMatrix {n : ℕ} :
    Continuous (@dirichletCofactorOfMatrix n) := by
  let R := (InnerProductSpace.toDual ℝ (E n)).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hC : Continuous (fun B : E n →L[ℝ] E n →L[ℝ] ℝ => R.comp B) :=
    (ContinuousLinearMap.compL ℝ (E n) (E n →L[ℝ] ℝ) (E n) R).continuous
  have hH : Continuous (@hermitianRealification n) := by
    unfold hermitianRealification
    apply Continuous.const_smul _ (2 : ℝ)
    apply continuous_finsetSum
    intro i _
    apply continuous_finsetSum
    intro j _
    have hij := (continuous_id : Continuous (id : Matrix (Fin n) (Fin n) ℂ → _)).matrix_elem i j
    exact ((Complex.continuous_re.comp hij).smul continuous_const).add
      ((Complex.continuous_im.comp hij).smul continuous_const)
  exact ((hC.comp (hH.comp continuous_id.matrix_adjugate)).const_smul (8 : ℝ)⁻¹)

private theorem cofactorContraction_directionalDerivative {n : ℕ}
    {u f : E n → ℝ} (hu : SmoothNear (closedUnitBall n) u)
    (hEq : ∀ y ∈ unitBall n, (complexHessian u y).det.re = f y)
    {x : E n} (hx : x ∈ unitBall n) (v : E n) :
    MoserTrudinger.cofactorContraction u (fun y => fderiv ℝ u y v) x = fderiv ℝ f x v := by
  rw [← cofactorTrace_realThirdDerivative_eq_fderiv hu hEq hx v]
  unfold MoserTrudinger.cofactorContraction Matrix.trace
  simp only [Matrix.diag_apply, Matrix.mul_apply]
  rw [Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  obtain ⟨U, hU, hSub, huU⟩ := hu
  have hxU := hSub (ball_subset_closedBall hx)
  rw [complexHessian_directionalDerivative hU huU hxU, fderiv_complexHessian_entry hU huU hxU]
  rfl

/-- A directional derivative of a smooth solution solves the cofactor
equation in divergence form on compactly supported tests. -/
theorem integral_cofactor_directionalDerivative_eq_neg {n : ℕ} (hn : 0 < n)
    {u f : E n → ℝ} (hu : SmoothNear (closedUnitBall n) u)
    (huP : ∀ x ∈ unitBall n, (complexHessian u x).PosDef)
    (hEq : ∀ y ∈ unitBall n, (complexHessian u y).det.re = f y)
    (ψ : 𝓓B[n]) (v : E n) :
    (∫ x, inner ℝ (dirichletCofactorOperator u x (∇ (fun y => fderiv ℝ u y v) x))
      (∇ (ψ : E n → ℝ) x) ∂ν[n]) =
      -(∫ x, ψ x * fderiv ℝ f x v ∂ν[n]) := by
  obtain ⟨U, hU, hSub, huU⟩ := hu
  have hDir := contDiffOn_directionalDerivative hU huU v
  rw [integral_dirichletCofactorOperator_eq_neg_linearization hn hU hSub huU ψ.contDiff.contDiffOn hDir huP
    (fun x hx => image_eq_zero_of_notMem_tsupport fun h => (not_lt_of_ge (mem_sphere_zero_iff_norm.mp hx).ge)
      (mem_ball_zero_iff.mp (ψ.tsupport_subset h)))]
  congr 1
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (μ := volume0 n) (show MeasurableSet (unitBall n) from measurableSet_ball)]
    with x hx
  rw [cofactorContraction_directionalDerivative ⟨U, hU, hSub, huU⟩ hEq hx]

/-- The Riesz representative of a real Hessian evaluated in its second slot. -/
noncomputable def directionalHessianVector {n : ℕ}
    (D : E n →L[ℝ] E n →L[ℝ] ℝ) (v : E n) : E n :=
  (InnerProductSpace.toDual ℝ (E n)).symm (D.flip v)

/-- For a Lipschitz gradient, the Riesz representative is the classical
gradient of each directional derivative almost everywhere in the ball. -/
theorem ae_gradient_directionalDerivative_eq {n : ℕ}
    {G : E n → E n →L[ℝ] ℝ} {L : ℝ≥0} (hG : LipschitzOnWith L G (closedUnitBall n))
    (v : E n) :
    (fun x => ∇ (fun y => G y v) x) =ᵐ[ν[n]]
      fun x => directionalHessianVector (fderiv ℝ G x) v := by
  obtain ⟨W, hW, hEq⟩ := hG.extend_finite_dimension
  have : (volume0 n).IsAddHaarMeasure := by
    unfold volume0
    exact Measure.IsAddHaarMeasure.smul _ (by positivity) ENNReal.ofReal_ne_top
  have hDiff := ae_restrict_of_ae (s := unitBall n) (hW.ae_differentiableAt (μ := volume0 n))
  filter_upwards [hDiff, ae_restrict_mem (μ := volume0 n)
    (show MeasurableSet (unitBall n) from measurableSet_ball)] with x hx hxb
  have hN : ∀ᶠ y in 𝓝 x, y ∈ unitBall n := isOpen_ball.mem_nhds hxb
  have hNear : G =ᶠ[𝓝 x] W := hN.mono fun y hy => hEq (ball_subset_closedBall hy)
  have hDG : DifferentiableAt ℝ G x := hx.congr_of_eventuallyEq hNear
  have h := (ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt.comp x hDG.hasFDerivAt
  unfold gradient directionalHessianVector
  congr 1
  ext a
  exact congrArg (fun P : E n →L[ℝ] ℝ => P a) h.fderiv

private theorem directionalHessianVector_eq_sum {n : ℕ}
    (D : E n →L[ℝ] E n →L[ℝ] ℝ) (v : E n) :
    directionalHessianVector D v = ∑ j, D (e[n] j) v • e[n] j := by
  let w := directionalHessianVector D v
  have h (j : Fin (2 * n)) : inner ℝ (e[n] j) w = D (e[n] j) v := by
    rw [real_inner_comm]
    exact congrArg (fun q : E n →L[ℝ] ℝ => q (e[n] j))
      ((InnerProductSpace.toDual ℝ (E n)).apply_symm_apply (D.flip v))
  simpa only [h] using ((e[n]).sum_repr' w).symm

private theorem gradient_directionalDerivative {n : ℕ} {u : E n → ℝ} {x : E n}
    (hu : ContDiffAt ℝ ∞ u x) (v : E n) :
    ∇ (fun y => fderiv ℝ u y v) x = directionalHessianVector (realHessian u x) v := by
  unfold gradient directionalHessianVector
  congr 1
  ext a
  exact fderiv_firstDerivative_apply hu a v

/-- The real Hessian converges in L² when evaluated on a fixed basis
vector and identified with the Riesz representative. -/
private theorem exists_tendsto_directionalHessianVector {n : ℕ}
    {u : ℕ → E n → ℝ} {G : E n → E n →L[ℝ] ℝ}
    (h : ∀ j k : Fin (2 * n), ∃ (H : DirichletBallL2 n ℝ) (R : ℕ → DirichletBallL2 n ℝ),
      Tendsto R atTop (𝓝 H) ∧
      (∀ m, R m =ᵐ[ν[n]] fun x => realHessian (u m) x (e[n] j) (e[n] k)) ∧
      H =ᵐ[ν[n]] fun x => fderiv ℝ G x (e[n] j) (e[n] k))
    (i : Fin (2 * n)) :
    ∃ (H : DirichletBallL2 n (E n)) (R : ℕ → DirichletBallL2 n (E n)),
      Tendsto R atTop (𝓝 H) ∧
      (∀ m, R m =ᵐ[ν[n]] fun x => directionalHessianVector (realHessian (u m) x) (e[n] i)) ∧
      H =ᵐ[ν[n]] fun x => directionalHessianVector (fderiv ℝ G x) (e[n] i) := by
  choose H R hT hR hH using fun j => h j i
  let C (j : Fin (2 * n)) := ContinuousLinearMap.toSpanSingleton ℝ (e[n] j)
  let B (j : Fin (2 * n)) : DirichletBallL2 n ℝ →L[ℝ] DirichletBallL2 n (E n) :=
    (C j).compLpL 2 ν[n]
  let X (m : ℕ) := ∑ j, B j (R j m)
  let Y := ∑ j, B j (H j)
  have hRep {W : Fin (2 * n) → DirichletBallL2 n ℝ}
      {D : E n → E n →L[ℝ] E n →L[ℝ] ℝ}
      (hW : ∀ j, W j =ᵐ[ν[n]] fun x => D x (e[n] j) (e[n] i)) :
      (⇑(∑ j, B j (W j)) : E n → E n) =ᵐ[ν[n]]
        fun x => directionalHessianVector (D x) (e[n] i) := by
    have hB (j : Fin (2 * n)) : B j (W j) =ᵐ[ν[n]] fun x => C j (W j x) :=
      (C j).coeFn_compLp' (W j)
    filter_upwards [Lp.coeFn_finsetSum (s := Finset.univ) (fun j => B j (W j)),
      ae_all_iff.mpr hB, ae_all_iff.mpr hW] with x hx hy hz
    rw [directionalHessianVector_eq_sum]
    change _ = ∑ j, D x (e[n] j) (e[n] i) • e[n] j
    simp only [hx, Finset.sum_apply, hy, hz, C, ContinuousLinearMap.toSpanSingleton_apply]
  refine ⟨Y, X, ?_, fun m => hRep (fun j => hR j m), hRep hH⟩
  exact tendsto_finsetSum _ (fun j _ => (B j).continuous.continuousAt.tendsto.comp (hT j))

private theorem exists_tendsto_cofactor_adjoint_test {n : ℕ} (hn : 0 < n)
    {A : ℕ → E n → Matrix (Fin n) (Fin n) ℂ} {B : E n → Matrix (Fin n) (Fin n) ℂ}
    (hA : ∀ m, AEStronglyMeasurable (A m) ν[n]) (hB : AEStronglyMeasurable B ν[n])
    {D : ℝ} (hBound : ∀ m, ∀ᵐ x ∂ν[n], ‖A m x‖ ≤ D)
    (hLim : ∀ᵐ x ∂ν[n], Tendsto (fun m => A m x) atTop (𝓝 (B x))) (ψ : 𝓓B[n]) :
    ∃ (P : ℕ → DirichletBallL2 n (E n)) (p : DirichletBallL2 n (E n)),
      Tendsto P atTop (𝓝 p) ∧
      (∀ m, P m =ᵐ[ν[n]] fun x => (dirichletCofactorOfMatrix (A m x)).adjoint (∇ (ψ : E n → ℝ) x)) ∧
      p =ᵐ[ν[n]] fun x => (dirichletCofactorOfMatrix (B x)).adjoint (∇ (ψ : E n → ℝ) x) := by
  have : NeZero n := ⟨hn.ne'⟩
  let W (p : E n × Matrix (Fin n) (Fin n) ℂ) :=
    (dirichletCofactorOfMatrix p.2).adjoint (∇ (ψ : E n → ℝ) p.1)
  have hGrad : Continuous (∇ (ψ : E n → ℝ)) :=
    (InnerProductSpace.toDual ℝ (E n)).symm.continuous.comp
      (ψ.contDiff.fderiv_right (m := ∞) (by simp)).continuous
  have hW : Continuous W :=
    (ContinuousLinearMap.adjoint.continuous.comp (continuous_dirichletCofactorOfMatrix.comp continuous_snd)).clm_apply
      (hGrad.comp continuous_fst)
  obtain ⟨C, hC⟩ := ((isCompact_closedBall (0 : E n) 1).prod
    (isCompact_closedBall (0 : Matrix (Fin n) (Fin n) ℂ) D)).exists_bound_of_continuousOn hW.continuousOn
  have hBall := ae_restrict_mem (μ := volume0 n) (show MeasurableSet (unitBall n) from measurableSet_ball)
  have hB' : ∀ᵐ x ∂ν[n], ‖B x‖ ≤ D := by
    filter_upwards [ae_all_iff.mpr hBound, hLim] with x hx hL
    exact le_of_tendsto' hL.norm hx
  have hPoint {M : E n → Matrix (Fin n) (Fin n) ℂ} (hM : ∀ᵐ x ∂ν[n], ‖M x‖ ≤ D) :
      ∀ᵐ x ∂ν[n], ‖W (x, M x)‖ ≤ C := by
    filter_upwards [hBall, hM] with x hx hy
    exact hC (x, M x) ⟨ball_subset_closedBall hx, mem_closedBall_zero_iff.mpr hy⟩
  have hMeas {M : E n → Matrix (Fin n) (Fin n) ℂ} (hM : AEStronglyMeasurable M ν[n]) :
      AEStronglyMeasurable (fun x => W (x, M x)) ν[n] :=
    hW.comp_aestronglyMeasurable (continuous_id.aestronglyMeasurable.prodMk hM)
  let P (m : ℕ) := (MemLp.of_bound (p := 2) (hMeas (hA m)) C (hPoint (hBound m))).toLp (fun x => W (x, A m x))
  let p := (MemLp.of_bound (p := 2) (hMeas hB) C (hPoint hB')).toLp (fun x => W (x, B x))
  have hRep (m : ℕ) : P m =ᵐ[ν[n]] fun x => W (x, A m x) := MemLp.coeFn_toLp _
  have hp : p =ᵐ[ν[n]] fun x => W (x, B x) := MemLp.coeFn_toLp _
  have hLeft : Tendsto P atTop (𝓝 p) := by
    apply tendsto_dirichletBallL2_of_ae_tendsto_of_bound hn (C := C)
    · intro m
      filter_upwards [hRep m, hPoint (hBound m)] with x hx hy
      rw [hx]
      exact hy
    · filter_upwards [ae_all_iff.mpr hRep, hp, hLim] with x hx hy hL
      rw [hy]
      exact ((hW.tendsto (x, B x)).comp (tendsto_const_nhds.prodMk_nhds hL)).congr
        (fun m => (hx m).symm)
  exact ⟨P, p, hLeft, hRep, hp⟩

private theorem inner_cofactor_adjoint_test {n : ℕ} {M : E n → Matrix (Fin n) (Fin n) ℂ}
    {V : DirichletBallL2 n (E n)} (ψ : 𝓓B[n])
    (hV : V =ᵐ[ν[n]] fun x => (dirichletCofactorOfMatrix (M x)).adjoint (∇ (ψ : E n → ℝ) x))
    (U : DirichletBallL2 n (E n)) :
    inner ℝ V U = ∫ x, inner ℝ (dirichletCofactorOfMatrix (M x) (U x))
      (∇ (ψ : E n → ℝ) x) ∂ν[n] := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hV] with x hx
  rw [hx, real_inner_comm]
  exact ContinuousLinearMap.adjoint_inner_right _ _ _

private theorem tendsto_integral_cofactor_pairing {n : ℕ} (hn : 0 < n)
    {A : ℕ → E n → Matrix (Fin n) (Fin n) ℂ} {B : E n → Matrix (Fin n) (Fin n) ℂ}
    (hA : ∀ m, AEStronglyMeasurable (A m) ν[n]) (hB : AEStronglyMeasurable B ν[n])
    {D : ℝ} (hBound : ∀ m, ∀ᵐ x ∂ν[n], ‖A m x‖ ≤ D)
    (hLim : ∀ᵐ x ∂ν[n], Tendsto (fun m => A m x) atTop (𝓝 (B x)))
    {R : ℕ → DirichletBallL2 n (E n)} {H : DirichletBallL2 n (E n)}
    (hR : Tendsto R atTop (𝓝 H)) (ψ : 𝓓B[n]) :
    Tendsto (fun m => ∫ x, inner ℝ (dirichletCofactorOfMatrix (A m x) (R m x))
      (∇ (ψ : E n → ℝ) x) ∂ν[n]) atTop
      (𝓝 (∫ x, inner ℝ (dirichletCofactorOfMatrix (B x) (H x))
        (∇ (ψ : E n → ℝ) x) ∂ν[n])) := by
  obtain ⟨P, p, hLeft, hRep, hp⟩ := exists_tendsto_cofactor_adjoint_test hn hA hB hBound hLim ψ
  rw [← inner_cofactor_adjoint_test ψ hp H]
  exact (hLeft.inner hR).congr (fun m => inner_cofactor_adjoint_test ψ (hRep m) (R m))

/-- A real continuous linear functional has zero complex Hessian. -/
theorem complexHessian_continuousLinearMap {n : ℕ}
    (l : E n →L[ℝ] ℝ) (x : E n) : complexHessian l x = 0 := by
  have hD : fderiv ℝ (l : E n → ℝ) = fun _ => l :=
    funext fun y => l.hasFDerivAt.fderiv
  rw [← complexHessianOfRealBilinear_eq l.contDiff.contDiffAt]
  simp only [realHessian, hD, fderiv_const]
  ext i j
  simp [complexHessianOfRealBilinear]

/-- Each constant column of the smooth real cofactor field is divergence
free. The normalization is the existing `dirichletCofactorOperator`, including
its factor `1 / 8`; no Euclidean/complex convention is changed here. -/
theorem integral_dirichletCofactorOperator_const_eq_zero {n : ℕ} (hn : 0 < n)
    {u : E n → ℝ} (hu : SmoothNear (closedUnitBall n) u)
    (huP : ∀ x ∈ unitBall n, (complexHessian u x).PosDef)
    (v : E n) (ψ : 𝓓B[n]) :
    (∫ x, inner ℝ (dirichletCofactorOperator u x v)
      (∇ (ψ : E n → ℝ) x) ∂ν[n]) = 0 := by
  obtain ⟨U, hU, hSub, huU⟩ := hu
  let l : E n →L[ℝ] ℝ := innerSL ℝ v
  have hGrad (x : E n) : ∇ (l : E n → ℝ) x = v := by
    apply ext_inner_right ℝ
    intro e
    rw [inner_gradient_left, l.hasFDerivAt.fderiv]
    rfl
  have hCof (x : E n) : MoserTrudinger.cofactorContraction u l x = 0 := by
    simp [MoserTrudinger.cofactorContraction, complexHessian_continuousLinearMap]
  have h := integral_dirichletCofactorOperator_eq_neg_linearization hn hU hSub
    huU ψ.contDiff.contDiffOn l.contDiff.contDiffOn huP
    (fun x hx => image_eq_zero_of_notMem_tsupport fun hs =>
      (not_lt_of_ge (mem_sphere_zero_iff_norm.mp hx).ge)
        (mem_ball_zero_iff.mp (ψ.tsupport_subset hs)))
  simpa only [hGrad, hCof, mul_zero, integral_zero, neg_zero] using h

/-- Distributional column divergence is preserved under bounded almost
everywhere convergence of the complex Hessians. This passage only uses the
already established cofactor pairing limit, with a constant L² vector. -/
theorem integral_dirichletCofactorOfMatrix_const_eq_zero_of_limit {n : ℕ}
    (hn : 0 < n) {u : ℕ → E n → ℝ}
    (hu : ∀ m, SmoothNear (closedUnitBall n) (u m))
    (huP : ∀ m x, x ∈ unitBall n → (complexHessian (u m) x).PosDef)
    {B : E n → Matrix (Fin n) (Fin n) ℂ}
    (hA : ∀ m, AEStronglyMeasurable (complexHessian (u m)) ν[n])
    (hB : AEStronglyMeasurable B ν[n]) {D : ℝ}
    (hBound : ∀ m, ∀ᵐ x ∂ν[n], ‖complexHessian (u m) x‖ ≤ D)
    (hLim : ∀ᵐ x ∂ν[n], Tendsto (fun m => complexHessian (u m) x)
      atTop (𝓝 (B x))) (v : E n) (ψ : 𝓓B[n]) :
    (∫ x, inner ℝ (dirichletCofactorOfMatrix (B x) v)
      (∇ (ψ : E n → ℝ) x) ∂ν[n]) = 0 := by
  have : NeZero n := ⟨hn.ne'⟩
  have : IsProbabilityMeasure ν[n] := volume0_restrict_isProbability n
  have hLp : MemLp (fun _ : E n => v) 2 ν[n] := memLp_const v
  let V : DirichletBallL2 n (E n) := hLp.toLp (fun _ => v)
  have hV : V =ᵐ[ν[n]] fun _ => v := MemLp.coeFn_toLp hLp
  have hT := tendsto_integral_cofactor_pairing hn hA hB hBound hLim
    (R := fun _ => V) (H := V) tendsto_const_nhds ψ
  have hZero (m : ℕ) :
      (∫ x, inner ℝ (dirichletCofactorOfMatrix (complexHessian (u m) x) (V x))
        (∇ (ψ : E n → ℝ) x) ∂ν[n]) = 0 := by
    calc
      _ = ∫ x, inner ℝ (dirichletCofactorOperator (u m) x v)
          (∇ (ψ : E n → ℝ) x) ∂ν[n] := by
            apply integral_congr_ae
            filter_upwards [hV] with x hx
            rw [hx, dirichletCofactorOfMatrix_complexHessian]
      _ = 0 := integral_dirichletCofactorOperator_const_eq_zero hn (hu m) (huP m) v ψ
  have hZ : Tendsto (fun m => ∫ x,
      inner ℝ (dirichletCofactorOfMatrix (complexHessian (u m) x) (V x))
        (∇ (ψ : E n → ℝ) x) ∂ν[n]) atTop (𝓝 (0 : ℝ)) := by
    simpa only [hZero] using (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  calc
    _ = ∫ x, inner ℝ (dirichletCofactorOfMatrix (B x) (V x))
        (∇ (ψ : E n → ℝ) x) ∂ν[n] := by
          apply integral_congr_ae
          filter_upwards [hV] with x hx
          rw [hx]
    _ = 0 := tendsto_nhds_unique hT hZ

private theorem exists_uniform_cofactor_ellipticity_of_logDensityPath {n : ℕ} (hn : 0 < n)
    {g : E n → ℝ} (hg : SmoothNear (closedUnitBall n) g) :
    ∃ l L : ℝ, 0 < l ∧ 0 < L ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ {u : E n → ℝ},
        SmoothNear (closedUnitBall n) u → (∀ x ∈ unitSphere n, u x = 0) →
        (∀ x ∈ unitBall n, (complexHessian u x).PosDef) →
        (∀ x ∈ unitBall n, (complexHessian u x).det.re = Real.exp (t * g x)) →
        ∀ x ∈ unitBall n, ∀ v : E n,
          l * ‖v‖ ^ 2 ≤ inner ℝ (dirichletCofactorOfMatrix (complexHessian u x) v) v ∧
          inner ℝ (dirichletCofactorOfMatrix (complexHessian u x) v) v ≤ L * ‖v‖ ^ 2 := by
  obtain ⟨a, b, K, M, ha, hb, hK, hM, hData⟩ := exists_logDensityPath_bounds hn hg
  obtain ⟨l, L, hl, hL, hEll⟩ := exists_uniform_ellipticity_of_dirichlet_density_bounds hn ha hb hK hM
  refine ⟨a ^ n * l, b ^ n * L, mul_pos (pow_pos ha _) hl, mul_pos (pow_pos hb _) hL, ?_⟩
  intro t ht u hu hu0 huP hEq x hx v
  let f (x : E n) := Real.exp (t * g x)
  have hf : SmoothNear (closedUnitBall n) f := by
    obtain ⟨U, hU, hSub, hgU⟩ := hg
    exact ⟨U, hU, hSub, (contDiffOn_const.mul hgU).exp⟩
  have hd (y : E n) (hy : y ∈ unitBall n) : a ^ n ≤ f y ∧ f y ≤ b ^ n :=
    (hData t ht).1 y (ball_subset_closedBall hy)
  have hE := hEll hu hf hu0 huP hEq hd
    (fun y hy => (hData t ht).2.1 y (ball_subset_closedBall hy))
    (fun y hy => (hData t ht).2.2 y (ball_subset_closedBall hy)) x (ball_subset_closedBall hx) v
  rw [dirichletCofactorOfMatrix_complexHessian, dirichletCofactorOperator_inner_self (huP x hx), hEq x hx]
  change _ ≤ f x * _ ∧ f x * _ ≤ _
  constructor
  · rw [mul_assoc]
    exact (mul_le_mul_of_nonneg_right (hd x hx).1 (by positivity)).trans
      (mul_le_mul_of_nonneg_left hE.1 (Real.exp_pos _).le)
  · rw [mul_assoc]
    exact (mul_le_mul_of_nonneg_left hE.2 (Real.exp_pos _).le).trans
      (mul_le_mul_of_nonneg_right (hd x hx).2 (by positivity))

/-- Twice differentiating the log-determinant gives a divergence-form
subsolution inequality for each second directional derivative. -/
theorem integral_cofactor_realHessian_self_le {n : ℕ} (hn : 0 < n)
    {u f : E n → ℝ} (hu : SmoothNear (closedUnitBall n) u) (hf : SmoothNear (closedUnitBall n) f)
    (huP : ∀ x ∈ unitBall n, (complexHessian u x).PosDef)
    (hEq : ∀ y ∈ unitBall n, (complexHessian u y).det.re = f y)
    (ψ : 𝓓B[n]) (hψ : ∀ x ∈ unitBall n, 0 ≤ ψ x) (v : E n) :
    (∫ x, inner ℝ (dirichletCofactorOperator u x (∇ (fun y => realHessian u y v v) x))
      (∇ (ψ : E n → ℝ) x) ∂ν[n]) ≤
      -(∫ x, ψ x * (f x * realHessian (fun y => Real.log (f y)) x v v) ∂ν[n]) := by
  have : NeZero n := ⟨hn.ne'⟩
  obtain ⟨U, hU, hSub, huU⟩ := hu
  let w (y : E n) := realHessian u y v v
  have hw : ContDiffOn ℝ ∞ w U :=
    (((huU.fderiv_of_isOpen hU (m := ∞) (by simp)).fderiv_of_isOpen hU (m := ∞) (by simp)).clm_apply
      contDiffOn_const).clm_apply contDiffOn_const
  rw [integral_dirichletCofactorOperator_eq_neg_linearization hn hU hSub huU ψ.contDiff.contDiffOn hw huP
    (fun x hx => image_eq_zero_of_notMem_tsupport fun h => (not_lt_of_ge (mem_sphere_zero_iff_norm.mp hx).ge)
      (mem_ball_zero_iff.mp (ψ.tsupport_subset h)))]
  apply neg_le_neg
  have hLog : ContDiffOn ℝ ∞ (fun x => Real.log (f x)) (unitBall n) := by
    obtain ⟨V, hV, hSubV, hfV⟩ := hf
    apply (hfV.mono (ball_subset_closedBall.trans hSubV)).log
    intro x hx
    rw [← hEq x hx]
    exact (posDef_det_re_pos (huP x hx)).ne'
  have hLC : ContinuousOn (fun x => realHessian (fun y => Real.log (f y)) x v v) (unitBall n) :=
    (((hLog.fderiv_of_isOpen isOpen_ball (m := ∞) (by simp)).fderiv_of_isOpen isOpen_ball
      (m := ∞) (by simp)).clm_apply contDiffOn_const |>.clm_apply contDiffOn_const).continuousOn
  have hA : Integrable (fun x => ψ x * (f x * realHessian (fun y => Real.log (f y)) x v v)) ν[n] := by
    have hFC : ContinuousOn f (unitBall n) :=
      fun x hx => (hf.contDiffAt (ball_subset_closedBall hx)).continuousAt.continuousWithinAt
    have hI := (hFC.mul hLC).locallyIntegrableOn measurableSet_ball (μ := ν[n])
    exact ψ.integrable_bilin (ContinuousLinearMap.lsmul ℝ ℝ) hI
  apply integral_mono_ae hA (MoserTrudinger.integrable_mul_contraction hn hU hSub huU ψ.contDiff.contDiffOn hw)
  filter_upwards [ae_restrict_mem (μ := volume0 n) (show MeasurableSet (unitBall n) from measurableSet_ball)]
    with x hx
  have hf' := (hEq x hx) ▸ posDef_det_re_pos (huP x hx)
  have hL := complexLaplacian_realHessian_self_ge_logDensity
    (⟨U, hU, hSub, huU⟩ : SmoothNear (closedUnitBall n) u) hf huP hEq hx v
  change ψ x * (f x * realHessian (fun y => Real.log (f y)) x v v) ≤ ψ x * MoserTrudinger.cofactorContraction u w x
  rw [cofactorContraction_eq_det_mul_complexLaplacian (huP x hx), hEq x hx]
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hL hf'.le) (hψ x hx)

private noncomputable def bilinearCoordinateDirection {n : ℕ} (v : E n) :
    DirichletBilinearCoordinates n →L[ℝ] E n :=
  ∑ j, ∑ k, (inner ℝ (e[n] k) v) •
    (ContinuousLinearMap.toSpanSingleton ℝ (e[n] j)).comp (EuclideanSpace.proj (j, k))

private theorem bilinearCoordinateDirection_apply {n : ℕ} (v : E n)
    (B : E n →L[ℝ] E n →L[ℝ] ℝ) :
    bilinearCoordinateDirection v (dirichletBilinearCoordinates B) = directionalHessianVector B v := by
  rw [directionalHessianVector_eq_sum]
  have h (j : Fin (2 * n)) : B (e[n] j) v = ∑ k, inner ℝ (e[n] k) v * B (e[n] j) (e[n] k) := by
    conv_lhs => rw [← (e[n]).sum_repr' v]
    simp only [map_sum, map_smul, smul_eq_mul]
  simp only [bilinearCoordinateDirection, _root_.sum_apply, _root_.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply, dirichletBilinearCoordinates, smul_smul, h, Finset.sum_smul]
  rfl

private theorem inner_bilinearCoordinateDirection_compLp {n : ℕ} (v : E n)
    (P : DirichletBallL2 n (E n)) (Q : DirichletBallL2 n (DirichletBilinearCoordinates n)) :
    inner ℝ ((bilinearCoordinateDirection v).adjoint.compLp P) Q =
      inner ℝ P ((bilinearCoordinateDirection v).compLp Q) := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(bilinearCoordinateDirection v).adjoint.coeFn_compLp P,
    (bilinearCoordinateDirection v).coeFn_compLp Q] with x hx hy
  rw [hx, hy, real_inner_comm, ContinuousLinearMap.adjoint_inner_right, real_inner_comm]

private theorem mapClusterPt_inner_cofactor_pairing {n : ℕ} (hn : 0 < n)
    {A : ℕ → E n → Matrix (Fin n) (Fin n) ℂ} {B : E n → Matrix (Fin n) (Fin n) ℂ}
    (hA : ∀ m, AEStronglyMeasurable (A m) ν[n]) (hB : AEStronglyMeasurable B ν[n])
    {D : ℝ} (hBound : ∀ m, ∀ᵐ x ∂ν[n], ‖A m x‖ ≤ D)
    (hLim : ∀ᵐ x ∂ν[n], Tendsto (fun m => A m x) atTop (𝓝 (B x)))
    {Q : ℕ → DirichletBallL2 n (DirichletBilinearCoordinates n)}
    {F : DirichletBallL2 n (DirichletBilinearCoordinates n)} {C : ℝ}
    (hNorm : ∀ m, ‖Q m‖ ≤ C)
    (hWeak : MapClusterPt (toWeakSpace ℝ _ F) atTop (fun m => toWeakSpace ℝ _ (Q m)))
    (v : E n) (ψ : 𝓓B[n]) :
    MapClusterPt (∫ x, inner ℝ (dirichletCofactorOfMatrix (B x)
        (((bilinearCoordinateDirection v).compLp F : DirichletBallL2 n (E n)) x)) (∇ (ψ : E n → ℝ) x) ∂ν[n])
      atTop (fun m => ∫ x, inner ℝ (dirichletCofactorOfMatrix (A m x)
        (((bilinearCoordinateDirection v).compLp (Q m) : DirichletBallL2 n (E n)) x))
        (∇ (ψ : E n → ℝ) x) ∂ν[n]) := by
  obtain ⟨P, p, hT, hP, hp⟩ := exists_tendsto_cofactor_adjoint_test hn hA hB hBound hLim ψ
  let J : DirichletBallL2 n (E n) →L[ℝ] DirichletBallL2 n (DirichletBilinearCoordinates n) :=
    (bilinearCoordinateDirection v).adjoint.compLpL 2 ν[n]
  have h := MapClusterPt.inner_of_tendsto_weak hNorm hWeak
    (J.continuous.continuousAt.tendsto.comp hT)
  change MapClusterPt (inner ℝ ((bilinearCoordinateDirection v).adjoint.compLp p) F) atTop
    (fun m => inner ℝ ((bilinearCoordinateDirection v).adjoint.compLp (P m)) (Q m)) at h
  simpa only [inner_bilinearCoordinateDirection_compLp, inner_cofactor_adjoint_test ψ hp,
    fun m => inner_cofactor_adjoint_test ψ (hP m)] using h

private theorem gradient_realHessian_self {n : ℕ} {u : E n → ℝ} {x : E n}
    (hu : ContDiffAt ℝ ∞ u x) (v : E n) :
    ∇ (fun y => realHessian u y v v) x =
      bilinearCoordinateDirection v (dirichletBilinearCoordinates (realThirdDerivative u x v)) := by
  rw [bilinearCoordinateDirection_apply]
  unfold gradient directionalHessianVector
  congr 1
  ext a
  exact (fderiv_realHessian_apply hu a v v).trans (realThirdDerivative_symm12 hu a v v)

private theorem integral_test_hessianSource_logDensityPath_tendsto {n : ℕ} (hn : 0 < n)
    {g : E n → ℝ} (hg : SmoothNear (closedUnitBall n) g)
    {t : ℕ → ℝ} {t₀ : ℝ} (ht : ∀ m, t m ∈ Icc (0 : ℝ) 1) (hT : Tendsto t atTop (𝓝 t₀))
    (ψ : 𝓓B[n]) (v : E n) :
    Tendsto (fun m => ∫ x, ψ x * (Real.exp (t m * g x) * (t m * realHessian g x v v)) ∂ν[n])
      atTop (𝓝 (∫ x, ψ x * (Real.exp (t₀ * g x) * (t₀ * realHessian g x v v)) ∂ν[n])) := by
  have : NeZero n := ⟨hn.ne'⟩
  obtain ⟨U, hU, hSub, hgU⟩ := hg
  let J (p : ℝ × E n) := ψ p.2 * (Real.exp (p.1 * g p.2) * (p.1 * realHessian g p.2 v v))
  have hJ : ContinuousOn J ((univ : Set ℝ) ×ˢ U) := by
    have hS : MapsTo Prod.snd ((univ : Set ℝ) ×ˢ U) U := fun _ hx => hx.2
    have hG := hgU.continuousOn.comp continuousOn_snd hS
    have hD : ContinuousOn (fun x => realHessian g x v v) U :=
      (((hgU.fderiv_of_isOpen hU (m := ∞) (by simp)).fderiv_of_isOpen hU (m := ∞) (by simp)).clm_apply
        (contDiffOn_const (c := v)) |>.clm_apply (contDiffOn_const (c := v))).continuousOn
    exact (ψ.continuous.comp continuous_snd).continuousOn.mul
      ((Real.continuous_exp.comp_continuousOn (continuousOn_fst.mul hG)).mul
        (continuousOn_fst.mul (hD.comp continuousOn_snd hS)))
  have hJ' (r : ℝ) : ContinuousOn (fun x => J (r, x)) (closedUnitBall n) :=
    hJ.comp (continuousOn_const.prodMk continuousOn_id) fun x hx => ⟨mem_univ _, hSub hx⟩
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod (isCompact_closedBall (0 : E n) 1)).exists_bound_of_continuousOn
    (hJ.mono (show Icc (0 : ℝ) 1 ×ˢ closedUnitBall n ⊆ (univ : Set ℝ) ×ˢ U from prod_mono (subset_univ _) hSub))
  change Tendsto (fun m => ∫ x, J (t m, x) ∂ν[n]) atTop (𝓝 (∫ x, J (t₀, x) ∂ν[n]))
  apply tendsto_integral_filter_of_norm_le_const
  · exact Eventually.of_forall fun m => ((hJ' (t m)).mono ball_subset_closedBall).aestronglyMeasurable measurableSet_ball
  · refine ⟨C, Eventually.of_forall fun m => ?_⟩
    filter_upwards [ae_restrict_mem (μ := volume0 n) (show MeasurableSet (unitBall n) from measurableSet_ball)]
      with x hx
    exact hC (t m, x) ⟨ht m, ball_subset_closedBall hx⟩
  · exact Eventually.of_forall fun x => tendsto_const_nhds.mul
      (((Real.continuous_exp.tendsto _).comp (hT.mul_const (g x))).mul (hT.mul_const (realHessian g x v v)))

private theorem hessian_log_exp_mul {n : ℕ} {g : E n → ℝ} {x v : E n}
    (hg : ContDiffAt ℝ ∞ g x) (t : ℝ) :
    realHessian (fun y => Real.log (Real.exp (t * g y))) x v v =
      t * realHessian g x v v := by
  have he : (fun y => Real.log (Real.exp (t * g y))) = t • g := by
    funext y
    simp [Pi.smul_apply, smul_eq_mul]
  rw [he]
  have h := PshLines.realHessian_smul (hg.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2) :
    ContDiffAt ℝ 2 g x) t v v
  simp only [PshLines.realHessian_eq_fderiv] at h
  exact h

private theorem integral_test_hessianSelf_weakGradient {n : ℕ} (hn : 0 < n)
    {u : ℕ → E n → ℝ} (hu : ∀ m, SmoothNear (closedUnitBall n) (u m)) (v : E n)
    {Q : ℕ → DirichletBallL2 n (DirichletBilinearCoordinates n)}
    {F : DirichletBallL2 n (DirichletBilinearCoordinates n)} {C : ℝ}
    (hQ : ∀ m, Q m =ᵐ[ν[n]] fun x => dirichletBilinearCoordinates (realThirdDerivative (u m) x v))
    (hNorm : ∀ m, ‖Q m‖ ≤ C)
    (hWeak : MapClusterPt (toWeakSpace ℝ _ F) atTop (fun m => toWeakSpace ℝ _ (Q m)))
    {H : Fin (2 * n) → Fin (2 * n) → DirichletBallL2 n ℝ}
    {R : ℕ → Fin (2 * n) → Fin (2 * n) → DirichletBallL2 n ℝ}
    {G : E n → E n →L[ℝ] ℝ}
    (hH : ∀ j k, Tendsto (fun m => R m j k) atTop (𝓝 (H j k)))
    (hR : ∀ m j k, R m j k =ᵐ[ν[n]] fun x => realHessian (u m) x (e[n] j) (e[n] k))
    (hActual : ∀ j k, H j k =ᵐ[ν[n]] fun x => fderiv ℝ G x (e[n] j) (e[n] k))
    (j : Fin (2 * n)) (ψ : 𝓓B[n]) :
    (∫ x, ψ x * inner ℝ (e[n] j)
      (((bilinearCoordinateDirection v).compLp F : DirichletBallL2 n (E n)) x) ∂ν[n]) =
      -(∫ x, fderiv ℝ (ψ : E n → ℝ) x (e[n] j) * fderiv ℝ G x v v ∂ν[n]) := by
  let L := ContinuousLinearMap.toSpanSingleton ℝ (e[n] j)
  let X : DirichletBallL2 n (E n) := L.compLp (dirichletTestToL2 ψ)
  have hX : X =ᵐ[ν[n]] fun x => ψ x • e[n] j := by
    filter_upwards [L.coeFn_compLp (dirichletTestToL2 ψ), dirichletTestToL2_ae ψ] with x hx hy
    change X x = L ((dirichletTestToL2 ψ) x) at hx
    rw [hx, hy]
    rfl
  have hTest (U : DirichletBallL2 n (E n)) :
      inner ℝ X U = ∫ x, ψ x * inner ℝ (e[n] j) (U x) ∂ν[n] := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hX] with x hx
    rw [hx, real_inner_smul_left]
  let Y : DirichletBallL2 n (DirichletBilinearCoordinates n) := (bilinearCoordinateDirection v).adjoint.compLp X
  let V (m : ℕ) : DirichletBallL2 n (E n) := (bilinearCoordinateDirection v).compLp (Q m)
  have hWeakPair := MapClusterPt.inner_of_tendsto_weak hNorm hWeak
    (tendsto_const_nhds (x := Y) (f := (atTop : Filter ℕ)))
  obtain ⟨φ, hφ, hSub⟩ := hWeakPair.tendsto_subseq
  let K : DirichletBallL2 n ℝ →L[ℝ] ℝ := innerSL ℝ (dirichletTestToL2 (dirichletTestLineDerivative (e[n] j) ψ))
  have hK (W : DirichletBallL2 n ℝ) :
      K W = ∫ x, fderiv ℝ (ψ : E n → ℝ) x (e[n] j) * W x ∂ν[n] := by
    change inner ℝ (dirichletTestToL2 (dirichletTestLineDerivative (e[n] j) ψ)) W = _
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [dirichletTestToL2_ae (dirichletTestLineDerivative (e[n] j) ψ)] with x hx
    rw [hx, Real.inner_apply]
    rfl
  let c (a b : Fin (2 * n)) := inner ℝ (e[n] a) v * inner ℝ (e[n] b) v
  have hCoord (B : E n →L[ℝ] E n →L[ℝ] ℝ) : B v v = ∑ a, ∑ b, c a b * B (e[n] a) (e[n] b) := by
    conv_lhs => rw [← (e[n]).sum_repr' v]
    simp only [map_sum, map_smul, _root_.sum_apply, _root_.smul_apply, smul_eq_mul, Finset.mul_sum, c, mul_assoc]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  let S (m : ℕ) : DirichletBallL2 n ℝ := ∑ a, ∑ b, c a b • R m a b
  let J : DirichletBallL2 n ℝ := ∑ a, ∑ b, c a b • H a b
  have hRep {W : Fin (2 * n) → Fin (2 * n) → DirichletBallL2 n ℝ}
      {B : E n → E n →L[ℝ] E n →L[ℝ] ℝ}
      (hW : ∀ a b, W a b =ᵐ[ν[n]] fun x => B x (e[n] a) (e[n] b)) :
      (⇑(∑ a, ∑ b, c a b • W a b) : E n → ℝ) =ᵐ[ν[n]] fun x => B x v v := by
    have hA (a : Fin (2 * n)) : (⇑(∑ b, c a b • W a b) : E n → ℝ) =ᵐ[ν[n]]
        fun x => ∑ b, c a b * B x (e[n] a) (e[n] b) := by
      filter_upwards [Lp.coeFn_finsetSum (s := Finset.univ) (fun b => c a b • W a b),
        ae_all_iff.mpr (fun b => Lp.coeFn_smul (c a b) (W a b)), ae_all_iff.mpr (hW a)] with x hx hy hz
      simp only [hx, Finset.sum_apply, hy, hz, Pi.smul_apply, smul_eq_mul]
    filter_upwards [Lp.coeFn_finsetSum (s := Finset.univ) (fun a => ∑ b, c a b • W a b),
      ae_all_iff.mpr hA] with x hx hy
    rw [hCoord]
    simp only [hx, Finset.sum_apply, hy]
  have hS (m : ℕ) : S m =ᵐ[ν[n]] fun x => realHessian (u m) x v v := hRep (hR m)
  have hJ : J =ᵐ[ν[n]] fun x => fderiv ℝ G x v v := hRep hActual
  have hT : Tendsto S atTop (𝓝 J) := tendsto_finsetSum _ fun a _ =>
    tendsto_finsetSum _ fun b _ => (hH a b).const_smul _
  have hEq (m : ℕ) : -(K (S m)) = inner ℝ Y (Q m) := by
    rw [hK, inner_bilinearCoordinateDirection_compLp, hTest]
    calc
      _ = -(∫ x, fderiv ℝ (ψ : E n → ℝ) x (e[n] j) * realHessian (u m) x v v ∂ν[n]) := by
        congr 1
        apply integral_congr_ae
        filter_upwards [hS m] with x hx
        rw [hx]
      _ = ∫ x, ψ x * realThirdDerivative (u m) x (e[n] j) v v ∂ν[n] :=
        (smooth_integral_test_realThirdDerivative hn (hu m) ψ _ _ _).symm
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [(bilinearCoordinateDirection v).coeFn_compLp (Q m), hQ m,
          ae_restrict_mem (μ := volume0 n) (show MeasurableSet (unitBall n) from measurableSet_ball)] with x hx hy hz
        rw [hx, hy, ← gradient_realHessian_self ((hu m).contDiffAt (ball_subset_closedBall hz)),
          ← real_inner_comm (e[n] j), inner_gradient_left, fderiv_realHessian_apply ((hu m).contDiffAt (ball_subset_closedBall hz))]
  have hStrong := ((K.continuous.continuousAt.tendsto.comp (hT.comp hφ.tendsto_atTop)).neg).congr (fun m => hEq (φ m))
  have h := tendsto_nhds_unique hSub hStrong
  rw [inner_bilinearCoordinateDirection_compLp, hTest, hK] at h
  rw [h]
  congr 1
  apply integral_congr_ae
  filter_upwards [hJ] with x hx
  rw [hx]

/-- For a Hermitian Hessian, the real cofactor coefficient is symmetric. -/
theorem dirichletCofactorOfMatrix_symmetric {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.IsHermitian) (v w : E n) :
    inner ℝ (dirichletCofactorOfMatrix A v) w =
      inner ℝ (dirichletCofactorOfMatrix A w) v := by
  have h (a b : E n) : inner ℝ (dirichletCofactorOfMatrix A a) b =
      (8 : ℝ)⁻¹ * hermitianRealification A.adjugate a b := by
    unfold dirichletCofactorOfMatrix
    rw [_root_.smul_apply, real_inner_smul_left]
    congr 1
    exact congrArg (fun F : E n →L[ℝ] ℝ => F b)
      ((InnerProductSpace.toDual ℝ (E n)).apply_symm_apply (hermitianRealification A.adjugate a))
  rw [h, h, hermitianRealification_symm hA.adjugate]

/-- A log-density path limit has a bounded uniformly elliptic cofactor
field. Its first directional derivatives satisfy the linearized divergence
equation, and its directional second derivatives satisfy the
corresponding subsolution inequalities in every real direction. -/
theorem exists_dirichlet_C1_limit_with_divergence_free_cofactor_of_logDensityPath {n : ℕ} (hn : 0 < n)
    {g : E n → ℝ} (hg : SmoothNear (closedUnitBall n) g)
    {t : ℕ → ℝ} {t₀ : ℝ} (ht : ∀ m, t m ∈ Icc (0 : ℝ) 1) (hT : Tendsto t atTop (𝓝 t₀))
    {u : ℕ → E n → ℝ} (hu : ∀ m, SmoothNear (closedUnitBall n) (u m))
    (hu0 : ∀ m x, x ∈ unitSphere n → u m x = 0)
    (huP : ∀ m x, x ∈ unitBall n → (complexHessian (u m) x).PosDef)
    (hEq : ∀ m x, x ∈ unitBall n → (complexHessian (u m) x).det.re = Real.exp (t m * g x)) :
    ∃ (φ : ℕ → ℕ) (w : E n → ℝ) (G : E n → E n →L[ℝ] ℝ) (L : ℝ≥0),
      StrictMono φ ∧ TendstoUniformlyOn u w atTop (closedUnitBall n) ∧
      TendstoUniformlyOn (fun j => fderiv ℝ (u (φ j))) G atTop (closedUnitBall n) ∧
      ContinuousOn w (closedUnitBall n) ∧
      (∀ x ∈ unitBall n, HasFDerivAt w (G x) x) ∧ LipschitzOnWith L G (closedUnitBall n) ∧
      (∀ x ∈ unitSphere n, w x = 0) ∧
      (∀ᵐ x ∂ν[n], (complexHessianOfRealBilinear (fderiv ℝ G x)).PosDef ∧
        (complexHessianOfRealBilinear (fderiv ℝ G x)).det.re = Real.exp (t₀ * g x)) ∧
      let A (x : E n) := dirichletCofactorOfMatrix (complexHessianOfRealBilinear (fderiv ℝ G x))
      MemLp A ⊤ ν[n] ∧
      (∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᵐ x ∂ν[n], ∀ v : E n,
        c * ‖v‖ ^ 2 ≤ inner ℝ (A x v) v ∧ inner ℝ (A x v) v ≤ C * ‖v‖ ^ 2) ∧
      (∀ (v : E n) (ψ : 𝓓B[n]),
        (∫ x, inner ℝ (A x v) (∇ (ψ : E n → ℝ) x) ∂ν[n]) = 0) ∧
      (∀ (i : Fin (2 * n)) (ψ : 𝓓B[n]),
        (∫ x, inner ℝ (A x (directionalHessianVector (fderiv ℝ G x) (e[n] i)))
          (∇ (ψ : E n → ℝ) x) ∂ν[n]) =
          -(∫ x, ψ x * fderiv ℝ (fun y => Real.exp (t₀ * g y)) x (e[n] i) ∂ν[n])) ∧
      ∀ v : E n, ∃ F : DirichletBallL2 n (E n),
        (∀ (j : Fin (2 * n)) (ψ : 𝓓B[n]),
          (∫ x, ψ x * inner ℝ (e[n] j) (F x) ∂ν[n]) =
            -(∫ x, fderiv ℝ (ψ : E n → ℝ) x (e[n] j) * fderiv ℝ G x v v ∂ν[n])) ∧
        ∀ ψ : 𝓓B[n], (∀ x ∈ unitBall n, 0 ≤ ψ x) →
          (∫ x, inner ℝ (A x (F x)) (∇ (ψ : E n → ℝ) x) ∂ν[n]) ≤
            -(∫ x, ψ x * (Real.exp (t₀ * g x) * (t₀ * realHessian g x v v)) ∂ν[n]) := by
  have : NeZero n := ⟨hn.ne'⟩
  obtain ⟨φ, w, G, L, hφ, hUw, hGrad, hD, hLip, hw0, _, _, M, _, ⟨ψ, hψ, hAe⟩, _, hEqA⟩ :=
    exists_dirichlet_C1_and_complexHessian_L2_limit_of_logDensityPath hn hg ht hT hu hu0 huP hEq
  let r (m : ℕ) := φ (ψ m)
  have hr := hφ.comp hψ
  let B (x : E n) := dirichletHessianMatrix (M x)
  let A (x : E n) := dirichletCofactorOfMatrix (B x)
  have hCont : Continuous (dirichletHessianMatrix (n := n)) :=
    continuous_matrix fun j k => (EuclideanSpace.proj (j, k)).continuous
  have hB : AEStronglyMeasurable B ν[n] := hCont.comp_aestronglyMeasurable (Lp.aestronglyMeasurable M)
  have hLim : ∀ᵐ x ∂ν[n], Tendsto (fun m => complexHessian (u (r m)) x) atTop (𝓝 (B x)) := by
    filter_upwards [hAe] with x hx
    exact ((hCont.tendsto (M x)).comp hx.1).congr
      (fun m => dirichletHessianMatrix_coordinates (complexHessian (u (r m)) x))
  have hA (m : ℕ) : AEStronglyMeasurable (complexHessian (u (r m))) ν[n] := by
    obtain ⟨U, hU, hSub, hC⟩ := hu (r m)
    have h : ContinuousOn (complexHessian (u (r m))) U :=
      continuousOn_pi.mpr fun j => continuousOn_pi.mpr fun k => (complexHessian_contDiffOn hU hC j k).continuousOn
    exact (h.mono (ball_subset_closedBall.trans hSub)).aestronglyMeasurable measurableSet_ball
  have hGradient : TendstoUniformlyOn (fun m => fderiv ℝ (u (r m))) G atTop (closedUnitBall n) :=
    fun U hU => hψ.tendsto_atTop.eventually (hGrad U hU)
  have hBall := ae_restrict_mem (μ := volume0 n) (show MeasurableSet (unitBall n) from measurableSet_ball)
  obtain ⟨D, hD'⟩ := exists_norm_complexHessian_le_of_logDensityPath hn hg
  have hBound (m : ℕ) (x : E n) (hx : x ∈ unitBall n) : ‖complexHessian (u (r m)) x‖ ≤ D :=
    hD' (t (r m)) (ht (r m)) (hu (r m)) (hu0 (r m)) (huP (r m)) (hEq (r m)) x hx
  have hBNorm : ∀ᵐ x ∂ν[n], ‖B x‖ ≤ D := by
    filter_upwards [hLim, hBall] with x hx hy
    exact le_of_tendsto' hx.norm (fun m => hBound m x hy)
  have hEqB : B =ᵐ[ν[n]] fun x => complexHessianOfRealBilinear (fderiv ℝ G x) := hEqA
  have hEqC : A =ᵐ[ν[n]] fun x => dirichletCofactorOfMatrix (complexHessianOfRealBilinear (fderiv ℝ G x)) :=
    hEqB.mono fun x hx => congrArg dirichletCofactorOfMatrix hx
  obtain ⟨H, R, hH, hR⟩ := exists_realHessian_L2_limit_of_logDensityPath hn hg
    (fun m => ht (r m)) (hT.comp hr.tendsto_atTop) (fun m => hu (r m)) (fun m => hu0 (r m))
    (fun m => huP (r m)) (fun m => hEq (r m))
  have hActual (j k : Fin (2 * n)) :
      H j k =ᵐ[ν[n]] fun x => fderiv ℝ G x (e[n] j) (e[n] k) :=
    ae_realHessian_eq_of_uniform_gradient hn (fun m => hu (r m)) hGradient hLip
      (e[n] j) (e[n] k) (H j k) (fun m => R m j k) (hH j k) (fun m => hR m j k)
  have hwC : ContinuousOn w (closedUnitBall n) :=
    hUw.continuousOn (Eventually.of_forall (fun m x hx =>
      ((hu m).contDiffAt hx).continuousAt.continuousWithinAt)).frequently
  refine ⟨φ, w, G, L, hφ, hUw, hGrad, hwC, hD, hLip, hw0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · filter_upwards [hAe, hEqB] with x hx hy
    rw [← hy]
    exact hx.2
  · obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : Matrix (Fin n) (Fin n) ℂ) D).exists_bound_of_continuousOn
      continuous_dirichletCofactorOfMatrix.continuousOn
    have hMem : MemLp A ⊤ ν[n] := memLp_top_of_bound
      (continuous_dirichletCofactorOfMatrix.comp_aestronglyMeasurable hB) C
      (hBNorm.mono fun x hx => hC (B x) (mem_closedBall_zero_iff.mpr hx))
    exact hMem.ae_eq hEqC
  · obtain ⟨c, C, hc, hC, hEll⟩ := exists_uniform_cofactor_ellipticity_of_logDensityPath hn hg
    refine ⟨c, C, hc, hC, ?_⟩
    filter_upwards [hEqC, hBall, hLim] with x hx hxb hL v
    rw [← hx]
    have hPair : Tendsto (fun m => inner ℝ (dirichletCofactorOfMatrix (complexHessian (u (r m)) x) v) v)
        atTop (𝓝 (inner ℝ (A x v) v)) :=
      ((continuous_id.inner (𝕜 := ℝ) (continuous_const : Continuous (fun _ : E n => v))).tendsto
      (A x v)).comp (((ContinuousLinearMap.apply ℝ (E n) v).continuous.tendsto (A x)).comp
        ((continuous_dirichletCofactorOfMatrix.tendsto (B x)).comp hL))
    exact ⟨ge_of_tendsto' hPair (fun m => (hEll (t (r m)) (ht (r m))
      (hu (r m)) (hu0 (r m)) (huP (r m)) (hEq (r m)) x hxb v).1),
      le_of_tendsto' hPair (fun m => (hEll (t (r m)) (ht (r m))
        (hu (r m)) (hu0 (r m)) (huP (r m)) (hEq (r m)) x hxb v).2)⟩
  · intro v η
    have hDiv := integral_dirichletCofactorOfMatrix_const_eq_zero_of_limit hn
      (fun m => hu (r m)) (fun m => huP (r m)) hA hB
      (fun m => hBall.mono fun x hx => hBound m x hx) hLim v η
    calc
      _ = ∫ x, inner ℝ (A x v) (∇ (η : E n → ℝ) x) ∂ν[n] := by
        apply integral_congr_ae
        filter_upwards [hEqC] with x hx
        rw [hx]
      _ = 0 := hDiv
  · intro i
    obtain ⟨Y, X, hX, hXm, hY⟩ := exists_tendsto_directionalHessianVector
      (fun j k => ⟨H j k, fun m => R m j k, hH j k, fun m => hR m j k, hActual j k⟩) i
    intro η
    have hLeft := tendsto_integral_cofactor_pairing hn hA hB
      (fun m => hBall.mono fun x hx => hBound m x hx) hLim hX η
    have hRight := (integral_test_fderiv_logDensityPath_tendsto hn hg (fun m => ht (r m))
      (hT.comp hr.tendsto_atTop) η (e[n] i)).neg
    have hI (m : ℕ) :
        -(∫ x, η x * fderiv ℝ (fun y => Real.exp (t (r m) * g y)) x (e[n] i) ∂ν[n]) =
          ∫ x, inner ℝ (dirichletCofactorOfMatrix (complexHessian (u (r m)) x) (X m x))
            (∇ (η : E n → ℝ) x) ∂ν[n] := by
      rw [← integral_cofactor_directionalDerivative_eq_neg hn (hu (r m)) (huP (r m)) (hEq (r m)) η]
      apply integral_congr_ae
      filter_upwards [hXm m, hBall] with x hx hxb
      rw [hx, dirichletCofactorOfMatrix_complexHessian,
        gradient_directionalDerivative ((hu (r m)).contDiffAt (ball_subset_closedBall hxb))]
    rw [← tendsto_nhds_unique hLeft (hRight.congr hI)]
    apply integral_congr_ae
    filter_upwards [hEqC, hY] with x hx hy
    change inner ℝ (dirichletCofactorOfMatrix (complexHessianOfRealBilinear (fderiv ℝ G x))
      (directionalHessianVector (fderiv ℝ G x) (e[n] i))) _ = inner ℝ (A x (Y x)) _
    rw [hx, hy]

  · intro v
    obtain ⟨C, _, hThird⟩ := exists_integral_sq_realThirdDerivative_le_of_logDensityPath hn hg
    obtain ⟨F, Q, hQ, hNorm, hWeak⟩ := exists_weakCluster_realThirdDerivative_of_direction hn
      (fun m => hu (r m))
      (fun m => hThird (t (r m)) (ht (r m)) (hu (r m)) (hu0 (r m)) (huP (r m)) (hEq (r m))) v
    let Y : DirichletBallL2 n (E n) := (bilinearCoordinateDirection v).compLp F
    refine ⟨Y, ?_, ?_⟩
    · exact integral_test_hessianSelf_weakGradient hn (fun m => hu (r m)) v hQ hNorm hWeak hH hR hActual
    · intro η hη
      have hW := mapClusterPt_inner_cofactor_pairing hn hA hB
        (fun m => hBall.mono fun x hx => hBound m x hx) hLim hNorm hWeak v η
      obtain ⟨σ, hσ, hS⟩ := hW.tendsto_subseq
      have hT' := ((integral_test_hessianSource_logDensityPath_tendsto hn hg
        (fun m => ht (r m)) (hT.comp hr.tendsto_atTop) η v).neg).comp hσ.tendsto_atTop
      have hI (m : ℕ) : (∫ x, inner ℝ (dirichletCofactorOfMatrix (complexHessian (u (r m)) x)
          (((bilinearCoordinateDirection v).compLp (Q m) : DirichletBallL2 n (E n)) x))
          (∇ (η : E n → ℝ) x) ∂ν[n]) ≤
          -(∫ x, η x * (Real.exp (t (r m) * g x) * (t (r m) * realHessian g x v v)) ∂ν[n]) := by
        let f (x : E n) := Real.exp (t (r m) * g x)
        have hf : SmoothNear (closedUnitBall n) f := by
          obtain ⟨U, hU, hSub, hgU⟩ := hg
          exact ⟨U, hU, hSub, (contDiffOn_const.mul hgU).exp⟩
        have hLeft : (∫ x, inner ℝ (dirichletCofactorOfMatrix (complexHessian (u (r m)) x)
            (((bilinearCoordinateDirection v).compLp (Q m) : DirichletBallL2 n (E n)) x))
            (∇ (η : E n → ℝ) x) ∂ν[n]) =
            ∫ x, inner ℝ (dirichletCofactorOperator (u (r m)) x
              (∇ (fun y => realHessian (u (r m)) y v v) x))
              (∇ (η : E n → ℝ) x) ∂ν[n] := by
          apply integral_congr_ae
          filter_upwards [(bilinearCoordinateDirection v).coeFn_compLp (Q m), hQ m, hBall] with x hx hy hz
          rw [hx, hy, ← gradient_realHessian_self ((hu (r m)).contDiffAt (ball_subset_closedBall hz)),
            dirichletCofactorOfMatrix_complexHessian]
        have hRight : (∫ x, η x * (f x * realHessian (fun y => Real.log (f y)) x v v) ∂ν[n]) =
            ∫ x, η x * (f x * (t (r m) * realHessian g x v v)) ∂ν[n] := by
          apply integral_congr_ae
          filter_upwards [hBall] with x hx
          rw [show (fun y => Real.log (f y)) = (fun y => Real.log (Real.exp (t (r m) * g y))) from rfl,
            hessian_log_exp_mul (hg.contDiffAt (ball_subset_closedBall hx))]
        rw [hLeft, ← hRight]
        exact integral_cofactor_realHessian_self_le hn (hu (r m)) hf (huP (r m)) (hEq (r m)) η hη v
      have hL := le_of_tendsto_of_tendsto' hS hT' (fun m => hI (σ m))
      apply le_trans _ hL
      apply le_of_eq
      apply integral_congr_ae
      filter_upwards [hEqC] with x hx
      change inner ℝ (dirichletCofactorOfMatrix (complexHessianOfRealBilinear (fderiv ℝ G x)) (Y x)) _ =
        inner ℝ (A x (Y x)) _
      rw [hx]

/-- The earlier interface is retained with exactly its original proposition.
The stronger theorem also exposes the original uniform C1 subsequence. -/
theorem exists_dirichlet_limit_with_divergence_free_cofactor_of_logDensityPath {n : ℕ} (hn : 0 < n)
    {g : E n → ℝ} (hg : SmoothNear (closedUnitBall n) g)
    {t : ℕ → ℝ} {t₀ : ℝ} (ht : ∀ m, t m ∈ Icc (0 : ℝ) 1) (hT : Tendsto t atTop (𝓝 t₀))
    {u : ℕ → E n → ℝ} (hu : ∀ m, SmoothNear (closedUnitBall n) (u m))
    (hu0 : ∀ m x, x ∈ unitSphere n → u m x = 0)
    (huP : ∀ m x, x ∈ unitBall n → (complexHessian (u m) x).PosDef)
    (hEq : ∀ m x, x ∈ unitBall n → (complexHessian (u m) x).det.re = Real.exp (t m * g x)) :
    ∃ (w : E n → ℝ) (G : E n → E n →L[ℝ] ℝ) (L : ℝ≥0),
      ContinuousOn w (closedUnitBall n) ∧
      (∀ x ∈ unitBall n, HasFDerivAt w (G x) x) ∧ LipschitzOnWith L G (closedUnitBall n) ∧
      (∀ x ∈ unitSphere n, w x = 0) ∧
      (∀ᵐ x ∂ν[n], (complexHessianOfRealBilinear (fderiv ℝ G x)).PosDef ∧
        (complexHessianOfRealBilinear (fderiv ℝ G x)).det.re = Real.exp (t₀ * g x)) ∧
      let A (x : E n) := dirichletCofactorOfMatrix (complexHessianOfRealBilinear (fderiv ℝ G x))
      MemLp A ⊤ ν[n] ∧
      (∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᵐ x ∂ν[n], ∀ v : E n,
        c * ‖v‖ ^ 2 ≤ inner ℝ (A x v) v ∧ inner ℝ (A x v) v ≤ C * ‖v‖ ^ 2) ∧
      (∀ (v : E n) (ψ : 𝓓B[n]),
        (∫ x, inner ℝ (A x v) (∇ (ψ : E n → ℝ) x) ∂ν[n]) = 0) ∧
      (∀ (i : Fin (2 * n)) (ψ : 𝓓B[n]),
        (∫ x, inner ℝ (A x (directionalHessianVector (fderiv ℝ G x) (e[n] i)))
          (∇ (ψ : E n → ℝ) x) ∂ν[n]) =
          -(∫ x, ψ x * fderiv ℝ (fun y => Real.exp (t₀ * g y)) x (e[n] i) ∂ν[n])) ∧
      ∀ v : E n, ∃ F : DirichletBallL2 n (E n),
        (∀ (j : Fin (2 * n)) (ψ : 𝓓B[n]),
          (∫ x, ψ x * inner ℝ (e[n] j) (F x) ∂ν[n]) =
            -(∫ x, fderiv ℝ (ψ : E n → ℝ) x (e[n] j) * fderiv ℝ G x v v ∂ν[n])) ∧
        ∀ ψ : 𝓓B[n], (∀ x ∈ unitBall n, 0 ≤ ψ x) →
          (∫ x, inner ℝ (A x (F x)) (∇ (ψ : E n → ℝ) x) ∂ν[n]) ≤
            -(∫ x, ψ x * (Real.exp (t₀ * g x) * (t₀ * realHessian g x v v)) ∂ν[n]) := by
  obtain ⟨φ, w, G, L, hφ, hUw, hGrad, h⟩ :=
    exists_dirichlet_C1_limit_with_divergence_free_cofactor_of_logDensityPath
      hn hg ht hT hu hu0 huP hEq
  exact ⟨w, G, L, h⟩

/-- The original S053 interface is retained verbatim. The stronger endpoint
also keeps the divergence-free cofactor identity for the very same limit. -/
theorem exists_dirichlet_limit_with_divergence_equation_of_logDensityPath {n : ℕ} (hn : 0 < n)
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
      let A (x : E n) := dirichletCofactorOfMatrix (complexHessianOfRealBilinear (fderiv ℝ G x))
      MemLp A ⊤ ν[n] ∧
      (∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᵐ x ∂ν[n], ∀ v : E n,
        c * ‖v‖ ^ 2 ≤ inner ℝ (A x v) v ∧ inner ℝ (A x v) v ≤ C * ‖v‖ ^ 2) ∧
      (∀ (i : Fin (2 * n)) (ψ : 𝓓B[n]),
        (∫ x, inner ℝ (A x (directionalHessianVector (fderiv ℝ G x) (e[n] i)))
          (∇ (ψ : E n → ℝ) x) ∂ν[n]) =
          -(∫ x, ψ x * fderiv ℝ (fun y => Real.exp (t₀ * g y)) x (e[n] i) ∂ν[n])) ∧
      ∀ v : E n, ∃ F : DirichletBallL2 n (E n),
        (∀ (j : Fin (2 * n)) (ψ : 𝓓B[n]),
          (∫ x, ψ x * inner ℝ (e[n] j) (F x) ∂ν[n]) =
            -(∫ x, fderiv ℝ (ψ : E n → ℝ) x (e[n] j) * fderiv ℝ G x v v ∂ν[n])) ∧
        ∀ ψ : 𝓓B[n], (∀ x ∈ unitBall n, 0 ≤ ψ x) →
          (∫ x, inner ℝ (A x (F x)) (∇ (ψ : E n → ℝ) x) ∂ν[n]) ≤
            -(∫ x, ψ x * (Real.exp (t₀ * g x) * (t₀ * realHessian g x v v)) ∂ν[n]) := by
  obtain ⟨w, G, L, _, hD, hLip, hw0, hH, hMem, hEll, _, hFirst, hSecond⟩ :=
    exists_dirichlet_limit_with_divergence_free_cofactor_of_logDensityPath
      hn hg ht hT hu hu0 huP hEq
  exact ⟨w, G, L, hD, hLip, hw0, hH, hMem, hEll, hFirst, hSecond⟩

end KEBall
