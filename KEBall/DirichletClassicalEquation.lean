import KEBall.DirichletSmoothRepresentative
import KEBall.DirichletCofactorHessian

/-! Classical representatives and zero boundary values for the cofactor Dirichlet equation. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Metric Set
open scoped ComplexOrder ContDiff Distributions Gradient NNReal Topology

namespace KEBall

local notation "ν[" n "]" => Measure.restrict (volume0 n) (unitBall n)
local notation "𝓓B[" n "]" => 𝓓(dirichletBallOpens n, ℝ)

theorem ae_eq_on_unitBall_of_tests {n : ℕ} {f g : E n → ℝ}
    (hf : LocallyIntegrableOn f (unitBall n) ν[n])
    (hg : LocallyIntegrableOn g (unitBall n) ν[n])
    (he : ∀ φ : 𝓓B[n], (∫ x, φ x * f x ∂ν[n]) = ∫ x, φ x * g x ∂ν[n]) :
    f =ᵐ[ν[n]] g := by
  have hz : ∀ᵐ x ∂ν[n], x ∈ unitBall n → f x - g x = 0 := by
    apply (show IsOpen (unitBall n) from isOpen_ball).ae_eq_zero_of_integral_contDiff_smul_eq_zero (hf.sub hg)
    intro ψ hψ hs hsub
    let φ : 𝓓B[n] := ⟨ψ, hψ, hs, hsub⟩
    have hI {u : E n → ℝ} (hu : LocallyIntegrableOn u (unitBall n) ν[n]) :
        Integrable (fun x => ψ x * u x) ν[n] :=
      φ.integrable_bilin (ContinuousLinearMap.lsmul ℝ ℝ) hu
    change (∫ x, ψ x * (f x - g x) ∂ν[n]) = 0
    simp_rw [mul_sub]
    rw [integral_sub (hI hf) (hI hg)]
    exact sub_eq_zero.mpr (he φ)
  filter_upwards [hz, ae_restrict_mem (μ := volume0 n)
    (show MeasurableSet (unitBall n) from measurableSet_ball)] with x hx hBall
  exact sub_eq_zero.mp (hx hBall)

private theorem contDiffOn_ball_gradient {n : ℕ} {g : E n → ℝ}
    (hg : ContDiffOn ℝ ∞ g (unitBall n)) :
    ContDiffOn ℝ ∞ (∇ g) (unitBall n) :=
  (InnerProductSpace.toDual ℝ (E n)).symm.toContinuousLinearEquiv.contDiff.contDiffOn.comp
    (hg.fderiv_of_isOpen isOpen_ball (by simp)) (mapsTo_univ _ _)

private theorem integral_dirichletTest_euclideanDivergence {n : ℕ} (hn : 0 < n)
    (ψ : 𝓓B[n]) {V : E n → E n} (hV : ContDiffOn ℝ ∞ V (unitBall n)) :
    (∫ x, ψ x * euclideanDivergence V x ∂ν[n]) =
      -(∫ x, fderiv ℝ (ψ : E n → ℝ) x (V x) ∂ν[n]) := by
  let W (x : E n) := ψ x • V x
  have hW : ContDiff ℝ ∞ W := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ unitBall n
    · exact ψ.contDiff.contDiffAt.smul (hV.contDiffAt (isOpen_ball.mem_nhds hx))
    · have hSupp : x ∉ tsupport (ψ : E n → ℝ) := fun hx' => hx (ψ.tsupport_subset hx')
      apply (contDiffAt_const (c := (0 : E n))).congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hSupp] with y hy
      change ψ y • V y = 0
      rw [hy, Pi.zero_apply, zero_smul]
  have hFlux (θ : Sphere n) : inner ℝ θ.1 (W θ.1) = 0 := by
    have hz : ψ θ.1 = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hs
      exact (not_lt_of_ge (mem_sphere_zero_iff_norm.mp θ.2).ge)
        (mem_ball_zero_iff.mp (ψ.tsupport_subset hs))
    simp [W, hz]
  have hZero : (∫ x, euclideanDivergence W x ∂ν[n]) = 0 := by
    simpa only [hFlux, integral_zero, mul_zero] using
      integral_unitBall_divergence_normalized hn (hW.of_le (by simp))
  have hD (x : E n) (hx : x ∈ unitBall n) :
      euclideanDivergence W x = ψ x * euclideanDivergence V x + fderiv ℝ (ψ : E n → ℝ) x (V x) :=
    euclideanDivergence_smul (ψ.contDiff.differentiable (by simp) x)
      ((hV.contDiffAt (isOpen_ball.mem_nhds hx)).differentiableAt (by simp))
  have hI₁ : Integrable (fun x => ψ x * euclideanDivergence V x) ν[n] := by
    have hC : ContinuousOn (euclideanDivergence V) (unitBall n) := by
      unfold euclideanDivergence
      exact continuousOn_finsetSum _ fun i _ =>
        (((EuclideanSpace.proj i : E n →L[ℝ] ℝ).contDiff.comp_contDiffOn hV).fderiv_of_isOpen
          isOpen_ball (by simp) (m := 0)).continuousOn.clm_apply continuousOn_const
    exact ψ.integrable_bilin (ContinuousLinearMap.lsmul ℝ ℝ)
      (hC.locallyIntegrableOn measurableSet_ball)
  have hI₂ : Integrable (fun x => fderiv ℝ (ψ : E n → ℝ) x (V x)) ν[n] := by
    let ψ' := TestFunction.fderivCLM ℝ ⊤ ⊤ ψ
    have he (x : E n) : ψ' x = fderiv ℝ (ψ : E n → ℝ) x :=
      congrFun (TestFunction.fderivCLM_apply_of_le (𝕜 := ℝ) (k := (⊤ : ℕ∞)) ψ (by simp)) x
    simp_rw [← he]
    exact ψ'.integrable_bilin (ContinuousLinearMap.apply ℝ ℝ (E := E n)).flip
      (hV.continuousOn.locallyIntegrableOn measurableSet_ball)
  have h := (setIntegral_congr_fun (show MeasurableSet (unitBall n) from measurableSet_ball) hD).symm.trans hZero
  rw [integral_add hI₁ hI₂] at h
  linarith only [h]

/-- A smooth representative of the scalar weak solution has the represented
classical gradient almost everywhere in the ball. -/
theorem dirichletSobolev_gradient_ae_eq_of_contDiffOn {n : ℕ} (hn : 0 < n)
    (w : DirichletSobolev n) {g : E n → ℝ} (hg : ContDiffOn ℝ ∞ g (unitBall n))
    (he : g =ᵐ[ν[n]] ((w : DirichletBallL2Pair n).fst : E n → ℝ)) :
    (∇ g) =ᵐ[ν[n]] ((w : DirichletBallL2Pair n).snd : E n → E n) := by
  let b := EuclideanSpace.basisFun (Fin (2 * n)) ℝ
  let W := (w : DirichletBallL2Pair n).snd
  have hDir (i : Fin (2 * n)) :
      (fun x => fderiv ℝ g x (b i)) =ᵐ[ν[n]] fun x => inner ℝ (b i) (W x) := by
    apply ae_eq_on_unitBall_of_tests
    · exact (((hg.fderiv_of_isOpen isOpen_ball (by simp) (m := 0)).continuousOn).clm_apply
        continuousOn_const).locallyIntegrableOn measurableSet_ball
    · exact ((Lp.memLp W).const_inner (b i)).locallyIntegrable (by norm_num)
        |>.locallyIntegrableOn _
    intro φ
    let V (x : E n) := g x • b i
    have hV : ContDiffOn ℝ ∞ V (unitBall n) := hg.smul contDiffOn_const
    have hDiv (x : E n) (hx : x ∈ unitBall n) : euclideanDivergence V x = fderiv ℝ g x (b i) := by
      rw [euclideanDivergence_smul ((hg.contDiffAt (isOpen_ball.mem_nhds hx)).differentiableAt (by simp))
        (differentiableAt_const (b i))]
      simp [euclideanDivergence]
    have h₁ := integral_dirichletTest_euclideanDivergence hn φ hV
    rw [setIntegral_congr_fun (show MeasurableSet (unitBall n) from measurableSet_ball)
      (fun x hx => congrArg (φ x * ·) (hDiv x hx))] at h₁
    have h₂ : (∫ x, fderiv ℝ (φ : E n → ℝ) x (V x) ∂ν[n]) =
        ∫ x, fderiv ℝ (φ : E n → ℝ) x (b i) * (w : DirichletBallL2Pair n).fst x ∂ν[n] := by
      apply integral_congr_ae
      filter_upwards [he] with x hx
      simp only [V, map_smul, smul_eq_mul, hx, mul_comm]
    rw [h₂] at h₁
    exact h₁.trans (dirichletSobolev_integral_weakGradient w φ (b i)).symm
  filter_upwards [Filter.eventually_all.mpr hDir] with x hx
  apply b.repr.injective
  ext i
  rw [OrthonormalBasis.repr_apply_apply, OrthonormalBasis.repr_apply_apply,
    real_inner_comm (∇ g x) (b i), inner_gradient_left]
  exact hx i

/-- A smooth representative of a weak Dirichlet solution satisfies the
divergence-form equation pointwise throughout the open ball. -/
theorem IsDirichletWeakSolution.euclideanDivergence_gradient_eq_of_contDiffOn
    {n : ℕ} (hn : 0 < n) {A : E n → E n →L[ℝ] E n} {g : DirichletBallL2 n ℝ}
    {w : DirichletSobolev n} (hw : IsDirichletWeakSolution A g w)
    (hA : ContDiffOn ℝ ∞ A (unitBall n)) {v G : E n → ℝ}
    (hv : ContDiffOn ℝ ∞ v (unitBall n))
    (hvRep : v =ᵐ[ν[n]] ((w : DirichletBallL2Pair n).fst : E n → ℝ))
    (hG : ContinuousOn G (unitBall n)) (hGRep : g =ᵐ[ν[n]] G) :
    EqOn (euclideanDivergence (fun x => A x (∇ v x))) (fun x => -G x) (unitBall n) := by
  let V (x : E n) := A x (∇ v x)
  have hV : ContDiffOn ℝ ∞ V (unitBall n) := hA.clm_apply (contDiffOn_ball_gradient hv)
  have hD : ContinuousOn (euclideanDivergence V) (unitBall n) := by
    unfold euclideanDivergence
    exact continuousOn_finsetSum _ fun i _ =>
      (((EuclideanSpace.proj i : E n →L[ℝ] ℝ).contDiff.comp_contDiffOn hV).fderiv_of_isOpen
        isOpen_ball (by simp) (m := 0)).continuousOn.clm_apply continuousOn_const
  apply (volume0 n).eqOn_open_of_ae_eq _ isOpen_ball hD hG.neg
  apply ae_eq_on_unitBall_of_tests (hD.locallyIntegrableOn measurableSet_ball)
    (hG.neg.locallyIntegrableOn measurableSet_ball)
  intro φ
  have h₁ := integral_dirichletTest_euclideanDivergence hn φ hV
  have h₂ := hw.integral_fderiv_test φ
  have hEq₁ : (∫ x, fderiv ℝ (φ : E n → ℝ) x (V x) ∂ν[n]) =
      ∫ x, fderiv ℝ (φ : E n → ℝ) x (A x ((w : DirichletBallL2Pair n).snd x)) ∂ν[n] := by
    apply integral_congr_ae
    filter_upwards [dirichletSobolev_gradient_ae_eq_of_contDiffOn hn w hv hvRep] with x hx
    simp only [V, hx]
  have hEq₂ : (∫ x, φ x * g x ∂ν[n]) = ∫ x, φ x * G x ∂ν[n] := by
    apply integral_congr_ae
    filter_upwards [hGRep] with x hx
    rw [hx]
  rw [hEq₁, h₂, hEq₂, ← integral_neg] at h₁
  simpa only [Pi.neg_apply, mul_neg] using h₁

/-- The real cofactor flux is twice the real coefficient applied to the gradient. -/
theorem cofactorRealField_eq_two_smul_operator {n : ℕ} {u v : E n → ℝ} {x : E n}
    (hv : DifferentiableAt ℝ v x) :
    cofactorRealField u v x = (2 : ℝ) • dirichletCofactorOperator u x (∇ v x) := by
  apply ext_inner_right ℝ
  intro d
  have he := cofactorRealField_pairing_eq_dirichletCofactorOperator
    (u := u) (x := x) (v := fun y => inner ℝ d y) (innerSL ℝ d).differentiableAt hv
  change fderiv ℝ (innerSL ℝ d : E n → ℝ) x (cofactorRealField u v x) =
    2 * inner ℝ (dirichletCofactorOperator u x (∇ v x)) (∇ (innerSL ℝ d : E n → ℝ) x) at he
  have hGrad : ∇ (innerSL ℝ d : E n → ℝ) x = d := by
    apply ext_inner_right ℝ
    intro e
    rw [inner_gradient_left, (innerSL ℝ d).hasFDerivAt.fderiv]
    rfl
  rw [(innerSL ℝ d).hasFDerivAt.fderiv, hGrad] at he
  rw [real_inner_smul_left]
  exact (real_inner_comm _ _).trans he

private theorem euclideanDivergence_half_smul {n : ℕ} {V : E n → E n} {x : E n}
    (hV : DifferentiableAt ℝ V x) :
    euclideanDivergence (fun y => (2 : ℝ)⁻¹ • V y) x =
      (2 : ℝ)⁻¹ * euclideanDivergence V x := by
  rw [euclideanDivergence_smul (differentiableAt_const ((2 : ℝ)⁻¹)) hV]
  simp

/-- On the interior, the classical equation for the real cofactor
operator is exactly the determinant linearization. -/
theorem dirichletCofactorOperator_divergence_gradient {n : ℕ} {u v : E n → ℝ}
    (hu : ContDiffOn ℝ ∞ u (unitBall n)) (hv : ContDiffOn ℝ ∞ v (unitBall n))
    {x : E n} (hx : x ∈ unitBall n) (hU : IsUnit (complexHessian u x).det) :
    euclideanDivergence (fun y => dirichletCofactorOperator u y (∇ v y)) x =
      MoserTrudinger.cofactorContraction u v x := by
  have hxN := isOpen_ball.mem_nhds hx
  have huX := hu.contDiffAt hxN
  have hvX := hv.contDiffAt hxN
  have huC : ContDiffAt ℝ ∞ (fun y => (u y : ℂ)) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x huX
  have hPiola (j : Fin n) :
      (∑ i : Fin n, partialZ i (fun y => (complexHessian u y).adjugate j i) x) = 0 :=
    cofactor_divergence_at huC realDirection imagDirection hU j
  have hFlux : DifferentiableAt ℝ (cofactorRealField u v) x :=
    ((cofactorRealField_contDiffOn isOpen_ball hu hv).contDiffAt hxN).differentiableAt (by simp)
  have hNear : (fun y => dirichletCofactorOperator u y (∇ v y)) =ᶠ[𝓝 x]
      fun y => (2 : ℝ)⁻¹ • cofactorRealField u v y := by
    filter_upwards [hxN] with y hy
    rw [cofactorRealField_eq_two_smul_operator ((hv.contDiffAt (isOpen_ball.mem_nhds hy)).differentiableAt
      (by simp)), smul_smul, inv_mul_cancel₀ (by norm_num), one_smul]
  have hDiv : euclideanDivergence (fun y => dirichletCofactorOperator u y (∇ v y)) x =
      euclideanDivergence (fun y => (2 : ℝ)⁻¹ • cofactorRealField u v y) x := by
    unfold euclideanDivergence
    apply Finset.sum_congr rfl
    intro i _
    have h : (fun y => (dirichletCofactorOperator u y (∇ v y)) i) =ᶠ[𝓝 x]
        fun y => ((2 : ℝ)⁻¹ • cofactorRealField u v y) i :=
      hNear.fun_comp (fun z : E n => z i)
    rw [h.fderiv_eq]
  rw [hDiv, euclideanDivergence_half_smul hFlux, cofactorRealField_divergence_of_piola huX hvX hPiola]
  simp [MoserTrudinger.cofactorContraction]

private theorem memLp_continuous_closedBall {n : ℕ} (hn : 0 < n) {F : Type*}
    [NormedAddCommGroup F] {h : E n → F} (hc : Continuous h) : MemLp h 2 ν[n] := by
  have : NeZero n := ⟨hn.ne'⟩
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : E n) 1).exists_bound_of_continuousOn hc.continuousOn
  refine MemLp.of_bound hc.aestronglyMeasurable C ?_
  filter_upwards [ae_restrict_mem (μ := volume0 n)
    (show MeasurableSet (unitBall n) from measurableSet_ball)] with x hx
  exact hC x (ball_subset_closedBall hx)

/-- The weak Green formula for a zero-trace graph element can be tested
against a smooth field that extends across the sphere. -/
theorem dirichletSobolev_integral_divergence {n : ℕ} (hn : 0 < n)
    (w : DirichletSobolev n) {X : E n → E n} (hX : ContDiff ℝ ∞ X) :
    (∫ x, (w : DirichletBallL2Pair n).fst x * euclideanDivergence X x ∂ν[n]) +
      (∫ x, inner ℝ ((w : DirichletBallL2Pair n).snd x) (X x) ∂ν[n]) = 0 := by
  let V := (memLp_continuous_closedBall hn hX.continuous).toLp X
  have hDiv : Continuous (euclideanDivergence X) := by
    rw [← funext (dirichletVectorDivergence_basisFun_eq_euclideanDivergence X)]
    exact (contDiff_dirichletVectorDivergence _ hX).continuous
  let g := (memLp_continuous_closedBall hn hDiv).toLp (euclideanDivergence X)
  let L : DirichletBallL2Pair n →L[ℝ] ℝ :=
    (innerSL ℝ g).comp (WithLp.fstL 2 ℝ _ _) + (innerSL ℝ V).comp (WithLp.sndL 2 ℝ _ _)
  have he (p : DirichletBallL2Pair n) : L p =
      (∫ x, p.fst x * euclideanDivergence X x ∂ν[n]) +
        ∫ x, inner ℝ (p.snd x) (X x) ∂ν[n] := by
    change inner ℝ g p.fst + inner ℝ V p.snd = _
    rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
    congr 1
    · apply integral_congr_ae
      filter_upwards [MemLp.coeFn_toLp (memLp_continuous_closedBall hn hDiv)] with x hx
      change inner ℝ (g x) (p.fst x) = _
      rw [hx, Real.inner_apply, mul_comm]
    · apply integral_congr_ae
      filter_upwards [MemLp.coeFn_toLp (memLp_continuous_closedBall hn hX.continuous)] with x hx
      change inner ℝ (V x) (p.snd x) = _
      rw [hx, real_inner_comm]
  have hClosed : IsClosed {p | L p = 0} := isClosed_eq L.continuous continuous_const
  have hRange : ((dirichletTestL2Graph n).range : Set (DirichletBallL2Pair n)) ⊆ {p | L p = 0} := by
    rintro p ⟨φ, rfl⟩
    change L (dirichletTestL2Graph n φ) = 0
    rw [he]
    have h₁ : (∫ x, (dirichletTestL2Graph n φ).fst x * euclideanDivergence X x ∂ν[n]) =
        ∫ x, φ x * euclideanDivergence X x ∂ν[n] := by
      apply integral_congr_ae
      filter_upwards [dirichletTestToL2_ae φ] with x hx
      change dirichletTestToL2 φ x * euclideanDivergence X x = _
      rw [hx]
    have h₂ : (∫ x, inner ℝ ((dirichletTestL2Graph n φ).snd x) (X x) ∂ν[n]) =
        ∫ x, fderiv ℝ (φ : E n → ℝ) x (X x) ∂ν[n] := by
      apply integral_congr_ae
      filter_upwards [dirichletTestGradientToL2_ae φ] with x hx
      change inner ℝ (dirichletTestGradientToL2 n φ x) (X x) = _
      rw [hx, inner_gradient_left]
    rw [h₁, h₂, integral_dirichletTest_euclideanDivergence hn φ hX.contDiffOn, neg_add_cancel]
  rw [← he]
  exact closure_minimal hRange hClosed w.property

private theorem eulerFlux_limit_square_zero {n : ℕ} (hn : 0 < n)
    (w : DirichletSobolev n) {g : E n → ℝ} (hg : ContDiffOn ℝ ∞ g (closedUnitBall n))
    (he : g =ᵐ[ν[n]] ((w : DirichletBallL2Pair n).fst : E n → ℝ))
    (F : ℕ → E n → ℝ) (hF : ∀ j, ContDiff ℝ ∞ (F j))
    (L : E n → E n →L[ℝ] ℝ)
    (h₀ : TendstoUniformlyOn F g atTop (closedUnitBall n))
    (h₁ : TendstoUniformlyOn (fun j => fderiv ℝ (F j)) L atTop (closedUnitBall n))
    (hL : EqOn L (fderiv ℝ g) (unitBall n)) :
    (∫ θ : Sphere n, (g θ.1) ^ 2 ∂sphere0 n) = 0 := by
  have : NeZero n := ⟨hn.ne'⟩
  let q (j : ℕ) (x : E n) := (F j x) ^ 2
  let V (j : ℕ) (x : E n) := q j x • x
  let D (j : ℕ) (x : E n) := (2 * n : ℝ) * q j x + 2 * F j x * (fderiv ℝ (F j) x x)
  let d (x : E n) := (2 * n : ℝ) * (g x) ^ 2 + 2 * g x * (L x x)
  let J (j : ℕ) := ∫ x, D j x ∂ν[n]
  have hJ (j : ℕ) : J j = (2 * n : ℝ) * ∫ θ : Sphere n, q j θ.1 ∂sphere0 n := by
    have hV : ContDiff ℝ 1 (V j) :=
      (((hF j).pow 2).smul contDiff_id).of_le (by simp)
    have hD (x : E n) : euclideanDivergence (V j) x = D j x := by
      have hf := (hF j).differentiable (by simp) x
      change euclideanDivergence (fun y => (F j y) ^ 2 • y) x = _
      rw [euclideanDivergence_scalar_euler (show DifferentiableAt ℝ (q j) x from hf.pow 2),
        show fderiv ℝ (q j) x = _ from fderiv_pow 2 hf]
      simp [D, q]
    have hFlux (θ : Sphere n) : inner ℝ θ.1 (V j θ.1) = q j θ.1 := by
      rw [show V j θ.1 = q j θ.1 • θ.1 from rfl, real_inner_smul_right,
        real_inner_self_eq_norm_sq, mem_sphere_zero_iff_norm.mp θ.2]
      ring
    simpa only [J, hD, hFlux] using integral_unitBall_divergence_normalized hn hV
  have hBound_g := (isCompact_closedBall (0 : E n) 1).exists_bound_of_continuousOn hg.continuousOn
  have hCL : ContinuousOn L (closedUnitBall n) :=
    h₁.continuousOn (Eventually.frequently (Eventually.of_forall fun j =>
      ((hF j).fderiv_right (m := ∞) (by simp)).continuous.continuousOn))
  obtain ⟨C, hC⟩ := hBound_g
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : E n) 1).exists_bound_of_continuousOn hCL
  have hBound₀ : ∀ᶠ j in atTop, ∀ x ∈ closedUnitBall n, ‖F j x‖ ≤ C + 1 := by
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp h₀ 1 zero_lt_one] with j hj x hx
    have h := hj x hx
    rw [dist_comm, dist_eq_norm] at h
    calc
      ‖F j x‖ ≤ ‖F j x - g x‖ + ‖g x‖ := norm_le_norm_sub_add _ _
      _ ≤ C + 1 := by linarith [hC x hx]
  have hBound₁ : ∀ᶠ j in atTop, ∀ x ∈ closedUnitBall n, ‖fderiv ℝ (F j) x‖ ≤ B + 1 := by
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp h₁ 1 zero_lt_one] with j hj x hx
    have h := hj x hx
    rw [dist_comm, dist_eq_norm] at h
    calc
      ‖fderiv ℝ (F j) x‖ ≤ ‖fderiv ℝ (F j) x - L x‖ + ‖L x‖ := norm_le_norm_sub_add _ _
      _ ≤ B + 1 := by linarith [hB x hx]
  have hDP (j : ℕ) : Continuous (D j) := by
    have h := ((hF j).fderiv_right (m := ∞) (by simp)).continuous.clm_apply continuous_id
    exact ((continuous_const.mul ((hF j).continuous.pow 2)).add
      ((continuous_const.mul (hF j).continuous).mul h))
  have hDlim : ∀ᵐ x ∂ν[n], Tendsto (fun j => D j x) atTop (𝓝 (d x)) := by
    filter_upwards [ae_restrict_mem (μ := volume0 n)
      (show MeasurableSet (unitBall n) from measurableSet_ball)] with x hx
    have ha := h₀.tendsto_at (ball_subset_closedBall hx)
    have hb := ((ContinuousLinearMap.apply ℝ ℝ x).continuous.continuousAt.tendsto).comp
      (h₁.tendsto_at (ball_subset_closedBall hx))
    exact ((ha.pow 2).const_mul _).add ((ha.const_mul 2).mul hb)
  have hNonC : 0 ≤ C + 1 := by
    have := hC 0 (by simp)
    linarith [norm_nonneg (g 0)]
  have hNonB : 0 ≤ B + 1 := by
    have := hB 0 (by simp)
    linarith [norm_nonneg (L 0)]
  have hDL : Tendsto J atTop (𝓝 (∫ x, d x ∂ν[n])) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun _ => (2 * n : ℝ) * (C + 1) ^ 2 + 2 * (C + 1) * (B + 1))
      (Eventually.of_forall fun j => (hDP j).aestronglyMeasurable) ?_ (integrable_const _) hDlim
    filter_upwards [hBound₀, hBound₁] with j hj₀ hj₁
    filter_upwards [ae_restrict_mem (μ := volume0 n)
      (show MeasurableSet (unitBall n) from measurableSet_ball)] with x hx
    have hx' := ball_subset_closedBall hx
    have hOp : ‖fderiv ℝ (F j) x x‖ ≤ B + 1 :=
      ((fderiv ℝ (F j) x).le_opNorm x).trans
        ((mul_le_of_le_one_right (norm_nonneg _) (mem_ball_zero_iff.mp hx).le).trans (hj₁ x hx'))
    refine (norm_add_le _ _).trans ?_
    simp only [q, norm_mul, norm_pow, Real.norm_of_nonneg (show (0 : ℝ) ≤ 2 * n by positivity),
      Real.norm_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]
    gcongr
    · exact hj₀ x hx'
    · exact hj₀ x hx'
  have hQL : Tendsto (fun j => ∫ θ : Sphere n, q j θ.1 ∂sphere0 n)
      atTop (𝓝 (∫ θ : Sphere n, (g θ.1) ^ 2 ∂sphere0 n)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => (C + 1) ^ 2)
      (Eventually.of_forall fun j => ((hF j).continuous.pow 2).comp
        continuous_subtype_val |>.aestronglyMeasurable) ?_ (integrable_const _) ?_
    · filter_upwards [hBound₀] with j hj
      exact Eventually.of_forall fun θ => by
        change ‖(F j θ.1) ^ 2‖ ≤ _
        rw [norm_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) (hj _ (sphere_subset_closedBall θ.2)) _
    · exact Eventually.of_forall fun θ =>
        (h₀.tendsto_at (sphere_subset_closedBall θ.2)).pow 2
  let U := (w : DirichletBallL2Pair n).fst
  let W := (w : DirichletBallL2Pair n).snd
  let H (j : ℕ) (x : E n) := U x *
    ((2 * n : ℝ) * F j x + fderiv ℝ (F j) x x)
  let K (j : ℕ) (x : E n) := inner ℝ (W x) (F j x • x)
  let H₀ (x : E n) := U x * ((2 * n : ℝ) * g x + L x x)
  let K₀ (x : E n) := inner ℝ (W x) (g x • x)
  have hId (j : ℕ) : (∫ x, H j x ∂ν[n]) + (∫ x, K j x ∂ν[n]) = 0 := by
    have h := dirichletSobolev_integral_divergence hn w
      (show ContDiff ℝ ∞ (fun x => F j x • x) from (hF j).smul contDiff_id)
    simp_rw [euclideanDivergence_scalar_euler ((hF j).differentiable (by simp) _)] at h
    exact h
  have hU : Integrable (U : E n → ℝ) ν[n] := (Lp.memLp U).integrable (by norm_num)
  have hW : Integrable (W : E n → E n) ν[n] := (Lp.memLp W).integrable (by norm_num)
  have hL₀ : Tendsto (fun j => ∫ x, H j x ∂ν[n]) atTop (𝓝 (∫ x, H₀ x ∂ν[n])) := by
    let b : ℝ := (2 * n : ℝ) * (C + 1) + (B + 1)
    have hCj (j : ℕ) : Continuous (fun x => (2 * n : ℝ) * F j x + fderiv ℝ (F j) x x) :=
      (continuous_const.mul (hF j).continuous).add
        (((hF j).fderiv_right (m := ∞) (by simp)).continuous.clm_apply continuous_id)
    refine tendsto_integral_filter_of_dominated_convergence (fun x => b * ‖U x‖)
      (Eventually.of_forall fun j => hU.aestronglyMeasurable.mul (hCj j).aestronglyMeasurable)
      ?_ (hU.norm.const_mul b) ?_
    · filter_upwards [hBound₀, hBound₁] with j hj₀ hj₁
      filter_upwards [ae_restrict_mem (μ := volume0 n)
        (show MeasurableSet (unitBall n) from measurableSet_ball)] with x hx
      have hx' := ball_subset_closedBall hx
      have hOp : ‖fderiv ℝ (F j) x x‖ ≤ B + 1 :=
        ((fderiv ℝ (F j) x).le_opNorm x).trans
          ((mul_le_of_le_one_right (norm_nonneg _) (mem_ball_zero_iff.mp hx).le).trans (hj₁ x hx'))
      change ‖H j x‖ ≤ _
      simp only [H, norm_mul]
      rw [mul_comm b]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      apply (norm_add_le _ _).trans
      rw [norm_mul, Real.norm_of_nonneg (show (0 : ℝ) ≤ 2 * n by positivity)]
      exact add_le_add (mul_le_mul_of_nonneg_left (hj₀ x hx') (by positivity)) hOp
    · filter_upwards [ae_restrict_mem (μ := volume0 n)
        (show MeasurableSet (unitBall n) from measurableSet_ball)] with x hx
      have ha := h₀.tendsto_at (ball_subset_closedBall hx)
      have hb := ((ContinuousLinearMap.apply ℝ ℝ x).continuous.continuousAt.tendsto).comp
        (h₁.tendsto_at (ball_subset_closedBall hx))
      exact ((ha.const_mul _).add hb).const_mul (U x)
  have hL₁ : Tendsto (fun j => ∫ x, K j x ∂ν[n]) atTop (𝓝 (∫ x, K₀ x ∂ν[n])) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun x => (C + 1) * ‖W x‖)
      (Eventually.of_forall fun j => hW.aestronglyMeasurable.inner
        ((hF j).continuous.smul continuous_id).aestronglyMeasurable)
      ?_ (hW.norm.const_mul (C + 1)) ?_
    · filter_upwards [hBound₀] with j hj
      filter_upwards [ae_restrict_mem (μ := volume0 n)
        (show MeasurableSet (unitBall n) from measurableSet_ball)] with x hx
      change ‖inner ℝ (W x) (F j x • x)‖ ≤ _
      rw [mul_comm (C + 1)]
      apply (norm_inner_le_norm _ _).trans
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left
        ((mul_le_of_le_one_right (norm_nonneg _) (mem_ball_zero_iff.mp hx).le).trans
          (hj x (ball_subset_closedBall hx))) (norm_nonneg _)
    · filter_upwards [ae_restrict_mem (μ := volume0 n)
        (show MeasurableSet (unitBall n) from measurableSet_ball)] with x hx
      have ha := h₀.tendsto_at (ball_subset_closedBall hx)
      exact tendsto_const_nhds.inner (ha.smul_const x)
  have hZero : (∫ x, H₀ x ∂ν[n]) + (∫ x, K₀ x ∂ν[n]) = 0 :=
    tendsto_nhds_unique (hL₀.add hL₁) (by simpa only [hId] using
      (tendsto_const_nhds (x := (0 : ℝ)) (f := atTop)))
  have hHI : Integrable H₀ ν[n] := by
    have hc : ContinuousOn (fun x => (2 * n : ℝ) * g x + L x x) (closedUnitBall n) :=
      (continuousOn_const.mul hg.continuousOn).add (hCL.clm_apply continuousOn_id)
    exact ((memLp_dirichlet_mul_of_continuousOn hc (Lp.memLp U)).integrable
      (by norm_num)).congr (Eventually.of_forall fun x => mul_comm _ _)
  have hKI : Integrable K₀ ν[n] := by
    have hc : ContinuousOn (fun x => g x • x) (closedUnitBall n) :=
      hg.continuousOn.smul continuousOn_id
    obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : E n) 1).exists_bound_of_continuousOn hc
    apply (hW.norm.const_mul M).mono'
      (hW.aestronglyMeasurable.inner ((hc.mono ball_subset_closedBall).aestronglyMeasurable measurableSet_ball))
    filter_upwards [ae_restrict_mem (μ := volume0 n)
      (show MeasurableSet (unitBall n) from measurableSet_ball)] with x hx
    rw [mul_comm M]
    exact (norm_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_left (hM x (ball_subset_closedBall hx)) (norm_nonneg _))
  have hEq : (∫ x, d x ∂ν[n]) = (∫ x, H₀ x ∂ν[n]) + ∫ x, K₀ x ∂ν[n] := by
    rw [← integral_add hHI hKI]
    apply integral_congr_ae
    filter_upwards [he, dirichletSobolev_gradient_ae_eq_of_contDiffOn hn w
      (hg.mono ball_subset_closedBall) he, ae_restrict_mem (μ := volume0 n)
      (show MeasurableSet (unitBall n) from measurableSet_ball)] with x hV hGrad hx
    change g x = U x at hV
    change ∇ g x = W x at hGrad
    dsimp only [d, H₀, K₀]
    rw [← hV, ← hGrad, hL hx, real_inner_smul_right, inner_gradient_left]
    ring
  have hJL : Tendsto J atTop
      (𝓝 ((2 * n : ℝ) * ∫ θ : Sphere n, (g θ.1) ^ 2 ∂sphere0 n)) :=
    (hQL.const_mul (2 * n : ℝ)).congr (fun j => (hJ j).symm)
  have hFlux := tendsto_nhds_unique hDL hJL
  rw [hEq, hZero] at hFlux
  exact (mul_eq_zero.mp hFlux.symm).resolve_left (by positivity)

/-- For an element of the zero-trace weak Dirichlet space, its smooth
representative on the closed ball vanishes pointwise on the sphere. -/
theorem DirichletSobolev.exists_contDiffOn_closedUnitBall_zero_boundary {n : ℕ} (hn : 0 < n)
    (w : DirichletSobolev n)
    (hw : ∀ k, HasDirichletWeakDerivativesL2 ((w : DirichletBallL2Pair n).fst : E n → ℝ) k) :
    ∃ g : E n → ℝ, ContDiffOn ℝ ∞ g (closedUnitBall n) ∧
      g =ᵐ[ν[n]] ((w : DirichletBallL2Pair n).fst : E n → ℝ) ∧
      ∀ x ∈ unitSphere n, g x = 0 := by
  obtain ⟨g, P, hTaylor, he, hP⟩ :=
    HasDirichletWeakDerivativesL2.exists_closedUnitBall_smoothJet hn hw
  let f := ((w : DirichletBallL2Pair n).fst : E n → ℝ)
  let F := dirichletSmoothApproximation f
  let C₀ := continuousMultilinearCurryFin0 ℝ (E n) ℝ
  let C₁ := continuousMultilinearCurryFin1 ℝ (E n) ℝ
  let L (x : E n) := C₁ (P x 1)
  have h₀ : TendstoUniformlyOn F g atTop (closedUnitBall n) := by
    have h := C₀.isometry.uniformContinuous.comp_tendstoUniformlyOn (hP 0)
    have hEval (j : ℕ) (x : E n) : C₀ (iteratedFDeriv ℝ 0 (F j) x) = F j x := by
      have h := congrFun (iteratedFDeriv_zero_eq_comp (𝕜 := ℝ) (f := F j)) x
      rw [h]
      exact C₀.apply_symm_apply _
    exact (h.congr (Eventually.of_forall fun j x _ => hEval j x)).congr_right
      (fun x hx => hTaylor.zero_eq x hx)
  have h₁ : TendstoUniformlyOn (fun j => fderiv ℝ (F j)) L atTop (closedUnitBall n) := by
    have h := C₁.isometry.uniformContinuous.comp_tendstoUniformlyOn (hP 1)
    have hEval (j : ℕ) (x : E n) : C₁ (iteratedFDeriv ℝ 1 (F j) x) = fderiv ℝ (F j) x := by
      ext v
      rw [continuousMultilinearCurryFin1_apply, iteratedFDeriv_one_apply]
      rfl
    exact h.congr (Eventually.of_forall fun j x _ => hEval j x)
  have hL : EqOn L (fderiv ℝ g) (unitBall n) := by
    intro x hx
    exact (hTaylor.hasFDerivAt (by simp)
      (mem_of_superset (isOpen_ball.mem_nhds hx) ball_subset_closedBall)).fderiv.symm
  have hFlux := eulerFlux_limit_square_zero hn w hTaylor.contDiffOn he F
    (contDiff_dirichletSmoothApproximation (hw 0).1) L h₀ h₁ hL
  have hCont : Continuous (fun θ : Sphere n => (g θ.1) ^ 2) :=
    (hTaylor.contDiffOn.continuousOn.comp_continuous continuous_subtype_val
      (fun θ => sphere_subset_closedBall θ.2)).pow 2
  have hz := sphere_eq_zero_of_integral_eq_zero n hn (fun θ : Sphere n => (g θ.1) ^ 2)
    hCont (fun _ => sq_nonneg _) hFlux
  refine ⟨g, hTaylor.contDiffOn, he, fun x hx => ?_⟩
  have h := congrFun hz (⟨x, hx⟩ : Sphere n)
  exact sq_eq_zero_iff.mp (by simpa only [Pi.zero_apply] using h)

/-- Smooth forcing for the cofactor equation has a representative smooth
on the closed ball with zero boundary values that solves the determinant linearization pointwise
in the open ball. -/
theorem exists_contDiffOn_closedUnitBall_cofactor_solution {n : ℕ} (hn : 0 < n)
    {u : E n → ℝ} (hu : SmoothNear (closedUnitBall n) u)
    (huP : ∀ x ∈ unitBall n, (complexHessian u x).PosDef)
    {a l : ℝ} (ha : 0 < a) (hl : 0 < l)
    (hDensity : ∀ x ∈ unitBall n, a ≤ (complexHessian u x).det.re)
    (hElliptic : ∀ x ∈ unitBall n, ∀ v : E n,
      l * ‖v‖ ^ 2 ≤ complexLaplacian u (fun y => (inner ℝ v y) ^ 2 / 2) x)
    (g : DirichletBallL2 n ℝ) {G : E n → ℝ} (hG : SmoothNear (closedUnitBall n) G)
    (hRep : g =ᵐ[ν[n]] G) :
    ∃ (w : DirichletSobolev n) (v : E n → ℝ),
      IsDirichletWeakSolution (dirichletCofactorOperator u) g w ∧
      ContDiffOn ℝ ∞ v (closedUnitBall n) ∧
      v =ᵐ[ν[n]] ((w : DirichletBallL2Pair n).fst : E n → ℝ) ∧
      (∀ x ∈ unitSphere n, v x = 0) ∧
      EqOn (MoserTrudinger.cofactorContraction u v) (fun x => -G x) (unitBall n) := by
  obtain ⟨w, hw, hW⟩ := exists_weakCofactorDirichletSolution_with_allWeakDerivatives hn
    hu huP ha hl hDensity hElliptic g hG hRep
  obtain ⟨v, hv, hV, hBoundary⟩ := w.exists_contDiffOn_closedUnitBall_zero_boundary hn hW
  have hu' : ContDiffOn ℝ ∞ u (unitBall n) := by
    obtain ⟨U, _, hU, hC⟩ := hu
    exact hC.mono (ball_subset_closedBall.trans hU)
  have hG' : ContinuousOn G (unitBall n) := by
    obtain ⟨U, _, hU, hC⟩ := hG
    exact hC.continuousOn.mono (ball_subset_closedBall.trans hU)
  have hv' := hv.mono ball_subset_closedBall
  have hEq := hw.euclideanDivergence_gradient_eq_of_contDiffOn hn
    (dirichletCofactorOperator_contDiffOn isOpen_ball hu') hv' hV hG' hRep
  refine ⟨w, v, hw, hv, hV, hBoundary, fun x hx => ?_⟩
  rw [← dirichletCofactorOperator_divergence_gradient hu' hv' hx
    (isUnit_iff_ne_zero.mpr (fun h => (posDef_det_re_pos (huP x hx)).ne' (by simp [h])))]
  exact hEq hx

end KEBall
