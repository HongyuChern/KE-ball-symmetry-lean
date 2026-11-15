import KEBall.DirichletRealHessianPathLimit
import KEBall.DirichletWeakHessianLimit

/-! The weak third derivatives of the gradient limit along the Dirichlet path. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter InnerProductSpace MeasureTheory Metric Set
open scoped ComplexOrder ContDiff Distributions ENNReal NNReal Topology

namespace KEBall

local notation "ν[" n "]" => Measure.restrict (volume0 n) (unitBall n)
local notation "e[" n "]" => EuclideanSpace.basisFun (Fin (2 * n)) ℝ
local notation "𝓓B[" n "]" => 𝓓(dirichletBallOpens n, ℝ)

theorem ae_realHessian_eq_of_uniform_gradient {n : ℕ} (hn : 0 < n)
    {u : ℕ → E n → ℝ} (hu : ∀ m, SmoothNear (closedUnitBall n) (u m))
    {G : E n → E n →L[ℝ] ℝ} {L : ℝ≥0}
    (hGrad : TendstoUniformlyOn (fun m => fderiv ℝ (u m)) G atTop (closedUnitBall n))
    (hLip : LipschitzOnWith L G (closedUnitBall n)) (a b : E n)
    (H : DirichletBallL2 n ℝ) (Q : ℕ → DirichletBallL2 n ℝ) (hQ : Tendsto Q atTop (𝓝 H))
    (hRep : ∀ m, Q m =ᵐ[ν[n]] fun x => realHessian (u m) x a b) :
    (H : E n → ℝ) =ᵐ[ν[n]] fun x => fderiv ℝ G x a b := by
  have : NeZero n := ⟨hn.ne'⟩
  have hBall := ae_restrict_mem (μ := volume0 n) (show MeasurableSet (unitBall n) from measurableSet_ball)
  have hD : MemLp (fun x => fderiv ℝ G x a b) 2 ν[n] := by
    have hMeas : Measurable (fun x => fderiv ℝ G x a b) :=
      (ContinuousLinearMap.measurable_apply b).comp (measurable_fderiv_apply_const ℝ G a)
    refine MemLp.of_bound hMeas.aestronglyMeasurable ((L : ℝ) * ‖a‖ * ‖b‖) ?_
    filter_upwards [hBall] with x hx
    have hNorm : ‖fderiv ℝ G x‖ ≤ L :=
      norm_fderiv_le_of_lipschitzOn ℝ
        (mem_of_superset (isOpen_ball.mem_nhds hx) ball_subset_closedBall) hLip
    exact ((fderiv ℝ G x a).le_opNorm b).trans
      (mul_le_mul_of_nonneg_right (((fderiv ℝ G x).le_opNorm a).trans
        (mul_le_mul_of_nonneg_right hNorm (norm_nonneg _))) (norm_nonneg _))
  apply ae_eq_on_unitBall_of_tests
    (((Lp.memLp H).integrable (by norm_num)).locallyIntegrable.locallyIntegrableOn _)
    ((hD.integrable (by norm_num)).locallyIntegrable.locallyIntegrableOn _)
  intro ψ
  let P : DirichletBallL2 n ℝ →L[ℝ] ℝ := innerSL ℝ (dirichletTestToL2 ψ)
  have hP (w : DirichletBallL2 n ℝ) : P w = ∫ x, ψ x * w x ∂ν[n] := by
    change inner ℝ (dirichletTestToL2 ψ) w = _
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [dirichletTestToL2_ae ψ] with x hx
    rw [hx, Real.inner_apply]
  have hLeft : Tendsto (fun m => P (Q m)) atTop (𝓝 (P H)) :=
    P.continuous.continuousAt.tendsto.comp hQ
  have hCont (m : ℕ) : ContinuousOn (fderiv ℝ (u m)) (closedUnitBall n) := by
    obtain ⟨U, hU, hSub, huU⟩ := hu m
    exact (huU.fderiv_of_isOpen hU (m := ∞) (by simp)).continuousOn.mono hSub
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : E n) 1).exists_bound_of_continuousOn hLip.continuousOn
  have hB : ∀ᶠ m in atTop, ∀ x ∈ closedUnitBall n, ‖fderiv ℝ (u m) x‖ ≤ C + 1 := by
    filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hGrad) 1 zero_lt_one] with m hm x hx
    have he := hm x hx
    rw [dist_comm, dist_eq_norm] at he
    have h := norm_add_le (fderiv ℝ (u m) x - G x) (G x)
    rw [sub_add_cancel] at h
    linarith only [he, hC x hx, h]
  let V (x : E n) (D : E n →L[ℝ] ℝ) := fderiv ℝ (ψ : E n → ℝ) x a * D b
  have hV : Continuous (fun p : E n × (E n →L[ℝ] ℝ) => V p.1 p.2) := by
    have hψ : Continuous (fun x => fderiv ℝ (ψ : E n → ℝ) x a) :=
      ((ψ.contDiff.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).continuous
    exact (hψ.comp continuous_fst).mul ((ContinuousLinearMap.apply ℝ ℝ b).continuous.comp continuous_snd)
  have hRight := (tendsto_integral_pairing_of_uniform_gradient hV hCont hGrad hB).neg
  have he (m : ℕ) : -(∫ x, V x (fderiv ℝ (u m) x) ∂ν[n]) = P (Q m) := by
    rw [hP]
    have h := smooth_integral_test_realHessian hn (hu m) ψ a b
    rw [← h]
    apply integral_congr_ae
    filter_upwards [hRep m] with x hx
    rw [hx]
  have hEq := tendsto_nhds_unique hLeft (hRight.congr he)
  rw [hP] at hEq
  exact hEq.trans (integral_test_fderiv_lipschitz_gradient hLip ψ a b).symm

/-- A limit along the smooth Dirichlet path has a Lipschitz gradient and
square-integrable weak third derivatives of its actual almost-everywhere Hessian. -/
theorem exists_dirichlet_limit_with_weakThird_of_logDensityPath {n : ℕ} (hn : 0 < n)
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
      ∃ F : Fin (2 * n) → Fin (2 * n) → Fin (2 * n) → DirichletBallL2 n ℝ,
        ∀ (i j k : Fin (2 * n)) (ψ : 𝓓B[n]),
          (∫ x, ψ x * F i j k x ∂ν[n]) =
            -(∫ x, fderiv ℝ (ψ : E n → ℝ) x (e[n] i) *
              fderiv ℝ G x (e[n] j) (e[n] k) ∂ν[n]) := by
  obtain ⟨φ, w, G, L, hφ, _, hGrad, hD, hLip, hw0, hw, hμ, A, _, ⟨ψ, hψ, hAe⟩, _, hEqA⟩ :=
    exists_dirichlet_C1_and_complexHessian_L2_limit_of_logDensityPath hn hg ht hT hu hu0 huP hEq
  obtain ⟨H, ⟨Q, hH, hQ⟩, F, hF⟩ :=
    exists_realHessian_L2_limit_and_weakThird_of_logDensityPath hn hg (fun m => ht (φ m))
      (hT.comp hφ.tendsto_atTop) (fun m => hu (φ m)) (fun m => hu0 (φ m))
      (fun m => huP (φ m)) (fun m => hEq (φ m))
  refine ⟨w, G, L, hD, hLip, hw0, ?_, F, fun i j k η => ?_⟩
  · filter_upwards [hAe, hEqA] with x hx h
    change dirichletHessianMatrix (A x) = complexHessianOfRealBilinear (fderiv ℝ G x) at h
    rw [← h]
    exact hx.2
  · have h := ae_realHessian_eq_of_uniform_gradient hn (fun m => hu (φ m)) hGrad hLip
      (e[n] j) (e[n] k) (H j k) (fun m => Q m j k) (hH j k) (fun m => hQ m j k)
    rw [hF i j k η]
    congr 1
    apply integral_congr_ae
    filter_upwards [h] with x hx
    rw [hx]

end KEBall
