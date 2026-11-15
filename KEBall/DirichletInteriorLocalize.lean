import KEBall.DirichletWholeEquation
import KEBall.DirichletWholeCutoff
import KEBall.DirichletGradientField
import KEBall.DirichletTangentWeak

/-! Interior localization of a weak Dirichlet solution to a whole-space equation. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter InnerProductSpace MeasureTheory Metric Set TopologicalSpace
open scoped ContDiff Distributions Gradient Topology

namespace KEBall

local notation "ν[" n "]" => Measure.restrict (volume0 n) (unitBall n)

private theorem cutoff_gradient_eq_zero_of_notMem_tsupport {n : ℕ}
    (χ : 𝓓(dirichletBallOpens n, ℝ)) {x : E n} (hx : x ∉ tsupport (χ : E n → ℝ)) :
    ∇ (χ : E n → ℝ) x = 0 := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_gradient_left, inner_zero_left, fderiv_of_notMem_tsupport ℝ hx, zero_apply]

/-- The scalar forcing produced by cutting off a Dirichlet solution. -/
noncomputable def dirichletCutoffForcing {n : ℕ}
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n))
    (A : E n → E n →L[ℝ] E n) (χ : 𝓓(dirichletBallOpens n, ℝ))
    (g : DirichletBallL2 n ℝ) (u : DirichletSobolev n) (x : E n) : ℝ :=
  let X (y : E n) := A y (∇ (χ : E n → ℝ) y)
  χ x * g x - 2 * inner ℝ (X x) ((u : DirichletBallL2Pair n).snd x) -
    dirichletVectorDivergence b X x * (u : DirichletBallL2Pair n).fst x

theorem dirichletCutoffForcing_eq_zero_of_notMem_tsupport {n : ℕ}
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n))
    (A : E n → E n →L[ℝ] E n) (χ : 𝓓(dirichletBallOpens n, ℝ))
    (g : DirichletBallL2 n ℝ) (u : DirichletSobolev n) {x : E n}
    (hx : x ∉ tsupport (χ : E n → ℝ)) : dirichletCutoffForcing b A χ g u x = 0 := by
  let X (y : E n) := A y (∇ (χ : E n → ℝ) y)
  have hX : ∀ y ∉ tsupport (χ : E n → ℝ), X y = 0 := fun y hy => by
    simp [X, cutoff_gradient_eq_zero_of_notMem_tsupport χ hy]
  have hD (i : Fin (2 * n)) :
      fderiv ℝ (fun y => inner ℝ (b i) (X y)) x = 0 := by
    have he : (fun y => inner ℝ (b i) (X y)) =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
      filter_upwards [isClosed_tsupport (χ : E n → ℝ) |>.isOpen_compl.mem_nhds hx] with y hy
      simp [hX y hy]
    rw [he.fderiv_eq, fderiv_fun_const, Pi.zero_apply]
  change χ x * g x - 2 * inner ℝ (X x) ((u : DirichletBallL2Pair n).snd x) -
    dirichletVectorDivergence b X x * (u : DirichletBallL2Pair n).fst x = 0
  simp [image_eq_zero_of_notMem_tsupport hx, hX x hx, dirichletVectorDivergence, hD]

set_option maxHeartbeats 1000000 in
/-- Cutting off a weak Dirichlet solution inside the ball gives a whole-space
weak solution with the localized L² forcing. The whole-space coefficients
agree with the original coefficients on the support of the cutoff. -/
theorem IsDirichletWeakSolution.exists_wholeCutoff_with_forcing {n : ℕ} (hn : 0 < n)
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n))
    {A B : E n → E n →L[ℝ] E n} (hA : ContDiff ℝ ∞ A)
    (hSym : ∀ x ∈ unitBall n, (A x).adjoint = A x) (hB : MemLp B ⊤ (volume0 n))
    (χ : 𝓓(dirichletBallOpens n, ℝ)) (hAgree : ∀ x ∈ tsupport (χ : E n → ℝ), B x = A x)
    {g : DirichletBallL2 n ℝ} {u : DirichletSobolev n} (hu : IsDirichletWeakSolution A g u) :
    ∃ f' : DirichletBallL2 n ℝ, f' =ᵐ[ν[n]] dirichletCutoffForcing b A χ g u ∧
      IsEuclideanWeakSolution hB (dirichletL2ZeroExtension f')
        (euclideanSobolevCutoff χ (dirichletSobolevZeroExtension n u)) := by
  have : NeZero n := ⟨hn.ne'⟩
  have : IsProbabilityMeasure ν[n] := volume0_restrict_isProbability n
  let f := (u : DirichletBallL2Pair n).fst
  let G := (u : DirichletBallL2Pair n).snd
  let X (x : E n) := A x (∇ (χ : E n → ℝ) x)
  have hX : ContDiff ℝ ∞ X := hA.clm_apply (contDiff_euclideanGradient χ.contDiff)
  have hXSupp : tsupport X ⊆ unitBall n := by
    apply (closure_minimal _ (isClosed_tsupport (χ : E n → ℝ))).trans χ.tsupport_subset
    intro x hx
    by_contra h
    exact hx (by simp [X, cutoff_gradient_eq_zero_of_notMem_tsupport χ h])
  let divX := dirichletVectorDivergence b X
  have hDivX : ContDiff ℝ ∞ divX := contDiff_dirichletVectorDivergence b hX
  have hEval {V : E n → E n →L[ℝ] ℝ} (hV : Continuous V) :
      MemLp (fun x => V x (G x)) 2 ν[n] := by
    obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : E n) 1).exists_bound_of_continuousOn hV.continuousOn
    have hPair : Continuous (fun p : (E n →L[ℝ] ℝ) × E n => p.1 p.2) :=
      continuous_fst.clm_apply continuous_snd
    have hMeas : AEStronglyMeasurable (fun x => V x (G x)) ν[n] :=
      hPair.comp_aestronglyMeasurable (hV.aestronglyMeasurable.prodMk (Lp.aestronglyMeasurable G))
    apply (Lp.memLp G).of_le_mul hMeas
    filter_upwards [ae_restrict_mem (μ := volume0 n)
      (show MeasurableSet (unitBall n) from measurableSet_ball)] with x hx
    exact ((V x).le_opNorm (G x)).trans
      (mul_le_mul_of_nonneg_right (hC x (ball_subset_closedBall hx)) (norm_nonneg _))
  have hXG : MemLp (fun x => inner ℝ (X x) (G x)) 2 ν[n] :=
    hEval ((innerSL ℝ).continuous.comp hX.continuous)
  have hχg : MemLp (fun x => χ x * g x) 2 ν[n] :=
    memLp_dirichlet_mul_of_continuousOn χ.continuous.continuousOn (Lp.memLp g)
  let f' (x : E n) := χ x * g x - 2 * inner ℝ (X x) (G x) - divX x * f x
  have hf' : MemLp f' 2 ν[n] :=
    (hχg.sub (hXG.const_smul (2 : ℝ))).sub
      (memLp_dirichlet_mul_of_continuousOn hDivX.continuous.continuousOn (Lp.memLp f))
  let g' := dirichletL2ZeroExtension (hf'.toLp f')
  let z := dirichletSobolevZeroExtension n u
  let w := euclideanSobolevCutoff χ z
  refine ⟨hf'.toLp f', MemLp.coeFn_toLp hf', IsEuclideanWeakSolution.of_test hB g' w fun ψ => ?_⟩
  let P (x : E n) := χ x * fderiv ℝ (ψ : E n → ℝ) x (A x (G x))
  let Q (x : E n) := f x * fderiv ℝ (ψ : E n → ℝ) x (X x)
  let R (x : E n) := ψ x * inner ℝ (X x) (G x)
  let D (x : E n) := ψ x * divX x * f x
  let M (x : E n) := ψ x * (χ x * g x)
  have hL : (∫ x, fderiv ℝ (ψ : E n → ℝ) x (B x ((w : EuclideanL2Pair n).snd x)) ∂volume0 n) =
      ∫ x, P x + Q x ∂ν[n] := by
    rw [← integral_indicator (show MeasurableSet (unitBall n) from measurableSet_ball)]
    apply integral_congr_ae
    filter_upwards [euclideanSobolevCutoff_gradient_ae χ z, dirichletSobolevZeroExtension_value_ae u,
      dirichletSobolevZeroExtension_gradient_ae u] with x hw hf hG
    change (z : EuclideanL2Pair n).fst x = (unitBall n).indicator (f : E n → ℝ) x at hf
    change (z : EuclideanL2Pair n).snd x = (unitBall n).indicator (G : E n → E n) x at hG
    rw [hw, hf, hG]
    by_cases hx : x ∈ unitBall n
    · rw [indicator_of_mem hx, indicator_of_mem hx, indicator_of_mem hx]
      have hBG : B x (χ x • G x + f x • ∇ (χ : E n → ℝ) x) =
          A x (χ x • G x + f x • ∇ (χ : E n → ℝ) x) := by
        by_cases hs : x ∈ tsupport (χ : E n → ℝ)
        · rw [hAgree x hs]
        · simp [image_eq_zero_of_notMem_tsupport hs, cutoff_gradient_eq_zero_of_notMem_tsupport χ hs]
      rw [hBG]
      simp [P, Q, X, map_add, map_smul]
    · simp [indicator_of_notMem hx]
  have hRhs : (∫ x, ψ x * g' x ∂volume0 n) = ∫ x, ψ x * f' x ∂ν[n] := by
    rw [← integral_indicator (show MeasurableSet (unitBall n) from measurableSet_ball)]
    apply integral_congr_ae
    filter_upwards [dirichletL2ZeroExtension_ae (hf'.toLp f'),
      (ae_restrict_iff' (μ := volume0 n) (show MeasurableSet (unitBall n) from measurableSet_ball)).mp
        (MemLp.coeFn_toLp hf')] with x hx hx'
    change g' x = (unitBall n).indicator (hf'.toLp f' : E n → ℝ) x at hx
    change ψ x * g' x = (unitBall n).indicator (fun x => ψ x * f' x) x
    rw [hx]
    by_cases hb : x ∈ unitBall n
    · rw [indicator_of_mem hb, indicator_of_mem hb, hx' hb]
    · rw [indicator_of_notMem hb, indicator_of_notMem hb, mul_zero]
  have hdψ : Continuous (fderiv ℝ (ψ : E n → ℝ)) :=
    (ψ.contDiff.fderiv_right (m := ∞) (by simp)).continuous
  have hP : Integrable P ν[n] := by
    have hPC : Continuous (fun x => χ x • (fderiv ℝ (ψ : E n → ℝ) x).comp (A x)) :=
      χ.continuous.smul (hdψ.clm_comp hA.continuous)
    exact (hEval hPC).integrable (by norm_num)
  have hR : Integrable R ν[n] :=
    (memLp_dirichlet_mul_of_continuousOn ψ.continuous.continuousOn hXG).integrable (by norm_num)
  have hQ : Integrable Q ν[n] := by
    have hQC : Continuous (fun x => fderiv ℝ (ψ : E n → ℝ) x (X x)) := hdψ.clm_apply hX.continuous
    simpa only [Q, mul_comm] using
      (memLp_dirichlet_mul_of_continuousOn hQC.continuousOn (Lp.memLp f)).integrable (by norm_num)
  have hD : Integrable D ν[n] :=
    (memLp_dirichlet_mul_of_continuousOn (ψ.continuous.mul hDivX.continuous).continuousOn
      (Lp.memLp f)).integrable (by norm_num)
  have hM : Integrable M ν[n] :=
    (memLp_dirichlet_mul_of_continuousOn ψ.continuous.continuousOn hχg).integrable (by norm_num)
  have hEq₁ : (∫ x, P x ∂ν[n]) + (∫ x, R x ∂ν[n]) = ∫ x, M x ∂ν[n] := by
    let τ := dirichletTestMul χ ψ.contDiff
    rw [← integral_add hP hR]
    calc
      _ = ∫ x, fderiv ℝ (τ : E n → ℝ) x (A x (G x)) ∂ν[n] := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem (μ := volume0 n)
          (show MeasurableSet (unitBall n) from measurableSet_ball)] with x hx
        change P x + R x = fderiv ℝ (fun y => χ y * ψ y) x (A x (G x))
        rw [fderiv_fun_mul (χ.contDiff.differentiable (by simp) x) (ψ.contDiff.differentiable (by simp) x)]
        have hAdj := (A x).adjoint_inner_left (G x) (∇ (χ : E n → ℝ) x)
        rw [hSym x hx, inner_gradient_left] at hAdj
        simp [P, R, X, ← hAdj]
      _ = ∫ x, τ x * g x ∂ν[n] := hu.integral_fderiv_test τ
      _ = _ := by simp [τ, M, mul_left_comm, mul_assoc]
  have hEq₂ : (∫ x, R x ∂ν[n]) = -((∫ x, Q x ∂ν[n]) + (∫ x, D x ∂ν[n])) := by
    rw [← integral_add hQ hD]
    refine (dirichletSobolev_integral_gradientField hn b u hX hXSupp ψ).trans ?_
    congr 1
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      change (fderiv ℝ (ψ : E n → ℝ) x (X x) + ψ x * divX x) * f x = Q x + D x
      simp [Q, D, add_mul, mul_comm (f x)]
  have hF' : (∫ x, ψ x * f' x ∂ν[n]) =
      (∫ x, M x ∂ν[n]) - 2 * (∫ x, R x ∂ν[n]) - ∫ x, D x ∂ν[n] := by
    have he : (fun x => ψ x * f' x) = fun x => M x - 2 * R x - D x := by
      funext x
      dsimp [f', M, R, D]
      ring
    have hR₂ : Integrable (fun x => 2 * R x) ν[n] := hR.const_mul 2
    have hMR : Integrable (fun x => M x - 2 * R x) ν[n] := hM.sub hR₂
    rw [he, integral_sub hMR hD, integral_sub hM hR₂, integral_const_mul]
  rw [hL, hRhs, integral_add hP hQ, hF']
  linarith only [hEq₁, hEq₂]

/-- Cutting off a weak Dirichlet solution inside the ball gives a whole-space
weak solution with the localized L² forcing. The whole-space coefficients
agree with the original coefficients on the support of the cutoff. -/
theorem IsDirichletWeakSolution.exists_wholeCutoff {n : ℕ} (hn : 0 < n)
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n))
    {A B : E n → E n →L[ℝ] E n} (hA : ContDiff ℝ ∞ A)
    (hSym : ∀ x ∈ unitBall n, (A x).adjoint = A x) (hB : MemLp B ⊤ (volume0 n))
    (χ : 𝓓(dirichletBallOpens n, ℝ)) (hAgree : ∀ x ∈ tsupport (χ : E n → ℝ), B x = A x)
    {g : DirichletBallL2 n ℝ} {u : DirichletSobolev n} (hu : IsDirichletWeakSolution A g u) :
    ∃ g' : EuclideanL2 n ℝ,
      IsEuclideanWeakSolution hB g' (euclideanSobolevCutoff χ (dirichletSobolevZeroExtension n u)) := by
  obtain ⟨f', _, hf'⟩ := hu.exists_wholeCutoff_with_forcing hn b hA hSym hB χ hAgree
  exact ⟨dirichletL2ZeroExtension f', hf'⟩

end KEBall
