import KEBall.DirichletHessianCompactness
import KEBall.DirichletLipschitzHessian
import KEBall.MoserTrudingerDirichletDensityLimit

/-!
# Dirichlet limits along the log-density continuity path

The estimates for smooth solutions are uniform along (\exp(tg)).
The resulting closed-ball C¹ limit has Lipschitz gradient and solves
the limiting equation in the Bedford–Taylor sense.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Metric Set
open scoped ComplexOrder ContDiff Distributions ENNReal Matrix.Norms.Elementwise NNReal Topology

namespace KEBall

open Cegrell BedfordTaylor
open PshLines.FirstPass (ComplexModel)

/-- Uniform density bounds and bounds on the first two log-density derivatives. -/
theorem exists_logDensityPath_bounds {n : ℕ} (hn : 0 < n)
    {g : E n → ℝ} (hg : SmoothNear (closedUnitBall n) g) :
    ∃ a b K M : ℝ, 0 < a ∧ 0 < b ∧ 0 ≤ K ∧ 0 ≤ M ∧
      ∀ t ∈ Icc (0 : ℝ) 1,
        (∀ x ∈ closedUnitBall n, a ^ n ≤ Real.exp (t * g x) ∧ Real.exp (t * g x) ≤ b ^ n) ∧
        (∀ x ∈ closedUnitBall n, ‖fderiv ℝ (fun y => Real.log (Real.exp (t * g y))) x‖ ≤ K) ∧
        (∀ x ∈ closedUnitBall n, ∀ v : E n, ‖v‖ = 1 →
          -M ≤ realHessian (fun y => Real.log (Real.exp (t * g y))) x v v) := by
  obtain ⟨U, hU, hSub, hgU⟩ := hg
  have hgD : ContDiffOn ℝ ∞ (fderiv ℝ g) U := hgU.fderiv_of_isOpen hU (by simp)
  have hgH : ContDiffOn ℝ ∞ (realHessian g) U := hgD.fderiv_of_isOpen hU (by simp)
  have hComp := isCompact_closedBall (0 : E n) 1
  obtain ⟨R₀, hR₀⟩ := hComp.exists_bound_of_continuousOn (hgU.continuousOn.mono hSub)
  obtain ⟨K₀, hK₀⟩ := hComp.exists_bound_of_continuousOn (hgD.continuousOn.mono hSub)
  let S : Set (E n × E n) := closedUnitBall n ×ˢ closedUnitBall n
  have hHC : ContinuousOn (fun z : E n × E n => realHessian g z.1 z.2 z.2) S := by
    have hFst : MapsTo Prod.fst S U := fun _ hz => hSub hz.1
    exact (((hgH.continuousOn.comp continuousOn_fst hFst).clm_apply continuousOn_snd).clm_apply
      continuousOn_snd)
  obtain ⟨M₀, hM₀⟩ := (hComp.prod hComp).exists_bound_of_continuousOn hHC
  let R := max 0 R₀
  let K := max 0 K₀
  let M := max 0 M₀
  have hR : 0 ≤ R := le_max_left _ _
  have hK : 0 ≤ K := le_max_left _ _
  have hM : 0 ≤ M := le_max_left _ _
  refine ⟨Real.exp (-R), Real.exp R, K, M, Real.exp_pos _, Real.exp_pos _, hK, hM, ?_⟩
  intro t ht
  have hLog : (fun y => Real.log (Real.exp (t * g y))) = (t • g) := by
    funext y
    simp only [Real.log_exp, Pi.smul_apply, smul_eq_mul]
  have htAbs : |t| ≤ 1 := by rw [abs_of_nonneg ht.1]; exact ht.2
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    have h : ‖g x‖ ≤ R := (hR₀ x hx).trans (le_max_right 0 R₀)
    rw [Real.norm_eq_abs] at h
    have htg : |t * g x| ≤ R := by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_right htAbs (abs_nonneg _)).trans (by simpa using h)
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
    refine ⟨Real.exp_le_exp.mpr ?_, Real.exp_le_exp.mpr ?_⟩
    · exact (by simpa only [one_mul] using mul_le_mul_of_nonpos_right hnR (neg_nonpos.mpr hR) :
        (n : ℝ) * -R ≤ -R).trans (abs_le.mp htg).1
    · exact (abs_le.mp htg).2.trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hnR hR)
  · intro x hx
    have hgAt := hgU.contDiffAt (hU.mem_nhds (hSub hx))
    have hd : fderiv ℝ (t • g) x = t • fderiv ℝ g x :=
      (hgAt.differentiableAt (by simp)).hasFDerivAt.const_smul t |>.fderiv
    rw [hLog, hd, norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_right htAbs (norm_nonneg _)).trans
      (by simpa only [one_mul] using (hK₀ x hx).trans (le_max_right _ _))
  · intro x hx v hv
    have hgAt := hgU.contDiffAt (hU.mem_nhds (hSub hx))
    have he := PshLines.realHessian_smul (hgAt.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2) : ContDiffAt ℝ 2 g x) t v v
    simp only [PshLines.realHessian_eq_fderiv] at he
    change realHessian (t • g) x v v = t * realHessian g x v v at he
    have hvC : v ∈ closedUnitBall n := mem_closedBall_zero_iff.mpr hv.le
    have hVM : |realHessian g x v v| ≤ M := by
      have h := hM₀ (x, v) ⟨hx, hvC⟩
      rw [Real.norm_eq_abs] at h
      exact h.trans (le_max_right _ _)
    rw [hLog, he]
    apply (abs_le.mp ?_).1
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_right htAbs (abs_nonneg _)).trans (by simpa using hVM)

/-- A convergent parameter sequence has a Bedford–Taylor limit with
uniformly converging gradients and strongly converging complex Hessians. -/
theorem exists_dirichlet_C1_and_complexHessian_L2_limit_of_logDensityPath {n : ℕ} (hn : 0 < n)
    {g : E n → ℝ} (hg : SmoothNear (closedUnitBall n) g)
    {t : ℕ → ℝ} {t₀ : ℝ} (ht : ∀ j, t j ∈ Icc (0 : ℝ) 1) (hT : Tendsto t atTop (𝓝 t₀))
    {u : ℕ → E n → ℝ} (hu : ∀ j, SmoothNear (closedUnitBall n) (u j))
    (hu0 : ∀ j x, x ∈ unitSphere n → u j x = 0)
    (huP : ∀ j x, x ∈ unitBall n → (complexHessian (u j) x).PosDef)
    (hEq : ∀ j x, x ∈ unitBall n → (complexHessian (u j) x).det.re = Real.exp (t j * g x)) :
    ∃ (φ : ℕ → ℕ) (w : E n → ℝ) (G : E n → E n →L[ℝ] ℝ) (L : ℝ≥0),
      StrictMono φ ∧ TendstoUniformlyOn u w atTop (closedUnitBall n) ∧
      TendstoUniformlyOn (fun j => fderiv ℝ (u (φ j))) G atTop (closedUnitBall n) ∧
      (∀ x ∈ unitBall n, HasFDerivAt w (G x) x) ∧ LipschitzOnWith L G (closedUnitBall n) ∧
      (∀ x ∈ unitSphere n, w x = 0) ∧
      ∃ hw : IsE0 (complexUnitBall n) (w ∘ (complexCoordinates n).symm),
        topMeasure hw.locallyBoundedPsh = Measure.map (complexCoordinates n)
          (((volume0 n).restrict (unitBall n)).withDensity
            (fun x => ENNReal.ofReal (Real.exp (t₀ * g x)))) ∧
        ∃ H : DirichletBallL2 n (DirichletHessianCoordinates n),
          (∃ Q : ℕ → DirichletBallL2 n (DirichletHessianCoordinates n), Tendsto Q atTop (𝓝 H) ∧
            ∀ j, Q j =ᵐ[(volume0 n).restrict (unitBall n)] fun x =>
              dirichletHessianCoordinates (complexHessian (u (φ j)) x)) ∧
          (∃ ψ : ℕ → ℕ, StrictMono ψ ∧
            ∀ᵐ x ∂(volume0 n).restrict (unitBall n),
              Tendsto (fun j => dirichletHessianCoordinates (complexHessian (u (φ (ψ j))) x))
                atTop (𝓝 (H x)) ∧
                (dirichletHessianMatrix (H x)).PosDef ∧
                (dirichletHessianMatrix (H x)).det.re = Real.exp (t₀ * g x)) ∧
          (∀ (η : 𝓓(dirichletBallOpens n, ℝ)) (i j : Fin n),
            (∫ x in unitBall n, (η x : ℂ) * dirichletHessianMatrix (H x) i j ∂volume0 n) =
              -(∫ x in unitBall n, dirichletTestGradientHessianEntry i j η G x ∂volume0 n)) ∧
          (dirichletHessianMatrix ∘ H =ᵐ[(volume0 n).restrict (unitBall n)]
            complexHessianOfRealBilinear ∘ fderiv ℝ G) := by
  let f (j : ℕ) (x : E n) := Real.exp (t j * g x)
  let p (x : E n) := Real.exp (t₀ * g x)
  have hSmooth (c : ℝ) : SmoothNear (closedUnitBall n) (fun x => Real.exp (c * g x)) := by
    obtain ⟨U, hU, hSub, hgU⟩ := hg
    exact ⟨U, hU, hSub, (contDiffOn_const.mul hgU).exp⟩
  have hCont (c : ℝ) : ContinuousOn (fun x => Real.exp (c * g x)) (closedUnitBall n) :=
    fun x hx => ((hSmooth c).contDiffAt hx).continuousAt.continuousWithinAt
  obtain ⟨a, b, K, M, ha, hb, hK, hM, hBounds⟩ := exists_logDensityPath_bounds hn hg
  have hDensity (j : ℕ) (x : E n) (hx : x ∈ unitBall n) : a ^ n ≤ f j x ∧ f j x ≤ b ^ n :=
    (hBounds (t j) (ht j)).1 x (ball_subset_closedBall hx)
  have hGrad (j : ℕ) (x : E n) (hx : x ∈ unitBall n) :
      ‖fderiv ℝ (fun y => Real.log (f j y)) x‖ ≤ K :=
    (hBounds (t j) (ht j)).2.1 x (ball_subset_closedBall hx)
  have hHess (j : ℕ) (x : E n) (hx : x ∈ unitBall n) (v : E n) (hv : ‖v‖ = 1) :
      -M ≤ realHessian (fun y => Real.log (f j y)) x v v :=
    (hBounds (t j) (ht j)).2.2 x (ball_subset_closedBall hx) v hv
  let c := (3 * K + 1) / (n : ℝ)
  let C := 2 * b + 4 * b * c +
    (2 * b + 4 * (b ^ n / a ^ (n - 1) + (b * c) ^ 2 / (4 * a)))
  let D : ℝ≥0 := ⟨C + ((M + 1) / (n : ℝ)) * b, by dsimp [C, c]; positivity⟩
  let K' : ℝ≥0 := ⟨2 * b + ((K + 1) / (n : ℝ)) * b, by positivity⟩
  have hU (j : ℕ) (x : E n) (hx : x ∈ closedUnitBall n) : ‖u j x‖ ≤ b := by
    have h := (Cegrell.quadratic_and_boundarySlope_bounds hn (hu j)
      (fun y hy => (huP j y hy).posSemidef) (hu0 j) ha hb
      (fun y hy => hEq j y hy ▸ hDensity j y hy)).1 x hx
    have hx' : ‖x‖ ≤ 1 := mem_closedBall_zero_iff.mp hx
    have hs : ‖x‖ ^ 2 ≤ 1 := by
      simpa only [one_pow] using pow_le_pow_left₀ (norm_nonneg x) hx' 2
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · nlinarith only [h.1, mul_nonneg hb.le (sq_nonneg ‖x‖)]
    · linarith only [h.2, mul_nonpos_of_nonneg_of_nonpos ha.le (sub_nonpos.mpr hs), hb]
  have hK' (j : ℕ) (x : E n) (hx : x ∈ closedUnitBall n) : ‖fderiv ℝ (u j) x‖ ≤ K' :=
    norm_fderiv_le_of_dirichlet_det hn (hu j) (hSmooth (t j)) (hu0 j) (huP j) (hEq j)
      ha hb hK (hDensity j) (hGrad j) x hx
  have hD (j : ℕ) (x : E n) (hx : x ∈ closedUnitBall n) (v : E n) (hv : ‖v‖ = 1) :
      |realHessian (u j) x v v| ≤ D :=
    abs_realHessian_self_le_of_dirichlet_det hn (hu j) (hSmooth (t j)) (hu0 j) (huP j) (hEq j)
      ha hb hM (hDensity j)
      (fun y hy w hw => abs_realHessian_self_le_on_sphere_of_dirichlet_det hn (hu j) (hSmooth (t j))
        (hu0 j) (huP j) (hEq j) ha hb hK (hDensity j) (hGrad j) hy hw)
      (hHess j) x hx v hv
  obtain ⟨φ, w, G, hφ, hUw, hUG, hwD, hLip⟩ :=
    exists_subseq_dirichlet_C1_of_uniform_hessian hu hU hK' hD
  let μ := (volume0 n).restrict (unitBall n)
  have hp : AEMeasurable p μ := ((hCont t₀).mono ball_subset_closedBall).aemeasurable measurableSet_ball
  have hLim : ∀ᵐ x ∂μ, Tendsto (fun j => f j x) atTop (𝓝 (p x)) :=
    Eventually.of_forall fun x => (Real.continuous_exp.continuousAt.tendsto.comp (hT.mul_const (g x)))
  have hBound (j : ℕ) : ∀ᵐ x ∂μ, f j x ∈ Icc 0 (b ^ n) := by
    filter_upwards [ae_restrict_mem (μ := volume0 n) (show MeasurableSet (unitBall n) from measurableSet_ball)]
      with x hx
    exact ⟨(Real.exp_pos _).le, (hDensity j x hx).2⟩
  obtain ⟨v, hUv, _, hv0, hv, hBT⟩ :=
    MoserTrudinger.exists_dirichletLimit_of_ae_of_bounded_density hn hu
      (fun j => hCont (t j)) hp hu0 huP hEq hBound hLim
  have hSame : EqOn w v (closedUnitBall n) := by
    intro x hx
    exact tendsto_nhds_unique (hUw.tendsto_at hx) ((hUv.tendsto_at hx).comp hφ.tendsto_atTop)
  have hF : TendstoUniformlyOn (fun j => f (φ j)) p atTop (closedUnitBall n) := by
    obtain ⟨U, hU, hSub, hgU⟩ := hg
    have hCont : ContinuousOn (fun q : ℝ × E n => Real.exp (q.1 * g q.2))
        (Icc (0 : ℝ) 1 ×ˢ closedUnitBall n) :=
      Real.continuous_exp.comp_continuousOn (continuous_fst.continuousOn.mul
        ((hgU.continuousOn.mono hSub).comp continuous_snd.continuousOn fun _ h => h.2))
    have ht₀ : t₀ ∈ Icc (0 : ℝ) 1 := isClosed_Icc.mem_of_tendsto hT (Eventually.of_forall ht)
    have hU := ((isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).prod
      (isCompact_closedBall (0 : E n) 1)).uniformContinuousOn_of_continuous hCont
    rw [Metric.uniformContinuousOn_iff] at hU
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    obtain ⟨δ, hδ, hU⟩ := hU ε hε
    filter_upwards [Metric.tendsto_nhds.mp (hT.comp hφ.tendsto_atTop) δ hδ] with j hj x hx
    exact hU (t₀, x) ⟨ht₀, hx⟩ (t (φ j), x) ⟨ht (φ j), hx⟩ (by
      rw [Prod.dist_eq, dist_self, max_eq_left dist_nonneg, dist_comm]
      exact hj)
  have hDpos : 0 < (D : ℝ) := by
    dsimp [D]
    have hC : 0 ≤ C := by dsimp [C, c]; positivity
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    exact add_pos_of_nonneg_of_pos hC (mul_pos (div_pos (by linarith) hnR) hb)
  obtain ⟨H, hStrong, ψ, hψ, hAE⟩ := exists_complexHessian_L2_limit_of_dirichlet_data hn
    (fun j => hu (φ j)) (fun j => hSmooth (t (φ j))) (fun j => huP (φ j)) (fun j => hEq (φ j))
    hUG hF ha hDpos (fun j x hx => (hDensity (φ j) x hx).1) (fun j => hD (φ j))
  have hAEball := ae_restrict_mem (μ := volume0 n) (show MeasurableSet (unitBall n) from measurableSet_ball)
  have hAEpos := ae_posDef_and_det_eq_of_dirichletHessian_limit
    (A := fun j => complexHessian (u (φ (ψ j)))) (H := H) (p := p)
    (hAEball.mono fun x hx j => huP _ x hx) hAE
    (by
      filter_upwards [hAEball, hLim] with x hx hTx
      simp only [hEq _ x hx]
      exact (hTx.comp hφ.tendsto_atTop).comp hψ.tendsto_atTop)
    (Eventually.of_forall fun _ => Real.exp_pos _)
  have hUG' : TendstoUniformlyOn (fun j => fderiv ℝ (u (φ (ψ j)))) G atTop (closedUnitBall n) :=
    fun U hU => hψ.tendsto_atTop.eventually (hUG U hU)
  have hHBound (j : ℕ) (x : E n) (hx : x ∈ unitBall n) :
      ‖complexHessian (u (φ (ψ j))) x‖ ≤ (D : ℝ) :=
    norm_complexHessian_le_of_unit_bound ((hu (φ (ψ j))).contDiffAt (ball_subset_closedBall hx))
      D.coe_nonneg (hD (φ (ψ j)) x (ball_subset_closedBall hx))
  have hWeak := integral_test_dirichletHessianMatrix_eq_of_limits hn
    (fun j => hu (φ (ψ j))) hUG' hAE hHBound
  refine ⟨φ, v, G, D, hφ, hUv, hUG, ?_, hLip, hv0, hv, hBT, H, hStrong, ⟨ψ, hψ, hAE.and hAEpos⟩, hWeak,
    ae_dirichletHessianMatrix_eq_complexHessianOfRealBilinear hn hLip H hWeak⟩
  intro x hx
  apply (hwD x hx).congr_of_eventuallyEq
  filter_upwards [isOpen_ball.mem_nhds hx] with y hy
  exact (hSame (ball_subset_closedBall hy)).symm

/-- The original C¹ compactness conclusion follows from the stronger
compactness theorem for complex Hessians. -/
theorem exists_dirichlet_C1_bedfordTaylor_limit_of_logDensityPath {n : ℕ} (hn : 0 < n)
    {g : E n → ℝ} (hg : SmoothNear (closedUnitBall n) g)
    {t : ℕ → ℝ} {t₀ : ℝ} (ht : ∀ j, t j ∈ Icc (0 : ℝ) 1) (hT : Tendsto t atTop (𝓝 t₀))
    {u : ℕ → E n → ℝ} (hu : ∀ j, SmoothNear (closedUnitBall n) (u j))
    (hu0 : ∀ j x, x ∈ unitSphere n → u j x = 0)
    (huP : ∀ j x, x ∈ unitBall n → (complexHessian (u j) x).PosDef)
    (hEq : ∀ j x, x ∈ unitBall n → (complexHessian (u j) x).det.re = Real.exp (t j * g x)) :
    ∃ (φ : ℕ → ℕ) (w : E n → ℝ) (G : E n → E n →L[ℝ] ℝ) (L : ℝ≥0),
      StrictMono φ ∧ TendstoUniformlyOn u w atTop (closedUnitBall n) ∧
      TendstoUniformlyOn (fun j => fderiv ℝ (u (φ j))) G atTop (closedUnitBall n) ∧
      (∀ x ∈ unitBall n, HasFDerivAt w (G x) x) ∧ LipschitzOnWith L G (closedUnitBall n) ∧
      (∀ x ∈ unitSphere n, w x = 0) ∧
      ∃ hw : IsE0 (complexUnitBall n) (w ∘ (complexCoordinates n).symm),
        topMeasure hw.locallyBoundedPsh = Measure.map (complexCoordinates n)
          (((volume0 n).restrict (unitBall n)).withDensity
            (fun x => ENNReal.ofReal (Real.exp (t₀ * g x)))) := by
  obtain ⟨φ, w, G, L, hφ, hU, hG, hD, hLip, hw0, hw, hBT, _⟩ :=
    exists_dirichlet_C1_and_complexHessian_L2_limit_of_logDensityPath hn hg ht hT hu hu0 huP hEq
  exact ⟨φ, w, G, L, hφ, hU, hG, hD, hLip, hw0, hw, hBT⟩

end KEBall
