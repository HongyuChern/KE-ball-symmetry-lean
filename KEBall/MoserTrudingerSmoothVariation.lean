import KEBall.MoserTrudingerSmoothGreen
import KEBall.MoserTrudingerSmooth
import PshLines.LeviForm
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convex.Deriv

/-!
# First and second variations of the smooth energy on the ball
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Metric Set
open scoped BigOperators ComplexOrder ContDiff ENNReal Topology

namespace KEBall.MoserTrudinger

/-- Extend the signed energy by the determinant formula to all smooth
potentials. This permits ordinary derivatives along a real affine path. -/
noncomputable def signedSmoothEnergy {n : ℕ} (u : E n → ℝ) : ℝ :=
  (∫ x in unitBall n, u x * (complexHessian u x).det.re ∂volume0 n) / (n + 1 : ℝ)

theorem signedSmoothEnergy_eq {n : ℕ} {U : Set (E n)} (hU : IsOpen U)
    {u : E n → ℝ} (hu : ContDiffOn ℝ ∞ u U)
    (hsub : closedUnitBall n ⊆ U)
    (hpos : ∀ x ∈ unitBall n, (complexHessian u x).PosDef) :
    signedSmoothEnergy u = -(smoothEnergy u) / (n + 1 : ℝ) := by
  unfold signedSmoothEnergy smoothEnergy
  rw [d0TopMeasure_eq_density, restrict_withDensity (show MeasurableSet (unitBall n) from measurableSet_ball)]
  have hA : ContinuousOn (fun x => (complexHessian u x).det.re) U :=
    Complex.continuous_re.comp_continuousOn
      (matrixField_det_contDiffOn (complexHessian_contDiffOn hU hu)).continuousOn
  have hm : AEMeasurable (fun x => ENNReal.ofReal (complexHessian u x).det.re)
      ((volume0 n).restrict (unitBall n)) :=
    ((hA.mono (ball_subset_closedBall.trans hsub)).aemeasurable measurableSet_ball).ennreal_ofReal
  rw [integral_withDensity_eq_integral_toReal_smul₀ hm
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top), ← integral_neg]
  congr 1
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (μ := volume0 n)
    (show MeasurableSet (unitBall n) from measurableSet_ball)] with x hx
  simp only [ENNReal.toReal_ofReal (posDef_det_re_pos (hpos x hx)).le, smul_eq_mul, mul_neg, neg_neg]
  exact mul_comm _ _

private theorem complexHessian_affine {n : ℕ} {u h : E n → ℝ} {x : E n}
    (hu : ContDiffAt ℝ ∞ u x) (hh : ContDiffAt ℝ ∞ h x) (s : ℝ) :
    complexHessian (u + s • h) x = complexHessian u x + (s : ℂ) • complexHessian h x := by
  have ht : ContDiffAt ℝ ∞ (s • h) x := hh.const_smul s
  have h2 : (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω) := ENat.natCast_le_of_coe_top_le_withTop le_rfl 2
  have hR (a b : E n) : realHessian (u + s • h) x a b =
      realHessian u x a b + s * realHessian h x a b := by
    simp only [← PshLines.realHessian_eq_fderiv, KEBall.realHessian]
    rw [PshLines.realHessian_add (hu.of_le h2) (ht.of_le h2),
      PshLines.realHessian_smul (hh.of_le h2)]
  ext i j
  have hp : ContDiffAt ℝ ∞ (u + s • h) x := hu.add ht
  rw [complexHessian_real_entry hp i j]
  simp only [complexHessian_real_entry hu, complexHessian_real_entry hh,
    Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, hR]
  push_cast
  ring

private theorem hasDerivAt_det_affine {n : ℕ} {u h : E n → ℝ} {x : E n}
    (hu : ContDiffAt ℝ ∞ u x) (hh : ContDiffAt ℝ ∞ h x) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (complexHessian (u + s • h) x).det.re)
      (cofactorContraction (u + t • h) h x) t := by
  let A (s : ℝ) := complexHessian u x + (s : ℂ) • complexHessian h x
  have hA (i j : Fin n) :
      HasDerivAt (fun s => A s i j) (complexHessian h x i j) t := by
    change HasDerivAt (fun s : ℝ => complexHessian u x i j + (s : ℂ) * complexHessian h x i j) _ t
    simpa using (Complex.ofRealCLM.hasFDerivAt.hasDerivAt.mul_const
      (complexHessian h x i j)).const_add (complexHessian u x i j)
  have hdiff := (field_det_differentiableAt fun i j => (hA i j).differentiableAt).hasDerivAt
  have heq : deriv (fun s => (A s).det) t =
      ∑ i : Fin n, ∑ j : Fin n, (A t).adjugate j i * complexHessian h x i j := by
    rw [← fderiv_apply_one_eq_deriv]
    change KEBallProbe.rd (1 : ℝ) (fun s => (A s).det) t = _
    rw [rd_det_field (fun i j => (hA i j).differentiableAt)]
    simp only [KEBallProbe.rd, fderiv_apply_one_eq_deriv, fun i j => (hA i j).deriv]
  rw [heq] at hdiff
  have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hdiff
  simpa only [Function.comp_def, complexHessian_affine hu hh, cofactorContraction,
    Complex.reCLM_apply, A] using h

theorem hasDerivAt_unitBall_integral {n : ℕ} (hn : 0 < n) {U : Set (E n)}
    (hsub : closedUnitBall n ⊆ U)
    {F F' : ℝ → E n → ℝ}
    (hF : ContinuousOn (Function.uncurry F) (univ ×ˢ U))
    (hF' : ContinuousOn (Function.uncurry F') (univ ×ˢ U))
    (hd : ∀ t x, x ∈ U → HasDerivAt (fun s => F s x) (F' t x) t) (t : ℝ) :
    HasDerivAt (fun s => ∫ x in unitBall n, F s x ∂volume0 n)
      (∫ x in unitBall n, F' t x ∂volume0 n) t := by
  let μ := (volume0 n).restrict (unitBall n)
  have hfin : (volume0 n) (unitBall n) ≠ ⊤ := by rw [volume0_unitBall n hn]; exact ENNReal.one_ne_top
  obtain ⟨C, hC⟩ := ((isCompact_closedBall t 1).prod (isCompact_closedBall (0 : E n) 1))
    |>.exists_bound_of_continuousOn (f := Function.uncurry F') (hF'.mono
      (Set.prod_mono (subset_univ _) hsub))
  have hsection (G : ℝ → E n → ℝ)
      (hG : ContinuousOn (Function.uncurry G) (univ ×ˢ U)) (s : ℝ) :
      Integrable (G s) μ := by
    have hc : ContinuousOn (G s) (closedUnitBall n) :=
      hG.comp (continuous_const.prodMk continuous_id).continuousOn fun x hx => ⟨mem_univ _, hsub hx⟩
    exact hc.integrableOn_of_subset_isCompact (isCompact_closedBall _ _)
      measurableSet_ball ball_subset_closedBall hfin
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (ball_mem_nhds t zero_lt_one)
    (Eventually.of_forall fun s => (hsection F hF s).aestronglyMeasurable)
    (hsection F hF t) ((hsection F' hF' t).aestronglyMeasurable)
    ((ae_restrict_mem (μ := volume0 n) (show MeasurableSet (unitBall n) from measurableSet_ball)).mono
      fun x hx s hs => hC (s, x) ⟨ball_subset_closedBall hs, ball_subset_closedBall hx⟩)
    (integrableOn_const hfin)
    ((ae_restrict_mem (μ := volume0 n) (show MeasurableSet (unitBall n) from measurableSet_ball)).mono
      fun x hx s _ => hd s x (hsub (ball_subset_closedBall hx)))).2

private theorem affineHessian_continuousOn {n : ℕ} {U : Set (E n)} (hU : IsOpen U)
    {u h : E n → ℝ} (hu : ContDiffOn ℝ ∞ u U) (hh : ContDiffOn ℝ ∞ h U) :
    ContinuousOn (fun p : ℝ × E n => complexHessian (u + p.1 • h) p.2) (univ ×ˢ U) := by
  apply continuousOn_pi.mpr
  intro i
  apply continuousOn_pi.mpr
  intro j
  have hu' : ContinuousOn (fun p : ℝ × E n => complexHessian u p.2 i j) (univ ×ˢ U) :=
    (complexHessian_contDiffOn hU hu i j).continuousOn.comp continuous_snd.continuousOn
      fun p hp => hp.2
  have hh' : ContinuousOn (fun p : ℝ × E n => complexHessian h p.2 i j) (univ ×ˢ U) :=
    (complexHessian_contDiffOn hU hh i j).continuousOn.comp continuous_snd.continuousOn
      fun p hp => hp.2
  refine (hu'.add ((Complex.continuous_ofReal.comp continuous_fst).continuousOn.mul hh')).congr ?_
  intro p hp
  dsimp only
  rw [complexHessian_affine (hu.contDiffAt (hU.mem_nhds hp.2))
    (hh.contDiffAt (hU.mem_nhds hp.2))]
  rfl

private theorem affineCofactor_continuousOn {n : ℕ} {U : Set (E n)} (hU : IsOpen U)
    {u h : E n → ℝ} (hu : ContDiffOn ℝ ∞ u U) (hh : ContDiffOn ℝ ∞ h U) :
    ContinuousOn (fun p : ℝ × E n => cofactorContraction (u + p.1 • h) h p.2)
      (univ ×ˢ U) := by
  have hA := affineHessian_continuousOn hU hu hh
  apply Complex.continuous_re.comp_continuousOn
  apply continuousOn_finsetSum
  intro i _
  apply continuousOn_finsetSum
  intro j _
  have hi : Continuous (fun A : Matrix (Fin n) (Fin n) ℂ => A.adjugate j i) := by
    simp_rw [Matrix.adjugate_apply]
    apply Continuous.matrix_det
    apply continuous_pi
    intro r
    apply continuous_pi
    intro k
    by_cases hr : r = i
    · subst r
      simp only [Matrix.updateRow_self]
      exact continuous_const
    · simp only [Matrix.updateRow_ne hr]
      exact (continuous_apply k).comp (continuous_apply r)
  exact (hi.comp_continuousOn hA).mul
    ((complexHessian_contDiffOn hU hh i j).continuousOn.comp continuous_snd.continuousOn
      fun p hp => hp.2)

private theorem rawEnergy_affine_deriv {n : ℕ} (hn : 0 < n) {U : Set (E n)}
    (hU : IsOpen U) (hsub : closedUnitBall n ⊆ U) {u h : E n → ℝ}
    (hu : ContDiffOn ℝ ∞ u U) (hh : ContDiffOn ℝ ∞ h U) (t : ℝ) :
    HasDerivAt (fun s =>
      ∫ x in unitBall n, (u + s • h) x * (complexHessian (u + s • h) x).det.re ∂volume0 n)
      (∫ x in unitBall n, h x * (complexHessian (u + t • h) x).det.re +
        (u + t • h) x * cofactorContraction (u + t • h) h x ∂volume0 n) t := by
  let A (s : ℝ) (x : E n) := (complexHessian (u + s • h) x).det.re
  let F (s : ℝ) (x : E n) := (u + s • h) x * A s x
  let F' (s : ℝ) (x : E n) := h x * A s x + (u + s • h) x * cofactorContraction (u + s • h) h x
  have hA : ContinuousOn (Function.uncurry A) (univ ×ˢ U) :=
    Complex.continuous_re.comp_continuousOn (continuous_id.matrix_det.comp_continuousOn
      (affineHessian_continuousOn hU hu hh))
  have hU' : ContinuousOn (fun p : ℝ × E n => u p.2) (univ ×ˢ U) :=
    hu.continuousOn.comp continuous_snd.continuousOn fun p hp => hp.2
  have hH' : ContinuousOn (fun p : ℝ × E n => h p.2) (univ ×ˢ U) :=
    hh.continuousOn.comp continuous_snd.continuousOn fun p hp => hp.2
  have hpath := hU'.add (continuous_fst.continuousOn.mul hH')
  have hF : ContinuousOn (Function.uncurry F) (univ ×ˢ U) := hpath.mul hA
  have hF' : ContinuousOn (Function.uncurry F') (univ ×ˢ U) :=
    (hH'.mul hA).add (hpath.mul (affineCofactor_continuousOn hU hu hh))
  have hd (s : ℝ) (x : E n) (hx : x ∈ U) :
      HasDerivAt (fun r => F r x) (F' s x) s := by
    have hlin : HasDerivAt (fun r : ℝ => (u + r • h) x) (h x) s := by
      simpa using ((hasDerivAt_id s).mul_const (h x)).const_add (u x)
    exact hlin.mul (hasDerivAt_det_affine (hu.contDiffAt (hU.mem_nhds hx))
      (hh.contDiffAt (hU.mem_nhds hx)) s)
  exact hasDerivAt_unitBall_integral hn hsub hF hF' hd t

set_option maxHeartbeats 700000 in
/-- The first variation of the signed smooth energy at an affine path point. -/
theorem hasDerivAt_signedSmoothEnergy {n : ℕ} (hn : 0 < n) {U : Set (E n)}
    (hU : IsOpen U) (hsub : closedUnitBall n ⊆ U) {u h : E n → ℝ}
    (hu : ContDiffOn ℝ ∞ u U) (hh : ContDiffOn ℝ ∞ h U)
    (hu0 : ∀ x ∈ unitSphere n, u x = 0) (hh0 : ∀ x ∈ unitSphere n, h x = 0)
    (t : ℝ) (hpos : ∀ x ∈ unitBall n, (complexHessian (u + t • h) x).PosDef) :
    HasDerivAt (fun s => signedSmoothEnergy (u + s • h))
      (∫ x in unitBall n, h x * (complexHessian (u + t • h) x).det.re ∂volume0 n) t := by
  let A (x : E n) := (complexHessian (u + t • h) x).det.re
  let v := u + t • h
  have hv : ContDiffOn ℝ ∞ v U := hu.add (hh.const_smul t)
  have hv0 (x : E n) (hx : x ∈ unitSphere n) : v x = 0 := by simp [v, hu0 x hx, hh0 x hx]
  have hswap := integral_mul_cofactorContraction_swap hn hU hsub hv hv hh hpos hv0 hh0
  have hI (g : E n → ℝ) (hg : ContinuousOn g U) : IntegrableOn g (unitBall n) (volume0 n) :=
    (hg.mono hsub).integrableOn_of_subset_isCompact (isCompact_closedBall _ _)
      measurableSet_ball ball_subset_closedBall (by rw [volume0_unitBall n hn]; exact ENNReal.one_ne_top)
  have h1 : IntegrableOn (fun x => h x * A x) (unitBall n) (volume0 n) :=
    hI _ (hh.continuousOn.mul (Complex.continuous_re.comp_continuousOn
      (matrixField_det_contDiffOn (complexHessian_contDiffOn hU hv)).continuousOn))
  have h2 := integrable_mul_contraction hn hU hsub hv hv hh
  have hEq :
      (∫ x in unitBall n, (h x * A x + v x * cofactorContraction v h x) ∂volume0 n) / (n + 1 : ℝ) =
        ∫ x in unitBall n, h x * A x ∂volume0 n := by
    rw [integral_add h1 h2, hswap]
    simp_rw [cofactorContraction_self, show ∀ x : E n, h x * ((n : ℝ) * (complexHessian v x).det.re) =
      (n : ℝ) * (h x * A x) from fun x => by dsimp [A, v]; ring]
    rw [integral_const_mul]
    field_simp
    ring
  rw [← hEq]
  exact (rawEnergy_affine_deriv hn hU hsub hu hh t).div_const _

/-- Integration by parts identifies the derivative of the determinant
energy with the integral of the variation against the top measure. -/
theorem integral_energyLinearization_eq {n : ℕ} (hn : 0 < n) {U : Set (E n)}
    (hU : IsOpen U) (hsub : closedUnitBall n ⊆ U) {u h : E n → ℝ}
    (hu : ContDiffOn ℝ ∞ u U) (hh : ContDiffOn ℝ ∞ h U)
    (hu0 : ∀ x ∈ unitSphere n, u x = 0) (hh0 : ∀ x ∈ unitSphere n, h x = 0)
    (hpos : ∀ x ∈ unitBall n, (complexHessian u x).PosDef) :
    (∫ x in unitBall n, h x * (complexHessian u x).det.re +
      u x * cofactorContraction u h x ∂volume0 n) / (n + 1 : ℝ) =
        ∫ x in unitBall n, h x * (complexHessian u x).det.re ∂volume0 n := by
  have h₀ : u + (0 : ℝ) • h = u := by simp
  have hRaw := (rawEnergy_affine_deriv hn hU hsub hu hh 0).div_const (n + 1 : ℝ)
  have h := hasDerivAt_signedSmoothEnergy hn hU hsub hu hh hu0 hh0 0
    (fun x hx => by rw [h₀]; exact hpos x hx)
  have he := hRaw.unique h
  simpa only [h₀] using he

/-- Differentiation of the determinant against a fixed continuous test on the ball. -/
theorem hasDerivAt_integral_test_mul_det {n : ℕ} (hn : 0 < n) {U : Set (E n)}
    (hU : IsOpen U) (hsub : closedUnitBall n ⊆ U)
    {u h : E n → ℝ} (hu : ContDiffOn ℝ ∞ u U) (hh : ContDiffOn ℝ ∞ h U)
    (t : ℝ)
    {ψ : E n → ℝ} (hψ : ContinuousOn ψ U) :
    HasDerivAt (fun s =>
      ∫ x in unitBall n, ψ x * (complexHessian (u + s • h) x).det.re ∂volume0 n)
      (∫ x in unitBall n, ψ x * cofactorContraction (u + t • h) h x ∂volume0 n) t := by
  have hA : ContinuousOn (fun p : ℝ × E n => (complexHessian (u + p.1 • h) p.2).det.re)
      (univ ×ˢ U) :=
    Complex.continuous_re.comp_continuousOn (continuous_id.matrix_det.comp_continuousOn
      (affineHessian_continuousOn hU hu hh))
  have hH : ContinuousOn (fun p : ℝ × E n => ψ p.2) (univ ×ˢ U) :=
    hψ.comp continuous_snd.continuousOn fun p hp => hp.2
  exact hasDerivAt_unitBall_integral hn hsub
    (F := fun s x => ψ x * (complexHessian (u + s • h) x).det.re)
    (F' := fun s x => ψ x * cofactorContraction (u + s • h) h x)
    (hH.mul hA) (hH.mul (affineCofactor_continuousOn hU hu hh))
    (fun s x hx => (hasDerivAt_det_affine (hu.contDiffAt (hU.mem_nhds hx))
      (hh.contDiffAt (hU.mem_nhds hx)) s).const_mul (ψ x)) t

private theorem hasDerivAt_integral_mul_det {n : ℕ} (hn : 0 < n) {U : Set (E n)}
    (hU : IsOpen U) (hsub : closedUnitBall n ⊆ U)
    {u h : E n → ℝ} (hu : ContDiffOn ℝ ∞ u U) (hh : ContDiffOn ℝ ∞ h U)
    (t : ℝ) :
    HasDerivAt (fun s =>
      ∫ x in unitBall n, h x * (complexHessian (u + s • h) x).det.re ∂volume0 n)
      (∫ x in unitBall n, h x * cofactorContraction (u + t • h) h x ∂volume0 n) t :=
  hasDerivAt_integral_test_mul_det hn hU hsub hu hh t hh.continuousOn

/-- The signed energy is concave along every affine segment of smooth
strictly plurisubharmonic zero-boundary potentials. -/
theorem concaveOn_signedSmoothEnergy_segment {n : ℕ} (hn : 0 < n) {U : Set (E n)}
    (hU : IsOpen U) (hsub : closedUnitBall n ⊆ U)
    {u h : E n → ℝ} (hu : ContDiffOn ℝ ∞ u U) (hh : ContDiffOn ℝ ∞ h U)
    (hu0 : ∀ x ∈ unitSphere n, u x = 0) (hh0 : ∀ x ∈ unitSphere n, h x = 0)
    (hpos : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ unitBall n, (complexHessian (u + t • h) x).PosDef) :
    ConcaveOn ℝ (Icc (0 : ℝ) 1) (fun t => signedSmoothEnergy (u + t • h)) := by
  refine concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc _ _)
    (f' := fun t => ∫ x in unitBall n, h x * (complexHessian (u + t • h) x).det.re ∂volume0 n)
    (f'' := fun t => ∫ x in unitBall n, h x * cofactorContraction (u + t • h) h x ∂volume0 n)
    ?_ ?_ ?_ ?_
  · intro t ht
    exact (hasDerivAt_signedSmoothEnergy hn hU hsub hu hh hu0 hh0 t (hpos t ht)).continuousAt.continuousWithinAt
  · intro t ht
    exact (hasDerivAt_signedSmoothEnergy hn hU hsub hu hh hu0 hh0 t (hpos t (interior_subset ht))).hasDerivWithinAt
  · intro t _
    exact (hasDerivAt_integral_mul_det hn hU hsub hu hh t).hasDerivWithinAt
  · intro t ht
    have hv : ContDiffOn ℝ ∞ (u + t • h) U := hu.add (hh.const_smul t)
    exact integral_mul_cofactorContraction_nonpos hn hU hsub hv hh (hpos t (interior_subset ht)) hh0

/-- The tangent upper bound for the signed energy at a smooth strict potential. -/
theorem signedSmoothEnergy_tangent_upper {n : ℕ} (hn : 0 < n) {U : Set (E n)}
    (hU : IsOpen U) (hsub : closedUnitBall n ⊆ U) {u v : E n → ℝ}
    (hu : ContDiffOn ℝ ∞ u U) (hv : ContDiffOn ℝ ∞ v U)
    (hu0 : ∀ x ∈ unitSphere n, u x = 0) (hv0 : ∀ x ∈ unitSphere n, v x = 0)
    (huP : ∀ x ∈ unitBall n, (complexHessian u x).PosDef)
    (hvP : ∀ x ∈ unitBall n, (complexHessian v x).PosDef) :
    signedSmoothEnergy v - signedSmoothEnergy u ≤
      ∫ x in unitBall n, (v x - u x) * (complexHessian u x).det.re ∂volume0 n := by
  let h := v - u
  let F (t : ℝ) := signedSmoothEnergy (u + t • h)
  let D (t : ℝ) := ∫ x in unitBall n, h x * (complexHessian (u + t • h) x).det.re ∂volume0 n
  have hh : ContDiffOn ℝ ∞ h U := hv.sub hu
  have hh0 (x : E n) (hx : x ∈ unitSphere n) : h x = 0 := by simp [h, hu0 x hx, hv0 x hx]
  have h₀ : u + (0 : ℝ) • h = u := by simp
  have h₁ : u + (1 : ℝ) • h = v := by simp [h]
  have hpos (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (x : E n) (hx : x ∈ unitBall n) :
      (complexHessian (u + t • h) x).PosDef := by
    by_cases hzero : t = 0
    · rw [hzero, h₀]
      exact huP x hx
    by_cases hone : t = 1
    · rw [hone, h₁]
      exact hvP x hx
    have hN := hU.mem_nhds (hsub (ball_subset_closedBall hx))
    have hH : complexHessian h x = complexHessian v x - complexHessian u x := by
      rw [show h = v + (-1 : ℝ) • u by simp [h, sub_eq_add_neg],
        complexHessian_affine (hv.contDiffAt hN) (hu.contDiffAt hN)]
      simp [sub_eq_add_neg]
    rw [complexHessian_affine (hu.contDiffAt hN) (hh.contDiffAt hN), hH]
    have he : complexHessian u x + (t : ℂ) • (complexHessian v x - complexHessian u x) =
        ((1 - t : ℝ) : ℂ) • complexHessian u x + (t : ℂ) • complexHessian v x := by
      ext i j
      simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, Complex.ofReal_sub,
        Complex.ofReal_one]
      ring
    rw [he]
    apply Matrix.PosDef.add
    · exact (huP x hx).smul (by exact_mod_cast (sub_pos.mpr (lt_of_le_of_ne ht.2 hone)))
    · exact (hvP x hx).smul (by exact_mod_cast (lt_of_le_of_ne ht.1 (Ne.symm hzero)))
  have hFD (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : HasDerivAt F (D t) t :=
    hasDerivAt_signedSmoothEnergy hn hU hsub hu hh hu0 hh0 t (hpos t ht)
  have hAnti : AntitoneOn D (Icc (0 : ℝ) 1) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _)
      (f' := fun t => ∫ x in unitBall n, h x * cofactorContraction (u + t • h) h x ∂volume0 n)
      ?_ ?_ ?_
    · intro t _
      exact (hasDerivAt_integral_mul_det hn hU hsub hu hh t).continuousAt.continuousWithinAt
    · intro t _
      exact (hasDerivAt_integral_mul_det hn hU hsub hu hh t).hasDerivWithinAt
    · intro t ht
      have hw : ContDiffOn ℝ ∞ (u + t • h) U := hu.add (hh.const_smul t)
      exact integral_mul_cofactorContraction_nonpos hn hU hsub hw hh
        (hpos t (interior_subset ht)) hh0
  have hc : ContinuousOn F (Icc 0 1) := fun t ht => (hFD t ht).continuousAt.continuousWithinAt
  have hd : DifferentiableOn ℝ F (Ioo 0 1) :=
    fun t ht => (hFD t ⟨ht.1.le, ht.2.le⟩).differentiableAt.differentiableWithinAt
  obtain ⟨t, ht, hEq⟩ := exists_deriv_eq_slope F zero_lt_one hc hd
  rw [(hFD t ⟨ht.1.le, ht.2.le⟩).deriv, sub_zero, div_one] at hEq
  have hle := hAnti (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by simp) ⟨ht.1.le, ht.2.le⟩ ht.1.le
  rw [hEq] at hle
  simpa only [F, D, h₀, h₁, h, Pi.sub_apply] using hle

end KEBall.MoserTrudinger
