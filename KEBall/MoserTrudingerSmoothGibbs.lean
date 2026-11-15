import KEBall.MoserTrudingerSmoothVariation
import Mathlib.Analysis.Convex.Integral

/-!
# Gibbs comparison for the smooth variational functional

The entropy argument is formulated directly with the Gibbs density and
the tangent inequality for the Monge–Ampère energy.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Metric Set
open scoped ComplexOrder ContDiff ENNReal

namespace KEBall.MoserTrudinger

private theorem integrableOn_unitBall_of_continuousOn {n : ℕ} (hn : 0 < n)
    {f : E n → ℝ} (hf : ContinuousOn f (closedUnitBall n)) :
    IntegrableOn f (unitBall n) (volume0 n) :=
  hf.integrableOn_of_subset_isCompact (isCompact_closedBall _ _)
    measurableSet_ball ball_subset_closedBall (by rw [volume0_unitBall n hn]; exact ENNReal.one_ne_top)

theorem normalizingIntegral_pos_of_continuousOn {n : ℕ} (hn : 0 < n)
    {u : E n → ℝ} (hu : ContinuousOn u (closedUnitBall n)) (γ : ℝ) :
    0 < normalizingIntegral γ u := by
  have h : IntegrableOn (fun x => Real.exp (-γ * u x)) (unitBall n) (volume0 n) :=
    integrableOn_unitBall_of_continuousOn hn
      (Real.continuous_exp.comp_continuousOn (continuousOn_const.mul hu))
  unfold normalizingIntegral
  rw [integral_pos_iff_support_of_nonneg (fun x => (Real.exp_pos _).le) h]
  have hS : Function.support (fun x => Real.exp (-γ * u x)) = univ := by
    ext x
    simp [Function.mem_support, Real.exp_ne_zero]
  rw [hS, Measure.restrict_apply_univ, volume0_unitBall n hn]
  exact zero_lt_one

/-- The Gibbs probability density with respect to the normalized ball volume. -/
noncomputable def gibbsDensity {n : ℕ} (γ : ℝ) (u : E n → ℝ) (x : E n) : ℝ :=
  Real.exp (-γ * u x) / normalizingIntegral γ u

private theorem integral_gibbs_log_ratio_comparison {n : ℕ} (hn : 0 < n)
    {u v : E n → ℝ} (hu : ContinuousOn u (closedUnitBall n))
    (hv : ContinuousOn v (closedUnitBall n)) (γ t : ℝ) :
    let I := ∫ x in unitBall n, gibbsDensity γ u x * (-t * v x + γ * u x) ∂volume0 n
    let R := Real.log (normalizingIntegral t v) - Real.log (normalizingIntegral γ u)
    I ≤ R ∧ (I = R → EqOn (fun x => -t * v x + γ * u x) (fun _ => I) (closedUnitBall n)) := by
  let ν := (volume0 n).restrict (unitBall n)
  let p := gibbsDensity γ u
  let μ := ν.withDensity (fun x => ENNReal.ofReal (p x))
  let L : E n → ℝ := fun x => -t * v x + γ * u x
  have hZ := normalizingIntegral_pos_of_continuousOn hn hu γ
  have hV := normalizingIntegral_pos_of_continuousOn hn hv t
  have hp₀ (x : E n) : 0 ≤ p x := div_nonneg (Real.exp_pos _).le hZ.le
  have hp : ContinuousOn p (closedUnitBall n) :=
    (Real.continuous_exp.comp_continuousOn (continuousOn_const.mul hu)).div_const _
  have hpi : Integrable p ν := integrableOn_unitBall_of_continuousOn hn hp
  have hp_meas : AEMeasurable (fun x => ENNReal.ofReal (p x)) ν :=
    ((hp.mono ball_subset_closedBall).aemeasurable measurableSet_ball).ennreal_ofReal
  have hp_lt : ∀ᵐ x ∂ν, ENNReal.ofReal (p x) < ⊤ :=
    Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  have hmass : (∫ x, p x ∂ν) = 1 := by
    change (∫ x in unitBall n, Real.exp (-γ * u x) / normalizingIntegral γ u ∂volume0 n) = 1
    rw [integral_div, ← normalizingIntegral, div_self hZ.ne']
  have : IsProbabilityMeasure μ := ⟨by
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hpi (Eventually.of_forall hp₀), hmass, ENNReal.ofReal_one]⟩
  have hL : ContinuousOn L (closedUnitBall n) :=
    (continuousOn_const.mul hv).add (continuousOn_const.mul hu)
  have hInt (g : E n → ℝ) (hg : ContinuousOn g (closedUnitBall n)) : Integrable g μ := by
    rw [integrable_withDensity_iff_integrable_smul₀' hp_meas hp_lt]
    have hEq : (fun x => (ENNReal.ofReal (p x)).toReal • g x) = (fun x => p x * g x) := by
      funext x
      simp [ENNReal.toReal_ofReal (hp₀ x), smul_eq_mul]
    rw [hEq]
    exact integrableOn_unitBall_of_continuousOn hn (hp.mul hg)
  have hI (g : E n → ℝ) : (∫ x, g x ∂μ) = ∫ x, p x * g x ∂ν := by
    rw [integral_withDensity_eq_integral_toReal_smul₀ hp_meas hp_lt]
    simp only [ENNReal.toReal_ofReal (hp₀ _), smul_eq_mul]
  have hJ := convexOn_exp.map_integral_le Real.continuous_exp.continuousOn isClosed_univ
    (Eventually.of_forall fun _ => mem_univ _) (hInt L hL)
    (hInt (Real.exp ∘ L) (Real.continuous_exp.comp_continuousOn hL))
  have hE (x : E n) : p x * Real.exp (L x) = Real.exp (-t * v x) / normalizingIntegral γ u := by
    dsimp only [p, L, gibbsDensity]
    rw [div_mul_eq_mul_div, ← Real.exp_add]
    congr 2
    ring
  have hEq : (∫ x, Real.exp (L x) ∂μ) = normalizingIntegral t v / normalizingIntegral γ u := by
    rw [hI]
    simp_rw [hE]
    rw [integral_div]
    rfl
  change Real.exp (∫ x, L x ∂μ) ≤ ∫ x, Real.exp (L x) ∂μ at hJ
  rw [hEq] at hJ
  have h := Real.log_le_log (Real.exp_pos _) hJ
  rw [Real.log_exp, Real.log_div hV.ne' hZ.ne', hI] at h
  refine ⟨h, ?_⟩
  intro hEqual
  let m := ∫ x, L x ∂μ
  have hm : m = Real.log (normalizingIntegral t v / normalizingIntegral γ u) := by
    rw [show m = _ from hI L, Real.log_div hV.ne' hZ.ne']
    exact hEqual
  let d (x : E n) := L x - m
  let g (x : E n) := Real.exp (d x) - (d x + 1)
  have hd : ContinuousOn d (closedUnitBall n) := hL.sub continuousOn_const
  have hExp : (∫ x, Real.exp (d x) ∂μ) = 1 := by
    simp only [d, Real.exp_sub, integral_div, hEq, hm, Real.exp_log (div_pos hV hZ),
      div_self (div_pos hV hZ).ne']
  have hLin : (∫ x, d x + 1 ∂μ) = 1 := by
    rw [integral_add (hInt d hd) (integrable_const _)]
    change (∫ x, L x - m ∂μ) + (∫ _ : E n, (1 : ℝ) ∂μ) = 1
    rw [integral_sub (hInt L hL) (integrable_const _)]
    simp [m]
  have hgInt := (hInt (fun x => Real.exp (d x)) (Real.continuous_exp.comp_continuousOn hd)).sub
    (hInt (fun x => d x + 1) (hd.add continuousOn_const))
  have hgZero : ∫ x, g x ∂μ = 0 := by
    rw [show (∫ x, g x ∂μ) = _ from integral_sub
      (hInt _ (Real.continuous_exp.comp_continuousOn hd)) (hInt _ (hd.add continuousOn_const)),
      hExp, hLin, sub_self]
  have hgNonneg (x : E n) : 0 ≤ g x := sub_nonneg.mpr (Real.add_one_le_exp (d x))
  have hgAE := (integral_eq_zero_iff_of_nonneg hgNonneg hgInt).mp hgZero
  have hdAE : ∀ᵐ x ∂ν, L x = m := by
    have hAE := (ae_withDensity_iff' hp_meas).mp hgAE
    filter_upwards [hAE] with x hx
    have hzero : g x = 0 := hx (ENNReal.ofReal_pos.mpr (div_pos (Real.exp_pos _) hZ)).ne'
    by_contra hne
    exact (sub_pos.mpr (Real.add_one_lt_exp (sub_ne_zero.mpr hne))).ne' hzero
  have hOn := Measure.eqOn_open_of_ae_eq hdAE isOpen_ball (hL.mono ball_subset_closedBall) continuousOn_const
  have hClosed : closedUnitBall n ⊆ closure (unitBall n) := by
    rw [show closure (unitBall n) = closedUnitBall n from closure_ball _ one_ne_zero]
  have he := hOn.of_subset_closure hL continuousOn_const ball_subset_closedBall hClosed
  rw [show m = _ from hI L] at he
  exact he

/-- Jensen applied to the ratio of two Gibbs densities. -/
theorem integral_gibbs_log_ratio_le {n : ℕ} (hn : 0 < n)
    {u v : E n → ℝ} (hu : ContinuousOn u (closedUnitBall n))
    (hv : ContinuousOn v (closedUnitBall n)) (γ t : ℝ) :
    (∫ x in unitBall n, gibbsDensity γ u x * (-t * v x + γ * u x) ∂volume0 n) ≤
      Real.log (normalizingIntegral t v) - Real.log (normalizingIntegral γ u) :=
  (integral_gibbs_log_ratio_comparison hn hu hv γ t).1

/-- The real-valued variational functional on smooth potentials. -/
noncomputable def smoothFunctional {n : ℕ} (γ : ℝ) (u : E n → ℝ) : ℝ :=
  signedSmoothEnergy u + Real.log (normalizingIntegral γ u) / γ

/-- The Gibbs step increases the functional, with equality only when the two
potentials agree on the closed ball. -/
theorem smoothFunctional_gibbs_step {n : ℕ} (hn : 0 < n) {U : Set (E n)}
    (hU : IsOpen U) (hsub : closedUnitBall n ⊆ U) {u v : E n → ℝ}
    (hu : ContDiffOn ℝ ∞ u U) (hv : ContDiffOn ℝ ∞ v U)
    (hu0 : ∀ x ∈ unitSphere n, u x = 0) (hv0 : ∀ x ∈ unitSphere n, v x = 0)
    (huP : ∀ x ∈ unitBall n, (complexHessian u x).PosDef)
    (hvP : ∀ x ∈ unitBall n, (complexHessian v x).PosDef)
    {γ : ℝ} (hγ : 0 < γ)
    (hEq : ∀ x ∈ unitBall n, (complexHessian v x).det.re = gibbsDensity γ u x) :
    smoothFunctional γ u ≤ smoothFunctional γ v ∧
      (smoothFunctional γ u = smoothFunctional γ v → EqOn u v (closedUnitBall n)) := by
  have hT := signedSmoothEnergy_tangent_upper hn hU hsub hv hu hv0 hu0 hvP huP
  have hComp := integral_gibbs_log_ratio_comparison hn (hu.continuousOn.mono hsub)
    (hv.continuousOn.mono hsub) γ γ
  have hE : (∫ x in unitBall n, gibbsDensity γ u x * (-γ * v x + γ * u x) ∂volume0 n) =
      γ * ∫ x in unitBall n, (u x - v x) * (complexHessian v x).det.re ∂volume0 n := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun (show MeasurableSet (unitBall n) from measurableSet_ball)
    intro x hx
    dsimp only
    rw [hEq x hx]
    ring
  have hJ := hComp.1
  rw [hE] at hJ
  have h := (le_div_iff₀ hγ).mpr (by simpa only [mul_comm] using hJ)
  refine ⟨by unfold smoothFunctional; linarith only [hT, sub_div _ _ γ ▸ h], ?_⟩
  intro hValue
  have hRev : (Real.log (normalizingIntegral γ v) - Real.log (normalizingIntegral γ u)) / γ ≤
      ∫ x in unitBall n, (u x - v x) * (complexHessian v x).det.re ∂volume0 n := by
    rw [sub_div]
    unfold smoothFunctional at hValue
    linarith only [hT, hValue]
  have hLog := (div_le_iff₀ hγ).mp hRev
  have hEqual := hComp.2 (le_antisymm hComp.1 (by rw [hE, mul_comm]; exact hLog))
  let : Nontrivial (E n) := Module.nontrivial_of_finrank_pos (R := ℝ)
    (by rw [finrank_E]; omega)
  obtain ⟨z, hz⟩ := NormedSpace.sphere_nonempty (x := (0 : E n)) (r := 1).mpr zero_le_one
  have hzC : z ∈ closedUnitBall n := sphere_subset_closedBall hz
  have hzEq := hEqual hzC
  dsimp only at hzEq
  rw [hu0 z hz, hv0 z hz, mul_zero, mul_zero, add_zero] at hzEq
  intro x hx
  have hxEq := hEqual hx
  dsimp only at hxEq
  rw [← hzEq] at hxEq
  apply mul_left_cancel₀ hγ.ne' (b := u x) (c := v x)
  linarith only [hxEq]

/-- One smooth Dirichlet solve with Gibbs density increases the functional. -/
theorem smoothFunctional_le_of_gibbs_step {n : ℕ} (hn : 0 < n) {U : Set (E n)}
    (hU : IsOpen U) (hsub : closedUnitBall n ⊆ U) {u v : E n → ℝ}
    (hu : ContDiffOn ℝ ∞ u U) (hv : ContDiffOn ℝ ∞ v U)
    (hu0 : ∀ x ∈ unitSphere n, u x = 0) (hv0 : ∀ x ∈ unitSphere n, v x = 0)
    (huP : ∀ x ∈ unitBall n, (complexHessian u x).PosDef)
    (hvP : ∀ x ∈ unitBall n, (complexHessian v x).PosDef)
    {γ : ℝ} (hγ : 0 < γ)
    (hEq : ∀ x ∈ unitBall n, (complexHessian v x).det.re = gibbsDensity γ u x) :
    smoothFunctional γ u ≤ smoothFunctional γ v :=
  (smoothFunctional_gibbs_step hn hU hsub hu hv hu0 hv0 huP hvP hγ hEq).1

/-- The smooth entropy reduction of a mass-one exponential estimate
to an upper bound on the variational functional. -/
theorem smoothFunctional_le_of_gibbs_mass_bound {n : ℕ} (hn : 0 < n) {U : Set (E n)}
    (hU : IsOpen U) (hsub : closedUnitBall n ⊆ U) {u v : E n → ℝ}
    (hu : ContDiffOn ℝ ∞ u U) (hv : ContDiffOn ℝ ∞ v U)
    (hu0 : ∀ x ∈ unitSphere n, u x = 0) (hv0 : ∀ x ∈ unitSphere n, v x = 0)
    (huP : ∀ x ∈ unitBall n, (complexHessian u x).PosDef)
    (hvP : ∀ x ∈ unitBall n, (complexHessian v x).PosDef)
    (hvneg : ∀ x ∈ unitBall n, v x ≤ 0)
    {γ t C : ℝ} (hγ : 0 < γ) (ht : γ * ((n : ℝ) / (n + 1)) ≤ t)
    (hEq : ∀ x ∈ unitBall n, (complexHessian v x).det.re = gibbsDensity γ u x)
    (hLog : Real.log (normalizingIntegral t v) ≤ C) :
    smoothFunctional γ u ≤ C / γ := by
  let A (x : E n) : ℝ := (complexHessian v x).det.re
  let Iu := ∫ x in unitBall n, u x * A x ∂volume0 n
  let Iv := ∫ x in unitBall n, v x * A x ∂volume0 n
  have hA : ContinuousOn A (closedUnitBall n) :=
    (Complex.continuous_re.comp_continuousOn
      (matrixField_det_contDiffOn (complexHessian_contDiffOn hU hv)).continuousOn).mono hsub
  have hIntU : IntegrableOn (fun x => u x * A x) (unitBall n) (volume0 n) :=
    integrableOn_unitBall_of_continuousOn hn ((hu.continuousOn.mono hsub).mul hA)
  have hIntV : IntegrableOn (fun x => v x * A x) (unitBall n) (volume0 n) :=
    integrableOn_unitBall_of_continuousOn hn ((hv.continuousOn.mono hsub).mul hA)
  have hT := signedSmoothEnergy_tangent_upper hn hU hsub hv hu hv0 hu0 hvP huP
  have hEn : signedSmoothEnergy v = Iv / (n + 1 : ℝ) := rfl
  have hDiff : (∫ x in unitBall n, (u x - v x) * A x ∂volume0 n) = Iu - Iv := by
    simp_rw [sub_mul]
    exact integral_sub hIntU hIntV
  change signedSmoothEnergy u - signedSmoothEnergy v ≤
    ∫ x in unitBall n, (u x - v x) * A x ∂volume0 n at hT
  rw [hEn, hDiff] at hT
  have hJ := integral_gibbs_log_ratio_le hn (hu.continuousOn.mono hsub)
    (hv.continuousOn.mono hsub) γ t
  have hE : (∫ x in unitBall n, gibbsDensity γ u x * (-t * v x + γ * u x) ∂volume0 n) =
      -t * Iv + γ * Iu := by
    unfold Iv Iu
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add
      (hIntV.const_mul _) (hIntU.const_mul _)]
    apply setIntegral_congr_fun (show MeasurableSet (unitBall n) from measurableSet_ball)
    intro x hx
    dsimp only
    rw [← hEq x hx]
    dsimp only [A]
    ring
  rw [hE] at hJ
  have hNonpos : Iv ≤ 0 := by
    apply integral_nonpos_of_ae
    filter_upwards [ae_restrict_mem (μ := volume0 n)
      (show MeasurableSet (unitBall n) from measurableSet_ball)] with x hx
    exact mul_nonpos_of_nonpos_of_nonneg (hvneg x hx) (posDef_det_re_pos (hvP x hx)).le
  have hCoeff : 0 ≤ t - γ * ((n : ℝ) / (n + 1)) := sub_nonneg.mpr ht
  have hProduct := mul_nonpos_of_nonneg_of_nonpos hCoeff hNonpos
  have hEnergy : signedSmoothEnergy u ≤ Iu - ((n : ℝ) / (n + 1)) * Iv := by
    have h : Iv / (n + 1 : ℝ) - Iv = -((n : ℝ) / (n + 1)) * Iv := by field_simp; ring
    linarith
  have hSum := mul_le_mul_of_nonneg_left hEnergy hγ.le
  apply (le_div_iff₀ hγ).mpr
  unfold smoothFunctional
  rw [add_mul, div_mul_cancel₀ _ hγ.ne']
  linarith [hJ.trans (sub_le_sub_right hLog _), hProduct, hSum]

/-- The entropy comparison is stable under a uniform error in the
Gibbs density of the auxiliary Dirichlet problem. -/
theorem smoothFunctional_le_of_approximate_gibbs {n : ℕ} (hn : 0 < n) {U : Set (E n)}
    (hU : IsOpen U) (hsub : closedUnitBall n ⊆ U) {u v : E n → ℝ}
    (hu : ContDiffOn ℝ ∞ u U) (hv : ContDiffOn ℝ ∞ v U)
    (hu0 : ∀ x ∈ unitSphere n, u x = 0) (hv0 : ∀ x ∈ unitSphere n, v x = 0)
    (huP : ∀ x ∈ unitBall n, (complexHessian u x).PosDef)
    (hvP : ∀ x ∈ unitBall n, (complexHessian v x).PosDef)
    (hvneg : ∀ x ∈ unitBall n, v x ≤ 0)
    {γ t C ε M : ℝ} (hγ : 0 < γ) (ht : γ * ((n : ℝ) / (n + 1)) ≤ t)
    (hε : 0 ≤ ε)
    (hErr : ∀ x ∈ unitBall n, |(complexHessian v x).det.re - gibbsDensity γ u x| ≤ ε)
    (hSize : ∀ x ∈ unitBall n, |u x - ((n : ℝ) / (n + 1)) * v x| ≤ M)
    (hLog : Real.log (normalizingIntegral t v) ≤ C) :
    smoothFunctional γ u ≤ C / γ + ε * M := by
  let A (x : E n) : ℝ := (complexHessian v x).det.re
  let p := gibbsDensity γ u
  let c : ℝ := (n : ℝ) / (n + 1)
  let L (x : E n) := u x - c * v x
  let μ := (volume0 n).restrict (unitBall n)
  have hZ := normalizingIntegral_pos_of_continuousOn hn (hu.continuousOn.mono hsub) γ
  have hCu := hu.continuousOn.mono hsub
  have hCv := hv.continuousOn.mono hsub
  have hA : ContinuousOn A (closedUnitBall n) :=
    (Complex.continuous_re.comp_continuousOn
      (matrixField_det_contDiffOn (complexHessian_contDiffOn hU hv)).continuousOn).mono hsub
  have hp : ContinuousOn p (closedUnitBall n) :=
    (Real.continuous_exp.comp_continuousOn (continuousOn_const.mul hCu)).div_const _
  have hI (f : E n → ℝ) (hf : ContinuousOn f (closedUnitBall n)) : Integrable f μ :=
    integrableOn_unitBall_of_continuousOn hn hf
  have hIntU : Integrable (fun x => u x * A x) μ := hI _ (hCu.mul hA)
  have hIntV : Integrable (fun x => v x * A x) μ := hI _ (hCv.mul hA)
  have hpU : Integrable (fun x => u x * p x) μ := hI _ (hCu.mul hp)
  have hpV : Integrable (fun x => v x * p x) μ := hI _ (hCv.mul hp)
  have hL : ContinuousOn L (closedUnitBall n) := hCu.sub (continuousOn_const.mul hCv)
  have hLA : Integrable (fun x => L x * A x) μ := hI _ (hL.mul hA)
  have hLp : Integrable (fun x => L x * p x) μ := hI _ (hL.mul hp)
  have hT := signedSmoothEnergy_tangent_upper hn hU hsub hv hu hv0 hu0 hvP huP
  have hT' : signedSmoothEnergy u ≤ ∫ x, L x * A x ∂μ := by
    have hs : (fun x => (u x - v x) * A x) = fun x => u x * A x - v x * A x := by
      funext x
      ring
    change signedSmoothEnergy u - (∫ x, v x * A x ∂μ) / (n + 1 : ℝ) ≤
      ∫ x, (u x - v x) * A x ∂μ at hT
    rw [hs, integral_sub hIntU hIntV] at hT
    have hL' : (fun x => L x * A x) = fun x => u x * A x - c * (v x * A x) := by
      funext x
      dsimp [L]
      ring
    rw [hL', integral_sub hIntU (hIntV.const_mul c), integral_const_mul]
    have he (a : ℝ) : a / (n + 1 : ℝ) - a = -c * a := by dsimp [c]; field_simp; ring
    linarith [he (∫ x, v x * A x ∂μ)]
  have hbound : (∫ x, L x * A x ∂μ) - (∫ x, L x * p x ∂μ) ≤ ε * M := by
    rw [← integral_sub hLA hLp]
    have hAE : ∀ᵐ x ∂μ, L x * A x - L x * p x ≤ ε * M := by
      filter_upwards [ae_restrict_mem (μ := volume0 n)
        (show MeasurableSet (unitBall n) from measurableSet_ball)] with x hx
      rw [← mul_sub]
      exact (le_abs_self _).trans (by
        rw [abs_mul, mul_comm]
        exact mul_le_mul (hErr x hx) (hSize x hx) (abs_nonneg _) hε)
    have hConst : Integrable (fun _ : E n => ε * M) μ :=
      integrableOn_const (by rw [volume0_unitBall n hn]; exact ENNReal.one_ne_top)
    have hs := integral_mono_ae (hLA.sub hLp) hConst hAE
    rwa [integral_const, measureReal_def, Measure.restrict_apply_univ, volume0_unitBall n hn,
      ENNReal.toReal_one, one_smul] at hs
  have hIu : (∫ x, L x * p x ∂μ) = (∫ x, u x * p x ∂μ) - c * ∫ x, v x * p x ∂μ := by
    have hEq : (fun x => L x * p x) = fun x => u x * p x - c * (v x * p x) := by
      funext x
      dsimp [L]
      ring
    rw [hEq, integral_sub hpU (hpV.const_mul c), integral_const_mul]
  have hJ := integral_gibbs_log_ratio_le hn hCu hCv γ t
  have hJ' : -t * (∫ x, v x * p x ∂μ) + γ * (∫ x, u x * p x ∂μ) ≤
      Real.log (normalizingIntegral t v) - Real.log (normalizingIntegral γ u) := by
    change (∫ x, p x * (-t * v x + γ * u x) ∂μ) ≤ _ at hJ
    have he : (fun x => p x * (-t * v x + γ * u x)) =
        fun x => -t * (v x * p x) + γ * (u x * p x) := by
      funext x
      ring
    rwa [he, integral_add (hpV.const_mul _) (hpU.const_mul _), integral_const_mul, integral_const_mul]
      at hJ
  have hneg : (∫ x, v x * p x ∂μ) ≤ 0 := by
    apply integral_nonpos_of_ae
    filter_upwards [ae_restrict_mem (μ := volume0 n)
      (show MeasurableSet (unitBall n) from measurableSet_ball)] with x hx
    exact mul_nonpos_of_nonpos_of_nonneg (hvneg x hx) (div_nonneg (Real.exp_pos _).le hZ.le)
  have hB' : signedSmoothEnergy u ≤
      (∫ x, u x * p x ∂μ) - c * (∫ x, v x * p x ∂μ) + ε * M := by
    rw [hIu] at hbound
    linarith
  have hCoeff : 0 ≤ t - γ * c := sub_nonneg.mpr ht
  have hProduct := mul_nonpos_of_nonneg_of_nonpos hCoeff hneg
  have hFinal := mul_le_mul_of_nonneg_left hB' hγ.le
  apply (le_of_mul_le_mul_right _ hγ)
  unfold smoothFunctional
  rw [add_mul, div_mul_cancel₀ _ hγ.ne', add_mul, div_mul_cancel₀ _ hγ.ne']
  linarith [hJ'.trans (sub_le_sub_right hLog _), hProduct, hFinal]

end KEBall.MoserTrudinger
