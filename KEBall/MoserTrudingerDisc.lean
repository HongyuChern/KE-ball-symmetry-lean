import KEBall.DiscPolynomialPoisson
import KEBall.MoserTrudingerSmoothGibbs

/-!
# The subcritical Moser–Trudinger bound on the disc

Polynomial Dirichlet solves approximate the Gibbs density. The
Brezis–Merle estimate bounds their exponential integrals uniformly.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Metric Set
open scoped ContDiff ComplexOrder ENNReal Laplacian

namespace KEBall.MoserTrudinger

open BrezisMerle DiscPolynomial

private theorem smooth_two_le_infty : (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω) :=
  ENat.natCast_le_of_coe_top_le_withTop le_rfl 2

private theorem posDef_of_laplacian_pos {v : E 1 → ℝ} {x : E 1}
    (hv : ContDiffAt ℝ ∞ v x) (hΔ : 0 < Δ v x) :
    (complexHessian v x).PosDef := by
  have hd := complexHessian_det_re_eq_laplacian_div_four hv
  rw [Matrix.det_fin_one] at hd
  have he : complexHessian v x = Matrix.diagonal (fun _ : Fin 1 => ((Δ v x / 4 : ℝ) : ℂ)) := by
    ext i j
    rw [Subsingleton.elim i (0 : Fin 1), Subsingleton.elim j (0 : Fin 1)]
    simp only [Matrix.diagonal_apply_eq]
    apply Complex.ext
    · exact hd
    · rw [complexHessian_real_entry hv]
      rw [realHessian_symm hv (realDirection 0) (imagDirection 0), sub_self]
      norm_num [Complex.mul_re, Complex.mul_im, Complex.inv_im]
  rw [he]
  apply Matrix.PosDef.diagonal
  intro _
  exact_mod_cast (div_pos hΔ (by norm_num) : 0 < Δ v x / 4)

theorem normalizingIntegral_disc_le_of_mass {v : E 1 → ℝ} (hv : ContDiff ℝ ∞ v)
    (hv0 : ∀ x ∈ unitSphere 1, v x = 0)
    (hvΔ : ∀ x ∈ unitBall 1, 0 ≤ Δ v x) {t r : ℝ}
    (ht : 0 < t) (hr : 0 < r) (hr' : r < 1)
    (hm : discMass (t • v) ≤ r) :
    normalizingIntegral t v ≤ 4 / (1 - r) := by
  let w := t • v
  have hw : ContDiff ℝ ∞ w := hv.const_smul t
  have hwΔ (x : E 1) (hx : x ∈ unitBall 1) : 0 ≤ Δ w x := by
    change 0 ≤ Δ (t • v) x
    rw [InnerProductSpace.laplacian_smul t (hv.of_le smooth_two_le_infty).contDiffAt, smul_eq_mul]
    exact mul_nonneg ht.le (hvΔ x hx)
  have hw0 (x : E 1) (hx : x ∈ unitSphere 1) : w x = 0 := by simp [w, hv0 x hx]
  have h := lintegral_exp_le_of_discMass_le (hw.of_le smooth_two_le_infty)
    (disc_nonpositive_of_laplacian_nonneg hw hwΔ (fun x hx => (hw0 x hx).le)) hw0 hwΔ hr hr' hm
  have hi : IntegrableOn (fun x => Real.exp (-w x)) (unitBall 1) :=
    ((Real.continuous_exp.comp hw.continuous.neg).continuousOn.integrableOn_compact
      (isCompact_closedBall (0 : E 1) 1)).mono_set ball_subset_closedBall
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun _ => (Real.exp_pos _).le)]
    at h
  have h' := (ENNReal.ofReal_le_ofReal_iff (by positivity : 0 ≤ 4 * Real.pi / (1 - r))).mp h
  unfold normalizingIntegral
  rw [setIntegral_volume0]
  norm_num [one_div]
  change Real.pi⁻¹ * (∫ x in unitBall 1, Real.exp (-w x)) ≤ _
  refine (mul_le_mul_of_nonneg_left h' (inv_nonneg.mpr Real.pi_pos.le)).trans_eq ?_
  have hp := Real.pi_pos
  field_simp

private theorem exists_disc_approximate_gibbs {u : E 1 → ℝ}
    (hu : ContinuousOn u (closedUnitBall 1)) {γ t r : ℝ}
    (ht : 0 < t) (htr : t < r) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ δ > 0, ∃ ε > 0, ε * M ≤ δ ∧ ∃ v : E 1 → ℝ,
      ContDiff ℝ ∞ v ∧
      (∀ x ∈ unitSphere 1, v x = 0) ∧
      (∀ x ∈ unitBall 1, 0 < Δ v x) ∧
      (∀ x ∈ unitBall 1, |(complexHessian v x).det.re - gibbsDensity γ u x| ≤ ε) ∧
      (∀ x ∈ unitBall 1, |u x - (1 / 2 : ℝ) * v x| ≤ M) ∧
      discMass (t • v) ≤ r := by
  let ρ := gibbsDensity γ u
  have hZ := normalizingIntegral_pos_of_continuousOn (n := 1) (by decide) hu γ
  have hρ : ContinuousOn ρ (closedUnitBall 1) :=
    (Real.continuous_exp.comp_continuousOn (continuousOn_const.mul hu)).div_const _
  have hpos (x : E 1) : 0 < ρ x := div_pos (Real.exp_pos _) hZ
  have hc := isCompact_closedBall (0 : E 1) 1
  have hne : (closedUnitBall 1).Nonempty := ⟨0, mem_closedBall_self zero_le_one⟩
  obtain ⟨xmin, hxmin, hMin⟩ := hc.exists_isMinOn hne hρ
  obtain ⟨xmax, _, hMax⟩ := hc.exists_isMaxOn hne hρ
  obtain ⟨U, hU⟩ := hc.exists_bound_of_continuousOn hu
  let P := ρ xmax + 1
  let M := |U| + P / 2 + 1
  have hP : 0 < P := by dsimp [P]; linarith [hpos xmax]
  have hM : 0 < M := by dsimp [M]; positivity
  refine ⟨M, hM.le, ?_⟩
  intro δ hδ
  let ε := min (min (ρ xmin / 2) 1) (min ((r - t) / t) (δ / M))
  have hε : 0 < ε := lt_min (lt_min (by positivity [hpos xmin]) zero_lt_one)
    (lt_min (div_pos (sub_pos.mpr htr) ht) (div_pos hδ hM))
  have hεm : ε ≤ ρ xmin / 2 := (min_le_left _ _).trans (min_le_left _ _)
  have hε1 : ε ≤ 1 := (min_le_left _ _).trans (min_le_right _ _)
  have hεr : ε ≤ (r - t) / t := (min_le_right _ _).trans (min_le_left _ _)
  have hεδ : ε ≤ δ / M := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨p, hp⟩ := exists_polynomial_uniformApprox hρ hε
  obtain ⟨q, hq0, hqΔ⟩ := exists_polynomial_zeroDirichlet p
  let v : E 1 → ℝ := fun x => (4 : ℝ) • evaluate q x
  have hv : ContDiff ℝ ∞ v := (contDiff_evaluate q).const_smul _
  have hv0 (x : E 1) (hx : x ∈ unitSphere 1) : v x = 0 := by simp [v, hq0 x hx]
  have hvΔ (x : E 1) : Δ v x = 4 * evaluate p x := by
    change Δ ((4 : ℝ) • evaluate q) x = _
    rw [InnerProductSpace.laplacian_smul _ ((contDiff_evaluate q).of_le smooth_two_le_infty).contDiffAt,
      smul_eq_mul, hqΔ]
  have hpPos (x : E 1) (hx : x ∈ closedUnitBall 1) : 0 < evaluate p x := by
    have h := (abs_lt.mp (hp x hx)).1
    have hmin : ρ xmin ≤ ρ x := hMin hx
    linarith [hmin, hεm, hpos xmin]
  have hpUpper (x : E 1) (hx : x ∈ closedUnitBall 1) : evaluate p x ≤ P := by
    have h := (abs_lt.mp (hp x hx)).2
    dsimp [P]
    have hmax : ρ x ≤ ρ xmax := hMax hx
    linarith [hmax, hε1]
  have hvΔ₀ (x : E 1) (hx : x ∈ unitBall 1) : 0 < Δ v x := by
    rw [hvΔ]
    exact mul_pos (by norm_num) (hpPos x (ball_subset_closedBall hx))
  have hvNonpos := disc_nonpositive_of_laplacian_nonneg hv (fun x hx => (hvΔ₀ x hx).le)
    (fun x hx => (hv0 x hx).le)
  let Q : E 1 → ℝ := fun x => ‖x‖ ^ 2 - 1
  have hQ : ContDiff ℝ ∞ Q := (contDiff_norm_sq ℝ).sub contDiff_const
  have hQP : ContDiff ℝ ∞ (P • Q) := hQ.const_smul P
  have hW : ContDiff ℝ ∞ (P • Q - v) := hQP.sub hv
  have hLower := disc_nonpositive_of_laplacian_nonneg hW
    (fun x hx => by
      rw [(hQP.of_le smooth_two_le_infty).contDiffAt.laplacian_sub
        ((hv.of_le smooth_two_le_infty).contDiffAt),
        InnerProductSpace.laplacian_smul _ (hQ.of_le smooth_two_le_infty).contDiffAt,
        show Δ Q x = 4 from laplacian_disc_quadratic x, smul_eq_mul, hvΔ]
      linarith [hpUpper x (ball_subset_closedBall hx)])
    (fun x hx => by
      have hnorm : ‖x‖ = 1 := mem_sphere_zero_iff_norm.mp hx
      simp [Q, hnorm, hv0 x hx])
  have hSize (x : E 1) (hx : x ∈ unitBall 1) : |u x - (1 / 2 : ℝ) * v x| ≤ M := by
    have hx' := ball_subset_closedBall hx
    have hvAbs : |v x| ≤ P := by
      rw [abs_of_nonpos (hvNonpos x hx')]
      have h := hLower x hx'
      change P * (‖x‖ ^ 2 - 1) - v x ≤ 0 at h
      linarith [mul_nonneg hP.le (sq_nonneg ‖x‖)]
    calc
      _ ≤ |u x| + |(1 / 2 : ℝ) * v x| := abs_sub _ _
      _ ≤ _ := by
        rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
        have h : |u x| ≤ U := by simpa [Real.norm_eq_abs] using hU x hx'
        dsimp [M]
        linarith [le_abs_self U]
  have hErr (x : E 1) (hx : x ∈ unitBall 1) :
      |(complexHessian v x).det.re - ρ x| ≤ ε := by
    rw [complexHessian_det_re_eq_laplacian_div_four hv.contDiffAt, hvΔ, mul_div_cancel_left₀ _ (by norm_num)]
    exact (hp x (ball_subset_closedBall hx)).le
  have hVol : (volume0 1) (unitBall 1) = 1 := volume0_unitBall 1 (by decide)
  have hpi : IntegrableOn (evaluate p) (unitBall 1) (volume0 1) :=
    (contDiff_evaluate p).continuous.continuousOn.integrableOn_of_subset_isCompact
      (isCompact_closedBall (0 : E 1) 1) measurableSet_ball ball_subset_closedBall
      (by rw [hVol]; exact ENNReal.one_ne_top)
  have hρi : IntegrableOn ρ (unitBall 1) (volume0 1) :=
    hρ.integrableOn_of_subset_isCompact (isCompact_closedBall (0 : E 1) 1)
      measurableSet_ball ball_subset_closedBall (by rw [hVol]; exact ENNReal.one_ne_top)
  have hρmass : (∫ x in unitBall 1, ρ x ∂volume0 1) = 1 := by
    dsimp [ρ, gibbsDensity]
    rw [integral_div, ← normalizingIntegral, div_self hZ.ne']
  have hpmass : (∫ x in unitBall 1, evaluate p x ∂volume0 1) ≤ 1 + ε := by
    have hεi : IntegrableOn (fun _ : E 1 => ε) (unitBall 1) (volume0 1) :=
      integrableOn_const (by rw [hVol]; exact ENNReal.one_ne_top)
    have hSum : IntegrableOn (fun x => ρ x + ε) (unitBall 1) (volume0 1) := hρi.add hεi
    have h := setIntegral_mono_on hpi hSum (show MeasurableSet (unitBall 1) from measurableSet_ball)
      (fun x hx => by linarith [(abs_lt.mp (hp x (ball_subset_closedBall hx))).2])
    rw [integral_add hρi hεi, hρmass, setIntegral_const, measureReal_def, hVol,
      ENNReal.toReal_one, one_smul] at h
    exact h
  have hm : discMass (t • v) ≤ r := by
    have he (x : E 1) : Δ (t • v) x = (4 * t) * evaluate p x := by
      rw [InnerProductSpace.laplacian_smul _ (hv.of_le smooth_two_le_infty).contDiffAt,
        smul_eq_mul, hvΔ]
      ring
    have hmass : discMass (t • v) = t * ∫ x in unitBall 1, evaluate p x ∂volume0 1 := by
      unfold discMass
      simp_rw [he]
      rw [integral_const_mul, setIntegral_volume0]
      norm_num
      have hpi := Real.pi_pos
      field_simp
    rw [hmass]
    have h := (le_div_iff₀ ht).mp hεr
    nlinarith [mul_le_mul_of_nonneg_left hpmass ht.le]
  exact ⟨ε, hε, (le_div_iff₀ hM).mp hεδ, v, hv, hv0, hvΔ₀, hErr, hSize, hm⟩

/-- The smooth one-dimensional subcritical Moser–Trudinger estimate
with the same signed energy as in higher dimension. -/
theorem smoothFunctional_disc_le {u : E 1 → ℝ} {U : Set (E 1)}
    (hU : IsOpen U) (hsub : closedUnitBall 1 ⊆ U) (hu : ContDiffOn ℝ ∞ u U)
    (hu0 : ∀ x ∈ unitSphere 1, u x = 0)
    (huP : ∀ x ∈ unitBall 1, (complexHessian u x).PosDef)
    {γ : ℝ} (hγ : 0 < γ) (hγ₂ : γ < 2) :
    smoothFunctional γ u ≤ Real.log (16 / (1 - γ / 2)) / γ := by
  let t : ℝ := (1 + γ / 2) / 2
  let r : ℝ := (1 + t) / 2
  have ht : 0 < t := by dsimp [t]; linarith
  have htr : t < r := by dsimp [r, t]; linarith
  have hr : 0 < r := ht.trans htr
  have hr' : r < 1 := by dsimp [r, t]; linarith
  have htγ : γ * (1 / 2 : ℝ) ≤ t := by dsimp [t]; linarith
  obtain ⟨M, _, hM⟩ := exists_disc_approximate_gibbs (γ := γ)
    (hu.continuousOn.mono hsub) ht htr
  apply le_of_forall_pos_le_add
  intro δ hδ
  obtain ⟨ε, hε, hεδ, v, hv, hv0, hvΔ, hErr, hSize, hm⟩ := hM δ hδ
  have hvP (x : E 1) (hx : x ∈ unitBall 1) : (complexHessian v x).PosDef :=
    posDef_of_laplacian_pos hv.contDiffAt (hvΔ x hx)
  have hvNonpos := disc_nonpositive_of_laplacian_nonneg hv
    (fun x hx => (hvΔ x hx).le) (fun x hx => (hv0 x hx).le)
  have hI := normalizingIntegral_disc_le_of_mass hv hv0 (fun x hx => (hvΔ x hx).le) ht hr hr' hm
  have hZ := normalizingIntegral_pos_of_continuousOn (n := 1) (by decide) hv.continuous.continuousOn t
  have hlog := Real.log_le_log hZ hI
  have h := smoothFunctional_le_of_approximate_gibbs (n := 1) (by decide) hU hsub hu
    hv.contDiffOn hu0 hv0 huP hvP (fun x hx => hvNonpos x (ball_subset_closedBall hx))
    hγ (by simpa only [Nat.cast_one, one_add_one_eq_two] using htγ) hε.le hErr
    (by simpa only [Nat.cast_one, one_add_one_eq_two] using hSize) hlog
  have hC : 4 / (1 - r) = 16 / (1 - γ / 2) := by
    dsimp [r, t]
    have h : 1 - γ / 2 ≠ 0 := by linarith
    field_simp
    ring
  rw [hC] at h
  linarith

end KEBall.MoserTrudinger
