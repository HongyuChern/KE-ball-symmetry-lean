import KEBall.BrezisMerleGreen

/-!
# Regularized Green tests with exact zero values on the circle
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Metric Set
open scoped ContDiff Laplacian RealInnerProductSpace Topology

namespace KEBall.BrezisMerle

/-- The squared reflected denominator of the unit disk Green function. -/
noncomputable def discGreenDenominator (z x : E 1) : ℝ :=
  ‖x - z‖ ^ 2 + (1 - ‖x‖ ^ 2) * (1 - ‖z‖ ^ 2)

theorem discGreenDenominator_nonneg (z x : E 1) :
    0 ≤ discGreenDenominator z x := by
  rw [discGreenDenominator, norm_sub_sq_real]
  nlinarith only [real_inner_le_norm x z, sq_nonneg (1 - ‖x‖ * ‖z‖)]

theorem discGreenDenominator_le_four {z x : E 1}
    (hz : z ∈ closedUnitBall 1) (hx : x ∈ closedUnitBall 1) :
    discGreenDenominator z x ≤ 4 := by
  have ht₀ : 0 ≤ ‖x‖ * ‖z‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have ht₁ : ‖x‖ * ‖z‖ ≤ 1 :=
    mul_le_one₀ (mem_closedBall_zero_iff.mp hx) (norm_nonneg _) (mem_closedBall_zero_iff.mp hz)
  have hSq := pow_le_pow_left₀ ht₀ ht₁ 2
  rw [discGreenDenominator, norm_sub_sq_real]
  nlinarith only [neg_le_of_abs_le (abs_real_inner_le_norm x z), ht₁, hSq]

/-- The regularized disk Green function preserves the boundary cancellation
at every positive regularization parameter. -/
noncomputable def regularizedDiscGreen (ε : ℝ) (z x : E 1) : ℝ :=
  Real.log (‖x - z‖ ^ 2 + ε) - Real.log (discGreenDenominator z x + ε)

theorem regularizedDiscGreen_contDiff {ε : ℝ} (hε : 0 < ε) (z : E 1) :
    ContDiff ℝ ∞ (regularizedDiscGreen ε z) := by
  have hN : ContDiff ℝ ∞ (fun x : E 1 => ‖x - z‖ ^ 2 + ε) :=
    ((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)).add contDiff_const
  have hD : ContDiff ℝ ∞ (fun x : E 1 => discGreenDenominator z x + ε) := by
    unfold discGreenDenominator
    exact (((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)).add
      ((contDiff_const.sub (contDiff_norm_sq ℝ)).mul contDiff_const)).add contDiff_const
  exact (hN.log fun x => (add_pos_of_nonneg_of_pos (sq_nonneg _) hε).ne').sub
    (hD.log fun x => (add_pos_of_nonneg_of_pos (discGreenDenominator_nonneg z x) hε).ne')

theorem regularizedDiscGreen_zero_on_sphere (ε : ℝ) (z : E 1) {x : E 1}
    (hx : x ∈ unitSphere 1) : regularizedDiscGreen ε z x = 0 := by
  simp only [regularizedDiscGreen, discGreenDenominator, mem_sphere_zero_iff_norm.mp hx,
    one_pow, sub_self, zero_mul, add_zero]

theorem regularizedDiscGreen_nonpos {ε : ℝ} (hε : 0 < ε)
    {z x : E 1} (hz : z ∈ closedUnitBall 1) (hx : x ∈ closedUnitBall 1) :
    regularizedDiscGreen ε z x ≤ 0 := by
  have hz' := mem_closedBall_zero_iff.mp hz
  have hx' := mem_closedBall_zero_iff.mp hx
  have hb : 0 ≤ (1 - ‖x‖ ^ 2) * (1 - ‖z‖ ^ 2) := by
    apply mul_nonneg <;> nlinarith [norm_nonneg x, norm_nonneg z]
  apply sub_nonpos.mpr (Real.log_le_log (add_pos_of_nonneg_of_pos (sq_nonneg _) hε) _)
  unfold discGreenDenominator
  linarith only [hb]

theorem regularizedLog_le_regularizedDiscGreen {ε : ℝ} (hε : 0 < ε)
    {z x : E 1} (hz : z ∈ closedUnitBall 1) (hx : x ∈ closedUnitBall 1) :
    regularizedLog ε z x ≤ regularizedDiscGreen ε z x := by
  apply sub_le_sub_left
  exact Real.log_le_log (add_pos_of_nonneg_of_pos (discGreenDenominator_nonneg z x) hε)
    (add_le_add (discGreenDenominator_le_four hz hx) le_rfl)

theorem discGreenDenominator_eq_reflectedPole {z : E 1} (hz : z ≠ 0) (x : E 1) :
    discGreenDenominator z x = ‖z‖ ^ 2 * ‖x - (‖z‖ ^ 2)⁻¹ • z‖ ^ 2 := by
  have hZ : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  simp only [discGreenDenominator, norm_sub_sq_real, real_inner_smul_right, norm_smul,
    Real.norm_of_nonneg (inv_nonneg.mpr (sq_nonneg ‖z‖))]
  field_simp [hZ]
  ring

theorem reflectedPole_norm {z : E 1} (hz : z ≠ 0) :
    ‖(‖z‖ ^ 2)⁻¹ • z‖ = ‖z‖⁻¹ := by
  have hZ := norm_ne_zero_iff.mpr hz
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (sq_nonneg ‖z‖))]
  field_simp [hZ]

/-- The pole reflected across the unit circle stays strictly outside it. -/
theorem one_lt_reflectedPole_norm {z : E 1} (hz : z ≠ 0) (hzB : z ∈ unitBall 1) :
    1 < ‖(‖z‖ ^ 2)⁻¹ • z‖ := by
  rw [reflectedPole_norm hz]
  exact (one_lt_inv₀ (norm_pos_iff.mpr hz)).mpr (mem_ball_zero_iff.mp hzB)

theorem laplacian_regularizedDiscGreen_zero {ε : ℝ} (hε : 0 < ε) (x : E 1) :
    Δ (regularizedDiscGreen ε 0) x / (4 * Real.pi) = logLaplacianKernel ε 0 x := by
  let C := Real.log (4 + ε) - Real.log (1 + ε)
  have hEq : regularizedDiscGreen ε 0 = regularizedLog ε 0 + fun _ => C := by
    funext y
    simp only [regularizedDiscGreen, discGreenDenominator, sub_zero, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0),
      sub_zero, mul_one, regularizedLog, Pi.add_apply, C]
    have h : ‖y‖ ^ 2 + (1 - ‖y‖ ^ 2) + ε = 1 + ε := by ring
    rw [h]
    ring
  rw [hEq, (regularizedLog_smooth hε (0 : E 1)).contDiffAt.laplacian_add contDiffAt_const,
    InnerProductSpace.laplacian_const, Pi.zero_apply, add_zero, logLaplacianKernel_eq hε]

/-- The interior Laplacian of the regularized Green test is the direct
logarithmic kernel minus the kernel at the reflected pole. -/
theorem laplacian_regularizedDiscGreen_of_ne_zero {ε : ℝ} (hε : 0 < ε) {z : E 1}
    (hz : z ≠ 0) (x : E 1) :
    Δ (regularizedDiscGreen ε z) x / (4 * Real.pi) =
      logLaplacianKernel ε z x -
        logLaplacianKernel (ε / ‖z‖ ^ 2) ((‖z‖ ^ 2)⁻¹ • z) x := by
  let a := ‖z‖ ^ 2
  let z' := a⁻¹ • z
  let η := ε / a
  have ha : 0 < a := pow_pos (norm_pos_iff.mpr hz) _
  have hη : 0 < η := div_pos hε ha
  let C := Real.log (4 + ε) - Real.log a - Real.log (4 + η)
  have hEq : regularizedDiscGreen ε z =
      (regularizedLog ε z - regularizedLog η z') + fun _ => C := by
    funext y
    simp only [regularizedDiscGreen, discGreenDenominator_eq_reflectedPole hz, regularizedLog,
      Pi.add_apply, Pi.sub_apply, C]
    change Real.log (‖y - z‖ ^ 2 + ε) - Real.log (a * ‖y - z'‖ ^ 2 + ε) = _
    have he : a * ‖y - z'‖ ^ 2 + ε = a * (‖y - z'‖ ^ 2 + η) := by
      dsimp only [η]
      field_simp
    rw [he, Real.log_mul ha.ne' (add_pos_of_nonneg_of_pos (sq_nonneg _) hη).ne']
    ring
  have hzSmooth := regularizedLog_smooth hε z
  have hz'Smooth := regularizedLog_smooth hη z'
  have hSub : ContDiff ℝ 2 (regularizedLog ε z - regularizedLog η z') := hzSmooth.sub hz'Smooth
  rw [hEq, hSub.contDiffAt.laplacian_add contDiffAt_const,
    hzSmooth.contDiffAt.laplacian_sub hz'Smooth.contDiffAt,
    InnerProductSpace.laplacian_const, Pi.zero_apply, add_zero, sub_div,
    ← logLaplacianKernel_eq hε, ← logLaplacianKernel_eq hη]

theorem measurable_laplacian_regularizedDiscGreen {ε : ℝ} (hε : 0 < ε) :
    Measurable (fun p : E 1 × E 1 => Δ (regularizedDiscGreen ε p.1) p.2) := by
  let D (p : E 1 × E 1) := logLaplacianKernel ε p.1 p.2
  let R (p : E 1 × E 1) :=
    logLaplacianKernel (ε / ‖p.1‖ ^ 2) ((‖p.1‖ ^ 2)⁻¹ • p.1) p.2
  have hD : Measurable D := (logLaplacianKernel_continuous hε).measurable
  have hR : Measurable R := by
    unfold R logLaplacianKernel
    fun_prop
  have hI : Measurable (fun p : E 1 × E 1 => if p.1 = 0 then 0 else R p) :=
    Measurable.ite (measurableSet_eq_fun measurable_fst measurable_const) measurable_const hR
  have hEq : (fun p : E 1 × E 1 => Δ (regularizedDiscGreen ε p.1) p.2) =
      fun p => (D p - (if p.1 = 0 then 0 else R p)) * (4 * Real.pi) := by
    funext p
    apply (div_eq_iff (by positivity : 4 * Real.pi ≠ 0)).mp
    by_cases hp : p.1 = 0
    · simpa only [hp, if_pos, sub_zero, D] using laplacian_regularizedDiscGreen_zero hε p.2
    · simpa only [if_neg hp, D, R] using laplacian_regularizedDiscGreen_of_ne_zero hε hp p.2
  rw [hEq]
  exact (hD.sub hI).mul_const _

/-- Green's inequality for a lower bound on the boundary values of the
function being estimated. The zero boundary condition belongs to the test. -/
theorem integral_regularizedDiscGreen_mul_laplacian_le {u : E 1 → ℝ}
    (hu : ContDiff ℝ 2 u) {δ ε : ℝ} (hε : 0 < ε)
    (hBoundary : ∀ x ∈ unitSphere 1, -δ ≤ u x) {z : E 1} (hz : z ∈ closedUnitBall 1) :
    (∫ x in unitBall 1, regularizedDiscGreen ε z x * Δ u x) ≤
      ∫ x in unitBall 1, (u x + δ) * Δ (regularizedDiscGreen ε z) x := by
  let G := regularizedDiscGreen ε z
  let w (x : E 1) := -(u x + δ)
  have hG : ContDiff ℝ 2 G := (regularizedDiscGreen_contDiff hε z).of_le
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hw : ContDiff ℝ 2 w := (hu.add contDiff_const).neg
  have h := integral_mul_laplacian_le (by decide : 0 < 1) hG hw
    (fun x hx => regularizedDiscGreen_nonpos hε hz hx)
    (fun x hx => regularizedDiscGreen_zero_on_sphere ε z hx)
    (fun x hx => neg_nonpos.mpr (by
      change 0 ≤ u x + δ
      linarith only [hBoundary x hx]))
  have hLap (x : E 1) : Δ w x = -Δ u x := by
    change Δ (-(u + fun _ : E 1 => δ) : E 1 → ℝ) x = _
    rw [InnerProductSpace.laplacian_neg, Pi.neg_apply,
      hu.contDiffAt.laplacian_add contDiffAt_const, InnerProductSpace.laplacian_const,
      Pi.zero_apply, add_zero]
  simp only [hLap, mul_neg, w, neg_mul, integral_neg] at h
  exact neg_le_neg_iff.mp h

private theorem tendsto_integral_logLaplacianKernel_of_outside {u : E 1 → ℝ} (hu : Continuous u)
    {z : E 1} (hz : 1 < ‖z‖) {ε : ℕ → ℝ} (hε : ∀ j, 0 < ε j)
    (hε₀ : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun j => ∫ x in unitBall 1, logLaplacianKernel (ε j) z x * u x) atTop (𝓝 0) := by
  let D := Real.pi * ((‖z‖ - 1) ^ 2) ^ 2
  have hD : 0 < D := by dsimp [D]; positivity
  have hInt : IntegrableOn u (unitBall 1) :=
    (hu.continuousOn.integrableOn_compact (isCompact_closedBall (0 : E 1) 1)).mono_set ball_subset_closedBall
  have ht : Tendsto (fun j => ε j / D * ∫ x in unitBall 1, ‖u x‖) atTop (𝓝 0) := by
    simpa only [zero_div, zero_mul] using (hε₀.div_const D).mul_const (∫ x in unitBall 1, ‖u x‖)
  apply squeeze_zero_norm _ ht
  intro j
  rw [← integral_const_mul]
  apply norm_integral_le_of_norm_le (hInt.norm.const_mul _)
  filter_upwards [ae_restrict_mem (μ := volume) (show MeasurableSet (unitBall 1) from measurableSet_ball)]
    with x hx
  have hx' := mem_ball_zero_iff.mp hx
  have hd : ‖z‖ - 1 ≤ ‖x - z‖ := by
    have h := norm_sub_norm_le z x
    rw [norm_sub_rev] at h
    linarith only [hx', h]
  have hgap : 0 ≤ ‖z‖ - 1 := sub_nonneg.mpr hz.le
  rw [norm_mul, Real.norm_of_nonneg (logLaplacianKernel_nonneg (hε j).le z x)]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  unfold logLaplacianKernel
  apply div_le_div_of_nonneg_left (hε j).le hD
  dsimp only [D]
  gcongr
  exact (pow_le_pow_left₀ hgap hd 2).trans (le_add_of_nonneg_right (hε j).le)

/-- The normalized Laplacians of the regularized Green tests concentrate
at the interior pole. The reflected pole contributes no limiting mass. -/
theorem tendsto_integral_laplacian_regularizedDiscGreen {u : E 1 → ℝ} (hu : Continuous u)
    {z : E 1} (hz : z ∈ unitBall 1) {ε : ℕ → ℝ} (hε : ∀ j, 0 < ε j)
    (hε₀ : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun j => ∫ x in unitBall 1, (Δ (regularizedDiscGreen (ε j) z) x / (4 * Real.pi)) * u x)
      atTop (𝓝 (u z)) := by
  by_cases hZ : z = 0
  · subst z
    simpa only [laplacian_regularizedDiscGreen_zero (hε _)] using
      tendsto_integral_logLaplacianKernel hu hz hε hε₀
  · let a := ‖z‖ ^ 2
    let y := a⁻¹ • z
    let η (j : ℕ) := ε j / a
    have ha : 0 < a := pow_pos (norm_pos_iff.mpr hZ) _
    have hη (j : ℕ) : 0 < η j := div_pos (hε j) ha
    have hη₀ : Tendsto η atTop (𝓝 0) := by
      simpa only [zero_div] using hε₀.div_const a
    have hRef := tendsto_integral_logLaplacianKernel_of_outside hu
      (show 1 < ‖y‖ from one_lt_reflectedPole_norm hZ hz) hη hη₀
    have h := (tendsto_integral_logLaplacianKernel hu hz hε hε₀).sub hRef
    have hI {s : ℝ} (hs : 0 < s) (b : E 1) :
        IntegrableOn (fun x => logLaplacianKernel s b x * u x) (unitBall 1) := by
      have hC := (logLaplacianKernel_continuous hs).comp
        (continuous_const.prodMk continuous_id : Continuous (fun x : E 1 => (b, x)))
      exact ((hC.mul hu).continuousOn.integrableOn_compact (isCompact_closedBall (0 : E 1) 1)).mono_set
        ball_subset_closedBall
    have hEq (j : ℕ) :
        (∫ x in unitBall 1, (Δ (regularizedDiscGreen (ε j) z) x / (4 * Real.pi)) * u x) =
          (∫ x in unitBall 1, logLaplacianKernel (ε j) z x * u x) -
          ∫ x in unitBall 1, logLaplacianKernel (η j) y x * u x := by
      simp_rw [laplacian_regularizedDiscGreen_of_ne_zero (hε _) hZ, sub_mul]
      exact integral_sub (hI (hε j) z) (hI (hη j) y)
    simpa only [hEq, sub_zero] using h

end KEBall.BrezisMerle
