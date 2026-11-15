import KEBall.Radial
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Data.Set.Card

/-!
# Scalar branches of the explicit radial family

These results classify the scalar parameter of the explicitly constructed
radial solutions.  They do not assume or assert that every PDE solution is
radial: that geometric classification is a separate theorem.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace KEBall

theorem continuous_boundaryPolynomial (n : ℕ) : Continuous (boundaryPolynomial n) := by
  exact (continuous_id.pow n).mul (continuous_const.sub (continuous_id.div_const _))

theorem hasDerivAt_boundaryPolynomial {n : ℕ} (hn : 1 ≤ n) (t : ℝ) :
    HasDerivAt (boundaryPolynomial n) (t ^ (n - 1) * ((n : ℝ) - t)) t := by
  have hk : (n + 1 : ℝ) ≠ 0 := by positivity
  have hp : t ^ n = t ^ (n - 1) * t := by
    rw [← pow_succ]
    congr 1
    omega
  have h := ((hasDerivAt_id t).pow n).mul
    ((hasDerivAt_const t 1).sub ((hasDerivAt_id t).div_const (n + 1 : ℝ)))
  convert h using 1 <;> try rfl
  dsimp
  rw [hp]
  field_simp
  ring

@[simp] theorem boundaryPolynomial_zero {n : ℕ} (hn : 1 ≤ n) :
    boundaryPolynomial n 0 = 0 := by
  simp [boundaryPolynomial, Nat.ne_of_gt hn]

@[simp] theorem boundaryPolynomial_upper (n : ℕ) :
    boundaryPolynomial n (n + 1 : ℝ) = 0 := by
  have hk : (n + 1 : ℝ) ≠ 0 := by positivity
  simp [boundaryPolynomial, hk]

@[simp] theorem boundaryPolynomial_peak (n : ℕ) :
    boundaryPolynomial n (n : ℝ) = criticalCoefficient n := by
  have hk : (n + 1 : ℝ) ≠ 0 := by positivity
  dsimp [boundaryPolynomial, criticalCoefficient]
  field_simp
  ring

theorem criticalCoefficient_pos {n : ℕ} (hn : 1 ≤ n) : 0 < criticalCoefficient n := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  exact div_pos (pow_pos hnR _) (by positivity)

theorem boundaryPolynomial_strictMonoOn {n : ℕ} (hn : 1 ≤ n) :
    StrictMonoOn (boundaryPolynomial n) (Set.Icc 0 (n : ℝ)) := by
  refine strictMonoOn_of_deriv_pos (convex_Icc _ _)
    (continuous_boundaryPolynomial n).continuousOn ?_
  intro t ht
  rw [interior_Icc] at ht
  rw [(hasDerivAt_boundaryPolynomial hn t).deriv]
  exact mul_pos (pow_pos ht.1 _) (sub_pos.mpr ht.2)

theorem boundaryPolynomial_strictAntiOn {n : ℕ} (hn : 1 ≤ n) :
    StrictAntiOn (boundaryPolynomial n) (Set.Icc (n : ℝ) (n + 1 : ℝ)) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  refine strictAntiOn_of_deriv_neg (convex_Icc _ _)
    (continuous_boundaryPolynomial n).continuousOn ?_
  intro t ht
  rw [interior_Icc] at ht
  rw [(hasDerivAt_boundaryPolynomial hn t).deriv]
  exact mul_neg_of_pos_of_neg (pow_pos (lt_trans hnR ht.1) _) (sub_neg.mpr ht.1)

theorem boundaryPolynomial_le_critical {n : ℕ} (hn : 1 ≤ n) {t : ℝ}
    (ht : t ∈ Set.Icc 0 (n + 1 : ℝ)) :
    boundaryPolynomial n t ≤ criticalCoefficient n := by
  have hnR : 0 ≤ (n : ℝ) := by positivity
  rw [← boundaryPolynomial_peak n]
  by_cases htn : t ≤ (n : ℝ)
  · exact (boundaryPolynomial_strictMonoOn hn).monotoneOn
      ⟨ht.1, htn⟩ ⟨hnR, le_rfl⟩ htn
  · exact (boundaryPolynomial_strictAntiOn hn).antitoneOn
      ⟨le_rfl, by linarith⟩ ⟨le_of_not_ge htn, ht.2⟩ (le_of_not_ge htn)

theorem boundaryPolynomial_eq_critical_iff {n : ℕ} (hn : 1 ≤ n) {t : ℝ}
    (ht : t ∈ Set.Icc 0 (n + 1 : ℝ)) :
    boundaryPolynomial n t = criticalCoefficient n ↔ t = (n : ℝ) := by
  have hnR : 0 ≤ (n : ℝ) := by positivity
  constructor
  · intro h
    rw [← boundaryPolynomial_peak n] at h
    by_cases htn : t ≤ (n : ℝ)
    · exact (boundaryPolynomial_strictMonoOn hn).injOn
        ⟨ht.1, htn⟩ ⟨hnR, le_rfl⟩ h
    · exact (boundaryPolynomial_strictAntiOn hn).injOn
        ⟨le_of_not_ge htn, ht.2⟩ ⟨le_rfl, by linarith⟩ h
  · rintro rfl
    exact boundaryPolynomial_peak n

theorem boundaryPolynomial_pos_iff {n : ℕ} {t : ℝ} (ht : 0 < t) :
    0 < boundaryPolynomial n t ↔ t < (n + 1 : ℝ) := by
  rw [boundaryPolynomial, mul_pos_iff_of_pos_left (pow_pos ht _), sub_pos,
    div_lt_one (by positivity : 0 < (n + 1 : ℝ))]

theorem boundaryPolynomial_le_critical_of_nonneg {n : ℕ} (hn : 1 ≤ n) {t : ℝ}
    (ht : 0 ≤ t) : boundaryPolynomial n t ≤ criticalCoefficient n := by
  by_cases htk : t ≤ (n + 1 : ℝ)
  · exact boundaryPolynomial_le_critical hn ⟨ht, htk⟩
  · have hfac : 1 - t / (n + 1 : ℝ) ≤ 0 := by
      have := (one_le_div (by positivity : 0 < (n + 1 : ℝ))).mpr
        (le_of_not_ge htk)
      linarith
    exact (mul_nonpos_of_nonneg_of_nonpos (pow_nonneg ht _) hfac).trans
      (criticalCoefficient_pos hn).le

/-- Each level strictly below the maximum has exactly two positive roots,
one on each side of the peak. -/
theorem boundaryPolynomial_subcritical {n : ℕ} (hn : 1 ≤ n) {μ : ℝ}
    (hμ : 0 < μ) (hμc : μ < criticalCoefficient n) :
    ∃ a c : ℝ, 0 < a ∧ a < (n : ℝ) ∧ (n : ℝ) < c ∧ c < (n + 1 : ℝ) ∧
      boundaryPolynomial n a = μ ∧ boundaryPolynomial n c = μ ∧
      (∀ t : ℝ, 0 < t → (boundaryPolynomial n t = μ ↔ t = a ∨ t = c)) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hleft : μ ∈ Set.Icc (boundaryPolynomial n 0) (boundaryPolynomial n (n : ℝ)) := by
    simpa only [boundaryPolynomial_zero hn, boundaryPolynomial_peak] using
      (show μ ∈ Set.Icc 0 (criticalCoefficient n) from ⟨hμ.le, hμc.le⟩)
  obtain ⟨a, ha, hfa⟩ := intermediate_value_Icc hnR.le
    (continuous_boundaryPolynomial n).continuousOn hleft
  have ha0 : 0 < a := by
    by_contra h
    have haeq : a = 0 := by linarith [ha.1]
    rw [haeq, boundaryPolynomial_zero hn] at hfa
    linarith
  have han : a < (n : ℝ) := by
    by_contra h
    have haeq : a = (n : ℝ) := by linarith [ha.2]
    rw [haeq, boundaryPolynomial_peak] at hfa
    linarith
  have hright : μ ∈ Set.Icc (boundaryPolynomial n (n + 1 : ℝ))
      (boundaryPolynomial n (n : ℝ)) := by
    simpa only [boundaryPolynomial_upper, boundaryPolynomial_peak] using
      (show μ ∈ Set.Icc 0 (criticalCoefficient n) from ⟨hμ.le, hμc.le⟩)
  obtain ⟨c, hc, hfc⟩ := intermediate_value_Icc' (by linarith : (n : ℝ) ≤ n + 1)
    (continuous_boundaryPolynomial n).continuousOn hright
  have hcn : (n : ℝ) < c := by
    by_contra h
    have hceq : c = (n : ℝ) := by linarith [hc.1]
    rw [hceq, boundaryPolynomial_peak] at hfc
    linarith
  have hck : c < (n + 1 : ℝ) := by
    by_contra h
    have hceq : c = (n + 1 : ℝ) := by linarith [hc.2]
    rw [hceq, boundaryPolynomial_upper] at hfc
    linarith
  refine ⟨a, c, ha0, han, hcn, hck, hfa, hfc, ?_⟩
  intro t ht
  constructor
  · intro hft
    have htk : t < (n + 1 : ℝ) :=
      (boundaryPolynomial_pos_iff ht).mp (hft.symm ▸ hμ)
    by_cases htn : t ≤ (n : ℝ)
    · exact Or.inl ((boundaryPolynomial_strictMonoOn hn).injOn
        ⟨ht.le, htn⟩ ha (hft.trans hfa.symm))
    · exact Or.inr ((boundaryPolynomial_strictAntiOn hn).injOn
        ⟨le_of_not_ge htn, htk.le⟩ hc (hft.trans hfc.symm))
  · rintro (rfl | rfl)
    · exact hfa
    · exact hfc

theorem boundaryPolynomial_critical {n : ℕ} (hn : 1 ≤ n) {t : ℝ} (ht : 0 < t) :
    boundaryPolynomial n t = criticalCoefficient n ↔ t = (n : ℝ) := by
  constructor
  · intro h
    have htk : t < (n + 1 : ℝ) :=
      (boundaryPolynomial_pos_iff ht).mp (h.symm ▸ criticalCoefficient_pos hn)
    exact (boundaryPolynomial_eq_critical_iff hn ⟨ht.le, htk.le⟩).mp h
  · rintro rfl
    exact boundaryPolynomial_peak n

theorem boundaryPolynomial_supercritical {n : ℕ} (hn : 1 ≤ n) {μ : ℝ}
    (hμ : criticalCoefficient n < μ) {t : ℝ} (ht : 0 ≤ t) :
    boundaryPolynomial n t ≠ μ := by
  exact ne_of_lt ((boundaryPolynomial_le_critical_of_nonneg hn ht).trans_lt hμ)

/-- The boundary-slope parameter of the explicit radial solution. -/
noncomputable def radialBoundaryParameter (n : ℕ) (b : ℝ) : ℝ :=
  (n + 1 : ℝ) * b / (1 + b)

theorem radial_boundarySlope (n : ℕ) {b : ℝ} (hb : 0 < b)
    {x : E n} (hx : x ∈ unitSphere n) :
    boundarySlope (radialPotential n b) x = radialBoundaryParameter n b := by
  have hxnorm : ‖x‖ = 1 := by simpa [unitSphere, Metric.mem_sphere, dist_zero_right] using hx
  have h := (hasDerivAt_radialProfile n hb (sq_nonneg ‖x‖)).comp_hasFDerivAt x
    (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  change HasFDerivAt (radialPotential n b)
    (radialSlopeProfile n b (‖x‖ ^ 2) • (2 • innerSL ℝ x)) x at h
  rw [boundarySlope, h.fderiv]
  simp only [smul_apply, innerSL_apply_apply, smul_eq_mul, real_inner_self_eq_norm_sq,
    hxnorm, one_pow]
  dsimp [radialSlopeProfile, radialBoundaryParameter]
  ring

theorem radialBoundaryParameter_mem (n : ℕ) {b : ℝ} (hb : 0 < b) :
    radialBoundaryParameter n b ∈ Set.Ioo 0 (n + 1 : ℝ) := by
  have hk : 0 < (n + 1 : ℝ) := by positivity
  constructor
  · exact div_pos (mul_pos hk hb) (by positivity)
  · dsimp [radialBoundaryParameter]
    rw [div_lt_iff₀ (by positivity : 0 < 1 + b)]
    nlinarith

theorem radialBoundaryParameter_strictMonoOn (n : ℕ) :
    StrictMonoOn (radialBoundaryParameter n) (Set.Ioi 0) := by
  intro b hb c hc hbc
  have hk : 0 < (n + 1 : ℝ) := by positivity
  dsimp [radialBoundaryParameter]
  rw [div_lt_div_iff₀ (add_pos zero_lt_one hb) (add_pos zero_lt_one hc)]
  nlinarith [mul_lt_mul_of_pos_left hbc hk]

theorem radialBoundaryParameter_inverse (n : ℕ) {t : ℝ}
    (ht : t ∈ Set.Ioo 0 (n + 1 : ℝ)) :
    radialBoundaryParameter n (t / ((n + 1 : ℝ) - t)) = t := by
  have hd : (n + 1 : ℝ) - t ≠ 0 := ne_of_gt (sub_pos.mpr ht.2)
  have hk : (n + 1 : ℝ) ≠ 0 := by positivity
  dsimp [radialBoundaryParameter]
  field_simp
  ring

theorem radialBoundaryParameter_surjOn (n : ℕ) :
    Set.SurjOn (radialBoundaryParameter n) (Set.Ioi 0) (Set.Ioo 0 (n + 1 : ℝ)) := by
  intro t ht
  exact ⟨t / ((n + 1 : ℝ) - t), div_pos ht.1 (sub_pos.mpr ht.2),
    radialBoundaryParameter_inverse n ht⟩

theorem radialBoundaryParameter_bijOn (n : ℕ) :
    Set.BijOn (radialBoundaryParameter n) (Set.Ioi 0) (Set.Ioo 0 (n + 1 : ℝ)) := by
  exact ⟨fun _ hb => radialBoundaryParameter_mem n hb,
    (radialBoundaryParameter_strictMonoOn n).injOn, radialBoundaryParameter_surjOn n⟩

theorem radialCoefficient_eq_boundaryPolynomial (n : ℕ) {b : ℝ} (hb : 0 < b) :
    radialCoefficient n b = boundaryPolynomial n (radialBoundaryParameter n b) := by
  have hb1 : 1 + b ≠ 0 := by positivity
  have hk : (n + 1 : ℝ) ≠ 0 := by positivity
  have hfac : 1 - radialBoundaryParameter n b / (n + 1 : ℝ) = 1 / (1 + b) := by
    dsimp [radialBoundaryParameter]
    field_simp
    ring
  rw [boundaryPolynomial, hfac]
  dsimp [radialCoefficient, radialBoundaryParameter]
  rw [div_pow, mul_pow, pow_succ]
  field_simp

@[simp] theorem radialBoundaryParameter_peak (n : ℕ) :
    radialBoundaryParameter n (n : ℝ) = (n : ℝ) := by
  have hk : (n + 1 : ℝ) ≠ 0 := by positivity
  dsimp [radialBoundaryParameter]
  rw [add_comm 1 (n : ℝ)]
  exact mul_div_cancel_left₀ _ hk

theorem radialCoefficient_le_critical {n : ℕ} (hn : 1 ≤ n) {b : ℝ} (hb : 0 < b) :
    radialCoefficient n b ≤ criticalCoefficient n := by
  rw [radialCoefficient_eq_boundaryPolynomial n hb]
  exact boundaryPolynomial_le_critical hn
    ⟨(radialBoundaryParameter_mem n hb).1.le, (radialBoundaryParameter_mem n hb).2.le⟩

theorem radialCoefficient_critical {n : ℕ} (hn : 1 ≤ n) {b : ℝ} (hb : 0 < b) :
    radialCoefficient n b = criticalCoefficient n ↔ b = (n : ℝ) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  rw [radialCoefficient_eq_boundaryPolynomial n hb,
    boundaryPolynomial_critical hn (radialBoundaryParameter_mem n hb).1]
  simpa only [radialBoundaryParameter_peak] using
    (radialBoundaryParameter_strictMonoOn n).injOn.eq_iff hb hnR

theorem radialCoefficient_supercritical {n : ℕ} (hn : 1 ≤ n) {μ : ℝ}
    (hμ : criticalCoefficient n < μ) {b : ℝ} (hb : 0 < b) :
    radialCoefficient n b ≠ μ := by
  exact ne_of_lt ((radialCoefficient_le_critical hn hb).trans_lt hμ)

theorem radialCoefficient_subcritical {n : ℕ} (hn : 1 ≤ n) {μ : ℝ}
    (hμ : 0 < μ) (hμc : μ < criticalCoefficient n) :
    ∃ b c : ℝ, 0 < b ∧ b < (n : ℝ) ∧ (n : ℝ) < c ∧
      radialCoefficient n b = μ ∧ radialCoefficient n c = μ ∧
      (∀ d : ℝ, 0 < d → (radialCoefficient n d = μ ↔ d = b ∨ d = c)) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  obtain ⟨a, d, ha, han, hnd, hdk, hfa, hfd, hroots⟩ :=
    boundaryPolynomial_subcritical hn hμ hμc
  obtain ⟨b, hb, htb⟩ := radialBoundaryParameter_surjOn n ⟨ha, by linarith⟩
  obtain ⟨c, hc, htc⟩ := radialBoundaryParameter_surjOn n ⟨by linarith, hdk⟩
  have hbn : b < (n : ℝ) :=
    ((radialBoundaryParameter_strictMonoOn n).lt_iff_lt hb hnR).mp
      (by simpa only [htb, radialBoundaryParameter_peak] using han)
  have hnc : (n : ℝ) < c :=
    ((radialBoundaryParameter_strictMonoOn n).lt_iff_lt hnR hc).mp
      (by simpa only [htc, radialBoundaryParameter_peak] using hnd)
  have hfb : radialCoefficient n b = μ := by
    rw [radialCoefficient_eq_boundaryPolynomial n hb, htb]
    exact hfa
  have hfc : radialCoefficient n c = μ := by
    rw [radialCoefficient_eq_boundaryPolynomial n hc, htc]
    exact hfd
  refine ⟨b, c, hb, hbn, hnc, hfb, hfc, ?_⟩
  intro e he
  rw [radialCoefficient_eq_boundaryPolynomial n he,
    hroots _ (radialBoundaryParameter_mem n he).1]
  constructor
  · rintro (h | h)
    · exact Or.inl ((radialBoundaryParameter_strictMonoOn n).injOn he hb (h.trans htb.symm))
    · exact Or.inr ((radialBoundaryParameter_strictMonoOn n).injOn he hc (h.trans htc.symm))
  · rintro (rfl | rfl)
    · exact Or.inl htb
    · exact Or.inr htc

@[simp] theorem radialPotential_origin (n : ℕ) (b : ℝ) :
    radialPotential n b 0 = -(n + 1 : ℝ) * Real.log (1 + b) := by
  simp [radialPotential, Real.log_inv]
  ring

theorem radialPotential_origin_strictAntiOn (n : ℕ) :
    StrictAntiOn (fun b : ℝ => radialPotential n b 0) (Set.Ioi 0) := by
  intro b hb c hc hbc
  change radialPotential n c 0 < radialPotential n b 0
  rw [radialPotential_origin, radialPotential_origin]
  have hlog : Real.log (1 + b) < Real.log (1 + c) :=
    Real.log_lt_log (add_pos zero_lt_one hb) (by linarith)
  exact mul_lt_mul_of_neg_left hlog (neg_lt_zero.mpr (by positivity))

theorem restrictClosedBall_radial_injective (n : ℕ) :
    Set.InjOn (fun b : ℝ => restrictClosedBall (radialPotential n b)) (Set.Ioi 0) := by
  intro b hb c hc h
  apply (radialPotential_origin_strictAntiOn n).injOn hb hc
  have h0 : (0 : E n) ∈ closedUnitBall n := by simp [closedUnitBall]
  exact congrFun h ⟨0, h0⟩

/-- The scalar analysis and the concrete construction supply two distinct
PDE solutions below the critical value, without using automatic symmetry. -/
theorem subcritical_two_radial_solutions {n : ℕ} (hn : 1 ≤ n) {μ : ℝ}
    (hμ : 0 < μ) (hμc : μ < criticalCoefficient n) :
    ∃ b c : ℝ, 0 < b ∧ 0 < c ∧ b < c ∧
      IsSolution n μ (radialPotential n b) ∧ IsSolution n μ (radialPotential n c) ∧
      restrictClosedBall (radialPotential n b) ≠ restrictClosedBall (radialPotential n c) := by
  obtain ⟨b, c, hb, hbn, hnc, hfb, hfc, _⟩ := radialCoefficient_subcritical hn hμ hμc
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hc : 0 < c := hnR.trans hnc
  have hbc : b < c := hbn.trans hnc
  refine ⟨b, c, hb, hc, hbc, ?_, ?_, ?_⟩
  · simpa only [hfb] using radial_isSolution n hb
  · simpa only [hfc] using radial_isSolution n hc
  · intro h
    exact (ne_of_lt hbc) ((restrictClosedBall_radial_injective n) hb hc h)

theorem critical_radial_solution {n : ℕ} (hn : 1 ≤ n) :
    IsSolution n (criticalCoefficient n) (radialPotential n (n : ℝ)) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hcoeff := (radialCoefficient_critical hn hnR).mpr rfl
  simpa only [hcoeff] using radial_isSolution n hnR

/-- Closed-ball restrictions belonging to the explicitly constructed family.
Equality of this set with `solutionSet` requires the separate symmetry and
radial-classification arguments. -/
def radialSolutionSet (n : ℕ) (μ : ℝ) : Set (ClosedBall n → ℝ) :=
  {v | ∃ b : ℝ, 0 < b ∧ radialCoefficient n b = μ ∧
    restrictClosedBall (radialPotential n b) = v}

theorem radialSolutionSet_subset_solutionSet (n : ℕ) (μ : ℝ) :
    radialSolutionSet n μ ⊆ solutionSet n μ := by
  rintro v ⟨b, hb, hcoeff, hv⟩
  refine ⟨radialPotential n b, ?_, hv⟩
  simpa only [hcoeff] using radial_isSolution n hb

theorem radialSolutionSet_subcritical {n : ℕ} (hn : 1 ≤ n) {μ : ℝ}
    (hμ : 0 < μ) (hμc : μ < criticalCoefficient n) :
    ∃ v w : ClosedBall n → ℝ, v ≠ w ∧ radialSolutionSet n μ = {v, w} := by
  obtain ⟨b, c, hb, hbn, hnc, hfb, hfc, hroots⟩ :=
    radialCoefficient_subcritical hn hμ hμc
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hc : 0 < c := hnR.trans hnc
  refine ⟨restrictClosedBall (radialPotential n b),
    restrictClosedBall (radialPotential n c), ?_, ?_⟩
  · intro h
    exact (ne_of_lt (hbn.trans hnc)) ((restrictClosedBall_radial_injective n) hb hc h)
  · ext v
    constructor
    · rintro ⟨d, hd, hfd, rfl⟩
      rcases (hroots d hd).mp hfd with rfl | rfl <;> simp
    · intro hv
      rcases Set.mem_insert_iff.mp hv with hv | hv
      · exact ⟨b, hb, hfb, hv.symm⟩
      · exact ⟨c, hc, hfc, (Set.mem_singleton_iff.mp hv).symm⟩

theorem radialSolutionSet_ncard_subcritical {n : ℕ} (hn : 1 ≤ n) {μ : ℝ}
    (hμ : 0 < μ) (hμc : μ < criticalCoefficient n) :
    (radialSolutionSet n μ).ncard = 2 := by
  obtain ⟨v, w, hvw, hset⟩ := radialSolutionSet_subcritical hn hμ hμc
  rw [hset]
  exact Set.ncard_pair hvw

theorem radialSolutionSet_critical {n : ℕ} (hn : 1 ≤ n) :
    radialSolutionSet n (criticalCoefficient n) =
      {restrictClosedBall (radialPotential n (n : ℝ))} := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  ext v
  constructor
  · rintro ⟨b, hb, hcoeff, rfl⟩
    rw [(radialCoefficient_critical hn hb).mp hcoeff]
    exact Set.mem_singleton _
  · intro hv
    exact ⟨(n : ℝ), hnR, (radialCoefficient_critical hn hnR).mpr rfl,
      (Set.mem_singleton_iff.mp hv).symm⟩

theorem radialSolutionSet_ncard_critical {n : ℕ} (hn : 1 ≤ n) :
    (radialSolutionSet n (criticalCoefficient n)).ncard = 1 := by
  rw [radialSolutionSet_critical hn, Set.ncard_singleton]

theorem radialSolutionSet_supercritical {n : ℕ} (hn : 1 ≤ n) {μ : ℝ}
    (hμ : criticalCoefficient n < μ) : radialSolutionSet n μ = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro v ⟨b, hb, hcoeff, _⟩
  exact radialCoefficient_supercritical hn hμ hb hcoeff

theorem radialSolutionSet_ncard_supercritical {n : ℕ} (hn : 1 ≤ n) {μ : ℝ}
    (hμ : criticalCoefficient n < μ) : (radialSolutionSet n μ).ncard = 0 := by
  rw [radialSolutionSet_supercritical hn hμ, Set.ncard_empty]

end KEBall
