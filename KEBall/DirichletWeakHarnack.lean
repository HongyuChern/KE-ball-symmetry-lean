import KEBall.DirichletDeGiorgiBridge

/-!
# Local weak Harnack for the actual Dirichlet coefficient field

The coefficient is the essentially bounded field already obtained in the
path limit.  The test identity uses its explicitly specified L² weak
gradient.  Choosing `q = (d - 2) / d`, for `d = 2n > 2`, gives an L¹
estimate from the pinned De Giorgi theorem.  The displayed essential infimum
retains the exact affine pullback used in that theorem.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter InnerProductSpace MeasureTheory Metric Set
open scoped ContDiff Distributions ENNReal Gradient NNReal Topology

noncomputable section

namespace KEBall

local notation "ν[" n "]" => Measure.restrict (volume0 n) (unitBall n)
local notation "𝓓B[" n "]" => 𝓓(dirichletBallOpens n, ℝ)

/-- Affine scaling preserves null sets on the corresponding balls. -/
theorem ae_dirichlet_affine_pullback {n : ℕ} {x₀ : E n} {R ρ : ℝ}
    (hR : 0 < R) {P : E n → Prop}
    (hP : ∀ᵐ x ∂(volume : Measure (E n)).restrict (ball x₀ (R * ρ)), P x) :
    ∀ᵐ z ∂(volume : Measure (E n)).restrict (ball (0 : E n) ρ), P (x₀ + R • z) := by
  have hMap : ∀ᵐ x ∂Measure.map (fun z : E n => x₀ + R • z)
      (volume.restrict (ball (0 : E n) ρ)), P x := by
    rw [DeGiorgi.affine_map_restrict_ball_radius hR]
    exact (Measure.ae_ennreal_smul_measure_iff
      (DeGiorgi.affine_scale_measure_ne_zero (d := 2 * n) hR)).mpr hP
  exact ae_of_ae_map
    (((measurable_const_add x₀).comp (measurable_const_smul R)).aemeasurable) hMap

/-- One weak Harnack constant works for every positive weak supersolution
of the given coefficient field and for every interior ball.  The power of
the radius is the real dimension `2 * n`. -/
theorem exists_dirichletWeakHarnack_constant {n : ℕ} (hn : 2 ≤ n)
    {B : E n → E n →L[ℝ] E n} (hB : MemLp B ⊤ ν[n])
    {c : ℝ} (hc : 0 < c)
    (hEll : ∀ᵐ x ∂ν[n], ∀ v : E n,
      c * ‖v‖ ^ 2 ≤ inner ℝ (B x v) v) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (f : E n → ℝ) (F : E n → E n),
        MemLp f 2 ν[n] → MemLp F 2 ν[n] → IsDirichletWeakGradient f F →
        (∀ ψ : 𝓓B[n], (∀ x ∈ unitBall n, 0 ≤ ψ x) →
          0 ≤ ∫ x, inner ℝ (B x (F x)) (∇ (ψ : E n → ℝ) x) ∂ν[n]) →
        ∀ (x₀ : E n) (R : ℝ), 0 < R → closedBall x₀ R ⊆ unitBall n →
          (∀ᵐ x ∂(volume : Measure (E n)).restrict (ball x₀ R), 0 < f x) →
          (R ^ (2 * n))⁻¹ * (∫ x in ball x₀ (R / 4), |f x|) ≤
            C * essInf (fun z : E n => f (x₀ + R • z))
              (volume.restrict (ball (0 : E n) (1 / 4 : ℝ))) := by
  have : NeZero n := ⟨by omega⟩
  have hd : (2 : ℝ) < (2 * n : ℕ) := by exact_mod_cast (show 2 < 2 * n by omega)
  let d : ℝ := (2 * n : ℕ)
  have hd0 : 0 < d := lt_trans (by norm_num) hd
  have hd2 : 0 < d - 2 := sub_pos.mpr hd
  let q : ℝ := (d - 2) / d
  have hq : 0 < q := div_pos hd2 hd0
  have hq1 : q < 1 := (div_lt_one hd0).mpr (by linarith)
  have hqd : q * d = d - 2 := div_mul_cancel₀ _ hd0.ne'
  have hp : q * d / (d - 2) = 1 := by rw [hqd, div_self hd2.ne']
  have hpinv : (d - 2) / (q * d) = 1 := by rw [hqd, div_self hd2.ne']
  obtain ⟨A, hAB⟩ := exists_dirichletDeGiorgi_coefficient hB hc hEll
  let C : ℝ :=
    (DeGiorgi.CWeakHarnack (2 * n) hd /
      (1 - q) ^ (DeGiorgi.weakHarnackDecayExp (2 * n))) ^ (A.1.Λ ^ ((1 : ℝ) / 2))
  have hC : 0 ≤ C := Real.rpow_nonneg
    (div_nonneg (zero_le_one.trans (DeGiorgi.one_le_C_weakHarnack hd))
      (Real.rpow_nonneg (sub_nonneg.mpr hq1.le) _)) _
  refine ⟨C, hC, ?_⟩
  intro f F hf hF hWeak hSuper x₀ R hR hSub hPos
  have hSuperA := isDeGiorgiSupersolution_of_dirichlet_weak hf hF hWeak hSuper
    A.1 (inv_nonneg.mpr hc.le) hAB
  let Ar : DeGiorgi.NormalizedEllipticCoeff (2 * n) (ball x₀ R) :=
    ⟨A.1.restrict (ball_subset_closedBall.trans hSub), A.2⟩
  have hSuperR : DeGiorgi.IsSupersolution Ar.1 f :=
    hSuperA.restrict_ball isOpen_ball hR hSub
  let fPos (x : E n) : ℝ := if 0 < f x then f x else 1
  have hEq : f =ᵐ[(volume : Measure (E n)).restrict (ball x₀ R)] fPos := by
    filter_upwards [hPos] with x hx
    simp only [fPos, if_pos hx]
  have hPosAll (x : E n) : 0 < fPos x := by
    by_cases hx : 0 < f x
    · simpa only [fPos, if_pos hx] using hx
    · simp only [fPos, if_neg hx, zero_lt_one]
  have hSuperPos : DeGiorgi.IsSupersolution Ar.1 fPos := hSuperR.congr_ae hEq
  have h := DeGiorgi.weak_harnack_on_ball hd hR Ar hq hq1
    (fun x _ => hPosAll x) hSuperPos
  have hEqQuarter : f =ᵐ[(volume : Measure (E n)).restrict (ball x₀ (R / 4))] fPos :=
    ae_restrict_of_ae_restrict_of_subset (ball_subset_ball (by linarith)) hEq
  have hInt : (∫ x in ball x₀ (R / 4), |fPos x|) =
      ∫ x in ball x₀ (R / 4), |f x| := by
    apply integral_congr_ae
    filter_upwards [hEqQuarter] with x hx
    rw [hx]
  have hPullback : (fun z : E n => f (x₀ + R • z)) =ᵐ[
      (volume : Measure (E n)).restrict (ball (0 : E n) (1 / 4 : ℝ))]
      (fun z : E n => fPos (x₀ + R • z)) := by
    apply ae_dirichlet_affine_pullback (n := n) (x₀ := x₀) (ρ := (1 / 4 : ℝ))
      (P := fun x => f x = fPos x) hR
    rw [show R * (1 / 4 : ℝ) = R / 4 by ring]
    exact hEqQuarter
  have hInf := essInf_congr_ae hPullback
  have hDim : Module.finrank ℝ (DeGiorgi.AmbientSpace (2 * n)) = 2 * n := by
    simp [DeGiorgi.AmbientSpace]
  rw [hInf]
  simpa only [hDim, show ((2 * n : ℕ) : ℝ) = d from rfl, hp, hpinv,
    Real.rpow_one, hInt, Ar, DeGiorgi.EllipticCoeff.restrict, C] using h

/-- Weak Harnack for the actual directional Hessian defects, with the
bounded source absorbed at precisely the scale `B * R² / (4 * n * c)`.
The upper bound on the Hessian is only almost everywhere; a positive
constant `ε` is retained so no pointwise representative is assumed. -/
theorem exists_correctedHessian_weakHarnack {n : ℕ} (hn : 2 ≤ n)
    {g : E n → ℝ} (hg : SmoothNear (closedUnitBall n) g) (t : ℝ)
    {G : E n → E n →L[ℝ] ℝ} {L : ℝ≥0}
    (hG : LipschitzOnWith L G (closedUnitBall n))
    {A : E n → E n →L[ℝ] E n} (hA : MemLp A ⊤ ν[n])
    (hDiv : ∀ (v : E n) (φ : 𝓓B[n]),
      (∫ x, inner ℝ (A x v) (∇ (φ : E n → ℝ) x) ∂ν[n]) = 0)
    {c : ℝ} (hc : 0 < c)
    (hEll : ∀ᵐ x ∂ν[n], ∀ v : E n, c * ‖v‖ ^ 2 ≤ inner ℝ (A x v) v) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (v : E n) (F : E n → E n),
      MemLp F 2 ν[n] → IsDirichletWeakGradient (fun x => fderiv ℝ G x v v) F →
      (∀ ψ : 𝓓B[n], (∀ x ∈ unitBall n, 0 ≤ ψ x) →
        (∫ x, inner ℝ (A x (F x)) (∇ (ψ : E n → ℝ) x) ∂ν[n]) ≤
          -(∫ x, ψ x * (Real.exp (t * g x) * (t * realHessian g x v v)) ∂ν[n])) →
      ∃ B : ℝ, 0 ≤ B ∧ ∀ (M R ε : ℝ) (x₀ : E n),
        0 < R → closedBall x₀ R ⊆ unitBall n → 0 < ε →
        (∀ᵐ x ∂(volume0 n).restrict (ball x₀ R), fderiv ℝ G x v v ≤ M) →
        (R ^ (2 * n))⁻¹ * (∫ x in ball x₀ (R / 4),
          |dirichletCorrectedHessianDefect G v (M + ε) (B / (4 * n * c)) R x₀ x|) ≤
          C * essInf (fun z : E n =>
            dirichletCorrectedHessianDefect G v (M + ε) (B / (4 * n * c)) R x₀
              (x₀ + R • z)) (volume.restrict (ball (0 : E n) (1 / 4 : ℝ))) := by
  obtain ⟨C, hC, hHarnack⟩ := exists_dirichletWeakHarnack_constant hn hA hc hEll
  refine ⟨C, hC, ?_⟩
  intro v F hF hWeak hSub
  obtain ⟨B, hB, hDefect⟩ := exists_homogeneous_corrected_hessian_defect
    (by omega : 0 < n) hg t hG hA hDiv hc hEll v hF hWeak hSub
  refine ⟨B, hB, ?_⟩
  intro M R ε x₀ hR hBall hε hM
  obtain ⟨hf, hQ, hW, hSup⟩ := hDefect (M + ε) R x₀
  apply hHarnack _ _ hf hQ hW hSup x₀ R hR hBall
  have ha : 0 ≤ B / (4 * n * c) := div_nonneg hB (by positivity)
  filter_upwards [ae_volume0_restrict_iff.mp hM,
    ae_restrict_mem (μ := (volume : Measure (E n))) measurableSet_ball] with x hx hxBall
  have hh := (correctedHessianDefect_nonneg_of_upper_bound G v ha hR.le
    (ball_subset_closedBall hxBall) hx).1
  have he : dirichletCorrectedHessianDefect G v (M + ε) (B / (4 * n * c)) R x₀ x =
      dirichletCorrectedHessianDefect G v M (B / (4 * n * c)) R x₀ x + ε := by
    simp only [dirichletCorrectedHessianDefect]
    ring
  rw [he]
  exact add_pos_of_nonneg_of_pos hh hε

end KEBall
