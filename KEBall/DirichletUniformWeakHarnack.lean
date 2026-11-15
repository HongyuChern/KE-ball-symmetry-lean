import KEBall.DirichletWeakHarnack
import KEBall.DirichletUniformHarnackCoefficient

/-!
# A weak Harnack constant uniform over the prescribed coefficient bounds

The estimate retains the exact real dimension and radius scaling, and the
same normalized-to-project measure bridge.  Its single constant depends
only on dimension, the coercivity lower bound, and the operator norm bound.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter InnerProductSpace MeasureTheory Metric Set
open scoped ContDiff Distributions ENNReal Gradient NNReal Topology

noncomputable section

namespace KEBall

local notation "ν[" n "]" => Measure.restrict (volume0 n) (unitBall n)
local notation "𝓓B[" n "]" => 𝓓(dirichletBallOpens n, ℝ)

theorem exists_uniform_dirichletWeakHarnack_constant {n : ℕ} (hn : 2 ≤ n)
    {c K : ℝ} (hc : 0 < c) (hK0 : 0 ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (B : E n → E n →L[ℝ] E n), MemLp B ⊤ ν[n] →
        (∀ᵐ x ∂ν[n], ‖B x‖ ≤ K) →
        (∀ᵐ x ∂ν[n], ∀ v : E n, c * ‖v‖ ^ 2 ≤ inner ℝ (B x v) v) →
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
  let C : ℝ :=
    (DeGiorgi.CWeakHarnack (2 * n) hd /
      (1 - q) ^ (DeGiorgi.weakHarnackDecayExp (2 * n))) ^ (((K / c) ^ 2 + 1) ^ ((1 : ℝ) / 2))
  have hC : 0 ≤ C := Real.rpow_nonneg
    (div_nonneg (zero_le_one.trans (DeGiorgi.one_le_C_weakHarnack hd))
      (Real.rpow_nonneg (sub_nonneg.mpr hq1.le) _)) _
  refine ⟨C, hC, ?_⟩
  intro B hB hBound hEll f F hf hF hWeak hSuper x₀ R hR hSub hPos
  obtain ⟨A, hΛ, hAB⟩ := exists_dirichletDeGiorgi_coefficient_of_bound hB hc hK0 hBound hEll
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
    Real.rpow_one, hInt, Ar, DeGiorgi.EllipticCoeff.restrict, hΛ, C] using h

end KEBall
