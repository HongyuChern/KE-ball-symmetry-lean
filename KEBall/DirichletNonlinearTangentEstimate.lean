import KEBall.DirichletNonlinearAngularEstimate
import Mathlib.Algebra.Order.Chebyshev

/-! Third derivative estimates with a tangential argument on an annulus. -/

set_option autoImplicit false
set_option maxSynthPendingDepth 8

open Filter InnerProductSpace MeasureTheory Metric Set
open scoped ComplexOrder ContDiff

namespace KEBall

local notation "e[" n "]" => EuclideanSpace.basisFun (Fin (2 * n)) ℝ

theorem exists_integral_sq_realThirdDerivative_tangent_le {n : ℕ} (hn : 0 < n)
    {a b D L : ℝ} (ha : 0 < a) (hb : 0 < b) (hD : 0 < D) (hL : 0 ≤ L) :
    ∃ C ≥ (0 : ℝ), ∀ {u f : E n → ℝ},
      SmoothNear (closedUnitBall n) u → SmoothNear (closedUnitBall n) f →
      (∀ x ∈ unitSphere n, u x = 0) →
      (∀ x ∈ unitBall n, (complexHessian u x).PosDef) →
      (∀ x ∈ unitBall n, (complexHessian u x).det.re = f x) →
      (∀ x ∈ unitBall n, a ^ n ≤ f x ∧ f x ≤ b ^ n) →
      (∀ x ∈ closedUnitBall n, ‖fderiv ℝ f x‖ ≤ L) →
      (∀ x ∈ closedUnitBall n, ∀ w : E n, ‖w‖ = 1 → |realHessian u x w w| ≤ D) →
      ∀ i : Fin (2 * n),
      (∫ x in unitBall n, ∑ j, ∑ k,
        (realThirdDerivative u x (‖x‖ ^ 2 • e[n] i - inner ℝ (e[n] i) x • x)
          (e[n] j) (e[n] k)) ^ 2 ∂volume0 n) ≤ C := by
  obtain ⟨K, hK, hEst⟩ := exists_integral_sq_realThirdDerivative_angular_le hn ha hb hD hL
  let M : ℝ := (2 * n : ℝ)
  let C := 2 * (M ^ 2 * (K * 4 ^ 2)) + 2 * K
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro u f hu hf hu0 huP huEq hDen hGrad hBound i
  let μ := (volume0 n).restrict (unitBall n)
  let b := e[n]
  let R (l : Fin (2 * n)) := dirichletUnitaryRotation (b i) (b l)
  let T := realThirdDerivative u
  let q (l : Fin (2 * n)) (x : E n) := ∑ j, ∑ k, (T x (R l x) (b j) (b k)) ^ 2
  let r (x : E n) := ∑ j, ∑ k, (T x (J x) (b j) (b k)) ^ 2
  let W (x : E n) := ‖x‖ ^ 2 • b i - inner ℝ (b i) x • x
  let p (x : E n) := ∑ j, ∑ k, (T x (W x) (b j) (b k)) ^ 2
  obtain ⟨U, hU, hSub, huU⟩ := hu
  have hu : SmoothNear (closedUnitBall n) u := ⟨U, hU, hSub, huU⟩
  have hD₁ := huU.fderiv_of_isOpen hU (m := ∞) (by simp)
  have hD₂ := hD₁.fderiv_of_isOpen hU (m := ∞) (by simp)
  have hT : ContDiffOn ℝ ∞ T U := hD₂.fderiv_of_isOpen hU (m := ∞) (by simp)
  have hC {V : E n → E n} (hV : Continuous V) :
      ContinuousOn (fun x => ∑ j, ∑ k, (T x (V x) (b j) (b k)) ^ 2) U :=
    continuousOn_finsetSum Finset.univ fun j _ => continuousOn_finsetSum Finset.univ fun k _ =>
      (((hT.continuousOn.clm_apply hV.continuousOn).clm_apply continuousOn_const).clm_apply
        continuousOn_const).pow 2
  have hQ (l : Fin (2 * n)) : ContinuousOn (q l) U := hC (R l).continuous
  have hR : ContinuousOn r U := by
    apply hC
    simpa only [JCLM_coe] using (JCLM n).continuous
  have hP : ContinuousOn p U := hC (((continuous_norm.pow 2).smul continuous_const).sub
    ((innerSL ℝ (b i)).continuous.smul continuous_id))
  have hI {F : E n → ℝ} (hF : ContinuousOn F U) : Integrable F μ :=
    (hF.mono hSub).integrableOn_of_subset_isCompact (isCompact_closedBall _ _)
      measurableSet_ball ball_subset_closedBall (by rw [volume0_unitBall n hn]; exact ENNReal.one_ne_top)
  have hJNorm : ‖JCLM n‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro y
    rw [JCLM_apply, norm_J, one_mul]
  have hRotNorm (l : Fin (2 * n)) : ‖R l‖ ≤ 4 := by
    unfold R dirichletUnitaryRotation
    have h (z y : E n) (hz : ‖z‖ = 1) (hy : ‖y‖ = 1) : ‖dirichletPlaneRotation z y‖ ≤ 2 := by
      unfold dirichletPlaneRotation
      exact (norm_sub_le _ _).trans (by rw [norm_rankOne, norm_rankOne, hz, hy]; norm_num)
    exact (norm_add_le _ _).trans ((add_le_add (h _ _ (b.orthonormal.norm_eq_one i)
      (b.orthonormal.norm_eq_one l)) (h _ _ (by rw [norm_J, b.orthonormal.norm_eq_one])
      (by rw [norm_J, b.orthonormal.norm_eq_one]))).trans_eq (by norm_num))
  have hQInt (l : Fin (2 * n)) : (∫ x, q l x ∂μ) ≤ K * 4 ^ 2 :=
    (hEst hu hf hu0 huP huEq hDen hGrad hBound (R l) (dirichletUnitaryRotation_star _ _)
      (dirichletUnitaryRotation_J _ _)).trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hRotNorm l) 2) hK)
  have hRInt : (∫ x, r x ∂μ) ≤ K := by
    have h := hEst hu hf hu0 huP huEq hDen hGrad hBound (JCLM n) (JCLM_star n)
      (fun x => by simp only [JCLM_apply])
    simp only [JCLM_apply] at h
    exact h.trans ((mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) hJNorm 2) hK).trans_eq (by simp))
  have hPoint : p ≤ᵐ[μ] fun x => 2 * M * (∑ l, q l x) + 2 * r x := by
    filter_upwards [ae_restrict_mem (μ := volume0 n) (show MeasurableSet (unitBall n) from measurableSet_ball)]
      with x hx
    have hxN : ‖x‖ ≤ 1 := (mem_ball_zero_iff.mp hx).le
    have hCoeff (z : E n) (hz : ‖z‖ = 1) : |inner ℝ z x| ≤ 1 := by
      rw [← Real.norm_eq_abs]
      exact (norm_inner_le_norm _ _).trans (by rwa [hz, one_mul])
    have hSq (z : E n) (hz : ‖z‖ = 1) (s : ℝ) :
        (inner ℝ z x * s) ^ 2 ≤ s ^ 2 := by
      rw [mul_pow, ← sq_abs (inner ℝ z x)]
      exact mul_le_of_le_one_left (sq_nonneg _)
        (by simpa only [one_pow] using pow_le_pow_left₀ (abs_nonneg _) (hCoeff z hz) 2)
    have hEntry (j k : Fin (2 * n)) :
        (T x (W x) (b j) (b k)) ^ 2 ≤
          2 * M * (∑ l, (T x (R l x) (b j) (b k)) ^ 2) + 2 * (T x (J x) (b j) (b k)) ^ 2 := by
      let S := ∑ l, inner ℝ (b l) x * T x (R l x) (b j) (b k)
      let A := inner ℝ (J (b i)) x * T x (J x) (b j) (b k)
      have hE : T x (W x) (b j) (b k) = S + A := by
        rw [show W x = _ from (sum_dirichletUnitaryRotation_eq_tangentProjection b (b i) x).symm]
        simp only [map_add, map_sum, map_smul, _root_.add_apply, _root_.smul_apply, sum_apply,
          smul_eq_mul, S, A, R]
      have hS : S ^ 2 ≤ M * ∑ l, (T x (R l x) (b j) (b k)) ^ 2 := by
        dsimp only [S, M]
        have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin (2 * n))))
          (f := fun l => inner ℝ (b l) x * T x (R l x) (b j) (b k))
        simp only [Finset.card_univ, Fintype.card_fin, Nat.cast_mul, Nat.cast_ofNat] at h
        exact h.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun l _ =>
          hSq (b l) (b.orthonormal.norm_eq_one l) _) (by positivity))
      have hA : A ^ 2 ≤ (T x (J x) (b j) (b k)) ^ 2 :=
        hSq (J (b i)) (by rw [norm_J, b.orthonormal.norm_eq_one]) _
      rw [hE]
      nlinarith only [hS, hA, sq_nonneg (S - A)]
    calc
      p x ≤ ∑ j, ∑ k, (2 * M * (∑ l, (T x (R l x) (b j) (b k)) ^ 2) +
          2 * (T x (J x) (b j) (b k)) ^ 2) :=
        Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => hEntry j k
      _ = _ := by
        simp only [q, r, Finset.sum_add_distrib, ← Finset.mul_sum]
        congr 2
        calc
          (∑ j, ∑ k, ∑ l, (T x (R l x) (b j) (b k)) ^ 2) =
              ∑ j, ∑ l, ∑ k, (T x (R l x) (b j) (b k)) ^ 2 := by
            exact Finset.sum_congr rfl fun j _ => Finset.sum_comm
          _ = ∑ l, ∑ j, ∑ k, (T x (R l x) (b j) (b k)) ^ 2 := Finset.sum_comm
  have hSumC : ContinuousOn (fun x => ∑ l, q l x) U :=
    continuousOn_finsetSum Finset.univ fun l _ => hQ l
  have h := integral_mono_ae (hI hP) (((hI hSumC).const_mul (2 * M)).add ((hI hR).const_mul 2)) hPoint
  change (∫ x, p x ∂μ) ≤ (∫ x, 2 * M * (∑ l, q l x) + 2 * r x ∂μ) at h
  rw [integral_add ((hI hSumC).const_mul _) ((hI hR).const_mul _), integral_const_mul,
    integral_const_mul, integral_finsetSum _ (fun l _ => hI (hQ l))] at h
  refine h.trans ((add_le_add (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun l _ => hQInt l)
    (by dsimp [M]; positivity)) (mul_le_mul_of_nonneg_left hRInt (show (0 : ℝ) ≤ 2 by norm_num))).trans_eq ?_)
  simp only [C, M, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_mul, Nat.cast_ofNat]
  ring

end KEBall
