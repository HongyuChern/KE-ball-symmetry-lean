import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Complex.Norm
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Proposition 3.1: finite-frame and scalar algebra

Stage05 source draft. NOT compiled and NOT kernel checked.

This independent algebra module proves finite complex Cauchy--Schwarz,
the rank-one norm and defect expansions, the exact product-rule cancellation,
and the scalar logarithmic inequality. It does not identify these finite-frame
quantities with the coordinate-invariant derivatives of `auxiliaryP`.
In particular no whole-paper specification is declared proved here.
-/

set_option autoImplicit false
open scoped BigOperators
noncomputable section

namespace KEBall.AuxiliaryPAlgebra

def vectorNormSq {ι : Type*} [Fintype ι] (v : ι → ℂ) : ℝ :=
  ∑ i, ‖v i‖ ^ 2

def tensorNormSq {ι κ : Type*} [Fintype ι] [Fintype κ]
    (T : ι → κ → ℂ) : ℝ := ∑ j, ∑ i, ‖T i j‖ ^ 2

def contract {ι κ : Type*} [Fintype ι] (T : ι → κ → ℂ)
    (v : ι → ℂ) (j : κ) : ℂ := ∑ i, T i j * star (v i)

theorem vectorNormSq_nonneg {ι : Type*} [Fintype ι] (v : ι → ℂ) :
    0 ≤ vectorNormSq v := Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem tensorNormSq_nonneg {ι κ : Type*} [Fintype ι] [Fintype κ]
    (T : ι → κ → ℂ) : 0 ≤ tensorNormSq T := by
  exact Finset.sum_nonneg (fun _ _ =>
    Finset.sum_nonneg (fun _ _ => sq_nonneg _))

theorem tensorNormSq_eq_zero_iff {ι κ : Type*} [Fintype ι] [Fintype κ]
    (T : ι → κ → ℂ) : tensorNormSq T = 0 ↔ ∀ i j, T i j = 0 := by
  classical
  constructor
  · intro h i j
    have hc : (∑ i, ‖T i j‖ ^ 2) ≤ tensorNormSq T := by
      exact Finset.single_le_sum
        (fun j _ => Finset.sum_nonneg (fun i _ => sq_nonneg ‖T i j‖))
        (Finset.mem_univ j)
    have he : ‖T i j‖ ^ 2 ≤ ∑ i, ‖T i j‖ ^ 2 := by
      exact Finset.single_le_sum (fun i _ => sq_nonneg ‖T i j‖)
        (Finset.mem_univ i)
    have hn : ‖T i j‖ = 0 := by rw [h] at hc; nlinarith [norm_nonneg (T i j)]
    exact norm_eq_zero.mp hn
  · intro h
    simp [tensorNormSq, h]

/-- Complex finite Cauchy--Schwarz, with all quantities explicitly defined. -/
theorem complex_sum_sq_le {ι : Type*} [Fintype ι] (a b : ι → ℂ) :
    ‖∑ i, a i * star (b i)‖ ^ 2 ≤ vectorNormSq a * vectorNormSq b := by
  classical
  have ht : ‖∑ i, a i * star (b i)‖ ≤ ∑ i, ‖a i‖ * ‖b i‖ := by
    calc
      _ ≤ ∑ i, ‖a i * star (b i)‖ := norm_sum_le _ _
      _ = _ := by simp only [norm_mul, norm_star]
  have hc := Finset.sum_mul_sq_le_sq_mul_sq
    (Finset.univ : Finset ι) (fun i => ‖a i‖) (fun i => ‖b i‖)
  have hn : 0 ≤ ‖∑ i, a i * star (b i)‖ := norm_nonneg _
  have hs := mul_nonneg (sub_nonneg.mpr ht)
    (add_nonneg (le_trans hn ht) hn)
  dsimp [vectorNormSq]
  simp only [starRingEnd_apply] at *
  nlinarith

/-- The sharp Hilbert--Schmidt contraction inequality; symmetry is unnecessary. -/
theorem contraction_sq_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    (T : ι → κ → ℂ) (v : ι → ℂ) :
    vectorNormSq (contract T v) ≤ tensorNormSq T * vectorNormSq v := by
  classical
  calc
    _ ≤ ∑ j, vectorNormSq (fun i => T i j) * vectorNormSq v := by
      exact Finset.sum_le_sum (fun j _ => complex_sum_sq_le (fun i => T i j) v)
    _ = _ := by simp only [vectorNormSq, tensorNormSq, Finset.sum_mul]

theorem rank_one_normSq {ι : Type*} [Fintype ι] (v : ι → ℂ) :
    tensorNormSq (fun i j => v i * v j) = vectorNormSq v ^ 2 := by
  classical
  unfold tensorNormSq vectorNormSq
  simp only [norm_mul, mul_pow, ← Finset.sum_mul, ← Finset.mul_sum]
  ring

theorem complex_norm_sq_sub_real_mul (z w : ℂ) (r : ℝ) :
    ‖z - (r : ℂ) * w‖ ^ 2 =
      ‖z‖ ^ 2 - 2 * r * (z * star w).re + r ^ 2 * ‖w‖ ^ 2 := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re,
    Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

def defect {ι : Type*} (S : ι → ι → ℂ) (v : ι → ℂ) (k : ℝ)
    (i j : ι) : ℂ := S i j - ((k⁻¹ : ℝ) : ℂ) * (v i * v j)

def rankOnePairing {ι : Type*} [Fintype ι]
    (S : ι → ι → ℂ) (v : ι → ℂ) : ℝ :=
  ∑ j, ∑ i, (S i j * star (v i * v j)).re

/-- Exact expansion of |S-k⁻¹ v⊗v|² in an orthonormal complex frame. -/
theorem defect_normSq {ι : Type*} [Fintype ι]
    (S : ι → ι → ℂ) (v : ι → ℂ) (k : ℝ) :
    tensorNormSq (defect S v k) = tensorNormSq S -
      2 * k⁻¹ * rankOnePairing S v + k⁻¹ ^ 2 * vectorNormSq v ^ 2 := by
  classical
  have hr := rank_one_normSq v
  unfold tensorNormSq at hr
  unfold tensorNormSq defect rankOnePairing
  simp_rw [complex_norm_sq_sub_real_mul]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hr]

def pValue (e k q : ℝ) : ℝ := e * (1 + q / k)

theorem pValue_sub_weight (e k q : ℝ) : pValue e k q - e = e * q / k := by
  unfold pValue
  ring

/-- Exact scalar product-rule computation using Lq=n+q+s and k=n+1.
Here c is Re⟨S,v⊗v⟩, so Re⟨∂u,∂q⟩=q+c. No LP identity is assumed. -/
theorem product_rule_cancellation (e k n q s c : ℝ) (hk : k ≠ 0)
    (hkn : k = n + 1) :
    e * (-n / k + q / k ^ 2) * (1 + q / k) +
        e / k * (n + q + s) - 2 * e / k ^ 2 * (q + c) =
      e / k * (s - 2 * k⁻¹ * c + k⁻¹ ^ 2 * q ^ 2) := by
  have hn : n = k - 1 := by linarith
  rw [hn]
  field_simp [hk]
  <;> ring

/-- The preceding product-rule expression equals the actual finite-frame
defect norm; this is algebra, not the unproved geometric product rule. -/
theorem product_rule_eq_defect {ι : Type*} [Fintype ι]
    (S : ι → ι → ℂ) (v : ι → ℂ) (e k n : ℝ)
    (hk : k ≠ 0) (hkn : k = n + 1) :
    e * (-n / k + vectorNormSq v / k ^ 2) * (1 + vectorNormSq v / k) +
      e / k * (n + vectorNormSq v + tensorNormSq S) -
        2 * e / k ^ 2 * (vectorNormSq v + rankOnePairing S v) =
      e / k * tensorNormSq (defect S v k) := by
  rw [defect_normSq]
  exact product_rule_cancellation e k n _ _ _ hk hkn

/-- The scalar coefficients in the manuscript's Kato bound agree exactly. -/
theorem kato_factorization (e k q t : ℝ) :
    (e / k) ^ 2 * (t * q) =
      (pValue e k q - e) * (e / k * t) := by
  rw [pValue_sub_weight]
  ring

/-- Finite-frame version of |∂P|²≤(P-E)LP, without geometric placeholders.
Both sides are explicit finite sums and scalar multiplications. -/
theorem kato_inequality {ι κ : Type*} [Fintype ι] [Fintype κ]
    (T : ι → κ → ℂ) (v : ι → ℂ) (e k : ℝ) :
    (e / k) ^ 2 * vectorNormSq (contract T v) ≤
      (pValue e k (vectorNormSq v) - e) * (e / k * tensorNormSq T) := by
  calc
    _ ≤ (e / k) ^ 2 * (tensorNormSq T * vectorNormSq v) :=
      mul_le_mul_of_nonneg_left (contraction_sq_le T v) (sq_nonneg _)
    _ = _ := kato_factorization e k _ _

theorem pValue_gt_one_interior {e k q : ℝ}
    (he : 1 < e) (hk : 0 < k) (hq : 0 ≤ q) : 1 < pValue e k q := by
  have h := mul_nonneg (le_trans (by norm_num) he.le) (div_nonneg hq hk.le)
  unfold pValue
  nlinarith

theorem pValue_gt_one_boundary {k q : ℝ} (hk : 0 < k) (hq : 0 < q) :
    1 < pValue 1 k q := by
  have h := div_pos hq hk
  simp only [pValue, one_mul]
  linarith

/-- Pure scalar lower bound used after the genuine logarithm chain rule. -/
theorem logarithmic_lower_bound {p e a g : ℝ} (hp : 1 < p)
    (hkato : g ≤ (p - e) * a) :
    (e - 1) / (p - 1) ^ 2 * a ≤ a / (p - 1) - g / (p - 1) ^ 2 := by
  have hden : 0 < (p - 1) ^ 2 := sq_pos_of_pos (sub_pos.mpr hp)
  have hp0 : p - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hp)
  have hid : a / (p - 1) - g / (p - 1) ^ 2 -
      (e - 1) / (p - 1) ^ 2 * a = ((p - e) * a - g) / (p - 1) ^ 2 := by
    field_simp [hp0]
    <;> ring
  apply sub_nonneg.mp
  rw [hid]
  exact div_nonneg (sub_nonneg.mpr hkato) hden.le

theorem logarithmic_nonneg {p e a g : ℝ} (hp : 1 < p)
    (he : 1 ≤ e) (ha : 0 ≤ a) (hkato : g ≤ (p - e) * a) :
    0 ≤ a / (p - 1) - g / (p - 1) ^ 2 := by
  apply le_trans _ (logarithmic_lower_bound hp hkato)
  exact mul_nonneg (div_nonneg (sub_nonneg.mpr he) (sq_nonneg _)) ha

/-- Strict E>1 forces the defect to vanish when the scalar log-Laplacian
vanishes. This is pointwise only; the zero-integral-to-pointwise step is open. -/
theorem logarithmic_zero_forces_zero {p e a g : ℝ} (hp : 1 < p)
    (he : 1 < e) (ha : 0 ≤ a) (hkato : g ≤ (p - e) * a)
    (hz : a / (p - 1) - g / (p - 1) ^ 2 = 0) : a = 0 := by
  have hl := logarithmic_lower_bound hp hkato
  rw [hz] at hl
  have hc : 0 < (e - 1) / (p - 1) ^ 2 :=
    div_pos (sub_pos.mpr he) (sq_pos_of_pos (sub_pos.mpr hp))
  nlinarith

/-- The complete pointwise equality conclusion at the finite-frame level.
The remaining geometric consumer must prove that the scalar expression in
`hz` is the actual L log(P-1); this module never assumes that bridge. -/
theorem finite_frame_log_zero {ι κ : Type*} [Fintype ι] [Fintype κ]
    (T : ι → κ → ℂ) (v : ι → ℂ) {e k : ℝ} (he : 1 < e) (hk : 0 < k)
    (hz : (e / k * tensorNormSq T) / (pValue e k (vectorNormSq v) - 1) -
      ((e / k) ^ 2 * vectorNormSq (contract T v)) /
        (pValue e k (vectorNormSq v) - 1) ^ 2 = 0) :
    ∀ i j, T i j = 0 := by
  have he0 : 0 < e := lt_trans (by norm_num) he
  have hscale : 0 < e / k := div_pos he0 hk
  have ha := logarithmic_zero_forces_zero
    (pValue_gt_one_interior he hk (vectorNormSq_nonneg v)) he
    (mul_nonneg hscale.le (tensorNormSq_nonneg T)) (kato_inequality T v e k) hz
  have ht : tensorNormSq T = 0 :=
    (mul_eq_zero.mp ha).resolve_left (ne_of_gt hscale)
  exact (tensorNormSq_eq_zero_iff T).mp ht

end KEBall.AuxiliaryPAlgebra
