import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases

/-! Constant-coordinate Wirtinger derivatives. The cofactor result below is
dimension TWO only; the all-dimensional Piola identity remains an obligation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff

namespace KEBallProbe
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def rd (v : E) (f : E → ℂ) (x : E) : ℂ := fderiv ℝ f x v

noncomputable def dz (a b : E) (f : E → ℂ) (x : E) : ℂ :=
  (2 : ℂ)⁻¹ * (rd a f x - Complex.I * rd b f x)

lemma smooth_rd {f : E → ℂ} (hf : ContDiff ℝ ∞ f) (v : E) :
    ContDiff ℝ ∞ (rd v f) := by
  exact (hf.fderiv_right (by simp)).clm_apply contDiff_const

lemma smooth_dz {f : E → ℂ} (hf : ContDiff ℝ ∞ f) (a b : E) :
    ContDiff ℝ ∞ (dz a b f) := by
  exact contDiff_const.mul ((smooth_rd hf a).sub (contDiff_const.mul (smooth_rd hf b)))

lemma rd_const_mul {f : E → ℂ} (hf : ContDiff ℝ ∞ f) (v : E) (c : ℂ) (x : E) :
    rd v (fun y => c * f y) x = c * rd v f x := by
  simp [rd, fderiv_const_mul (hf.differentiable (by simp) x)]

lemma rd_sub {f h : E → ℂ} (hf : ContDiff ℝ ∞ f) (hh : ContDiff ℝ ∞ h)
    (v x : E) : rd v (fun y => f y - h y) x = rd v f x - rd v h x := by
  simp [rd, fderiv_fun_sub (hf.differentiable (by simp) x) (hh.differentiable (by simp) x)]

lemma rd_rd {f : E → ℂ} (hf : ContDiff ℝ ∞ f) (a b x : E) :
    rd a (rd b f) x = fderiv ℝ (fderiv ℝ f) x a b := by
  unfold rd
  have hdf : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  rw [fderiv_clm_apply (hdf.differentiable (by simp) x)
    (differentiableAt_const b)]
  simp

lemma rd_comm {f : E → ℂ} (hf : ContDiff ℝ ∞ f) (a b x : E) :
    rd a (rd b f) x = rd b (rd a f) x := by
  rw [rd_rd hf, rd_rd hf]
  exact (hf.contDiffAt.isSymmSndFDerivAt (by simp; norm_cast)).eq a b

lemma rd_dz {f : E → ℂ} (hf : ContDiff ℝ ∞ f) (v a b x : E) :
    rd v (dz a b f) x = (2 : ℂ)⁻¹ *
      (rd v (rd a f) x - Complex.I * rd v (rd b f) x) := by
  unfold dz
  rw [rd_const_mul ((smooth_rd hf a).sub (contDiff_const.mul (smooth_rd hf b))),
    rd_sub (smooth_rd hf a) (contDiff_const.mul (smooth_rd hf b)),
    rd_const_mul (smooth_rd hf b)]

theorem dz_comm {f : E → ℂ} (hf : ContDiff ℝ ∞ f) (a b c d x : E) :
    dz a b (dz c d f) x = dz c d (dz a b f) x := by
  change (2 : ℂ)⁻¹ * (rd a (dz c d f) x - Complex.I * rd b (dz c d f) x) =
    (2 : ℂ)⁻¹ * (rd c (dz a b f) x - Complex.I * rd d (dz a b f) x)
  rw [rd_dz hf, rd_dz hf, rd_dz hf, rd_dz hf]
  rw [rd_comm hf a c, rd_comm hf a d, rd_comm hf b c, rd_comm hf b d]
  ring

lemma dz_neg (f : E → ℂ) (a b x : E) :
    dz a b (fun y => -f y) x = -dz a b f x := by
  simp [dz, rd]
  ring

/-- The paper's convention is `det(g) * g^{i bar j} = adjugate(g) j i`.
This theorem proves divergence of those cofactor columns in complex dimension 2,
from an actual C-infinity potential and actual real Frechet derivatives. -/
theorem cofactor_divergence_dim_two {f : E → ℂ} (hf : ContDiff ℝ ∞ f)
    (a b : Fin 2 → E) (j : Fin 2) (x : E) :
    let H : E → Matrix (Fin 2) (Fin 2) ℂ := fun y i k =>
      dz (a i) (b i) (dz (a k) (-b k) f) y
    (∑ i : Fin 2, dz (a i) (b i) (fun y => (H y).adjugate j i) x) = 0 := by
  dsimp only
  fin_cases j
  · simp only [Fin.sum_univ_two, Matrix.adjugate_fin_two]
    change dz (a 0) (b 0) (dz (a 1) (b 1) (dz (a 1) (-b 1) f)) x +
      dz (a 1) (b 1) (fun y => -dz (a 0) (b 0) (dz (a 1) (-b 1) f) y) x = 0
    rw [dz_neg, dz_comm (smooth_dz hf (a 1) (-b 1))]
    ring
  · simp only [Fin.sum_univ_two, Matrix.adjugate_fin_two]
    change dz (a 0) (b 0) (fun y => -dz (a 1) (b 1) (dz (a 0) (-b 0) f) y) x +
      dz (a 1) (b 1) (dz (a 0) (b 0) (dz (a 0) (-b 0) f)) x = 0
    rw [dz_neg, dz_comm (smooth_dz hf (a 0) (-b 0))]
    ring

#print axioms dz_comm
#print axioms cofactor_divergence_dim_two
end KEBallProbe
