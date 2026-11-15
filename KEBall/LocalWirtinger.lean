import KEBallProbe.WirtingerCofactor

/-!
# Local constant-direction complex differentiation

All operators are the actual real Frechet derivatives from the inherited probe.
The hypotheses in this module are local at a point or on an open set.
No extension to a globally smooth potential is assumed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff

namespace KEBall
open KEBallProbe

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma smoothAt_rd {f : E → ℂ} {x : E} (hf : ContDiffAt ℝ ∞ f x) (v : E) :
    ContDiffAt ℝ ∞ (rd v f) x := by
  exact (hf.fderiv_right (by simp)).clm_apply contDiffAt_const

lemma smoothAt_dz {f : E → ℂ} {x : E} (hf : ContDiffAt ℝ ∞ f x) (a b : E) :
    ContDiffAt ℝ ∞ (dz a b f) x := by
  exact contDiffAt_const.mul
    ((smoothAt_rd hf a).sub (contDiffAt_const.mul (smoothAt_rd hf b)))

lemma rd_const_mul_at {f : E → ℂ} {x : E} (hf : ContDiffAt ℝ ∞ f x)
    (v : E) (c : ℂ) :
    rd v (fun y => c * f y) x = c * rd v f x := by
  simp [rd, fderiv_const_mul (hf.differentiableAt (by simp))]

lemma rd_sub_at {f h : E → ℂ} {x : E}
    (hf : ContDiffAt ℝ ∞ f x) (hh : ContDiffAt ℝ ∞ h x) (v : E) :
    rd v (fun y => f y - h y) x = rd v f x - rd v h x := by
  simp [rd, fderiv_fun_sub (hf.differentiableAt (by simp))
    (hh.differentiableAt (by simp))]

lemma rd_rd_at {f : E → ℂ} {x : E} (hf : ContDiffAt ℝ ∞ f x) (a b : E) :
    rd a (rd b f) x = fderiv ℝ (fderiv ℝ f) x a b := by
  unfold rd
  have hdf : ContDiffAt ℝ ∞ (fderiv ℝ f) x := hf.fderiv_right (by simp)
  rw [fderiv_clm_apply (hdf.differentiableAt (by simp))
    (differentiableAt_const b)]
  simp

lemma rd_comm_at {f : E → ℂ} {x : E} (hf : ContDiffAt ℝ ∞ f x) (a b : E) :
    rd a (rd b f) x = rd b (rd a f) x := by
  rw [rd_rd_at hf, rd_rd_at hf]
  exact (hf.isSymmSndFDerivAt (by simp; norm_cast)).eq a b

lemma rd_dz_at {f : E → ℂ} {x : E} (hf : ContDiffAt ℝ ∞ f x) (v a b : E) :
    rd v (dz a b f) x = (2 : ℂ)⁻¹ *
      (rd v (rd a f) x - Complex.I * rd v (rd b f) x) := by
  unfold dz
  rw [rd_const_mul_at ((smoothAt_rd hf a).sub
      (contDiffAt_const.mul (smoothAt_rd hf b))),
    rd_sub_at (smoothAt_rd hf a) (contDiffAt_const.mul (smoothAt_rd hf b)),
    rd_const_mul_at (smoothAt_rd hf b)]

/-- Commutation is a local fact; no global smoothness is used. -/
theorem dz_comm_at {f : E → ℂ} {x : E} (hf : ContDiffAt ℝ ∞ f x)
    (a b c d : E) :
    dz a b (dz c d f) x = dz c d (dz a b f) x := by
  change (2 : ℂ)⁻¹ * (rd a (dz c d f) x - Complex.I * rd b (dz c d f) x) =
    (2 : ℂ)⁻¹ * (rd c (dz a b f) x - Complex.I * rd d (dz a b f) x)
  rw [rd_dz_at hf, rd_dz_at hf, rd_dz_at hf, rd_dz_at hf]
  rw [rd_comm_at hf a c, rd_comm_at hf a d, rd_comm_at hf b c, rd_comm_at hf b d]
  ring

lemma smoothOn_rd {f : E → ℂ} {U : Set E} (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) (v : E) : ContDiffOn ℝ ∞ (rd v f) U := by
  intro x hx
  exact (smoothAt_rd (hf.contDiffAt (hU.mem_nhds hx)) v).contDiffWithinAt

lemma smoothOn_dz {f : E → ℂ} {U : Set E} (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) (a b : E) : ContDiffOn ℝ ∞ (dz a b f) U := by
  intro x hx
  exact (smoothAt_dz (hf.contDiffAt (hU.mem_nhds hx)) a b).contDiffWithinAt

theorem dz_comm_on {f : E → ℂ} {U : Set E} (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) (a b c d : E) {x : E} (hx : x ∈ U) :
    dz a b (dz c d f) x = dz c d (dz a b f) x := by
  exact dz_comm_at (hf.contDiffAt (hU.mem_nhds hx)) a b c d

/-- The mixed third-derivative identity used in arbitrary-dimensional Piola. -/
theorem complex_hessian_third_comm_at {f : E → ℂ} {x : E}
    (hf : ContDiffAt ℝ ∞ f x) (a b c d e k : E) :
    dz a b (dz c d (dz e (-k) f)) x =
      dz c d (dz a b (dz e (-k) f)) x := by
  exact dz_comm_at (smoothAt_dz hf e (-k)) a b c d

end KEBall
