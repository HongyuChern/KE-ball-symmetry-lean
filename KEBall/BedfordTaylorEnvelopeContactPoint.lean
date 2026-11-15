import KEBall.BedfordTaylorObstacleMaximality
import Mathlib.Analysis.Matrix.Order

/-!
# Degeneracy of a quadratic model away from contact
-/

set_option autoImplicit false

open Filter Metric Set TopologicalSpace
open scoped ComplexOrder ContDiff Matrix Topology

namespace KEBall.BedfordTaylor

open PshLines.FirstPass (ComplexModel)
open PshLines.FirstPass.MongeAmpere
  (IsLocallyBoundedPshOn complexHessian_add complexHessian_smul complexHessian_norm_sq)

local notation "modelHessian" => PshLines.FirstPass.MongeAmpere.complexHessian

theorem posSemidef_of_tendsto_of_isHermitian {n : ℕ}
    {H : Matrix (Fin n) (Fin n) ℂ} {Hj : ℕ → Matrix (Fin n) (Fin n) ℂ}
    (hH : H.IsHermitian) (hlim : Tendsto Hj atTop (𝓝 H))
    (hpsd : ∀ j, (Hj j).PosSemidef) : H.PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hH
  intro v
  have hc : Continuous (fun M : Matrix (Fin n) (Fin n) ℂ => star v ⬝ᵥ (M *ᵥ v)) :=
    continuous_const.dotProduct (continuous_id.matrix_mulVec continuous_const)
  have h := (hc.tendsto H).comp hlim
  rw [Complex.nonneg_iff]
  refine ⟨ge_of_tendsto ((Complex.continuous_re.tendsto _).comp h)
    (Eventually.of_forall fun j => (Complex.nonneg_iff.mp ((hpsd j).dotProduct_mulVec_nonneg v)).1), ?_⟩
  have hzero : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0) := tendsto_const_nhds
  have him : Tendsto (fun j => (star v ⬝ᵥ (Hj j *ᵥ v)).im) atTop (𝓝 0) :=
    hzero.congr fun j => (Complex.nonneg_iff.mp ((hpsd j).dotProduct_mulVec_nonneg v)).2
  exact tendsto_nhds_unique him ((Complex.continuous_im.tendsto _).comp h)

private theorem exists_posSemidef_sub_scalar_one {n : ℕ} (hn : 0 < n)
    {M : Matrix (Fin n) (Fin n) ℂ} (hM : M.PosDef) :
    ∃ c : ℝ, 0 < c ∧ (M - (c : ℂ) • 1).PosSemidef := by
  let H := hM.isHermitian
  let U := H.eigenvectorUnitary
  let D := Matrix.diagonal (fun i => (H.eigenvalues i : ℂ))
  let F := Unitary.conjStarAlgAut ℂ _ U
  have hF : F D = M := H.spectral_theorem.symm
  obtain ⟨i, _, hi⟩ := Finset.exists_min_image Finset.univ H.eigenvalues
    ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  let c := H.eigenvalues i / 2
  have hc : 0 < c := half_pos (hM.eigenvalues_pos i)
  have hc' (j : Fin n) : c ≤ H.eigenvalues j :=
    (half_le_self (hM.eigenvalues_pos i).le).trans (hi j (Finset.mem_univ j))
  have hD : D - (c : ℂ) • 1 =
      Matrix.diagonal (fun j => ((H.eigenvalues j - c : ℝ) : ℂ)) := by
    ext j k
    by_cases he : j = k
    · subst k
      simp [D, Matrix.diagonal_apply_eq]
    · simp [D, Matrix.diagonal_apply_ne _ he, Matrix.one_apply_ne he]
  have hdiag : (D - (c : ℂ) • 1).PosSemidef := by
    rw [hD]
    exact Matrix.PosSemidef.diagonal fun j => by
      change (0 : ℂ) ≤ ((H.eigenvalues j - c : ℝ) : ℂ)
      exact_mod_cast sub_nonneg.mpr (hc' j)
  have hI : F ((c : ℂ) • 1) = (c : ℂ) • 1 := by simp [F]
  refine ⟨c, hc, ?_⟩
  rw [← hF, ← hI, ← map_sub]
  change ((U : Matrix (Fin n) (Fin n) ℂ) * (D - (c : ℂ) • 1) *
    (U : Matrix (Fin n) (Fin n) ℂ)ᴴ).PosSemidef
  exact hdiag.mul_mul_conjTranspose_same _

private theorem complexHessian_sub_centered_quadratic {n : ℕ}
    {q : ComplexModel n → ℝ} (hq : ContDiff ℝ ∞ q) (x y : ComplexModel n) (c : ℝ) :
    modelHessian (fun z => q z - c * ‖z - x‖ ^ 2) y = modelHessian q y - (c : ℂ) • 1 := by
  let s (z : ComplexModel n) := ‖z - x‖ ^ 2
  have hs : ContDiff ℝ 2 s := (contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)
  have hss : modelHessian s y = 1 := by
    rw [← complexHessian_norm_sq (y - x)]
    have htr := iteratedFDeriv_comp_sub (𝕜 := ℝ) (f := fun z : ComplexModel n => ‖z‖ ^ 2) 2 x y
    funext i j
    simp only [PshLines.FirstPass.MongeAmpere.complexHessian, PshLines.realHessian, s, htr]
  have he : (fun z => q z - c * ‖z - x‖ ^ 2) = q + (-c) • s := by
    funext z
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, neg_mul, s, sub_eq_add_neg]
  have hq' : ContDiffAt ℝ 2 q y := hq.contDiffAt.of_le
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hs' : ContDiffAt ℝ 2 ((-c) • s) y := (hs.const_smul (-c)).contDiffAt
  rw [he, complexHessian_add hq' hs', complexHessian_smul hs.contDiffAt, hss,
    Complex.ofReal_neg, neg_smul, sub_eq_add_neg]

/-- At an off-contact point, a semipositive quadratic Taylor model of the
greatest PSH minorant has vanishing determinant. -/
theorem det_eq_zero_of_quadratic_expansion_off_contact
    {n : ℕ} (hn : 0 < n) {Ω : Opens (ComplexModel n)} {v f q : ComplexModel n → ℝ}
    (hv : IsLocallyBoundedPshOn Ω v) (hvf : ∀ y ∈ Ω, v y ≤ f y)
    (hgreatest : ∀ w : ComplexModel n → ℝ, IsLocallyBoundedPshOn Ω w →
      (∀ y ∈ Ω, w y ≤ f y) → ∀ y ∈ Ω, w y ≤ v y)
    {x : ComplexModel n} (hx : x ∈ Ω) (hf : ContinuousAt f x) (hgap : v x < f x)
    (hq : ContDiff ℝ ∞ q) (heq : q x = v x)
    (hH : ∀ y, modelHessian q y = modelHessian q x)
    (hpsd : (modelHessian q x).PosSemidef)
    (hrem : ∀ ε : ℝ, 0 < ε → ∀ᶠ h in 𝓝 (0 : ComplexModel n), |v (x + h) - q (x + h)| ≤ ε * ‖h‖ ^ 2) :
    (modelHessian q x).det = 0 := by
  by_contra hdet
  have hpos := hpsd.posDef_iff_det_ne_zero.mpr hdet
  obtain ⟨δ, hδ, hδH⟩ := exists_posSemidef_sub_scalar_one hn hpos
  let c := δ / 2
  have hc : 0 < c := half_pos hδ
  let w (y : ComplexModel n) := q y - c * ‖y - x‖ ^ 2
  have hw : ContDiff ℝ ∞ w := hq.sub (contDiff_const.mul
    ((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)))
  have hwx : w x = v x := by simp [w, heq]
  have hlt : ∀ᶠ y in 𝓝 x, w y ≤ v y := by
    have hs : Continuous (fun y : ComplexModel n => y - x) := continuous_id.sub continuous_const
    have ht : Tendsto (fun y : ComplexModel n => y - x) (𝓝 x) (𝓝 0) := by
      simpa only [sub_self] using (hs.continuousAt (x := x)).tendsto
    filter_upwards [ht.eventually (hrem c hc)] with y hy
    have he : x + (y - x) = y := by abel
    rw [he] at hy
    dsimp only [w]
    linarith only [(abs_le.mp hy).1]
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
    ((show ∀ᶠ y in 𝓝 x, y ∈ Ω from Ω.isOpen.mem_nhds hx).and hlt)
  let W : Opens (ComplexModel n) := ⟨ball x r, isOpen_ball⟩
  have hW : W ≤ Ω := fun _ hy => (hball hy).1
  have hPSH : IsLocallyBoundedPshOn W (fun y => w y - c * ‖y - x‖ ^ 2) := by
    apply isLocallyBoundedPshOn_of_isSmoothPshOn
    apply isSmoothPshOn_of_coordinateHessian
    · exact (hw.sub (contDiff_const.mul ((contDiff_norm_sq ℝ).comp
        (contDiff_id.sub contDiff_const)))).contDiffOn
    · intro y _
      have he : (fun y => w y - c * ‖y - x‖ ^ 2) = fun y => q y - δ * ‖y - x‖ ^ 2 := by
        funext z
        dsimp only [w, c]
        ring
      rw [he, complexHessian_sub_centered_quadratic hq, hH]
      exact hδH
  exact no_strictly_psh_lower_touch_off_contact hv
    (fun y hy => EReal.coe_le_coe_iff.mpr (hvf y hy))
    (fun u hu huf => hgreatest u hu fun y hy => EReal.coe_le_coe_iff.mp (huf y hy))
    (show x ∈ W from mem_ball_self hr) hW (EReal.coe_lt_coe_iff.mpr hgap)
    (continuous_coe_real_ereal.continuousAt.comp hf) hw.continuous.continuousAt
    (fun y hy => (hball hy).2) hwx hc hPSH

end KEBall.BedfordTaylor
