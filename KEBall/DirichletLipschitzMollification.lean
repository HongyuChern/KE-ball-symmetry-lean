import KEBall.DirichletInteriorCoefficients
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import PshLines.MollifierApproximation

/-! Mollifying a Lipschitz function differentiates its actual a.e. derivative. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Metric Set
open scoped ContDiff NNReal Topology

noncomputable section

namespace KEBall

theorem fderiv_dirichletTranslationPairing_of_lipschitz {n : ℕ}
    {f ψ : E n → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    (hψ : ContDiff ℝ ∞ ψ) (hψS : HasCompactSupport ψ) (x v : E n) :
    fderiv ℝ (PshLines.translationPairing volume f ψ) x v =
      PshLines.translationPairing volume (fun y => fderiv ℝ f y v) ψ x := by
  let g : E n → ℝ := fun y => ψ (y - x)
  have hg : ContDiff ℝ ∞ g := hψ.comp (contDiff_id.sub contDiff_const)
  have hgS : HasCompactSupport g := by
    simpa [g, Function.comp_def, sub_eq_add_neg] using
      hψS.comp_homeomorph (Homeomorph.addRight (-x))
  obtain ⟨K, hgLip⟩ := exists_lipschitzWith_of_contDiff_hasCompactSupport hg hgS
  have hIBP := hf.integral_lineDeriv_mul_eq (μ := volume) hgLip hgS v
  have hLineG (y : E n) : lineDeriv ℝ g y (-v) = -(fderiv ℝ ψ (y - x) v) := by
    have hd := (hψ.differentiable (by simp) (y - x)).hasFDerivAt.comp y
      ((hasFDerivAt_id y).sub_const x)
    have hd' : HasFDerivAt g (fderiv ℝ ψ (y - x)) y := by
      simpa only [Function.comp_def, id_eq, ContinuousLinearMap.comp_id] using hd
    rw [(hd'.hasLineDerivAt (-v)).lineDeriv, map_neg]
  have hLineF : (fun y => lineDeriv ℝ f y v) =ᵐ[volume] fun y => fderiv ℝ f y v := by
    filter_upwards [hf.ae_differentiableAt (μ := volume)] with y hy
    exact (hy.hasFDerivAt.hasLineDerivAt v).lineDeriv
  simp only [hLineG, neg_mul, integral_neg] at hIBP
  rw [PshLines.fderiv_translationPairing hf.continuous.locallyIntegrable hψS (hψ.of_le (by simp))]
  calc
    _ = ∫ y, lineDeriv ℝ f y v * g y := by
      simpa only [PshLines.translationPairing, mul_comm] using hIBP.symm
    _ = PshLines.translationPairing volume (fun y => fderiv ℝ f y v) ψ x := by
      apply integral_congr_ae
      filter_upwards [hLineF] with y hy
      change lineDeriv ℝ f y v * g y = fderiv ℝ f y v * ψ (y - x)
      rw [hy]

theorem fderiv_dirichlet_mollify_of_lipschitz {n : ℕ}
    {f : E n → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    (φ : ContDiffBump (0 : E n)) (x v : E n) :
    fderiv ℝ (PshLines.mollify volume f φ) x v =
      PshLines.mollify volume (fun y => fderiv ℝ f y v) φ x :=
  fderiv_dirichletTranslationPairing_of_lipschitz hf φ.contDiff_normed φ.hasCompactSupport_normed x v

end KEBall
