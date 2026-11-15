import KEBall.DirichletHessianCampanato
import KEBall.DirichletHessianPathOscillation
import KEBall.DirichletBilinearReconstruction
import KEBall.DirichletHessianSymmetry
import KEBall.DirichletHolderContinuity

/-!
# Continuous local representatives of the full actual real Hessian

Polarization uses the almost-everywhere symmetry of the derivative of the
same first jet, together with the frame's coordinate and pair-sum directions.
The result is an a.e. representative theorem; classical differentiability
of the first jet is a separate subsequent step.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter InnerProductSpace MeasureTheory Metric Set
open scoped BigOperators NNReal

noncomputable section

namespace KEBall

local notation "e[" n "]" => EuclideanSpace.basisFun (Fin (2 * n)) ℝ

set_option maxHeartbeats 1000000 in
theorem exists_dirichlet_continuous_hessian_field_on_ball {n : ℕ}
    {w : E n → ℝ} {G : E n → E n →L[ℝ] ℝ} {L : ℝ≥0}
    (hD : ∀ x ∈ unitBall n, HasFDerivAt w (G x) x)
    (hG : LipschitzOnWith L G (closedUnitBall n))
    (hDecay : HasDirichletHessianOscillationDecay G)
    {x₀ : E n} {R : ℝ} (hR : 0 < R) (hR1 : R ≤ 1)
    (hMargin : closedBall x₀ (2 * R) ⊆ unitBall n) :
    ∃ H : E n → E n →L[ℝ] E n →L[ℝ] ℝ,
      ContinuousOn H (ball x₀ (R / 2)) ∧
      H =ᵐ[(volume : Measure (E n)).restrict (ball x₀ (R / 2))] fderiv ℝ G := by
  obtain ⟨m, v, θ, C, hθ0, hθ1, hC, hBasis, hPairs, hStep⟩ := hDecay
  obtain ⟨α, D, hα0, hα1, hD0, hHolder⟩ :=
    exists_dirichlet_hessian_local_holder_of_step hG v hθ0 hθ1 hC hStep
  choose q hqEq hqHold using hHolder x₀ R hR hR1 hMargin
  have hqC (j : Fin m) : ContinuousOn (q j) (ball x₀ (R / 2)) :=
    continuousOn_of_dirichlet_holder_bound hα0 (hqHold j)
  choose b hb using hBasis
  choose p hp using hPairs
  let a : E n → Fin (2 * n) → Fin (2 * n) → ℝ :=
    fun x i j => (q (p i j) x - q (b i) x - q (b j) x) / 2
  let H : E n → E n →L[ℝ] E n →L[ℝ] ℝ := fun x => dirichletBilinearFromEntries (a x)
  have hHC : ContinuousOn H (ball x₀ (R / 2)) := by
    apply continuousOn_dirichletBilinearFromEntries
    intro i j
    exact (((hqC (p i j)).sub (hqC (b i))).sub (hqC (b j))).div_const 2
  have hSmall : ball x₀ (R / 2) ⊆ ball x₀ R := ball_subset_ball (by linarith)
  have hInside : ball x₀ (R / 2) ⊆ unitBall n :=
    ball_subset_closedBall.trans ((closedBall_subset_closedBall (by linarith)).trans hMargin)
  have hEqAll : ∀ᵐ x ∂(volume : Measure (E n)).restrict (ball x₀ (R / 2)),
      ∀ j : Fin m, q j x = fderiv ℝ G x (v j) (v j) :=
    ae_all_iff.mpr fun j => ae_restrict_of_ae_restrict_of_subset hSmall (hqEq j)
  have hSym := ae_restrict_of_ae_restrict_of_subset hInside
    (ae_dirichlet_firstJet_hessian_symmetric hD hG)
  refine ⟨H, hHC, ?_⟩
  filter_upwards [hEqAll, hSym] with x hxEq hxSym
  have ha (i j : Fin (2 * n)) : a x i j = fderiv ℝ G x (e[n] i) (e[n] j) := by
    dsimp only [a]
    rw [hxEq (p i j), hxEq (b i), hxEq (b j), hp i j, hb i, hb j]
    exact (dirichlet_symmetric_bilinear_polarization (fderiv ℝ G x) hxSym (e[n] i) (e[n] j)).symm
  calc
    H x = dirichletBilinearFromEntries (fun i j => fderiv ℝ G x (e[n] i) (e[n] j)) := by
      exact congrArg dirichletBilinearFromEntries (funext fun i => funext fun j => ha i j)
    _ = fderiv ℝ G x := dirichletBilinearFromEntries_basis _

end KEBall
