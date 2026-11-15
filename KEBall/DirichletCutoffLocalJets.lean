import DifferentialGeometry.Analysis.Schauder.Cutoff.Bounds.SecondJet

/-!
# Cutoff jets require differentiability only on the cutoff support

Outside the closed support, the cutoff and all its actual derivatives
vanish locally.  Thus arbitrary bounded continuous extensions of the
local jets produce genuine global jets after multiplication by the cutoff.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Set
open DifferentialGeometry.Analysis.Schauder

namespace KEBall

variable {V F : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem dirichlet_tsupport_cutoffValue_subset
    (χ : BoundedContinuousFunction V ℝ) (u : BoundedContinuousFunction V F) :
    tsupport (cutoffValue χ u : V → F) ⊆ tsupport (χ : V → ℝ) := by
  apply closure_minimal _ isClosed_closure
  intro x hx
  by_contra h
  exact hx (by simp only [cutoffValue_apply, image_eq_zero_of_notMem_tsupport h, zero_smul])

theorem dirichlet_tsupport_cutoffJet1_subset
    (χ : BoundedContinuousFunction V ℝ)
    (Dχ : BoundedContinuousFunction V (V →L[ℝ] ℝ))
    (u : BoundedContinuousFunction V F) (Du : BoundedContinuousFunction V (V →L[ℝ] F))
    (hχ : ∀ x, HasFDerivAt (χ : V → ℝ) (Dχ x) x) :
    tsupport (cutoffJet1 χ Dχ u Du : V → V →L[ℝ] F) ⊆ tsupport (χ : V → ℝ) := by
  apply closure_minimal _ isClosed_closure
  intro x hx
  by_contra h
  have hD : Dχ x = 0 := (hχ x).unique (HasFDerivAt.of_notMem_tsupport ℝ h)
  exact hx (by simp [cutoffJet1_apply, image_eq_zero_of_notMem_tsupport h, hD])

theorem dirichlet_cutoffValue_hasFDerivAt_of_local
    (χ : BoundedContinuousFunction V ℝ)
    (Dχ : BoundedContinuousFunction V (V →L[ℝ] ℝ))
    (u : BoundedContinuousFunction V F) (Du : BoundedContinuousFunction V (V →L[ℝ] F))
    (hχ : ∀ x, HasFDerivAt (χ : V → ℝ) (Dχ x) x)
    (hu : ∀ x ∈ tsupport (χ : V → ℝ), HasFDerivAt (u : V → F) (Du x) x)
    (x : V) :
    HasFDerivAt (cutoffValue χ u : V → F) (cutoffJet1 χ Dχ u Du x) x := by
  by_cases hx : x ∈ tsupport (χ : V → ℝ)
  · exact (hχ x).smul (hu x hx)
  · have hD : Dχ x = 0 := (hχ x).unique (HasFDerivAt.of_notMem_tsupport ℝ hx)
    have h0 : HasFDerivAt (cutoffValue χ u : V → F) 0 x :=
      HasFDerivAt.of_notMem_tsupport ℝ (fun h => hx (dirichlet_tsupport_cutoffValue_subset χ u h))
    simpa [cutoffJet1_apply, image_eq_zero_of_notMem_tsupport hx, hD] using h0

theorem dirichlet_cutoffJet1_hasFDerivAt_of_local
    (χ : BoundedContinuousFunction V ℝ)
    (Dχ : BoundedContinuousFunction V (V →L[ℝ] ℝ))
    (Hχ : BoundedContinuousFunction V (V →L[ℝ] V →L[ℝ] ℝ))
    (u : BoundedContinuousFunction V F)
    (Du : BoundedContinuousFunction V (V →L[ℝ] F))
    (Hu : BoundedContinuousFunction V (V →L[ℝ] V →L[ℝ] F))
    (hχ : ∀ x, HasFDerivAt (χ : V → ℝ) (Dχ x) x)
    (hDχ : ∀ x, HasFDerivAt (Dχ : V → V →L[ℝ] ℝ) (Hχ x) x)
    (hu : ∀ x ∈ tsupport (χ : V → ℝ), HasFDerivAt (u : V → F) (Du x) x)
    (hDu : ∀ x ∈ tsupport (χ : V → ℝ), HasFDerivAt (Du : V → V →L[ℝ] F) (Hu x) x)
    (x : V) :
    HasFDerivAt (cutoffJet1 χ Dχ u Du : V → V →L[ℝ] F)
      (cutoffJet2 χ Dχ Hχ u Du Hu x) x := by
  by_cases hx : x ∈ tsupport (χ : V → ℝ)
  · have hleft := (hχ x).smul (hDu x hx)
    have hright := (ContinuousLinearMap.smulRightL ℝ V F).hasFDerivAt_of_bilinear (hDχ x) (hu x hx)
    change HasFDerivAt (fun y => χ y • Du y + (Dχ y).smulRight (u y))
      (cutoffJet2 χ Dχ Hχ u Du Hu x) x
    simpa only [cutoffJet2_apply, Pi.smul_apply, Pi.add_apply, add_assoc] using! hleft.add hright
  · have hD : Dχ x = 0 := (hχ x).unique (HasFDerivAt.of_notMem_tsupport ℝ hx)
    have hDer : (Dχ : V → V →L[ℝ] ℝ) = fderiv ℝ (χ : V → ℝ) := by
      funext y
      exact (hχ y).fderiv.symm
    have hDSupp : tsupport (Dχ : V → V →L[ℝ] ℝ) ⊆ tsupport (χ : V → ℝ) := by
      rw [hDer]
      exact tsupport_fderiv_subset ℝ
    have hH : Hχ x = 0 := (hDχ x).unique
      (HasFDerivAt.of_notMem_tsupport ℝ (fun h => hx (hDSupp h)))
    have h0 : HasFDerivAt (cutoffJet1 χ Dχ u Du : V → V →L[ℝ] F) 0 x :=
      HasFDerivAt.of_notMem_tsupport ℝ
        (fun h => hx (dirichlet_tsupport_cutoffJet1_subset χ Dχ u Du hχ h))
    rw [cutoffJet2_eq_zero_of_cutoff_eq_zero χ Dχ Hχ u Du Hu x
      (image_eq_zero_of_notMem_tsupport hx) hD hH]
    exact h0

end KEBall
