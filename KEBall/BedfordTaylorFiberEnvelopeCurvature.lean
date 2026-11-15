import KEBall.BedfordTaylorFiberExtensionCurvature
import KEBall.BedfordTaylorFiberEnergySeam

/-!
# The projected Monge–Ampère measure and the true unit-fiber energy
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Metric Set TopologicalSpace
open scoped ContDiff Laplacian Topology

namespace KEBall.BedfordTaylor

open PshLines.FirstPass (ComplexModel)
open PshLines.FirstPass.MongeAmpere (IsLocallyBoundedPshOn)

/-- The distributional Laplacian of the actual unit-fiber energy is the
projection of the Monge–Ampère measure of the product envelope. -/
theorem integral_bedfordTaylorFiberEnergy_mul_laplacian_productEnvelope
    {n : ℕ} (hn : 0 < n) {R : ℝ} (hR : 0 < R) (hR₁ : R < 1)
    {u v : ComplexModel (n + 1) → ℝ} (hu : ContDiff ℝ 2 u)
    (hu₀ : ∀ x ∈ ball 0 R, u x ≤ 0) (huBoundary : ∀ x ∈ sphere 0 R, u x = 0)
    (hv : IsLocallyBoundedPshOn (complexProductBall n 1) v)
    (hvf : ∀ x ∈ complexProductBall n 1,
      v x ≤ (ball (0 : ComplexModel (n + 1)) R).indicator u x)
    (hgreatest : ∀ w : ComplexModel (n + 1) → ℝ,
      IsLocallyBoundedPshOn (complexProductBall n 1) w →
      (∀ x ∈ complexProductBall n 1, w x ≤ (ball (0 : ComplexModel (n + 1)) R).indicator u x) →
      ∀ x ∈ complexProductBall n 1, w x ≤ v x)
    {A : ℝ} (hA : 0 < A)
    (hvLower : ∀ x ∈ complexProductBall n 1, A * productFiberQuadratic n 1 x ≤ v x)
    {φ : E 1 → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφs : tsupport φ ⊆ unitBall 1) :
    Integrable (fun w => bedfordTaylorFiberEnergy (R := 1) (ρ := 1) hv w * Δ φ w) ∧
      (∫ w, bedfordTaylorFiberEnergy (R := 1) (ρ := 1) hv w * Δ φ w) =
        (4 * Real.pi / (n + 1 : ℝ)) *
          ∫ x, φ ((complexCoordinates 1).symm (complexProductCoordinates n 1 x).2)
            ∂topMeasure hv := by
  obtain ⟨r, hr, hφr⟩ := exists_lt_subset_ball (isClosed_tsupport φ) hφs
  obtain ⟨hp, hMeas⟩ :=
    exists_topMeasure_productFiberExtension_eq hR hR₁ hu hu₀ huBoundary hv hvf hgreatest hA hvLower
  obtain ⟨hInt, hExt⟩ := integral_bedfordTaylorFiberEnergy_mul_laplacian_productFiberExtension
    hn hA hp hr hφ hφc hφr
  obtain ⟨C, hC⟩ := bedfordTaylorFiberEnergy_productFiberExtension_eq_add_const hA hv hvLower hp
  let F (w : E 1) := bedfordTaylorFiberEnergy
    (IsLocallyBoundedPshOn.mono hp (fiberEnergyCylinder_le_complexProductCylinder 2 le_rfl)) w * Δ φ w
  let G (w : E 1) := bedfordTaylorFiberEnergy (R := 1) (ρ := 1) hv w * Δ φ w
  let H (w : E 1) := C * Δ φ w
  have hH : Integrable H := (integrable_laplacian_of_compactSupport hφ hφc).const_mul C
  have hEq (w : E 1) : F w = G w + H w := by
    by_cases hw : w ∈ unitBall 1
    · dsimp only [F, G, H]
      rw [hC w hw, add_mul]
    · have hz : Δ φ w = 0 := image_eq_zero_of_notMem_tsupport
        (fun h => hw (hφs (tsupport_laplacian_subset φ h)))
      simp only [F, G, H, hz, mul_zero, add_zero]
  have hG : Integrable G := (hInt.sub hH).congr (Eventually.of_forall fun w => by
    change F w - H w = G w
    rw [hEq, add_sub_cancel_right])
  refine ⟨hG, ?_⟩
  change (∫ w, G w) = _
  have hFH : (∫ w, F w) = ∫ w, G w := by
    have he : F = fun w => G w + H w := funext hEq
    rw [he, integral_add hG hH, integral_const_mul, integral_laplacian_eq_zero_of_compactSupport hφ hφc,
      mul_zero, add_zero]
  rw [← hFH]
  exact hExt.trans (by rw [hMeas])

end KEBall.BedfordTaylor
