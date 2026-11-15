import KEBall.BedfordTaylorPolarization
import Mathlib.Algebra.BigOperators.Fin

/-!
# Exterior differentiation of distributional coefficients

The two tuple variables keep holomorphic and antiholomorphic indices
separate. Applying the two alternating derivative sums gives the
coefficient formula used in the Bedford–Taylor recursion.
-/

set_option autoImplicit false

open TopologicalSpace
open scoped Distributions

namespace KEBall.BedfordTaylor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {U : Opens E}

/-- Differentiate each omitted index with its alternating sign. -/
noncomputable def alternatingDerivative {α : Type*}
    (D : α → 𝓓'(U, ℂ) →L[ℝ] 𝓓'(U, ℂ))
    {k : ℕ} (T : (Fin k → α) → 𝓓'(U, ℂ)) (v : Fin (k + 1) → α) : 𝓓'(U, ℂ) :=
  ∑ i : Fin (k + 1), (-1 : ℤ) ^ (i : ℕ) • D (v i) (T (i.removeNth v))

theorem alternatingDerivative_sq {α : Type*}
    (D : α → 𝓓'(U, ℂ) →L[ℝ] 𝓓'(U, ℂ))
    (hD : ∀ a b T, D a (D b T) = D b (D a T))
    {k : ℕ} (T : (Fin k → α) → 𝓓'(U, ℂ)) (v : Fin (k + 2) → α) :
    alternatingDerivative D (alternatingDerivative D T) v = 0 := by
  simp only [alternatingDerivative, map_sum, map_zsmul, Finset.smul_sum]
  rw [Fin.sum_sum_eq_sum_triangle_add]
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j hj
  rw [Finset.mem_Ici] at hj
  have h₁ : i.castSucc.removeNth v j = v j.succ := by
    simp [Fin.removeNth_apply, Fin.succAbove_of_le_castSucc, hj]
  have h₂ : j.succ.removeNth v i = v i.castSucc := by
    simp [Fin.removeNth_apply, Fin.succAbove_of_castSucc_lt, hj]
  have h₃ : j.removeNth (i.castSucc.removeNth v) = i.removeNth (j.succ.removeNth v) := by
    rw [Fin.removeNth_removeNth_eq_swap]
    simp [Fin.predAbove, Fin.succAbove, not_lt.mpr hj]
  simp only [Fin.val_castSucc, Fin.val_succ, h₁, h₂, h₃,
    hD (v i.castSucc) (v j.succ), pow_succ, mul_smul, neg_one_smul, smul_neg]
  rw [smul_comm ((-1 : ℤ) ^ (j : ℕ)), add_neg_cancel]

/-- The coefficients of bidegree (k,l) tested on ordered tuples of
constant complex directions. -/
abbrev DistributionalCoefficients (U : Opens E) (k l : ℕ) :=
  (Fin k → E) → (Fin l → E) → 𝓓'(U, ℂ)

variable [NormedSpace ℂ E]

/-- Differentiate the holomorphic indices and alternate. -/
noncomputable def holomorphicExteriorDerivative {k l : ℕ}
    (T : DistributionalCoefficients U k l) : DistributionalCoefficients U (k + 1) l :=
  fun v w => alternatingDerivative (fun a => wirtingerDerivative a (Complex.I • a)) (T · w) v

/-- Differentiate the antiholomorphic indices and alternate. -/
noncomputable def antiholomorphicExteriorDerivative {k l : ℕ}
    (T : DistributionalCoefficients U k l) : DistributionalCoefficients U k (l + 1) :=
  fun v w => alternatingDerivative (fun a => wirtingerDerivative a (-(Complex.I • a))) (T v) w

theorem holomorphicExteriorDerivative_sq {k l : ℕ} (T : DistributionalCoefficients U k l) :
    holomorphicExteriorDerivative (holomorphicExteriorDerivative T) = 0 := by
  funext v w
  exact alternatingDerivative_sq _ (fun _ _ _ => wirtingerDerivative_comm _ _ _ _ _) (T · w) v

theorem antiholomorphicExteriorDerivative_sq {k l : ℕ} (T : DistributionalCoefficients U k l) :
    antiholomorphicExteriorDerivative (antiholomorphicExteriorDerivative T) = 0 := by
  funext v w
  exact alternatingDerivative_sq _ (fun _ _ _ => wirtingerDerivative_comm _ _ _ _ _) (T v) w

/-- In the convention with separate row and column alternation the two
coefficient derivatives commute. -/
theorem exteriorDerivatives_comm {k l : ℕ} (T : DistributionalCoefficients U k l) :
    holomorphicExteriorDerivative (antiholomorphicExteriorDerivative T) =
      antiholomorphicExteriorDerivative (holomorphicExteriorDerivative T) := by
  funext v w
  simp only [holomorphicExteriorDerivative, antiholomorphicExteriorDerivative, alternatingDerivative,
    map_sum, map_zsmul, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rw [smul_comm, wirtingerDerivative_comm]

open PshLines.FirstPass (ComplexModel)
open PshLines.FirstPass.MongeAmpere (IsLocallyBoundedPshOn)

/-- The unscaled coefficients of the second Bedford–Taylor product,
obtained by differentiating the weighted first Hessian. -/
noncomputable def secondMixedHessian {n : ℕ} {Ω : Opens (ComplexModel n)}
    {u p : ComplexModel n → ℝ} (hu : IsLocallyBoundedPshOn Ω u)
    (hp : IsLocallyBoundedPshOn Ω p) : DistributionalCoefficients Ω 2 2 :=
  holomorphicExteriorDerivative (antiholomorphicExteriorDerivative
    (fun v w => weightedComplexHessian hu hp (v 0) (w 0)))

theorem secondMixedHessian_eq {n : ℕ} {Ω : Opens (ComplexModel n)}
    {u p : ComplexModel n → ℝ} (hu : IsLocallyBoundedPshOn Ω u)
    (hp : IsLocallyBoundedPshOn Ω p) (v w : Fin 2 → ComplexModel n) :
    let F := fun a r b s => wirtingerDerivative a (Complex.I • a)
      (wirtingerDerivative r (-(Complex.I • r)) (weightedComplexHessian hu hp b s))
    secondMixedHessian hu hp v w =
      F (v 0) (w 0) (v 1) (w 1) - F (v 1) (w 0) (v 0) (w 1) -
      F (v 0) (w 1) (v 1) (w 0) + F (v 1) (w 1) (v 0) (w 0) := by
  have h₀ (z : Fin 2 → ComplexModel n) : (Fin.removeNth 0 z) 0 = z 1 := rfl
  have h₁ (z : Fin 2 → ComplexModel n) : (Fin.removeNth 1 z) 0 = z 0 := rfl
  simp only [secondMixedHessian, holomorphicExteriorDerivative, antiholomorphicExteriorDerivative,
    alternatingDerivative]
  rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
  simp only [h₀, h₁, Fin.val_zero, Fin.val_one, pow_zero, pow_one,
    one_smul, neg_one_smul, map_add, map_neg]
  abel

theorem holomorphicExteriorDerivative_secondMixedHessian {n : ℕ} {Ω : Opens (ComplexModel n)}
    {u p : ComplexModel n → ℝ} (hu : IsLocallyBoundedPshOn Ω u)
    (hp : IsLocallyBoundedPshOn Ω p) :
    holomorphicExteriorDerivative (secondMixedHessian hu hp) = 0 :=
  holomorphicExteriorDerivative_sq _

theorem antiholomorphicExteriorDerivative_secondMixedHessian
    {n : ℕ} {Ω : Opens (ComplexModel n)} {u p : ComplexModel n → ℝ}
    (hu : IsLocallyBoundedPshOn Ω u) (hp : IsLocallyBoundedPshOn Ω p) :
    antiholomorphicExteriorDerivative (secondMixedHessian hu hp) = 0 := by
  let T : DistributionalCoefficients Ω 1 1 := fun v w => weightedComplexHessian hu hp (v 0) (w 0)
  change antiholomorphicExteriorDerivative (holomorphicExteriorDerivative
    (antiholomorphicExteriorDerivative T)) = 0
  rw [← exteriorDerivatives_comm (antiholomorphicExteriorDerivative T),
    antiholomorphicExteriorDerivative_sq]
  funext v w
  simp [holomorphicExteriorDerivative, alternatingDerivative]

end KEBall.BedfordTaylor
