import KEBall.CofactorDivergence

/-! An independent consumer: Piola for a vector-valued complex map.
No KE equation, Hermitian metric, or classification theorem is imported. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff BigOperators Matrix.Norms.Elementwise

namespace KEBallExamples
open KEBall KEBallProbe

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def rowGradient (a b : ι → X) (F : ι → X → ℂ) (x : X) :
    Matrix ι ι ℂ := fun i k => dz (a i) (b i) (F k) x

theorem row_gradient_piola {F : ι → X → ℂ} {x : X}
    (hF : ∀ k, ContDiffAt ℝ ∞ (F k) x) (a b : ι → X)
    (hunit : IsUnit (rowGradient a b F x).det) (j : ι) :
    (∑ i, dz (a i) (b i) (fun y => (rowGradient a b F y).adjugate j i) x) = 0 := by
  apply cofactor_divergence_of_commuting_rows a b
  · intro i k
    exact (smoothAt_dz (hF k) (a i) (b i)).differentiableAt (by simp)
  · intro i r k
    exact dz_comm_at (hF k) (a i) (b i) (a r) (b r)
  · exact hunit

#print axioms row_gradient_piola

end KEBallExamples
