import KEBall.BedfordTaylorMatrixDensity
import KEBall.CofactorDivergence

/-!
# The smooth product rule for closed coefficient matrices
-/

set_option autoImplicit false

open Filter Set TopologicalSpace
open scoped ContDiff Topology Distributions

namespace KEBall.BedfordTaylor

open KEBallProbe
open PshLines.FirstPass (ComplexModel)
open PshLines.FirstPass.MongeAmpere (coordinateVector)

variable {n k : ℕ} {Ω : Opens (ComplexModel n)} {u : ComplexModel n → ℝ}

/-- Wedge multiplication by the smooth Hessian, in the separate row and
column convention. -/
noncomputable def smoothHessianWedge (u : ComplexModel n → ℝ) (g : CoordinateDensities n k k) :
    CoordinateDensities n (k + 1) (k + 1) :=
  Matrix.of fun I J x => ∑ i : Fin (k + 1), ∑ j : Fin (k + 1),
    (-1 : ℂ) ^ ((i : ℕ) + (j : ℕ)) *
      classicalComplexHessianEntry u (coordinateVector (I i)) (coordinateVector (J j)) x *
      g (i.removeNth I) (j.removeNth J) x

theorem contDiffOn_smoothHessianWedge (g : CoordinateDensities n k k)
    (hg : ∀ I J, ContDiffOn ℝ ∞ (g I J) Ω) (hu : ContDiffOn ℝ ∞ u Ω)
    (I J : CoordinateTuple n (k + 1)) : ContDiffOn ℝ ∞ (smoothHessianWedge u g I J) Ω := by
  change ContDiffOn ℝ ∞ (fun x => ∑ i : Fin (k + 1), ∑ j : Fin (k + 1),
    (-1 : ℂ) ^ ((i : ℕ) + (j : ℕ)) *
      classicalComplexHessianEntry u (coordinateVector (I i)) (coordinateVector (J j)) x *
      g (i.removeNth I) (j.removeNth J) x) Ω
  exact ContDiffOn.sum fun i _ => ContDiffOn.sum fun j _ =>
    (contDiffOn_const.mul (contDiffOn_classicalComplexHessianEntry hu
      (coordinateVector (I i)) (coordinateVector (J j)))).mul (hg (i.removeNth I) (j.removeNth J))

private theorem dz_congr_of_germ {f g : ComplexModel n → ℂ} {x : ComplexModel n}
    (heq : f =ᶠ[𝓝 x] g) (a b : ComplexModel n) :
    dz a b f x = dz a b g x := by
  simp only [dz, rd, heq.fderiv_eq]

private theorem dz_const_mul_smoothAt {f : ComplexModel n → ℂ} {x : ComplexModel n}
    (hf : ContDiffAt ℝ ∞ f x) (a b : ComplexModel n) (c : ℂ) :
    dz a b (fun y => c * f y) x = c * dz a b f x := by
  rw [dz_mul_differentiableAt (differentiableAt_const _) (hf.differentiableAt (by simp))]
  simp [dz, rd]

/-- On a closed smooth coefficient matrix, applying both exterior
derivatives after multiplication by a smooth weight wedges the matrix
with the Hessian of the weight. -/
theorem coordinateRowColumnDensity_mul_eqOn_wedge (g : CoordinateDensities n k k)
    (hg : ∀ I J, ContDiffOn ℝ ∞ (g I J) Ω) (hu : ContDiffOn ℝ ∞ u Ω)
    (hrow : ∀ I J, EqOn (coordinateRowDensity g I J) 0 Ω)
    (hcol : ∀ I J, EqOn (coordinateColumnDensity g I J) 0 Ω) :
    ∀ I J, EqOn
      (coordinateRowDensity (coordinateColumnDensity
        (Matrix.of fun I' J' x => (u x : ℂ) * g I' J' x)) I J)
      (smoothHessianWedge u g I J) Ω := by
  let f : ComplexModel n → ℂ := fun x => u x
  let w : CoordinateDensities n k k := Matrix.of fun I J x => f x * g I J x
  let P : CoordinateTuple n k → CoordinateTuple n (k + 1) → ComplexModel n → ℂ :=
    fun I J x => ∑ j : Fin (k + 1), (-1 : ℂ) ^ (j : ℕ) *
      dz (coordinateVector (J j)) (-(Complex.I • coordinateVector (J j))) f x *
      g I (j.removeNth J) x
  have hf : ContDiffOn ℝ ∞ f Ω := Complex.ofRealCLM.contDiff.comp_contDiffOn hu
  have hP (I : CoordinateTuple n k) (J : CoordinateTuple n (k + 1)) :
      EqOn (coordinateColumnDensity w I J) (P I J) Ω := by
    intro x hx
    have hfx := hf.contDiffAt (Ω.isOpen.mem_nhds hx)
    change (∑ j : Fin (k + 1), (-1 : ℂ) ^ (j : ℕ) *
      dz (coordinateVector (J j)) (-(Complex.I • coordinateVector (J j)))
        (fun y => f y * g I (j.removeNth J) y) x) = P I J x
    calc
      _ = ∑ j : Fin (k + 1), ((-1 : ℂ) ^ (j : ℕ) *
          dz (coordinateVector (J j)) (-(Complex.I • coordinateVector (J j))) f x *
          g I (j.removeNth J) x + f x * ((-1 : ℂ) ^ (j : ℕ) *
            dz (coordinateVector (J j)) (-(Complex.I • coordinateVector (J j)))
              (g I (j.removeNth J)) x)) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [dz_mul_differentiableAt (hfx.differentiableAt (by simp))
          (((hg I (j.removeNth J)).contDiffAt (Ω.isOpen.mem_nhds hx)).differentiableAt (by simp))]
        ring
      _ = P I J x + f x * coordinateColumnDensity g I J x := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        rfl
      _ = _ := by rw [hcol I J hx, Pi.zero_apply, mul_zero, add_zero]
  intro I J x hx
  let R := fun i : Fin (k + 1) => coordinateVector (I i)
  let C := fun j : Fin (k + 1) => coordinateVector (J j)
  let G := fun i j : Fin (k + 1) => g (i.removeNth I) (j.removeNth J)
  let sign := fun i : Fin (k + 1) => (-1 : ℂ) ^ (i : ℕ)
  let bar := fun j => dz (C j) (-(Complex.I • C j)) f
  have hgAt (i j : Fin (k + 1)) : ContDiffAt ℝ ∞ (G i j) x :=
    (hg _ _).contDiffAt (Ω.isOpen.mem_nhds hx)
  have hbar (j : Fin (k + 1)) : ContDiffAt ℝ ∞ (bar j) x :=
    smoothAt_dz (hf.contDiffAt (Ω.isOpen.mem_nhds hx)) _ _
  have hsum (i : Fin (k + 1)) :
      dz (R i) (Complex.I • R i) (coordinateColumnDensity w (i.removeNth I) J) x =
        ∑ j, sign j * (classicalComplexHessianEntry u (R i) (C j) x * G i j x +
          bar j x * dz (R i) (Complex.I • R i) (G i j) x) := by
    have heq : coordinateColumnDensity w (i.removeNth I) J =ᶠ[𝓝 x] P (i.removeNth I) J := by
      filter_upwards [Ω.isOpen.mem_nhds hx] with y hy
      exact hP _ _ hy
    rw [dz_congr_of_germ heq]
    have hPeq : P (i.removeNth I) J = fun y => ∑ j, sign j * (bar j y * G i j y) := by
      funext y
      simp only [P, sign, bar, G, C, mul_assoc]
    rw [hPeq]
    rw [dz_sum_differentiableAt (fun j =>
      (contDiffAt_const.mul ((hbar j).mul (hgAt i j))).differentiableAt (by simp))]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [dz_const_mul_smoothAt ((hbar j).mul (hgAt i j)),
      dz_mul_differentiableAt ((hbar j).differentiableAt (by simp))
        ((hgAt i j).differentiableAt (by simp))]
    rfl
  change (∑ i, sign i *
    dz (R i) (Complex.I • R i) (coordinateColumnDensity w (i.removeNth I) J) x) =
      smoothHessianWedge u g I J x
  simp only [hsum]
  have hzero :
      (∑ i : Fin (k + 1), ∑ j : Fin (k + 1),
        (sign j * bar j x) * (sign i * dz (R i) (Complex.I • R i) (G i j) x)) = 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro j _
    rw [← Finset.mul_sum]
    change (sign j * bar j x) * coordinateRowDensity g I (j.removeNth J) x = 0
    rw [hrow I (j.removeNth J) hx, Pi.zero_apply, mul_zero]
  calc
    _ = (∑ i : Fin (k + 1), ∑ j : Fin (k + 1),
          (-1 : ℂ) ^ ((i : ℕ) + (j : ℕ)) *
            classicalComplexHessianEntry u (R i) (C j) x * G i j x) +
        ∑ i : Fin (k + 1), ∑ j : Fin (k + 1),
          (sign j * bar j x) * (sign i * dz (R i) (Complex.I • R i) (G i j) x) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [sign, pow_add]
      ring
    _ = _ := by rw [hzero, add_zero]; rfl

end KEBall.BedfordTaylor
