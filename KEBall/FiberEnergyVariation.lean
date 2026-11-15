import KEBall.FiberEnergyParameter

/-!
# First and second derivatives of the energy of a smooth fiber family
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Set
open scoped ComplexOrder ContDiff Topology

namespace KEBall.MoserTrudinger

private theorem familySlice_contDiff {n : ℕ} {u : ℝ × E n → ℝ} (hu : ContDiff ℝ ∞ u)
    (t : ℝ) : ContDiff ℝ ∞ (fun x => u (t, x)) :=
  hu.comp (contDiff_const.prodMk contDiff_id)

private theorem continuous_familyHessian {n : ℕ} {u : ℝ × E n → ℝ} (hu : ContDiff ℝ ∞ u) :
    Continuous (fun p : ℝ × E n => complexHessian (fun x => u (p.1, x)) p.2) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact (familyHessian_contDiff hu i j).continuous

private theorem continuous_familyDeterminant {n : ℕ} {u : ℝ × E n → ℝ}
    (hu : ContDiff ℝ ∞ u) :
    Continuous (fun p : ℝ × E n => (complexHessian (fun x => u (p.1, x)) p.2).det.re) :=
  Complex.continuous_re.comp (continuous_familyHessian hu).matrix_det

private theorem continuous_familyCofactor {n : ℕ} {u v : ℝ × E n → ℝ}
    (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) :
    Continuous (fun p : ℝ × E n => cofactorContraction (fun x => u (p.1, x))
      (fun x => v (p.1, x)) p.2) := by
  have hAdj := (continuous_familyHessian hu).matrix_adjugate
  apply Complex.continuous_re.comp
  apply continuous_finsetSum
  intro i _
  apply continuous_finsetSum
  intro j _
  exact ((continuous_apply i).comp ((continuous_apply j).comp hAdj)).mul (familyHessian_contDiff hv i j).continuous

private theorem parameterDerivative_boundary {n : ℕ} {u : ℝ × E n → ℝ}
    (hu : ContDiff ℝ ∞ u) (h0 : ∀ t x, x ∈ unitSphere n → u (t, x) = 0)
    (t : ℝ) (x : E n) (hx : x ∈ unitSphere n) : parameterDerivative u (t, x) = 0 := by
  have h := (hasDerivAt_family_value hu t x).deriv
  have he : (fun s : ℝ => u (s, x)) = 0 := funext fun s => h0 s x hx
  rw [he, deriv_zero] at h
  exact h.symm

/-- The ordinary derivative of the signed energy of a zero-boundary fiber. -/
theorem hasDerivAt_familyEnergy {n : ℕ} (hn : 0 < n) {u : ℝ × E n → ℝ}
    (hu : ContDiff ℝ ∞ u) (h0 : ∀ t x, x ∈ unitSphere n → u (t, x) = 0)
    (t : ℝ) (hP : ∀ x ∈ unitBall n, (complexHessian (fun y => u (t, y)) x).PosDef) :
    HasDerivAt (fun s => signedSmoothEnergy (fun x => u (s, x)))
      (∫ x in unitBall n, parameterDerivative u (t, x) *
        (complexHessian (fun y => u (t, y)) x).det.re ∂volume0 n) t := by
  let g := parameterDerivative u
  let D (s : ℝ) (x : E n) := (complexHessian (fun y => u (s, y)) x).det.re
  let Q (s : ℝ) (x : E n) := cofactorContraction (fun y => u (s, y)) (fun y => g (s, y)) x
  let F (s : ℝ) (x : E n) := u (s, x) * D s x
  let F' (s : ℝ) (x : E n) := g (s, x) * D s x + u (s, x) * Q s x
  have hg : ContDiff ℝ ∞ g := parameterDerivative_contDiff hu
  have hD : Continuous (Function.uncurry D) := continuous_familyDeterminant hu
  have hQ : Continuous (Function.uncurry Q) := continuous_familyCofactor hu hg
  have hF : Continuous (Function.uncurry F) := hu.continuous.mul hD
  have hF' : Continuous (Function.uncurry F') := (hg.continuous.mul hD).add (hu.continuous.mul hQ)
  have hd (s : ℝ) (x : E n) (_ : x ∈ (univ : Set (E n))) :
      HasDerivAt (fun r => F r x) (F' s x) s :=
    (hasDerivAt_family_value hu s x).mul (hasDerivAt_familyDeterminant hu s x)
  have h := (hasDerivAt_unitBall_integral hn (subset_univ _) hF.continuousOn hF'.continuousOn hd t)
    |>.div_const (n + 1 : ℝ)
  have heq := integral_energyLinearization_eq hn isOpen_univ (subset_univ _)
    (familySlice_contDiff hu t).contDiffOn (familySlice_contDiff hg t).contDiffOn
    (h0 t) (parameterDerivative_boundary hu h0 t) hP
  change (∫ x in unitBall n, F' t x ∂volume0 n) / (n + 1 : ℝ) =
    (∫ x in unitBall n, g (t, x) * D t x ∂volume0 n) at heq
  rw [← heq]
  exact h

/-- The second real parameter derivative of the signed fiber energy. -/
theorem hasDerivAt_deriv_familyEnergy {n : ℕ} (hn : 0 < n) {u : ℝ × E n → ℝ}
    (hu : ContDiff ℝ ∞ u) (h0 : ∀ t x, x ∈ unitSphere n → u (t, x) = 0)
    (t : ℝ) (hP : ∀ᶠ s in 𝓝 t, ∀ x ∈ unitBall n, (complexHessian (fun y => u (s, y)) x).PosDef) :
    HasDerivAt (deriv (fun s => signedSmoothEnergy (fun x => u (s, x))))
      (∫ x in unitBall n,
        parameterDerivative (parameterDerivative u) (t, x) *
            (complexHessian (fun y => u (t, y)) x).det.re +
          parameterDerivative u (t, x) *
            cofactorContraction (fun y => u (t, y)) (fun y => parameterDerivative u (t, y)) x
        ∂volume0 n) t := by
  let g := parameterDerivative u
  let k := parameterDerivative g
  let D (s : ℝ) (x : E n) := (complexHessian (fun y => u (s, y)) x).det.re
  let Q (s : ℝ) (x : E n) := cofactorContraction (fun y => u (s, y)) (fun y => g (s, y)) x
  let F (s : ℝ) (x : E n) := g (s, x) * D s x
  let F' (s : ℝ) (x : E n) := k (s, x) * D s x + g (s, x) * Q s x
  have hg : ContDiff ℝ ∞ g := parameterDerivative_contDiff hu
  have hk : ContDiff ℝ ∞ k := parameterDerivative_contDiff hg
  have hD : Continuous (Function.uncurry D) := continuous_familyDeterminant hu
  have hQ : Continuous (Function.uncurry Q) := continuous_familyCofactor hu hg
  have hF : Continuous (Function.uncurry F) := hg.continuous.mul hD
  have hF' : Continuous (Function.uncurry F') := (hk.continuous.mul hD).add (hg.continuous.mul hQ)
  have hd (s : ℝ) (x : E n) (_ : x ∈ (univ : Set (E n))) :
      HasDerivAt (fun r => F r x) (F' s x) s :=
    (hasDerivAt_family_value hg s x).mul (hasDerivAt_familyDeterminant hu s x)
  have h := hasDerivAt_unitBall_integral hn (subset_univ _) hF.continuousOn hF'.continuousOn hd t
  have heq : deriv (fun s => signedSmoothEnergy (fun x => u (s, x))) =ᶠ[𝓝 t]
      (fun s => ∫ x in unitBall n, F s x ∂volume0 n) := by
    filter_upwards [hP] with s hs
    exact (hasDerivAt_familyEnergy hn hu h0 s hs).deriv
  exact h.congr_of_eventuallyEq heq

end KEBall.MoserTrudinger
