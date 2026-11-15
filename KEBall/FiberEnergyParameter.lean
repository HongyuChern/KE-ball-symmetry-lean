import KEBall.FiberEnergyHessian

/-!
# Differentiating the Hessian of a smooth family of fibers
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators ContDiff

namespace KEBall.MoserTrudinger

open KEBallProbe

/-- The first derivative in the real parameter of a smooth family. -/
noncomputable def parameterDerivative {n : ℕ} (u : ℝ × E n → ℝ) (y : ℝ × E n) : ℝ :=
  fderiv ℝ u y (1, 0)

theorem parameterDerivative_contDiff {n : ℕ} {u : ℝ × E n → ℝ} (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (parameterDerivative u) :=
  (hu.fderiv_right (by simp)).clm_apply contDiff_const

theorem hasDerivAt_family_value {n : ℕ} {u : ℝ × E n → ℝ} (hu : ContDiff ℝ ∞ u)
    (t : ℝ) (x : E n) :
    HasDerivAt (fun s : ℝ => u (s, x)) (parameterDerivative u (t, x)) t := by
  have h : HasDerivAt (fun s : ℝ => (s, x)) ((1 : ℝ), (0 : E n)) t :=
    (hasFDerivAt_prodMk_left (𝕜 := ℝ) t x).hasDerivAt
  exact ((hu.differentiable (by simp) (t, x)).hasFDerivAt.comp_hasDerivAt t h)

theorem rd_dz_comm {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : F → ℂ} (hf : ContDiff ℝ ∞ f) (v a b : F) :
    rd v (dz a b f) = dz a b (rd v f) := by
  funext y
  rw [rd_dz_at hf.contDiffAt]
  change _ = (2 : ℂ)⁻¹ * (rd a (rd v f) y - Complex.I * rd b (rd v f) y)
  rw [rd_comm_at hf.contDiffAt v a, rd_comm_at hf.contDiffAt v b]

private theorem rd_wirtingerHessian_comm {F ι : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : F → ℂ} (hf : ContDiff ℝ ∞ f) (v : F) (a b : ι → F) (i j : ι) :
    rd v (fun y => wirtingerHessian a b f y i j) =
      fun y => wirtingerHessian a b (rd v f) y i j := by
  have h : ContDiff ℝ ∞ (dz (a j) (-b j) f) :=
    contDiff_iff_contDiffAt.mpr fun y => smoothAt_dz hf.contDiffAt _ _
  change rd v (dz (a i) (b i) (dz (a j) (-b j) f)) =
    dz (a i) (b i) (dz (a j) (-b j) (rd v f))
  rw [rd_dz_comm h, rd_dz_comm hf]

private theorem fiberHessian_parameter {n : ℕ} {u : ℝ × E n → ℝ} (hu : ContDiff ℝ ∞ u)
    (t : ℝ) (x : E n) (i j : Fin n) :
    complexHessian (fun y => u (t, y)) x i j =
      wirtingerHessian (fun k => (0, realDirection k)) (fun k => (0, imagDirection k))
        (fun p => (u p : ℂ)) (t, x) i j := by
  let L := ContinuousLinearMap.inr ℝ ℝ (E n)
  have hc : ContDiff ℝ ∞ (fun p => (u p : ℂ)) := Complex.ofRealCLM.contDiff.comp hu
  have he (y : E n) : ((t, 0) : ℝ × E n) + L y = (t, y) := by simp [L]
  have h := wirtingerHessian_comp_affine hc L (t, 0) realDirection imagDirection x i j
  simp only [he] at h
  exact h

theorem familyHessian_contDiff {n : ℕ} {u : ℝ × E n → ℝ} (hu : ContDiff ℝ ∞ u)
    (i j : Fin n) :
    ContDiff ℝ ∞ (fun y : ℝ × E n => complexHessian (fun x => u (y.1, x)) y.2 i j) := by
  have hc : ContDiff ℝ ∞ (fun p => (u p : ℂ)) := Complex.ofRealCLM.contDiff.comp hu
  have hEq :
      (fun y : ℝ × E n => complexHessian (fun x => u (y.1, x)) y.2 i j) =
        (fun y => wirtingerHessian (fun k => (0, realDirection k)) (fun k => (0, imagDirection k))
          (fun p => (u p : ℂ)) y i j) :=
    funext fun y => fiberHessian_parameter hu y.1 y.2 i j
  rw [hEq]
  exact contDiff_iff_contDiffAt.mpr fun _ =>
    smoothAt_dz (smoothAt_dz hc.contDiffAt _ _) _ _

/-- Parameter differentiation commutes with the complex Hessian of the fiber. -/
theorem hasDerivAt_familyHessian {n : ℕ} {u : ℝ × E n → ℝ} (hu : ContDiff ℝ ∞ u)
    (t : ℝ) (x : E n) (i j : Fin n) :
    HasDerivAt (fun s : ℝ => complexHessian (fun y => u (s, y)) x i j)
      (complexHessian (fun y => parameterDerivative u (t, y)) x i j) t := by
  let a : Fin n → ℝ × E n := fun k => (0, realDirection k)
  let b : Fin n → ℝ × E n := fun k => (0, imagDirection k)
  let f : ℝ × E n → ℂ := fun y => (u y : ℂ)
  let H : ℝ × E n → ℂ := fun y => wirtingerHessian a b f y i j
  have hf : ContDiff ℝ ∞ f := Complex.ofRealCLM.contDiff.comp hu
  have hH : ContDiff ℝ ∞ H :=
    contDiff_iff_contDiffAt.mpr fun _ => smoothAt_dz (smoothAt_dz hf.contDiffAt _ _) _ _
  have hline : HasDerivAt (fun s : ℝ => (s, x)) ((1 : ℝ), (0 : E n)) t :=
    (hasFDerivAt_prodMk_left (𝕜 := ℝ) t x).hasDerivAt
  have h := ((hH.differentiable (by simp) (t, x)).hasFDerivAt.comp_hasDerivAt t hline)
  change HasDerivAt (fun s => H (s, x)) (rd (1, 0) H (t, x)) t at h
  have he (s : ℝ) : H (s, x) = complexHessian (fun y => u (s, y)) x i j :=
    (fiberHessian_parameter hu s x i j).symm
  simp only [he] at h
  have hd : rd (1, 0) f = fun y => (parameterDerivative u y : ℂ) := by
    funext y
    have h := Complex.ofRealCLM.hasFDerivAt.comp y (hu.differentiable (by simp) y).hasFDerivAt
    change HasFDerivAt (fun q => (u q : ℂ)) _ y at h
    change fderiv ℝ (fun q => (u q : ℂ)) y (1, 0) = _
    rw [h.fderiv]
    rfl
  have hr : rd (1, 0) H (t, x) = complexHessian (fun y => parameterDerivative u (t, y)) x i j := by
    change rd (1, 0) (fun y => wirtingerHessian a b f y i j) (t, x) = _
    rw [rd_wirtingerHessian_comm hf (1, 0) a b i j, hd]
    exact (fiberHessian_parameter (parameterDerivative_contDiff hu) t x i j).symm
  rwa [hr] at h

theorem hasDerivAt_familyDeterminant {n : ℕ} {u : ℝ × E n → ℝ} (hu : ContDiff ℝ ∞ u)
    (t : ℝ) (x : E n) :
    HasDerivAt (fun s : ℝ => (complexHessian (fun y => u (s, y)) x).det.re)
      (cofactorContraction (fun y => u (t, y)) (fun y => parameterDerivative u (t, y)) x) t := by
  let A (s : ℝ) := complexHessian (fun y => u (s, y)) x
  have hA (i j : Fin n) :
      HasDerivAt (fun s => A s i j) (complexHessian (fun y => parameterDerivative u (t, y)) x i j) t :=
    hasDerivAt_familyHessian hu t x i j
  have hd := (field_det_differentiableAt fun i j => (hA i j).differentiableAt).hasDerivAt
  have he : deriv (fun s => (A s).det) t =
      ∑ i : Fin n, ∑ j : Fin n, (A t).adjugate j i *
        complexHessian (fun y => parameterDerivative u (t, y)) x i j := by
    rw [← fderiv_apply_one_eq_deriv]
    change rd (1 : ℝ) (fun s => (A s).det) t = _
    rw [rd_det_field (fun i j => (hA i j).differentiableAt)]
    simp only [rd, fderiv_apply_one_eq_deriv, fun i j => (hA i j).deriv]
  rw [he] at hd
  exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hd

end KEBall.MoserTrudinger
