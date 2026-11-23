/-
`lem:slice-convexity` of BALABAN_CORE.tex (`a021c13be348`), the abstract steps of its proof. On a finite-dimensional
real normed space `E` (the space `𝒮` of the forms `h` with `Qh = 0`, `RD^*h = 0`):

* *The second derivative does not degenerate*: the derivative of a map which is Lipschitz with the constant `K` on a
  ball has the norm at most `K` at the interior points (`fderiv_le_of_lipschitz`), and at the boundary points when it
  is continuous on the closed ball (`fderiv_le_closedBall`); and `h = -Th` with `‖T‖ ≤ ½` forces `h = 0`
  (`eq_zero_of_fixed`).
* *Positivity*: a continuous family `t ↦ k_t` of symmetric bilinear forms on `E`, `t ∈ [0, 1]`, which does not
  degenerate for any `t` and is positive definite at `t = 0`, is positive definite for every `t ∈ [0, 1]`
  (`posDef_of_path`). The core argues with the eigenvalues of the representing operator; here the continuous function
  `m(t) = min_{‖h‖ = 1}k_t(h, h)` replaces them, `m(t) = 0` being excluded because a positive semidefinite form vanishes
  on the diagonal only at its kernel (`kernel_of_semidef`), and the intermediate value theorem replacing the continuity
  of the eigenvalues.
* *The minimum*: `f'' > 0` on `[0, 1]` and `f'(0) = 0` give `f(1) > f(0)` (`strict_min`).
-/
import Mathlib

open Set Filter Topology Metric

noncomputable section

namespace CoreLean
namespace SliceConvexity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The derivative of a `K`-Lipschitz map at the interior points of a ball. -/
theorem fderiv_le_of_lipschitz {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {Φ : E → F}
    {D : E → E →L[ℝ] F} {a : E} {r : ℝ} {K : NNReal} (hD : ∀ x ∈ ball a r, HasFDerivAt Φ (D x) x)
    (hlip : LipschitzOnWith K Φ (ball a r)) : ∀ x ∈ ball a r, ‖D x‖ ≤ K := fun x hx =>
  (hD x hx).le_of_lipschitzOn (isOpen_ball.mem_nhds hx) hlip

/-- And at the boundary points, by continuity. -/
theorem fderiv_le_closedBall {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {Φ : E → F}
    {D : E → E →L[ℝ] F} {a : E} {r : ℝ} (hr : r ≠ 0) {K : NNReal}
    (hD : ∀ x ∈ ball a r, HasFDerivAt Φ (D x) x) (hlip : LipschitzOnWith K Φ (ball a r))
    (hc : ContinuousOn D (closedBall a r)) : ∀ x ∈ closedBall a r, ‖D x‖ ≤ K := by
  intro x hx
  have hcl : x ∈ closure (ball a r) := by rw [closure_ball a hr]; exact hx
  have hcw : ContinuousWithinAt (fun y => ‖D y‖) (ball a r) x :=
    ((hc x hx).mono ball_subset_closedBall).norm
  exact hcw.closure_le hcl continuousWithinAt_const (fderiv_le_of_lipschitz hD hlip)

/-- `h = -Th` with `‖T‖ ≤ ½` forces `h = 0`. -/
theorem eq_zero_of_fixed (T : E →L[ℝ] E) (hT : ‖T‖ ≤ 1 / 2) {h : E} (hh : h = -T h) : h = 0 := by
  have h1 : ‖h‖ ≤ 1 / 2 * ‖h‖ := by
    calc ‖h‖ = ‖T h‖ := by rw [hh, norm_neg]; congr 1; rw [← hh]
      _ ≤ ‖T‖ * ‖h‖ := T.le_opNorm h
      _ ≤ 1 / 2 * ‖h‖ := mul_le_mul_of_nonneg_right hT (norm_nonneg h)
  exact norm_le_zero_iff.1 (by linarith [norm_nonneg h])

/-- A positive semidefinite symmetric form vanishes on the diagonal only at its kernel. -/
lemma kernel_of_semidef (k : E →L[ℝ] E →L[ℝ] ℝ) (hsym : ∀ x y, k x y = k y x) (hpos : ∀ x, 0 ≤ k x x)
    {h : E} (hh : k h h = 0) (δ : E) : k δ h = 0 := by
  set a := k δ h
  set b := k δ δ
  have hb : 0 ≤ b := hpos δ
  have hq : ∀ s : ℝ, 0 ≤ 2 * s * a + s ^ 2 * b := by
    intro s
    have := hpos (h + s • δ)
    have e : k (h + s • δ) (h + s • δ) = k h h + 2 * s * a + s ^ 2 * b := by
      simp only [map_add, map_smul, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        smul_eq_mul]
      rw [hsym h δ]
      ring
    rw [e, hh] at this
    linarith
  have h1 := hq (-a / (b + 1))
  have hb1 : 0 < b + 1 := by linarith
  have h2 : 0 ≤ -(a ^ 2 * (b + 2)) := by
    have e : 2 * (-a / (b + 1)) * a + (-a / (b + 1)) ^ 2 * b = -(a ^ 2 * (b + 2)) / (b + 1) ^ 2 := by
      field_simp
      ring
    rw [e] at h1
    exact (div_nonneg_iff.1 h1).elim (fun h => h.1) fun h => by nlinarith [h.2, sq_nonneg (b + 1)]
  have : a ^ 2 ≤ 0 := by nlinarith [sq_nonneg a]
  exact pow_eq_zero_iff (n := 2) two_ne_zero |>.1 (le_antisymm this (sq_nonneg a))

lemma quad_scale (k : E →L[ℝ] E →L[ℝ] ℝ) (c : ℝ) (x : E) : k (c • x) (c • x) = c ^ 2 * k x x := by
  simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

/-- **Positivity**: a continuous family of symmetric bilinear forms on a finite-dimensional space, nondegenerate on
`[0, 1]` and positive definite at `0`, is positive definite on `[0, 1]`. -/
theorem posDef_of_path [FiniteDimensional ℝ E] (k : ℝ → E →L[ℝ] E →L[ℝ] ℝ) (hk : ContinuousOn k (Icc 0 1))
    (hsym : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x y, k t x y = k t y x)
    (hnd : ∀ t ∈ Icc (0 : ℝ) 1, ∀ h, (∀ δ, k t δ h = 0) → h = 0) (h0 : ∀ h, h ≠ 0 → 0 < k 0 h h) :
    ∀ t ∈ Icc (0 : ℝ) 1, ∀ h, h ≠ 0 → 0 < k t h h := by
  intro t ht h hh
  -- the family extended continuously to `ℝ`
  set k' : ℝ → E →L[ℝ] E →L[ℝ] ℝ := fun t => k (projIcc 0 1 zero_le_one t)
  have hk' : Continuous k' := hk.comp_continuous (continuous_subtype_val.comp continuous_projIcc) fun t => (projIcc 0 1 zero_le_one t).2
  have hk'eq : ∀ t ∈ Icc (0 : ℝ) 1, k' t = k t := fun t ht => by simp only [k', projIcc_of_mem _ ht]
  set S : Set E := sphere 0 1
  have hS : IsCompact S := isCompact_sphere 0 1
  have hSne : S.Nonempty := ⟨‖h‖⁻¹ • h, by
    simp [S, norm_smul, inv_mul_cancel₀ (norm_ne_zero_iff.2 hh)]⟩
  have hf : Continuous (fun p : ℝ × E => k' p.1 p.2 p.2) :=
    ((hk'.comp continuous_fst).clm_apply continuous_snd).clm_apply continuous_snd
  set m : ℝ → ℝ := fun t => sInf ((fun x => k' t x x) '' S)
  have hm : Continuous m := hS.continuous_sInf (f := fun t x => k' t x x) hf
  -- the minimum is attained
  have hmin : ∀ t, ∃ u ∈ S, m t = k' t u u ∧ ∀ x ∈ S, k' t u u ≤ k' t x x := by
    intro t
    obtain ⟨u, hu, hmin⟩ := hS.exists_isMinOn hSne (hf.comp (Continuous.prodMk_right t)).continuousOn
    refine ⟨u, hu, ?_, fun x hx => hmin hx⟩
    refine IsLeast.csInf_eq ⟨⟨u, hu, rfl⟩, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact hmin hx
  -- the quadratic form on all of `E` from the sphere
  have hscale : ∀ t, ∀ x : E, x ≠ 0 → k' t x x = ‖x‖ ^ 2 * k' t (‖x‖⁻¹ • x) (‖x‖⁻¹ • x) ∧
      ‖x‖⁻¹ • x ∈ S := by
    intro t x hx
    have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
    refine ⟨?_, by simp [S, norm_smul, inv_mul_cancel₀ hn]⟩
    rw [quad_scale, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hn, one_pow, one_mul]
  -- `m` does not vanish on `[0, 1]`
  have hne : ∀ s ∈ Icc (0 : ℝ) 1, m s ≠ 0 := by
    intro s hs hms
    obtain ⟨u, hu, hmu, hle⟩ := hmin s
    have hpos : ∀ x, 0 ≤ k s x x := by
      intro x
      rcases eq_or_ne x 0 with rfl | hx
      · simp
      · obtain ⟨e, hxS⟩ := hscale s x hx
        rw [← hk'eq s hs, e]
        exact mul_nonneg (sq_nonneg _) (by have := hle _ hxS; rw [← hmu, hms] at this; exact this)
    have hu0 : k s u u = 0 := by rw [← hk'eq s hs, ← hmu, hms]
    have := hnd s hs u fun δ => kernel_of_semidef (k s) (hsym s hs) hpos hu0 δ
    have : ‖u‖ = 1 := by simpa [S] using hu
    simp_all
  -- `m 0 > 0`
  have hm0 : 0 < m 0 := by
    obtain ⟨u, hu, hmu, -⟩ := hmin 0
    have hu0 : u ≠ 0 := by rintro rfl; simp [S] at hu
    rw [hmu, hk'eq 0 ⟨le_refl _, zero_le_one⟩]
    exact h0 u hu0
  -- the intermediate value theorem
  have hmt : 0 < m t := by
    by_contra hc
    replace hc := not_lt.1 hc
    obtain ⟨s, hs, hms⟩ := intermediate_value_Icc' ht.1 hm.continuousOn ⟨hc, hm0.le⟩
    exact hne s ⟨hs.1, hs.2.trans ht.2⟩ hms
  obtain ⟨u, hu, hmu, hle⟩ := hmin t
  obtain ⟨e, hxS⟩ := hscale t h hh
  rw [← hk'eq t ht, e]
  have : m t ≤ k' t (‖h‖⁻¹ • h) (‖h‖⁻¹ • h) := hmu ▸ hle _ hxS
  exact mul_pos (pow_pos (norm_pos_iff.2 hh) 2) (lt_of_lt_of_le hmt this)

/-- **The minimum**: `f'' > 0` on `[0, 1]` and `f'(0) = 0` give `f(0) < f(1)`. -/
theorem strict_min {f f' f'' : ℝ → ℝ} (hf : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt f (f' s) s)
    (hf' : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt f' (f'' s) s) (hpos : ∀ s ∈ Icc (0 : ℝ) 1, 0 < f'' s)
    (h0 : f' 0 = 0) : f 0 < f 1 := by
  have hmono' : StrictMonoOn f' (Icc 0 1) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc 0 1)
      (fun s hs => (hf' s hs).continuousAt.continuousWithinAt) fun s hs => ?_
    rw [interior_Icc] at hs
    rw [(hf' s (Ioo_subset_Icc_self hs)).deriv]
    exact hpos s (Ioo_subset_Icc_self hs)
  have hmono : StrictMonoOn f (Icc 0 1) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc 0 1)
      (fun s hs => (hf s hs).continuousAt.continuousWithinAt) fun s hs => ?_
    rw [interior_Icc] at hs
    rw [(hf s (Ioo_subset_Icc_self hs)).deriv, ← h0]
    exact hmono' ⟨le_refl 0, zero_le_one⟩ (Ioo_subset_Icc_self hs) hs.1
  exact hmono ⟨le_refl 0, zero_le_one⟩ ⟨zero_le_one, le_refl 1⟩ zero_lt_one

end SliceConvexity
end CoreLean

end
