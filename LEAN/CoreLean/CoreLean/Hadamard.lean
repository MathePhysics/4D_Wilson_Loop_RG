/-
The invariance of a subspace under `Ad_{e^B}` when it is invariant under `ad_B`, used for
`lem:norms`(iii) of BALABAN_CORE.tex (the core's proof: `Ad_{e^{iA}} = exp(i ad A)`).

The proof does not use the series of `exp(ad B)`: with a projection `P` onto `V` and `Q = 1 - P`,
the curve `g(t) = Q(e^{tB} X e^{-tB})` solves the linear equation `g' = Q ad_B g` with `g(0) = 0`,
so it vanishes by the uniqueness of solutions of ordinary differential equations.
-/
import CoreLean.Differences

open Matrix Complex
open scoped Matrix.Norms.L2Operator

namespace CoreLean

variable {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ

/-- If a complex subspace `V` is invariant under `X ↦ BX - XB`, then `e^B X e^{-B} ∈ V` for
`X ∈ V`. -/
theorem exp_conj_mem (V : Submodule ℂ Mat) (B : Mat) (hV : ∀ X ∈ V, B * X - X * B ∈ V)
    {X : Mat} (hX : X ∈ V) : NormedSpace.exp B * X * NormedSpace.exp (-B) ∈ V := by
  obtain ⟨W, hVW⟩ := V.exists_isCompl
  set P : Mat →ₗ[ℂ] Mat := V.projection W hVW with hP
  set Q : Mat →ₗ[ℂ] Mat := LinearMap.id - P with hQ
  have hQV : ∀ Y ∈ V, Q Y = 0 := fun Y hY => by
    simp [hQ, hP, Submodule.projection_apply_of_mem_left hVW hY]
  have hQ_mem : ∀ Y, Q Y = 0 → Y ∈ V := fun Y hY => by
    have h : Y = P Y := by
      have : Y - P Y = 0 := by simpa [hQ] using hY
      exact sub_eq_zero.mp this
    rw [h]; exact Submodule.projection_apply_mem hVW Y
  have hPQ : ∀ Y, Y = P Y + Q Y := fun Y => by simp [hQ]
  -- `ad_B` and `S = Q ad_B`
  set ad : Mat →ₗ[ℂ] Mat := LinearMap.mulLeft ℂ B - LinearMap.mulRight ℂ B with had
  have had_apply : ∀ Y, ad Y = B * Y - Y * B := fun Y => by simp [had]
  set S : Mat →ₗ[ℂ] Mat := Q ∘ₗ ad with hS
  -- the curve `f t = e^{tB} X e^{-tB}`
  set f : ℝ → Mat := fun t => NormedSpace.exp (t • B) * X * NormedSpace.exp (t • -B)
    with hf_def
  have hf : ∀ t : ℝ, HasDerivAt f (B * f t - f t * B) t := by
    intro t
    have h1 : HasDerivAt (fun y : ℝ => NormedSpace.exp (y • B))
        (B * NormedSpace.exp (t • B)) t :=
      hasDerivAt_exp_smul_const' (𝕂 := ℝ) B t
    have h2 : HasDerivAt (fun y : ℝ => NormedSpace.exp (y • -B))
        (NormedSpace.exp (t • -B) * -B) t :=
      hasDerivAt_exp_smul_const (𝕂 := ℝ) (-B) t
    have h3 := (h1.mul_const X).mul h2
    convert h3 using 1
    simp only [hf_def, Matrix.mul_neg, Matrix.mul_assoc]
    noncomm_ring
  -- `g = Q f` solves `g' = S g`
  set Qc : Mat →L[ℝ] Mat := (LinearMap.toContinuousLinearMap Q).restrictScalars ℝ
  have hg : ∀ t : ℝ, HasDerivAt (fun t => Q (f t)) (S (Q (f t))) t := by
    intro t
    have h1 : HasDerivAt (fun t => Q (f t)) (Q (B * f t - f t * B)) t :=
      Qc.hasFDerivAt.comp_hasDerivAt t (hf t)
    have h2 : Q (B * f t - f t * B) = S (Q (f t)) := by
      rw [← had_apply, hS, LinearMap.comp_apply]
      conv_lhs => rw [hPQ (f t), map_add, map_add]
      rw [hQV (ad (P (f t))) (by
        rw [had_apply]; exact hV _ (Submodule.projection_apply_mem hVW (f t))), zero_add]
    rwa [h2] at h1
  set Sc : Mat →L[ℂ] Mat := LinearMap.toContinuousLinearMap S
  have hzero : (fun t => Q (f t)) = fun _ => (0 : Mat) := by
    refine ODE_solution_unique_univ (v := fun _ y => S y) (s := fun _ => Set.univ)
      (K := ‖Sc‖₊) (t₀ := 0) (fun _ => (Sc.lipschitzWith).lipschitzOnWith)
      (fun t => ⟨hg t, Set.mem_univ _⟩)
      (fun t => ⟨by simpa using (hasDerivAt_const t (0 : Mat)), Set.mem_univ _⟩) ?_
    simp only [hf_def, zero_smul, NormedSpace.exp_zero, Matrix.one_mul,
      Matrix.mul_one]
    exact hQV X hX
  have h1 := congrFun hzero 1
  have := hQ_mem _ h1
  simpa [hf_def] using this

end CoreLean
