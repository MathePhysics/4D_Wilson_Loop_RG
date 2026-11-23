/-
`lem:axial-box` of BALABAN_CORE.tex (`50787904c4ef`): an axial gauge on a box. For a gauge field `U`, a box `X` of
offsets `lo ≤ v ≤ hi` around `y₀` (containing `0`), `m ≥ Σ_ρ|v_ρ|` on `X`, and `u(z) = U(τ_z)` with `τ_z` the staircase path
from `y₀` to `z` through the coordinates `0, 1, 2, 3`: if the plaquettes with corners in `X` are at most `α` and
`√N mα ≤ r_G`, then `u` has values in `G`, `u(y₀) = id`, and `U^u = e^{iA}` on the bonds of `X` with `A(b) ∈ 𝔤`,
`‖A(b)‖ ≤ (π/2)√N mα`; on a coordinate line through `y₀`, `τ_z` is the straight path.
-/
import CoreLean.AxialFamilies
import CoreLean.Logarithm

open Matrix NormedSpace
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace CoreLean
namespace AxialBox

open LatticePaths LatticeKappa

variable {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "GLN" => (Matrix (Fin N) (Fin N) ℂ)ˣ

/-- The ordering `[0, 1, 2, 3]` split at a coordinate `ρ`. -/
lemma split_at (ρ : Fin 4) : ∃ P S : List (Fin 4), ([0, 1, 2, 3] : List (Fin 4)) = P ++ ρ :: S := by
  fin_cases ρ
  · exact ⟨[], [1, 2, 3], rfl⟩
  · exact ⟨[0], [2, 3], rfl⟩
  · exact ⟨[0, 1], [3], rfl⟩
  · exact ⟨[0, 1, 2], [], rfl⟩

set_option maxHeartbeats 4000000 in
/-- **`lem:axial-box`**: there is `r > 0`, depending on `G` only, with the following property. For a `G`-valued `U`, a box
`lo ≤ v ≤ hi` of offsets around `y₀` containing `0`, `m ≥ Σ_ρ|v_ρ|` on the box, the plaquettes with corners in the box at
most `α`, and `√N mα ≤ r`: the staircase transports `u(v) = U(τ_v)` lie in `G`, `u(0) = id`, `U^u(b) = e^{iA(b)}` on the
positive bonds `b` of the box with `A(b) ∈ 𝔤` and `‖A(b)‖ ≤ (π/2)√N mα`, and for an offset with a single nonzero coordinate
`τ_v` is the straight path. The bound of `U^u(b) - id` is `eq:axial-strip` (`strip`), with `‖·‖ ≤ √N|·|`. -/
theorem axial_box (G : GaugeGroup N) (hG : IsClosed G.mats) :
    ∃ r : ℝ, 0 < r ∧ ∀ {n : ℕ} [NeZero n] (U : Config N n), IsGField G U → ∀ (y₀ : Site n) (lo hi : Fin 4 → ℤ),
      LatticePaths.InBox lo hi 0 → ∀ (m α : ℝ), (∀ v, LatticePaths.InBox lo hi v → ((Finset.univ.sum fun σ => (v σ).natAbs : ℕ) : ℝ) ≤ m) →
      0 ≤ α → (∀ μ ν x, PlaqIn (boxR y₀ lo hi) μ ν x → hs (((plaq U μ ν x : GLN) : Mat) - 1) ≤ α) →
      Real.sqrt N * m * α ≤ r →
      (∀ v, LatticePaths.InBox lo hi v → U.hol (stair y₀ v [0, 1, 2, 3] 0) ∈ G.carrier) ∧
      U.hol (stair y₀ 0 [0, 1, 2, 3] 0) = 1 ∧
      (∀ v ρ, LatticePaths.InBox lo hi v → LatticePaths.InBox lo hi (v + Pi.single ρ 1) → ∃ A ∈ G.lie,
        U.hol (stair y₀ v [0, 1, 2, 3] 0) * U.val ⟨ofs y₀ v, ρ, true⟩ *
          (U.hol (stair y₀ (v + Pi.single ρ 1) [0, 1, 2, 3] 0))⁻¹ = expU (Complex.I • A) ∧
        ‖A‖ ≤ Real.pi / 2 * (Real.sqrt N * m * α)) ∧
      (∀ v ρ, (∀ σ, σ ≠ ρ → v σ = 0) → stair y₀ v [0, 1, 2, 3] 0 = segZ ρ y₀ (v ρ)) := by
  obtain ⟨-, ⟨r, hr0, hr1, hch⟩, -, hiii⟩ := Logarithm.logarithm G hG
  refine ⟨r, hr0, fun U hU y₀ lo hi h0 m α hm hα hP hr => ⟨fun v _ => hU.hol_mem _, ?_, fun v ρ hv hv' => ?_, ?_⟩⟩
  · -- the trivial path
    rw [BlockPaths.stair_zero_coords y₀ 0 _ 0 (fun σ _ => rfl)]
    exact LatticePaths.hol_nil
  · -- the transported bond
    have hUg := hU.gauge
    have hβ : 0 ≤ Real.sqrt N * α := by positivity
    have hPB : PlaqBound U (boxR y₀ lo hi) (Real.sqrt N * α) := fun μ ν x _ hx =>
      (opNorm_le_sqrt_mul_hs _).trans (mul_le_mul_of_nonneg_left (hP μ ν x hx) (Real.sqrt_nonneg _))
    obtain ⟨P, S, hPS⟩ := split_at ρ
    have hnd : (P ++ ρ :: S).Nodup := by rw [← hPS]; decide
    have hstrip := strip hUg hβ hPB v P S ρ hnd h0 hv hv'
    rw [← hPS, offs_perm v (List.Perm.refl _)] at hstrip
    -- the sum over the coordinates after `ρ` is at most `m`
    have hSm : ((S.map fun σ => (v σ).natAbs).sum : ℝ) ≤ m := by
      refine le_trans ?_ (hm v hv)
      have hsub : (S.map fun σ => (v σ).natAbs).sum ≤ Finset.univ.sum fun σ => (v σ).natAbs := by
        have hSnd : S.Nodup := (List.nodup_cons.1 (List.nodup_append.1 hnd).2.1).2
        rw [← List.sum_toFinset _ hSnd]
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => Nat.zero_le _
      exact_mod_cast hsub
    set W := U.hol (stair y₀ v [0, 1, 2, 3] 0) * U.val ⟨ofs y₀ v, ρ, true⟩ *
      (U.hol (stair y₀ (v + Pi.single ρ 1) [0, 1, 2, 3] 0))⁻¹ with hW
    have hWn : ‖(W : Mat) - 1‖ ≤ Real.sqrt N * m * α := by
      refine hstrip.trans ?_
      calc ((S.map fun σ => (v σ).natAbs).sum : ℝ) * (Real.sqrt N * α) ≤ m * (Real.sqrt N * α) :=
            mul_le_mul_of_nonneg_right (by exact_mod_cast hSm) hβ
        _ = Real.sqrt N * m * α := by ring
    have hWG : W ∈ G.carrier :=
      G.carrier.mul_mem (G.carrier.mul_mem (hU.hol_mem _) (hU.val_mem _)) (G.carrier.inv_mem (hU.hol_mem _))
    obtain ⟨A, hA, hAe, hAn, -⟩ := hch W hWG (hWn.trans hr)
    refine ⟨A, hA, Units.ext (by rw [expU_val]; exact hAe.symm), ?_⟩
    have h3 := (hiii A hA.1 (le_of_lt (hAn.trans Real.log_two_lt_d9 |>.trans (by
      have := Real.pi_gt_three; linarith)))).2.1
    rw [hAe] at h3
    exact h3.trans (mul_le_mul_of_nonneg_left hWn (by positivity))
  · -- the straight paths
    intro v ρ hv
    rw [RelativeAverage.stair_filter]
    by_cases hρ : v ρ = 0
    · have hf : ([0, 1, 2, 3] : List (Fin 4)).filter (fun σ => decide (v σ ≠ 0)) = [] := by
        refine List.filter_eq_nil_iff.2 fun σ _ => ?_
        by_cases hσ : σ = ρ
        · subst hσ; simp [hρ]
        · simp [hv σ hσ]
      rw [hf, hρ, segZ_zero]; rfl
    · have hf : ([0, 1, 2, 3] : List (Fin 4)).filter (fun σ => decide (v σ ≠ 0)) = [ρ] := by
        have hcongr : ∀ σ ∈ ([0, 1, 2, 3] : List (Fin 4)), decide (v σ ≠ 0) = decide (σ = ρ) := fun σ _ => by
          by_cases hσ : σ = ρ
          · subst hσ; simp [hρ]
          · simp [hv σ hσ, hσ]
        rw [List.filter_congr hcongr]
        fin_cases ρ <;> rfl
      rw [hf]
      simp [stair, ofs_zero]

end AxialBox
end CoreLean

end
