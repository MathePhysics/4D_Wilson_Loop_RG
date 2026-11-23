/-
`prop:landau-divergence`(ii) of BALABAN_CORE.tex (`a021c13be348`), and the series `G_c = Σ_{n ≥ 0}(GΔ^{(2)})^nG` of
`prop:pair-operators`(i), in abstract form. On a Banach space, let `G` be the two-sided inverse of `Δ_𝖺` and
`T = GΔ'` with `‖T‖ ≤ ½` (`(i)`, `‖GΔ'_πA‖_ϖ ≤ C_𝒦γ‖A‖_ϖ` with `C_𝒦γ ≤ ½`, in the norm of a weight). Then:

* the series `G_π = Σ_{n ≥ 0}T^nG` converges (`summable_series`);
* `G_π` is the two-sided inverse of `Δ_𝖺 - Δ'` (`series_right_inverse`, `series_left_inverse`);
* `‖G_πf‖ ≤ 2‖Gf‖` (`series_bound`), which with `‖Gf‖_ϖ ≤ B_g‖ϖf‖_{∞,(-3)}` is `eq:landau-divergence`.
-/
import Mathlib

noncomputable section

namespace CoreLean
namespace LandauNeumann

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]

local notation "Op" => E →L[𝕜] E

/-- The series `G_π = Σ_n T^nG`. -/
def series (T G : Op) : Op := (∑' n : ℕ, T ^ n) * G

lemma norm_pow_le_half {T : Op} (hT : ‖T‖ ≤ 1 / 2) (n : ℕ) : ‖T ^ n‖ ≤ (1 / 2) ^ n := by
  induction n with
  | zero =>
    simp only [pow_zero]
    exact ContinuousLinearMap.norm_id_le
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact (norm_mul_le _ _).trans (mul_le_mul ih hT (norm_nonneg _) (by positivity))

/-- **The series converges**. -/
theorem summable_series {T : Op} (hT : ‖T‖ ≤ 1 / 2) : Summable fun n : ℕ => T ^ n :=
  Summable.of_norm_bounded (summable_geometric_of_lt_one (by norm_num) (by norm_num))
    (norm_pow_le_half hT)

lemma geom_mul {T : Op} (hT : ‖T‖ ≤ 1 / 2) : (∑' n : ℕ, T ^ n) * (1 - T) = 1 :=
  geom_series_mul_neg T (lt_of_le_of_lt hT (by norm_num))

lemma mul_geom {T : Op} (hT : ‖T‖ ≤ 1 / 2) : (1 - T) * (∑' n : ℕ, T ^ n) = 1 :=
  mul_neg_geom_series T (lt_of_le_of_lt hT (by norm_num))

/-- **`G_π` is a right inverse of `Δ_𝖺 - Δ'`**. -/
theorem series_right_inverse (Δ Δ' G : Op) (hΔG : Δ * G = 1) (hT : ‖G * Δ'‖ ≤ 1 / 2) :
    (Δ - Δ') * series (G * Δ') G = 1 := by
  -- `Δ - Δ' = Δ(1 - GΔ')`
  have e : Δ - Δ' = Δ * (1 - G * Δ') := by
    rw [mul_sub, mul_one, ← mul_assoc, hΔG, one_mul]
  unfold series
  rw [e, mul_assoc, ← mul_assoc (1 - G * Δ'), mul_geom hT, one_mul, hΔG]

/-- **`G_π` is a left inverse of `Δ_𝖺 - Δ'`**. -/
theorem series_left_inverse (Δ Δ' G : Op) (hGΔ : G * Δ = 1) (hT : ‖G * Δ'‖ ≤ 1 / 2) :
    series (G * Δ') G * (Δ - Δ') = 1 := by
  have e : G * (Δ - Δ') = 1 - G * Δ' := by rw [mul_sub, hGΔ]
  unfold series
  rw [mul_assoc, e, geom_mul hT]

/-- **The bound** `‖G_πf‖ ≤ 2‖Gf‖`. -/
theorem series_bound {T G : Op} (hT : ‖T‖ ≤ 1 / 2) (f : E) : ‖series T G f‖ ≤ 2 * ‖G f‖ := by
  have hs := summable_series hT
  unfold series
  rw [ContinuousLinearMap.mul_apply]
  have hev : (∑' n : ℕ, T ^ n) (G f) = ∑' n : ℕ, (T ^ n) (G f) :=
    (ContinuousLinearMap.apply 𝕜 E (G f)).map_tsum hs
  rw [hev]
  have hb : ∀ n : ℕ, ‖(T ^ n) (G f)‖ ≤ (1 / 2) ^ n * ‖G f‖ := fun n =>
    ((T ^ n).le_opNorm _).trans (mul_le_mul_of_nonneg_right (norm_pow_le_half hT n) (norm_nonneg _))
  have hg : Summable fun n : ℕ => (1 / 2 : ℝ) ^ n * ‖G f‖ :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_right _
  calc ‖∑' n : ℕ, (T ^ n) (G f)‖ ≤ ∑' n : ℕ, (1 / 2 : ℝ) ^ n * ‖G f‖ := tsum_of_norm_bounded hg.hasSum hb
    _ = 2 * ‖G f‖ := by
        rw [tsum_mul_right, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
        norm_num

end LandauNeumann
end CoreLean

end
