/-
`lem:chain-sequences` of BALABAN_CORE.tex (`a021c13be348`), the arithmetic of its proof (`L ≥ 28`, the convention of
this part of the core).

* `third_fact`: `MR_{h+1}a_{h+1} = LMR_{h+1}a_h ≥ L³M_ca_h` for `M ≥ L²M_c`, `R_{h+1} ≥ 1`, and
  `ρ_h = 2(27 + L)M_ca_{h-1} ≤ 4M_ca_h` for `a_h = La_{h-1}`, `L ≥ 27`.
* `separation_h`: `(L³ - 4)M_ca_h > 27M_ca_h` for `L ≥ 4` (so for `L ≥ 28`), the distance from the complement of
  `Ω_h(𝒴)` being at least `L³M_ca_h - ρ_h ≥ (L³ - 4)M_ca_h`.
* `separation_new`: `2MR_na_n ≥ 2LMa_i > 27Ma_i` for `a_n ≥ La_i`, `R_n ≥ 1`, `L ≥ 14`.
-/
import Mathlib

noncomputable section

namespace CoreLean
namespace ChainSequencesArith

/-- **The third fact.** -/
theorem third_fact {L M Mc R a a' : ℝ} (hL : 27 ≤ L) (hMc : 0 ≤ Mc) (hM : L ^ 2 * Mc ≤ M) (hR : 1 ≤ R)
    (ha : 0 ≤ a') (haa : a = L * a') :
    L ^ 3 * Mc * a ≤ M * R * (L * a) ∧ 2 * (27 + L) * Mc * a' ≤ 4 * Mc * a := by
  have hL0 : 0 ≤ L := by linarith
  have ha0 : 0 ≤ a := by rw [haa]; positivity
  refine ⟨?_, ?_⟩
  · have hM0 : 0 ≤ M := (by positivity : (0 : ℝ) ≤ L ^ 2 * Mc).trans hM
    have h1 : L ^ 2 * Mc ≤ M * R := hM.trans (le_mul_of_one_le_right hM0 hR)
    have h2 : L ^ 2 * Mc * (L * a) ≤ M * R * (L * a) := mul_le_mul_of_nonneg_right h1 (by positivity)
    nlinarith
  · rw [haa]
    have : 2 * (27 + L) ≤ 4 * L := by linarith
    have := mul_le_mul_of_nonneg_right this (mul_nonneg hMc ha)
    nlinarith

/-- **The separation at `i = h`**: `L³ - 4 > 27` for `L ≥ 4`. -/
theorem separation_h {L Mc a : ℝ} (hL : 4 ≤ L) (hMc : 0 < Mc) (ha : 0 < a) :
    27 * Mc * a < (L ^ 3 - 4) * Mc * a := by
  have h3 : 64 ≤ L ^ 3 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 4) hL 3
    norm_num at this; linarith
  have : 27 < L ^ 3 - 4 := by linarith
  have hp : 0 < Mc * a := mul_pos hMc ha
  nlinarith

/-- **The separation of the new sequence**: `2MR_na_n ≥ 2LMa_i > 27Ma_i`. -/
theorem separation_new {L M R an ai : ℝ} (hL : 14 ≤ L) (hM : 0 < M) (hR : 1 ≤ R) (hai : 0 < ai)
    (han : L * ai ≤ an) : 2 * L * M * ai ≤ 2 * M * R * an ∧ 27 * M * ai < 2 * L * M * ai := by
  have han0 : 0 ≤ an := by nlinarith
  refine ⟨?_, ?_⟩
  · have h1 : L * ai ≤ R * an := by nlinarith
    nlinarith
  · have : 27 < 2 * L := by linarith
    have hp : 0 < M * ai := mul_pos hM hai
    nlinarith

end ChainSequencesArith
end CoreLean

end
