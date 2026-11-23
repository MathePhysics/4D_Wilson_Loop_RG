/-
`lem:third-exists` of BALABAN_CORE.tex (`a021c13be348`), the consequences of `eq:a-star` used in its proof: with
`a_⋆ = m/(8C_sB₃)`, `m ≤ ε_⋆/L²`, `m ≤ c₂/L²`, `m ≤ c_s`, `C_s ≥ 1`:

* `two_L2`: `2L²B₃a_⋆ ≤ c₂`;
* `four_L2`: `4L²B₃a_⋆ ≤ ε_⋆`;
* `two_B3`: `2B₃a_⋆ ≤ c_s`.
-/
import Mathlib

noncomputable section

namespace CoreLean
namespace AStarConsequences

variable {Cs B₃ L m : ℝ}

lemma key (hCs : 1 ≤ Cs) (hB : 0 < B₃) (hm : 0 ≤ m) (k : ℝ) (hk : 0 ≤ k) (hk4 : k ≤ 4) :
    k * B₃ * (m / (8 * Cs * B₃)) ≤ m / 2 := by
  have hD : 0 < 8 * Cs * B₃ := by positivity
  rw [show k * B₃ * (m / (8 * Cs * B₃)) = k / (8 * Cs) * m by field_simp]
  have : k / (8 * Cs) ≤ 1 / 2 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  nlinarith

/-- `2L²B₃a_⋆ ≤ c₂`. -/
theorem two_L2 {c₂ : ℝ} (hCs : 1 ≤ Cs) (hB : 0 < B₃) (hL : 0 < L) (hm : 0 ≤ m) (hc : m ≤ c₂ / L ^ 2) :
    2 * L ^ 2 * B₃ * (m / (8 * Cs * B₃)) ≤ c₂ := by
  have h := key hCs hB hm 2 (by norm_num) (by norm_num)
  have hL2 : 0 < L ^ 2 := by positivity
  have hc' : m * L ^ 2 ≤ c₂ := (le_div_iff₀ hL2).1 hc
  have e : 2 * L ^ 2 * B₃ * (m / (8 * Cs * B₃)) = L ^ 2 * (2 * B₃ * (m / (8 * Cs * B₃))) := by ring
  rw [e]
  nlinarith

/-- `4L²B₃a_⋆ ≤ ε_⋆`. -/
theorem four_L2 {εs : ℝ} (hCs : 1 ≤ Cs) (hB : 0 < B₃) (hL : 0 < L) (hm : 0 ≤ m) (hc : m ≤ εs / L ^ 2) :
    4 * L ^ 2 * B₃ * (m / (8 * Cs * B₃)) ≤ εs := by
  have h := key hCs hB hm 4 (by norm_num) (by norm_num)
  have hL2 : 0 < L ^ 2 := by positivity
  have hc' : m * L ^ 2 ≤ εs := (le_div_iff₀ hL2).1 hc
  have e : 4 * L ^ 2 * B₃ * (m / (8 * Cs * B₃)) = L ^ 2 * (4 * B₃ * (m / (8 * Cs * B₃))) := by ring
  rw [e]
  nlinarith

/-- `2B₃a_⋆ ≤ c_s`. -/
theorem two_B3 {cs : ℝ} (hCs : 1 ≤ Cs) (hB : 0 < B₃) (hm : 0 ≤ m) (hc : m ≤ cs) :
    2 * B₃ * (m / (8 * Cs * B₃)) ≤ cs := by
  have h := key hCs hB hm 2 (by norm_num) (by norm_num)
  linarith

end AStarConsequences
end CoreLean

end
