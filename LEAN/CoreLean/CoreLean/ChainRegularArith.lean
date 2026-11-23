/-
`prop:chain-regular` of BALABAN_CORE.tex (`a021c13be348`), the step "the constants" of its proof.

With `m_⋆ = 8C_sB₃a_⋆` the minimum in `eq:a-star`, `ε₁ = max{4L², 5C_s}B₃a_⋆`, `α₀ = 4C_hC_sB₃a_⋆`:

* `eps1_counterexample`: the claim `ε₁ ≤ m_⋆` needs `4L² ≤ 8C_s`; with `C_s = max{1, 4C_ax}`, `C_ax = 59√N`
  (`cor:axial-straight`, `lem:axial-smallness`), it fails for `N = 1`, `L = 29` (and for every fixed `N` once
  `L² > 472√N`), while this part of the core takes `L ≥ 28`.
* `eps1_le_star`: the first clause of (H1), `ε₁ ≤ ε_⋆`, holds directly, since `a_⋆ ≤ ε_⋆/(8C_sB₃L²)` and
  `max{4L², 5C_s} ≤ 8C_sL²` (`C_s ≥ 1`); so only the intermediate claim is wrong.
* `eps1_repaired`: alternatively, with the prefactor `1/(max{8C_s, 4L²}B₃)` in `eq:a-star` in place of `1/(8C_sB₃)`, both
  `m_⋆ = 8C_sB₃a_⋆` and `ε₁` are at most the minimum.
* `alpha0_half`, `alpha0_consequences`: `α₀ = ½C_hm_⋆`, and the terms of `eq:a-star` with `C_h` give
  `(M_c + 1)(1 + B₂)α₀ ≤ ½a₅`, `α₀ ≤ ½L⁻²c'₄`, `(M₁ + 1)C_pfα₀ ≤ ½c₅`; and `B₂C_pfα₀ ≤ (M_c + 1)(1 + B₂)α₀` for
  `C_pf ≤ M_c + 1`.
-/
import Mathlib

noncomputable section

namespace CoreLean
namespace ChainRegularArith

/-- **The claim `ε₁ ≤ m_⋆` fails** for `N = 1`, `L = 29`: `4L² > 8C_s` with `C_s = max{1, 4·59√1}`. -/
theorem eps1_counterexample : 8 * max 1 (4 * (59 * Real.sqrt 1)) < 4 * (29 : ℝ) ^ 2 := by
  rw [Real.sqrt_one]; norm_num

/-- In general `ε₁ ≤ m_⋆` is equivalent to `4L² ≤ 8C_s` (for `B₃a_⋆ > 0`, `C_s ≥ 0`). -/
theorem eps1_le_iff {L Cs B : ℝ} (hB : 0 < B) (hCs : 0 ≤ Cs) :
    max (4 * L ^ 2) (5 * Cs) * B ≤ 8 * Cs * B ↔ 4 * L ^ 2 ≤ 8 * Cs := by
  rw [mul_le_mul_iff_of_pos_right hB, max_le_iff]
  constructor
  · exact fun h => h.1
  · exact fun h => ⟨h, by linarith⟩

/-- **The repair**: with `a_⋆ = m/(max{8C_s, 4L²}B₃)`, `8C_sB₃a_⋆ ≤ m` and `max{4L², 5C_s}B₃a_⋆ ≤ m`. -/
theorem eps1_repaired {L Cs B₃ m : ℝ} (hL : 0 < L) (hB : 0 < B₃) (hCs : 0 ≤ Cs) (hm : 0 ≤ m) :
    8 * Cs * B₃ * (m / (max (8 * Cs) (4 * L ^ 2) * B₃)) ≤ m ∧
      max (4 * L ^ 2) (5 * Cs) * B₃ * (m / (max (8 * Cs) (4 * L ^ 2) * B₃)) ≤ m := by
  have hD : 0 < max (8 * Cs) (4 * L ^ 2) * B₃ := mul_pos (lt_max_of_lt_right (by positivity)) hB
  refine ⟨?_, ?_⟩
  · rw [show 8 * Cs * B₃ * (m / (max (8 * Cs) (4 * L ^ 2) * B₃)) =
        8 * Cs * B₃ / (max (8 * Cs) (4 * L ^ 2) * B₃) * m by ring]
    apply mul_le_of_le_one_left hm
    rw [div_le_one hD]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) hB.le
  · rw [show max (4 * L ^ 2) (5 * Cs) * B₃ * (m / (max (8 * Cs) (4 * L ^ 2) * B₃)) =
        max (4 * L ^ 2) (5 * Cs) * B₃ / (max (8 * Cs) (4 * L ^ 2) * B₃) * m by ring]
    apply mul_le_of_le_one_left hm
    rw [div_le_one hD]
    apply mul_le_mul_of_nonneg_right _ hB.le
    exact max_le (le_max_right _ _) ((by linarith : 5 * Cs ≤ 8 * Cs).trans (le_max_left _ _))

/-- **The direct route to the first clause of (H1)**: `a_⋆ ≤ ε_⋆/(8C_sB₃L²)` with `C_s ≥ 1`, `L ≥ 1` gives
`ε₁ = max{4L², 5C_s}B₃a_⋆ ≤ ε_⋆`, which is what (H1) asks; the intermediate `ε₁ ≤ m_⋆` is not needed. -/
theorem eps1_le_star {L Cs B₃ a εs : ℝ} (hL : 1 ≤ L) (hCs : 1 ≤ Cs) (hB : 0 < B₃) (ha0 : 0 ≤ a)
    (ha : a ≤ εs / (8 * Cs * B₃ * L ^ 2)) : max (4 * L ^ 2) (5 * Cs) * B₃ * a ≤ εs := by
  have hD : 0 < 8 * Cs * B₃ * L ^ 2 := by positivity
  have h1 : a * (8 * Cs * B₃ * L ^ 2) ≤ εs := (le_div_iff₀ hD).1 ha
  have hmax : max (4 * L ^ 2) (5 * Cs) ≤ 8 * Cs * L ^ 2 := by
    have hL2 : 1 ≤ L ^ 2 := by nlinarith
    exact max_le (by nlinarith) (by nlinarith)
  calc max (4 * L ^ 2) (5 * Cs) * B₃ * a ≤ 8 * Cs * L ^ 2 * B₃ * a := by
        apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hmax hB.le) ha0
    _ = a * (8 * Cs * B₃ * L ^ 2) := by ring
    _ ≤ εs := h1

/-- `α₀ = 4C_hC_sB₃a_⋆ = ½C_hm_⋆`. -/
theorem alpha0_half (Ch Cs B₃ a : ℝ) : 4 * Ch * Cs * B₃ * a = 1 / 2 * Ch * (8 * Cs * B₃ * a) := by ring

/-- **The consequences of the terms with `C_h`** of `eq:a-star`. -/
theorem alpha0_consequences {Ch m Mc B₂ a₅ L c₄ M₁ Cpf c₅ : ℝ} (hCh : 0 < Ch) (hMc : 0 ≤ Mc) (hB₂ : 0 ≤ B₂)
    (hL : 0 < L) (hM₁ : 0 ≤ M₁) (hCpf : 0 < Cpf) (hm0 : 0 ≤ m)
    (h1 : m ≤ a₅ / ((Mc + 1) * (1 + B₂) * Ch)) (h2 : m ≤ c₄ / (L ^ 2 * Ch))
    (h3 : m ≤ c₅ / ((M₁ + 1) * Cpf * Ch)) :
    (Mc + 1) * (1 + B₂) * (1 / 2 * Ch * m) ≤ 1 / 2 * a₅ ∧ 1 / 2 * Ch * m ≤ 1 / 2 * (c₄ / L ^ 2) ∧
      (M₁ + 1) * Cpf * (1 / 2 * Ch * m) ≤ 1 / 2 * c₅ := by
  have p1 : 0 < (Mc + 1) * (1 + B₂) * Ch := by positivity
  have p2 : 0 < L ^ 2 * Ch := by positivity
  have p3 : 0 < (M₁ + 1) * Cpf * Ch := by positivity
  rw [le_div_iff₀ p1] at h1
  rw [le_div_iff₀ p2] at h2
  rw [le_div_iff₀ p3] at h3
  refine ⟨by nlinarith, ?_, by nlinarith⟩
  have hL2 : 0 < L ^ 2 := by positivity
  have e : 1 / 2 * (c₄ / L ^ 2) = (1 / 2 * c₄) / L ^ 2 := by ring
  rw [e, le_div_iff₀ hL2]
  nlinarith

/-- `B₂C_pfα₀ ≤ (M_c + 1)(1 + B₂)α₀` for `C_pf ≤ M_c + 1`. -/
theorem fourth_condition {B₂ Cpf Mc α : ℝ} (hB₂ : 0 ≤ B₂) (hα : 0 ≤ α) (hC : Cpf ≤ Mc + 1) (hCpf : 0 ≤ Cpf) :
    B₂ * Cpf * α ≤ (Mc + 1) * (1 + B₂) * α := by
  have h1 : B₂ * Cpf ≤ (Mc + 1) * B₂ := by nlinarith
  have h2 : (Mc + 1) * B₂ ≤ (Mc + 1) * (1 + B₂) := by nlinarith
  exact mul_le_mul_of_nonneg_right (h1.trans h2) hα

end ChainRegularArith
end CoreLean

end
