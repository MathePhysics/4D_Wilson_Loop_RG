/-
`lem:collar-geometry` of BALABAN_CORE.tex (`a021c13be348`), the arithmetic of (i) and of (ii).

* (i): with `d ≥ 27M_c(|i' - j'| - 1)` (`lem:distance`(ii)) and `27M_c·δ_⋆/8 ≥ log L` (the second condition of
  `eq:layer-condition`), `L^{|i' - j'| - 1} ≤ e^{δ_⋆d/8}`, so that a ratio of spacings `L^{|i' - j'|}` is at most
  `Le^{δ_⋆d/8}` (`spacing_ratio`).
* (ii), the exponents of `eq:sum-composition`: for `d(y, y'') ≤ d(y, y') + d(y', y'')`, `κ' > 0` and
  `κ'' = min{κ - (m + 1)/8, κ'}`, `(κ - m/8)d(y, y') + κ'd(y', y'') ≥ κ''d(y, y'') + d(y, y')/8`
  (`exponent_split`), **provided `κ ≥ (m + 1)/8`**, i.e. `κ'' ≥ 0`. The core states (ii) for all `κ, κ' > 0`; its
  proof uses `κ''d(y, y'') ≤ κ''(d(y, y') + d(y', y''))`, which needs `κ'' ≥ 0`. All uses of `eq:sum-composition` in
  the core have `κ ≥ 5/4`, so that only the statement is affected.
-/
import Mathlib

noncomputable section

namespace CoreLean
namespace CollarGeometry

/-- **(i)**: `L^{k - 1} ≤ e^{δ_⋆d/8}` for `d ≥ 27M_c(k - 1)` and `27M_cδ_⋆/8 ≥ log L`. -/
theorem spacing_ratio {L δ Mc d : ℝ} (hL : 1 ≤ L) (hδ : 0 ≤ δ) (hMc : 0 < Mc) (k : ℕ) (hk : 1 ≤ k)
    (hd : 27 * Mc * ((k : ℝ) - 1) ≤ d) (hcond : Real.log L ≤ 27 * Mc * δ / 8) :
    L ^ (k - 1) ≤ Real.exp (δ * d / 8) := by
  have hL0 : 0 < L := by linarith
  rw [← Real.exp_log (pow_pos hL0 (k - 1)), Real.log_pow]
  refine Real.exp_le_exp.2 ?_
  have hk1 : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by rw [Nat.cast_sub hk, Nat.cast_one]
  rw [hk1]
  have hk0 : 0 ≤ (k : ℝ) - 1 := by rw [← hk1]; exact Nat.cast_nonneg _
  calc ((k : ℝ) - 1) * Real.log L ≤ ((k : ℝ) - 1) * (27 * Mc * δ / 8) :=
        mul_le_mul_of_nonneg_left hcond hk0
    _ = δ / 8 * (27 * Mc * ((k : ℝ) - 1)) := by ring
    _ ≤ δ / 8 * d := mul_le_mul_of_nonneg_left hd (by positivity)
    _ = δ * d / 8 := by ring

/-- **(ii)**, the exponents of `eq:sum-composition`, under `κ ≥ (m + 1)/8`. -/
theorem exponent_split {κ κ' m d₁ d₂ d₁₃ : ℝ} (hκ : (m + 1) / 8 ≤ κ) (hκ' : 0 < κ') (hd₁ : 0 ≤ d₁) (hd₂ : 0 ≤ d₂)
    (htri : d₁₃ ≤ d₁ + d₂) :
    min (κ - (m + 1) / 8) κ' * d₁₃ + d₁ / 8 ≤ (κ - m / 8) * d₁ + κ' * d₂ := by
  set k'' := min (κ - (m + 1) / 8) κ'
  have hk0 : 0 ≤ k'' := le_min (by linarith) hκ'.le
  have h1 : k'' ≤ κ - (m + 1) / 8 := min_le_left _ _
  have h2 : k'' ≤ κ' := min_le_right _ _
  calc k'' * d₁₃ + d₁ / 8 ≤ k'' * (d₁ + d₂) + d₁ / 8 := by gcongr
    _ = k'' * d₁ + k'' * d₂ + d₁ / 8 := by ring
    _ ≤ (κ - (m + 1) / 8) * d₁ + κ' * d₂ + d₁ / 8 := by gcongr
    _ = (κ - m / 8) * d₁ + κ' * d₂ := by ring

end CollarGeometry
end CoreLean

end
