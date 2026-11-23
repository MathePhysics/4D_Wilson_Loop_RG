/-
`cor:axial-straight` of BALABAN_CORE.tex (`a7d5e1f955b0`), in abstract form: the downward induction on the
order `i` of the averages, with `lem:axial-smallness` at each step as a hypothesis.

Bonds of the order `i` (`Bd i`) inside the two blocks `𝖡` carry the averages `M^i(U)(b)` and the targets
`s(b)`; each bond `b` of the order `i < j` has a bond `c(b)` of the order `i + 1` (the bond `c̃` of the proof)
and a value `V₀(b)` of the reference field, which is either `s(b)` (both ends in one block of the order
`i + 1`) or `M^{i+1}(U)(c(b))` with `s(b) = s(c(b))`. `lem:axial-smallness` gives
`‖M^i(U)(b) - V₀(b)‖ ≤ C_ax α₀` with `α₀ = 2αL^{-2(j-i-1)}`. Then `‖M^i(U)(b) - s(b)‖ ≤ σ_i α ≤ 4C_ax α`
with `σ_j = 0`, `σ_i = σ_{i+1} + 2C_ax L^{-2(j-i-1)}`.
-/
import Mathlib

noncomputable section

namespace CoreLean

namespace AxialStraight

/-- `σ_i = Σ_{i ≤ m < j} 2C L^{-2(j-m-1)}`, written with `k = j - i` steps: `σ(0) = 0`,
`σ(k+1) = σ(k) + 2C L^{-2k}`. -/
def sigma (C L : ℝ) : ℕ → ℝ
  | 0 => 0
  | k + 1 => sigma C L k + 2 * C * (L ^ 2)⁻¹ ^ k

/-- `σ ≤ 2C(1 - L^{-2})⁻¹ ≤ 4C` for `L ≥ 2`, `C ≥ 0`. -/
lemma sigma_le (C L : ℝ) (hC : 0 ≤ C) (hL : 2 ≤ L) (k : ℕ) : sigma C L k ≤ 4 * C := by
  have hq0 : 0 ≤ (L ^ 2)⁻¹ := by positivity
  have hq : (L ^ 2)⁻¹ ≤ 1 / 4 := by
    rw [inv_eq_one_div]; gcongr; nlinarith
  -- `σ(k) = 2C Σ_{m<k} q^m` and `Σ_{m<k} q^m ≤ (1 - q)⁻¹ ≤ 4/3`
  have e : ∀ k, sigma C L k = 2 * C * ∑ m ∈ Finset.range k, (L ^ 2)⁻¹ ^ m := by
    intro k
    induction k with
    | zero => simp [sigma]
    | succ k ih => rw [sigma, ih, Finset.sum_range_succ]; ring
  rw [e]
  have hg : ∑ m ∈ Finset.range k, (L ^ 2)⁻¹ ^ m ≤ 2 := by
    calc ∑ m ∈ Finset.range k, (L ^ 2)⁻¹ ^ m ≤ ∑ m ∈ Finset.range k, (1 / 4 : ℝ) ^ m :=
          Finset.sum_le_sum fun m _ => pow_le_pow_left₀ hq0 hq m
      _ ≤ 2 := by
        have := geom_sum_Ico_le_of_lt_one (x := (1 / 4 : ℝ)) (m := 0) (n := k) (by norm_num)
          (by norm_num)
        rw [Finset.range_eq_Ico]
        refine this.trans ?_
        norm_num
  nlinarith

variable {Bd : ℕ → Type*} {Gp : Type*} [SeminormedAddCommGroup Gp]

/-- `cor:axial-straight`, the induction. For bonds of the order `i ≤ j`: `Mi i b` is `M^i(U)(b)`, `s i b`
the target, `V0 i b` the reference value, `c i b` the bond of the order `i + 1` (for `i < j` only: there is
no bond of the order `j + 1` with both ends in `𝖡`). Hypotheses: at the order
`j`, `M^j(U) = s` (the bond `c'` and its reverse); for `i < j`, `V0 i b = s i b` or
(`V0 i b = Mi (i + 1) (c i b)` and `s i b = s (i + 1) (c i b)`), and `lem:axial-smallness` gives
`‖Mi i b - V0 i b‖ ≤ C_ax · 2αL^{-2(j-i-1)}`. Then `‖Mi i b - s i b‖ ≤ σ(j - i) α ≤ 4C_ax α` for
`i ≤ j` (`eq:axial-straight` with `C_s ≥ 4C_ax`). -/
theorem axial_straight (j : ℕ) (C L α : ℝ) (hC : 0 ≤ C) (hL : 2 ≤ L) (hα : 0 ≤ α)
    (Mi s V0 : ∀ i, Bd i → Gp) (c : ∀ i, i < j → Bd i → Bd (i + 1))
    (htop : ∀ b, Mi j b = s j b)
    (hV0 : ∀ i (hi : i < j), ∀ b, V0 i b = s i b ∨
      (V0 i b = Mi (i + 1) (c i hi b) ∧ s i b = s (i + 1) (c i hi b)))
    (hsmall : ∀ i, i < j → ∀ b, ‖Mi i b - V0 i b‖ ≤ C * (2 * α * (L ^ 2)⁻¹ ^ (j - i - 1)))
    (i : ℕ) (hi : i ≤ j) (b : Bd i) :
    ‖Mi i b - s i b‖ ≤ sigma C L (j - i) * α ∧ ‖Mi i b - s i b‖ ≤ 4 * C * α := by
  have hsig0 : ∀ k, 0 ≤ sigma C L k := by
    intro k
    induction k with
    | zero => simp [sigma]
    | succ k ih => rw [sigma]; positivity
  -- induction on the number `k = j - i` of steps below the order `j`
  have hfin : ∀ k, ∀ i, j - i = k → i ≤ j → ∀ b : Bd i, ‖Mi i b - s i b‖ ≤ sigma C L k * α := by
    intro k
    induction k with
    | zero =>
      intro i hk hi b
      have : i = j := by omega
      subst this
      simp [sigma, htop b]
    | succ k ih =>
      intro i hk hi b
      have hij : i < j := by omega
      have hexp : j - i - 1 = k := by omega
      have hs := hsmall i hij b
      rw [hexp] at hs
      have hsig : sigma C L (k + 1) * α = sigma C L k * α + C * (2 * α * (L ^ 2)⁻¹ ^ k) := by
        rw [sigma]; ring
      rw [hsig]
      have hsk0 : 0 ≤ sigma C L k * α := mul_nonneg (hsig0 k) hα
      rcases hV0 i hij b with h | ⟨h, hs'⟩
      · calc ‖Mi i b - s i b‖ = ‖Mi i b - V0 i b‖ := by rw [h]
          _ ≤ sigma C L k * α + C * (2 * α * (L ^ 2)⁻¹ ^ k) := by linarith
      · have hc := ih (i + 1) (by omega) (by omega) (c i hij b)
        calc ‖Mi i b - s i b‖ = ‖(Mi i b - V0 i b) + (Mi (i + 1) (c i hij b) - s (i + 1) (c i hij b))‖ := by
              rw [h, hs', sub_add_sub_cancel]
          _ ≤ ‖Mi i b - V0 i b‖ + ‖Mi (i + 1) (c i hij b) - s (i + 1) (c i hij b)‖ := norm_add_le _ _
          _ ≤ sigma C L k * α + C * (2 * α * (L ^ 2)⁻¹ ^ k) := by linarith
  have h1 := hfin (j - i) i rfl hi b
  exact ⟨h1, h1.trans (mul_le_mul_of_nonneg_right (sigma_le C L hC hL _) hα)⟩

end AxialStraight

end CoreLean

end
