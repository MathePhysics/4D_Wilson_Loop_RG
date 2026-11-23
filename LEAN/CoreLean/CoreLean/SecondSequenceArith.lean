/-
`lem:second-sequence` of BALABAN_CORE.tex (`a021c13be348`), the step "`σ_𝒲 ≤ Ma_n`" of its proof.

* `power_le_one`: an integer power `L^k` of `L ≥ 5` which is less than `5` is at most `1`.
* `sigma_le`: from `21σ_𝒲 ≤ 100Ma_n` and `σ_𝒲/(Ma_n) = L^k`, `L ≥ 5`: `σ_𝒲 ≤ Ma_n`.
-/
import Mathlib

noncomputable section

namespace CoreLean
namespace SecondSequenceArith

/-- An integer power of `L ≥ 5` below `5` is at most `1`. -/
theorem power_le_one {L : ℝ} (hL : 5 ≤ L) (k : ℤ) (h : L ^ k < 5) : L ^ k ≤ 1 := by
  by_contra hk
  push_neg at hk
  have hL1 : 1 < L := by linarith
  have hk0 : 0 < k := by
    by_contra h0
    push_neg at h0
    have : L ^ k ≤ L ^ (0 : ℤ) := zpow_le_zpow_right₀ hL1.le h0
    rw [zpow_zero] at this
    linarith
  have : L ^ (1 : ℤ) ≤ L ^ k := zpow_le_zpow_right₀ hL1.le hk0
  rw [zpow_one] at this
  linarith

/-- **`σ_𝒲 ≤ Ma_n`.** -/
theorem sigma_le {σ M a L : ℝ} (k : ℤ) (hL : 5 ≤ L) (hMa : 0 < M * a) (h21 : 21 * σ ≤ 100 * (M * a))
    (hpow : σ / (M * a) = L ^ k) : σ ≤ M * a := by
  have h1 : L ^ k < 5 := by
    rw [← hpow, div_lt_iff₀ hMa]; linarith
  have h2 := power_le_one hL k h1
  rw [← hpow, div_le_one hMa] at h2
  exact h2

end SecondSequenceArith
end CoreLean

end
