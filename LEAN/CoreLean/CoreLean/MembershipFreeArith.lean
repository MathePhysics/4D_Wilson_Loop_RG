/-
`cor:membership-free` of BALABAN_CORE.tex (`a021c13be348`), the two numerical steps of its proof, with
`1 + β₀ ≤ √2` and `ρ_{0,i} ≤ (1 + β₀)(i - l)^{1/2}ρ_{0,l}` (`lem:factor-field`(i)), `s = i - l ≥ 1`.

* `field_factor`: `L^{-s}(1 + β₀)s^{1/2} ≤ 2^{-s}` for `L ≥ 4`, so that `L^{-(i-l)}cρ_{0,i} ≤ c2^{-(i-l)}ρ_{0,l}`.
* `current_factor`: `L^{-3s}(1 + β₀)s^{1/2} ≤ 1/16` for `L ≥ 4`.
-/
import Mathlib

noncomputable section

namespace CoreLean
namespace MembershipFreeArith

/-- `√2·√s ≤ 2^s` for `s ≥ 1`. -/
lemma sqrt_le_two_pow (s : ℕ) : Real.sqrt 2 * Real.sqrt s ≤ 2 ^ s := by
  rw [← Real.sqrt_mul (by norm_num)]
  rw [Real.sqrt_le_left (by positivity)]
  have : 2 * (s : ℝ) ≤ 4 ^ s := by
    induction s with
    | zero => norm_num
    | succ n ih => push_cast; rw [pow_succ]; nlinarith [one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 4) (n := n)]
  calc 2 * (s : ℝ) ≤ 4 ^ s := this
    _ = (2 ^ s) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num

/-- `L^{-s}c√s ≤ 2^{-s}` for `L ≥ 4`, `0 ≤ c ≤ √2`. -/
theorem field_factor {L c : ℝ} (s : ℕ) (hL : 4 ≤ L) (hc0 : 0 ≤ c) (hc : c ≤ Real.sqrt 2) :
    (L ^ s)⁻¹ * c * Real.sqrt s ≤ (2 ^ s)⁻¹ := by
  have h1 : c * Real.sqrt s ≤ 2 ^ s :=
    (mul_le_mul_of_nonneg_right hc (Real.sqrt_nonneg _)).trans (sqrt_le_two_pow s)
  have h4 : (4 : ℝ) ^ s ≤ L ^ s := pow_le_pow_left₀ (by norm_num) hL s
  have e4 : (4 : ℝ) ^ s = 2 ^ s * 2 ^ s := by rw [← mul_pow]; norm_num
  rw [mul_assoc, inv_mul_le_iff₀ (by positivity)]
  have h2 : (0 : ℝ) < 2 ^ s := by positivity
  calc c * Real.sqrt s ≤ 2 ^ s := h1
    _ = 2 ^ s * 2 ^ s * (2 ^ s)⁻¹ := by field_simp
    _ ≤ L ^ s * (2 ^ s)⁻¹ := by rw [← e4]; exact mul_le_mul_of_nonneg_right h4 (by positivity)

/-- `L^{-3s}c√s ≤ 1/16` for `L ≥ 4`, `s ≥ 1`, `0 ≤ c ≤ √2`. -/
theorem current_factor {L c : ℝ} (s : ℕ) (hs : 1 ≤ s) (hL : 4 ≤ L) (hc0 : 0 ≤ c) (hc : c ≤ Real.sqrt 2) :
    (L ^ (3 * s))⁻¹ * c * Real.sqrt s ≤ 1 / 16 := by
  have h := field_factor s hL hc0 hc
  have hL1 : 1 ≤ L := by linarith
  have hLs : (L ^ s)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hL1)
  have e : (L ^ (3 * s))⁻¹ = (L ^ s)⁻¹ * ((L ^ s)⁻¹ * (L ^ s)⁻¹) := by
    rw [show 3 * s = s + s + s by ring, pow_add, pow_add]; field_simp
  have h16 : (L ^ s)⁻¹ * (L ^ s)⁻¹ ≤ 1 / 16 := by
    have : (L ^ s)⁻¹ ≤ 1 / 4 := by
      rw [inv_le_comm₀ (by positivity) (by norm_num)]
      calc (1 / 4 : ℝ)⁻¹ = 4 := by norm_num
        _ ≤ L := hL
        _ = L ^ 1 := (pow_one L).symm
        _ ≤ L ^ s := pow_le_pow_right₀ hL1 hs
    have h0 : 0 ≤ (L ^ s)⁻¹ := by positivity
    nlinarith
  have h2 : (2 ^ s)⁻¹ ≤ (1 : ℝ) := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  have hpos : 0 ≤ c * Real.sqrt s := by positivity
  calc (L ^ (3 * s))⁻¹ * c * Real.sqrt s = ((L ^ s)⁻¹ * c * Real.sqrt s) * ((L ^ s)⁻¹ * (L ^ s)⁻¹) := by
        rw [e]; ring
    _ ≤ 1 * (1 / 16) := by
        apply mul_le_mul (h.trans h2) h16 (by positivity) (by norm_num)
    _ = 1 / 16 := one_mul _

end MembershipFreeArith
end CoreLean

end
