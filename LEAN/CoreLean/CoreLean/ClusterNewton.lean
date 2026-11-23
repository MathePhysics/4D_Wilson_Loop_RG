/-
The logarithmic derivative of a product of linear factors, for the cluster expansion of `thm:polymer-logarithm` of
BALABAN_CORE.tex (`5bbe1bc62521`): in `ℂ⟦X⟧`, `G = Π_{ρ ∈ M}(1 - ρX)` satisfies `X·G' = -S·G` with
`S = Σ_{k ≥ 1}p_kX^k`, `p_k = Σ_{ρ ∈ M}ρ^k` (the identities of Newton). If another series `B = Σ_kb_kX^k` satisfies
`X·G' = -(X·B')·G`, then `kb_k = p_k`, since `G` has the constant coefficient `1` and `ℂ⟦X⟧` has no zero divisors.
-/
import Mathlib

open PowerSeries

noncomputable section

namespace CoreLean
namespace Newton

/-- `Σ_kρ^kX^k = (1 - ρX)⁻¹`. -/
def geo (ρ : ℂ) : ℂ⟦X⟧ := PowerSeries.mk fun k => ρ ^ k

lemma coeff_CX_mul (ρ : ℂ) (f : ℂ⟦X⟧) (n : ℕ) :
    coeff (n + 1) (C ρ * X * f) = ρ * coeff n f := by
  rw [mul_assoc, coeff_C_mul, coeff_succ_X_mul]

lemma coeff_CX_mul_zero (ρ : ℂ) (f : ℂ⟦X⟧) : coeff 0 (C ρ * X * f) = 0 := by
  rw [mul_assoc, coeff_C_mul, coeff_zero_X_mul, mul_zero]

lemma geo_mul (ρ : ℂ) : (1 - C ρ * X) * geo ρ = 1 := by
  ext n
  rw [sub_mul, one_mul, map_sub, coeff_one]
  rcases n with _ | n
  · rw [coeff_CX_mul_zero]; simp [geo]
  · rw [coeff_CX_mul]; simp [geo, pow_succ]; ring

/-- `S_M = Σ_{ρ ∈ M}ρX(1 - ρX)⁻¹ = Σ_{k ≥ 1}p_kX^k`. -/
def S (M : Multiset ℂ) : ℂ⟦X⟧ := (M.map fun ρ => C ρ * X * geo ρ).sum

lemma coeff_S (M : Multiset ℂ) (k : ℕ) :
    coeff k (S M) = if k = 0 then 0 else (M.map fun ρ => ρ ^ k).sum := by
  unfold S
  rw [map_multiset_sum, Multiset.map_map]
  rcases k with _ | k
  · simp only [Function.comp_def, coeff_CX_mul_zero, Multiset.map_const', Multiset.sum_replicate, smul_zero,
      if_true]
  · simp only [Function.comp_def, coeff_CX_mul, geo, coeff_mk, Nat.succ_ne_zero, if_false, pow_succ']

/-- `G_M = Π_{ρ ∈ M}(1 - ρX)`. -/
def G (M : Multiset ℂ) : ℂ⟦X⟧ := (M.map fun ρ => 1 - C ρ * X).prod

/-- **The logarithmic derivative**: `X·G_M' = -S_M·G_M`. -/
theorem X_deriv_G (M : Multiset ℂ) : X * (PowerSeries.derivative (R := ℂ)) (G M) = -(S M * G M) := by
  induction M using Multiset.induction_on with
  | empty => simp [G, S]
  | cons ρ M ih =>
    have hG : G (ρ ::ₘ M) = (1 - C ρ * X) * G M := by simp [G]
    have hS : S (ρ ::ₘ M) = C ρ * X * geo ρ + S M := by simp [S]
    rw [hG, hS, Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_sub, Derivation.map_one_eq_zero,
      derivative_C_mul_X]
    have hgeo := geo_mul ρ
    linear_combination (1 - C ρ * X) * ih + C ρ * X * G M * hgeo

/-- **Cancellation**: if `X·G_M' = -T·G_M`, then `T = S_M`. -/
theorem eq_S_of_deriv (M : Multiset ℂ) (T : ℂ⟦X⟧) (hT : X * (PowerSeries.derivative (R := ℂ)) (G M) = -(T * G M)) : T = S M := by
  have hG0 : G M ≠ 0 := by
    intro h
    have : constantCoeff (G M) = 1 := by
      unfold G
      rw [map_multiset_prod, Multiset.map_map]
      simp [Function.comp_def]
    rw [h, map_zero] at this
    exact zero_ne_one this
  have h := X_deriv_G M
  rw [hT] at h
  have : (T - S M) * G M = 0 := by linear_combination -h
  exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hG0)

end Newton
end CoreLean

end
