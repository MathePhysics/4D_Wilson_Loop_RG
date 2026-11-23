/-
`lem:parametrix-walks`(iii) of BALABAN_CORE.tex (`a021c13be348`), the identity `eq:parametrix` and the inverse, in
abstract form. In a ring (the operators on the data), with `x` central, restrictions `1_{S_□}`, real cut-offs `h̄_□`
with `h̄_□ = h̄_□1_{S_□}` and `Σ_□h̄_□² = I`, local inverses `Γ_□ = 1_{S_□}Γ_□` with `F_□Γ_□ = 1_{S_□}`, and
`1_{S_□}(x + 𝒜)1_{S_□} = F_□ + E_□`:

* `(x + 𝒜)C₀ = I - Θ` with `C₀ = Σ_□h̄_□Γ_□h̄_□` and `Θ = -Σ_□([𝒜, h̄_□] + h̄_□E_□)Γ_□h̄_□` (`parametrix_identity`);
* in a complete normed ring, if `‖Θ‖ ≤ ½` and `x + 𝒜` has a left inverse (in finite dimension a right inverse is
  two-sided), then `(x + 𝒜)⁻¹ = C₀(I - Θ)⁻¹ = C₀Σ_nΘⁿ` (`parametrix_inverse`).
-/
import Mathlib

open Finset

noncomputable section

namespace CoreLean
namespace Parametrix

variable {R : Type*} [Ring R]

/-- **`eq:parametrix`**. -/
theorem parametrix_identity {ι : Type*} (s : Finset ι) (x A : R) (hx : ∀ y : R, x * y = y * x)
    (h oneS Γ F E : ι → R) (hh : ∀ i, h i = h i * oneS i) (hΓ : ∀ i, Γ i = oneS i * Γ i)
    (hFΓ : ∀ i, F i * Γ i = oneS i) (hFE : ∀ i, oneS i * (x + A) * oneS i = F i + E i)
    (hsum : ∑ i ∈ s, h i * h i = 1) :
    (x + A) * ∑ i ∈ s, h i * Γ i * h i =
      1 - (-∑ i ∈ s, ((A * h i - h i * A) + h i * E i) * Γ i * h i) := by
  rw [sub_neg_eq_add, Finset.mul_sum, ← hsum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  -- `h(x + A)Γh = h1_S(x + A)1_SΓh = h(F + E)Γh = h² + hEΓh`
  have h1 : h i * (x + A) * Γ i * h i = h i * h i + h i * E i * Γ i * h i := by
    calc h i * (x + A) * Γ i * h i = h i * oneS i * (x + A) * (oneS i * Γ i) * h i := by rw [← hh, ← hΓ]
      _ = h i * (oneS i * (x + A) * oneS i) * Γ i * h i := by simp only [mul_assoc]
      _ = h i * (F i + E i) * Γ i * h i := by rw [hFE]
      _ = h i * (F i * Γ i) * h i + h i * E i * Γ i * h i := by simp only [mul_add, add_mul, mul_assoc]
      _ = h i * oneS i * h i + h i * E i * Γ i * h i := by rw [hFΓ, mul_assoc]
      _ = h i * h i + h i * E i * Γ i * h i := by rw [← hh]
  -- `(x + A)h = h(x + A) + [A, h]`, `x` being central
  have h2 : (x + A) * h i = h i * (x + A) + (A * h i - h i * A) := by
    rw [mul_add, add_mul, hx]; abel
  calc (x + A) * (h i * Γ i * h i) = ((x + A) * h i) * Γ i * h i := by simp only [mul_assoc]
    _ = (h i * (x + A) + (A * h i - h i * A)) * Γ i * h i := by rw [h2]
    _ = h i * (x + A) * Γ i * h i + (A * h i - h i * A) * Γ i * h i := by simp only [add_mul]
    _ = h i * h i + (((A * h i - h i * A) + h i * E i) * Γ i * h i) := by rw [h1]; simp only [add_mul]; abel

/-- **The inverse by the parametrix**: `(x + 𝒜)⁻¹ = C₀(I - Θ)⁻¹` when `‖Θ‖ ≤ ½`. -/
theorem parametrix_inverse {S : Type*} [NormedRing S] [CompleteSpace S] (X C₀ Θ Xinv : S)
    (hpar : X * C₀ = 1 - Θ) (hΘ : ‖Θ‖ < 1) (hleft : Xinv * X = 1) :
    Xinv = C₀ * ∑' n : ℕ, Θ ^ n := by
  have hgeo : (1 - Θ) * ∑' n : ℕ, Θ ^ n = 1 := mul_neg_geom_series Θ hΘ
  calc Xinv = Xinv * ((1 - Θ) * ∑' n : ℕ, Θ ^ n) := by rw [hgeo, mul_one]
    _ = Xinv * (X * C₀) * ∑' n : ℕ, Θ ^ n := by rw [hpar]; simp only [mul_assoc]
    _ = C₀ * ∑' n : ℕ, Θ ^ n := by rw [← mul_assoc, hleft, one_mul]

end Parametrix
end CoreLean

end
