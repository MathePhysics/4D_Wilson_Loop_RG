/-
`lem:critical-current` of BALABAN_CORE.tex (`a021c13be348`), the two abstract steps of its proof.
* *The current is a transposed average* (`current_transposed`): in finite-dimensional real inner product spaces (the
  `1`-forms on the bonds of `W` with the pairing `eq:pairing`, the functions on `𝐁₁^W` with `Σ_c a_c⁴tr μ(c)ν(c)`), a
  vector `J` orthogonal to the kernel of `Q` is `Q^*μ` for some `μ`, the orthogonal complement of the kernel being the
  range of the adjoint.
* *The inverse of the test fields* (`test_inverse`, `eq:test-inverse`): in a complete normed ring with `‖1‖ = 1` (the
  operators on the functions on `𝐁₁^W` with the norm `‖ν‖_w = Σ_c a_c|ν(c)|`), if `𝓔₁² = 0`, `‖𝓔₁‖ ≤ C₁`, `‖𝓔₀‖ ≤ C₀ε`,
  and `C₀(1 + C₁)ε ≤ 1/2`, then `I + 𝓔₀ + 𝓔₁ = (I + 𝓔₀(I - 𝓔₁))(I + 𝓔₁)` is invertible with
  `‖(I + 𝓔₀ + 𝓔₁)⁻¹‖ ≤ 2(1 + C₁)`, by the series of Neumann.
* *The bound of `μ`* (`mu_bound`): `a⁴|μ|² ≤ Cεa|μ|` gives `|μ| ≤ Cεa⁻³`.
-/
import Mathlib

open scoped InnerProductSpace

noncomputable section

namespace CoreLean
namespace CriticalCurrent

/-- **The current is a transposed average**: `J ⊥ ker Q` gives `J = Q^*μ`. -/
theorem current_transposed {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] (Q : E →L[ℝ] F) (J : E)
    (hJ : ∀ δ : E, Q δ = 0 → ⟪δ, J⟫_ℝ = 0) : ∃ μ : F, J = (ContinuousLinearMap.adjoint Q) μ := by
  have hmem : J ∈ (LinearMap.ker (Q : E →ₗ[ℝ] F))ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro δ hδ
    exact hJ δ hδ
  erw [Q.orthogonal_ker] at hmem
  rw [IsClosed.submodule_topologicalClosure_eq (Submodule.closed_of_finiteDimensional _)] at hmem
  obtain ⟨μ, hμ⟩ := hmem
  exact ⟨μ, hμ.symm⟩

/-- **`eq:test-inverse`**: `I + 𝓔₀ + 𝓔₁` is invertible with the inverse of norm at most `2(1 + C₁)`. -/
theorem test_inverse {R : Type*} [NormedRing R] [CompleteSpace R] [NormOneClass R] (E₀ E₁ : R)
    (hE₁ : E₁ * E₁ = 0) {C₀ C₁ ε : ℝ} (h1 : ‖E₁‖ ≤ C₁) (h0 : ‖E₀‖ ≤ C₀ * ε)
    (hsmall : C₀ * (1 + C₁) * ε ≤ 1 / 2) :
    ∃ V : R, (1 + E₀ + E₁) * V = 1 ∧ V * (1 + E₀ + E₁) = 1 ∧ ‖V‖ ≤ 2 * (1 + C₁) := by
  have hC₁ : 0 ≤ C₁ := (norm_nonneg _).trans h1
  set t : R := -(E₀ * (1 - E₁)) with ht
  have hn1 : ‖(1 : R) - E₁‖ ≤ 1 + C₁ := by
    calc ‖(1 : R) - E₁‖ ≤ ‖(1 : R)‖ + ‖E₁‖ := norm_sub_le _ _
      _ ≤ 1 + C₁ := by rw [norm_one]; linarith
  have htn : ‖t‖ ≤ 1 / 2 := by
    rw [ht, norm_neg]
    calc ‖E₀ * (1 - E₁)‖ ≤ ‖E₀‖ * ‖(1 : R) - E₁‖ := norm_mul_le _ _
      _ ≤ C₀ * ε * (1 + C₁) := mul_le_mul h0 hn1 (norm_nonneg _) ((norm_nonneg _).trans h0)
      _ = C₀ * (1 + C₁) * ε := by ring
      _ ≤ 1 / 2 := hsmall
  have htl : ‖t‖ < 1 := by linarith
  set S : R := ∑' n : ℕ, t ^ n
  have hS1 : (1 - t) * S = 1 := mul_neg_geom_series t htl
  have hS2 : S * (1 - t) = 1 := geom_series_mul_neg t htl
  have hSn : ‖S‖ ≤ 2 := by
    have := tsum_geometric_le_of_norm_lt_one t htl
    rw [norm_one, sub_self, zero_add] at this
    refine this.trans ?_
    rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
  have hfac : 1 + E₀ + E₁ = (1 - t) * (1 + E₁) := by
    rw [ht, sub_neg_eq_add]
    calc 1 + E₀ + E₁ = 1 + E₁ + (E₀ - E₀ * (E₁ * E₁)) := by rw [hE₁, mul_zero, sub_zero]; abel
      _ = (1 + E₀ * (1 - E₁)) * (1 + E₁) := by noncomm_ring
  refine ⟨(1 - E₁) * S, ?_, ?_, ?_⟩
  · rw [hfac]
    calc (1 - t) * (1 + E₁) * ((1 - E₁) * S) = (1 - t) * ((1 + E₁) * (1 - E₁)) * S := by noncomm_ring
      _ = 1 := by
          rw [show (1 + E₁) * (1 - E₁) = 1 - E₁ * E₁ by noncomm_ring, hE₁, sub_zero, mul_one, hS1]
  · rw [hfac]
    calc (1 - E₁) * S * ((1 - t) * (1 + E₁)) = (1 - E₁) * (S * (1 - t)) * (1 + E₁) := by noncomm_ring
      _ = 1 := by
          rw [hS2, mul_one, show (1 - E₁) * (1 + E₁) = 1 - E₁ * E₁ by noncomm_ring, hE₁, sub_zero]
  · calc ‖(1 - E₁) * S‖ ≤ ‖(1 : R) - E₁‖ * ‖S‖ := norm_mul_le _ _
      _ ≤ (1 + C₁) * 2 := mul_le_mul hn1 hSn (norm_nonneg _) (by linarith)
      _ = 2 * (1 + C₁) := by ring

/-- **The bound of `μ`**: `a⁴|μ|² ≤ Cεa|μ|` gives `|μ| ≤ Cεa⁻³`. -/
theorem mu_bound {a m C : ℝ} (ha : 0 < a) (hm : 0 ≤ m) (hC : 0 ≤ C) (h : a ^ 4 * m ^ 2 ≤ C * a * m) : m ≤ C * a⁻¹ ^ 3 := by
  rcases hm.eq_or_lt with rfl | hm0
  · positivity
  have h1 : a ^ 3 * m ≤ C := by
    have h2 : a * m * (a ^ 3 * m) ≤ a * m * C := by nlinarith
    exact le_of_mul_le_mul_left h2 (by positivity)
  rw [inv_pow, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  linarith

end CriticalCurrent
end CoreLean

end
