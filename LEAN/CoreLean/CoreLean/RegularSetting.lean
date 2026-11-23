/-
`lem:regular-setting` of BALABAN_CORE.tex (`a021c13be348`), the arithmetic of its proof, with `σ = 30NL³Mα₀ + α₁`.

* `sigma_bounds`: `Mα₀`, `ε_p = 30√NL³Mα₀`, `10LMα₀`, and `α₁` are at most `σ` (`N ≥ 1`, `L ≥ 3`).
* `wide_class_condition`: `320LMα₀ ≤ 1`, the hypothesis of `lem:wide-class`(ii), from `σ ≤ c_rs ≤ ½ā₀ ≤ 1/(64L)`.
  The proof in the core states `320LMα₀ ≤ σ`, which needs `NL² ≥ 32/3` and fails for `N = 1`, `L = 3`
  (`sigma_counterexample`); the route through `30NL² ≥ 270` used here gives the same conclusion for every `N ≥ 1`.
* `s4_last`: `√Nε_p + 10L²α₁ ≤ (√N + 10L²)σ`.
* `eight_t_le`, `s5_chain`, `s5_first`: `8t ≤ 1` for `t = 10LMα₀`, `9(α₁ + 8tα₁ + t) ≤ 18(t + α₁) ≤ 18σ ≤ c'_S`, and
  `9α₁ + t ≤ c'_S`.
* `psi_size`: `‖Ψ(X, Y)‖ ≤ 9‖X‖ + ‖Y‖` from `Ψ(0, Y) = Y` and the Lipschitz bound `9` of `eq:product-lipschitz`.
* `transported_derivative`: `‖∂Ã‖ ≤ ‖∇_UA''‖ + 8‖A‖‖A''‖` from the formula for `Ad_u∇_UA''` and `eq:adjoint-lipschitz`.
-/
import Mathlib

noncomputable section

namespace CoreLean
namespace RegularSetting

variable {N L M α₀ α₁ : ℝ}

/-- `270L ≤ 30NL³` for `N ≥ 1`, `L ≥ 3`. -/
lemma key (hN : 1 ≤ N) (hL : 3 ≤ L) : 270 * L ≤ 30 * N * L ^ 3 := by
  have hL2 : 9 ≤ L ^ 2 := by nlinarith
  have h : 9 ≤ N * L ^ 2 := by nlinarith
  calc 270 * L = 30 * 9 * L := by ring
    _ ≤ 30 * (N * L ^ 2) * L := by gcongr
    _ = 30 * N * L ^ 3 := by ring

/-- `Mα₀`, `30√NL³Mα₀`, `10LMα₀`, `α₁` are at most `σ = 30NL³Mα₀ + α₁`. -/
theorem sigma_bounds (hN : 1 ≤ N) (hL : 3 ≤ L) (hM : 0 ≤ M) (h0 : 0 ≤ α₀) (h1 : 0 ≤ α₁) :
    M * α₀ ≤ 30 * N * L ^ 3 * M * α₀ + α₁ ∧
      30 * Real.sqrt N * L ^ 3 * M * α₀ ≤ 30 * N * L ^ 3 * M * α₀ + α₁ ∧
      10 * L * M * α₀ ≤ 30 * N * L ^ 3 * M * α₀ + α₁ ∧ α₁ ≤ 30 * N * L ^ 3 * M * α₀ + α₁ := by
  have hMa : 0 ≤ M * α₀ := mul_nonneg hM h0
  have hL3 : 27 ≤ L ^ 3 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) hL 3
    norm_num at this; linarith
  have hsq : Real.sqrt N ≤ N := by
    rw [Real.sqrt_le_left (by linarith)]; nlinarith
  have hNL : 1 ≤ N * L ^ 3 := by nlinarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · have : M * α₀ ≤ 30 * (N * L ^ 3) * (M * α₀) := by nlinarith
    nlinarith
  · have : Real.sqrt N * L ^ 3 * (M * α₀) ≤ N * L ^ 3 * (M * α₀) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hsq (by positivity)) hMa
    nlinarith
  · have hL' : 10 * L ≤ 30 * N * L ^ 3 := by linarith [key hN hL]
    have : 10 * L * (M * α₀) ≤ 30 * N * L ^ 3 * (M * α₀) := mul_le_mul_of_nonneg_right hL' hMa
    nlinarith
  · nlinarith

/-- **The hypothesis of `lem:wide-class`(ii)**: `320LMα₀ ≤ 1` from `σ ≤ 1/(64L)`. -/
theorem wide_class_condition (hN : 1 ≤ N) (hL : 3 ≤ L) (hM : 0 ≤ M) (h0 : 0 ≤ α₀) (h1 : 0 ≤ α₁)
    (hσ : 30 * N * L ^ 3 * M * α₀ + α₁ ≤ 1 / (64 * L)) : 320 * L * M * α₀ ≤ 1 := by
  have hMa : 0 ≤ M * α₀ := mul_nonneg hM h0
  have hL0 : 0 < L := by linarith
  -- `320L ≤ (32/27)·30NL³`
  have hk : 320 * L * (M * α₀) ≤ 32 / 27 * (30 * N * L ^ 3 * (M * α₀)) := by
    have : 320 * L ≤ 32 / 27 * (30 * N * L ^ 3) := by linarith [key hN hL]
    exact (mul_le_mul_of_nonneg_right this hMa).trans_eq (by ring)
  have h64 : 1 / (64 * L) ≤ 1 / 192 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  nlinarith

/-- **The intermediate claim `320LMα₀ ≤ σ` fails** for `N = 1`, `L = 3`, `α₁ = 0`, `Mα₀ > 0`. -/
theorem sigma_counterexample {M α₀ : ℝ} (hM : 0 < M) (h0 : 0 < α₀) :
    30 * 1 * 3 ^ 3 * M * α₀ + 0 < 320 * 3 * M * α₀ := by
  have : 0 < M * α₀ := mul_pos hM h0
  nlinarith

/-- The last inequality of (S4): `√Nε_p + 10L²α₁ ≤ (√N + 10L²)σ`. -/
theorem s4_last {εp σ : ℝ} (hε : εp ≤ σ) (hα : α₁ ≤ σ) :
    Real.sqrt N * εp + 10 * L ^ 2 * α₁ ≤ (Real.sqrt N + 10 * L ^ 2) * σ := by
  have h1 : Real.sqrt N * εp ≤ Real.sqrt N * σ := mul_le_mul_of_nonneg_left hε (Real.sqrt_nonneg _)
  have h2 : 10 * L ^ 2 * α₁ ≤ 10 * L ^ 2 * σ := mul_le_mul_of_nonneg_left hα (by positivity)
  nlinarith

/-- `8t ≤ 1` for `t ≤ σ ≤ 1/(64L)`, `L ≥ 3`. -/
theorem eight_t_le {t σ : ℝ} (hL : 3 ≤ L) (ht : t ≤ σ) (hσ : σ ≤ 1 / (64 * L)) : 8 * t ≤ 1 := by
  have h64 : 1 / (64 * L) ≤ 1 / 192 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  linarith

/-- **(S5)**: `9(α₁ + 8tα₁ + t) ≤ 18(t + α₁) ≤ 18σ ≤ c'_S` for `8t ≤ 1`, `t + α₁ ≤ σ ≤ c'_S/18`. -/
theorem s5_chain {t σ cS : ℝ} (ht : 0 ≤ t) (h1 : 0 ≤ α₁) (h8 : 8 * t ≤ 1) (hs : t + α₁ ≤ σ)
    (hc : σ ≤ cS / 18) : 9 * (α₁ + 8 * t * α₁ + t) ≤ 18 * (t + α₁) ∧ 18 * (t + α₁) ≤ cS := by
  refine ⟨?_, ?_⟩
  · have : 8 * t * α₁ ≤ α₁ := by nlinarith
    linarith
  · linarith

/-- `9α₁ + t ≤ c'_S`. -/
theorem s5_first {t σ cS : ℝ} (ht : 0 ≤ t) (h1 : 0 ≤ α₁) (hs : t + α₁ ≤ σ) (hc : σ ≤ cS / 18) :
    9 * α₁ + t ≤ cS := by linarith

/-- `t + α₁ ≤ σ` for `t = 10LMα₀`. -/
theorem t_add_le (hN : 1 ≤ N) (hL : 3 ≤ L) (hM : 0 ≤ M) (h0 : 0 ≤ α₀) :
    10 * L * M * α₀ + α₁ ≤ 30 * N * L ^ 3 * M * α₀ + α₁ := by
  have hMa : 0 ≤ M * α₀ := mul_nonneg hM h0
  have hL' : 10 * L ≤ 30 * N * L ^ 3 := by linarith [key hN hL]
  have : 10 * L * (M * α₀) ≤ 30 * N * L ^ 3 * (M * α₀) := mul_le_mul_of_nonneg_right hL' hMa
  nlinarith

/-- `‖Ψ(X, Y)‖ ≤ 9‖X‖ + ‖Y‖` from `Ψ(0, Y) = Y` and `‖Ψ(X', Y') - Ψ(X, Y)‖ ≤ 9(‖X' - X‖ + ‖Y' - Y‖)`. -/
theorem psi_size {E : Type*} [NormedAddCommGroup E] (Ψ : E → E → E) (X Y : E) (h0 : Ψ 0 Y = Y)
    (hlip : ‖Ψ X Y - Ψ 0 Y‖ ≤ 9 * (‖X - 0‖ + ‖Y - Y‖)) : ‖Ψ X Y‖ ≤ 9 * ‖X‖ + ‖Y‖ := by
  rw [sub_zero, sub_self, norm_zero, add_zero, h0] at hlip
  calc ‖Ψ X Y‖ = ‖(Ψ X Y - Y) + Y‖ := by rw [sub_add_cancel]
    _ ≤ ‖Ψ X Y - Y‖ + ‖Y‖ := norm_add_le _ _
    _ ≤ 9 * ‖X‖ + ‖Y‖ := by linarith

/-- `‖∂Ã‖ ≤ ‖∇_UA''‖ + 8‖A‖‖A''‖`: if `∇ = ∂Ã + a₀⁻¹(Ad - 1)Z` with `‖(Ad - 1)Z‖ ≤ 8a₀‖A‖‖Z‖` and `‖Z‖ = ‖A''‖`. -/
theorem transported_derivative {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (dA nab W : E)
    {a₀ nA nZ : ℝ} (ha : 0 < a₀) (heq : nab = dA + a₀⁻¹ • W) (hW : ‖W‖ ≤ 8 * a₀ * nA * nZ) :
    ‖dA‖ ≤ ‖nab‖ + 8 * nA * nZ := by
  have e : dA = nab - a₀⁻¹ • W := by rw [heq]; abel
  have hW' : ‖a₀⁻¹ • W‖ ≤ 8 * nA * nZ := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 ha.le)]
    calc a₀⁻¹ * ‖W‖ ≤ a₀⁻¹ * (8 * a₀ * nA * nZ) := mul_le_mul_of_nonneg_left hW (inv_nonneg.2 ha.le)
      _ = 8 * nA * nZ := by field_simp
  rw [e]
  exact (norm_sub_le _ _).trans (by linarith)

end RegularSetting
end CoreLean

end
