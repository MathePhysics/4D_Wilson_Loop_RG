/-
`lem:solution-holder` of BALABAN_CORE.tex (`a021c13be348`), the conclusion of its proof from
`prop:interior-schauder` at the scale `j - 2`, in the model of `InteriorSchauder.lean` (`a = Kη`, `a' = a/L² = K'η`).

* *The bounds at the finer scale*: `‖v‖ ≤ Va`, `‖∇v‖ ≤ V`, `‖ρ̃‖ ≤ V/a` give the same bounds with `V' = L²V` and `a'`
  (`finer_inputs`).
* *Near pairs*, `|x - x'|₁ ≤ a'`: `prop:interior-schauder` on the cube `Q'_x` centred at `x` gives
  `C_I(β)(L²V + ΣΛ₀)(r/a')^β ≤ L⁴C_I(β)(V + ΣΛ₀)(r/a)^β` (`near_pairs`).
* *Far pairs*, `a' < r ≤ a`: `3V ≤ 3L²V(r/a)^β` (`far_pairs`), and at the scale `1`, where `(r/a)^β ≥ 1/L`,
  `3S ≤ 3LS(r/a)^β` (`scale_one`).
-/
import CoreLean.SchauderStep

open Matrix NormedSpace
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace CoreLean
namespace InteriorSchauder

variable {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ

/-- The bounds at the finer scale `a' = a/L²` with `V' = L²V`. -/
theorem finer_inputs {L a' V nv nDv nr : ℝ} (hL : 1 ≤ L) (ha' : 0 < a') (hV : 0 ≤ V)
    (hv : nv ≤ V * (L ^ 2 * a')) (hDv : nDv ≤ V) (hr : nr ≤ V / (L ^ 2 * a')) :
    nv ≤ L ^ 2 * V * a' ∧ nDv ≤ L ^ 2 * V ∧ nr ≤ L ^ 2 * V / a' := by
  have hL2 : 1 ≤ L ^ 2 := one_le_pow₀ hL
  refine ⟨by linarith [hv], hDv.trans (le_mul_of_one_le_left hV hL2), hr.trans ?_⟩
  rw [div_le_div_iff₀ (by positivity) ha']
  have hL4 : 1 ≤ L ^ 2 * L ^ 2 := one_le_mul_of_one_le_of_one_le hL2 hL2
  have h0 : 0 ≤ V * a' := mul_nonneg hV ha'.le
  calc V * a' ≤ (L ^ 2 * L ^ 2) * (V * a') := le_mul_of_one_le_left h0 hL4
    _ = L ^ 2 * V * (L ^ 2 * a') := by ring

/-- The conversion of the modulus from the scale `a' = a/L²` to the scale `a`. -/
lemma rescale {L r K' β : ℝ} (hL : 1 ≤ L) (hr : 0 ≤ r) (hK' : 0 < K') (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    (r / K') ^ β ≤ L ^ 2 * (r / (L ^ 2 * K')) ^ β := by
  have hL2 : 1 ≤ L ^ 2 := one_le_pow₀ hL
  have e : r / K' = L ^ 2 * (r / (L ^ 2 * K')) := by field_simp
  rw [e, Real.mul_rpow (by positivity) (by positivity)]
  gcongr
  calc (L ^ 2) ^ β ≤ (L ^ 2) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL2 hβ1
    _ = L ^ 2 := Real.rpow_one _

lemma CI_nonneg {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) : 0 ≤ CI β := by
  have hc := c0_pos
  have h1 : 0 < 1 - β := by linarith
  have hm : 0 < m1 := by unfold m1; positivity
  unfold CI CS CS'
  positivity

/-- **Near pairs**: `prop:interior-schauder` at the scale `a' = K'η` on the cube centred at `x`. -/
theorem near_pairs {η : ℝ} {K' : ℕ} {L : ℝ} (hL : 1 ≤ L) {x : Fin 4 → ℤ} {A : Fin 4 → (Fin 4 → ℤ) → Mat}
    {v : (Fin 4 → ℤ) → Mat} {lam : Fin 4 → (Fin 4 → ℤ) → Mat} {rho : (Fin 4 → ℤ) → Mat} {V : ℝ}
    {Λ : Fin 4 → ℝ} {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (H : Hyp η K' x A v lam rho (L ^ 2 * V) Λ β)
    {x' : Fin 4 → ℤ} (hx' : ∀ μ, |x' μ - x μ| ≤ K') {l : List (Fin 4)} (hl : IsShortest x x' l)
    (hxx : l1 (x' - x) ≤ K') (ν : Fin 4) :
    ‖Ad (pathT η A (sgnv x x') x l) (Dfw η A ν v x') - Dfw η A ν v x‖ ≤
      L ^ 4 * CI β * (V + ∑ κ, Λ κ) * (l1 (x' - x) / (L ^ 2 * K')) ^ β := by
  have hK := H.hK
  have hKr := H.K_pos
  have hx : InQ x (4 * K' - 2) x := fun μ => by simp; omega
  have hx'Q : InQ x (4 * K' - 2) x' := fun μ => by have := hx' μ; omega
  have hI := interior_schauder hβ0 hβ1 H hx hx'Q hxx hl ν
  rw [H.holder_rewrite] at hI
  have hV : 0 ≤ L ^ 2 * V := H.V_nonneg
  have hL2 : 1 ≤ L ^ 2 := one_le_pow₀ hL
  have hV0 : 0 ≤ V := by
    by_contra h; replace h := not_le.1 h; nlinarith
  have hΛ : 0 ≤ ∑ κ, Λ κ := Finset.sum_nonneg fun κ _ => H.Λ_nonneg κ
  have hCI : 0 ≤ CI β := CI_nonneg hβ0 hβ1
  have hr := rescale hL (by unfold l1; positivity : (0 : ℝ) ≤ l1 (x' - x)) hKr hβ0.le hβ1.le
  refine hI.trans ?_
  have h1 : L ^ 2 * V + ∑ κ, Λ κ ≤ L ^ 2 * (V + ∑ κ, Λ κ) := by nlinarith
  calc CI β * (L ^ 2 * V + ∑ κ, Λ κ) * (l1 (x' - x) / K') ^ β
      ≤ CI β * (L ^ 2 * (V + ∑ κ, Λ κ)) * (L ^ 2 * (l1 (x' - x) / (L ^ 2 * K')) ^ β) := by
        have ht0 : 0 ≤ (l1 (x' - x) / K') ^ β :=
          Real.rpow_nonneg (div_nonneg (by unfold l1; positivity) hKr.le) β
        gcongr
    _ = L ^ 4 * CI β * (V + ∑ κ, Λ κ) * (l1 (x' - x) / (L ^ 2 * K')) ^ β := by ring

/-- **Far pairs**: `a' < r ≤ a` gives `(r/a)^β ≥ L^{-2}`. -/
theorem far_pairs {L a r V β : ℝ} (hL : 1 ≤ L) (ha : 0 < a) (hr : a / L ^ 2 < r) (hra : r ≤ a) (hV : 0 ≤ V)
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) : 3 * V ≤ 3 * L ^ 2 * V * (r / a) ^ β := by
  have hL2 : 1 ≤ L ^ 2 := one_le_pow₀ hL
  have hL20 : 0 < L ^ 2 := by positivity
  have hr0 : 0 < r / a := div_pos (lt_trans (div_pos ha hL20) hr) ha
  have hra1 : r / a ≤ 1 := (div_le_one ha).2 hra
  have h1 : 1 / L ^ 2 ≤ r / a := by
    rw [div_le_div_iff₀ hL20 ha]; rw [div_lt_iff₀ hL20] at hr; linarith
  have h2 : r / a ≤ (r / a) ^ β := by
    calc r / a = (r / a) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (r / a) ^ β := Real.rpow_le_rpow_of_exponent_ge hr0 hra1 hβ1
  have h3 : 1 ≤ L ^ 2 * (r / a) ^ β := by
    calc (1 : ℝ) = L ^ 2 * (1 / L ^ 2) := by field_simp
      _ ≤ L ^ 2 * (r / a) ^ β := mul_le_mul_of_nonneg_left (h1.trans h2) hL20.le
  nlinarith

/-- **The scale `1`**: `(r/a)^β ≥ 1/L` gives `3S ≤ 3LS(r/a)^β`. -/
theorem scale_one {L S t : ℝ} (hL : 0 < L) (hS : 0 ≤ S) (ht : 1 / L ≤ t) : 3 * S ≤ 3 * L * S * t := by
  have : 1 ≤ L * t := by rw [div_le_iff₀ hL] at ht; linarith
  nlinarith

end InteriorSchauder
end CoreLean

end
