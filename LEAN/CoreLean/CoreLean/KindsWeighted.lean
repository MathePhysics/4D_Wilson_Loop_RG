/-
`lem:kinds-weighted` of BALABAN_CORE.tex (`a021c13be348`), the first statement, in the setting of `Composition.lean`.
A linear map `𝒯` with the block bound `(b, p, δ)` in a set `X`: `[𝒯f]_y ≤ b a_{j(y)}^p Σ_{y' ∈ X} e^{-δd(y, y')}[f]_{y'}`
for `y ∈ X` and `[𝒯f]_y = 0` outside `X`. For a weight `ϖ` of a rate at most `δ/2`
(`ϖ(y) ≤ e^{(δ/2)d(y, y')}ϖ(y')`), `|τ| ≤ S`, `4S log L ≤ δRM`, and `eq:summation` at the rate `δ/4` with the constant
`c₁`, the bound `ϖ(y')a_{j(y')}^{-τ}[f]_{y'} ≤ N` at every point gives `ϖ(y)a_{j(y)}^{-(τ+p)}[𝒯f]_y ≤ L^Sc₁bN` at every
point (`kinds_weighted`), which is `eq:kinds-weighted`, `‖𝒯f‖_{(τ+p),ϖ} ≤ L^Sc₁(¼, δ)b‖f‖_{(τ),ϖ}`. The proof is the
core's. The consequences (T1), (T3) are not formalised.
-/
import CoreLean.Composition

open Finset

noncomputable section

namespace CoreLean
namespace Composition

variable {β : Type*} [Fintype β] [DecidableEq β] (B : Setting β)

/-- **`eq:kinds-weighted`** in pointwise form. -/
theorem kinds_weighted {V V' : Type*} (nrm : V → β → ℝ) (nrm' : V' → β → ℝ) (hn : ∀ f y, 0 ≤ nrm f y)
    (X : Finset β) (T : V → V') {b : ℝ} {p τ : ℤ} {δ S c₁ : ℝ} (hb : 0 ≤ b) (hδ : 0 < δ) (hS : 0 ≤ S)
    (hτ : |(τ : ℝ)| ≤ S) (hSL : 4 * S * Real.log B.L ≤ δ * B.RM)
    (hsum : ∀ y, ∑ y', Real.exp (-(δ / 4 * B.d y y')) ≤ c₁)
    (hT : ∀ f, ∀ y, nrm' (T f) y ≤ b * B.a (B.j y) ^ p *
      ∑ y' ∈ X, Real.exp (-(δ * B.d y y')) * nrm f y')
    (ϖ : β → ℝ) (hϖ : ∀ y, 0 < ϖ y) (hrate : ∀ y y', ϖ y ≤ Real.exp (δ / 2 * B.d y y') * ϖ y')
    {f : V} {N : ℝ} (hf : ∀ y', ϖ y' * B.a (B.j y') ^ (-τ) * nrm f y' ≤ N) (y : β) :
    ϖ y * B.a (B.j y) ^ (-(τ + p)) * nrm' (T f) y ≤ B.L ^ S * c₁ * b * N := by
  have hL0 : 0 < B.L := lt_of_lt_of_le zero_lt_one B.one_le_L
  have haj := B.a_pos (B.j y)
  have hN : 0 ≤ N := le_trans (mul_nonneg (mul_nonneg (hϖ y).le (zpow_pos haj _).le) (hn f y)) (hf y)
  -- the term of `y'`
  have hterm : ∀ y', ϖ y * B.a (B.j y) ^ (-τ) * (Real.exp (-(δ * B.d y y')) * nrm f y') ≤
      B.L ^ S * N * Real.exp (-(δ / 4 * B.d y y')) := by
    intro y'
    have hay' := B.a_pos (B.j y')
    have hz := B.zpow_a_le (α := 1 / 2) (δ := δ) (S := S) hS (by linarith) y y' (s := τ) hτ
    rw [show 1 / 2 * δ / 2 = δ / 4 by ring] at hz
    -- `[f]_{y'} ≤ N ϖ(y')⁻¹ a_{j(y')}^τ`
    have hf' : nrm f y' ≤ N * (ϖ y')⁻¹ * B.a (B.j y') ^ τ := by
      have h1 := hf y'
      have hp : 0 < ϖ y' * B.a (B.j y') ^ (-τ) := mul_pos (hϖ y') (zpow_pos hay' _)
      rw [show N * (ϖ y')⁻¹ * B.a (B.j y') ^ τ = N / (ϖ y' * B.a (B.j y') ^ (-τ)) by
        rw [zpow_neg]; field_simp]
      rw [le_div_iff₀ hp]; linarith
    have hd := B.d_nonneg y y'
    have hE : Real.exp (-(δ * B.d y y')) * Real.exp (δ / 2 * B.d y y') * Real.exp (δ / 4 * B.d y y') =
        Real.exp (-(δ / 4 * B.d y y')) := by
      rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    calc ϖ y * B.a (B.j y) ^ (-τ) * (Real.exp (-(δ * B.d y y')) * nrm f y')
        ≤ (Real.exp (δ / 2 * B.d y y') * ϖ y') * B.a (B.j y) ^ (-τ) *
            (Real.exp (-(δ * B.d y y')) * (N * (ϖ y')⁻¹ * B.a (B.j y') ^ τ)) :=
          mul_le_mul (mul_le_mul_of_nonneg_right (hrate y y') (zpow_pos haj _).le)
            (mul_le_mul_of_nonneg_left hf' (Real.exp_pos _).le)
            (mul_nonneg (Real.exp_pos _).le (hn f y'))
            (mul_nonneg (mul_nonneg (Real.exp_pos _).le (hϖ y').le) (zpow_pos haj _).le)
      _ = N * Real.exp (-(δ * B.d y y')) * Real.exp (δ / 2 * B.d y y') *
            (B.a (B.j y') ^ τ * B.a (B.j y) ^ (-τ)) := by
          field_simp [(hϖ y').ne']
      _ ≤ N * Real.exp (-(δ * B.d y y')) * Real.exp (δ / 2 * B.d y y') *
            (B.L ^ S * Real.exp (δ / 4 * B.d y y')) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          calc B.a (B.j y') ^ τ * B.a (B.j y) ^ (-τ)
              ≤ B.L ^ S * Real.exp (δ / 4 * B.d y y') * B.a (B.j y) ^ τ * B.a (B.j y) ^ (-τ) :=
                mul_le_mul_of_nonneg_right hz (zpow_pos haj _).le
            _ = B.L ^ S * Real.exp (δ / 4 * B.d y y') := by
                rw [mul_assoc, ← zpow_add₀ haj.ne', add_neg_cancel, zpow_zero, mul_one]
      _ = B.L ^ S * N * Real.exp (-(δ / 4 * B.d y y')) := by rw [← hE]; ring
  calc ϖ y * B.a (B.j y) ^ (-(τ + p)) * nrm' (T f) y
      ≤ ϖ y * B.a (B.j y) ^ (-(τ + p)) * (b * B.a (B.j y) ^ p *
          ∑ y' ∈ X, Real.exp (-(δ * B.d y y')) * nrm f y') :=
        mul_le_mul_of_nonneg_left (hT f y) (mul_nonneg (hϖ y).le (zpow_pos haj _).le)
    _ = b * ∑ y' ∈ X, ϖ y * B.a (B.j y) ^ (-τ) * (Real.exp (-(δ * B.d y y')) * nrm f y') := by
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun y' _ => ?_
        rw [show -(τ + p) = -τ + -p by ring, zpow_add₀ haj.ne', zpow_neg (B.a (B.j y)) p]
        field_simp
    _ ≤ b * ∑ y' ∈ X, B.L ^ S * N * Real.exp (-(δ / 4 * B.d y y')) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun y' _ => hterm y') hb
    _ = b * (B.L ^ S * N) * ∑ y' ∈ X, Real.exp (-(δ / 4 * B.d y y')) := by
        rw [← Finset.mul_sum]; ring
    _ ≤ b * (B.L ^ S * N) * c₁ := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ X)
          fun _ _ _ => (Real.exp_pos _).le).trans (hsum y)
    _ = B.L ^ S * c₁ * b * N := by ring

end Composition
end CoreLean

end
