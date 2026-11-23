/-
`prop:unit-linearising` of BALABAN_CORE.tex (`a021c13be348`), (ii) from the bonds and (iii), in abstract form.

* (ii), *the decoupling*: if for every bond `c` the equation at `c` has exactly one solution in the ball of the radius
  `a` (`lem:unit-average-bond`(iii) at `c`), then the family of these solutions is the only family which solves the
  equation at every bond and is bounded by `a` (`decoupled_unique`).
* (iii): with `LQ̃h = I`, `D̃(B) = C̃(B - hD̃(B))` and `B' = B - hD̃(B)`:
  `LQ̃B' + C̃(B') = LQ̃B` (`linearising_identity`); the map `B ↦ B'` is injective on the ball (`linearising_injective`);
  and if `B'` is such that `B = B' + hC̃(B')` and `C̃(B')` lie in the balls of the uniqueness, then `B'` is the image of
  `B` (`linearising_surjective`).
-/
import Mathlib

noncomputable section

namespace CoreLean
namespace UnitLinearising

/-- **(ii)**: the decoupled equations have exactly one bounded family of solutions. -/
theorem decoupled_unique {ι : Type*} {Zc : ι → Type*} [∀ c, Norm (Zc c)] {a : ℝ}
    (Eq : ∀ c, Zc c → Prop) (huniq : ∀ c, ∃! z : Zc c, ‖z‖ ≤ a ∧ Eq c z) :
    ∃! D : (∀ c, Zc c), ∀ c, ‖D c‖ ≤ a ∧ Eq c (D c) := by
  choose D hD hDu using huniq
  refine ⟨D, hD, fun D' hD' => funext fun c => hDu c (D' c) (hD' c)⟩

variable {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]

/-- **(iii)**, the identity `LQ̃B' + C̃(B') = LQ̃B`. -/
theorem linearising_identity (LQ : X →+ Y) (h : Y →+ X) (hQh : ∀ y, LQ (h y) = y) (C : X → Y) (D : X → Y)
    (hD : ∀ B, D B = C (B - h (D B))) (B : X) : LQ (B - h (D B)) + C (B - h (D B)) = LQ B := by
  rw [map_sub, hQh, ← hD]; abel

/-- **(iii)**, the injectivity on the ball. -/
theorem linearising_injective (h : Y →+ X) (C : X → Y) (D : X → Y)
    (hD : ∀ B, D B = C (B - h (D B))) {B₁ B₂ : X} (he : B₁ - h (D B₁) = B₂ - h (D B₂)) : B₁ = B₂ := by
  have hD12 : D B₁ = D B₂ := by rw [hD B₁, hD B₂, he]
  have : B₁ = (B₁ - h (D B₁)) + h (D B₁) := by abel
  rw [this, he, hD12]; abel

/-- **(iii)**, the image contains the small `B'`: if `B = B' + hC̃(B')` lies in the ball of the uniqueness and `C̃(B')`
in that of the fixed point, then `D̃(B) = C̃(B')` and `B - hD̃(B) = B'`. -/
theorem linearising_surjective [Norm Y] (h : Y →+ X) (C : X → Y) {inBall : X → Prop} {a : ℝ}
    (D : X → Y) (huniq : ∀ B, inBall B → ∀ z : Y, ‖z‖ ≤ a → z = C (B - h z) → z = D B) (B' : X)
    (hB : inBall (B' + h (C B'))) (hCB : ‖C B'‖ ≤ a) :
    D (B' + h (C B')) = C B' ∧ (B' + h (C B')) - h (D (B' + h (C B'))) = B' := by
  have hsol : C B' = C ((B' + h (C B')) - h (C B')) := by rw [add_sub_cancel_right]
  have hDeq : D (B' + h (C B')) = C B' := (huniq _ hB (C B') hCB hsol).symm
  refine ⟨hDeq, ?_⟩
  rw [hDeq, add_sub_cancel_right]

/-- **(iii)**, the bounds: for `‖B'‖ ≤ a₇/2`, `‖C̃(B')‖ ≤ 4(a₇/2)²/r₀² = a₇²/r₀² ≤ a₇` and
`‖B' + hC̃(B')‖ ≤ a₇/2 + 2L³a₇²/r₀² ≤ a₇`, with `a₇ = r₀²/(192L⁶)`. -/
theorem surjective_bounds {L r₀ b c : ℝ} (hL : 1 ≤ L) (hr₀ : 0 < r₀) (hr₁ : r₀ ≤ 1)
    (hb : b ≤ r₀ ^ 2 / (192 * L ^ 6) / 2 + 2 * L ^ 3 * c)
    (hc : c ≤ 4 * (r₀ ^ 2 / (192 * L ^ 6) / 2) ^ 2 / r₀ ^ 2) :
    c ≤ r₀ ^ 2 / (192 * L ^ 6) ∧ b ≤ r₀ ^ 2 / (192 * L ^ 6) := by
  have hL0 : 0 < L := by linarith
  have hL3 : 1 ≤ L ^ 3 := one_le_pow₀ hL
  set a := r₀ ^ 2 / (192 * L ^ 6) with ha
  have ha0 : 0 < a := by positivity
  have hc' : c ≤ a * (a / r₀ ^ 2) := by
    calc c ≤ 4 * (a / 2) ^ 2 / r₀ ^ 2 := hc
      _ = a * (a / r₀ ^ 2) := by ring
  have har : a / r₀ ^ 2 = 1 / (192 * L ^ 6) := by rw [ha]; field_simp
  have hsmall : a / r₀ ^ 2 ≤ 1 / 192 := by
    rw [har]; apply one_div_le_one_div_of_le (by norm_num)
    have : 1 ≤ L ^ 6 := one_le_pow₀ hL
    linarith
  have hc1 : c ≤ a / 192 := hc'.trans (by nlinarith)
  constructor
  · linarith
  · have h2 : 2 * L ^ 3 * c ≤ 2 * L ^ 3 * (a * (1 / (192 * L ^ 6))) := by
      rw [← har]; exact mul_le_mul_of_nonneg_left hc' (by positivity)
    have h3 : 2 * L ^ 3 * (a * (1 / (192 * L ^ 6))) = a / (96 * L ^ 3) := by field_simp; ring
    have h4 : a / (96 * L ^ 3) ≤ a / 2 := by
      apply div_le_div_of_nonneg_left ha0.le (by norm_num); nlinarith
    linarith

end UnitLinearising
end CoreLean

end
