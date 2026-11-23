/-
`lem:real-preimage` of BALABAN_CORE.tex (`a021c13be348`), its argument in abstract form. The conjugation `σ` of
`𝔤^c` fixing `𝔤`, applied at every bond, acts on the forms `X` and on the functions on the bonds of the layers `Y`;
it is an involution and preserves the norms. The operator `H` commutes with it, and so does the remainder `𝖢` on the
ball of its definition (in the core: the map `A ↦ σ𝖢(σA)` is holomorphic and agrees with `𝖢` on the real forms; this
identity-theorem step is the hypothesis `hC` here, stated for all arguments; the core needs it on the ball of
`𝖢`, which contains the arguments `A' - H𝖣(A')` used). Then:

* the conjugate of the solution `𝖣(A')` of `eq:linearising-equation` solves it at `σA'`, so that
  `σ𝖣(A') = 𝖣(σA')` by the uniqueness (`D_conj`), and `T(σA') = σT(A')` (`T_conj`);
* if `T(A') = A` with `A` real, then `σA'` is again a preimage of `A` in the ball, and `A'` is real by the injectivity
  of `T` (`real_preimage`);
* `RD^*A' = RD^*A + RD^*H𝖣(A') = 0` if `RD^*A = 0` and `RD^*H = 0` (`gauge_condition`).
-/
import Mathlib

noncomputable section

namespace CoreLean
namespace RealPreimage

variable {X Y : Type*} [AddCommGroup X] [AddCommGroup Y] [Norm X] [Norm Y]

variable (σX : X →+ X) (σY : Y →+ Y) (H : Y →+ X) (C : X → Y) (D : X → Y) {a : ℝ}

/-- The conjugate of `𝖣(A')` is `𝖣(σA')`. -/
theorem D_conj (hσX : ∀ x, ‖σX x‖ = ‖x‖) (hσY : ∀ y, ‖σY y‖ = ‖y‖) (hH : ∀ y, H (σY y) = σX (H y))
    (hC : ∀ x, σY (C x) = C (σX x))
    (hD : ∀ A', ‖A'‖ ≤ a → ‖D A'‖ ≤ a ∧ D A' = C (A' - H (D A')))
    (huniq : ∀ A', ‖A'‖ ≤ a → ∀ z : Y, ‖z‖ ≤ a → z = C (A' - H z) → z = D A') {A' : X} (hA' : ‖A'‖ ≤ a) :
    σY (D A') = D (σX A') := by
  obtain ⟨h1, h2⟩ := hD A' hA'
  refine huniq (σX A') (by rw [hσX]; exact hA') (σY (D A')) (by rw [hσY]; exact h1) ?_
  conv_lhs => rw [h2]
  rw [hC, map_sub, hH]

/-- `T(σA') = σT(A')`. -/
theorem T_conj (hσX : ∀ x, ‖σX x‖ = ‖x‖) (hσY : ∀ y, ‖σY y‖ = ‖y‖) (hH : ∀ y, H (σY y) = σX (H y))
    (hC : ∀ x, σY (C x) = C (σX x))
    (hD : ∀ A', ‖A'‖ ≤ a → ‖D A'‖ ≤ a ∧ D A' = C (A' - H (D A')))
    (huniq : ∀ A', ‖A'‖ ≤ a → ∀ z : Y, ‖z‖ ≤ a → z = C (A' - H z) → z = D A') {A' : X} (hA' : ‖A'‖ ≤ a) :
    σX A' - H (D (σX A')) = σX (A' - H (D A')) := by
  rw [← D_conj σX σY H C D hσX hσY hH hC hD huniq hA', hH, map_sub]

/-- **`lem:real-preimage`**: a preimage of a real form in the ball is real. -/
theorem real_preimage (hσX : ∀ x, ‖σX x‖ = ‖x‖) (hσY : ∀ y, ‖σY y‖ = ‖y‖) (hH : ∀ y, H (σY y) = σX (H y))
    (hC : ∀ x, σY (C x) = C (σX x))
    (hD : ∀ A', ‖A'‖ ≤ a → ‖D A'‖ ≤ a ∧ D A' = C (A' - H (D A')))
    (huniq : ∀ A', ‖A'‖ ≤ a → ∀ z : Y, ‖z‖ ≤ a → z = C (A' - H z) → z = D A')
    (hinj : ∀ A₁ A₂ : X, ‖A₁‖ ≤ a → ‖A₂‖ ≤ a → A₁ - H (D A₁) = A₂ - H (D A₂) → A₁ = A₂)
    {A A' : X} (hA : σX A = A) (hA' : ‖A'‖ ≤ a) (hT : A' - H (D A') = A) : σX A' = A' := by
  refine hinj (σX A') A' (by rw [hσX]; exact hA') hA' ?_
  rw [T_conj σX σY H C D hσX hσY hH hC hD huniq hA', hT, hA]

/-- **The gauge condition**: `RD^*A' = 0`. -/
theorem gauge_condition {Z : Type*} [AddCommGroup Z] (RD : X →+ Z) {A A' : X} (z : Y)
    (hT : A' - H z = A) (hA : RD A = 0) (hRH : ∀ y, RD (H y) = 0) : RD A' = 0 := by
  have : A' = A + H z := by rw [← hT]; abel
  rw [this, map_add, hA, hRH, add_zero]

end RealPreimage
end CoreLean

end
