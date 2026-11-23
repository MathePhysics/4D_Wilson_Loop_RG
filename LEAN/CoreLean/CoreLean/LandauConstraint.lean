/-
`lem:landau-constraint` of BALABAN_CORE.tex (`a021c13be348`), (iii) and the constant of (ii), in abstract form.

* (iii): the data on the layers `Γ_j` are functions `V j` on the bonds of the layer with values in a group, the
  factors `m_j` of `eq:block-mean-factor` depend on the data of the layers below `j` only, and
  `𝖻(V, V₀)(c) = log(m_j(c₋)^{-1}V(c)m_j(c₊)V₀(c)^{-1})` with a logarithm which is inverted by the exponential on the
  arguments considered. If `𝖻(V, V₀) = 𝖻(V', V₀)`, then `V = V'` (`data_injective`), by induction over `j`.
* (ii), the constant: `(π/2)(96πL + 1) ≤ 480L` for `L ≥ 3` (`constant_rep`).
-/
import Mathlib

noncomputable section

namespace CoreLean
namespace LandauConstraint

variable {G A X : Type*} [Group G] {Bd : ℕ → Type*}

/-- The field `𝖻(V, V₀)` of the data on a bond `c` of the layer `j` with the ends `src c`, `tgt c`. -/
def bField (log : G → A) (m : ℕ → (∀ i, Bd i → G) → X → G) (src tgt : ∀ j, Bd j → X) (V V₀ : ∀ i, Bd i → G)
    (j : ℕ) (c : Bd j) : A :=
  log ((m j V (src j c))⁻¹ * V j c * m j V (tgt j c) * (V₀ j c)⁻¹)

/-- **(iii)**: the data are determined by the field. -/
theorem data_injective (log : G → A) (exp : A → G) (m : ℕ → (∀ i, Bd i → G) → X → G)
    (hm : ∀ j (V V' : ∀ i, Bd i → G), (∀ i < j, V i = V' i) → m j V = m j V')
    (src tgt : ∀ j, Bd j → X) (V V' V₀ : ∀ i, Bd i → G)
    (hexp : ∀ j (c : Bd j), exp (bField log m src tgt V V₀ j c) =
      (m j V (src j c))⁻¹ * V j c * m j V (tgt j c) * (V₀ j c)⁻¹)
    (hexp' : ∀ j (c : Bd j), exp (bField log m src tgt V' V₀ j c) =
      (m j V' (src j c))⁻¹ * V' j c * m j V' (tgt j c) * (V₀ j c)⁻¹)
    (hb : ∀ j (c : Bd j), bField log m src tgt V V₀ j c = bField log m src tgt V' V₀ j c) :
    V = V' := by
  -- strong induction over the layers
  have key : ∀ j, ∀ i < j, V i = V' i := by
    intro j
    induction j with
    | zero => intro i hi; omega
    | succ j ih =>
      intro i hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | rfl
      · exact ih i h
      · have hmj : m i V = m i V' := hm i V V' ih
        funext c
        have h1 := hexp i c
        rw [hb i c, hexp' i c, hmj] at h1
        have h2 : V' i c = V i c := by
          have := congrArg (fun g => m i V' (src i c) * g * (V₀ i c) * (m i V' (tgt i c))⁻¹) h1
          simpa [mul_assoc] using this
        exact h2.symm
  funext i
  exact key (i + 1) i (Nat.lt_succ_self i)

/-- **(ii)**, the constant `K_rep = 480L`. -/
theorem constant_rep {L : ℝ} (hL : 3 ≤ L) : Real.pi / 2 * (96 * Real.pi * L + 1) ≤ 480 * L := by
  have hπ := Real.pi_lt_d2
  have hπ0 := Real.pi_pos
  have h1 : Real.pi * Real.pi < 3.15 * 3.15 := mul_lt_mul'' hπ hπ hπ0.le hπ0.le
  have hL0 : 0 ≤ L := by linarith
  have h2 : Real.pi * Real.pi * L ≤ 3.15 * 3.15 * L := mul_le_mul_of_nonneg_right h1.le hL0
  have e : Real.pi / 2 * (96 * Real.pi * L + 1) = 48 * (Real.pi * Real.pi * L) + Real.pi / 2 := by ring
  rw [e]
  norm_num at h2 ⊢
  linarith

end LandauConstraint
end CoreLean

end
