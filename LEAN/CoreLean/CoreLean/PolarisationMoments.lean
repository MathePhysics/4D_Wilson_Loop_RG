/-
`prop:polarisation`(iv) of BALABAN_CORE.tex (`a021c13be348`), the algebra of the last step of the proof, in exact form
(the core carries an error ε through the same linear relations). A real tensor `m_{μν;κλ}` on the indices 0, ..., 3 which is
symmetric in `κ, λ`, invariant under the permutations `π` of the coordinates and odd under the reflection of one
coordinate when that coordinate occurs an odd number of times (the signed permutations, `m_{μν;κλ} =
ε_με_νε_κε_λm_{πμπν;πκπλ}`), and satisfies the cyclic relation `eq:polarisation-cyclic`,
`m_{μκ;λσ} + m_{μλ;κσ} + m_{μσ;κλ} = 0`, is `β(δ_{μκ}δ_{νλ} + δ_{μλ}δ_{νκ} - 2δ_{μν}δ_{κλ})` with `β = m_{01;01}`
(`second_moments`, the first line of `eq:polarisation-moments`). The proof is the core's: the moments with an index which
occurs once vanish by a reflection, the others depend only on the pattern of the indices, and the cyclic relation gives
`A + 2B = 0` and `3D = 0`.
-/
import Mathlib

noncomputable section

namespace CoreLean
namespace Polarisation

/-- The sign of the reflection of the coordinate `σ` at the index `i`. -/
def sgn (σ i : Fin 4) : ℝ := if i = σ then -1 else 1

variable (m : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ)

lemma perm_to (a b : Fin 4) (hab : a ≠ b) : ∃ π : Equiv.Perm (Fin 4), π a = 0 ∧ π b = 1 := by
  set τ := Equiv.swap a 0
  have hτa : τ a = 0 := Equiv.swap_apply_left a 0
  have hτb : τ b ≠ 0 := by
    intro h; apply hab; exact (τ.injective (h.trans hτa.symm)).symm
  refine ⟨τ.trans (Equiv.swap (τ b) 1), ?_, ?_⟩
  · simp only [Equiv.trans_apply, hτa]
    rw [Equiv.swap_apply_of_ne_of_ne (Ne.symm hτb) (by decide)]
  · simp only [Equiv.trans_apply]
    exact Equiv.swap_apply_left _ _

variable {m}

/-- **The moments of the orders two** (`eq:polarisation-moments`, first line). -/
theorem second_moments (hsym : ∀ μ ν κ l, m μ ν κ l = m μ ν l κ)
    (hperm : ∀ (π : Equiv.Perm (Fin 4)) μ ν κ l, m (π μ) (π ν) (π κ) (π l) = m μ ν κ l)
    (hrefl : ∀ σ μ ν κ l, m μ ν κ l = sgn σ μ * sgn σ ν * sgn σ κ * sgn σ l * m μ ν κ l)
    (hcyc : ∀ μ κ l s, m μ κ l s + m μ l κ s + m μ s κ l = 0) (μ ν κ l : Fin 4) :
    m μ ν κ l = m 0 1 0 1 * ((if μ = κ ∧ ν = l then 1 else 0) + (if μ = l ∧ ν = κ then 1 else 0) -
      2 * (if μ = ν ∧ κ = l then 1 else 0)) := by
  -- an index which occurs once
  have u1 : ∀ a b c d : Fin 4, a ≠ b → a ≠ c → a ≠ d → m a b c d = 0 := fun a b c d h1 h2 h3 => by
    have := hrefl a a b c d
    simp only [sgn, ↓reduceIte, Ne.symm h1, Ne.symm h2, Ne.symm h3] at this
    linarith
  have u2 : ∀ a b c d : Fin 4, b ≠ a → b ≠ c → b ≠ d → m a b c d = 0 := fun a b c d h1 h2 h3 => by
    have := hrefl b a b c d
    simp only [sgn, ↓reduceIte, Ne.symm h1, Ne.symm h2, Ne.symm h3] at this
    linarith
  have u3 : ∀ a b c d : Fin 4, c ≠ a → c ≠ b → c ≠ d → m a b c d = 0 := fun a b c d h1 h2 h3 => by
    have := hrefl c a b c d
    simp only [sgn, ↓reduceIte, Ne.symm h1, Ne.symm h2, Ne.symm h3] at this
    linarith
  have u4 : ∀ a b c d : Fin 4, d ≠ a → d ≠ b → d ≠ c → m a b c d = 0 := fun a b c d h1 h2 h3 => by
    have := hrefl d a b c d
    simp only [sgn, ↓reduceIte, Ne.symm h1, Ne.symm h2, Ne.symm h3] at this
    linarith
  -- the patterns
  have hD : ∀ a : Fin 4, m a a a a = 0 := fun a => by have := hcyc a a a a; linarith
  have hB : ∀ a b : Fin 4, a ≠ b → m a b a b = m 0 1 0 1 := fun a b hab => by
    obtain ⟨π, h0, h1⟩ := perm_to a b hab
    rw [← hperm π, h0, h1]
  have hA : ∀ a b : Fin 4, a ≠ b → m a a b b = -2 * m 0 1 0 1 := fun a b hab => by
    obtain ⟨π, h0, h1⟩ := perm_to a b hab
    rw [← hperm π, h0, h1]
    have := hcyc 0 0 1 1
    have := hsym 0 1 1 0
    linarith
  rcases eq_or_ne μ ν with hμν | hμν
  · subst hμν
    rcases eq_or_ne μ κ with hμκ | hμκ
    · subst hμκ
      rcases eq_or_ne μ l with hμl | hμl
      · subst hμl; rw [hD]; norm_num
      · rw [u4 μ μ μ l (Ne.symm hμl) (Ne.symm hμl) (Ne.symm hμl)]
        simp [hμl]
    · rcases eq_or_ne κ l with hκl | hκl
      · subst hκl; rw [hA μ κ hμκ]; simp [hμκ]; ring
      · rw [u3 μ μ κ l (Ne.symm hμκ) (Ne.symm hμκ) hκl]
        simp [hμκ, hκl]
  · rcases eq_or_ne μ κ with hμκ | hμκ
    · subst hμκ
      rcases eq_or_ne ν l with hνl | hνl
      · subst hνl; rw [hB μ ν hμν]; simp [hμν]
      · rw [u2 μ ν μ l (Ne.symm hμν) (Ne.symm hμν) hνl]
        simp [hμν, hνl, Ne.symm hμν]
    · rcases eq_or_ne μ l with hμl | hμl
      · subst hμl
        rcases eq_or_ne ν κ with hνκ | hνκ
        · subst hνκ; rw [hsym, hB μ ν hμν]; simp [hμν]
        · rw [u2 μ ν κ μ (Ne.symm hμν) hνκ (Ne.symm hμν)]
          simp [hμν, hνκ, hμκ]
      · rw [u1 μ ν κ l hμν hμκ hμl]
        simp [hμν, hμκ, hμl]

end Polarisation
end CoreLean

end
