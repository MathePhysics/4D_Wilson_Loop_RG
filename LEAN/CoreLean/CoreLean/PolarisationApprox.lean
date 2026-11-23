/-
`prop:polarisation`(iv) of BALABAN_CORE.tex (`a021c13be348`), the last step with the error of the torus. On the torus the
cyclic relation `eq:polarisation-cyclic` holds up to an error `ε` (the cut of the polynomials at the seam), while the
symmetries under the signed permutations are exact. Then the second moments are
`β(δ_{μκ}δ_{νλ} + δ_{μλ}δ_{νκ} - 2δ_{μν}δ_{κλ})` up to `ε`, with `β = m_{01;01}` (`second_moments_approx`): the moments
with an index which occurs once vanish exactly, `|m_{aa;aa}| ≤ ε/3` and `|m_{aa;bb} + 2β| ≤ ε` by the cyclic relation, and
the other patterns equal `±β` or `0` exactly. This is the exact `second_moments` (`PolarisationMoments.lean`) with the
error carried through.
-/
import CoreLean.PolarisationMoments

noncomputable section

namespace CoreLean
namespace Polarisation

variable (m : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ)

/-- **The second moments up to the error `ε`**. -/
theorem second_moments_approx {ε : ℝ} (hsym : ∀ μ ν κ l, m μ ν κ l = m μ ν l κ)
    (hperm : ∀ (π : Equiv.Perm (Fin 4)) μ ν κ l, m (π μ) (π ν) (π κ) (π l) = m μ ν κ l)
    (hrefl : ∀ σ μ ν κ l, m μ ν κ l = sgn σ μ * sgn σ ν * sgn σ κ * sgn σ l * m μ ν κ l)
    (hcyc : ∀ μ κ l s, |m μ κ l s + m μ l κ s + m μ s κ l| ≤ ε) (μ ν κ l : Fin 4) :
    |m μ ν κ l - m 0 1 0 1 * ((if μ = κ ∧ ν = l then 1 else 0) + (if μ = l ∧ ν = κ then 1 else 0) -
      2 * (if μ = ν ∧ κ = l then 1 else 0))| ≤ ε := by
  have hε : 0 ≤ ε := (abs_nonneg _).trans (hcyc 0 0 0 0)
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
  have hD : ∀ a : Fin 4, |m a a a a| ≤ ε := fun a => by
    have h := hcyc a a a a
    rw [show m a a a a + m a a a a + m a a a a = 3 * m a a a a by ring, abs_mul] at h
    have : |(3 : ℝ)| = 3 := by norm_num
    rw [this] at h
    linarith [abs_nonneg (m a a a a)]
  have hB : ∀ a b : Fin 4, a ≠ b → m a b a b = m 0 1 0 1 := fun a b hab => by
    obtain ⟨π, h0, h1⟩ := perm_to a b hab
    rw [← hperm π, h0, h1]
  have hA : ∀ a b : Fin 4, a ≠ b → |m a a b b + 2 * m 0 1 0 1| ≤ ε := fun a b hab => by
    obtain ⟨π, h0, h1⟩ := perm_to a b hab
    rw [← hperm π, h0, h1]
    have h := hcyc 0 0 1 1
    have hs := hsym 0 1 1 0
    rw [show m 0 0 1 1 + m 0 1 0 1 + m 0 1 0 1 = m 0 0 1 1 + 2 * m 0 1 0 1 by ring] at h
    exact h
  rcases eq_or_ne μ ν with hμν | hμν
  · subst hμν
    rcases eq_or_ne μ κ with hμκ | hμκ
    · subst hμκ
      rcases eq_or_ne μ l with hμl | hμl
      · subst hμl; simp only [and_self, ↓reduceIte]; norm_num; exact hD μ
      · rw [u4 μ μ μ l (Ne.symm hμl) (Ne.symm hμl) (Ne.symm hμl)]
        simp [hμl, hε]
    · rcases eq_or_ne κ l with hκl | hκl
      · subst hκl
        simp only [hμκ, false_and, and_true, ↓reduceIte]
        have := hA μ κ hμκ
        rw [show m μ μ κ κ - m 0 1 0 1 * (0 + 0 - 2 * 1) = m μ μ κ κ + 2 * m 0 1 0 1 by ring]
        exact this
      · rw [u3 μ μ κ l (Ne.symm hμκ) (Ne.symm hμκ) hκl]
        simp [hμκ, hκl, hε]
  · rcases eq_or_ne μ κ with hμκ | hμκ
    · subst hμκ
      rcases eq_or_ne ν l with hνl | hνl
      · subst hνl; rw [hB μ ν hμν]; simp [hμν, hε]
      · rw [u2 μ ν μ l (Ne.symm hμν) (Ne.symm hμν) hνl]
        simp [hμν, hνl, Ne.symm hμν, hε]
    · rcases eq_or_ne μ l with hμl | hμl
      · subst hμl
        rcases eq_or_ne ν κ with hνκ | hνκ
        · subst hνκ; rw [hsym, hB μ ν hμν]; simp [hμν, hε]
        · rw [u2 μ ν κ μ (Ne.symm hμν) hνκ (Ne.symm hμν)]
          simp [hμν, hνκ, hμκ, hε]
      · rw [u1 μ ν κ l hμν hμκ hμl]
        simp [hμν, hμκ, hμl, hε]

end Polarisation
end CoreLean

end
