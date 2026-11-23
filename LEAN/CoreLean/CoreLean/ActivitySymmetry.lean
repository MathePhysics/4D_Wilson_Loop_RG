/-
`lem:activity-parameters` of BALABAN_CORE.tex (`a021c13be348`), the arguments of its proof in abstract form.

* (i), the symmetry: the measures `μ₀` (of `X`) and `ν_{Q(s)}` (of `A`) are invariant under the negation, and the
  integrand of `eq:conditioned-term` at `ιλ`, `-A`, `-X` is `Π_Gε_G` times that at `λ`, `A`, `X`; the substitution
  `A = -A''`, `X ↦ -X` gives `f(Z₀; s; ιλ) = Π_Gε_G f(Z₀; s; λ)` (`activity_sign`). The sign of a product of marked
  factors is the product of their signs (`prod_sign`), and the activities, being derivatives in `s` and finite sums
  of these functions, have the same sign (`deriv_sign`, `sum_sign`).
* (ii), the bound of the cut-offs: `1 - χ_b ≤ 1[‖A(b)‖ ≥ ½𝗍(h)] ≤ e^{½γ₂(|A(b)|² - r₀²)}` for `r₀ = ½𝗍₀ ≤ ½𝗍(h)`,
  `χ_b ≥ 0`, `χ_b = 1` below `½𝗍(h)`, and `‖A(b)‖ ≤ |A(b)|` (`cutoff_bound`).
-/
import Mathlib

open MeasureTheory

noncomputable section

namespace CoreLean
namespace ActivitySymmetry

/-- **(i)**: the sign under `λ ↦ ιλ` of the doubly integrated term. -/
theorem activity_sign {Λ Xs As : Type*} [MeasurableSpace Xs] [AddGroup Xs] [MeasurableNeg Xs]
    [MeasurableSpace As] [AddGroup As] [MeasurableNeg As] (μ₀ : Measure Xs) (ν : Measure As)
    [μ₀.IsNegInvariant] [ν.IsNegInvariant] (F : Λ → As → Xs → ℂ) (ι : Λ → Λ) (ε : ℂ)
    (hF : ∀ l A X, F (ι l) (-A) (-X) = ε * F l A X) (l : Λ) :
    ∫ X, ∫ A, F (ι l) A X ∂ν ∂μ₀ = ε * ∫ X, ∫ A, F l A X ∂ν ∂μ₀ := by
  rw [← integral_neg_eq_self (fun X => ∫ A, F (ι l) A X ∂ν) μ₀]
  have h : ∀ X, ∫ A, F (ι l) A (-X) ∂ν = ε * ∫ A, F l A X ∂ν := by
    intro X
    rw [← integral_neg_eq_self (fun A => F (ι l) A (-X)) ν]
    simp only [hF]
    exact integral_const_mul ε _
  simp only [h]
  exact integral_const_mul ε _

/-- The sign of a product of marked factors. -/
theorem prod_sign {ι' Λ As : Type*} [Neg As] (s : Finset ι') (Xf : ι' → Λ → As → ℂ) (ι : Λ → Λ) (ε : ι' → ℂ)
    (hX : ∀ G l A, Xf G (ι l) (-A) = ε G * Xf G l A) (l : Λ) (A : As) :
    ∏ G ∈ s, Xf G (ι l) (-A) = (∏ G ∈ s, ε G) * ∏ G ∈ s, Xf G l A := by
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun G _ => hX G l A

/-- Derivatives in `s` keep the sign. -/
theorem deriv_sign {Λ : Type*} (f : Λ → ℂ → ℂ) (ι : Λ → Λ) (ε : ℂ) (hf : ∀ l s, f (ι l) s = ε * f l s)
    (l : Λ) (n : ℕ) (s : ℂ) : iteratedDeriv n (f (ι l)) s = ε * iteratedDeriv n (f l) s := by
  have : f (ι l) = fun s => ε * f l s := funext (hf l)
  rw [this, iteratedDeriv_const_mul_field]

/-- Finite sums keep the sign. -/
theorem sum_sign {Λ κ : Type*} (t : Finset κ) (f : κ → Λ → ℂ) (ι : Λ → Λ) (ε : ℂ)
    (hf : ∀ i l, f i (ι l) = ε * f i l) (l : Λ) : ∑ i ∈ t, f i (ι l) = ε * ∑ i ∈ t, f i l := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => hf i l

/-- **(ii)**, the bound of `1 - χ_b`. -/
theorem cutoff_bound {χ a a' t r₀ γ : ℝ} (hγ : 0 ≤ γ) (ha : 0 ≤ a) (ha' : a ≤ a') (hχ0 : 0 ≤ χ)
    (hχ : a < t / 2 → χ = 1) (hr : r₀ ≤ t / 2) (hr0 : 0 ≤ r₀) :
    1 - χ ≤ Real.exp (γ / 2 * (a' ^ 2 - r₀ ^ 2)) := by
  by_cases h : a < t / 2
  · rw [hχ h, sub_self]; exact (Real.exp_pos _).le
  · replace h := not_lt.1 h
    have : r₀ ^ 2 ≤ a' ^ 2 := pow_le_pow_left₀ hr0 ((hr.trans h).trans ha') 2
    have h1 : 1 ≤ Real.exp (γ / 2 * (a' ^ 2 - r₀ ^ 2)) :=
      Real.one_le_exp (mul_nonneg (by positivity) (by linarith))
    linarith

end ActivitySymmetry
end CoreLean

end
