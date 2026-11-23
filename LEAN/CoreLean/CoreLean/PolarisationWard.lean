/-
`prop:polarisation`(iv) of BALABAN_CORE.tex (`a021c13be348`), the relations between the moments, in exact form. For a
kernel `Π_{μν}(x)` on `ℤ⁴` supported in a finite set `S`, with the moments `m⁰_{μν} = Σ_xΠ_{μν}(x)`,
`m¹_{μν;κ} = Σ_xΠ_{μν}(x)x_κ`, `m²_{μν;κλ} = Σ_xΠ_{μν}(x)x_κx_λ`, the Ward identity `eq:polarisation-ward`,
`Σ_{x,ν}Π_{μν}(x)(p(x + e_ν) - p(x)) = 0`, for `p = x_κ`, `x_κx_λ`, `x_κx_λx_σ` gives `m⁰ = 0` (`ward_zero`),
`m¹_{μκ;λ} + m¹_{μλ;κ} = 0` (`ward_one`), and, once the first moments vanish, the cyclic relation
`eq:polarisation-cyclic` (`ward_two`). With the relation `2m¹_{μν;κ} = (δ_{μκ} - δ_{νκ})m⁰_{μν}` of the reflection
`r = -id` the first moments vanish (`first_moments`), and with the invariance under the signed permutations
`second_moments` gives the first line of `eq:polarisation-moments` (`polarisation_moments`).
-/
import CoreLean.PolarisationMoments

open Finset

noncomputable section

namespace CoreLean
namespace Polarisation

variable (S : Finset (Fin 4 → ℤ)) (P : Fin 4 → Fin 4 → (Fin 4 → ℤ) → ℝ)

/-- `m⁰_{μν}`. -/
def m0 (μ ν : Fin 4) : ℝ := ∑ x ∈ S, P μ ν x
/-- `m¹_{μν;κ}`. -/
def m1 (μ ν κ : Fin 4) : ℝ := ∑ x ∈ S, P μ ν x * (x κ : ℝ)
/-- `m²_{μν;κλ}`. -/
def m2 (μ ν κ l : Fin 4) : ℝ := ∑ x ∈ S, P μ ν x * ((x κ : ℝ) * (x l : ℝ))

/-- The Ward sum `Σ_{x,ν}P_{μν}(x)(p(x + e_ν) - p(x))`. -/
def ward (μ : Fin 4) (p : (Fin 4 → ℤ) → ℝ) : ℝ :=
  ∑ x ∈ S, ∑ ν, P μ ν x * (p (x + Pi.single ν 1) - p x)

lemma shift (x : Fin 4 → ℤ) (ν κ : Fin 4) :
    (((x + Pi.single ν 1 : Fin 4 → ℤ) κ : ℤ) : ℝ) = (x κ : ℝ) + if κ = ν then 1 else 0 := by
  simp only [Pi.add_apply, Pi.single_apply]; split_ifs <;> push_cast <;> ring

/-- The linear polynomial: `ward(x_κ) = m⁰_{μκ}`. -/
lemma ward_lin (μ κ : Fin 4) : ward S P μ (fun x => (x κ : ℝ)) = m0 S P μ κ := by
  unfold ward m0
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [shift, add_sub_cancel_left, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]; simp

/-- The quadratic polynomial: `ward(x_κx_λ) = m¹_{μκ;λ} + m¹_{μλ;κ} + δ_{κλ}m⁰_{μκ}`. -/
lemma ward_quad (μ κ l : Fin 4) :
    ward S P μ (fun x => (x κ : ℝ) * (x l : ℝ)) =
      m1 S P μ κ l + m1 S P μ l κ + if κ = l then m0 S P μ κ else 0 := by
  unfold ward m1 m0
  have e : ∀ x : Fin 4 → ℤ, ∑ ν, P μ ν x * ((((x + Pi.single ν 1 : Fin 4 → ℤ) κ : ℤ) : ℝ) *
      (((x + Pi.single ν 1 : Fin 4 → ℤ) l : ℤ) : ℝ) - (x κ : ℝ) * (x l : ℝ)) =
      P μ κ x * (x l : ℝ) + P μ l x * (x κ : ℝ) + if κ = l then P μ κ x else 0 := by
    intro x
    simp only [shift]
    have : ∀ ν, P μ ν x * (((x κ : ℝ) + if κ = ν then 1 else 0) * ((x l : ℝ) + if l = ν then 1 else 0) -
        (x κ : ℝ) * (x l : ℝ)) = (if κ = ν then P μ ν x * (x l : ℝ) else 0) +
          (if l = ν then P μ ν x * (x κ : ℝ) else 0) + (if κ = ν ∧ l = ν then P μ ν x else 0) := by
      intro ν
      by_cases h1 : κ = ν <;> by_cases h2 : l = ν <;>
        simp only [h1, h2, if_true, if_false, and_self, and_false, false_and, add_zero, zero_add,
          not_false_eq_true] <;> ring
    rw [Finset.sum_congr rfl fun ν _ => this ν, Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_ite_eq, Finset.sum_ite_eq]
    simp only [mem_univ, if_true]
    congr 1
    by_cases h : κ = l
    · subst h; simp
    · rw [if_neg h]
      exact Finset.sum_eq_zero fun ν _ => if_neg fun h' => h (h'.1.trans h'.2.symm)
  rw [Finset.sum_congr rfl fun x _ => e x, Finset.sum_add_distrib, Finset.sum_add_distrib]
  congr 1
  by_cases h : κ = l
  · simp [h]
  · simp [h]

lemma sum_pair (κ l : Fin 4) (g : Fin 4 → ℝ) :
    ∑ ν, (if κ = ν ∧ l = ν then g ν else 0) = if κ = l then g κ else 0 := by
  by_cases h : κ = l
  · subst h; simp
  · rw [if_neg h]
    exact Finset.sum_eq_zero fun ν _ => if_neg fun h' => h (h'.1.trans h'.2.symm)

/-- The cubic polynomial, with vanishing zeroth and first moments: `ward(x_κx_λx_σ)` is the cyclic sum of the
second moments. -/
lemma ward_cubic (h0 : ∀ μ ν, m0 S P μ ν = 0) (h1 : ∀ μ ν κ, m1 S P μ ν κ = 0) (μ κ l σ : Fin 4) :
    ward S P μ (fun x => (x κ : ℝ) * (x l : ℝ) * (x σ : ℝ)) =
      m2 S P μ κ l σ + m2 S P μ l κ σ + m2 S P μ σ κ l := by
  unfold ward
  have e : ∀ x : Fin 4 → ℤ, ∑ ν, P μ ν x * ((((x + Pi.single ν 1 : Fin 4 → ℤ) κ : ℤ) : ℝ) *
      (((x + Pi.single ν 1 : Fin 4 → ℤ) l : ℤ) : ℝ) * (((x + Pi.single ν 1 : Fin 4 → ℤ) σ : ℤ) : ℝ) -
        (x κ : ℝ) * (x l : ℝ) * (x σ : ℝ)) =
      P μ κ x * ((x l : ℝ) * (x σ : ℝ)) + P μ l x * ((x κ : ℝ) * (x σ : ℝ)) +
        P μ σ x * ((x κ : ℝ) * (x l : ℝ)) +
      ((if κ = l then P μ κ x * (x σ : ℝ) else 0) + (if κ = σ then P μ κ x * (x l : ℝ) else 0) +
        (if l = σ then P μ l x * (x κ : ℝ) else 0) +
        (if κ = l then (if l = σ then P μ κ x else 0) else 0)) := by
    intro x
    simp only [shift]
    have : ∀ ν, P μ ν x * (((x κ : ℝ) + if κ = ν then 1 else 0) * ((x l : ℝ) + if l = ν then 1 else 0) *
        ((x σ : ℝ) + if σ = ν then 1 else 0) - (x κ : ℝ) * (x l : ℝ) * (x σ : ℝ)) =
        (if κ = ν then P μ ν x * ((x l : ℝ) * (x σ : ℝ)) else 0) +
        (if l = ν then P μ ν x * ((x κ : ℝ) * (x σ : ℝ)) else 0) +
        (if σ = ν then P μ ν x * ((x κ : ℝ) * (x l : ℝ)) else 0) +
        ((if κ = ν ∧ l = ν then P μ ν x * (x σ : ℝ) else 0) +
          (if κ = ν ∧ σ = ν then P μ ν x * (x l : ℝ) else 0) +
          (if l = ν ∧ σ = ν then P μ ν x * (x κ : ℝ) else 0) +
          (if κ = ν ∧ l = ν then (if σ = ν then P μ ν x else 0) else 0)) := by
      intro ν
      by_cases h1 : κ = ν <;> by_cases h2 : l = ν <;> by_cases h3 : σ = ν <;>
        simp only [h1, h2, h3, if_true, if_false, and_self, and_false, false_and, add_zero, zero_add,
          not_false_eq_true] <;> ring
    rw [Finset.sum_congr rfl fun ν _ => this ν]
    simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, mem_univ, if_true, sum_pair]
    congr 1
    by_cases hκl : κ = l
    · subst hκl
      by_cases hls : κ = σ
      · subst hls; simp
      · simp [hls, Ne.symm hls]
    · simp [hκl]
  rw [Finset.sum_congr rfl fun x _ => e x]
  simp only [Finset.sum_add_distrib]
  have r1 : ∑ x ∈ S, (if κ = l then P μ κ x * (x σ : ℝ) else 0) = 0 := by
    split_ifs
    · exact h1 μ κ σ
    · simp
  have r2 : ∑ x ∈ S, (if κ = σ then P μ κ x * (x l : ℝ) else 0) = 0 := by
    split_ifs
    · exact h1 μ κ l
    · simp
  have r3 : ∑ x ∈ S, (if l = σ then P μ l x * (x κ : ℝ) else 0) = 0 := by
    split_ifs
    · exact h1 μ l κ
    · simp
  have r4 : ∑ x ∈ S, (if κ = l then (if l = σ then P μ κ x else 0) else 0) = 0 := by
    split_ifs
    · exact h0 μ κ
    · simp
    · simp
  rw [r1, r2, r3, r4]
  unfold m2
  ring

/-- **The first moments vanish**: from `2m¹_{μν;κ} = (δ_{μκ} - δ_{νκ})m⁰_{μν}` and `m⁰ = 0`. -/
theorem first_moments (h0 : ∀ μ ν, m0 S P μ ν = 0)
    (hr : ∀ μ ν κ, 2 * m1 S P μ ν κ = ((if μ = κ then 1 else 0) - (if ν = κ then 1 else 0)) * m0 S P μ ν)
    (μ ν κ : Fin 4) : m1 S P μ ν κ = 0 := by
  have := hr μ ν κ
  rw [h0, mul_zero] at this
  linarith

/-- **The moments of `eq:polarisation-moments`** in exact form: the Ward identities for the polynomials of the
degrees one to three, the reflection relation of the first moments, and the invariance of the second moments under
the signed permutations give `m⁰ = 0`, `m¹ = 0`, and `m²_{μν;κλ} = β(δ_{μκ}δ_{νλ} + δ_{μλ}δ_{νκ} - 2δ_{μν}δ_{κλ})`. -/
theorem polarisation_moments
    (hw1 : ∀ μ κ, ward S P μ (fun x => (x κ : ℝ)) = 0)
    (hw3 : ∀ μ κ l σ, ward S P μ (fun x => (x κ : ℝ) * (x l : ℝ) * (x σ : ℝ)) = 0)
    (hr : ∀ μ ν κ, 2 * m1 S P μ ν κ = ((if μ = κ then 1 else 0) - (if ν = κ then 1 else 0)) * m0 S P μ ν)
    (hperm : ∀ (π : Equiv.Perm (Fin 4)) μ ν κ l, m2 S P (π μ) (π ν) (π κ) (π l) = m2 S P μ ν κ l)
    (hrefl : ∀ σ μ ν κ l, m2 S P μ ν κ l = sgn σ μ * sgn σ ν * sgn σ κ * sgn σ l * m2 S P μ ν κ l) :
    (∀ μ ν, m0 S P μ ν = 0) ∧ (∀ μ ν κ, m1 S P μ ν κ = 0) ∧
      ∀ μ ν κ l, m2 S P μ ν κ l = m2 S P 0 1 0 1 * ((if μ = κ ∧ ν = l then 1 else 0) +
        (if μ = l ∧ ν = κ then 1 else 0) - 2 * (if μ = ν ∧ κ = l then 1 else 0)) := by
  have h0 : ∀ μ ν, m0 S P μ ν = 0 := fun μ ν => by rw [← ward_lin, hw1]
  have h1 := first_moments S P h0 hr
  refine ⟨h0, h1, fun μ ν κ l => ?_⟩
  refine second_moments (fun μ ν κ l => ?_) hperm hrefl (fun μ κ l s => ?_) μ ν κ l
  · unfold m2; exact Finset.sum_congr rfl fun x _ => by ring
  · rw [← ward_cubic S P h0 h1, hw3]

end Polarisation
end CoreLean

end
