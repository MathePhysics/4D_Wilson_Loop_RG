/-
`prop:polarisation`(iv) of BALABAN_CORE.tex (`a021c13be348`), in exact form on `ℤ⁴` (without the seam of the torus),
from (ii) and (iii). The symmetry of (ii) under a signed permutation `re_μ = ε_μe_{πμ}` is
`Π_{μν}(x) = ε_με_νΠ_{πμ,πν}(rx + s)` with `s = ½(1 - ε_μ)e_{πμ} - ½(1 - ε_ν)e_{πν}`; the substitution `y = rx + s`
(`rmap`, an affine bijection of `ℤ⁴`) transforms the moments (`m1_sym`, `m2_sym`). For `r = -id` it gives
`2m¹_{μν;κ} = (δ_{μκ} - δ_{νκ})m⁰_{μν}`, and, once the first moments vanish, the invariance of the second moments under
the permutations and the reflections; with the Ward identities of (iii) (`PolarisationWard.lean`) this is the first
line of `eq:polarisation-moments` and the vanishing of the zeroth and first moments (`polarisation_iv`).
-/
import CoreLean.PolarisationWard

open Finset

noncomputable section

namespace CoreLean
namespace Polarisation

/-- A sign function. -/
def IsSign (ε : Fin 4 → ℤ) : Prop := ∀ i, ε i = 1 ∨ ε i = -1

lemma sign_sq {ε : Fin 4 → ℤ} (hε : IsSign ε) (i : Fin 4) : ε i * ε i = 1 := by
  rcases hε i with h | h <;> rw [h] <;> norm_num

/-- The affine bijection `x ↦ rx + s`, `(rx)_{πκ} = ε_κx_κ`. -/
def rmap (ε : Fin 4 → ℤ) (hε : IsSign ε) (π : Equiv.Perm (Fin 4)) (s : Fin 4 → ℤ) :
    (Fin 4 → ℤ) ≃ (Fin 4 → ℤ) where
  toFun x := fun i => ε (π.symm i) * x (π.symm i) + s i
  invFun y := fun κ => ε κ * (y (π κ) - s (π κ))
  left_inv x := by
    funext κ; simp only [Equiv.symm_apply_apply, add_sub_cancel_right, ← mul_assoc, sign_sq hε, one_mul]
  right_inv y := by
    funext i; simp only [Equiv.apply_symm_apply, ← mul_assoc, sign_sq hε, one_mul, sub_add_cancel]

variable (S : Finset (Fin 4 → ℤ)) (P : Fin 4 → Fin 4 → (Fin 4 → ℤ) → ℝ)

lemma sum_eq_finsum (hS : ∀ μ ν x, x ∉ S → P μ ν x = 0) (μ ν : Fin 4) (g : (Fin 4 → ℤ) → ℝ) :
    ∑ x ∈ S, P μ ν x * g x = ∑ᶠ x, P μ ν x * g x := by
  rw [finsum_eq_sum_of_support_subset]
  intro x hx
  rw [Function.mem_support] at hx
  by_contra h
  exact hx (by rw [hS μ ν x h, zero_mul])

/-- The substitution `y = rx + s` in a moment. -/
lemma sum_sym (hS : ∀ μ ν x, x ∉ S → P μ ν x = 0) {ε : Fin 4 → ℤ} (hε : IsSign ε) (π : Equiv.Perm (Fin 4))
    (μ ν : Fin 4) (s : Fin 4 → ℤ) (hsym : ∀ x, P μ ν x = ε μ * ε ν * P (π μ) (π ν) (rmap ε hε π s x))
    (g : (Fin 4 → ℤ) → ℝ) :
    ∑ x ∈ S, P μ ν x * g x = ε μ * ε ν * ∑ y ∈ S, P (π μ) (π ν) y * g ((rmap ε hε π s).symm y) := by
  rw [sum_eq_finsum S P hS, sum_eq_finsum S P hS]
  have h1 : ∑ᶠ x, P μ ν x * g x = ∑ᶠ x, ((ε μ : ℝ) * ε ν) * (P (π μ) (π ν) (rmap ε hε π s x) *
      g ((rmap ε hε π s).symm (rmap ε hε π s x))) := by
    refine finsum_congr fun x => ?_
    rw [hsym x, Equiv.symm_apply_apply]; push_cast; ring
  rw [h1, ← mul_finsum']
  · congr 1
    exact finsum_comp_equiv (rmap ε hε π s) (f := fun y => P (π μ) (π ν) y * g ((rmap ε hε π s).symm y))
  · refine (S.finite_toSet.image (rmap ε hε π s).symm).subset fun x hx => ?_
    rw [Function.mem_support] at hx
    refine ⟨rmap ε hε π s x, ?_, Equiv.symm_apply_apply _ _⟩
    by_contra h
    exact hx (by rw [hS _ _ _ h, zero_mul])

lemma symm_coord {ε : Fin 4 → ℤ} (hε : IsSign ε) (π : Equiv.Perm (Fin 4)) (s y : Fin 4 → ℤ) (κ : Fin 4) :
    (((rmap ε hε π s).symm y κ : ℤ) : ℝ) = ε κ * ((y (π κ) : ℝ) - s (π κ)) := by
  simp [rmap]

/-- The first moments under the symmetry. -/
theorem m1_sym (hS : ∀ μ ν x, x ∉ S → P μ ν x = 0) {ε : Fin 4 → ℤ} (hε : IsSign ε) (π : Equiv.Perm (Fin 4))
    (μ ν : Fin 4) (s : Fin 4 → ℤ) (hsym : ∀ x, P μ ν x = ε μ * ε ν * P (π μ) (π ν) (rmap ε hε π s x))
    (κ : Fin 4) :
    m1 S P μ ν κ = ε μ * ε ν * ε κ * (m1 S P (π μ) (π ν) (π κ) - s (π κ) * m0 S P (π μ) (π ν)) := by
  unfold m1 m0
  rw [sum_sym S P hS hε π μ ν s hsym (fun x => (x κ : ℝ))]
  simp only [symm_coord]
  have h : ∑ y ∈ S, P (π μ) (π ν) y * ((ε κ : ℝ) * ((y (π κ) : ℝ) - s (π κ))) =
      (ε κ : ℝ) * (∑ y ∈ S, P (π μ) (π ν) y * (y (π κ) : ℝ) - (s (π κ) : ℝ) * ∑ y ∈ S, P (π μ) (π ν) y) := by
    simp only [Finset.mul_sum, mul_sub, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun y _ => by ring
  rw [h]; ring

/-- The second moments under the symmetry. -/
theorem m2_sym (hS : ∀ μ ν x, x ∉ S → P μ ν x = 0) {ε : Fin 4 → ℤ} (hε : IsSign ε) (π : Equiv.Perm (Fin 4))
    (μ ν : Fin 4) (s : Fin 4 → ℤ) (hsym : ∀ x, P μ ν x = ε μ * ε ν * P (π μ) (π ν) (rmap ε hε π s x))
    (κ l : Fin 4) :
    m2 S P μ ν κ l = ε μ * ε ν * ε κ * ε l * (m2 S P (π μ) (π ν) (π κ) (π l) -
      s (π l) * m1 S P (π μ) (π ν) (π κ) - s (π κ) * m1 S P (π μ) (π ν) (π l) +
      s (π κ) * s (π l) * m0 S P (π μ) (π ν)) := by
  unfold m2 m1 m0
  rw [sum_sym S P hS hε π μ ν s hsym (fun x => (x κ : ℝ) * (x l : ℝ))]
  simp only [symm_coord]
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun y _ => by ring

/-- The shift of a signed permutation, `½(1 - ε_μ)e_{πμ} - ½(1 - ε_ν)e_{πν}`. -/
def shiftv (ε : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)) (μ ν : Fin 4) : Fin 4 → ℤ :=
  (if ε μ = 1 then 0 else Pi.single (π μ) 1) - (if ε ν = 1 then 0 else Pi.single (π ν) 1)

/-- **`prop:polarisation`(iv)** in exact form on `ℤ⁴`, from the symmetries (ii) and the Ward identities (iii). -/
theorem polarisation_iv (hS : ∀ μ ν x, x ∉ S → P μ ν x = 0)
    (hw1 : ∀ μ κ, ward S P μ (fun x => (x κ : ℝ)) = 0)
    (hw3 : ∀ μ κ l σ, ward S P μ (fun x => (x κ : ℝ) * (x l : ℝ) * (x σ : ℝ)) = 0)
    (hsym : ∀ (ε : Fin 4 → ℤ) (hε : IsSign ε) (π : Equiv.Perm (Fin 4)) (μ ν : Fin 4) (x : Fin 4 → ℤ),
      P μ ν x = ε μ * ε ν * P (π μ) (π ν) (rmap ε hε π (shiftv ε π μ ν) x)) :
    (∀ μ ν, m0 S P μ ν = 0) ∧ (∀ μ ν κ, m1 S P μ ν κ = 0) ∧
      ∀ μ ν κ l, m2 S P μ ν κ l = m2 S P 0 1 0 1 * ((if μ = κ ∧ ν = l then 1 else 0) +
        (if μ = l ∧ ν = κ then 1 else 0) - 2 * (if μ = ν ∧ κ = l then 1 else 0)) := by
  have h0 : ∀ μ ν, m0 S P μ ν = 0 := fun μ ν => by rw [← ward_lin, hw1]
  -- `r = -id`
  have hneg : IsSign (fun _ => -1) := fun _ => Or.inr rfl
  have hr : ∀ μ ν κ, 2 * m1 S P μ ν κ =
      ((if μ = κ then 1 else 0) - (if ν = κ then 1 else 0)) * m0 S P μ ν := by
    intro μ ν κ
    have := m1_sym S P hS hneg (Equiv.refl _) μ ν _ (hsym _ hneg (Equiv.refl _) μ ν) κ
    simp only [Equiv.refl_apply, shiftv, if_neg (show (-1 : ℤ) ≠ 1 by norm_num), zero_sub] at this
    rw [h0] at this ⊢
    simp only [mul_zero, sub_zero] at this
    push_cast at this
    linarith
  have h1 := first_moments S P h0 hr
  have hpos : IsSign (fun _ => 1) := fun _ => Or.inl rfl
  refine polarisation_moments S P hw1 hw3 hr (fun π μ ν κ l => ?_) (fun σ μ ν κ l => ?_)
  · have := m2_sym S P hS hpos π μ ν _ (hsym _ hpos π μ ν) κ l
    rw [h1, h1, h0] at this
    simp only [Int.cast_one, one_mul, mul_zero, sub_zero, add_zero] at this
    exact this.symm
  · set ε : Fin 4 → ℤ := fun i => if i = σ then -1 else 1
    have hε : IsSign ε := fun i => by simp only [ε]; split_ifs <;> simp
    have := m2_sym S P hS hε (Equiv.refl _) μ ν _ (hsym ε hε (Equiv.refl _) μ ν) κ l
    rw [h1, h1, h0] at this
    simp only [Equiv.refl_apply, mul_zero, sub_zero, add_zero] at this
    rw [this]
    simp only [ε, sgn]
    congr 1
    simp only [apply_ite (fun z : ℤ => (z : ℝ)), Int.cast_neg, Int.cast_one]

end Polarisation
end CoreLean

end
