/-
The discrete Fourier transform on the torus `(ℤ/N)⁴`, for `prop:momentum-space` of BALABAN_CORE.tex: the characters
`χ_s(z) = ∏_i e(s_iz_i)`, `e = ZMod.stdAddChar`, their orthogonality, the transform `f̂(s) = Σ_z χ̄_s(z)f(z)`, its inversion
in both directions, the Parseval identity, and the transform of a translate.
-/
import Mathlib

open Complex

noncomputable section

namespace CoreLean
namespace TorusFourier

variable {N : ℕ} [NeZero N]

/-- The torus `(ℤ/N)⁴`. -/
abbrev Tor (N : ℕ) := Fin 4 → ZMod N

local notation "e" => (ZMod.stdAddChar : AddChar (ZMod N) ℂ)

lemma e_add (a b : ZMod N) : e (a + b) = e a * e b := AddChar.map_add_eq_mul _ _ _

lemma e_zero : e (0 : ZMod N) = 1 := AddChar.map_zero_eq_one _

lemma norm_e (a : ZMod N) : ‖e a‖ = 1 := by rw [ZMod.stdAddChar_apply]; exact Circle.norm_coe _

lemma conj_e (a : ZMod N) : starRingEnd ℂ (e a) = e (-a) := by
  rw [ZMod.stdAddChar_apply, ZMod.stdAddChar_apply, ← Circle.coe_inv_eq_conj, AddChar.map_neg_eq_inv]

/-- `χ_s(z) = ∏_i e(s_iz_i)`. -/
def ch (s z : Tor N) : ℂ := ∏ i, e (s i * z i)

lemma ch_add_right (s z z' : Tor N) : ch s (z + z') = ch s z * ch s z' := by
  unfold ch
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => by rw [Pi.add_apply, mul_add, e_add]

lemma ch_add_left (s s' z : Tor N) : ch (s + s') z = ch s z * ch s' z := by
  unfold ch
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => by rw [Pi.add_apply, add_mul, e_add]

lemma ch_comm (s z : Tor N) : ch s z = ch z s := by
  unfold ch; exact Finset.prod_congr rfl fun i _ => by rw [mul_comm]

lemma ch_zero_left (z : Tor N) : ch 0 z = 1 := by simp [ch, e_zero]

lemma ch_zero_right (s : Tor N) : ch s 0 = 1 := by simp [ch, e_zero]

lemma conj_ch (s z : Tor N) : starRingEnd ℂ (ch s z) = ch (-s) z := by
  unfold ch
  rw [map_prod]
  exact Finset.prod_congr rfl fun i _ => by rw [conj_e, Pi.neg_apply, neg_mul]

lemma ch_neg_left (s z : Tor N) : ch (-s) z = ch s (-z) := by
  unfold ch; exact Finset.prod_congr rfl fun i _ => by rw [Pi.neg_apply, Pi.neg_apply, neg_mul, mul_neg]

lemma norm_ch (s z : Tor N) : ‖ch s z‖ = 1 := by
  unfold ch; rw [norm_prod]; exact Finset.prod_eq_one fun i _ => norm_e _

lemma ch_mul_conj (s z : Tor N) : ch s z * ch (-s) z = 1 := by
  rw [← ch_add_left, add_neg_cancel, ch_zero_left]

/-- `Σ_x e(tx) = N·1{t = 0}` on `ℤ/N`. -/
lemma sum_e_mul (t : ZMod N) : ∑ x : ZMod N, e (t * x) = if t = 0 then (N : ℂ) else 0 := by
  split_ifs with ht
  · simp [ht, e_zero, ZMod.card]
  · set S := ∑ x : ZMod N, e (t * x)
    have hS : e t * S = S := by
      rw [Finset.mul_sum]
      refine Fintype.sum_equiv (Equiv.addRight 1) _ _ fun x => ?_
      simp only [Equiv.coe_addRight]
      rw [← e_add, mul_add, mul_one, add_comm]
    have hne : e t ≠ 1 := by
      intro h
      rw [← e_zero (N := N)] at h
      exact ht (ZMod.injective_stdAddChar h)
    have : (e t - 1) * S = 0 := by rw [sub_mul, hS, one_mul, sub_self]
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne)

/-- **Orthogonality**: `Σ_zχ_s(z) = N⁴·1{s = 0}`. -/
lemma orth (s : Tor N) : ∑ z, ch s z = if s = 0 then (N : ℂ) ^ 4 else 0 := by
  unfold ch
  rw [← Fintype.piFinset_univ, ← Finset.prod_univ_sum (fun _ => Finset.univ) (fun i (x : ZMod N) => e (s i * x))]
  simp only [sum_e_mul]
  split_ifs with hs
  · simp [hs]
  · obtain ⟨i, hi⟩ : ∃ i, s i ≠ 0 := by
      by_contra h; push_neg at h; exact hs (funext h)
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [if_neg hi])

lemma orth' (z : Tor N) : ∑ s, ch s z = if z = 0 then (N : ℂ) ^ 4 else 0 := by
  rw [← orth z]; exact Finset.sum_congr rfl fun s _ => ch_comm s z

/-- The transform `f̂(s) = Σ_zχ̄_s(z)f(z)`. -/
def hat (f : Tor N → ℂ) (s : Tor N) : ℂ := ∑ z, ch (-s) z * f z

/-- The inverse transform `N⁻⁴Σ_sχ_s(z)g(s)`. -/
def inv (g : Tor N → ℂ) (z : Tor N) : ℂ := ((N : ℂ) ^ 4)⁻¹ * ∑ s, ch s z * g s

lemma N4_ne : ((N : ℂ) ^ 4) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (NeZero.ne N))

lemma hat_inv (g : Tor N → ℂ) : hat (inv g) = g := by
  funext s
  unfold hat inv
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  have h : ∀ s' : Tor N, ∑ z, ch (-s) z * (((N : ℂ) ^ 4)⁻¹ * (ch s' z * g s')) =
      ((N : ℂ) ^ 4)⁻¹ * g s' * ∑ z, ch (s' - s) z := by
    intro s'
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [sub_eq_add_neg, ch_add_left]; ring
  simp only [h, orth, sub_eq_zero, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq' Finset.univ s]
  simp only [Finset.mem_univ, if_true]
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  field_simp

lemma inv_hat (f : Tor N → ℂ) : inv (hat f) = f := by
  funext z
  unfold hat inv
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  have h : ∀ z' : Tor N, ∑ s, ((N : ℂ) ^ 4)⁻¹ * (ch s z * (ch (-s) z' * f z')) =
      ((N : ℂ) ^ 4)⁻¹ * f z' * ∑ s, ch s (z - z') := by
    intro z'
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [ch_neg_left, sub_eq_add_neg, ch_add_right]; ring
  simp only [h, orth', sub_eq_zero, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq Finset.univ z]
  simp only [Finset.mem_univ, if_true]
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  field_simp

lemma hat_injective {f g : Tor N → ℂ} (h : hat f = hat g) : f = g := by
  rw [← inv_hat f, ← inv_hat g, h]

/-- **The Parseval identity**: `Σ_z|f(z)|² = N⁻⁴Σ_s|f̂(s)|²`. -/
lemma parseval (f : Tor N → ℂ) : ∑ z, ‖f z‖ ^ 2 = ((N : ℝ) ^ 4)⁻¹ * ∑ s, ‖hat f s‖ ^ 2 := by
  have key : ∀ w : ℂ, ((‖w‖ ^ 2 : ℝ) : ℂ) = starRingEnd ℂ w * w := fun w => by
    rw [← Complex.normSq_eq_conj_mul_self, Complex.sq_norm]
  apply Complex.ofReal_injective
  push_cast
  simp only [← Complex.ofReal_pow, key]
  have h1 : ∑ z, starRingEnd ℂ (f z) * f z = ∑ z, starRingEnd ℂ (f z) * inv (hat f) z := by
    rw [inv_hat]
  rw [h1]
  unfold inv
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  have h2 : starRingEnd ℂ (hat f s) = ∑ z, ch s z * starRingEnd ℂ (f z) := by
    unfold hat
    rw [map_sum]
    exact Finset.sum_congr rfl fun z _ => by rw [map_mul, conj_ch, neg_neg]
  rw [h2, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun z _ => by ring

/-- **The transform of a translate**: `(f(· + a))^(s) = χ_s(a)f̂(s)`. -/
lemma hat_shift (f : Tor N → ℂ) (a s : Tor N) : hat (fun z => f (z + a)) s = ch s a * hat f s := by
  unfold hat
  rw [Finset.mul_sum]
  refine Fintype.sum_equiv (Equiv.addRight a) _ _ fun z => ?_
  simp only [Equiv.coe_addRight]
  have : ch (-s) z = ch (-s) (z + a) * ch s a := by
    rw [ch_add_right, mul_assoc, ch_neg_left s a, ← ch_add_right, neg_add_cancel, ch_zero_right, mul_one]
  rw [this]; ring

lemma hat_sub (f g : Tor N → ℂ) : hat (fun z => f z - g z) = fun s => hat f s - hat g s := by
  funext s; unfold hat; rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun z _ => by ring

lemma hat_smul (c : ℂ) (f : Tor N → ℂ) : hat (fun z => c * f z) = fun s => c * hat f s := by
  funext s; unfold hat; rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun z _ => by ring

end TorusFourier
end CoreLean

end
