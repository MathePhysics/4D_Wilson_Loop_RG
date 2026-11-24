/-
`lem:local-laplacian`(i) of BALABAN_CORE.tex (`0580551bf179`): Young's inequality for convolutions on a group, in the
finite form used in the proof: for `1 < s < q`, `1 < p < q` with `s⁻¹ + p⁻¹ = 1 + q⁻¹`, a kernel `K ≥ 0` on a finite set
`Z` and `f ≥ 0` vanishing outside a finite set `B`,
`Σ_{n ∈ A}(Σ_{z ∈ Z}K(z)f(n - z))^q ≤ (Σ_{z ∈ Z}K(z)^s)^{q/s}(Σ_{m ∈ B}f(m)^p)^{q/p}`
(`young_fin`), and for `q = ∞` (`s⁻¹ + p⁻¹ = 1`) `Σ_{z ∈ Z}K(z)f(n - z) ≤ ‖K‖_s‖f‖_p` (`young_inf`).

The proof is the classical one: `Kf = (K^sf^p)^{1/q}·K^{1-s/q}·f^{1-p/q}`, Hölder's inequality with the exponents
`q`, `sq/(q - s)`, `pq/(q - p)`, and the sum over `n`.
-/
import Mathlib.Analysis.MeanInequalities

open Finset NNReal

noncomputable section

namespace CoreLean
namespace LocalLaplacian

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- A sum of `g ∘ φ`, `φ` injective, over any finite set is at most the sum of `g` over a set containing the support. -/
lemma sum_comp_inj_le {g : G → ℝ≥0} {B : Finset G} (hg : ∀ m, g m ≠ 0 → m ∈ B) {φ : G → G}
    (hφ : Function.Injective φ) (S : Finset G) : ∑ x ∈ S, g (φ x) ≤ ∑ m ∈ B, g m := by
  rw [← sum_image (hφ.injOn), ← sum_filter_ne_zero]
  exact sum_le_sum_of_subset fun m hm => by rw [mem_filter] at hm; exact hg m hm.2

/-- **Young's inequality**, `q < ∞`. -/
theorem young_fin (A Z B : Finset G) (K f : G → ℝ≥0) (hf : ∀ m, f m ≠ 0 → m ∈ B) {s p q : ℝ} (hs : 1 < s)
    (hp : 1 < p) (hsq : s < q) (hpq : p < q) (hrel : s⁻¹ + p⁻¹ = 1 + q⁻¹) :
    ∑ n ∈ A, (∑ z ∈ Z, K z * f (n - z)) ^ q ≤ (∑ z ∈ Z, K z ^ s) ^ (q / s) * (∑ m ∈ B, f m ^ p) ^ (q / p) := by
  have hq0 : 0 < q := by linarith
  have hq1 : 1 < q := by linarith
  have hs0 : 0 < s := by linarith
  have hp0 : 0 < p := by linarith
  set q' := Real.conjExponent q
  have hq' : q.HolderConjugate q' := Real.HolderConjugate.conjExponent hq1
  set a := s * q / (q - s) with ha
  set b := p * q / (q - p) with hb
  have ha0 : 0 < a := div_pos (mul_pos hs0 hq0) (by linarith)
  have hb0 : 0 < b := div_pos (mul_pos hp0 hq0) (by linarith)
  have hqs : q - s ≠ 0 := by linarith
  have hqp : q - p ≠ 0 := by linarith
  have hai : a⁻¹ = s⁻¹ - q⁻¹ := by rw [ha]; field_simp
  have hbi : b⁻¹ = p⁻¹ - q⁻¹ := by rw [hb]; field_simp
  have hq'i : q'⁻¹ = 1 - q⁻¹ := by
    show (q / (q - 1))⁻¹ = 1 - q⁻¹
    have : q - 1 ≠ 0 := by linarith
    field_simp
  have hab : a.HolderTriple b q' := ⟨by rw [hai, hbi, hq'i]; linarith, ha0, hb0⟩
  set SK := ∑ z ∈ Z, K z ^ s
  set Sf := ∑ m ∈ B, f m ^ p
  -- the bound at one point
  have hn : ∀ n, (∑ z ∈ Z, K z * f (n - z)) ^ q ≤ (∑ z ∈ Z, K z ^ s * f (n - z) ^ p) * SK ^ (q / a) * Sf ^ (q / b) := by
    intro n
    set X : G → ℝ≥0 := fun z => (K z ^ s * f (n - z) ^ p) ^ q⁻¹
    set Y : G → ℝ≥0 := fun z => K z ^ (1 - s / q)
    set W : G → ℝ≥0 := fun z => f (n - z) ^ (1 - p / q)
    have e1 : ∀ z, K z * f (n - z) = X z * (Y z * W z) := fun z => by
      simp only [X, Y, W, mul_rpow, ← rpow_mul]
      calc K z * f (n - z) = K z ^ (1 : ℝ) * f (n - z) ^ (1 : ℝ) := by simp
        _ = K z ^ (s * q⁻¹ + (1 - s / q)) * f (n - z) ^ (p * q⁻¹ + (1 - p / q)) := by
            congr 2 <;> field_simp <;> ring
        _ = K z ^ (s * q⁻¹) * f (n - z) ^ (p * q⁻¹) * (K z ^ (1 - s / q) * f (n - z) ^ (1 - p / q)) := by
            have e1 : s * q⁻¹ + (1 - s / q) = 1 := by field_simp [hq0.ne']; ring
            have e2 : p * q⁻¹ + (1 - p / q) = 1 := by field_simp [hq0.ne']; ring
            rw [rpow_add' (by rw [e1]; norm_num), rpow_add' (by rw [e2]; norm_num)]; ring
    have eX : ∀ z, X z ^ q = K z ^ s * f (n - z) ^ p := fun z => by
      simp only [X, ← rpow_mul, inv_mul_cancel₀ hq0.ne', rpow_one]
    have eY : ∀ z, Y z ^ a = K z ^ s := fun z => by
      simp only [Y, ← rpow_mul]; congr 1; rw [ha]; field_simp <;> ring
    have eW : ∀ z, W z ^ b = f (n - z) ^ p := fun z => by
      simp only [W, ← rpow_mul]; congr 1; rw [hb]; field_simp <;> ring
    have h1 := inner_le_Lp_mul_Lq Z X (fun z => Y z * W z) hq'
    have h2 := Lr_le_Lp_mul_Lq Z Y W hab
    have h3 : ∑ z ∈ Z, W z ^ b ≤ Sf := by
      simp only [eW]
      exact sum_comp_inj_le (g := fun m => f m ^ p) (fun m hm => hf m fun h => hm (by simp [h, hp0.ne'])) (sub_right_injective) Z
    simp only [eX, eY] at h1 h2
    have hsum : ∑ z ∈ Z, K z * f (n - z) ≤
        (∑ z ∈ Z, K z ^ s * f (n - z) ^ p) ^ (1 / q) * (SK ^ (1 / a) * Sf ^ (1 / b)) := by
      rw [sum_congr rfl fun z _ => e1 z]
      refine h1.trans (mul_le_mul_of_nonneg_left (h2.trans (mul_le_mul_of_nonneg_left (rpow_le_rpow h3 (by positivity)) (by positivity))) (by positivity))
    calc (∑ z ∈ Z, K z * f (n - z)) ^ q
        ≤ ((∑ z ∈ Z, K z ^ s * f (n - z) ^ p) ^ (1 / q) * (SK ^ (1 / a) * Sf ^ (1 / b))) ^ q :=
          rpow_le_rpow hsum hq0.le
      _ = (∑ z ∈ Z, K z ^ s * f (n - z) ^ p) * SK ^ (q / a) * Sf ^ (q / b) := by
          rw [mul_rpow, mul_rpow, ← rpow_mul, ← rpow_mul, ← rpow_mul, one_div_mul_cancel hq0.ne', rpow_one,
            one_div_mul_eq_div, one_div_mul_eq_div, mul_assoc]
  -- the sum over `n`
  have hsumn : ∑ n ∈ A, ∑ z ∈ Z, K z ^ s * f (n - z) ^ p ≤ SK * Sf := by
    rw [sum_comm, sum_mul]
    refine sum_le_sum fun z _ => ?_
    rw [← mul_sum]
    exact mul_le_mul_of_nonneg_left (sum_comp_inj_le (g := fun m => f m ^ p)
      (fun m hm => hf m fun h => hm (by simp [h, hp0.ne'])) (sub_left_injective) A) (by positivity)
  calc ∑ n ∈ A, (∑ z ∈ Z, K z * f (n - z)) ^ q
      ≤ ∑ n ∈ A, (∑ z ∈ Z, K z ^ s * f (n - z) ^ p) * SK ^ (q / a) * Sf ^ (q / b) := sum_le_sum fun n _ => hn n
    _ = (∑ n ∈ A, ∑ z ∈ Z, K z ^ s * f (n - z) ^ p) * (SK ^ (q / a) * Sf ^ (q / b)) := by
        rw [sum_mul]; exact sum_congr rfl fun n _ => by ring
    _ ≤ SK * Sf * (SK ^ (q / a) * Sf ^ (q / b)) := mul_le_mul_of_nonneg_right hsumn (by positivity)
    _ = SK ^ (q / s) * Sf ^ (q / p) := by
        have ea : (1 : ℝ) + q / a = q / s := by rw [ha]; field_simp; ring
        have eb : (1 : ℝ) + q / b = q / p := by rw [hb]; field_simp; ring
        rw [← ea, ← eb, rpow_add' (by rw [ea]; positivity), rpow_add' (by rw [eb]; positivity), rpow_one, rpow_one]
        ring

/-- **Young's inequality**, `q = ∞`. -/
theorem young_inf (Z B : Finset G) (K f : G → ℝ≥0) (hf : ∀ m, f m ≠ 0 → m ∈ B) {s p : ℝ}
    (hsp : s.HolderConjugate p) (n : G) :
    ∑ z ∈ Z, K z * f (n - z) ≤ (∑ z ∈ Z, K z ^ s) ^ (1 / s) * (∑ m ∈ B, f m ^ p) ^ (1 / p) := by
  have hp0 : 0 < p := hsp.right_pos
  refine (inner_le_Lp_mul_Lq Z K (fun z => f (n - z)) hsp).trans (mul_le_mul_of_nonneg_left (rpow_le_rpow ?_ (by positivity)) (by positivity))
  exact sum_comp_inj_le (g := fun m => f m ^ p) (fun m hm => hf m fun h => hm (by simp [h, hp0.ne']))
    (sub_right_injective) Z

end LocalLaplacian
end CoreLean

end
