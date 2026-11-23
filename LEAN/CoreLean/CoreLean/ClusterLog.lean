/-
The logarithm of a polynomial without zeros in the unit disc, for the cluster expansion of `thm:polymer-logarithm` of
BALABAN_CORE.tex (`5bbe1bc62521`). If `P ∈ ℂ[X]` has `P(0) = 1`, no zero in the open unit disc, and
`X·P' = -(Σ_kkb_kX^k)·P` in `ℂ⟦X⟧` for a real sequence `b` with `b_0 = 0`, then for real `t ∈ [0, 1)`
`Σ_kb_kt^k = -log|P(t)|`. Proof: `P = Π_ρ(1 - ρX)` over the inverses `ρ` of its roots, `|ρ| ≤ 1`; Newton's identities
give `kb_k = Σ_ρρ^k`; and `Σ_k(ρt)^k/k = -log(1 - ρt)` with the real part `-log|1 - ρt|`.
-/
import CoreLean.ClusterNewton

open Polynomial

noncomputable section

namespace CoreLean
namespace Newton

/-- `P = Π_{r ∈ roots}(1 - r⁻¹X)` for `P(0) = 1`. -/
lemma factor_of_eval_zero (P : ℂ[X]) (hP0 : P.eval 0 = 1) :
    P = (P.roots.map fun r => (1 - Polynomial.C r⁻¹ * X)).prod := by
  have hP : P ≠ 0 := fun h => by rw [h, eval_zero] at hP0; exact zero_ne_one hP0
  have hr0 : ∀ r ∈ P.roots, r ≠ 0 := fun r hr h => by
    rw [h] at hr; rw [(mem_roots hP).1 hr] at hP0; exact zero_ne_one hP0
  have hfac := C_leadingCoeff_mul_prod_multiset_X_sub_C (IsAlgClosed.card_roots_eq_natDegree (p := P))
  have hlin : ∀ r ∈ P.roots, (X - Polynomial.C r) = Polynomial.C (-r) * (1 - Polynomial.C r⁻¹ * X) := by
    intro r hr
    rw [mul_sub, mul_one, ← mul_assoc, ← Polynomial.C_mul, neg_mul, mul_inv_cancel₀ (hr0 r hr)]
    simp only [map_neg, map_one]
    ring
  rw [Multiset.map_congr rfl hlin, Multiset.prod_map_mul] at hfac
  set Qf := (P.roots.map fun r => (1 - Polynomial.C r⁻¹ * X)).prod with hQf
  set c := P.leadingCoeff * (P.roots.map fun r => -r).prod with hc
  have hCprod : (P.roots.map fun r => Polynomial.C (-r)).prod = Polynomial.C ((P.roots.map fun r => -r).prod) := by
    rw [map_multiset_prod, Multiset.map_map]; rfl
  rw [hCprod, ← mul_assoc, ← Polynomial.C_mul] at hfac
  -- `c = 1` from the value at `0`
  have hQ0 : Qf.eval 0 = 1 := by
    rw [hQf, eval_multiset_prod, Multiset.map_map]
    simp [Function.comp_def]
  have hc1 : c = 1 := by
    have := congrArg (eval 0) hfac
    rw [eval_mul, eval_C, hQ0, mul_one, hP0] at this
    exact this
  have h2 : Polynomial.C c * Qf = P := hfac
  rw [hc1, Polynomial.C_1, one_mul] at h2
  exact h2.symm

lemma coe_factor (R : Multiset ℂ) :
    (((R.map fun r => (1 - Polynomial.C r⁻¹ * X)).prod : ℂ[X]) : PowerSeries ℂ) = G (R.map fun r => r⁻¹) := by
  unfold G
  rw [← Polynomial.coeToPowerSeries.ringHom_apply, map_multiset_prod, Multiset.map_map, Multiset.map_map]
  congr 1
  refine Multiset.map_congr rfl fun r _ => ?_
  simp [Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_C, Polynomial.coe_X]

lemma hasSum_log_multiset {t : ℂ} : ∀ M : Multiset ℂ, (∀ ρ ∈ M, ‖ρ * t‖ < 1) →
    HasSum (fun k : ℕ => (M.map fun ρ => (ρ * t) ^ k / k).sum) (M.map fun ρ => -Complex.log (1 - ρ * t)).sum := by
  intro M
  induction M using Multiset.induction_on with
  | empty => intro _; simpa using hasSum_zero
  | cons ρ M ih =>
    intro h
    simp only [Multiset.map_cons, Multiset.sum_cons]
    exact (Complex.hasSum_taylorSeries_neg_log (h ρ (Multiset.mem_cons_self ρ M))).add
      (ih fun ρ' hρ' => h ρ' (Multiset.mem_cons_of_mem hρ'))

lemma log_norm_prod {t : ℂ} : ∀ M : Multiset ℂ, (∀ ρ ∈ M, 1 - ρ * t ≠ 0) →
    Real.log ‖(M.map fun ρ => 1 - ρ * t).prod‖ = (M.map fun ρ => Real.log ‖1 - ρ * t‖).sum := by
  intro M
  induction M using Multiset.induction_on with
  | empty => intro _; simp
  | cons ρ M ih =>
    intro h
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons, norm_mul]
    have h1 : ‖1 - ρ * t‖ ≠ 0 := norm_ne_zero_iff.2 (h ρ (Multiset.mem_cons_self ρ M))
    have h2 : ‖(M.map fun ρ => 1 - ρ * t).prod‖ ≠ 0 := by
      rw [norm_ne_zero_iff]
      refine Multiset.prod_ne_zero fun h0 => ?_
      obtain ⟨ρ', hρ', he⟩ := Multiset.mem_map.1 h0
      exact h ρ' (Multiset.mem_cons_of_mem hρ') he
    rw [Real.log_mul h1 h2, ih fun ρ' hρ' => h ρ' (Multiset.mem_cons_of_mem hρ')]

/-- **The logarithm as a series**: if `P(0) = 1`, `P` has no zero in the open unit disc, and
`X·P' = -(Σ_kkb_kX^k)·P` with `b_0 = 0`, then `Σ_kb_kt^k = -log|P(t)|` for `t ∈ [0, 1)`. -/
theorem log_series (P : ℂ[X]) (hP0 : P.eval 0 = 1) (hroots : ∀ s : ℂ, ‖s‖ < 1 → P.eval s ≠ 0)
    (b : ℕ → ℝ) (hb0 : b 0 = 0)
    (hrec : PowerSeries.X * (PowerSeries.derivative (R := ℂ)) (P : PowerSeries ℂ) =
      -((PowerSeries.mk fun k => ((k : ℂ) * (b k : ℂ))) * (P : PowerSeries ℂ)))
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    HasSum (fun k => b k * t ^ k) (-Real.log ‖P.eval (t : ℂ)‖) := by
  have hP : P ≠ 0 := fun h => by rw [h, eval_zero] at hP0; exact zero_ne_one hP0
  set R := P.roots with hR
  set M := R.map fun r => r⁻¹ with hM
  have hfac := factor_of_eval_zero P hP0
  have hG : (P : PowerSeries ℂ) = G M := by
    conv_lhs => rw [hfac]
    exact coe_factor R
  rw [hG] at hrec
  have hT := eq_S_of_deriv M _ hrec
  -- `kb_k = Σ_ρρ^k`
  have hcoef : ∀ k : ℕ, 1 ≤ k → ((k : ℂ) * b k) = (M.map fun ρ => ρ ^ k).sum := by
    intro k hk
    have := congrArg (PowerSeries.coeff k) hT
    rw [PowerSeries.coeff_mk, coeff_S, if_neg (by omega)] at this
    exact this
  -- `|ρ| ≤ 1`, hence `|ρt| < 1`
  have hρ : ∀ ρ ∈ M, ‖ρ‖ ≤ 1 := by
    intro ρ hρ
    obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.1 hρ
    have hr1 : 1 ≤ ‖r‖ := by
      by_contra h
      push_neg at h
      exact hroots r h ((mem_roots hP).1 hr)
    rw [norm_inv]
    exact inv_le_one_of_one_le₀ hr1
  have hlt : ∀ ρ ∈ M, ‖ρ * (t : ℂ)‖ < 1 := fun ρ hρ' => by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht0]
    calc ‖ρ‖ * t ≤ 1 * t := mul_le_mul_of_nonneg_right (hρ ρ hρ') ht0
      _ < 1 := by linarith
  -- the terms
  have hterm : ∀ k : ℕ, (M.map fun ρ => (ρ * (t : ℂ)) ^ k / k).sum = ((b k * t ^ k : ℝ) : ℂ) := by
    intro k
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [hb0]
    · have hk0 : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
      have e : (M.map fun ρ => (ρ * (t : ℂ)) ^ k / k).sum = (M.map fun ρ => ρ ^ k).sum * ((t : ℂ) ^ k / k) := by
        rw [← Multiset.sum_map_mul_right]
        exact congrArg Multiset.sum (Multiset.map_congr rfl fun ρ _ => by rw [mul_pow]; ring)
      rw [e, ← hcoef k hk]
      push_cast
      field_simp
  have hsum := hasSum_log_multiset M hlt
  simp only [hterm] at hsum
  have hre := (Complex.reCLM.hasSum hsum)
  simp only [Complex.reCLM_apply, Complex.ofReal_re] at hre
  convert hre using 1
  -- the real part of the logarithms
  have heval : P.eval (t : ℂ) = (M.map fun ρ => 1 - ρ * (t : ℂ)).prod := by
    conv_lhs => rw [hfac]
    rw [eval_multiset_prod, Multiset.map_map, hM, Multiset.map_map]
    congr 1
    refine Multiset.map_congr rfl fun r _ => ?_
    simp only [Function.comp_apply, eval_sub, eval_one, eval_mul, eval_C, eval_X]
  have hne : ∀ ρ ∈ M, 1 - ρ * (t : ℂ) ≠ 0 := fun ρ hρ' h => by
    have := hlt ρ hρ'
    rw [show ρ * (t : ℂ) = 1 from (sub_eq_zero.1 h).symm, norm_one] at this
    exact lt_irrefl _ this
  have hre_sum : ∀ M' : Multiset ℂ, ((M'.map fun ρ => -Complex.log (1 - ρ * (t : ℂ))).sum).re =
      -(M'.map fun ρ => Real.log ‖1 - ρ * (t : ℂ)‖).sum := by
    intro M'
    induction M' using Multiset.induction_on with
    | empty => simp
    | cons ρ M' ih =>
      simp only [Multiset.map_cons, Multiset.sum_cons, Complex.add_re, Complex.neg_re, Complex.log_re, ih]
      ring
  rw [heval, log_norm_prod M hne, hre_sum]

end Newton
end CoreLean

end
