/-
The complex logarithm of a polynomial without zeros in the closed unit disc, for `thm:polymer-logarithm` of
BALABAN_CORE.tex (`733037410da1`). If `P ∈ ℂ[X]` has `P(0) = 1`, no zero in the closed unit disc, and
`X·P' = (Σ_kkc_kX^k)·P` in `ℂ⟦X⟧` with `c_0 = 0`, then with `ρ` running over the inverses of the roots (`|ρ| < 1`) the
function `L(t) = Σ_ρlog(1 - ρt)` is continuous on the closed unit disc, `e^{L(t)} = P(t)`, `L(0) = 0`, and
`Σ_kc_kt^k = L(t)` for `|t| ≤ 1`.
-/
import CoreLean.ClusterLog

open Polynomial

noncomputable section

namespace CoreLean
namespace Newton

/-- `L(t) = Σ_{ρ ∈ M}log(1 - ρt)`. -/
def logSum (M : Multiset ℂ) (t : ℂ) : ℂ := (M.map fun ρ => Complex.log (1 - ρ * t)).sum

lemma exp_logSum (M : Multiset ℂ) (t : ℂ) (h : ∀ ρ ∈ M, 1 - ρ * t ≠ 0) :
    Complex.exp (logSum M t) = (M.map fun ρ => 1 - ρ * t).prod := by
  unfold logSum
  rw [Complex.exp_multiset_sum, Multiset.map_map]
  congr 1
  exact Multiset.map_congr rfl fun ρ hρ => Complex.exp_log (h ρ hρ)

lemma logSum_zero (M : Multiset ℂ) : logSum M 0 = 0 := by
  unfold logSum
  simp only [mul_zero, sub_zero, Complex.log_one, Multiset.map_const', Multiset.sum_replicate, smul_zero]

lemma continuousOn_logSum (M : Multiset ℂ) (S : Set ℂ) (h : ∀ ρ ∈ M, ∀ t ∈ S, ‖ρ * t‖ < 1) :
    ContinuousOn (logSum M) S := by
  induction M using Multiset.induction_on with
  | empty =>
    have e : logSum 0 = fun _ => 0 := by funext t; simp [logSum]
    rw [e]; exact continuousOn_const
  | cons ρ M ih =>
    have e : logSum (ρ ::ₘ M) = fun t => Complex.log (1 - ρ * t) + logSum M t := by
      funext t; simp [logSum]
    rw [e]
    refine ContinuousOn.add ?_ (ih fun ρ' hρ' => h ρ' (Multiset.mem_cons_of_mem hρ'))
    intro t ht
    refine ContinuousAt.continuousWithinAt ?_
    refine ContinuousAt.clog (by fun_prop) ?_
    rw [Complex.mem_slitPlane_iff]
    left
    have h1 := h ρ (Multiset.mem_cons_self ρ M) t ht
    have h2 : |(ρ * t).re| < 1 := lt_of_le_of_lt (Complex.abs_re_le_norm _) h1
    rw [Complex.sub_re, Complex.one_re]
    linarith [(abs_lt.1 h2).2]

/-- **The complex logarithm as a series**. -/
theorem log_series_complex (P : ℂ[X]) (hP0 : P.eval 0 = 1) (hroots : ∀ s : ℂ, ‖s‖ ≤ 1 → P.eval s ≠ 0)
    (c : ℕ → ℂ) (hc0 : c 0 = 0)
    (hrec : PowerSeries.X * (PowerSeries.derivative (R := ℂ)) (P : PowerSeries ℂ) =
      (PowerSeries.mk fun k => (k : ℂ) * c k) * (P : PowerSeries ℂ)) :
    ∃ L : ℂ → ℂ, ContinuousOn L (Metric.closedBall 0 1) ∧ L 0 = 0 ∧
      (∀ t : ℂ, ‖t‖ ≤ 1 → Complex.exp (L t) = P.eval t) ∧
      ∀ t : ℂ, ‖t‖ ≤ 1 → HasSum (fun k => c k * t ^ k) (L t) := by
  have hP : P ≠ 0 := fun h => by rw [h, eval_zero] at hP0; exact zero_ne_one hP0
  set R := P.roots with hR
  set M := R.map fun r => r⁻¹ with hM
  have hfac := factor_of_eval_zero P hP0
  have hG : (P : PowerSeries ℂ) = G M := by
    conv_lhs => rw [hfac]
    exact coe_factor R
  rw [hG] at hrec
  have hrec' : PowerSeries.X * (PowerSeries.derivative (R := ℂ)) (G M) =
      -((-(PowerSeries.mk fun k => (k : ℂ) * c k)) * G M) := by rw [hrec]; ring
  have hT := eq_S_of_deriv M _ hrec'
  -- `-kc_k = Σ_ρρ^k`
  have hcoef : ∀ k : ℕ, 1 ≤ k → -((k : ℂ) * c k) = (M.map fun ρ => ρ ^ k).sum := by
    intro k hk
    have := congrArg (PowerSeries.coeff k) hT
    rw [map_neg, PowerSeries.coeff_mk, coeff_S, if_neg (by omega)] at this
    exact this
  -- `|ρ| < 1`
  have hρ : ∀ ρ ∈ M, ‖ρ‖ < 1 := by
    intro ρ hρ
    obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.1 hρ
    have hr1 : 1 < ‖r‖ := by
      by_contra h
      push_neg at h
      exact hroots r h ((mem_roots hP).1 hr)
    rw [norm_inv]
    exact inv_lt_one_of_one_lt₀ hr1
  have hlt : ∀ ρ ∈ M, ∀ t ∈ Metric.closedBall (0 : ℂ) 1, ‖ρ * t‖ < 1 := fun ρ hρ' t ht => by
    rw [Metric.mem_closedBall, dist_zero_right] at ht
    rw [norm_mul]
    calc ‖ρ‖ * ‖t‖ ≤ ‖ρ‖ * 1 := mul_le_mul_of_nonneg_left ht (norm_nonneg _)
      _ < 1 := by rw [mul_one]; exact hρ ρ hρ'
  have hne : ∀ t ∈ Metric.closedBall (0 : ℂ) 1, ∀ ρ ∈ M, 1 - ρ * t ≠ 0 := fun t ht ρ hρ' h => by
    have := hlt ρ hρ' t ht
    rw [show ρ * t = 1 from (sub_eq_zero.1 h).symm, norm_one] at this
    exact lt_irrefl _ this
  have heval : ∀ t : ℂ, P.eval t = (M.map fun ρ => 1 - ρ * t).prod := by
    intro t
    conv_lhs => rw [hfac]
    rw [eval_multiset_prod, Multiset.map_map, hM, Multiset.map_map]
    congr 1
    refine Multiset.map_congr rfl fun r _ => ?_
    simp only [Function.comp_apply, eval_sub, eval_one, eval_mul, eval_C, eval_X]
  refine ⟨logSum M, continuousOn_logSum M _ hlt, logSum_zero M, fun t ht => ?_, fun t ht => ?_⟩
  · have ht' : t ∈ Metric.closedBall (0 : ℂ) 1 := by rwa [Metric.mem_closedBall, dist_zero_right]
    rw [exp_logSum M t (hne t ht'), heval]
  · have ht' : t ∈ Metric.closedBall (0 : ℂ) 1 := by rwa [Metric.mem_closedBall, dist_zero_right]
    have hsum := hasSum_log_multiset M fun ρ hρ' => hlt ρ hρ' t ht'
    have hterm : ∀ k : ℕ, (M.map fun ρ => (ρ * t) ^ k / k).sum = -(c k * t ^ k) := by
      intro k
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp [hc0]
      · have hk0 : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
        have e : (M.map fun ρ => (ρ * t) ^ k / k).sum = (M.map fun ρ => ρ ^ k).sum * (t ^ k / k) := by
          rw [← Multiset.sum_map_mul_right]
          exact congrArg Multiset.sum (Multiset.map_congr rfl fun ρ _ => by rw [mul_pow]; ring)
        rw [e, ← hcoef k hk]
        field_simp
    simp only [hterm] at hsum
    have hneg := hsum.neg
    simp only [neg_neg] at hneg
    convert hneg using 1
    unfold logSum
    rw [show (M.map fun ρ => -Complex.log (1 - ρ * t)) = (M.map fun ρ => Complex.log (1 - ρ * t)).map Neg.neg from
      (Multiset.map_map Neg.neg _ M).symm, Multiset.sum_map_neg', neg_neg]

end Newton
end CoreLean

end
