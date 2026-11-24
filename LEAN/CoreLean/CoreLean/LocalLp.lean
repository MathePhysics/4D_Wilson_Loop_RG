/-
`lem:local-laplacian`(i) of BALABAN_CORE.tex (`0580551bf179`): the norms `‖f‖_{p,Q_s} = (Σ_{z ∈ Q_s}ε⁴‖f(z)‖^p)^{1/p}` on
the finite sets `QF s`.

* `pn`: the weighted `L^p` norm of a function `f ≥ 0`; `pn_add` (Minkowski), `pn_mono`, `pn_smul`, `pn_sum4`, `pn_subset`,
  `pn_supp`.
* `pn_Sst`: `‖S_*‖_{p,Q_{r+2/3}} ≤ 81^{1/p}‖u‖_{p,Q_{r+1}} ≤ 9‖u‖_{p,Q_{r+1}}` for `p ≥ 2` (`E` has `81` elements).
* `card_QF_le`, `pn_le_vol`: `Q_s` has at most `(2s/ε + 1)⁴` points, so `‖f‖_{p,Q_s} ≤ (2s + 1)^{4/p}‖f‖_{∞,Q_s}`.
-/
import CoreLean.LocalConvolution
import CoreLean.LocalSecond

open Finset

noncomputable section

namespace CoreLean
namespace LocalLaplacian

variable {ε : ℝ} {n₀ : Fin 4 → ℤ}

/-- `‖f‖_{p,T} = (Σ_{n ∈ T}ε⁴f(n)^p)^{1/p}`. -/
def pn (ε : ℝ) (T : Finset (Fin 4 → ℤ)) (p : ℝ) (f : (Fin 4 → ℤ) → ℝ) : ℝ := (∑ n ∈ T, ε ^ 4 * f n ^ p) ^ (1 / p)

variable {T : Finset (Fin 4 → ℤ)} {p : ℝ}

lemma pn_nonneg {f : (Fin 4 → ℤ) → ℝ} (hf : ∀ n ∈ T, 0 ≤ f n) : 0 ≤ pn ε T p f :=
  Real.rpow_nonneg (sum_nonneg fun n hn => mul_nonneg (by positivity) (Real.rpow_nonneg (hf n hn) _)) _

lemma pn_eq (hε : 0 < ε) (hp : 0 < p) {f : (Fin 4 → ℤ) → ℝ} (hf : ∀ n ∈ T, 0 ≤ f n) :
    pn ε T p f = (∑ n ∈ T, (ε ^ (4 / p) * f n) ^ p) ^ (1 / p) := by
  unfold pn
  congr 1
  refine sum_congr rfl fun n hn => ?_
  rw [Real.mul_rpow (Real.rpow_nonneg hε.le _) (hf n hn), ← Real.rpow_mul hε.le, div_mul_cancel₀ _ hp.ne']
  norm_cast

lemma pn_add (hε : 0 < ε) (hp : 1 ≤ p) {f g : (Fin 4 → ℤ) → ℝ} (hf : ∀ n ∈ T, 0 ≤ f n) (hg : ∀ n ∈ T, 0 ≤ g n) :
    pn ε T p (fun n => f n + g n) ≤ pn ε T p f + pn ε T p g := by
  have hp0 : 0 < p := by linarith
  rw [pn_eq hε hp0 hf, pn_eq hε hp0 hg, pn_eq hε hp0 fun n hn => add_nonneg (hf n hn) (hg n hn)]
  have h := Real.Lp_add_le_of_nonneg (s := T) (f := fun n => ε ^ (4 / p) * f n) (g := fun n => ε ^ (4 / p) * g n) hp
    (fun n hn => mul_nonneg (Real.rpow_nonneg hε.le _) (hf n hn))
    (fun n hn => mul_nonneg (Real.rpow_nonneg hε.le _) (hg n hn))
  simpa only [mul_add] using h

lemma pn_mono (hp : 0 < p) {f g : (Fin 4 → ℤ) → ℝ} (hf : ∀ n ∈ T, 0 ≤ f n) (hfg : ∀ n ∈ T, f n ≤ g n) :
    pn ε T p f ≤ pn ε T p g :=
  Real.rpow_le_rpow (sum_nonneg fun n hn => mul_nonneg (by positivity) (Real.rpow_nonneg (hf n hn) _))
    (sum_le_sum fun n hn => mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (hf n hn) (hfg n hn) hp.le) (by positivity))
    (by positivity)

lemma pn_smul (hp : 0 < p) {c : ℝ} (hc : 0 ≤ c) {f : (Fin 4 → ℤ) → ℝ} (hf : ∀ n ∈ T, 0 ≤ f n) :
    pn ε T p (fun n => c * f n) = c * pn ε T p f := by
  unfold pn
  rw [show ∑ n ∈ T, ε ^ 4 * (c * f n) ^ p = c ^ p * ∑ n ∈ T, ε ^ 4 * f n ^ p by
      rw [mul_sum]; exact sum_congr rfl fun n hn => by rw [Real.mul_rpow hc (hf n hn)]; ring,
    Real.mul_rpow (Real.rpow_nonneg hc _) (sum_nonneg fun n hn => mul_nonneg (by positivity)
      (Real.rpow_nonneg (hf n hn) _)), ← Real.rpow_mul hc, mul_one_div_cancel hp.ne', Real.rpow_one]

lemma pn_sum4 (hε : 0 < ε) (hp : 1 ≤ p) (f : Fin 4 → (Fin 4 → ℤ) → ℝ) (hf : ∀ μ, ∀ n ∈ T, 0 ≤ f μ n) :
    pn ε T p (fun n => ∑ μ, f μ n) ≤ ∑ μ, pn ε T p (f μ) := by
  simp only [Fin.sum_univ_four]
  have h01 : ∀ n ∈ T, 0 ≤ f 0 n + f 1 n := fun n hn => add_nonneg (hf 0 n hn) (hf 1 n hn)
  have h012 : ∀ n ∈ T, 0 ≤ f 0 n + f 1 n + f 2 n := fun n hn => add_nonneg (h01 n hn) (hf 2 n hn)
  refine (pn_add hε hp h012 (hf 3)).trans (add_le_add ((pn_add hε hp h01 (hf 2)).trans
    (add_le_add (pn_add hε hp (hf 0) (hf 1)) le_rfl)) le_rfl)

lemma pn_subset (hp : 0 < p) {T' : Finset (Fin 4 → ℤ)} (h : T ⊆ T') {f : (Fin 4 → ℤ) → ℝ}
    (hf : ∀ n ∈ T', 0 ≤ f n) : pn ε T p f ≤ pn ε T' p f :=
  Real.rpow_le_rpow (sum_nonneg fun n hn => mul_nonneg (by positivity) (Real.rpow_nonneg (hf n (h hn)) _))
    (sum_le_sum_of_subset_of_nonneg h fun n hn _ => mul_nonneg (by positivity) (Real.rpow_nonneg (hf n hn) _))
    (by positivity)

lemma pn_supp (hp : 0 < p) {T' : Finset (Fin 4 → ℤ)} (h : T' ⊆ T) {f : (Fin 4 → ℤ) → ℝ}
    (hf : ∀ n ∈ T, n ∉ T' → f n = 0) : pn ε T p f = pn ε T' p f := by
  unfold pn
  rw [sum_subset h fun n hn hn' => by rw [hf n hn hn', Real.zero_rpow hp.ne', mul_zero]]

/-! ### Counting -/

lemma rpow81_le (hp : 2 ≤ p) : (81 : ℝ) ^ (1 / p) ≤ 9 := by
  have hp0 : 0 < p := by linarith
  calc (81 : ℝ) ^ (1 / p) ≤ 81 ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by rw [div_le_div_iff₀ hp0 (by norm_num)]; linarith)
    _ = 9 := by rw [← Real.sqrt_eq_rpow, show (81 : ℝ) = 9 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

lemma Sst_rpow_le (u : (Fin 4 → ℤ) → V) (n : Fin 4 → ℤ) (hp : 0 ≤ p) :
    Sst u n ^ p ≤ ∑ e ∈ Eoff, ‖u (n + e)‖ ^ p := by
  obtain ⟨e, he, heq⟩ := exists_mem_eq_sup' Eoff_nonempty (fun e => ‖u (n + e)‖)
  have : Sst u n = ‖u (n + e)‖ := heq
  rw [this]
  exact single_le_sum (f := fun e => ‖u (n + e)‖ ^ p) (fun e _ => Real.rpow_nonneg (norm_nonneg _) _) he

/-- `‖S_*‖_{p,Q_{r+2/3}} ≤ 9‖u‖_{p,Q_{r+1}}`. -/
theorem pn_Sst (hε : 0 < ε) (hε3 : ε ≤ 1 / 3) (hp : 2 ≤ p) {r : ℝ} (u : (Fin 4 → ℤ) → V) :
    pn ε (QF ε n₀ (r + 2 / 3)) p (Sst u) ≤ 9 * pn ε (QF ε n₀ (r + 1)) p (fun n => ‖u n‖) := by
  have hp0 : 0 < p := by linarith
  have he4 : 0 ≤ ε ^ 4 := by positivity
  have hS : ∑ n ∈ QF ε n₀ (r + 2 / 3), ε ^ 4 * Sst u n ^ p ≤ 81 * ∑ m ∈ QF ε n₀ (r + 1), ε ^ 4 * ‖u m‖ ^ p := by
    calc ∑ n ∈ QF ε n₀ (r + 2 / 3), ε ^ 4 * Sst u n ^ p
        ≤ ∑ n ∈ QF ε n₀ (r + 2 / 3), ∑ e ∈ Eoff, ε ^ 4 * ‖u (n + e)‖ ^ p := sum_le_sum fun n _ => by
          rw [← mul_sum]; exact mul_le_mul_of_nonneg_left (Sst_rpow_le u n hp0.le) he4
      _ = ∑ e ∈ Eoff, ∑ n ∈ QF ε n₀ (r + 2 / 3), ε ^ 4 * ‖u (n + e)‖ ^ p := sum_comm
      _ ≤ ∑ _e ∈ Eoff, ∑ m ∈ QF ε n₀ (r + 1), ε ^ 4 * ‖u m‖ ^ p := sum_le_sum fun e he => by
          have := count_shift hε hε3 (n₀ := n₀) (F := fun m => ε ^ 4 * ‖u m‖ ^ p)
            (fun m => mul_nonneg he4 (Real.rpow_nonneg (norm_nonneg _) _)) he (r + 2 / 3)
          rwa [show r + 2 / 3 + 1 / 3 = r + 1 by ring] at this
      _ = 81 * ∑ m ∈ QF ε n₀ (r + 1), ε ^ 4 * ‖u m‖ ^ p := by rw [sum_const, card_Eoff, nsmul_eq_mul]; norm_num
  have hX := sum_nonneg fun m (_ : m ∈ QF ε n₀ (r + 1)) => mul_nonneg he4 (Real.rpow_nonneg (norm_nonneg (u m)) p)
  unfold pn
  calc (∑ n ∈ QF ε n₀ (r + 2 / 3), ε ^ 4 * Sst u n ^ p) ^ (1 / p)
      ≤ (81 * ∑ m ∈ QF ε n₀ (r + 1), ε ^ 4 * ‖u m‖ ^ p) ^ (1 / p) :=
        Real.rpow_le_rpow (sum_nonneg fun n _ => mul_nonneg he4 (Real.rpow_nonneg (Sst_nonneg u n) _)) hS
          (by positivity)
    _ = 81 ^ (1 / p) * (∑ m ∈ QF ε n₀ (r + 1), ε ^ 4 * ‖u m‖ ^ p) ^ (1 / p) := Real.mul_rpow (by norm_num) hX
    _ ≤ 9 * (∑ m ∈ QF ε n₀ (r + 1), ε ^ 4 * ‖u m‖ ^ p) ^ (1 / p) :=
        mul_le_mul_of_nonneg_right (rpow81_le hp) (Real.rpow_nonneg hX _)

/-! ### The volume -/

omit [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] in
lemma card_QF_le (hε : 0 < ε) (hε1 : ε ≤ 1) {s : ℝ} (hs : 0 ≤ s) :
    ε ^ 4 * ((QF ε n₀ s).card : ℝ) ≤ (2 * s + 1) ^ 4 := by
  set K := ⌊s / ε⌋₊
  have hsub : QF ε n₀ s ⊆ Fintype.piFinset fun μ => Icc (n₀ μ - K) (n₀ μ + K) := fun n hn => by
    have h := (mem_QF hε).1 hn
    refine Fintype.mem_piFinset.2 fun μ => ?_
    have h1 := h μ
    unfold tc at h1
    rw [abs_mul, abs_of_pos hε] at h1
    have h2 : ((n μ - n₀ μ).natAbs : ℝ) ≤ s / ε := by
      rw [le_div_iff₀ hε, Nat.cast_natAbs, Int.cast_abs]; linarith
    have h3 : (n μ - n₀ μ).natAbs ≤ K := Nat.le_floor h2
    have h4 : |n μ - n₀ μ| ≤ (K : ℤ) := by rw [Int.abs_eq_natAbs]; exact_mod_cast h3
    rw [mem_Icc]; constructor <;> linarith [abs_le.1 h4]
  have hcard : ((Fintype.piFinset fun μ : Fin 4 => Icc (n₀ μ - K) (n₀ μ + K)).card : ℝ) = (2 * K + 1) ^ 4 := by
    have e : ∀ μ : Fin 4, (n₀ μ + (K : ℤ) + 1 - (n₀ μ - K)).toNat = 2 * K + 1 := fun μ => by omega
    rw [Fintype.card_piFinset]
    simp only [Int.card_Icc, e, prod_const, card_univ, Fintype.card_fin]
    push_cast; ring
  have hKe : (K : ℝ) * ε ≤ s := by
    have := Nat.floor_le (div_nonneg hs hε.le)
    rwa [le_div_iff₀ hε] at this
  calc ε ^ 4 * ((QF ε n₀ s).card : ℝ) ≤ ε ^ 4 * (2 * K + 1) ^ 4 := by
        rw [← hcard]; exact mul_le_mul_of_nonneg_left (by exact_mod_cast card_le_card hsub) (by positivity)
    _ = (2 * (K * ε) + ε) ^ 4 := by ring
    _ ≤ (2 * s + 1) ^ 4 := pow_le_pow_left₀ (by positivity) (by linarith) 4

omit [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] in
/-- `‖f‖_{p,Q_s} ≤ (2s + 1)^{4/p}‖f‖_{∞,Q_s}`. -/
theorem pn_le_vol (hε : 0 < ε) (hε1 : ε ≤ 1) {s : ℝ} (hs : 0 ≤ s) (hp : 0 < p) {f : (Fin 4 → ℤ) → ℝ} {M : ℝ}
    (hf0 : ∀ n ∈ QF ε n₀ s, 0 ≤ f n) (hM : ∀ n ∈ QF ε n₀ s, f n ≤ M) :
    pn ε (QF ε n₀ s) p f ≤ (2 * s + 1) ^ (4 / p) * M := by
  have hM0 : 0 ≤ M := by
    have : n₀ ∈ QF ε n₀ s := (mem_QF hε).2 fun μ => by simp [tc, hs]
    exact (hf0 _ this).trans (hM _ this)
  unfold pn
  calc (∑ n ∈ QF ε n₀ s, ε ^ 4 * f n ^ p) ^ (1 / p) ≤ (ε ^ 4 * ((QF ε n₀ s).card : ℝ) * M ^ p) ^ (1 / p) := by
        refine Real.rpow_le_rpow (sum_nonneg fun n hn => mul_nonneg (by positivity) (Real.rpow_nonneg (hf0 n hn) _))
          ?_ (by positivity)
        calc ∑ n ∈ QF ε n₀ s, ε ^ 4 * f n ^ p ≤ ∑ _n ∈ QF ε n₀ s, ε ^ 4 * M ^ p :=
              sum_le_sum fun n hn => mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (hf0 n hn) (hM n hn) hp.le)
                (by positivity)
          _ = _ := by rw [sum_const, nsmul_eq_mul]; ring
    _ ≤ ((2 * s + 1) ^ 4 * M ^ p) ^ (1 / p) :=
        Real.rpow_le_rpow (by positivity) (mul_le_mul_of_nonneg_right (card_QF_le hε hε1 hs)
          (Real.rpow_nonneg hM0 _)) (by positivity)
    _ = (2 * s + 1) ^ (4 / p) * M := by
        rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg hM0 _), ← Real.rpow_mul hM0, mul_one_div_cancel hp.ne',
          Real.rpow_one, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
          show ((4 : ℕ) : ℝ) * (1 / p) = 4 / p by push_cast; ring]

end LocalLaplacian
end CoreLean

end
