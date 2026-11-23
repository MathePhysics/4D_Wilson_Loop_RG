/-
The assembly of the cluster expansion for `eq:cluster-sum` of `lem:cluster-bounds` of BALABAN_CORE.tex (`5bbe1bc62521`),
stage 1: the two forms of the Ursell function, its sign, and the elementary properties of `E_n`.
-/
import CoreLean.ClusterSequences
import CoreLean.ClusterLog

open Finset

noncomputable section

namespace CoreLean
namespace TreeGraph

open Classical

variable {Q : Type*} [Fintype Q] {inc : Q → Q → Prop}

lemma pairsIn_univ_eq_offdiag (k : ℕ) : pairsIn (Finset.univ : Finset (Fin k)) = offdiag k := by
  ext e
  rw [mem_pairsIn']
  simp [offdiag]

/-- The two forms of `ρ^T` agree. -/
lemma ursS_eq_ursell {k : ℕ} (Z : Fin k → Q) : ursS inc Z = ursell inc Z := by
  unfold ursS ursell
  rw [pairsIn_univ_eq_offdiag]
  refine Finset.sum_congr rfl fun g hg => Finset.prod_congr rfl fun e he => ?_
  have heo : e ∈ offdiag k := Finset.mem_powerset.1 (Finset.mem_filter.1 hg).1 he
  unfold fp incG
  by_cases h : ∃ i j, e = s(i, j) ∧ inc (Z i) (Z j)
  · rw [if_pos h, if_pos (Finset.mem_filter.2 ⟨heo, h⟩)]
  · rw [if_neg h, if_neg]
    intro h'
    exact h (Finset.mem_filter.1 h').2

/-- **The sign**: `(-1)^{k-1}ρ^T = |ρ^T|` for `k ≥ 1`. -/
lemma sign_ursS {k : ℕ} (hk : 1 ≤ k) (Z : Fin k → Q) : (-1) ^ (k - 1) * ursS inc Z = |ursS inc Z| := by
  have h := (ursell_bound inc hk Z).2
  rw [← ursS_eq_ursell] at h
  rcases neg_one_pow_eq_or ℤ (k - 1) with h1 | h1
  · rw [h1, one_mul] at h ⊢; exact (abs_of_nonneg h).symm
  · rw [h1, neg_one_mul] at h ⊢; exact (abs_of_nonpos (by linarith)).symm

variable {R : Type*} [CommRing R]

lemma En_zero (w : Q → R) : En (inc := inc) w 0 = 1 := by
  unfold En Ei zetaS
  simp [pairsIn]

lemma En_homog (c : R) (w : Q → R) (n : ℕ) :
    En (inc := inc) (fun q => c * w q) n = c ^ n * En (inc := inc) w n := by
  unfold En Ei
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun Z _ => ?_
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  ring

lemma En_large (hrefl : ∀ a, inc a a) (hsymm : ∀ a b, inc a b → inc b a) (w : Q → R) {n : ℕ}
    (hn : Fintype.card Q < n) : En (inc := inc) w n = 0 := by
  rw [En_eq_sets hrefl hsymm]
  rw [Finset.filter_eq_empty_iff.2 fun S _ h => by
    have := Finset.card_le_univ S
    omega]
  simp

/-! ### The polynomial `P(s) = Ξ(-sw)` -/

/-- The complex weights. -/
def wc (w : Q → ℝ) : Q → ℂ := fun q => (w q : ℂ)

/-- `g_n = (-1)^nE_n/n!`, the coefficients of `Ξ(-sw)`. -/
def gC (inc : Q → Q → Prop) (w : Q → ℝ) (n : ℕ) : ℂ := (-1) ^ n * En (inc := inc) (wc w) n / (n.factorial : ℂ)

/-- `P(s) = Ξ(-sw) = Σ_ng_ns^n`. -/
def Pw (inc : Q → Q → Prop) (w : Q → ℝ) : Polynomial ℂ :=
  ∑ n ∈ Finset.range (Fintype.card Q + 1), Polynomial.C (gC inc w n) * Polynomial.X ^ n

/-- `b_k = (-1)^{k-1}C_k/k! = (1/k!)Σ_Z|ρ^T(Z)|Π_iw(Z_i)`, `b_0 = 0`. -/
def bR (inc : Q → Q → Prop) (w : Q → ℝ) (k : ℕ) : ℝ :=
  if k = 0 then 0 else (-1) ^ (k - 1) * Ck (inc := inc) w k / (k.factorial : ℝ)

lemma Ck_cast (w : Q → ℝ) (k : ℕ) : ((Ck (inc := inc) w k : ℝ) : ℂ) = Ck (inc := inc) (wc w) k := by
  unfold Ck Ci wc; push_cast; rfl

lemma coeff_Pw (hrefl : ∀ a, inc a a) (hsymm : ∀ a b, inc a b → inc b a) (w : Q → ℝ) (n : ℕ) :
    PowerSeries.coeff n (Pw inc w : PowerSeries ℂ) = gC inc w n := by
  rw [Polynomial.coeff_coe, Pw, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · rw [gC, En_large hrefl hsymm _ (by simp only [Finset.mem_range] at h; omega)]; simp

lemma eval_Pw (hrefl : ∀ a, inc a a) (hsymm : ∀ a b, inc a b → inc b a) (w : Q → ℝ) (s : ℂ) :
    (Pw inc w).eval s = Cluster.Xi inc Finset.univ (fun q => -s * wc w q) := by
  rw [Xi_eq_sequences hrefl hsymm, Pw, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, En_homog, gC]
  field_simp
  rw [neg_pow]
  ring

lemma Pw_zero (hrefl : ∀ a, inc a a) (hsymm : ∀ a b, inc a b → inc b a) (w : Q → ℝ) :
    (Pw inc w).eval 0 = 1 := by
  rw [Pw, Polynomial.eval_finsetSum, Finset.sum_eq_single 0]
  · simp [gC, En_zero]
  · intro m _ hm; simp [hm]
  · intro h; simp at h

/-- **No zero in the unit disc**, by the criterion of Kotecký and Preiss. -/
lemma Pw_ne_zero (hrefl : ∀ a, inc a a) (hsymm : ∀ a b, inc a b → inc b a) (w a : Q → ℝ) (hw : ∀ q, 0 ≤ w q)
    (hKP : Cluster.KP inc Finset.univ w a) {s : ℂ} (hs : ‖s‖ < 1) : (Pw inc w).eval s ≠ 0 := by
  rw [eval_Pw hrefl hsymm]
  refine (Cluster.dobrushin inc hrefl hsymm Finset.univ w a hw hKP _ (fun q _ => ?_) _ Finset.univ
    (Finset.Subset.refl _) rfl).1
  rw [norm_mul, norm_neg, wc, Complex.norm_real, Real.norm_of_nonneg (hw q)]
  calc ‖s‖ * w q ≤ 1 * w q := mul_le_mul_of_nonneg_right hs.le (hw q)
    _ = w q := one_mul _

/-- One term of the recursion: `-(k+1)b_{k+1}g_{m-k} = (-1)^{m+1}C(m, k)C_{k+1}E_{m-k}/m!`. -/
lemma term_id (w : Q → ℝ) {m k : ℕ} (hk : k ≤ m) :
    -(((k + 1 : ℕ) : ℂ) * (bR inc w (k + 1) : ℂ) * gC inc w (m - k)) =
      (-1) ^ (m + 1) * (m.choose k : ℂ) * Ck (inc := inc) (wc w) (k + 1) * En (inc := inc) (wc w) (m - k) /
        (m.factorial : ℂ) := by
  have hch := Nat.choose_mul_factorial_mul_factorial hk
  have hf1 : ((k + 1).factorial : ℂ) = (k + 1 : ℂ) * (k.factorial : ℂ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have hmf : (m.factorial : ℂ) = (m.choose k : ℂ) * (k.factorial : ℂ) * ((m - k).factorial : ℂ) := by
    exact_mod_cast hch.symm
  have hsign : ((-1 : ℂ) ^ k) * (-1) ^ (m - k) = (-1) ^ m := by rw [← pow_add, Nat.add_sub_cancel' hk]
  unfold bR gC
  rw [if_neg (Nat.succ_ne_zero k), Nat.add_sub_cancel]
  push_cast
  rw [Ck_cast]
  have hk0 : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero k)
  have hmk0 : ((m - k).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  have hc0 : (m.choose k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.choose_pos hk).ne'
  have hk1 : (k + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  rw [hf1, hmf]
  field_simp
  rw [pow_succ, ← hsign]
  ring

/-- **The recursion in power series**: `X·P' = -(Σ_kkb_kX^k)·P`. -/
lemma Pw_rec (hrefl : ∀ a, inc a a) (hsymm : ∀ a b, inc a b → inc b a) (w : Q → ℝ) :
    PowerSeries.X * (PowerSeries.derivative (R := ℂ)) (Pw inc w : PowerSeries ℂ) =
      -((PowerSeries.mk fun k => (k : ℂ) * (bR inc w k : ℂ)) * (Pw inc w : PowerSeries ℂ)) := by
  ext n
  rw [map_neg]
  conv_rhs => rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => PowerSeries.coeff i (PowerSeries.mk fun k => (k : ℂ) * (bR inc w k : ℂ)) *
      PowerSeries.coeff j (Pw inc w : PowerSeries ℂ)) n]
  simp only [PowerSeries.coeff_mk, coeff_Pw hrefl hsymm]
  rcases n with _ | m
  · simp [PowerSeries.coeff_zero_X_mul]
  · rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative, coeff_Pw hrefl hsymm, Finset.sum_range_succ']
    simp only [Nat.cast_zero, zero_mul, add_zero]
    rw [← Finset.sum_neg_distrib]
    have hrec := En_rec hsymm (wc w) (m + 1) (by omega)
    simp only [Nat.add_sub_cancel] at hrec
    rw [Finset.sum_congr rfl (g := fun k => (-1) ^ (m + 1) * (m.choose k : ℂ) * Ck (inc := inc) (wc w) (k + 1) *
        En (inc := inc) (wc w) (m - k) / (m.factorial : ℂ)) fun k hk => by
      rw [show m + 1 - (k + 1) = m - k by omega]
      exact term_id w (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk))]
    have hsum : ∑ k ∈ Finset.range (m + 1), (-1) ^ (m + 1) * (m.choose k : ℂ) * Ck (inc := inc) (wc w) (k + 1) *
        En (inc := inc) (wc w) (m - k) / (m.factorial : ℂ) =
          (-1) ^ (m + 1) / (m.factorial : ℂ) * ∑ k ∈ Finset.range (m + 1),
            (m.choose k : ℂ) * Ck (inc := inc) (wc w) (k + 1) * En (inc := inc) (wc w) (m - k) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [hsum, ← hrec]
    unfold gC
    have hm0 : (m.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero m)
    rw [Nat.factorial_succ]
    push_cast
    field_simp

end TreeGraph
end CoreLean

end
