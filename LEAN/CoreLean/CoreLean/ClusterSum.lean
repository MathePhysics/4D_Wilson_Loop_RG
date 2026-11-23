/-
`eq:cluster-sum` of `lem:cluster-bounds` of BALABAN_CORE.tex (`5bbe1bc62521`): under `eq:kotecky-preiss` on a finite set
of polymers `Q` with weights `w = h̄e^{d} ≥ 0`, for every set `N` of polymers (those `≁ Z₀`),
`Σ_{m ≥ 1}(1/m!)Σ_{(Z_1, …, Z_m) : some Z_i ∈ N}|ρ^T(Z_1, …, Z_m)|Π_iw(Z_i) ≤ Σ_{Z ∈ N}w(Z)e^{a(Z)}`.
Proof: `b_k = (1/k!)Σ_Z|ρ^T|Πw` are the coefficients of `-log|Ξ(-tw)|` for `t ∈ [0, 1)` (`log_series`); with `w'` the
weights vanishing on `N`, `b_k(w) - b_k(w')` is the sum over the sequences meeting `N`, and
`-log|Ξ(-tw)| + log|Ξ(-tw')| ≤ Σ_{Z ∈ N}w(Z)e^{a(Z)}` by the ratio bounds of Dobrushin; let `t → 1`.
-/
import CoreLean.ClusterBound

open Finset

noncomputable section

namespace CoreLean
namespace TreeGraph

open Classical

variable {Q : Type*} [Fintype Q] {inc : Q → Q → Prop}

/-- The log identity for `t ∈ [0, 1)`. -/
lemma hasSum_bR (hrefl : ∀ a, inc a a) (hsymm : ∀ a b, inc a b → inc b a) (w a : Q → ℝ) (hw : ∀ q, 0 ≤ w q)
    (hKP : Cluster.KP inc Finset.univ w a) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    HasSum (fun k => bR inc w k * t ^ k)
      (-Real.log ‖Cluster.Xi inc Finset.univ (fun q => -(t : ℂ) * wc w q)‖) := by
  have h := Newton.log_series (Pw inc w) (Pw_zero hrefl hsymm w)
    (fun s hs => Pw_ne_zero hrefl hsymm w a hw hKP hs) (bR inc w) (by simp [bR]) (Pw_rec hrefl hsymm w) ht0 ht1
  rwa [eval_Pw hrefl hsymm] at h

/-- `b_k = (1/k!)Σ_Z|ρ^T(Z)|Π_iw(Z_i)` for `k ≥ 1`. -/
lemma bR_eq (w : Q → ℝ) {k : ℕ} (hk : 1 ≤ k) :
    bR inc w k = ((k.factorial : ℝ))⁻¹ * ∑ Z : Fin k → Q, (|ursS inc Z| : ℝ) * ∏ i, w (Z i) := by
  unfold bR Ck Ci
  rw [if_neg (by omega), div_eq_inv_mul, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun Z _ => ?_
  have hs := sign_ursS (inc := inc) hk Z
  have hs' : ((-1 : ℝ) ^ (k - 1)) * (ursS inc Z : ℝ) = (|ursS inc Z| : ℝ) := by exact_mod_cast hs
  rw [← hs']
  ring

/-- The polymer sum with the weights vanishing on `N` is the polymer sum on the complement. -/
lemma Xi_vanish (N : Finset Q) (z : Q → ℂ) :
    Cluster.Xi inc Finset.univ (fun q => if q ∈ N then 0 else z q) = Cluster.Xi inc (Finset.univ \ N) z := by
  unfold Cluster.Xi
  have hsub : ((Finset.univ \ N).powerset.filter (Cluster.Compat inc)) ⊆
      ((Finset.univ : Finset Q).powerset.filter (Cluster.Compat inc)) := by
    intro S hS
    simp only [Finset.mem_filter, Finset.mem_powerset] at hS ⊢
    exact ⟨Finset.subset_univ _, hS.2⟩
  symm
  rw [← Finset.sum_subset hsub]
  · refine Finset.sum_congr rfl fun S hS => Finset.prod_congr rfl fun q hq => ?_
    have := Finset.mem_powerset.1 (Finset.mem_filter.1 hS).1 hq
    simp only [if_neg (Finset.mem_sdiff.1 this).2]
  · intro S hS hnS
    have : ¬S ⊆ Finset.univ \ N := fun h => hnS (Finset.mem_filter.2
      ⟨Finset.mem_powerset.2 h, (Finset.mem_filter.1 hS).2⟩)
    obtain ⟨q, hq, hqN⟩ := Finset.not_subset.1 this
    have hqN' : q ∈ N := by simpa using hqN
    exact Finset.prod_eq_zero hq (if_pos hqN')

/-- **Telescoping the ratio bounds**: `|Ξ_{Λ₀∖A}| ≤ e^{Σ_Awe^a}|Ξ_{Λ₀}|`. -/
lemma Xi_sdiff_le (hrefl : ∀ a, inc a a) (hsymm : ∀ a b, inc a b → inc b a) (Λ0 : Finset Q) (w a : Q → ℝ)
    (hw : ∀ q, 0 ≤ w q) (hKP : Cluster.KP inc Λ0 w a) (z : Q → ℂ) (hz : ∀ q ∈ Λ0, ‖z q‖ ≤ w q) :
    ∀ A ⊆ Λ0, ‖Cluster.Xi inc (Λ0 \ A) z‖ ≤ Real.exp (∑ q ∈ A, w q * Real.exp (a q)) * ‖Cluster.Xi inc Λ0 z‖ := by
  intro A
  induction A using Finset.induction_on with
  | empty => intro _; simp
  | insert x A' hxA' ih =>
    intro hA
    have hA' : A' ⊆ Λ0 := (Finset.subset_insert x A').trans hA
    have hx : x ∈ Λ0 \ A' := Finset.mem_sdiff.2 ⟨hA (Finset.mem_insert_self x A'), hxA'⟩
    have hsub : Λ0 \ insert x A' = (Λ0 \ A').erase x := by
      ext y; simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]; tauto
    have hd := (Cluster.dobrushin inc hrefl hsymm Λ0 w a hw hKP z hz _ (Λ0 \ A') Finset.sdiff_subset rfl).2 x hx
    rw [hsub, Finset.sum_insert hxA', Real.exp_add, mul_assoc]
    exact hd.trans (mul_le_mul_of_nonneg_left (ih hA') (Real.exp_pos _).le)

/-- The difference of the coefficients is the sum over the sequences meeting `N`. -/
lemma bR_diff (w : Q → ℝ) (N : Finset Q) {k : ℕ} (hk : 1 ≤ k) :
    bR inc w k - bR inc (fun q => if q ∈ N then 0 else w q) k =
      ((k.factorial : ℝ))⁻¹ * ∑ Z : Fin k → Q,
        (if ∃ i, Z i ∈ N then (|ursS inc Z| : ℝ) * ∏ i, w (Z i) else 0) := by
  rw [bR_eq w hk, bR_eq _ hk, ← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun Z _ => ?_
  by_cases h : ∃ i, Z i ∈ N
  · obtain ⟨i, hi⟩ := h
    have h0 : ∏ j, (if Z j ∈ N then (0 : ℝ) else w (Z j)) = 0 :=
      Finset.prod_eq_zero (f := fun j => if Z j ∈ N then (0 : ℝ) else w (Z j)) (Finset.mem_univ i) (if_pos hi)
    rw [if_pos ⟨i, hi⟩, h0, mul_zero, sub_zero]
  · have h' : ∀ j, Z j ∉ N := fun j hj => h ⟨j, hj⟩
    rw [if_neg h]
    have : ∏ j, (if Z j ∈ N then (0 : ℝ) else w (Z j)) = ∏ j, w (Z j) :=
      Finset.prod_congr rfl fun j _ => if_neg (h' j)
    rw [this, sub_self]

/-- **`eq:cluster-sum`**: under `eq:kotecky-preiss` with the weights `w = h̄e^{d} ≥ 0`, for every set `N` of polymers
(those `≁ Z₀`) and every `K`, `Σ_{m ≤ K}(1/m!)Σ_{(Z_1, …, Z_m) meeting N}|ρ^T|Π_iw(Z_i) ≤ Σ_{Z ∈ N}w(Z)e^{a(Z)}`. -/
theorem cluster_sum (hrefl : ∀ a, inc a a) (hsymm : ∀ a b, inc a b → inc b a) (w a : Q → ℝ) (hw : ∀ q, 0 ≤ w q)
    (hKP : Cluster.KP inc Finset.univ w a) (N : Finset Q) (K : ℕ) :
    ∑ k ∈ Finset.range K, (((k + 1).factorial : ℝ))⁻¹ * ∑ Z : Fin (k + 1) → Q,
      (if ∃ i, Z i ∈ N then (|ursS inc Z| : ℝ) * ∏ i, w (Z i) else 0) ≤ ∑ q ∈ N, w q * Real.exp (a q) := by
  set w' : Q → ℝ := fun q => if q ∈ N then 0 else w q with hw'def
  have hw' : ∀ q, 0 ≤ w' q := fun q => by simp only [hw'def]; split_ifs; exact le_rfl; exact hw q
  have hww' : ∀ q, w' q ≤ w q := fun q => by simp only [hw'def]; split_ifs; exact hw q; exact le_rfl
  have hKP' : Cluster.KP inc Finset.univ w' a := fun Z hZ =>
    le_trans (Finset.sum_le_sum fun q _ => mul_le_mul_of_nonneg_right (hww' q) (Real.exp_pos _).le) (hKP Z hZ)
  set β : ℕ → ℝ := fun k => bR inc w k - bR inc w' k with hβdef
  have hβ0 : β 0 = 0 := by simp [hβdef, bR]
  have hβ : ∀ k, 1 ≤ k → β k = ((k.factorial : ℝ))⁻¹ * ∑ Z : Fin k → Q,
      (if ∃ i, Z i ∈ N then (|ursS inc Z| : ℝ) * ∏ i, w (Z i) else 0) := fun k hk => bR_diff w N hk
  have hβnn : ∀ k, 0 ≤ β k := by
    intro k
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · rw [hβ0]
    · rw [hβ k hk]
      refine mul_nonneg (by positivity) (Finset.sum_nonneg fun Z _ => ?_)
      split_ifs
      · exact mul_nonneg (abs_nonneg _) (Finset.prod_nonneg fun i _ => hw _)
      · exact le_rfl
  -- the bound for `t ∈ [0, 1)`
  have hbound : ∀ t : ℝ, 0 ≤ t → t < 1 →
      ∑ k ∈ Finset.range (K + 1), β k * t ^ k ≤ ∑ q ∈ N, w q * Real.exp (a q) := by
    intro t ht0 ht1
    have h1 := hasSum_bR hrefl hsymm w a hw hKP ht0 ht1
    have h2 := hasSum_bR hrefl hsymm w' a hw' hKP' ht0 ht1
    have h3 : HasSum (fun k => β k * t ^ k)
        (-Real.log ‖Cluster.Xi inc Finset.univ (fun q => -(t : ℂ) * wc w q)‖ -
          -Real.log ‖Cluster.Xi inc Finset.univ (fun q => -(t : ℂ) * wc w' q)‖) := by
      have := h1.sub h2
      simp only [← sub_mul] at this
      exact this
    have hle := sum_le_hasSum (Finset.range (K + 1)) (fun k _ => mul_nonneg (hβnn k) (pow_nonneg ht0 k)) h3
    refine hle.trans ?_
    -- `log|Ξ'| - log|Ξ| ≤ Σ_Nwe^a`
    set z : Q → ℂ := fun q => -(t : ℂ) * wc w q with hz
    have hz' : (fun q => -(t : ℂ) * wc w' q) = fun q => if q ∈ N then 0 else z q := by
      funext q; simp only [hz, hw'def, wc]; split_ifs <;> simp
    rw [hz', Xi_vanish N z]
    have hzw : ∀ q ∈ (Finset.univ : Finset Q), ‖z q‖ ≤ w q := fun q _ => by
      rw [hz, norm_mul, norm_neg, wc, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg ht0,
        Real.norm_of_nonneg (hw q)]
      calc t * w q ≤ 1 * w q := mul_le_mul_of_nonneg_right ht1.le (hw q)
        _ = w q := one_mul _
    have hX := (Cluster.dobrushin inc hrefl hsymm Finset.univ w a hw hKP z hzw _ Finset.univ
      (Finset.Subset.refl _) rfl).1
    have hX' := (Cluster.dobrushin inc hrefl hsymm Finset.univ w a hw hKP z hzw _ (Finset.univ \ N)
      Finset.sdiff_subset rfl).1
    have hrat := Xi_sdiff_le hrefl hsymm Finset.univ w a hw hKP z hzw N (Finset.subset_univ N)
    have hpos : 0 < ‖Cluster.Xi inc Finset.univ z‖ := norm_pos_iff.2 hX
    have hpos' : 0 < ‖Cluster.Xi inc (Finset.univ \ N) z‖ := norm_pos_iff.2 hX'
    have hlog := Real.log_le_log hpos' hrat
    rw [Real.log_mul (Real.exp_pos _).ne' hpos.ne', Real.log_exp] at hlog
    linarith
  -- the limit `t → 1`
  have hlim : ∑ k ∈ Finset.range (K + 1), β k ≤ ∑ q ∈ N, w q * Real.exp (a q) := by
    set p : ℝ → ℝ := fun t => ∑ k ∈ Finset.range (K + 1), β k * t ^ k with hp
    have hcont : Continuous p := by
      simp only [hp]; fun_prop
    have ht : Filter.Tendsto (fun n : ℕ => 1 - 1 / ((n : ℝ) + 1)) Filter.atTop (nhds 1) := by
      have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_sub 1
      simpa using this
    have hp1 : p 1 = ∑ k ∈ Finset.range (K + 1), β k := by simp [hp]
    rw [← hp1]
    refine le_of_tendsto' ((hcont.tendsto 1).comp ht) fun n => hbound _ ?_ ?_
    · have : 1 / ((n : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      linarith
    · have : 0 < 1 / ((n : ℝ) + 1) := by positivity
      linarith
  rw [Finset.sum_range_succ', hβ0, add_zero] at hlim
  refine le_trans (le_of_eq ?_) hlim
  exact Finset.sum_congr rfl fun k _ => (hβ (k + 1) (by omega)).symm

/-- The terms of `eq:cluster-sum`, `(1/m!)Σ_{(Z_1, …, Z_m) meeting N}|ρ^T|Π_iw(Z_i)` at `m = k + 1`. -/
def clusterTerm (inc : Q → Q → Prop) (w : Q → ℝ) (N : Finset Q) (k : ℕ) : ℝ :=
  (((k + 1).factorial : ℝ))⁻¹ * ∑ Z : Fin (k + 1) → Q,
    (if ∃ i, Z i ∈ N then (|ursS inc Z| : ℝ) * ∏ i, w (Z i) else 0)

lemma clusterTerm_nonneg (w : Q → ℝ) (hw : ∀ q, 0 ≤ w q) (N : Finset Q) (k : ℕ) :
    0 ≤ clusterTerm inc w N k := by
  refine mul_nonneg (by positivity) (Finset.sum_nonneg fun Z _ => ?_)
  split_ifs
  · exact mul_nonneg (abs_nonneg _) (Finset.prod_nonneg fun i _ => hw _)
  · exact le_rfl

/-- **`lem:cluster-bounds`, `eq:cluster-sum`** in the core's form: let `h̄, d ≥ 0` and `a` satisfy `eq:kotecky-preiss`,
`Σ_{Z' ≁ Z}h̄(Z')e^{a(Z') + d(Z')} ≤ a(Z)` for every `Z ∈ 𝒫`, and let `N` (the polymers `≁ Z₀`) and `a₀` (the value
`a(Z₀)`) satisfy `Σ_{Z ∈ N}h̄(Z)e^{a(Z) + d(Z)} ≤ a₀`. Then the series
`Σ_{m ≥ 1}(1/m!)Σ_{(Z_1, …, Z_m) meeting N}|ρ^T|Π_ih̄(Z_i)e^{d(Z_i)}` converges and is at most
`Σ_{Z ∈ N}h̄(Z)e^{a(Z) + d(Z)} ≤ a₀`. -/
theorem cluster_bound (hrefl : ∀ a, inc a a) (hsymm : ∀ a b, inc a b → inc b a) (hbar d a : Q → ℝ)
    (hh : ∀ q, 0 ≤ hbar q)
    (hKP : ∀ Z, ∑ Z' ∈ Finset.univ.filter (fun Z' => inc Z' Z), hbar Z' * Real.exp (a Z' + d Z') ≤ a Z)
    (N : Finset Q) (a₀ : ℝ) (hN : ∑ q ∈ N, hbar q * Real.exp (a q + d q) ≤ a₀) :
    Summable (clusterTerm inc (fun q => hbar q * Real.exp (d q)) N) ∧
      ∑' k, clusterTerm inc (fun q => hbar q * Real.exp (d q)) N k ≤ ∑ q ∈ N, hbar q * Real.exp (a q + d q) ∧
      ∑ q ∈ N, hbar q * Real.exp (a q + d q) ≤ a₀ := by
  set w : Q → ℝ := fun q => hbar q * Real.exp (d q) with hwdef
  have hw : ∀ q, 0 ≤ w q := fun q => mul_nonneg (hh q) (Real.exp_pos _).le
  have hwe : ∀ q, w q * Real.exp (a q) = hbar q * Real.exp (a q + d q) := fun q => by
    rw [hwdef, Real.exp_add]; ring
  have hKP' : Cluster.KP inc Finset.univ w a := fun Z _ => by
    simp only [hwe]; exact hKP Z
  have hpart : ∀ K, ∑ k ∈ Finset.range K, clusterTerm inc w N k ≤ ∑ q ∈ N, hbar q * Real.exp (a q + d q) := by
    intro K
    have := cluster_sum hrefl hsymm w a hw hKP' N K
    simp only [hwe] at this
    exact this
  exact ⟨summable_of_sum_range_le (clusterTerm_nonneg w hw N) hpart,
    Real.tsum_le_of_sum_range_le (clusterTerm_nonneg w hw N) hpart, hN⟩

end TreeGraph
end CoreLean

end
