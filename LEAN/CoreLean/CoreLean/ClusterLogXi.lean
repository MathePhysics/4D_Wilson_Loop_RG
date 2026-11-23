/-
The logarithm of a polymer sum with complex activities, `thm:polymer-logarithm` of BALABAN_CORE.tex
(`733037410da1`), for an abstract reflexive and symmetric incompatibility relation on a finite set `Q` of polymers:
if `|H(Z)| ≤ w(Z)` with `w ≥ 0` satisfying `eq:kotecky-preiss`, then `Ξ(H) ≠ 0`, the continuous logarithm of
`t ↦ Ξ(tH)` on `[0, 1]` vanishing at `0` exists and is unique, its value at `1` is the absolutely convergent series
`Σ_{m ≥ 1}c_m(H)/m!`, `c_m(H) = Σ_{Z ∈ Q^m}ρ^T(Z)Π_iH(Z_i)`, the series regroups by the union of the polymers of a
sequence, and the result is holomorphic in a parameter on which `H` depends holomorphically with the bound uniform.
The proof: `P(s) = Ξ(sH)` is a polynomial with `P(0) = 1`, no zero in the closed unit disc (Dobrushin), and
`X·P' = (Σ_kkc_kX^k/k!)·P` (the exponential formula `En_rec`); `log_series_complex` gives the rest.
-/
import CoreLean.ClusterSum
import CoreLean.ClusterLogC

open Finset

noncomputable section

namespace CoreLean
namespace TreeGraph

open Classical

variable {Q : Type*} [Fintype Q] {inc : Q → Q → Prop}

/-! ### The polynomial `P(s) = Ξ(sH)` -/

/-- `E_n(H)/n!`, the coefficients of `Ξ(sH)`. -/
def gH (inc : Q → Q → Prop) (H : Q → ℂ) (n : ℕ) : ℂ := En (inc := inc) H n / (n.factorial : ℂ)

/-- `P(s) = Ξ(sH)`. -/
def PH (inc : Q → Q → Prop) (H : Q → ℂ) : Polynomial ℂ :=
  ∑ n ∈ Finset.range (Fintype.card Q + 1), Polynomial.C (gH inc H n) * Polynomial.X ^ n

/-- `c_k(H)/k!`, `0` at `k = 0`. -/
def cH (inc : Q → Q → Prop) (H : Q → ℂ) (k : ℕ) : ℂ :=
  if k = 0 then 0 else Ck (inc := inc) H k / (k.factorial : ℂ)

lemma coeff_PH (hrefl : ∀ a, inc a a) (hsymm : ∀ a b, inc a b → inc b a) (H : Q → ℂ) (n : ℕ) :
    PowerSeries.coeff n (PH inc H : PowerSeries ℂ) = gH inc H n := by
  rw [Polynomial.coeff_coe, PH, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · rw [gH, En_large hrefl hsymm _ (by simp only [Finset.mem_range] at h; omega)]; simp

lemma eval_PH (hrefl : ∀ a, inc a a) (hsymm : ∀ a b, inc a b → inc b a) (H : Q → ℂ) (s : ℂ) :
    (PH inc H).eval s = Cluster.Xi inc Finset.univ (fun q => s * H q) := by
  rw [Xi_eq_sequences hrefl hsymm, PH, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, En_homog, gH]
  field_simp

lemma PH_zero (H : Q → ℂ) : (PH inc H).eval 0 = 1 := by
  rw [PH, Polynomial.eval_finsetSum, Finset.sum_eq_single 0]
  · simp [gH, En_zero]
  · intro m _ hm; simp [hm]
  · intro h; simp at h

/-- **No zero in the closed unit disc**, by the criterion of Kotecký and Preiss. -/
lemma PH_ne_zero (hrefl : ∀ a, inc a a) (hsymm : ∀ a b, inc a b → inc b a) (w a : Q → ℝ) (hw : ∀ q, 0 ≤ w q)
    (hKP : Cluster.KP inc Finset.univ w a) (H : Q → ℂ) (hH : ∀ q, ‖H q‖ ≤ w q) {s : ℂ} (hs : ‖s‖ ≤ 1) :
    (PH inc H).eval s ≠ 0 := by
  rw [eval_PH hrefl hsymm]
  refine (Cluster.dobrushin inc hrefl hsymm Finset.univ w a hw hKP _ (fun q _ => ?_) _ Finset.univ
    (Finset.Subset.refl _) rfl).1
  rw [norm_mul]
  calc ‖s‖ * ‖H q‖ ≤ 1 * w q := mul_le_mul hs (hH q) (norm_nonneg _) zero_le_one
    _ = w q := one_mul _

/-- One term of the recursion: `(k+1)c_{k+1}g_{m-k} = C(m, k)C_{k+1}E_{m-k}/m!`. -/
lemma term_idH (H : Q → ℂ) {m k : ℕ} (hk : k ≤ m) :
    ((k + 1 : ℕ) : ℂ) * cH inc H (k + 1) * gH inc H (m - k) =
      (m.choose k : ℂ) * Ck (inc := inc) H (k + 1) * En (inc := inc) H (m - k) / (m.factorial : ℂ) := by
  have hch := Nat.choose_mul_factorial_mul_factorial hk
  have hf1 : ((k + 1).factorial : ℂ) = (k + 1 : ℂ) * (k.factorial : ℂ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have hmf : (m.factorial : ℂ) = (m.choose k : ℂ) * (k.factorial : ℂ) * ((m - k).factorial : ℂ) := by
    exact_mod_cast hch.symm
  unfold cH gH
  rw [if_neg (Nat.succ_ne_zero k)]
  have hk0 : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero k)
  have hmk0 : ((m - k).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  have hc0 : (m.choose k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.choose_pos hk).ne'
  have hk1 : (k + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  rw [hf1, hmf]
  push_cast
  field_simp

/-- **The recursion in power series**: `X·P' = (Σ_kkc_kX^k/k!)·P`. -/
lemma PH_rec (hrefl : ∀ a, inc a a) (hsymm : ∀ a b, inc a b → inc b a) (H : Q → ℂ) :
    PowerSeries.X * (PowerSeries.derivative (R := ℂ)) (PH inc H : PowerSeries ℂ) =
      (PowerSeries.mk fun k => (k : ℂ) * cH inc H k) * (PH inc H : PowerSeries ℂ) := by
  ext n
  conv_rhs => rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => PowerSeries.coeff i (PowerSeries.mk fun k => (k : ℂ) * cH inc H k) *
      PowerSeries.coeff j (PH inc H : PowerSeries ℂ)) n]
  simp only [PowerSeries.coeff_mk, coeff_PH hrefl hsymm]
  rcases n with _ | m
  · simp [PowerSeries.coeff_zero_X_mul]
  · rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative, coeff_PH hrefl hsymm, Finset.sum_range_succ']
    simp only [Nat.cast_zero, zero_mul, add_zero]
    have hrec := En_rec hsymm H (m + 1) (by omega)
    simp only [Nat.add_sub_cancel] at hrec
    rw [Finset.sum_congr rfl (g := fun k => (m.choose k : ℂ) * Ck (inc := inc) H (k + 1) *
        En (inc := inc) H (m - k) / (m.factorial : ℂ)) fun k hk => by
      rw [show m + 1 - (k + 1) = m - k by omega]
      exact term_idH H (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk))]
    rw [← Finset.sum_div, ← hrec]
    unfold gH
    have hm0 : (m.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero m)
    rw [Nat.factorial_succ]
    push_cast
    field_simp

/-! ### The continuous logarithm -/

/-- **Uniqueness of the continuous logarithm**: two continuous logarithms on `[0, 1]` of the same function which
agree at `0` agree at `1`. -/
lemma clog_unique {L₁ L₂ : ℝ → ℂ} (h₁ : ContinuousOn L₁ (Set.Icc 0 1)) (h₂ : ContinuousOn L₂ (Set.Icc 0 1))
    (h0 : L₁ 0 = L₂ 0) (he : ∀ t ∈ Set.Icc (0 : ℝ) 1, Complex.exp (L₁ t) = Complex.exp (L₂ t)) : L₁ 1 = L₂ 1 := by
  set c : ℂ := 2 * Real.pi * Complex.I with hc
  have hc0 : c ≠ 0 := by
    rw [hc]; simp [Real.pi_ne_zero, Complex.I_ne_zero]
  set f : ℝ → ℝ := fun t => ((L₁ t - L₂ t) / c).re with hf
  have hfc : ContinuousOn f (Set.Icc 0 1) :=
    Complex.continuous_re.comp_continuousOn ((h₁.sub h₂).div_const c)
  have hint : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∃ n : ℤ, L₁ t - L₂ t = n * c := by
    intro t ht
    have : Complex.exp (L₁ t - L₂ t) = 1 := by
      rw [Complex.exp_sub, he t ht, div_self (Complex.exp_ne_zero _)]
    exact Complex.exp_eq_one_iff.1 this
  have hfint : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∃ n : ℤ, f t = n ∧ L₁ t - L₂ t = n * c := by
    intro t ht
    obtain ⟨n, hn⟩ := hint t ht
    refine ⟨n, ?_, hn⟩
    rw [hf]; simp only [hn, mul_div_assoc, div_self hc0, mul_one, Complex.intCast_re]
  have hmem0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hmem1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hf0 : f 0 = 0 := by rw [hf]; simp [h0]
  obtain ⟨n, hn1, hL⟩ := hfint 1 hmem1
  have hnot_half : ∀ t ∈ Set.Icc (0 : ℝ) 1, f t ≠ 1 / 2 ∧ f t ≠ -(1 / 2) := by
    intro t ht
    obtain ⟨m, hm, -⟩ := hfint t ht
    rw [hm]
    constructor
    · intro h
      rcases le_or_gt m 0 with hm0 | hm0
      · have : (m : ℝ) ≤ 0 := by exact_mod_cast hm0
        linarith
      · have : (1 : ℝ) ≤ m := by exact_mod_cast hm0
        linarith
    · intro h
      rcases le_or_gt 0 m with hm0 | hm0
      · have : (0 : ℝ) ≤ m := by exact_mod_cast hm0
        linarith
      · have hm1 : m ≤ -1 := by omega
        have : (m : ℝ) ≤ -1 := by exact_mod_cast hm1
        linarith
  have hn0 : n = 0 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hneg | hpos
    · have hn1' : n ≤ -1 := by omega
      have hle : (n : ℝ) ≤ -1 := by exact_mod_cast hn1'
      have hsub := intermediate_value_Icc' (zero_le_one' ℝ) hfc
      obtain ⟨t, ht, hft⟩ := hsub (show -(1 / 2 : ℝ) ∈ Set.Icc (f 1) (f 0) from
        ⟨by rw [hn1]; linarith, by rw [hf0]; norm_num⟩)
      exact (hnot_half t ht).2 hft
    · have hle : (1 : ℝ) ≤ n := by exact_mod_cast hpos
      have hsub := intermediate_value_Icc (zero_le_one' ℝ) hfc
      obtain ⟨t, ht, hft⟩ := hsub (show (1 / 2 : ℝ) ∈ Set.Icc (f 0) (f 1) from
        ⟨by rw [hf0]; norm_num, by rw [hn1]; linarith⟩)
      exact (hnot_half t ht).1 hft
  rw [hn0, Int.cast_zero, zero_mul, sub_eq_zero] at hL
  exact hL

/-! ### The theorem -/

/-- The terms of the logarithm, `c_{k+1}(H)/(k+1)!`. -/
def logTerm (inc : Q → Q → Prop) (H : Q → ℂ) (k : ℕ) : ℂ :=
  Ck (inc := inc) H (k + 1) / ((k + 1).factorial : ℂ)

lemma norm_logTerm_le (w : Q → ℝ) (H : Q → ℂ) (hH : ∀ q, ‖H q‖ ≤ w q) (k : ℕ) :
    ‖logTerm inc H k‖ ≤ clusterTerm inc w Finset.univ k := by
  unfold logTerm clusterTerm Ck Ci
  rw [norm_div, Complex.norm_natCast, div_eq_inv_mul]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun Z _ => ?_)
  rw [if_pos ⟨0, Finset.mem_univ _⟩, norm_mul, Complex.norm_intCast, norm_prod]
  push_cast
  exact mul_le_mul_of_nonneg_left (Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) fun i _ => hH _) (abs_nonneg _)

lemma summable_clusterTerm (hrefl : ∀ a, inc a a) (hsymm : ∀ a b, inc a b → inc b a) (w a : Q → ℝ)
    (hw : ∀ q, 0 ≤ w q) (hKP : Cluster.KP inc Finset.univ w a) (N : Finset Q) :
    Summable (clusterTerm inc w N) :=
  summable_of_sum_range_le (clusterTerm_nonneg w hw N) fun K => cluster_sum hrefl hsymm w a hw hKP N K

/-- **`thm:polymer-logarithm`, the logarithm**: under `eq:kotecky-preiss` for `w ≥ 0` and `|H| ≤ w`, the polymer sum
`Ξ(H)` does not vanish; there is a continuous logarithm `L` of `t ↦ Ξ(tH)` on `[0, 1]` with `L(0) = 0` (unique by
`clog_unique`); and `L(1) = Σ_{m ≥ 1}c_m(H)/m!`, the series converging absolutely. -/
theorem polymer_log (hrefl : ∀ a, inc a a) (hsymm : ∀ a b, inc a b → inc b a) (w a : Q → ℝ) (hw : ∀ q, 0 ≤ w q)
    (hKP : Cluster.KP inc Finset.univ w a) (H : Q → ℂ) (hH : ∀ q, ‖H q‖ ≤ w q) :
    Cluster.Xi inc Finset.univ H ≠ 0 ∧
      ∃ L : ℝ → ℂ, ContinuousOn L (Set.Icc 0 1) ∧ L 0 = 0 ∧
        (∀ t ∈ Set.Icc (0 : ℝ) 1, Complex.exp (L t) = Cluster.Xi inc Finset.univ (fun q => (t : ℂ) * H q)) ∧
        Summable (fun k => ‖logTerm inc H k‖) ∧ HasSum (logTerm inc H) (L 1) := by
  have hne := fun {s : ℂ} (hs : ‖s‖ ≤ 1) => PH_ne_zero hrefl hsymm w a hw hKP H hH hs
  obtain ⟨L, hLc, hL0, hLe, hLs⟩ := Newton.log_series_complex (PH inc H) (PH_zero H) (fun s hs => hne hs)
    (cH inc H) (by simp [cH]) (PH_rec hrefl hsymm H)
  refine ⟨?_, fun t => L (t : ℂ), ?_, by simpa using hL0, fun t ht => ?_, ?_, ?_⟩
  · have h1 := hne (s := 1) (by simp)
    rw [eval_PH hrefl hsymm] at h1
    simpa using h1
  · refine hLc.comp Complex.continuous_ofReal.continuousOn fun t ht => ?_
    rw [Metric.mem_closedBall, dist_zero_right, Complex.norm_real, Real.norm_of_nonneg ht.1]
    exact ht.2
  · rw [hLe _ (by rw [Complex.norm_real, Real.norm_of_nonneg ht.1]; exact ht.2), eval_PH hrefl hsymm]
  · exact Summable.of_nonneg_of_le (fun k => norm_nonneg _) (norm_logTerm_le w H hH)
      (summable_clusterTerm hrefl hsymm w a hw hKP Finset.univ)
  · have h1 := hLs 1 (by simp)
    simp only [one_pow, mul_one] at h1
    have h2 := (hasSum_nat_add_iff' 1).mpr h1
    simp only [Finset.range_one, Finset.sum_singleton, cH, if_true, sub_zero] at h2
    convert h2 using 1
    funext k
    simp [logTerm]

/-! ### The grouping by the union -/

variable {C : Type*} [DecidableEq C]

/-- The union `⋃_iZ_i` of the cubes of a sequence of polymers, `u(Z)` the set of the cubes of `Z`. -/
def unionOf (u : Q → Finset C) {m : ℕ} (Z : Fin m → Q) : Finset C := Finset.univ.sup fun i => u (Z i)

/-- The terms of `E(X)`: `(1/m!)Σ_{Z ∈ Q^m, ⋃Z = X}ρ^TΠH` at `m = k + 1`. -/
def unionTerm (inc : Q → Q → Prop) (u : Q → Finset C) (H : Q → ℂ) (X : Finset C) (k : ℕ) : ℂ :=
  ((k + 1).factorial : ℂ)⁻¹ * ∑ Z : Fin (k + 1) → Q,
    (if unionOf u Z = X then (ursS inc Z : ℂ) * ∏ i, H (Z i) else 0)

/-- `E(X) = Σ_{m ≥ 1}(1/m!)Σ_{⋃Z = X}ρ^TΠH`. -/
def EX (inc : Q → Q → Prop) (u : Q → Finset C) (H : Q → ℂ) (X : Finset C) : ℂ := ∑' k, unionTerm inc u H X k

lemma norm_unionTerm_le (u : Q → Finset C) (w : Q → ℝ) (H : Q → ℂ) (hH : ∀ q, ‖H q‖ ≤ w q) (X : Finset C)
    (k : ℕ) : ‖unionTerm inc u H X k‖ ≤ clusterTerm inc w Finset.univ k := by
  unfold unionTerm clusterTerm
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun Z _ => ?_)
  rw [if_pos (show ∃ i, Z i ∈ (Finset.univ : Finset Q) from ⟨0, Finset.mem_univ _⟩)]
  split_ifs
  · rw [norm_mul, Complex.norm_intCast, norm_prod]
    push_cast
    exact mul_le_mul_of_nonneg_left (Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) fun i _ => hH _)
      (abs_nonneg _)
  · rw [norm_zero]
    exact mul_nonneg (abs_nonneg _) (Finset.prod_nonneg fun i _ => (norm_nonneg _).trans (hH _))

lemma unionOf_mem (u : Q → Finset C) {m : ℕ} (Z : Fin m → Q) :
    unionOf u Z ∈ (Finset.univ.sup u).powerset := by
  rw [Finset.mem_powerset, unionOf]
  exact Finset.sup_le fun i _ => Finset.le_sup (f := u) (Finset.mem_univ (Z i))

/-- **`eq:polymer-logarithm`**: `Σ_{m ≥ 1}c_m(H)/m! = Σ_XE(X)`, the sum over the unions `X` of the cubes of the
polymers, each `E(X)` an absolutely convergent series; `E(X) = 0` for the other sets of cubes. -/
theorem log_eq_sum_EX (hrefl : ∀ a, inc a a) (hsymm : ∀ a b, inc a b → inc b a) (w a : Q → ℝ)
    (hw : ∀ q, 0 ≤ w q) (hKP : Cluster.KP inc Finset.univ w a) (H : Q → ℂ) (hH : ∀ q, ‖H q‖ ≤ w q)
    (u : Q → Finset C) :
    (∀ X, Summable fun k => ‖unionTerm inc u H X k‖) ∧
      (∀ X ∉ (Finset.univ.sup u).powerset, EX inc u H X = 0) ∧
      HasSum (logTerm inc H) (∑ X ∈ (Finset.univ.sup u).powerset, EX inc u H X) := by
  have hsum := summable_clusterTerm hrefl hsymm w a hw hKP Finset.univ
  have habs : ∀ X, Summable fun k => ‖unionTerm inc u H X k‖ := fun X =>
    Summable.of_nonneg_of_le (fun k => norm_nonneg _) (norm_unionTerm_le u w H hH X) hsum
  refine ⟨habs, fun X hX => ?_, ?_⟩
  · unfold EX
    convert tsum_zero with k
    unfold unionTerm
    rw [Finset.sum_eq_zero fun Z _ => if_neg (fun h : unionOf u Z = X => hX (h ▸ unionOf_mem u Z)), mul_zero]
  · have h := hasSum_sum (s := (Finset.univ.sup u).powerset) fun X _ => (habs X).of_norm.hasSum
    convert h using 1
    funext k
    unfold logTerm unionTerm Ck Ci
    rw [← Finset.mul_sum, Finset.sum_comm, div_eq_inv_mul]
    congr 1
    refine Finset.sum_congr rfl fun Z _ => ?_
    rw [Finset.sum_ite_eq, if_pos (unionOf_mem u Z)]
    rfl

/-! ### Holomorphy in a parameter -/

/-- **Holomorphy**: if `H` depends holomorphically on a parameter `ζ` in an open `U ⊆ ℂ` with `|H_ζ| ≤ w` there,
then `ζ ↦ Σ_{m ≥ 1}c_m(H_ζ)/m!` and `ζ ↦ E_ζ(X)` are holomorphic on `U`. -/
theorem polymer_log_holomorphic (hrefl : ∀ a, inc a a) (hsymm : ∀ a b, inc a b → inc b a) (w a : Q → ℝ)
    (hw : ∀ q, 0 ≤ w q) (hKP : Cluster.KP inc Finset.univ w a) {U : Set ℂ} (hU : IsOpen U) (H : ℂ → Q → ℂ)
    (hHd : ∀ q, DifferentiableOn ℂ (fun ζ => H ζ q) U) (hH : ∀ ζ ∈ U, ∀ q, ‖H ζ q‖ ≤ w q) (u : Q → Finset C)
    (X : Finset C) :
    DifferentiableOn ℂ (fun ζ => ∑' k, logTerm inc (H ζ) k) U ∧
      DifferentiableOn ℂ (fun ζ => EX inc u (H ζ) X) U := by
  have hsum := summable_clusterTerm hrefl hsymm w a hw hKP Finset.univ
  have hprod : ∀ {m : ℕ} (Z : Fin m → Q), DifferentiableOn ℂ (fun ζ => ∏ i, H ζ (Z i)) U := fun Z =>
    DifferentiableOn.fun_finsetProd fun i _ => hHd (Z i)
  constructor
  · refine Complex.differentiableOn_tsum_of_summable_norm hsum (fun k => ?_) hU
      fun k ζ hζ => norm_logTerm_le w (H ζ) (hH ζ hζ) k
    unfold logTerm Ck Ci
    refine DifferentiableOn.div_const (DifferentiableOn.fun_sum fun Z _ => ?_) _
    exact (hprod Z).const_mul _
  · refine Complex.differentiableOn_tsum_of_summable_norm hsum (fun k => ?_) hU
      fun k ζ hζ => norm_unionTerm_le u w (H ζ) (hH ζ hζ) X k
    unfold unionTerm
    refine DifferentiableOn.const_mul (DifferentiableOn.fun_sum fun Z _ => ?_) _
    split_ifs
    · exact (hprod Z).const_mul _
    · exact differentiableOn_const _

end TreeGraph
end CoreLean

end
