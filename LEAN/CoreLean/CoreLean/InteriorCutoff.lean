/-
The cutoff of the proof of `prop:schauder` of BALABAN_CORE.tex (`a71f8998da10`), used in
`prop:interior-schauder`: a function `χ₁` on `ℝ` equal to `1` on `[-2, 2]`, vanishing outside
`[-5/2, 5/2]`, with `|χ₁(t + h) - χ₁(t)| ≤ 3|h|` and `|χ₁(t + h) - 2χ₁(t) + χ₁(t - h)| ≤ 24h²` for `|h| ≤ 1`,
and the product `χ(n) = Π_μ χ₁((n_μ - y_μ)/K)` on `ℤ⁴`.

The core asks for a twice continuously differentiable `χ₁` with `|χ₁'| ≤ 4` and `|χ₁''| ≤ 24`; its proof uses
only the bounds of the first and second differences which follow. We take the smooth step
`σ(u) = ∫_0^u 6c(1 - c)`, `c = max(0, min(u, 1))`, whose derivative is Lipschitz with the constant `6`, and
`χ₁(t) = σ(5 - 2|t|)`; the bounds are `3|h|` and `24h²`.
-/
import CoreLean.InteriorSetup
import CoreLean.PartitionBounds

open Real MeasureTheory Set Filter Topology

noncomputable section

namespace CoreLean
namespace InteriorSchauder

/-! ### The smooth step -/

/-- `c(u) = max(0, min(u, 1))`. -/
def clamp01 (u : ℝ) : ℝ := max 0 (min u 1)

/-- `q(u) = 6c(1 - c)`. -/
def qs (u : ℝ) : ℝ := 6 * clamp01 u * (1 - clamp01 u)

lemma clamp01_nonneg (u : ℝ) : 0 ≤ clamp01 u := le_max_left _ _

lemma clamp01_le_one (u : ℝ) : clamp01 u ≤ 1 := max_le zero_le_one (min_le_right _ _)

lemma continuous_clamp01 : Continuous clamp01 :=
  continuous_const.max (continuous_id.min continuous_const)

lemma continuous_qs : Continuous qs := by
  unfold qs; exact (continuous_const.mul continuous_clamp01).mul (continuous_const.sub continuous_clamp01)

lemma qs_nonneg (u : ℝ) : 0 ≤ qs u := by
  unfold qs; have := clamp01_nonneg u; have := clamp01_le_one u; nlinarith

lemma qs_le (u : ℝ) : qs u ≤ 3 / 2 := by
  unfold qs; nlinarith [sq_nonneg (clamp01 u - 1 / 2)]

lemma abs_clamp01_sub (u v : ℝ) : |clamp01 u - clamp01 v| ≤ |u - v| := by
  have h1 := le_abs_self (u - v)
  have h2 := neg_abs_le (u - v)
  unfold clamp01
  rw [abs_le]
  constructor <;> simp only [max_def, min_def] <;> split_ifs <;> linarith

lemma qs_lip (u v : ℝ) : |qs u - qs v| ≤ 6 * |u - v| := by
  have h := abs_clamp01_sub u v
  have e : qs u - qs v = 6 * (clamp01 u - clamp01 v) * (1 - clamp01 u - clamp01 v) := by unfold qs; ring
  have h1 : |1 - clamp01 u - clamp01 v| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith [clamp01_nonneg u, clamp01_le_one u, clamp01_nonneg v,
      clamp01_le_one v]
  rw [e, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 6)]
  calc 6 * |clamp01 u - clamp01 v| * |1 - clamp01 u - clamp01 v| ≤ 6 * |clamp01 u - clamp01 v| * 1 := by
        gcongr
    _ ≤ 6 * |u - v| := by linarith

lemma qs_eq_zero_of_nonpos {u : ℝ} (hu : u ≤ 0) : qs u = 0 := by
  unfold qs clamp01; rw [min_eq_left (by linarith), max_eq_left hu]; ring

lemma qs_eq_zero_of_one_le {u : ℝ} (hu : 1 ≤ u) : qs u = 0 := by
  unfold qs clamp01; rw [min_eq_right hu, max_eq_right zero_le_one]; ring

/-- The smooth step `σ(u) = ∫_0^u q`. -/
def sig (u : ℝ) : ℝ := ∫ s in (0 : ℝ)..u, qs s

lemma hasDerivAt_sig (u : ℝ) : HasDerivAt sig (qs u) u :=
  intervalIntegral.integral_hasDerivAt_right (continuous_qs.intervalIntegrable _ _)
    (continuous_qs.stronglyMeasurableAtFilter _ _) continuous_qs.continuousAt

lemma sig_eq_zero {u : ℝ} (hu : u ≤ 0) : sig u = 0 := by
  unfold sig
  rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun t ht => ?_]
  · simp
  · rw [uIcc_of_ge hu] at ht
    exact qs_eq_zero_of_nonpos ht.2

lemma sig_one : sig 1 = 1 := by
  unfold sig
  rw [intervalIntegral.integral_congr (g := fun t => 6 * t * (1 - t)) fun t ht => ?_]
  · rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t => 3 * t ^ 2 - 2 * t ^ 3)
      (fun x _ => ?_) ((by fun_prop : Continuous fun t : ℝ => 6 * t * (1 - t)).intervalIntegrable 0 1)]
    · norm_num
    · have := ((hasDerivAt_pow 2 x).const_mul 3).sub ((hasDerivAt_pow 3 x).const_mul 2)
      convert this using 1; push_cast; ring
  · rw [uIcc_of_le zero_le_one] at ht
    simp only [qs, clamp01]
    rw [min_eq_left ht.2, max_eq_right ht.1]

lemma sig_eq_one {u : ℝ} (hu : 1 ≤ u) : sig u = 1 := by
  unfold sig
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 1) (continuous_qs.intervalIntegrable _ _)
    (continuous_qs.intervalIntegrable _ _)]
  rw [intervalIntegral.integral_congr (a := 1) (b := u) (g := fun _ => (0 : ℝ)) fun t ht => ?_]
  · have := sig_one; unfold sig at this; rw [this]; simp
  · rw [uIcc_of_le hu] at ht
    exact qs_eq_zero_of_one_le ht.1

lemma monotone_sig : Monotone sig := monotone_of_hasDerivAt_nonneg hasDerivAt_sig qs_nonneg

lemma sig_nonneg (u : ℝ) : 0 ≤ sig u := by
  rcases le_total u 0 with h | h
  · rw [sig_eq_zero h]
  · have := monotone_sig h; rwa [sig_eq_zero le_rfl] at this

lemma sig_le_one (u : ℝ) : sig u ≤ 1 := by
  rcases le_total u 1 with h | h
  · have := monotone_sig h; rwa [sig_one] at this
  · rw [sig_eq_one h]

attribute [irreducible] sig

/-! ### Two lemmas of one-variable calculus -/

lemma lip_of_deriv {g d : ℝ → ℝ} (hd : ∀ x, HasDerivAt g (d x) x) {B : ℝ} (hb : ∀ x, |d x| ≤ B)
    (s t : ℝ) : |g s - g t| ≤ B * |s - t| := by
  have := Convex.norm_image_sub_le_of_norm_deriv_le (s := univ) (fun x _ => (hd x).differentiableAt)
    (fun x _ => by rw [(hd x).deriv, Real.norm_eq_abs]; exact hb x) convex_univ (mem_univ t) (mem_univ s)
  simpa [Real.norm_eq_abs] using this

lemma second_of_deriv_lip {g d : ℝ → ℝ} (hd : ∀ x, HasDerivAt g (d x) x) {C : ℝ}
    (hL : ∀ x y, |d x - d y| ≤ C * |x - y|) (t h : ℝ) : |g (t + h) - 2 * g t + g (t - h)| ≤ C * h ^ 2 := by
  set G : ℝ → ℝ := fun r => g (r + h) - g r with hG
  have hdG : ∀ r, HasDerivAt G (d (r + h) - d r) r := fun r =>
    ((hd (r + h)).comp_add_const r h).sub (hd r)
  have hb : ∀ r, |d (r + h) - d r| ≤ C * |h| := fun r => by
    have := hL (r + h) r; rwa [add_sub_cancel_left] at this
  have := lip_of_deriv hdG hb t (t - h)
  simp only [hG, sub_add_cancel, sub_sub_cancel] at this
  calc |g (t + h) - 2 * g t + g (t - h)| = |g (t + h) - g t - (g t - g (t - h))| := by ring_nf
    _ ≤ C * |h| * |h| := this
    _ = C * h ^ 2 := by rw [mul_assoc, ← sq, sq_abs]

/-! ### The one-dimensional cutoff -/

/-- `σ(5 - 2t)`. -/
def gp : ℝ → ℝ := sig ∘ fun t => 5 - 2 * t

/-- `σ(5 + 2t)`. -/
def gm : ℝ → ℝ := sig ∘ fun t => 5 + 2 * t

lemma gp_apply (t : ℝ) : gp t = sig (5 - 2 * t) := rfl

lemma gm_apply (t : ℝ) : gm t = sig (5 + 2 * t) := rfl

lemma hasDerivAt_gp (t : ℝ) : HasDerivAt gp (qs (5 - 2 * t) * (-2)) t := by
  have h1 : HasDerivAt (fun t : ℝ => 5 - 2 * t) (-2) t := by
    have := ((hasDerivAt_id t).const_mul (2 : ℝ)).const_sub (5 : ℝ)
    simpa using this
  have h2 : HasDerivAt sig (qs (5 - 2 * t)) ((fun t : ℝ => 5 - 2 * t) t) := hasDerivAt_sig _
  exact HasDerivAt.comp (h₂ := sig) (h := fun t : ℝ => 5 - 2 * t) t h2 h1

lemma hasDerivAt_gm (t : ℝ) : HasDerivAt gm (qs (5 + 2 * t) * 2) t := by
  have h1 : HasDerivAt (fun t : ℝ => 5 + 2 * t) 2 t := by
    have := ((hasDerivAt_id t).const_mul (2 : ℝ)).const_add (5 : ℝ)
    simpa using this
  have h2 : HasDerivAt sig (qs (5 + 2 * t)) ((fun t : ℝ => 5 + 2 * t) t) := hasDerivAt_sig _
  exact HasDerivAt.comp (h₂ := sig) (h := fun t : ℝ => 5 + 2 * t) t h2 h1

lemma gp_lip (s t : ℝ) : |gp s - gp t| ≤ 3 * |s - t| :=
  lip_of_deriv hasDerivAt_gp (fun x => by
    rw [abs_mul, abs_of_nonneg (qs_nonneg _)]; norm_num; linarith [qs_le (5 - 2 * x)]) s t

lemma gm_lip (s t : ℝ) : |gm s - gm t| ≤ 3 * |s - t| :=
  lip_of_deriv hasDerivAt_gm (fun x => by
    rw [abs_mul, abs_of_nonneg (qs_nonneg _)]; norm_num; linarith [qs_le (5 + 2 * x)]) s t

lemma gp_second (t h : ℝ) : |gp (t + h) - 2 * gp t + gp (t - h)| ≤ 24 * h ^ 2 :=
  second_of_deriv_lip hasDerivAt_gp (fun x y => by
    have h := qs_lip (5 - 2 * x) (5 - 2 * y)
    have e1 : qs (5 - 2 * x) * -2 - qs (5 - 2 * y) * -2 = -2 * (qs (5 - 2 * x) - qs (5 - 2 * y)) := by ring
    have e2 : 5 - 2 * x - (5 - 2 * y) = -2 * (x - y) := by ring
    rw [e1, abs_mul, abs_neg, abs_two]
    rw [e2, abs_mul, abs_neg, abs_two] at h
    linarith) t h

lemma gm_second (t h : ℝ) : |gm (t + h) - 2 * gm t + gm (t - h)| ≤ 24 * h ^ 2 :=
  second_of_deriv_lip hasDerivAt_gm (fun x y => by
    have h := qs_lip (5 + 2 * x) (5 + 2 * y)
    have e1 : qs (5 + 2 * x) * 2 - qs (5 + 2 * y) * 2 = 2 * (qs (5 + 2 * x) - qs (5 + 2 * y)) := by ring
    have e2 : 5 + 2 * x - (5 + 2 * y) = 2 * (x - y) := by ring
    rw [e1, abs_mul, abs_two]
    rw [e2, abs_mul, abs_two] at h
    linarith) t h

/-- `χ₁(t) = σ(5 - 2|t|)`. -/
def chi1 (t : ℝ) : ℝ := if 0 ≤ t then gp t else gm t

lemma chi1_eq_gp {t : ℝ} (ht : -2 ≤ t) : chi1 t = gp t := by
  unfold chi1
  split_ifs with h
  · rfl
  · rw [gm_apply, gp_apply, sig_eq_one (by linarith), sig_eq_one (by linarith)]

lemma chi1_eq_gm {t : ℝ} (ht : t ≤ 2) : chi1 t = gm t := by
  unfold chi1
  split_ifs with h
  · rw [gm_apply, gp_apply, sig_eq_one (by linarith), sig_eq_one (by linarith)]
  · rfl

lemma chi1_nonneg (t : ℝ) : 0 ≤ chi1 t := by unfold chi1; split_ifs <;> simp only [gp_apply, gm_apply, sig_nonneg]

lemma chi1_le_one (t : ℝ) : chi1 t ≤ 1 := by unfold chi1; split_ifs <;> simp only [gp_apply, gm_apply, sig_le_one]

lemma chi1_eq_one {t : ℝ} (ht : |t| ≤ 2) : chi1 t = 1 := by
  rw [abs_le] at ht
  rw [chi1_eq_gp ht.1, gp_apply]; exact sig_eq_one (by linarith)

lemma chi1_eq_zero {t : ℝ} (ht : 5 / 2 ≤ |t|) : chi1 t = 0 := by
  rcases le_total 0 t with h | h
  · rw [abs_of_nonneg h] at ht
    rw [chi1_eq_gp (by linarith), gp_apply]; exact sig_eq_zero (by linarith)
  · rw [abs_of_nonpos h] at ht
    rw [chi1_eq_gm (by linarith), gm_apply]; exact sig_eq_zero (by linarith)

lemma chi1_lip (s t : ℝ) : |chi1 s - chi1 t| ≤ 3 * |s - t| := by
  wlog hst : t ≤ s generalizing s t
  · rw [abs_sub_comm, abs_sub_comm s]; exact this t s (le_of_not_ge hst)
  by_cases h1 : -2 ≤ t
  · rw [chi1_eq_gp h1, chi1_eq_gp (by linarith)]; exact gp_lip s t
  by_cases h2 : s ≤ 2
  · rw [chi1_eq_gm h2, chi1_eq_gm (by linarith)]; exact gm_lip s t
  push_neg at h1 h2
  calc |chi1 s - chi1 t| ≤ |chi1 s - chi1 0| + |chi1 0 - chi1 t| := abs_sub_le _ _ _
    _ ≤ 3 * |s - 0| + 3 * |0 - t| := by
        gcongr
        · rw [chi1_eq_gp (by linarith), chi1_eq_gp (by norm_num)]; exact gp_lip s 0
        · rw [chi1_eq_gm (by norm_num), chi1_eq_gm (by linarith)]; exact gm_lip 0 t
    _ = 3 * |s - t| := by
        rw [sub_zero, zero_sub, abs_neg, abs_of_pos (by linarith), abs_of_neg (by linarith),
          abs_of_pos (by linarith)]; ring

lemma chi1_second {t h : ℝ} (hh : |h| ≤ 1) : |chi1 (t + h) - 2 * chi1 t + chi1 (t - h)| ≤ 24 * h ^ 2 := by
  rw [abs_le] at hh
  rcases le_total 0 t with ht | ht
  · rw [chi1_eq_gp (by linarith), chi1_eq_gp (by linarith), chi1_eq_gp (by linarith)]
    exact gp_second t h
  · rw [chi1_eq_gm (by linarith), chi1_eq_gm (by linarith), chi1_eq_gm (by linarith)]
    exact gm_second t h

/-! ### The cutoff on `ℤ⁴` -/

/-- `χ(n) = Π_μ χ₁((n_μ - y_μ)/K)`: in the units of the lattice `ηℤ⁴` and with `a = Kη`, this is
`Π_μ χ₁((x_μ - y_μ)/a)`. -/
def chiK (K : ℕ) (y n : Fin 4 → ℤ) : ℝ := ∏ μ, chi1 (((n μ - y μ : ℤ) : ℝ) / K)

variable {K : ℕ}

lemma chiK_nonneg (y n : Fin 4 → ℤ) : 0 ≤ chiK K y n := Finset.prod_nonneg fun _ _ => chi1_nonneg _

lemma chiK_le_one (y n : Fin 4 → ℤ) : chiK K y n ≤ 1 :=
  Finset.prod_le_one₀ (fun _ _ => chi1_nonneg _) fun _ _ => chi1_le_one _

lemma chiK_eq_one (hK : 1 ≤ K) {y n : Fin 4 → ℤ} (h : ∀ μ, |((n μ - y μ : ℤ) : ℝ)| ≤ 2 * K) :
    chiK K y n = 1 := by
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  refine Finset.prod_eq_one fun μ _ => chi1_eq_one ?_
  rw [abs_div, abs_of_pos hK', div_le_iff₀ hK']; linarith [h μ]

lemma abs_lt_of_chiK_ne_zero (hK : 1 ≤ K) {y n : Fin 4 → ℤ} (h : chiK K y n ≠ 0) (μ : Fin 4) :
    |((n μ - y μ : ℤ) : ℝ)| < 5 / 2 * K := by
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  by_contra h'
  push_neg at h'
  apply h
  refine Finset.prod_eq_zero (Finset.mem_univ μ) (chi1_eq_zero ?_)
  rw [abs_div, abs_of_pos hK', le_div_iff₀ hK']; linarith

/-- Moving the point in the direction `ν` changes only the factor of `ν`. -/
lemma chiK_shift (y n : Fin 4 → ℤ) (ν : Fin 4) (c : ℤ) :
    chiK K y (n + c • e4 ν) = chi1 (((n ν - y ν : ℤ) : ℝ) / K + c / K) *
      ∏ μ ∈ Finset.univ.erase ν, chi1 (((n μ - y μ : ℤ) : ℝ) / K) := by
  unfold chiK
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ ν)]
  congr 1
  · simp only [Pi.add_apply, Pi.smul_apply, e4, Pi.single_eq_same, smul_eq_mul, mul_one]
    push_cast; ring
  · refine Finset.prod_congr rfl fun μ hμ => ?_
    have hne : μ ≠ ν := Finset.ne_of_mem_erase hμ
    simp [e4, Pi.single_eq_of_ne hne]

lemma chiK_eq_mul (y n : Fin 4 → ℤ) (ν : Fin 4) :
    chiK K y n = chi1 (((n ν - y ν : ℤ) : ℝ) / K) * ∏ μ ∈ Finset.univ.erase ν, chi1 (((n μ - y μ : ℤ) : ℝ) / K) := by
  have := chiK_shift (K := K) y n ν 0
  simpa using this

lemma prod_erase_mem (y n : Fin 4 → ℤ) (ν : Fin 4) :
    0 ≤ ∏ μ ∈ Finset.univ.erase ν, chi1 (((n μ - y μ : ℤ) : ℝ) / K) ∧
      ∏ μ ∈ Finset.univ.erase ν, chi1 (((n μ - y μ : ℤ) : ℝ) / K) ≤ 1 :=
  ⟨Finset.prod_nonneg fun _ _ => chi1_nonneg _,
    Finset.prod_le_one₀ (fun _ _ => chi1_nonneg _) fun _ _ => chi1_le_one _⟩

/-- `|χ(n ± e_ν) - χ(n)| ≤ 3/K`. -/
lemma abs_chiK_shift_sub_le (hK : 1 ≤ K) (y n : Fin 4 → ℤ) (ν : Fin 4) (c : ℤ) (hc : |(c : ℝ)| ≤ 1) :
    |chiK K y (n + c • e4 ν) - chiK K y n| ≤ 3 / K := by
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  rw [chiK_shift, chiK_eq_mul y n ν, ← sub_mul, abs_mul]
  obtain ⟨p0, p1⟩ := prod_erase_mem (K := K) y n ν
  rw [abs_of_nonneg p0]
  have h := chi1_lip (((n ν - y ν : ℤ) : ℝ) / K + c / K) (((n ν - y ν : ℤ) : ℝ) / K)
  rw [add_sub_cancel_left, abs_div, abs_of_pos hK'] at h
  calc _ ≤ 3 * (|(c : ℝ)| / K) * 1 := mul_le_mul h p1 p0 (by positivity)
    _ ≤ 3 / K := by rw [mul_one, mul_div_assoc']; exact div_le_div_of_nonneg_right (by linarith) hK'.le

/-- `|χ(n + e_ν) - 2χ(n) + χ(n - e_ν)| ≤ 24/K²`. -/
lemma abs_chiK_second_le (hK : 1 ≤ K) (y n : Fin 4 → ℤ) (ν : Fin 4) :
    |chiK K y (n + e4 ν) - 2 * chiK K y n + chiK K y (n - e4 ν)| ≤ 24 / (K : ℝ) ^ 2 := by
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  have e1 : n + e4 ν = n + (1 : ℤ) • e4 ν := by simp
  have e2 : n - e4 ν = n + (-1 : ℤ) • e4 ν := by simp [sub_eq_add_neg]
  rw [e1, e2, chiK_shift, chiK_shift, chiK_eq_mul y n ν]
  obtain ⟨p0, p1⟩ := prod_erase_mem (K := K) y n ν
  set t := ((n ν - y ν : ℤ) : ℝ) / K
  set P := ∏ μ ∈ Finset.univ.erase ν, chi1 (((n μ - y μ : ℤ) : ℝ) / K)
  have hh : |(1 : ℝ) / K| ≤ 1 := by
    rw [abs_of_pos (by positivity), div_le_one hK']; exact_mod_cast hK
  have h := chi1_second (t := t) (h := 1 / K) hh
  have e3 : t + ((-1 : ℤ) : ℝ) / K = t - 1 / K := by push_cast; ring
  have e4' : t + ((1 : ℤ) : ℝ) / K = t + 1 / K := by push_cast; ring
  rw [e3, e4', show chi1 (t + 1 / K) * P - 2 * (chi1 t * P) + chi1 (t - 1 / K) * P =
      (chi1 (t + 1 / K) - 2 * chi1 t + chi1 (t - 1 / K)) * P by ring, abs_mul, abs_of_nonneg p0]
  calc _ ≤ (24 : ℝ) * (1 / (K : ℝ)) ^ 2 * 1 := mul_le_mul h p1 p0 (by positivity)
    _ = 24 / (K : ℝ) ^ 2 := by ring

/-- `|χ(n + m) - χ(n)| ≤ 3|m|₁/K`. -/
lemma abs_chiK_add_sub_le (hK : 1 ≤ K) (y n m : Fin 4 → ℤ) :
    |chiK K y (n + m) - chiK K y n| ≤ 3 / K * l1 m := by
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  unfold chiK
  refine (PartitionUnity.prod4_lip (fun _ => chi1_nonneg _) (fun _ => chi1_le_one _)
    (fun _ => chi1_nonneg _) (fun _ => chi1_le_one _)).trans ?_
  unfold l1
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun μ _ => ?_
  have h := chi1_lip (((n μ + m μ - y μ : ℤ) : ℝ) / K) (((n μ - y μ : ℤ) : ℝ) / K)
  simp only [Pi.add_apply] at h ⊢
  refine h.trans (le_of_eq ?_)
  rw [← sub_div, abs_div, abs_of_pos hK']
  push_cast
  rw [show (n μ : ℝ) + m μ - y μ - (n μ - y μ) = m μ by ring]
  ring

end InteriorSchauder
end CoreLean

end
