/-
`lem:local-laplacian` of BALABAN_CORE.tex (`0580551bf179`), the step "The cut-off".

The lattice is `εℤ⁴`, its points `εn` indexed by `n ∈ ℤ⁴` as in `HeatOperator`; the centre is `x₀ = εn₀`, the
coordinates of a point relative to it are `t_μ(n) = ε(n_μ - n₀_μ)`, and `Q_r` is `InQr ε n₀ r`.

* `chiR r t = 1 - σ(3(|t| - r))`, with the smooth step `σ` of `InteriorCutoff` (`σ = S` on `[0, 1]`, `S(s) = 3s² - 2s³`):
  the core's `χ₁`. It is `1` for `|t| ≤ r` and `0` for `|t| ≥ r + 1/3`, takes values in `[0, 1]`, has the derivative
  `dchi r` (`hasDerivAt_chiR`, for `r > 0`) with `|dchi| ≤ 9/2` and the Lipschitz constant `54` (`dchi_lip`).
* `chiL ε r n₀ n = Π_μ χ₁(t_μ(n))`: the core's `χ`; `|∂_μχ| ≤ 9/2` (`abs_dfw_chiL`), `|∂^*_μ∂_μχ| ≤ 54`
  (`abs_dbw_dfw_chiL`), `∂_μχ` is Lipschitz for `|·|₁` with the constant `54` (`dfw_chiL_lip`), `χ` and
  `χ(· + εe_μ)` with the constant `9/2` (`chiL_lip`); the supports (`chiL_supp`, `dfw_chiL_supp`, `dbw_dfw_chiL_supp`,
  `psi_supp`) for `ε ≤ 1/3`.
-/
import CoreLean.InteriorCutoff
import CoreLean.BlockPartition

open Finset

noncomputable section

namespace CoreLean
namespace LocalLaplacian

open InteriorSchauder

/-! ### One variable -/

/-- `u ↦ 1 - σ(3(u - r))`. -/
def fr (r u : ℝ) : ℝ := 1 - sig (3 * (u - r))

/-- Its derivative `-3σ'(3(u - r))`. -/
def dfr (r u : ℝ) : ℝ := -(qs (3 * (u - r)) * 3)

lemma hasDerivAt_fr (r u : ℝ) : HasDerivAt (fr r) (dfr r u) u := by
  have h1 : HasDerivAt (fun u => 3 * (u - r)) 3 u := by
    simpa using ((hasDerivAt_id u).sub_const r).const_mul 3
  exact ((hasDerivAt_sig _).comp u h1).const_sub 1

lemma dfr_eq_zero {r u : ℝ} (h : u ≤ r) : dfr r u = 0 := by
  unfold dfr; rw [qs_eq_zero_of_nonpos (by linarith)]; ring

lemma abs_dfr_le (r u : ℝ) : |dfr r u| ≤ 9 / 2 := by
  unfold dfr
  rw [abs_neg, abs_mul, abs_of_nonneg (qs_nonneg _)]
  have := qs_le (3 * (u - r))
  norm_num; linarith

lemma dfr_lip (r u v : ℝ) : |dfr r u - dfr r v| ≤ 54 * |u - v| := by
  unfold dfr
  have h := qs_lip (3 * (u - r)) (3 * (v - r))
  rw [show 3 * (u - r) - 3 * (v - r) = 3 * (u - v) by ring, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3)] at h
  rw [show -(qs (3 * (u - r)) * 3) - -(qs (3 * (v - r)) * 3) = -(3 * (qs (3 * (u - r)) - qs (3 * (v - r)))) by ring,
    abs_neg, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
  linarith

lemma fr_eq_one {r u : ℝ} (h : u ≤ r) : fr r u = 1 := by
  unfold fr; rw [sig_eq_zero (by linarith)]; ring

lemma fr_eq_zero {r u : ℝ} (h : r + 1 / 3 ≤ u) : fr r u = 0 := by
  unfold fr; rw [sig_eq_one (by linarith)]; ring

/-- **The cut-off** `χ₁(t) = 1 - σ(3(|t| - r))`. -/
def chiR (r t : ℝ) : ℝ := fr r |t|

/-- Its derivative. -/
def dchi (r t : ℝ) : ℝ := if 0 ≤ t then dfr r t else -dfr r (-t)

lemma chiR_nonneg (r t : ℝ) : 0 ≤ chiR r t := by unfold chiR fr; linarith [sig_le_one (3 * (|t| - r))]

lemma chiR_le_one (r t : ℝ) : chiR r t ≤ 1 := by unfold chiR fr; linarith [sig_nonneg (3 * (|t| - r))]

lemma chiR_eq_one {r t : ℝ} (h : |t| ≤ r) : chiR r t = 1 := fr_eq_one h

lemma chiR_eq_zero {r t : ℝ} (h : r + 1 / 3 ≤ |t|) : chiR r t = 0 := fr_eq_zero h

lemma hasDerivAt_chiR {r : ℝ} (hr : 0 < r) (t : ℝ) : HasDerivAt (chiR r) (dchi r t) t := by
  rcases lt_trichotomy t 0 with ht | ht | ht
  · have h1 : HasDerivAt (fun t => fr r (-t)) (dfr r (-t) * (-1)) t :=
      (hasDerivAt_fr r (-t)).comp t (hasDerivAt_neg t)
    have e : dchi r t = dfr r (-t) * (-1) := by unfold dchi; rw [if_neg (not_le.2 ht)]; ring
    rw [e]
    refine h1.congr_of_eventuallyEq ?_
    filter_upwards [eventually_lt_nhds ht] with s hs
    unfold chiR; rw [abs_of_neg hs]
  · subst ht
    have e : dchi r 0 = 0 := by unfold dchi; rw [if_pos le_rfl]; exact dfr_eq_zero hr.le
    rw [e]
    refine (hasDerivAt_const (0 : ℝ) (1 : ℝ)).congr_of_eventuallyEq ?_
    have : ∀ᶠ s in nhds (0 : ℝ), |s| < r := by
      have h := (continuous_abs.tendsto (0 : ℝ)).eventually (eventually_lt_nhds (show |(0 : ℝ)| < r by simpa using hr))
      simpa using h
    filter_upwards [this] with s hs
    exact chiR_eq_one hs.le
  · have e : dchi r t = dfr r t := by unfold dchi; rw [if_pos ht.le]
    rw [e]
    refine (hasDerivAt_fr r t).congr_of_eventuallyEq ?_
    filter_upwards [eventually_gt_nhds ht] with s hs
    unfold chiR; rw [abs_of_pos hs]

lemma abs_dchi_le (r t : ℝ) : |dchi r t| ≤ 9 / 2 := by
  unfold dchi; split_ifs
  · exact abs_dfr_le r t
  · rw [abs_neg]; exact abs_dfr_le r (-t)

lemma dchi_lip {r : ℝ} (hr : 0 ≤ r) (t s : ℝ) : |dchi r t - dchi r s| ≤ 54 * |t - s| := by
  have h0 : dfr r 0 = 0 := dfr_eq_zero hr
  unfold dchi
  split_ifs with h1 h2 h2
  · exact dfr_lip r t s
  · push_neg at h2
    have a1 := dfr_lip r t 0
    have a2 := dfr_lip r (-s) 0
    rw [h0, sub_zero, sub_zero, abs_of_nonneg h1] at a1
    rw [h0, sub_zero, sub_zero, abs_of_pos (by linarith : 0 < -s)] at a2
    rw [sub_neg_eq_add, abs_of_nonneg (by linarith : 0 ≤ t - s)]
    calc |dfr r t + dfr r (-s)| ≤ |dfr r t| + |dfr r (-s)| := abs_add_le _ _
      _ ≤ 54 * t + 54 * -s := add_le_add a1 a2
      _ = 54 * (t - s) := by ring
  · push_neg at h1
    have a1 := dfr_lip r (-t) 0
    have a2 := dfr_lip r s 0
    rw [h0, sub_zero, sub_zero, abs_of_pos (by linarith : 0 < -t)] at a1
    rw [h0, sub_zero, sub_zero, abs_of_nonneg h2] at a2
    rw [show -dfr r (-t) - dfr r s = -(dfr r (-t) + dfr r s) by ring, abs_neg,
      abs_of_nonpos (by linarith : t - s ≤ 0)]
    calc |dfr r (-t) + dfr r s| ≤ |dfr r (-t)| + |dfr r s| := abs_add_le _ _
      _ ≤ 54 * -t + 54 * s := add_le_add a1 a2
      _ = 54 * -(t - s) := by ring
  · have := dfr_lip r (-t) (-s)
    rw [show -dfr r (-t) - -dfr r (-s) = -(dfr r (-t) - dfr r (-s)) by ring, abs_neg,
      show -t - -s = -(t - s) by ring, abs_neg] at *
    exact this

lemma chiR_lip {r : ℝ} (hr : 0 < r) (s t : ℝ) : |chiR r s - chiR r t| ≤ 9 / 2 * |s - t| :=
  lip_of_deriv (hasDerivAt_chiR hr) (abs_dchi_le r) s t

/-- The mixed difference: `|χ₁(t + h) - χ₁(t) - (χ₁(s + h) - χ₁(s))| ≤ 54|h||t - s|`. -/
lemma chiR_mixed {r : ℝ} (hr : 0 < r) (t s h : ℝ) :
    |chiR r (t + h) - chiR r t - (chiR r (s + h) - chiR r s)| ≤ 54 * |h| * |t - s| := by
  have hdG : ∀ x, HasDerivAt (fun x => chiR r (x + h) - chiR r x) (dchi r (x + h) - dchi r x) x := fun x =>
    ((hasDerivAt_chiR hr (x + h)).comp_add_const x h).sub (hasDerivAt_chiR hr x)
  have hb : ∀ x, |dchi r (x + h) - dchi r x| ≤ 54 * |h| := fun x => by
    have := dchi_lip hr.le (x + h) x; rwa [add_sub_cancel_left] at this
  exact lip_of_deriv hdG hb t s

lemma chiR_second {r : ℝ} (hr : 0 < r) (t h : ℝ) :
    |chiR r (t + h) - 2 * chiR r t + chiR r (t - h)| ≤ 54 * h ^ 2 :=
  second_of_deriv_lip (hasDerivAt_chiR hr) (dchi_lip hr.le) t h

/-! ### Four variables -/

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The coordinate `t_μ(n) = ε(n_μ - n₀_μ)`. -/
def tc (ε : ℝ) (n₀ n : Fin 4 → ℤ) (μ : Fin 4) : ℝ := ε * ((n μ - n₀ μ : ℤ) : ℝ)

/-- `Q_r = {εn | |εn - x₀|_∞ ≤ r}`. -/
def InQr (ε : ℝ) (n₀ : Fin 4 → ℤ) (r : ℝ) (n : Fin 4 → ℤ) : Prop := ∀ μ, |tc ε n₀ n μ| ≤ r

/-- **The cut-off** `χ(n) = Π_μ χ₁(t_μ(n))`. -/
def chiL (ε r : ℝ) (n₀ n : Fin 4 → ℤ) : ℝ := ∏ μ, chiR r (tc ε n₀ n μ)

variable {ε r : ℝ} {n₀ : Fin 4 → ℤ}

lemma tc_add_e (n : Fin 4 → ℤ) (μ ν : Fin 4) (c : ℤ) :
    tc ε n₀ (n + c • e4 μ) ν = tc ε n₀ n ν + (if ν = μ then ε * c else 0) := by
  unfold tc
  by_cases h : ν = μ
  · subst h; simp only [Pi.add_apply, Pi.smul_apply, e4, Pi.single_eq_same, smul_eq_mul, mul_one, if_true]
    push_cast; ring
  · simp [e4, Pi.single_eq_of_ne h, h]

lemma tc_sub (n m : Fin 4 → ℤ) (μ : Fin 4) : tc ε n₀ n μ - tc ε n₀ m μ = ε * ((n μ - m μ : ℤ) : ℝ) := by
  unfold tc; push_cast; ring

lemma chiL_nonneg (n : Fin 4 → ℤ) : 0 ≤ chiL ε r n₀ n := prod_nonneg fun _ _ => chiR_nonneg _ _

lemma chiL_le_one (n : Fin 4 → ℤ) : chiL ε r n₀ n ≤ 1 :=
  prod_le_one₀ (fun _ _ => chiR_nonneg _ _) fun _ _ => chiR_le_one _ _

lemma chiL_eq_one {n : Fin 4 → ℤ} (h : InQr ε n₀ r n) : chiL ε r n₀ n = 1 :=
  prod_eq_one fun μ _ => chiR_eq_one (h μ)

lemma chiL_supp {n : Fin 4 → ℤ} (h : chiL ε r n₀ n ≠ 0) (μ : Fin 4) : |tc ε n₀ n μ| < r + 1 / 3 := by
  by_contra h'
  exact h (prod_eq_zero (mem_univ μ) (chiR_eq_zero (not_lt.1 h')))

/-- The factors other than the one of `μ`. -/
def pe (ε r : ℝ) (n₀ n : Fin 4 → ℤ) (μ : Fin 4) : ℝ := ∏ ν ∈ univ.erase μ, chiR r (tc ε n₀ n ν)

lemma pe_mem (n : Fin 4 → ℤ) (μ : Fin 4) : 0 ≤ pe ε r n₀ n μ ∧ pe ε r n₀ n μ ≤ 1 :=
  ⟨prod_nonneg fun _ _ => chiR_nonneg _ _, prod_le_one₀ (fun _ _ => chiR_nonneg _ _) fun _ _ => chiR_le_one _ _⟩

lemma chiL_eq_mul (n : Fin 4 → ℤ) (μ : Fin 4) : chiL ε r n₀ n = chiR r (tc ε n₀ n μ) * pe ε r n₀ n μ := by
  unfold chiL pe; rw [← mul_prod_erase _ _ (mem_univ μ)]

lemma pe_shift (n : Fin 4 → ℤ) (μ : Fin 4) (c : ℤ) : pe ε r n₀ (n + c • e4 μ) μ = pe ε r n₀ n μ := by
  unfold pe
  refine prod_congr rfl fun ν hν => ?_
  rw [tc_add_e, if_neg (ne_of_mem_erase hν), add_zero]

lemma chiL_shift (n : Fin 4 → ℤ) (μ : Fin 4) (c : ℤ) :
    chiL ε r n₀ (n + c • e4 μ) = chiR r (tc ε n₀ n μ + ε * c) * pe ε r n₀ n μ := by
  rw [chiL_eq_mul _ μ, pe_shift, tc_add_e, if_pos rfl]

lemma add_e4 (n : Fin 4 → ℤ) (μ : Fin 4) : n + e4 μ = n + (1 : ℤ) • e4 μ := by simp

lemma sub_e4 (n : Fin 4 → ℤ) (μ : Fin 4) : n - e4 μ = n + (-1 : ℤ) • e4 μ := by simp [sub_eq_add_neg]

/-- `∂_μχ = ε⁻¹(χ₁(t_μ + ε) - χ₁(t_μ))` times the other factors. -/
lemma dfw_chiL (n : Fin 4 → ℤ) (μ : Fin 4) :
    dfw ε μ (chiL ε r n₀) n = ε⁻¹ * (chiR r (tc ε n₀ n μ + ε) - chiR r (tc ε n₀ n μ)) * pe ε r n₀ n μ := by
  unfold dfw
  rw [add_e4, chiL_shift, chiL_eq_mul n μ, smul_eq_mul]; push_cast; ring

lemma abs_dfw_chiL (hε : 0 < ε) (hr : 0 < r) (n : Fin 4 → ℤ) (μ : Fin 4) :
    |dfw ε μ (chiL ε r n₀) n| ≤ 9 / 2 := by
  rw [dfw_chiL, abs_mul, abs_mul, abs_of_pos (inv_pos.2 hε)]
  obtain ⟨p0, p1⟩ := pe_mem (ε := ε) (r := r) (n₀ := n₀) n μ
  have h := chiR_lip hr (tc ε n₀ n μ + ε) (tc ε n₀ n μ)
  rw [add_sub_cancel_left, abs_of_pos hε] at h
  rw [abs_of_nonneg p0]
  calc ε⁻¹ * |chiR r (tc ε n₀ n μ + ε) - chiR r (tc ε n₀ n μ)| * pe ε r n₀ n μ
      ≤ ε⁻¹ * (9 / 2 * ε) * 1 := by gcongr
    _ = 9 / 2 := by field_simp

lemma abs_dbw_dfw_chiL (hε : 0 < ε) (hr : 0 < r) (n : Fin 4 → ℤ) (μ : Fin 4) :
    |dbw ε μ (dfw ε μ (chiL ε r n₀)) n| ≤ 54 := by
  have e : dbw ε μ (dfw ε μ (chiL ε r n₀)) n = -((ε ^ 2)⁻¹ * (chiR r (tc ε n₀ n μ + ε) -
      2 * chiR r (tc ε n₀ n μ) + chiR r (tc ε n₀ n μ - ε)) * pe ε r n₀ n μ) := by
    unfold dbw
    rw [dfw_chiL, dfw_chiL, sub_e4, pe_shift, tc_add_e, if_pos rfl, smul_eq_mul]
    have : tc ε n₀ n μ + ε * ((-1 : ℤ) : ℝ) + ε = tc ε n₀ n μ := by push_cast; ring
    rw [this]
    field_simp
    push_cast; ring
  rw [e, abs_neg, abs_mul, abs_mul, abs_of_pos (by positivity : 0 < (ε ^ 2)⁻¹)]
  obtain ⟨p0, p1⟩ := pe_mem (ε := ε) (r := r) (n₀ := n₀) n μ
  rw [abs_of_nonneg p0]
  have h := chiR_second hr (tc ε n₀ n μ) ε
  calc (ε ^ 2)⁻¹ * |chiR r (tc ε n₀ n μ + ε) - 2 * chiR r (tc ε n₀ n μ) + chiR r (tc ε n₀ n μ - ε)| *
        pe ε r n₀ n μ ≤ (ε ^ 2)⁻¹ * (54 * ε ^ 2) * 1 := by gcongr
    _ = 54 := by field_simp

/-- `|χ(n) - χ(n')| ≤ (9/2)ε|n - n'|₁`. -/
lemma chiL_lip (hr : 0 < r) (n n' : Fin 4 → ℤ) : |chiL ε r n₀ n - chiL ε r n₀ n'| ≤ 9 / 2 * (|ε| * l1 (n - n')) := by
  unfold chiL
  refine (Blocks.DomSeq.abs_prod_sub_prod_le univ _ _ (fun _ => chiR_nonneg _ _) (fun _ => chiR_le_one _ _)
    (fun _ => chiR_nonneg _ _) (fun _ => chiR_le_one _ _)).trans ?_
  unfold l1
  rw [mul_sum, mul_sum]
  refine sum_le_sum fun μ _ => ?_
  refine (chiR_lip hr _ _).trans (le_of_eq ?_)
  rw [tc_sub, abs_mul]; simp only [Pi.sub_apply]

/-- `|∂_μχ(n) - ∂_μχ(n')| ≤ 54ε|n - n'|₁`. -/
lemma dfw_chiL_lip (hε : 0 < ε) (hr : 0 < r) (n n' : Fin 4 → ℤ) (μ : Fin 4) :
    |dfw ε μ (chiL ε r n₀) n - dfw ε μ (chiL ε r n₀) n'| ≤ 54 * (ε * l1 (n - n')) := by
  rw [dfw_chiL, dfw_chiL]
  set D := ε⁻¹ * (chiR r (tc ε n₀ n μ + ε) - chiR r (tc ε n₀ n μ))
  set D' := ε⁻¹ * (chiR r (tc ε n₀ n' μ + ε) - chiR r (tc ε n₀ n' μ))
  obtain ⟨p0, p1⟩ := pe_mem (ε := ε) (r := r) (n₀ := n₀) n μ
  obtain ⟨p0', p1'⟩ := pe_mem (ε := ε) (r := r) (n₀ := n₀) n' μ
  have hD' : |D'| ≤ 9 / 2 := by
    have h := chiR_lip hr (tc ε n₀ n' μ + ε) (tc ε n₀ n' μ)
    rw [add_sub_cancel_left, abs_of_pos hε] at h
    simp only [D', abs_mul, abs_of_pos (inv_pos.2 hε)]
    calc ε⁻¹ * |chiR r (tc ε n₀ n' μ + ε) - chiR r (tc ε n₀ n' μ)| ≤ ε⁻¹ * (9 / 2 * ε) := by gcongr
      _ = 9 / 2 := by field_simp
  have hDD : |D - D'| ≤ 54 * (ε * |((n μ - n' μ : ℤ) : ℝ)|) := by
    have h := chiR_mixed hr (tc ε n₀ n μ) (tc ε n₀ n' μ) ε
    rw [tc_sub, abs_of_pos hε, abs_mul, abs_of_pos hε] at h
    simp only [D, D', ← mul_sub, abs_mul, abs_of_pos (inv_pos.2 hε)]
    calc ε⁻¹ * |chiR r (tc ε n₀ n μ + ε) - chiR r (tc ε n₀ n μ) - (chiR r (tc ε n₀ n' μ + ε) - chiR r (tc ε n₀ n' μ))|
        ≤ ε⁻¹ * (54 * ε * (ε * |((n μ - n' μ : ℤ) : ℝ)|)) := by gcongr
      _ = 54 * (ε * |((n μ - n' μ : ℤ) : ℝ)|) := by field_simp
  have hP : |pe ε r n₀ n μ - pe ε r n₀ n' μ| ≤ 9 / 2 * (ε * ∑ ν ∈ univ.erase μ, |((n ν - n' ν : ℤ) : ℝ)|) := by
    unfold pe
    refine (Blocks.DomSeq.abs_prod_sub_prod_le _ _ _ (fun _ => chiR_nonneg _ _) (fun _ => chiR_le_one _ _)
      (fun _ => chiR_nonneg _ _) (fun _ => chiR_le_one _ _)).trans ?_
    rw [mul_sum, mul_sum]
    refine sum_le_sum fun ν _ => ?_
    refine (chiR_lip hr _ _).trans (le_of_eq ?_)
    rw [tc_sub, abs_mul, abs_of_pos hε]
  have hsplit : l1 (n - n') = |((n μ - n' μ : ℤ) : ℝ)| + ∑ ν ∈ univ.erase μ, |((n ν - n' ν : ℤ) : ℝ)| := by
    unfold l1; rw [← add_sum_erase _ _ (mem_univ μ)]; simp only [Pi.sub_apply]
  have hS : 0 ≤ ∑ ν ∈ univ.erase μ, |((n ν - n' ν : ℤ) : ℝ)| := sum_nonneg fun _ _ => abs_nonneg _
  calc |D * pe ε r n₀ n μ - D' * pe ε r n₀ n' μ|
      = |(D - D') * pe ε r n₀ n μ + D' * (pe ε r n₀ n μ - pe ε r n₀ n' μ)| := by ring_nf
    _ ≤ |D - D'| * 1 + 9 / 2 * |pe ε r n₀ n μ - pe ε r n₀ n' μ| := by
        refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [abs_mul, abs_of_nonneg p0]; exact mul_le_mul_of_nonneg_left p1 (abs_nonneg _)
        · rw [abs_mul]; exact mul_le_mul_of_nonneg_right hD' (abs_nonneg _)
    _ ≤ 54 * (ε * |((n μ - n' μ : ℤ) : ℝ)|) + 9 / 2 * (9 / 2 * (ε * ∑ ν ∈ univ.erase μ, |((n ν - n' ν : ℤ) : ℝ)|)) :=
        add_le_add (by rw [mul_one]; exact hDD) (mul_le_mul_of_nonneg_left hP (by norm_num))
    _ ≤ 54 * (ε * l1 (n - n')) := by
        rw [hsplit]; nlinarith [mul_nonneg hε.le hS]

lemma tc_near (hε : 0 < ε) (n : Fin 4 → ℤ) (μ ν : Fin 4) (c : ℤ) (hc : |(c : ℝ)| ≤ 1) :
    |tc ε n₀ n ν| ≤ |tc ε n₀ (n + c • e4 μ) ν| + ε := by
  rw [tc_add_e]
  split_ifs
  · have h := abs_sub_abs_le_abs_sub (tc ε n₀ n ν) (tc ε n₀ n ν + ε * c)
    rw [sub_add_cancel_left, abs_neg, abs_mul, abs_of_pos hε] at h
    nlinarith [abs_nonneg (c : ℝ)]
  · rw [add_zero]; linarith

/-- `∂_μχ(n) ≠ 0` only if `|t(n)|_∞ < r + 2/3`. -/
lemma dfw_chiL_supp (hε : 0 < ε) (hε3 : ε ≤ 1 / 3) {n : Fin 4 → ℤ} {μ : Fin 4}
    (h : dfw ε μ (chiL ε r n₀) n ≠ 0) (ν : Fin 4) : |tc ε n₀ n ν| < r + 2 / 3 := by
  by_cases h0 : chiL ε r n₀ n = 0
  · have h1 : chiL ε r n₀ (n + e4 μ) ≠ 0 := by
      intro h1; apply h; unfold dfw; rw [h0, h1]; simp
    have := chiL_supp h1 ν
    rw [add_e4] at this
    have := tc_near (n₀ := n₀) hε n μ ν 1 (by norm_num)
    linarith
  · have := chiL_supp h0 ν; linarith

/-- `∂^*_μ∂_μχ(n) ≠ 0` only if `|t(n)|_∞ < r + 2/3`. -/
lemma dbw_dfw_chiL_supp (hε : 0 < ε) (hε3 : ε ≤ 1 / 3) {n : Fin 4 → ℤ} {μ : Fin 4}
    (h : dbw ε μ (dfw ε μ (chiL ε r n₀)) n ≠ 0) (ν : Fin 4) : |tc ε n₀ n ν| < r + 2 / 3 := by
  by_cases h0 : dfw ε μ (chiL ε r n₀) n = 0
  · have h1 : dfw ε μ (chiL ε r n₀) (n - e4 μ) ≠ 0 := by
      intro h1; apply h; unfold dbw; rw [h0, h1]; simp
    by_cases h2 : chiL ε r n₀ (n - e4 μ) = 0
    · have h3 : chiL ε r n₀ (n - e4 μ + e4 μ) ≠ 0 := by
        intro h3; apply h1; unfold dfw; rw [h2, h3]; simp
      rw [sub_add_cancel] at h3
      have := chiL_supp h3 ν; linarith
    · have := chiL_supp h2 ν
      rw [sub_e4] at this
      have := tc_near (n₀ := n₀) hε n μ ν (-1) (by norm_num)
      linarith
  · exact dfw_chiL_supp hε hε3 h0 ν

/-- `χ(n + e_μ) ≠ 0` only if `|t(n)|_∞ < r + 2/3`. -/
lemma chiL_add_supp (hε : 0 < ε) (hε3 : ε ≤ 1 / 3) {n : Fin 4 → ℤ} {μ : Fin 4}
    (h : chiL ε r n₀ (n + e4 μ) ≠ 0) (ν : Fin 4) : |tc ε n₀ n ν| < r + 2 / 3 := by
  have := chiL_supp h ν
  rw [add_e4] at this
  have := tc_near (n₀ := n₀) hε n μ ν 1 (by norm_num)
  linarith

/-- `ψ_μ(n) = ∂_μχ(n - e_μ) ≠ 0` only if `|t(n)|_∞ < r + 1`. -/
lemma psi_supp (hε : 0 < ε) (hε3 : ε ≤ 1 / 3) {n : Fin 4 → ℤ} {μ : Fin 4}
    (h : dfw ε μ (chiL ε r n₀) (n - e4 μ) ≠ 0) (ν : Fin 4) : |tc ε n₀ n ν| < r + 1 := by
  have := dfw_chiL_supp hε hε3 h ν
  rw [sub_e4] at this
  have := tc_near (n₀ := n₀) hε n μ ν (-1) (by norm_num)
  linarith

end LocalLaplacian
end CoreLean

end
