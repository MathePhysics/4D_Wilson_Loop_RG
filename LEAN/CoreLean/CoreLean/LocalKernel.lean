/-
`lem:local-laplacian`(i) of BALABAN_CORE.tex (`0580551bf179`): the bounds of the heat kernel of unit spacing which give
the `L^{6/5}` bounds of the kernels of `G₁` and of its differences (with `lem:heat-kernel`(iv)).

* `heatKernel1_le_zero`, `heatKernel_le`: `q_s(n) ≤ q_s(0)` and `p_s(z) ≤ q_s(0)⁴` (`lem:heat-kernel`(iv), third bound).
* `sum_rpow_heatKernel_le`: `Σ_{z ∈ Z}p_s(z)^{6/5} ≤ (q_s(0)⁴)^{1/5}` for every finite `Z` (since `Σ_zp_s(z) = 1`).
* `sum_abs_diff_le`: `Σ_{z ∈ Z}|p_s(z + e_μ) - p_s(z)| ≤ 2q_s(0)` (`eq:heat-gradient`).
* `abs_diff_le`: `|p_s(z + e_μ) - p_s(z)| ≤ 2q_{s/2}(0)⁵`, from `p_s = p_{s/2} * p_{s/2}`.
* `sum_rpow_abs_diff_le`: `Σ_{z ∈ Z}|p_s(z + e_μ) - p_s(z)|^{6/5} ≤ (2q_{s/2}(0)⁵)^{1/5}·2q_s(0)`.
-/
import CoreLean.HeatOperator

open Finset Balaban.LatticeGreen

noncomputable section

namespace CoreLean
namespace LocalLaplacian

variable {s : ℝ}

lemma heatKernel1_le_zero (hs : 0 ≤ s) (n : ℤ) : heatKernel1 s n ≤ heatKernel1 s 0 := by
  have hnat : ∀ k : ℕ, heatKernel1 s (k : ℤ) ≤ heatKernel1 s 0 := fun k => by
    induction k with
    | zero => simp
    | succ k ih =>
      have := heatKernel1_antitone hs (Int.natCast_nonneg k)
      push_cast; linarith
  rcases le_or_gt 0 n with hn | hn
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hn; exact hnat k
  · have : n = -((-n).toNat : ℤ) := by rw [Int.toNat_of_nonneg (by linarith)]; ring
    rw [this, heatKernel1_neg]; exact hnat _

lemma heatKernel_le (hs : 0 ≤ s) (z : Fin 4 → ℤ) : heatKernel 4 s z ≤ heatKernel1 s 0 ^ 4 := by
  unfold heatKernel
  calc ∏ μ, heatKernel1 s (z μ) ≤ ∏ _μ : Fin 4, heatKernel1 s 0 :=
        Finset.prod_le_prod₀ (fun μ _ => heatKernel1_nonneg hs _) fun μ _ => heatKernel1_le_zero hs _
    _ = heatKernel1 s 0 ^ 4 := by simp

lemma sum_heatKernel_le (hs : 0 ≤ s) (Z : Finset (Fin 4 → ℤ)) : ∑ z ∈ Z, heatKernel 4 s z ≤ 1 :=
  sum_le_hasSum Z (fun z _ => heatKernel4_nonneg hs z) (hasSum_heatKernel4 hs)

/-- `x^{6/5} ≤ M^{1/5}x` for `0 ≤ x ≤ M`. -/
lemma rpow_six_fifths_le {x M : ℝ} (hx : 0 ≤ x) (hxM : x ≤ M) : x ^ (6 / 5 : ℝ) ≤ M ^ (1 / 5 : ℝ) * x := by
  rw [show (6 / 5 : ℝ) = 1 + 1 / 5 by norm_num, Real.rpow_add' hx (by norm_num), Real.rpow_one, mul_comm]
  exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hx hxM (by norm_num)) hx

theorem sum_rpow_heatKernel_le (hs : 0 ≤ s) (Z : Finset (Fin 4 → ℤ)) :
    ∑ z ∈ Z, heatKernel 4 s z ^ (6 / 5 : ℝ) ≤ (heatKernel1 s 0 ^ 4) ^ (1 / 5 : ℝ) := by
  calc ∑ z ∈ Z, heatKernel 4 s z ^ (6 / 5 : ℝ) ≤ ∑ z ∈ Z, (heatKernel1 s 0 ^ 4) ^ (1 / 5 : ℝ) * heatKernel 4 s z :=
        sum_le_sum fun z _ => rpow_six_fifths_le (heatKernel4_nonneg hs z) (heatKernel_le hs z)
    _ = (heatKernel1 s 0 ^ 4) ^ (1 / 5 : ℝ) * ∑ z ∈ Z, heatKernel 4 s z := by rw [mul_sum]
    _ ≤ (heatKernel1 s 0 ^ 4) ^ (1 / 5 : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left (sum_heatKernel_le hs Z) (by
          have := heatKernel1_nonneg hs 0; positivity)
    _ = _ := mul_one _

theorem sum_abs_diff_le (hs : 0 ≤ s) (Z : Finset (Fin 4 → ℤ)) (μ : Fin 4) :
    ∑ z ∈ Z, |heatKernel 4 s (z + e4 μ) - heatKernel 4 s z| ≤ 2 * heatKernel1 s 0 :=
  sum_le_hasSum Z (fun z _ => abs_nonneg _) (hasSum_abs_shift_sub hs μ)

/-- `|p_s(z + e_μ) - p_s(z)| ≤ 2q_{s/2}(0)⁵`. -/
theorem abs_diff_le (hs : 0 ≤ s) (z : Fin 4 → ℤ) (μ : Fin 4) :
    |heatKernel 4 s (z + e4 μ) - heatKernel 4 s z| ≤ 2 * heatKernel1 (s / 2) 0 ^ 5 := by
  have hs2 : 0 ≤ s / 2 := by linarith
  have e : s = s / 2 + s / 2 := by ring
  have h1 := hasSum_heatKernel_conv (d := 4) hs2 hs2 (z + e4 μ)
  have h2 := hasSum_heatKernel_conv (d := 4) hs2 hs2 z
  rw [← e] at h1 h2
  have h := h1.sub h2
  set q0 := heatKernel1 (s / 2) 0
  have hq0 : 0 ≤ q0 := heatKernel1_nonneg hs2 0
  -- the majorant
  have hg : HasSum (fun y : Fin 4 → ℤ => q0 ^ 4 * |heatKernel 4 (s / 2) (z - y + e4 μ) - heatKernel 4 (s / 2) (z - y)|)
      (q0 ^ 4 * (2 * q0)) := by
    refine HasSum.mul_left _ ?_
    have h0 := hasSum_abs_shift_sub (d := 4) hs2 μ
    have h1 := ((Equiv.subLeft z).hasSum_iff (f := fun w : Fin 4 → ℤ =>
      |heatKernel 4 (s / 2) (w + Pi.single μ 1) - heatKernel 4 (s / 2) w|)).mpr h0
    exact h1
  have hpt : ∀ y, |heatKernel 4 (s / 2) y * heatKernel 4 (s / 2) (z + e4 μ - y) -
      heatKernel 4 (s / 2) y * heatKernel 4 (s / 2) (z - y)| ≤
      q0 ^ 4 * |heatKernel 4 (s / 2) (z - y + e4 μ) - heatKernel 4 (s / 2) (z - y)| := fun y => by
    rw [← mul_sub, abs_mul, abs_of_nonneg (heatKernel4_nonneg hs2 y), show z + e4 μ - y = z - y + e4 μ by abel]
    exact mul_le_mul_of_nonneg_right (heatKernel_le hs2 y) (abs_nonneg _)
  have hup := hasSum_le (fun y => (abs_le.1 (hpt y)).2) h hg
  have hlo := hasSum_le (fun y => (abs_le.1 (hpt y)).1) hg.neg h
  rw [abs_le]
  constructor <;> linarith

theorem sum_rpow_abs_diff_le (hs : 0 ≤ s) (Z : Finset (Fin 4 → ℤ)) (μ : Fin 4) :
    ∑ z ∈ Z, |heatKernel 4 s (z + e4 μ) - heatKernel 4 s z| ^ (6 / 5 : ℝ) ≤
      (2 * heatKernel1 (s / 2) 0 ^ 5) ^ (1 / 5 : ℝ) * (2 * heatKernel1 s 0) := by
  have hq : 0 ≤ 2 * heatKernel1 (s / 2) 0 ^ 5 := by have := heatKernel1_nonneg (by linarith : 0 ≤ s / 2) 0; positivity
  calc _ ≤ ∑ z ∈ Z, (2 * heatKernel1 (s / 2) 0 ^ 5) ^ (1 / 5 : ℝ) * |heatKernel 4 s (z + e4 μ) - heatKernel 4 s z| :=
        sum_le_sum fun z _ => rpow_six_fifths_le (abs_nonneg _) (abs_diff_le hs z μ)
    _ = (2 * heatKernel1 (s / 2) 0 ^ 5) ^ (1 / 5 : ℝ) * ∑ z ∈ Z, |heatKernel 4 s (z + e4 μ) - heatKernel 4 s z| := by
        rw [mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_abs_diff_le hs Z μ) (by positivity)

end LocalLaplacian
end CoreLean

end
