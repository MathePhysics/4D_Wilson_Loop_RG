/-
`lem:function-field` of BALABAN_CORE.tex (`a021c13be348`), the test of Schur and the constants of its proof.

* *The test of Schur with counted entries*: a kernel whose entries are at most `e`, with at most `n_R` nonvanishing
  entries in a row and at most `n_C` in a column, has the norm at most `√(n_Re·n_Ce)` (`schur_count`, from
  `schur_sqrt` of `Schur.lean`).
* `C_{1b}`: with `16L⁴` entries in a row, `8` in a column, and the entries `√N·L·C_QC_φL^{-4}` of `ˇℰ₁`,
  `√(16L⁴e·8e) ≤ 4√NC_QC_φ` for `L ≥ 3` (`constant_one`).
* `C_{0b}`: with `16` entries in a row, `8` in a column, and the entries `√N·19√N(C'_3 + 192)C_φL²ε_p` of `ℰ₀`,
  `√(16e·8e) ≤ 304NC_φ(C'_3 + 192)L²ε_p` (`constant_zero`).
* The transports along the paths `γ_{b,c'}`: `e^{96ε₀} - 1 ≤ 192ε₀` for `96ε₀ ≤ 1` (`transport_bound`).
-/
import CoreLean.Schur
import CoreLean.ProductExp

open Finset

noncomputable section

namespace CoreLean
namespace FunctionField

variable {X Y : Type*} [Fintype X] [Fintype Y] {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

lemma count_sum {Z : Type*} [Fintype Z] (g : Z → ℝ) (hg : ∀ z, 0 ≤ g z) {e : ℝ} (he : ∀ z, g z ≤ e) {n : ℕ}
    (hn : (univ.filter fun z => g z ≠ 0).card ≤ n) (he0 : 0 ≤ e) : ∑ z, g z ≤ n * e := by
  rw [← Finset.sum_filter_ne_zero]
  calc ∑ z ∈ univ.filter (fun z => g z ≠ 0), g z ≤ ∑ z ∈ univ.filter (fun z => g z ≠ 0), e :=
        Finset.sum_le_sum fun z _ => he z
    _ = (univ.filter fun z => g z ≠ 0).card * e := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ n * e := mul_le_mul_of_nonneg_right (by exact_mod_cast hn) he0

/-- **The test of Schur with counted entries**. -/
theorem schur_count (K : X → Y → E →L[ℂ] F) {e : ℝ} (he : 0 ≤ e) (nR nC : ℕ) (hK : ∀ x y, ‖K x y‖ ≤ e)
    (hrow : ∀ x, (univ.filter fun y => ‖K x y‖ ≠ 0).card ≤ nR)
    (hcol : ∀ y, (univ.filter fun x => ‖K x y‖ ≠ 0).card ≤ nC) (f : Y → E) :
    Real.sqrt (∑ x, ‖∑ y, K x y (f y)‖ ^ 2) ≤ Real.sqrt (nR * e * (nC * e)) * Real.sqrt (∑ y, ‖f y‖ ^ 2) := by
  have h := Schur.schur_sqrt (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) (fun _ => zero_le_one) (fun _ => zero_le_one) K
    (nR * e) (nC * e) (by positivity) (by positivity)
    (fun x => by simpa using count_sum (fun y => ‖K x y‖) (fun _ => norm_nonneg _) (hK x) (hrow x) he)
    (fun y => by simpa using count_sum (fun x => ‖K x y‖) (fun _ => norm_nonneg _) (fun x => hK x y) (hcol y) he) f
  simpa using h

/-- **`C_{1b}`**. -/
theorem constant_one {L N CQ Cφ : ℝ} (hL : 3 ≤ L) (hN : 0 ≤ N) (hQ : 0 ≤ CQ) (hφ : 0 ≤ Cφ) :
    Real.sqrt (16 * L ^ 4 * (Real.sqrt N * L * CQ * Cφ * L⁻¹ ^ 4) * (8 * (Real.sqrt N * L * CQ * Cφ * L⁻¹ ^ 4))) ≤
      4 * Real.sqrt N * CQ * Cφ := by
  have hL0 : 0 < L := by linarith
  set e := Real.sqrt N * CQ * Cφ
  have he : 0 ≤ e := by positivity
  have h1 : 16 * L ^ 4 * (Real.sqrt N * L * CQ * Cφ * L⁻¹ ^ 4) * (8 * (Real.sqrt N * L * CQ * Cφ * L⁻¹ ^ 4)) =
      (128 / L ^ 2) * e ^ 2 := by
    simp only [e]; field_simp; ring
  rw [h1, Real.sqrt_mul (by positivity), Real.sqrt_sq he]
  have h2 : Real.sqrt (128 / L ^ 2) ≤ 4 := by
    rw [Real.sqrt_le_left (by norm_num)]
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  calc Real.sqrt (128 / L ^ 2) * e ≤ 4 * e := mul_le_mul_of_nonneg_right h2 he
    _ = 4 * Real.sqrt N * CQ * Cφ := by simp only [e]; ring

/-- **`C_{0b}`**. -/
theorem constant_zero {N C3 Cφ L εp : ℝ} (hN : 0 ≤ N) (h3 : 0 ≤ C3) (hφ : 0 ≤ Cφ) (hεp : 0 ≤ εp) :
    Real.sqrt (16 * (Real.sqrt N * (19 * Real.sqrt N * (C3 + 192) * Cφ * L ^ 2 * εp)) *
      (8 * (Real.sqrt N * (19 * Real.sqrt N * (C3 + 192) * Cφ * L ^ 2 * εp)))) ≤
      304 * N * Cφ * (C3 + 192) * L ^ 2 * εp := by
  set e := Real.sqrt N * (19 * Real.sqrt N * (C3 + 192) * Cφ * L ^ 2 * εp)
  have he : e = 19 * N * (C3 + 192) * Cφ * L ^ 2 * εp := by
    simp only [e]
    have : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hN
    linear_combination (19 * (C3 + 192) * Cφ * L ^ 2 * εp) * this
  have he0 : 0 ≤ e := by rw [he]; positivity
  have h1 : 16 * e * (8 * e) = 128 * e ^ 2 := by ring
  rw [h1, Real.sqrt_mul (by norm_num), Real.sqrt_sq he0]
  have h2 : Real.sqrt 128 ≤ 16 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
  calc Real.sqrt 128 * e ≤ 16 * e := mul_le_mul_of_nonneg_right h2 he0
    _ = 304 * N * Cφ * (C3 + 192) * L ^ 2 * εp := by rw [he]; ring

/-- **The transports**: `e^{96ε₀} - 1 ≤ 192ε₀` for `0 ≤ 96ε₀ ≤ 1`. -/
theorem transport_bound {ε₀ : ℝ} (h0 : 0 ≤ ε₀) (h1 : 96 * ε₀ ≤ 1) : Real.exp (96 * ε₀) - 1 ≤ 192 * ε₀ := by
  have := exp_sub_one_le_two_mul' (t := 96 * ε₀) (by positivity) h1
  linarith

end FunctionField
end CoreLean

end
