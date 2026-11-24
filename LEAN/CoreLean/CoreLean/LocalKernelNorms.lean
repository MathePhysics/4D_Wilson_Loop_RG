/-
`lem:local-laplacian`(i) of BALABAN_CORE.tex (`0580551bf179`): the `L^{6/5}` bounds of the kernels of `G₁` and of its
differences, `‖g₁‖_{6/5} ≤ 1` and `‖𝒟g₁‖_{6/5} ≤ 5` in the core's normalisation. In the units of `εℤ⁴` the kernel of `G₁`
is `k = resKernel ε` (`(G₁F)(n) = Σ_zk(z)F(n - z)`), the core's `ε⁴g₁(εz)`, and the kernel of `∂_μG₁` is bounded by
`ε⁻¹dKer ε μ`, `dKer ε μ z = ∫_0^∞e^{-t}|p_{t/ε²}(z + e_μ) - p_{t/ε²}(z)|dt`; the bounds read
`(Σ_{z ∈ Z}k(z)^{6/5})^{5/6} ≤ ε^{2/3}` (`resKernel_l65`) and `(Σ_{z ∈ Z}dKer(z)^{6/5})^{5/6} ≤ 5ε^{5/3}` (`dKer_l65`)
for every finite `Z`.
-/
import CoreLean.LocalMinkowski
import CoreLean.ResolventEquation

open Finset MeasureTheory Set Balaban.LatticeGreen

noncomputable section

namespace CoreLean
namespace LocalLaplacian

variable {ε : ℝ}

/-- `dKer ε μ z = ∫_0^∞e^{-t}|p_{t/ε²}(z + e_μ) - p_{t/ε²}(z)|dt`. -/
def dKer (ε : ℝ) (μ : Fin 4) (z : Fin 4 → ℤ) : ℝ :=
  ∫ t in Ioi 0, Real.exp (-t) * |heatKernel 4 (t / ε ^ 2) (z + e4 μ) - heatKernel 4 (t / ε ^ 2) z|

lemma integrableOn_dKer (μ : Fin 4) (z : Fin 4 → ℤ) :
    IntegrableOn (fun t => Real.exp (-t) * |heatKernel 4 (t / ε ^ 2) (z + e4 μ) - heatKernel 4 (t / ε ^ 2) z|)
      (Ioi 0) := by
  refine Integrable.mono' (integrableOn_exp_neg.mul_const 2)
    ((Continuous.aestronglyMeasurable (by fun_prop)).mul
      ((((continuous_heatKernel (z + e4 μ)).comp (continuous_id.div_const _)).sub
        ((continuous_heatKernel z).comp (continuous_id.div_const _))).abs.aestronglyMeasurable)) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun t ht => ?_)
  have hs : 0 ≤ t / ε ^ 2 := by have : 0 < t := ht; positivity
  rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le (abs_nonneg _))]
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  have h1 := heatKernel4_le_one hs (z + e4 μ)
  have h2 := heatKernel4_le_one hs z
  have h3 := heatKernel4_nonneg hs (z + e4 μ)
  have h4 := heatKernel4_nonneg hs z
  rw [abs_le]; constructor <;> linarith

lemma dKer_nonneg (μ : Fin 4) (z : Fin 4 → ℤ) : 0 ≤ dKer ε μ z :=
  setIntegral_nonneg measurableSet_Ioi fun t _ => mul_nonneg (Real.exp_pos _).le (abs_nonneg _)

/-- `(Σ_z(cx_z)^{6/5})^{5/6} = c(Σ_zx_z^{6/5})^{5/6}` for `c, x ≥ 0`. -/
lemma l65_smul {ι : Type*} (Z : Finset ι) {c : ℝ} (hc : 0 ≤ c) (x : ι → ℝ) (hx : ∀ z ∈ Z, 0 ≤ x z) :
    (∑ z ∈ Z, (c * x z) ^ (6 / 5 : ℝ)) ^ (5 / 6 : ℝ) = c * (∑ z ∈ Z, x z ^ (6 / 5 : ℝ)) ^ (5 / 6 : ℝ) := by
  rw [sum_congr rfl fun z hz => Real.mul_rpow hc (hx z hz), ← mul_sum,
    Real.mul_rpow (Real.rpow_nonneg hc _) (sum_nonneg fun z hz => Real.rpow_nonneg (hx z hz) _), ← Real.rpow_mul hc]
  norm_num

lemma c_rpow_le : (Real.sqrt Real.pi / 4) ^ (2 / 3 : ℝ) ≤ 2 / 3 := by
  have h0 : 0 ≤ Real.sqrt Real.pi / 4 := by positivity
  refine (Real.rpow_le_rpow h0 sqrt_pi_div_four_le (by norm_num)).trans ?_
  have hx0 : 0 ≤ (9 / 20 : ℝ) ^ (2 / 3 : ℝ) := Real.rpow_nonneg (by norm_num) _
  refine le_of_pow_le_pow_left₀ (n := 3) (by norm_num) (by norm_num) ?_
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num

/-- **`‖g₁‖_{6/5} ≤ 1`**. -/
theorem resKernel_l65 (hε : 0 < ε) (Z : Finset (Fin 4 → ℤ)) :
    (∑ z ∈ Z, resKernel ε z ^ (6 / 5 : ℝ)) ^ (5 / 6 : ℝ) ≤ ε ^ (2 / 3 : ℝ) := by
  set c := Real.sqrt Real.pi / 4
  have hc0 : 0 ≤ c := by positivity
  set C := c ^ (2 / 3 : ℝ) * ε ^ (2 / 3 : ℝ)
  have hC0 : 0 ≤ C := by positivity
  have hmk := minkowski_65 Z (fun z t => Real.exp (-t) * heatKernel 4 (t / ε ^ 2) z)
    (fun z t ht => mul_nonneg (Real.exp_pos _).le (heatKernel4_nonneg (by positivity) z))
    (fun z => integrableOn_exp_neg_heatKernel z) (fun t => C * (Real.exp (-t) * t ^ ((2 / 3 : ℝ) - 1)))
    ((integrableOn_exp_neg_rpow (by norm_num)).const_mul C) (fun t ht => by
      have hs : 0 ≤ t / ε ^ 2 := by positivity
      have he := (Real.exp_pos (-t)).le
      rw [l65_smul Z he _ fun z _ => heatKernel4_nonneg hs z]
      have hq0 := heatKernel1_nonneg hs 0
      have h1 : (∑ z ∈ Z, heatKernel 4 (t / ε ^ 2) z ^ (6 / 5 : ℝ)) ^ (5 / 6 : ℝ) ≤ heatKernel1 (t / ε ^ 2) 0 ^ (2 / 3 : ℝ) := by
        refine (Real.rpow_le_rpow (sum_nonneg fun z _ => Real.rpow_nonneg (heatKernel4_nonneg hs z) _)
          (sum_rpow_heatKernel_le hs Z) (by norm_num)).trans (le_of_eq ?_)
        rw [← Real.rpow_natCast, ← Real.rpow_mul hq0, ← Real.rpow_mul hq0]; norm_num
      have h2 : heatKernel1 (t / ε ^ 2) 0 ^ (2 / 3 : ℝ) ≤ C * t ^ ((2 / 3 : ℝ) - 1) := by
        refine (Real.rpow_le_rpow hq0 (origin_le hε ht) (by norm_num)).trans (le_of_eq ?_)
        rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg ht.le _), Real.mul_rpow (by positivity) hε.le,
          ← Real.rpow_mul ht.le, show (-(1 / 2 : ℝ)) * (2 / 3) = (2 / 3 : ℝ) - 1 by norm_num]
      calc Real.exp (-t) * (∑ z ∈ Z, heatKernel 4 (t / ε ^ 2) z ^ (6 / 5 : ℝ)) ^ (5 / 6 : ℝ)
          ≤ Real.exp (-t) * (C * t ^ ((2 / 3 : ℝ) - 1)) := mul_le_mul_of_nonneg_left (h1.trans h2) he
        _ = C * (Real.exp (-t) * t ^ ((2 / 3 : ℝ) - 1)) := by ring)
  refine (le_trans (le_of_eq ?_) hmk).trans ?_
  · rfl
  · rw [integral_const_mul, integral_exp_neg_rpow (by norm_num)]
    have hG := Gamma_two_thirds_le
    have hG0 : 0 ≤ Real.Gamma (2 / 3) := (Real.Gamma_pos_of_pos (by norm_num)).le
    have hc := c_rpow_le
    have he := Real.rpow_nonneg hε.le (2 / 3 : ℝ)
    calc C * Real.Gamma (2 / 3) = c ^ (2 / 3 : ℝ) * Real.Gamma (2 / 3) * ε ^ (2 / 3 : ℝ) := by ring
      _ ≤ (2 / 3) * (3 / 2) * ε ^ (2 / 3 : ℝ) := by gcongr
      _ = ε ^ (2 / 3 : ℝ) := by ring

lemma c_rpow53_le : (2 : ℝ) ^ (17 / 12 : ℝ) * (Real.sqrt Real.pi / 4) ^ (5 / 3 : ℝ) ≤ 5 / 6 := by
  have h0 : 0 ≤ Real.sqrt Real.pi / 4 := by positivity
  refine (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow h0 sqrt_pi_div_four_le (by norm_num))
    (Real.rpow_nonneg (by norm_num) _)).trans ?_
  refine le_of_pow_le_pow_left₀ (n := 12) (by norm_num) (by norm_num) ?_
  rw [mul_pow, ← Real.rpow_natCast, ← Real.rpow_natCast ((9 / 20 : ℝ) ^ (5 / 3 : ℝ)),
    ← Real.rpow_mul (by norm_num), ← Real.rpow_mul (by norm_num)]
  norm_num

/-- **`‖𝒟g₁‖_{6/5} ≤ 5`** (before the factor `ε⁻¹`). -/
theorem dKer_l65 (hε : 0 < ε) (Z : Finset (Fin 4 → ℤ)) (μ : Fin 4) :
    (∑ z ∈ Z, dKer ε μ z ^ (6 / 5 : ℝ)) ^ (5 / 6 : ℝ) ≤ 5 * ε ^ (5 / 3 : ℝ) := by
  set c := Real.sqrt Real.pi / 4 with hcdef
  have hc0 : 0 ≤ c := by positivity
  set C := (2 : ℝ) ^ (17 / 12 : ℝ) * c ^ (5 / 3 : ℝ) * ε ^ (5 / 3 : ℝ)
  have hC0 : 0 ≤ C := by positivity
  have hmk := minkowski_65 Z
    (fun z t => Real.exp (-t) * |heatKernel 4 (t / ε ^ 2) (z + e4 μ) - heatKernel 4 (t / ε ^ 2) z|)
    (fun z t ht => mul_nonneg (Real.exp_pos _).le (abs_nonneg _))
    (fun z => integrableOn_dKer μ z) (fun t => C * (Real.exp (-t) * t ^ ((1 / 6 : ℝ) - 1)))
    ((integrableOn_exp_neg_rpow (by norm_num)).const_mul C) (fun t ht => by
      have hs : 0 ≤ t / ε ^ 2 := by positivity
      have he := (Real.exp_pos (-t)).le
      rw [l65_smul Z he _ fun z _ => abs_nonneg _]
      set M := c * ε * t ^ (-(1 / 2) : ℝ)
      have hM0 : 0 ≤ M := by positivity
      set X := 2 * heatKernel1 (t / ε ^ 2 / 2) 0 ^ 5
      set Y := 2 * heatKernel1 (t / ε ^ 2) 0
      have hX0 : 0 ≤ X := by have := heatKernel1_nonneg (by positivity : 0 ≤ t / ε ^ 2 / 2) 0; positivity
      have hY0 : 0 ≤ Y := by have := heatKernel1_nonneg hs 0; positivity
      have hY : Y ≤ 2 * M := by
        have h := origin_le hε ht; rw [← hcdef] at h; simp only [Y, M]; linarith
      have hX : X ≤ 2 ^ (7 / 2 : ℝ) * M ^ (5 : ℝ) := by
        have h := origin_le hε (by linarith : 0 < t / 2)
        rw [show t / 2 / ε ^ 2 = t / ε ^ 2 / 2 by ring, ← hcdef] at h
        have e : (t / 2) ^ (-(1 / 2) : ℝ) = 2 ^ (1 / 2 : ℝ) * t ^ (-(1 / 2) : ℝ) := by
          rw [Real.div_rpow ht.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_eq_mul_inv, inv_inv,
            mul_comm]
        rw [e] at h
        have h5 := pow_le_pow_left₀ (heatKernel1_nonneg (by positivity) 0) h 5
        calc X ≤ 2 * (c * ε * (2 ^ (1 / 2 : ℝ) * t ^ (-(1 / 2) : ℝ))) ^ 5 := by simp only [X]; linarith
          _ = 2 * (2 ^ (1 / 2 : ℝ)) ^ (5 : ℕ) * M ^ (5 : ℕ) := by simp only [M]; ring
          _ = 2 ^ (7 / 2 : ℝ) * M ^ (5 : ℝ) := by
              rw [← Real.rpow_natCast (2 ^ (1 / 2 : ℝ)), ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast M]
              rw [show (2 : ℝ) * 2 ^ ((1 / 2 : ℝ) * ((5 : ℕ) : ℝ)) = 2 ^ ((1 : ℝ) + (1 / 2 : ℝ) * ((5 : ℕ) : ℝ)) by
                rw [Real.rpow_add (by norm_num), Real.rpow_one]]
              norm_num
      have hsum : (∑ z ∈ Z, |heatKernel 4 (t / ε ^ 2) (z + e4 μ) - heatKernel 4 (t / ε ^ 2) z| ^ (6 / 5 : ℝ)) ^ (5 / 6 : ℝ)
          ≤ C * t ^ ((1 / 6 : ℝ) - 1) := by
        refine (Real.rpow_le_rpow (sum_nonneg fun z _ => Real.rpow_nonneg (abs_nonneg _) _)
          (sum_rpow_abs_diff_le hs Z μ) (by norm_num)).trans ?_
        rw [Real.mul_rpow (Real.rpow_nonneg hX0 _) hY0, ← Real.rpow_mul hX0]
        calc X ^ ((1 / 5 : ℝ) * (5 / 6)) * Y ^ (5 / 6 : ℝ)
            ≤ (2 ^ (7 / 2 : ℝ) * M ^ (5 : ℝ)) ^ ((1 / 5 : ℝ) * (5 / 6)) * (2 * M) ^ (5 / 6 : ℝ) :=
              mul_le_mul (Real.rpow_le_rpow hX0 hX (by norm_num)) (Real.rpow_le_rpow hY0 hY (by norm_num))
                (Real.rpow_nonneg hY0 _) (Real.rpow_nonneg (by positivity) _)
          _ = (2 : ℝ) ^ (17 / 12 : ℝ) * M ^ (5 / 3 : ℝ) := by
              rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by norm_num) hM0, ← Real.rpow_mul hM0,
                ← Real.rpow_mul (by norm_num)]
              rw [show (2 : ℝ) ^ (7 / 2 * (1 / 5 * (5 / 6)) : ℝ) * M ^ ((5 : ℝ) * (1 / 5 * (5 / 6))) *
                  ((2 : ℝ) ^ (5 / 6 : ℝ) * M ^ (5 / 6 : ℝ)) =
                  ((2 : ℝ) ^ (7 / 2 * (1 / 5 * (5 / 6)) : ℝ) * 2 ^ (5 / 6 : ℝ)) *
                  (M ^ ((5 : ℝ) * (1 / 5 * (5 / 6))) * M ^ (5 / 6 : ℝ)) by ring,
                ← Real.rpow_add (by norm_num)]
              rcases hM0.eq_or_lt with hM | hM
              · rw [← hM, Real.zero_rpow (by norm_num), Real.zero_rpow (by norm_num)]; ring
              · rw [← Real.rpow_add hM]; norm_num
          _ = C * t ^ ((1 / 6 : ℝ) - 1) := by
              simp only [M, C]
              rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg ht.le _), Real.mul_rpow hc0 hε.le,
                ← Real.rpow_mul ht.le]
              norm_num; ring
      calc Real.exp (-t) * _ ≤ Real.exp (-t) * (C * t ^ ((1 / 6 : ℝ) - 1)) := mul_le_mul_of_nonneg_left hsum he
        _ = C * (Real.exp (-t) * t ^ ((1 / 6 : ℝ) - 1)) := by ring)
  refine (le_trans (le_of_eq rfl) hmk).trans ?_
  rw [integral_const_mul, integral_exp_neg_rpow (by norm_num)]
  have hG := Gamma_one_sixth_le
  have hc := c_rpow53_le
  have he := Real.rpow_nonneg hε.le (5 / 3 : ℝ)
  calc C * Real.Gamma (1 / 6) = (2 : ℝ) ^ (17 / 12 : ℝ) * c ^ (5 / 3 : ℝ) * Real.Gamma (1 / 6) * ε ^ (5 / 3 : ℝ) := by ring
    _ ≤ (5 / 6) * 6 * ε ^ (5 / 3 : ℝ) := by gcongr
    _ = 5 * ε ^ (5 / 3 : ℝ) := by ring

end LocalLaplacian
end CoreLean

end
