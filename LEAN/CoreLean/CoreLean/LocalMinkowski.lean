/-
`lem:local-laplacian`(i) of BALABAN_CORE.tex (`0580551bf179`): the `L^{6/5}` norm of a time integral, and the constants.

* `minkowski_65`: `(Σ_{z ∈ Z}(∫_0^∞a_z)^{6/5})^{5/6} ≤ ∫_0^∞B` whenever `(Σ_{z ∈ Z}a_z(t)^{6/5})^{5/6} ≤ B(t)` (Minkowski's
  inequality, proved by duality with Hölder's inequality and the test function `(∫a_z)^{1/5}`).
* `origin_le`: `q_{t/ε²}(0) ≤ (√π/4)εt^{-1/2}` (`eq:heat-origin` in the units of `εℤ⁴`).
* `Gamma_two_thirds_le`, `Gamma_one_sixth_le`: `Γ(2/3) ≤ 3/2`, `Γ(1/6) ≤ 6` (convexity of `Γ` and `Γ(1) = Γ(2) = 1`).
* `sqrt_pi_div_four_le`: `√π/4 ≤ 9/20` (the core's `c₀ ≤ 9/10`).
-/
import CoreLean.LocalKernel
import CoreLean.FreeSchauderBasics
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup

open Finset MeasureTheory Set Balaban.LatticeGreen

noncomputable section

namespace CoreLean
namespace LocalLaplacian

/-- **Minkowski's inequality** for the `ℓ^{6/5}` norm of a time integral. -/
theorem minkowski_65 {ι : Type*} (Z : Finset ι) (a : ι → ℝ → ℝ) (ha0 : ∀ z t, 0 < t → 0 ≤ a z t)
    (hint : ∀ z, IntegrableOn (a z) (Ioi 0)) (B : ℝ → ℝ) (hBint : IntegrableOn B (Ioi 0))
    (hB : ∀ t, 0 < t → (∑ z ∈ Z, a z t ^ (6 / 5 : ℝ)) ^ (5 / 6 : ℝ) ≤ B t) :
    (∑ z ∈ Z, (∫ t in Ioi 0, a z t) ^ (6 / 5 : ℝ)) ^ (5 / 6 : ℝ) ≤ ∫ t in Ioi 0, B t := by
  set A : ι → ℝ := fun z => ∫ t in Ioi 0, a z t with hAdef
  have hA0 : ∀ z, 0 ≤ A z := fun z => setIntegral_nonneg measurableSet_Ioi fun t ht => ha0 z t ht
  set N := ∑ z ∈ Z, A z ^ (6 / 5 : ℝ)
  have hN0 : 0 ≤ N := sum_nonneg fun z _ => Real.rpow_nonneg (hA0 z) _
  have hBt0 : ∀ t, 0 < t → 0 ≤ B t := fun t ht => (Real.rpow_nonneg (sum_nonneg fun z _ =>
    Real.rpow_nonneg (ha0 z t ht) _) _).trans (hB t ht)
  have hI0 : 0 ≤ ∫ t in Ioi 0, B t := setIntegral_nonneg measurableSet_Ioi hBt0
  have hconj : (6 / 5 : ℝ).HolderConjugate 6 := ⟨by norm_num, by norm_num, by norm_num⟩
  set φ : ι → ℝ := fun z => A z ^ (1 / 5 : ℝ)
  have hφ0 : ∀ z, 0 ≤ φ z := fun z => Real.rpow_nonneg (hA0 z) _
  have hφ6 : ∑ z ∈ Z, φ z ^ (6 : ℝ) = N := sum_congr rfl fun z _ => by
    simp only [φ, ← Real.rpow_mul (hA0 z)]; norm_num
  have hAφ : ∑ z ∈ Z, A z * φ z = N := sum_congr rfl fun z _ => by
    simp only [φ]
    rw [show (6 / 5 : ℝ) = 1 + 1 / 5 by norm_num, Real.rpow_add' (hA0 z) (by norm_num), Real.rpow_one]
  -- Hölder at each time
  have hpt : ∀ t, 0 < t → ∑ z ∈ Z, a z t * φ z ≤ B t * N ^ (1 / 6 : ℝ) := fun t ht => by
    have h := Real.inner_le_Lp_mul_Lq_of_nonneg Z hconj (fun z _ => ha0 z t ht) (fun z _ => hφ0 z)
    rw [hφ6, show (1 : ℝ) / (6 / 5) = 5 / 6 by norm_num] at h
    exact h.trans (mul_le_mul_of_nonneg_right (hB t ht) (Real.rpow_nonneg hN0 _))
  -- integrate
  have hint1 : IntegrableOn (fun t => ∑ z ∈ Z, a z t * φ z) (Ioi 0) :=
    integrable_finsetSum _ fun z _ => (hint z).mul_const _
  have hmain : N ≤ (∫ t in Ioi 0, B t) * N ^ (1 / 6 : ℝ) := by
    calc N = ∑ z ∈ Z, A z * φ z := hAφ.symm
      _ = ∫ t in Ioi 0, ∑ z ∈ Z, a z t * φ z := by
          rw [integral_finsetSum _ fun z _ => (hint z).mul_const _]
          exact sum_congr rfl fun z _ => (integral_mul_const _ _).symm
      _ ≤ ∫ t in Ioi 0, B t * N ^ (1 / 6 : ℝ) :=
          setIntegral_mono_on hint1 (hBint.mul_const _) measurableSet_Ioi fun t ht => hpt t ht
      _ = (∫ t in Ioi 0, B t) * N ^ (1 / 6 : ℝ) := integral_mul_const _ _
  rcases hN0.eq_or_lt with h | h
  · rw [← h, Real.zero_rpow (by norm_num)]; exact hI0
  · have h16 : 0 < N ^ (1 / 6 : ℝ) := Real.rpow_pos_of_pos h _
    have e : N ^ (5 / 6 : ℝ) * N ^ (1 / 6 : ℝ) = N := by
      rw [← Real.rpow_add h]; norm_num
    exact le_of_mul_le_mul_right (by rw [e]; exact hmain) h16

/-! ### The constants -/

lemma sqrt_pi_div_four_le : Real.sqrt Real.pi / 4 ≤ 9 / 20 := by
  have : Real.sqrt Real.pi ≤ 9 / 5 := by
    rw [Real.sqrt_le_left (by norm_num)]; linarith [Real.pi_lt_d2]
  linarith

lemma Gamma_le_one_of_mem {x : ℝ} (h1 : 1 ≤ x) (h2 : x ≤ 2) : Real.Gamma x ≤ 1 := by
  have hc := Real.convexOn_Gamma
  have := hc.2 (show (1 : ℝ) ∈ Set.Ioi 0 by norm_num) (show (2 : ℝ) ∈ Set.Ioi 0 by norm_num)
    (show (0 : ℝ) ≤ 2 - x by linarith) (show (0 : ℝ) ≤ x - 1 by linarith) (by ring)
  simp only [smul_eq_mul, Real.Gamma_one, Real.Gamma_two] at this
  rw [show (2 - x) * 1 + (x - 1) * 2 = x by ring] at this
  linarith

lemma Gamma_two_thirds_le : Real.Gamma (2 / 3) ≤ 3 / 2 := by
  have h := Real.Gamma_add_one (show (2 / 3 : ℝ) ≠ 0 by norm_num)
  rw [show (2 / 3 : ℝ) + 1 = 5 / 3 by norm_num] at h
  have := Gamma_le_one_of_mem (show (1 : ℝ) ≤ 5 / 3 by norm_num) (by norm_num)
  linarith

lemma Gamma_one_sixth_le : Real.Gamma (1 / 6) ≤ 6 := by
  have h := Real.Gamma_add_one (show (1 / 6 : ℝ) ≠ 0 by norm_num)
  rw [show (1 / 6 : ℝ) + 1 = 7 / 6 by norm_num] at h
  have := Gamma_le_one_of_mem (show (1 : ℝ) ≤ 7 / 6 by norm_num) (by norm_num)
  linarith

/-- `q_{t/ε²}(0) ≤ (√π/4)εt^{-1/2}`. -/
lemma origin_le {ε t : ℝ} (hε : 0 < ε) (ht : 0 < t) :
    heatKernel1 (t / ε ^ 2) 0 ≤ Real.sqrt Real.pi / 4 * ε * t ^ (-(1 / 2) : ℝ) := by
  refine (heatKernel1_zero_le (by positivity)).trans (le_of_eq ?_)
  rw [Real.sqrt_div' _ (sq_nonneg ε), Real.sqrt_sq hε.le, Real.rpow_neg ht.le, ← Real.sqrt_eq_rpow]
  have := Real.sqrt_pos.2 ht
  field_simp

end LocalLaplacian
end CoreLean

end
