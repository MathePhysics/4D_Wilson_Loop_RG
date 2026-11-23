/-
`lem:central-bond` of BALABAN_CORE.tex (`a021c13be348`), the two facts on matrices of its proof and its arithmetic, in a
C⋆-algebra `A` (the matrices with the operator norm are one).

* `norm_inv_le`: for a normal unit `u` whose spectrum lies outside the disc of radius `δ`, `‖u⁻¹‖ ≤ 1/δ` (the norm of
  `(N - z)⁻¹` is the inverse of the distance from `z` to the spectrum of `N`).
* **The first fact** (`eigenvalue_near`): if `N₁` is normal and `‖N₁ - N₂‖ < δ ≤ |z - λ|` for every eigenvalue `λ` of
  `N₁`, then `z` is not in the spectrum of `N₂`: `N₂ - z = (N₁ - z)(1 + (N₁ - z)⁻¹(N₂ - N₁))` is invertible.
* `segment_norm`, `cos_half_ge`: `|1 + t(e^{iθ} - 1)| ≥ cos ½θ ≥ sin ½ϑ` for `t ∈ [0, 1]`, `|θ| ≤ π - ϑ`.
* `resolvent_bound`: for a normal `W` whose spectrum consists of numbers `e^{iθ}`, `|θ| ≤ π - ϑ`, the element
  `1 + t(W - 1)`, `t ∈ [0, 1]`, is invertible with `‖(1 + t(W - 1))⁻¹‖ ≤ (sin ½ϑ)⁻¹`.
* `resolvent_identity`: `(W₁ - 1)R₁ - (W₂ - 1)R₂ = R₁(W₁ - W₂)R₂` with `R_i = (1 + t(W_i - 1))⁻¹`.
* **The second fact** (`log_sub_le`): with `log W = ∫₀¹(W - 1)(1 + t(W - 1))⁻¹ dt` (`def:logarithm`),
  `‖log W₁ - log W₂‖ ≤ (sin ½ϑ)⁻²‖W₁ - W₂‖`.
* The arithmetic (`first_bound_arith`, `last_bound_arith`): the choice of `c₉` gives `½πL⁴(ϱ + (2 + K₁)ν) ≤ r_G/32`
  and, from `(2/π)L⁻⁴‖A‖ ≤ ϱ + π(C_Ψ + 4)ν‖A‖`, `‖A‖ ≤ πL⁴ϱ`.

Jordan's inequality `2|θ|/π ≤ |e^{iθ} - 1|` used in the proof is `MomentumSymbols.chord_bounds`.
-/
import Mathlib

open Complex Set
open scoped Interval

noncomputable section

namespace CoreLean
namespace CentralBond

section Scalar

/-- `|1 + t(e^{iθ} - 1)| ≥ cos ½θ` for `t ∈ [0, 1]`: the segment from `1` to `e^{iθ}`, turned by `e^{-iθ/2}`, has
the real part `cos ½θ`. -/
lemma segment_norm (θ t : ℝ) :
    Real.cos (θ / 2) ≤ ‖1 + (t : ℂ) * (exp (θ * I) - 1)‖ := by
  set w : ℂ := exp (↑(-(θ / 2)) * I)
  have hw : ‖w‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have hprod : (1 + (t : ℂ) * (exp (θ * I) - 1)) * w = w + (t : ℂ) * (exp (↑(θ / 2) * I) - w) := by
    have : exp (θ * I) * w = exp (↑(θ / 2) * I) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    linear_combination (t : ℂ) * this
  have hre : ((1 + (t : ℂ) * (exp (θ * I) - 1)) * w).re = Real.cos (θ / 2) := by
    rw [hprod]
    simp only [w, add_re, mul_re, ofReal_re, ofReal_im, sub_re, sub_im, Complex.exp_ofReal_mul_I_re,
      Complex.exp_ofReal_mul_I_im, Real.cos_neg, zero_mul, sub_zero]
    ring
  calc Real.cos (θ / 2) = ((1 + (t : ℂ) * (exp (θ * I) - 1)) * w).re := hre.symm
    _ ≤ ‖(1 + (t : ℂ) * (exp (θ * I) - 1)) * w‖ := Complex.re_le_norm _
    _ = ‖1 + (t : ℂ) * (exp (θ * I) - 1)‖ := by rw [norm_mul, hw, mul_one]

/-- `cos ½θ ≥ sin ½ϑ` for `|θ| ≤ π - ϑ`, `0 ≤ ϑ`. -/
lemma cos_half_ge {θ ϑ : ℝ} (hϑ : 0 ≤ ϑ) (hθ : |θ| ≤ Real.pi - ϑ) : Real.sin (ϑ / 2) ≤ Real.cos (θ / 2) := by
  have e1 : Real.cos (θ / 2) = Real.cos (|θ| / 2) := by
    rw [← Real.cos_abs (θ / 2), abs_div, abs_two]
  have e2 : Real.sin (ϑ / 2) = Real.cos ((Real.pi - ϑ) / 2) := by
    rw [show (Real.pi - ϑ) / 2 = Real.pi / 2 - ϑ / 2 by ring, Real.cos_pi_div_two_sub]
  rw [e1, e2]
  exact Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) (by linarith [Real.pi_pos]) (by linarith)

end Scalar

section CStar

variable {A : Type*} [CStarAlgebra A]

local notation "↑ₐ" => algebraMap ℂ A

/-- **The norm of the inverse of a normal unit**: `‖u⁻¹‖ ≤ 1/δ` if `δ ≤ |λ|` on the spectrum of `u`. -/
theorem norm_inv_le (u : Aˣ) [IsStarNormal (u : A)] {δ : ℝ} (hδ : 0 < δ)
    (hσ : ∀ z ∈ spectrum ℂ (u : A), δ ≤ ‖z‖) : ‖((u⁻¹ : Aˣ) : A)‖ ≤ 1 / δ := by
  have hr := IsStarNormal.spectralRadius_eq_nnNorm ((u⁻¹ : Aˣ) : A)
  have hle : spectralRadius ℂ ((u⁻¹ : Aˣ) : A) ≤ ENNReal.ofReal (1 / δ) := by
    rw [spectralRadius_eq_of_unital]
    refine iSup₂_le fun k hk => ?_
    have hk0 : k ≠ 0 := fun h => by
      rw [h, spectrum.zero_mem_iff] at hk; exact hk (Units.isUnit _)
    have hinv : ((((Units.mk0 k hk0)⁻¹ : ℂˣ)) : ℂ) ∈ spectrum ℂ (u : A) := by
      rw [spectrum.inv_mem_iff]; simpa using hk
    have h1 := hσ _ hinv
    simp only [Units.val_inv_eq_inv_val, Units.val_mk0, norm_inv] at h1
    have hk' : 0 < ‖k‖ := norm_pos_iff.2 hk0
    have h2 : ‖k‖ ≤ 1 / δ := by
      rw [le_div_iff₀ hδ]
      calc ‖k‖ * δ ≤ ‖k‖ * ‖k‖⁻¹ := mul_le_mul_of_nonneg_left h1 hk'.le
        _ = 1 := mul_inv_cancel₀ hk'.ne'
    rw [← ENNReal.ofReal_coe_nnreal, coe_nnNorm]
    exact ENNReal.ofReal_le_ofReal h2
  rw [hr, ← ENNReal.ofReal_coe_nnreal, coe_nnNorm] at hle
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hle

/-- The translate `N - z` of a normal element is normal. -/
lemma normal_sub (N : A) [hN : IsStarNormal N] (z : ℂ) : IsStarNormal (N - ↑ₐ z) := by
  constructor
  rw [star_sub, ← algebraMap_star_comm]
  exact (hN.star_comm_self.sub_right (Algebra.commute_algebraMap_right z (star N))).sub_left
    (Algebra.commute_algebraMap_left (star z) _)

/-- **The first fact**: if `N₁` is normal and `‖N₁ - N₂‖ < δ ≤ |z - λ|` for every `λ` in the spectrum of `N₁`, then
`z` is not in the spectrum of `N₂`. -/
theorem eigenvalue_near (N₁ N₂ : A) [IsStarNormal N₁] {z : ℂ} {δ : ℝ} (hδ : 0 < δ) (hN : ‖N₁ - N₂‖ < δ)
    (hσ : ∀ l ∈ spectrum ℂ N₁, δ ≤ ‖z - l‖) : z ∉ spectrum ℂ N₂ := by
  haveI := normal_sub N₁ z
  -- the spectrum of `N₁ - z`
  have hσ' : ∀ μ ∈ spectrum ℂ (N₁ - ↑ₐ z), δ ≤ ‖μ‖ := fun μ hμ => by
    have : μ + z ∈ spectrum ℂ N₁ := by
      rw [spectrum.mem_iff] at hμ ⊢
      rwa [show ↑ₐ (μ + z) - N₁ = ↑ₐ μ - (N₁ - ↑ₐ z) by rw [map_add]; abel]
    have h := hσ _ this
    rwa [show z - (μ + z) = -μ by ring, norm_neg] at h
  have h0 : (0 : ℂ) ∉ spectrum ℂ (N₁ - ↑ₐ z) := fun h => by
    have := hσ' 0 h; rw [norm_zero] at this; linarith
  rw [spectrum.zero_mem_iff, not_not] at h0
  obtain ⟨u, hu⟩ := h0
  haveI : IsStarNormal (u : A) := by rw [hu]; infer_instance
  have hinv := norm_inv_le u hδ (by rw [hu]; exact hσ')
  -- `N₂ - z = u(1 - u⁻¹(N₁ - N₂))`
  have hsmall : ‖((u⁻¹ : Aˣ) : A) * (N₁ - N₂)‖ < 1 := by
    calc ‖((u⁻¹ : Aˣ) : A) * (N₁ - N₂)‖ ≤ ‖((u⁻¹ : Aˣ) : A)‖ * ‖N₁ - N₂‖ := norm_mul_le _ _
      _ ≤ 1 / δ * ‖N₁ - N₂‖ := by gcongr
      _ < 1 / δ * δ := by gcongr
      _ = 1 := by field_simp
  have hunit : IsUnit (1 - ((u⁻¹ : Aˣ) : A) * (N₁ - N₂)) := (Units.oneSub _ hsmall).isUnit
  have heq : N₂ - ↑ₐ z = (u : A) * (1 - ((u⁻¹ : Aˣ) : A) * (N₁ - N₂)) := by
    rw [mul_sub, mul_one, ← mul_assoc, Units.mul_inv, one_mul, hu]; abel
  rw [spectrum.mem_iff, not_not]
  have : ↑ₐ z - N₂ = -(N₂ - ↑ₐ z) := by abel
  rw [this, IsUnit.neg_iff, heq]
  exact (Units.isUnit u).mul hunit

/-- The element `1 + t(W - 1)` is normal with `W`. -/
lemma normal_segment (W : A) [hW : IsStarNormal W] (t : ℝ) : IsStarNormal (1 + (t : ℂ) • (W - 1)) := by
  constructor
  rw [star_add, star_one, star_smul, star_sub, star_one, Complex.star_def, Complex.conj_ofReal]
  have hc := hW.star_comm_self
  have h1 : Commute (star W - 1) (W - 1) := (hc.sub_left (Commute.one_left W)).sub_right (Commute.one_right _)
  have h2 : Commute ((t : ℂ) • (star W - 1)) ((t : ℂ) • (W - 1)) := (h1.smul_left _).smul_right _
  exact (Commute.one_left _).add_left ((Commute.one_right _).add_right h2)

/-- The spectrum of `1 + t(W - 1)` lies outside the disc of radius `sin ½ϑ`. -/
lemma segment_spectrum (W : A) {ϑ : ℝ} (hϑ : 0 ≤ ϑ)
    (hW : ∀ l ∈ spectrum ℂ W, ∃ θ : ℝ, |θ| ≤ Real.pi - ϑ ∧ l = exp (θ * I)) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) : ∀ μ ∈ spectrum ℂ (1 + (t : ℂ) • (W - 1)), Real.sin (ϑ / 2) ≤ ‖μ‖ := by
  intro μ hμ
  have hs1 : Real.sin (ϑ / 2) ≤ 1 := Real.sin_le_one _
  rcases eq_or_ne t 0 with h | h
  · subst h
    simp only [ofReal_zero, zero_smul, add_zero] at hμ
    have : μ = 1 := by
      by_contra hne
      rw [spectrum.mem_iff] at hμ
      apply hμ
      have e : ↑ₐ μ - 1 = ↑ₐ (μ - 1) := by rw [map_sub, map_one]
      rw [e]
      exact (isUnit_iff_ne_zero.2 (sub_ne_zero.2 hne)).map _
    rw [this, norm_one]; exact hs1
  · set l : ℂ := 1 + (μ - 1) / (t : ℂ)
    have htC : (t : ℂ) ≠ 0 := ofReal_ne_zero.2 h
    have hl : l ∈ spectrum ℂ W := by
      by_contra hl
      rw [spectrum.mem_iff, not_not] at hl
      rw [spectrum.mem_iff] at hμ
      apply hμ
      have e : ↑ₐ μ - (1 + (t : ℂ) • (W - 1)) = (t : ℂ) • (↑ₐ l - W) := by
        have htl : (t : ℂ) * l = t + μ - 1 := by simp only [l]; field_simp; ring
        simp only [Algebra.algebraMap_eq_smul_one, smul_sub, smul_smul, htl, sub_smul, add_smul, one_smul]
        abel
      rw [e, Algebra.smul_def]
      exact ((isUnit_iff_ne_zero.2 htC).map _).mul hl
    obtain ⟨θ, hθ, hlθ⟩ := hW l hl
    have hμl : μ = 1 + (t : ℂ) * (exp (θ * I) - 1) := by
      rw [← hlθ]; simp only [l]; field_simp; ring
    rw [hμl]
    exact (cos_half_ge hϑ hθ).trans (segment_norm θ t)

/-- **The resolvent on the segment**: `1 + t(W - 1)` is invertible, with `‖(1 + t(W - 1))⁻¹‖ ≤ (sin ½ϑ)⁻¹`. -/
theorem resolvent_bound (W : A) [IsStarNormal W] {ϑ : ℝ} (hϑ0 : 0 < ϑ) (hϑ : ϑ < Real.pi)
    (hW : ∀ l ∈ spectrum ℂ W, ∃ θ : ℝ, |θ| ≤ Real.pi - ϑ ∧ l = exp (θ * I)) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) :
    IsUnit (1 + (t : ℂ) • (W - 1)) ∧ ‖Ring.inverse (1 + (t : ℂ) • (W - 1))‖ ≤ 1 / Real.sin (ϑ / 2) := by
  have hs : 0 < Real.sin (ϑ / 2) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hσ := segment_spectrum W hϑ0.le hW ht0 ht1
  have h0 : (0 : ℂ) ∉ spectrum ℂ (1 + (t : ℂ) • (W - 1)) := fun h => by
    have := hσ 0 h; rw [norm_zero] at this; linarith
  rw [spectrum.zero_mem_iff, not_not] at h0
  refine ⟨h0, ?_⟩
  obtain ⟨u, hu⟩ := h0
  haveI : IsStarNormal (1 + (t : ℂ) • (W - 1)) := normal_segment W t
  haveI : IsStarNormal (u : A) := by rw [hu]; infer_instance
  rw [← hu, Ring.inverse_unit]
  exact norm_inv_le u hs (by rw [hu]; exact hσ)

/-- **The resolvent identity**: `(W₁ - 1)R₁ - (W₂ - 1)R₂ = R₁(W₁ - W₂)R₂` with `R_i = (1 + c(W_i - 1))⁻¹`. -/
theorem resolvent_identity (W₁ W₂ : A) (c : ℂ) (u₁ u₂ : Aˣ) (h₁ : (u₁ : A) = 1 + c • (W₁ - 1))
    (h₂ : (u₂ : A) = 1 + c • (W₂ - 1)) :
    (W₁ - 1) * ((u₁⁻¹ : Aˣ) : A) - (W₂ - 1) * ((u₂⁻¹ : Aˣ) : A) =
      ((u₁⁻¹ : Aˣ) : A) * (W₁ - W₂) * ((u₂⁻¹ : Aˣ) : A) := by
  set R₁ := ((u₁⁻¹ : Aˣ) : A)
  set R₂ := ((u₂⁻¹ : Aˣ) : A)
  set X₁ := W₁ - 1
  set X₂ := W₂ - 1
  have hR₁ : R₁ * (u₁ : A) = 1 := Units.inv_mul u₁
  have hR₁' : (u₁ : A) * R₁ = 1 := Units.mul_inv u₁
  have hR₂ : (u₂ : A) * R₂ = 1 := Units.mul_inv u₂
  -- `X₁` commutes with `R₁`
  have hcomm : X₁ * R₁ = R₁ * X₁ := by
    have hXN : X₁ * (u₁ : A) = (u₁ : A) * X₁ := by
      rw [h₁, mul_add, add_mul, mul_one, one_mul, mul_smul_comm, smul_mul_assoc]
    calc X₁ * R₁ = R₁ * ((u₁ : A) * X₁) * R₁ := by rw [← mul_assoc, hR₁, one_mul]
      _ = R₁ * (X₁ * (u₁ : A)) * R₁ := by rw [hXN]
      _ = R₁ * X₁ := by rw [mul_assoc, mul_assoc, hR₁', mul_one]
  have e1 : X₁ * R₁ = R₁ * X₁ * R₂ + c • (R₁ * X₁ * X₂ * R₂) := by
    calc X₁ * R₁ = R₁ * X₁ * ((u₂ : A) * R₂) := by rw [hR₂, mul_one, hcomm]
      _ = R₁ * X₁ * R₂ + c • (R₁ * X₁ * X₂ * R₂) := by
        rw [h₂]; simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, mul_assoc]
  have e2 : X₂ * R₂ = R₁ * X₂ * R₂ + c • (R₁ * X₁ * X₂ * R₂) := by
    calc X₂ * R₂ = (R₁ * (u₁ : A)) * X₂ * R₂ := by rw [hR₁, one_mul]
      _ = R₁ * X₂ * R₂ + c • (R₁ * X₁ * X₂ * R₂) := by
        rw [h₁]; simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, mul_assoc]
  rw [e1, e2, show W₁ - W₂ = X₁ - X₂ by simp only [X₁, X₂]; abel]
  simp only [mul_sub, sub_mul, mul_assoc]
  abel

/-- The logarithm of `def:logarithm`, `log W = ∫₀¹(W - 1)(1 + t(W - 1))⁻¹ dt`. -/
def logI (W : A) : A := ∫ t in (0 : ℝ)..1, (W - 1) * Ring.inverse (1 + (t : ℂ) • (W - 1))

/-- The integrand of `logI` is continuous on `[0, 1]` when `1 + t(W - 1)` is invertible there. -/
lemma integrand_continuousOn (W : A) (hu : ∀ t ∈ Icc (0 : ℝ) 1, IsUnit (1 + (t : ℂ) • (W - 1))) :
    ContinuousOn (fun t : ℝ => Ring.inverse (1 + (t : ℂ) • (W - 1))) (Icc 0 1) := by
  intro t ht
  obtain ⟨u, hu'⟩ := hu t ht
  have hinv := NormedRing.inverse_continuousAt u
  rw [hu'] at hinv
  have hf : Continuous fun t : ℝ => 1 + (t : ℂ) • (W - 1) := by fun_prop
  exact (ContinuousAt.comp (g := Ring.inverse) (f := fun t : ℝ => 1 + (t : ℂ) • (W - 1)) hinv
    hf.continuousAt).continuousWithinAt

/-- **The second fact**: `‖log W₁ - log W₂‖ ≤ (sin ½ϑ)⁻²‖W₁ - W₂‖` for normal `W₁`, `W₂` whose spectra consist of
numbers `e^{iθ}`, `|θ| ≤ π - ϑ`. -/
theorem log_sub_le (W₁ W₂ : A) [IsStarNormal W₁] [IsStarNormal W₂] {ϑ : ℝ} (hϑ0 : 0 < ϑ) (hϑ : ϑ < Real.pi)
    (hW₁ : ∀ l ∈ spectrum ℂ W₁, ∃ θ : ℝ, |θ| ≤ Real.pi - ϑ ∧ l = exp (θ * I))
    (hW₂ : ∀ l ∈ spectrum ℂ W₂, ∃ θ : ℝ, |θ| ≤ Real.pi - ϑ ∧ l = exp (θ * I)) :
    ‖logI W₁ - logI W₂‖ ≤ (1 / Real.sin (ϑ / 2)) ^ 2 * ‖W₁ - W₂‖ := by
  have hb₁ := fun t (ht : t ∈ Icc (0 : ℝ) 1) => resolvent_bound W₁ hϑ0 hϑ hW₁ ht.1 ht.2
  have hb₂ := fun t (ht : t ∈ Icc (0 : ℝ) 1) => resolvent_bound W₂ hϑ0 hϑ hW₂ ht.1 ht.2
  have hc₁ := integrand_continuousOn W₁ fun t ht => (hb₁ t ht).1
  have hc₂ := integrand_continuousOn W₂ fun t ht => (hb₂ t ht).1
  have hi₁ : IntervalIntegrable (fun t : ℝ => (W₁ - 1) * Ring.inverse (1 + (t : ℂ) • (W₁ - 1)))
      MeasureTheory.volume 0 1 :=
    (continuousOn_const.mul hc₁).intervalIntegrable_of_Icc zero_le_one
  have hi₂ : IntervalIntegrable (fun t : ℝ => (W₂ - 1) * Ring.inverse (1 + (t : ℂ) • (W₂ - 1)))
      MeasureTheory.volume 0 1 :=
    (continuousOn_const.mul hc₂).intervalIntegrable_of_Icc zero_le_one
  rw [logI, logI, ← intervalIntegral.integral_sub hi₁ hi₂]
  have hbound : ∀ t ∈ Ι (0 : ℝ) 1, ‖(W₁ - 1) * Ring.inverse (1 + (t : ℂ) • (W₁ - 1)) -
      (W₂ - 1) * Ring.inverse (1 + (t : ℂ) • (W₂ - 1))‖ ≤ (1 / Real.sin (ϑ / 2)) ^ 2 * ‖W₁ - W₂‖ := by
    intro t ht
    rw [uIoc_of_le zero_le_one] at ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2⟩
    obtain ⟨⟨u₁, hu₁⟩, hn₁⟩ := hb₁ t ht'
    obtain ⟨⟨u₂, hu₂⟩, hn₂⟩ := hb₂ t ht'
    rw [← hu₁, Ring.inverse_unit] at hn₁
    rw [← hu₂, Ring.inverse_unit] at hn₂
    rw [← hu₁, ← hu₂, Ring.inverse_unit, Ring.inverse_unit]
    rw [resolvent_identity W₁ W₂ (t : ℂ) u₁ u₂ hu₁ hu₂]
    calc ‖((u₁⁻¹ : Aˣ) : A) * (W₁ - W₂) * ((u₂⁻¹ : Aˣ) : A)‖
        ≤ ‖((u₁⁻¹ : Aˣ) : A)‖ * ‖W₁ - W₂‖ * ‖((u₂⁻¹ : Aˣ) : A)‖ :=
          (norm_mul_le _ _).trans (by gcongr; exact norm_mul_le _ _)
      _ ≤ (1 / Real.sin (ϑ / 2)) * ‖W₁ - W₂‖ * (1 / Real.sin (ϑ / 2)) := by
          have hs : 0 < Real.sin (ϑ / 2) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
          exact mul_le_mul (mul_le_mul_of_nonneg_right hn₁ (norm_nonneg _)) hn₂ (norm_nonneg _)
            (mul_nonneg (div_nonneg zero_le_one hs.le) (norm_nonneg _))
      _ = (1 / Real.sin (ϑ / 2)) ^ 2 * ‖W₁ - W₂‖ := by ring
  have := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  rwa [sub_zero, abs_one, mul_one] at this

end CStar

section ExpLipschitz

open NormedSpace

variable {A : Type*} [CStarAlgebra A] [Nontrivial A]

/-- `e^{isX}` is unitary, of norm one, for self-adjoint `X` and real `s`. -/
lemma norm_exp_isX (X : A) (hX : IsSelfAdjoint X) (s : ℝ) : ‖exp (s • (I • X))‖ = 1 := by
  letI : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℂ A
  apply CStarRing.norm_of_mem_unitary
  apply exp_mem_unitary_of_mem_skewAdjoint
  rw [skewAdjoint.mem_iff, ← Complex.coe_smul, star_smul, star_smul, hX.star_eq, Complex.star_def,
    Complex.conj_ofReal, Complex.conj_I, neg_smul, smul_neg]

/-- **`‖e^{iX} - e^{iY}‖ ≤ ‖X - Y‖`** for self-adjoint `X`, `Y`, by
`e^{iX} - e^{iY} = ∫₀¹ e^{isX} i(X - Y) e^{i(1-s)Y} ds`. -/
theorem norm_exp_sub_exp_le (X Y : A) (hX : IsSelfAdjoint X) (hY : IsSelfAdjoint Y) :
    ‖exp (I • X) - exp (I • Y)‖ ≤ ‖X - Y‖ := by
  set x := I • X
  set y := I • Y
  set F : ℝ → A := fun s => exp (s • x) * exp ((1 - s) • y)
  set F' : ℝ → A := fun s => exp (s • x) * (x - y) * exp ((1 - s) • y)
  have hd1 : ∀ s : ℝ, HasDerivAt (fun s : ℝ => exp (s • x)) (exp (s • x) * x) s := fun s =>
    hasDerivAt_exp_smul_const x s
  have hd2 : ∀ s : ℝ, HasDerivAt (fun s : ℝ => exp ((1 - s) • y)) (-(y * exp ((1 - s) • y))) s := fun s => by
    have h := hasDerivAt_exp_smul_const' y (1 - s)
    have hl : HasDerivAt (fun s : ℝ => 1 - s) (-1) s := by
      simpa using (hasDerivAt_id s).const_sub 1
    have := h.scomp s hl
    simpa [Function.comp_def] using this
  have hderiv : ∀ s : ℝ, HasDerivAt F (F' s) s := fun s => by
    have := (hd1 s).mul (hd2 s)
    convert this using 1
    simp only [F', mul_neg, neg_mul, sub_eq_add_neg, mul_add, add_mul, mul_assoc]
  have he1 : Continuous fun s : ℝ => exp (s • x) :=
    continuous_iff_continuousAt.2 fun s => (hd1 s).continuousAt
  have he2 : Continuous fun s : ℝ => exp ((1 - s) • y) :=
    continuous_iff_continuousAt.2 fun s => (hd2 s).continuousAt
  have hcont : Continuous F' := (he1.mul continuous_const).mul he2
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hderiv s)
    (hcont.intervalIntegrable 0 1)
  have hF1 : F 1 = exp x := by simp [F]
  have hF0 : F 0 = exp y := by simp [F]
  rw [hF1, hF0] at hFTC
  rw [← hFTC]
  have hxy : ‖x - y‖ = ‖X - Y‖ := by
    rw [show x - y = I • (X - Y) by simp only [x, y, smul_sub], norm_smul, Complex.norm_I, one_mul]
  have hbound : ∀ s ∈ Ι (0 : ℝ) 1, ‖F' s‖ ≤ ‖X - Y‖ := fun s _ => by
    calc ‖F' s‖ ≤ ‖exp (s • x)‖ * ‖x - y‖ * ‖exp ((1 - s) • y)‖ :=
          (norm_mul_le _ _).trans (by gcongr; exact norm_mul_le _ _)
      _ = ‖X - Y‖ := by rw [norm_exp_isX X hX, norm_exp_isX Y hY, hxy, one_mul, mul_one]
  have := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  rwa [sub_zero, abs_one, mul_one] at this

end ExpLipschitz

section Arithmetic

/-- **The first bound**: with `c₉ ≤ r_G/(32πL⁴(2 + K₁))` and `ϱ, ν ≤ c₉`, `½πL⁴(ϱ + (2 + K₁)ν) ≤ r_G/32`. -/
lemma first_bound_arith {L K₁ rG c₉ ϱ ν : ℝ} (hL : 0 < L) (hK : 0 ≤ K₁) (hϱ0 : 0 ≤ ϱ) (_hν0 : 0 ≤ ν)
    (hϱ : ϱ ≤ c₉) (hν : ν ≤ c₉) (hc : c₉ ≤ rG / (32 * Real.pi * L ^ 4 * (2 + K₁))) :
    (1 / 2) * Real.pi * L ^ 4 * (ϱ + (2 + K₁) * ν) ≤ rG / 32 := by
  have hP : 0 < 32 * Real.pi * L ^ 4 * (2 + K₁) := by positivity
  have hc0 : 0 ≤ c₉ := hϱ0.trans hϱ
  have h1 : ϱ + (2 + K₁) * ν ≤ 2 * (2 + K₁) * c₉ := by nlinarith
  have h2 : 32 * Real.pi * L ^ 4 * (2 + K₁) * c₉ ≤ rG := (le_div_iff₀' hP).1 hc
  have hpos : 0 ≤ (1 / 2) * Real.pi * L ^ 4 := by positivity
  calc (1 / 2) * Real.pi * L ^ 4 * (ϱ + (2 + K₁) * ν) ≤ (1 / 2) * Real.pi * L ^ 4 * (2 * (2 + K₁) * c₉) :=
        mul_le_mul_of_nonneg_left h1 hpos
    _ = (32 * Real.pi * L ^ 4 * (2 + K₁) * c₉) / 32 := by ring
    _ ≤ rG / 32 := by linarith

/-- **The last bound**: if `(2/π)L⁻⁴a ≤ ϱ + π(C_Ψ + 4)νa` and `ν ≤ 1/(π²L⁴(C_Ψ + 4))`, then `a ≤ πL⁴ϱ`. -/
lemma last_bound_arith {L CΨ ν ϱ a : ℝ} (hL : 0 < L) (hC : 0 ≤ CΨ) (ha : 0 ≤ a)
    (hν : ν ≤ 1 / (Real.pi ^ 2 * L ^ 4 * (CΨ + 4)))
    (h : 2 / Real.pi * (L ^ 4)⁻¹ * a ≤ ϱ + Real.pi * (CΨ + 4) * ν * a) :
    a ≤ Real.pi * L ^ 4 * ϱ := by
  have hπ := Real.pi_pos
  have hL4 : 0 < L ^ 4 := by positivity
  have hD : 0 < Real.pi ^ 2 * L ^ 4 * (CΨ + 4) := by positivity
  -- `π(C_Ψ + 4)ν ≤ 1/(πL⁴)`
  have h1 : Real.pi * (CΨ + 4) * ν ≤ 1 / Real.pi * (L ^ 4)⁻¹ := by
    have := mul_le_mul_of_nonneg_left hν (by positivity : 0 ≤ Real.pi * (CΨ + 4))
    calc Real.pi * (CΨ + 4) * ν ≤ Real.pi * (CΨ + 4) * (1 / (Real.pi ^ 2 * L ^ 4 * (CΨ + 4))) := this
      _ = 1 / Real.pi * (L ^ 4)⁻¹ := by field_simp
  have h2 : Real.pi * (CΨ + 4) * ν * a ≤ 1 / Real.pi * (L ^ 4)⁻¹ * a := mul_le_mul_of_nonneg_right h1 ha
  have h3 : 1 / Real.pi * (L ^ 4)⁻¹ * a ≤ ϱ := by
    have e : 2 / Real.pi * (L ^ 4)⁻¹ * a = 1 / Real.pi * (L ^ 4)⁻¹ * a + 1 / Real.pi * (L ^ 4)⁻¹ * a := by ring
    linarith
  have e : a = Real.pi * L ^ 4 * (1 / Real.pi * (L ^ 4)⁻¹ * a) := by field_simp
  rw [e]
  exact mul_le_mul_of_nonneg_left h3 (by positivity)

end Arithmetic

end CentralBond
end CoreLean

end
