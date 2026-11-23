/-
`prop:near-remainder` of BALABAN_CORE.tex (`a021c13be348`), the analytic part of its proof. Let `f` be holomorphic on
an open set `U ⊂ ℂ` which contains the closed discs of the radius `r > 0` about the points of `[0, 1]`, and bounded
by `E` on these discs (in the core: `σ ↦ f(τ + σ)` on `|σ| ≤ r = α₃/‖B‖_∞`, bounded by `E₀e^{-κd_j(X)}`). Then
`f(1) = Σ_{m=0}^4 f^{(m)}(0)/m! + ∫_0^1 (1 - τ)^4/4! f^{(5)}(τ) dτ` and the remainder is at most `E r^{-5}`
(`near_taylor`): Taylor's formula with the remainder in integral form for the restriction of `f` to `[0, 1]`
(whose derivatives within `[0, 1]` are the complex derivatives, `iteratedDerivWithin_eq`), and Cauchy's estimate
`|f^{(5)}(τ)| ≤ 5! r^{-5}E` with `∫_0^1(1 - τ)^4 dτ = 1/5`. With `r = α₃/‖B‖_∞` the bound is `E(‖B‖_∞/α₃)^5`, the
second line of `eq:near-taylor`.
-/
import Mathlib

open Set Filter Topology Metric

noncomputable section

namespace CoreLean
namespace NearRemainder

variable {f : ℂ → ℂ} {U : Set ℂ}

lemma iteratedDeriv_diffOn (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (k : ℕ) :
    DifferentiableOn ℂ (iteratedDeriv k f) U := by
  induction k with
  | zero => simpa using hf
  | succ k ih => rw [iteratedDeriv_succ]; exact ih.deriv hU

/-- The derivatives within `[0, 1]` of the restriction are the complex derivatives. -/
lemma iteratedDerivWithin_eq (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (hsub : ∀ t ∈ Icc (0 : ℝ) 1, (t : ℂ) ∈ U) (k : ℕ) :
    ∀ t ∈ Icc (0 : ℝ) 1, iteratedDerivWithin k (fun t : ℝ => f t) (Icc 0 1) t = iteratedDeriv k f t := by
  induction k with
  | zero => intro t _; simp
  | succ k ih =>
    intro t ht
    rw [iteratedDerivWithin_succ, derivWithin_congr (fun s hs => ih s hs) (ih t ht)]
    have hd : HasDerivAt (fun s : ℝ => iteratedDeriv k f s) (iteratedDeriv (k + 1) f t) t := by
      have h1 := ((iteratedDeriv_diffOn hU hf k) _ (hsub t ht)).differentiableAt
        (hU.mem_nhds (hsub t ht))
      rw [iteratedDeriv_succ]
      exact h1.hasDerivAt.comp_ofReal
    exact hd.hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc zero_lt_one t ht)

/-- **`eq:near-taylor`**. -/
theorem near_taylor (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) {r E : ℝ} (hr : 0 < r)
    (hsub : ∀ τ ∈ Icc (0 : ℝ) 1, closedBall (τ : ℂ) r ⊆ U)
    (hE : ∀ τ ∈ Icc (0 : ℝ) 1, ∀ z ∈ closedBall (τ : ℂ) r, ‖f z‖ ≤ E) :
    f 1 = ∑ m ∈ Finset.range 5, iteratedDeriv m f 0 / (m.factorial : ℂ) +
        ∫ τ in (0 : ℝ)..1, ((1 - τ) ^ 4 / 24 : ℝ) • iteratedDeriv 5 f τ ∧
      ‖∫ τ in (0 : ℝ)..1, ((1 - τ) ^ 4 / 24 : ℝ) • iteratedDeriv 5 f τ‖ ≤ E / r ^ 5 := by
  have hmem : ∀ t ∈ Icc (0 : ℝ) 1, (t : ℂ) ∈ U := fun t ht => hsub t ht (mem_closedBall_self hr.le)
  set g : ℝ → ℂ := fun t => f t
  have hI : uIcc (0 : ℝ) 1 = Icc 0 1 := uIcc_of_le zero_le_one
  -- the regularity of the restriction
  have hg : ContDiffOn ℝ ((4 : ℕ) + 1 : ℕ) g (uIcc 0 1) := by
    rw [hI]
    have h1 : ContDiffOn ℝ ((4 : ℕ) + 1 : ℕ) f U := (hf.contDiffOn hU).restrict_scalars ℝ
    exact h1.comp Complex.ofRealCLM.contDiff.contDiffOn fun t ht => hmem t ht
  have htay := taylor_integral_remainder hg
  rw [hI, taylor_within_apply] at htay
  have hD := iteratedDerivWithin_eq hU hf hmem
  -- the Taylor polynomial
  have hpoly : ∑ k ∈ Finset.range (4 + 1), ((k.factorial : ℝ)⁻¹ * (1 - 0) ^ k) •
      iteratedDerivWithin k g (Icc 0 1) 0 = ∑ m ∈ Finset.range 5, iteratedDeriv m f 0 / (m.factorial : ℂ) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hD k 0 ⟨le_refl 0, zero_le_one⟩]
    simp only [sub_zero, one_pow, mul_one, Complex.ofReal_zero]
    rw [Complex.real_smul, div_eq_inv_mul]
    push_cast
    ring
  -- the remainder
  have hrem : ∫ t in (0 : ℝ)..1, ((1 - t) ^ 4 / (Nat.factorial 4 : ℝ)) • iteratedDerivWithin (4 + 1) g (Icc 0 1) t =
      ∫ τ in (0 : ℝ)..1, ((1 - τ) ^ 4 / 24 : ℝ) • iteratedDeriv 5 f τ := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [hI] at ht
    rw [hD 5 t ht]
    norm_num [Nat.factorial]
  rw [hpoly, hrem] at htay
  refine ⟨by simp only [g] at htay; rw [← htay, Complex.ofReal_one]; ring, ?_⟩
  -- Cauchy's estimate
  have hC : ∀ t ∈ Icc (0 : ℝ) 1, ‖iteratedDeriv 5 f t‖ ≤ 120 * E / r ^ 5 := by
    intro t ht
    have hdc : DiffContOnCl ℂ f (ball (t : ℂ) r) := by
      refine DifferentiableOn.diffContOnCl ?_
      rw [closure_ball _ hr.ne']
      exact hf.mono (hsub t ht)
    have := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le 5 hr hdc
      fun z hz => hE t ht z (sphere_subset_closedBall hz)
    simpa [Nat.factorial] using this
  have hb : ∀ᵐ t ∂MeasureTheory.volume, t ∈ Ioc (0 : ℝ) 1 →
      ‖((1 - t) ^ 4 / 24 : ℝ) • iteratedDeriv 5 f t‖ ≤ (1 - t) ^ 4 / 24 * (120 * E / r ^ 5) := by
    refine Filter.Eventually.of_forall fun t ht => ?_
    have ht' : t ∈ Icc (0 : ℝ) 1 := Ioc_subset_Icc_self ht
    have h0 : 0 ≤ (1 - t) ^ 4 / 24 := by positivity
    rw [norm_smul, Real.norm_of_nonneg h0]
    exact mul_le_mul_of_nonneg_left (hC t ht') h0
  refine (intervalIntegral.norm_integral_le_of_norm_le zero_le_one hb ?_).trans_eq ?_
  · exact (Continuous.intervalIntegrable (by fun_prop) _ _)
  · have e : ∫ t in (0 : ℝ)..1, (1 - t) ^ 4 / 24 * (120 * E / r ^ 5) =
        (∫ t in (0 : ℝ)..1, (1 - t) ^ 4) * (5 * E / r ^ 5) := by
      rw [← intervalIntegral.integral_mul_const]
      refine intervalIntegral.integral_congr fun t _ => ?_
      ring
    rw [e, intervalIntegral.integral_comp_sub_left (fun t => t ^ 4), integral_pow]
    norm_num
    ring

/-- With `r = α₃/‖B‖_∞` the bound is `E(‖B‖_∞/α₃)^5`. -/
lemma ratio_form (E α₃ nB : ℝ) : E / (α₃ / nB) ^ 5 = E * (nB / α₃) ^ 5 := by
  rw [div_pow, div_pow, div_div_eq_mul_div, mul_div_assoc]

end NearRemainder
end CoreLean

end
