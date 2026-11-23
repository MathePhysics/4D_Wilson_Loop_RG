/-
`prop:linearising-pair` of BALABAN_CORE.tex: `eq:remainder-second` and `eq:remainder-third` from
`eq:remainder-bounds` by the formula of Cauchy.

Let `𝖢` be holomorphic on the ball `‖A‖ < r` (`r = c'₄/L`) of a complex normed space `X`, with values in a
complete space `Y`, and let a weighted norm be `w(y) = ‖M_w y‖` for a continuous linear map `M_w` (the
multiplication by the weight `ϖ`), `v` any function of the forms (`v(δ) = ‖ϖδ‖_{∞,(-1)}`). The second bound of
`eq:remainder-bounds` is `w(𝖢'(A)δ) ≤ κ'‖A‖v(δ)` for `‖A‖ < r`. On the disc `|z|‖A‖ < r` the function
`g(z) = M_w𝖢'(zA)δ` is holomorphic (`ray_differentiableOn`), `g'(0) = M_w D²𝖢(0)[A, δ] = M_w 2𝖢⁽²⁾(A, δ)`
(`hasDerivAt_ray`), and `g(0) = 0`.

* `remainder_second` (`eq:remainder-second`): `w(2𝖢⁽²⁾(A, δ)) ≤ κ'‖A‖v(δ)` for all `A`, by Cauchy's bound of
  `g'(0)` on any circle inside the disc.
* `remainder_third` (`eq:remainder-third`): for `‖A‖ ≤ r/2`, `w(𝖢₃'(A)δ) ≤ (2/r)κ'‖A‖²v(δ)`, where
  `𝖢₃'(A)δ = 𝖢'(A)δ - 2𝖢⁽²⁾(A, δ) = g(1) - g(0) - g'(0)`: the Taylor coefficients of the orders `n ≥ 2` on the
  circle `|z| = ρ`, `1 < ρ < r/‖A‖`, sum to at most `κ'‖A‖v(δ)/(ρ - 1)` (`norm_taylor_two_le_ball`), and the
  limit `ρ → r/‖A‖` gives `κ'‖A‖v(δ)/(r/‖A‖ - 1) ≤ (2/r)κ'‖A‖²v(δ)`.
-/
import Mathlib

open Filter Asymptotics Metric
open scoped Topology Nat

noncomputable section

namespace CoreLean

namespace Linearising

/-- Cauchy's estimate for the remainder of the order two on a disc: for `g` complex differentiable on the
ball of radius `R` and `1 < ρ < R` with `‖g‖ ≤ M` on `|z| = ρ`, `‖g(1) - g(0) - g'(0)‖ ≤ Mρ⁻²(1 - ρ⁻¹)⁻¹`. -/
theorem norm_taylor_two_le_ball {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {g : ℂ → E} {R ρ M : ℝ} (hg : DifferentiableOn ℂ g (ball 0 R)) (hρ1 : 1 < ρ) (hρR : ρ < R)
    (hM : ∀ z : ℂ, ‖z‖ = ρ → ‖g z‖ ≤ M) :
    ‖g 1 - g 0 - deriv g 0‖ ≤ M * ρ⁻¹ ^ 2 * (1 - ρ⁻¹)⁻¹ := by
  have hρ0 : 0 < ρ := by linarith
  have h1 : (1 : ℂ) ∈ ball (0 : ℂ) R := by simp; linarith
  have hT := Complex.hasSum_taylorSeries_on_ball hg h1
  simp only [sub_zero, one_pow, one_smul] at hT
  have hT2 := (hasSum_nat_add_iff' 2).mpr hT
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.factorial_zero,
    Nat.factorial_one, Nat.cast_one, inv_one, one_smul, iteratedDeriv_zero, iteratedDeriv_one] at hT2
  have hdc : DiffContOnCl ℂ g (ball 0 ρ) :=
    (hg.mono (by rw [closure_ball _ hρ0.ne']; exact closedBall_subset_ball hρR)).diffContOnCl
  have hcoef : ∀ k : ℕ, ‖((k + 2)! : ℂ)⁻¹ • iteratedDeriv (k + 2) g 0‖ ≤ M * ρ⁻¹ ^ 2 * ρ⁻¹ ^ k := by
    intro k
    have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (k + 2) hρ0 hdc
      fun z hz => hM z (by simpa using hz)
    have hf : (0 : ℝ) < ((k + 2)! : ℝ) := by exact_mod_cast Nat.factorial_pos _
    rw [norm_smul, norm_inv, Complex.norm_natCast]
    calc ((k + 2)! : ℝ)⁻¹ * ‖iteratedDeriv (k + 2) g 0‖
        ≤ ((k + 2)! : ℝ)⁻¹ * ((k + 2)! * M / ρ ^ (k + 2)) :=
          mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hf.le)
      _ = M * ρ⁻¹ ^ 2 * ρ⁻¹ ^ k := by
          rw [inv_pow, inv_pow, pow_add]
          field_simp
  have hq : ρ⁻¹ < 1 := inv_lt_one_of_one_lt₀ hρ1
  have hgeo := (hasSum_geometric_of_lt_one (inv_nonneg.mpr hρ0.le) hq).mul_left (M * ρ⁻¹ ^ 2)
  have hle := hT2.norm_le_of_bounded hgeo hcoef
  have e : g 1 - g 0 - deriv g 0 = g 1 - (g 0 + deriv g 0) := by abel
  rw [e]
  exact hle

variable {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [NormedAddCommGroup Y]
  [NormedSpace ℂ Y] [CompleteSpace Y] [NormedAddCommGroup Z] [NormedSpace ℂ Z]

/-- `z ↦ M_w𝖢'(zA)δ` is holomorphic on the disc `|z| < r/‖A‖`. -/
lemma ray_differentiableOn {C : X → Y} {r : ℝ} (hC : AnalyticOnNhd ℂ C (ball 0 r)) (Mw : Y →L[ℂ] Z)
    {A : X} (hA : A ≠ 0) (δ : X) :
    DifferentiableOn ℂ (fun z : ℂ => Mw (fderiv ℂ C (z • A) δ)) (ball 0 (r / ‖A‖)) := by
  intro z hz
  have hAn : 0 < ‖A‖ := norm_pos_iff.mpr hA
  have hzA : z • A ∈ ball (0 : X) r := by
    have : ‖z‖ < r / ‖A‖ := by simpa using hz
    rw [mem_ball_zero_iff, norm_smul]
    rwa [lt_div_iff₀ hAn] at this
  have h1 : AnalyticAt ℂ (fderiv ℂ C) (z • A) := hC.fderiv _ hzA
  have h2 : AnalyticAt ℂ (fun s : ℂ => s • A) z := analyticAt_id.smul analyticAt_const
  have h4 : AnalyticAt ℂ (fun s : ℂ => Mw (fderiv ℂ C (s • A) δ)) z :=
    (Mw.analyticAt _).comp (((ContinuousLinearMap.apply ℂ Y δ).analyticAt _).comp (h1.comp_of_eq h2 rfl))
  exact h4.differentiableAt.differentiableWithinAt

/-- `d/dz M_w𝖢'(zA)δ|₀ = M_w D²𝖢(0)[A, δ]`. -/
lemma hasDerivAt_ray {C : X → Y} {r : ℝ} (hr : 0 < r) (hC : AnalyticOnNhd ℂ C (ball 0 r))
    (Mw : Y →L[ℂ] Z) (A δ : X) :
    HasDerivAt (fun z : ℂ => Mw (fderiv ℂ C (z • A) δ)) (Mw (fderiv ℂ (fderiv ℂ C) 0 A δ)) 0 := by
  have h1 : HasFDerivAt (fderiv ℂ C) (fderiv ℂ (fderiv ℂ C) 0) ((0 : ℂ) • A) := by
    rw [zero_smul]; exact (hC.fderiv 0 (mem_ball_self hr)).differentiableAt.hasFDerivAt
  have hl : HasDerivAt (fun s : ℂ => s • A) A 0 := by
    simpa using (hasDerivAt_id (0 : ℂ)).smul_const A
  exact (Mw.comp (ContinuousLinearMap.apply ℂ Y δ)).hasFDerivAt.comp_hasDerivAt 0 (h1.comp_hasDerivAt 0 hl)

/-- `eq:remainder-second`: `w(2𝖢⁽²⁾(A, δ)) ≤ κ'‖A‖v(δ)` for every `A`, with `2𝖢⁽²⁾(A, δ) = D²𝖢(0)[A, δ]`. -/
theorem remainder_second {C : X → Y} {r κ' : ℝ} (hr : 0 < r) (hC : AnalyticOnNhd ℂ C (ball 0 r))
    (Mw : Y →L[ℂ] Z) (v : X → ℝ)
    (hbound : ∀ A, ‖A‖ < r → ∀ δ, ‖Mw (fderiv ℂ C A δ)‖ ≤ κ' * ‖A‖ * v δ) (A δ : X) :
    ‖Mw (fderiv ℂ (fderiv ℂ C) 0 A δ)‖ ≤ κ' * ‖A‖ * v δ := by
  by_cases hA : A = 0
  · subst hA; simp
  have hAn : 0 < ‖A‖ := norm_pos_iff.mpr hA
  set R := r / ‖A‖ with hR
  have hR0 : 0 < R := by positivity
  set ρ := R / 2 with hρdef
  have hρ0 : 0 < ρ := by positivity
  have hg := ray_differentiableOn hC Mw hA δ
  have hdc : DiffContOnCl ℂ (fun z : ℂ => Mw (fderiv ℂ C (z • A) δ)) (ball 0 ρ) :=
    (hg.mono (by rw [closure_ball _ hρ0.ne']; exact closedBall_subset_ball (by linarith [hρdef, hR, hR0]))).diffContOnCl
  have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hρ0 hdc (C := κ' * (ρ * ‖A‖) * v δ)
    fun z hz => by
      have hz' : ‖z‖ = ρ := by simpa using hz
      have hzA : ‖z • A‖ < r := by
        rw [norm_smul, hz']
        have : ρ * ‖A‖ = r / 2 := by rw [show ρ = R / 2 from rfl, hR]; field_simp
        linarith
      have := hbound _ hzA δ
      rwa [norm_smul, hz'] at this
  rw [(hasDerivAt_ray hr hC Mw A δ).deriv] at h
  refine h.trans (le_of_eq ?_)
  field_simp

/-- `eq:remainder-third`: for `‖A‖ ≤ r/2`, `w(𝖢'(A)δ - 2𝖢⁽²⁾(A, δ)) ≤ (2/r)κ'‖A‖²v(δ)`. -/
theorem remainder_third [CompleteSpace Z] {C : X → Y} {r κ' : ℝ} (hr : 0 < r)
    (hC : AnalyticOnNhd ℂ C (ball 0 r)) (Mw : Y →L[ℂ] Z) (v : X → ℝ) (hv0 : ∀ x, 0 ≤ v x)
    (hκ' : 0 ≤ κ') (hbound : ∀ A, ‖A‖ < r → ∀ δ, ‖Mw (fderiv ℂ C A δ)‖ ≤ κ' * ‖A‖ * v δ) {A : X}
    (hA : ‖A‖ ≤ r / 2) (δ : X) :
    ‖Mw (fderiv ℂ C A δ - fderiv ℂ (fderiv ℂ C) 0 A δ)‖ ≤ 2 / r * κ' * ‖A‖ ^ 2 * v δ := by
  have hvδ := hv0 δ
  -- `g(0) = 0`
  have hg0 : ∀ δ', Mw (fderiv ℂ C 0 δ') = 0 := fun δ' => by
    have := hbound 0 (by simpa using hr) δ'
    simpa using this
  by_cases hA0 : A = 0
  · subst hA0
    simp [hg0]
  have hAn : 0 < ‖A‖ := norm_pos_iff.mpr hA0
  set R := r / ‖A‖ with hR
  have hR2 : 2 ≤ R := by rw [hR, le_div_iff₀ hAn]; linarith
  set g : ℂ → Z := fun z => Mw (fderiv ℂ C (z • A) δ) with hgdef
  have hg := ray_differentiableOn hC Mw hA0 δ
  have hval : Mw (fderiv ℂ C A δ - fderiv ℂ (fderiv ℂ C) 0 A δ) = g 1 - g 0 - deriv g 0 := by
    rw [(hasDerivAt_ray hr hC Mw A δ).deriv]
    simp [g, hg0, map_sub]
  rw [hval]
  set c := κ' * ‖A‖ * v δ with hc
  have hc0 : 0 ≤ c := by positivity
  -- the bound on every circle `|z| = ρ`, `1 < ρ < R`
  have hρ : ∀ ρ ∈ Set.Ioo 1 R, ‖g 1 - g 0 - deriv g 0‖ ≤ c / (ρ - 1) := by
    rintro ρ ⟨hρ1, hρR⟩
    have hρ0 : 0 < ρ := by linarith
    have h := norm_taylor_two_le_ball hg hρ1 hρR (M := κ' * (ρ * ‖A‖) * v δ) fun z hz => by
      have hzA : ‖z • A‖ < r := by
        rw [norm_smul, hz]
        have : ρ * ‖A‖ < R * ‖A‖ := mul_lt_mul_of_pos_right hρR hAn
        rwa [hR, div_mul_cancel₀ _ hAn.ne'] at this
      have := hbound _ hzA δ
      rwa [norm_smul, hz] at this
    refine h.trans (le_of_eq ?_)
    have hρ1' : ρ - 1 ≠ 0 := by linarith
    rw [hc]
    field_simp
  -- the limit `ρ → R`
  have hlim : Tendsto (fun ρ : ℝ => c / (ρ - 1)) (𝓝[<] R) (𝓝 (c / (R - 1))) :=
    ((continuousAt_const.div (continuousAt_id.sub continuousAt_const)
      (by linarith : R - 1 ≠ 0)).tendsto).mono_left nhdsWithin_le_nhds
  have hX : ‖g 1 - g 0 - deriv g 0‖ ≤ c / (R - 1) :=
    ge_of_tendsto hlim (by
      filter_upwards [Ioo_mem_nhdsLT (by linarith : (1 : ℝ) < R)] with ρ hρ' using hρ ρ hρ')
  refine hX.trans ?_
  -- `1/(R - 1) ≤ 2/R = 2‖A‖/r`
  have hR1 : 0 < R - 1 := by linarith
  rw [div_le_iff₀ hR1, hc, hR]
  have e : 2 / r * κ' * ‖A‖ ^ 2 * v δ * (r / ‖A‖ - 1) = κ' * ‖A‖ * v δ * (2 - 2 * ‖A‖ / r) := by
    field_simp
  rw [e]
  have h2 : 1 ≤ 2 - 2 * ‖A‖ / r := by
    have : 2 * ‖A‖ / r ≤ 1 := by rw [div_le_one hr]; linarith
    linarith
  nlinarith

end Linearising

end CoreLean
