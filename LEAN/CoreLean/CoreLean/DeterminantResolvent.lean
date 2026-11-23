/-
`prop:step-interpolations` of BALABAN_CORE.tex (`a021c13be348`), the identity `eq:determinant-resolvent` in the
eigenvalues. For positive numbers `γ` and `λ₀`,
`∫_0^∞ (γ - λ₀)/((λ₀ + λ)(γ + λ)) dλ = log(γ/λ₀)` (`log_ratio_integral`, the core's computation with the
antiderivative `log(λ₀ + λ) - log(γ + λ)`), and hence, for the eigenvalues `γ_i > 0` of `Γ^{in}` (the inverse of the
covariance `C`), `½Σ_i log γ_i⁻¹ = -(N/2)log λ₀ - ½Σ_i∫_0^∞(γ_i - λ₀)/((λ₀ + λ)(γ_i + λ)) dλ` (`det_resolvent`), which
is `eq:determinant-resolvent` with the trace written as the sum over the eigenvalues; for a positive definite real
matrix `Γ^{in}` the identity itself, `½log det (Γ^{in})⁻¹ = -(N/2)log λ₀ - ½∫_0^∞(λ₀ + λ)⁻¹Tr((Γ^{in} - λ₀)(Γ^{in} + λ)⁻¹)dλ`
(`det_resolvent_matrix`, by the spectral theorem). Finally `eq:characteristic-interpolation` as the fundamental
theorem of calculus along the diagonal (`characteristic_interpolation`), with the regularity of `F` as hypothesis.
-/
import Mathlib

open MeasureTheory Set Filter Topology

noncomputable section

namespace CoreLean
namespace DetResolvent

lemma tendsto_log_ratio {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun x : ℝ => Real.log (a + x) - Real.log (b + x)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun x : ℝ => (a + x) / (b + x)) atTop (𝓝 1) := by
    have e : ∀ᶠ x : ℝ in atTop, (a + x) / (b + x) = 1 + (a - b) / (b + x) := by
      filter_upwards [eventually_gt_atTop 0] with x hx
      field_simp
      ring
    have h2 : Tendsto (fun x : ℝ => (a - b) / (b + x)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_left _ _ tendsto_id)
    have h3 := (tendsto_const_nhds (x := (1 : ℝ))).add h2
    rw [add_zero] at h3
    exact h3.congr' (e.mono fun x hx => hx.symm)
  have h4 := ((Real.continuousAt_log one_ne_zero).tendsto).comp h1
  rw [Real.log_one] at h4
  refine h4.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  simp only [Function.comp]
  rw [Real.log_div (by linarith) (by linarith)]

/-- **The scalar identity**: `∫_0^∞ (γ - λ₀)/((λ₀ + λ)(γ + λ)) dλ = log(γ/λ₀)`. -/
theorem log_ratio_integral {l0 g : ℝ} (hl0 : 0 < l0) (hg : 0 < g) :
    ∫ x in Ioi (0 : ℝ), (g - l0) / ((l0 + x) * (g + x)) = Real.log (g / l0) := by
  set F : ℝ → ℝ := fun x => Real.log (l0 + x) - Real.log (g + x)
  have hderiv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt F ((g - l0) / ((l0 + x) * (g + x))) x := by
    intro x hx
    rw [mem_Ioi] at hx
    have h1 : HasDerivAt (fun x => Real.log (l0 + x)) (1 / (l0 + x)) x := by
      have := ((hasDerivAt_id x).const_add l0).log (by simp; linarith)
      simpa using this
    have h2 : HasDerivAt (fun x => Real.log (g + x)) (1 / (g + x)) x := by
      have := ((hasDerivAt_id x).const_add g).log (by simp; linarith)
      simpa using this
    convert h1.sub h2 using 1
    field_simp
    ring
  have hcont : ContinuousWithinAt F (Ici 0) 0 := by
    have c1 : ContinuousAt (fun x : ℝ => Real.log (l0 + x)) 0 :=
      ((continuous_const.add continuous_id).continuousAt (x := (0 : ℝ))).log
        (by simpa using hl0.ne')
    have c2 : ContinuousAt (fun x : ℝ => Real.log (g + x)) 0 :=
      ((continuous_const.add continuous_id).continuousAt (x := (0 : ℝ))).log
        (by simpa using hg.ne')
    exact (c1.sub c2).continuousWithinAt
  have hlim := tendsto_log_ratio hl0 hg
  have hF0 : F 0 = Real.log l0 - Real.log g := by simp [F]
  rcases le_total l0 g with h | h
  · have hpos : ∀ x ∈ Ioi (0 : ℝ), 0 ≤ (g - l0) / ((l0 + x) * (g + x)) := fun x hx => by
      rw [mem_Ioi] at hx; exact div_nonneg (by linarith) (by positivity)
    rw [integral_Ioi_of_hasDerivAt_of_nonneg hcont hderiv hpos hlim, hF0,
      Real.log_div hg.ne' hl0.ne']
    ring
  · have hneg : ∀ x ∈ Ioi (0 : ℝ), (g - l0) / ((l0 + x) * (g + x)) ≤ 0 := fun x hx => by
      rw [mem_Ioi] at hx; exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
    rw [integral_Ioi_of_hasDerivAt_of_nonpos hcont hderiv hneg hlim, hF0,
      Real.log_div hg.ne' hl0.ne']
    ring

/-- **`eq:determinant-resolvent`** in the eigenvalues. -/
theorem det_resolvent {N : ℕ} (γ : Fin N → ℝ) (hγ : ∀ i, 0 < γ i) {l0 : ℝ} (hl0 : 0 < l0) :
    1 / 2 * ∑ i, Real.log (γ i)⁻¹ =
      -(N / 2 : ℝ) * Real.log l0 - 1 / 2 * ∑ i, ∫ x in Ioi (0 : ℝ), (γ i - l0) / ((l0 + x) * (γ i + x)) := by
  simp only [log_ratio_integral hl0 (hγ _), Real.log_inv, Real.log_div (hγ _).ne' hl0.ne',
    Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Finset.sum_neg_distrib]
  ring

/-- The integrand is integrable. -/
lemma ratio_integrable {l0 g : ℝ} (hl0 : 0 < l0) (hg : 0 < g) :
    IntegrableOn (fun x : ℝ => (g - l0) / ((l0 + x) * (g + x))) (Ioi 0) := by
  set F : ℝ → ℝ := fun x => Real.log (l0 + x) - Real.log (g + x)
  have hderiv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt F ((g - l0) / ((l0 + x) * (g + x))) x := by
    intro x hx
    rw [mem_Ioi] at hx
    have h1 : HasDerivAt (fun x => Real.log (l0 + x)) (1 / (l0 + x)) x := by
      have := ((hasDerivAt_id x).const_add l0).log (by simp; linarith)
      simpa using this
    have h2 : HasDerivAt (fun x => Real.log (g + x)) (1 / (g + x)) x := by
      have := ((hasDerivAt_id x).const_add g).log (by simp; linarith)
      simpa using this
    convert h1.sub h2 using 1
    field_simp
    ring
  have hcont : ContinuousWithinAt F (Ici 0) 0 := by
    have c1 : ContinuousAt (fun x : ℝ => Real.log (l0 + x)) 0 :=
      ((continuous_const.add continuous_id).continuousAt (x := (0 : ℝ))).log (by simpa using hl0.ne')
    have c2 : ContinuousAt (fun x : ℝ => Real.log (g + x)) 0 :=
      ((continuous_const.add continuous_id).continuousAt (x := (0 : ℝ))).log (by simpa using hg.ne')
    exact (c1.sub c2).continuousWithinAt
  have hlim := tendsto_log_ratio hl0 hg
  rcases le_total l0 g with h | h
  · exact integrableOn_Ioi_deriv_of_nonneg hcont hderiv (fun x hx => by
      rw [mem_Ioi] at hx; exact div_nonneg (by linarith) (by positivity)) hlim
  · exact integrableOn_Ioi_deriv_of_nonpos hcont hderiv (fun x hx => by
      rw [mem_Ioi] at hx; exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)) hlim

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

lemma conj_mul (U : Matrix n n ℝ) (hU : star U * U = 1) (d e : n → ℝ) :
    (U * diagonal d * star U) * (U * diagonal e * star U) = U * diagonal (fun i => d i * e i) * star U := by
  rw [← diagonal_mul_diagonal]
  calc U * diagonal d * star U * (U * diagonal e * star U)
      = U * diagonal d * (star U * U) * diagonal e * star U := by simp only [Matrix.mul_assoc]
    _ = U * (diagonal d * diagonal e) * star U := by rw [hU, Matrix.mul_one]; simp only [Matrix.mul_assoc]

lemma conj_sub (U : Matrix n n ℝ) (hU : U * star U = 1) (d : n → ℝ) (c : ℝ) :
    U * diagonal d * star U + c • (1 : Matrix n n ℝ) = U * diagonal (fun i => d i + c) * star U := by
  have e : diagonal (fun i => d i + c) = diagonal d + c • (1 : Matrix n n ℝ) := by
    ext i j
    by_cases h : i = j
    · subst h; simp
    · simp [Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]
  rw [e, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hU]

/-- The trace of the resolvent in the eigenvalues. -/
lemma trace_resolvent (U : Matrix n n ℝ) (hU1 : star U * U = 1) (hU2 : U * star U = 1) (d : n → ℝ)
    (l0 x : ℝ) (hd : ∀ i, d i + x ≠ 0) :
    trace ((U * diagonal d * star U + (-l0) • (1 : Matrix n n ℝ)) *
      (U * diagonal d * star U + x • (1 : Matrix n n ℝ))⁻¹) = ∑ i, (d i - l0) / (d i + x) := by
  rw [conj_sub U hU2, conj_sub U hU2]
  have hinv : (U * diagonal (fun i => d i + x) * star U)⁻¹ = U * diagonal (fun i => (d i + x)⁻¹) * star U := by
    refine Matrix.inv_eq_right_inv ?_
    rw [conj_mul U hU1]
    have : (fun i => (d i + x) * (d i + x)⁻¹) = fun _ => (1 : ℝ) := funext fun i => mul_inv_cancel₀ (hd i)
    rw [this, diagonal_one, Matrix.mul_one, hU2]
  rw [hinv, conj_mul U hU1, Matrix.trace_mul_cycle, hU1, Matrix.one_mul, trace_diagonal]
  exact Finset.sum_congr rfl fun i _ => by rw [div_eq_mul_inv]; ring

/-- **`eq:determinant-resolvent`** for a positive definite real matrix `Γ^{in}` with the covariance `C = (Γ^{in})⁻¹`:
`½log det C = -(N/2)log λ₀ - ½∫_0^∞(λ₀ + λ)⁻¹Tr((Γ^{in} - λ₀)(Γ^{in} + λ)⁻¹)dλ`, `N = #n`. -/
theorem det_resolvent_matrix (A : Matrix n n ℝ) (hA : A.PosDef) {l0 : ℝ} (hl0 : 0 < l0) :
    1 / 2 * Real.log (A⁻¹).det = -(Fintype.card n / 2 : ℝ) * Real.log l0 -
      1 / 2 * ∫ x in Ioi (0 : ℝ), 1 / (l0 + x) *
        trace ((A + (-l0) • (1 : Matrix n n ℝ)) * (A + x • (1 : Matrix n n ℝ))⁻¹) := by
  set γ := hA.1.eigenvalues
  have hγ : ∀ i, 0 < γ i := hA.eigenvalues_pos
  set U : Matrix n n ℝ := (hA.1.eigenvectorUnitary : Matrix n n ℝ)
  have hU1 : star U * U = 1 := Unitary.coe_star_mul_self _
  have hU2 : U * star U = 1 := Unitary.coe_mul_star_self _
  have hAU : A = U * diagonal γ * star U := by
    have := hA.1.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply, RCLike.ofReal_real_eq_id, Function.id_comp] at this
    exact this
  have hdet : A.det = ∏ i, γ i := by
    have := hA.1.det_eq_prod_eigenvalues
    simpa using this
  have hint : ∫ x in Ioi (0 : ℝ), 1 / (l0 + x) *
      trace ((A + (-l0) • (1 : Matrix n n ℝ)) * (A + x • (1 : Matrix n n ℝ))⁻¹) =
      ∫ x in Ioi (0 : ℝ), ∑ i, (γ i - l0) / ((l0 + x) * (γ i + x)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    rw [mem_Ioi] at hx
    rw [hAU, trace_resolvent U hU1 hU2 γ l0 x (fun i => by linarith [hγ i]), Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have : l0 + x ≠ 0 := by linarith
    have : γ i + x ≠ 0 := by linarith [hγ i]
    field_simp
  rw [hint, integral_finsetSum _ (fun i _ => ratio_integrable hl0 (hγ i))]
  simp only [log_ratio_integral hl0 (hγ _)]
  rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv', hdet, Real.log_inv,
    Real.log_prod (fun i _ => (hγ i).ne')]
  simp only [Real.log_div (hγ _).ne' hl0.ne', Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]
  ring

/-- **`eq:characteristic-interpolation`**: for `F` with `F(0) = 0`, continuous along the diagonal of `[0, 1]^B` and
differentiable at its interior points, `F(1, …, 1) = ∫_0^1 Σ_b ∂F/∂τ_b(t, …, t) dt`. -/
theorem characteristic_interpolation {B : Type*} [Fintype B] [DecidableEq B] (F : (B → ℝ) → ℝ)
    (DF : ℝ → (B → ℝ) →L[ℝ] ℝ) (hc : ContinuousOn (fun t => F (fun _ => t)) (Icc 0 1))
    (hd : ∀ t ∈ Ioo (0 : ℝ) 1, HasFDerivAt F (DF t) (fun _ => t))
    (hi : IntervalIntegrable (fun t => ∑ b, DF t (Pi.single b 1)) MeasureTheory.volume 0 1) (h0 : F 0 = 0) :
    F (fun _ => 1) = ∫ t in (0 : ℝ)..1, ∑ b, DF t (Pi.single b 1) := by
  have hderiv : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt (fun t => F (fun _ => t)) (∑ b, DF t (Pi.single b 1)) t := by
    intro t ht
    have hdiag : HasDerivAt (fun t : ℝ => (fun _ : B => t)) (fun _ => (1 : ℝ)) t :=
      hasDerivAt_pi.2 fun _ => hasDerivAt_id t
    have := (hd t ht).comp_hasDerivAt t hdiag
    have e : (∑ b, DF t (Pi.single b 1)) = DF t (fun _ => 1) := by
      rw [← map_sum]
      congr 1
      funext c
      simp [Finset.sum_apply, Pi.single_apply]
    rw [e]
    exact this
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hc hderiv hi]
  have : F (fun _ => (0 : ℝ)) = 0 := h0
  rw [this, sub_zero]

end DetResolvent
end CoreLean

end
