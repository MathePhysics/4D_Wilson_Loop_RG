/-
`prop:momentum-space` of BALABAN_CORE.tex (`fc142d786d90`): the geometric sums behind `eq:average-symbols`, and the bounds
of `σ_{μν}` in (iv). With `n = L^k = 2r + 1` and `a₀ = 1/n`:

* `dirichlet_mean`: `n⁻¹Σ_{|j| ≤ r}e^{ia₀pj} = u` (one factor of `u_k(p)`), the sum written over `i = j + r < n`;
* `path_mean`: `n⁻¹Σ_{t < n}e^{ia₀pt} = v_μ(p)`;
* `vs_mul_diff`, `vs_mul_diff_shift`: `v_μ(p)∂_μ(p) = e^{ip} - 1 = ∂¹_μ(p')` for `p = p' + 2πm`, `∂_μ(p) = (e^{ia₀p} - 1)/a₀`;
* `sigma_bounds`: `γ₀γ₁⁻² ≤ σ_{μν}(p') ≤ γ₁γ₀⁻²` with `σ_{μν}` of `eq:minimal-form`, from `phi_bounds`.
-/
import CoreLean.MomentumPhi

open Real Complex

noncomputable section

namespace CoreLean
namespace MomentumSymbols

/-- `e^{ix} - e^{-ix} = 2i sin x`. -/
lemma exp_sub_exp_neg (x : ℝ) :
    Complex.exp (I * (x : ℂ)) - Complex.exp (I * ((-x : ℝ) : ℂ)) = 2 * I * (Real.sin x : ℂ) := by
  rw [mul_comm I, mul_comm I, Complex.exp_mul_I, Complex.exp_mul_I]
  push_cast
  rw [Complex.cos_neg, Complex.sin_neg]
  ring

/-- **The mean over a block of a plane wave, one direction**: `n⁻¹Σ_{|j| ≤ r}e^{ipj/n} = sin(p/2)/(n sin(p/(2n)))`, the
value one where the denominator vanishes; the sum runs over `i = j + r ∈ {0, …, 2r}`. The sum telescopes after
multiplication by `e^{ip/(2n)} - e^{-ip/(2n)}`. -/
theorem dirichlet_mean (r : ℕ) (p : ℝ) :
    (1 / ((2 * r + 1 : ℕ) : ℂ)) * ∑ i ∈ Finset.range (2 * r + 1),
      Complex.exp (I * ((p / (2 * r + 1 : ℕ) * ((i : ℝ) - r) : ℝ) : ℂ)) = (uf (2 * r + 1) p : ℂ) := by
  set n := 2 * r + 1 with hn
  have hn0 : (0 : ℝ) < n := by positivity
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn0.ne'
  set s := p / (2 * n) with hs
  unfold uf
  split_ifs with h0
  · -- `s ∈ πℤ`: every term is one
    obtain ⟨k, hk⟩ := Real.sin_eq_zero_iff.1 h0
    have hterm : ∀ i : ℕ, Complex.exp (I * ((p / n * ((i : ℝ) - r) : ℝ) : ℂ)) = 1 := by
      intro i
      rw [Complex.exp_eq_one_iff]
      refine ⟨k * ((i : ℤ) - r), ?_⟩
      have : p / n = 2 * (k * π) := by rw [hk]; field_simp
      rw [this]
      push_cast
      ring
    simp only [hterm, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    push_cast
    field_simp
  · -- the telescoping sum
    set E : ℝ → ℂ := fun x => Complex.exp (I * (x : ℂ)) with hE
    have hsin : (Real.sin s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 h0
    have hEE : ∀ x : ℝ, E x - E (-x) = 2 * I * (Real.sin x : ℂ) := fun x => by
      simp only [hE]; exact exp_sub_exp_neg x
    have htel : (E s - E (-s)) * ∑ i ∈ Finset.range n, E (p / n * ((i : ℝ) - r)) =
        E (p / 2) - E (-(p / 2)) := by
      rw [Finset.mul_sum]
      have hstep : ∀ i ∈ Finset.range n, (E s - E (-s)) * E (p / n * ((i : ℝ) - r)) =
          E (2 * s * (((i + 1 : ℕ) : ℝ) - r) - s) - E (2 * s * ((i : ℝ) - r) - s) := by
        intro i _
        have ha : p / n * ((i : ℝ) - r) = 2 * s * ((i : ℝ) - r) := by rw [hs]; field_simp
        simp only [hE]
        rw [ha, sub_mul, ← Complex.exp_add, ← Complex.exp_add]
        have e1 : I * (s : ℂ) + I * ((2 * s * ((i : ℝ) - r) : ℝ) : ℂ) =
            I * ((2 * s * (((i + 1 : ℕ) : ℝ) - r) - s : ℝ) : ℂ) := by push_cast; ring
        have e2 : I * ((-s : ℝ) : ℂ) + I * ((2 * s * ((i : ℝ) - r) : ℝ) : ℂ) =
            I * ((2 * s * ((i : ℝ) - r) - s : ℝ) : ℂ) := by push_cast; ring
        rw [e1, e2]
      rw [Finset.sum_congr rfl hstep,
        Finset.sum_range_sub (fun i => E (2 * s * ((i : ℝ) - r) - s)) n]
      have hn1 : 2 * s * (((n : ℕ) : ℝ) - r) - s = p / 2 := by rw [hs, hn]; push_cast; field_simp; ring
      have hn2 : 2 * s * (((0 : ℕ) : ℝ) - r) - s = -(p / 2) := by rw [hs, hn]; push_cast; field_simp; ring
      rw [hn1, hn2]
    rw [hEE, hEE] at htel
    have hsum : ∑ i ∈ Finset.range n, E (p / n * ((i : ℝ) - r)) = (Real.sin (p / 2) : ℂ) / (Real.sin s : ℂ) := by
      rw [eq_div_iff hsin]
      have h2I : (2 * I : ℂ) ≠ 0 := by simp
      apply mul_left_cancel₀ h2I
      rw [← htel]; ring
    have hs' : (s : ℂ) = (p : ℂ) / ((n : ℂ) * 2) := by rw [hs]; push_cast; ring
    simp only [hE] at hsum
    rw [hsum]
    push_cast
    field_simp
    rw [hs']

/-- **The mean along a straight path of a plane wave**: `n⁻¹Σ_{t < n}e^{ia₀pt} = v_μ(p)`, `a₀ = 1/n`. -/
theorem path_mean (n : ℕ) (hn : 1 ≤ n) (p : ℝ) :
    (1 / (n : ℂ)) * ∑ t ∈ Finset.range n, Complex.exp (I * (((1 / n : ℝ) * p * t : ℝ) : ℂ)) = vs n p := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn0.ne'
  set x := Complex.exp (I * (((1 / n : ℝ) * p : ℝ) : ℂ)) with hx
  have hpow : ∀ t : ℕ, Complex.exp (I * (((1 / n : ℝ) * p * t : ℝ) : ℂ)) = x ^ t := by
    intro t
    rw [hx, ← Complex.exp_nat_mul]
    congr 1; push_cast; ring
  have hxn : x ^ n = Complex.exp (I * p) := by
    rw [← hpow]; congr 1; push_cast; field_simp
  simp only [hpow]
  unfold vs
  rw [← hx]
  split_ifs with h0
  · have hx1 : x = 1 := sub_eq_zero.1 h0
    simp [hx1]
    field_simp
  · rw [geom_sum_eq (fun h => h0 (sub_eq_zero.2 h)), hxn]
    field_simp

/-- **`v_μ(p)∂_μ(p) = e^{ip} - 1`**, `∂_μ(p) = (e^{ia₀p} - 1)/a₀ = n(e^{ia₀p} - 1)`, for every `p`. -/
theorem vs_mul_diff (n : ℕ) (hn : 1 ≤ n) (p : ℝ) :
    vs n p * ((Complex.exp (I * (((1 / n : ℝ) * p : ℝ) : ℂ)) - 1) / ((1 / n : ℝ) : ℂ)) = Complex.exp (I * p) - 1 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn0.ne'
  set x := Complex.exp (I * (((1 / n : ℝ) * p : ℝ) : ℂ)) with hx
  have hxn : x ^ n = Complex.exp (I * p) := by
    rw [hx, ← Complex.exp_nat_mul]; congr 1; push_cast; field_simp
  unfold vs
  rw [← hx]
  split_ifs with h0
  · have hx1 : x = 1 := sub_eq_zero.1 h0
    rw [← hxn, hx1]; simp
  · push_cast
    field_simp

/-- `e^{i(p' + 2πm)} = e^{ip'}`: so `v_μ(p' + l)∂_μ(p' + l) = ∂¹_μ(p')`. -/
theorem vs_mul_diff_shift (n : ℕ) (hn : 1 ≤ n) (p' : ℝ) (m : ℤ) :
    vs n (p' + 2 * π * m) * ((Complex.exp (I * (((1 / n : ℝ) * (p' + 2 * π * m) : ℝ) : ℂ)) - 1) / ((1 / n : ℝ) : ℂ)) =
      Complex.exp (I * p') - 1 := by
  rw [vs_mul_diff n hn]
  congr 1
  rw [show (I * ((p' + 2 * π * m : ℝ) : ℂ)) = I * (p' : ℂ) + (m : ℂ) * (2 * π * I) by push_cast; ring,
    Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- The bounds of `(x_μx_νΣ_λc_λ/x_λ)⁻¹` for `x_λ ∈ [γ₀, γ₁]` and weights `c_λ ≥ 0` of the sum one. -/
lemma sigma_abstract {γ0 γ1 : ℝ} (h0 : 0 < γ0) (x : Fin 4 → ℝ) (hx : ∀ l, γ0 ≤ x l ∧ x l ≤ γ1) (c : Fin 4 → ℝ)
    (hc : ∀ l, 0 ≤ c l) (hc1 : ∑ l, c l = 1) (μ ν : Fin 4) :
    γ0 / γ1 ^ 2 ≤ (x μ * x ν * ∑ l, c l / x l)⁻¹ ∧ (x μ * x ν * ∑ l, c l / x l)⁻¹ ≤ γ1 / γ0 ^ 2 := by
  have h1 : 0 < γ1 := lt_of_lt_of_le h0 ((hx 0).1.trans (hx 0).2)
  have hxpos : ∀ l, 0 < x l := fun l => lt_of_lt_of_le h0 (hx l).1
  set S := ∑ l, c l / x l
  have hSl : 1 / γ1 ≤ S := by
    calc 1 / γ1 = ∑ l, c l / γ1 := by rw [← Finset.sum_div, hc1]
      _ ≤ S := Finset.sum_le_sum fun l _ => div_le_div_of_nonneg_left (hc l) (hxpos l) (hx l).2
  have hSu : S ≤ 1 / γ0 := by
    calc S ≤ ∑ l, c l / γ0 := Finset.sum_le_sum fun l _ => div_le_div_of_nonneg_left (hc l) h0 (hx l).1
      _ = 1 / γ0 := by rw [← Finset.sum_div, hc1]
  have hSpos : 0 < S := lt_of_lt_of_le (by positivity) hSl
  have hP : 0 < x μ * x ν * S := by have := hxpos μ; have := hxpos ν; positivity
  have hPle : x μ * x ν * S ≤ γ1 ^ 2 / γ0 := by
    calc x μ * x ν * S ≤ γ1 * γ1 * (1 / γ0) :=
          mul_le_mul (mul_le_mul (hx μ).2 (hx ν).2 (hxpos ν).le h1.le) hSu hSpos.le (by positivity)
      _ = γ1 ^ 2 / γ0 := by ring
  have hPge : γ0 ^ 2 / γ1 ≤ x μ * x ν * S := by
    calc γ0 ^ 2 / γ1 = γ0 * γ0 * (1 / γ1) := by ring
      _ ≤ x μ * x ν * S :=
          mul_le_mul (mul_le_mul (hx μ).1 (hx ν).1 h0.le (hxpos μ).le) hSl (div_nonneg zero_le_one h1.le)
            (mul_nonneg (hxpos μ).le (hxpos ν).le)
  constructor
  · calc γ0 / γ1 ^ 2 = (γ1 ^ 2 / γ0)⁻¹ := by field_simp
      _ ≤ _ := inv_anti₀ hP hPle
  · calc (x μ * x ν * S)⁻¹ ≤ (γ0 ^ 2 / γ1)⁻¹ := inv_anti₀ (div_pos (pow_pos h0 2) h1) hPge
      _ = γ1 / γ0 ^ 2 := by field_simp

/-- `σ_{μν}(p') = (Δ₀φ_μ Δ₀φ_ν Σ_λ|∂¹_λ|²/(Δ₀²φ_λ))⁻¹`, `eq:minimal-form`. -/
def sigma (r : ℕ) (μ ν : Fin 4) (p : Fin 4 → ℝ) : ℝ :=
  (Del0 p * phi r μ p * (Del0 p * phi r ν p) *
    ∑ l, ‖Complex.exp (I * p l) - 1‖ ^ 2 / (Del0 p ^ 2 * phi r l p))⁻¹

/-- **The bounds of `σ_{μν}`** in `prop:momentum-space`(iv): `γ₀γ₁⁻² ≤ σ_{μν}(p') ≤ γ₁γ₀⁻²` for `|p'_μ| ≤ π`, `p' ≠ 0`,
with the `γ₀`, `γ₁` of (iii). Since `Σ_λ|∂¹_λ|²/Δ₀ = 1`, the sum is a mean of the `(Δ₀φ_λ)⁻¹`. -/
theorem sigma_bounds (r : ℕ) (μ ν : Fin 4) {p : Fin 4 → ℝ} (hp : ∀ l, |p l| ≤ π) (hp0 : p ≠ 0) :
    (2 / π) ^ 12 / (π ^ 2 / 4 + π ^ 2 * (4 * (π ^ 2 / 3 - 1)) ^ 4) ^ 2 ≤ sigma r μ ν p ∧
      sigma r μ ν p ≤ (π ^ 2 / 4 + π ^ 2 * (4 * (π ^ 2 / 3 - 1)) ^ 4) / ((2 / π) ^ 12) ^ 2 := by
  have hπ := Real.pi_pos
  have hS : 0 < ∑ l, p l ^ 2 := by
    obtain ⟨l, hl⟩ : ∃ l, p l ≠ 0 := by
      by_contra h; push_neg at h; exact hp0 (funext h)
    exact lt_of_lt_of_le (by positivity) (Finset.single_le_sum (fun i _ => sq_nonneg (p i)) (Finset.mem_univ l))
  have hD0 : 0 < Del0 p := lt_of_lt_of_le (by positivity) (Del0_bounds hp).1
  have hx := fun l => phi_bounds r l hp hp0
  have hphi : ∀ l, 0 < phi r l p := fun l => by
    have := (hx l).1
    have h12 : (0 : ℝ) < (2 / π) ^ 12 := by positivity
    exact pos_of_mul_pos_right (lt_of_lt_of_le h12 this) hD0.le
  have hc1 : ∑ l, ‖Complex.exp (I * p l) - 1‖ ^ 2 / Del0 p = 1 := by
    rw [← Finset.sum_div]; unfold Del0; exact div_self hD0.ne'
  have e : sigma r μ ν p = (Del0 p * phi r μ p * (Del0 p * phi r ν p) *
      ∑ l, (‖Complex.exp (I * p l) - 1‖ ^ 2 / Del0 p) / (Del0 p * phi r l p))⁻¹ := by
    unfold sigma
    congr 2
    refine Finset.sum_congr rfl fun l _ => ?_
    have := hphi l
    field_simp
  rw [e]
  exact sigma_abstract (by positivity) (fun l => Del0 p * phi r l p) hx _ (fun l => by positivity) hc1 μ ν

end MomentumSymbols
end CoreLean

end
