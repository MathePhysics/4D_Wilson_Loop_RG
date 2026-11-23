/-
`prop:momentum-space`(iv) of BALABAN_CORE.tex (`fc142d786d90`) on one fibre, with the symbols of the core: for
`n = L^k = 2r + 1`, `|p'_μ| ≤ π`, `p' ≠ 0`, and `b ∈ ℂ⁴`, the minimum of `½Σ_{μ,ν}Σ_l|∂_μ(p' + l)a_ν(l) - ∂_ν(p' + l)a_μ(l)|²`
over the families `a` with `Σ_lu_k(p' + l)v_μ(p' + l)a_μ(l) = b_μ` is `½Σ_{μ,ν}σ_{μν}(p')|∂¹_μ(p')b_ν - ∂¹_ν(p')b_μ|²`.
This is the computation of the core's proof of (iv) at a fixed `p' ≠ 0`; `fibre_min` with `w_μ∂_μ = u_k∂¹_μ`
(`vs_mul_diff_shift`), `φ_μ > 0` (`phi_bounds`), and `u_k(p') ≠ 0` (`uf_lower`).
-/
import CoreLean.MomentumSums
import CoreLean.MomentumMinimal

open Real Complex

noncomputable section

namespace CoreLean
namespace MomentumSymbols

open MomentumMinimal

/-- `∂_μ(p) = (e^{ia₀p_μ} - 1)/a₀`, `a₀ = 1/n`. -/
def dsym (n : ℕ) (p : Fin 4 → ℝ) (μ : Fin 4) : ℂ :=
  (Complex.exp (I * (((1 / n : ℝ) * p μ : ℝ) : ℂ)) - 1) / ((1 / n : ℝ) : ℂ)

/-- `∂¹_μ(p') = e^{ip'_μ} - 1`. -/
def d1sym (p : Fin 4 → ℝ) (μ : Fin 4) : ℂ := Complex.exp (I * p μ) - 1

lemma nsq_dsym (n : ℕ) (hn : 1 ≤ n) (p : Fin 4 → ℝ) : nsq (dsym n p) = Del n p := by
  have hn1 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < 1 / n := by positivity
  unfold nsq dsym Del
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hn0.le]

lemma nsq_d1sym (p : Fin 4 → ℝ) : nsq (d1sym p) = Del0 p := rfl

/-- The shifted momenta are nonzero. -/
lemma shift_ne_zero {p : Fin 4 → ℝ} (hp : ∀ μ, |p μ| ≤ π) (hp0 : p ≠ 0) (m : Fin 4 → ℤ) : shift p m ≠ 0 := by
  have hπ := Real.pi_pos
  by_cases hm : m = 0
  · rw [hm, shift_zero]; exact hp0
  · obtain ⟨ν, hν⟩ : ∃ ν, m ν ≠ 0 := by
      by_contra h; push_neg at h; exact hm (funext h)
    intro h
    have h0 : shift p m ν = 0 := by rw [h]; rfl
    have h1 : (1 : ℝ) ≤ |((m ν : ℤ) : ℝ)| := by
      have : (1 : ℤ) ≤ |m ν| := Int.one_le_abs hν
      rw [← Int.cast_abs]; exact_mod_cast this
    have e : 2 * π * (m ν : ℝ) = -p ν := by simp only [shift] at h0; linarith
    have : |2 * π * (m ν : ℝ)| ≤ π := by rw [e, abs_neg]; exact hp ν
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)] at this
    nlinarith

/-- **The minimal form on one fibre** (`prop:momentum-space`(iv), the computation at a fixed `p' ≠ 0`). -/
theorem fibre_minimum (r : ℕ) {p : Fin 4 → ℝ} (hp : ∀ μ, |p μ| ≤ π) (hp0 : p ≠ 0) (b : Fin 4 → ℂ) :
    (∀ a : box r → Fin 4 → ℂ,
      (∀ μ, ∑ l : box r, (uk (2 * r + 1) (shift p l) : ℂ) * vs (2 * r + 1) (shift p l μ) * a l μ = b μ) →
        1 / 2 * ∑ μ, ∑ ν, sigma r μ ν p * ‖d1sym p μ * b ν - d1sym p ν * b μ‖ ^ 2 ≤
          1 / 2 * ∑ l : box r, ∑ μ, ∑ ν, ‖dsym (2 * r + 1) (shift p l) μ * a l ν -
            dsym (2 * r + 1) (shift p l) ν * a l μ‖ ^ 2) ∧
    ∃ a : box r → Fin 4 → ℂ,
      (∀ μ, ∑ l : box r, (uk (2 * r + 1) (shift p l) : ℂ) * vs (2 * r + 1) (shift p l μ) * a l μ = b μ) ∧
        1 / 2 * ∑ l : box r, ∑ μ, ∑ ν, ‖dsym (2 * r + 1) (shift p l) μ * a l ν -
            dsym (2 * r + 1) (shift p l) ν * a l μ‖ ^ 2 =
          1 / 2 * ∑ μ, ∑ ν, sigma r μ ν p * ‖d1sym p μ * b ν - d1sym p ν * b μ‖ ^ 2 := by
  set n := 2 * r + 1 with hn_def
  have hn : 1 ≤ n := by omega
  have hπ := Real.pi_pos
  set D : box r → Fin 4 → ℂ := fun l => dsym n (shift p l) with hD
  set w : box r → Fin 4 → ℂ := fun l μ => (uk n (shift p l) : ℂ) * vs n (shift p l μ) with hw
  set u : box r → ℝ := fun l => uk n (shift p l) with hu
  set d := d1sym p with hd
  -- `Δ(p' + l) > 0`
  have hΔ : ∀ l : box r, 0 < nsq (D l) := by
    intro l
    rw [hD, nsq_dsym n hn]
    have hr := shift_range (r := r) hp l.2
    have hne := shift_ne_zero hp hp0 l
    obtain ⟨ν, hν⟩ : ∃ ν, shift p l ν ≠ 0 := by
      by_contra h; push_neg at h; exact hne (funext h)
    have hS : 0 < ∑ μ, shift p l μ ^ 2 :=
      lt_of_lt_of_le (by positivity) (Finset.single_le_sum (fun i _ => sq_nonneg (shift p l i)) (Finset.mem_univ ν))
    exact lt_of_lt_of_le (by positivity) (Del_ge n hn hr)
  -- `φ_μ` is the core's
  have hphi : ∀ μ, phiF D w μ = phi r μ p := by
    intro μ
    unfold phiF phi
    rw [← Finset.sum_coe_sort (box r)]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [hD, hw, nsq_dsym n hn, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
    rfl
  have hS0 : 0 < ∑ l, p l ^ 2 := by
    obtain ⟨l, hl⟩ : ∃ l, p l ≠ 0 := by
      by_contra h; push_neg at h; exact hp0 (funext h)
    exact lt_of_lt_of_le (by positivity) (Finset.single_le_sum (fun i _ => sq_nonneg (p i)) (Finset.mem_univ l))
  have hD0 : 0 < Del0 p := lt_of_lt_of_le (by positivity) (Del0_bounds hp).1
  have hφpos : ∀ μ, 0 < phi r μ p := fun μ => by
    have := (phi_bounds r μ hp hp0).1
    have h12 : (0 : ℝ) < (2 / π) ^ 12 := by positivity
    exact pos_of_mul_pos_right (lt_of_lt_of_le h12 this) hD0.le
  have hφ : ∀ μ, 0 < phiF D w μ := fun μ => by rw [hphi]; exact hφpos μ
  -- `S > 0`
  have hSF : SF D w d = ∑ μ, ‖d1sym p μ‖ ^ 2 / phi r μ p := by
    unfold SF; exact Finset.sum_congr rfl fun μ _ => by rw [hphi]
  have hS : 0 < SF D w d := by
    rw [hSF]
    have hd0 : 0 < ∑ μ, ‖d1sym p μ‖ ^ 2 := hD0
    obtain ⟨ν, hν⟩ : ∃ ν, 0 < ‖d1sym p ν‖ ^ 2 := by
      by_contra h; push_neg at h
      have : ∑ μ, ‖d1sym p μ‖ ^ 2 ≤ 0 := Finset.sum_nonpos fun μ _ => h μ
      linarith
    exact Finset.sum_pos' (fun μ _ => div_nonneg (sq_nonneg _) (hφpos μ).le)
      ⟨ν, Finset.mem_univ _, div_pos hν (hφpos ν)⟩
  -- `w_μ(l)∂_μ(p' + l) = u_k(p' + l)∂¹_μ(p')`
  have hwd : ∀ l μ, w l μ * D l μ = (u l : ℂ) * d μ := by
    intro l μ
    simp only [hw, hD, hu, hd, dsym, d1sym]
    rw [mul_assoc, show shift p l μ = p μ + 2 * π * ((l : Fin 4 → ℤ) μ) from rfl, vs_mul_diff_shift n hn]
  -- `u_k(p') ≠ 0`
  have hu0 : u ⟨0, zero_mem_box r⟩ ≠ 0 := by
    show uk n (shift p 0) ≠ 0
    rw [shift_zero]
    have h : (2 / π) ^ 4 ≤ |uk n p| := by
      unfold uk; rw [Finset.abs_prod]
      calc (2 / π) ^ 4 = ∏ _ν : Fin 4, (2 / π) := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        _ ≤ ∏ ν, |uf n (p ν)| := Finset.prod_le_prod₀ (fun _ _ => by positivity) fun ν _ => uf_lower n hn (hp ν)
    intro h0
    rw [h0, abs_zero] at h
    have : (0 : ℝ) < (2 / π) ^ 4 := by positivity
    linarith
  -- `σ_{μν} = (Sφ_μφ_ν)⁻¹`
  have hsig : ∀ μ ν, sigma r μ ν p = (SF D w d * phiF D w μ * phiF D w ν)⁻¹ := by
    intro μ ν
    rw [hSF, hphi, hphi]
    unfold sigma
    simp only [d1sym]
    have e : ∑ l, ‖Complex.exp (I * p l) - 1‖ ^ 2 / (Del0 p ^ 2 * phi r l p) =
        (∑ l, ‖Complex.exp (I * p l) - 1‖ ^ 2 / phi r l p) / Del0 p ^ 2 := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun l _ => by have := hφpos l; field_simp
    rw [e]
    have := hφpos μ; have := hφpos ν
    field_simp
  obtain ⟨hlow, a, ha, hval⟩ := fibre_min D w d b u hΔ hφ hS hwd ⟨0, zero_mem_box r⟩ hu0
  have hV : VF D w d b = 1 / 2 * ∑ μ, ∑ ν, sigma r μ ν p * ‖d1sym p μ * b ν - d1sym p ν * b μ‖ ^ 2 := by
    unfold VF
    refine congrArg (fun t => 1 / 2 * t) (Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => ?_)
    rw [hsig, div_eq_inv_mul]
  refine ⟨fun a ha => ?_, a, ha, ?_⟩
  · have := hlow a ha
    rw [hV] at this
    exact this
  · rw [← hV]
    exact hval

/-- **The comparison on one fibre**: `γ'₀½Σ|∂¹_μb_ν - ∂¹_νb_μ|² ≤ ½Σσ_{μν}|∂¹_μb_ν - ∂¹_νb_μ|² ≤ γ'₁½Σ|∂¹_μb_ν - ∂¹_νb_μ|²`
with `γ'₀ = γ₀γ₁⁻²` and `γ'₁ = γ₁γ₀⁻²`, by `sigma_bounds`. -/
theorem fibre_comparison (r : ℕ) {p : Fin 4 → ℝ} (hp : ∀ μ, |p μ| ≤ π) (hp0 : p ≠ 0) (b : Fin 4 → ℂ) :
    (2 / π) ^ 12 / (π ^ 2 / 4 + π ^ 2 * (4 * (π ^ 2 / 3 - 1)) ^ 4) ^ 2 *
        (1 / 2 * ∑ μ, ∑ ν, ‖d1sym p μ * b ν - d1sym p ν * b μ‖ ^ 2) ≤
      1 / 2 * ∑ μ, ∑ ν, sigma r μ ν p * ‖d1sym p μ * b ν - d1sym p ν * b μ‖ ^ 2 ∧
    1 / 2 * ∑ μ, ∑ ν, sigma r μ ν p * ‖d1sym p μ * b ν - d1sym p ν * b μ‖ ^ 2 ≤
      (π ^ 2 / 4 + π ^ 2 * (4 * (π ^ 2 / 3 - 1)) ^ 4) / ((2 / π) ^ 12) ^ 2 *
        (1 / 2 * ∑ μ, ∑ ν, ‖d1sym p μ * b ν - d1sym p ν * b μ‖ ^ 2) := by
  have e : ∀ c : ℝ, c * (1 / 2 * ∑ μ, ∑ ν, ‖d1sym p μ * b ν - d1sym p ν * b μ‖ ^ 2) =
      1 / 2 * ∑ μ, ∑ ν, c * ‖d1sym p μ * b ν - d1sym p ν * b μ‖ ^ 2 := fun c => by
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => by ring
  rw [e, e]
  constructor
  · gcongr with μ _ ν _
    exact (sigma_bounds r μ ν hp hp0).1
  · gcongr with μ _ ν _
    exact (sigma_bounds r μ ν hp hp0).2

end MomentumSymbols
end CoreLean

end
