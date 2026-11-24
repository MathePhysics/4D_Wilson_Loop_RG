/-
`lem:sf-one-layer` of BALABAN_CORE.tex (`aaaa938bb57d`), the step "The bound at a momentum": on one fibre
`{p' + l}_l`, `p' ≠ 0`, with `g = u/Δ`, `s(l) = ∂(l)^*a(l)`, `K = Σ_μ|Σ_lw_μ(l)a_μ(l)|²`, and
`E = Σ_l(Δ(l)|a(l)|² - |s(l)|²)`:

    |⟨g, s⟩|² ≤ C_ol(K + E)|g|²,   C_ol = 2C_u max{16, γ₁}γ₀⁻²,   C_u = (4(π²/3 - 1))⁴.

* `pyth`: `Δ|a - (s/Δ)∂|² = Δ|a|² - |s|²` (the decomposition `a = c∂ + t`, `∂^*t = 0`).
* `cs_weighted`: `|Σ_lx_ly_l|² ≤ (Σ_l|x_l|²/Δ_l)(Σ_lΔ_l|y_l|²)`.
* `fibre_bound`: the inequality for abstract data (`w_μ∂_μ = u∂¹_μ`, `|w_μ| ≤ |u|`, `γ₀ ≤ Δ₀φ_μ ≤ γ₁`, `Δ₀ ≤ 16`,
  `Σ_lu² ≤ C_u`); `sum_uk_sq_le`, `Del0_le`, `one_layer_fibre`: the instance with the symbols of `prop:momentum-space`.
* `proj_fibre_bound`: a vector `v = Pf` which is fibrewise a multiple of `g(q)`, with `‖v‖² = Re⟨v, f⟩`, has
  `‖v‖² ≤ Σ_q|⟨g(q), f(q)⟩|²/|g(q)|²` (the step "The projection in momentum space", as an upper bound).
* `fibre_energy`: `E` of a fibre is `½Σ_{μ,ν}|∂_μa_ν - ∂_νa_μ|²` (the Lagrange identity), the fibre term of `energy0`.
-/
import CoreLean.MomentumFibre

open Finset Complex
open scoped Real

noncomputable section

namespace CoreLean
namespace SFOneLayer

open MomentumSymbols

/-- `Δ|a - (s/Δ)∂|² = Δ|a|² - |s|²` for `Δ = |∂|² > 0`, `s = ∂^*a`. -/
lemma pyth (d a : Fin 4 → ℂ) (hD : 0 < ∑ μ, ‖d μ‖ ^ 2) :
    (∑ μ, ‖d μ‖ ^ 2) * ∑ μ, ‖a μ - (∑ ν, starRingEnd ℂ (d ν) * a ν) / ((∑ ν, ‖d ν‖ ^ 2 : ℝ) : ℂ) * d μ‖ ^ 2 =
      (∑ μ, ‖d μ‖ ^ 2) * ∑ μ, ‖a μ‖ ^ 2 - ‖∑ ν, starRingEnd ℂ (d ν) * a ν‖ ^ 2 := by
  set D := ∑ μ, ‖d μ‖ ^ 2
  set s := ∑ ν, starRingEnd ℂ (d ν) * a ν
  set c := s / ((D : ℝ) : ℂ)
  have hD0 : (D : ℂ) ≠ 0 := by exact_mod_cast hD.ne'
  -- `|a_μ - cd_μ|² = |a_μ|² - 2Re(c̄ d̄_μa_μ) + |c|²|d_μ|²`
  have hterm : ∀ μ, ‖a μ - c * d μ‖ ^ 2 =
      ‖a μ‖ ^ 2 - 2 * (starRingEnd ℂ c * (starRingEnd ℂ (d μ) * a μ)).re + ‖c‖ ^ 2 * ‖d μ‖ ^ 2 := by
    intro μ
    rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm, Complex.sq_norm, Complex.normSq_sub,
      Complex.normSq_mul]
    simp only [map_mul, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im]
    ring
  have hsum : ∑ μ, ‖a μ - c * d μ‖ ^ 2 = ∑ μ, ‖a μ‖ ^ 2 - 2 * (starRingEnd ℂ c * s).re + ‖c‖ ^ 2 * D := by
    simp only [hterm, sum_add_distrib, sum_sub_distrib, ← mul_sum, ← sum_mul]
    congr 2
    rw [← Complex.re_sum, ← mul_sum]
  have hcs : (starRingEnd ℂ c * s).re = ‖s‖ ^ 2 / D := by
    simp only [c, map_div₀, Complex.conj_ofReal]
    rw [div_mul_eq_mul_div, mul_comm, Complex.mul_conj, ← Complex.ofReal_div, Complex.ofReal_re, Complex.sq_norm]
  have hc2 : ‖c‖ ^ 2 = ‖s‖ ^ 2 / D ^ 2 := by
    simp only [c, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hD, div_pow]
  rw [hsum, hcs, hc2]
  field_simp
  ring

/-- `|Σ_lx_ly_l|² ≤ (Σ_l|x_l|²/Δ_l)(Σ_lΔ_l|y_l|²)` for `Δ_l > 0`. -/
lemma cs_weighted {ι : Type*} (s : Finset ι) (x y : ι → ℂ) (Δ : ι → ℝ) (hΔ : ∀ l ∈ s, 0 < Δ l) :
    ‖∑ l ∈ s, x l * y l‖ ^ 2 ≤ (∑ l ∈ s, ‖x l‖ ^ 2 / Δ l) * ∑ l ∈ s, Δ l * ‖y l‖ ^ 2 := by
  have h1 : ‖∑ l ∈ s, x l * y l‖ ≤ ∑ l ∈ s, ‖x l‖ / Real.sqrt (Δ l) * (Real.sqrt (Δ l) * ‖y l‖) := by
    refine (norm_sum_le _ _).trans (le_of_eq (sum_congr rfl fun l hl => ?_))
    have hs := Real.sqrt_pos.2 (hΔ l hl)
    rw [norm_mul]; field_simp
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq s (fun l => ‖x l‖ / Real.sqrt (Δ l)) (fun l => Real.sqrt (Δ l) * ‖y l‖)
  have e1 : ∑ l ∈ s, (‖x l‖ / Real.sqrt (Δ l)) ^ 2 = ∑ l ∈ s, ‖x l‖ ^ 2 / Δ l :=
    sum_congr rfl fun l hl => by rw [div_pow, Real.sq_sqrt (hΔ l hl).le]
  have e2 : ∑ l ∈ s, (Real.sqrt (Δ l) * ‖y l‖) ^ 2 = ∑ l ∈ s, Δ l * ‖y l‖ ^ 2 :=
    sum_congr rfl fun l hl => by rw [mul_pow, Real.sq_sqrt (hΔ l hl).le]
  rw [e1, e2] at h2
  calc ‖∑ l ∈ s, x l * y l‖ ^ 2
      ≤ (∑ l ∈ s, ‖x l‖ / Real.sqrt (Δ l) * (Real.sqrt (Δ l) * ‖y l‖)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := h2

/-- **The bound at a momentum**, for abstract data on a fibre. -/
theorem fibre_bound {ι : Type*} (s : Finset ι) (u Δ : ι → ℝ) (d w a : ι → Fin 4 → ℂ) (d1 : Fin 4 → ℂ)
    {γ0 γ1 Cu : ℝ} (hγ0 : 0 < γ0)
    (hΔ : ∀ l ∈ s, Δ l = ∑ μ, ‖d l μ‖ ^ 2) (hΔpos : ∀ l ∈ s, 0 < Δ l)
    (hw : ∀ l ∈ s, ∀ μ, w l μ * d l μ = u l * d1 μ) (hwu : ∀ l ∈ s, ∀ μ, ‖w l μ‖ ≤ |u l|)
    (hD0 : 0 < ∑ μ, ‖d1 μ‖ ^ 2) (hD16 : ∑ μ, ‖d1 μ‖ ^ 2 ≤ 16)
    (hphi : ∀ μ, γ0 ≤ (∑ ν, ‖d1 ν‖ ^ 2) * ∑ l ∈ s, ‖w l μ‖ ^ 2 / Δ l ∧
      (∑ ν, ‖d1 ν‖ ^ 2) * ∑ l ∈ s, ‖w l μ‖ ^ 2 / Δ l ≤ γ1)
    (hCu : ∑ l ∈ s, u l ^ 2 ≤ Cu) :
    ‖∑ l ∈ s, ((u l / Δ l : ℝ) : ℂ) * ∑ μ, starRingEnd ℂ (d l μ) * a l μ‖ ^ 2 ≤
      2 * Cu * max 16 γ1 / γ0 ^ 2 *
        (∑ μ, ‖∑ l ∈ s, w l μ * a l μ‖ ^ 2 +
          ∑ l ∈ s, (Δ l * ∑ μ, ‖a l μ‖ ^ 2 - ‖∑ μ, starRingEnd ℂ (d l μ) * a l μ‖ ^ 2)) *
        ∑ l ∈ s, (u l / Δ l) ^ 2 := by
  set D0 := ∑ ν, ‖d1 ν‖ ^ 2
  set sv : ι → ℂ := fun l => ∑ μ, starRingEnd ℂ (d l μ) * a l μ
  set c : ι → ℂ := fun l => sv l / ((Δ l : ℝ) : ℂ)
  set t : ι → Fin 4 → ℂ := fun l μ => a l μ - c l * d l μ
  set φ : Fin 4 → ℝ := fun μ => ∑ l ∈ s, ‖w l μ‖ ^ 2 / Δ l
  set G2 := ∑ l ∈ s, (u l / Δ l) ^ 2
  set m : ℂ := ∑ l ∈ s, ((u l / Δ l : ℝ) : ℂ) * sv l
  set K := ∑ μ, ‖∑ l ∈ s, w l μ * a l μ‖ ^ 2
  set E := ∑ l ∈ s, (Δ l * ∑ μ, ‖a l μ‖ ^ 2 - ‖sv l‖ ^ 2)
  set Eμ : Fin 4 → ℝ := fun μ => ∑ l ∈ s, Δ l * ‖t l μ‖ ^ 2
  have hφ0 : ∀ μ, 0 ≤ φ μ := fun μ => sum_nonneg fun l hl => div_nonneg (sq_nonneg _) (hΔpos l hl).le
  -- `ΣE_μ = E`
  have hE : ∑ μ, Eμ μ = E := by
    simp only [Eμ, E]
    rw [Finset.sum_comm]
    refine sum_congr rfl fun l hl => ?_
    rw [← mul_sum]
    have := pyth (d l) (a l) (by rw [← hΔ l hl]; exact hΔpos l hl)
    rw [← hΔ l hl] at this
    exact this
  have hEμ0 : ∀ μ, 0 ≤ Eμ μ := fun μ => sum_nonneg fun l hl => mul_nonneg (hΔpos l hl).le (sq_nonneg _)
  -- `m = Σ_lu(l)c(l)`
  have hm : m = ∑ l ∈ s, (u l : ℂ) * c l := by
    refine sum_congr rfl fun l hl => ?_
    have hΔ0 : ((Δ l : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (hΔpos l hl).ne'
    simp only [c]; push_cast; field_simp
  -- `Σ_lw_μa_μ = ∂¹_μm + Σ_lw_μt_μ`
  have hdec : ∀ μ, ∑ l ∈ s, w l μ * a l μ = d1 μ * m + ∑ l ∈ s, w l μ * t l μ := by
    intro μ
    rw [hm, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun l hl => ?_
    simp only [t]
    have := hw l hl μ
    linear_combination c l * this
  -- the Cauchy–Schwarz step
  have hcs : ∀ μ, ‖∑ l ∈ s, w l μ * t l μ‖ ^ 2 ≤ φ μ * Eμ μ := fun μ =>
    cs_weighted s (fun l => w l μ) (fun l => t l μ) Δ hΔpos
  -- `Δ₀|m|² ≤ 2K + 2(γ₁/Δ₀)E`
  have hφle : ∀ μ, φ μ ≤ γ1 / D0 := fun μ => by
    rw [le_div_iff₀ hD0, mul_comm]; exact (hphi μ).2
  have hm2 : D0 * ‖m‖ ^ 2 ≤ 2 * K + 2 * (γ1 / D0) * E := by
    have h1 : D0 * ‖m‖ ^ 2 = ∑ μ, ‖d1 μ * m‖ ^ 2 := by
      simp only [D0, sum_mul, norm_mul, mul_pow]
    have h2 : ∀ μ, ‖d1 μ * m‖ ^ 2 ≤ 2 * ‖∑ l ∈ s, w l μ * a l μ‖ ^ 2 + 2 * ((γ1 / D0) * Eμ μ) := by
      intro μ
      have e : d1 μ * m = ∑ l ∈ s, w l μ * a l μ - ∑ l ∈ s, w l μ * t l μ := by rw [hdec μ]; ring
      rw [e]
      have hsub := norm_sub_le (∑ l ∈ s, w l μ * a l μ) (∑ l ∈ s, w l μ * t l μ)
      have hX := norm_nonneg (∑ l ∈ s, w l μ * a l μ)
      have hY := norm_nonneg (∑ l ∈ s, w l μ * t l μ)
      have hYb : ‖∑ l ∈ s, w l μ * t l μ‖ ^ 2 ≤ (γ1 / D0) * Eμ μ :=
        (hcs μ).trans (mul_le_mul_of_nonneg_right (hφle μ) (hEμ0 μ))
      have hZ := pow_le_pow_left₀ (norm_nonneg _) hsub 2
      nlinarith [sq_nonneg (‖∑ l ∈ s, w l μ * a l μ‖ - ‖∑ l ∈ s, w l μ * t l μ‖)]
    rw [h1]
    calc ∑ μ, ‖d1 μ * m‖ ^ 2 ≤ ∑ μ, (2 * ‖∑ l ∈ s, w l μ * a l μ‖ ^ 2 + 2 * ((γ1 / D0) * Eμ μ)) :=
          sum_le_sum fun μ _ => h2 μ
      _ = 2 * K + 2 * (γ1 / D0) * E := by
          rw [sum_add_distrib, ← mul_sum, ← mul_sum, ← mul_sum, hE]; ring
  -- `φ₀² ≤ C_uG₂`
  have hφG : φ 0 ^ 2 ≤ Cu * G2 := by
    have h1 : φ 0 ≤ ∑ l ∈ s, u l / Δ l * u l := by
      refine sum_le_sum fun l hl => ?_
      have hu := hwu l hl 0
      have : ‖w l 0‖ ^ 2 ≤ u l ^ 2 := by
        rw [← sq_abs (u l)]; exact pow_le_pow_left₀ (norm_nonneg _) hu 2
      rw [div_mul_eq_mul_div, ← sq]
      exact div_le_div_of_nonneg_right this (hΔpos l hl).le
    have h2 := Finset.sum_mul_sq_le_sq_mul_sq s (fun l => u l / Δ l) u
    calc φ 0 ^ 2 ≤ (∑ l ∈ s, u l / Δ l * u l) ^ 2 := pow_le_pow_left₀ (hφ0 0) h1 2
      _ ≤ G2 * ∑ l ∈ s, u l ^ 2 := h2
      _ ≤ G2 * Cu := mul_le_mul_of_nonneg_left hCu (sum_nonneg fun l _ => sq_nonneg _)
      _ = Cu * G2 := mul_comm _ _
  -- `G₂ ≥ γ₀²/(C_uΔ₀²)`
  have hφlo : γ0 / D0 ≤ φ 0 := by rw [div_le_iff₀ hD0, mul_comm]; exact (hphi 0).1
  have hγ0D : 0 < γ0 / D0 := div_pos hγ0 hD0
  have hG : (γ0 / D0) ^ 2 ≤ Cu * G2 := (pow_le_pow_left₀ hγ0D.le hφlo 2).trans hφG
  -- the conclusion
  have hK0 : 0 ≤ K := sum_nonneg fun μ _ => sq_nonneg _
  have hE0 : 0 ≤ E := by rw [← hE]; exact sum_nonneg fun μ _ => hEμ0 μ
  have hmax : 16 ≤ max 16 γ1 := le_max_left _ _
  have hmax' : γ1 ≤ max 16 γ1 := le_max_right _ _
  -- `|m|² ≤ (2Δ₀K + 2γ₁E)/Δ₀²`
  have hm3 : ‖m‖ ^ 2 * D0 ^ 2 ≤ 2 * D0 * K + 2 * γ1 * E := by
    have := mul_le_mul_of_nonneg_left hm2 hD0.le
    have e : D0 * (2 * K + 2 * (γ1 / D0) * E) = 2 * D0 * K + 2 * γ1 * E := by field_simp
    nlinarith
  have hrhs : 2 * D0 * K + 2 * γ1 * E ≤ 2 * max 16 γ1 * (K + E) := by nlinarith
  -- `γ₀²|m|² ≤ C_uG₂(2Δ₀K + 2γ₁E)`
  have hG' : γ0 ^ 2 ≤ Cu * G2 * D0 ^ 2 := by
    have := hG; rw [div_pow, div_le_iff₀ (by positivity)] at this; exact this
  have hfin : γ0 ^ 2 * ‖m‖ ^ 2 ≤ Cu * G2 * (2 * max 16 γ1 * (K + E)) := by
    have hCG : 0 ≤ Cu * G2 := le_trans (sq_nonneg _) hG
    calc γ0 ^ 2 * ‖m‖ ^ 2 ≤ Cu * G2 * D0 ^ 2 * ‖m‖ ^ 2 := mul_le_mul_of_nonneg_right hG' (sq_nonneg _)
      _ = Cu * G2 * (‖m‖ ^ 2 * D0 ^ 2) := by ring
      _ ≤ Cu * G2 * (2 * max 16 γ1 * (K + E)) :=
          mul_le_mul_of_nonneg_left (hm3.trans hrhs) hCG
  show ‖m‖ ^ 2 ≤ 2 * Cu * max 16 γ1 / γ0 ^ 2 * (K + E) * G2
  rw [show 2 * Cu * max 16 γ1 / γ0 ^ 2 * (K + E) * G2 = Cu * G2 * (2 * max 16 γ1 * (K + E)) / γ0 ^ 2 by ring,
    le_div_iff₀ (by positivity)]
  linarith

lemma sum_sq_pos {q : Fin 4 → ℝ} (hq : q ≠ 0) : 0 < ∑ ν, q ν ^ 2 := by
  obtain ⟨ν, hν⟩ : ∃ ν, q ν ≠ 0 := by
    by_contra h; push_neg at h; exact hq (funext h)
  have : 0 < q ν ^ 2 := by positivity
  exact lt_of_lt_of_le this (Finset.single_le_sum (fun i _ => sq_nonneg (q i)) (Finset.mem_univ ν))

/-- `Δ₀(p') ≤ 16`. -/
lemma Del0_le (p : Fin 4 → ℝ) : Del0 p ≤ 16 := by
  unfold Del0
  calc ∑ μ, ‖Complex.exp (I * p μ) - 1‖ ^ 2 ≤ ∑ _μ : Fin 4, (4 : ℝ) := by
        refine sum_le_sum fun μ _ => ?_
        rw [norm_exp_sub_one]
        have := Real.abs_sin_le_one (p μ / 2)
        nlinarith [abs_nonneg (Real.sin (p μ / 2))]
    _ = 16 := by simp; norm_num

/-- `Σ_l u_k(p' + l)² ≤ C_u = (4(π²/3 - 1))⁴`. -/
lemma sum_uk_sq_le (r : ℕ) {p : Fin 4 → ℝ} (hp : ∀ μ, |p μ| ≤ π) :
    ∑ m ∈ MomentumSymbols.box r, uk (2 * r + 1) (shift p m) ^ 2 ≤ (4 * (π ^ 2 / 3 - 1)) ^ 4 := by
  have hn : 1 ≤ 2 * r + 1 := by omega
  have hb : ∀ m ∈ MomentumSymbols.box r, uk (2 * r + 1) (shift p m) ^ 2 ≤ ∏ ν, 4 / (1 + |((m ν : ℤ) : ℝ)|) ^ 2 := by
    intro m hm
    have hu := u_bound (2 * r + 1) hn hp m (fun ν => by have := mem_box hm ν; push_cast; linarith)
    have e : ∏ ν, 4 / (1 + |((m ν : ℤ) : ℝ)|) ^ 2 = (∏ ν, 2 / (1 + |((m ν : ℤ) : ℝ)|)) ^ 2 := by
      rw [← Finset.prod_pow]; exact Finset.prod_congr rfl fun ν _ => by rw [div_pow]; norm_num
    rw [e, ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hu 2
  refine (sum_le_sum hb).trans ?_
  rw [MomentumSymbols.box, ← Finset.prod_univ_sum (fun _ => Finset.Icc (-(r : ℤ)) r) (fun _ j => 4 / (1 + |(j : ℝ)|) ^ 2),
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => by positivity) (sum_box_le r) 4

/-- `γ₀ = (2/π)¹²`. -/
def g0 : ℝ := (2 / π) ^ 12

/-- `γ₁ = π²/4 + π²(4(π²/3 - 1))⁴`. -/
def g1 : ℝ := π ^ 2 / 4 + π ^ 2 * (4 * (π ^ 2 / 3 - 1)) ^ 4

/-- `C_ol = 2C_u max{16, γ₁}γ₀⁻²`. -/
def Col : ℝ := 2 * (4 * (π ^ 2 / 3 - 1)) ^ 4 * max 16 g1 / g0 ^ 2

/-- **The bound at a momentum** (`lem:sf-one-layer`), with the symbols of `prop:momentum-space`: for `n = 2r + 1`,
`|p'_μ| ≤ π`, `p' ≠ 0`, and a family `a(l) ∈ ℂ⁴` on the fibre, `|⟨g, s⟩|² ≤ C_ol(K + E)|g|²`. -/
theorem one_layer_fibre (r : ℕ) {p : Fin 4 → ℝ} (hp : ∀ μ, |p μ| ≤ π) (hp0 : p ≠ 0)
    (a : (Fin 4 → ℤ) → Fin 4 → ℂ) :
    ‖∑ m ∈ MomentumSymbols.box r, ((uk (2 * r + 1) (shift p m) / Del (2 * r + 1) (shift p m) : ℝ) : ℂ) *
        ∑ μ, starRingEnd ℂ (dsym (2 * r + 1) (shift p m) μ) * a m μ‖ ^ 2 ≤
      Col * (∑ μ, ‖∑ m ∈ MomentumSymbols.box r, ((uk (2 * r + 1) (shift p m) : ℝ) : ℂ) * vs (2 * r + 1) (shift p m μ) * a m μ‖ ^ 2 +
        ∑ m ∈ MomentumSymbols.box r, (Del (2 * r + 1) (shift p m) * ∑ μ, ‖a m μ‖ ^ 2 -
          ‖∑ μ, starRingEnd ℂ (dsym (2 * r + 1) (shift p m) μ) * a m μ‖ ^ 2)) *
      ∑ m ∈ MomentumSymbols.box r, (uk (2 * r + 1) (shift p m) / Del (2 * r + 1) (shift p m)) ^ 2 := by
  set n := 2 * r + 1 with hn_def
  have hn : 1 ≤ n := by omega
  have hπ := Real.pi_pos
  have hΔpos : ∀ m ∈ MomentumSymbols.box r, 0 < Del n (shift p m) := fun m hm =>
    lt_of_lt_of_le (mul_pos (by positivity) (sum_sq_pos (shift_ne_zero hp hp0 m)))
      (Del_ge n hn (shift_range hp hm))
  have hD0 : 0 < ∑ ν, ‖d1sym p ν‖ ^ 2 := by
    show 0 < Del0 p
    exact lt_of_lt_of_le (mul_pos (by positivity) (sum_sq_pos hp0)) (Del0_bounds hp).1
  refine fibre_bound (MomentumSymbols.box r) (fun m => uk n (shift p m)) (fun m => Del n (shift p m))
    (fun m => dsym n (shift p m)) (fun m μ => ((uk n (shift p m) : ℝ) : ℂ) * vs n (shift p m μ)) a (d1sym p)
    (γ1 := g1) (show (0 : ℝ) < g0 by unfold g0; positivity)
    (fun m _ => (nsq_dsym n hn (shift p m)).symm) hΔpos (fun m _ μ => ?_) (fun m _ μ => ?_) hD0
    (Del0_le p) (fun μ => ?_) (sum_uk_sq_le r hp)
  · rw [mul_assoc]
    congr 1
    have := vs_mul_diff_shift n hn (p μ) (m μ)
    simp only [dsym, shift, d1sym]
    exact this
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_of_le_one_right (abs_nonneg _) (vs_norm_le_one n hn _)
  · have h := phi_bounds r μ hp hp0
    have e : (∑ ν, ‖d1sym p ν‖ ^ 2) * ∑ m ∈ MomentumSymbols.box r, ‖((uk n (shift p m) : ℝ) : ℂ) * vs n (shift p m μ)‖ ^ 2 /
        Del n (shift p m) = Del0 p * phi r μ p := by
      congr 1
      refine sum_congr rfl fun m _ => ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
    rw [e]
    exact ⟨h.1, h.2⟩

/-- **The projection in the fibres**: if `v = Pf` is fibrewise a multiple of `g(q)` and `‖v‖² = Re⟨v, f⟩` (as for an
orthogonal projection), then `‖v‖² ≤ Σ_q|⟨g(q), f(q)⟩|²/|g(q)|²`. -/
lemma proj_fibre_bound {Qd ι : Type*} [Fintype Qd] [Fintype ι] (g f v : Qd → ι → ℂ) (c : Qd → ℂ)
    (hv : ∀ q l, v q l = c q * g q l)
    (hpf : ∑ q, ∑ l, ‖v q l‖ ^ 2 = (∑ q, ∑ l, starRingEnd ℂ (v q l) * f q l).re) :
    ∑ q, ∑ l, ‖v q l‖ ^ 2 ≤ ∑ q, ‖∑ l, starRingEnd ℂ (g q l) * f q l‖ ^ 2 / ∑ l, ‖g q l‖ ^ 2 := by
  set G : Qd → ℝ := fun q => ∑ l, ‖g q l‖ ^ 2
  set ip : Qd → ℂ := fun q => ∑ l, starRingEnd ℂ (g q l) * f q l
  set X := ∑ q, ∑ l, ‖v q l‖ ^ 2
  set Y := ∑ q, ‖ip q‖ ^ 2 / G q
  have hG0 : ∀ q, 0 ≤ G q := fun q => sum_nonneg fun l _ => sq_nonneg _
  have hX : X = ∑ q, ‖c q‖ ^ 2 * G q := by
    refine sum_congr rfl fun q _ => ?_
    simp only [G, hv, norm_mul, mul_pow, mul_sum]
  have hY0 : 0 ≤ Y := sum_nonneg fun q _ => div_nonneg (sq_nonneg _) (hG0 q)
  -- `|ip(q)| ≤ √G(q)·√(|ip(q)|²/G(q))`, both sides vanishing where `G(q) = 0`
  have hip : ∀ q, ‖ip q‖ ≤ Real.sqrt (G q) * Real.sqrt (‖ip q‖ ^ 2 / G q) := by
    intro q
    rcases (hG0 q).eq_or_lt with h0 | hpos
    · have hg : ∀ l, g q l = 0 := fun l => by
        have := (sum_eq_zero_iff_of_nonneg (fun l _ => sq_nonneg ‖g q l‖)).1 h0.symm l (mem_univ l)
        exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 this)
      have : ip q = 0 := by simp only [ip, hg, map_zero, zero_mul, sum_const_zero]
      rw [this, norm_zero]; positivity
    · rw [← Real.sqrt_mul hpos.le, mul_div_cancel₀ _ hpos.ne', Real.sqrt_sq (norm_nonneg _)]
  -- `X = Re Σ_qc̄(q)ip(q) ≤ Σ_q|c(q)|√G(q)·√(|ip(q)|²/G(q)) ≤ √X√Y`
  have h1 : X ≤ ∑ q, (‖c q‖ * Real.sqrt (G q)) * Real.sqrt (‖ip q‖ ^ 2 / G q) := by
    rw [hpf]
    have e : ∑ q, ∑ l, starRingEnd ℂ (v q l) * f q l = ∑ q, starRingEnd ℂ (c q) * ip q := by
      refine sum_congr rfl fun q _ => ?_
      simp only [hv, map_mul, ip, mul_sum]
      exact sum_congr rfl fun l _ => by ring
    rw [e]
    refine (Complex.re_le_norm _).trans ((norm_sum_le _ _).trans (sum_le_sum fun q _ => ?_))
    rw [norm_mul, Complex.norm_conj, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hip q) (norm_nonneg _)
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq univ (fun q => ‖c q‖ * Real.sqrt (G q))
    (fun q => Real.sqrt (‖ip q‖ ^ 2 / G q))
  have e1 : ∑ q, (‖c q‖ * Real.sqrt (G q)) ^ 2 = X := by
    rw [hX]; exact sum_congr rfl fun q _ => by rw [mul_pow, Real.sq_sqrt (hG0 q)]
  have e2 : ∑ q, Real.sqrt (‖ip q‖ ^ 2 / G q) ^ 2 = Y :=
    sum_congr rfl fun q _ => Real.sq_sqrt (div_nonneg (sq_nonneg _) (hG0 q))
  rw [e1, e2] at h2
  have hX0 : 0 ≤ X := sum_nonneg fun q _ => sum_nonneg fun l _ => sq_nonneg _
  have h3 : X ^ 2 ≤ X * Y := (pow_le_pow_left₀ hX0 h1 2).trans h2
  rcases hX0.eq_or_lt with h | h
  · rw [← h]; exact hY0
  · nlinarith

/-- The term `E` of a fibre is the energy: `Δ|a|² - |∂^*a|² = ½Σ_{μ,ν}|∂_μa_ν - ∂_νa_μ|²` (the Lagrange identity). -/
lemma fibre_energy (d a : Fin 4 → ℂ) :
    (∑ μ, ‖d μ‖ ^ 2) * ∑ μ, ‖a μ‖ ^ 2 - ‖∑ μ, starRingEnd ℂ (d μ) * a μ‖ ^ 2 =
      1 / 2 * ∑ μ, ∑ ν, ‖d μ * a ν - d ν * a μ‖ ^ 2 := by
  rw [MomentumMinimal.lagrange]
  rfl

end SFOneLayer
end CoreLean

end
