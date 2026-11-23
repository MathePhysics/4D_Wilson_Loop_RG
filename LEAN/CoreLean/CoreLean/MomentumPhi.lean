/-
`prop:momentum-space`(iii) of BALABAN_CORE.tex (`ba2f40296da0`): the two-sided bound of `Δ₀φ_μ`. With `n = L^k = 2r + 1`
and `a₀ = 1/n` (the units of the last lattice), `p = p' + l`, `l = 2πm`, `|m_μ| ≤ r`:

    φ_μ(p') = Σ_l |u_k(p' + l)|²|v_μ(p' + l)|²/Δ(p' + l),

and for `|p'_μ| ≤ π`, `p' ≠ 0`: `γ₀ ≤ Δ₀(p')φ_μ(p') ≤ γ₁` with `γ₀ = (2/π)¹²` and `γ₁ = π²/4 + π²(4(π²/3 - 1))⁴`.
-/
import CoreLean.MomentumSymbols

open Real Complex

noncomputable section

namespace CoreLean
namespace MomentumSymbols

/-- `v_μ(p) = (e^{ip} - 1)/(n(e^{ia₀p} - 1))`, `a₀ = 1/n`, with the value one where the denominator vanishes. -/
def vs (n : ℕ) (p : ℝ) : ℂ :=
  if Complex.exp (I * (((1 / n : ℝ) * p : ℝ) : ℂ)) - 1 = 0 then 1
  else (Complex.exp (I * p) - 1) / (n * (Complex.exp (I * (((1 / n : ℝ) * p : ℝ) : ℂ)) - 1))

/-- `u_k(p) = ∏_ν sin(p_ν/2)/(n sin(a₀p_ν/2))`. -/
def uk (n : ℕ) (p : Fin 4 → ℝ) : ℝ := ∏ ν, uf n (p ν)

/-- `Δ(p) = Σ_μ |(e^{ia₀p_μ} - 1)/a₀|²`, `a₀ = 1/n`. -/
def Del (n : ℕ) (p : Fin 4 → ℝ) : ℝ := ∑ μ, (‖Complex.exp (I * (((1 / n : ℝ) * p μ : ℝ) : ℂ)) - 1‖ / (1 / n : ℝ)) ^ 2

/-- `Δ₀(p') = Σ_μ |e^{ip'_μ} - 1|²`. -/
def Del0 (p : Fin 4 → ℝ) : ℝ := ∑ μ, ‖Complex.exp (I * p μ) - 1‖ ^ 2

/-- `p' + 2πm`. -/
def shift (p : Fin 4 → ℝ) (m : Fin 4 → ℤ) : Fin 4 → ℝ := fun ν => p ν + 2 * π * m ν

/-- The indices `m` with `|m_μ| ≤ r`. -/
def box (r : ℕ) : Finset (Fin 4 → ℤ) := Fintype.piFinset fun _ => Finset.Icc (-(r : ℤ)) r

/-- `φ_μ(p') = Σ_l |u_k(p' + l)|²|v_μ(p' + l)|²/Δ(p' + l)`, `n = 2r + 1`. -/
def phi (r : ℕ) (μ : Fin 4) (p : Fin 4 → ℝ) : ℝ :=
  ∑ m ∈ box r, uk (2 * r + 1) (shift p m) ^ 2 * ‖vs (2 * r + 1) (shift p m μ)‖ ^ 2 / Del (2 * r + 1) (shift p m)

/-- `|sin(p/2)/(n sin(p/(2n)))| ≤ 1`: `|sin(nx)| ≤ n|sin x|`. -/
lemma uf_abs_le_one (n : ℕ) (hn : 1 ≤ n) (p : ℝ) : |uf n p| ≤ 1 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  unfold uf
  split_ifs with h0
  · simp
  · have hd : 0 < |Real.sin (p / (2 * n))| := abs_pos.2 h0
    rw [abs_div, abs_mul, abs_of_pos hn0, div_le_one (by positivity)]
    have e : p / 2 = (n : ℝ) * (p / (2 * n)) := by field_simp
    rw [e]
    exact abs_sin_nat_mul_le _ n

/-- `|sin(p/2)/(n sin(p/(2n)))| ≥ 2/π` for `|p| ≤ π`: `|sin(p/2)| ≥ |p|/π` and `|sin(p/(2n))| ≤ |p|/(2n)`. -/
lemma uf_lower (n : ℕ) (hn : 1 ≤ n) {p : ℝ} (hp : |p| ≤ π) : 2 / π ≤ |uf n p| := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hπ := Real.pi_pos
  unfold uf
  split_ifs with h0
  · rw [abs_one, div_le_one hπ]; linarith [Real.pi_gt_three]
  · have hd : 0 < |Real.sin (p / (2 * n))| := abs_pos.2 h0
    have hp0 : p ≠ 0 := fun h => h0 (by simp [h])
    have hpa : 0 < |p| := abs_pos.2 hp0
    -- `|sin(p/2)| ≥ |p|/π`
    have hnum : |p| / π ≤ |Real.sin (p / 2)| := by
      have h := (chord_bounds hp).1
      rw [norm_exp_sub_one] at h
      have : 2 / π * |p| = 2 * (|p| / π) := by ring
      linarith
    -- `|sin(p/(2n))| ≤ |p|/(2n)`
    have hden : |Real.sin (p / (2 * n))| ≤ |p| / (2 * n) := by
      have := Real.abs_sin_le_abs (x := p / (2 * n))
      rwa [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * n)] at this
    rw [abs_div, abs_mul, abs_of_pos hn0, le_div_iff₀ (by positivity)]
    calc 2 / π * (n * |Real.sin (p / (2 * n))|) ≤ 2 / π * (n * (|p| / (2 * n))) := by gcongr
      _ = |p| / π := by field_simp
      _ ≤ _ := hnum

/-- `|v_μ(p)| ≤ 1`. -/
lemma vs_norm_le_one (n : ℕ) (hn : 1 ≤ n) (p : ℝ) : ‖vs n p‖ ≤ 1 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  unfold vs
  split_ifs with h0
  · simp
  · have hd : 0 < ‖Complex.exp (I * (((1 / n : ℝ) * p : ℝ) : ℂ)) - 1‖ := norm_pos_iff.2 h0
    rw [norm_div, norm_mul, Complex.norm_natCast, div_le_one (by positivity)]
    have h := v_bound n hn p
    have e : (p / n : ℝ) = (1 / n : ℝ) * p := by ring
    rw [e] at h
    exact h

/-- `|v_μ(p)| ≥ 2/π` for `|p| ≤ π`: `|e^{ip} - 1| ≥ 2|p|/π` and `|e^{ip/n} - 1| ≤ |p|/n`. -/
lemma vs_lower (n : ℕ) (hn : 1 ≤ n) {p : ℝ} (hp : |p| ≤ π) : 2 / π ≤ ‖vs n p‖ := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hπ := Real.pi_pos
  unfold vs
  split_ifs with h0
  · rw [norm_one, div_le_one hπ]; linarith [Real.pi_gt_three]
  · have hd : 0 < ‖Complex.exp (I * (((1 / n : ℝ) * p : ℝ) : ℂ)) - 1‖ := norm_pos_iff.2 h0
    have hap : |(1 / n : ℝ) * p| ≤ π := by
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / n)]
      calc 1 / n * |p| ≤ 1 * |p| := by
            gcongr; rw [div_le_one hn0]; exact_mod_cast hn
        _ ≤ π := by linarith
    have hnum := (chord_bounds hp).1
    have hden := (chord_bounds hap).2
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / n)] at hden
    rw [norm_div, norm_mul, Complex.norm_natCast, le_div_iff₀ (by positivity)]
    calc 2 / π * (n * ‖Complex.exp (I * (((1 / n : ℝ) * p : ℝ) : ℂ)) - 1‖) ≤ 2 / π * (n * (1 / n * |p|)) := by
          gcongr
      _ = 2 / π * |p| := by field_simp
      _ ≤ _ := hnum

/-- `Δ(p) ≤ |p|²` for `|p_μ| ≤ π`... and in fact for all `p` with `|a₀p_μ| ≤ π`. -/
lemma Del_le (n : ℕ) (hn : 1 ≤ n) {p : Fin 4 → ℝ} (hp : ∀ μ, |(1 / n : ℝ) * p μ| ≤ π) :
    Del n p ≤ ∑ μ, p μ ^ 2 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  unfold Del
  refine Finset.sum_le_sum fun μ _ => ?_
  have h := (chord_bounds (hp μ)).2
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / n)] at h
  have h' : ‖Complex.exp (I * (((1 / n : ℝ) * p μ : ℝ) : ℂ)) - 1‖ / (1 / n : ℝ) ≤ |p μ| := by
    rw [div_le_iff₀ (by positivity)]; linarith
  calc (‖Complex.exp (I * (((1 / n : ℝ) * p μ : ℝ) : ℂ)) - 1‖ / (1 / n : ℝ)) ^ 2 ≤ |p μ| ^ 2 :=
        pow_le_pow_left₀ (by positivity) h' 2
    _ = p μ ^ 2 := sq_abs _

/-- `Δ(p) ≥ 4π⁻²|p|²` for `|a₀p_μ| ≤ π`. -/
lemma Del_ge (n : ℕ) (hn : 1 ≤ n) {p : Fin 4 → ℝ} (hp : ∀ μ, |(1 / n : ℝ) * p μ| ≤ π) :
    4 / π ^ 2 * ∑ μ, p μ ^ 2 ≤ Del n p := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  unfold Del
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun μ _ => delta_lower (by positivity) (hp μ)

/-- `4π⁻²|p'|² ≤ Δ₀(p') ≤ |p'|²` for `|p'_μ| ≤ π`. -/
lemma Del0_bounds {p : Fin 4 → ℝ} (hp : ∀ μ, |p μ| ≤ π) :
    4 / π ^ 2 * ∑ μ, p μ ^ 2 ≤ Del0 p ∧ Del0 p ≤ ∑ μ, p μ ^ 2 := by
  unfold Del0
  rw [Finset.mul_sum]
  exact ⟨Finset.sum_le_sum fun μ _ => (delta0_bounds (hp μ)).1,
    Finset.sum_le_sum fun μ _ => (delta0_bounds (hp μ)).2⟩

/-- `Σ_{j ∈ ℤ} (1 + |j|)⁻² = π²/3 - 1`, from `Σ_{n ≥ 1} n⁻² = π²/6`. -/
lemma hasSum_inv_one_add_abs_sq :
    HasSum (fun j : ℤ => 1 / (1 + |(j : ℝ)|) ^ 2) (π ^ 2 / 3 - 1) := by
  have h1 : HasSum (fun n : ℕ => (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2) (π ^ 2 / 6 - 0) := by
    have := (hasSum_nat_add_iff' 1).2 hasSum_zeta_two
    simpa using this
  have h2 : HasSum (fun n : ℕ => (1 : ℝ) / ((n + 2 : ℕ) : ℝ) ^ 2) (π ^ 2 / 6 - 1) := by
    have := (hasSum_nat_add_iff' 2).2 hasSum_zeta_two
    simpa [Finset.sum_range_succ] using this
  have e := HasSum.of_nat_of_neg_add_one (f := fun j : ℤ => 1 / (1 + |(j : ℝ)|) ^ 2)
    (h1.congr_fun fun n => by
      simp only [Int.cast_natCast]
      rw [abs_of_nonneg (Nat.cast_nonneg n)]; push_cast; ring_nf)
    (h2.congr_fun fun n => by
      have : |((-((n : ℤ) + 1) : ℤ) : ℝ)| = (n : ℝ) + 1 := by
        push_cast; rw [abs_neg, abs_of_nonneg (by positivity)]
      simp only [this]; push_cast; ring_nf)
  convert e using 1
  ring

/-- `Σ_{|j| ≤ r} 4(1 + |j|)⁻² ≤ 4(π²/3 - 1)`. -/
lemma sum_box_le (r : ℕ) :
    ∑ j ∈ Finset.Icc (-(r : ℤ)) r, 4 / (1 + |(j : ℝ)|) ^ 2 ≤ 4 * (π ^ 2 / 3 - 1) := by
  have h := sum_le_hasSum (Finset.Icc (-(r : ℤ)) r) (fun j _ => by positivity) hasSum_inv_one_add_abs_sq
  calc ∑ j ∈ Finset.Icc (-(r : ℤ)) r, 4 / (1 + |(j : ℝ)|) ^ 2
      = 4 * ∑ j ∈ Finset.Icc (-(r : ℤ)) r, 1 / (1 + |(j : ℝ)|) ^ 2 := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => by ring
    _ ≤ 4 * (π ^ 2 / 3 - 1) := by linarith

lemma shift_zero (p : Fin 4 → ℝ) : shift p 0 = p := by funext ν; simp [shift]

lemma zero_mem_box (r : ℕ) : (0 : Fin 4 → ℤ) ∈ box r := by
  simp [box, Fintype.mem_piFinset]

lemma mem_box {r : ℕ} {m : Fin 4 → ℤ} (hm : m ∈ box r) (ν : Fin 4) : |m ν| ≤ r := by
  have := Fintype.mem_piFinset.1 hm ν
  rw [Finset.mem_Icc] at this
  exact abs_le.2 this

/-- The shifted momenta `p' + 2πm`, `|m_μ| ≤ r`, satisfy `|a₀p_μ| ≤ π`, `a₀ = 1/(2r + 1)`. -/
lemma shift_range {r : ℕ} {p : Fin 4 → ℝ} (hp : ∀ μ, |p μ| ≤ π) {m : Fin 4 → ℤ} (hm : m ∈ box r) (μ : Fin 4) :
    |(1 / ((2 * r + 1 : ℕ) : ℝ)) * shift p m μ| ≤ π := by
  have hπ := Real.pi_pos
  have hbR : |((m μ : ℤ) : ℝ)| ≤ r := by
    have : ((|m μ| : ℤ) : ℝ) ≤ ((r : ℤ) : ℝ) := by exact_mod_cast mem_box hm μ
    rwa [Int.cast_abs, Int.cast_natCast] at this
  have hs : |shift p m μ| ≤ π * (2 * r + 1) := by
    calc |shift p m μ| ≤ |p μ| + |2 * π * (m μ : ℝ)| := abs_add_le _ _
      _ = |p μ| + 2 * π * |((m μ : ℤ) : ℝ)| := by rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
      _ ≤ π * (2 * r + 1) := by nlinarith [hp μ]
  rw [abs_mul, abs_of_pos (by positivity), one_div_mul_eq_div, div_le_iff₀ (by positivity)]
  push_cast
  linarith

set_option maxHeartbeats 1000000 in
/-- **`prop:momentum-space`(iii)**: for `n = L^k = 2r + 1`, `|p'_μ| ≤ π` and `p' ≠ 0`,
`(2/π)¹² ≤ Δ₀(p')φ_μ(p') ≤ π²/4 + π²(4(π²/3 - 1))⁴`. The lower bound is the term `l = 0`: the factors of `u_k(p')` and
`v_μ(p')` are at least `2/π`, and `Δ(p') ≤ |p'|² ≤ (π²/4)Δ₀(p')`. For the upper bound the term `l = 0` is at most
`Δ₀(p')/Δ(p') ≤ π²/4`; for `l ≠ 0` some `|p_ν| ≥ π`, so `Δ(p) ≥ 4`, `Δ₀(p') ≤ 4π²`, and the term is at most
`π²∏_ν4(1 + |m_ν|)⁻²`, whose sum over `l` is at most `π²(4(π²/3 - 1))⁴` by `Σ_{j ∈ ℤ}(1 + |j|)⁻² = π²/3 - 1`. -/
theorem phi_bounds (r : ℕ) (μ : Fin 4) {p : Fin 4 → ℝ} (hp : ∀ ν, |p ν| ≤ π) (hp0 : p ≠ 0) :
    (2 / π) ^ 12 ≤ Del0 p * phi r μ p ∧
      Del0 p * phi r μ p ≤ π ^ 2 / 4 + π ^ 2 * (4 * (π ^ 2 / 3 - 1)) ^ 4 := by
  set n := 2 * r + 1 with hn_def
  have hn : 1 ≤ n := by omega
  have hπ := Real.pi_pos
  set S := ∑ ν, p ν ^ 2 with hS
  have hSpos : 0 < S := by
    obtain ⟨ν, hν⟩ : ∃ ν, p ν ≠ 0 := by
      by_contra h; push_neg at h; exact hp0 (funext h)
    have : 0 < p ν ^ 2 := by positivity
    exact lt_of_lt_of_le this (Finset.single_le_sum (fun i _ => sq_nonneg (p i)) (Finset.mem_univ ν))
  obtain ⟨hD0l, hD0u⟩ := Del0_bounds hp
  have hD0nn : 0 ≤ Del0 p := le_trans (by positivity) hD0l
  -- the terms of `φ_μ`
  set T : (Fin 4 → ℤ) → ℝ := fun m => uk n (shift p m) ^ 2 * ‖vs n (shift p m μ)‖ ^ 2 / Del n (shift p m) with hT
  have hphi : phi r μ p = ∑ m ∈ box r, T m := rfl
  have hTnn : ∀ m, 0 ≤ T m := fun m => by
    simp only [hT]; refine div_nonneg (by positivity) ?_
    unfold Del; positivity
  -- `Δ(p')` lies between `4π⁻²|p'|²` and `|p'|²`
  have hp' : ∀ ν, |(1 / (n : ℝ)) * p ν| ≤ π := by
    intro ν; have := shift_range (r := r) hp (zero_mem_box r) ν; rwa [shift_zero] at this
  have hDl := Del_ge n hn hp'
  have hDu := Del_le n hn hp'
  have hDpos : 0 < Del n p := lt_of_lt_of_le (by positivity) hDl
  have hT0 : T 0 = uk n p ^ 2 * ‖vs n (p μ)‖ ^ 2 / Del n p := by simp only [hT, shift_zero]
  have hq : 0 ≤ Del0 p / Del n p := div_nonneg hD0nn hDpos.le
  constructor
  · -- the lower bound, from the term `l = 0`
    have hu : (2 / π) ^ 4 ≤ |uk n p| := by
      unfold uk; rw [Finset.abs_prod]
      calc (2 / π) ^ 4 = ∏ _ν : Fin 4, (2 / π) := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        _ ≤ ∏ ν, |uf n (p ν)| := Finset.prod_le_prod₀ (fun _ _ => by positivity) fun ν _ => uf_lower n hn (hp ν)
    have hu2 : (2 / π) ^ 8 ≤ uk n p ^ 2 := by
      calc (2 / π) ^ 8 = ((2 / π) ^ 4) ^ 2 := by ring
        _ ≤ |uk n p| ^ 2 := pow_le_pow_left₀ (by positivity) hu 2
        _ = uk n p ^ 2 := sq_abs _
    have hv2 : (2 / π) ^ 2 ≤ ‖vs n (p μ)‖ ^ 2 := pow_le_pow_left₀ (by positivity) (vs_lower n hn (hp μ)) 2
    have hratio : 4 / π ^ 2 ≤ Del0 p / Del n p := by
      rw [le_div_iff₀ hDpos]
      calc 4 / π ^ 2 * Del n p ≤ 4 / π ^ 2 * S := by gcongr
        _ ≤ Del0 p := hD0l
    have hsingle : T 0 ≤ phi r μ p := by
      rw [hphi]; exact Finset.single_le_sum (fun m _ => hTnn m) (zero_mem_box r)
    calc (2 / π) ^ 12 = (2 / π) ^ 8 * (2 / π) ^ 2 * (4 / π ^ 2) := by ring
      _ ≤ uk n p ^ 2 * ‖vs n (p μ)‖ ^ 2 * (Del0 p / Del n p) := by gcongr
      _ = Del0 p * T 0 := by rw [hT0]; ring
      _ ≤ Del0 p * phi r μ p := mul_le_mul_of_nonneg_left hsingle hD0nn
  · -- the term `l = 0`
    have hup0 : Del0 p * T 0 ≤ π ^ 2 / 4 := by
      have hu1 : uk n p ^ 2 ≤ 1 := by
        have : |uk n p| ≤ 1 := by
          unfold uk; rw [Finset.abs_prod]
          exact Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) fun ν _ => uf_abs_le_one n hn _
        rw [← sq_abs]; exact pow_le_one₀ (abs_nonneg _) this
      have hv1 : ‖vs n (p μ)‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) (vs_norm_le_one n hn _)
      have hr : Del0 p / Del n p ≤ π ^ 2 / 4 := by
        rw [div_le_iff₀ hDpos]
        calc Del0 p ≤ S := hD0u
          _ = π ^ 2 / 4 * (4 / π ^ 2 * S) := by field_simp
          _ ≤ π ^ 2 / 4 * Del n p := by gcongr
      rw [hT0]
      calc Del0 p * (uk n p ^ 2 * ‖vs n (p μ)‖ ^ 2 / Del n p) =
            uk n p ^ 2 * ‖vs n (p μ)‖ ^ 2 * (Del0 p / Del n p) := by ring
        _ ≤ 1 * 1 * (π ^ 2 / 4) := by gcongr
        _ = π ^ 2 / 4 := by ring
    -- the terms `l ≠ 0`
    have hS4 : S ≤ 4 * π ^ 2 := by
      calc S = ∑ ν, p ν ^ 2 := rfl
        _ ≤ ∑ _ν : Fin 4, π ^ 2 := Finset.sum_le_sum fun ν _ => by
            have := pow_le_pow_left₀ (abs_nonneg _) (hp ν) 2; rwa [sq_abs] at this
        _ = 4 * π ^ 2 := by simp
    have hD0 : Del0 p ≤ 4 * π ^ 2 := hD0u.trans hS4
    have hupm : ∀ m ∈ box r, m ≠ 0 → Del0 p * T m ≤ π ^ 2 * ∏ ν, 4 / (1 + |((m ν : ℤ) : ℝ)|) ^ 2 := by
      intro m hm hm0
      obtain ⟨ν, hν⟩ : ∃ ν, m ν ≠ 0 := by
        by_contra h; push_neg at h; exact hm0 (funext h)
      have hr := shift_range (r := r) hp hm
      -- `|p_ν| ≥ π`
      have hpν : π ≤ |shift p m ν| := by
        have h1 : (1 : ℝ) ≤ |((m ν : ℤ) : ℝ)| := by
          have : (1 : ℤ) ≤ |m ν| := Int.one_le_abs hν
          rw [← Int.cast_abs]; exact_mod_cast this
        have : |2 * π * (m ν : ℝ)| ≤ |shift p m ν| + |p ν| := by
          have e : 2 * π * (m ν : ℝ) = shift p m ν - p ν := by simp [shift]
          rw [e]; exact abs_sub _ _
        rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)] at this
        nlinarith [hp ν]
      -- `Δ(p) ≥ 4`
      have hD4 : 4 ≤ Del n (shift p m) := by
        have hsum := Del_ge n hn hr
        have : π ^ 2 ≤ ∑ μ, shift p m μ ^ 2 := by
          calc π ^ 2 ≤ |shift p m ν| ^ 2 := pow_le_pow_left₀ hπ.le hpν 2
            _ = shift p m ν ^ 2 := sq_abs _
            _ ≤ _ := Finset.single_le_sum (fun i _ => sq_nonneg (shift p m i)) (Finset.mem_univ ν)
        calc (4 : ℝ) = 4 / π ^ 2 * π ^ 2 := by field_simp
          _ ≤ 4 / π ^ 2 * ∑ μ, shift p m μ ^ 2 := by gcongr
          _ ≤ _ := hsum
      -- `|u_k(p)|² ≤ ∏_ν 4(1 + |m_ν|)⁻²`
      have hu := u_bound n hn hp m (fun ν => by
        have := mem_box hm ν
        simp only [hn_def]; push_cast; linarith)
      have hu2 : uk n (shift p m) ^ 2 ≤ ∏ ν, 4 / (1 + |((m ν : ℤ) : ℝ)|) ^ 2 := by
        have e : ∏ ν, 4 / (1 + |((m ν : ℤ) : ℝ)|) ^ 2 = (∏ ν, 2 / (1 + |((m ν : ℤ) : ℝ)|)) ^ 2 := by
          rw [← Finset.prod_pow]; exact Finset.prod_congr rfl fun ν _ => by rw [div_pow]; norm_num
        rw [e, ← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) hu 2
      have hv1 : ‖vs n (shift p m μ)‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) (vs_norm_le_one n hn _)
      have hP : 0 ≤ ∏ ν, 4 / (1 + |((m ν : ℤ) : ℝ)|) ^ 2 := Finset.prod_nonneg fun _ _ => by positivity
      calc Del0 p * T m = Del0 p * (uk n (shift p m) ^ 2 * ‖vs n (shift p m μ)‖ ^ 2) / Del n (shift p m) := by
            simp only [hT]; ring
        _ ≤ 4 * π ^ 2 * ((∏ ν, 4 / (1 + |((m ν : ℤ) : ℝ)|) ^ 2) * 1) / 4 := by gcongr
        _ = π ^ 2 * ∏ ν, 4 / (1 + |((m ν : ℤ) : ℝ)|) ^ 2 := by ring
    -- the sum over `l` of the bounds
    have hgeom : ∑ m ∈ box r, ∏ ν, 4 / (1 + |((m ν : ℤ) : ℝ)|) ^ 2 ≤ (4 * (π ^ 2 / 3 - 1)) ^ 4 := by
      rw [box, ← Finset.prod_univ_sum (fun _ => Finset.Icc (-(r : ℤ)) r) (fun _ j => 4 / (1 + |(j : ℝ)|) ^ 2),
        Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      exact pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => by positivity) (sum_box_le r) 4
    have hrest : Del0 p * ∑ m ∈ (box r).erase 0, T m ≤ π ^ 2 * (4 * (π ^ 2 / 3 - 1)) ^ 4 := by
      rw [Finset.mul_sum]
      calc ∑ m ∈ (box r).erase 0, Del0 p * T m
          ≤ ∑ m ∈ (box r).erase 0, π ^ 2 * ∏ ν, 4 / (1 + |((m ν : ℤ) : ℝ)|) ^ 2 :=
            Finset.sum_le_sum fun m hm => hupm m (Finset.mem_of_mem_erase hm) (Finset.ne_of_mem_erase hm)
        _ ≤ ∑ m ∈ box r, π ^ 2 * ∏ ν, 4 / (1 + |((m ν : ℤ) : ℝ)|) ^ 2 :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) fun m _ _ =>
              mul_nonneg (by positivity) (Finset.prod_nonneg fun _ _ => by positivity)
        _ = π ^ 2 * ∑ m ∈ box r, ∏ ν, 4 / (1 + |((m ν : ℤ) : ℝ)|) ^ 2 := (Finset.mul_sum _ _ _).symm
        _ ≤ π ^ 2 * (4 * (π ^ 2 / 3 - 1)) ^ 4 := by gcongr
    rw [hphi, ← Finset.add_sum_erase _ _ (zero_mem_box r), mul_add]
    linarith

end MomentumSymbols
end CoreLean

end
