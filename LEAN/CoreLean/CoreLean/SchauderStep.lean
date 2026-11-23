/-
`prop:schauder` of BALABAN_CORE.tex (`a021c13be348`), from `prop:interior-schauder` (`InteriorSchauder.lean`), in the
model `ηℤ⁴ = ℤ⁴`, `a = a_j = Kη` of that file. The core's proof is the interior estimate applied to
`v = G'D^*_{𝐔,μ}λ`, with the equation `Δ_𝐔v = D^*_{𝐔,μ}λ - Q'^*𝖺Q'v` (so `ρ = -Q'^*𝖺Q'v`), followed by the
multiplication by `ζ`. Here the inputs which the core takes from `thm:propagators` and from the hypothesis (b) are
hypotheses: `‖v‖ ≤ Ta` and `‖∇_𝐔v‖ ≤ T` on `Q_y` (`eq:schauder-input`, `T = Wθ Λ`), `‖ρ‖ ≤ qT/a` (from (b),
`q = q_QL²`), and the modulus `Λ₀` of `λ` along the shortest paths in `Q_y`.

* `schauder_step`: for `x, x' ∈ S = {|x - y|_∞ ≤ 2a - η}` with `|x - x'|₁ ≤ a`, every shortest path `γ` and every `ν`,
  `‖Ad_{𝐔(γ)}(ζD_{𝐔,ν}v)(x') - (ζD_{𝐔,ν}v)(x)‖ ≤ (Z₀C_I(β)((1 + q)T + Λ₀) + Z_βT)(|x - x'|₁/a)^β`, with
  `|ζ| ≤ Z₀` and the modulus `Z_β` of `ζ`: `eq:schauder` once `Λ₀` is bounded by a multiple of `T`.
* The modulus of `λ` in the units of `a` (the core's claim, the transports aside): for `a/L ≤ a' ≤ La` and
  `|z|₁ ≤ min{a', a}`, `H(|z|₁/a')^β + (|z|₁/a)S ≤ L(H + S)(|z|₁/a)^β` (`modulus_near`), and for `a/L < |z|₁ ≤ a`,
  `2S ≤ 2LS(|z|₁/a)^β` (`modulus_far`).
-/
import CoreLean.InteriorSchauder

open Matrix NormedSpace
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace CoreLean
namespace InteriorSchauder

variable {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ

lemma Ad_zero' (W : (Matrix (Fin N) (Fin N) ℂ)ˣ) : Ad W (0 : Mat) = 0 := by simp [Ad]

lemma Dbw_zero (η : ℝ) (A : Fin 4 → (Fin 4 → ℤ) → Mat) (κ : Fin 4) (n : Fin 4 → ℤ) :
    Dbw η A κ (fun _ => (0 : Mat)) n = 0 := by
  simp [Dbw, Ad_zero']

/-- **`prop:schauder`** from the interior estimate. -/
theorem schauder_step {η : ℝ} {K : ℕ} {y : Fin 4 → ℤ} {A : Fin 4 → (Fin 4 → ℤ) → Mat}
    {v lam rho : (Fin 4 → ℤ) → Mat} {μ : Fin 4} {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hη : 0 < η) (hK : 1 ≤ K)
    (hA : ∀ μ n, InQ y (8 * K) n → InQ y (8 * K) (n + e4 μ) → (K * η) * ‖A μ n‖ ≤ 1 / 32)
    (hdA : ∀ μ ν n, InQ y (8 * K) n → InQ y (8 * K) (n + e4 ν) → InQ y (8 * K) (n + e4 μ) →
      InQ y (8 * K) (n + e4 ν + e4 μ) → (K * η) ^ 2 * ‖dfw η ν (A μ) n‖ ≤ 1 / 32)
    (heq : ∀ n, InQ y (5 * K) n → covLap η A v n = Dbw η A μ lam n + rho n)
    {T q Λ₀ : ℝ} (hT : 0 ≤ T) (hq : 0 ≤ q) (hΛ₀ : 0 ≤ Λ₀)
    (hv : ∀ n, InQ y (8 * K) n → ‖v n‖ ≤ T * (K * η))
    (hDv : ∀ ν n, InQ y (8 * K) n → InQ y (8 * K) (n + e4 ν) → ‖Dfw η A ν v n‖ ≤ T)
    (hrho : ∀ n, InQ y (8 * K) n → ‖rho n‖ ≤ q * T / (K * η))
    (hlam : ∀ n, InQ y (8 * K) n → ‖lam n‖ ≤ Λ₀)
    (hhol : ∀ x x' l, InQ y (8 * K) x → InQ y (8 * K) x' → l1 (x' - x) ≤ K → IsShortest x x' l →
      ‖Ad (pathT η A (sgnv x x') x l) (lam x') - lam x‖ ≤ Λ₀ * (η * l1 (x' - x) / (K * η)) ^ β)
    (ζ : (Fin 4 → ℤ) → ℝ) {Z₀ Zβ : ℝ} (hζ : ∀ n, |ζ n| ≤ Z₀)
    (hζhol : ∀ x x', l1 (x' - x) ≤ K → |ζ x' - ζ x| ≤ Zβ * (l1 (x' - x) / K) ^ β)
    {x x' : Fin 4 → ℤ} (hx : InQ y (4 * K - 2) x) (hx' : InQ y (4 * K - 2) x') (hxx : l1 (x' - x) ≤ K)
    {l : List (Fin 4)} (hl : IsShortest x x' l) (ν : Fin 4) :
    ‖Ad (pathT η A (sgnv x x') x l) ((ζ x' : ℂ) • Dfw η A ν v x') - (ζ x : ℂ) • Dfw η A ν v x‖ ≤
      (Z₀ * (CI β * ((1 + q) * T + Λ₀)) + Zβ * T) * (l1 (x' - x) / K) ^ β := by
  -- the family `λ_κ` with the single member `λ_μ = λ`
  set lamF : Fin 4 → (Fin 4 → ℤ) → Mat := fun κ => if κ = μ then lam else fun _ => 0
  set ΛF : Fin 4 → ℝ := fun κ => if κ = μ then Λ₀ else 0
  have hsumΛ : ∑ κ, ΛF κ = Λ₀ := by simp [ΛF]
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have ha : 0 < (K : ℝ) * η := mul_pos hKr hη
  have h1q : T ≤ (1 + q) * T := by nlinarith
  have H : Hyp η K y A v lamF rho ((1 + q) * T) ΛF β := by
    refine ⟨hη, hK, hA, hdA, fun n hn => ?_, fun n hn => ?_, fun ν' n hn hn' => ?_, fun n hn => ?_,
      fun κ n hn => ?_, fun κ x₁ x₂ l' h₁ h₂ h₁₂ hl' => ?_⟩
    · rw [heq n hn, Finset.sum_eq_single μ]
      · simp [lamF]
      · intro κ _ hκ; simp only [lamF, if_neg hκ]; exact Dbw_zero η A κ n
      · intro h; exact absurd (Finset.mem_univ μ) h
    · exact (hv n hn).trans (mul_le_mul_of_nonneg_right h1q ha.le)
    · exact (hDv ν' n hn hn').trans h1q
    · refine (hrho n hn).trans ?_
      exact div_le_div_of_nonneg_right (by nlinarith) ha.le
    · by_cases hκ : κ = μ
      · simp only [lamF, ΛF, if_pos hκ]; exact hlam n hn
      · simp [lamF, ΛF, if_neg hκ]
    · by_cases hκ : κ = μ
      · simp only [lamF, ΛF, if_pos hκ]; exact hhol x₁ x₂ l' h₁ h₂ h₁₂ hl'
      · simp [lamF, ΛF, if_neg hκ, Ad_zero']
  have hI := interior_schauder hβ0 hβ1 H hx hx' hxx hl ν
  rw [hsumΛ, H.holder_rewrite] at hI
  -- the multiplication by `ζ`
  have hx8 : InQ y (8 * K) x := hx.mono (by omega)
  have hxe : InQ y (8 * K) (x + e4 ν) := (hx.add_e ν).mono (by omega)
  have hDx : ‖Dfw η A ν v x‖ ≤ T := hDv ν x hx8 hxe
  have e : Ad (pathT η A (sgnv x x') x l) ((ζ x' : ℂ) • Dfw η A ν v x') - (ζ x : ℂ) • Dfw η A ν v x =
      (ζ x' : ℂ) • (Ad (pathT η A (sgnv x x') x l) (Dfw η A ν v x') - Dfw η A ν v x) +
        ((ζ x' - ζ x : ℝ) : ℂ) • Dfw η A ν v x := by
    rw [Ad_smul, smul_sub]; push_cast; rw [sub_smul]; abel
  rw [e]
  set t := (l1 (x' - x) / K) ^ β
  have ht : 0 ≤ t := Real.rpow_nonneg (div_nonneg (by unfold l1; positivity) hKr.le) β
  have hZ0 : 0 ≤ Z₀ := (abs_nonneg _).trans (hζ x)
  calc ‖(ζ x' : ℂ) • (Ad (pathT η A (sgnv x x') x l) (Dfw η A ν v x') - Dfw η A ν v x) +
        ((ζ x' - ζ x : ℝ) : ℂ) • Dfw η A ν v x‖
      ≤ ‖(ζ x' : ℂ) • (Ad (pathT η A (sgnv x x') x l) (Dfw η A ν v x') - Dfw η A ν v x)‖ +
        ‖((ζ x' - ζ x : ℝ) : ℂ) • Dfw η A ν v x‖ := norm_add_le _ _
    _ = |ζ x'| * ‖Ad (pathT η A (sgnv x x') x l) (Dfw η A ν v x') - Dfw η A ν v x‖ +
        |ζ x' - ζ x| * ‖Dfw η A ν v x‖ := by
        rw [norm_smul, norm_smul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ Z₀ * (CI β * ((1 + q) * T + Λ₀) * t) + Zβ * t * T := by
        have hZt : 0 ≤ Zβ * t := (abs_nonneg _).trans (hζhol x x' hxx)
        exact add_le_add (mul_le_mul (hζ x') hI (norm_nonneg _) hZ0)
          (mul_le_mul (hζhol x x' hxx) hDx (norm_nonneg _) hZt)
    _ = (Z₀ * (CI β * ((1 + q) * T + Λ₀)) + Zβ * T) * t := by ring

/-- **`cor:schauder-vector`**, the interior step for the components: each component `v_μ` of `𝐯 = GD^*_{𝐔,κ}J`
satisfies `Δ_𝐔v_μ = D^*_{𝐔,κ}J_μ + ρ_μ` with `ρ = -(𝖪(𝐔) + Δ'(𝐔) - DPD^* + Q^*𝖺Q)𝐯`, and `schauder_step` applies to
it with the bounds of `ρ_μ` as hypotheses. -/
theorem schauder_vector_component {η : ℝ} {K : ℕ} {y : Fin 4 → ℤ} {A : Fin 4 → (Fin 4 → ℤ) → Mat}
    {v J rho : Fin 4 → (Fin 4 → ℤ) → Mat} {κ : Fin 4} {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hη : 0 < η)
    (hK : 1 ≤ K)
    (hA : ∀ μ n, InQ y (8 * K) n → InQ y (8 * K) (n + e4 μ) → (K * η) * ‖A μ n‖ ≤ 1 / 32)
    (hdA : ∀ μ ν n, InQ y (8 * K) n → InQ y (8 * K) (n + e4 ν) → InQ y (8 * K) (n + e4 μ) →
      InQ y (8 * K) (n + e4 ν + e4 μ) → (K * η) ^ 2 * ‖dfw η ν (A μ) n‖ ≤ 1 / 32)
    (heq : ∀ μ n, InQ y (5 * K) n → covLap η A (v μ) n = Dbw η A κ (J μ) n + rho μ n)
    {T q Λ₀ : ℝ} (hT : 0 ≤ T) (hq : 0 ≤ q) (hΛ₀ : 0 ≤ Λ₀)
    (hv : ∀ μ n, InQ y (8 * K) n → ‖v μ n‖ ≤ T * (K * η))
    (hDv : ∀ μ ν n, InQ y (8 * K) n → InQ y (8 * K) (n + e4 ν) → ‖Dfw η A ν (v μ) n‖ ≤ T)
    (hrho : ∀ μ n, InQ y (8 * K) n → ‖rho μ n‖ ≤ q * T / (K * η))
    (hJ : ∀ μ n, InQ y (8 * K) n → ‖J μ n‖ ≤ Λ₀)
    (hhol : ∀ μ x x' l, InQ y (8 * K) x → InQ y (8 * K) x' → l1 (x' - x) ≤ K → IsShortest x x' l →
      ‖Ad (pathT η A (sgnv x x') x l) (J μ x') - J μ x‖ ≤ Λ₀ * (η * l1 (x' - x) / (K * η)) ^ β)
    (ζ : (Fin 4 → ℤ) → ℝ) {Z₀ Zβ : ℝ} (hζ : ∀ n, |ζ n| ≤ Z₀)
    (hζhol : ∀ x x', l1 (x' - x) ≤ K → |ζ x' - ζ x| ≤ Zβ * (l1 (x' - x) / K) ^ β)
    {x x' : Fin 4 → ℤ} (hx : InQ y (4 * K - 2) x) (hx' : InQ y (4 * K - 2) x') (hxx : l1 (x' - x) ≤ K)
    {l : List (Fin 4)} (hl : IsShortest x x' l) (μ ν : Fin 4) :
    ‖Ad (pathT η A (sgnv x x') x l) ((ζ x' : ℂ) • Dfw η A ν (v μ) x') - (ζ x : ℂ) • Dfw η A ν (v μ) x‖ ≤
      (Z₀ * (CI β * ((1 + q) * T + Λ₀)) + Zβ * T) * (l1 (x' - x) / K) ^ β :=
  schauder_step hβ0 hβ1 hη hK hA hdA (heq μ) hT hq hΛ₀ (hv μ) (hDv μ) (hrho μ) (hJ μ) (hhol μ) ζ hζ hζhol
    hx hx' hxx hl ν

/-- The modulus of `λ` near the diagonal, in the units of `a`. -/
theorem modulus_near {a a' L z H S β : ℝ} (ha : 0 < a) (hL : 1 ≤ L) (ha' : a / L ≤ a') (hz0 : 0 ≤ z)
    (hza' : z ≤ a') (hza : z ≤ a) (hH : 0 ≤ H) (hS : 0 ≤ S) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    H * (z / a') ^ β + z / a * S ≤ L * (H + S) * (z / a) ^ β := by
  have hL0 : 0 < L := by linarith
  have ha'0 : 0 < a' := lt_of_lt_of_le (div_pos ha hL0) ha'
  have hza1 : z / a ≤ 1 := (div_le_one ha).2 hza
  have hza0 : 0 ≤ z / a := div_nonneg hz0 ha.le
  -- `(z/a')^β ≤ (L z/a)^β ≤ L(z/a)^β`
  have h1 : z / a' ≤ L * (z / a) := by
    rw [div_le_iff₀ ha'0]
    calc z = L * (z / a) * (a / L) := by field_simp
      _ ≤ L * (z / a) * a' := mul_le_mul_of_nonneg_left ha' (by positivity)
  have h2 : (z / a') ^ β ≤ L * (z / a) ^ β := by
    calc (z / a') ^ β ≤ (L * (z / a)) ^ β := Real.rpow_le_rpow (div_nonneg hz0 ha'0.le) h1 hβ0
      _ = L ^ β * (z / a) ^ β := Real.mul_rpow hL0.le hza0
      _ ≤ L * (z / a) ^ β := by
          gcongr
          calc L ^ β ≤ L ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL hβ1
            _ = L := Real.rpow_one L
  -- `z/a ≤ (z/a)^β ≤ L(z/a)^β`
  have h3 : z / a ≤ L * (z / a) ^ β := by
    have : z / a ≤ (z / a) ^ β := by
      rcases eq_or_lt_of_le hza0 with h | h
      · rw [← h]; exact Real.rpow_nonneg (le_refl 0) β
      · calc z / a = (z / a) ^ (1 : ℝ) := (Real.rpow_one _).symm
          _ ≤ (z / a) ^ β := Real.rpow_le_rpow_of_exponent_ge h hza1 hβ1
    calc z / a ≤ (z / a) ^ β := this
      _ ≤ L * (z / a) ^ β := le_mul_of_one_le_left (Real.rpow_nonneg hza0 _) hL
  calc H * (z / a') ^ β + z / a * S ≤ H * (L * (z / a) ^ β) + L * (z / a) ^ β * S := by gcongr
    _ = L * (H + S) * (z / a) ^ β := by ring

/-- The modulus of `λ` away from the diagonal. -/
theorem modulus_far {a L z S β : ℝ} (ha : 0 < a) (hL : 1 ≤ L) (hz : a / L < z) (hza : z ≤ a) (hS : 0 ≤ S)
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) : 2 * S ≤ 2 * L * S * (z / a) ^ β := by
  have hL0 : 0 < L := by linarith
  have hz0 : 0 < z / a := div_pos (lt_trans (div_pos ha hL0) hz) ha
  have hza1 : z / a ≤ 1 := (div_le_one ha).2 hza
  have h1 : 1 / L ≤ z / a := by
    rw [div_le_div_iff₀ hL0 ha]; rw [div_lt_iff₀ hL0] at hz; linarith
  have h2 : z / a ≤ (z / a) ^ β := by
    calc z / a = (z / a) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (z / a) ^ β := Real.rpow_le_rpow_of_exponent_ge hz0 hza1 hβ1
  have h3 : 1 ≤ L * (z / a) ^ β := by
    calc (1 : ℝ) = L * (1 / L) := by field_simp
      _ ≤ L * (z / a) ^ β := mul_le_mul_of_nonneg_left (h1.trans h2) hL0.le
  nlinarith

end InteriorSchauder
end CoreLean

end
