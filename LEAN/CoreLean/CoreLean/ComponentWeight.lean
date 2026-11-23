/-
`lem:component-weight` of BALABAN_CORE.tex (`a021c13be348`), the self-contained steps of the proof of (i)–(iii).

* `m_ge_six`, `eight_m_le`: `m_n = ⌊R_{n+1}/8⌋ ≥ 6` for `R_{n+1} ≥ 50`, and `8m_n ≤ R_{n+1}`.
* `weight_identity`: (ii), `e^{-½⟨A,SA⟩} = Π_𝒳 e^{-½⟨A_𝒳,𝔨_𝒳A_𝒳⟩} e^{𝔕(A)}` with `𝔕` defined by `eq:weight-remainder`.
* `remainder_split`: the form of `𝔕` in the proof of (iii), `𝔕 = ½Σ_𝒳⟨A_𝒳,(𝔨_𝒳 - S_{𝒳𝒳})A_𝒳⟩ - ½Σ_{𝒳≠𝒳'}⟨A_𝒳,SA_{𝒳'}⟩`,
  for any partition of the bonds (the pairings `⟨A(b), K(b,b')A(b')⟩` being arbitrary numbers).
* `weight_positive`: (i), `re⟨A,𝔨_𝒳A⟩ ≥ (γ₀ - √Nε_𝒳)‖A‖² ≥ ½γ₀‖A‖²`.
* `first_sum_bound`: the first sum of (iii) is at most `½N^{3/2}ε t² #𝖡^{out}` when `tr A(b)² ≤ Nt²`.
* `schur_quadratic`: the test of Schur for a quadratic form, used for both sums.
* `cauchy_difference`: the bound `‖S^{(1)} - S^{(0)}‖ ≤ (2/T)B` for a function holomorphic on `|t| < T` and bounded by `B`.
* `walk_cut_distance`, `walk_cut_factor`: `2(2m_nML - M/L - 1) ≥ 3m_nML` and the factor `e^{-¾δm_nML}` of the cut walks.
* `cross_factor`: the factor `e^{½δ}e^{-2δm_nML}` of the walks between two components.
* `rate_le`: `e^{-¾δ_Γ m_nML}`, `e^{-2δ_Γ m_nML}` and `e^{-½δ₂m_nM}` are at most `e^{-κ₂m_n}`.
-/
import Mathlib

open Metric Set

noncomputable section

namespace CoreLean
namespace ComponentWeight

/-- `m_n = ⌊R_{n+1}/8⌋ ≥ 6` for `R_{n+1} ≥ 50`. -/
lemma m_ge_six {R : ℕ} (hR : 50 ≤ R) : 6 ≤ R / 8 := by omega

/-- `8m_n ≤ R_{n+1}`, hence `4m_n ≤ ½R_{n+1}`. -/
lemma eight_m_le (R : ℕ) : 8 * (R / 8) ≤ R := Nat.mul_div_le R 8

section Forms

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ] {𝕜 : Type*} [Field 𝕜]

/-- The part of a double sum in one block `c b = c b' = 𝒳`, and the part across the blocks. -/
lemma block_split (c : ι → κ) (t : ι → ι → 𝕜) :
    ∑ b, ∑ b', t b b' = ∑ X, ∑ b, ∑ b', (if c b = X ∧ c b' = X then t b b' else 0) +
      ∑ b, ∑ b', (if c b ≠ c b' then t b b' else 0) := by
  have h : ∀ b b', t b b' = ∑ X, (if c b = X ∧ c b' = X then t b b' else 0) +
      (if c b ≠ c b' then t b b' else 0) := fun b b' => by
    by_cases hb : c b = c b'
    · have : ∀ X, (c b = X ∧ c b' = X) ↔ c b' = X := fun X => by rw [hb, and_self]
      simp only [hb, and_self, ne_eq, not_true_eq_false, ↓reduceIte, add_zero]
      rw [Finset.sum_ite_eq]; simp
    · have : ∀ X, ¬(c b = X ∧ c b' = X) := fun X h => hb (h.1.trans h.2.symm)
      simp [this, hb]
  conv_lhs => enter [2, b, 2, b']; rw [h b b']
  simp only [Finset.sum_add_distrib]
  congr 1
  calc ∑ b, ∑ b', ∑ X, (if c b = X ∧ c b' = X then t b b' else 0)
      = ∑ b, ∑ X, ∑ b', (if c b = X ∧ c b' = X then t b b' else 0) :=
        Finset.sum_congr rfl fun b _ => Finset.sum_comm
    _ = ∑ X, ∑ b, ∑ b', (if c b = X ∧ c b' = X then t b b' else 0) := Finset.sum_comm

/-- **The remainder in block form** (the proof of (iii)): with `𝔕 = ½Σ_𝒳 q_𝒳 - ½q`,
`𝔕 = ½Σ_𝒳 Σ_{c b = c b' = 𝒳}(k_𝒳 - s)(b, b') - ½Σ_{c b ≠ c b'} s(b, b')`. -/
theorem remainder_split (c : ι → κ) (k : κ → ι → ι → 𝕜) (s : ι → ι → 𝕜) :
    (1 / 2) * ∑ X, ∑ b, ∑ b', (if c b = X ∧ c b' = X then k X b b' else 0) - (1 / 2) * ∑ b, ∑ b', s b b' =
      (1 / 2) * ∑ X, ∑ b, ∑ b', (if c b = X ∧ c b' = X then k X b b' - s b b' else 0) -
        (1 / 2) * ∑ b, ∑ b', (if c b ≠ c b' then s b b' else 0) := by
  rw [block_split c s]
  have e : ∑ X, ∑ b, ∑ b', (if c b = X ∧ c b' = X then k X b b' - s b b' else 0) =
      ∑ X, ∑ b, ∑ b', (if c b = X ∧ c b' = X then k X b b' else 0) -
        ∑ X, ∑ b, ∑ b', (if c b = X ∧ c b' = X then s b b' else 0) := by
    simp only [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun X _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
    split_ifs <;> ring
  rw [e]; ring

/-- **(ii)**: `e^{-½q} = Π_𝒳 e^{-½q_𝒳} e^{𝔕}` with `𝔕 = ½Σ_𝒳 q_𝒳 - ½q` (`eq:weight-remainder`). -/
theorem weight_identity (q : ℂ) (qX : κ → ℂ) :
    Complex.exp (-(1 / 2) * q) =
      (∏ X, Complex.exp (-(1 / 2) * qX X)) * Complex.exp ((1 / 2) * ∑ X, qX X - (1 / 2) * q) := by
  rw [← Complex.exp_sum, ← Complex.exp_add, Finset.mul_sum]
  congr 1
  simp only [neg_mul, Finset.sum_neg_distrib]
  ring

end Forms

/-- **(i)**: if `⟨A,S_{𝒳𝒳}A⟩ ≥ γ₀‖A‖²` and `|⟨A,(𝔨_𝒳 - S_{𝒳𝒳})A⟩| ≤ √Nε_𝒳‖A‖²` with `√Nε_𝒳 ≤ ½γ₀`, then
`re⟨A,𝔨_𝒳A⟩ ≥ ½γ₀‖A‖²`. -/
theorem weight_positive {kA sA n γ₀ e : ℝ} (hn : 0 ≤ n) (hS : γ₀ * n ≤ sA) (hd : |kA - sA| ≤ e * n)
    (he : e ≤ γ₀ / 2) : γ₀ / 2 * n ≤ kA := by
  have h1 : -(e * n) ≤ kA - sA := (abs_le.1 hd).1
  have h2 : e * n ≤ γ₀ / 2 * n := mul_le_mul_of_nonneg_right he hn
  linarith

/-- **The first sum of (iii)**: if `|d_𝒳| ≤ √Nε Σ_{c b = 𝒳} tr A(b)²` and `0 ≤ tr A(b)² ≤ Nt²`, then
`|½Σ_𝒳 d_𝒳| ≤ ½N^{3/2}ε t² #𝖡^{out}` (`N^{3/2} = √N·N`). -/
theorem first_sum_bound {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ] (c : ι → κ) (d : κ → ℝ)
    (nrm : ι → ℝ) {sN N ε t : ℝ} (hsN : 0 ≤ sN) (hε : 0 ≤ ε)
    (hnt : ∀ b, nrm b ≤ N * t ^ 2)
    (hd : ∀ X, |d X| ≤ sN * ε * ∑ b ∈ Finset.univ.filter (fun b => c b = X), nrm b) :
    |(1 / 2) * ∑ X, d X| ≤ (1 / 2) * (sN * N) * ε * t ^ 2 * Fintype.card ι := by
  have hfib : ∑ X, ∑ b ∈ Finset.univ.filter (fun b => c b = X), nrm b = ∑ b, nrm b :=
    Finset.sum_fiberwise Finset.univ c nrm
  have hsum : ∑ b, nrm b ≤ Fintype.card ι * (N * t ^ 2) := by
    calc ∑ b, nrm b ≤ ∑ _b : ι, N * t ^ 2 := Finset.sum_le_sum fun b _ => hnt b
      _ = Fintype.card ι * (N * t ^ 2) := by rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  calc (1 / 2) * |∑ X, d X| ≤ (1 / 2) * ∑ X, |d X| := by gcongr; exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ (1 / 2) * ∑ X, sN * ε * ∑ b ∈ Finset.univ.filter (fun b => c b = X), nrm b := by
        gcongr with X; exact hd X
    _ = (1 / 2) * (sN * ε * ∑ b, nrm b) := by rw [← Finset.mul_sum, hfib]
    _ ≤ (1 / 2) * (sN * ε * (Fintype.card ι * (N * t ^ 2))) := by gcongr
    _ = (1 / 2) * (sN * N) * ε * t ^ 2 * Fintype.card ι := by ring

/-- **The test of Schur for a quadratic form**: if `|t(b,b')| ≤ K(b,b')x_bx_{b'}` with `K ≥ 0` and the row and
column sums of `K` at most `C`, then `|Σ_{b,b'} t(b,b')| ≤ CΣ_b x_b²`. -/
theorem schur_quadratic {ι : Type*} [Fintype ι] (t : ι → ι → ℂ) (K : ι → ι → ℝ) (x : ι → ℝ) {C : ℝ}
    (hK : ∀ b b', 0 ≤ K b b') (ht : ∀ b b', ‖t b b'‖ ≤ K b b' * x b * x b')
    (hrow : ∀ b, ∑ b', K b b' ≤ C) (hcol : ∀ b', ∑ b, K b b' ≤ C) :
    ‖∑ b, ∑ b', t b b'‖ ≤ C * ∑ b, x b ^ 2 := by
  have hamgm : ∀ b b', K b b' * x b * x b' ≤ K b b' * (x b ^ 2 / 2 + x b' ^ 2 / 2) := fun b b' => by
    have : x b * x b' ≤ x b ^ 2 / 2 + x b' ^ 2 / 2 := by nlinarith [sq_nonneg (x b - x b')]
    calc K b b' * x b * x b' = K b b' * (x b * x b') := by ring
      _ ≤ K b b' * (x b ^ 2 / 2 + x b' ^ 2 / 2) := mul_le_mul_of_nonneg_left this (hK b b')
  have hr : ∑ b, ∑ b', K b b' * (x b ^ 2 / 2) ≤ ∑ b, C * (x b ^ 2 / 2) := Finset.sum_le_sum fun b _ => by
    rw [← Finset.sum_mul]; exact mul_le_mul_of_nonneg_right (hrow b) (by positivity)
  have hc : ∑ b, ∑ b', K b b' * (x b' ^ 2 / 2) ≤ ∑ b', C * (x b' ^ 2 / 2) := by
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun b' _ => ?_
    rw [← Finset.sum_mul]; exact mul_le_mul_of_nonneg_right (hcol b') (by positivity)
  calc ‖∑ b, ∑ b', t b b'‖ ≤ ∑ b, ∑ b', ‖t b b'‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => norm_sum_le _ _)
    _ ≤ ∑ b, ∑ b', K b b' * (x b ^ 2 / 2 + x b' ^ 2 / 2) :=
        Finset.sum_le_sum fun b _ => Finset.sum_le_sum fun b' _ => (ht b b').trans (hamgm b b')
    _ = ∑ b, ∑ b', K b b' * (x b ^ 2 / 2) + ∑ b, ∑ b', K b b' * (x b' ^ 2 / 2) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun b' _ => ?_
        ring
    _ ≤ ∑ b, C * (x b ^ 2 / 2) + ∑ b', C * (x b' ^ 2 / 2) := add_le_add hr hc
    _ = C * ∑ b, x b ^ 2 := by rw [← Finset.sum_add_distrib, Finset.mul_sum]; congr 1; funext b; ring

/-- **The formula of Cauchy along the move**: a function holomorphic on `|t| < T`, `T > 1`, and bounded there by
`B` changes by at most `(2/T)B` between `t = 0` and `t = 1`. -/
theorem cauchy_difference {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : ℂ → E} {T B : ℝ}
    (hT : 1 < T) (hf : DifferentiableOn ℂ f (ball 0 T)) (hB : ∀ z ∈ ball (0 : ℂ) T, ‖f z‖ ≤ B) :
    ‖f 1 - f 0‖ ≤ 2 / T * B := by
  have h0 : (0 : ℂ) ∈ ball (0 : ℂ) T := mem_ball_self (by linarith)
  have hmaps : MapsTo f (ball 0 T) (closedBall (f 0) (2 * B)) := fun z hz => by
    rw [mem_closedBall, dist_eq_norm]
    calc ‖f z - f 0‖ ≤ ‖f z‖ + ‖f 0‖ := norm_sub_le _ _
      _ ≤ B + B := add_le_add (hB z hz) (hB 0 h0)
      _ = 2 * B := by ring
  have h1 : (1 : ℂ) ∈ ball (0 : ℂ) T := by rw [mem_ball, dist_zero_right, norm_one]; exact hT
  have := Complex.dist_le_div_mul_dist_of_mapsTo_ball hf hmaps h1
  rw [dist_eq_norm, dist_eq_norm, sub_zero, norm_one, mul_one] at this
  calc ‖f 1 - f 0‖ ≤ 2 * B / T := this
    _ = 2 / T * B := by ring

/-- **The distance of a cut walk**: `2(2mML - M/L - 1) ≥ 3mML` for `m ≥ 6`, `M ≥ 1`, `L ≥ 1`. -/
lemma walk_cut_distance {m M L : ℝ} (hm : 6 ≤ m) (hM : 1 ≤ M) (hL : 1 ≤ L) :
    3 * m * M * L ≤ 2 * (2 * m * M * L - M / L - 1) := by
  have h1 : M / L ≤ M := div_le_self (by linarith) hL
  have h2 : 1 ≤ M * L := by nlinarith
  have h3 : 6 * (M * L) ≤ m * (M * L) := mul_le_mul_of_nonneg_right hm (by linarith)
  nlinarith

/-- **The factor of a cut walk**: for `d ≥ 3mML`, `e^{-½δd} ≤ e^{-¾δmML}e^{-¼δd}`. -/
lemma walk_cut_factor {δ d m M L : ℝ} (hδ : 0 ≤ δ) (hd : 3 * m * M * L ≤ d) :
    Real.exp (-(1 / 2) * δ * d) ≤ Real.exp (-(3 / 4) * δ * m * M * L) * Real.exp (-(1 / 4) * δ * d) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.2
  nlinarith

/-- **The factor between two components**: for `d ≥ 8mML - 2`, `e^{-½δd} ≤ e^{½δ}e^{-2δmML}e^{-¼δd}`. -/
lemma cross_factor {δ d m M L : ℝ} (hδ : 0 ≤ δ) (hd : 8 * m * M * L - 2 ≤ d) :
    Real.exp (-(1 / 2) * δ * d) ≤
      Real.exp ((1 / 2) * δ) * Real.exp (-2 * δ * m * M * L) * Real.exp (-(1 / 4) * δ * d) := by
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.2
  nlinarith

/-- `R_{n+1}ML - 2 ≥ 8m_nML - 2` from `8m_n ≤ R_{n+1}`. -/
lemma cross_distance {R m M L : ℝ} (hR : 8 * m ≤ R) (hM : 0 ≤ M) (hL : 0 ≤ L) :
    8 * m * M * L - 2 ≤ R * M * L - 2 := by
  have : 8 * m * (M * L) ≤ R * (M * L) := mul_le_mul_of_nonneg_right hR (mul_nonneg hM hL)
  nlinarith

/-- **The rates** (end of the proof of (iii)): from `δ_M M ≥ 2κ₂`, `δ_Γ ≥ δ_M`, `δ₂ ≥ δ_M`, `L ≥ 1`, `m ≥ 0`,
the three factors are at most `e^{-κ₂m}`. -/
theorem rate_le {δM δΓ δ₂ M L κ₂ m : ℝ} (hδM : 0 ≤ δM) (hM : 0 ≤ M) (hL : 1 ≤ L) (hm : 0 ≤ m)
    (hMk : 2 * κ₂ ≤ δM * M) (hΓ : δM ≤ δΓ) (h2 : δM ≤ δ₂) :
    Real.exp (-(3 / 4) * δΓ * m * M * L) ≤ Real.exp (-κ₂ * m) ∧
      Real.exp (-2 * δΓ * m * M * L) ≤ Real.exp (-κ₂ * m) ∧
      Real.exp (-(1 / 2) * δ₂ * m * M) ≤ Real.exp (-κ₂ * m) := by
  have hΓM : δM * M ≤ δΓ * M := mul_le_mul_of_nonneg_right hΓ hM
  have h2M : δM * M ≤ δ₂ * M := mul_le_mul_of_nonneg_right h2 hM
  have hΓ0 : 0 ≤ δΓ * M := (mul_nonneg hδM hM).trans hΓM
  have hL' : δΓ * M ≤ δΓ * M * L := le_mul_of_one_le_right hΓ0 hL
  have hk1 : κ₂ ≤ (3 / 4) * (δΓ * M * L) := by
    linarith
  have hk2 : κ₂ ≤ 2 * (δΓ * M * L) := by linarith
  have hk3 : κ₂ ≤ (1 / 2) * (δ₂ * M) := by linarith
  refine ⟨Real.exp_le_exp.2 ?_, Real.exp_le_exp.2 ?_, Real.exp_le_exp.2 ?_⟩
  · have := mul_le_mul_of_nonneg_right hk1 hm; nlinarith
  · have := mul_le_mul_of_nonneg_right hk2 hm; nlinarith
  · have := mul_le_mul_of_nonneg_right hk3 hm; nlinarith

end ComponentWeight
end CoreLean

end
