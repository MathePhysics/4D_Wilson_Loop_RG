/-
`lem:cubic-gradient` of BALABAN_CORE.tex, the bound of `g` and the conclusion at one bond.

For a positive bond `b = (μ, x)` and `z ∈ ℂ`, `g(z) = 𝒥(zA)(b) - J(𝐔)(b) - z(D^*_𝐔D_𝐔A)(b)`. By
`eq:current-expansion` at the form `zA`,
`g(z) = (E_{-iazA(b)} - 1)J(e^{iazA}𝐔)(b) + 𝐅(𝐔, zA)(b)`, and `J(e^{iazA}𝐔)(b) = J(𝐔)(b) + z(D^*DA)(b) + 𝐅(𝐔, zA)(b)`.
The four factors are bounded by `norm_Eop_sub_one_le` (`‖E_Z - 1‖ ≤ 4‖Z‖` for `‖Z‖ ≤ ½`, from the series of
`E_Z = φ(ad Z)`), `norm_current_le` (`‖J(𝐔)(b)‖ ≤ (27/2)√N η⁻³ω`), `norm_DsD_le` (`‖(D^*DA)(b)‖ ≤ 18η⁻¹m₁`), and
`current_remainder` (`eq:current-remainder`, `C₈ = 512N`); this is `norm_g_le`, in the local quantities
`m₀`, `m₁`, `ω` of `lem:current-expansion`.

`norm_g_scale` is the bound of the core in the quantities of the scale `j` (`s = a_j ≥ η`):
`‖A‖ ≤ Ls⁻¹m`, first differences `≤ L²s⁻²m`, `‖𝐔(∂p) - 1‖ ≤ L²ε(η/s)²` on the plaquettes at `b`, and
`|z|Lm ≤ c₆`, `L²ε ≤ c₆`; it gives `‖g(z)‖ ≤ C_g s⁻³|z|m(|z|m + ε)` with the core's
`C_g = 84√NL³ + 108L³ + 6C₈L⁴`. With Cauchy's estimate on the circle `|z| = c₆/(Lm)` (`norm_N0_le`) this
gives `cubic_gradient_bond`: `‖𝖭₀(A)(b)‖ ≤ C₀s⁻³m²`, `C₀ = 4C_g`, for `m ≤ c₆/(2L)`, which is
`eq:cubic-gradient` at the bond `b` (the weighted norms supply exactly these local bounds).
-/
import CoreLean.CubicCauchy
import CoreLean.CurrentRemainder

open Matrix Complex BakerCampbellHausdorff Filter
open scoped Topology Matrix.Norms.L2Operator

noncomputable section

namespace CoreLean

variable {N n : ℕ} [NeZero n] (a : ℂ)

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "GLN" => (Matrix (Fin N) (Fin N) ℂ)ˣ

variable {G : GaugeGroup N}

/-- `‖E_Z - 1‖ ≤ 4‖Z‖` for `‖Z‖ ≤ ½`: `‖φ(ad Z) - 1‖ ≤ e^{‖ad Z‖} - 1 ≤ 2‖ad Z‖`. -/
lemma norm_Eop_sub_one_le {Z : Mat} (hZ : ‖Z‖ ≤ 1 / 2) : ‖Eop Z - 1‖ ≤ 4 * ‖Z‖ := by
  have h1 := norm_expSubOneDiv_sub_one_le (𝕂 := ℂ) (ad ℂ Z)
  have h2 : ‖ad ℂ Z‖ ≤ 2 * ‖Z‖ := norm_ad_le (𝕂 := ℂ) Z
  have h3 : Real.exp ‖ad ℂ Z‖ - 1 ≤ 2 * ‖ad ℂ Z‖ := by
    have := Real.abs_exp_sub_one_le (x := ‖ad ℂ Z‖)
      (by rw [abs_of_nonneg (norm_nonneg _)]; linarith)
    rw [abs_of_nonneg (norm_nonneg _)] at this
    exact (le_abs_self _).trans this
  unfold Eop
  linarith

lemma norm_sum_ne_le {μ : Fin 4} {f : Fin 4 → Mat} {B : ℝ} (h : ∀ ν, ν ≠ μ → ‖f ν‖ ≤ B) :
    ‖∑ ν, (if ν ≠ μ then f ν else 0)‖ ≤ 3 * B := by
  have hB : ∀ ν, ‖(if ν ≠ μ then f ν else 0)‖ ≤ if ν ≠ μ then B else 0 := by
    intro ν
    split_ifs with hν
    · exact h ν hν
    · simp
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun ν _ => hB ν).trans (le_of_eq ?_))
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, Finset.filter_ne',
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  norm_num

lemma Dfw_smul_form (U : Config N n) (c : ℂ) (A : Form1 N n) (ν μ : Fin 4) (y : Site n) :
    Dfw a U ν ((c • A) μ) y = c • Dfw a U ν (A μ) y := by
  simp only [Dfw, Pi.smul_apply, Ad_smul, smul_sub, smul_comm a⁻¹ c]

lemma D1_smul_form (U : Config N n) (c : ℂ) (A : Form1 N n) : D1 a U (c • A) = c • D1 a U A := by
  funext μ ν x
  rw [D1_smul]; rfl

lemma Ds2_smul (U : Config N n) (c : ℂ) (F : Form2 N n) : Ds2 a U (c • F) = c • Ds2 a U F := by
  funext μ x
  simp only [Ds2, Dbw, Pi.smul_apply, Ad_smul, Finset.smul_sum]
  refine Finset.sum_congr rfl fun ν _ => ?_
  split_ifs
  · simp only [smul_sub, smul_comm c a⁻¹]
  · simp

/-- `‖J(𝐔)(b)‖ ≤ (27/2)√N η⁻³ω` when the plaquettes at `b` satisfy `‖𝐔(∂p) - 1‖ ≤ ω ≤ 1/48` and the
transports double the norm at most. -/
theorem norm_current_le [NeZero N] (hG : G.LieInput) (U : Config N n) (μ : Fin 4) (x : Site n)
    {ω : ℝ} (hω1 : ω ≤ 1 / 48)
    (hP : ∀ ν, ν ≠ μ → ∀ y ∈ ({x, x - unit n ν} : Finset (Site n)),
      ‖((plaq U ν μ y : GLN) : Mat) - 1‖ ≤ ω)
    (hV : ∀ ν, ν ≠ μ → ∀ Z : Mat, ‖Ad (U.val ⟨x, ν, false⟩) Z‖ ≤ 2 * ‖Z‖) :
    ‖current a hG U μ x‖ ≤ 27 / 2 * Real.sqrt N * ‖a‖⁻¹ ^ 3 * ω := by
  have hc : ∀ ν, ν ≠ μ → ∀ y ∈ ({x, x - unit n ν} : Finset (Site n)),
      ‖curv a hG U ν μ y‖ ≤ ‖a‖⁻¹ ^ 2 * (Real.sqrt N * (3 / 2 * ω)) := by
    intro ν hν y hy
    simp only [curv]
    rw [norm_smul, norm_inv, norm_pow, ← inv_pow]
    exact mul_le_mul_of_nonneg_left ((opNorm_proj_le hG _).trans
      (mul_le_mul_of_nonneg_left (norm_imW_le _ (hP ν hν y hy) hω1) (Real.sqrt_nonneg _)))
      (by positivity)
  have hterm : ∀ ν, ν ≠ μ →
      ‖Dbw a U ν (curv a hG U ν μ) x‖ ≤ 9 / 2 * Real.sqrt N * ‖a‖⁻¹ ^ 3 * ω := by
    intro ν hν
    refine (norm_dbw_le a U ν x _ (hV ν hν)).trans ?_
    have h1 := hc ν hν (x - unit n ν) (by simp)
    have h2 := hc ν hν x (by simp)
    calc ‖a‖⁻¹ * (2 * ‖curv a hG U ν μ (x - unit n ν)‖ + ‖curv a hG U ν μ x‖)
        ≤ ‖a‖⁻¹ * (2 * (‖a‖⁻¹ ^ 2 * (Real.sqrt N * (3 / 2 * ω))) +
            ‖a‖⁻¹ ^ 2 * (Real.sqrt N * (3 / 2 * ω))) := by gcongr
      _ = 9 / 2 * Real.sqrt N * ‖a‖⁻¹ ^ 3 * ω := by ring
  show ‖∑ ν, (if ν ≠ μ then Dbw a U ν (curv a hG U ν μ) x else 0)‖ ≤ _
  exact (norm_sum_ne_le hterm).trans (le_of_eq (by ring))

/-- `‖(D^*_𝐔D_𝐔A)(b)‖ ≤ 18η⁻¹m₁` when the first differences of `A` at `b` are at most `m₁`. -/
theorem norm_DsD_le (U : Config N n) (A : Form1 N n) (μ : Fin 4) (x : Site n) {m₁ : ℝ}
    (hV : ∀ ν, ν ≠ μ → ∀ Z : Mat, ‖Ad (U.val ⟨x, ν, false⟩) Z‖ ≤ 2 * ‖Z‖)
    (hDm : ∀ ν, ν ≠ μ → ∀ y ∈ ({x, x - unit n ν} : Finset (Site n)),
      ‖Dfw a U ν (A μ) y‖ ≤ m₁ ∧ ‖Dfw a U μ (A ν) y‖ ≤ m₁) :
    ‖Ds2 a U (D1 a U A) μ x‖ ≤ 18 * ‖a‖⁻¹ * m₁ := by
  have hd : ∀ ν, ν ≠ μ → ∀ y ∈ ({x, x - unit n ν} : Finset (Site n)),
      ‖D1 a U A ν μ y‖ ≤ 2 * m₁ := by
    intro ν hν y hy
    obtain ⟨h1, h2⟩ := hDm ν hν y hy
    simp only [D1]
    exact (norm_sub_le _ _).trans (by linarith)
  have hterm : ∀ ν, ν ≠ μ → ‖Dbw a U ν (D1 a U A ν μ) x‖ ≤ 6 * ‖a‖⁻¹ * m₁ := by
    intro ν hν
    refine (norm_dbw_le a U ν x _ (hV ν hν)).trans ?_
    have h1 := hd ν hν (x - unit n ν) (by simp)
    have h2 := hd ν hν x (by simp)
    calc ‖a‖⁻¹ * (2 * ‖D1 a U A ν μ (x - unit n ν)‖ + ‖D1 a U A ν μ x‖)
        ≤ ‖a‖⁻¹ * (2 * (2 * m₁) + 2 * m₁) := by gcongr
      _ = 6 * ‖a‖⁻¹ * m₁ := by ring
  show ‖∑ ν, (if ν ≠ μ then Dbw a U ν (D1 a U A ν μ) x else 0)‖ ≤ _
  exact (norm_sum_ne_le hterm).trans (le_of_eq (by ring))

/-- The bound of `g(z) = 𝒥(zA)(b) - J(𝐔)(b) - z(D^*DA)(b)` in the local quantities of
`lem:current-expansion`, with `R` the right side of `eq:current-remainder` at `zA`. -/
theorem norm_g_le [NeZero N] (hG : G.LieInput) (ha : a ≠ 0) (U : Config N n)
    (hU : ∀ μ x, U μ x ∈ G.complexified) (A : Form1 N n) (hA : ∀ μ x, A μ x ∈ G.lieC)
    (μ : Fin 4) (x : Site n) (z : ℂ) {m₀ m₁ ω : ℝ} (hm0 : 0 ≤ m₀) (hm1 : 0 ≤ m₁)
    (hω : ω ≤ 1 / (48 * Real.sqrt N)) (hηm : ‖a‖ * (‖z‖ * m₀) ≤ 1 / (48 * Real.sqrt N))
    (hP : ∀ ν, ν ≠ μ → ∀ y ∈ ({x, x - unit n ν} : Finset (Site n)),
      ‖((plaq U ν μ y : GLN) : Mat) - 1‖ ≤ ω)
    (hAm : ∀ ν, ν ≠ μ → ∀ y ∈ ({x, x - unit n ν} : Finset (Site n)),
      ‖A ν y‖ ≤ m₀ ∧ ‖A μ y‖ ≤ m₀ ∧ ‖A μ (y + unit n ν)‖ ≤ m₀ ∧ ‖A ν (y + unit n μ)‖ ≤ m₀)
    (hTr : ∀ ν, ν ≠ μ → ∀ y ∈ ({x, x - unit n ν} : Finset (Site n)), ∀ Z : Mat,
      ‖Ad (U ν y) Z‖ ≤ 2 * ‖Z‖ ∧ ‖Ad (U μ y) Z‖ ≤ 2 * ‖Z‖)
    (hV : ∀ ν, ν ≠ μ → ∀ Z : Mat, ‖Ad (U.val ⟨x, ν, false⟩) Z‖ ≤ 2 * ‖Z‖)
    (hDm : ∀ ν, ν ≠ μ → ∀ y ∈ ({x, x - unit n ν} : Finset (Site n)),
      ‖Dfw a U ν (A μ) y‖ ≤ m₁ ∧ ‖Dfw a U μ (A ν) y‖ ≤ m₁)
    (hDν : ∀ ν, ν ≠ μ → ‖Dfw a U ν (A ν) (x - unit n ν)‖ ≤ m₁) :
    ‖gradAction a hG U (z • A) μ x - current a hG U μ x - z • Ds2 a U (D1 a U A) μ x‖ ≤
      4 * (‖a‖ * (‖z‖ * m₀)) * (27 / 2 * Real.sqrt N * ‖a‖⁻¹ ^ 3 * ω + ‖z‖ * (18 * ‖a‖⁻¹ * m₁) +
        512 * N * ((‖z‖ * m₀ + ‖a‖ * (‖z‖ * m₁)) * (‖z‖ * m₁ + ‖a‖⁻¹ ^ 2 * ω) + (‖z‖ * m₀) ^ 3)) +
      512 * N * ((‖z‖ * m₀ + ‖a‖ * (‖z‖ * m₁)) * (‖z‖ * m₁ + ‖a‖⁻¹ ^ 2 * ω) + (‖z‖ * m₀) ^ 3) := by
  have hsqrt : 1 ≤ Real.sqrt N := by
    rw [Real.one_le_sqrt]; exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hc6 : 1 / (48 * Real.sqrt N) ≤ 1 / 48 :=
    one_div_le_one_div_of_le (by norm_num) (by linarith)
  set R := 512 * N * ((‖z‖ * m₀ + ‖a‖ * (‖z‖ * m₁)) * (‖z‖ * m₁ + ‖a‖⁻¹ ^ 2 * ω) + (‖z‖ * m₀) ^ 3)
  set J' := current a hG (expMul a (z • A) U) μ x
  have hzA : ∀ μ x, (z • A) μ x ∈ G.lieC := fun μ x =>
    (GaugeGroup.lieCSubmodule hG).smul_mem z (hA μ x)
  -- `eq:current-remainder` at `zA`
  have hF : ‖J' - current a hG U μ x - Ds2 a U (D1 a U (z • A)) μ x‖ ≤ R := by
    refine current_remainder a hG ha U hU (z • A) hzA μ x (m₀ := ‖z‖ * m₀) (m₁ := ‖z‖ * m₁)
      (h := ω) (by positivity) (by positivity) hω hηm ?_ ?_ hTr hV ?_ ?_
    · intro ν hν y hy
      exact (hs_le_opNorm (Nat.pos_of_ne_zero (NeZero.ne N)) _).trans (hP ν hν y hy)
    · intro ν hν y hy
      obtain ⟨h1, h2, h3, h4⟩ := hAm ν hν y hy
      simp only [Pi.smul_apply, norm_smul]
      exact ⟨by gcongr, by gcongr, by gcongr, by gcongr⟩
    · intro ν hν y hy
      obtain ⟨h1, h2⟩ := hDm ν hν y hy
      rw [Dfw_smul_form, Dfw_smul_form, norm_smul, norm_smul]
      exact ⟨by gcongr, by gcongr⟩
    · intro ν hν
      rw [Dfw_smul_form, norm_smul]
      exact mul_le_mul_of_nonneg_left (hDν ν hν) (norm_nonneg _)
  have hDD : Ds2 a U (D1 a U (z • A)) μ x = z • Ds2 a U (D1 a U A) μ x := by
    rw [D1_smul_form, Ds2_smul]; rfl
  rw [hDD] at hF
  -- the bounds of `J(𝐔)(b)`, `(D^*DA)(b)`, and `J(e^{iazA}𝐔)(b)`
  have hJ := norm_current_le a hG U μ x (hω.trans hc6) hP hV
  have hD := norm_DsD_le a U A μ x hV hDm
  have hJ' : ‖J'‖ ≤ 27 / 2 * Real.sqrt N * ‖a‖⁻¹ ^ 3 * ω + ‖z‖ * (18 * ‖a‖⁻¹ * m₁) + R := by
    have e : J' = current a hG U μ x + z • Ds2 a U (D1 a U A) μ x +
        (J' - current a hG U μ x - z • Ds2 a U (D1 a U A) μ x) := by abel
    rw [e]
    refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans ?_) hF)
    rw [norm_smul]
    exact add_le_add hJ (mul_le_mul_of_nonneg_left hD (norm_nonneg _))
  -- `E - 1`
  have hZ : ‖-((I * a) • (z • A) μ x)‖ ≤ ‖a‖ * (‖z‖ * m₀) := by
    obtain ⟨ν, hν⟩ : ∃ ν : Fin 4, ν ≠ μ := ⟨μ + 1, by simp⟩
    have h := (hAm ν hν x (by simp)).2.1
    simp only [Pi.smul_apply]
    rw [norm_neg, norm_smul, norm_mul, Complex.norm_I, one_mul, norm_smul]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h (norm_nonneg _)) (norm_nonneg _)
  have hZ2 : ‖-((I * a) • (z • A) μ x)‖ ≤ 1 / 2 := hZ.trans (hηm.trans (hc6.trans (by norm_num)))
  have hE : ‖Eop (-((I * a) • (z • A) μ x)) - 1‖ ≤ 4 * (‖a‖ * (‖z‖ * m₀)) :=
    (norm_Eop_sub_one_le hZ2).trans (by linarith)
  have e : gradAction a hG U (z • A) μ x - current a hG U μ x - z • Ds2 a U (D1 a U A) μ x =
      (Eop (-((I * a) • (z • A) μ x)) - 1) J' +
        (J' - current a hG U μ x - z • Ds2 a U (D1 a U A) μ x) := by
    simp only [gradAction, ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, J']
    abel
  rw [e]
  refine (norm_add_le _ _).trans (add_le_add ?_ hF)
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul hE hJ' (norm_nonneg _) (by positivity))

/-- The bound of `g` in the quantities of the scale `s = a_j` (the core's
`‖g(z)‖ ≤ C_g a^{-3}|z|m(|z|m + ε_𝐔)`, `C_g = 84√NL³ + 108L³ + 6C₈L⁴`). -/
theorem norm_g_scale [NeZero N] (hG : G.LieInput) (ha : a ≠ 0) (U : Config N n)
    (hU : ∀ μ x, U μ x ∈ G.complexified) (A : Form1 N n) (hA : ∀ μ x, A μ x ∈ G.lieC)
    (μ : Fin 4) (x : Site n) (z : ℂ) {s L m ε : ℝ} (hs : ‖a‖ ≤ s) (hL : 1 ≤ L) (hm : 0 ≤ m)
    (hε : 0 ≤ ε) (hLε : L ^ 2 * ε ≤ 1 / (48 * Real.sqrt N))
    (hzm : ‖z‖ * L * m ≤ 1 / (48 * Real.sqrt N))
    (hP : ∀ ν, ν ≠ μ → ∀ y ∈ ({x, x - unit n ν} : Finset (Site n)),
      ‖((plaq U ν μ y : GLN) : Mat) - 1‖ ≤ L ^ 2 * ε * (‖a‖ / s) ^ 2)
    (hAm : ∀ ν, ν ≠ μ → ∀ y ∈ ({x, x - unit n ν} : Finset (Site n)),
      ‖A ν y‖ ≤ L / s * m ∧ ‖A μ y‖ ≤ L / s * m ∧ ‖A μ (y + unit n ν)‖ ≤ L / s * m ∧
        ‖A ν (y + unit n μ)‖ ≤ L / s * m)
    (hTr : ∀ ν, ν ≠ μ → ∀ y ∈ ({x, x - unit n ν} : Finset (Site n)), ∀ Z : Mat,
      ‖Ad (U ν y) Z‖ ≤ 2 * ‖Z‖ ∧ ‖Ad (U μ y) Z‖ ≤ 2 * ‖Z‖)
    (hV : ∀ ν, ν ≠ μ → ∀ Z : Mat, ‖Ad (U.val ⟨x, ν, false⟩) Z‖ ≤ 2 * ‖Z‖)
    (hDm : ∀ ν, ν ≠ μ → ∀ y ∈ ({x, x - unit n ν} : Finset (Site n)),
      ‖Dfw a U ν (A μ) y‖ ≤ L ^ 2 / s ^ 2 * m ∧ ‖Dfw a U μ (A ν) y‖ ≤ L ^ 2 / s ^ 2 * m)
    (hDν : ∀ ν, ν ≠ μ → ‖Dfw a U ν (A ν) (x - unit n ν)‖ ≤ L ^ 2 / s ^ 2 * m) :
    ‖gradAction a hG U (z • A) μ x - current a hG U μ x - z • Ds2 a U (D1 a U A) μ x‖ ≤
      (84 * Real.sqrt N * L ^ 3 + 108 * L ^ 3 + 6 * (512 * N) * L ^ 4) * (s ^ 3)⁻¹ *
        (‖z‖ * m) * (‖z‖ * m + ε) := by
  have hη : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hs0 : 0 < s := hη.trans_le hs
  have hL0 : 0 ≤ L := by linarith
  have hsqrt : 1 ≤ Real.sqrt N := by
    rw [Real.one_le_sqrt]; exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hc6 : 1 / (48 * Real.sqrt N) ≤ 1 / 48 :=
    one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hu : ‖a‖ / s ≤ 1 := div_le_one_of_le₀ hs hs0.le
  have hu0 : 0 ≤ ‖a‖ / s := by positivity
  have ht0 : 0 ≤ ‖z‖ * m := by positivity
  have hLt : L * (‖z‖ * m) ≤ 1 / 48 := by
    have : L * (‖z‖ * m) = ‖z‖ * L * m := by ring
    linarith
  have ht1 : ‖z‖ * m ≤ 1 := by nlinarith
  have hg := norm_g_le a hG ha U hU A hA μ x z (m₀ := L / s * m) (m₁ := L ^ 2 / s ^ 2 * m)
    (ω := L ^ 2 * ε * (‖a‖ / s) ^ 2) (by positivity) (by positivity) ?_ ?_ hP hAm hTr hV hDm hDν
  rotate_left
  · exact (mul_le_of_le_one_right (by positivity) (pow_le_one₀ hu0 hu)).trans hLε
  · have e : ‖a‖ * (‖z‖ * (L / s * m)) = ‖a‖ / s * (‖z‖ * L * m) := by ring
    rw [e]
    exact (mul_le_of_le_one_left (by positivity) hu).trans hzm
  refine hg.trans ?_
  -- the four pieces in the quantities of the scale
  set K : ℝ := (s ^ 3)⁻¹ with hK
  have hK0 : 0 ≤ K := by positivity
  set t : ℝ := ‖z‖ * m with ht
  have e1 : ‖a‖ * (‖z‖ * (L / s * m)) = ‖a‖ / s * (L * t) := by rw [ht]; ring
  have e2 : 4 * (‖a‖ * (‖z‖ * (L / s * m))) *
      (27 / 2 * Real.sqrt N * ‖a‖⁻¹ ^ 3 * (L ^ 2 * ε * (‖a‖ / s) ^ 2)) =
      54 * Real.sqrt N * L ^ 3 * ε * t * K := by
    rw [hK, ht]; field_simp; ring
  have e3 : 4 * (‖a‖ * (‖z‖ * (L / s * m))) * (‖z‖ * (18 * ‖a‖⁻¹ * (L ^ 2 / s ^ 2 * m))) =
      72 * L ^ 3 * t ^ 2 * K := by
    rw [hK, ht]; field_simp; ring
  have e4 : 512 * N * ((‖z‖ * (L / s * m) + ‖a‖ * (‖z‖ * (L ^ 2 / s ^ 2 * m))) *
      (‖z‖ * (L ^ 2 / s ^ 2 * m) + ‖a‖⁻¹ ^ 2 * (L ^ 2 * ε * (‖a‖ / s) ^ 2)) +
      (‖z‖ * (L / s * m)) ^ 3) =
      512 * N * (L ^ 3 * t * (1 + ‖a‖ / s * L) * (t + ε) + L ^ 3 * t ^ 3) * K := by
    rw [hK, ht]; field_simp
  set R := 512 * N * ((‖z‖ * (L / s * m) + ‖a‖ * (‖z‖ * (L ^ 2 / s ^ 2 * m))) *
      (‖z‖ * (L ^ 2 / s ^ 2 * m) + ‖a‖⁻¹ ^ 2 * (L ^ 2 * ε * (‖a‖ / s) ^ 2)) +
      (‖z‖ * (L / s * m)) ^ 3) with hRdef
  have htt : 0 ≤ t * (t + ε) := by positivity
  have hR : R ≤ 3 * (512 * N) * L ^ 4 * (t * (t + ε)) * K := by
    rw [e4]
    have h1 : 1 + ‖a‖ / s * L ≤ 2 * L := by nlinarith
    have h2 : L ^ 3 * t * (1 + ‖a‖ / s * L) * (t + ε) ≤ 2 * L ^ 4 * (t * (t + ε)) := by
      have : L ^ 3 * t * (1 + ‖a‖ / s * L) * (t + ε) = L ^ 3 * (t * (t + ε)) * (1 + ‖a‖ / s * L) := by
        ring
      rw [this]
      calc L ^ 3 * (t * (t + ε)) * (1 + ‖a‖ / s * L) ≤ L ^ 3 * (t * (t + ε)) * (2 * L) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = 2 * L ^ 4 * (t * (t + ε)) := by ring
    have h3 : L ^ 3 * t ^ 3 ≤ L ^ 4 * (t * (t + ε)) := by
      have ha3 : t ^ 3 ≤ t * (t + ε) := by nlinarith
      have hL3 : L ^ 3 ≤ L ^ 4 := pow_le_pow_right₀ hL (by norm_num)
      exact mul_le_mul hL3 ha3 (by positivity) (by positivity)
    have hN : (0 : ℝ) ≤ 512 * N := by positivity
    calc 512 * N * (L ^ 3 * t * (1 + ‖a‖ / s * L) * (t + ε) + L ^ 3 * t ^ 3) * K
        ≤ 512 * N * (2 * L ^ 4 * (t * (t + ε)) + L ^ 4 * (t * (t + ε))) * K := by gcongr
      _ = 3 * (512 * N) * L ^ 4 * (t * (t + ε)) * K := by ring
  have hR0 : 0 ≤ R := by rw [hRdef]; positivity
  have hP4 : 4 * (‖a‖ * (‖z‖ * (L / s * m))) ≤ 1 := by
    rw [e1]
    have : ‖a‖ / s * (L * t) ≤ L * t := mul_le_of_le_one_left (by positivity) hu
    linarith
  calc 4 * (‖a‖ * (‖z‖ * (L / s * m))) * (27 / 2 * Real.sqrt N * ‖a‖⁻¹ ^ 3 *
        (L ^ 2 * ε * (‖a‖ / s) ^ 2) + ‖z‖ * (18 * ‖a‖⁻¹ * (L ^ 2 / s ^ 2 * m)) + R) + R
      = 4 * (‖a‖ * (‖z‖ * (L / s * m))) * (27 / 2 * Real.sqrt N * ‖a‖⁻¹ ^ 3 *
          (L ^ 2 * ε * (‖a‖ / s) ^ 2)) +
        4 * (‖a‖ * (‖z‖ * (L / s * m))) * (‖z‖ * (18 * ‖a‖⁻¹ * (L ^ 2 / s ^ 2 * m))) +
        4 * (‖a‖ * (‖z‖ * (L / s * m))) * R + R := by ring
    _ ≤ 54 * Real.sqrt N * L ^ 3 * ε * t * K + 72 * L ^ 3 * t ^ 2 * K + 1 * R + R := by
        rw [e2, e3]
        exact add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_right hP4 hR0)) le_rfl
    _ ≤ 54 * Real.sqrt N * L ^ 3 * ε * t * K + 72 * L ^ 3 * t ^ 2 * K +
        2 * (3 * (512 * N) * L ^ 4 * (t * (t + ε)) * K) := by linarith
    _ ≤ (84 * Real.sqrt N * L ^ 3 + 108 * L ^ 3 + 6 * (512 * N) * L ^ 4) * K * t * (t + ε) := by
        have hd : (84 * Real.sqrt N * L ^ 3 + 108 * L ^ 3 + 6 * (512 * N) * L ^ 4) * K * t * (t + ε) -
            (54 * Real.sqrt N * L ^ 3 * ε * t * K + 72 * L ^ 3 * t ^ 2 * K +
              2 * (3 * (512 * N) * L ^ 4 * (t * (t + ε)) * K)) =
            Real.sqrt N * L ^ 3 * K * (84 * t ^ 2 + 30 * (ε * t)) +
              L ^ 3 * K * (36 * t ^ 2 + 108 * (ε * t)) := by ring
        have hp : 0 ≤ Real.sqrt N * L ^ 3 * K * (84 * t ^ 2 + 30 * (ε * t)) +
            L ^ 3 * K * (36 * t ^ 2 + 108 * (ε * t)) := by
          have hεt : 0 ≤ ε * t := mul_nonneg hε ht0
          have hL3 : 0 ≤ L ^ 3 := pow_nonneg hL0 3
          positivity
        linarith

/-- If `X ≤ Kδ²` for all `δ ∈ (0, d]`, then `X ≤ 0`. -/
lemma nonpos_of_forall_sq {X K d : ℝ} (hK : 0 ≤ K) (hd : 0 < d)
    (h : ∀ δ, 0 < δ → δ ≤ d → X ≤ K * δ ^ 2) : X ≤ 0 := by
  by_contra hX
  push_neg at hX
  set δ := min (min d 1) (X / (K + 1))
  have hδ0 : 0 < δ := lt_min (lt_min hd one_pos) (div_pos hX (by linarith))
  have hδ1 : δ ≤ 1 := (min_le_left _ _).trans (min_le_right _ _)
  have hδd : δ ≤ d := (min_le_left _ _).trans (min_le_left _ _)
  have hδX : δ ≤ X / (K + 1) := min_le_right _ _
  have h1 := h δ hδ0 hδd
  have h2 : K * δ ^ 2 ≤ K * δ := mul_le_mul_of_nonneg_left (by nlinarith) hK
  have h3 : K * δ ≤ K * (X / (K + 1)) := mul_le_mul_of_nonneg_left hδX hK
  have h4 : K * (X / (K + 1)) < X := by
    rw [mul_div_assoc', div_lt_iff₀ (by linarith)]
    nlinarith
  linarith

/-- `lem:cubic-gradient` at one bond `b = (μ, x)` whose first end lies in the layer of the scale
`s = a_j`: with `m = ‖A‖_{∞,*}`, the local bounds which the weighted norms give on the bonds and
plaquettes of `st(b)`, and `m ≤ c₆/(2L)`, `‖𝖭₀(A)(b)‖ ≤ C₀s⁻³m²`, `C₀ = 4(84√NL³ + 108L³ + 6C₈L⁴)`. -/
theorem cubic_gradient_bond [NeZero N] (hG : G.LieInput) (ha : a ≠ 0) (U : Config N n)
    (hU : ∀ μ x, U μ x ∈ G.complexified) (A : Form1 N n) (hA : ∀ μ x, A μ x ∈ G.lieC)
    (μ : Fin 4) (x : Site n) {s L m ε : ℝ} (hs : ‖a‖ ≤ s) (hL : 1 ≤ L) (hm : 0 ≤ m)
    (hε : 0 ≤ ε) (hLε : L ^ 2 * ε ≤ 1 / (48 * Real.sqrt N))
    (hmr : m ≤ 1 / (48 * Real.sqrt N) / (2 * L))
    (hP : ∀ ν, ν ≠ μ → ∀ y ∈ ({x, x - unit n ν} : Finset (Site n)),
      ‖((plaq U ν μ y : GLN) : Mat) - 1‖ ≤ L ^ 2 * ε * (‖a‖ / s) ^ 2)
    (hAm : ∀ ν, ν ≠ μ → ∀ y ∈ ({x, x - unit n ν} : Finset (Site n)),
      ‖A ν y‖ ≤ L / s * m ∧ ‖A μ y‖ ≤ L / s * m ∧ ‖A μ (y + unit n ν)‖ ≤ L / s * m ∧
        ‖A ν (y + unit n μ)‖ ≤ L / s * m)
    (hTr : ∀ ν, ν ≠ μ → ∀ y ∈ ({x, x - unit n ν} : Finset (Site n)), ∀ Z : Mat,
      ‖Ad (U ν y) Z‖ ≤ 2 * ‖Z‖ ∧ ‖Ad (U μ y) Z‖ ≤ 2 * ‖Z‖)
    (hV : ∀ ν, ν ≠ μ → ∀ Z : Mat, ‖Ad (U.val ⟨x, ν, false⟩) Z‖ ≤ 2 * ‖Z‖)
    (hDm : ∀ ν, ν ≠ μ → ∀ y ∈ ({x, x - unit n ν} : Finset (Site n)),
      ‖Dfw a U ν (A μ) y‖ ≤ L ^ 2 / s ^ 2 * m ∧ ‖Dfw a U μ (A ν) y‖ ≤ L ^ 2 / s ^ 2 * m)
    (hDν : ∀ ν, ν ≠ μ → ‖Dfw a U ν (A ν) (x - unit n ν)‖ ≤ L ^ 2 / s ^ 2 * m) :
    ‖N0 a hG U A μ x‖ ≤
      4 * (84 * Real.sqrt N * L ^ 3 + 108 * L ^ 3 + 6 * (512 * N) * L ^ 4) * (s ^ 3)⁻¹ * m ^ 2 := by
  have hη : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hs0 : 0 < s := hη.trans_le hs
  have hL0 : 0 < L := by linarith
  have hsqrt : 1 ≤ Real.sqrt N := by
    rw [Real.one_le_sqrt]; exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  set c₆ : ℝ := 1 / (48 * Real.sqrt N) with hc₆
  have hc0 : 0 < c₆ := by positivity
  set Cg : ℝ := 84 * Real.sqrt N * L ^ 3 + 108 * L ^ 3 + 6 * (512 * N) * L ^ 4 with hCg
  have hCg0 : 0 ≤ Cg := by positivity
  -- the case `m > 0`: Cauchy's estimate on the circle `|z| = r₀/m`, `r₀ = c₆/L`
  have pos : ∀ m' : ℝ, 0 < m' → m ≤ m' → m' ≤ c₆ / (2 * L) →
      ‖N0 a hG U A μ x‖ ≤ 4 * Cg * (s ^ 3)⁻¹ * m' ^ 2 := by
    intro m' hm' hmm' hm'r
    set r₀ : ℝ := c₆ / L with hr₀
    have hr0 : 0 < r₀ := by positivity
    have hρ : 2 ≤ r₀ / m' := by
      rw [le_div_iff₀ hm']
      have : c₆ / (2 * L) = r₀ / 2 := by rw [hr₀]; field_simp
      linarith
    have hεr : ε ≤ r₀ := by
      rw [hr₀, le_div_iff₀ hL0]
      have : ε * L ≤ ε * L ^ 2 := mul_le_mul_of_nonneg_left (by nlinarith) hε
      linarith
    have hm'' : ∀ c : ℝ, 0 ≤ c → c * m ≤ c * m' := fun c hc => mul_le_mul_of_nonneg_left hmm' hc
    have hLs : 0 ≤ L / s := by positivity
    have hLs2 : 0 ≤ L ^ 2 / s ^ 2 := by positivity
    have hfin : 2 * (2 * Cg * (s ^ 3)⁻¹ * r₀ ^ 2) / (r₀ / m') ^ 2 = 4 * Cg * (s ^ 3)⁻¹ * m' ^ 2 := by
      field_simp; ring
    refine (norm_N0_le a hG ha hU hA μ x (hessOp' a hG U A μ x) hρ (M := 2 * Cg * (s ^ 3)⁻¹ * r₀ ^ 2)
      fun z hz => ?_).trans hfin.le
    have hzm' : ‖z‖ * m' = r₀ := by rw [hz]; field_simp
    have hzL : ‖z‖ * L * m' ≤ c₆ := by
      have : ‖z‖ * L * m' = L * r₀ := by rw [← hzm']; ring
      rw [this, hr₀]; field_simp; rfl
    have hgz := norm_g_scale a hG ha U hU A hA μ x z (m := m') hs hL hm'.le hε hLε hzL hP
      (fun ν hν y hy => by
        obtain ⟨h1, h2, h3, h4⟩ := hAm ν hν y hy
        exact ⟨h1.trans (hm'' _ hLs), h2.trans (hm'' _ hLs), h3.trans (hm'' _ hLs),
          h4.trans (hm'' _ hLs)⟩)
      hTr hV
      (fun ν hν y hy => by
        obtain ⟨h1, h2⟩ := hDm ν hν y hy
        exact ⟨h1.trans (hm'' _ hLs2), h2.trans (hm'' _ hLs2)⟩)
      (fun ν hν => (hDν ν hν).trans (hm'' _ hLs2))
    have e : N0 a hG U (z • A) μ x + z • hessOp' a hG U A μ x =
        gradAction a hG U (z • A) μ x - current a hG U μ x - z • Ds2 a U (D1 a U A) μ x := by
      have hsm : hessOp a hG U (z • A) = z • hessOp a hG U A := (hessLin a hG ha U).map_smul z A
      simp only [N0, Pi.sub_apply]
      rw [hsm]
      simp only [hessOp, Pi.smul_apply, Pi.add_apply, smul_add]
      abel
    rw [e]
    refine hgz.trans ?_
    rw [hzm']
    have hK0 : 0 ≤ (s ^ 3)⁻¹ := by positivity
    calc Cg * (s ^ 3)⁻¹ * r₀ * (r₀ + ε) ≤ Cg * (s ^ 3)⁻¹ * r₀ * (r₀ + r₀) := by gcongr
      _ = 2 * Cg * (s ^ 3)⁻¹ * r₀ ^ 2 := by ring
  rcases hm.lt_or_eq with hm0 | hm0
  · refine (pos m hm0 le_rfl hmr).trans (le_of_eq ?_)
    rfl
  · -- `m = 0`: the bound holds for every `m' ∈ (0, c₆/(2L)]`
    subst hm0
    have hX := nonpos_of_forall_sq (X := ‖N0 a hG U A μ x‖) (K := 4 * Cg * (s ^ 3)⁻¹)
      (d := c₆ / (2 * L)) (by positivity) (by positivity)
      fun δ hδ hδd => pos δ hδ hδ.le hδd
    simpa using hX

end CoreLean
