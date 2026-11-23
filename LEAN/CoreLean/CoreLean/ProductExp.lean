/-
`lem:product` of BALABAN_CORE.tex, the parts which do not involve the logarithm: the bounds
`eq:adjoint-lipschitz` on `Ad_{e^{iX}}` and the expansion `eq:four-exponentials` of a product of four
exponentials.

The exponential bounds `‖e^x - 1‖ ≤ e^‖x‖ - 1` and the series of `e^t` are those of the library
`BakerCampbellHausdorff` (statements rechecked: `norm_exp_sub_one_le`, `hasSum_real_exp`,
`norm_expSeries_term_le`, `exp_mul_exp_neg`). The core multiplies out the four exponential series
term by term; since matrices do not commute, we instead multiply one factor at a time, keeping
track of the parts of degree `1`, of degree `2`, and of degree `≥ 3` with the majorants
`s`, `s²/2` and `e^s - 1 - s - s²/2` (`mul_trunc`). The majorants are those of the core's proof.
-/
import CoreLean.Hadamard
import CoreLean.OpNorm
import CoreLean.Projection
import BakerCampbellHausdorff.ExpBounds

open NormedSpace
open scoped Nat

noncomputable section

namespace CoreLean

section Algebra

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸] [CompleteSpace 𝔸]

/-- `φ(s) = e^s - 1 - s - s²/2`, the majorant of the part of degree `≥ 3`. -/
def phi3 (s : ℝ) : ℝ := Real.exp s - 1 - s - s ^ 2 / 2

/-- The tail of the exponential series after the quadratic term. -/
theorem norm_exp_sub_quad_le (x : 𝔸) :
    ‖exp x - 1 - x - (2 : ℂ)⁻¹ • x ^ 2‖ ≤ phi3 ‖x‖ := by
  have h1 := (hasSum_nat_add_iff' 3).mpr (exp_series_hasSum_exp' (𝕂 := ℂ) x)
  have h2 := (hasSum_nat_add_iff' 3).mpr (BakerCampbellHausdorff.hasSum_real_exp ‖x‖)
  have e1 : ∑ i ∈ Finset.range 3, ((i ! : ℂ)⁻¹ • x ^ i) = 1 + x + (2 : ℂ)⁻¹ • x ^ 2 := by
    simp [Finset.sum_range_succ, Nat.factorial]
  have e2 : ∑ i ∈ Finset.range 3, (i !⁻¹ : ℝ) • ‖x‖ ^ i = 1 + ‖x‖ + ‖x‖ ^ 2 / 2 := by
    simp [Finset.sum_range_succ, Nat.factorial]; ring
  rw [e1] at h1
  rw [e2] at h2
  have := h1.norm_le_of_bounded h2 fun n =>
    BakerCampbellHausdorff.norm_expSeries_term_le ℂ x (by omega)
  rw [show exp x - 1 - x - (2 : ℂ)⁻¹ • x ^ 2 = exp x - (1 + x + (2 : ℂ)⁻¹ • x ^ 2) by abel]
  refine this.trans (le_of_eq ?_)
  unfold phi3; ring

/-- The difference of `n`-th powers: `‖aⁿ - bⁿ‖ ≤ n ρⁿ⁻¹ ‖a - b‖` for `‖a‖, ‖b‖ ≤ ρ`. -/
theorem norm_pow_sub_pow_le (h1 : ‖(1 : 𝔸)‖ ≤ 1) {a b : 𝔸} {ρ : ℝ} (ha : ‖a‖ ≤ ρ) (hb : ‖b‖ ≤ ρ)
    (n : ℕ) : ‖a ^ n - b ^ n‖ ≤ n * ρ ^ (n - 1) * ‖a - b‖ := by
  have hρ : 0 ≤ ρ := (norm_nonneg _).trans ha
  have hbn : ∀ m : ℕ, ‖b ^ m‖ ≤ ρ ^ m := fun m => by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simpa using h1
    · exact (norm_pow_le' b hm).trans (pow_le_pow_left₀ (norm_nonneg _) hb m)
  induction n with
  | zero => simp
  | succ n ih =>
    have e : a ^ (n + 1) - b ^ (n + 1) = a * (a ^ n - b ^ n) + (a - b) * b ^ n := by
      rw [pow_succ', pow_succ']; noncomm_ring
    rw [e]
    calc ‖a * (a ^ n - b ^ n) + (a - b) * b ^ n‖
        ≤ ‖a‖ * ‖a ^ n - b ^ n‖ + ‖a - b‖ * ‖b ^ n‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
      _ ≤ ρ * (n * ρ ^ (n - 1) * ‖a - b‖) + ‖a - b‖ * ρ ^ n := by
          gcongr
          · exact hbn n
      _ = (n + 1 : ℕ) * ρ ^ (n + 1 - 1) * ‖a - b‖ := by
          rcases Nat.eq_zero_or_pos n with rfl | hn
          · simp
          · have : ρ * ρ ^ (n - 1) = ρ ^ n := by
              rw [← pow_succ', Nat.sub_add_cancel hn]
            push_cast
            rw [show ρ * (↑n * ρ ^ (n - 1) * ‖a - b‖) = ↑n * (ρ * ρ ^ (n - 1)) * ‖a - b‖ by ring,
              this]
            ring

/-- `‖e^a - e^b‖ ≤ e^ρ ‖a - b‖` for `‖a‖, ‖b‖ ≤ ρ`. -/
theorem norm_exp_sub_exp_le (h1 : ‖(1 : 𝔸)‖ ≤ 1) {a b : 𝔸} {ρ : ℝ} (ha : ‖a‖ ≤ ρ)
    (hb : ‖b‖ ≤ ρ) : ‖exp a - exp b‖ ≤ Real.exp ρ * ‖a - b‖ := by
  have hA := (exp_series_hasSum_exp' (𝕂 := ℂ) a).sub (exp_series_hasSum_exp' (𝕂 := ℂ) b)
  -- the majorant series `Σ n ρⁿ⁻¹ / n! ‖a - b‖ = e^ρ ‖a - b‖`
  have hB : HasSum (fun n : ℕ => (n !⁻¹ : ℝ) * (n * ρ ^ (n - 1) * ‖a - b‖))
      (Real.exp ρ * ‖a - b‖) := by
    refine (hasSum_nat_add_iff' 1).mp ?_
    simp only [Finset.range_one, Finset.sum_singleton, Nat.factorial_zero, Nat.cast_zero,
      zero_mul, mul_zero, sub_zero]
    have := ((BakerCampbellHausdorff.hasSum_real_exp ρ).mul_right ‖a - b‖)
    refine this.congr_fun fun n => ?_
    simp only [smul_eq_mul, Nat.add_sub_cancel]
    rw [Nat.factorial_succ]
    push_cast
    field_simp
  refine hA.norm_le_of_bounded hB fun n => ?_
  rw [← smul_sub, norm_smul, norm_inv, RCLike.norm_natCast]
  exact mul_le_mul_of_nonneg_left (norm_pow_sub_pow_le h1 ha hb n) (by positivity)

/-- The product of two elements written as `1 +` (degree `1`) `+` (degree `2`) `+` (degree `≥ 3`):
the product has the same form, with the majorants of `s + a`. -/
theorem mul_trunc {A1 A2 A3 B1 B2 B3 : 𝔸} {s a : ℝ} (hs : 0 ≤ s) (ha : 0 ≤ a)
    (hA1 : ‖A1‖ ≤ s) (hA2 : ‖A2‖ ≤ s ^ 2 / 2) (hA3 : ‖A3‖ ≤ phi3 s)
    (hB1 : ‖B1‖ ≤ a) (hB2 : ‖B2‖ ≤ a ^ 2 / 2) (hB3 : ‖B3‖ ≤ phi3 a) :
    ‖(1 + A1 + A2 + A3) * (1 + B1 + B2 + B3) - (1 + (A1 + B1) + (A2 + B2 + A1 * B1))‖ ≤
      phi3 (s + a) := by
  have hφs : 0 ≤ phi3 s := (norm_nonneg _).trans hA3
  have hφa : 0 ≤ phi3 a := (norm_nonneg _).trans hB3
  have e : (1 + A1 + A2 + A3) * (1 + B1 + B2 + B3) - (1 + (A1 + B1) + (A2 + B2 + A1 * B1)) =
      A3 + B3 + A1 * B2 + A1 * B3 + A2 * B1 + A2 * B2 + A2 * B3 + A3 * B1 + A3 * B2 + A3 * B3 := by
    noncomm_ring
  rw [e]
  have m : ∀ (x y : 𝔸) (p q : ℝ), ‖x‖ ≤ p → ‖y‖ ≤ q → ‖x * y‖ ≤ p * q := fun x y p q hx hy =>
    (norm_mul_le _ _).trans (mul_le_mul hx hy (norm_nonneg _) ((norm_nonneg _).trans hx))
  have hsum : ‖A3 + B3 + A1 * B2 + A1 * B3 + A2 * B1 + A2 * B2 + A2 * B3 + A3 * B1 + A3 * B2 +
      A3 * B3‖ ≤ phi3 s + phi3 a + s * (a ^ 2 / 2) + s * phi3 a + s ^ 2 / 2 * a +
        s ^ 2 / 2 * (a ^ 2 / 2) + s ^ 2 / 2 * phi3 a + phi3 s * a + phi3 s * (a ^ 2 / 2) +
        phi3 s * phi3 a := by
    refine (norm_add_le _ _).trans (add_le_add ?_ (m _ _ _ _ hA3 hB3))
    refine (norm_add_le _ _).trans (add_le_add ?_ (m _ _ _ _ hA3 hB2))
    refine (norm_add_le _ _).trans (add_le_add ?_ (m _ _ _ _ hA3 hB1))
    refine (norm_add_le _ _).trans (add_le_add ?_ (m _ _ _ _ hA2 hB3))
    refine (norm_add_le _ _).trans (add_le_add ?_ (m _ _ _ _ hA2 hB2))
    refine (norm_add_le _ _).trans (add_le_add ?_ (m _ _ _ _ hA2 hB1))
    refine (norm_add_le _ _).trans (add_le_add ?_ (m _ _ _ _ hA1 hB3))
    refine (norm_add_le _ _).trans (add_le_add ?_ (m _ _ _ _ hA1 hB2))
    exact (norm_add_le _ _).trans (add_le_add hA3 hB3)
  refine hsum.trans (le_of_eq ?_)
  unfold phi3
  rw [Real.exp_add]
  ring

end Algebra

/-! ### Matrices -/

variable {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "GLN" => (Matrix (Fin N) (Fin N) ℂ)ˣ

open scoped Matrix.Norms.L2Operator

lemma norm_one_mat_le : ‖(1 : Mat)‖ ≤ 1 := by
  rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg zero_le_one).2 fun _ => by simp

lemma expU_inv_val (Y : Mat) : (((expU Y)⁻¹ : GLN) : Mat) = exp (-Y) :=
  Units.inv_eq_of_mul_eq_one_right (by
    rw [expU_val]; exact BakerCampbellHausdorff.exp_mul_exp_neg ℂ Y)

lemma Ad_expU (Y Z : Mat) : Ad (expU Y) Z = exp Y * Z * exp (-Y) := by
  rw [Ad, expU_val, expU_inv_val]

/-- `e^t - 1 ≤ 2t` for `0 ≤ t ≤ 1`. -/
lemma exp_sub_one_le_two_mul' {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : Real.exp t - 1 ≤ 2 * t := by
  have := Real.exp_bound (x := t) (by rw [abs_of_nonneg h0]; exact h1) (n := 1) one_pos
  simp only [Finset.range_one, Finset.sum_singleton, pow_zero, Nat.factorial_zero,
    Nat.cast_one, div_one, pow_one, Nat.succ_eq_add_one, zero_add, mul_one] at this
  rw [abs_of_nonneg h0] at this
  have h := (abs_le.1 this).2
  norm_num at h
  linarith

lemma norm_I_smul (X : Mat) : ‖Complex.I • X‖ = ‖X‖ := by
  rw [norm_smul, Complex.norm_I, one_mul]

/-- `‖e^{±iX} - 1‖ ≤ 2‖X‖` and `‖e^{±iX}‖ ≤ 2` for `‖X‖ ≤ 1/32`. -/
lemma norm_exp_I_bounds {X : Mat} (hX : ‖X‖ ≤ 1 / 32) (σ : ℂ) (hσ : ‖σ‖ = 1) :
    ‖exp (σ • X) - 1‖ ≤ 2 * ‖X‖ ∧ ‖exp (σ • X)‖ ≤ 2 := by
  have hn : ‖σ • X‖ = ‖X‖ := by rw [norm_smul, hσ, one_mul]
  have h1 := BakerCampbellHausdorff.norm_exp_sub_one_le ℂ (σ • X)
  rw [hn] at h1
  have h2 := exp_sub_one_le_two_mul' (norm_nonneg X) (by linarith)
  refine ⟨h1.trans h2, ?_⟩
  calc ‖exp (σ • X)‖ = ‖(exp (σ • X) - 1) + 1‖ := by rw [sub_add_cancel]
    _ ≤ 2 * ‖X‖ + 1 := (norm_add_le _ _).trans (add_le_add (h1.trans h2) norm_one_mat_le)
    _ ≤ 2 := by linarith

/-- `eq:adjoint-lipschitz`, first bound: `‖Ad_{e^{iX}} Z - Z‖ ≤ 6‖X‖‖Z‖` for `‖X‖ ≤ 1/32`. -/
theorem norm_Ad_exp_sub_le {X : Mat} (hX : ‖X‖ ≤ 1 / 32) (Z : Mat) :
    ‖Ad (expU (Complex.I • X)) Z - Z‖ ≤ 6 * ‖X‖ * ‖Z‖ := by
  obtain ⟨hp1, _⟩ := norm_exp_I_bounds hX Complex.I (by simp)
  obtain ⟨hm1, hm2⟩ := norm_exp_I_bounds hX (-Complex.I) (by simp)
  rw [Ad_expU, ← neg_smul]
  have e : exp (Complex.I • X) * Z * exp (-Complex.I • X) - Z =
      (exp (Complex.I • X) - 1) * Z * exp (-Complex.I • X) + Z * (exp (-Complex.I • X) - 1) := by
    noncomm_ring
  rw [e]
  calc _ ≤ ‖exp (Complex.I • X) - 1‖ * ‖Z‖ * ‖exp (-Complex.I • X)‖ +
        ‖Z‖ * ‖exp (-Complex.I • X) - 1‖ :=
        (norm_add_le _ _).trans (add_le_add
          ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)))
          (norm_mul_le _ _))
    _ ≤ 2 * ‖X‖ * ‖Z‖ * 2 + ‖Z‖ * (2 * ‖X‖) := by gcongr
    _ = 6 * ‖X‖ * ‖Z‖ := by ring

/-- `eq:adjoint-lipschitz`, second bound: `‖Ad_{e^{iX'}} Z - Ad_{e^{iX}} Z‖ ≤ 8‖X' - X‖‖Z‖`. -/
theorem norm_Ad_exp_sub_Ad_exp_le {X X' : Mat} (hX : ‖X‖ ≤ 1 / 32) (hX' : ‖X'‖ ≤ 1 / 32)
    (Z : Mat) :
    ‖Ad (expU (Complex.I • X')) Z - Ad (expU (Complex.I • X)) Z‖ ≤ 8 * ‖X' - X‖ * ‖Z‖ := by
  obtain ⟨_, hp2⟩ := norm_exp_I_bounds hX Complex.I (by simp)
  obtain ⟨_, hm2'⟩ := norm_exp_I_bounds hX' (-Complex.I) (by simp)
  -- `‖e^{σX'} - e^{σX}‖ ≤ e^{1/32}‖X' - X‖ ≤ 2‖X' - X‖`
  have hdiff : ∀ σ : ℂ, ‖σ‖ = 1 → ‖exp (σ • X') - exp (σ • X)‖ ≤ 2 * ‖X' - X‖ := fun σ hσ => by
    have hX'σ : ‖σ • X'‖ ≤ 1 / 32 := by rw [norm_smul, hσ, one_mul]; exact hX'
    have hXσ : ‖σ • X‖ ≤ 1 / 32 := by rw [norm_smul, hσ, one_mul]; exact hX
    have h := norm_exp_sub_exp_le norm_one_mat_le hX'σ hXσ
    rw [← smul_sub, norm_smul, hσ, one_mul] at h
    have he : Real.exp (1 / 32) ≤ 2 := by
      have := exp_sub_one_le_two_mul' (t := 1 / 32) (by norm_num) (by norm_num); linarith
    exact h.trans (mul_le_mul_of_nonneg_right he (norm_nonneg _))
  rw [Ad_expU, Ad_expU, ← neg_smul, ← neg_smul]
  have e : exp (Complex.I • X') * Z * exp (-Complex.I • X') -
      exp (Complex.I • X) * Z * exp (-Complex.I • X) =
      (exp (Complex.I • X') - exp (Complex.I • X)) * Z * exp (-Complex.I • X') +
        exp (Complex.I • X) * Z * (exp (-Complex.I • X') - exp (-Complex.I • X)) := by
    noncomm_ring
  rw [e]
  have h1 := hdiff Complex.I (by simp)
  have h2 := hdiff (-Complex.I) (by simp)
  calc _ ≤ ‖exp (Complex.I • X') - exp (Complex.I • X)‖ * ‖Z‖ * ‖exp (-Complex.I • X')‖ +
        ‖exp (Complex.I • X)‖ * ‖Z‖ * ‖exp (-Complex.I • X') - exp (-Complex.I • X)‖ :=
        (norm_add_le _ _).trans (add_le_add
          ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)))
          ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))))
    _ ≤ 2 * ‖X' - X‖ * ‖Z‖ * 2 + 2 * ‖Z‖ * (2 * ‖X' - X‖) := by gcongr
    _ = 8 * ‖X' - X‖ * ‖Z‖ := by ring

/-- The triangle inequality for the Hilbert–Schmidt norm, from `‖flat X‖ = √N |X|`. -/
lemma hs_add_le (X Y : Mat) : hs (X + Y) ≤ hs X + hs Y := by
  rcases Nat.eq_zero_or_pos N with h0 | h0
  · subst h0
    have : ∀ Z : Matrix (Fin 0) (Fin 0) ℂ, hs Z = 0 := fun Z => by
      simp [hs, hs2, ntr, Matrix.trace]
    rw [this, this, this, add_zero]
  · have hN : 0 < Real.sqrt N := Real.sqrt_pos.2 (by exact_mod_cast h0)
    have h := norm_add_le (flat X) (flat Y)
    rw [← map_add, norm_flat, norm_flat, norm_flat, ← mul_add] at h
    exact le_of_mul_le_mul_left h hN

lemma hs_mul_mul_le (A Z B : Mat) : hs (A * Z * B) ≤ ‖A‖ * hs Z * ‖B‖ :=
  (hs_mul_le_hs_mul_opNorm _ _).trans
    (mul_le_mul_of_nonneg_right (hs_mul_le_opNorm_mul_hs _ _) (norm_nonneg _))

/-- `eq:adjoint-lipschitz` with the Hilbert–Schmidt norms of `Z` and of the left side. -/
theorem hs_Ad_exp_sub_le {X : Mat} (hX : ‖X‖ ≤ 1 / 32) (Z : Mat) :
    hs (Ad (expU (Complex.I • X)) Z - Z) ≤ 6 * ‖X‖ * hs Z := by
  obtain ⟨hp1, _⟩ := norm_exp_I_bounds hX Complex.I (by simp)
  obtain ⟨hm1, hm2⟩ := norm_exp_I_bounds hX (-Complex.I) (by simp)
  rw [Ad_expU, ← neg_smul]
  have e : exp (Complex.I • X) * Z * exp (-Complex.I • X) - Z =
      (exp (Complex.I • X) - 1) * Z * exp (-Complex.I • X) + 1 * Z * (exp (-Complex.I • X) - 1) := by
    noncomm_ring
  rw [e]
  have hZ := hs_nonneg Z
  calc _ ≤ ‖exp (Complex.I • X) - 1‖ * hs Z * ‖exp (-Complex.I • X)‖ +
        ‖(1 : Mat)‖ * hs Z * ‖exp (-Complex.I • X) - 1‖ :=
        (hs_add_le _ _).trans (add_le_add (hs_mul_mul_le _ _ _) (hs_mul_mul_le _ _ _))
    _ ≤ 2 * ‖X‖ * hs Z * 2 + 1 * hs Z * (2 * ‖X‖) := by
        gcongr
        exact norm_one_mat_le
    _ = 6 * ‖X‖ * hs Z := by ring

theorem hs_Ad_exp_sub_Ad_exp_le {X X' : Mat} (hX : ‖X‖ ≤ 1 / 32) (hX' : ‖X'‖ ≤ 1 / 32)
    (Z : Mat) :
    hs (Ad (expU (Complex.I • X')) Z - Ad (expU (Complex.I • X)) Z) ≤ 8 * ‖X' - X‖ * hs Z := by
  obtain ⟨_, hp2⟩ := norm_exp_I_bounds hX Complex.I (by simp)
  obtain ⟨_, hm2'⟩ := norm_exp_I_bounds hX' (-Complex.I) (by simp)
  have hdiff : ∀ σ : ℂ, ‖σ‖ = 1 → ‖exp (σ • X') - exp (σ • X)‖ ≤ 2 * ‖X' - X‖ := fun σ hσ => by
    have hX'σ : ‖σ • X'‖ ≤ 1 / 32 := by rw [norm_smul, hσ, one_mul]; exact hX'
    have hXσ : ‖σ • X‖ ≤ 1 / 32 := by rw [norm_smul, hσ, one_mul]; exact hX
    have h := norm_exp_sub_exp_le norm_one_mat_le hX'σ hXσ
    rw [← smul_sub, norm_smul, hσ, one_mul] at h
    have he : Real.exp (1 / 32) ≤ 2 := by
      have := exp_sub_one_le_two_mul' (t := 1 / 32) (by norm_num) (by norm_num); linarith
    exact h.trans (mul_le_mul_of_nonneg_right he (norm_nonneg _))
  rw [Ad_expU, Ad_expU, ← neg_smul, ← neg_smul]
  have e : exp (Complex.I • X') * Z * exp (-Complex.I • X') -
      exp (Complex.I • X) * Z * exp (-Complex.I • X) =
      (exp (Complex.I • X') - exp (Complex.I • X)) * Z * exp (-Complex.I • X') +
        exp (Complex.I • X) * Z * (exp (-Complex.I • X') - exp (-Complex.I • X)) := by
    noncomm_ring
  rw [e]
  have h1 := hdiff Complex.I (by simp)
  have h2 := hdiff (-Complex.I) (by simp)
  have hZ := hs_nonneg Z
  calc _ ≤ ‖exp (Complex.I • X') - exp (Complex.I • X)‖ * hs Z * ‖exp (-Complex.I • X')‖ +
        ‖exp (Complex.I • X)‖ * hs Z * ‖exp (-Complex.I • X') - exp (-Complex.I • X)‖ :=
        (hs_add_le _ _).trans (add_le_add (hs_mul_mul_le _ _ _) (hs_mul_mul_le _ _ _))
    _ ≤ 2 * ‖X' - X‖ * hs Z * 2 + 2 * hs Z * (2 * ‖X' - X‖) := by gcongr
    _ = 8 * ‖X' - X‖ * hs Z := by ring

/-! ### `eq:four-exponentials` -/

/-- One factor `e^{iY} = 1 + iY + (-Y²/2) + R` with `‖R‖ ≤ φ(‖Y‖)`. -/
lemma exp_I_trunc (Y : Mat) :
    ‖exp (Complex.I • Y) - 1 - Complex.I • Y - (-(2 : ℂ)⁻¹ • Y ^ 2)‖ ≤ phi3 ‖Y‖ := by
  have h := norm_exp_sub_quad_le (Complex.I • Y)
  rw [norm_I_smul] at h
  have hx : (2 : ℂ)⁻¹ • (Complex.I • Y) ^ 2 = -(2 : ℂ)⁻¹ • Y ^ 2 := by
    rw [smul_pow, Complex.I_sq, smul_smul, mul_neg_one]
  rwa [hx] at h

/-- `P = 1 + L + Q + R` with `‖L‖ ≤ s`, `‖Q‖ ≤ s²/2`, `‖R‖ ≤ φ(s)`. -/
def Trunc (P L Q : Mat) (s : ℝ) : Prop :=
  ‖L‖ ≤ s ∧ ‖Q‖ ≤ s ^ 2 / 2 ∧ ‖P - (1 + L + Q)‖ ≤ phi3 s

lemma Trunc.mul {P L Q E L' Q' : Mat} {s a : ℝ} (hs : 0 ≤ s) (ha : 0 ≤ a) (hP : Trunc P L Q s)
    (hE : Trunc E L' Q' a) : Trunc (P * E) (L + L') (Q + Q' + L * L') (s + a) := by
  obtain ⟨h1, h2, h3⟩ := hP
  obtain ⟨g1, g2, g3⟩ := hE
  refine ⟨(norm_add_le _ _).trans (add_le_add h1 g1), ?_, ?_⟩
  · calc ‖Q + Q' + L * L'‖ ≤ s ^ 2 / 2 + a ^ 2 / 2 + s * a :=
          (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add h2 g2))
            ((norm_mul_le _ _).trans (mul_le_mul h1 g1 (norm_nonneg _) hs)))
      _ = (s + a) ^ 2 / 2 := by ring
  · have h := mul_trunc hs ha h1 h2 h3 g1 g2 g3
    have eP : 1 + L + Q + (P - (1 + L + Q)) = P := by abel
    have eE : 1 + L' + Q' + (E - (1 + L' + Q')) = E := by abel
    rwa [eP, eE, show 1 + (L + L') + (Q + Q' + L * L') = 1 + (L + L') + (Q + Q' + L * L') from rfl]
      at h

lemma trunc_exp (Y : Mat) :
    Trunc (exp (Complex.I • Y)) (Complex.I • Y) (-(2 : ℂ)⁻¹ • Y ^ 2) ‖Y‖ := by
  refine ⟨(norm_I_smul Y).le, ?_, ?_⟩
  · rw [norm_smul, norm_neg, norm_inv, Complex.norm_ofNat]
    have := norm_pow_le' Y two_pos
    linarith
  · have h := exp_I_trunc Y
    rwa [show exp (Complex.I • Y) - 1 - Complex.I • Y - -(2 : ℂ)⁻¹ • Y ^ 2 =
      exp (Complex.I • Y) - (1 + Complex.I • Y + -(2 : ℂ)⁻¹ • Y ^ 2) by abel] at h

/-- The quadratic part of a product of four exponentials. -/
lemma quad_four (Y₁ Y₂ Y₃ Y₄ : Mat) :
    -(2 : ℂ)⁻¹ • Y₁ ^ 2 + -(2 : ℂ)⁻¹ • Y₂ ^ 2 + (Complex.I • Y₁) * (Complex.I • Y₂) +
        -(2 : ℂ)⁻¹ • Y₃ ^ 2 + (Complex.I • Y₁ + Complex.I • Y₂) * (Complex.I • Y₃) +
        -(2 : ℂ)⁻¹ • Y₄ ^ 2 +
        (Complex.I • Y₁ + Complex.I • Y₂ + Complex.I • Y₃) * (Complex.I • Y₄) =
      -(2 : ℂ)⁻¹ • (Y₁ + Y₂ + Y₃ + Y₄) ^ 2 -
        (2 : ℂ)⁻¹ • ((Y₁ * Y₂ - Y₂ * Y₁) + (Y₁ * Y₃ - Y₃ * Y₁) + (Y₁ * Y₄ - Y₄ * Y₁) +
          (Y₂ * Y₃ - Y₃ * Y₂) + (Y₂ * Y₄ - Y₄ * Y₂) + (Y₃ * Y₄ - Y₄ * Y₃)) := by
  simp only [sq, add_mul, mul_add, smul_mul_smul_comm, Complex.I_mul_I, smul_add, smul_sub]
  module

set_option maxHeartbeats 1000000 in
/-- `eq:four-exponentials`: with `s = Σ‖Y_k‖`, `S = ΣY_k`, `C = Σ_{k<l}[Y_k, Y_l]`,
`‖e^{iY₁}e^{iY₂}e^{iY₃}e^{iY₄} - (1 + iS - S²/2 - C/2)‖ ≤ e^s - 1 - s - s²/2`. -/
theorem norm_four_exp_sub_le (Y₁ Y₂ Y₃ Y₄ : Mat) :
    ‖exp (Complex.I • Y₁) * exp (Complex.I • Y₂) * exp (Complex.I • Y₃) * exp (Complex.I • Y₄) -
      (1 + Complex.I • (Y₁ + Y₂ + Y₃ + Y₄) - (2 : ℂ)⁻¹ • (Y₁ + Y₂ + Y₃ + Y₄) ^ 2 -
        (2 : ℂ)⁻¹ • ((Y₁ * Y₂ - Y₂ * Y₁) + (Y₁ * Y₃ - Y₃ * Y₁) + (Y₁ * Y₄ - Y₄ * Y₁) +
          (Y₂ * Y₃ - Y₃ * Y₂) + (Y₂ * Y₄ - Y₄ * Y₂) + (Y₃ * Y₄ - Y₄ * Y₃)))‖ ≤
      phi3 (‖Y₁‖ + ‖Y₂‖ + ‖Y₃‖ + ‖Y₄‖) := by
  have h := ((((trunc_exp Y₁).mul (norm_nonneg _) (norm_nonneg _) (trunc_exp Y₂)).mul
    (by positivity) (norm_nonneg _) (trunc_exp Y₃)).mul (by positivity) (norm_nonneg _)
    (trunc_exp Y₄)).2.2
  have e : 1 + Complex.I • (Y₁ + Y₂ + Y₃ + Y₄) - (2 : ℂ)⁻¹ • (Y₁ + Y₂ + Y₃ + Y₄) ^ 2 -
        (2 : ℂ)⁻¹ • ((Y₁ * Y₂ - Y₂ * Y₁) + (Y₁ * Y₃ - Y₃ * Y₁) + (Y₁ * Y₄ - Y₄ * Y₁) +
          (Y₂ * Y₃ - Y₃ * Y₂) + (Y₂ * Y₄ - Y₄ * Y₂) + (Y₃ * Y₄ - Y₄ * Y₃)) =
      1 + (Complex.I • Y₁ + Complex.I • Y₂ + Complex.I • Y₃ + Complex.I • Y₄) +
        (-(2 : ℂ)⁻¹ • Y₁ ^ 2 + -(2 : ℂ)⁻¹ • Y₂ ^ 2 + (Complex.I • Y₁) * (Complex.I • Y₂) +
          -(2 : ℂ)⁻¹ • Y₃ ^ 2 + (Complex.I • Y₁ + Complex.I • Y₂) * (Complex.I • Y₃) +
          -(2 : ℂ)⁻¹ • Y₄ ^ 2 +
          (Complex.I • Y₁ + Complex.I • Y₂ + Complex.I • Y₃) * (Complex.I • Y₄)) := by
    rw [quad_four]
    simp only [smul_add, neg_smul]
    abel
  rw [e]
  exact h

/-- The inverse of the product: `e^{-iY₄}e^{-iY₃}e^{-iY₂}e^{-iY₁}` is a two-sided inverse of
`e^{iY₁}e^{iY₂}e^{iY₃}e^{iY₄}`, and it satisfies the bound with `-S` and `-C`. -/
theorem four_exp_inv (Y₁ Y₂ Y₃ Y₄ : Mat) :
    exp (Complex.I • Y₁) * exp (Complex.I • Y₂) * exp (Complex.I • Y₃) * exp (Complex.I • Y₄) *
      (exp (Complex.I • -Y₄) * exp (Complex.I • -Y₃) * exp (Complex.I • -Y₂) *
        exp (Complex.I • -Y₁)) = 1 := by
  have e : ∀ Y : Mat, exp (Complex.I • Y) * exp (Complex.I • -Y) = 1 := fun Y => by
    rw [smul_neg]; exact BakerCampbellHausdorff.exp_mul_exp_neg ℂ _
  simp only [← mul_assoc]
  rw [mul_assoc _ (exp (Complex.I • Y₄)), e, mul_one, mul_assoc _ (exp (Complex.I • Y₃)), e,
    mul_one, mul_assoc _ (exp (Complex.I • Y₂)), e, mul_one, e]

theorem norm_four_exp_inv_sub_le (Y₁ Y₂ Y₃ Y₄ : Mat) :
    ‖exp (Complex.I • -Y₄) * exp (Complex.I • -Y₃) * exp (Complex.I • -Y₂) *
        exp (Complex.I • -Y₁) -
      (1 + Complex.I • -(Y₁ + Y₂ + Y₃ + Y₄) - (2 : ℂ)⁻¹ • (-(Y₁ + Y₂ + Y₃ + Y₄)) ^ 2 -
        (2 : ℂ)⁻¹ • -((Y₁ * Y₂ - Y₂ * Y₁) + (Y₁ * Y₃ - Y₃ * Y₁) + (Y₁ * Y₄ - Y₄ * Y₁) +
          (Y₂ * Y₃ - Y₃ * Y₂) + (Y₂ * Y₄ - Y₄ * Y₂) + (Y₃ * Y₄ - Y₄ * Y₃)))‖ ≤
      phi3 (‖Y₁‖ + ‖Y₂‖ + ‖Y₃‖ + ‖Y₄‖) := by
  have h := norm_four_exp_sub_le (-Y₄) (-Y₃) (-Y₂) (-Y₁)
  simp only [norm_neg] at h
  rw [show ‖Y₄‖ + ‖Y₃‖ + ‖Y₂‖ + ‖Y₁‖ = ‖Y₁‖ + ‖Y₂‖ + ‖Y₃‖ + ‖Y₄‖ by ring] at h
  convert h using 3
  simp only [sq, mul_add, add_mul, neg_mul, mul_neg, neg_neg, smul_add, smul_neg, smul_sub,
    neg_add_rev, neg_sub]
  module

end CoreLean
