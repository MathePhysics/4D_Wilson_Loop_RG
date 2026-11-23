/-
`lem:ward` of BALABAN_CORE.tex, the series: the remainders of the fourth order of `e^X` and of
`φ(X) = (e^X - 1)/X = Σ X^k/(k + 1)!` in a Banach algebra, and the solution of `φ(X)H = e^Xa - c` to the
third order.

With `Q₋(X) = 1 + X/2 + X²/12` and `Q₊(X) = -1 + X/2 - X²/12`,
`φ(X)Q₋(X) - e^X` and `φ(X)Q₊(X) + 1` are of the fourth order in `X`, so that `H = Q₋(X)a + Q₊(X)c`
solves `φ(X)H = e^Xa - c` up to `O(‖X‖⁴)`. Applied with `X = -ad(iB)`, `a = λ(b₋)`, `c = λ(b₊)`, this is
the expansion `-dλ + ½i[λ(b₋) + λ(b₊), B] + (1/12)[B, [B, dλ]] + O(B⁴)` of the proof of `lem:ward`
(`ψ(z) = z/(1 - e^{-z}) = 1 + z/2 + z²/12 + O(z⁴)`).
-/
import Mathlib
import BakerCampbellHausdorff.Dexp

open NormedSpace BakerCampbellHausdorff Finset
open scoped Nat

noncomputable section

namespace CoreLean

namespace Ward

variable {𝔹 : Type*} [NormedRing 𝔹] [NormedAlgebra ℂ 𝔹] [CompleteSpace 𝔹]

/-- The tail after four terms: if `‖f (k + 4)‖ ≤ x^{k+4}/(k + 4)!`, then `‖Σ f - Σ_{k<4} f k‖ ≤ x⁴eˣ`. -/
lemma norm_tail_four_le {f : ℕ → 𝔹} {s : 𝔹} (hf : HasSum f s) {x : ℝ} (hx : 0 ≤ x)
    (hb : ∀ k, ‖f (k + 4)‖ ≤ ((k + 4)! : ℝ)⁻¹ * x ^ (k + 4)) :
    ‖s - ∑ k ∈ range 4, f k‖ ≤ x ^ 4 * Real.exp x := by
  have h1 := (hasSum_nat_add_iff' 4).mpr hf
  have hE := (hasSum_real_exp x).mul_left (x ^ 4)
  refine h1.norm_le_of_bounded hE fun k => (hb k).trans ?_
  rw [smul_eq_mul, pow_add, mul_comm (x ^ k) (x ^ 4)]
  have hk : ((k + 4)! : ℝ)⁻¹ ≤ (k ! : ℝ)⁻¹ :=
    inv_anti₀ (by positivity) (by exact_mod_cast Nat.factorial_le (by omega))
  have h0 : 0 ≤ x ^ 4 * x ^ k := by positivity
  nlinarith

/-- The cubic Taylor polynomial of `e^X`. -/
def Pe (X : 𝔹) : 𝔹 := 1 + X + (2 : ℂ)⁻¹ • X ^ 2 + (6 : ℂ)⁻¹ • X ^ 3

/-- The cubic Taylor polynomial of `φ(X) = (e^X - 1)/X`. -/
def Pφ (X : 𝔹) : 𝔹 := 1 + (2 : ℂ)⁻¹ • X + (6 : ℂ)⁻¹ • X ^ 2 + (24 : ℂ)⁻¹ • X ^ 3

/-- `Q₋(X) = 1 + X/2 + X²/12`. -/
def Qm (X : 𝔹) : 𝔹 := 1 + (2 : ℂ)⁻¹ • X + (12 : ℂ)⁻¹ • X ^ 2

/-- `Q₊(X) = -1 + X/2 - X²/12`. -/
def Qp (X : 𝔹) : 𝔹 := -1 + (2 : ℂ)⁻¹ • X - (12 : ℂ)⁻¹ • X ^ 2

lemma norm_exp_sub_Pe_le (X : 𝔹) : ‖exp X - Pe X‖ ≤ ‖X‖ ^ 4 * Real.exp ‖X‖ := by
  have h := norm_tail_four_le (exp_series_hasSum_exp' (𝕂 := ℂ) X) (norm_nonneg X) fun k => by
    rw [norm_smul, norm_inv, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left (norm_pow_le' X (by omega)) (by positivity)
  have e : ∑ k ∈ range 4, ((k ! : ℂ)⁻¹ • X ^ k) = Pe X := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Pe]
    norm_num
    try abel
  rwa [e] at h

lemma norm_φ_sub_Pφ_le (X : 𝔹) : ‖expSubOneDiv ℂ X - Pφ X‖ ≤ ‖X‖ ^ 4 * Real.exp ‖X‖ := by
  have h := norm_tail_four_le (hasSum_expSubOneDiv (𝕂 := ℂ) X) (norm_nonneg X) fun k => by
    have := norm_expSubOneDiv_term_le (𝕂 := ℂ) X (k := k + 4) (by omega)
    simpa only [smul_eq_mul] using this
  have e : ∑ k ∈ range 4, (((k + 1)! : ℂ)⁻¹ • X ^ k) = Pφ X := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Pφ]
    norm_num
  rwa [e] at h

lemma pow_two_mul (X : 𝔹) : X ^ 2 * X = X ^ 3 := (pow_succ X 2).symm
lemma mul_pow_two (X : 𝔹) : X * X ^ 2 = X ^ 3 := (pow_succ' X 2).symm

/-- `Pφ(X)Q₋(X) = Pe(X) + (5/144)X⁴ + (1/288)X⁵`. -/
lemma Pφ_mul_Qm (X : 𝔹) :
    Pφ X * Qm X = Pe X + ((5 : ℂ) / 144) • X ^ 4 + ((1 : ℂ) / 288) • X ^ 5 := by
  have h2 : X * X = X ^ 2 := (sq X).symm
  have h3 : X * X ^ 2 = X ^ 3 := (pow_succ' X 2).symm
  have h3' : X ^ 2 * X = X ^ 3 := (pow_succ X 2).symm
  have h4 : X ^ 2 * X ^ 2 = X ^ 4 := (pow_add X 2 2).symm
  have h4' : X ^ 3 * X = X ^ 4 := (pow_succ X 3).symm
  have h5 : X ^ 3 * X ^ 2 = X ^ 5 := (pow_add X 3 2).symm
  simp only [Pφ, Qm, Pe, add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm,
    h2, h3, h3', h4, h4', h5]
  module

/-- `Pφ(X)Q₊(X) = -1 + (1/144)X⁴ - (1/288)X⁵`. -/
lemma Pφ_mul_Qp (X : 𝔹) :
    Pφ X * Qp X = -1 + ((1 : ℂ) / 144) • X ^ 4 - ((1 : ℂ) / 288) • X ^ 5 := by
  have h2 : X * X = X ^ 2 := (sq X).symm
  have h3 : X * X ^ 2 = X ^ 3 := (pow_succ' X 2).symm
  have h3' : X ^ 2 * X = X ^ 3 := (pow_succ X 2).symm
  have h4 : X ^ 2 * X ^ 2 = X ^ 4 := (pow_add X 2 2).symm
  have h4' : X ^ 3 * X = X ^ 4 := (pow_succ X 3).symm
  have h5 : X ^ 3 * X ^ 2 = X ^ 5 := (pow_add X 3 2).symm
  simp only [Pφ, Qp, add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one, neg_mul, mul_neg,
    smul_mul_assoc, mul_smul_comm, h2, h3, h3', h4, h4', h5]
  module

variable (h1 : ‖(1 : 𝔹)‖ ≤ 1)
include h1

lemma norm_Q_le {X : 𝔹} (hX : ‖X‖ ≤ 1) : ‖Qm X‖ ≤ 2 ∧ ‖Qp X‖ ≤ 2 := by
  have hX2 : ‖X ^ 2‖ ≤ 1 :=
    (norm_pow_le' X (by norm_num)).trans (pow_le_one₀ (norm_nonneg _) hX)
  have hs1 : ‖(2 : ℂ)⁻¹ • X‖ ≤ 2⁻¹ := by
    rw [norm_smul]; norm_num; linarith
  have hs2 : ‖(12 : ℂ)⁻¹ • X ^ 2‖ ≤ 12⁻¹ := by
    rw [norm_smul]; norm_num; linarith
  constructor
  · calc ‖Qm X‖ ≤ ‖(1 : 𝔹)‖ + ‖(2 : ℂ)⁻¹ • X‖ + ‖(12 : ℂ)⁻¹ • X ^ 2‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ 2 := by linarith
  · calc ‖Qp X‖ ≤ ‖-(1 : 𝔹)‖ + ‖(2 : ℂ)⁻¹ • X‖ + ‖(12 : ℂ)⁻¹ • X ^ 2‖ :=
          (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ 2 := by rw [norm_neg]; linarith

lemma exp_norm_le_three {X : 𝔹} (hX : ‖X‖ ≤ 1) : Real.exp ‖X‖ ≤ 3 :=
  (Real.exp_le_exp.mpr hX).trans (by have := Real.exp_one_lt_d9; norm_num at this; linarith)

lemma norm_pow_four_five {X : 𝔹} (hX : ‖X‖ ≤ 1) : ‖X ^ 4‖ ≤ ‖X‖ ^ 4 ∧ ‖X ^ 5‖ ≤ ‖X‖ ^ 4 :=
  ⟨norm_pow_le' X (by norm_num), (norm_pow_le' X (by norm_num)).trans (by
    rw [pow_succ]; exact mul_le_of_le_one_right (by positivity) hX)⟩

/-- `‖φ(X)Q₋(X) - e^X‖ ≤ 10‖X‖⁴` for `‖X‖ ≤ 1`. -/
lemma norm_φQm_sub_exp_le {X : 𝔹} (hX : ‖X‖ ≤ 1) :
    ‖expSubOneDiv ℂ X * Qm X - exp X‖ ≤ 10 * ‖X‖ ^ 4 := by
  have hQ := (norm_Q_le h1 hX).1
  have he := exp_norm_le_three h1 hX
  have hφ := norm_φ_sub_Pφ_le X
  have hE := norm_exp_sub_Pe_le X
  obtain ⟨h4, h5⟩ := norm_pow_four_five h1 hX
  have hx4 : 0 ≤ ‖X‖ ^ 4 := by positivity
  have e : expSubOneDiv ℂ X * Qm X - exp X = (expSubOneDiv ℂ X - Pφ X) * Qm X +
      (((5 : ℂ) / 144) • X ^ 4 + ((1 : ℂ) / 288) • X ^ 5) - (exp X - Pe X) := by
    rw [sub_mul, Pφ_mul_Qm]; abel
  rw [e]
  have hr : ‖((5 : ℂ) / 144) • X ^ 4 + ((1 : ℂ) / 288) • X ^ 5‖ ≤ 1 * ‖X‖ ^ 4 := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul]
    norm_num
    nlinarith
  calc ‖(expSubOneDiv ℂ X - Pφ X) * Qm X + (((5 : ℂ) / 144) • X ^ 4 + ((1 : ℂ) / 288) • X ^ 5) -
        (exp X - Pe X)‖
      ≤ ‖expSubOneDiv ℂ X - Pφ X‖ * ‖Qm X‖ + 1 * ‖X‖ ^ 4 + ‖exp X - Pe X‖ :=
        (norm_sub_le _ _).trans (add_le_add ((norm_add_le _ _).trans
          (add_le_add (norm_mul_le _ _) hr)) le_rfl)
    _ ≤ (‖X‖ ^ 4 * 3) * 2 + 1 * ‖X‖ ^ 4 + ‖X‖ ^ 4 * 3 := by
        gcongr
        · exact hφ.trans (mul_le_mul_of_nonneg_left he hx4)
        · exact hE.trans (mul_le_mul_of_nonneg_left he hx4)
    _ ≤ 10 * ‖X‖ ^ 4 := by nlinarith

/-- `‖φ(X)Q₊(X) + 1‖ ≤ 10‖X‖⁴` for `‖X‖ ≤ 1`. -/
lemma norm_φQp_add_one_le {X : 𝔹} (hX : ‖X‖ ≤ 1) :
    ‖expSubOneDiv ℂ X * Qp X + 1‖ ≤ 10 * ‖X‖ ^ 4 := by
  have hQ := (norm_Q_le h1 hX).2
  have he := exp_norm_le_three h1 hX
  have hφ := norm_φ_sub_Pφ_le X
  obtain ⟨h4, h5⟩ := norm_pow_four_five h1 hX
  have hx4 : 0 ≤ ‖X‖ ^ 4 := by positivity
  have e : expSubOneDiv ℂ X * Qp X + 1 = (expSubOneDiv ℂ X - Pφ X) * Qp X +
      (((1 : ℂ) / 144) • X ^ 4 - ((1 : ℂ) / 288) • X ^ 5) := by
    rw [sub_mul, Pφ_mul_Qp]; abel
  rw [e]
  have hr : ‖((1 : ℂ) / 144) • X ^ 4 - ((1 : ℂ) / 288) • X ^ 5‖ ≤ 1 * ‖X‖ ^ 4 := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_smul, norm_smul]
    norm_num
    nlinarith
  calc ‖(expSubOneDiv ℂ X - Pφ X) * Qp X + (((1 : ℂ) / 144) • X ^ 4 - ((1 : ℂ) / 288) • X ^ 5)‖
      ≤ ‖expSubOneDiv ℂ X - Pφ X‖ * ‖Qp X‖ + 1 * ‖X‖ ^ 4 :=
        (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) hr)
    _ ≤ (‖X‖ ^ 4 * 3) * 2 + 1 * ‖X‖ ^ 4 := by
        gcongr
        exact hφ.trans (mul_le_mul_of_nonneg_left he hx4)
    _ ≤ 10 * ‖X‖ ^ 4 := by nlinarith

end Ward

end CoreLean
