import GaussianBlockSpin.Pullback
import GaussianBlockSpin.FieldCoordinates
import GaussianBlockSpin.GaussianGraphs

/-! Elementary bounds used to choose the parameters of the cumulant lemma:
* one_add_pow_mul_exp_neg_le: `(1 + u)^n e^{-c u} ≤ n! e^c/c^n` for `u ≥ 0`, `c > 0`;
* le_max_of_exp_lt: `e^u < A + B u` (`A ≥ 0`, `u ≥ 0`) gives `u ≤ max 1 (2(A + B))`;
* pow_le_mul_one_add_pow, exists_pow_between (`n ≤ L^j ≤ L n` with `j ≤ m` when `n ≤ L^m`), inv_sqrt_pow_div_sq
  (`(√(X^d/X²))⁻¹ = X^{-(d-2)/2}`);
* abs_polyVal_le (`|H(z)| ≤ (Σ_Z |a_Z|)(1 + M)^D` for `|z_i| ≤ M`), polyVal_eq_add_const (`H = H₀ + c`, `c` the
  coefficient of the empty monomial, `H₀` without constant term);
* abs_fieldCoord_symm_le (a coordinate of a field is at most its norm), integrable_one_add_norm_pow_gaussProb
  (`(1 + ‖x‖)^n` is integrable for a normalised Gaussian measure). -/

namespace GaussianBlockSpin

open MeasureTheory Real
open scoped RealInnerProductSpace

/-- `(1 + u)^n e^{-c u} ≤ n! e^c/c^n`. -/
lemma one_add_pow_mul_exp_neg_le {c : ℝ} (hc : 0 < c) (n : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    (1 + u) ^ n * exp (-(c * u)) ≤ n.factorial * exp c / c ^ n := by
  have h := Real.pow_div_factorial_le_exp (c * (1 + u)) (by positivity) n
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hcn : 0 < c ^ n := pow_pos hc n
  rw [div_le_iff₀ hf, mul_pow] at h
  rw [le_div_iff₀ hcn]
  have he : exp (c * (1 + u)) = exp c * exp (c * u) := by rw [← exp_add]; ring_nf
  rw [he] at h
  have hpos : 0 < exp (-(c * u)) := exp_pos _
  have hinv : exp (c * u) * exp (-(c * u)) = 1 := by rw [← exp_add]; simp
  calc (1 + u) ^ n * exp (-(c * u)) * c ^ n = c ^ n * (1 + u) ^ n * exp (-(c * u)) := by ring
    _ ≤ exp c * exp (c * u) * n.factorial * exp (-(c * u)) :=
        mul_le_mul_of_nonneg_right h hpos.le
    _ = n.factorial * exp c * (exp (c * u) * exp (-(c * u))) := by ring
    _ = n.factorial * exp c := by rw [hinv, mul_one]

/-- `e^u < A + B u` bounds `u`. -/
lemma le_max_of_exp_lt {A B u : ℝ} (hA : 0 ≤ A) (hu : 0 ≤ u) (h : exp u < A + B * u) :
    u ≤ max 1 (2 * (A + B)) := by
  by_contra hcon
  push Not at hcon
  have h1 : 1 < u := lt_of_le_of_lt (le_max_left _ _) hcon
  have h2 : 2 * (A + B) < u := lt_of_le_of_lt (le_max_right _ _) hcon
  have hq := Real.quadratic_le_exp_of_nonneg hu
  have h3 := mul_lt_mul_of_pos_right h2 (show (0 : ℝ) < u by linarith)
  have h4 := mul_nonneg hA (show (0 : ℝ) ≤ u - 1 by linarith)
  nlinarith

lemma pow_le_mul_one_add_pow {x a u : ℝ} (hx : 0 ≤ x) (h : x ≤ a * (1 + u)) (n : ℕ) :
    x ^ n ≤ a ^ n * (1 + u) ^ n := by
  rw [← mul_pow]; exact pow_le_pow_left₀ hx h n

/-- A power `L^j`, `j ≤ m`, between `n` and `L n`. -/
lemma exists_pow_between {L n m : ℕ} (hL : 2 ≤ L) (hn : 1 ≤ n) (hnm : n ≤ L ^ m) :
    ∃ j ≤ m, n ≤ L ^ j ∧ L ^ j ≤ L * n := by
  classical
  have hex : ∃ j, n ≤ L ^ j := ⟨m, hnm⟩
  refine ⟨Nat.find hex, Nat.find_min' hex hnm, Nat.find_spec hex, ?_⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
  · rw [h0, pow_zero]; nlinarith
  · have h1 := Nat.find_min hex (Nat.sub_lt hpos one_pos)
    push Not at h1
    calc L ^ Nat.find hex = L * L ^ (Nat.find hex - 1) := by rw [← pow_succ', Nat.sub_add_cancel hpos]
      _ ≤ L * n := Nat.mul_le_mul_left _ h1.le

/-- `(√(X^d/X²))⁻¹ = X^{-(d-2)/2}`. -/
lemma inv_sqrt_pow_div_sq {X : ℝ} (hX : 0 < X) (d : ℕ) :
    (Real.sqrt (X ^ d / X ^ 2))⁻¹ = X ^ (-((d : ℝ) - 2) / 2) := by
  have h1 : X ^ d / X ^ 2 = X ^ ((d : ℝ) - 2) := by
    rw [Real.rpow_sub hX, Real.rpow_natCast, Real.rpow_two]
  rw [h1, Real.sqrt_eq_rpow, ← Real.rpow_mul hX.le, ← Real.rpow_neg hX.le]
  congr 1
  ring

section Poly

variable {ι : Type*} [Fintype ι] {D : ℕ}

/-- A polynomial of degree `≤ D` at a point with coordinates bounded by `M ≥ 0`. -/
lemma abs_polyVal_le (a : MonoIdx ι D → ℝ) (z : ι → ℝ) {M : ℝ} (hM : 0 ≤ M) (hz : ∀ i, |z i| ≤ M) :
    |polyVal a z| ≤ (∑ Z, |a Z|) * (1 + M) ^ D := by
  unfold polyVal
  rw [Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun Z _ => ?_)
  rw [abs_mul]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  unfold monoVal
  rw [Finset.abs_prod]
  calc ∏ l, |z (Z.2 l)| ≤ ∏ _l : Fin Z.1, (1 + M) :=
        Finset.prod_le_prod₀ (fun l _ => abs_nonneg _) fun l _ => (hz _).trans (by linarith)
    _ = (1 + M) ^ (Z.1 : ℕ) := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    _ ≤ (1 + M) ^ D := pow_le_pow_right₀ (by linarith) (Nat.lt_succ_iff.mp Z.1.isLt)

/-- **The constant term of a polynomial**: `H = H₀ + c` with `H₀` without constant term. -/
lemma polyVal_eq_add_const (a : MonoIdx ι D → ℝ) (z : ι → ℝ) :
    polyVal a z = polyVal (fun Z => if (Z.1 : ℕ) = 0 then 0 else a Z) z +
      ∑ Z : MonoIdx ι D, if (Z.1 : ℕ) = 0 then a Z else 0 := by
  unfold polyVal
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun Z _ => ?_
  by_cases h : (Z.1 : ℕ) = 0
  · have : monoVal Z.2 z = 1 := Finset.prod_eq_one fun l _ => absurd l.isLt (by omega)
    simp [h, this]
  · simp [h]

end Poly

/-- A coordinate of a field is at most its norm. -/
lemma abs_fieldCoord_symm_le {X : Type*} [Fintype X] [DecidableEq X] {N : ℕ}
    (x : PiLp 2 (fun _ : X => EuclideanSpace ℝ (Fin N))) (p : X × Fin N) : |(fieldCoord.symm x) p| ≤ ‖x‖ := by
  rw [fieldCoord_symm_apply]
  have h1 := PiLp.norm_apply_le (x p.1) p.2
  rw [Real.norm_eq_abs] at h1
  exact h1.trans (PiLp.norm_apply_le x p.1)

/-- `(1 + ‖x‖)^n` is integrable for a normalised Gaussian measure. -/
lemma integrable_one_add_norm_pow_gaussProb {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric)
    (hpos : ∀ x, x ≠ 0 → 0 < ⟪x, T x⟫) (n : ℕ) : Integrable (fun x => (1 + ‖x‖) ^ n) (gaussProb T) := by
  rw [integrable_gaussProb_iff hT hpos]
  exact integrable_mul_gaussWeight_of_le_one_add hT hpos (by fun_prop) n
    (fun x => by rw [one_mul, abs_of_nonneg (by positivity)])

end GaussianBlockSpin
