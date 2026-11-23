import GaussianBlockSpin.MonomialPolynomials

/-! Preparations for the comparison (MonomialCumulants) of the truncated expectations of a polynomial
`F = Σ_{X ∈ S} c_X ξ^X` (monomials of degree `1 ≤ p ≤ D`) under two product laws `ν`, `γ` whose one-dimensional
moments satisfy `|∫ x^q| ≤ 2 q! K` and differ by at most `η q!` (the restricted and the full normal law):
* monoConst, pow_mul_factorial_le_monoConst: the per-tuple bound `max(1, Q) Q! (2K)^Q ≤ C^{|U|}`,
  `C = D t (D t)! (2K)^D`, for `|U| ≤ t` monomials of degrees in `[1, D]` (total degree `Q`);
* integrable_prod_sum_monoPiece: products of sums of pieces are integrable when every `(1 + |x|)^r` is. -/

namespace GaussianBlockSpin

open MeasureTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {D : ℕ}

/-- The constant `C = D t (D t)! (2K)^D` of the per-piece bound. -/
noncomputable def monoConst (D t : ℕ) (K : ℝ) : ℝ := (D * t : ℕ) * ((D * t).factorial : ℝ) * (2 * K) ^ D

lemma one_le_monoConst {t : ℕ} {K : ℝ} (hD : 1 ≤ D) (ht : 1 ≤ t) (hK : 1 ≤ 2 * K) : 1 ≤ monoConst D t K := by
  unfold monoConst
  have h1 : (1 : ℝ) ≤ (D * t : ℕ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by positivity)
  have h2 : (1 : ℝ) ≤ ((D * t).factorial : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)
  have h3 : (1 : ℝ) ≤ (2 * K) ^ D := one_le_pow₀ hK
  calc (1 : ℝ) = 1 * 1 * 1 := by ring
    _ ≤ _ := by gcongr

/-- **The per-tuple bound**: for `|U| ≤ t` monomials of degrees in `[1, D]` with total degree `Q`,
`max(1, Q) Q! (2K)^Q ≤ C^{|U|}`. -/
lemma pow_mul_factorial_le_monoConst {t : ℕ} {K : ℝ} (hD : 1 ≤ D) (ht : 1 ≤ t) (hK : 1 ≤ 2 * K) {u Q : ℕ}
    (hu : u ≤ t) (hQ1 : u ≤ Q) (hQD : Q ≤ D * u) :
    (max 1 Q : ℕ) * (Q.factorial : ℝ) * (2 * K) ^ Q ≤ monoConst D t K ^ u := by
  rcases Nat.eq_zero_or_pos u with hu0 | hupos
  · subst hu0
    have : Q = 0 := by omega
    subst this
    simp
  · have hQt : Q ≤ D * t := hQD.trans (Nat.mul_le_mul_left D hu)
    have hmax : (max 1 Q : ℕ) ≤ D * t := max_le (by nlinarith) hQt
    have hC := one_le_monoConst hD ht hK
    have hDt1 : (1 : ℝ) ≤ (D * t : ℕ) * ((D * t).factorial : ℝ) := by
      have h1 : (1 : ℝ) ≤ (D * t : ℕ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by positivity)
      have h2 : (1 : ℝ) ≤ ((D * t).factorial : ℝ) := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)
      nlinarith
    calc (max 1 Q : ℕ) * (Q.factorial : ℝ) * (2 * K) ^ Q
        ≤ (D * t : ℕ) * ((D * t).factorial : ℝ) * (2 * K) ^ (D * u) := by
          have h1 : ((max 1 Q : ℕ) : ℝ) ≤ (D * t : ℕ) := by exact_mod_cast hmax
          have h2 : (Q.factorial : ℝ) ≤ ((D * t).factorial : ℝ) := by exact_mod_cast Nat.factorial_le hQt
          have h3 : (2 * K) ^ Q ≤ (2 * K) ^ (D * u) := pow_le_pow_right₀ hK hQD
          gcongr
      _ = (D * t : ℕ) * ((D * t).factorial : ℝ) * ((2 * K) ^ D) ^ u := by rw [pow_mul]
      _ ≤ ((D * t : ℕ) * ((D * t).factorial : ℝ)) ^ u * ((2 * K) ^ D) ^ u := by
          gcongr
          calc ((D * t : ℕ) * ((D * t).factorial : ℝ)) = ((D * t : ℕ) * ((D * t).factorial : ℝ)) ^ 1 := (pow_one _).symm
            _ ≤ _ := pow_le_pow_right₀ hDt1 hupos
      _ = monoConst D t K ^ u := by unfold monoConst; rw [mul_pow (((D * t : ℕ) : ℝ) * _)]

omit [DecidableEq ι] in
/-- Products of sums of pieces are integrable under a product law with all polynomial moments. -/
lemma integrable_prod_sum_monoPiece [DecidableEq ι] (μ : ι → Measure ℝ) [∀ c, IsProbabilityMeasure (μ c)]
    (hpoly : ∀ c (r : ℕ), Integrable (fun x : ℝ => (1 + |x|) ^ r) (μ c)) (coef : MonoIdx ι D → ℝ)
    {A : Type*} (Y : A → MonoIdx ι D) {k : ℕ} (T : Finset (Fin k)) (tt : Fin k → Finset A) :
    Integrable (fun ξ => ∏ v ∈ T, ∑ a ∈ tt v, monoPiece coef (Y a) ξ) (Measure.pi μ) := by
  have hdom : Integrable (fun ξ : ι → ℝ => (∏ v ∈ T, ∑ a ∈ tt v, |coef (Y a)|) *
      ∏ c, (1 + |ξ c|) ^ (D * T.card)) (Measure.pi μ) :=
    (Integrable.fintype_prod (f := fun c x => (1 + |x|) ^ (D * T.card)) fun c => hpoly c _).const_mul _
  refine hdom.mono' ?_ (ae_of_all _ fun ξ => ?_)
  · exact (Finset.measurable_prod _ fun v _ => Finset.measurable_sum _ fun a _ =>
      measurable_monoPiece coef (Y a)).aestronglyMeasurable
  · rw [Real.norm_eq_abs, Finset.abs_prod]
    have hW : ∀ v ∈ T, |∑ a ∈ tt v, monoPiece coef (Y a) ξ| ≤
        (∑ a ∈ tt v, |coef (Y a)|) * ∏ c, (1 + |ξ c|) ^ D := by
      intro v _
      rw [Finset.sum_mul]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a _ => ?_)
      rw [monoPiece, abs_mul]
      exact mul_le_mul_of_nonneg_left (abs_monoVal_le (Y a) ξ) (abs_nonneg _)
    calc ∏ v ∈ T, |∑ a ∈ tt v, monoPiece coef (Y a) ξ|
        ≤ ∏ v ∈ T, ((∑ a ∈ tt v, |coef (Y a)|) * ∏ c, (1 + |ξ c|) ^ D) :=
          Finset.prod_le_prod₀ (fun v _ => abs_nonneg _) hW
      _ = (∏ v ∈ T, ∑ a ∈ tt v, |coef (Y a)|) * ∏ c, (1 + |ξ c|) ^ (D * T.card) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, ← Finset.prod_pow]
          congr 1
          refine Finset.prod_congr rfl fun c _ => ?_
          rw [← pow_mul]

end GaussianBlockSpin
