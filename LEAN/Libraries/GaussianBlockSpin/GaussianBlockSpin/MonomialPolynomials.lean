import GaussianBlockSpin.ProductMomentBounds
import GaussianBlockSpin.TupleBounds
import GaussianBlockSpin.ProductIndependence

/-! Polynomials in independent coordinates as sums of monomials `c_X ξ_{y_1} ⋯ ξ_{y_p}` (`X = (p, y)`, `p ≤ D`):
* MonoIdx, monoPiece, monoSupp: the monomial index type, the pieces and their coordinate sets;
* integral_prod_monoPiece: moments of products of pieces are the coefficients times the coordinate moments;
* sum_expoOf: the total degree of a product of monomials is the sum of their degrees;
* abs_monoVal_le: `|ξ_{y_1} ⋯ ξ_{y_p}| ≤ ∏_c (1 + |ξ_c|)^D` (domination for integrability). -/

namespace GaussianBlockSpin

open MeasureTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {D : ℕ}

/-- Monomials of degree at most `D` in the coordinates `ι`. -/
abbrev MonoIdx (ι : Type*) (D : ℕ) := Σ p : Fin (D + 1), (Fin p → ι)

/-- The underlying tuple. -/
def MonoIdx.toNat (X : MonoIdx ι D) : Σ p : ℕ, Fin p → ι := ⟨X.1, X.2⟩

/-- The piece `c_X ξ_{y_1} ⋯ ξ_{y_p}`. -/
def monoPiece (coef : MonoIdx ι D → ℝ) (X : MonoIdx ι D) (ξ : ι → ℝ) : ℝ := coef X * monoVal X.2 ξ

/-- The coordinates of a monomial. -/
def monoSupp (X : MonoIdx ι D) : Finset ι := Finset.univ.image X.2

omit [Fintype ι] [DecidableEq ι] in
lemma monoSupp_card_le [DecidableEq ι] (X : MonoIdx ι D) : (monoSupp X).card ≤ D :=
  (Finset.card_image_le).trans (by simp; exact Nat.lt_succ_iff.mp X.1.isLt)

omit [Fintype ι] in
lemma dependsOn_monoPiece (coef : MonoIdx ι D → ℝ) (X : MonoIdx ι D) :
    DependsOn (monoPiece coef X) (monoSupp X : Set ι) := by
  intro ξ ξ' h
  unfold monoPiece monoVal
  congr 1
  exact Finset.prod_congr rfl fun l _ => h _ (by simp [monoSupp])

omit [DecidableEq ι] [Fintype ι] in
lemma measurable_monoPiece (coef : MonoIdx ι D → ℝ) (X : MonoIdx ι D) : Measurable (monoPiece coef X) := by
  unfold monoPiece monoVal
  exact (Finset.measurable_prod _ fun l _ => measurable_pi_apply (X.2 l)).const_mul _

/-- **Moments of products of pieces**. -/
lemma integral_prod_monoPiece (ν₁ : ι → Measure ℝ) [∀ i, SigmaFinite (ν₁ i)] (coef : MonoIdx ι D → ℝ) {k : ℕ}
    (g : Fin k → MonoIdx ι D) (U : Finset (Fin k)) :
    ∫ ξ, ∏ i ∈ U, monoPiece coef (g i) ξ ∂(Measure.pi ν₁) =
      (∏ i ∈ U, coef (g i)) * ∏ c, ∫ x, x ^ expoOf (fun i => (g i).toNat) U c ∂(ν₁ c) := by
  simp_rw [monoPiece, Finset.prod_mul_distrib]
  rw [integral_const_mul]
  congr 1
  exact integral_prod_monoVal ν₁ (fun i => (g i).toNat) U

omit [DecidableEq ι] in
/-- The total degree of a product of monomials. -/
lemma sum_expoOf [DecidableEq ι] {k : ℕ} (g : Fin k → Σ p : ℕ, Fin p → ι) (U : Finset (Fin k)) :
    ∑ c, expoOf g U c = ∑ i ∈ U, (g i).1 := by
  unfold expoOf
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.card_eq_sum_card_fiberwise (fun l _ => Finset.mem_univ ((g i).2 l))]
  simp

omit [DecidableEq ι] in
/-- `|ξ_{y_1} ⋯ ξ_{y_p}| ≤ ∏_c (1 + |ξ_c|)^D` for `p ≤ D`. -/
lemma abs_monoVal_le [DecidableEq ι] (X : MonoIdx ι D) (ξ : ι → ℝ) :
    |monoVal X.2 ξ| ≤ ∏ c, (1 + |ξ c|) ^ D := by
  rw [monoVal_eq_prod, Finset.abs_prod]
  refine Finset.prod_le_prod₀ (fun c _ => abs_nonneg _) fun c _ => ?_
  rw [abs_pow]
  have h1 : |ξ c| ^ (Finset.univ.filter fun l => X.2 l = c).card ≤
      (1 + |ξ c|) ^ (Finset.univ.filter fun l => X.2 l = c).card :=
    pow_le_pow_left₀ (abs_nonneg _) (by linarith) _
  refine h1.trans (pow_le_pow_right₀ (by linarith [abs_nonneg (ξ c)]) ?_)
  calc (Finset.univ.filter fun l => X.2 l = c).card ≤ (Finset.univ : Finset (Fin X.1)).card :=
        Finset.card_filter_le _ _
    _ = X.1 := by simp
    _ ≤ D := Nat.lt_succ_iff.mp X.1.isLt

end GaussianBlockSpin
