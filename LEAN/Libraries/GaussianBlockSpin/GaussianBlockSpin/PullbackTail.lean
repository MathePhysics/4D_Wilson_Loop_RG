import GaussianBlockSpin.Pullback

/-! Weighted bounds on the pulled-back coefficients (the decay of `H(A ξ)` in the independent coordinates): with the
spread `w(X) = Σ_{i,j} dist(X_i, X_j)` of a monomial, for a symmetric nonnegative `dist` with the triangle inequality,
* spread_le: `w(X) ≤ w(Z) + 2 p Σ_l dist(Z_l, X_l)`;
* sum_site_pull_weighted_le: `Σ_{X ∋ y} |b_X| e^{κ' w(X)} ≤ (D + 1)² K^D aS`, where `K` bounds the row and column
  sums of `|A| e^{2 D κ' dist}` and `aS` the per-site sums of `|a| e^{κ' w}`. -/

namespace GaussianBlockSpin

open Matrix Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {D : ℕ} (dist : ι → ι → ℝ)

/-- The spread `w(X) = Σ_{i,j} dist(X_i, X_j)` of a monomial. -/
def spread (X : MonoIdx ι D) : ℝ := ∑ i, ∑ j, dist (X.2 i) (X.2 j)

omit [Fintype ι] [DecidableEq ι] in
lemma spread_le {p : ℕ} (hsymm : ∀ x y, dist x y = dist y x) (htri : ∀ x y z, dist x z ≤ dist x y + dist y z)
    (X Z : Fin p → ι) :
    ∑ i, ∑ j, dist (X i) (X j) ≤ ∑ i, ∑ j, dist (Z i) (Z j) + 2 * p * ∑ l, dist (Z l) (X l) := by
  have hpair : ∀ i j, dist (X i) (X j) ≤ dist (Z i) (X i) + dist (Z i) (Z j) + dist (Z j) (X j) := fun i j => by
    have h1 := htri (X i) (Z i) (X j)
    have h2 := htri (Z i) (Z j) (X j)
    rw [hsymm (X i) (Z i)] at h1
    linarith
  calc ∑ i, ∑ j, dist (X i) (X j)
      ≤ ∑ i, ∑ j, (dist (Z i) (X i) + dist (Z i) (Z j) + dist (Z j) (X j)) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hpair i j
    _ = ∑ i, ∑ j, dist (Z i) (Z j) + 2 * p * ∑ l, dist (Z l) (X l) := by
        simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [← Finset.mul_sum]
        ring

/-- **Weighted per-site bound of the pulled-back coefficients**. -/
theorem sum_site_pull_weighted_le (a : MonoIdx ι D → ℝ) (A : Matrix ι ι ℝ)
    (hsymm : ∀ x y, dist x y = dist y x) (htri : ∀ x y z, dist x z ≤ dist x y + dist y z)
    (hd0 : ∀ x y, 0 ≤ dist x y) {κ' : ℝ} (hκ : 0 ≤ κ') {K : ℝ} (hK : 1 ≤ K)
    (hrow : ∀ z, ∑ x, |A z x| * exp (2 * D * κ' * dist z x) ≤ K)
    (hcol : ∀ x, ∑ z, |A z x| * exp (2 * D * κ' * dist z x) ≤ K) {aS : ℝ}
    (haS : ∀ z, ∑ Z' ∈ Finset.univ.filter (fun Z' : MonoIdx ι D => z ∈ monoSupp Z'),
      |a Z'| * exp (κ' * spread dist Z') ≤ aS) (y : ι) :
    ∑ X ∈ Finset.univ.filter (fun X : MonoIdx ι D => y ∈ monoSupp X),
        |pullCoef a A X| * exp (κ' * spread dist X) ≤ ((D + 1) ^ 2 : ℕ) * K ^ D * aS := by
  set a' : MonoIdx ι D → ℝ := fun Z' => |a Z'| * exp (κ' * spread dist Z') with ha'
  set A' : ι → ι → ℝ := fun z x => |A z x| * exp (2 * D * κ' * dist z x) with hA'
  have hpoint : ∀ X : MonoIdx ι D, |pullCoef a A X| * exp (κ' * spread dist X) ≤
      ∑ Z : Fin X.1 → ι, a' ⟨X.1, Z⟩ * ∏ l, A' (Z l) (X.2 l) := by
    intro X
    have habs : |pullCoef a A X| ≤ ∑ Z : Fin X.1 → ι, |a ⟨X.1, Z⟩| * ∏ l, |A (Z l) (X.2 l)| := by
      unfold pullCoef
      refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq (Finset.sum_congr rfl fun Z _ => ?_))
      rw [abs_mul, Finset.abs_prod]
    refine (mul_le_mul_of_nonneg_right habs (exp_pos _).le).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun Z _ => ?_
    have hw := spread_le dist hsymm htri X.2 Z
    have hexp : exp (κ' * spread dist X) ≤
        exp (κ' * spread dist (⟨X.1, Z⟩ : MonoIdx ι D)) * ∏ l, exp (2 * D * κ' * dist (Z l) (X.2 l)) := by
      rw [← exp_sum, ← exp_add]
      refine exp_le_exp.mpr ?_
      have hpD : ((X.1 : ℕ) : ℝ) ≤ D := by exact_mod_cast Nat.lt_succ_iff.mp X.1.isLt
      have hsum0 : 0 ≤ ∑ l, dist (Z l) (X.2 l) := Finset.sum_nonneg fun l _ => hd0 _ _
      have h2 : ∑ l, 2 * (D : ℝ) * κ' * dist (Z l) (X.2 l) = 2 * D * κ' * ∑ l, dist (Z l) (X.2 l) := by
        rw [Finset.mul_sum]
      rw [h2]
      unfold spread
      simp only
      nlinarith [mul_le_mul_of_nonneg_left hw hκ, mul_le_mul_of_nonneg_right hpD (mul_nonneg hκ hsum0)]
    calc |a ⟨X.1, Z⟩| * (∏ l, |A (Z l) (X.2 l)|) * exp (κ' * spread dist X)
        ≤ |a ⟨X.1, Z⟩| * (∏ l, |A (Z l) (X.2 l)|) *
          (exp (κ' * spread dist (⟨X.1, Z⟩ : MonoIdx ι D)) * ∏ l, exp (2 * D * κ' * dist (Z l) (X.2 l))) :=
          mul_le_mul_of_nonneg_left hexp (mul_nonneg (abs_nonneg _) (Finset.prod_nonneg fun l _ => abs_nonneg _))
      _ = a' ⟨X.1, Z⟩ * ∏ l, A' (Z l) (X.2 l) := by
          simp only [ha', hA', Finset.prod_mul_distrib]
          ring
  calc ∑ X ∈ Finset.univ.filter (fun X : MonoIdx ι D => y ∈ monoSupp X), |pullCoef a A X| * exp (κ' * spread dist X)
      ≤ ∑ X ∈ Finset.univ.filter (fun X : MonoIdx ι D => y ∈ monoSupp X),
          ∑ Z : Fin X.1 → ι, a' ⟨X.1, Z⟩ * ∏ l, A' (Z l) (X.2 l) := Finset.sum_le_sum fun X _ => hpoint X
    _ ≤ ((D + 1) ^ 2 : ℕ) * K ^ D * aS :=
        sum_site_pull_le a' (fun Z => mul_nonneg (abs_nonneg _) (exp_pos _).le) A'
          (fun z x => mul_nonneg (abs_nonneg _) (exp_pos _).le) hK hrow hcol haS y

end GaussianBlockSpin
