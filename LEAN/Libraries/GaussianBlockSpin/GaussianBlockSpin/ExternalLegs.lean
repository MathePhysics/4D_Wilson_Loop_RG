import GaussianBlockSpin.GaussianGraphs

/-! **External legs and explicit vertices.** A polynomial at a shifted point `x₀ + y` is a polynomial in `y` whose
monomials are the pairs `(a, S)`: the legs in `S` stay (internal legs, to be paired by the Gaussian), the others give
the factors `⟪u, x₀⟫` (external legs) (monomial_add_eq_sum, sum_monomial_add_eq; shiftCoeff, shiftDeg, shiftLegs);
with `x₀` a sum of fields the external legs are labelled by the summands (shiftCoeff_sum_eq). The
vector of a leg given as a linear functional (legVec, by the Riesz representation). Coordinates of operators on `ℝ^N`
(apply_eq_sum_single, inner_eq_sum_coord, inner_apply_eq_sum). Ordered pairs of a symmetric sum regrouped into unordered
pairs with the weights `c` and `c/2` (half_sum_range_eq_pairs). Used for the vertices and graphs of Bałaban III
(1.4)-(1.18). -/

open scoped RealInnerProductSpace
open Finset.HasAntidiagonal

namespace GaussianBlockSpin

section Shift

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {A : Type*}

/-- The coefficient of the shifted monomial `(a, S)`: `c_a ∏_{i ∉ S} ⟪u_{a,i}, x₀⟫` (the legs outside `S` external). -/
noncomputable def shiftCoeff (c : A → ℝ) (k : A → ℕ) (u : ∀ a, Fin (k a) → E) (x₀ : E)
    (p : Σ a, Finset (Fin (k a))) : ℝ :=
  c p.1 * ∏ i ∈ p.2ᶜ, ⟪u p.1 i, x₀⟫

/-- The degree of the shifted monomial `(a, S)`: the number `|S|` of internal legs. -/
def shiftDeg (k : A → ℕ) (p : Σ a, Finset (Fin (k a))) : ℕ := p.2.card

/-- The internal legs of the shifted monomial `(a, S)`: the legs of `a` in `S`, in increasing order. -/
noncomputable def shiftLegs (k : A → ℕ) (u : ∀ a, Fin (k a) → E) (p : Σ a, Finset (Fin (k a))) :
    Fin (shiftDeg k p) → E :=
  fun j => u p.1 (p.2.orderEmbOfFin rfl j)

lemma prod_orderEmbOfFin {M : Type*} [CommMonoid M] {m : ℕ} (s : Finset (Fin m)) (f : Fin m → M) :
    ∏ j : Fin s.card, f (s.orderEmbOfFin rfl j) = ∏ i ∈ s, f i := by
  rw [← Finset.prod_coe_sort s f]
  exact Fintype.prod_equiv (s.orderIsoOfFin rfl).toEquiv _ _ fun j => by simp

/-- **A monomial at a shifted point**: `c_a ∏_i ⟪u_{a,i}, x₀ + y⟫` is the sum over the sets `S` of internal legs of
`c_a ∏_{i ∉ S} ⟪u_{a,i}, x₀⟫ ∏_{i ∈ S} ⟪u_{a,i}, y⟫`. -/
lemma monomial_add_eq_sum (c : A → ℝ) (k : A → ℕ) (u : ∀ a, Fin (k a) → E) (x₀ y : E) (a : A) :
    monomial c k u a (x₀ + y) =
      ∑ S : Finset (Fin (k a)), monomial (shiftCoeff c k u x₀) (shiftDeg k) (shiftLegs k u) ⟨a, S⟩ y := by
  unfold monomial shiftCoeff shiftLegs shiftDeg
  simp only [inner_add_right]
  rw [show (∏ i, (⟪u a i, x₀⟫ + ⟪u a i, y⟫)) = ∏ i, (⟪u a i, y⟫ + ⟪u a i, x₀⟫) from
    Finset.prod_congr rfl fun i _ => add_comm _ _, Finset.prod_add, Finset.powerset_univ, Finset.mul_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [prod_orderEmbOfFin S (fun i => ⟪u a i, y⟫), Finset.compl_eq_univ_sdiff]
  ring

/-- **A polynomial at a shifted point** is a polynomial with the shifted monomials `(a, S)`. -/
lemma sum_monomial_add_eq [Fintype A] (c : A → ℝ) (k : A → ℕ) (u : ∀ a, Fin (k a) → E) (x₀ y : E) :
    ∑ a, monomial c k u a (x₀ + y) =
      ∑ p : Σ a, Finset (Fin (k a)), monomial (shiftCoeff c k u x₀) (shiftDeg k) (shiftLegs k u) p y := by
  rw [Fintype.sum_sigma]
  exact Finset.sum_congr rfl fun a _ => monomial_add_eq_sum c k u x₀ y a

/-- **External legs at a sum of fields**: with `x₀ = Σ_x f_x`, a shifted monomial is the sum over the labellings `μ`
of its external legs of `c_a ∏_{i ∉ S} ⟪u_{a,i}, f_{μ i}⟫`. -/
lemma shiftCoeff_sum_eq {X : Type*} [Fintype X] (c : A → ℝ) (k : A → ℕ) (u : ∀ a, Fin (k a) → E) (f : X → E)
    (p : Σ a, Finset (Fin (k a))) :
    shiftCoeff c k u (∑ x, f x) p = ∑ μ : ↥(p.2ᶜ) → X, c p.1 * ∏ i, ⟪u p.1 i.1, f (μ i)⟫ := by
  unfold shiftCoeff
  rw [← Finset.prod_coe_sort]
  simp only [inner_sum]
  rw [Fintype.prod_sum, Finset.mul_sum]

/-- The vector of a leg `ℓ` (Riesz): `⟪legVec ℓ, x⟫ = ℓ x`. -/
noncomputable def legVec [FiniteDimensional ℝ E] (ℓ : E →ₗ[ℝ] ℝ) : E :=
  (InnerProductSpace.toDual ℝ E).symm (LinearMap.toContinuousLinearMap ℓ)

lemma inner_legVec [FiniteDimensional ℝ E] (ℓ : E →ₗ[ℝ] ℝ) (x : E) : ⟪legVec ℓ, x⟫ = ℓ x := by
  simp [legVec, InnerProductSpace.toDual_symm_apply]

end Shift

section Coordinates

/-- **Coordinates of an operator on `ℝ^N`**: `(M w)_a = Σ_{a'} M_{a a'} w_{a'}`, `M_{a a'} = (M e_{a'})_a`. -/
lemma apply_eq_sum_single {N : ℕ} (M : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N))
    (w : EuclideanSpace ℝ (Fin N)) (a : Fin N) :
    M w a = ∑ a', M (EuclideanSpace.single a' 1) a * w a' := by
  conv_lhs => rw [← (EuclideanSpace.basisFun (Fin N) ℝ).sum_repr w]
  simp [map_sum, map_smul, mul_comm]

/-- `⟪v, w⟫ = Σ_a v_a w_a` on `ℝ^N`. -/
lemma inner_eq_sum_coord {N : ℕ} (v w : EuclideanSpace ℝ (Fin N)) : ⟪v, w⟫ = ∑ a, v a * w a := by
  simp [PiLp.inner_apply, mul_comm]

/-- `⟪v, M w⟫ = Σ_{a, a'} v_a M_{a a'} w_{a'}` on `ℝ^N`. -/
lemma inner_apply_eq_sum {N : ℕ} (M : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N))
    (v w : EuclideanSpace ℝ (Fin N)) :
    ⟪v, M w⟫ = ∑ a, ∑ a', v a * M (EuclideanSpace.single a' 1) a * w a' := by
  rw [inner_eq_sum_coord]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [apply_eq_sum_single, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a' _ => by ring

end Coordinates

section Pairs

/-- **Ordered pairs regrouped into unordered pairs**: for `g` symmetric and `n ≥ 1`,
`(c/2) Σ_{m ≤ n} g(m, n - m) = c g(0, n) + Σ_{m + m' = n, 1 ≤ m ≤ m'} (c/2 if m = m', else c) g(m, m')`. -/
lemma half_sum_range_eq_pairs (c : ℝ) {n : ℕ} (hn : 1 ≤ n) (g : ℕ → ℕ → ℝ) (hg : ∀ m m', g m m' = g m' m) :
    c / 2 * ∑ m ∈ Finset.range (n + 1), g m (n - m) =
      c * g 0 n + ∑ p ∈ (antidiagonal n).filter (fun p : ℕ × ℕ => 1 ≤ p.1 ∧ p.1 ≤ p.2),
        (if p.1 = p.2 then c / 2 else c) * g p.1 p.2 := by
  set w : ℕ × ℕ → ℝ := fun p => (if p = (0, n) then c else 0) +
    (if 1 ≤ p.1 ∧ p.1 ≤ p.2 then (if p.1 = p.2 then c / 2 else c) else 0) with hw
  have hR : c * g 0 n + ∑ p ∈ (antidiagonal n).filter (fun p : ℕ × ℕ => 1 ≤ p.1 ∧ p.1 ≤ p.2),
      (if p.1 = p.2 then c / 2 else c) * g p.1 p.2 = ∑ p ∈ antidiagonal n, w p * g p.1 p.2 := by
    simp only [hw, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul, Finset.sum_filter]
    congr 1
    rw [Finset.sum_ite_eq' (antidiagonal n) (0, n) (fun p => c * g p.1 p.2)]
    simp
  have hswap : ∑ p ∈ antidiagonal n, w p * g p.1 p.2 = ∑ p ∈ antidiagonal n, w p.swap * g p.1 p.2 := by
    rw [← Finset.Nat.sum_antidiagonal_swap]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [Prod.fst_swap, Prod.snd_swap]
    rw [hg]
  have hpt : ∀ p ∈ antidiagonal n, w p + w p.swap = c := by
    intro p hp
    rw [mem_antidiagonal] at hp
    obtain ⟨m, m'⟩ := p
    simp only [hw, Prod.swap_prod_mk, Prod.mk.injEq] at hp ⊢
    split_ifs <;> first | (exfalso; omega) | ring
  have h2 : 2 * ∑ p ∈ antidiagonal n, w p * g p.1 p.2 = c * ∑ p ∈ antidiagonal n, g p.1 p.2 := by
    rw [two_mul]
    nth_rewrite 2 [hswap]
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [← add_mul, hpt p hp]
  have hrange := Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk (fun p => g p.1 p.2) n
  simp only at hrange
  rw [hR, ← hrange]
  linarith

end Pairs

end GaussianBlockSpin
