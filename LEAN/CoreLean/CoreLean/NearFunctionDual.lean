/-
`lem:near-function` of BALABAN_CORE.tex (`a021c13be348`), the step "(c): the kernel on ℤ⁴" of its proof.

* `mono_linearIndependent`: the monomials `n ↦ n^γ`, `γ` with every exponent at most `3` (in particular `|γ| ≤ 3`),
  restricted to the grid `{0, 1, 2, 3}⁴`, are linearly independent: a polynomial of degree at most three in each
  variable which vanishes on `{0, 1, 2, 3}⁴` vanishes (the combinatorial Nullstellensatz,
  `MvPolynomial.eq_zero_of_eval_zero_at_prod_finset`).
* `dual_functions`: hence there are functions `φ_γ` on `{0, 1, 2, 3}⁴` with `Σ_n n^{γ'}φ_γ(n) = δ_{γγ'}`, built from
  the inverse of the Gram matrix of the monomials.
* `moment_correction`: for moments `m_{γ'}` (linear functionals) with `m_{γ'}(φ_γ) = δ_{γγ'}`, the kernel
  `K = K̃ - Σ_γ m_γ(K̃)φ_γ` has `m_{γ'}(K) = 0`.
-/
import Mathlib

open MvPolynomial Matrix

noncomputable section

namespace CoreLean
namespace NearFunctionDual

/-- The points of the grid `{0, 1, 2, 3}⁴`. -/
abbrev Pt := Fin 4 → Fin 4

/-- The monomial `n^γ` on the grid. -/
def mono (γ : Fin 4 →₀ ℕ) (n : Pt) : ℝ := ∏ i, ((n i : ℕ) : ℝ) ^ γ i

/-- The grid points as real numbers. -/
def S (_ : Fin 4) : Finset ℝ := Finset.image (fun k : Fin 4 => ((k : ℕ) : ℝ)) Finset.univ

lemma card_S (i : Fin 4) : (S i).card = 4 := by
  rw [S, Finset.card_image_of_injective _ (fun a b h => Fin.ext (by exact_mod_cast h))]
  simp

/-- **The monomials are linearly independent on the grid.** -/
theorem mono_linearIndependent (Γ : Finset (Fin 4 →₀ ℕ)) (hΓ : ∀ γ ∈ Γ, ∀ i, γ i ≤ 3) :
    LinearIndependent ℝ (fun γ : Γ => mono γ) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg γ₀
  set P : MvPolynomial (Fin 4) ℝ := ∑ γ : Γ, monomial (γ : Fin 4 →₀ ℕ) (g γ)
  -- `P` vanishes on the grid
  have heval : ∀ x : Fin 4 → ℝ, (∀ i, x i ∈ S i) → eval x P = 0 := by
    intro x hx
    choose n hn using fun i => Finset.mem_image.1 (hx i)
    have hxn : x = fun i => (((n i : Fin 4) : ℕ) : ℝ) := funext fun i => (hn i).2.symm
    have := congrFun hg (fun i => n i)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, mono] at this
    rw [hxn]
    simp only [P, map_sum, eval_monomial]
    rw [← this]
    refine Finset.sum_congr rfl fun γ _ => ?_
    rw [Finsupp.prod_fintype _ _ (fun i => pow_zero _)]
  -- the degrees
  have hdeg : ∀ i, P.degreeOf i < (S i).card := by
    intro i
    rw [card_S]
    have : P.degreeOf i ≤ 3 := by
      rw [degreeOf_le_iff]
      intro m hm
      have hm' := Finset.mem_of_subset (support_sum) hm
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and] at hm'
      obtain ⟨γ, hγ⟩ := hm'
      have := support_monomial_subset hγ
      rw [Finset.mem_singleton] at this
      rw [this]
      exact hΓ γ γ.2 i
    omega
  have hP := eq_zero_of_eval_zero_at_prod_finset P S hdeg heval
  have hc := congrArg (MvPolynomial.lcoeff ℝ (γ₀ : Fin 4 →₀ ℕ)) hP
  simp only [P, map_sum, MvPolynomial.lcoeff_apply, coeff_monomial, map_zero] at hc
  rw [Finset.sum_eq_single γ₀ (fun γ _ hne => by
    rw [if_neg]; exact fun h => hne (Subtype.ext h)) (by simp)] at hc
  simpa using hc

/-- **The dual functions**: `Σ_n n^{γ'}φ_γ(n) = δ_{γγ'}`. -/
theorem dual_functions (Γ : Finset (Fin 4 →₀ ℕ)) (hΓ : ∀ γ ∈ Γ, ∀ i, γ i ≤ 3) :
    ∃ φ : Γ → Pt → ℝ, ∀ γ γ' : Γ, ∑ n, mono γ' n * φ γ n = if γ = γ' then 1 else 0 := by
  set v : Γ → EuclideanSpace ℝ Pt := fun γ => WithLp.toLp 2 (mono γ)
  have hli : LinearIndependent ℝ v := by
    have h := mono_linearIndependent Γ hΓ
    exact h.map' (WithLp.linearEquiv 2 ℝ (Pt → ℝ)).symm.toLinearMap (LinearEquiv.ker _)
  set G := gram ℝ v
  have hG : G.det ≠ 0 := det_gram_ne_zero_iff_linearIndependent.2 hli
  have hGu : IsUnit G.det := isUnit_iff_ne_zero.2 hG
  have hinner : ∀ γ γ' : Γ, ∑ n, mono γ' n * mono γ n = G γ γ' := fun γ γ' => by
    simp only [G, gram_apply, v, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, star_trivial]
  refine ⟨fun γ n => ∑ γ'', G⁻¹ γ γ'' * mono γ'' n, fun γ γ' => ?_⟩
  have hsym : ∀ a b, G a b = G b a := fun a b => by
    simp only [G, gram_apply]; exact real_inner_comm _ _
  calc ∑ n, mono γ' n * ∑ γ'', G⁻¹ γ γ'' * mono γ'' n
      = ∑ γ'', G⁻¹ γ γ'' * ∑ n, mono γ' n * mono γ'' n := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun γ'' _ => Finset.sum_congr rfl fun n _ => by ring
    _ = ∑ γ'', G⁻¹ γ γ'' * G γ'' γ' := by
        refine Finset.sum_congr rfl fun γ'' _ => ?_
        rw [hinner γ'' γ']
    _ = (G⁻¹ * G) γ γ' := by rw [Matrix.mul_apply]
    _ = if γ = γ' then 1 else 0 := by
        rw [Matrix.nonsing_inv_mul G hGu, Matrix.one_apply]

/-- **The correction of the moments**: `m_{γ'}(K̃ - Σ_γ m_γ(K̃)φ_γ) = 0`. -/
theorem moment_correction {V Γ : Type*} [AddCommGroup V] [Module ℝ V] [Fintype Γ] [DecidableEq Γ]
    (m : Γ → V →ₗ[ℝ] ℝ) (φ : Γ → V) (hφ : ∀ γ γ', m γ' (φ γ) = if γ = γ' then 1 else 0) (K : V) (γ' : Γ) :
    m γ' (K - ∑ γ, m γ K • φ γ) = 0 := by
  rw [map_sub, map_sum]
  simp only [map_smul, hφ, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq']
  simp

end NearFunctionDual
end CoreLean

end
