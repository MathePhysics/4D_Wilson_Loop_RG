import GaussianBlockSpin.RestrictedLaw

/-! Moments of monomials under a product measure on `ι → ℝ` (independent coordinates):
* monoVal: the monomial `ξ_{y_1} ⋯ ξ_{y_p}` of a tuple of coordinates; prod_monoVal_eq: a product of monomials is
  `∏_c ξ_c^{e_c}` with the exponents `e_c` counting the occurrences of `c`;
* integral_prod_monoVal: its integral is `∏_c ∫ x^{e_c} dν_c` (Fubini, no integrability needed);
* abs_prod_sub_prod_le: `|∏ a_c - ∏ b_c| ≤ Σ_c |a_c - b_c| ∏_{c' ≠ c} M_{c'}` for `|a_c|, |b_c| ≤ M_c`. -/

namespace GaussianBlockSpin

open MeasureTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The monomial of a tuple of coordinates. -/
def monoVal {p : ℕ} (y : Fin p → ι) (ξ : ι → ℝ) : ℝ := ∏ l, ξ (y l)

/-- The exponent of the coordinate `c` in the product of the monomials `g i`, `i ∈ U`. -/
def expoOf {k : ℕ} (g : Fin k → Σ p : ℕ, Fin p → ι) (U : Finset (Fin k)) (c : ι) : ℕ :=
  ∑ i ∈ U, (Finset.univ.filter fun l => (g i).2 l = c).card

lemma monoVal_eq_prod {p : ℕ} (y : Fin p → ι) (ξ : ι → ℝ) :
    monoVal y ξ = ∏ c, ξ c ^ (Finset.univ.filter fun l => y l = c).card := by
  unfold monoVal
  rw [← Finset.prod_fiberwise Finset.univ y (fun l => ξ (y l))]
  refine Finset.prod_congr rfl fun c _ => ?_
  rw [Finset.prod_congr rfl fun l hl => by rw [(Finset.mem_filter.mp hl).2], Finset.prod_const]

/-- A product of monomials is `∏_c ξ_c^{e_c}`. -/
lemma prod_monoVal_eq {k : ℕ} (g : Fin k → Σ p : ℕ, Fin p → ι) (U : Finset (Fin k)) (ξ : ι → ℝ) :
    ∏ i ∈ U, monoVal (g i).2 ξ = ∏ c, ξ c ^ expoOf g U c := by
  simp_rw [monoVal_eq_prod, expoOf]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun c _ => ?_
  rw [Finset.prod_pow_eq_pow_sum]

/-- **Moments of monomials factorise over the coordinates** under a product measure. -/
lemma integral_prod_monoVal (ν₁ : ι → Measure ℝ) [∀ i, SigmaFinite (ν₁ i)] {k : ℕ}
    (g : Fin k → Σ p : ℕ, Fin p → ι) (U : Finset (Fin k)) :
    ∫ ξ, ∏ i ∈ U, monoVal (g i).2 ξ ∂(Measure.pi ν₁) = ∏ c, ∫ x, x ^ expoOf g U c ∂(ν₁ c) := by
  simp_rw [prod_monoVal_eq]
  exact integral_fintype_prod_eq_prod (fun c x => x ^ expoOf g U c)

omit [Fintype ι] in
/-- **Telescoping**: `|∏_{c ∈ s} a_c - ∏_{c ∈ s} b_c| ≤ Σ_{c ∈ s} |a_c - b_c| ∏_{c' ∈ s, c' ≠ c} M_{c'}` when
`|a_c|, |b_c| ≤ M_c`. -/
lemma abs_prod_sub_prod_le (s : Finset ι) (a b M : ι → ℝ) (ha : ∀ c ∈ s, |a c| ≤ M c)
    (hb : ∀ c ∈ s, |b c| ≤ M c) :
    |∏ c ∈ s, a c - ∏ c ∈ s, b c| ≤ ∑ c ∈ s, |a c - b c| * ∏ c' ∈ s.erase c, M c' := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert c0 s hc0 ih =>
    have ha' : ∀ c ∈ s, |a c| ≤ M c := fun c hc => ha c (Finset.mem_insert_of_mem hc)
    have hb' : ∀ c ∈ s, |b c| ≤ M c := fun c hc => hb c (Finset.mem_insert_of_mem hc)
    have hM0 : 0 ≤ M c0 := (abs_nonneg _).trans (ha c0 (Finset.mem_insert_self _ _))
    have hMs : ∀ c ∈ s, 0 ≤ M c := fun c hc => (abs_nonneg _).trans (ha' c hc)
    rw [Finset.prod_insert hc0, Finset.prod_insert hc0, Finset.sum_insert hc0, Finset.erase_insert hc0]
    have hsplit : a c0 * ∏ c ∈ s, a c - b c0 * ∏ c ∈ s, b c =
        (a c0 - b c0) * ∏ c ∈ s, b c + a c0 * (∏ c ∈ s, a c - ∏ c ∈ s, b c) := by ring
    rw [hsplit]
    have hbprod : |∏ c ∈ s, b c| ≤ ∏ c ∈ s, M c := by
      rw [Finset.abs_prod]; exact Finset.prod_le_prod₀ (fun c _ => abs_nonneg _) hb'
    have herase : ∀ c ∈ s, (insert c0 s).erase c = insert c0 (s.erase c) := fun c hc => by
      have hne : c0 ≠ c := fun h => hc0 (h ▸ hc)
      exact Finset.erase_insert_of_ne hne
    calc |(a c0 - b c0) * ∏ c ∈ s, b c + a c0 * (∏ c ∈ s, a c - ∏ c ∈ s, b c)|
        ≤ |a c0 - b c0| * |∏ c ∈ s, b c| + |a c0| * |∏ c ∈ s, a c - ∏ c ∈ s, b c| := by
          rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      _ ≤ |a c0 - b c0| * ∏ c ∈ s, M c + M c0 * ∑ c ∈ s, |a c - b c| * ∏ c' ∈ s.erase c, M c' := by
          gcongr
          · exact ha c0 (Finset.mem_insert_self _ _)
          · exact ih ha' hb'
      _ = |a c0 - b c0| * ∏ c ∈ s, M c + ∑ c ∈ s, |a c - b c| * ∏ c' ∈ (insert c0 s).erase c, M c' := by
          rw [Finset.mul_sum]
          congr 1
          refine Finset.sum_congr rfl fun c hc => ?_
          rw [herase c hc, Finset.prod_insert (fun h => hc0 (Finset.mem_of_mem_erase h))]
          ring

end GaussianBlockSpin
