import GaussianBlockSpin.GaussChangeOfVariables

/-! Gaussian laws of pairs of fields:
* gaussPush_eq_of_sq: two symmetric square roots `A`, `B` of `Q⁻¹` (`A A = B B = Q⁻¹`) give the same law
  `A_* N(0,1)^{⊗ι} = B_* N(0,1)^{⊗ι}` (the densities agree);
* dotProduct_fromBlocks, dotProduct_self_sum, inv_fromBlocks_diag: quadratic forms and inverses of block-diagonal
  matrices;
* gaussPush_fromBlocks: for a block-diagonal `A = diag(A₁, A₂)` on `ι₁ ⊕ ι₂`, the law, split into the two blocks, is
  the product of the two laws. -/

namespace GaussianBlockSpin

open MeasureTheory ProbabilityTheory Real Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Two symmetric square roots of `Q⁻¹` give the same Gaussian law.** -/
theorem gaussPush_eq_of_sq {A B Q : Matrix ι ι ℝ} (hA : Aᵀ = A) (hAA : A * A = Q⁻¹) (hB : Bᵀ = B)
    (hBB : B * B = Q⁻¹) (hQ : IsUnit Q.det) : gaussPush A = gaussPush B := by
  rw [gaussPush_eq_withDensity hA hAA hQ, gaussPush_eq_withDensity hB hBB hQ]
  have hdet : |A.det| = |B.det| := by
    have h1 : A.det * A.det = B.det * B.det := by rw [← det_mul, ← det_mul, hAA, hBB]
    have h2 : |A.det| ^ 2 = |B.det| ^ 2 := by rw [sq_abs, sq_abs, sq, sq, h1]
    exact (pow_left_inj₀ (abs_nonneg _) (abs_nonneg _) two_ne_zero).mp h2
  rw [hdet]

variable {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]

omit [DecidableEq ι₁] [DecidableEq ι₂] in
/-- The quadratic form of a block-diagonal matrix. -/
lemma dotProduct_fromBlocks (Q₁ : Matrix ι₁ ι₁ ℝ) (Q₂ : Matrix ι₂ ι₂ ℝ) (v : ι₁ ⊕ ι₂ → ℝ) :
    v ⬝ᵥ fromBlocks Q₁ 0 0 Q₂ *ᵥ v =
      (fun i => v (Sum.inl i)) ⬝ᵥ Q₁ *ᵥ (fun i => v (Sum.inl i)) +
        (fun i => v (Sum.inr i)) ⬝ᵥ Q₂ *ᵥ (fun i => v (Sum.inr i)) := by
  rw [fromBlocks_mulVec]
  simp only [zero_mulVec, add_zero, zero_add, dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
  rfl

omit [DecidableEq ι₁] [DecidableEq ι₂] in
lemma dotProduct_self_sum (v : ι₁ ⊕ ι₂ → ℝ) :
    v ⬝ᵥ v = (fun i => v (Sum.inl i)) ⬝ᵥ (fun i => v (Sum.inl i)) +
      (fun i => v (Sum.inr i)) ⬝ᵥ (fun i => v (Sum.inr i)) := by
  simp only [dotProduct, Fintype.sum_sum_type]

/-- The inverse of a block-diagonal matrix. -/
lemma inv_fromBlocks_diag {Q₁ : Matrix ι₁ ι₁ ℝ} {Q₂ : Matrix ι₂ ι₂ ℝ} (h₁ : IsUnit Q₁.det) (h₂ : IsUnit Q₂.det) :
    (fromBlocks Q₁ 0 0 Q₂)⁻¹ = fromBlocks Q₁⁻¹ 0 0 Q₂⁻¹ := by
  refine inv_eq_left_inv ?_
  rw [fromBlocks_multiply]
  simp [nonsing_inv_mul _ h₁, nonsing_inv_mul _ h₂, fromBlocks_one]

omit [DecidableEq ι₁] [DecidableEq ι₂] in
/-- **Block-diagonal laws are products**: splitting `ι₁ ⊕ ι₂ → ℝ` into its two blocks maps the law of
`diag(A₁, A₂) ξ` to the product of the laws of `A₁ ξ₁` and `A₂ ξ₂`. -/
theorem gaussPush_fromBlocks (A₁ : Matrix ι₁ ι₁ ℝ) (A₂ : Matrix ι₂ ι₂ ℝ) :
    (gaussPush (fromBlocks A₁ 0 0 A₂)).map (MeasurableEquiv.sumPiEquivProdPi fun _ : ι₁ ⊕ ι₂ => ℝ) =
      (gaussPush A₁).prod (gaussPush A₂) := by
  set e := MeasurableEquiv.sumPiEquivProdPi fun _ : ι₁ ⊕ ι₂ => ℝ with he
  have hmp : MeasurePreserving e (Measure.pi fun _ : ι₁ ⊕ ι₂ => gaussianReal 0 1)
      ((Measure.pi fun _ : ι₁ => gaussianReal 0 1).prod (Measure.pi fun _ : ι₂ => gaussianReal 0 1)) :=
    measurePreserving_sumPiEquivProdPi (fun _ : ι₁ ⊕ ι₂ => gaussianReal 0 1)
  have hm1 := measurable_mulVec A₁
  have hm2 := measurable_mulVec A₂
  have hmB := measurable_mulVec (fromBlocks A₁ 0 0 A₂)
  have hcomm : (e ∘ fun ξ => fromBlocks A₁ 0 0 A₂ *ᵥ ξ) =
      (Prod.map (fun ξ₁ => A₁ *ᵥ ξ₁) (fun ξ₂ => A₂ *ᵥ ξ₂)) ∘ e := by
    funext ξ
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
    · show (fromBlocks A₁ 0 0 A₂ *ᵥ ξ) (Sum.inl i) = (A₁ *ᵥ fun j => ξ (Sum.inl j)) i
      rw [fromBlocks_mulVec]; simp; rfl
    · show (fromBlocks A₁ 0 0 A₂ *ᵥ ξ) (Sum.inr i) = (A₂ *ᵥ fun j => ξ (Sum.inr j)) i
      rw [fromBlocks_mulVec]; simp; rfl
  unfold gaussPush
  rw [Measure.map_map e.measurable hmB, hcomm, ← Measure.map_map (hm1.prodMap hm2) e.measurable, hmp.map_eq,
    ← Measure.map_prod_map _ _ hm1 hm2]

end GaussianBlockSpin
