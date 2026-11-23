import GaussianBlockSpin.InvSqrtLaws

/-! **A normalised Gaussian field measure in unit-scale coordinates** (gaussProb_eq_map_unit): if the matrix of the
precision is `fieldMatrix T = c Q` (`c > 0`) with `γ₀ ≤ Q ≤ γ₁`, then `gaussProb T` is the image of
`A_* N(0,1)^{⊗(ι' × κ)}`, `A = invSqrt Q γ₁`, under `z ↦ φ(c^{-1/2} z)`; and the product of two such measures is the
image of the block-diagonal law (prod_gaussProb_eq_map). -/

namespace GaussianBlockSpin

open MeasureTheory ProbabilityTheory Real Matrix
open scoped RealInnerProductSpace Matrix.Norms.L2Operator

variable {ι' κ : Type*} [Fintype ι'] [DecidableEq ι'] [Fintype κ] [DecidableEq κ]

/-- **A normalised Gaussian field measure in unit-scale coordinates.** -/
theorem gaussProb_eq_map_unit {T : PiLp 2 (fun _ : ι' => EuclideanSpace ℝ κ) →ₗ[ℝ] PiLp 2 (fun _ : ι' => EuclideanSpace ℝ κ)}
    (hT : T.IsSymmetric) (hpos : ∀ x, x ≠ 0 → 0 < ⟪x, T x⟫) {c : ℝ} (hc : 0 < c) {Q : Matrix (ι' × κ) (ι' × κ) ℝ}
    (hQ : Qᵀ = Q) (hTQ : fieldMatrix T = c • Q) {γ₀ γ₁ : ℝ} (hγ₀ : 0 < γ₀) (hγ₀₁ : γ₀ ≤ γ₁)
    (hlo : ∀ v, γ₀ * (v ⬝ᵥ v) ≤ v ⬝ᵥ Q *ᵥ v) (hhi : ∀ v, v ⬝ᵥ Q *ᵥ v ≤ γ₁ * (v ⬝ᵥ v)) :
    gaussProb T = (gaussPush (invSqrt Q γ₁)).map fun z => fieldCoord ((Real.sqrt c)⁻¹ • z) := by
  have hQT : ∀ z, ⟪(fieldCoord z : PiLp 2 (fun _ : ι' => EuclideanSpace ℝ κ)), T (fieldCoord z)⟫ =
      z ⬝ᵥ (c • Q) *ᵥ z := fun z => by rw [← hTQ, dotProduct_fieldMatrix]
  have hmp := measurePreserving_fieldCoord (ι := ι') (κ := κ)
  have h := gaussProb_eq_map_gaussPush (fieldCoord (ι := ι') (κ := κ)) hmp hT hpos (Q := c • Q)
    (A := (Real.sqrt c)⁻¹ • invSqrt Q γ₁) hQT
  obtain ⟨hAs, hAA, hQu⟩ := invSqrt_facts hQ hγ₀ hγ₀₁ hlo hhi
  have hB : ((Real.sqrt c)⁻¹ • invSqrt Q γ₁)ᵀ = (Real.sqrt c)⁻¹ • invSqrt Q γ₁ := by rw [transpose_smul, hAs]
  have hQc : IsUnit (c • Q).det := by
    rw [det_smul]
    exact isUnit_iff_ne_zero.mpr (mul_ne_zero (pow_ne_zero _ hc.ne') hQu.ne_zero)
  have hBB : ((Real.sqrt c)⁻¹ • invSqrt Q γ₁) * ((Real.sqrt c)⁻¹ • invSqrt Q γ₁) = (c • Q)⁻¹ := by
    rw [smul_mul_smul_comm, hAA, inv_smul_of_ne hQu hc.ne', ← mul_inv, Real.mul_self_sqrt hc.le]
  rw [h hB hBB hQc, gaussPush_smul, Measure.map_map hmp.measurable (measurable_const_smul _)]
  rfl

variable {ι₁ κ₁ ι₂ κ₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype κ₁] [DecidableEq κ₁]
  [Fintype ι₂] [DecidableEq ι₂] [Fintype κ₂] [DecidableEq κ₂]

/-- The unit-scale coordinate map of a pair of fields. -/
noncomputable def pairUnitMap (c : ℝ) (z : (ι₁ × κ₁) ⊕ (ι₂ × κ₂) → ℝ) :
    PiLp 2 (fun _ : ι₁ => EuclideanSpace ℝ κ₁) × PiLp 2 (fun _ : ι₂ => EuclideanSpace ℝ κ₂) :=
  (fieldCoord ((Real.sqrt c)⁻¹ • fun i => z (Sum.inl i)), fieldCoord ((Real.sqrt c)⁻¹ • fun i => z (Sum.inr i)))

/-- **The product of two normalised Gaussian field measures** in unit-scale coordinates. -/
theorem prod_gaussProb_eq_map
    {T₁ : PiLp 2 (fun _ : ι₁ => EuclideanSpace ℝ κ₁) →ₗ[ℝ] PiLp 2 (fun _ : ι₁ => EuclideanSpace ℝ κ₁)}
    {T₂ : PiLp 2 (fun _ : ι₂ => EuclideanSpace ℝ κ₂) →ₗ[ℝ] PiLp 2 (fun _ : ι₂ => EuclideanSpace ℝ κ₂)}
    (hT₁ : T₁.IsSymmetric) (hpos₁ : ∀ x, x ≠ 0 → 0 < ⟪x, T₁ x⟫) (hT₂ : T₂.IsSymmetric)
    (hpos₂ : ∀ x, x ≠ 0 → 0 < ⟪x, T₂ x⟫) {c : ℝ} (hc : 0 < c) {Q₁ : Matrix (ι₁ × κ₁) (ι₁ × κ₁) ℝ}
    {Q₂ : Matrix (ι₂ × κ₂) (ι₂ × κ₂) ℝ} (hQ₁ : Q₁ᵀ = Q₁) (hQ₂ : Q₂ᵀ = Q₂) (hTQ₁ : fieldMatrix T₁ = c • Q₁)
    (hTQ₂ : fieldMatrix T₂ = c • Q₂) {γ₀ γ₁ : ℝ} (hγ₀ : 0 < γ₀) (hγ₀₁ : γ₀ ≤ γ₁)
    (hlo₁ : ∀ v, γ₀ * (v ⬝ᵥ v) ≤ v ⬝ᵥ Q₁ *ᵥ v) (hhi₁ : ∀ v, v ⬝ᵥ Q₁ *ᵥ v ≤ γ₁ * (v ⬝ᵥ v))
    (hlo₂ : ∀ v, γ₀ * (v ⬝ᵥ v) ≤ v ⬝ᵥ Q₂ *ᵥ v) (hhi₂ : ∀ v, v ⬝ᵥ Q₂ *ᵥ v ≤ γ₁ * (v ⬝ᵥ v)) :
    (gaussProb T₁).prod (gaussProb T₂) = (gaussPush (invSqrt (fromBlocks Q₁ 0 0 Q₂) γ₁)).map (pairUnitMap c) := by
  obtain ⟨hA₁, hAA₁, hQu₁⟩ := invSqrt_facts hQ₁ hγ₀ hγ₀₁ hlo₁ hhi₁
  obtain ⟨hA₂, hAA₂, hQu₂⟩ := invSqrt_facts hQ₂ hγ₀ hγ₀₁ hlo₂ hhi₂
  have hQb : (fromBlocks Q₁ 0 0 Q₂)ᵀ = fromBlocks Q₁ 0 0 Q₂ := by
    rw [fromBlocks_transpose, hQ₁, hQ₂, transpose_zero, transpose_zero]
  have hlob : ∀ v, γ₀ * (v ⬝ᵥ v) ≤ v ⬝ᵥ fromBlocks Q₁ 0 0 Q₂ *ᵥ v := fun v => by
    rw [dotProduct_fromBlocks, dotProduct_self_sum, mul_add]
    exact add_le_add (hlo₁ _) (hlo₂ _)
  have hhib : ∀ v, v ⬝ᵥ fromBlocks Q₁ 0 0 Q₂ *ᵥ v ≤ γ₁ * (v ⬝ᵥ v) := fun v => by
    rw [dotProduct_fromBlocks, dotProduct_self_sum, mul_add]
    exact add_le_add (hhi₁ _) (hhi₂ _)
  obtain ⟨hAb, hAAb, hQub⟩ := invSqrt_facts hQb hγ₀ hγ₀₁ hlob hhib
  have hBt : (fromBlocks (invSqrt Q₁ γ₁) 0 0 (invSqrt Q₂ γ₁))ᵀ = fromBlocks (invSqrt Q₁ γ₁) 0 0 (invSqrt Q₂ γ₁) := by
    rw [fromBlocks_transpose, hA₁, hA₂, transpose_zero, transpose_zero]
  have hBB : fromBlocks (invSqrt Q₁ γ₁) 0 0 (invSqrt Q₂ γ₁) * fromBlocks (invSqrt Q₁ γ₁) 0 0 (invSqrt Q₂ γ₁) =
      (fromBlocks Q₁ 0 0 Q₂)⁻¹ := by
    rw [fromBlocks_multiply, inv_fromBlocks_diag hQu₁ hQu₂]
    simp [hAA₁, hAA₂]
  rw [gaussPush_eq_of_sq hAb hAAb hBt hBB hQub, gaussProb_eq_map_unit hT₁ hpos₁ hc hQ₁ hTQ₁ hγ₀ hγ₀₁ hlo₁ hhi₁,
    gaussProb_eq_map_unit hT₂ hpos₂ hc hQ₂ hTQ₂ hγ₀ hγ₀₁ hlo₂ hhi₂]
  have hf₁ : Measurable fun z : (ι₁ × κ₁) → ℝ =>
      (fieldCoord ((Real.sqrt c)⁻¹ • z) : PiLp 2 (fun _ : ι₁ => EuclideanSpace ℝ κ₁)) :=
    (measurePreserving_fieldCoord (ι := ι₁) (κ := κ₁)).measurable.comp (measurable_const_smul _)
  have hf₂ : Measurable fun z : (ι₂ × κ₂) → ℝ =>
      (fieldCoord ((Real.sqrt c)⁻¹ • z) : PiLp 2 (fun _ : ι₂ => EuclideanSpace ℝ κ₂)) :=
    (measurePreserving_fieldCoord (ι := ι₂) (κ := κ₂)).measurable.comp (measurable_const_smul _)
  rw [Measure.map_prod_map _ _ hf₁ hf₂, ← gaussPush_fromBlocks,
    Measure.map_map (hf₁.prodMap hf₂) (MeasurableEquiv.measurable _)]
  rfl

end GaussianBlockSpin
