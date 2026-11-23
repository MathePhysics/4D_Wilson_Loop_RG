import GaussianBlockSpin.ProductIndependence

/-! Fubini over boxes for a product probability measure on `ι → ℝ` (the factorisation (5.13) of [2], here exact
because the measure is a product): with partial integrals `∫⋯∫⁻_s` (Mathlib's `lmarginal`),
* lmarginal_of_dependsOn: integrating a function over coordinates it does not depend on returns it;
* lmarginal_mul_left: a factor not depending on the integrated coordinates comes out;
* dependsOn_lmarginal: the partial integral over `s` of a function depending on `R` depends on `R \ s`;
* lmarginal_prod_boxes: the partial integral over a disjoint union of boxes of `∏_b g_b`, each `g_b` depending on its
  box and the corridors `Γ`, is the product of the partial integrals over the single boxes. -/

namespace GaussianBlockSpin

open MeasureTheory Function
open scoped ENNReal

variable {ι : Type*} [DecidableEq ι] (ν₁ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (ν₁ i)]

/-- Integrating over coordinates the function does not depend on returns the function. -/
lemma lmarginal_of_dependsOn {s : Finset ι} {f : (ι → ℝ) → ℝ≥0∞} (hf : DependsOn f ((s : Set ι)ᶜ)) :
    ∫⋯∫⁻_s, f ∂ν₁ = f := by
  ext x
  have h : ∀ y : (i : s) → ℝ, f (updateFinset x s y) = f x := fun y =>
    hf fun i hi => by simp [updateFinset_def, Finset.mem_coe.not.mp hi]
  simp [lmarginal, h]

omit [∀ i, IsProbabilityMeasure (ν₁ i)] in
/-- A factor that does not depend on the integrated coordinates comes out of the partial integral. -/
lemma lmarginal_mul_left {s : Finset ι} {c f : (ι → ℝ) → ℝ≥0∞} (hc : DependsOn c ((s : Set ι)ᶜ))
    (hf : Measurable f) :
    ∫⋯∫⁻_s, (fun x => c x * f x) ∂ν₁ = fun x => c x * (∫⋯∫⁻_s, f ∂ν₁) x := by
  ext x
  have h : ∀ y : (i : s) → ℝ, c (updateFinset x s y) = c x := fun y =>
    hc fun i hi => by simp [updateFinset_def, Finset.mem_coe.not.mp hi]
  simp only [lmarginal, h]
  exact lintegral_const_mul _ (hf.comp measurable_updateFinset)

omit [∀ i, IsProbabilityMeasure (ν₁ i)] in
/-- The partial integral over `s` of a function depending on `R` depends only on `R \ s`. -/
lemma dependsOn_lmarginal {s : Finset ι} {f : (ι → ℝ) → ℝ≥0∞} {R : Set ι} (hf : DependsOn f R) :
    DependsOn (∫⋯∫⁻_s, f ∂ν₁) (R \ (s : Set ι)) := by
  intro x y hxy
  simp only [lmarginal]
  refine lintegral_congr fun z => hf fun i hi => ?_
  by_cases his : i ∈ s
  · simp [updateFinset_def, his]
  · simp only [updateFinset_def, his, ↓reduceDIte]
    exact hxy i ⟨hi, Finset.mem_coe.not.mpr his⟩

omit [DecidableEq ι] in
/-- A product of functions depending on `R` depends on `R`. -/
lemma dependsOn_finset_prod {β : Type*} (bs : Finset β) {g : β → (ι → ℝ) → ℝ≥0∞} {R : Set ι}
    (hg : ∀ b ∈ bs, DependsOn (g b) R) : DependsOn (fun x => ∏ b ∈ bs, g b x) R := by
  intro x y hxy
  exact Finset.prod_congr rfl fun b hb => hg b hb hxy

/-- **Fubini over disjoint boxes**: if `g_b` depends only on the coordinates of its box and of the corridors `Γ`
(disjoint from every box), the partial integral of `∏_{b ∈ bs} g_b` over the union of the boxes of `bs` is the product
of the partial integrals of the `g_b` over their own boxes. -/
theorem lmarginal_prod_boxes {β : Type*} [DecidableEq β] (box : β → Finset ι) (Γ : Set ι)
    (hΓ : ∀ b, Disjoint (box b : Set ι) Γ) (g : β → (ι → ℝ) → ℝ≥0∞) (hg : ∀ b, DependsOn (g b) (box b ∪ Γ))
    (mg : ∀ b, Measurable (g b)) (bs : Finset β) (hdisj : (bs : Set β).PairwiseDisjoint box) :
    ∫⋯∫⁻_(bs.biUnion box), (fun x => ∏ b ∈ bs, g b x) ∂ν₁ = fun x => ∏ b ∈ bs, (∫⋯∫⁻_(box b), g b ∂ν₁) x := by
  induction bs using Finset.induction_on with
  | empty => ext x; simp
  | insert b0 bs hb0 ih =>
    have hdisj' : (bs : Set β).PairwiseDisjoint box :=
      hdisj.subset (by simp [Set.subset_insert])
    have hd0 : Disjoint (box b0) (bs.biUnion box) := by
      refine (Finset.disjoint_biUnion_right _ _ _).mpr fun b hb => ?_
      exact hdisj (by simp) (by simp [hb]) (by rintro rfl; exact hb0 hb)
    rw [Finset.biUnion_insert]
    have hmeas : Measurable (fun x => ∏ b ∈ insert b0 bs, g b x) :=
      Finset.measurable_prod _ fun b _ => mg b
    rw [lmarginal_union ν₁ _ hmeas hd0]
    simp_rw [Finset.prod_insert hb0]
    -- the factor `g b0` does not depend on the other boxes
    have hc0 : DependsOn (g b0) (((bs.biUnion box : Finset ι) : Set ι)ᶜ) := by
      refine (hg b0).mono fun i hi => ?_
      rcases hi with hi | hi
      · exact fun h => Finset.disjoint_left.mp hd0 hi (Finset.mem_coe.mp h)
      · intro h
        obtain ⟨b, hb, hib⟩ := Finset.mem_biUnion.mp (Finset.mem_coe.mp h)
        exact Set.disjoint_left.mp (hΓ b) hib hi
    rw [lmarginal_mul_left ν₁ hc0 (Finset.measurable_prod _ fun b _ => mg b), ih hdisj']
    -- the product of the other partial integrals does not depend on the box `b0`
    have hc1 : DependsOn (fun x => ∏ b ∈ bs, (∫⋯∫⁻_(box b), g b ∂ν₁) x) (((box b0 : Finset ι) : Set ι)ᶜ) := by
      refine dependsOn_finset_prod bs fun b hb => ((dependsOn_lmarginal ν₁ (hg b)).mono ?_)
      intro i ⟨hi, hni⟩
      rcases hi with hi | hi
      · exact absurd hi hni
      · exact fun h => Set.disjoint_left.mp (hΓ b0) h hi
    have hcomm : (fun x => g b0 x * ∏ b ∈ bs, (∫⋯∫⁻_(box b), g b ∂ν₁) x) =
        fun x => (∏ b ∈ bs, (∫⋯∫⁻_(box b), g b ∂ν₁) x) * g b0 x := by
      ext x; ring
    rw [hcomm, lmarginal_mul_left ν₁ hc1 (mg b0)]
    ext x
    ring

end GaussianBlockSpin
