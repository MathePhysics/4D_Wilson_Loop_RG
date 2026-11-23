import GaussianBlockSpin.BoxFubini

/-! Moments over a box for a product probability measure on `ι → ℝ`:
* measurePreserving_restrictFinset: the restriction to the coordinates of `s` maps `Measure.pi ν₁` to the product over
  `s`;
* integral_updateFinset_eq: a function of the coordinates of `s` has the same integral over the box `s` (the other
  coordinates fixed at any `x`) as over the whole product;
* truncExp_moments_finset_sum_eq: `⟨(Σ_{X ∈ s} Y_X)^k⟩^T = Σ_{g ∈ s^k} κ(Y_{g(1)}, …, Y_{g(k)})` for bounded measurable
  pieces, the tuples taken in `Fintype.piFinset`. -/

namespace GaussianBlockSpin

open MeasureTheory Function

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (ν₁ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (ν₁ i)]

/-- The restriction to the coordinates of `s` is measure preserving from the product measure to the product over
`s`. -/
lemma measurePreserving_restrictFinset (s : Finset ι) :
    MeasurePreserving (fun (ω : ι → ℝ) (i : s) => ω i) (Measure.pi ν₁) (Measure.pi fun i : s => ν₁ i) := by
  have h := measurePreserving_piEquivPiSubtypeProd ν₁ (fun i => i ∈ s)
  convert (measurePreserving_fst).comp h
  rfl

/-- **Box integrals of box-local functions**: if `G` depends only on the coordinates in `s`, its integral over the
box `s`, with the other coordinates fixed at any `x`, is its integral under the whole product measure. -/
lemma integral_updateFinset_eq (s : Finset ι) (x : ι → ℝ) {G : (ι → ℝ) → ℝ} (hG : DependsOn G (s : Set ι))
    (mG : Measurable G) :
    ∫ y, G (updateFinset x s y) ∂(Measure.pi fun i : s => ν₁ i) = ∫ ω, G ω ∂(Measure.pi ν₁) := by
  have hr := measurePreserving_restrictFinset ν₁ s
  have hGe : (fun ω => G ω) = fun ω => G (updateFinset x s (fun i : s => ω i)) := by
    funext ω
    refine hG fun i hi => ?_
    simp [updateFinset_def, Finset.mem_coe.mp hi]
  rw [hGe, ← hr.map_eq, integral_map hr.measurable.aemeasurable]
  rw [hr.map_eq]
  exact (mG.comp measurable_updateFinset).aestronglyMeasurable

omit [Fintype ι] [DecidableEq ι] [∀ i, IsProbabilityMeasure (ν₁ i)] in
/-- Products of sums of bounded measurable pieces are integrable under a probability measure. -/
lemma integrable_prod_sum_of_bdd {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {A : Type*} {k : ℕ} (V : A → Ω → ℝ) (mV : ∀ a, Measurable (V a)) (c : A → ℝ) (hV : ∀ a ω, |V a ω| ≤ c a)
    (T : Finset (Fin k)) (t : Fin k → Finset A) :
    Integrable (fun ω => ∏ v ∈ T, ∑ a ∈ t v, V a ω) μ := by
  refine Integrable.of_bound (Finset.measurable_prod _ fun v _ => Finset.measurable_sum _ fun a _ => mV a).aestronglyMeasurable
    (∏ v ∈ T, ∑ a ∈ t v, c a) (ae_of_all _ fun ω => ?_)
  rw [Real.norm_eq_abs, Finset.abs_prod]
  refine Finset.prod_le_prod₀ (fun v _ => abs_nonneg _) fun v _ => ?_
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a _ => hV a ω)

omit [Fintype ι] [DecidableEq ι] [∀ i, IsProbabilityMeasure (ν₁ i)] in
/-- **Truncated expectations of a finite sum of bounded pieces**: `⟨(Σ_{X ∈ s} Y_X)^k⟩^T` is the sum over the tuples
`g ∈ s^k` of the joint cumulants of `Y_{g(1)}, …, Y_{g(k)}`. -/
theorem truncExp_moments_finset_sum_eq {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {P : Type*} [DecidableEq P] (s : Finset P) (Y : P → Ω → ℝ) (mY : ∀ X, Measurable (Y X)) (c : P → ℝ)
    (hY : ∀ X ω, |Y X ω| ≤ c X) {k : ℕ} (hk : 0 < k) :
    truncExp (moments μ (fun ω => ∑ X ∈ s, Y X ω)) k =
      ∑ g ∈ Fintype.piFinset (fun _ : Fin k => s),
        jointCumulant (fun T => ∫ ω, ∏ i ∈ T, Y (g i) ω ∂μ) Finset.univ := by
  have h := truncExp_moments_sum_eq μ (A := s) (n := k) (fun a => Y a.1)
    (fun T t => integrable_prod_sum_of_bdd μ (fun a : s => Y a.1) (fun a => mY a.1) (fun a => c a.1)
      (fun a ω => hY a.1 ω) T t) hk
  have hsum : (fun ω => ∑ a : s, Y a.1 ω) = fun ω => ∑ X ∈ s, Y X ω := by
    funext ω
    exact Finset.sum_coe_sort s (fun X => Y X ω)
  rw [hsum] at h
  rw [h]
  refine Finset.sum_bij (fun g _ => fun j => (g j).1) (fun g _ => ?_) (fun g1 _ g2 _ h12 => ?_)
    (fun g hg => ?_) (fun g _ => rfl)
  · exact Fintype.mem_piFinset.mpr fun j => (g j).2
  · funext j
    exact Subtype.ext (congrFun h12 j)
  · exact ⟨fun j => ⟨g j, Fintype.mem_piFinset.mp hg j⟩, Finset.mem_univ _, rfl⟩

end GaussianBlockSpin
