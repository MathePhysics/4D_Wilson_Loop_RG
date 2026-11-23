import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-!
# The measure on a disjoint union

For a family of measure spaces `(X i, μ i)` indexed by an arbitrary (possibly uncountable) type
`ι`, the sigma type `Σ i, X i` carries mathlib's measurable space `Sigma.instMeasurableSpace`, in
which a set is measurable iff each of its slices `Sigma.mk i ⁻¹' s` is.  We equip it with the
measure `sigmaMeasure μ = Measure.sum (fun i => (μ i).map (Sigma.mk i))`.

Since `ι` may be uncountable, `sigmaMeasure μ` need not be σ-finite and mathlib's results on sums
of measures that assume a countable index do not apply.  The key point that replaces countability
is that measurable supersets of the slices can be glued into a measurable superset of the whole
set (`measurableSet_sigma_glue`).

## Main results

* `measurableSet_sigma_iff`, `measurable_sigma_iff`: measurability is checked slice by slice.
* `sigmaMeasure_apply`: `sigmaMeasure μ s = ∑' i, μ i (Sigma.mk i ⁻¹' s)` for **every** set `s`.
* `ae_sigmaMeasure_iff`: an a.e. statement holds iff it holds a.e. on every slice.
* `lintegral_sigmaMeasure`: `∫⁻ p, f p ∂sigmaMeasure μ = ∑' i, ∫⁻ x, f ⟨i, x⟩ ∂μ i` for every
  `f`, measurable or not.
* `aestronglyMeasurable_sigma_iff`: for a second-countable Borel target, a.e. strong
  measurability is checked slice by slice.
* `eLpNorm_sigmaMeasure_two_sq` and `memLp_two_sigma_iff`: the `L²` norm squared is the sum of the
  squared `L²` norms of the slices.
-/

open MeasureTheory Measure Set Filter TopologicalSpace
open scoped ENNReal

namespace SpectralTheorem

variable {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)]

/-! ### Measurability on a sigma type -/

/-- A set in a sigma type is measurable iff all its slices are measurable. -/
theorem measurableSet_sigma_iff {s : Set (Σ i, X i)} :
    MeasurableSet s ↔ ∀ i, MeasurableSet (Sigma.mk i ⁻¹' s) :=
  MeasurableSpace.measurableSet_iInf

/-- The inclusion of a summand into a sigma type is measurable. -/
theorem measurable_sigmaMk (i : ι) : Measurable (Sigma.mk i : X i → Σ i, X i) :=
  fun _ hs => measurableSet_sigma_iff.1 hs i

/-- A function on a sigma type is measurable iff all its restrictions to summands are. -/
theorem measurable_sigma_iff {β : Type*} [MeasurableSpace β] {f : (Σ i, X i) → β} :
    Measurable f ↔ ∀ i, Measurable fun x : X i => f ⟨i, x⟩ :=
  ⟨fun hf i => hf.comp (measurable_sigmaMk i), fun hf _ ht =>
    measurableSet_sigma_iff.2 fun i => hf i ht⟩

/-- Gluing a family of measurable sets `t i ⊆ X i` gives a measurable subset of the sigma type. -/
theorem measurableSet_sigma_glue {t : ∀ i, Set (X i)} (ht : ∀ i, MeasurableSet (t i)) :
    MeasurableSet {p : Σ i, X i | p.2 ∈ t p.1} :=
  measurableSet_sigma_iff.2 ht

/-- The inclusion of a summand into a sigma type is a measurable embedding. -/
theorem measurableEmbedding_sigmaMk (i : ι) :
    MeasurableEmbedding (Sigma.mk i : X i → Σ i, X i) where
  injective := sigma_mk_injective
  measurable := measurable_sigmaMk i
  measurableSet_image' s hs := by
    classical
    refine measurableSet_sigma_iff.2 fun j => ?_
    by_cases hij : i = j
    · subst hij
      rwa [preimage_image_eq _ sigma_mk_injective]
    · convert MeasurableSet.empty
      ext x
      simp [hij]

/-! ### The measure -/

/-- The measure on `Σ i, X i` whose restriction to the `i`-th summand is `μ i`. -/
noncomputable def sigmaMeasure (μ : ∀ i, Measure (X i)) : Measure (Σ i, X i) :=
  Measure.sum fun i => (μ i).map (Sigma.mk i)

variable (μ : ∀ i, Measure (X i))

/-- The pushforward of `μ i` to the sigma type is dominated by `sigmaMeasure μ`. -/
theorem map_sigmaMk_le_sigmaMeasure (i : ι) : (μ i).map (Sigma.mk i) ≤ sigmaMeasure μ :=
  Measure.le_sum (fun i => (μ i).map (Sigma.mk i)) i

/-- `sigmaMeasure μ` of a measurable set is the sum of the measures of its slices. -/
theorem sigmaMeasure_apply_of_measurableSet {s : Set (Σ i, X i)} (hs : MeasurableSet s) :
    sigmaMeasure μ s = ∑' i, μ i (Sigma.mk i ⁻¹' s) := by -- totalisation-audit: allow ℝ≥0∞ sum
  simp only [sigmaMeasure, Measure.sum_apply _ hs,
    (measurableEmbedding_sigmaMk _).map_apply]

/-- `sigmaMeasure μ` of an arbitrary set is the sum of the measures of its slices.  No
countability of `ι` is needed: measurable hulls of the slices glue to a measurable hull. -/
theorem sigmaMeasure_apply (s : Set (Σ i, X i)) :
    sigmaMeasure μ s = ∑' i, μ i (Sigma.mk i ⁻¹' s) := by -- totalisation-audit: allow ℝ≥0∞ sum
  refine le_antisymm ?_ ?_
  · set t : ∀ i, Set (X i) := fun i => toMeasurable (μ i) (Sigma.mk i ⁻¹' s)
    have ht : MeasurableSet {p : Σ i, X i | p.2 ∈ t p.1} :=
      measurableSet_sigma_glue fun i => measurableSet_toMeasurable _ _
    have hst : s ⊆ {p : Σ i, X i | p.2 ∈ t p.1} := fun p hp =>
      subset_toMeasurable (μ p.1) (Sigma.mk p.1 ⁻¹' s) hp
    exact (measure_mono hst).trans_eq ((sigmaMeasure_apply_of_measurableSet μ ht).trans
      (tsum_congr fun i => measure_toMeasurable (μ := μ i) (Sigma.mk i ⁻¹' s)))
  · rw [← measure_toMeasurable (μ := sigmaMeasure μ) s,
      sigmaMeasure_apply_of_measurableSet μ (measurableSet_toMeasurable _ _)]
    exact ENNReal.tsum_le_tsum fun i => measure_mono (preimage_mono (subset_toMeasurable _ _))

/-- A set is `sigmaMeasure μ`-null iff all its slices are null. -/
theorem sigmaMeasure_eq_zero_iff {s : Set (Σ i, X i)} :
    sigmaMeasure μ s = 0 ↔ ∀ i, μ i (Sigma.mk i ⁻¹' s) = 0 := by
  rw [sigmaMeasure_apply, ENNReal.tsum_eq_zero]

/-- An a.e. statement for `sigmaMeasure μ` holds iff it holds a.e. on every summand. -/
theorem ae_sigmaMeasure_iff {P : (Σ i, X i) → Prop} :
    (∀ᵐ p ∂sigmaMeasure μ, P p) ↔ ∀ i, ∀ᵐ x ∂μ i, P ⟨i, x⟩ := by
  simp only [ae_iff]
  exact sigmaMeasure_eq_zero_iff μ

/-- Two functions are `sigmaMeasure μ`-a.e. equal iff their restrictions to each summand are
a.e. equal. -/
theorem ae_eq_sigmaMeasure_iff {β : Type*} {f g : (Σ i, X i) → β} :
    f =ᵐ[sigmaMeasure μ] g ↔ ∀ i, (fun x => f ⟨i, x⟩) =ᵐ[μ i] fun x => g ⟨i, x⟩ :=
  ae_sigmaMeasure_iff μ

/-- The Lebesgue integral over the sigma type is the sum of the integrals over the summands.
No measurability of `f` is needed. -/
theorem lintegral_sigmaMeasure (f : (Σ i, X i) → ℝ≥0∞) :
    ∫⁻ p, f p ∂sigmaMeasure μ =
      ∑' i, ∫⁻ x, f ⟨i, x⟩ ∂μ i := by -- totalisation-audit: allow ℝ≥0∞ sum
  simp only [sigmaMeasure, lintegral_sum_measure, (measurableEmbedding_sigmaMk _).lintegral_map]

/-! ### Strong measurability and the `L²` norm -/

section Lp

variable {E : Type*}

/-- For a target that is second countable and Borel, a function on the sigma type is a.e.
strongly measurable iff all its restrictions to summands are.  The reverse direction glues
strongly measurable representatives of the slices; the glued function is measurable, hence
strongly measurable by second countability, even for uncountable `ι`. -/
theorem aestronglyMeasurable_sigma_iff [TopologicalSpace E] [PseudoMetrizableSpace E]
    [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E] {f : (Σ i, X i) → E} :
    AEStronglyMeasurable f (sigmaMeasure μ) ↔
      ∀ i, AEStronglyMeasurable (fun x => f ⟨i, x⟩) (μ i) := by
  refine ⟨fun hf i => ?_, fun hf => ?_⟩
  · exact (hf.mono_measure (map_sigmaMk_le_sigmaMeasure μ i)).comp_measurable
      (measurable_sigmaMk i)
  · let g : (Σ i, X i) → E := fun p => (hf p.1).mk _ p.2
    have hg : Measurable g := measurable_sigma_iff.2 fun i => (hf i).measurable_mk
    exact ⟨g, hg.stronglyMeasurable, (ae_eq_sigmaMeasure_iff μ).2 fun i => (hf i).ae_eq_mk⟩

/-- The square of the `L²` seminorm is the integral of the squared pointwise norm. -/
theorem eLpNorm_two_sq_eq_lintegral [TopologicalSpace E] [ENorm E] {α : Type*}
    [MeasurableSpace α] {ν : Measure α} {f : α → E} (hf : AEStronglyMeasurable f ν) :
    eLpNorm f 2 ν ^ 2 = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂ν := by
  have h := eLpNorm_nnreal_pow_eq_lintegral (p := 2) two_ne_zero hf
  simpa [ENNReal.rpow_two] using h

/-- The restriction to a summand of an `Lᵖ` function on the sigma type is `Lᵖ`. -/
theorem memLp_sigma_slice [NormedAddCommGroup E] {p : ℝ≥0∞} {f : (Σ i, X i) → E}
    (hf : MemLp f p (sigmaMeasure μ)) (i : ι) : MemLp (fun x => f ⟨i, x⟩) p (μ i) :=
  (measurableEmbedding_sigmaMk i).memLp_map_measure_iff.1
    (hf.mono_measure (map_sigmaMk_le_sigmaMeasure μ i))

variable [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- The squared `L²` seminorm over the sigma type is the sum of the squared `L²` seminorms of the
slices.  This holds for every function: if `f` is not a.e. strongly measurable, neither is some
slice, and both sides are `∞`. -/
theorem eLpNorm_sigmaMeasure_two_sq (f : (Σ i, X i) → E) :
    eLpNorm f 2 (sigmaMeasure μ) ^ 2 =
      ∑' i, eLpNorm (fun x => f ⟨i, x⟩) 2 (μ i) ^ 2 := by -- totalisation-audit: allow ℝ≥0∞ sum
  by_cases hf : AEStronglyMeasurable f (sigmaMeasure μ)
  · have hf' := (aestronglyMeasurable_sigma_iff μ).1 hf
    rw [eLpNorm_two_sq_eq_lintegral hf, lintegral_sigmaMeasure]
    exact tsum_congr fun i => (eLpNorm_two_sq_eq_lintegral (hf' i)).symm
  · obtain ⟨i, hi⟩ : ∃ i, ¬AEStronglyMeasurable (fun x => f ⟨i, x⟩) (μ i) := by
      simpa [aestronglyMeasurable_sigma_iff μ] using hf
    rw [eLpNorm_of_not_aestronglyMeasurable hf, ENNReal.tsum_eq_top_of_eq_top
      ⟨i, by rw [eLpNorm_of_not_aestronglyMeasurable hi]; simp⟩]
    simp

/-- A function is in `L²(sigmaMeasure μ)` iff all its slices are in `L²` and the sum of their
squared `L²` norms is finite. -/
theorem memLp_two_sigma_iff {f : (Σ i, X i) → E} : MemLp f 2 (sigmaMeasure μ) ↔
    (∀ i, MemLp (fun x => f ⟨i, x⟩) 2 (μ i)) ∧
    ∑' i, eLpNorm (fun x => f ⟨i, x⟩) 2 (μ i) ^ 2 < ∞ := by -- totalisation-audit: allow ℝ≥0∞ sum
  rw [← eLpNorm_sigmaMeasure_two_sq, ENNReal.pow_lt_top_iff]
  simp only [two_ne_zero, or_false]
  exact ⟨fun h => ⟨fun i => memLp_sigma_slice μ h i, h⟩, fun h => h.2⟩

end Lp

end SpectralTheorem
