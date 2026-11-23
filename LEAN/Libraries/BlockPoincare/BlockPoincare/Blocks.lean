import BlockPoincare.Cube

/-!
# Block partitions

The manuscript's blocks: a finite family of pairwise disjoint measurable sets covering the space,
all of the same measure and of diameter at most `side`.  A partition of the torus `T_L` into
`(L / l)²` congruent cubes of side `l` is the intended instance, and the parameters are named
accordingly, but nothing here is specific to the torus or to cubes.

## Main definitions and results

* `BlockPartition` — the structure, with fields `block`, `side`, `vol` and proofs of pairwise
  disjointness, covering, equality of the measures and the diameter bound.
* `BlockPartition.sum_setLIntegral` — a lower integral is the sum of its restrictions to the
  blocks.
* `BlockPartition.sum_l2sq` — the `L²` energy is the sum of the block energies.
* `BlockPartition.sum_gagliardoSq_le` — the block Gagliardo seminorms sum to at most the global
  one.  This is the "disjointness" half of the argument: `⋃ B × B ⊆ X × X`.
* `BlockPartition.sum_setIntegral` — the Bochner version of the first, for an integrable
  function.

## Scope

All four results are proved.  The structure carries the hypothesis that all blocks have the same
measure `vol`; this is what makes the constant in `BlockPoincare.Estimate` uniform over the
blocks.  No existence statement is proved here: producing a block partition of a concrete space
(for instance the torus) is the caller's task, and none is constructed in this library.
-/

noncomputable section

open MeasureTheory Set Finset
open scoped ENNReal NNReal Function

namespace BlockPoincare

/-- A finite partition of `X` into congruent measurable blocks of diameter at most `side`. -/
structure BlockPartition (X : Type*) [MeasurableSpace X] [MetricSpace X] (μ : Measure X)
    (ι : Type*) [Fintype ι] where
  /-- The blocks. -/
  block : ι → Set X
  /-- An upper bound for the diameter of each block (the side of a cube, up to `√2`). -/
  side : ℝ
  /-- The common measure of the blocks. -/
  vol : ℝ≥0∞
  /-- Each block is measurable. -/
  measurableSet_block : ∀ i, MeasurableSet (block i)
  /-- Distinct blocks are disjoint. -/
  disjoint_block : Pairwise (Disjoint on block)
  /-- The blocks cover the space. -/
  iUnion_block : ⋃ i, block i = univ
  /-- All blocks have the same measure. -/
  measure_block : ∀ i, μ (block i) = vol
  /-- The blocks are not null. -/
  vol_ne_zero : vol ≠ 0
  /-- The blocks have finite measure. -/
  vol_ne_top : vol ≠ ∞
  /-- The blocks have diameter at most `side`. -/
  dist_le : ∀ i, ∀ x ∈ block i, ∀ y ∈ block i, dist x y ≤ side
  /-- The side is nonnegative.  (Automatic unless `ι` is empty.) -/
  side_nonneg : 0 ≤ side

namespace BlockPartition

variable {X : Type*} [MeasurableSpace X] [MetricSpace X] {μ : Measure X} {ι : Type*} [Fintype ι]
  (P : BlockPartition X μ ι) {f g : X → ℝ} {s : ℝ}

lemma measure_ne_zero (i : ι) : μ (P.block i) ≠ 0 := by rw [P.measure_block i]; exact P.vol_ne_zero

lemma measure_ne_top (i : ι) : μ (P.block i) ≠ ∞ := by rw [P.measure_block i]; exact P.vol_ne_top

/-- A lower integral splits over the blocks. -/
theorem sum_setLIntegral (F : X → ℝ≥0∞) : ∑ i, ∫⁻ x in P.block i, F x ∂μ = ∫⁻ x, F x ∂μ := by
  have h := lintegral_iUnion (μ := μ) P.measurableSet_block P.disjoint_block F
  rw [P.iUnion_block, Measure.restrict_univ, tsum_fintype] at h
  exact h.symm

/-- The `L²` energy is the sum of the block energies. -/
theorem sum_l2sq : ∑ i, l2sq μ (P.block i) g = l2sq μ univ g := by
  rw [l2sq, Measure.restrict_univ]
  exact P.sum_setLIntegral _

/-- The block Gagliardo seminorms sum to at most the global one: the squares `B × B` are disjoint
subsets of `X × X`. -/
theorem sum_gagliardoSq_le : ∑ i, gagliardoSq s μ (P.block i) g ≤ gagliardoSq s μ univ g := by
  have hle : ∀ i, gagliardoSq s μ (P.block i) g
      ≤ ∫⁻ x in P.block i, ∫⁻ y, ENNReal.ofReal ((g x - g y) ^ 2)
          /  -- totalisation-audit: allow > 0
          ENNReal.ofReal (dist x y ^ (2 + 2 * s)) ∂μ ∂μ := by
    intro i
    exact lintegral_mono fun x => lintegral_mono' Measure.restrict_le_self le_rfl
  refine le_trans (Finset.sum_le_sum fun i _ => hle i) (le_of_eq ?_)
  rw [P.sum_setLIntegral, gagliardoSq]
  simp only [Measure.restrict_univ]

/-- The space has measure `card ι * vol`; in particular it is finite. -/
theorem measure_univ_eq : μ univ = (Fintype.card ι : ℝ≥0∞) * P.vol := by
  have h := P.sum_setLIntegral (fun _ => 1)
  simp only [lintegral_one, Measure.restrict_apply_univ, P.measure_block] at h
  rw [← h, Finset.sum_const, nsmul_eq_mul, Finset.card_univ]

/-- A space carrying a block partition has finite measure. -/
lemma isFiniteMeasure (Q : BlockPartition X μ ι) : IsFiniteMeasure μ := by
  refine ⟨?_⟩
  rw [Q.measure_univ_eq]
  exact ENNReal.mul_lt_top (ENNReal.natCast_lt_top _) (lt_top_iff_ne_top.2 Q.vol_ne_top)

/-- A Bochner integral splits over the blocks. -/
theorem sum_setIntegral (hf : Integrable f μ) :
    ∑ i, ∫ x in P.block i, f x ∂μ = ∫ x, f x ∂μ := by  -- totalisation-audit: allow L1 hyp
  rw [← integral_iUnion_fintype P.measurableSet_block P.disjoint_block
      fun i => hf.integrableOn, P.iUnion_block, Measure.restrict_univ]

end BlockPartition

end BlockPoincare
