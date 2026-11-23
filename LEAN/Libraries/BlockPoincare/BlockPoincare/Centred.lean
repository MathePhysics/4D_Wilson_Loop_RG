import BlockPoincare.Estimate

/-!
# The centred fibre coordinate

The manuscript's `lem:app-centred-fibre` (v163, line 12013): the map

`D_B ζ = ζ - 1_B m_B ζ`

that subtracts from `ζ` its mean on each block.  Here it is taken over a whole block partition at
once:

`centre P ζ x = ζ x - Σ_i 1_{B i}(x) * mean (B i) ζ`,

which on the block `B i` is `ζ - mean (B i) ζ`.

## Main results

* `centre_apply` — on a block, `centre P ζ = ζ - mean`.
* `setIntegral_centre` — `∫_B centre P ζ = 0` on every block: `centre` lands in the class of
  functions the block estimate applies to.
* `centre_eq_self_of_setIntegral_eq_zero` and `centre_idem` — `centre` is the identity on that
  class, hence idempotent: it is a projection onto it.
* `memLp_centre` — it preserves `L²`.
* `hNegNorm_centre_le` — the block estimate applies to `centre P ζ` for every `ζ ∈ L²`: this is
  how an arbitrary field is brought into the class the estimate speaks about.

## Conventions

The value `mean μ (B i) ζ` is the Bochner mean, so `ζ` must be integrable on each block for the
statements to say anything; this is a hypothesis (`MemLp ζ 2 μ`) wherever it is needed.

## Scope

All four results are proved.  The manuscript states that `D_B` is an *isomorphism* onto the
zero-mean subspace; what is proved here is the projection property (`centre` is idempotent, its
range is contained in the zero-mean class, and it is the identity on that class), which is the
content actually used.  The inverse map and a statement in terms of submodules are not
formalised.
-/

noncomputable section

open MeasureTheory Set Finset
open scoped ENNReal NNReal Function

namespace BlockPoincare

namespace BlockPartition

variable {X : Type*} [MeasurableSpace X] [MetricSpace X] {μ : Measure X} {ι : Type*} [Fintype ι]
  (P : BlockPartition X μ ι) (ζ : X → ℝ)

/-- The centred fibre coordinate: subtract from `ζ` its mean on each block. -/
def centre : X → ℝ :=
  fun x => ζ x - ∑ i, (P.block i).indicator (fun _ => mean μ (P.block i) ζ) x

variable {P ζ}

/-- On a block, centring subtracts the mean over that block. -/
lemma centre_apply {i : ι} {x : X} (hx : x ∈ P.block i) :
    P.centre ζ x = ζ x - mean μ (P.block i) ζ := by
  have hzero : ∀ j ∈ Finset.univ, j ≠ i →
      (P.block j).indicator (fun _ => mean μ (P.block j) ζ) x = 0 := by
    intro j _ hj
    refine Set.indicator_of_notMem (fun hxj => ?_) _
    exact (P.disjoint_block hj).le_bot ⟨hxj, hx⟩
  rw [centre, Finset.sum_eq_single_of_mem i (Finset.mem_univ i) hzero,
    Set.indicator_of_mem hx]

/-- Centring makes the integral over every block vanish. -/
theorem setIntegral_centre (hζ : Integrable ζ μ) (i : ι) :
    ∫ x in P.block i, P.centre ζ x ∂μ = 0 := by  -- totalisation-audit: allow L1 hyp
  have hfm : IsFiniteMeasure (μ.restrict (P.block i)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.2 (P.measure_ne_top i)⟩
  have hfin : (μ (P.block i)).toReal ≠ 0 :=  -- totalisation-audit: allow finite
    ENNReal.toReal_ne_zero.2 ⟨P.measure_ne_zero i, P.measure_ne_top i⟩
  have hcongr : ∫ x in P.block i, P.centre ζ x ∂μ  -- totalisation-audit: allow L1 hyp
      = ∫ x in P.block i, (ζ x - mean μ (P.block i) ζ) ∂μ :=  -- totalisation-audit: allow L1 hyp
    setIntegral_congr_fun (P.measurableSet_block i) fun x hx => centre_apply hx
  rw [hcongr, integral_sub hζ.integrableOn (integrable_const _), setIntegral_const,
    measureReal_def, smul_eq_mul, mean]
  field_simp
  ring

/-- Centring is the identity on functions whose block integrals vanish. -/
theorem centre_eq_self_of_setIntegral_eq_zero (h : ∀ i, ∫ x in  -- totalisation-audit: allow L1 hyp
    P.block i, ζ x ∂μ = 0) :
    P.centre ζ = ζ := by
  funext x
  obtain ⟨i, hi⟩ : ∃ i, x ∈ P.block i := by
    have : x ∈ ⋃ i, P.block i := by rw [P.iUnion_block]; trivial
    simpa using this
  rw [centre_apply hi, mean, h i, mul_zero, sub_zero]

/-- `centre` is a projection. -/
theorem centre_idem (hζ : Integrable ζ μ) : P.centre (P.centre ζ) = P.centre ζ :=
  centre_eq_self_of_setIntegral_eq_zero (setIntegral_centre hζ)

/-- Centring preserves `L²`. -/
theorem memLp_centre (hζ : MemLp ζ 2 μ) : MemLp (P.centre ζ) 2 μ := by
  refine hζ.sub (memLp_finsetSum _ fun i _ => ?_)
  exact memLp_indicator_const 2 (P.measurableSet_block i) _ (Or.inr (P.measure_ne_top i))

/-- **The block estimate applies to every centred `L²` function.** -/
theorem hNegNorm_centre_le {s : ℝ} (hs : 0 < s) (hζ : MemLp ζ 2 μ) :
    hNegNorm s μ (P.centre ζ)
      ≤ ENNReal.ofReal (Real.sqrt (P.side ^ (2 + 2 * s) /  -- totalisation-audit: allow > 0
          P.vol.toReal) *  -- totalisation-audit: allow finite
          Real.sqrt (∫ x, P.centre ζ x ^ 2 ∂μ)) := by  -- totalisation-audit: allow L1 hyp
  have hfm : IsFiniteMeasure μ := P.isFiniteMeasure
  exact hNegNorm_le_of_blockIntegral_zero P hs (memLp_centre hζ)
    (setIntegral_centre (hζ.integrable one_le_two))

end BlockPartition

end BlockPoincare
