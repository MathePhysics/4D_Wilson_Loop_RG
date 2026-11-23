import BlockPoincare.Estimate
import BlockPoincare.Nontrivial
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
# A concrete instance: the two-point space

A model on which every hypothesis of the block estimate is discharged and both sides of the
estimate are positive.  The space is the two-point metric space `TwoPoint` with the discrete
distance and the counting measure; the partition has a single block (the whole space, of
diameter `1` and measure `2`); the function is `f = ±1`, which has zero integral on that block.

This is the smallest space carrying a block partition: a partition into finitely many blocks of
finite diameter forces the space to be bounded, so `ℝ²` is not an instance and the torus is the
intended one.  The torus is not constructed in this library; this two-point model is here to
show that the definitions and the estimate are not vacuous, not to be the intended application.

## Main results

* `TwoPoint.instMetricSpace`, `TwoPoint.count_univ_eq`: the space, its distance and its measure.
* `TwoPoint.blocks`: the one-block partition, with `side = 1` and `vol = 2`.
* `TwoPoint.integral_witness_sq`, `TwoPoint.hsNormSq_witness`: `‖f‖²_{L²} = 2` and
  `‖f‖²_{Hˢ} = 10`, both finite and positive.
* `TwoPoint.hNegNorm_witness_pos` and `TwoPoint.hNegNorm_witness_le`: `0 < ‖f‖_{H^{-s}} ≤ 1`.

## Scope

Everything here is proved.  The instance is a model and nothing more: it is zero-dimensional, so
the two-dimensional constant `2^((1+s)/2) l^s` of `BlockPoincare.Scales` is not what appears —
the general constant `√(side^(2+2s) / vol)` is.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace BlockPoincare

namespace TwoPoint

variable {s : ℝ}

/-- The two-point space. -/
def _root_.BlockPoincare.TwoPoint : Type := Bool

/-- The first point. -/
def a : TwoPoint := false

/-- The second point. -/
def b : TwoPoint := true

instance : DecidableEq TwoPoint := inferInstanceAs (DecidableEq Bool)
instance : Fintype TwoPoint := inferInstanceAs (Fintype Bool)
instance : MeasurableSpace TwoPoint := ⊤
instance : MeasurableSingletonClass TwoPoint := ⟨fun _ => trivial⟩

lemma a_ne_b : a ≠ b := Bool.false_ne_true

lemma b_ne_a : b ≠ a := Ne.symm a_ne_b

lemma sum_eq {M : Type*} [AddCommMonoid M] (g : TwoPoint → M) : ∑ x, g x = g b + g a :=
  Fintype.sum_bool g

/-- The discrete distance on the two-point space. -/
def tpDist (x y : TwoPoint) : ℝ := if x = y then 0 else 1

lemma tpDist_self (x : TwoPoint) : tpDist x x = 0 := by simp [tpDist]

lemma tpDist_of_ne {x y : TwoPoint} (h : x ≠ y) : tpDist x y = 1 := by simp [tpDist, h]

lemma tpDist_nonneg (x y : TwoPoint) : 0 ≤ tpDist x y := by
  rw [tpDist]; split <;> norm_num

lemma tpDist_le_one (x y : TwoPoint) : tpDist x y ≤ 1 := by
  rw [tpDist]; split <;> norm_num

lemma tpDist_comm (x y : TwoPoint) : tpDist x y = tpDist y x := by
  by_cases h : x = y
  · rw [h]
  · rw [tpDist_of_ne h, tpDist_of_ne (Ne.symm h)]

lemma tpDist_triangle (x y z : TwoPoint) : tpDist x z ≤ tpDist x y + tpDist y z := by
  by_cases hxz : x = z
  · rw [hxz, tpDist_self]
    exact add_nonneg (tpDist_nonneg _ _) (tpDist_nonneg _ _)
  · rw [tpDist_of_ne hxz]
    rcases eq_or_ne x y with h | h
    · have hyz : y ≠ z := by rw [← h]; exact hxz
      rw [h, tpDist_self, tpDist_of_ne hyz, zero_add]
    · rw [tpDist_of_ne h]
      have := tpDist_nonneg y z
      linarith

lemma eq_of_tpDist_eq_zero {x y : TwoPoint} (h : tpDist x y = 0) : x = y := by
  by_contra hne
  rw [tpDist_of_ne hne] at h
  exact one_ne_zero h

instance instMetricSpace : MetricSpace TwoPoint where
  dist := tpDist
  dist_self := tpDist_self
  dist_comm := tpDist_comm
  dist_triangle := tpDist_triangle
  eq_of_dist_eq_zero := eq_of_tpDist_eq_zero

lemma dist_eq (x y : TwoPoint) : dist x y = tpDist x y := rfl

lemma count_singleton' (x : TwoPoint) : (Measure.count : Measure TwoPoint) {x} = 1 :=
  Measure.count_singleton x

lemma count_univ_eq : (Measure.count : Measure TwoPoint) univ = 2 := by
  rw [← lintegral_one, lintegral_fintype, sum_eq]
  simp only [count_singleton', one_mul]
  norm_num

instance : IsFiniteMeasure (Measure.count : Measure TwoPoint) :=
  ⟨by rw [count_univ_eq]; exact ENNReal.ofNat_lt_top⟩

/-- The one-block partition: a single block of diameter `1` and measure `2`. -/
def blocks : BlockPartition TwoPoint Measure.count Unit where
  block := fun _ => univ
  side := 1
  vol := 2
  measurableSet_block := fun _ => MeasurableSet.univ
  disjoint_block := fun i j h => absurd (Subsingleton.elim i j) h
  iUnion_block := iUnion_const univ
  measure_block := fun _ => count_univ_eq
  vol_ne_zero := by norm_num
  vol_ne_top := ENNReal.ofNat_ne_top
  dist_le := fun _ x _ y _ => by rw [dist_eq]; exact tpDist_le_one x y
  side_nonneg := zero_le_one

/-- The witness: `f b = 1`, `f a = -1`. -/
def witness : TwoPoint → ℝ := fun x => if x = b then 1 else -1

lemma witness_b : witness b = 1 := by simp [witness]

lemma witness_a : witness a = -1 := by simp [witness, a_ne_b]

lemma integrable_witness : Integrable witness (Measure.count : Measure TwoPoint) :=
  Integrable.of_finite

lemma memLp_witness : MemLp witness 2 (Measure.count : Measure TwoPoint) :=
  (memLp_two_iff_integrable_sq integrable_witness.1).2 Integrable.of_finite

lemma count_real_singleton (x : TwoPoint) :
    (Measure.count : Measure TwoPoint).real {x} = 1 := by
  simp [measureReal_def]

lemma integral_witness : ∫ x, witness x ∂(Measure.count :  -- totalisation-audit: allow L1 hyp
    Measure TwoPoint) = 0 := by
  rw [integral_fintype integrable_witness, sum_eq]
  simp [witness_a, witness_b]

lemma integral_witness_sq : ∫ x, witness x ^ 2 ∂(Measure.count  -- totalisation-audit: allow L1 hyp
    : Measure TwoPoint) = 2 := by
  rw [integral_fintype Integrable.of_finite, sum_eq]
  simp [witness_a, witness_b]
  norm_num

lemma eq_b_or_a (x : TwoPoint) : x = b ∨ x = a := Bool.eq_false_or_eq_true x

lemma gagliardo_integrand (x y : TwoPoint) :
    ENNReal.ofReal ((witness x - witness y) ^ 2) /  -- totalisation-audit: allow > 0
      ENNReal.ofReal (dist x y ^ (2 + 2 * s)) = if x = y then 0 else 4 := by
  by_cases h : x = y
  · simp [h]
  · have hif : (if x = y then (0 : ℝ≥0∞) else 4) = 4 := by simp [h]
    rw [hif, dist_eq, tpDist_of_ne h, Real.one_rpow, ENNReal.ofReal_one, div_one]
    have hval : (witness x - witness y) ^ 2 = 4 := by
      rcases eq_b_or_a x with hx | hx <;> rcases eq_b_or_a y with hy | hy <;>
        subst hx <;> subst hy
      · exact absurd rfl h
      · rw [witness_b, witness_a]; norm_num
      · rw [witness_a, witness_b]; norm_num
      · exact absurd rfl h
    rw [hval]
    norm_num

lemma gagliardoSq_witness : gagliardoSq s Measure.count univ witness = 8 := by
  simp only [gagliardoSq, Measure.restrict_univ, lintegral_fintype, sum_eq,
    gagliardo_integrand, count_singleton', a_ne_b, b_ne_a, mul_one]
  norm_num

lemma hsNormSq_witness : hsNormSq s Measure.count witness = 10 := by
  rw [hsNormSq, l2sq_univ_eq memLp_witness, integral_witness_sq, gagliardoSq_witness]
  norm_num

/-- The dual norm of the witness is positive: the estimate is not `0 ≤ 0`. -/
theorem hNegNorm_witness_pos : 0 < hNegNorm s Measure.count witness := by
  refine hNegNorm_pos memLp_witness ?_ ?_
  · rw [hsNormSq_witness]; norm_num
  · rw [integral_witness_sq]; norm_num

lemma setIntegral_witness (i : Unit) :
    ∫ x in blocks.block i, witness x ∂(Measure.count : Measure  -- totalisation-audit: allow L1 hyp
        TwoPoint) = 0 := by
  rw [show blocks.block i = univ from rfl, setIntegral_univ]
  exact integral_witness

/-- The block estimate on the two-point model. -/
theorem hNegNorm_witness_le (hs : 0 < s) :
    hNegNorm s Measure.count witness
      ≤ ENNReal.ofReal (Real.sqrt (blocks.side ^ (2 + 2 *
          s) / blocks.vol.toReal) *  -- totalisation-audit: allow finite, > 0
          Real.sqrt (∫ x, witness x ^ 2 ∂(Measure.count :  -- totalisation-audit: allow L1 hyp
              Measure TwoPoint))) :=
  hNegNorm_le_of_blockIntegral_zero blocks hs memLp_witness setIntegral_witness

/-- The same, with the constant evaluated: `‖f‖_{H^{-s}} ≤ 1`. -/
theorem hNegNorm_witness_le_one (hs : 0 < s) : hNegNorm s Measure.count witness ≤ 1 := by
  refine le_trans (hNegNorm_witness_le hs) (le_of_eq ?_)
  rw [show blocks.side = 1 from rfl, Real.one_rpow, show blocks.vol = 2 from rfl,
    integral_witness_sq, ← Real.sqrt_mul (by norm_num)]
  norm_num

/-- **The two-point model is a witness**: both sides of the block estimate are positive. -/
theorem witness_nontrivial (hs : 0 < s) :
    0 < hNegNorm s Measure.count witness ∧ hNegNorm s Measure.count witness ≤ 1 :=
  ⟨hNegNorm_witness_pos, hNegNorm_witness_le_one hs⟩

end TwoPoint

end BlockPoincare
