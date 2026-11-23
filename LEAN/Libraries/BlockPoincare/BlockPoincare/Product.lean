import BlockPoincare.Torus
import BlockPoincare.Scales
import BlockPoincare.Centred

/-!
# Products of block partitions, and the two-dimensional torus

If `X` and `Y` carry block partitions, so does `X × Y`, with the product measure, the product
blocks, `vol` the product of the volumes and `side` the larger of the two sides — the last
because mathlib's distance on a product is the supremum distance.  Applying this to two copies of
the subdivision of `AddCircle T` into `M` arcs gives the manuscript's torus `T_L` cut into `M²`
squares of side `l = T/M`, and the estimate

`‖f‖_{H^{-s}} ≤ l^s ‖f‖_{L²}`

for every `f ∈ L²` with zero integral on every square.

## Conventions

The distance on `AddCircle T × AddCircle T` is the supremum of the two circle distances, so a
square of side `l` has diameter `l`, not `√2 l`, and the constant is `l^s` with no numerical
factor.  With the Euclidean distance the diameter would be `√2 l` and the constant
`2^((1+s)/2) l^s`, which is what `BlockPoincare.Scales.hNegNorm_le_cube` gives; the two
statements differ only in that factor.

The measure used is `volume.prod volume`, which is the `volume` of the product measure space
(`MeasureTheory.Measure.volume_eq_prod`); it is written as a product here so that no measure
rewriting is needed inside the statements.

## Scope

All results are proved.  `squares` is a genuine `BlockPartition` of the two-dimensional torus:
this is the instance the rest of the library was missing.  The manuscript's scales are obtained
by taking `M = M₀^j`, so that `l = T / M₀^j = a_j`.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal Function

namespace BlockPoincare

namespace BlockPartition

variable {X Y : Type*} [MeasurableSpace X] [MetricSpace X] [MeasurableSpace Y] [MetricSpace Y]
  {μ : Measure X} {ν : Measure Y} {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The product of two block partitions. -/
def prod (P : BlockPartition X μ ι) (Q : BlockPartition Y ν κ) [SFinite μ] [SFinite ν] :
    BlockPartition (X × Y) (μ.prod ν) (ι × κ) where
  block := fun p => P.block p.1 ×ˢ Q.block p.2
  side := max P.side Q.side
  vol := P.vol * Q.vol
  measurableSet_block := fun p => (P.measurableSet_block p.1).prod (Q.measurableSet_block p.2)
  disjoint_block := by
    intro p q hpq
    rw [Function.onFun, Set.disjoint_left]
    rintro ⟨x, y⟩ ⟨hx, hy⟩ ⟨hx', hy'⟩
    have h1 : p.1 = q.1 := by
      by_contra h
      exact (Set.disjoint_left.1 (P.disjoint_block h)) hx hx'
    have h2 : p.2 = q.2 := by
      by_contra h
      exact (Set.disjoint_left.1 (Q.disjoint_block h)) hy hy'
    exact hpq (Prod.ext h1 h2)
  iUnion_block := by
    refine eq_univ_of_forall fun p => ?_
    obtain ⟨i, hi⟩ : ∃ i, p.1 ∈ P.block i := by
      have h : p.1 ∈ ⋃ i, P.block i := by rw [P.iUnion_block]; trivial
      simpa using h
    obtain ⟨j, hj⟩ : ∃ j, p.2 ∈ Q.block j := by
      have h : p.2 ∈ ⋃ j, Q.block j := by rw [Q.iUnion_block]; trivial
      simpa using h
    exact mem_iUnion.2 ⟨(i, j), ⟨hi, hj⟩⟩
  measure_block := fun p => by
    rw [Measure.prod_prod, P.measure_block, Q.measure_block]
  vol_ne_zero := mul_ne_zero P.vol_ne_zero Q.vol_ne_zero
  vol_ne_top := ENNReal.mul_ne_top P.vol_ne_top Q.vol_ne_top
  dist_le := by
    rintro p ⟨x, y⟩ ⟨hx, hy⟩ ⟨x', y'⟩ ⟨hx', hy'⟩
    rw [Prod.dist_eq]
    exact max_le_max (P.dist_le p.1 x hx x' hx') (Q.dist_le p.2 y hy y' hy')
  side_nonneg := le_trans P.side_nonneg (le_max_left _ _)

end BlockPartition

namespace Torus

variable (T : ℝ) [hT : Fact (0 < T)] (M : ℕ)

/-- The two-dimensional torus `AddCircle T × AddCircle T`, cut into `M²` squares of side
`T / M`. -/
def squares (hM : 0 < M) :
    BlockPartition (AddCircle T × AddCircle T) (volume.prod volume) (Fin M × Fin M) :=
  (arcs (T := T) hM).prod (arcs (T := T) hM)

variable {T M}

@[simp] lemma squares_side (hM : 0 < M) : (squares T M hM).side =
    T / M :=  -- totalisation-audit: allow > 0
  max_self _

@[simp] lemma squares_vol_toReal (hM : 0 < M) :
    ((squares T M hM).vol).toReal = (T / M) * (T / M) :=  -- totalisation-audit: allow finite, > 0
        by
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hl : (0 : ℝ) ≤ T / M := (div_pos hT.out hMR).le  -- totalisation-audit: allow > 0
  rw [show (squares T M hM).vol = ENNReal.ofReal (T / M) *  -- totalisation-audit: allow > 0
      ENNReal.ofReal (T / M) from rfl,  -- totalisation-audit: allow > 0
    ← ENNReal.ofReal_mul hl, ENNReal.toReal_ofReal (by positivity)]

lemma sqrt_square_const {l s : ℝ} (hl : 0 < l) :
    Real.sqrt (l ^ (2 + 2 * s) / (l * l)) = l ^ s := by  -- totalisation-audit: allow > 0
  have hll : l * l ≠ 0 := by positivity
  have h2 : l ^ (2 : ℝ) = l * l := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq]
  have h1 : l ^ (2 + 2 * s) / (l * l) = l ^ (2 * s) := by  -- totalisation-audit: allow > 0
    rw [Real.rpow_add hl, h2, mul_comm, mul_div_assoc, div_self hll, mul_one]
  rw [h1, Real.sqrt_eq_rpow, ← Real.rpow_mul hl.le]
  congr 1
  ring

/-- **The block estimate on the two-dimensional torus.**  If `f ∈ L²` has zero integral on every
square of the subdivision of `AddCircle T × AddCircle T` into `M²` squares of side `l = T / M`,
then `‖f‖_{H^{-s}} ≤ l^s ‖f‖_{L²}`. -/
theorem hNegNorm_le_squares {s : ℝ} {f : AddCircle T × AddCircle T → ℝ} (hM : 0 < M) (hs : 0 < s)
    (hf : MemLp f 2 (volume.prod volume))
    (hzero : ∀ k, ∫ x in (squares T M hM).block k, f x  -- totalisation-audit: allow L1 hyp
        ∂(volume.prod volume) = 0) :
    hNegNorm s (volume.prod volume) f
      ≤ ENNReal.ofReal ((T / M) ^ s *  -- totalisation-audit: allow > 0
          Real.sqrt (∫ x, f x ^ 2 ∂(volume.prod volume :  -- totalisation-audit: allow L1 hyp
              Measure (AddCircle T × AddCircle T)))) := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have h := hNegNorm_le_of_blockIntegral_zero (squares T M hM) hs hf hzero
  rwa [squares_side, squares_vol_toReal, sqrt_square_const (div_pos hT.out hMR)] at h

/-- **The manuscript's scales.**  With `M = M₀ ^ j` squares in each direction the side is
`a_j = T / M₀^j = scale T M₀ j`, and the estimate reads `‖f‖_{H^{-s}} ≤ a_j^s ‖f‖_{L²}`.
Together with `summable_scale_rpow` this is the summability the manuscript's remark uses. -/
theorem hNegNorm_le_scale_pow {s : ℝ} {M₀ j : ℕ} {f : AddCircle T × AddCircle T → ℝ}
    (hM : 0 < M₀ ^ j) (hs : 0 < s) (hf : MemLp f 2 (volume.prod volume))
    (hzero : ∀ k, ∫ x in (squares T (M₀ ^ j) hM).block k, f x  -- totalisation-audit: allow L1 hyp
        ∂(volume.prod volume) = 0) :
    hNegNorm s (volume.prod volume) f
      ≤ ENNReal.ofReal (scale T (M₀ : ℝ) j ^ s *
          Real.sqrt (∫ x, f x ^ 2 ∂(volume.prod volume :  -- totalisation-audit: allow L1 hyp
              Measure (AddCircle T × AddCircle T)))) := by
  have hcast : T / ((M₀ ^ j : ℕ) : ℝ) = scale T (M₀ : ℝ) j := by  -- totalisation-audit: allow > 0
    rw [scale]
    push_cast
    ring
  have h := hNegNorm_le_squares (T := T) (M := M₀ ^ j) hM hs hf hzero
  rwa [hcast] at h

/-- The sides `a_j = T / M₀^j` of the subdivisions are summable to the power `s`. -/
theorem summable_torus_scale {s : ℝ} {M₀ : ℕ} (hM₀ : 1 < M₀) (hs : 0 < s) :
    Summable fun j : ℕ => scale T (M₀ : ℝ) j ^ s :=
  summable_scale_rpow hT.out (by exact_mod_cast hM₀) hs

/-- **Every `L²` field on the torus obeys the estimate once it is centred on the squares.**  This
is the form in which the estimate is applied: `centre` is the manuscript's `D_B`. -/
theorem hNegNorm_centre_le_squares {s : ℝ} {ζ : AddCircle T × AddCircle T → ℝ} (hM : 0 < M)
    (hs : 0 < s) (hζ : MemLp ζ 2 (volume.prod volume)) :
    hNegNorm s (volume.prod volume) ((squares T M hM).centre ζ)
      ≤ ENNReal.ofReal ((T / M) ^ s * Real.sqrt (∫ x,  -- totalisation-audit: allow > 0, L1 hyp
          ((squares T M hM).centre ζ) x ^ 2
          ∂(volume.prod volume : Measure (AddCircle T × AddCircle T)))) := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have h := (squares T M hM).hNegNorm_centre_le hs hζ
  rwa [squares_side, squares_vol_toReal, sqrt_square_const (div_pos hT.out hMR)] at h

end Torus

end BlockPoincare
