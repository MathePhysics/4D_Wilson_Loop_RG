import BlockPoincare.Estimate
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Cubes of side `l`, and the geometric scales `a_j`

Two complements to `BlockPoincare.Estimate`.

* `hNegNorm_le_cube`: for a partition of a two-dimensional space into cubes of side `l`
  (`vol = l²`, `diam ≤ √2 l`) the estimate reads
  `‖f‖_{H^{-s}} ≤ 2^((1+s)/2) l^s ‖f‖_{L²}`.  This is the manuscript's `C_{s,M} a_j^s` with
  `l = a_{j-1} = M a_j` and `C_{s,M} = 2^((1+s)/2) M^s`.
* `summable_scale_rpow`: `Σ_j a_j^s < ∞` for `a_j = a₀ M^{-j}`, `M > 1`, `s > 0`, which is the
  summability the manuscript's remark draws from the estimate.

## Conventions

The constant `2^((1+s)/2)` is *dimensionless*: it involves neither the number of blocks, nor the
index `j`, nor the volume of the space.  All the `j`-dependence is in the factor `l^s`.

## Scope

Both results are proved.  `hNegNorm_le_cube` takes the geometry of the cubes (`vol = l²` and
`diam ≤ √2 l`) as hypotheses on the partition; no such partition is constructed here, on the
torus or elsewhere.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace BlockPoincare

variable {X : Type*} [MeasurableSpace X] [MetricSpace X] {μ : Measure X}
  {ι : Type*} [Fintype ι] {f : X → ℝ} {s l : ℝ}

/-- The cube constant: `√((√2 l)^(2+2s) / l²) = 2^((1+s)/2) l^s`. -/
theorem sqrt_cube_const (hl : 0 < l) (s : ℝ) :
    Real.sqrt ((Real.sqrt 2 * l) ^ (2 + 2 * s) / l ^ 2) = 2 ^ ((1  -- totalisation-audit: allow > 0
        + s) / 2) * l ^ s := by  -- totalisation-audit: allow > 0
  have h2 : (0 : ℝ) ≤ 2 := by norm_num
  have hsq : Real.sqrt 2 ^ (2 + 2 * s) = 2 ^ (1 + s) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul h2]
    congr 1
    ring
  have hl2 : l ^ (2 + 2 * s) = l ^ (2 : ℕ) * l ^ (2 * s) := by
    rw [Real.rpow_add hl, show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hquot : (Real.sqrt 2 * l) ^ (2 + 2 * s) / l ^ 2 = 2 ^ (1 +  -- totalisation-audit: allow > 0
      s) * l ^ (2 * s) := by
    rw [Real.mul_rpow (Real.sqrt_nonneg 2) hl.le, hsq, hl2,
      mul_comm (l ^ (2 : ℕ)) (l ^ (2 * s)), ← mul_assoc, mul_div_assoc,
      div_self (by positivity), mul_one]
  rw [hquot, Real.sqrt_mul (Real.rpow_nonneg h2 _), Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
    ← Real.rpow_mul h2, ← Real.rpow_mul hl.le, show (1 + s) * (1 /  -- totalisation-audit: allow > 0
        2) = (1 + s) / 2 by ring,  -- totalisation-audit: allow > 0
    show 2 * s * (1 / 2) = s by ring]  -- totalisation-audit: allow > 0

/-- **The fractional block Poincaré estimate for cubes of side `l` in two dimensions.**
`‖f‖_{H^{-s}} ≤ 2^((1+s)/2) l^s ‖f‖_{L²}` for `f ∈ L²` with zero integral on every cube. -/
theorem hNegNorm_le_cube (P : BlockPartition X μ ι) (hs : 0 < s) (hl : 0 < l)
    (hvol : P.vol = ENNReal.ofReal (l ^ 2)) (hside : P.side = Real.sqrt 2 * l)
    (hf : MemLp f 2 μ) (hzero : ∀ i, ∫ x in P.block i, f x ∂μ =  -- totalisation-audit: allow L1 hyp
        0) :
    hNegNorm s μ f
      ≤ ENNReal.ofReal (2 ^ ((1 + s) / 2) * l ^ s *  -- totalisation-audit: allow > 0
          Real.sqrt (∫ x, f x ^ 2 ∂μ)) := by  -- totalisation-audit: allow L1 hyp
  have h := hNegNorm_le_of_blockIntegral_zero P hs hf hzero
  rwa [hvol, hside, ENNReal.toReal_ofReal (by positivity), sqrt_cube_const hl] at h

/-- The manuscript's scales `a_j = a₀ M^{-j}`. -/
def scale (a₀ M : ℝ) (j : ℕ) : ℝ := a₀ / M ^ j  -- totalisation-audit: allow > 0

lemma scale_nonneg {a₀ M : ℝ} (ha : 0 ≤ a₀) (hM : 0 ≤ M) (j : ℕ) : 0 ≤ scale a₀ M j :=
  div_nonneg ha (pow_nonneg hM j)

/-- `Σ_j a_j^s < ∞` for `a_j = a₀ M^{-j}` with `M > 1` and `s > 0`: the geometric summability the
manuscript's remark draws from the block estimate. -/
theorem summable_scale_rpow {a₀ M : ℝ} (ha : 0 < a₀) (hM : 1 < M) (hs : 0 < s) :
    Summable fun j : ℕ => scale a₀ M j ^ s := by
  have hM0 : (0 : ℝ) < M := lt_trans one_pos hM
  have hr : ∀ j : ℕ, scale a₀ M j ^ s = a₀ ^ s * ((M ^ s)⁻¹) ^ j := by
    intro j
    rw [scale, Real.div_rpow ha.le (pow_nonneg hM0.le j), ← Real.rpow_natCast M j,
      ← Real.rpow_mul hM0.le, show ((j : ℝ)) * s = s * j from mul_comm _ _, inv_pow,
      ← Real.rpow_natCast (M ^ s) j, ← Real.rpow_mul hM0.le, div_eq_mul_inv]
  have hlt : (M ^ s)⁻¹ < 1 := by
    rw [inv_lt_one_iff₀]
    exact Or.inr (Real.one_lt_rpow_iff_of_pos hM0 |>.2 (Or.inl ⟨hM, hs⟩))
  have hnn : 0 ≤ (M ^ s)⁻¹ := by positivity
  refine Summable.congr ((summable_geometric_of_lt_one hnn hlt).mul_left (a₀ ^ s)) ?_
  intro j
  exact (hr j).symm

/-- **The manuscript's form of the estimate.**  With blocks of side `l = a_{j-1} = M a_j`,
`‖f‖_{H^{-s}} ≤ C_{s,M} a_j^s ‖f‖_{L²}` with `C_{s,M} = 2^((1+s)/2) M^s`. -/
theorem hNegNorm_le_scale (P : BlockPartition X μ ι) (hs : 0 < s) {a M : ℝ} (ha : 0 < a)
    (hM : 0 < M) (hvol : P.vol = ENNReal.ofReal ((M * a) ^ 2))
    (hside : P.side = Real.sqrt 2 * (M * a)) (hf : MemLp f 2 μ)
    (hzero : ∀ i, ∫ x in P.block i, f x ∂μ = 0) :  -- totalisation-audit: allow L1 hyp
    hNegNorm s μ f ≤ ENNReal.ofReal (2 ^ ((1 + s) / 2) * M ^ s * a  -- totalisation-audit: allow > 0
        ^ s *
      Real.sqrt (∫ x, f x ^ 2 ∂μ)) := by  -- totalisation-audit: allow L1 hyp
  have h := hNegNorm_le_cube P hs (mul_pos hM ha) hvol hside hf hzero
  rwa [Real.mul_rpow hM.le ha.le, ← mul_assoc] at h

end BlockPoincare
