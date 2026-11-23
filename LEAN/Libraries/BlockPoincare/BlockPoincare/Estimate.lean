import BlockPoincare.Blocks

/-!
# The fractional block Poincaré estimate

The lemma of the manuscript.  Let `P` be a partition of `X` into congruent blocks of measure
`vol` and diameter at most `side`, and let `f ∈ L²` have zero integral on every block.  Then for
every test function `ψ`

`⟪f, ψ⟫ ≤ √(side^(2+2s) / vol) ‖f‖_{L²} [ψ]_{Hˢ}`,

and hence `‖f‖_{H^{-s}} ≤ √(side^(2+2s) / vol) ‖f‖_{L²}`.  For a partition of the two-torus into
cubes of side `l` this constant is `2^((1+s)/2) l^s`, which is the manuscript's
`C_{s,M} a_j^s` with `l = a_{j-1} = M a_j`.

## The proof

`⟪f, ψ⟫ = Σ_B ∫_B f (ψ - ψ_B)` because `∫_B f = 0`; Cauchy–Schwarz on each block; the fractional
Poincaré inequality of `BlockPoincare.Cube` on each block; Cauchy–Schwarz over the blocks; and
finally `Σ_B [ψ]²_{Hˢ(B)} ≤ [ψ]²_{Hˢ(X)}`, which holds because the blocks are disjoint.

## Conventions

The constant `√(side^(2+2s) / vol)` depends on the partition only through `side` and `vol`, and
on nothing else: not on the block, not on the number of blocks, and not on the total measure of
`X`.  This is the uniformity the downstream use needs.

## Scope

`pairing_le` and `hNegNorm_le` are proved in full.  They assume `f, ψ ∈ L²` and, for `ψ`, that
its Gagliardo seminorm is finite; both hold for every `ψ` in the unit ball of `Hˢ`
(`memLp_two_of_mem_unitBall`).  No converse and no sharpness is proved.
-/

noncomputable section

open MeasureTheory Set Finset
open scoped ENNReal NNReal Function

namespace BlockPoincare

variable {X : Type*} [MeasurableSpace X] [MetricSpace X] {μ : Measure X}
  {ι : Type*} [Fintype ι] {f ψ : X → ℝ} {s : ℝ}

omit [MetricSpace X] in
/-- **Cauchy–Schwarz** for the Bochner integral of a product of two `L²` functions. -/
theorem integral_mul_le_sqrt_mul_sqrt {ν : Measure X} {u v : X → ℝ}
    (hu : MemLp u 2 ν) (hv : MemLp v 2 ν) :
    ∫ x, u x * v x ∂ν ≤ Real.sqrt (∫ x, u x ^ 2 ∂ν) * Real.sqrt  -- totalisation-audit: allow L1 hyp
        (∫ x, v x ^ 2 ∂ν) := by  -- totalisation-audit: allow L1 hyp
  have h2 : ENNReal.ofReal (2 : ℝ) = 2 := by simp
  have key := integral_mul_norm_le_Lp_mul_Lq (μ := ν) (f := u) (g := v)
    Real.HolderConjugate.two_two (by rwa [h2]) (by rwa [h2])
  have hpow : ∀ (w : X → ℝ) (a : X), ‖w a‖ ^ (2 : ℝ) = w a ^ 2 := by
    intro w a
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, Real.norm_eq_abs, sq_abs]
  simp only [hpow, ← Real.sqrt_eq_rpow] at key
  refine le_trans (le_trans (integral_mono ?_ ?_ fun x => ?_) key) le_rfl
  · exact hu.integrable_mul hv
  · exact hu.norm.integrable_mul hv.norm
  · rw [Real.norm_eq_abs, Real.norm_eq_abs, ← abs_mul]
    exact le_abs_self _

variable (P : BlockPartition X μ ι)

/-- The fractional Poincaré inequality on one block, in real form: the `L²` energy of
`ψ - ψ_B` is at most `side^(2+2s) / vol` times the block Gagliardo seminorm. -/
theorem integral_sub_bmean_sq_le (hs : 0 < s) (hψ : MemLp ψ 2 μ)
    (hgag : gagliardoSq s μ univ ψ ≠ ∞) (i : ι) :
    ∫ x in P.block i, (ψ x - mean μ (P.block i) ψ) ^ 2 ∂μ  -- totalisation-audit: allow L1 hyp
      ≤ P.side ^ (2 + 2 * s) / P.vol.toReal * (gagliardoSq  -- totalisation-audit: allow finite, > 0
          s μ (P.block i) ψ).toReal := by  -- totalisation-audit: allow finite
  have hvol : 0 < P.vol.toReal := ENNReal.toReal_pos  -- totalisation-audit: allow finite
      P.vol_ne_zero P.vol_ne_top
  have hfin : IsFiniteMeasure (μ.restrict (P.block i)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.2 (P.measure_ne_top i)⟩
  have hψi : MemLp ψ 2 (μ.restrict (P.block i)) := hψ.restrict _
  have hsub : MemLp (fun x => ψ x - mean μ (P.block i) ψ) 2 (μ.restrict (P.block i)) :=
    hψi.sub (memLp_const _)
  have hC0 : 0 ≤ ∫ x in P.block i, (ψ x - mean μ (P.block i) ψ)  -- totalisation-audit: allow L1 hyp
      ^ 2 ∂μ :=
    integral_nonneg fun x => sq_nonneg _
  have hGne : gagliardoSq s μ (P.block i) ψ ≠ ∞ :=
    ne_top_of_le_ne_top hgag (gagliardoSq_mono_set (subset_univ _))
  have hcube := mul_l2sq_sub_mean_le_diam (μ := μ) (A := P.block i) (g := ψ) (D := P.side) hs
    (P.measurableSet_block i) (P.measure_ne_zero i) (P.measure_ne_top i) hψi (P.dist_le i)
  rw [l2sq_toReal hsub.integrable_sq, P.measure_block i] at hcube
  have hne : ENNReal.ofReal (P.side ^ (2 + 2 * s)) * gagliardoSq s μ (P.block i) ψ ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hGne
  have hreal := ENNReal.toReal_mono hne hcube
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hC0,
    ENNReal.toReal_ofReal (Real.rpow_nonneg P.side_nonneg _)] at hreal
  have hCeq : ∫ x in P.block i, (ψ x - mean μ (P.block i) ψ) ^  -- totalisation-audit: allow L1 hyp
      2 ∂μ
      = (P.vol.toReal * ∫ x in P.block i, (ψ x -  -- totalisation-audit: allow finite, L1 hyp
          mean μ (P.block i) ψ) ^ 2 ∂μ) / P.vol.toReal :=  -- totalisation-audit: allow finite, > 0
              by
    field_simp
  rw [hCeq]
  refine le_trans (b := (P.side ^ (2 + 2 * s) *
    (gagliardoSq s μ (P.block i) ψ).toReal) /  -- totalisation-audit: allow finite, > 0
        P.vol.toReal) ?_ (le_of_eq (by ring))  -- totalisation-audit: allow finite
  gcongr

/-- **The fractional block Poincaré estimate**, in pairing form.  If `f` has zero integral on
every block then `⟪f, ψ⟫ ≤ √(side^(2+2s) / vol) ‖f‖_{L²} [ψ]_{Hˢ}`. -/
theorem pairing_le (hs : 0 < s) (hf : MemLp f 2 μ)
    (hzero : ∀ i, ∫ x in P.block i, f x ∂μ = 0) (hψ : MemLp ψ 2  -- totalisation-audit: allow L1 hyp
        μ)
    (hgag : gagliardoSq s μ univ ψ ≠ ∞) :
    ∫ x, f x * ψ x ∂μ ≤ Real.sqrt (P.side ^ (2 + 2  -- totalisation-audit: allow L1 hyp
        * s) / P.vol.toReal) *  -- totalisation-audit: allow finite, > 0
      (Real.sqrt (∫ x, f x ^ 2 ∂μ) * Real.sqrt  -- totalisation-audit: allow L1 hyp
          ((gagliardoSq s μ univ ψ).toReal)) := by  -- totalisation-audit: allow finite
  have hvol : 0 < P.vol.toReal := ENNReal.toReal_pos  -- totalisation-audit: allow finite
      P.vol_ne_zero P.vol_ne_top
  set θ : ℝ := P.side ^ (2 + 2 * s) / P.vol.toReal with hθ  -- totalisation-audit: allow finite, > 0
  have hθ0 : 0 ≤ θ := div_nonneg (Real.rpow_nonneg P.side_nonneg _) hvol.le
  set A : ι → ℝ := fun i => ∫ x in P.block i, f x ^ 2 ∂μ with  -- totalisation-audit: allow L1 hyp
      hA
  set G : ι → ℝ := fun i => (gagliardoSq s μ (P.block i)
      ψ).toReal with hG  -- totalisation-audit: allow finite
  have hA0 : ∀ i, 0 ≤ A i := fun i => integral_nonneg fun x => sq_nonneg _
  have hG0 : ∀ i, 0 ≤ θ * G i := fun i => mul_nonneg hθ0 ENNReal.toReal_nonneg
  -- the pairing on one block
  have hblock : ∀ i, ∫ x in P.block i, f x * ψ x ∂μ ≤ Real.sqrt  -- totalisation-audit: allow L1 hyp
      (A i) * Real.sqrt (θ * G i) := by
    intro i
    have hfin : IsFiniteMeasure (μ.restrict (P.block i)) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.2 (P.measure_ne_top i)⟩
    have hfi : MemLp f 2 (μ.restrict (P.block i)) := hf.restrict _
    have hψi : MemLp ψ 2 (μ.restrict (P.block i)) := hψ.restrict _
    have hsub : MemLp (fun x => ψ x - mean μ (P.block i) ψ) 2 (μ.restrict (P.block i)) :=
      hψi.sub (memLp_const _)
    have e1 : ∫ x in P.block i, f x * ψ x ∂μ  -- totalisation-audit: allow L1 hyp
        = ∫ x in P.block i, f x * (ψ x - mean μ (P.block i) ψ)  -- totalisation-audit: allow L1 hyp
            ∂μ := by
      have hfψ : Integrable (fun x => f x * ψ x) (μ.restrict (P.block i)) :=
        hfi.integrable_mul hψi
      have hfun : (fun x => f x * (ψ x - mean μ (P.block i) ψ))
          = fun x => f x * ψ x - mean μ (P.block i) ψ * f x := by
        funext x; ring
      rw [hfun, integral_sub hfψ ((hfi.integrable one_le_two).const_mul _), integral_const_mul,
        hzero i, mul_zero, sub_zero]
    rw [e1]
    refine le_trans (integral_mul_le_sqrt_mul_sqrt hfi hsub) ?_
    simp only [hA, hG]
    gcongr
    exact integral_sub_bmean_sq_le P hs hψ hgag i
  -- sum over the blocks
  have hfψ : Integrable (fun x => f x * ψ x) μ := hf.integrable_mul hψ
  have hsumA : ∑ i, A i = ∫ x, f x ^ 2 ∂μ := P.sum_setIntegral  -- totalisation-audit: allow L1 hyp
      hf.integrable_sq
  have hsumG : ∑ i, G i ≤ (gagliardoSq s μ univ ψ).toReal := by  -- totalisation-audit: allow finite
    have hGne : ∀ i, gagliardoSq s μ (P.block i) ψ ≠ ∞ := fun i =>
      ne_top_of_le_ne_top hgag (gagliardoSq_mono_set (subset_univ _))
    rw [hG, ← ENNReal.toReal_sum fun i _ => hGne i]
    exact ENNReal.toReal_mono hgag P.sum_gagliardoSq_le
  calc ∫ x, f x * ψ x ∂μ  -- totalisation-audit: allow L1 hyp
      = ∑ i, ∫ x in P.block i, f x * ψ x ∂μ :=  -- totalisation-audit: allow L1 hyp
          (P.sum_setIntegral hfψ).symm
    _ ≤ ∑ i, Real.sqrt (A i) * Real.sqrt (θ * G i) := Finset.sum_le_sum fun i _ => hblock i
    _ ≤ Real.sqrt (∑ i, A i) * Real.sqrt (∑ i, θ * G i) :=
        Real.sum_sqrt_mul_sqrt_le _ hA0 hG0
    _ = Real.sqrt (∫ x, f x ^ 2 ∂μ) * (Real.sqrt θ * Real.sqrt  -- totalisation-audit: allow L1 hyp
        (∑ i, G i)) := by
        rw [hsumA, ← Finset.mul_sum, Real.sqrt_mul hθ0]
    _ ≤ Real.sqrt (∫ x, f x ^ 2 ∂μ) *  -- totalisation-audit: allow L1 hyp
          (Real.sqrt θ * Real.sqrt ((gagliardoSq s μ univ
              ψ).toReal)) := by  -- totalisation-audit: allow finite
        gcongr
    _ = Real.sqrt θ * (Real.sqrt (∫ x, f x ^ 2 ∂μ) *  -- totalisation-audit: allow L1 hyp
          Real.sqrt ((gagliardoSq s μ univ ψ).toReal)) := by  -- totalisation-audit: allow finite
              ring

omit [MetricSpace X] in
/-- A test function of finite `L²` energy is in `L²` once it is measurable. -/
theorem memLp_two_of_l2sq_ne_top (hm : AEStronglyMeasurable ψ μ) (h : l2sq μ univ ψ ≠ ∞) :
    MemLp ψ 2 μ := by
  rw [memLp_two_iff_integrable_sq hm]
  refine ⟨(hm.mul hm).congr (.of_forall fun x => (pow_two (ψ x)).symm), ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have he : ∀ x : X, ‖ψ x ^ 2‖ₑ = ENNReal.ofReal (ψ x ^ 2) :=
    fun x => Real.enorm_eq_ofReal (sq_nonneg _)
  simp only [he]
  rw [l2sq, Measure.restrict_univ] at h
  exact lt_top_iff_ne_top.2 h

/-- A member of the unit ball of `Hˢ` is in `L²`. -/
theorem memLp_two_of_mem_unitBall (h : ψ ∈ unitBall s μ f) : MemLp ψ 2 μ :=
  memLp_two_of_l2sq_ne_top h.1
    (ne_top_of_le_ne_top ENNReal.one_ne_top (le_trans l2sq_le_hsNormSq h.2.1))

/-- **The fractional block Poincaré estimate**, in dual-norm form:
`‖f‖_{H^{-s}} ≤ √(side^(2+2s) / vol) ‖f‖_{L²}` for every `f ∈ L²` with zero integral on every
block. -/
theorem hNegNorm_le_of_blockIntegral_zero (hs : 0 < s) (hf : MemLp f 2 μ)
    (hzero : ∀ i, ∫ x in P.block i, f x ∂μ = 0) :  -- totalisation-audit: allow L1 hyp
    hNegNorm s μ f ≤ ENNReal.ofReal (Real.sqrt (P.side ^
        (2 + 2 * s) / P.vol.toReal) *  -- totalisation-audit: allow finite, > 0
      Real.sqrt (∫ x, f x ^ 2 ∂μ)) := by  -- totalisation-audit: allow L1 hyp
  refine hNegNorm_le fun ψ hψ => ENNReal.ofReal_le_ofReal ?_
  have hgag : gagliardoSq s μ univ ψ ≤ 1 := le_trans gagliardoSq_le_hsNormSq hψ.2.1
  have hgagne : gagliardoSq s μ univ ψ ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top hgag
  have hG1 : Real.sqrt ((gagliardoSq s μ univ ψ).toReal) ≤ 1 :=  -- totalisation-audit: allow finite
      by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by simpa using ENNReal.toReal_mono ENNReal.one_ne_top hgag)
  refine le_trans (pairing_le P hs hf hzero (memLp_two_of_mem_unitBall hψ) hgagne) ?_
  have h1 : Real.sqrt (∫ x, f x ^ 2 ∂μ) *  -- totalisation-audit: allow L1 hyp
      Real.sqrt ((gagliardoSq s μ univ ψ).toReal)  -- totalisation-audit: allow finite
      ≤ Real.sqrt (∫ x, f x ^ 2 ∂μ) := by  -- totalisation-audit: allow L1 hyp
    have h2 := mul_le_mul_of_nonneg_left hG1
      (Real.sqrt_nonneg (∫ x, f x ^ 2 ∂μ))  -- totalisation-audit: allow L1 hyp
    rwa [mul_one] at h2
  exact mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg _)

end BlockPoincare
