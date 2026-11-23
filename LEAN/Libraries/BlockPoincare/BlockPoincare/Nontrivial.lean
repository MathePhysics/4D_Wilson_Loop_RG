import BlockPoincare.Defs
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Non-vacuity of the dual norm

The failure mode this library has to avoid is an estimate whose two sides are both zero.  The
right-hand side of the block estimate is a multiple of `‖f‖_{L²}`, which is visibly positive for
`f ≠ 0`; the left-hand side is the supremum `‖f‖_{H^{-s}}`, and a supremum over an accidentally
tiny set of test functions could be zero.  It is not:

`hNegNorm_pos`: if `f ∈ L²` has `∫ f² > 0` and *finite* `Hˢ` norm, then `‖f‖_{H^{-s}} > 0`.

The test function that proves it is `f` itself, normalised: `ψ = f / ‖f‖_{Hˢ}` is admissible and
pairs with `f` to `‖f‖²_{L²} / ‖f‖_{Hˢ} > 0`.

## Conventions

The homogeneity lemmas `l2sq_const_mul`, `gagliardoSq_const_mul` and `hsNormSq_const_mul` state
that all three quantities are homogeneous of degree `2`, which is what the normalisation needs.

## Scope

`hNegNorm_pos` is proved.  It assumes `hsNormSq s μ f ≠ ∞`; for a piecewise constant `f` on a
two-dimensional space this holds exactly for `s < 1/2`, which is not proved here (it needs the
integrability of `dist ^ (-2s)` near the jump set).  The hypothesis is therefore *not* discharged
for a concrete `f`: no concrete measure space, block partition or test function is constructed
anywhere in this library, so the non-vacuity established here is conditional on a caller
supplying one.  See the README for what that costs.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace BlockPoincare

variable {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X] {μ : Measure X} {A : Set X}
  {f g : X → ℝ} {s c : ℝ}

omit [PseudoMetricSpace X] in
/-- `l2sq` is homogeneous of degree two. -/
lemma l2sq_const_mul (c : ℝ) (g : X → ℝ) :
    l2sq μ A (fun x => c * g x) = ENNReal.ofReal (c ^ 2) * l2sq μ A g := by
  rw [l2sq, l2sq, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun x => ?_
  rw [← ENNReal.ofReal_mul (sq_nonneg c), mul_pow]

/-- The Gagliardo seminorm is homogeneous of degree two. -/
lemma gagliardoSq_const_mul (c : ℝ) (g : X → ℝ) :
    gagliardoSq s μ A (fun x => c * g x) = ENNReal.ofReal (c ^ 2) * gagliardoSq s μ A g := by
  rw [gagliardoSq, gagliardoSq, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun x => ?_
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun y => ?_
  rw [← mul_div_assoc, ← ENNReal.ofReal_mul (sq_nonneg c)]
  congr 2
  ring

/-- The `Hˢ` norm is homogeneous of degree two. -/
lemma hsNormSq_const_mul (c : ℝ) (g : X → ℝ) :
    hsNormSq s μ (fun x => c * g x) = ENNReal.ofReal (c ^ 2) * hsNormSq s μ g := by
  rw [hsNormSq, hsNormSq, l2sq_const_mul, gagliardoSq_const_mul, mul_add]

omit [PseudoMetricSpace X] in
lemma l2sq_univ_eq (hf : MemLp f 2 μ) : l2sq μ univ f =
    ENNReal.ofReal (∫ x, f x ^ 2 ∂μ) := by  -- totalisation-audit: allow L1 hyp
  have h : Integrable (fun x => f x ^ 2) (μ.restrict univ) := by
    rw [Measure.restrict_univ]; exact hf.integrable_sq
  rw [l2sq_toReal h, setIntegral_univ]

/-- **The dual norm is positive on a nonzero function of finite `Hˢ` norm.**  In particular the
block estimate is not an inequality between two zeros. -/
theorem hNegNorm_pos (hf : MemLp f 2 μ) (hfin : hsNormSq s μ f ≠ ∞)
    (hpos : 0 < ∫ x, f x ^ 2 ∂μ) : 0 < hNegNorm s μ f := by  -- totalisation-audit: allow L1 hyp
  have hne : hsNormSq s μ f ≠ 0 := by
    refine fun h => absurd (le_trans l2sq_le_hsNormSq h.le) (not_le.2 ?_)
    rw [l2sq_univ_eq hf]
    simpa using hpos
  have hN : 0 < (hsNormSq s μ f).toReal := ENNReal.toReal_pos  -- totalisation-audit: allow finite
      hne hfin
  set N := (hsNormSq s μ f).toReal with hNdef  -- totalisation-audit: allow finite
  set c : ℝ := 1 / Real.sqrt N with hc  -- totalisation-audit: allow > 0
  have hcpos : 0 < c := by
    rw [hc]
    exact one_div_pos.2 (Real.sqrt_pos.2 hN)
  have hcsq : c ^ 2 = 1 / N := by  -- totalisation-audit: allow > 0
    rw [hc, div_pow, one_pow, Real.sq_sqrt hN.le]
  have hnorm : hsNormSq s μ (fun x => c * f x) ≤ 1 := by
    rw [hsNormSq_const_mul, hcsq, ← ENNReal.ofReal_toReal hfin, ← hNdef,
      ← ENNReal.ofReal_mul (by positivity)]
    rw [one_div_mul_cancel hN.ne', ENNReal.ofReal_one]
  have hint : Integrable (fun x => f x * (c * f x)) μ :=
    (hf.integrable_sq.const_mul c).congr (.of_forall fun x => by ring)
  have hpair : ∫ x, f x * (c * f x) ∂μ = c * ∫ x, f x ^ 2 ∂μ :=  -- totalisation-audit: allow L1 hyp
      by
    rw [← integral_const_mul]
    exact integral_congr_ae (.of_forall fun x => by ring)
  refine lt_of_lt_of_le ?_ (le_hNegNorm (s := s) (μ := μ) (f := f) (ψ := fun x => c * f x)
    ⟨hf.aestronglyMeasurable.const_mul c, hnorm, hint⟩)
  rw [hpair]
  exact ENNReal.ofReal_pos.2 (mul_pos hcpos hpos)

end BlockPoincare
