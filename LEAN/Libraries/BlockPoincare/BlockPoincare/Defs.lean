import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Fractional Sobolev quantities on a metric measure space

The three quantities the fractional block Poincaré estimate is stated with: the `L²` energy of a
function on a set, the Gagliardo (fractional Sobolev) seminorm of order `s`, and the dual norm
`‖·‖_{H^{-s}}` defined as a supremum of pairings.  They are defined for an arbitrary metric
measure space `X`; the two–dimensional torus of the manuscript is one instance, obtained by
supplying the torus measure and the torus distance.

## Conventions

All three quantities take values in `ℝ≥0∞`, so that they are *total*: no integrability
hypothesis enters a definition, and monotonicity steps are free.  Explicitly,

* `l2sq μ A g = ∫⁻_A |g|²`;
* `gagliardoSq s μ A g = ∫⁻_A ∫⁻_A |g x - g y|² / dist x y ^ (2 + 2 s)`;
* `hsNormSq s μ g = l2sq μ univ g + gagliardoSq s μ univ g`;
* `hNegNorm s μ f = ⨆ { ⟪f, ψ⟫ : ‖ψ‖_{H^s} ≤ 1 }`, the supremum taken in `ℝ≥0∞` over those
  measurable `ψ` for which the pairing is defined (`Integrable (f * ψ)`), of
  `ENNReal.ofReal ⟪f, ψ⟫`.

Division in `ℝ≥0∞` sends `a / 0` to `∞` for `a ≠ 0` and `0 / 0` to `0`.  On a genuine metric
space the Gagliardo integrand is therefore `0` on the diagonal, which is the intended value; off
the diagonal the denominator is positive.

`hNegNorm` is the honest dual norm of the manuscript: a supremum of pairings, with no completion
and no duality theorem behind it.  `ENNReal.ofReal` truncates a negative pairing to `0`, which is
harmless because the admissible set is symmetric under `ψ ↦ -ψ` (`neg_mem_unitBall`).

## Scope

This module contains definitions and their formal API only: monotonicity in the set, vanishing on
constants, the bridge `l2sq_toReal` between `l2sq` and a Bochner integral, and the two
characteristic properties of a supremum for `hNegNorm`.  Nothing here is an estimate.  The
non-vacuity of these definitions (a function with positive `L²` norm, zero block means and
positive dual norm) is proved in `BlockPoincare.Witness`.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace BlockPoincare

variable {X : Type*} [MeasurableSpace X]

/-- The `L²` energy `∫_A |g|²` of `g` on `A`, as an extended nonnegative real. -/
def l2sq (μ : Measure X) (A : Set X) (g : X → ℝ) : ℝ≥0∞ :=
  ∫⁻ x in A, ENNReal.ofReal (g x ^ 2) ∂μ

/-- The mean of `g` over `A`.  If `μ A` is `0` or `∞` this is a junk value, and every lemma
using it assumes `μ A ≠ 0` and `μ A ≠ ∞`. -/
def mean (μ : Measure X) (A : Set X) (g : X → ℝ) : ℝ :=
  (μ A).toReal⁻¹ * ∫ x in A, g x ∂μ  -- totalisation-audit: allow finite, L1 hyp

variable [PseudoMetricSpace X]

/-- The squared Gagliardo seminorm of order `s` of `g` on `A`:
`∫_A ∫_A |g x - g y|² / dist x y ^ (2 + 2 s)`. -/
def gagliardoSq (s : ℝ) (μ : Measure X) (A : Set X) (g : X → ℝ) : ℝ≥0∞ :=
  ∫⁻ x in A, ∫⁻ y in A,
    -- totalisation-audit: allow `a / 0 = ∞` in `ℝ≥0∞`; on the diagonal `0 / 0 = 0`
    ENNReal.ofReal ((g x - g y) ^ 2) / ENNReal.ofReal (dist x y ^  -- totalisation-audit: allow > 0
        (2 + 2 * s)) ∂μ ∂μ

/-- The squared `Hˢ` norm `‖g‖²_{L²} + [g]²_s`. -/
def hsNormSq (s : ℝ) (μ : Measure X) (g : X → ℝ) : ℝ≥0∞ :=
  l2sq μ univ g + gagliardoSq s μ univ g

/-- Test functions of `Hˢ` norm at most one whose pairing with `f` is defined. -/
def unitBall (s : ℝ) (μ : Measure X) (f : X → ℝ) : Set (X → ℝ) :=
  {ψ | AEStronglyMeasurable ψ μ ∧ hsNormSq s μ ψ ≤ 1 ∧ Integrable (fun x => f x * ψ x) μ}

/-- The dual norm `‖f‖_{H^{-s}} = sup {⟪f, ψ⟫ : ‖ψ‖_{H^s} ≤ 1}`. -/
def hNegNorm (s : ℝ) (μ : Measure X) (f : X → ℝ) : ℝ≥0∞ :=
  ⨆ ψ ∈ unitBall s μ f, ENNReal.ofReal (∫ x, f x * ψ x ∂μ)  -- totalisation-audit: allow L1 hyp

variable {μ : Measure X} {A B : Set X} {g : X → ℝ} {s : ℝ}

omit [PseudoMetricSpace X] in
@[simp] lemma l2sq_zero : l2sq μ A (fun _ => 0) = 0 := by simp [l2sq]

omit [PseudoMetricSpace X] in
lemma l2sq_mono_set (h : A ⊆ B) : l2sq μ A g ≤ l2sq μ B g :=
  lintegral_mono_set h

omit [PseudoMetricSpace X] in
/-- `l2sq` is the Bochner integral of `g²` whenever the latter is integrable. -/
lemma l2sq_toReal (h : Integrable (fun x => g x ^ 2) (μ.restrict A)) :
    l2sq μ A g = ENNReal.ofReal (∫ x in A, g x ^ 2 ∂μ) :=  -- totalisation-audit: allow L1 hyp
  (ofReal_integral_eq_lintegral_ofReal h (.of_forall fun x => sq_nonneg (g x))).symm

omit [PseudoMetricSpace X] in
lemma l2sq_ne_top (h : Integrable (fun x => g x ^ 2) (μ.restrict A)) : l2sq μ A g ≠ ∞ := by
  rw [l2sq_toReal h]; exact ENNReal.ofReal_ne_top

@[simp] lemma gagliardoSq_const (c : ℝ) : gagliardoSq s μ A (fun _ => c) = 0 := by
  simp [gagliardoSq]

lemma gagliardoSq_mono_set (h : A ⊆ B) : gagliardoSq s μ A g ≤ gagliardoSq s μ B g := by
  refine le_trans (lintegral_mono fun x => lintegral_mono_set (μ := μ) h) ?_
  exact lintegral_mono_set h

/-- The Gagliardo seminorm does not change when a constant is added. -/
lemma gagliardoSq_add_const (c : ℝ) :
    gagliardoSq s μ A (fun x => g x + c) = gagliardoSq s μ A g := by
  simp only [gagliardoSq]
  refine lintegral_congr fun x => lintegral_congr fun y => ?_
  congr 2
  ring

@[simp] lemma hsNormSq_zero : hsNormSq s μ (fun _ => 0) = 0 := by
  simp [hsNormSq]

lemma l2sq_le_hsNormSq : l2sq μ univ g ≤ hsNormSq s μ g := le_self_add

lemma gagliardoSq_le_hsNormSq : gagliardoSq s μ univ g ≤ hsNormSq s μ g := le_add_self

/-- The admissible set is symmetric: `ψ ↦ -ψ` preserves it. -/
lemma neg_mem_unitBall {f ψ : X → ℝ} (h : ψ ∈ unitBall s μ f) :
    (fun x => -ψ x) ∈ unitBall s μ f := by
  refine ⟨h.1.neg, ?_, by simpa using h.2.2.neg⟩
  have hl : l2sq μ univ (fun x => -ψ x) = l2sq μ univ ψ := by simp [l2sq]
  have hg : gagliardoSq s μ univ (fun x => -ψ x) = gagliardoSq s μ univ ψ := by
    simp only [gagliardoSq]
    refine lintegral_congr fun x => lintegral_congr fun y => ?_
    congr 2
    ring
  rw [hsNormSq, hl, hg]
  exact h.2.1

/-- Every admissible pairing is below the dual norm. -/
lemma le_hNegNorm {f ψ : X → ℝ} (h : ψ ∈ unitBall s μ f) :
    ENNReal.ofReal (∫ x, f x * ψ x ∂μ) ≤ hNegNorm s μ f :=  -- totalisation-audit: allow L1 hyp
  le_iSup₂ (f := fun ψ (_ : ψ ∈ unitBall s μ f) =>
      ENNReal.ofReal (∫ x, f x * ψ x ∂μ)) ψ h  -- totalisation-audit: allow L1 hyp

/-- A bound valid for every admissible pairing bounds the dual norm. -/
lemma hNegNorm_le {f : X → ℝ} {C : ℝ≥0∞}
    (h : ∀ ψ ∈ unitBall s μ f, ENNReal.ofReal (∫ x, f x * ψ x  -- totalisation-audit: allow L1 hyp
        ∂μ) ≤ C) :
    hNegNorm s μ f ≤ C :=
  iSup₂_le h

@[simp] lemma hNegNorm_zero : hNegNorm s μ (fun _ => 0) = 0 := by
  refine le_antisymm (hNegNorm_le fun ψ _ => ?_) bot_le
  simp

end BlockPoincare
