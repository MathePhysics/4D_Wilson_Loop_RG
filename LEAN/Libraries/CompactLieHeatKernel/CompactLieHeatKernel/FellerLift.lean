import CompactLieHeatKernel.L2Semigroup
import Mathlib.MeasureTheory.Function.ContinuousMapDense

/-!
# Feller lifts of the L² heat semigroup

On a compact space with a full-support finite Borel measure, the inclusion `C(M,ℝ) → L²(M,μ)` is
injective.  Consequently a continuous-function lift of an L² semigroup inherits its semigroup law
and preservation of constants automatically.  These facts are therefore not independent analytic
inputs in the compact-manifold heat-kernel theorem.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace CompactLieHeatKernel

variable
    {M : Type*} [TopologicalSpace M] [CompactSpace M]
    [MeasurableSpace M] [BorelSpace M]
    {μ : Measure M} [IsProbabilityMeasure μ]

/-- A Feller lift of an `L²` Markov semigroup: each continuous-function time slice has the same
`L²` class as the corresponding `L²` semigroup action. -/
structure FellerLift (S : L2SelfAdjointMarkovSemigroup μ) where
  op : ℝ≥0 → C(M, ℝ) →L[ℝ] C(M, ℝ)
  compatible : ∀ t f,
    (ContinuousMap.toLp (E := ℝ) 2 μ ℝ) (op t f) =
      S.op t ((ContinuousMap.toLp (E := ℝ) 2 μ ℝ) f)

namespace FellerLift

variable {S : L2SelfAdjointMarkovSemigroup μ}

/-- The continuous constant-one function represents the `oneL2` vector. -/
theorem continuous_one_toL2 :
    (ContinuousMap.toLp (E := ℝ) 2 μ ℝ) (ContinuousMap.const M (1 : ℝ)) = oneL2 μ := by
  rw [Lp.ext_iff]
  have hcont := ContinuousMap.coeFn_toLp
    (p := (2 : ℝ≥0∞)) (μ := μ) (𝕜 := ℝ) (ContinuousMap.const M (1 : ℝ))
  have hone : ((oneL2 μ : RealL2 μ) : M → ℝ) =ᵐ[μ] (fun _ => (1 : ℝ)) := by
    simpa [oneL2] using
      (@indicatorConstLp_coeFn M ℝ _ (2 : ℝ≥0∞) μ _ Set.univ MeasurableSet.univ
        (measure_ne_top μ Set.univ) (1 : ℝ))
  exact hcont.trans hone.symm

variable [μ.IsOpenPosMeasure]

/-- Compatibility and the L² identity at time zero force the Feller lift to be the identity at
zero. -/
theorem op_zero (F : FellerLift S) :
    F.op 0 = ContinuousLinearMap.id ℝ C(M, ℝ) := by
  apply ContinuousLinearMap.ext
  intro f
  apply ContinuousMap.toLp_injective (p := (2 : ℝ≥0∞)) (𝕜 := ℝ) μ
  calc
    (ContinuousMap.toLp (E := ℝ) 2 μ ℝ) (F.op 0 f)
        = S.op 0 ((ContinuousMap.toLp (E := ℝ) 2 μ ℝ) f) := F.compatible 0 f
    _ = (ContinuousMap.toLp (E := ℝ) 2 μ ℝ) f := S.op_zero_apply _
    _ = (ContinuousMap.toLp (E := ℝ) 2 μ ℝ)
        ((ContinuousLinearMap.id ℝ C(M, ℝ)) f) := by simp

/-- Compatibility and injectivity of `C(M) → L²(M)` force the Feller semigroup law. -/
theorem op_add (F : FellerLift S) (s t : ℝ≥0) :
    F.op (s + t) = (F.op s).comp (F.op t) := by
  apply ContinuousLinearMap.ext
  intro f
  apply ContinuousMap.toLp_injective (p := (2 : ℝ≥0∞)) (𝕜 := ℝ) μ
  calc
    (ContinuousMap.toLp (E := ℝ) 2 μ ℝ) (F.op (s + t) f)
        = S.op (s + t) ((ContinuousMap.toLp (E := ℝ) 2 μ ℝ) f) := F.compatible (s + t) f
    _ = S.op s (S.op t ((ContinuousMap.toLp (E := ℝ) 2 μ ℝ) f)) := by
          rw [S.op_add]
          rfl
    _ = S.op s ((ContinuousMap.toLp (E := ℝ) 2 μ ℝ) (F.op t f)) := by
          rw [F.compatible t f]
    _ = (ContinuousMap.toLp (E := ℝ) 2 μ ℝ) (F.op s (F.op t f)) :=
          (F.compatible s (F.op t f)).symm
    _ = (ContinuousMap.toLp (E := ℝ) 2 μ ℝ) (((F.op s).comp (F.op t)) f) := by rfl

/-- Preservation of the L² constant-one vector forces preservation of the continuous constant-one
function. -/
theorem op_one (F : FellerLift S) (t : ℝ≥0) :
    F.op t (ContinuousMap.const M (1 : ℝ)) = ContinuousMap.const M 1 := by
  apply ContinuousMap.toLp_injective (p := (2 : ℝ≥0∞)) (𝕜 := ℝ) μ
  calc
    (ContinuousMap.toLp (E := ℝ) 2 μ ℝ)
        (F.op t (ContinuousMap.const M (1 : ℝ)))
        = S.op t ((ContinuousMap.toLp (E := ℝ) 2 μ ℝ)
            (ContinuousMap.const M (1 : ℝ))) := F.compatible t _
    _ = S.op t (oneL2 μ) := by rw [continuous_one_toL2]
    _ = oneL2 μ := S.map_one t
    _ = (ContinuousMap.toLp (E := ℝ) 2 μ ℝ) (ContinuousMap.const M (1 : ℝ)) :=
          continuous_one_toL2.symm

end FellerLift
end CompactLieHeatKernel
