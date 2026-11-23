import SpectralTheorem.MultiplicationBounded
import Mathlib.Algebra.Star.Subalgebra

/-!
# Bounded Borel functions and multiplication `⋆`-homomorphisms

`boundedMeasurable X` is the `⋆`-subalgebra of `X → ℂ` of bounded measurable functions; for a
topological space with its Borel σ-algebra this is Reed–Simon's `𝓑`, the domain of the Borel
functional calculus (Reed–Simon I, Theorem VII.2, p. 225).

For a measurable map `F : M → X` and a measure `μ` on `M`, multiplication by `g ∘ F` on `L²(M, μ)`
is a `⋆`-algebra homomorphism `boundedMeasurable X → 𝓛(L²(M, μ))`
(`SpectralTheorem.mulHom`), by the algebra of `mulL` (`SpectralTheorem.MultiplicationBounded`).

## Main definitions

* `SpectralTheorem.boundedMeasurable X`: bounded measurable functions `X → ℂ`.
* `SpectralTheorem.mulHom μ hF`: the `⋆`-homomorphism `g ↦ M_{g ∘ F}`.
-/

noncomputable section

open scoped ENNReal ComplexConjugate
open MeasureTheory

namespace SpectralTheorem

variable (X : Type*) [MeasurableSpace X]

/-- **Bounded measurable functions** `X → ℂ`, a `⋆`-subalgebra of `X → ℂ`. -/
def boundedMeasurable : StarSubalgebra ℂ (X → ℂ) where
  carrier := {g | Measurable g ∧ ∃ C, ∀ x, ‖g x‖ ≤ C}
  mul_mem' := by
    rintro f g ⟨hf, Cf, hCf⟩ ⟨hg, Cg, hCg⟩
    refine ⟨hf.mul hg, |Cf| * |Cg|, fun x => ?_⟩
    rw [Pi.mul_apply, norm_mul]
    exact mul_le_mul ((hCf x).trans (le_abs_self Cf)) ((hCg x).trans (le_abs_self Cg))
      (norm_nonneg _) (abs_nonneg _)
  one_mem' := ⟨measurable_const, 1, fun _ => by simp⟩
  add_mem' := by
    rintro f g ⟨hf, Cf, hCf⟩ ⟨hg, Cg, hCg⟩
    exact ⟨hf.add hg, Cf + Cg, fun x => (norm_add_le _ _).trans (add_le_add (hCf x) (hCg x))⟩
  zero_mem' := ⟨measurable_const, 0, fun _ => by simp⟩
  algebraMap_mem' c := ⟨measurable_const, ‖c‖, fun _ => by simp⟩
  star_mem' := by
    rintro f ⟨hf, C, hC⟩
    exact ⟨continuous_star.measurable.comp hf, C, fun x => by simpa using hC x⟩

variable {X}

theorem mem_boundedMeasurable {g : X → ℂ} :
    g ∈ boundedMeasurable X ↔ Measurable g ∧ ∃ C, ∀ x, ‖g x‖ ≤ C :=
  Iff.rfl

theorem boundedMeasurable.measurable (g : boundedMeasurable X) : Measurable (g : X → ℂ) :=
  g.2.1

theorem boundedMeasurable.exists_bound (g : boundedMeasurable X) :
    ∃ C, 0 ≤ C ∧ ∀ x, ‖(g : X → ℂ) x‖ ≤ C := by
  obtain ⟨C, hC⟩ := g.2.2
  exact ⟨|C|, abs_nonneg C, fun x => (hC x).trans (le_abs_self C)⟩

/-- Bounded continuous functions are bounded measurable. -/
theorem continuous_mem_boundedMeasurable [TopologicalSpace X] [OpensMeasurableSpace X]
    {g : X → ℂ} (hg : Continuous g) (hbd : ∃ C, ∀ x, ‖g x‖ ≤ C) : g ∈ boundedMeasurable X :=
  ⟨hg.measurable, hbd⟩

/-- Continuous functions on a compact space are bounded measurable. -/
theorem continuousMap_mem_boundedMeasurable [TopologicalSpace X] [OpensMeasurableSpace X]
    [CompactSpace X] (g : C(X, ℂ)) : (g : X → ℂ) ∈ boundedMeasurable X :=
  ⟨g.continuous.measurable, ‖g‖, g.norm_coe_le_norm⟩

/-- The inclusion of continuous functions on a compact space into bounded measurable functions,
as a `⋆`-algebra homomorphism. -/
def continuousMapToBoundedMeasurable [TopologicalSpace X] [OpensMeasurableSpace X]
    [CompactSpace X] : C(X, ℂ) →⋆ₐ[ℂ] boundedMeasurable X where
  toFun g := ⟨g, continuousMap_mem_boundedMeasurable g⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl

@[simp]
theorem coe_continuousMapToBoundedMeasurable [TopologicalSpace X] [OpensMeasurableSpace X]
    [CompactSpace X] (g : C(X, ℂ)) :
    ((continuousMapToBoundedMeasurable g : boundedMeasurable X) : X → ℂ) = g :=
  rfl

section MulHom

variable {M : Type*} [MeasurableSpace M] (μ : Measure M)

/-- `g ∘ F` is in `L^∞` for bounded measurable `g`. -/
theorem memLp_top_comp {F : M → X} (hF : Measurable F) (g : boundedMeasurable X) :
    MemLp ((g : X → ℂ) ∘ F) ∞ μ := by
  obtain ⟨C, -, hC⟩ := boundedMeasurable.exists_bound g
  exact memLp_top_of_bound ((boundedMeasurable.measurable g).comp hF).aestronglyMeasurable C
    (Filter.Eventually.of_forall fun m => hC (F m))

/-- **Multiplication by `g ∘ F`** on `L²(M, μ)`, as a `⋆`-algebra homomorphism
`boundedMeasurable X → 𝓛(L²(M, μ))`. -/
def mulHom {F : M → X} (hF : Measurable F) :
    boundedMeasurable X →⋆ₐ[ℂ] (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) where
  toFun g := mulL ((g : X → ℂ) ∘ F) (memLp_top_comp μ hF g)
  map_one' := mulL_one _
  map_mul' f g := mulL_mul (memLp_top_comp μ hF f) (memLp_top_comp μ hF g)
  map_zero' := mulL_zero _
  map_add' f g := mulL_add (memLp_top_comp μ hF f) (memLp_top_comp μ hF g)
  commutes' c := by
    conv_rhs => rw [Algebra.algebraMap_eq_smul_one]
    exact mulL_const (μ := μ) c _
  map_star' g := (star_mulL (memLp_top_comp μ hF g)).symm

theorem mulHom_apply {F : M → X} (hF : Measurable F) (g : boundedMeasurable X) :
    mulHom μ hF g = mulL ((g : X → ℂ) ∘ F) (memLp_top_comp μ hF g) :=
  rfl

end MulHom

end SpectralTheorem
