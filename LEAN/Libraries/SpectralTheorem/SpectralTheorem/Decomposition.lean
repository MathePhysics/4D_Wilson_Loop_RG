import SpectralTheorem.Cyclic
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Order.Zorn

/-!
# Decomposition into cyclic subspaces

Reed–Simon I, §VII.2, Lemma 2, p. 226: a Hilbert space is a direct sum of subspaces, each
invariant under the operator and cyclic for it.  Reed–Simon assume `H` separable, obtain countably
many summands, and leave the proof as "a simple Zornication" (Problem 15).  Here `H` is arbitrary:
Zorn's lemma gives a set of vectors whose cyclic subspaces are pairwise orthogonal and maximal
with this property, and maximality forces the cyclic subspaces to span a dense subspace, because
a vector orthogonal to all of them has a cyclic subspace orthogonal to all of them
(`cyclicSubmodule_isOrtho`).

Combined with the cyclic isometries `L²(σ(T), μ_ψ) → H` of `SpectralTheorem.Cyclic`, this makes
`H` a Hilbert sum of the spaces `L²(σ(T), μ_ψ)`.

## Main definitions and results

* `SpectralTheorem.CyclicDecomposition T`: a set of vectors with pairwise orthogonal cyclic
  subspaces, such that only `0` is orthogonal to all of them.
* `SpectralTheorem.CyclicDecomposition.nonempty`: such a decomposition exists (Zorn).
* `SpectralTheorem.CyclicDecomposition.isHilbertSum`: `H` is the Hilbert sum of the
  `L²(σ(T), μ_ψ)`, `ψ` in the decomposition, through the cyclic isometries.
* `SpectralTheorem.CyclicDecomposition.equiv`: the resulting unitary
  `H ≃ ⊕̂ L²(σ(T), μ_ψ)` (mathlib's `lp`, with `p = 2`).
-/

noncomputable section

open scoped InnerProductSpace

namespace SpectralTheorem

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (T : H →L[ℂ] H) [hT : IsStarNormal T]

/-- A set of vectors whose cyclic subspaces are pairwise orthogonal. -/
def IsCyclicOrthogonal (s : Set H) : Prop :=
  s.Pairwise fun ψ φ => cyclicSubmodule T ψ ⟂ cyclicSubmodule T φ

/-- **A cyclic decomposition** of `H` for `T`: vectors with pairwise orthogonal cyclic subspaces
such that only `0` is orthogonal to all of them (Reed–Simon I, §VII.2, Lemma 2, p. 226). -/
structure CyclicDecomposition where
  /-- The generating vectors. -/
  vectors : Set H
  /-- The cyclic subspaces are pairwise orthogonal. -/
  pairwise : IsCyclicOrthogonal T vectors
  /-- The cyclic subspaces are total: only `0` is orthogonal to all of them. -/
  total : ∀ v : H, (∀ ψ ∈ vectors, v ∈ (cyclicSubmodule T ψ)ᗮ) → v = 0

/-- **Existence of a cyclic decomposition**, by Zorn's lemma. -/
theorem CyclicDecomposition.nonempty : Nonempty (CyclicDecomposition T) := by
  obtain ⟨s, hs⟩ := zorn_subset {s : Set H | IsCyclicOrthogonal T s} fun c hc hchain => by
    refine ⟨⋃₀ c, fun ψ hψ φ hφ hne => ?_, fun s hs => Set.subset_sUnion_of_mem hs⟩
    obtain ⟨a, ha, hψa⟩ := Set.mem_sUnion.mp hψ
    obtain ⟨b, hb, hφb⟩ := Set.mem_sUnion.mp hφ
    rcases hchain.total ha hb with hab | hba
    · exact hc hb (hab hψa) hφb hne
    · exact hc ha hψa (hba hφb) hne
  refine ⟨⟨s, hs.prop, fun v hv => ?_⟩⟩
  have hins : IsCyclicOrthogonal T (insert v s) := by
    refine hs.prop.insert fun ψ hψ _ => ⟨?_, ?_⟩
    · exact cyclicSubmodule_isOrtho T (hv ψ hψ)
    · exact (cyclicSubmodule_isOrtho T (hv ψ hψ)).symm
  have hvs : v ∈ s := hs.eq_of_subset hins (Set.subset_insert v s) ▸ Set.mem_insert v s
  have hvv := hv v hvs
  have hself := mem_cyclicSubmodule_self T v
  exact inner_self_eq_zero.mp ((Submodule.mem_orthogonal' _ _).mp hvv v hself)

namespace CyclicDecomposition

variable {T} (D : CyclicDecomposition T)

/-- The spaces `L²(σ(T), μ_ψ)` of a cyclic decomposition. -/
abbrev Summand (ψ : D.vectors) : Type _ :=
  MeasureTheory.Lp ℂ 2 (spectralMeasure T (ψ : H))

/-- The cyclic isometries `L²(σ(T), μ_ψ) → H` of a decomposition form an orthogonal family. -/
theorem orthogonalFamily :
    OrthogonalFamily ℂ D.Summand fun ψ => cyclicIsometry T (ψ : H) := by
  intro ψ φ hne x y
  have hx : cyclicIsometry T (ψ : H) x ∈ cyclicSubmodule T ψ := by
    rw [← range_cyclicIsometry]
    exact ⟨x, rfl⟩
  have hy : cyclicIsometry T (φ : H) y ∈ cyclicSubmodule T φ := by
    rw [← range_cyclicIsometry]
    exact ⟨y, rfl⟩
  exact (D.pairwise ψ.2 φ.2 fun h => hne (Subtype.ext h)).inner_eq hx hy

/-- **`H` is the Hilbert sum of the spaces `L²(σ(T), μ_ψ)`** of a cyclic decomposition. -/
theorem isHilbertSum : IsHilbertSum ℂ D.Summand fun ψ => cyclicIsometry T (ψ : H) := by
  refine IsHilbertSum.mk D.orthogonalFamily ?_
  rw [top_le_iff, Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
  intro v hv
  refine D.total v fun ψ hψ => ?_
  rw [← range_cyclicIsometry]
  refine (Submodule.mem_orthogonal _ v).mpr fun u hu => ?_
  exact (Submodule.mem_orthogonal _ v).mp hv u
    (Submodule.mem_iSup_of_mem (⟨ψ, hψ⟩ : D.vectors) hu)

/-- **The unitary `H ≃ ⊕̂_ψ L²(σ(T), μ_ψ)`** of a cyclic decomposition. -/
def equiv : H ≃ₗᵢ[ℂ] lp D.Summand 2 :=
  D.isHilbertSum.linearIsometryEquiv

open scoped Classical in
/-- The inverse unitary sends a single component `φ ∈ L²(σ(T), μ_ψ)` to `U_ψ φ ∈ H`. -/
theorem equiv_symm_single (ψ : D.vectors) (φ : D.Summand ψ) :
    D.equiv.symm (lp.single 2 ψ φ) = cyclicIsometry T (ψ : H) φ :=
  D.isHilbertSum.linearIsometryEquiv_symm_apply_single φ

end CyclicDecomposition

end SpectralTheorem
