/-
`lem:fluctuation-identity` of BALABAN_CORE.tex (`a021c13be348`), the algebra of the step "the integrand" of its proof.

* `chi_expansion`: `Π_{b ∈ S} χ_b = Σ_{P ⊆ S} Π_{b ∈ P}(χ_b - 1)`, the expansion of
  `Π_{b'}(1 - (1 - χ_{b'}))` into the sum over the sets `P` of `eq:mayer-resummed`.
* `chi_split`: for `S₀ ⊆ S`, `Π_{b ∈ S} χ_b = Π_{b ∈ S₀} χ_b · Σ_{P ⊆ S ∖ S₀} Π_{b ∈ P}(χ_b - 1)`.
* `vanishing`: if `χ_b = 0` at a bond `b ∈ S`, the sum over `P` vanishes, so both sides of the identity of the proof
  vanish.
-/
import Mathlib

noncomputable section

namespace CoreLean
namespace FluctuationIdentityAlg

variable {ι R : Type*} [DecidableEq ι] [CommRing R]

/-- `Π_{b ∈ S} χ_b = Σ_{P ⊆ S} Π_{b ∈ P}(χ_b - 1)`. -/
theorem chi_expansion (S : Finset ι) (χ : ι → R) :
    ∏ b ∈ S, χ b = ∑ P ∈ S.powerset, ∏ b ∈ P, (χ b - 1) := by
  have h := Finset.prod_add (fun b => χ b - 1) (fun _ => (1 : R)) S
  simp only [Finset.prod_const_one, mul_one, sub_add_cancel] at h
  exact h

/-- The split along `S₀ ⊆ S`. -/
theorem chi_split (S S₀ : Finset ι) (hS : S₀ ⊆ S) (χ : ι → R) :
    ∏ b ∈ S, χ b = (∏ b ∈ S₀, χ b) * ∑ P ∈ (S \ S₀).powerset, ∏ b ∈ P, (χ b - 1) := by
  rw [← chi_expansion, ← Finset.prod_union Finset.disjoint_sdiff, Finset.union_sdiff_of_subset hS]

/-- If some `χ_b` vanishes, so does the expansion. -/
theorem vanishing (S : Finset ι) (χ : ι → R) {b : ι} (hb : b ∈ S) (h0 : χ b = 0) :
    ∑ P ∈ S.powerset, ∏ c ∈ P, (χ c - 1) = 0 := by
  rw [← chi_expansion]
  exact Finset.prod_eq_zero hb h0

end FluctuationIdentityAlg
end CoreLean

end
