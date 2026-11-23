/-
`lem:support` of BALABAN_CORE.tex (`a021c13be348`), in abstract form. The bonds `β`; the bonds `W` of the support and
those `E₁ ⊂ W` with an end in `Ω₁` (the remark before the lemma); gauge fields `β → G`. The set `𝔘(ε₀)` is given by
local conditions `cond i`, each depending on the field on a set `supp i` of bonds (the plaquettes and the bonds of
`eq:plaquette-regular`); those of `W` (`ιW`) have their supports in `W`, the others have no bond in `E₁`. The
constraint `𝔙(V)` is `U = V` on the bonds with no end in `Ω₁` (where `M⁰` is the identity) together with a condition
`Cons` on the field on `W` (the averages of the layers `j ≥ 1`, `lem:average`). The action is a sum of local terms over
the plaquettes, those not of `W` having no bond in `E₁`. Then the restriction is a bijection of
`𝔘(ε₀) ∩ 𝔙(V)` onto `𝔘_W(ε₀) ∩ 𝔙_W(V|_W)` (`restrict_bijOn`), `A(U) - A_W(U|_W)` is constant on it (`action_diff`),
and minimality is the same on both sides (`minimal_iff`), given one `U₀ ∈ 𝔘(ε₀) ∩ 𝔙(V)` (the hypothesis of the
lemma). The proof is the core's.
-/
import Mathlib

open Classical

noncomputable section

namespace CoreLean
namespace Support

/-- The abstract setting of `lem:support`. -/
structure Setting (β G ι P : Type*) [Fintype P] where
  W : Set β
  E₁ : Set β
  E₁_sub : E₁ ⊆ W
  supp : ι → Set β
  cond : ι → (β → G) → Prop
  cond_local : ∀ i (U U' : β → G), (∀ b ∈ supp i, U b = U' b) → (cond i U ↔ cond i U')
  ιW : Set ι
  supp_W : ∀ i ∈ ιW, supp i ⊆ W
  supp_out : ∀ i ∉ ιW, ∀ b ∈ supp i, b ∉ E₁
  Cons : (W → G) → Prop
  bp : P → Set β
  f : P → (β → G) → ℝ
  f_local : ∀ p (U U' : β → G), (∀ b ∈ bp p, U b = U' b) → f p U = f p U'
  PW : Set P
  bp_out : ∀ p ∉ PW, ∀ b ∈ bp p, b ∉ E₁

namespace Setting

variable {β G ι P : Type*} [Fintype P] (S : Setting β G ι P) (V : β → G)

/-- The restriction `U ↦ U|_W`. -/
def r (U : β → G) : S.W → G := fun b => U b

/-- The continuation of a field on `W` by `V`. -/
def ext (U' : S.W → G) : β → G := fun b => if h : b ∈ S.W then U' ⟨b, h⟩ else V b

/-- `𝔘(ε₀)`. -/
def UU : Set (β → G) := {U | ∀ i, S.cond i U}

/-- `𝔙(V)`. -/
def VV : Set (β → G) := {U | (∀ b, b ∉ S.E₁ → U b = V b) ∧ S.Cons (S.r U)}

/-- `𝔘_W(ε₀)`. -/
def UW : Set (S.W → G) := {U' | ∀ i ∈ S.ιW, S.cond i (S.ext V U')}

/-- `𝔙_W(V|_W)`. -/
def VW : Set (S.W → G) := {U' | (∀ b : S.W, b.1 ∉ S.E₁ → U' b = V b) ∧ S.Cons U'}

/-- The action `A`. -/
def A (U : β → G) : ℝ := ∑ p, S.f p U

/-- The action `A_W` of the plaquettes of `W`. -/
def AW (U' : S.W → G) : ℝ := ∑ p ∈ Finset.univ.filter (· ∈ S.PW), S.f p (S.ext V U')

lemma r_ext (U' : S.W → G) : S.r (S.ext V U') = U' := by
  funext b; simp [r, ext, b.2]

lemma ext_r {U : β → G} (hU : U ∈ S.VV V) : S.ext V (S.r U) = U := by
  funext b
  by_cases h : b ∈ S.W
  · simp [ext, r, h]
  · simp only [ext, h, dite_false]
    exact (hU.1 b fun hb => h (S.E₁_sub hb)).symm

lemma ext_eq_off {U' : S.W → G} (hU' : U' ∈ S.VW V) {b : β} (hb : b ∉ S.E₁) : S.ext V U' b = V b := by
  by_cases h : b ∈ S.W
  · simp only [ext, h, dite_true]; exact hU'.1 ⟨b, h⟩ hb
  · simp [ext, h]

variable {V}

/-- **`lem:support`**: the restriction is a bijection of `𝔘(ε₀) ∩ 𝔙(V)` onto `𝔘_W(ε₀) ∩ 𝔙_W(V|_W)`. -/
theorem restrict_bijOn {U₀ : β → G} (hU₀ : U₀ ∈ S.UU ∩ S.VV V) :
    Set.BijOn S.r (S.UU ∩ S.VV V) (S.UW V ∩ S.VW V) := by
  refine ⟨fun U hU => ⟨fun i _ => ?_, fun b hb => hU.2.1 b hb, hU.2.2⟩, fun U hU U' hU' h => ?_,
    fun U' hU' => ⟨S.ext V U', ⟨fun i => ?_, fun b hb => S.ext_eq_off V hU'.2 hb, ?_⟩, S.r_ext V U'⟩⟩
  · rw [S.ext_r V hU.2]; exact hU.1 i
  · rw [← S.ext_r V hU.2, ← S.ext_r V hU'.2, h]
  · by_cases hi : i ∈ S.ιW
    · exact hU'.1 i hi
    · refine (S.cond_local i _ U₀ fun b hb => ?_).2 (hU₀.1 i)
      have hb' := S.supp_out i hi b hb
      rw [S.ext_eq_off V hU'.2 hb', hU₀.2.1 b hb']
  · rw [S.r_ext]; exact hU'.2.2

/-- **`lem:support`**: `A(U) - A_W(U|_W)` is constant on `𝔘(ε₀) ∩ 𝔙(V)`. -/
theorem action_diff {U₀ U : β → G} (hU₀ : U₀ ∈ S.VV V) (hU : U ∈ S.VV V) :
    S.A U - S.AW V (S.r U) = S.A U₀ - S.AW V (S.r U₀) := by
  have key : ∀ U ∈ S.VV V, S.A U - S.AW V (S.r U) =
      ∑ p ∈ Finset.univ.filter (· ∉ S.PW), S.f p U := by
    intro U hU
    unfold A AW
    rw [S.ext_r V hU, ← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ S.PW)]
    ring
  rw [key U hU, key U₀ hU₀]
  refine Finset.sum_congr rfl fun p hp => S.f_local p _ _ fun b hb => ?_
  have hb' := S.bp_out p (Finset.mem_filter.1 hp).2 b hb
  rw [hU.1 b hb', hU₀.1 b hb']

/-- **`lem:support`**: `U` is minimal in `𝔘(ε₀) ∩ 𝔙(V)` iff `U|_W` is minimal in `𝔘_W(ε₀) ∩ 𝔙_W(V|_W)`. -/
theorem minimal_iff {U : β → G} (hU : U ∈ S.UU ∩ S.VV V) :
    (∀ U' ∈ S.UU ∩ S.VV V, S.A U ≤ S.A U') ↔
      (∀ U'' ∈ S.UW V ∩ S.VW V, S.AW V (S.r U) ≤ S.AW V U'') := by
  have hb := S.restrict_bijOn hU
  constructor
  · intro h U'' hU''
    obtain ⟨U', hU', rfl⟩ := hb.surjOn hU''
    have := S.action_diff hU.2 hU'.2
    have := h U' hU'
    linarith
  · intro h U' hU'
    have := S.action_diff hU.2 hU'.2
    have := h (S.r U') (hb.mapsTo hU')
    linarith

end Setting
end Support
end CoreLean

end
