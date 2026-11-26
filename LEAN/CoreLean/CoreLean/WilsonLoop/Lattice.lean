import CoreLean.Lattice
import CoreLean.Algebra

/-!
# The lattice theory, loops, and loop ensembles

This file defines the lattice theory of Section 1.1 and the loop ensembles of Section 1.2 of
`Continuum Limit Manuscripts/WILSON_LOOPS_CONTINUUM_LIMIT.tex`, which is referred to as [WL]
throughout `CoreLean.WilsonLoop`.  References `l.N` are to lines of that file.

The lattice, its bonds, the configurations, the parallel transport, the action, and the gauge
group are those of `CoreLean`: `CoreLean.Site`, `CoreLean.Bond`, `CoreLean.Config`,
`CoreLean.Config.hol`, `CoreLean.action`, `CoreLean.GaugeGroup`.  This file adds what [WL] needs
beyond them.

## Main definitions

* `CoreLean.WilsonLoop.GField G n`: the gauge fields with values in `G`, the space on which the
  measure of the lattice theory lives.
* `CoreLean.WilsonLoop.haar`, `CoreLean.WilsonLoop.haarField`, `CoreLean.WilsonLoop.expect`: the
  normalised Haar measure, its product over the positive bonds, and the expectation of the
  lattice theory ([WL] `eq:lattice-measure`).
* `CoreLean.WilsonLoop.Loop n`: a loop ([WL] `def:loop-ensemble`(i)).
* `CoreLean.WilsonLoop.Irrep G`: an irreducible unitary representation, with
  `CoreLean.WilsonLoop.Irrep.character`.
* `CoreLean.WilsonLoop.Ensemble n G`: a loop ensemble ([WL] `def:loop-ensemble`(iii)).
* `CoreLean.WilsonLoop.Ensemble.observable`: the observable `W_𝒞` of an ensemble, read on a finer
  lattice ([WL] `eq:ensemble-observable`).

## Implementation notes

* As in `CoreLean.Lattice`, lengths are in units of the lattice spacing and the lattice is
  `Site n = (ℤ / n ℤ)⁴`.  In [WL] the lattice `𝕋_K` has spacing `u L^{-K}` and period
  `T = 2 L^{m_T} u`, hence `n = 2 * L ^ (m_T + K)` sites per side (l.83-87).  The length `u` does
  not enter the lattice theory.
* A configuration of `CoreLean` has values in `GL(N, ℂ)`.  The measure of [WL] is a measure on
  the gauge fields with values in `G`, which are the functions `GField G n` from the positive
  bonds to the subgroup `G.carrier`; `GField.toConfig` is the configuration of such a field.
* `G.carrier` carries the Borel σ-algebra of its topology as a subspace of `GL(N, ℂ)` (the
  instance `BorelSpace GL(N, ℂ)` below), and the normalised Haar measure exists when it is
  compact, which is a typeclass assumption.
* A `Loop` is a list of bonds and so has a first bond.  A loop of [WL] is this datum up to
  cyclic rotation; `CoreLean.WilsonLoop.Loop.character_hol_rotate` shows that the observable
  does not depend on the choice.
* For `n = 0` (where `ZMod 0 = ℤ`) the inclusion `scaleSite` of a lattice in a finer one is not
  the intended map.  The action and the measure require `NeZero n`, and the main statement uses
  `n = 2 * L ^ k` with `L ≠ 0` only.
-/

open MeasureTheory

noncomputable section

namespace CoreLean

variable {N n : ℕ}

local notation "GLN" => (Matrix (Fin N) (Fin N) ℂ)ˣ

/-- The orientation `± e_μ` of a bond: its direction `μ` and whether it is positive
([WL] l.260). -/
def Bond.orient (b : Bond n) : Fin 4 × Bool := (b.dir, b.pos)

namespace WilsonLoop

/-! ### Gauge fields with values in `G` ([WL] l.87) -/

/-- A gauge field with values in `G`: an element of `G` for each positive bond. -/
abbrev GField (G : GaugeGroup N) (n : ℕ) := Fin 4 → Site n → G.carrier

namespace GField

variable {G : GaugeGroup N}

/-- The configuration of a gauge field with values in `G`. -/
def toConfig (V : GField G n) : Config N n := fun μ x ↦ (V μ x : GLN)

/-- The value of a gauge field with values in `G` on a bond lies in `G`. -/
lemma val_mem (V : GField G n) (b : Bond n) : V.toConfig.val b ∈ G.carrier := by
  unfold Config.val toConfig
  split_ifs
  · exact (V _ _).2
  · exact G.carrier.inv_mem (V _ _).2

/-- The parallel transport of a gauge field with values in `G` lies in `G`. -/
lemma hol_mem (V : GField G n) (γ : List (Bond n)) : V.toConfig.hol γ ∈ G.carrier := by
  refine G.carrier.list_prod_mem fun g hg ↦ ?_
  obtain ⟨b, -, rfl⟩ := List.mem_map.1 hg
  exact V.val_mem b

/-- The parallel transport `U(γ) = U(b₁) ⋯ U(b_k)` of a gauge field with values in `G` along
the path `γ = (b₁, …, b_k)`, as an element of `G` ([WL] l.87). -/
def hol (V : GField G n) (γ : List (Bond n)) : G.carrier := ⟨V.toConfig.hol γ, V.hol_mem γ⟩

end GField

/-! ### The lattice theory ([WL] `eq:lattice-measure`, l.87-91) -/

section Measure

open scoped Matrix.Norms.L2Operator in
/-- The topology of `GL(N, ℂ)` is its topology as a subset of the matrices. -/
theorem isInducing_units_val :
    Topology.IsInducing (Units.val : GLN → Matrix (Fin N) (Fin N) ℂ) :=
  Units.isOpenEmbedding_val.isInducing

/-- The σ-algebra of `GL(N, ℂ)` is the Borel σ-algebra of its topology.  Hence so is that of
the subgroup `G.carrier` (`Subtype.borelSpace`). -/
instance : BorelSpace GLN := by
  constructor
  rw [(isInducing_units_val (N := N)).eq_induced, borel_comap, ← BorelSpace.measurable_eq]
  rfl

variable (G : GaugeGroup N) [CompactSpace G.carrier]

/-- The normalised Haar measure of the gauge group ([WL] l.91). -/
def haar : Measure G.carrier := Measure.haarMeasure ⊤

/-- The measure `dU`: the product of the normalised Haar measures over the positive bonds
([WL] l.91). -/
def haarField (n : ℕ) [NeZero n] : Measure (GField G n) :=
  Measure.pi fun _ ↦ Measure.pi fun _ ↦ haar G

/-- The expectation of `f` in the lattice theory at `β = g₀⁻²`, with respect to the probability
measure `Z⁻¹ exp (-β ∑_p (1 - Re tr U(∂p))) dU` ([WL] `eq:lattice-measure`).  The sum over the
plaquettes is `CoreLean.action`, which is real on gauge fields
(`CoreLean.action_gaugeField`). -/
def expect (n : ℕ) [NeZero n] (β : ℝ) (f : GField G n → ℂ) : ℂ :=
  (∫ V, (Real.exp (-β * (action V.toConfig).re) : ℂ) * f V ∂(haarField G n)) /
    ((∫ V, Real.exp (-β * (action V.toConfig).re) ∂(haarField G n) : ℝ) : ℂ)

end Measure

/-! ### Loops and ensembles ([WL] `def:loop-ensemble`, l.103-110) -/

/-- A loop on the lattice with `n` sites per side: a closed path of at least three bonds which
visits no site twice, with its orientation ([WL] `def:loop-ensemble`(i)).  Loops may wind around
the torus. -/
structure Loop (n : ℕ) where
  /-- The consecutive bonds `b₁, …, b_P`. -/
  bonds : List (Bond n)
  /-- The loop has at least three bonds. -/
  three_le : 3 ≤ bonds.length
  /-- The path is closed: each bond ends where the next one begins, and the last bond ends
  where the first one begins. -/
  closed : ∀ p ∈ bonds.zip (bonds.rotate 1), p.1.plus = p.2.site
  /-- The path visits no site twice. -/
  nodup : (bonds.map Bond.site).Nodup

/-- The sites of a loop. -/
def Loop.sites (C : Loop n) : List (Site n) := C.bonds.map Bond.site

/-- The orientations `v₁, …, v_P` of the consecutive bonds of a loop ([WL] l.260). -/
def Loop.orients (C : Loop n) : List (Fin 4 × Bool) := C.bonds.map Bond.orient

/-- The initial site of the first bond of a loop. -/
def Loop.base (C : Loop n) : Site n := C.sites.headD 0

/-- An irreducible unitary representation `π` of `G`, in matrix form
([WL] `def:loop-ensemble`(iii)). -/
structure Irrep (G : GaugeGroup N) where
  /-- The dimension of the representation. -/
  dim : ℕ
  /-- The dimension is positive. -/
  dim_pos : 0 < dim
  /-- The representation, as a homomorphism to the unitary group. -/
  toHom : G.carrier →* Matrix.unitaryGroup (Fin dim) ℂ
  /-- The representation is continuous. -/
  continuous_toHom : Continuous toHom
  /-- The representation is irreducible: an invariant subspace is `0` or everything. -/
  irreducible : ∀ W : Submodule ℂ (Fin dim → ℂ),
    (∀ g : G.carrier, ∀ v ∈ W, (toHom g : Matrix (Fin dim) (Fin dim) ℂ).mulVec v ∈ W) →
      W = ⊥ ∨ W = ⊤

/-- The normalised character `χ = (dim π)⁻¹ Tr π` ([WL] `def:loop-ensemble`(iii)), with the
normalised trace `CoreLean.ntr`. -/
def Irrep.character {G : GaugeGroup N} (π : Irrep G) (g : G.carrier) : ℂ :=
  ntr (π.toHom g : Matrix (Fin π.dim) (Fin π.dim) ℂ)

/-- A loop ensemble `𝒞 = ((C₁, χ₁), …, (C_k, χ_k))`, `k ≥ 1`: a finite family of pairwise
vertex-disjoint loops, each with an irreducible unitary representation
([WL] `def:loop-ensemble`(iii)). -/
structure Ensemble (n : ℕ) (G : GaugeGroup N) where
  /-- The loops with their representations. -/
  loops : List (Loop n × Irrep G)
  /-- There is at least one loop. -/
  ne_nil : loops ≠ []
  /-- Distinct loops have no site in common. -/
  disjoint : loops.Pairwise fun a b ↦ ∀ x ∈ a.1.sites, x ∉ b.1.sites

/-! ### Reading a loop on a finer lattice ([WL] l.101) and the observable -/

/-- The inclusion of the lattice with `n` sites per side in the lattice with `r * n` sites per
side, whose spacing is `r` times smaller: the coordinates are multiplied by `r`. -/
def scaleSite (r : ℕ) (x : Site n) : Site (r * n) :=
  fun μ ↦ ((r * (x μ).val : ℕ) : ZMod (r * n))

/-- A bond of the coarse lattice as a path of the finer lattice: `r` consecutive bonds of the
same orientation, the first of which begins at the image of the initial site. -/
def refineBond (r : ℕ) (b : Bond n) : List (Bond (r * n)) :=
  (List.range r).map fun j : ℕ ↦
    ⟨scaleSite r b.site + (if b.pos then (j : ℤ) else -(j : ℤ)) • unit (r * n) b.dir,
      b.dir, b.pos⟩

/-- A path of the coarse lattice as a path of the finer lattice ([WL] l.101). -/
def refinePath (r : ℕ) (γ : List (Bond n)) : List (Bond (r * n)) := γ.flatMap (refineBond r)

section Observable

variable {G : GaugeGroup N}

/-- The holonomy `U(C)` of a loop of the lattice with `n` sites per side in a gauge field of
the lattice with `r * n` sites per side ([WL] l.101, l.112). -/
def Loop.hol (C : Loop n) (r : ℕ) (V : GField G (r * n)) : G.carrier :=
  V.hol (refinePath r C.bonds)

/-- The observable `W_𝒞(U) = ∏ᵢ χᵢ(U(Cᵢ))` of an ensemble ([WL] `eq:ensemble-observable`). -/
def Ensemble.observable (E : Ensemble n G) (r : ℕ) (V : GField G (r * n)) : ℂ :=
  (E.loops.map fun p ↦ p.2.character (p.1.hol r V)).prod

end Observable

end WilsonLoop

end CoreLean
