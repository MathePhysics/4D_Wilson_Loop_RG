import CoreLean.WilsonLoop.Lattice

/-!
# The shape of a loop on the torus

This file defines the geometric quantities of a loop which enter Theorem 1.5 of [WL] and its
Nonvanishing proposition: the chord–arc constant, the corners, the corner isolation, and small
diameter.  The definitions follow [WL] Section 2.3 ("Loops on a Torus", l.421-433), where they
are read on the preimage of the loop in `ℝ⁴`.

## Main definitions

* `CoreLean.WilsonLoop.Loop.perimeter`: the number `P(C)` of bonds.
* `CoreLean.WilsonLoop.Loop.point`: the lift of the loop to `ℝ⁴`, parametrised by arc length.
* `CoreLean.WilsonLoop.Loop.ChordArcLE`: the bound `Λ(C) ≤ Λ` on the chord–arc constant
  ([WL] `def:torus-lengths`).
* `CoreLean.WilsonLoop.Loop.corners`: the corners with their incoming and outgoing orientations.
* `CoreLean.WilsonLoop.Loop.shortestSegment`, `CoreLean.WilsonLoop.Loop.separation`,
  `CoreLean.WilsonLoop.Loop.cornerIsolation`: the lengths `s(C)`, `δ(C)`, and
  `r(C) = min(s(C)/2, δ(C), P(C)/8)` of [WL] `def:torus-lengths`.
* `CoreLean.WilsonLoop.Loop.SmallDiameter`: [WL] `def:loop-ensemble`(ii).
* `CoreLean.WilsonLoop.Ensemble.Admissible`: the loops of an ensemble are admissible
  ([WL] `def:admissible`).

## Implementation notes

* All lengths are in units of the bond of the lattice on which the loop is given.  For a loop
  at level `q` this is the lattice `𝕋_q` with `n = 2 * L ^ (m_T + q)` sites per side, and the
  period `T` of the torus is `n` in these units.  The quantities `Λ(C)` and `P(C)/r(C)` do not
  depend on the lattice on which the loop is read ([WL] l.118).
* The lift of a loop starts at the representative of the initial site of the first bond with
  coordinates in `[0, n)` and is continued through all arc lengths `t ≥ 0`, the bonds being
  read cyclically.  For a loop which winds around the torus the lift is not closed.
* The chord–arc constant is not defined as a number: only the bound `Λ(C) ≤ Λ` is used.
* The distance on `Fin 4 → ℝ` is the `ℓ^∞`-distance, which is the distance of [WL].
-/

noncomputable section

namespace CoreLean

namespace WilsonLoop

variable {n : ℕ}

/-! ### The lift of a loop to `ℝ⁴` -/

/-- The displacement `± e_μ` of an orientation, in `ℤ⁴`. -/
def orientVec (o : Fin 4 × Bool) : Fin 4 → ℤ :=
  if o.2 then Pi.single o.1 1 else -Pi.single o.1 1

/-- The perimeter `P(C)`: the number of bonds ([WL] l.260).  For a loop at level `q` this is the
number `P_q(C)` of its bonds in `𝕋_q` ([WL] l.149). -/
def Loop.perimeter (C : Loop n) : ℕ := C.bonds.length

/-- The orientation `v_i` of the `i`-th bond, the index being read modulo the perimeter
([WL] l.260). -/
def Loop.orientAt (C : Loop n) (i : ℕ) : Fin 4 × Bool :=
  C.orients.getD (i % C.perimeter) (0, true)

/-- The site `x̃_i`, `i ≥ 0`, of the lift of the loop to `ℤ⁴`, so that
`x̃_{i + P(C)} = x̃_i + n w(C)` with the winding vector `w(C)` of [WL] `def:loop-ensemble`(i). -/
def Loop.liftSite (C : Loop n) (i : ℕ) : Fin 4 → ℤ :=
  (fun μ ↦ ((C.base μ).val : ℤ)) + ∑ j ∈ Finset.range i, orientVec (C.orientAt j)

/-- The point of the lifted loop at arc length `t ≥ 0` from the initial site.  For
`0 ≤ t < P(C)` these points represent the points of `|C|`, the union of the closed unit intervals
of the bonds ([WL] l.425). -/
def Loop.point (C : Loop n) (t : ℝ) : Fin 4 → ℝ := fun μ ↦
  (C.liftSite ⌊t⌋₊ μ : ℝ) + Int.fract t * (orientVec (C.orientAt ⌊t⌋₊) μ : ℝ)

/-- The period vector `n k` of the torus, for `k ∈ ℤ⁴`. -/
def periodShift (n : ℕ) (k : Fin 4 → ℤ) : Fin 4 → ℝ := fun μ ↦ (n : ℝ) * (k μ : ℝ)

/-! ### The chord–arc constant ([WL] `def:torus-lengths`, l.425-431) -/

/-- The periodic distance `|x - y|_N` on `ℝ⁴ / N ℤ⁴`: the least `ℓ^∞`-distance between a preimage
of `x` and a preimage of `y` ([WL] l.425).  In each coordinate this is the distance of
`x μ - y μ` to the nearest multiple of `N`. -/
def torusDist (N : ℕ) (x y : Fin 4 → ℝ) : ℝ :=
  Finset.sup' Finset.univ Finset.univ_nonempty fun μ ↦
    |(x μ - y μ) - N * round ((x μ - y μ) / N)|

/-- The distance `d_C` along the loop: the length of the shorter of the two arcs of `|C|` which
join the points at arc lengths `t` and `t'` ([WL] l.425). -/
def Loop.arcDist (C : Loop n) (t t' : ℝ) : ℝ := min |t - t'| (C.perimeter - |t - t'|)

/-- The bound `Λ(C) ≤ Λ` on the chord–arc constant
`Λ(C) = max(2, sup { d_C(x, y) / |x - y|_N : x ≠ y ∈ |C| })` of [WL] `eq:torus-lengths`. -/
def Loop.ChordArcLE (C : Loop n) (Λ : ℝ) : Prop :=
  2 ≤ Λ ∧ ∀ t t' : ℝ, 0 ≤ t → t < C.perimeter → 0 ≤ t' → t' < C.perimeter →
    C.arcDist t t' ≤ Λ * torusDist n (C.point t) (C.point t')

/-! ### Corners and segments ([WL] l.262 and l.425) -/

/-- The corners of a loop, each given by the pair `(v_c, w_c)` of its incoming and its outgoing
orientation ([WL] l.262). -/
def Loop.corners (C : Loop n) : List ((Fin 4 × Bool) × (Fin 4 × Bool)) :=
  (C.orients.zip (C.orients.rotate 1)).filter fun p ↦ p.1 ≠ p.2

/-- The lifted site `x̃_i`, `i ≥ 1`, lies over a corner: `v_{i-1} ≠ v_i` ([WL] l.262).  As the
indices are read modulo the perimeter, every corner of the loop occurs with some
`1 ≤ i ≤ P(C)`. -/
def Loop.IsCornerAt (C : Loop n) (i : ℕ) : Prop := 1 ≤ i ∧ C.orientAt (i - 1) ≠ C.orientAt i

/-- The lifted sites `x̃_i` and `x̃_j`, `i < j`, lie over consecutive corners, so that the bonds
`i, …, j - 1` form a segment: a maximal run of consecutive bonds of one orientation
([WL] l.262). -/
def Loop.IsSegment (C : Loop n) (i j : ℕ) : Prop :=
  i < j ∧ C.IsCornerAt i ∧ C.IsCornerAt j ∧ ∀ m, i < m → m < j → ¬ C.IsCornerAt m

/-- The numbers of bonds of the segments of a loop, a loop without corner being its own single
segment ([WL] l.425). -/
def Loop.segmentLengths (C : Loop n) : Set ℕ :=
  {l | (∃ i j, C.IsSegment i j ∧ l = j - i) ∨ ((¬ ∃ i, C.IsCornerAt i) ∧ l = C.perimeter)}

/-- The shortest segment `s(C)`: the least number of bonds of a segment
([WL] `def:torus-lengths`). -/
def Loop.shortestSegment (C : Loop n) : ℕ := sInf C.segmentLengths

/-! ### The unfolding and the corner isolation ([WL] l.425-431) -/

/-- The preimages of the corners in `ℝ⁴`. -/
def Loop.cornerLifts (C : Loop n) : Set (Fin 4 → ℝ) :=
  {x | ∃ (i : ℕ) (k : Fin 4 → ℤ), C.IsCornerAt i ∧ x = C.point (i : ℝ) + periodShift n k}

/-- The segments of the unfolding `Ĉ ⊂ ℝ⁴`, the preimage of `|C|`: the lifts of the segments of
`C`, that is, the closed intervals between two consecutive preimages of corners, or the lines of
`Ĉ` if `C` has no corner ([WL] l.425). -/
def Loop.unfoldingSegments (C : Loop n) : Set (Set (Fin 4 → ℝ)) :=
  {S | (∃ (i j : ℕ) (k : Fin 4 → ℤ), C.IsSegment i j ∧
          S = {x | ∃ t : ℝ, (i : ℝ) ≤ t ∧ t ≤ (j : ℝ) ∧ x = C.point t + periodShift n k}) ∨
       ((¬ ∃ i, C.IsCornerAt i) ∧ ∃ k : Fin 4 → ℤ,
          S = {x | ∃ s : ℝ, x = C.point 0 + s • (fun μ ↦ (orientVec (C.orientAt 0) μ : ℝ)) +
            periodShift n k})}

/-- The separation `δ(C)`: the least `ℓ^∞`-distance between two distinct non-adjacent segments
of the unfolding, two distinct segments being adjacent if they share a preimage of a corner
([WL] `def:torus-lengths` and l.425). -/
def Loop.separation (C : Loop n) : ℝ :=
  sInf {d | ∃ S ∈ C.unfoldingSegments, ∃ S' ∈ C.unfoldingSegments, S ≠ S' ∧
    (¬ ∃ x ∈ C.cornerLifts, x ∈ S ∧ x ∈ S') ∧ ∃ x ∈ S, ∃ y ∈ S', d = dist x y}

/-- The corner isolation `r(C) = min(s(C)/2, δ(C), P(C)/8)` ([WL] `eq:torus-lengths`). -/
def Loop.cornerIsolation (C : Loop n) : ℝ :=
  min ((C.shortestSegment : ℝ) / 2) (min C.separation ((C.perimeter : ℝ) / 8))

/-- The ratio `P(C)/r(C)` of the perimeter to the corner isolation ([WL] l.118). -/
def Loop.isolationRatio (C : Loop n) : ℝ := (C.perimeter : ℝ) / C.cornerIsolation

/-! ### Small diameter ([WL] `def:loop-ensemble`(ii), l.107) -/

/-- The loop has small diameter: its winding vector vanishes, so that its lift is a closed path,
and the `ℓ^∞`-diameter of the lift satisfies `3 diam(C) < T`, where `T = n`. -/
def Loop.SmallDiameter (C : Loop n) : Prop :=
  C.liftSite C.perimeter = C.liftSite 0 ∧
    3 * Metric.diam (C.point '' Set.Icc (0 : ℝ) (C.perimeter : ℝ)) < (n : ℝ)

/-! ### Ensembles -/

section Ensemble

variable {N : ℕ} {G : GaugeGroup N}

/-- The loops of the ensemble are admissible for the bound `Λ` on the chord–arc constants:
`Λ(Cᵢ) ≤ Λ` for all `i` ([WL] `def:admissible`, l.151-155). -/
def Ensemble.Admissible (E : Ensemble n G) (Λ : ℝ) : Prop := ∀ p ∈ E.loops, p.1.ChordArcLE Λ

/-- The loops of the ensemble have small diameter. -/
def Ensemble.SmallDiameter (E : Ensemble n G) : Prop := ∀ p ∈ E.loops, p.1.SmallDiameter

end Ensemble

end WilsonLoop

end CoreLean
