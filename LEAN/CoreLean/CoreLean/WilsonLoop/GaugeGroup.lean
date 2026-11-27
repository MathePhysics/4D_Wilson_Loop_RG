import CoreLean.WilsonLoop.Lattice

/-!
# The assumptions on the gauge group and the representation constant

[WL] takes for the gauge group "a compact connected simple Lie group in a fixed unitary
realisation `G ⊂ U(N)`" (l.83), and measures the size of a representation `π` by the constant
`c_π = sup { ‖dπ(X)‖ : X ∈ Lie G, ‖X‖ ≤ 1 }` (`eq:representation-constant`, l.146-149).

The group is a `CoreLean.GaugeGroup`: a subgroup of `GL(N, ℂ)` of unitary matrices.  Its Lie
algebra is `CoreLean.GaugeGroup.lie`, the space `𝔤 = i Lie G` of the Hermitian matrices `A` with
`e^{itA} ∈ G` for all real `t`, which is the convention of [WL] (l.149) and of Bałaban's papers.

## Main definitions

* `CoreLean.GaugeGroup.IsSimple`: the Lie algebra of the group is simple.
* `CoreLean.WilsonLoop.Irrep.IsDifferential`: `D = dπ(iA)` for `A ∈ 𝔤`.
* `CoreLean.WilsonLoop.Irrep.repConst`, `CoreLean.WilsonLoop.Ensemble.repConst`: the constants
  `c_π` and `c_𝒞 = maxᵢ c_{πᵢ}`.

## Implementation notes

* The three assumptions of [WL] on the group enter the main theorem as follows.  Compactness is
  the typeclass assumption `CompactSpace G.carrier`, which is needed to state the Haar measure;
  a compact subgroup of `U(N)` is closed, hence a Lie subgroup.  Connectedness is the hypothesis
  `IsConnected (G.carrier : Set GL(N, ℂ))`, in the form in which `CoreLean` uses it.  Simplicity
  is `GaugeGroup.IsSimple`.
* `Lie G = i 𝔤` consists of anti-Hermitian matrices, and `X = iA ∈ Lie G` has the same operator
  norm as `A ∈ 𝔤`.  The constant `c_π` is therefore the supremum of `‖dπ(iA)‖` over `A ∈ 𝔤` with
  `‖A‖ ≤ 1`.
* The differential is characterised without derivatives: `dπ(iA)` is the matrix `D` with
  `π(e^{itA}) = e^{tD}` for all real `t`.  For `A ∈ 𝔤` there is exactly one such `D`, the
  generator of the one-parameter group `t ↦ π(e^{itA})`.
* The norms are the operator norms of matrices acting on the Hermitian spaces `ℂ^N` and
  `ℂ^{dim π}` ([WL] l.149).
-/

noncomputable section

namespace CoreLean

open Complex

open scoped Matrix.Norms.L2Operator

variable {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ

/-! ### Simplicity ([WL] l.83) -/

/-- The Lie algebra of the group is simple: it is not abelian, and a real subspace of `𝔤` which
is an ideal is `0` or the whole of `𝔤`.  The bracket of `𝔤` is `(A, B) ↦ i[A, B]`, as in
`CoreLean.GaugeGroup.LieInput`. -/
def GaugeGroup.IsSimple (G : GaugeGroup N) : Prop :=
  (∃ A ∈ G.lie, ∃ B ∈ G.lie, A * B - B * A ≠ 0) ∧
  ∀ J : Submodule ℝ Mat, (J : Set Mat) ⊆ G.lie →
    (∀ A ∈ G.lie, ∀ B ∈ J, I • (A * B - B * A) ∈ J) → J = ⊥ ∨ (J : Set Mat) = G.lie

namespace WilsonLoop

variable {G : GaugeGroup N}

/-! ### The representation constant ([WL] `eq:representation-constant`, l.146-149) -/

/-- `D` is the differential `dπ(iA)` of the representation `π` at `iA ∈ Lie G`, for `A ∈ 𝔤`:
`π(e^{itA}) = e^{tD}` for all real `t`. -/
def Irrep.IsDifferential (π : Irrep G) (A : Mat)
    (D : Matrix (Fin π.dim) (Fin π.dim) ℂ) : Prop :=
  ∀ (t : ℝ) (h : expU ((I * t) • A) ∈ G.carrier),
    (π.toHom ⟨expU ((I * t) • A), h⟩ : Matrix (Fin π.dim) (Fin π.dim) ℂ) =
      NormedSpace.exp (t • D)

/-- The constant `c_π = sup { ‖dπ(X)‖ : X ∈ Lie G, ‖X‖ ≤ 1 }` of a representation, with the
operator norms ([WL] `eq:representation-constant`); here `X = iA` with `A ∈ 𝔤`. -/
def Irrep.repConst (π : Irrep G) : ℝ :=
  sSup {c | ∃ A ∈ G.lie, ‖A‖ ≤ 1 ∧ ∃ D, π.IsDifferential A D ∧ c = ‖D‖}

/-- The constant `c_𝒞 = maxᵢ c_{πᵢ}` of an ensemble ([WL] l.149). -/
def Ensemble.repConst {n : ℕ} (E : Ensemble n G) : ℝ :=
  (E.loops.map fun p ↦ p.2.repConst).foldr max 0

end WilsonLoop

end CoreLean
