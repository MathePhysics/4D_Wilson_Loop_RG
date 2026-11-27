import CoreLean.WilsonLoop.Geometry
import CoreLean.WilsonLoop.GaugeGroup

/-!
# The statement of Theorem 1.5 of [WL] ("Uniform Bound and Limit")

This file defines the proposition `CoreLean.WilsonLoop.BoundAndLimit G`: the conclusion of [WL]
Theorem 1.5 (`thm:main`, l.160-176) together with that of [WL] Proposition `prop:nonvanishing`
(l.5309-5319), for the lattice theory of a gauge group `G`.  The theorem itself,
`CoreLean.WilsonLoop.boundAndLimit`, is stated in `CoreLean.WilsonLoop.MainTheorem`.

## Main definitions

* `CoreLean.WilsonLoop.Coefficients`, `CoreLean.WilsonLoop.Coefficients.kappa`: perimeter and
  corner coefficients and the normalisation `κ_K^{(q)}(C, χ)` built from them
  ([WL] `prop:normalisation-structure`).
* `CoreLean.WilsonLoop.renormExpect`: the renormalised expectation `W_K(𝒞)`
  ([WL] `def:renormalised-expectation`).
* `CoreLean.WilsonLoop.Constants`: the constants `γ₀`, `b`, `b'`, `C_W` and the level threshold
  `q_♯`.
* `CoreLean.WilsonLoop.NonvanishingData`: the data `ḡ₁`, `ℓ` of the Nonvanishing proposition.
* `CoreLean.WilsonLoop.MainBound`: the bound and the summability [WL] `eq:main-bound`.
* `CoreLean.WilsonLoop.BoundAndLimit`: the statement.

## The form of the statement

In [WL] the renormalised expectation is defined through two objects which come out of Bałaban's
renormalisation group construction: the bare coupling `g₀(K, ḡ)` (`thm:coupling-flow`, l.967)
and the normalisation `κ_K^{(q)}(C, χ)` (`def:normalisation`, l.3954).  Stating Theorem 1.5
literally would require that construction.  `BoundAndLimit` is *construction-free*: it asserts
that a coupling and a normalisation exist with the properties which [WL] proves of them,

* the coupling lies in the window `eq:bare-coupling-window` (l.94-96), and
* `log κ_K^{(q)}(C, χ)` is the sum of a term for each bond of `C` in the lattice `𝕋_K` and of a
  term for each corner of `C`, with coefficients which do not depend on the loop
  (`prop:normalisation-structure`, l.3960-3970),

and that the conclusions of Theorem 1.5 hold for them.  With these two properties alone the
conclusions of Theorem 1.5 would hold trivially: a normalisation which grows fast makes
`W_K(𝒞) → 0`, since `|𝔼_K[W_𝒞]| ≤ 1` (`CoreLean.WilsonLoop.boundOnly_trivial`).  The lower
bound `|W_K(𝒞)| ≥ 1/2` of the Nonvanishing proposition excludes this, and it is therefore part
of the statement, for the same coupling and the same coefficients.

## The order of the quantifiers

1. The function `L₀`; then `Λ_*` and the blocking factor `L`, odd with `L ≥ L₀(Λ_*)`
   ([WL] l.83, l.143).
2. The `Constants`.  In [WL] they depend only on the constants of the construction and on `Λ_*`
   (l.161 and Appendix `app:constants`), hence not on the torus.
3. The size `m_T` of the torus, whose period is `T = 2 L^{m_T} u` ([WL] l.83).
4. The `NonvanishingData` of each level `q`, which in [WL] depend on the constants of the
   construction, `Λ_*`, `q`, and `T/u` (l.5310).
5. The coupling `ḡ ∈ (0, γ₀]`.
6. The bare couplings `g₀(K)` and the coefficients of the normalisation.
7. The level `q` ([WL] l.104).
8. `K₀` and `B`, as functions of the data of an ensemble named in the last sentence of the
   theorem (l.175).
9. The ensemble.

## Differences from [WL]

* The coupling and the normalisation are existentially quantified, as explained above.  The
  coefficients are complex numbers and may depend on the representation, not only on its
  character.  [WL] states that they do not depend on the torus (l.3970); here they are chosen
  after `m_T`, so this is not asserted.
* Only `0 < b ≤ b'` and `C_W ≥ 0` are required of the constants of the window, as in [WL] l.93.
  The more precise `b, b' = 2 c ln L ∓ δ'` of `thm:coupling-flow` is not asserted.
* `L₀` is not required to be increasing.
* `q ≤ K₀` is required, so that only cutoffs `K ≥ q` occur, at which the loops are paths of
  `𝕋_K`.  In [WL], `K > j_q ≥ q` (l.128, l.135).
* The function `ℓ` is real valued, where [WL] allows the value `∞`.  This is no restriction:
  `ℓ` may be replaced by `min(ℓ, 1/ḡ)`.
-/

noncomputable section

namespace CoreLean

namespace WilsonLoop

variable {N : ℕ} {G : GaugeGroup N}

/-! ### The normalisation ([WL] `prop:normalisation-structure`, l.3960-3970) -/

/-- Perimeter coefficients `m_{v,K}` and corner coefficients `z_{v,w,K}`.  They depend on the
cutoff `K`, the level `q`, the representation, and the orientations, and not on the loop
([WL] `eq:mass-and-corner`).  They also depend on `ḡ`, `L`, and the constants of the
construction: in `BoundAndLimit` they are chosen after these. -/
structure Coefficients (G : GaugeGroup N) where
  /-- `m K q π v`: the coefficient of a bond of the lattice `𝕋_K` of orientation `v`. -/
  m : ℕ → ℕ → Irrep G → Fin 4 × Bool → ℂ
  /-- `z K q π v w`: the coefficient of a corner with the incoming orientation `v` and the
  outgoing orientation `w`. -/
  z : ℕ → ℕ → Irrep G → Fin 4 × Bool → Fin 4 × Bool → ℂ

/-- `log κ_K^{(q)}(C, χ) = ∑_v N_v^{(0)}(C) m_{v,K} + ∑_{c ∈ 𝒦(C)} z_{v_c,w_c,K}`
([WL] `eq:normalisation-structure`).  Here `N_v^{(0)}(C)` is the number of the bonds of
orientation `v` of `C` as a path of `𝕋_K`: each bond of `𝕋_q` consists of `L ^ (K - q)` bonds
of `𝕋_K`. -/
def Coefficients.logKappa (κ : Coefficients G) (L K q : ℕ) {n : ℕ} (C : Loop n)
    (π : Irrep G) : ℂ :=
  (C.orients.map fun v ↦ (L ^ (K - q) : ℂ) * κ.m K q π v).sum +
    (C.corners.map fun c ↦ κ.z K q π c.1 c.2).sum

/-- The normalisation `κ_K^{(q)}(C, χ)` of a loop at level `q` at the cutoff `K`
([WL] `eq:normalisation-product`, `def:normalisation`). -/
def Coefficients.kappa (κ : Coefficients G) (L K q : ℕ) {n : ℕ} (C : Loop n) (π : Irrep G) :
    ℂ :=
  Complex.exp (κ.logKappa L K q C π)

/-! ### The renormalised expectation ([WL] `def:renormalised-expectation`, l.134-139) -/

section RenormExpect

variable [CompactSpace G.carrier]

/-- The renormalised expectation `W_K(𝒞) = 𝔼_K[W_𝒞] / ∏ᵢ κ_K^{(q)}(Cᵢ, χᵢ)` of an ensemble at
level `q`, for `K ≥ q`.  The lattice `𝕋_q` has `2 * L ^ (m_T + q)` sites per side, the lattice
`𝕋_K` has `L ^ (K - q)` times as many, and `𝔼_K` is the expectation of the lattice theory on
`𝕋_K` at the bare coupling `g₀ K` ([WL] l.97). -/
def renormExpect (L mT q : ℕ) [NeZero L] (g₀ : ℕ → ℝ) (κ : Coefficients G)
    (E : Ensemble (2 * L ^ (mT + q)) G) (K : ℕ) : ℂ :=
  expect G (L ^ (K - q) * (2 * L ^ (mT + q))) ((g₀ K) ^ (-2 : ℤ))
      (E.observable (L ^ (K - q))) /
    (E.loops.map fun p ↦ κ.kappa L K q p.1 p.2).prod

end RenormExpect

/-! ### The data of an ensemble -/

/-- The type of the data of an ensemble on which the numbers `K₀` and `B` of Theorem 1.5 may
depend ([WL] l.175): for each loop its character, the ratio `P(Cᵢ)/r(Cᵢ)`, and the number
`P_q(Cᵢ)` of its bonds.  The length of the list is the number of the loops. -/
abbrev EnsembleData (G : GaugeGroup N) := List ((G.carrier → ℂ) × ℝ × ℕ)

/-- The data of an ensemble on which `K₀` and `B` may depend. -/
def Ensemble.data {n : ℕ} (E : Ensemble n G) : EnsembleData G :=
  E.loops.map fun p ↦ (p.2.character, p.1.isolationRatio, p.1.perimeter)

/-- The left side `∑ᵢ (P_q(Cᵢ)² + P(Cᵢ)/r(Cᵢ))` of [WL] `eq:nonvanishing-length` (l.5311). -/
def Ensemble.lengthSum {n : ℕ} (E : Ensemble n G) : ℝ :=
  (E.loops.map fun p ↦ (p.1.perimeter : ℝ) ^ 2 + p.1.isolationRatio).sum

/-! ### The constants -/

/-- The constants of [WL] Theorem 1.5 and of the window of the bare coupling: `γ₀`, the
constants `b ≤ b'` and `C_W` of `eq:bare-coupling-window` (l.93-96), and the level threshold
`q_♯ : [0, ∞) × (0, γ₀] → ℕ`, which is "nondecreasing in each argument and, for every `c`, equal
to `0` for all sufficiently small `ḡ`" (l.161). -/
structure Constants where
  /-- The bound `γ₀` on the coupling `ḡ`. -/
  γ₀ : ℝ
  /-- The constant `b` of the lower bound of the window. -/
  b : ℝ
  /-- The constant `b'` of the upper bound of the window. -/
  b' : ℝ
  /-- The constant `C_W` of the window. -/
  CW : ℝ
  /-- The level threshold `q_♯(c, ḡ)`. -/
  qsharp : ℝ → ℝ → ℕ
  /-- `γ₀ > 0`. -/
  γ₀_pos : 0 < γ₀
  /-- `b > 0`. -/
  b_pos : 0 < b
  /-- `b ≤ b'`. -/
  b_le : b ≤ b'
  /-- `C_W ≥ 0`. -/
  CW_nonneg : 0 ≤ CW
  /-- `q_♯` is nondecreasing in its first argument. -/
  qsharp_mono_left : ∀ c c' g, 0 ≤ c → c ≤ c' → 0 < g → g ≤ γ₀ → qsharp c g ≤ qsharp c' g
  /-- `q_♯` is nondecreasing in its second argument. -/
  qsharp_mono_right : ∀ c g g', 0 ≤ c → 0 < g → g ≤ g' → g' ≤ γ₀ → qsharp c g ≤ qsharp c g'
  /-- For every `c`, `q_♯(c, ḡ) = 0` for all sufficiently small `ḡ`. -/
  qsharp_eq_zero : ∀ c, 0 ≤ c → ∃ g₁, 0 < g₁ ∧ ∀ g, 0 < g → g ≤ g₁ → qsharp c g = 0

/-- The bare couplings `g₀ K = g₀(K, ḡ)` are positive and lie in the window
`ḡ⁻² + b K - C_W ≤ g₀(K, ḡ)⁻² ≤ ḡ⁻² + b' K + C_W` ([WL] `eq:bare-coupling-window`, l.94-96). -/
def Constants.InWindow (c : Constants) (gbar : ℝ) (g₀ : ℕ → ℝ) : Prop :=
  ∀ K : ℕ, 0 < g₀ K ∧ gbar ^ (-2 : ℤ) + c.b * K - c.CW ≤ (g₀ K) ^ (-2 : ℤ) ∧
    (g₀ K) ^ (-2 : ℤ) ≤ gbar ^ (-2 : ℤ) + c.b' * K + c.CW

/-- The data of [WL] `prop:nonvanishing` at one level: "`ḡ₁ ∈ (0, γ₀]` and a function
`ℓ : [0, ∞) × (0, ḡ₁] → [0, ∞]`, nonincreasing in its first argument and with `ℓ(c, ḡ) → ∞` as
`ḡ → 0` for every `c`" (l.5310). -/
structure NonvanishingData (γ₀ : ℝ) where
  /-- The bound `ḡ₁` on the coupling. -/
  gbar₁ : ℝ
  /-- The bound `ℓ(c, ḡ)` on the lengths of the loops. -/
  ℓ : ℝ → ℝ → ℝ
  /-- `ḡ₁ > 0`. -/
  gbar₁_pos : 0 < gbar₁
  /-- `ḡ₁ ≤ γ₀`. -/
  gbar₁_le : gbar₁ ≤ γ₀
  /-- `ℓ` is nonincreasing in its first argument. -/
  ℓ_anti_left : ∀ c c' g, 0 ≤ c → c ≤ c' → 0 < g → g ≤ gbar₁ → ℓ c' g ≤ ℓ c g
  /-- `ℓ(c, ḡ) → ∞` as `ḡ → 0`, for every `c`. -/
  ℓ_tendsto : ∀ c M, 0 ≤ c → ∃ g₂, 0 < g₂ ∧ ∀ g, 0 < g → g ≤ g₂ → M ≤ ℓ c g

/-! ### The statement -/

/-- The conclusion [WL] `eq:main-bound` of Theorem 1.5 for the sequence `W = (W_K(𝒞))_K`:
`sup_{K ≥ K₀} |W_K| ≤ B` and `∑_{K ≥ K₀} |W_{K+1} - W_K| < ∞`. -/
def MainBound (W : ℕ → ℂ) (K₀ : ℕ) (B : ℝ) : Prop :=
  (∀ K, K₀ ≤ K → ‖W K‖ ≤ B) ∧ Summable fun K ↦ ‖W (K₀ + K + 1) - W (K₀ + K)‖

/-- The conclusions of [WL] Theorem 1.5 (`thm:main`, l.160-176) and of [WL] `prop:nonvanishing`
(l.5309-5319) for the lattice theory of the gauge group `G`, in construction-free form.  See the
header of this file for the form of the statement and the order of the quantifiers. -/
def BoundAndLimit (G : GaugeGroup N) [CompactSpace G.carrier] : Prop :=
  -- "there is an increasing function `L₀` on `[2, ∞)` … we fix `Λ_* ≥ 2` with `L ≥ L₀(Λ_*)`"
  -- (l.143); `L` is odd (l.83)
  ∃ L₀ : ℝ → ℕ, ∀ (Λstar : ℝ) (L : ℕ) [NeZero L], 2 ≤ Λstar → Odd L → L₀ Λstar ≤ L →
  -- "There are `γ₀ > 0` and a function `q_♯` …" (l.161); the constants of the window (l.93)
  ∃ c : Constants,
  -- the torus `T = 2 L^{m_T} u` (l.83)
  ∀ mT : ℕ,
  -- "There are `ḡ₁ ∈ (0, γ₀]` and a function `ℓ` …, which depend only on the constants of the
  -- construction, `Λ_*`, `q`, and `T/u`" (l.5310)
  ∃ nv : ℕ → NonvanishingData c.γ₀,
  -- "such that the following holds for every `ḡ ∈ (0, γ₀]`" (l.161)
  ∀ gbar : ℝ, 0 < gbar → gbar ≤ c.γ₀ →
  -- the bare couplings `g₀(K, ḡ)` (l.93-97) and the coefficients of the normalisation (l.3960)
  ∃ (g₀ : ℕ → ℝ) (κ : Coefficients G), c.InWindow gbar g₀ ∧
  -- a level: "an integer `q ≥ 0` with `m_T + q ≥ 1`" (l.104)
  ∀ q : ℕ, 1 ≤ mT + q →
  -- "`K₀` and `B` depend on …, on `ḡ`, `q`, and `T/u`, and on `𝒞` through `n`, the characters,
  -- the ratios `P(Cᵢ)/r(Cᵢ)`, and the numbers `P_q(Cᵢ)`" (l.175)
  ∃ (K₀ : EnsembleData G → ℕ) (B : EnsembleData G → ℝ),
  -- "every loop ensemble `𝒞` at a level `q` … whose loops are admissible" (l.161-165)
  ∀ E : Ensemble (2 * L ^ (mT + q)) G, E.Admissible Λstar →
    -- Theorem 1.5: if `q ≥ q_♯(c_𝒞, ḡ)` (`eq:level-condition`), then `eq:main-bound` holds
    (c.qsharp E.repConst gbar ≤ q →
      q ≤ K₀ E.data ∧ MainBound (renormExpect L mT q g₀ κ E) (K₀ E.data) (B E.data)) ∧
    -- Nonvanishing (l.5310-5318): if `ḡ ≤ ḡ₁`, the loops have small diameter, and
    -- `eq:nonvanishing-length` holds, then `q ≥ q_♯(c_𝒞, ḡ)` and `|W_K(𝒞)| ≥ 1/2` for
    -- `K ≥ K₀(𝒞)`
    (gbar ≤ (nv q).gbar₁ → E.SmallDiameter →
      E.lengthSum ≤ (nv q).ℓ E.repConst gbar →
      c.qsharp E.repConst gbar ≤ q ∧
      ∀ K, K₀ E.data ≤ K → 1 / 2 ≤ ‖renormExpect L mT q g₀ κ E K‖)

end WilsonLoop

end CoreLean
