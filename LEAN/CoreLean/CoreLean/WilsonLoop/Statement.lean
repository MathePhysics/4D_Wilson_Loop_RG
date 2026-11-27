import CoreLean.WilsonLoop.RGConstruction

/-!
# The statement of Theorem 1.5 of [WL] ("Uniform Bound and Limit")

The lattice expectation is evaluated with the bare coupling of the RG run. The loop
normalisation is the product of its step factors up to the stopping index. `BoundAndLimit`
states the uniform bound and summable cutoff differences for this expectation.
`Nonvanishing` states the separate lower bound for the same RG construction.

`ExistentialBoundAndLimit` records the original statement in terms of a coupling window
and perimeter and corner coefficients.
-/

noncomputable section

namespace CoreLean

namespace WilsonLoop

variable {N : ℕ} {G : GaugeGroup N}

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

/-- Theorem 1.5 of [WL] for the specified RG construction. -/
def BoundAndLimit {L : ℕ} [NeZero L] [CompactSpace G.carrier]
    (rg : RGConstruction G L) (Λstar : ℝ) : Prop :=
  ∀ (mT : ℕ) (gbar : ℝ), 0 < gbar → gbar ≤ rg.constants.γ₀ →
    (∀ K : ℕ, 0 < K → rg.runningCoupling mT K gbar K = gbar) ∧
    rg.constants.InWindow gbar (rg.bareCoupling mT gbar) ∧
    ∀ q : ℕ, 1 ≤ mT + q →
      ∃ (K₀ : EnsembleData G → ℕ) (B : EnsembleData G → ℝ),
        ∀ E : Ensemble (2 * L ^ (mT + q)) G, E.Admissible Λstar →
          rg.constants.qsharp E.repConst gbar ≤ q →
          rg.stoppingIndex gbar q < K₀ E.data ∧
            MainBound (rg.renormExpect mT q gbar E) (K₀ E.data) (B E.data)

/-- The separate nonvanishing result of [WL] for the same RG construction. -/
def Nonvanishing {L : ℕ} [NeZero L] [CompactSpace G.carrier]
    (rg : RGConstruction G L) (Λstar : ℝ) : Prop :=
  ∀ mT : ℕ, ∃ nv : ℕ → NonvanishingData rg.constants.γ₀,
    ∀ (gbar : ℝ), 0 < gbar → gbar ≤ rg.constants.γ₀ →
      ∀ q : ℕ, 1 ≤ mT + q → gbar ≤ (nv q).gbar₁ →
        ∃ K₀ : EnsembleData G → ℕ,
          ∀ E : Ensemble (2 * L ^ (mT + q)) G, E.Admissible Λstar → E.SmallDiameter →
            E.lengthSum ≤ (nv q).ℓ E.repConst gbar →
            rg.constants.qsharp E.repConst gbar ≤ q ∧ rg.stoppingIndex gbar q < K₀ E.data ∧
              ∀ K, K₀ E.data ≤ K → 1 / 2 ≤ ‖rg.renormExpect mT q gbar E K‖

/-- The conclusions of [WL] Theorem 1.5 (`thm:main`, l.160-176) and of [WL] `prop:nonvanishing`
(l.5309-5319) for the lattice theory of the gauge group `G`, in construction-free form. -/
def ExistentialBoundAndLimit (G : GaugeGroup N) [CompactSpace G.carrier] : Prop :=
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
