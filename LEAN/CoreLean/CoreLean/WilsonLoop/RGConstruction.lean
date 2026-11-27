import CoreLean.WilsonLoop.Geometry
import CoreLean.WilsonLoop.GaugeGroup

/-!
# RG construction data and Wilson loop normalisation

The bare coupling and the step factors of a single construction determine the
renormalised lattice expectation. The product of step factors satisfies the
perimeter-and-corner formula of [WL].
-/

noncomputable section

open scoped BigOperators

namespace CoreLean

namespace WilsonLoop

variable {N : ℕ} {G : GaugeGroup N}

/-! ### The normalisation ([WL] `prop:normalisation-structure`, l.3960-3970) -/

/-- Perimeter coefficients `m_{v,K}` and corner coefficients `z_{v,w,K}`.  They depend on the
cutoff `K`, the level `q`, the representation, and the orientations, and not on the loop
([WL] `eq:mass-and-corner`).  They also depend on `ḡ`, `L`, and the constants of the
construction. -/
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

private abbrev renormExpectWith (L mT q : ℕ) [NeZero L] (g₀ : ℕ → ℝ)
    (E : Ensemble (2 * L ^ (mT + q)) G) (K : ℕ)
    (κ : Loop (2 * L ^ (mT + q)) → Irrep G → ℂ) : ℂ :=
  expect G (L ^ (K - q) * (2 * L ^ (mT + q))) ((g₀ K) ^ (-2 : ℤ))
      (E.observable (L ^ (K - q))) /
    (E.loops.map fun p ↦ κ p.1 p.2).prod

/-- The renormalised expectation `W_K(𝒞) = 𝔼_K[W_𝒞] / ∏ᵢ κ_K^{(q)}(Cᵢ, χᵢ)` of an ensemble at
level `q`, for `K ≥ q`.  The lattice `𝕋_q` has `2 * L ^ (m_T + q)` sites per side, the lattice
`𝕋_K` has `L ^ (K - q)` times as many, and `𝔼_K` is the expectation of the lattice theory on
`𝕋_K` at the bare coupling `g₀ K` ([WL] l.97). -/
def renormExpect (L mT q : ℕ) [NeZero L] (g₀ : ℕ → ℝ) (κ : Coefficients G)
    (E : Ensemble (2 * L ^ (mT + q)) G) (K : ℕ) : ℂ :=
  renormExpectWith L mT q g₀ E K (κ.kappa L K q)

end RenormExpect

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

/-! ### The RG construction -/

/-- The data of the RG construction used by the Wilson loop results in [WL].
The step coefficients are the combined perimeter and corner coefficients of
`eq:step-factor`, including the contribution from the large-field operation at its steps. -/
structure RGConstruction (G : GaugeGroup N) (L : ℕ) where
  constants : Constants
  /-- `runningCoupling mT K gbar k` is the coupling at step `k` of the run at cutoff `K`. -/
  runningCoupling : ℕ → ℕ → ℝ → ℕ → ℝ
  /-- The stopping index `j_q` for the given reference coupling and level. -/
  stoppingIndex : ℝ → ℕ → ℕ
  level_le_stoppingIndex : ∀ gbar q, 0 < gbar → gbar ≤ constants.γ₀ → q ≤ stoppingIndex gbar q
  /-- The coefficient per traversal of the preceding lattice, indexed by cutoff,
  reference coupling, step, normalised character, and orientation. -/
  stepMass : ℕ → ℝ → ℕ → (G.carrier → ℂ) → Fin 4 × Bool → ℂ
  /-- The coefficient per corner, with the incoming and outgoing orientations. -/
  stepCorner : ℕ → ℝ → ℕ → (G.carrier → ℂ) → Fin 4 × Bool → Fin 4 × Bool → ℂ

namespace RGConstruction

variable {L : ℕ} (rg : RGConstruction G L)

/-- The initial coupling of the run at cutoff `K`. -/
def bareCoupling (mT : ℕ) (gbar : ℝ) (K : ℕ) : ℝ :=
  rg.runningCoupling mT K gbar 0

/-- The mass coefficient for step `j + 1` in units of one bond of the fine lattice. -/
def fineStepMass (K : ℕ) (gbar : ℝ) (j : ℕ) (χ : G.carrier → ℂ) (v : Fin 4 × Bool) : ℂ :=
  ((L : ℂ) ^ j)⁻¹ * rg.stepMass K gbar (j + 1) χ v

/-- The step factor for step `j + 1` of a loop read at level `q`. -/
def stepFactor (K q : ℕ) (gbar : ℝ) (j : ℕ) {n : ℕ} (C : Loop n) (π : Irrep G) : ℂ :=
  Complex.exp
    ((C.orients.map fun v ↦ (L ^ (K - q) : ℂ) * rg.fineStepMass K gbar j π.character v).sum +
      (C.corners.map fun c ↦ rg.stepCorner K gbar (j + 1) π.character c.1 c.2).sum)

/-- The product of step factors through step `K - j_q` ([WL] `def:normalisation`). -/
def normalisation (K q : ℕ) (gbar : ℝ) {n : ℕ} (C : Loop n) (π : Irrep G) : ℂ :=
  ∏ j ∈ Finset.range (K - rg.stoppingIndex gbar q), rg.stepFactor K q gbar j C π

/-- The sums of the step coefficients through step `K - j_q` in
[WL] `eq:mass-and-corner`. -/
def coefficients (gbar : ℝ) : Coefficients G where
  m K q π v := ∑ j ∈ Finset.range (K - rg.stoppingIndex gbar q),
    rg.fineStepMass K gbar j π.character v
  z K q π v w := ∑ j ∈ Finset.range (K - rg.stoppingIndex gbar q),
    rg.stepCorner K gbar (j + 1) π.character v w

private theorem sum_list_map_sum {α : Type*} (s : Finset ℕ) (xs : List α) (f : α → ℕ → ℂ) :
    (∑ j ∈ s, (xs.map (fun x ↦ f x j)).sum) =
      (xs.map (fun x ↦ ∑ j ∈ s, f x j)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [Finset.sum_add_distrib, ih]

/-- The perimeter-and-corner formula for the product of step factors. -/
theorem normalisation_eq_kappa (K q : ℕ) (gbar : ℝ) {n : ℕ} (C : Loop n) (π : Irrep G) :
    rg.normalisation K q gbar C π = (rg.coefficients gbar).kappa L K q C π := by
  unfold normalisation stepFactor Coefficients.kappa Coefficients.logKappa coefficients
  rw [← Complex.exp_sum]
  simp only [Finset.sum_add_distrib, sum_list_map_sum, Finset.mul_sum]

variable [NeZero L] [CompactSpace G.carrier]

/-- The renormalised expectation for the coupling and step factors of the same construction. -/
def renormExpect (mT q : ℕ) (gbar : ℝ) (E : Ensemble (2 * L ^ (mT + q)) G) (K : ℕ) : ℂ :=
  renormExpectWith L mT q (rg.bareCoupling mT gbar) E K (rg.normalisation K q gbar)

theorem renormExpect_eq (mT q : ℕ) (gbar : ℝ) (E : Ensemble (2 * L ^ (mT + q)) G) (K : ℕ) :
    rg.renormExpect mT q gbar E K =
      WilsonLoop.renormExpect L mT q (rg.bareCoupling mT gbar) (rg.coefficients gbar) E K := by
  simp only [renormExpect, WilsonLoop.renormExpect, renormExpectWith, normalisation_eq_kappa]

end RGConstruction

end WilsonLoop

end CoreLean
