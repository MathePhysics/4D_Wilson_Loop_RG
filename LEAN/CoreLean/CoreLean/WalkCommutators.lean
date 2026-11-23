/-
The commutators with the functions of the partition of unity in BALABAN_CORE.tex (`bf6b2bc552ba`).

* `lem:walk-factor`(i): the part of `eq:commutator-scalar` which comes from `Δ_U`
  (`comm_lap_scalar`), and the commutator with an operator given by a kernel, of which
  `[h, Q'^* 𝖺 Q']` is one (`comm_kernel`).
* `lem:walk-factor`(iv): the rule of Leibniz, `T^-_μ D_{U,μ} = -D^*_{U,μ}`, `D^*_{U,μ} T_μ = -D_{U,μ}`,
  and the part of `eq:commutator-divergence` which comes from `Δ_U` (`comm_lap_divergence`).
* `lem:walk-factor`(v): `Δ_U` is symmetric for the pairing, the commutator of a symmetric operator
  with a multiplication is antisymmetric, the inverse of a symmetric operator is symmetric, and
  `h G K'(h) = -(K'(h) G h)^T` (`transposed_factor`).
* `lem:walk-units`: `eq:unit-leibniz` (`leibniz_first`, `leibniz_second`).
* `lem:vector-commutator`: the first form of the commutator `[h, 𝒟₁𝒟₂]` and
  `eq:second-order-commutator` (`comm_DD_first`, `comm_DD_second`).

The identities of the products of differences hold for any shift with transports
`(T w)(z) = Ad_{W(z)} w(σ z)` on any set of sites; the differences of the core are the shifts
`σ z = z ± e_μ` with the transports `U(z, z ± e_μ)`. The functions are complex valued; the core's are
real, which is used only for the bounds. Not formalised here: the bounds of (ii)–(v), which rest on
`lem:partition-of-unity`(ii), `lem:transports`, `lem:block-average-transports`, and the local bounds
of `thm:small-field`; and the compression to a Dirichlet domain, which commutes with the
multiplications and enters only through the symmetry of the operator, a hypothesis of the abstract
statements.
-/
import CoreLean.Differences

open Matrix Complex

noncomputable section

set_option linter.unusedSectionVars false

namespace CoreLean
namespace WalkCommutators

variable {N : ℕ} {X : Type*} (a : ℂ)

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "GLN" => (Matrix (Fin N) (Fin N) ℂ)ˣ

/-! ### Shifts with transports -/

/-- A shift with transports: `(T w)(z) = Ad_{W(z)} w(σ z)`. -/
structure Shift (N : ℕ) (X : Type*) where
  σ : X → X
  W : X → (Matrix (Fin N) (Fin N) ℂ)ˣ

/-- The multiplication of a form by a function. -/
def mulF (φ : X → ℂ) (w : X → Mat) : X → Mat := fun z => φ z • w z

/-- The translate `φ^𝒟 = φ ∘ σ` of a function. -/
def shF (σ : X → X) (φ : X → ℂ) : X → ℂ := fun z => φ (σ z)

/-- The difference `∂_𝒟 φ = a⁻¹ (φ^𝒟 - φ)` of a function. -/
def dF (σ : X → X) (φ : X → ℂ) : X → ℂ := fun z => a⁻¹ * (φ (σ z) - φ z)

namespace Shift

/-- `(T w)(z) = Ad_{W(z)} w(σ z)`. -/
def T (S : Shift N X) (w : X → Mat) : X → Mat := fun z => Ad (S.W z) (w (S.σ z))

/-- The difference `𝒟 = a⁻¹ (T - 1)`. -/
def D (S : Shift N X) (w : X → Mat) : X → Mat := fun z => a⁻¹ • (S.T w z - w z)

variable (S : Shift N X)

lemma T_add (w w' : X → Mat) : S.T (w + w') = S.T w + S.T w' := by
  funext z; simp [T, Ad_add]

lemma T_sub (w w' : X → Mat) : S.T (w - w') = S.T w - S.T w' := by
  funext z; simp [T, Ad_sub]

lemma T_neg (w : X → Mat) : S.T (-w) = -S.T w := by
  funext z; simp [T, Ad_neg]

lemma T_smul (c : ℂ) (w : X → Mat) : S.T (c • w) = c • S.T w := by
  funext z; simp [T, Ad_smul]

lemma T_mulF (φ : X → ℂ) (w : X → Mat) : S.T (mulF φ w) = mulF (shF S.σ φ) (S.T w) := by
  funext z; simp [T, mulF, shF, Ad_smul]

lemma D_eq (w : X → Mat) : S.D a w = a⁻¹ • (S.T w - w) := rfl

lemma D_add (w w' : X → Mat) : S.D a (w + w') = S.D a w + S.D a w' := by
  simp only [D_eq, T_add]; module

lemma D_sub (w w' : X → Mat) : S.D a (w - w') = S.D a w - S.D a w' := by
  simp only [D_eq, T_sub]; module

lemma D_neg (w : X → Mat) : S.D a (-w) = -S.D a w := by
  simp only [D_eq, T_neg]; module

end Shift

lemma mulF_add (φ : X → ℂ) (w w' : X → Mat) : mulF φ (w + w') = mulF φ w + mulF φ w' := by
  funext z; simp [mulF, smul_add]

lemma mulF_sub (φ : X → ℂ) (w w' : X → Mat) : mulF φ (w - w') = mulF φ w - mulF φ w' := by
  funext z; simp [mulF, smul_sub]

lemma mulF_neg (φ : X → ℂ) (w : X → Mat) : mulF φ (-w) = -mulF φ w := by
  funext z; simp [mulF]

lemma mulF_smul (φ : X → ℂ) (c : ℂ) (w : X → Mat) : mulF φ (c • w) = c • mulF φ w := by
  funext z; simp [mulF, smul_smul, mul_comm]

lemma sub_mulF (φ ψ : X → ℂ) (w : X → Mat) : mulF (φ - ψ) w = mulF φ w - mulF ψ w := by
  funext z; simp [mulF, sub_smul]

lemma neg_mulF (φ : X → ℂ) (w : X → Mat) : mulF (-φ) w = -mulF φ w := by
  funext z; simp [mulF]

lemma mulF_mulF (φ ψ : X → ℂ) (w : X → Mat) : mulF φ (mulF ψ w) = mulF (φ * ψ) w := by
  funext z; simp [mulF, smul_smul]

/-! ### `eq:unit-leibniz` and the rule of Leibniz of `lem:walk-factor`(iv) -/

/-- The first identity of `eq:unit-leibniz`: `𝒟(φ w) = φ^𝒟 𝒟w + (∂_𝒟 φ) w`. -/
theorem leibniz_first (S : Shift N X) (φ : X → ℂ) (w : X → Mat) :
    S.D a (mulF φ w) = mulF (shF S.σ φ) (S.D a w) + mulF (dF a S.σ φ) w := by
  funext z
  simp only [Shift.D, Shift.T, mulF, shF, dF, Ad_smul, Pi.add_apply]
  module

/-- The rule of Leibniz of `lem:walk-factor`(iv), the second identity of `eq:unit-leibniz`:
`𝒟(φ w) = φ 𝒟w + (∂_𝒟 φ) T_𝒟 w`. -/
theorem leibniz_second (S : Shift N X) (φ : X → ℂ) (w : X → Mat) :
    S.D a (mulF φ w) = mulF φ (S.D a w) + mulF (dF a S.σ φ) (S.T w) := by
  funext z
  simp only [Shift.D, Shift.T, mulF, dF, Ad_smul, Pi.add_apply]
  module

/-! ### The commutator with a product of two differences (`lem:vector-commutator`) -/

/-- The first form of the commutator in the proof of `lem:vector-commutator`:
`[h, 𝒟₁𝒟₂]u = (h - (h^{𝒟₂})^{𝒟₁}) 𝒟₁𝒟₂u - (∂₁ h^{𝒟₂}) 𝒟₂u - (∂₂h)^{𝒟₁} 𝒟₁u - (∂₁∂₂h) u`. -/
theorem comm_DD_first (S₁ S₂ : Shift N X) (h : X → ℂ) (u : X → Mat) :
    mulF h (S₁.D a (S₂.D a u)) - S₁.D a (S₂.D a (mulF h u)) =
      mulF (h - shF S₁.σ (shF S₂.σ h)) (S₁.D a (S₂.D a u)) -
        mulF (dF a S₁.σ (shF S₂.σ h)) (S₂.D a u) -
        mulF (shF S₁.σ (dF a S₂.σ h)) (S₁.D a u) -
        mulF (dF a S₁.σ (dF a S₂.σ h)) u := by
  rw [leibniz_first, Shift.D_add, leibniz_first, leibniz_first, sub_mulF]
  abel

/-- The commutator with a product of two differences, before the shifts are moved:
`[h, 𝒟₁𝒟₂]u = -(∂₁h) T₁𝒟₂u - 𝒟₁((∂₂h) T₂u)`. -/
theorem comm_DD_mid (S₁ S₂ : Shift N X) (h : X → ℂ) (u : X → Mat) :
    mulF h (S₁.D a (S₂.D a u)) - S₁.D a (S₂.D a (mulF h u)) =
      -mulF (dF a S₁.σ h) (S₁.T (S₂.D a u)) - S₁.D a (mulF (dF a S₂.σ h) (S₂.T u)) := by
  rw [leibniz_second a S₂, Shift.D_add, leibniz_second a S₁]
  abel

/-- `κ₁₂ = a⁻¹ (T₁T₂ - T₂T₁)`. -/
def kappa (S₁ S₂ : Shift N X) (u : X → Mat) : X → Mat :=
  a⁻¹ • (S₁.T (S₂.T u) - S₂.T (S₁.T u))

/-- `T₁𝒟₂ = 𝒟₂T₁ + κ₁₂`. -/
lemma T_D_comm (S₁ S₂ : Shift N X) (u : X → Mat) :
    S₁.T (S₂.D a u) = S₂.D a (S₁.T u) + kappa a S₁ S₂ u := by
  simp only [Shift.D_eq, Shift.T_smul, Shift.T_sub, kappa]
  module

/-- `eq:second-order-commutator`:
`[h, 𝒟₁𝒟₂]u = -𝒟₂((∂₁h) T₁u) - 𝒟₁((∂₂h) T₂u) + (∂₂∂₁h) T₂T₁u - (∂₁h) κ₁₂u`. -/
theorem comm_DD_second (S₁ S₂ : Shift N X) (h : X → ℂ) (u : X → Mat) :
    mulF h (S₁.D a (S₂.D a u)) - S₁.D a (S₂.D a (mulF h u)) =
      -S₂.D a (mulF (dF a S₁.σ h) (S₁.T u)) - S₁.D a (mulF (dF a S₂.σ h) (S₂.T u)) +
        mulF (dF a S₂.σ (dF a S₁.σ h)) (S₂.T (S₁.T u)) -
        mulF (dF a S₁.σ h) (kappa a S₁ S₂ u) := by
  rw [comm_DD_mid, T_D_comm, mulF_add]
  have hl := leibniz_second a S₂ (dF a S₁.σ h) (S₁.T u)
  rw [hl]
  abel

/-! ### The commutator with an operator given by a kernel -/

/-- `([h, Q]u)(x) = Σ_{x'} q(x, x') (h(x) - h(x')) Ad_{V(x,x')} u(x')` for
`(Qu)(x) = Σ_{x'} q(x, x') Ad_{V(x,x')} u(x')`; for `Q'^* 𝖺 Q'` the kernel is
`𝖺_n a_n^{-2} (η/a_n)⁴` on the block of `x`, with the transports of `lem:block-average-transports`
(`lem:walk-factor`(i)). -/
theorem comm_kernel [Fintype X] (q : X → X → ℂ) (V : X → X → GLN) (h : X → ℂ) (u : X → Mat)
    (x : X) :
    h x • (∑ x', q x x' • Ad (V x x') (u x')) - ∑ x', q x x' • Ad (V x x') (h x' • u x') =
      ∑ x', (q x x' * (h x - h x')) • Ad (V x x') (u x') := by
  rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x' _ => ?_
  rw [Ad_smul, smul_smul, smul_smul, ← sub_smul]
  congr 1; ring

/-! ### The differences of the lattice -/

variable {n : ℕ} [NeZero n]

/-- The shift of `D_{U,μ}`: `(T_μ w)(z) = Ad_{U(z, z + e_μ)} w(z + e_μ)`. -/
def sFw (U : Config N n) (μ : Fin 4) : Shift N (Site n) :=
  ⟨fun z => z + unit n μ, U μ⟩

/-- The shift of `D^*_{U,μ}`: `(T^-_μ w)(z) = Ad_{U(z, z - e_μ)} w(z - e_μ)`. -/
def sBw (U : Config N n) (μ : Fin 4) : Shift N (Site n) :=
  ⟨fun z => z - unit n μ, fun z => U.val ⟨z, μ, false⟩⟩

lemma Dfw_eq (U : Config N n) (μ : Fin 4) (l : Form0 N n) :
    Dfw a U μ l = (sFw U μ).D a l := rfl

lemma Dbw_eq (U : Config N n) (μ : Fin 4) (l : Form0 N n) :
    Dbw a U μ l = (sBw U μ).D a l := rfl

/-- `T^-_μ T_μ = 1`. -/
lemma Tbw_Tfw (U : Config N n) (μ : Fin 4) (w : Form0 N n) :
    (sBw U μ).T ((sFw U μ).T w) = w := by
  funext z
  simp only [Shift.T, sBw, sFw, Config.val, Bool.false_eq_true, ite_false, sub_add_cancel]
  exact Ad_inv_Ad _ _

/-- `T_μ T^-_μ = 1`. -/
lemma Tfw_Tbw (U : Config N n) (μ : Fin 4) (w : Form0 N n) :
    (sFw U μ).T ((sBw U μ).T w) = w := by
  funext z
  simp only [Shift.T, sBw, sFw, Config.val, Bool.false_eq_true, ite_false, add_sub_cancel_right]
  rw [← Ad_mul, mul_inv_cancel]
  simp [Ad]

/-- `T^-_μ D_{U,μ} = -D^*_{U,μ}` (`lem:walk-factor`(iv)). -/
theorem Tbw_Dfw (U : Config N n) (μ : Fin 4) (w : Form0 N n) :
    (sBw U μ).T ((sFw U μ).D a w) = -(sBw U μ).D a w := by
  rw [Shift.D_eq, Shift.T_smul, Shift.T_sub, Tbw_Tfw, Shift.D_eq]
  module

/-- `D^*_{U,μ} T_μ = -D_{U,μ}` (`lem:walk-factor`(iv)). -/
theorem Dbw_Tfw (U : Config N n) (μ : Fin 4) (w : Form0 N n) :
    (sBw U μ).D a ((sFw U μ).T w) = -(sFw U μ).D a w := by
  rw [Shift.D_eq, Tbw_Tfw, Shift.D_eq]
  module

/-- `∂_μ` of a function on the sites. -/
abbrev dfw (μ : Fin 4) (h : Site n → ℂ) : Site n → ℂ := dF a (fun z => z + unit n μ) h
/-- `∂^*_μ` of a function on the sites. -/
abbrev dbw (μ : Fin 4) (h : Site n → ℂ) : Site n → ℂ := dF a (fun z => z - unit n μ) h

/-- `Δ_{id} h = Σ_μ ∂^*_μ ∂_μ h` for a function on the sites. -/
def lapF (h : Site n → ℂ) : Site n → ℂ := fun x => ∑ μ, dbw a μ (dfw a μ h) x

/-- `[h, D^*_{U,μ} D_{U,μ}]u = (∂_μh) D_{U,μ}u + (∂^*_μh) D^*_{U,μ}u - (∂^*_μ∂_μh) u`. -/
lemma comm_DbwDfw (U : Config N n) (μ : Fin 4) (h : Site n → ℂ) (u : Form0 N n) :
    mulF h (Dbw a U μ (Dfw a U μ u)) - Dbw a U μ (Dfw a U μ (mulF h u)) =
      mulF (dfw a μ h) (Dfw a U μ u) + mulF (dbw a μ h) (Dbw a U μ u) -
        mulF (dbw a μ (dfw a μ h)) u := by
  simp only [Dbw_eq, Dfw_eq]
  rw [comm_DD_first]
  have h1 : h - shF (sBw U μ).σ (shF (sFw U μ).σ h) = 0 := by
    funext z; simp [shF, sBw, sFw]
  have h2 : dF a (sBw U μ).σ (shF (sFw U μ).σ h) = -dfw a μ h := by
    funext z; simp only [dF, shF, sBw, sFw, sub_add_cancel, Pi.neg_apply]; ring
  have h3 : shF (sBw U μ).σ (dF a (sFw U μ).σ h) = -dbw a μ h := by
    funext z; simp only [dF, shF, sBw, sFw, sub_add_cancel, Pi.neg_apply]; ring
  rw [h1, h2, h3, neg_mulF, neg_mulF]
  have h0 : mulF (0 : Site n → ℂ) ((sBw U μ).D a ((sFw U μ).D a u)) = 0 := by
    funext z; simp [mulF]
  rw [h0]
  simp only [sBw, sFw]
  abel

/-- `lem:walk-factor`(i), the part of `eq:commutator-scalar` which comes from `Δ_U`:
`[h, Δ_U]u = Σ_μ ((∂_μh) D_{U,μ}u + (∂^*_μh) D^*_{U,μ}u) - (Δ_{id}h) u`. -/
theorem comm_lap_scalar (U : Config N n) (h : Site n → ℂ) (u : Form0 N n) (x : Site n) :
    h x • Lap a U u x - Lap a U (mulF h u) x =
      ∑ μ, (dfw a μ h x • Dfw a U μ u x + dbw a μ h x • Dbw a U μ u x) - lapF a h x • u x := by
  have key : ∀ μ, h x • Dbw a U μ (Dfw a U μ u) x - Dbw a U μ (Dfw a U μ (mulF h u)) x =
      dfw a μ h x • Dfw a U μ u x + dbw a μ h x • Dbw a U μ u x -
        dbw a μ (dfw a μ h) x • u x := fun μ => by
    have := congrFun (comm_DbwDfw a U μ h u) x
    simpa [mulF] using this
  simp only [Lap, lapF, Finset.smul_sum, Finset.sum_smul, ← Finset.sum_sub_distrib, key]

/-- `lem:walk-factor`(iv), for one direction:
`[h, D^*_{U,μ}D_{U,μ}]u = D^*_{U,μ}((∂^*_μh) u) + D_{U,μ}(ψ_μ u) - (∂^*_μ∂^*_μh) T^-_μ u`,
`ψ_μ(z) = (∂_μh)(z - e_μ)`. -/
lemma comm_DbwDfw_divergence (U : Config N n) (μ : Fin 4) (h : Site n → ℂ) (u : Form0 N n) :
    mulF h (Dbw a U μ (Dfw a U μ u)) - Dbw a U μ (Dfw a U μ (mulF h u)) =
      Dbw a U μ (mulF (dbw a μ h) u) +
        Dfw a U μ (mulF (shF (fun z => z - unit n μ) (dfw a μ h)) u) -
        mulF (dbw a μ (dbw a μ h)) ((sBw U μ).T u) := by
  simp only [Dbw_eq, Dfw_eq]
  rw [comm_DD_mid, Tbw_Dfw]
  have hψ : mulF (dF a (sFw U μ).σ h) ((sFw U μ).T u) =
      (sFw U μ).T (mulF (shF (fun z => z - unit n μ) (dfw a μ h)) u) := by
    rw [Shift.T_mulF]
    congr 1
    funext z; simp [shF, sFw, dF]
  rw [hψ, Dbw_Tfw, mulF_neg]
  have hl := leibniz_second a (sBw U μ) (dbw a μ h) u
  rw [hl]
  simp only [sBw, sFw]
  abel

/-- `lem:walk-factor`(iv), the part of `eq:commutator-divergence` which comes from `Δ_U`, on the
torus: `[h, Δ_U]u = Σ_μ (D^*_{U,μ}((∂^*_μh) u) + D_{U,μ}(ψ_μ u)) + c(u)`,
`c(u) = -Σ_μ (∂^*_μ∂^*_μh) T^-_μ u`. -/
theorem comm_lap_divergence (U : Config N n) (h : Site n → ℂ) (u : Form0 N n) (x : Site n) :
    h x • Lap a U u x - Lap a U (mulF h u) x =
      ∑ μ, (Dbw a U μ (mulF (dbw a μ h) u) x +
          Dfw a U μ (mulF (shF (fun z => z - unit n μ) (dfw a μ h)) u) x) -
        ∑ μ, dbw a μ (dbw a μ h) x • (sBw U μ).T u x := by
  have key : ∀ μ, h x • Dbw a U μ (Dfw a U μ u) x - Dbw a U μ (Dfw a U μ (mulF h u)) x =
      Dbw a U μ (mulF (dbw a μ h) u) x +
        Dfw a U μ (mulF (shF (fun z => z - unit n μ) (dfw a μ h)) u) x -
        dbw a μ (dbw a μ h) x • (sBw U μ).T u x := fun μ => by
    have := congrFun (comm_DbwDfw_divergence a U μ h u) x
    simpa [mulF] using this
  simp only [Lap, Finset.smul_sum, ← Finset.sum_sub_distrib, key]

/-! ### Symmetry (`lem:walk-factor`(v)) -/

lemma pair0_comm (l l' : Form0 N n) : pair0 a l l' = pair0 a l' l := by
  unfold pair0 ntr
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Matrix.trace_mul_comm]

lemma pair0_sub_right (l l' l'' : Form0 N n) :
    pair0 a l (fun x => l' x - l'' x) = pair0 a l l' - pair0 a l l'' := by
  rw [pair0_comm, pair0_sub_left, pair0_comm a l', pair0_comm a l'']

lemma pair0_sum_left {ι : Type*} (s : Finset ι) (l : Form0 N n) (f : ι → Form0 N n) :
    pair0 a (fun x => ∑ i ∈ s, f i x) l = ∑ i ∈ s, pair0 a (f i) l := by
  rw [pair0_comm, pair0_sum_right]
  exact Finset.sum_congr rfl fun i _ => pair0_comm a _ _

/-- `⟨D^*_{U,μ} λ, λ'⟩ = ⟨λ, D_{U,μ} λ'⟩`. -/
lemma pair0_Dbw (U : Config N n) (μ : Fin 4) (l l' : Form0 N n) :
    pair0 a (Dbw a U μ l) l' = pair0 a l (Dfw a U μ l') := by
  rw [pair0_comm, ← pair0_Dfw, pair0_comm]

/-- `Δ_U` is symmetric for the pairing, at every configuration (`lem:walk-factor`(v)). -/
theorem pair0_Lap (U : Config N n) (l l' : Form0 N n) :
    pair0 a (Lap a U l) l' = pair0 a l (Lap a U l') := by
  unfold Lap
  rw [pair0_sum_left, pair0_sum_right]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [pair0_Dbw, ← pair0_Dfw]

/-- The multiplication by a function is symmetric for the pairing. -/
lemma pair0_mulF (h : Site n → ℂ) (l l' : Form0 N n) :
    pair0 a (mulF h l) l' = pair0 a l (mulF h l') := by
  unfold pair0 mulF ntr
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Matrix.smul_mul, Matrix.mul_smul]

/-- An operator on `0`-forms is symmetric for the pairing. -/
def Symm (S : Form0 N n → Form0 N n) : Prop := ∀ l l', pair0 a (S l) l' = pair0 a l (S l')

/-- The commutator `K(h) = [h, S]` of a multiplication with an operator. -/
def comm (h : Site n → ℂ) (S : Form0 N n → Form0 N n) (l : Form0 N n) : Form0 N n :=
  fun x => mulF h (S l) x - S (mulF h l) x

/-- `lem:walk-factor`(v): `K'(h)^T = -K'(h)` for a symmetric operator. -/
theorem comm_antisymm {S : Form0 N n → Form0 N n} (hS : Symm a S) (h : Site n → ℂ)
    (l l' : Form0 N n) : pair0 a (comm h S l) l' = -pair0 a l (comm h S l') := by
  unfold comm
  rw [pair0_sub_left, pair0_sub_right, pair0_mulF, hS, hS, pair0_mulF]
  ring

/-- `lem:walk-factor`(v): the inverse of a symmetric operator is symmetric. -/
theorem symm_inverse {S G : Form0 N n → Form0 N n} (hS : Symm a S) (hSG : ∀ l, S (G l) = l) :
    Symm a G := fun l l' => by
  calc pair0 a (G l) l' = pair0 a (G l) (S (G l')) := by rw [hSG]
    _ = pair0 a (S (G l)) (G l') := (hS _ _).symm
    _ = pair0 a l (G l') := by rw [hSG]

/-- `lem:walk-factor`(v): `h G K'(h) = -(K'(h) G h)^T` for symmetric operators `S` and `G`. -/
theorem transposed_factor {S G : Form0 N n → Form0 N n} (hS : Symm a S) (hG : Symm a G)
    (h : Site n → ℂ) (l l' : Form0 N n) :
    pair0 a (mulF h (G (comm h S l))) l' = -pair0 a l (comm h S (G (mulF h l'))) := by
  rw [pair0_mulF, hG, comm_antisymm a hS]

/-- `Δ_U` with the commutator: the part of `K'(h)` which comes from `Δ_U` is antisymmetric. -/
theorem comm_lap_antisymm (U : Config N n) (h : Site n → ℂ) (l l' : Form0 N n) :
    pair0 a (comm h (Lap a U) l) l' = -pair0 a l (comm h (Lap a U) l') :=
  comm_antisymm a (pair0_Lap a U) h l l'

end WalkCommutators
end CoreLean

end
