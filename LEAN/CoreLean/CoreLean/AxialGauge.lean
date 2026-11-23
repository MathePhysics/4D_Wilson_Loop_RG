/-
The algebra of the axial gauge in BALABAN_CORE.tex (`39c88d556af9`, `sec:gauges`): `lem:axial-representative`,
`lem:chain-transport`(i)–(ii), and `lem:admissible-explicit`(i)–(iii), in abstract form.

The model of one block `B^j(y)`: the points of `T^{(n)}` in the block form a type `X n`; `p n : X n → X (n+1)`
sends a point to the centre of its block of order one (`x_n ∈ B(x_{n+1})`), and `ι n : X (n+1) → X n` regards
a point of `T^{(n+1)}` as a point of `T^{(n)}`, the centre of its own block (`p n (ι n y) = y`). A gauge
transformation is a family `u n : X n → Gp` with `u n (ι n y) = u (n+1) y`. The transports enter as data
`a n x`, `b n x` (the transports of the two averaged configurations from `p n x` to `x`), with the rule
`𝐔^u_𝔱(y, x) = u(y)𝐔_𝔱(y, x)u(x)⁻¹` of `def:transports` and the trivial transport at a centre.

* `rep`: the solution of `u(x) = a(x)⁻¹u(p x)b(x)` below the level `j` with given values `top` from the
  level `j` on (`eq:axial-transformation`); `rep_axial`, `rep_unique`, `rep_compat` (the values at the
  different levels agree), `rep_conj` (covariance).
* `axial_representative` (`lem:axial-representative`): exactly one `u ∈ 𝒢_𝐁` with `U^u` in the axial gauge of
  `U₀`; `axial_representative_covariant`: the representative of `U^w` relative to `U₀^w` is `wuw⁻¹`, i.e.
  `(U^u)^w` — for every gauge transformation `w`, constant on the blocks or not.
* `tau`, `tau_covariant` (`lem:chain-transport`(i), `eq:transport-covariance`), `tau_trivial`
  (`lem:chain-transport`(ii)).
* `avg_pow_eq` (`lem:admissible-explicit`(i)): `M^l(W) = v_l · W^{(l)}` with an abstract covariant average
  on abstract bonds.
* `N_eq` (`lem:admissible-explicit`(ii)): `N^n_{𝐔₀}(u) = u v_n`, the argument of each logarithm being
  `W^{(n-1)}_𝔱(y', x)T₀⁻¹`, independent of `u`.
* `admissible_unique` (`lem:admissible-explicit`(iii)): exactly one `u_A` with `W^{u_A}` in the axial gauge
  of `𝐔₀` and `N^j(u_A)(y) = 1`, given by `u_A(y) = v_j(y)⁻¹` and `eq:chain-recursion`.
-/
import CoreLean.ChartLog

open NormedSpace
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace CoreLean

namespace Axial

/-! ### The downward recursion -/

section Recursion

variable {Gp : Type*} [Group Gp] {X : ℕ → Type*} (j : ℕ) (p : ∀ n, X n → X (n + 1))

/-- The solution of `u(x) = a(x)⁻¹ u(p x) b(x)` for `n < j`, with `u = top` from the level `j` on. -/
def rep (top a b : ∀ n, X n → Gp) (n : ℕ) : X n → Gp :=
  if _h : n < j then fun x => (a n x)⁻¹ * rep top a b (n + 1) (p n x) * b n x else top n
termination_by j - n

variable {j p} {top a b : ∀ n, X n → Gp}

lemma rep_of_lt {n : ℕ} (h : n < j) (x : X n) :
    rep j p top a b n x = (a n x)⁻¹ * rep j p top a b (n + 1) (p n x) * b n x := by
  rw [rep, dite_eq_left_of_eq_true (eq_true h)]

lemma rep_of_ge {n : ℕ} (h : j ≤ n) (x : X n) : rep j p top a b n x = top n x := by
  rw [rep, dite_eq_right_of_eq_false (eq_false (not_lt.mpr h))]

/-- The solution satisfies `u(p x)b(x)u(x)⁻¹ = a(x)`. -/
lemma rep_axial {n : ℕ} (h : n < j) (x : X n) :
    rep j p top a b (n + 1) (p n x) * b n x * (rep j p top a b n x)⁻¹ = a n x := by
  rw [rep_of_lt h]; group

/-- Uniqueness: a family with the values `top` from the level `j` on and `u(p x)b(x)u(x)⁻¹ = a(x)` below
is `rep`. -/
theorem rep_unique (u : ∀ n, X n → Gp) (htop : ∀ n, j ≤ n → ∀ x, u n x = top n x)
    (hax : ∀ n, n < j → ∀ x, u (n + 1) (p n x) * b n x * (u n x)⁻¹ = a n x) (n : ℕ) (x : X n) :
    u n x = rep j p top a b n x := by
  by_cases h : n < j
  · rw [rep_of_lt h, ← rep_unique u htop hax (n + 1) (p n x), ← hax n h x]; group
  · rw [rep_of_ge (not_lt.mp h), htop n (not_lt.mp h)]
termination_by j - n

/-- The values at the different levels agree: `u(ι y) = u(y)`, since the transports at a centre are
trivial. -/
lemma rep_compat (ι : ∀ n, X (n + 1) → X n) (hp : ∀ n y, p n (ι n y) = y)
    (ha : ∀ n y, a n (ι n y) = 1) (hb : ∀ n y, b n (ι n y) = 1) {n : ℕ} (h : n < j) (y : X (n + 1)) :
    rep j p top a b n (ι n y) = rep j p top a b (n + 1) y := by
  rw [rep_of_lt h, ha, hb, hp, inv_one, one_mul, mul_one]

/-- Covariance: for a family `w`, the data `w(p x)a(x)w(x)⁻¹`, `w(p x)b(x)w(x)⁻¹` and the values
`w top w⁻¹` give the solution `w u w⁻¹`. -/
theorem rep_conj (w : ∀ n, X n → Gp) (n : ℕ) (x : X n) :
    rep j p (fun n x => w n x * top n x * (w n x)⁻¹)
        (fun n x => w (n + 1) (p n x) * a n x * (w n x)⁻¹)
        (fun n x => w (n + 1) (p n x) * b n x * (w n x)⁻¹) n x =
      w n x * rep j p top a b n x * (w n x)⁻¹ := by
  by_cases h : n < j
  · rw [rep_of_lt h, rep_of_lt h, rep_conj w (n + 1) (p n x)]; group
  · rw [rep_of_ge (not_lt.mp h), rep_of_ge (not_lt.mp h)]
termination_by j - n

/-- `lem:axial-representative`: there is exactly one `u` with `u = 1` from the level `j` on (`u ∈ 𝒢_𝐁`)
for which `U^u` is in the axial gauge of `U₀`, `u(p x)M(U)_𝔱(p x, x)u(x)⁻¹ = M(U₀)_𝔱(p x, x)`
(`eq:axial-gauge`); it is `rep` (`eq:axial-transformation`). -/
theorem axial_representative (a b : ∀ n, X n → Gp) :
    ∃! u : ∀ n, X n → Gp, (∀ n, j ≤ n → ∀ x, u n x = 1) ∧
      ∀ n, n < j → ∀ x, u (n + 1) (p n x) * b n x * (u n x)⁻¹ = a n x := by
  refine ⟨rep j p (fun _ _ => 1) a b, ⟨fun n h x => rep_of_ge h x, fun n h x => rep_axial h x⟩,
    fun u ⟨htop, hax⟩ => ?_⟩
  funext n x
  exact rep_unique u htop hax n x

/-- `lem:axial-representative`, the covariance: if `u` is the representative of `U` relative to `U₀`, then
`w u w⁻¹` is that of `U^w` relative to `U₀^w`, so that the representative of `U^w` is `(U^u)^w`. -/
theorem axial_representative_covariant (a b w : ∀ n, X n → Gp) (n : ℕ) (x : X n) :
    rep j p (fun _ _ => 1) (fun n x => w (n + 1) (p n x) * a n x * (w n x)⁻¹)
        (fun n x => w (n + 1) (p n x) * b n x * (w n x)⁻¹) n x =
      w n x * rep j p (fun _ _ => 1) a b n x * (w n x)⁻¹ := by
  have := rep_conj (j := j) (p := p) (top := fun _ _ => (1 : Gp)) (a := a) (b := b) w n x
  simpa only [mul_one, mul_inv_cancel] using this

/-! ### The transport from the centre of a block -/

variable (j p) in
/-- `τ_{y, x}(𝐔) = M^{j-1}_𝔱(x_j, x_{j-1}) ⋯ M^m_𝔱(x_{m+1}, x_m)` (`eq:chain-transport`), for `x` at the
level `m`, with the transports `t n x` from `p n x` to `x`. -/
def tau (t : ∀ n, X n → Gp) : ∀ n, X n → Gp := rep j p (fun _ _ => 1) (fun _ _ => 1) t

variable (j p) in
/-- The value of `w` at the top of the chain, `w(y)`. -/
def wTop (w : ∀ n, X n → Gp) : ∀ n, X n → Gp := rep j p w (fun _ _ => 1) (fun _ _ => 1)

lemma tau_of_lt (t : ∀ n, X n → Gp) {n : ℕ} (h : n < j) (x : X n) :
    tau j p t n x = tau j p t (n + 1) (p n x) * t n x := by
  rw [tau, rep_of_lt h]; simp only [inv_one, one_mul]

/-- `lem:chain-transport`(i): `τ_{y, x}(𝐔^w) = w(y) τ_{y, x}(𝐔) w(x)⁻¹`. -/
theorem tau_covariant (t w : ∀ n, X n → Gp) (n : ℕ) (x : X n) :
    tau j p (fun n x => w (n + 1) (p n x) * t n x * (w n x)⁻¹) n x =
      wTop j p w n x * tau j p t n x * (w n x)⁻¹ := by
  by_cases h : n < j
  · rw [tau_of_lt _ h, tau_of_lt _ h, tau_covariant t w (n + 1) (p n x)]
    unfold wTop
    rw [rep_of_lt h (top := w)]
    group
  · unfold tau wTop
    rw [rep_of_ge (not_lt.mp h), rep_of_ge (not_lt.mp h), rep_of_ge (not_lt.mp h)]
    group
termination_by j - n

/-- `lem:chain-transport`(ii): if `g(x) = τ_{y, x}(U)` and `g(y) = 1`, then `τ_{y, x}(U^g) = 1`. -/
theorem tau_trivial (t g : ∀ n, X n → Gp) {n : ℕ} (x : X n) (hg : g n x = tau j p t n x)
    (hy : wTop j p g n x = 1) :
    tau j p (fun n x => g (n + 1) (p n x) * t n x * (g n x)⁻¹) n x = 1 := by
  rw [tau_covariant, hy, hg, one_mul, mul_inv_cancel]

end Recursion

/-! ### The averages of the moved configuration -/

section Bonds

variable {Gp : Type*} [Group Gp] {X : ℕ → Type*} {Bd : ℕ → Type*}
  (src tgt : ∀ n, Bd n → X n) (ι : ∀ n, X (n + 1) → X n)

/-- The gauge transform `V^u(c) = u(c₋)V(c)u(c₊)⁻¹` of a configuration on the bonds. -/
def gt {n : ℕ} (u : X n → Gp) (V : Bd n → Gp) : Bd n → Gp :=
  fun c => u (src n c) * V c * (u (tgt n c))⁻¹

/-- The iterated average `M^l`. -/
def avgPow (M : ∀ n, (Bd n → Gp) → (Bd (n + 1) → Gp)) (W : Bd 0 → Gp) : ∀ l, Bd l → Gp
  | 0 => W
  | l + 1 => M l (avgPow M W l)

/-- `W^{(l)}` of `eq:site-factors`: `W^{(l+1)}(c) = v^{(l+1)}(c₋)⁻¹ M(W^{(l)})(c) v^{(l+1)}(c₊)`. -/
def Wl (M : ∀ n, (Bd n → Gp) → (Bd (n + 1) → Gp)) (v : ∀ l, X (l + 1) → Gp) (W : Bd 0 → Gp) :
    ∀ l, Bd l → Gp
  | 0 => W
  | l + 1 => gt src tgt (fun y => (v l y)⁻¹) (M l (Wl M v W l))

/-- `v_l = v^{(1)} ⋯ v^{(l)}`, the factor `v_{l-1}` read at the point `ι y` of `T^{(l-1)}`. -/
def vprod (v : ∀ l, X (l + 1) → Gp) : ∀ l, X l → Gp
  | 0 => fun _ => 1
  | l + 1 => fun y => vprod v l (ι l y) * v l y

lemma gt_gt {n : ℕ} (u u' : X n → Gp) (V : Bd n → Gp) :
    gt src tgt u (gt src tgt u' V) = gt src tgt (fun x => u x * u' x) V := by
  funext c; simp only [gt]; group

/-- `lem:admissible-explicit`(i): `M^l(W)(c) = v_l(c₋) W^{(l)}(c) v_l(c₊)⁻¹`, for an average which commutes
with the gauge transformations, `M(V^u) = M(V)^{u ∘ ι}` (`lem:average`(iii)). -/
theorem avg_pow_eq (M : ∀ n, (Bd n → Gp) → (Bd (n + 1) → Gp))
    (hM : ∀ n (u : X n → Gp) (V : Bd n → Gp), M n (gt src tgt u V) = gt src tgt (u ∘ ι n) (M n V))
    (v : ∀ l, X (l + 1) → Gp) (W : Bd 0 → Gp) :
    ∀ l, avgPow M W l = gt src tgt (vprod ι v l) (Wl src tgt M v W l)
  | 0 => by funext c; simp [avgPow, Wl, vprod, gt]
  | l + 1 => by
    have hW : M l (Wl src tgt M v W l) = gt src tgt (v l) (Wl src tgt M v W (l + 1)) := by
      simp only [Wl, gt_gt]; funext c; simp [gt]
    rw [avgPow, avg_pow_eq M hM v W l, hM, hW, gt_gt]
    rfl

end Bonds

/-! ### The averaged gauge transformation -/

section Averaged

variable {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "GLN" => (Matrix (Fin N) (Fin N) ℂ)ˣ

variable {X : ℕ → Type*} [∀ n, Fintype (X n)] [∀ n, DecidableEq (X n)]

/-- The block mean `exp(L⁻⁴ Σ_{x ∈ B(y)} Log F(x))`, with `c = L⁻⁴`. -/
def blockExp (p : ∀ n, X n → X (n + 1)) (c : ℂ) {n : ℕ} (F : X n → GLN) (y : X (n + 1)) : GLN :=
  expU (c • ∑ x ∈ Finset.univ.filter (fun x => p n x = y), LogM ((F x : GLN) : Mat))

/-- `eq:averaged-gauge-transformation`:
`v̄(y) = v(y) exp(L⁻⁴ Σ_{x ∈ B(y)} Log(v(y)⁻¹ Ad_{𝐕_{0,𝔱}(y, x)} v(x)))`. -/
def Nstep (p : ∀ n, X n → X (n + 1)) (ι : ∀ n, X (n + 1) → X n) (c : ℂ) (T0 : ∀ n, X n → GLN)
    {n : ℕ} (u : X n → GLN) (y : X (n + 1)) : GLN :=
  u (ι n y) * blockExp p c (fun x => (u (ι n y))⁻¹ * (T0 n x * u x * (T0 n x)⁻¹)) y

/-- `N^n_{𝐔₀}(u)`, `eq:averaged-gauge-transformation` applied `n` times. -/
def Npow (p : ∀ n, X n → X (n + 1)) (ι : ∀ n, X (n + 1) → X n) (c : ℂ) (T0 : ∀ n, X n → GLN)
    (u : ∀ n, X n → GLN) : ∀ n, X n → GLN
  | 0 => u 0
  | n + 1 => Nstep p ι c T0 (Npow p ι c T0 u n)

/-- The site factors: `v^{(n+1)}(y) = exp(L⁻⁴ Σ_{x ∈ B(y)} Log(W^{(n)}_𝔱(y, x)𝐔^{(n)}_{0,𝔱}(y, x)⁻¹))` and
`v_{n+1}(y) = v_n(y)v^{(n+1)}(y)` (`eq:site-factors`). -/
def vfac (p : ∀ n, X n → X (n + 1)) (ι : ∀ n, X (n + 1) → X n) (c : ℂ) (T0 : ∀ n, X n → GLN)
    (Wt : ∀ n, X n → GLN) : ∀ n, X n → GLN
  | 0 => fun _ => 1
  | n + 1 => fun y => vfac p ι c T0 Wt n (ι n y) * blockExp p c (fun x => Wt n x * (T0 n x)⁻¹) y

/-- `lem:admissible-explicit`(ii): if `W^u` satisfies the equations of the axial gauge along the chains
(`eq:chain-recursion`, `T₀(x)u(x) = u(p x)M^n(W)_𝔱(p x, x)`), the transports of `M^n(W)` are those of
`W^{(n)}` transformed by `v_n` (`(i)` and `def:transports`), and `u` is a gauge transformation, then
`N^n_{𝐔₀}(u) = u v_n` for `n ≤ j`. -/
theorem N_eq (p : ∀ n, X n → X (n + 1)) (ι : ∀ n, X (n + 1) → X n) (c : ℂ) (T0 : ∀ n, X n → GLN)
    (j : ℕ) (u Mt Wt : ∀ n, X n → GLN)
    (hrec : ∀ n, n < j → ∀ x, T0 n x * u n x = u (n + 1) (p n x) * Mt n x)
    (hM : ∀ n, n < j → ∀ x, Mt n x = vfac p ι c T0 Wt n (ι n (p n x)) * Wt n x *
      (vfac p ι c T0 Wt n x)⁻¹)
    (hcomp : ∀ n, n < j → ∀ y, u n (ι n y) = u (n + 1) y) (n : ℕ) (hn : n ≤ j) :
    ∀ x, Npow p ι c T0 u n x = u n x * vfac p ι c T0 Wt n x := by
  induction n with
  | zero => intro x; simp [Npow, vfac]
  | succ n ihn =>
    intro y
    have hlt : n < j := by omega
    have ih : Npow p ι c T0 u n = fun x => u n x * vfac p ι c T0 Wt n x :=
      funext (ihn (by omega))
    -- the argument of the logarithm does not depend on `u`
    have harg : ∀ x ∈ Finset.univ.filter (fun x => p n x = y),
        ((u n (ι n y) * vfac p ι c T0 Wt n (ι n y))⁻¹ *
          (T0 n x * (u n x * vfac p ι c T0 Wt n x) * (T0 n x)⁻¹)) = Wt n x * (T0 n x)⁻¹ := by
      intro x hx
      have hpx : p n x = y := (Finset.mem_filter.mp hx).2
      have h1 : T0 n x * u n x = u n (ι n y) * Mt n x := by
        rw [hrec n hlt x, hpx, hcomp n hlt y]
      have h2 : Mt n x = vfac p ι c T0 Wt n (ι n y) * Wt n x * (vfac p ι c T0 Wt n x)⁻¹ := by
        rw [hM n hlt x, hpx]
      calc (u n (ι n y) * vfac p ι c T0 Wt n (ι n y))⁻¹ *
            (T0 n x * (u n x * vfac p ι c T0 Wt n x) * (T0 n x)⁻¹)
          = (u n (ι n y) * vfac p ι c T0 Wt n (ι n y))⁻¹ *
            ((T0 n x * u n x) * vfac p ι c T0 Wt n x * (T0 n x)⁻¹) := by group
        _ = Wt n x * (T0 n x)⁻¹ := by rw [h1, h2]; group
    have hsum : ∑ x ∈ Finset.univ.filter (fun x => p n x = y),
        LogM ((((Npow p ι c T0 u n (ι n y))⁻¹ * (T0 n x * Npow p ι c T0 u n x * (T0 n x)⁻¹) : GLN) :
          Mat)) =
        ∑ x ∈ Finset.univ.filter (fun x => p n x = y), LogM (((Wt n x * (T0 n x)⁻¹ : GLN) : Mat)) :=
      Finset.sum_congr rfl fun x hx => by
        rw [ih]
        exact congrArg (fun g : GLN => LogM (g : Mat)) (harg x hx)
    have hblock : blockExp p c (fun x => (Npow p ι c T0 u n (ι n y))⁻¹ *
        (T0 n x * Npow p ι c T0 u n x * (T0 n x)⁻¹)) y =
        blockExp p c (fun x => Wt n x * (T0 n x)⁻¹) y := by
      unfold blockExp
      rw [hsum]
    have hNs : Npow p ι c T0 u (n + 1) y = Nstep p ι c T0 (Npow p ι c T0 u n) y := rfl
    have hvs : vfac p ι c T0 Wt (n + 1) y =
        vfac p ι c T0 Wt n (ι n y) * blockExp p c (fun x => Wt n x * (T0 n x)⁻¹) y := rfl
    rw [hNs, Nstep, hblock, hvs, ← hcomp n hlt y]
    have hu : Npow p ι c T0 u n (ι n y) = u n (ι n y) * vfac p ι c T0 Wt n (ι n y) := by rw [ih]
    rw [hu, mul_assoc]

/-- `lem:admissible-explicit`(iii): with trivial transports at the centres, there is exactly one `u` (with
`u = 1` above the level `j`) for which `W^u` satisfies the equations of the axial gauge, `u` is a gauge
transformation, and `N^j_{𝐔₀}(u)(y) = 1`; it has `u(y) = v_j(y)⁻¹` and satisfies `eq:chain-recursion`. -/
theorem admissible_unique (p : ∀ n, X n → X (n + 1)) (ι : ∀ n, X (n + 1) → X n) (c : ℂ)
    (T0 : ∀ n, X n → GLN) (j : ℕ) (Mt Wt : ∀ n, X n → GLN)
    (hM : ∀ n, n < j → ∀ x, Mt n x = vfac p ι c T0 Wt n (ι n (p n x)) * Wt n x *
      (vfac p ι c T0 Wt n x)⁻¹)
    (hp : ∀ n y, p n (ι n y) = y) (hT : ∀ n y, T0 n (ι n y) = 1) (hMt : ∀ n y, Mt n (ι n y) = 1) :
    ∃! u : ∀ n, X n → GLN, (∀ n, j < n → ∀ x, u n x = 1) ∧
      (∀ n, n < j → ∀ x, T0 n x * u n x = u (n + 1) (p n x) * Mt n x) ∧
      (∀ n, n < j → ∀ y, u n (ι n y) = u (n + 1) y) ∧
      (∀ y, Npow p ι c T0 u j y = 1) := by
  classical
  set top : ∀ n, X n → GLN := fun n x => if n = j then (vfac p ι c T0 Wt n x)⁻¹ else 1
  set u0 := rep j p top T0 Mt
  have hax : ∀ n, n < j → ∀ x, T0 n x * u0 n x = u0 (n + 1) (p n x) * Mt n x := fun n h x => by
    have := rep_axial (j := j) (p := p) (top := top) (a := T0) (b := Mt) h x
    show T0 n x * rep j p top T0 Mt n x = rep j p top T0 Mt (n + 1) (p n x) * Mt n x
    rw [← this]; group
  have hcomp : ∀ n, n < j → ∀ y, u0 n (ι n y) = u0 (n + 1) y := fun n h y =>
    rep_compat ι hp hT hMt h y
  refine ⟨u0, ⟨fun n h x => ?_, hax, hcomp, fun y => ?_⟩, fun u ⟨hu1, hurec, hucomp, huN⟩ => ?_⟩
  · show rep j p top T0 Mt n x = 1
    rw [rep_of_ge h.le]; simp [top, h.ne']
  · rw [N_eq p ι c T0 j u0 Mt Wt hax hM hcomp j le_rfl y]
    show rep j p top T0 Mt j y * _ = 1
    rw [rep_of_ge le_rfl]
    simp [top]
  · funext n x
    refine rep_unique u (fun n hn x => ?_) (fun n hn x => ?_) n x
    · rcases Nat.eq_or_lt_of_le hn with h | hlt
      · subst h
        have := huN x
        rw [N_eq p ι c T0 j u Mt Wt hurec hM hucomp j le_rfl x] at this
        simp only [top, ↓reduceIte]
        exact eq_inv_of_mul_eq_one_left this
      · rw [hu1 n hlt x]; simp [top, hlt.ne']
    · rw [← hurec n hn x]; group

end Averaged

end Axial

end CoreLean

end
