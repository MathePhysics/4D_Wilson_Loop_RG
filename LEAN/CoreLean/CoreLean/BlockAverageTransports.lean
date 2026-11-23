/-
`lem:block-average-transports` of BALABAN_CORE.tex (`c41070d66d5d`), abstract form.

Model. The sites of the scales `i, i + 1, …` are finite types `X l` (`l` counted from `i`), and the
block structure is a map `p l : X l → X (l + 1)`, the block `B(y)` of `y ∈ X (l + 1)` being the fibre of
`p l` over `y` (`B^n(y)` is the fibre of the iterated map `anc n`). The block average of the order one
at the configuration `𝐔^{(l)}` is `eq:block-average`, `(Q'λ)(y) = L^{-4} Σ_{x ∈ B(y)} Ad_{V_l(y,x)} λ(x)`
with the transports `V_l(y, x) = 𝐔^{(l)}(y, x)` (`blockAvg`), and `Q'_n = Q'(𝐔^{(n-1)}) ⋯ Q'(𝐔^{(0)})`
(`eq:composite-linear-part`, `Qn`).

* `composite`: `(Q'_nλ)(y) = L^{-4n} Σ_{x ∈ B^n(y)} Ad_{W(y,x)} λ(x)`, with
  `W(y, x) = 𝐔^{(n-1)}(y_n, y_{n-1}) ⋯ 𝐔^{(0)}(y_1, y_0)` (`W`), `y_l` the block centre of the order `l`
  of `x`.
* `pert_of_avg`: `prop:relative-average`(vi) for `Q'`, `‖Q'(𝐔^{(l)}) - Q'(U_l)‖ ≤ C₁α₁^{(l)}` in the
  supremum norms, applied to the `0`-form which is `Z` at one site, gives
  `L^{-4}‖(Ad_{𝐔^{(l)}(y,x)} - Ad_{U_l(y,x)})Z‖ ≤ C₁α₁^{(l)}‖Z‖`.
* `near_iso`: an isometry plus a map of norm at most `ε ≤ 1/2` and its inverse change the norm by a
  factor of at most `e^{2ε}` (the Neumann series of the core, in the form `(1 - ε)⁻¹ ≤ e^{2ε}`).
* `W_bound`: the product changes the norm by at most `exp(2Σ_l ε_l)`, and so does its inverse.
* `sum_alpha_le`: `Σ_{l<n} 2C'₃α₁L^{-(n-l)} ≤ C'₃α₁` for `L ≥ 3`.
* `block_average_transports`: the lemma — the identity, and `‖Ad_{W(y,x)}^{±1}Z‖ ≤ 2‖Z‖`,
  `|Ad_{W(y,x)}^{±1}Z| ≤ 2√N|Z|`, from `C_A ≥ 16L⁴C₁C'₃`, `C_Ac''₄ ≤ log 2`, and `α₁ ≤ c''₄`.

Inputs as hypotheses, as in the core: `prop:relative-average`(vi) for `Q'` at each order, with the
constants `α₁^{(l)} = 2C'₃α₁L^{-(n-l)}` of the proof of `lem:average-kernels`
(`prop:relative-average-order`, stated in the core); and that the transports `U_l(y, x)` of the gauge
fields are isometries, which the core derives from `lem:group-mean` (they are means of elements of `G`).
Not formalised: that `W(y, x) ∈ G^c`.
-/
import CoreLean.Differences
import CoreLean.OpNorm

open scoped Matrix.Norms.L2Operator
open Finset

noncomputable section

namespace CoreLean
namespace BlockAverageTransports

variable {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "GLN" => (Matrix (Fin N) (Fin N) ℂ)ˣ

variable {X : ℕ → Type*} [∀ l, Fintype (X l)] [∀ l, DecidableEq (X l)] (p : ∀ l, X l → X (l + 1))

/-- `eq:block-average`: `(Q'λ)(y) = c Σ_{x ∈ B(y)} Ad_{V(y,x)} λ(x)`, `c = L^{-4}`. -/
def blockAvg (c : ℂ) {l : ℕ} (V : X (l + 1) → X l → GLN) (lam : X l → Mat) (y : X (l + 1)) : Mat :=
  c • ∑ x ∈ univ.filter (fun x => p l x = y), Ad (V y x) (lam x)

/-- The block centre of the order `l` of a site `x` of the finest scale. -/
def anc : (l : ℕ) → X 0 → X l
  | 0, x => x
  | l + 1, x => p l (anc l x)

/-- `Q'_n = Q'(𝐔^{(n-1)}) ⋯ Q'(𝐔^{(0)})` (`eq:composite-linear-part`). -/
def Qn (c : ℂ) (V : ∀ l, X (l + 1) → X l → GLN) : (n : ℕ) → (X 0 → Mat) → (X n → Mat)
  | 0, lam => lam
  | n + 1, lam => blockAvg p c (V n) (Qn c V n lam)

/-- `W(y, x) = 𝐔^{(n-1)}(y_n, y_{n-1}) ⋯ 𝐔^{(0)}(y_1, y_0)`, `y_l = anc l x`. -/
def W (V : ∀ l, X (l + 1) → X l → GLN) : (n : ℕ) → X 0 → GLN
  | 0, _ => 1
  | n + 1, x => V n (anc p (n + 1) x) (anc p n x) * W V n x

lemma Ad_one (Z : Mat) : Ad (1 : GLN) Z = Z := by simp [Ad]

lemma Ad_zero (V : GLN) : Ad V (0 : Mat) = 0 := by simp [Ad]

/-- The composite average: `(Q'_nλ)(y) = c^n Σ_{x ∈ B^n(y)} Ad_{W(y,x)} λ(x)`. -/
theorem composite (c : ℂ) (V : ∀ l, X (l + 1) → X l → GLN) (n : ℕ) (lam : X 0 → Mat) (y : X n) :
    Qn p c V n lam y = c ^ n • ∑ x ∈ univ.filter (fun x => anc p n x = y), Ad (W p V n x) (lam x) := by
  induction n with
  | zero =>
    have hf : univ.filter (fun x => anc p 0 x = y) = {y} := by
      ext x; rw [Finset.mem_filter, Finset.mem_singleton]; simp [anc]
    simp only [Qn, pow_zero, one_smul, W]
    rw [hf, Finset.sum_singleton, Ad_one]
  | succ n ih =>
    simp only [Qn, blockAvg, ih, Ad_smul, Ad_sum, ← Finset.smul_sum, smul_smul, pow_succ]
    rw [mul_comm c (c ^ n)]
    congr 1
    rw [← Finset.sum_fiberwise_of_maps_to (s := univ.filter (fun x => anc p (n + 1) x = y))
      (t := univ.filter (fun y' => p n y' = y)) (g := anc p n)
      (fun x hx => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hx).2⟩)]
    refine Finset.sum_congr rfl fun y' hy' => ?_
    rw [Finset.filter_filter]
    have hy'' : p n y' = y := (Finset.mem_filter.mp hy').2
    refine Finset.sum_congr ?_ fun x hx => ?_
    · ext x
      rw [Finset.mem_filter, Finset.mem_filter]
      constructor
      · intro h
        refine ⟨Finset.mem_univ _, ?_, h.2⟩
        show p n (anc p n x) = y
        rw [h.2, hy'']
      · intro h; exact ⟨Finset.mem_univ _, h.2.2⟩
    · have hx' : anc p n x = y' := (Finset.mem_filter.mp hx).2.2
      simp only [W, anc, hx', hy'', Ad_mul]

/-- A `0`-form which is `Z` at one site. -/
lemma blockAvg_single (c : ℂ) {l : ℕ} (V : X (l + 1) → X l → GLN) (x₀ : X l) (Z : Mat) :
    blockAvg p c V (fun x => if x = x₀ then Z else 0) (p l x₀) = c • Ad (V (p l x₀) x₀) Z := by
  unfold blockAvg
  congr 1
  rw [Finset.sum_eq_single x₀]
  · simp
  · intro x _ hx; simp [hx, Ad_zero]
  · intro h; simp at h

/-- `prop:relative-average`(vi) for `Q'` at one site: if `‖(Q'(𝐔) - Q'(U))λ‖_∞ ≤ K‖λ‖_∞`, then
`‖Ad_{𝐔(y,x)}Z - Ad_{U(y,x)}Z‖ ≤ |c|⁻¹K‖Z‖`. -/
theorem pert_of_avg (c : ℂ) (hc : c ≠ 0) {l : ℕ} (V V₀ : X (l + 1) → X l → GLN) (K : ℝ)
    (h : ∀ (lam : X l → Mat) (M : ℝ), (∀ x, ‖lam x‖ ≤ M) →
      ∀ y, ‖blockAvg p c V lam y - blockAvg p c V₀ lam y‖ ≤ K * M) (x₀ : X l) (Z : Mat) :
    ‖Ad (V (p l x₀) x₀) Z - Ad (V₀ (p l x₀) x₀) Z‖ ≤ ‖c‖⁻¹ * K * ‖Z‖ := by
  have hb := h (fun x => if x = x₀ then Z else 0) ‖Z‖
    (fun x => by by_cases hx : x = x₀ <;> simp [hx]) (p l x₀)
  rw [blockAvg_single, blockAvg_single, ← smul_sub, norm_smul] at hb
  have hcn : 0 < ‖c‖ := norm_pos_iff.mpr hc
  rw [mul_assoc, le_inv_mul_iff₀ hcn]
  linarith

/-- An isometry plus a map of norm at most `ε ≤ 1/2`, and its inverse, change the norm by a factor of
at most `e^{2ε}`. -/
theorem near_iso {V U : GLN} {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 2) (hU : ∀ Z, ‖Ad U Z‖ = ‖Z‖)
    (h : ∀ Z, ‖Ad V Z - Ad U Z‖ ≤ ε * ‖Z‖) (Z : Mat) :
    ‖Ad V Z‖ ≤ Real.exp (2 * ε) * ‖Z‖ ∧ ‖Ad V⁻¹ Z‖ ≤ Real.exp (2 * ε) * ‖Z‖ := by
  have he : 1 + 2 * ε ≤ Real.exp (2 * ε) := by linarith [Real.add_one_le_exp (2 * ε)]
  constructor
  · have h1 : ‖Ad V Z‖ ≤ ‖Ad U Z‖ + ‖Ad V Z - Ad U Z‖ := by
      have := norm_add_le (Ad U Z) (Ad V Z - Ad U Z)
      rwa [add_sub_cancel] at this
    rw [hU] at h1
    nlinarith [h Z, norm_nonneg Z]
  · have hVY : Ad V (Ad V⁻¹ Z) = Z := by
      rw [← Ad_mul, mul_inv_cancel, Ad_one]
    have h2 : ‖Ad U (Ad V⁻¹ Z)‖ ≤ ‖Ad V (Ad V⁻¹ Z)‖ + ‖Ad V (Ad V⁻¹ Z) - Ad U (Ad V⁻¹ Z)‖ := by
      have := norm_sub_le (Ad V (Ad V⁻¹ Z)) (Ad V (Ad V⁻¹ Z) - Ad U (Ad V⁻¹ Z))
      rwa [sub_sub_cancel] at this
    have hhY := h (Ad V⁻¹ Z)
    rw [hU, hVY] at h2
    rw [hVY] at hhY
    generalize Ad V⁻¹ Z = Y at h2 hhY ⊢
    have h3 : (1 - ε) * ‖Y‖ ≤ ‖Z‖ := by nlinarith
    have hY := norm_nonneg Y
    have h4 : 1 ≤ (1 - ε) * (1 + 2 * ε) := by nlinarith
    calc ‖Y‖ ≤ (1 - ε) * (1 + 2 * ε) * ‖Y‖ := by nlinarith
      _ = (1 + 2 * ε) * ((1 - ε) * ‖Y‖) := by ring
      _ ≤ (1 + 2 * ε) * ‖Z‖ := by gcongr
      _ ≤ Real.exp (2 * ε) * ‖Z‖ := by gcongr

/-- The product of the transports: `‖Ad_{W}^{±1}Z‖ ≤ exp(2Σ_{l<m} ε_l)‖Z‖`, if every factor is an
isometry plus a map of norm at most `ε_l ≤ 1/2`. -/
theorem W_bound (V V₀ : ∀ l, X (l + 1) → X l → GLN) (n : ℕ) (ε : ℕ → ℝ)
    (hε0 : ∀ l, 0 ≤ ε l) (hε : ∀ l < n, ε l ≤ 1 / 2)
    (hV₀ : ∀ l y x Z, ‖Ad (V₀ l y x) Z‖ = ‖Z‖)
    (hpert : ∀ l < n, ∀ (x : X l) (Z : Mat), ‖Ad (V l (p l x) x) Z - Ad (V₀ l (p l x) x) Z‖ ≤ ε l * ‖Z‖) :
    ∀ m ≤ n, ∀ (x : X 0) (Z : Mat),
      ‖Ad (W p V m x) Z‖ ≤ Real.exp (2 * ∑ l ∈ range m, ε l) * ‖Z‖ ∧
        ‖Ad (W p V m x)⁻¹ Z‖ ≤ Real.exp (2 * ∑ l ∈ range m, ε l) * ‖Z‖ := by
  intro m
  induction m with
  | zero => intro _ x Z; simp [W]
  | succ m ih =>
    intro hm x Z
    have hml : m < n := hm
    have hi := ih hml.le
    have hfac := fun Z => near_iso (hε0 m) (hε m hml) (hV₀ m (p m (anc p m x)) (anc p m x))
      (hpert m hml (anc p m x)) Z
    have hexp : Real.exp (2 * ∑ l ∈ range (m + 1), ε l) =
        Real.exp (2 * ε m) * Real.exp (2 * ∑ l ∈ range m, ε l) := by
      rw [Finset.sum_range_succ, ← Real.exp_add]; ring_nf
    rw [hexp]
    simp only [W, anc]
    constructor
    · rw [Ad_mul]
      calc ‖Ad (V m (p m (anc p m x)) (anc p m x)) (Ad (W p V m x) Z)‖
          ≤ Real.exp (2 * ε m) * ‖Ad (W p V m x) Z‖ := (hfac _).1
        _ ≤ Real.exp (2 * ε m) * (Real.exp (2 * ∑ l ∈ range m, ε l) * ‖Z‖) := by
          gcongr; exact (hi x Z).1
        _ = _ := by ring
    · rw [mul_inv_rev, Ad_mul]
      calc ‖Ad (W p V m x)⁻¹ (Ad (V m (p m (anc p m x)) (anc p m x))⁻¹ Z)‖
          ≤ Real.exp (2 * ∑ l ∈ range m, ε l) * ‖Ad (V m (p m (anc p m x)) (anc p m x))⁻¹ Z‖ :=
            (hi x _).2
        _ ≤ Real.exp (2 * ∑ l ∈ range m, ε l) * (Real.exp (2 * ε m) * ‖Z‖) := by
          gcongr; exact (hfac Z).2
        _ = _ := by ring

/-- `Σ_{l<n} L^{-(n-l)} ≤ 1/2` for `L ≥ 3`. -/
lemma sum_inv_pow_le (L : ℝ) (hL : 3 ≤ L) (n : ℕ) : ∑ l ∈ range n, ((L ^ (n - l))⁻¹ : ℝ) ≤ 1 / 2 := by
  set r : ℝ := L⁻¹
  have hr0 : 0 < r := inv_pos.mpr (by linarith)
  have hr : r ≤ 1 / 3 := by
    simp only [r]; rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
  have e : ∑ l ∈ range n, ((L ^ (n - l))⁻¹ : ℝ) = ∑ j ∈ range n, r ^ (j + 1) := by
    rw [← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : j < n := Finset.mem_range.mp hj
    rw [show n - (n - 1 - j) = j + 1 by omega, inv_pow]
  rw [e]
  have hS : (∑ j ∈ range n, r ^ j) * (1 - r) = 1 - r ^ n := geom_sum_mul_neg r n
  have hS0 : 0 ≤ ∑ j ∈ range n, r ^ j := Finset.sum_nonneg fun j _ => pow_nonneg hr0.le j
  have e2 : ∑ j ∈ range n, r ^ (j + 1) = r * ∑ j ∈ range n, r ^ j := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
  rw [e2]
  have hrn : 0 ≤ r ^ n := pow_nonneg hr0.le n
  have hS1 : ∑ j ∈ range n, r ^ j ≤ 3 / 2 := by nlinarith
  nlinarith [mul_le_mul hr hS1 hS0 (by norm_num : (0 : ℝ) ≤ 1 / 3)]

/-- The constants: `Σ_{l<n} α₁^{(l)} ≤ C'₃α₁` for `α₁^{(l)} = 2C'₃α₁L^{-(n-l)}`, `L ≥ 3`. -/
theorem sum_alpha_le (L C₃ α₁ : ℝ) (hL : 3 ≤ L) (hC₃ : 0 ≤ C₃) (hα : 0 ≤ α₁) (n : ℕ) :
    ∑ l ∈ range n, 2 * C₃ * α₁ * (L ^ (n - l))⁻¹ ≤ C₃ * α₁ := by
  rw [← Finset.mul_sum]
  have := sum_inv_pow_le L hL n
  have h0 : 0 ≤ 2 * C₃ * α₁ := by positivity
  nlinarith

/-- `lem:block-average-transports`, abstract form. -/
theorem block_average_transports (n : ℕ) (L C₁ C₃ C_A c₄ α₁ : ℝ) (hL : 3 ≤ L) (hC₁ : 0 ≤ C₁)
    (hC₃ : 0 ≤ C₃) (hα : 0 ≤ α₁) (hαc : α₁ ≤ c₄) (hCA : 16 * L ^ 4 * C₁ * C₃ ≤ C_A)
    (hCAc : C_A * c₄ ≤ Real.log 2) (c : ℂ) (hc : c = (((L ^ 4 : ℝ)⁻¹ : ℝ) : ℂ))
    (V V₀ : ∀ l, X (l + 1) → X l → GLN) (hV₀ : ∀ l y x Z, ‖Ad (V₀ l y x) Z‖ = ‖Z‖)
    (hrel : ∀ l < n, ∀ (lam : X l → Mat) (M : ℝ), (∀ x, ‖lam x‖ ≤ M) →
      ∀ y, ‖blockAvg p c (V l) lam y - blockAvg p c (V₀ l) lam y‖ ≤
        C₁ * (2 * C₃ * α₁ * (L ^ (n - l))⁻¹) * M) :
    (∀ (lam : X 0 → Mat) (y : X n),
      Qn p c V n lam y = c ^ n • ∑ x ∈ univ.filter (fun x => anc p n x = y), Ad (W p V n x) (lam x)) ∧
    ∀ (x : X 0) (Z : Mat),
      ‖Ad (W p V n x) Z‖ ≤ 2 * ‖Z‖ ∧ ‖Ad (W p V n x)⁻¹ Z‖ ≤ 2 * ‖Z‖ ∧
      (0 < N → hs (Ad (W p V n x) Z) ≤ 2 * Real.sqrt N * hs Z ∧
        hs (Ad (W p V n x)⁻¹ Z) ≤ 2 * Real.sqrt N * hs Z) := by
  have hL0 : 0 < L := by linarith
  have hL4 : 0 < L ^ 4 := by positivity
  have hcn : ‖c‖ = (L ^ 4)⁻¹ := by
    rw [hc, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr hL4.le)]
  have hc0 : c ≠ 0 := by rw [← norm_ne_zero_iff, hcn]; positivity
  set ε : ℕ → ℝ := fun l => L ^ 4 * (C₁ * (2 * C₃ * α₁ * (L ^ (n - l))⁻¹))
  have hε0 : ∀ l, 0 ≤ ε l := fun l => by positivity
  have hpert : ∀ l < n, ∀ (x : X l) (Z : Mat),
      ‖Ad (V l (p l x) x) Z - Ad (V₀ l (p l x) x) Z‖ ≤ ε l * ‖Z‖ := fun l hl x Z => by
    have := pert_of_avg p c hc0 (V l) (V₀ l) _ (hrel l hl) x Z
    rw [hcn, inv_inv] at this
    simpa [ε, mul_assoc] using this
  -- the constants
  have hsum : ∑ l ∈ range n, ε l ≤ L ^ 4 * C₁ * (C₃ * α₁) := by
    have := sum_alpha_le L C₃ α₁ hL hC₃ hα n
    have e : ∑ l ∈ range n, ε l = L ^ 4 * C₁ * ∑ l ∈ range n, 2 * C₃ * α₁ * (L ^ (n - l))⁻¹ := by
      simp only [ε]; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun l _ => by ring
    rw [e]; exact mul_le_mul_of_nonneg_left this (by positivity)
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog1 : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9; linarith
  have hkey : 2 * (L ^ 4 * C₁ * (C₃ * α₁)) ≤ Real.log 2 / 8 := by
    have h1 : 16 * L ^ 4 * C₁ * C₃ * α₁ ≤ C_A * c₄ := by
      have hCA0 : 0 ≤ C_A := le_trans (by positivity) hCA
      exact mul_le_mul hCA hαc hα hCA0
    nlinarith
  have hεle : ∀ l < n, ε l ≤ 1 / 2 := fun l hl => by
    have hsingle : ε l ≤ ∑ l ∈ range n, ε l :=
      Finset.single_le_sum (fun i _ => hε0 i) (Finset.mem_range.mpr hl)
    linarith
  have hexp2 : Real.exp (2 * ∑ l ∈ range n, ε l) ≤ 2 := by
    calc Real.exp (2 * ∑ l ∈ range n, ε l) ≤ Real.exp (Real.log 2) := by
          apply Real.exp_le_exp.mpr; linarith
      _ = 2 := Real.exp_log (by norm_num)
  refine ⟨fun lam y => composite p c V n lam y, fun x Z => ?_⟩
  have hb := W_bound p V V₀ n ε hε0 hεle hV₀ hpert n le_rfl x Z
  have hZ := norm_nonneg Z
  have h1 : ‖Ad (W p V n x) Z‖ ≤ 2 * ‖Z‖ := hb.1.trans (by gcongr)
  have h2 : ‖Ad (W p V n x)⁻¹ Z‖ ≤ 2 * ‖Z‖ := hb.2.trans (by gcongr)
  refine ⟨h1, h2, fun hN => ⟨?_, ?_⟩⟩
  · calc hs (Ad (W p V n x) Z) ≤ ‖Ad (W p V n x) Z‖ := hs_le_opNorm hN _
      _ ≤ 2 * ‖Z‖ := h1
      _ ≤ 2 * (Real.sqrt N * hs Z) := by gcongr; exact opNorm_le_sqrt_mul_hs Z
      _ = 2 * Real.sqrt N * hs Z := by ring
  · calc hs (Ad (W p V n x)⁻¹ Z) ≤ ‖Ad (W p V n x)⁻¹ Z‖ := hs_le_opNorm hN _
      _ ≤ 2 * ‖Z‖ := h2
      _ ≤ 2 * (Real.sqrt N * hs Z) := by gcongr; exact opNorm_le_sqrt_mul_hs Z
      _ = 2 * Real.sqrt N * hs Z := by ring

end BlockAverageTransports
end CoreLean

end
