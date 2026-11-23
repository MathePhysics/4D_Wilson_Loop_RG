/-
`lem:walk-expansion-product` of BALABAN_CORE.tex, in abstract form: products and series of families of
walk terms.

Setting. The points of `𝐁` with their scales, spacings, and distance are the `Setting` of
`lem:composition` (`Composition.lean`); `eq:summation` at the rate `δ/4` enters as a hypothesis (it is
`lem:summation` with `α = ¼` for (i), with `α = ½` and the rate `½δ` for (ii)). Walks are the elements of a
type `Ω`; a walk has the points of `𝐁` in the enlarged cube of its first cube (`first`) and of its last
cube (`last`), its distance `d_ω ≥ d`, and the composition of walks satisfies `first(ωω') = first ω`,
`last(ωω') = last ω'`, and `d_{ωω'}(y, y') ≤ d_ω(y, y'') + d_{ω'}(y'', y')` for every point `y''` (a path
through the enlarged cubes of `ω` followed by one through those of `ω'` passes through those of `ωω'` in
their order). Objects are elements of types with block norms `[·]_y ≥ 0`.

Modelling. (W1) is used through its two inequalities (`Bound`, with an additional decay `e^{-κd}` used in
the induction for (ii)); (W3) is stated for sums in `ℝ≥0∞` over the indices whose walk begins with a given
key (a cube with a radius), the linked indices of an index having their keys in a set of at most `N''`
keys. The holomorphy and the covariance of (W2), and the locality of the terms in `f`, are not modelled.
For (ii), the invertibility of `I - 𝓡` is proved in every Hausdorff topological ring in which the
geometric series of `𝓡` converges.
-/
import CoreLean.Composition

open Finset
open scoped ENNReal

noncomputable section

namespace CoreLean

namespace WalkProduct

open Composition

/-- Abstract walks over the points `β` of `𝐁`. -/
structure Walks (β Ω : Type*) where
  first : Ω → Finset β
  last : Ω → Finset β
  dw : Ω → β → β → ℝ
  comp : Ω → Ω → Ω
  first_comp : ∀ ω ω', first (comp ω ω') = first ω
  last_comp : ∀ ω ω', last (comp ω ω') = last ω'
  dw_comp : ∀ ω ω' y y'' y', dw (comp ω ω') y y' ≤ dw ω y y'' + dw ω' y'' y'

variable {β Ω : Type*} [Fintype β] [DecidableEq β] (B : Setting β) (W : Walks β Ω)

/-- The inequalities of (W1) for an operator `K` with the walk `ω`, the number `b`, the exponent `p`, and
the rate `δ`, with an additional decay `e^{-κd(y, y')}` (`κ = 0` is (W1)). -/
def Bound {V V' : Type*} (nrm : V → β → ℝ) (nrm' : V' → β → ℝ) (K : V → V') (ω : Ω) (b : ℝ)
    (p : ℤ) (δ κ : ℝ) : Prop :=
  ∀ f, (∀ y ∉ W.first ω, nrm' (K f) y = 0) ∧
    ∀ y ∈ W.first ω, nrm' (K f) y ≤ b * B.a (B.j y) ^ p *
      ∑ y' ∈ W.last ω, Real.exp (-(δ * W.dw ω y y' + κ * B.d y y')) * nrm f y'

variable {B W}

/-- The bound of (W1) holds at every point, the right side being nonnegative. -/
lemma Bound.le {V V' : Type*} {nrm : V → β → ℝ} {nrm' : V' → β → ℝ} (hn : ∀ f y, 0 ≤ nrm f y)
    {K : V → V'} {ω : Ω} {b : ℝ} {p : ℤ} {δ κ : ℝ} (hb : 0 ≤ b) (hK : Bound B W nrm nrm' K ω b p δ κ)
    (f : V) (y : β) :
    nrm' (K f) y ≤ b * B.a (B.j y) ^ p *
      ∑ y' ∈ W.last ω, Real.exp (-(δ * W.dw ω y y' + κ * B.d y y')) * nrm f y' := by
  by_cases h : y ∈ W.first ω
  · exact (hK f).2 y h
  · rw [(hK f).1 y h]
    exact mul_nonneg (mul_nonneg hb (zpow_pos (B.a_pos _) _).le)
      (Finset.sum_nonneg fun y' _ => mul_nonneg (Real.exp_pos _).le (hn f y'))

/-- A larger additional decay gives a weaker bound. -/
lemma Bound.mono_kappa {V V' : Type*} {nrm : V → β → ℝ} {nrm' : V' → β → ℝ}
    (hn : ∀ f y, 0 ≤ nrm f y) {K : V → V'} {ω : Ω} {b : ℝ} {p : ℤ} {δ κ κ' : ℝ} (hb : 0 ≤ b)
    (hκ : κ' ≤ κ) (hK : Bound B W nrm nrm' K ω b p δ κ) : Bound B W nrm nrm' K ω b p δ κ' := by
  intro f
  refine ⟨(hK f).1, fun y hy => ((hK f).2 y hy).trans ?_⟩
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun y' _ => ?_)
    (mul_nonneg hb (zpow_pos (B.a_pos _) _).le)
  refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (hn f y')
  have := mul_le_mul_of_nonneg_right hκ (B.d_nonneg y y')
  linarith

/-! ### (i): products -/

/-- (i), the pairs which are not linked: if the points of `𝐁` of the last enlarged cube of `ω` and of the
first enlarged cube of `ω'` are disjoint, all block norms of `K_ιK'_{ι'}f` vanish. -/
theorem product_unlinked {V₁ V₂ V₃ : Type*} {n₁ : V₁ → β → ℝ} {n₂ : V₂ → β → ℝ} {n₃ : V₃ → β → ℝ}
    (hn₁ : ∀ g y, 0 ≤ n₁ g y) {K : V₂ → V₁} {K' : V₃ → V₂} {ω ω' : Ω} {b b' : ℝ} {p p' : ℤ}
    {δ : ℝ} (hK : Bound B W n₂ n₁ K ω b p δ 0) (hK' : Bound B W n₃ n₂ K' ω' b' p' δ 0)
    (hlink : Disjoint (W.last ω) (W.first ω')) (f : V₃) (y : β) : n₁ (K (K' f)) y = 0 := by
  by_cases hy : y ∈ W.first ω
  · refine le_antisymm (((hK (K' f)).2 y hy).trans (le_of_eq ?_)) (hn₁ _ _)
    rw [Finset.sum_eq_zero fun y'' hy'' => by
      rw [(hK' f).1 y'' (Finset.disjoint_left.mp hlink hy''), mul_zero], mul_zero]
  · exact (hK (K' f)).1 y hy

/-- (i), (W1) for the products: with `4|p'| log L ≤ δRM` (the core's `27δM ≥ 4|p'| log L`) and
`eq:summation` at the rate `δ/4` with the constant `c₁`, the product `K_ιK'_{ι'}` has the walk `ωω'`, the
number `c₁L^{|p'|}b_ιb_{ι'}`, the exponent `p + p'`, and the rate `δ/2`. -/
theorem product_bound {V₁ V₂ V₃ : Type*} {n₁ : V₁ → β → ℝ} {n₂ : V₂ → β → ℝ} {n₃ : V₃ → β → ℝ}
    (hn₂ : ∀ g y, 0 ≤ n₂ g y) (hn₃ : ∀ f y, 0 ≤ n₃ f y) (hd : ∀ ω y y', B.d y y' ≤ W.dw ω y y')
    {δ c₁ : ℝ} (hδ : 0 < δ) (hsum : ∀ y, ∑ y'', Real.exp (-(δ / 4 * B.d y y'')) ≤ c₁)
    {K : V₂ → V₁} {K' : V₃ → V₂} {ω ω' : Ω} {b b' : ℝ} {p p' : ℤ} (hb : 0 ≤ b) (hb' : 0 ≤ b')
    (hp' : 4 * |(p' : ℝ)| * Real.log B.L ≤ δ * B.RM)
    (hK : Bound B W n₂ n₁ K ω b p δ 0) (hK' : Bound B W n₃ n₂ K' ω' b' p' δ 0) :
    Bound B W n₃ n₁ (K ∘ K') (W.comp ω ω') (c₁ * B.L ^ |(p' : ℝ)| * b * b') (p + p') (δ / 2) 0 := by
  intro f
  refine ⟨fun y hy => (hK (K' f)).1 y (by rwa [W.first_comp] at hy), fun y hy => ?_⟩
  rw [W.first_comp] at hy
  rw [W.last_comp]
  simp only [Function.comp, zero_mul, add_zero]
  set S := |(p' : ℝ)|
  set T := ∑ y' ∈ W.last ω', Real.exp (-(δ / 2 * W.dw (W.comp ω ω') y y')) * n₃ f y'
  have hT : 0 ≤ T := Finset.sum_nonneg fun y' _ => mul_nonneg (Real.exp_pos _).le (hn₃ f y')
  have hL0 : 0 < B.L := lt_of_lt_of_le zero_lt_one B.one_le_L
  have hay := B.a_pos (B.j y)
  -- the quotient of the spacings (`lem:distance`(ii))
  have hzp : ∀ y'', B.a (B.j y'') ^ p' ≤
      B.L ^ S * Real.exp (δ / 4 * B.d y y'') * B.a (B.j y) ^ p' := by
    intro y''
    have h := B.zpow_a_le (α := 1 / 2) (δ := δ) (S := S) (abs_nonneg _) (by linarith) y y''
      (s := p') le_rfl
    rwa [show 1 / 2 * δ / 2 = δ / 4 by ring] at h
  -- the bound of `K'f` at every point
  have h2 : ∀ y'', n₂ (K' f) y'' ≤ b' * B.a (B.j y'') ^ p' *
      ∑ y' ∈ W.last ω', Real.exp (-(δ * W.dw ω' y'' y')) * n₃ f y' := by
    intro y''
    have := Bound.le hn₃ hb' hK' f y''
    simpa only [zero_mul, add_zero] using this
  -- the exponents
  have hexp : ∀ y'' y', Real.exp (-(δ * W.dw ω y y'')) * Real.exp (δ / 4 * B.d y y'') *
      Real.exp (-(δ * W.dw ω' y'' y')) ≤
        Real.exp (-(δ / 4 * B.d y y'')) * Real.exp (-(δ / 2 * W.dw (W.comp ω ω') y y')) := by
    intro y'' y'
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have h1 := mul_le_mul_of_nonneg_left (W.dw_comp ω ω' y y'' y') hδ.le
    have h3 := mul_le_mul_of_nonneg_left (hd ω y y'') hδ.le
    have h4 := mul_nonneg hδ.le ((B.d_nonneg y'' y').trans (hd ω' y'' y'))
    linarith
  -- the term of a point `y''`
  have hy'' : ∀ y'', Real.exp (-(δ * W.dw ω y y'')) * n₂ (K' f) y'' ≤
      b' * B.L ^ S * B.a (B.j y) ^ p' * T * Real.exp (-(δ / 4 * B.d y y'')) := by
    intro y''
    have hE := (Real.exp_pos (-(δ * W.dw ω y y''))).le
    calc Real.exp (-(δ * W.dw ω y y'')) * n₂ (K' f) y''
        ≤ Real.exp (-(δ * W.dw ω y y'')) * (b' * B.a (B.j y'') ^ p' *
            ∑ y' ∈ W.last ω', Real.exp (-(δ * W.dw ω' y'' y')) * n₃ f y') :=
          mul_le_mul_of_nonneg_left (h2 y'') hE
      _ = b' * ∑ y' ∈ W.last ω', (Real.exp (-(δ * W.dw ω y y'')) * B.a (B.j y'') ^ p' *
            Real.exp (-(δ * W.dw ω' y'' y'))) * n₃ f y' := by
          rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl fun y' _ => by ring
      _ ≤ b' * ∑ y' ∈ W.last ω', (B.L ^ S * B.a (B.j y) ^ p' *
            (Real.exp (-(δ / 4 * B.d y y'')) * Real.exp (-(δ / 2 * W.dw (W.comp ω ω') y y')))) *
              n₃ f y' := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun y' _ =>
            mul_le_mul_of_nonneg_right ?_ (hn₃ f y')) hb'
          calc Real.exp (-(δ * W.dw ω y y'')) * B.a (B.j y'') ^ p' *
                Real.exp (-(δ * W.dw ω' y'' y'))
              ≤ Real.exp (-(δ * W.dw ω y y'')) *
                  (B.L ^ S * Real.exp (δ / 4 * B.d y y'') * B.a (B.j y) ^ p') *
                    Real.exp (-(δ * W.dw ω' y'' y')) := by
                gcongr
                exact hzp y''
            _ = B.L ^ S * B.a (B.j y) ^ p' * (Real.exp (-(δ * W.dw ω y y'')) *
                  Real.exp (δ / 4 * B.d y y'') * Real.exp (-(δ * W.dw ω' y'' y'))) := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_left (hexp y'' y')
                  (mul_nonneg (Real.rpow_nonneg hL0.le _) (zpow_pos hay _).le)
      _ = b' * B.L ^ S * B.a (B.j y) ^ p' * T * Real.exp (-(δ / 4 * B.d y y'')) := by
          simp only [T, Finset.mul_sum, Finset.sum_mul]
          exact Finset.sum_congr rfl fun y' _ => by ring
  have hC : 0 ≤ b' * B.L ^ S * B.a (B.j y) ^ p' * T :=
    mul_nonneg (mul_nonneg (mul_nonneg hb' (Real.rpow_nonneg hL0.le _)) (zpow_pos hay _).le) hT
  calc n₁ (K (K' f)) y
      ≤ b * B.a (B.j y) ^ p * ∑ y'' ∈ W.last ω, Real.exp (-(δ * W.dw ω y y'')) * n₂ (K' f) y'' :=
        by simpa only [zero_mul, add_zero] using (hK (K' f)).2 y hy
    _ ≤ b * B.a (B.j y) ^ p * ∑ y'' ∈ W.last ω,
          b' * B.L ^ S * B.a (B.j y) ^ p' * T * Real.exp (-(δ / 4 * B.d y y'')) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun y'' _ => hy'' y'')
          (mul_nonneg hb (zpow_pos hay _).le)
    _ = b * B.a (B.j y) ^ p * (b' * B.L ^ S * B.a (B.j y) ^ p' * T *
          ∑ y'' ∈ W.last ω, Real.exp (-(δ / 4 * B.d y y''))) := by
        simp only [Finset.mul_sum]
    _ ≤ b * B.a (B.j y) ^ p * (b' * B.L ^ S * B.a (B.j y) ^ p' * T * c₁) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hC)
          (mul_nonneg hb (zpow_pos hay _).le)
        exact (Finset.sum_le_univ_sum_of_nonneg fun y'' => (Real.exp_pos _).le).trans (hsum y)
    _ = c₁ * B.L ^ S * b * b' * B.a (B.j y) ^ (p + p') * T := by
        rw [zpow_add₀ hay.ne']; ring

/-! ### (ii): series -/

/-- (ii), one more factor: if `P` has the bound `(c, 0, δ/2)` with the additional decay `e^{-δd/4}` and
`𝓡` has the bound `(b, 0, δ)`, then `P𝓡` has the bound `(c'cb, 0, δ/2)` with the same additional decay,
where `c'` is the constant of `eq:summation` at the rate `δ/4`; `d` is symmetric with the triangle
inequality (`lem:distance`(i)). -/
theorem series_step {V : Type*} {nrm : V → β → ℝ} (hn : ∀ f y, 0 ≤ nrm f y)
    (hd : ∀ ω y y', B.d y y' ≤ W.dw ω y y') (hsymm : ∀ y y', B.d y y' = B.d y' y)
    (htri : ∀ y y' y'', B.d y y'' ≤ B.d y y' + B.d y' y'')
    {δ c' : ℝ} (hδ : 0 < δ) (hsum : ∀ y, ∑ y'', Real.exp (-(δ / 4 * B.d y y'')) ≤ c')
    {P R : V → V} {Ω₀ ω : Ω} {c b : ℝ} (hc : 0 ≤ c) (hb : 0 ≤ b)
    (hP : Bound B W nrm nrm P Ω₀ c 0 (δ / 2) (δ / 4)) (hR : Bound B W nrm nrm R ω b 0 δ 0) :
    Bound B W nrm nrm (P ∘ R) (W.comp Ω₀ ω) (c' * c * b) 0 (δ / 2) (δ / 4) := by
  intro f
  refine ⟨fun y hy => (hP (R f)).1 y (by rwa [W.first_comp] at hy), fun y hy => ?_⟩
  rw [W.first_comp] at hy
  rw [W.last_comp]
  simp only [Function.comp, zpow_zero, mul_one]
  set Z : β → ℝ := fun y' => Real.exp (-(δ / 2 * W.dw (W.comp Ω₀ ω) y y' + δ / 4 * B.d y y')) *
    nrm f y'
  have hZ : ∀ y', 0 ≤ Z y' := fun y' => mul_nonneg (Real.exp_pos _).le (hn f y')
  have hR' : ∀ y'', nrm (R f) y'' ≤ b * ∑ y' ∈ W.last ω, Real.exp (-(δ * W.dw ω y'' y')) * nrm f y' := by
    intro y''
    have := Bound.le hn hb hR f y''
    simpa only [zpow_zero, mul_one, zero_mul, add_zero] using this
  have hexp : ∀ y'' y', Real.exp (-(δ / 2 * W.dw Ω₀ y y'' + δ / 4 * B.d y y'')) *
      Real.exp (-(δ * W.dw ω y'' y')) ≤
        Real.exp (-(δ / 4 * B.d y'' y')) *
          Real.exp (-(δ / 2 * W.dw (W.comp Ω₀ ω) y y' + δ / 4 * B.d y y')) := by
    intro y'' y'
    rw [← Real.exp_add, ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have h1 := mul_le_mul_of_nonneg_left (W.dw_comp Ω₀ ω y y'' y') hδ.le
    have h2 := mul_le_mul_of_nonneg_left (hd ω y'' y') hδ.le
    have h3 := mul_le_mul_of_nonneg_left (htri y y'' y') hδ.le
    linarith
  have hc' : ∀ y', ∑ y'' ∈ W.last Ω₀, Real.exp (-(δ / 4 * B.d y'' y')) ≤ c' := fun y' =>
    (Finset.sum_le_univ_sum_of_nonneg fun y'' => (Real.exp_pos _).le).trans
      (by simpa only [hsymm _ y'] using hsum y')
  calc nrm (P (R f)) y
      ≤ c * ∑ y'' ∈ W.last Ω₀, Real.exp (-(δ / 2 * W.dw Ω₀ y y'' + δ / 4 * B.d y y'')) *
          nrm (R f) y'' := by simpa only [zpow_zero, mul_one] using (hP (R f)).2 y hy
    _ ≤ c * ∑ y'' ∈ W.last Ω₀, Real.exp (-(δ / 2 * W.dw Ω₀ y y'' + δ / 4 * B.d y y'')) *
          (b * ∑ y' ∈ W.last ω, Real.exp (-(δ * W.dw ω y'' y')) * nrm f y') :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun y'' _ =>
          mul_le_mul_of_nonneg_left (hR' y'') (Real.exp_pos _).le) hc
    _ = c * b * ∑ y'' ∈ W.last Ω₀, ∑ y' ∈ W.last ω,
          (Real.exp (-(δ / 2 * W.dw Ω₀ y y'' + δ / 4 * B.d y y'')) *
            Real.exp (-(δ * W.dw ω y'' y'))) * nrm f y' := by
        simp only [Finset.mul_sum]
        exact Finset.sum_congr rfl fun y'' _ => Finset.sum_congr rfl fun y' _ => by ring
    _ ≤ c * b * ∑ y'' ∈ W.last Ω₀, ∑ y' ∈ W.last ω,
          Real.exp (-(δ / 4 * B.d y'' y')) * Z y' := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun y'' _ =>
          Finset.sum_le_sum fun y' _ => ?_) (mul_nonneg hc hb)
        simp only [Z]
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right (hexp y'' y') (hn f y')
    _ = c * b * ∑ y' ∈ W.last ω, (∑ y'' ∈ W.last Ω₀, Real.exp (-(δ / 4 * B.d y'' y'))) * Z y' := by
        rw [Finset.sum_comm]
        simp only [Finset.sum_mul]
    _ ≤ c * b * ∑ y' ∈ W.last ω, c' * Z y' :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun y' _ =>
          mul_le_mul_of_nonneg_right (hc' y') (hZ y')) (mul_nonneg hc hb)
    _ = c' * c * b * ∑ y' ∈ W.last ω, Z y' := by rw [← Finset.mul_sum]; ring

/-- The first factor: the bound `(b, 0, δ)` gives `(b, 0, δ/2)` with the additional decay `e^{-δd/4}`,
since `d ≤ d_ω`. -/
theorem series_first {V : Type*} {nrm : V → β → ℝ} (hn : ∀ f y, 0 ≤ nrm f y)
    (hd : ∀ ω y y', B.d y y' ≤ W.dw ω y y') {δ : ℝ} (hδ : 0 < δ) {R : V → V} {ω : Ω} {b : ℝ}
    (hb : 0 ≤ b) (hR : Bound B W nrm nrm R ω b 0 δ 0) : Bound B W nrm nrm R ω b 0 (δ / 2) (δ / 4) := by
  intro f
  refine ⟨(hR f).1, fun y hy => ((hR f).2 y hy).trans ?_⟩
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun y' _ => ?_)
    (mul_nonneg hb (zpow_pos (B.a_pos _) _).le)
  refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (hn f y')
  have := mul_le_mul_of_nonneg_left (hd ω y y') hδ.le
  have h2 := mul_nonneg hδ.le ((B.d_nonneg y y').trans (hd ω y y'))
  linarith

/-- The operator, the walk, and the number of a sequence `ι₁, ι₂, …, ι_n` of indices (the factor `𝓡_{ι₁}`
on the left), given by its first index and the list of the others. -/
def chainOp {I V : Type*} (R : I → V → V) (ι₁ : I) (l : List I) : V → V :=
  l.foldl (fun P ι => P ∘ R ι) (R ι₁)

def chainWalk {I : Type*} (ωI : I → Ω) (ι₁ : I) (l : List I) : Ω :=
  l.foldl (fun Ω₀ ι => W.comp Ω₀ (ωI ι)) (ωI ι₁)

lemma chain_foldl {I V : Type*} {nrm : V → β → ℝ} (hn : ∀ f y, 0 ≤ nrm f y)
    (hd : ∀ ω y y', B.d y y' ≤ W.dw ω y y') (hsymm : ∀ y y', B.d y y' = B.d y' y)
    (htri : ∀ y y' y'', B.d y y'' ≤ B.d y y' + B.d y' y'')
    {δ c' : ℝ} (hδ : 0 < δ) (hc'0 : 0 ≤ c') (hsum : ∀ y, ∑ y'', Real.exp (-(δ / 4 * B.d y y'')) ≤ c')
    (R : I → V → V) (ωI : I → Ω) (b : I → ℝ) (hb : ∀ ι, 0 ≤ b ι)
    (hR : ∀ ι, Bound B W nrm nrm (R ι) (ωI ι) (b ι) 0 δ 0) (l : List I) :
    ∀ (P : V → V) (Ω₀ : Ω) (c : ℝ), 0 ≤ c → Bound B W nrm nrm P Ω₀ c 0 (δ / 2) (δ / 4) →
      Bound B W nrm nrm (l.foldl (fun P ι => P ∘ R ι) P)
        (l.foldl (fun Ω₀ ι => W.comp Ω₀ (ωI ι)) Ω₀)
        (c' ^ l.length * c * (l.map b).prod) 0 (δ / 2) (δ / 4) := by
  induction l with
  | nil => intro P Ω₀ c _ hP; simpa using hP
  | cons ι l ih =>
    intro P Ω₀ c hc hP
    have hstep := series_step hn hd hsymm htri hδ hsum hc (hb ι) hP (hR ι)
    have := ih (P ∘ R ι) (W.comp Ω₀ (ωI ι)) (c' * c * b ι)
      (mul_nonneg (mul_nonneg hc'0 hc) (hb ι)) hstep
    simp only [List.foldl_cons, List.length_cons, List.map_cons, List.prod_cons]
    have e : c' ^ (l.length + 1) * c * (b ι * (l.map b).prod) =
        c' ^ l.length * (c' * c * b ι) * (l.map b).prod := by ring
    rw [e]
    exact this

/-- (ii), (W1) for the products of `n = l.length + 1` factors: the number `c'^{n-1}b_{ι₁}⋯b_{ι_n}`, the
exponent `0`, and the rate `δ/2`. -/
theorem series_bound {I V : Type*} {nrm : V → β → ℝ} (hn : ∀ f y, 0 ≤ nrm f y)
    (hd : ∀ ω y y', B.d y y' ≤ W.dw ω y y') (hsymm : ∀ y y', B.d y y' = B.d y' y)
    (htri : ∀ y y' y'', B.d y y'' ≤ B.d y y' + B.d y' y'')
    {δ c' : ℝ} (hδ : 0 < δ) (hc'0 : 0 ≤ c') (hsum : ∀ y, ∑ y'', Real.exp (-(δ / 4 * B.d y y'')) ≤ c')
    (R : I → V → V) (ωI : I → Ω) (b : I → ℝ) (hb : ∀ ι, 0 ≤ b ι)
    (hR : ∀ ι, Bound B W nrm nrm (R ι) (ωI ι) (b ι) 0 δ 0) (ι₁ : I) (l : List I) :
    Bound B W nrm nrm (chainOp R ι₁ l) (chainWalk (W := W) ωI ι₁ l)
      (c' ^ l.length * b ι₁ * (l.map b).prod) 0 (δ / 2) 0 := by
  have h := chain_foldl hn hd hsymm htri hδ hc'0 hsum R ωI b hb hR l (R ι₁) (ωI ι₁) (b ι₁) (hb ι₁)
    (series_first hn hd hδ (hb ι₁) (hR ι₁))
  refine Bound.mono_kappa hn ?_ (by linarith) h
  exact mul_nonneg (mul_nonneg (pow_nonneg hc'0 _) (hb ι₁))
    (List.prod_nonneg fun x hx => by
      obtain ⟨ι, -, rfl⟩ := List.mem_map.mp hx
      exact hb ι)

/-! ### `lem:one-cube`: terms of one cube -/

/-- Spacings of neighbouring scales: if `|j - j(y)| ≤ 1`, then `a_j^p ≤ L^{|p|}a_{j(y)}^p`. -/
lemma zpow_a_near {j j' : ℕ} (h1 : (j : ℤ) ≤ j' + 1) (h2 : (j' : ℤ) ≤ j + 1) (p : ℤ) :
    B.a j ^ p ≤ B.L ^ |p| * B.a j' ^ p := by
  have hL0 : 0 < B.L := lt_of_lt_of_le zero_lt_one B.one_le_L
  set m : ℤ := (j : ℤ) - j'
  have ha : B.a j = B.a j' * B.L ^ m := by
    simp only [Setting.a, m]
    rw [mul_assoc, ← zpow_natCast, ← zpow_natCast, ← zpow_add₀ hL0.ne']
    congr 2; ring
  have hm : |m| ≤ 1 := abs_le.mpr ⟨by simp only [m]; omega, by simp only [m]; omega⟩
  have hmp : m * p ≤ |p| :=
    calc m * p ≤ |m * p| := le_abs_self _
      _ = |m| * |p| := abs_mul _ _
      _ ≤ 1 * |p| := mul_le_mul_of_nonneg_right hm (abs_nonneg _)
      _ = |p| := one_mul _
  rw [ha, mul_zpow, ← zpow_mul, mul_comm (B.L ^ |p|)]
  exact mul_le_mul_of_nonneg_left (zpow_le_zpow_right₀ B.one_le_L hmp)
    (zpow_pos (B.a_pos _) _).le

/-- `lem:one-cube`: a map `𝒯_□` whose block norms vanish outside the points `S = 𝐁 ∩ □`, with
`[𝒯_□f]_y ≤ ba_j^p sup_{y' ∈ S}[f]_{y'}` for `y ∈ S` (stated for every upper bound of the block norms on `S`),
where the points of `S` have the scales `j - 1`, `j`, `j + 1` and the distance of the walk `(□)` is at most
`D` on `S`, satisfies (W1) with the walk `(□)`, the number `L^{|p|}e^{δD}b`, the exponent `p`, and the
rate `δ` (the core: `δ = ¼δ₀`, `D = 8LM_w`, or `D = 8L²` when the supremum runs over `|y - y'|_∞ ≤ 2La_j`). -/
theorem one_cube {V V' : Type*} {nrm : V → β → ℝ} {nrm' : V' → β → ℝ} (hn : ∀ f y, 0 ≤ nrm f y)
    {T : V → V'} {ω : Ω} {S : Finset β} (hSf : S ⊆ W.first ω) (hSl : S ⊆ W.last ω) {j : ℕ}
    (hj : ∀ y ∈ S, (j : ℤ) ≤ B.j y + 1 ∧ (B.j y : ℤ) ≤ j + 1) {D : ℝ}
    (hD : ∀ y ∈ S, ∀ y' ∈ S, W.dw ω y y' ≤ D) {b : ℝ} (hb : 0 ≤ b) {p : ℤ} {δ : ℝ} (hδ : 0 ≤ δ)
    (hT0 : ∀ f, ∀ y ∉ S, nrm' (T f) y = 0)
    (hT : ∀ f, ∀ y ∈ S, ∀ M : ℝ, (∀ y' ∈ S, nrm f y' ≤ M) → nrm' (T f) y ≤ b * B.a j ^ p * M) :
    Bound B W nrm nrm' T ω (B.L ^ |p| * Real.exp (δ * D) * b) p δ 0 := by
  intro f
  refine ⟨fun y hy => hT0 f y fun h => hy (hSf h), fun y _ => ?_⟩
  by_cases hyS : y ∈ S
  · have hL0 : 0 < B.L := lt_of_lt_of_le zero_lt_one B.one_le_L
    have hsum := hT f y hyS (∑ y' ∈ S, nrm f y') fun y' hy' =>
      Finset.single_le_sum (fun z _ => hn f z) hy'
    have hzp := zpow_a_near (B := B) (hj y hyS).1 (hj y hyS).2 p
    simp only [zero_mul, add_zero]
    calc nrm' (T f) y ≤ b * B.a j ^ p * ∑ y' ∈ S, nrm f y' := hsum
      _ ≤ b * (B.L ^ |p| * B.a (B.j y) ^ p) * ∑ y' ∈ S, nrm f y' :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hzp hb)
            (Finset.sum_nonneg fun y' _ => hn f y')
      _ = B.L ^ |p| * b * B.a (B.j y) ^ p *
            ∑ y' ∈ S, Real.exp (δ * D) * (Real.exp (-(δ * D)) * nrm f y') := by
          congr 1
          · ring
          · refine Finset.sum_congr rfl fun y' _ => ?_
            rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
      _ ≤ B.L ^ |p| * b * B.a (B.j y) ^ p *
            ∑ y' ∈ S, Real.exp (δ * D) * (Real.exp (-(δ * W.dw ω y y')) * nrm f y') := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun y' hy' => ?_)
            (mul_nonneg (mul_nonneg (zpow_pos hL0 _).le hb) (zpow_pos (B.a_pos _) _).le)
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ?_ (hn f y'))
            (Real.exp_pos _).le
          exact Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_left (hD y hyS y' hy') hδ))
      _ ≤ B.L ^ |p| * b * B.a (B.j y) ^ p *
            ∑ y' ∈ W.last ω, Real.exp (δ * D) * (Real.exp (-(δ * W.dw ω y y')) * nrm f y') := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg hSl
            fun y' _ _ => mul_nonneg (Real.exp_pos _).le
              (mul_nonneg (Real.exp_pos _).le (hn f y')))
            (mul_nonneg (mul_nonneg (zpow_pos hL0 _).le hb) (zpow_pos (B.a_pos _) _).le)
      _ = B.L ^ |p| * Real.exp (δ * D) * b * B.a (B.j y) ^ p *
            ∑ y' ∈ W.last ω, Real.exp (-(δ * W.dw ω y y')) * nrm f y' := by
          rw [← Finset.mul_sum]; ring
  · rw [hT0 f y hyS]
    have hL0 : 0 < B.L := lt_of_lt_of_le zero_lt_one B.one_le_L
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (zpow_pos hL0 _).le (Real.exp_pos _).le)
      hb) (zpow_pos (B.a_pos _) _).le)
      (Finset.sum_nonneg fun y' _ => mul_nonneg (Real.exp_pos _).le (hn f y'))

/-! ### (W3): the majorants -/

/-- The sum of the numbers of the indices linked to a fixed index: their keys lie in a set of at most `N`
keys, and the sum over the indices with a given key is at most `B'`. -/
theorem linked_sum {I I' κ : Type*} (b' : I' → ℝ≥0∞) (st' : I' → κ) (link : I → I' → Prop)
    [∀ ι ι', Decidable (link ι ι')] [DecidableEq κ] (S : I → Finset κ) {N : ℕ}
    (hS : ∀ ι ι', link ι ι' → st' ι' ∈ S ι) (hN : ∀ ι, (S ι).card ≤ N) {B' : ℝ≥0∞}
    (hB' : ∀ c, ∑' ι', (if st' ι' = c then b' ι' else 0) ≤ B') (ι : I) :
    ∑' ι', (if link ι ι' then b' ι' else 0) ≤ N * B' := by
  calc ∑' ι', (if link ι ι' then b' ι' else 0)
      ≤ ∑' ι', ∑ c ∈ S ι, (if st' ι' = c then b' ι' else 0) := by
        refine ENNReal.tsum_le_tsum fun ι' => ?_
        split_ifs with h
        · calc b' ι' = (if st' ι' = st' ι' then b' ι' else 0) := by simp
            _ ≤ ∑ c ∈ S ι, (if st' ι' = c then b' ι' else 0) :=
                Finset.single_le_sum (f := fun c => if st' ι' = c then b' ι' else 0)
                  (fun _ _ => zero_le) (hS ι ι' h)
        · exact zero_le
    _ = ∑ c ∈ S ι, ∑' ι', (if st' ι' = c then b' ι' else 0) :=
        Summable.tsum_finsetSum fun _ _ => ENNReal.summable
    _ ≤ ∑ _c ∈ S ι, B' := Finset.sum_le_sum fun c _ => hB' c
    _ = (S ι).card * B' := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ N * B' := by gcongr; exact_mod_cast hN ι

/-- (i), (W3) for the products: the sum of the numbers `Cb_ιb_{ι'}` of the linked pairs whose first walk
begins with the key `c` is at most `CN''BB'`. -/
theorem product_majorant {I I' κ : Type*} (b : I → ℝ≥0∞) (b' : I' → ℝ≥0∞) (st : I → κ)
    (st' : I' → κ) (link : I → I' → Prop) [∀ ι ι', Decidable (link ι ι')] [DecidableEq κ]
    (S : I → Finset κ) {N : ℕ} (hS : ∀ ι ι', link ι ι' → st' ι' ∈ S ι) (hN : ∀ ι, (S ι).card ≤ N)
    {B₁ B' : ℝ≥0∞} (hB : ∀ c, ∑' ι, (if st ι = c then b ι else 0) ≤ B₁)
    (hB' : ∀ c, ∑' ι', (if st' ι' = c then b' ι' else 0) ≤ B') (C : ℝ≥0∞) (c : κ) :
    ∑' ι, (if st ι = c then ∑' ι', (if link ι ι' then C * b ι * b' ι' else 0) else 0) ≤
      C * N * B₁ * B' := by
  calc ∑' ι, (if st ι = c then ∑' ι', (if link ι ι' then C * b ι * b' ι' else 0) else 0)
      = ∑' ι, C * ((if st ι = c then b ι else 0) * ∑' ι', (if link ι ι' then b' ι' else 0)) := by
        refine tsum_congr fun ι => ?_
        split_ifs with h
        · rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]
          refine tsum_congr fun ι' => ?_
          split_ifs <;> ring
        · simp
    _ ≤ ∑' ι, C * ((if st ι = c then b ι else 0) * (N * B')) := by
        refine ENNReal.tsum_le_tsum fun ι => ?_
        gcongr
        exact linked_sum b' st' link S hS hN hB' ι
    _ = C * (N * B') * ∑' ι, (if st ι = c then b ι else 0) := by
        rw [← ENNReal.tsum_mul_left]
        exact tsum_congr fun ι => by ring
    _ ≤ C * (N * B') * B₁ := by gcongr; exact hB c
    _ = C * N * B₁ * B' := by ring

/-- The sum `F_n(ι₁)` of the products `b_{ι₁}⋯b_{ι_{n+1}}` over the sequences beginning with `ι₁` in which
consecutive indices are linked. -/
def chainSum {I : Type*} (b : I → ℝ≥0∞) (link : I → I → Prop) [∀ ι ι', Decidable (link ι ι')] :
    ℕ → I → ℝ≥0∞
  | 0, ι => b ι
  | n + 1, ι => b ι * ∑' ι', if link ι ι' then chainSum b link n ι' else 0

theorem chainSum_le {I κ : Type*} (b : I → ℝ≥0∞) (st : I → κ) (link : I → I → Prop)
    [∀ ι ι', Decidable (link ι ι')] [DecidableEq κ] (S : I → Finset κ) {N : ℕ}
    (hS : ∀ ι ι', link ι ι' → st ι' ∈ S ι) (hN : ∀ ι, (S ι).card ≤ N) {θ : ℝ≥0∞}
    (hθ : ∀ c, ∑' ι, (if st ι = c then b ι else 0) ≤ θ) :
    ∀ n c, ∑' ι, (if st ι = c then chainSum b link n ι else 0) ≤ θ * (N * θ) ^ n := by
  intro n
  induction n with
  | zero => intro c; simpa [chainSum] using hθ c
  | succ n ih =>
    intro c
    calc ∑' ι, (if st ι = c then chainSum b link (n + 1) ι else 0)
        = ∑' ι, (if st ι = c then b ι else 0) *
            ∑' ι', (if link ι ι' then chainSum b link n ι' else 0) := by
          refine tsum_congr fun ι => ?_
          split_ifs <;> simp [chainSum]
      _ ≤ ∑' ι, (if st ι = c then b ι else 0) * (N * (θ * (N * θ) ^ n)) := by
          refine ENNReal.tsum_le_tsum fun ι => ?_
          gcongr
          exact linked_sum (chainSum b link n) st link S hS hN ih ι
      _ = (∑' ι, (if st ι = c then b ι else 0)) * (N * (θ * (N * θ) ^ n)) :=
          ENNReal.tsum_mul_right
      _ ≤ θ * (N * (θ * (N * θ) ^ n)) := by gcongr; exact hθ c
      _ = θ * (N * θ) ^ (n + 1) := by ring

/-- (ii), (W3) for the series: with `c'N''θ ≤ ½`, the sum over `n ≥ 1` factors of the numbers
`c'^{n-1}b_{ι₁}⋯b_{ι_n}` of the linked sequences whose first walk begins with the key `c` is at most `2θ`. -/
theorem series_majorant {I κ : Type*} (b : I → ℝ≥0∞) (st : I → κ) (link : I → I → Prop)
    [∀ ι ι', Decidable (link ι ι')] [DecidableEq κ] (S : I → Finset κ) {N : ℕ}
    (hS : ∀ ι ι', link ι ι' → st ι' ∈ S ι) (hN : ∀ ι, (S ι).card ≤ N) {θ c' : ℝ≥0∞}
    (hθ : ∀ c, ∑' ι, (if st ι = c then b ι else 0) ≤ θ) (hsmall : c' * N * θ ≤ 2⁻¹) (c : κ) :
    ∑' n, c' ^ n * ∑' ι, (if st ι = c then chainSum b link n ι else 0) ≤ 2 * θ := by
  calc ∑' n, c' ^ n * ∑' ι, (if st ι = c then chainSum b link n ι else 0)
      ≤ ∑' n : ℕ, c' ^ n * (θ * (N * θ) ^ n) :=
        ENNReal.tsum_le_tsum fun n => by gcongr; exact chainSum_le b st link S hS hN hθ n c
    _ = θ * ∑' n : ℕ, (c' * N * θ) ^ n := by
        rw [← ENNReal.tsum_mul_left]
        exact tsum_congr fun n => by rw [mul_assoc c', mul_pow, mul_pow]; ring
    _ = θ * (1 - c' * N * θ)⁻¹ := by rw [ENNReal.tsum_geometric]
    _ ≤ θ * 2 := by
        gcongr
        rw [ENNReal.inv_le_iff_inv_le, show (2 : ℝ≥0∞)⁻¹ = 1 - 2⁻¹ from ENNReal.one_sub_inv_two.symm]
        exact tsub_le_tsub_left hsmall 1
    _ = 2 * θ := by ring

/-! ### `lem:walk-expansion-parameters`(i): the operator with parameters -/

/-- `lem:walk-expansion-parameters`(i), the majorant: if the numbers `σ_ι = |s_ι|` satisfy
`σ_ι ≤ Ce^{(δ/2)d_{ω(ι)}(y, y')}` (`eq:parameter-walks`, with `C = e^{16κ₁}`), the terms satisfy (W1) and
(W3) with the constants `(B₁, p, δ)`, and a point `y` lies in the first enlarged cube only of walks whose
first key is one of at most `N` keys (`N = N_𝒟`), then
`Σ_ι σ_ι[K_ιf]_y ≤ CNB₁a_{j(y)}^p Σ_{y'} e^{-(δ/2)d(y, y')}[f]_{y'}`; the series of the block norms of
`s_ιK_ιf` converges, uniformly in `s`. -/
theorem parameters_majorant {I κ V V' : Type*} {nrm : V → β → ℝ} {nrm' : V' → β → ℝ}
    (hn : ∀ f y, 0 ≤ nrm f y) (hd : ∀ ω y y', B.d y y' ≤ W.dw ω y y')
    {δ C : ℝ} (hδ : 0 < δ) (hC : 0 ≤ C) {p : ℤ} (K : I → V → V') (ωI : I → Ω) (b : I → ℝ)
    (hb : ∀ ι, 0 ≤ b ι) (hK : ∀ ι, Bound B W nrm nrm' (K ι) (ωI ι) (b ι) p δ 0) (σ : I → ℝ)
    (hσ0 : ∀ ι, 0 ≤ σ ι) (hσ : ∀ ι y y', σ ι ≤ C * Real.exp (δ / 2 * W.dw (ωI ι) y y'))
    [DecidableEq κ] (st : I → κ) (keys : β → Finset κ) {N : ℕ}
    (hkeys : ∀ ι y, y ∈ W.first (ωI ι) → st ι ∈ keys y) (hN : ∀ y, (keys y).card ≤ N) {B₁ : ℝ}
    (hB₁ : 0 ≤ B₁)
    (hW3 : ∀ c, ∑' ι, (if st ι = c then ENNReal.ofReal (b ι) else 0) ≤ ENNReal.ofReal B₁)
    (f : V) (y : β) :
    ∑' ι, ENNReal.ofReal (σ ι * nrm' (K ι f) y) ≤
      ENNReal.ofReal (C * N * B₁ * B.a (B.j y) ^ p *
        ∑ y', Real.exp (-(δ / 2 * B.d y y')) * nrm f y') := by
  set T := ∑ y', Real.exp (-(δ / 2 * B.d y y')) * nrm f y'
  have hT : 0 ≤ T := Finset.sum_nonneg fun y' _ => mul_nonneg (Real.exp_pos _).le (hn f y')
  have hay := zpow_pos (B.a_pos (B.j y)) p
  -- the term of one index
  have hterm : ∀ ι, ENNReal.ofReal (σ ι * nrm' (K ι f) y) ≤
      (if st ι ∈ keys y then ENNReal.ofReal (b ι) else 0) *
        ENNReal.ofReal (C * B.a (B.j y) ^ p * T) := by
    intro ι
    by_cases hy : y ∈ W.first (ωI ι)
    · rw [if_pos (hkeys ι y hy), ← ENNReal.ofReal_mul (hb ι)]
      refine ENNReal.ofReal_le_ofReal ?_
      have h1 := (hK ι f).2 y hy
      simp only [zero_mul, add_zero] at h1
      calc σ ι * nrm' (K ι f) y
          ≤ σ ι * (b ι * B.a (B.j y) ^ p *
              ∑ y' ∈ W.last (ωI ι), Real.exp (-(δ * W.dw (ωI ι) y y')) * nrm f y') :=
            mul_le_mul_of_nonneg_left h1 (hσ0 ι)
        _ = b ι * B.a (B.j y) ^ p *
              ∑ y' ∈ W.last (ωI ι), (σ ι * Real.exp (-(δ * W.dw (ωI ι) y y'))) * nrm f y' := by
            simp only [Finset.mul_sum]
            exact Finset.sum_congr rfl fun y' _ => by ring
        _ ≤ b ι * B.a (B.j y) ^ p *
              ∑ y' ∈ W.last (ωI ι), (C * Real.exp (-(δ / 2 * B.d y y'))) * nrm f y' := by
            refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun y' _ =>
              mul_le_mul_of_nonneg_right ?_ (hn f y')) (mul_nonneg (hb ι) hay.le)
            calc σ ι * Real.exp (-(δ * W.dw (ωI ι) y y'))
                ≤ C * Real.exp (δ / 2 * W.dw (ωI ι) y y') * Real.exp (-(δ * W.dw (ωI ι) y y')) :=
                  mul_le_mul_of_nonneg_right (hσ ι y y') (Real.exp_pos _).le
              _ = C * Real.exp (-(δ / 2 * W.dw (ωI ι) y y')) := by
                  rw [mul_assoc, ← Real.exp_add]; congr 2; ring
              _ ≤ C * Real.exp (-(δ / 2 * B.d y y')) := by
                  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC
                  have := mul_le_mul_of_nonneg_left (hd (ωI ι) y y') hδ.le
                  linarith
        _ ≤ b ι * B.a (B.j y) ^ p * ∑ y', (C * Real.exp (-(δ / 2 * B.d y y'))) * nrm f y' :=
            mul_le_mul_of_nonneg_left (Finset.sum_le_univ_sum_of_nonneg fun y' =>
              mul_nonneg (mul_nonneg hC (Real.exp_pos _).le) (hn f y')) (mul_nonneg (hb ι) hay.le)
        _ = b ι * (C * B.a (B.j y) ^ p * T) := by
            simp only [T, Finset.mul_sum]
            exact Finset.sum_congr rfl fun y' _ => by ring
    · rw [(hK ι f).1 y hy, mul_zero, ENNReal.ofReal_zero]
      exact zero_le
  -- the count of the keys
  have hcount : ∑' ι, (if st ι ∈ keys y then ENNReal.ofReal (b ι) else 0) ≤ N * ENNReal.ofReal B₁ :=
    linked_sum (I := Unit) (fun ι => ENNReal.ofReal (b ι)) st (fun _ ι => st ι ∈ keys y)
      (fun _ => keys y) (fun _ _ h => h) (fun _ => hN y) hW3 ()
  calc ∑' ι, ENNReal.ofReal (σ ι * nrm' (K ι f) y)
      ≤ ∑' ι, (if st ι ∈ keys y then ENNReal.ofReal (b ι) else 0) *
          ENNReal.ofReal (C * B.a (B.j y) ^ p * T) := ENNReal.tsum_le_tsum hterm
    _ = (∑' ι, (if st ι ∈ keys y then ENNReal.ofReal (b ι) else 0)) *
          ENNReal.ofReal (C * B.a (B.j y) ^ p * T) := ENNReal.tsum_mul_right
    _ ≤ N * ENNReal.ofReal B₁ * ENNReal.ofReal (C * B.a (B.j y) ^ p * T) := by gcongr
    _ = ENNReal.ofReal (C * N * B₁ * B.a (B.j y) ^ p * T) := by
        rw [show (N : ℝ≥0∞) = ENNReal.ofReal N by simp, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1; ring

/-- (ii), the operator: if the geometric series of `x` converges in a Hausdorff topological ring, then
`1 - x` is invertible with the inverse `Σ_{n ≥ 0} xⁿ`, so that `Σ_{n ≥ 1} xⁿ = (1 - x)⁻¹ - 1`. -/
theorem one_sub_inverse {R : Type*} [Ring R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]
    (x : R) (hx : Summable fun n : ℕ => x ^ n) :
    (∑' n : ℕ, x ^ n) * (1 - x) = 1 ∧ (1 - x) * (∑' n : ℕ, x ^ n) = 1 ∧
      ∑' n : ℕ, x ^ (n + 1) = (∑' n : ℕ, x ^ n) - 1 := by
  have h0 : ∑' n : ℕ, x ^ n = 1 + ∑' n : ℕ, x ^ (n + 1) := by
    rw [hx.tsum_eq_zero_add, pow_zero]
  have hr : ∑' n : ℕ, x ^ (n + 1) = (∑' n : ℕ, x ^ n) * x := by
    rw [← hx.tsum_mul_right]; simp only [pow_succ]
  have hl : ∑' n : ℕ, x ^ (n + 1) = x * ∑' n : ℕ, x ^ n := by
    rw [← hx.tsum_mul_left]; simp only [pow_succ']
  refine ⟨?_, ?_, ?_⟩
  · rw [mul_sub, mul_one, ← hr]; nth_rewrite 1 [h0]; abel
  · rw [sub_mul, one_mul, ← hl]; nth_rewrite 1 [h0]; abel
  · rw [h0]; abel

end WalkProduct

end CoreLean
