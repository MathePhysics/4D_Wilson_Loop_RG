import SpectralTheorem.RealCalculus
import SpectralTheorem.UnboundedBorel

/-!
# Unbounded Borel functions of a self-adjoint operator on a real Hilbert space

**Reed–Simon I, Theorem VIII.6 (second part), p. 264, over `ℝ`.**  Let `A` be self-adjoint on a
real Hilbert space `E` and `g` a real-valued Borel function on `ℝ`.  Then `g(A)`, defined on
`D_g = {ψ | ∫ |g(λ)|² dμ_ψ < ∞}`, is self-adjoint.  If `g` is bounded, `g(A)` is the operator
`φ̂(g)` of Theorem VIII.5 (`SpectralTheorem.realCalc`), and `g(A) = A` for `g(x) = x`.

Reed–Simon work over complex Hilbert spaces; the real statement is obtained through the
complexification `E_ℂ`.  With `A_ℂ` the complexification of `A` and `g(A_ℂ)` the operator of
`SpectralTheorem.UnboundedBorel`, `g(A)` is the real operator underlying `g(A_ℂ)`.

Proof sketch.
* The spectral measures of `z` and `conj z` for `A_ℂ` agree: `μ_z(Ω) = (z, χ_Ω(A_ℂ) z)` is real,
  and `(conj z, χ_Ω(A_ℂ) conj z) = conj (z, χ_Ω(A_ℂ) z)` by the conjugation symmetry of the
  functional calculus (`SpectralTheorem.conj_selfAdjointCalc`).  Hence `D_g` is invariant under
  the conjugation.
* `g(A_ℂ)` commutes with the conjugation: `g(A_ℂ) z` is the limit of `gₙ(A_ℂ) z` for the real
  truncations `gₙ` of `g`, and each `gₙ(A_ℂ)` commutes with the conjugation.
* An unbounded operator `B` on `E_ℂ` commuting with the conjugation is the complexification of the
  real operator `x ↦ Re B x` on `{x | x ∈ D(B)}` (`Complexification.complexifyPMap_descendPMap`).
  So `g(A)_ℂ = g(A_ℂ)`, which is self-adjoint (`SpectralTheorem.isSelfAdjoint_borelPMap`), and
  `g(A)` is self-adjoint by `Complexification.isSelfAdjoint_complexifyPMap_iff`.

Semibounded operators.  If `c ‖ψ‖² ≤ ⟪A ψ, ψ⟫` on `D(A)`, then `P_{(-∞, c)} = 0`, so `h(A)`
depends only on `h` on `[c, ∞)`.  For a bounded Borel set `S`, `P_S` maps into `D(A)` with
`A P_S = (x χ_S)(A)` (as `h(A) = (A + i)⁻¹ ((x + i) h)(A)` when `h` and `x h` are bounded).
On `S_m = {x | c - (m + 1) < x, 1 < (m + 1)(c - x)}` the function `((m + 1)(c - x) - 1) χ_{S_m}`
is nonnegative, so with `w = P_{S_m} ψ`, (f) gives
`0 ≤ (m + 1)(c ‖w‖² - ⟪A w, w⟫) - ‖w‖² ≤ -‖w‖²`; hence `P_{S_m} = 0`, and `P_{(-∞, c)} = 0` by
(d), as `χ_{S_m} → χ_{(-∞, c)}` pointwise.

## Main definitions and results

* `SpectralTheorem.Complexification.descendPMap B hB`: the real operator underlying an unbounded
  complex operator `B` on `E_ℂ` that commutes with the conjugation, with
  `complexifyPMap_descendPMap`.
* `SpectralTheorem.saMeasure_conj`: `μ_{conj z} = μ_z` for `A_ℂ`.
* `SpectralTheorem.borelPMap_conj`: `g(A_ℂ)` commutes with the conjugation for real `g`.
* `SpectralTheorem.realBorelPMap hA hg`: the operator `g(A)` on `E`, with
  `complexifyPMap_realBorelPMap`, `mem_realBorelPMap_domain`, `realBorelPMap_apply`.
* `SpectralTheorem.isSelfAdjoint_realBorelPMap`: **Theorem VIII.6** (second part) over `ℝ`.
* `SpectralTheorem.realBorelPMap_bounded`, `SpectralTheorem.realBorelPMap_id`.
* `SpectralTheorem.selfAdjointCalc_apply_mem_domain`: `h(A)` maps into `D(A)` with
  `A h(A) = (x h)(A)` when `h` and `x h` are bounded (complex `H`);
  `SpectralTheorem.realSpectralProjection_apply_mem_domain`: `A P_S = (x χ_S)(A)` for bounded `S`.
* `SpectralTheorem.realSpectralProjection_Iio_eq_zero`: `P_{(-∞, c)} = 0` if `c ‖ψ‖² ≤ ⟪A ψ, ψ⟫`;
  `SpectralTheorem.realCalc_eq_of_eqOn_Ici`: then `h(A)` depends only on `h` on `[c, ∞)`.
-/

noncomputable section

open scoped InnerProductSpace Topology
open MeasureTheory Filter

namespace SpectralTheorem

universe u

namespace Complexification

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### Descent of unbounded operators commuting with the conjugation -/

/-- An unbounded operator `B` on `E_ℂ` commutes with the conjugation: its domain is invariant and
`B (conj z) = conj (B z)`. -/
structure PMapCommutesConj (B : Complexification E →ₗ.[ℂ] Complexification E) : Prop where
  conj_mem : ∀ {z : Complexification E}, z ∈ B.domain → conj z ∈ B.domain
  apply_conj : ∀ z : B.domain, B ⟨conj (z : Complexification E), conj_mem z.2⟩ = conj (B z)

/-- The real domain `{x | x ∈ D(B)}` of an unbounded operator `B` on `E_ℂ`. -/
def descendDomain (B : Complexification E →ₗ.[ℂ] Complexification E) : Submodule ℝ E where
  carrier := {x | ofReal x ∈ B.domain}
  add_mem' {x y} hx hy := by
    change ofReal (x + y) ∈ B.domain
    rw [map_add]
    exact B.domain.add_mem hx hy
  zero_mem' := by
    change ofReal (0 : E) ∈ B.domain
    rw [map_zero]
    exact B.domain.zero_mem
  smul_mem' r x hx := by
    change ofReal (r • x) ∈ B.domain
    rw [map_smul, ← Complex.coe_smul]
    exact B.domain.smul_mem _ hx

theorem mem_descendDomain {B : Complexification E →ₗ.[ℂ] Complexification E} {x : E} :
    x ∈ descendDomain B ↔ ofReal x ∈ B.domain :=
  Iff.rfl

/-- The action `x ↦ Re (B x)` of `B` on real vectors. -/
def descendAux (B : Complexification E →ₗ.[ℂ] Complexification E) :
    descendDomain B →ₗ[ℝ] E where
  toFun x := (B ⟨ofReal (x : E), x.2⟩).re
  map_add' x y := by
    have e : (⟨ofReal ((x + y : descendDomain B) : E), (x + y).2⟩ : B.domain) =
        ⟨ofReal (x : E), x.2⟩ + ⟨ofReal (y : E), y.2⟩ :=
      Subtype.ext (map_add ofReal (x : E) (y : E))
    rw [e, B.map_add, add_re]
  map_smul' r x := by
    have e : (⟨ofReal ((r • x : descendDomain B) : E), (r • x).2⟩ : B.domain) =
        (r : ℂ) • (⟨ofReal (x : E), x.2⟩ : B.domain) :=
      Subtype.ext (by
        change ofReal (r • (x : E)) = (r : ℂ) • ofReal (x : E)
        rw [map_smul, Complex.coe_smul])
    rw [e, B.map_smul, Complex.coe_smul, real_smul_re, RingHom.id_apply]

/-- **The real operator underlying `B`**: `x ↦ Re (B x)` on `{x | x ∈ D(B)}`, for an unbounded
operator `B` on `E_ℂ` commuting with the conjugation. -/
def descendPMap (B : Complexification E →ₗ.[ℂ] Complexification E)
    (_hB : PMapCommutesConj B) : E →ₗ.[ℝ] E where
  domain := descendDomain B
  toFun := descendAux B

variable {B : Complexification E →ₗ.[ℂ] Complexification E}

theorem mem_descendPMap_domain (hB : PMapCommutesConj B) {x : E} :
    x ∈ (descendPMap B hB).domain ↔ ofReal x ∈ B.domain :=
  Iff.rfl

theorem descendPMap_apply (hB : PMapCommutesConj B) (x : (descendPMap B hB).domain) :
    descendPMap B hB x = (B ⟨ofReal (x : E), x.2⟩).re :=
  rfl

/-- `B` maps real vectors to real vectors. -/
theorem PMapCommutesConj.apply_ofReal_im (hB : PMapCommutesConj B) {x : E}
    (hx : ofReal x ∈ B.domain) : (B ⟨ofReal x, hx⟩).im = 0 := by
  refine conj_eq_self_iff.mp ?_
  rw [← hB.apply_conj ⟨ofReal x, hx⟩]
  exact congrArg B (Subtype.ext (conj_ofReal x))

theorem PMapCommutesConj.apply_ofReal (hB : PMapCommutesConj B) {x : E}
    (hx : ofReal x ∈ B.domain) : B ⟨ofReal x, hx⟩ = ofReal ((B ⟨ofReal x, hx⟩).re) := by
  ext
  · rfl
  · exact hB.apply_ofReal_im hx

/-- `ofReal (descendPMap B x) = B x` on real vectors. -/
theorem ofReal_descendPMap_apply (hB : PMapCommutesConj B) (x : (descendPMap B hB).domain) :
    ofReal (descendPMap B hB x) = B ⟨ofReal (x : E), x.2⟩ :=
  (hB.apply_ofReal x.2).symm

theorem two_smul_ofReal_re (z : Complexification E) :
    (2 : ℂ) • ofReal z.re = z + conj z := by
  ext <;> simp [two_smul]

theorem two_smul_ofReal_im (z : Complexification E) :
    (2 : ℂ) • ofReal z.im = (-Complex.I) • (z - conj z) := by
  ext <;> simp [two_smul]

/-- The domain of `B` is `D ⊕ i D` with `D` its real part. -/
theorem mem_domain_iff_of_commutesConj (hB : PMapCommutesConj B) {z : Complexification E} :
    z ∈ B.domain ↔ ofReal z.re ∈ B.domain ∧ ofReal z.im ∈ B.domain := by
  constructor
  · intro hz
    have hc := hB.conj_mem hz
    refine ⟨(Submodule.smul_mem_iff _ (two_ne_zero (α := ℂ))).mp ?_,
      (Submodule.smul_mem_iff _ (two_ne_zero (α := ℂ))).mp ?_⟩
    · rw [two_smul_ofReal_re]
      exact B.domain.add_mem hz hc
    · rw [two_smul_ofReal_im]
      exact B.domain.smul_mem _ (B.domain.sub_mem hz hc)
  · rintro ⟨h1, h2⟩
    rw [← ofReal_add_I_smul z]
    exact B.domain.add_mem h1 (B.domain.smul_mem _ h2)

/-- **An operator commuting with the conjugation is the complexification of its descent.** -/
theorem complexifyPMap_descendPMap (hB : PMapCommutesConj B) :
    complexifyPMap (descendPMap B hB) = B := by
  refine LinearPMap.ext ?_ fun z h h' => ?_
  · ext z
    rw [mem_complexifyPMap_domain, mem_descendPMap_domain, mem_descendPMap_domain]
    exact (mem_domain_iff_of_commutesConj hB).symm
  · have hz := (mem_domain_iff_of_commutesConj hB).mp h'
    have e : (⟨z, h'⟩ : B.domain) = ⟨ofReal z.re, hz.1⟩ + Complex.I • ⟨ofReal z.im, hz.2⟩ :=
      Subtype.ext (ofReal_add_I_smul z).symm
    rw [e, B.map_add, B.map_smul, hB.apply_ofReal hz.1, hB.apply_ofReal hz.2, ← mk_eq]
    rfl

end Complexification

/-! ### Conjugation symmetry of `g(A_ℂ)` for real `g` -/

section ConjBorel

open Complexification

theorem star_indicatorReal {Ω : Set ℝ} (hΩ : MeasurableSet Ω) :
    star (indicatorReal hΩ) = indicatorReal hΩ :=
  Subtype.ext (funext fun x => by
    change star (Ω.indicator (fun _ => (1 : ℂ)) x) = Ω.indicator (fun _ => (1 : ℂ)) x
    by_cases hx : x ∈ Ω <;> simp [hx])

theorem measurable_ofReal_comp {g : ℝ → ℝ} (hg : Measurable g) :
    Measurable fun x => (g x : ℂ) :=
  Complex.measurable_ofReal.comp hg

/-- The truncations `gₙ = g · 1_{|g| ≤ n}` of a real function are real. -/
theorem star_borelTrunc_ofReal {g : ℝ → ℝ} (hg : Measurable g) (n : ℕ) :
    star (borelTrunc (measurable_ofReal_comp hg) n) = borelTrunc (measurable_ofReal_comp hg) n :=
  Subtype.ext (funext fun x => by
    change star ({x | ‖(g x : ℂ)‖ ≤ n}.indicator (fun x => (g x : ℂ)) x) =
      {x | ‖(g x : ℂ)‖ ≤ n}.indicator (fun x => (g x : ℂ)) x
    by_cases hx : ‖(g x : ℂ)‖ ≤ n
    · rw [Set.indicator_of_mem (show x ∈ {x | ‖(g x : ℂ)‖ ≤ n} from hx)]
      exact Complex.conj_ofReal _
    · rw [Set.indicator_of_notMem (show x ∉ {x | ‖(g x : ℂ)‖ ≤ n} from hx), star_zero])

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {A : E →ₗ.[ℝ] E} (hA : IsSelfAdjoint A)

/-- **The spectral measures of `z` and `conj z` for `A_ℂ` agree.** -/
theorem saMeasure_conj (z : Complexification E) :
    saMeasure hA.complexify (conj z) = saMeasure hA.complexify z := by
  ext Ω hΩ
  have h1 := inner_selfAdjointCalc_indicatorReal hA.complexify (conj z) hΩ
  have h2 := inner_selfAdjointCalc_indicatorReal hA.complexify z hΩ
  have h3 : selfAdjointCalc hA.complexify (indicatorReal hΩ) (conj z) =
      conj (selfAdjointCalc hA.complexify (indicatorReal hΩ) z) := by
    rw [conj_selfAdjointCalc hA, star_indicatorReal]
  rw [h3, inner_conj_conj', ← inner_conj_symm, h2, Complex.conj_ofReal] at h1
  have h4 := Complex.ofReal_injective h1
  have e1 := ofReal_measureReal (μ := saMeasure hA.complexify (conj z)) (s := Ω)
    (measure_ne_top _ _)
  have e2 := ofReal_measureReal (μ := saMeasure hA.complexify z) (s := Ω) (measure_ne_top _ _)
  rw [← e1, ← e2, h4]

/-- For real `g`, the domain `D_g` of `g(A_ℂ)` is invariant under the conjugation. -/
theorem conj_mem_borelPMap_domain {g : ℝ → ℝ} (hg : Measurable g) {z : Complexification E}
    (hz : z ∈ (borelPMap hA.complexify fun x => (g x : ℂ)).domain) :
    conj z ∈ (borelPMap hA.complexify fun x => (g x : ℂ)).domain := by
  rw [mem_borelPMap_domain _ (measurable_ofReal_comp hg)] at hz ⊢
  rw [saMeasure_conj hA]
  exact hz

/-- **For real `g`, `g(A_ℂ)` commutes with the conjugation**: `gₙ(A_ℂ)` does for the real
truncations `gₙ`, and `gₙ(A_ℂ) z → g(A_ℂ) z`. -/
theorem borelPMap_conj {g : ℝ → ℝ} (hg : Measurable g)
    (z : (borelPMap hA.complexify fun x => (g x : ℂ)).domain) :
    borelPMap hA.complexify (fun x => (g x : ℂ))
        ⟨conj (z : Complexification E), conj_mem_borelPMap_domain hA hg z.2⟩ =
      conj (borelPMap hA.complexify (fun x => (g x : ℂ)) z) := by
  have hgc := measurable_ofReal_comp hg
  have h1 := tendsto_trunc_borelPMap hA.complexify hgc
    ⟨conj (z : Complexification E), conj_mem_borelPMap_domain hA hg z.2⟩
  have h2 := (conj.continuous.tendsto _).comp (tendsto_trunc_borelPMap hA.complexify hgc z)
  refine tendsto_nhds_unique h1 (h2.congr fun n => ?_)
  change conj (selfAdjointCalc hA.complexify (borelTrunc hgc n) z) =
    selfAdjointCalc hA.complexify (borelTrunc hgc n) (conj (z : Complexification E))
  rw [conj_selfAdjointCalc hA, star_borelTrunc_ofReal hg]

theorem pmapCommutesConj_borelPMap {g : ℝ → ℝ} (hg : Measurable g) :
    PMapCommutesConj (borelPMap hA.complexify fun x => (g x : ℂ)) :=
  ⟨conj_mem_borelPMap_domain hA hg, borelPMap_conj hA hg⟩

end ConjBorel

/-! ### The operator `g(A)` on the real Hilbert space -/

section RealBorel

open Complexification

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {A : E →ₗ.[ℝ] E} (hA : IsSelfAdjoint A)

/-- **The operator `g(A) = ∫ g(λ) dP_λ`** for a real Borel function `g` and a self-adjoint `A` on
a real Hilbert space (Reed–Simon I, pp. 263–264, over `ℝ`): the real operator underlying
`g(A_ℂ)`. -/
def realBorelPMap {g : ℝ → ℝ} (hg : Measurable g) : E →ₗ.[ℝ] E :=
  descendPMap (borelPMap hA.complexify fun x => (g x : ℂ)) (pmapCommutesConj_borelPMap hA hg)

/-- `g(A)_ℂ = g(A_ℂ)`. -/
theorem complexifyPMap_realBorelPMap {g : ℝ → ℝ} (hg : Measurable g) :
    complexifyPMap (realBorelPMap hA hg) = borelPMap hA.complexify fun x => (g x : ℂ) :=
  complexifyPMap_descendPMap _

/-- **The domain of `g(A)`** is `D_g = {ψ | ∫ |g|² dμ_ψ < ∞}`. -/
theorem mem_realBorelPMap_domain {g : ℝ → ℝ} (hg : Measurable g) {x : E} :
    x ∈ (realBorelPMap hA hg).domain ↔ MemLp g 2 (saMeasure hA.complexify (ofReal x)) := by
  rw [realBorelPMap, mem_descendPMap_domain, mem_borelPMap_domain _ (measurable_ofReal_comp hg)]
  exact memLp_congr_norm (measurable_ofReal_comp hg).aestronglyMeasurable
    hg.aestronglyMeasurable (.of_forall fun y => Complex.norm_real (g y))

/-- `g(A) x = g(A_ℂ) x` on real vectors. -/
theorem realBorelPMap_apply {g : ℝ → ℝ} (hg : Measurable g) (x : (realBorelPMap hA hg).domain) :
    ofReal (realBorelPMap hA hg x) =
      borelPMap hA.complexify (fun y => (g y : ℂ)) ⟨ofReal (x : E), x.2⟩ :=
  ofReal_descendPMap_apply _ x

/-- **Reed–Simon I, Theorem VIII.6** (second part, p. 264, over `ℝ`): for a real Borel
function `g`, the operator `g(A)` on `D_g` is self-adjoint. -/
theorem isSelfAdjoint_realBorelPMap {g : ℝ → ℝ} (hg : Measurable g) :
    IsSelfAdjoint (realBorelPMap hA hg) := by
  rw [← isSelfAdjoint_complexifyPMap_iff, complexifyPMap_realBorelPMap]
  exact isSelfAdjoint_borelPMap hA.complexify hg

/-- **Bounded `g`**: `g(A)` is the everywhere defined operator `realCalc hA g`. -/
theorem realBorelPMap_bounded (h : boundedMeasurableReal ℝ) :
    realBorelPMap hA (boundedMeasurableReal.measurable h) =
      ((realCalc hA h : E →L[ℝ] E) : E →ₗ[ℝ] E).toPMap ⊤ := by
  apply complexifyPMap_injective
  rw [complexifyPMap_realBorelPMap, complexifyPMap_toPMap, complexifyCLM_realCalc]
  have e := borelPMap_bounded hA.complexify (ofRealBM h)
  rw [coe_ofRealBM] at e
  exact e

/-- **`A = ∫ λ dP_λ`**: `g(A) = A` for `g(x) = x`. -/
theorem realBorelPMap_id : realBorelPMap hA (measurable_id' : Measurable fun x : ℝ => x) = A := by
  apply complexifyPMap_injective
  rw [complexifyPMap_realBorelPMap]
  exact borelPMap_id hA.complexify

end RealBorel

/-! ### Functions of `A` with values in `D(A)` -/

section Domain

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)

/-- If `h` and `x h` are bounded Borel functions, then `h(A)` maps into `D(A)` and
`A h(A) = (x h)(A)`: `h(A) = (A + i)⁻¹ ((x + i) h)(A)`. -/
theorem selfAdjointCalc_apply_mem_domain (h xh : boundedMeasurable ℝ)
    (hxh : ∀ x : ℝ, (xh : ℝ → ℂ) x = (x : ℂ) * (h : ℝ → ℂ) x) (z : H) :
    ∃ hm : selfAdjointCalc hA h z ∈ A.domain,
      A ⟨selfAdjointCalc hA h z, hm⟩ = selfAdjointCalc hA xh z := by
  set v := selfAdjointCalc hA (xh + Complex.I • h) z with hv
  have hg : resolventFnBM * (xh + Complex.I • h) = h := Subtype.ext (funext fun x => by
    change resolventFn x * ((xh : ℝ → ℂ) x + Complex.I * (h : ℝ → ℂ) x) = (h : ℝ → ℂ) x
    rw [hxh]
    linear_combination ((h : ℝ → ℂ) x) * ofReal_mul_resolventFn x)
  have hR : selfAdjointCalc hA h z = resolventI hA 1 abs_one v := by
    have e : selfAdjointCalc hA h z = selfAdjointCalc hA resolventFnBM v := by
      conv_lhs => rw [← hg]
      rw [map_mul]
      rfl
    rw [e, (isSelfAdjointCalculus_selfAdjointCalc hA).map_resolventFn]
    rfl
  have hmem : selfAdjointCalc hA h z ∈ A.domain := by
    rw [hR]
    exact resolventI_mem_domain hA abs_one v
  refine ⟨hmem, ?_⟩
  have key : ∀ (y : H) (hy : y ∈ A.domain), y = resolventI hA 1 abs_one v →
      A ⟨y, hy⟩ = A ⟨resolventI hA 1 abs_one v, resolventI_mem_domain hA abs_one v⟩ := by
    rintro y hy rfl
    rfl
  rw [key _ hmem hR]
  have hadd := addScalar_resolventI hA abs_one v
  simp only [Complex.ofReal_one, one_mul, RCLike.I_to_complex] at hadd
  rw [eq_sub_of_add_eq hadd, ← hR, hv, map_add, map_smul, add_apply,
    smul_apply, add_sub_cancel_right]

end Domain

/-! ### Semibounded operators -/

section Semibounded

open Complexification

/-- `x ↦ x χ_S(x)` for a Borel set `S ⊆ [a, b]`, a bounded measurable function. -/
def mulIndicatorBMReal {S : Set ℝ} (hS : MeasurableSet S) {a b : ℝ} (hab : S ⊆ Set.Icc a b) :
    boundedMeasurableReal ℝ :=
  ⟨fun x => x * S.indicator (fun _ => (1 : ℝ)) x,
    measurable_id.mul (measurable_const.indicator hS), |a| + |b|, fun x => by
      change |x * S.indicator (fun _ => (1 : ℝ)) x| ≤ |a| + |b|
      by_cases hx : x ∈ S
      · rw [Set.indicator_of_mem hx, mul_one]
        obtain ⟨h1, h2⟩ := hab hx
        exact abs_le.mpr ⟨by linarith [neg_abs_le a, abs_nonneg b],
          by linarith [le_abs_self b, abs_nonneg a]⟩
      · rw [Set.indicator_of_notMem hx, mul_zero, abs_zero]
        positivity⟩

theorem coe_mulIndicatorBMReal {S : Set ℝ} (hS : MeasurableSet S) {a b : ℝ}
    (hab : S ⊆ Set.Icc a b) :
    (mulIndicatorBMReal hS hab : ℝ → ℝ) = fun x => x * S.indicator (fun _ => (1 : ℝ)) x :=
  rfl

theorem indicatorBMReal_mul_mulIndicatorBMReal {S : Set ℝ} (hS : MeasurableSet S) {a b : ℝ}
    (hab : S ⊆ Set.Icc a b) :
    indicatorBMReal hS * mulIndicatorBMReal hS hab = mulIndicatorBMReal hS hab := by
  refine Subtype.ext (funext fun x => ?_)
  change S.indicator (fun _ => (1 : ℝ)) x * (x * S.indicator (fun _ => (1 : ℝ)) x) =
    x * S.indicator (fun _ => (1 : ℝ)) x
  by_cases hx : x ∈ S <;> simp [hx]

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {A : E →ₗ.[ℝ] E} (hA : IsSelfAdjoint A)

/-- For a bounded Borel set `S`, `P_S` maps into `D(A)` and `A P_S = (x χ_S)(A)`. -/
theorem realSpectralProjection_apply_mem_domain {S : Set ℝ} (hS : MeasurableSet S) {a b : ℝ}
    (hab : S ⊆ Set.Icc a b) (ψ : E) :
    ∃ hm : realSpectralProjection hA hS ψ ∈ A.domain,
      A ⟨realSpectralProjection hA hS ψ, hm⟩ = realCalc hA (mulIndicatorBMReal hS hab) ψ := by
  obtain ⟨hm, he⟩ := selfAdjointCalc_apply_mem_domain hA.complexify
    (ofRealBM (indicatorBMReal hS)) (ofRealBM (mulIndicatorBMReal hS hab))
    (fun x => Complex.ofReal_mul _ _) (ofReal ψ)
  have e0 := realCalc_apply hA (indicatorBMReal hS) ψ
  rw [← e0] at hm
  have hw : realSpectralProjection hA hS ψ ∈ A.domain := (mem_complexifyPMap_domain.mp hm).1
  refine ⟨hw, ofReal_injective ?_⟩
  rw [← complexifyPMap_ofReal hw, realCalc_apply, ← he]
  exact congrArg (complexifyPMap A) (Subtype.ext e0)

/-- The sets `S_m = {x | c - (m + 1) < x, 1 < (m + 1) (c - x)}`, increasing to `(-∞, c)`. -/
def semiboundSet (c : ℝ) (m : ℕ) : Set ℝ :=
  {x | c - (m + 1) < x} ∩ {x | 1 < (m + 1) * (c - x)}

theorem measurableSet_semiboundSet (c : ℝ) (m : ℕ) : MeasurableSet (semiboundSet c m) :=
  (measurableSet_lt measurable_const measurable_id).inter
    (measurableSet_lt measurable_const (measurable_const.mul (measurable_const.sub measurable_id)))

theorem lt_of_mem_semiboundSet {c x : ℝ} {m : ℕ} (hx : x ∈ semiboundSet c m) : x < c := by
  have h2 : 1 < (m + 1) * (c - x) := hx.2
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  by_contra hcx
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ m + 1) (sub_nonneg.mpr (not_lt.mp hcx))]

theorem semiboundSet_subset (c : ℝ) (m : ℕ) : semiboundSet c m ⊆ Set.Icc (c - (m + 1)) c :=
  fun _ hx => ⟨hx.1.le, (lt_of_mem_semiboundSet hx).le⟩

/-- At each point, `χ_{S_m} = χ_{(-∞, c)}` for large `m`. -/
theorem eventually_indicator_semiboundSet (c x : ℝ) :
    ∀ᶠ m in atTop, (semiboundSet c m).indicator (fun _ => (1 : ℝ)) x =
      (Set.Iio c).indicator (fun _ => (1 : ℝ)) x := by
  by_cases hx : x < c
  · have h0 : 0 < c - x := sub_pos.mpr hx
    obtain ⟨N₁, hN₁⟩ := exists_nat_gt (c - x)
    obtain ⟨N₂, hN₂⟩ := Archimedean.arch (2 : ℝ) h0
    rw [nsmul_eq_mul] at hN₂
    filter_upwards [eventually_ge_atTop (N₁ + N₂)] with m hm
    have hm' : ((N₁ + N₂ : ℕ) : ℝ) ≤ m := by exact_mod_cast hm
    push_cast at hm'
    have hN₁' : (0 : ℝ) ≤ N₁ := Nat.cast_nonneg N₁
    have hN₂' : (0 : ℝ) ≤ N₂ := Nat.cast_nonneg N₂
    have hmem : x ∈ semiboundSet c m := by
      refine ⟨?_, ?_⟩
      · change c - (m + 1) < x
        linarith
      · change 1 < (m + 1) * (c - x)
        nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ m + 1 - N₂) h0.le]
    rw [Set.indicator_of_mem hmem, Set.indicator_of_mem (show x ∈ Set.Iio c from hx)]
  · refine Eventually.of_forall fun m => ?_
    have h1 : x ∉ semiboundSet c m := fun h => hx (lt_of_mem_semiboundSet h)
    rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem (show x ∉ Set.Iio c from hx)]

/-- For a lower bound `c` of `A`, `P_{S_m} = 0`: with `w = P_{S_m} ψ ∈ D(A)`, positivity of
`((m + 1)(c - x) - 1) χ_{S_m}(A)` gives `‖w‖² ≤ (m + 1) (c ‖w‖² - ⟪A w, w⟫) ≤ 0`. -/
theorem realSpectralProjection_semiboundSet_eq_zero {c : ℝ}
    (hc : ∀ (ψ : E) (hψ : ψ ∈ A.domain), c * ‖ψ‖ ^ 2 ≤ ⟪A ⟨ψ, hψ⟩, ψ⟫_ℝ) (m : ℕ) :
    realSpectralProjection hA (measurableSet_semiboundSet c m) = 0 := by
  have hS := measurableSet_semiboundSet c m
  have hsub := semiboundSet_subset c m
  ext ψ
  obtain ⟨hw, hAw⟩ := realSpectralProjection_apply_mem_domain hA hS hsub ψ
  have hw' : realCalc hA (indicatorBMReal hS) ψ ∈ A.domain := hw
  have hAw' : A ⟨realCalc hA (indicatorBMReal hS) ψ, hw'⟩ =
      realCalc hA (mulIndicatorBMReal hS hsub) ψ := hAw
  have ht : ∀ x, 0 ≤ ((((m + 1 : ℝ) * c) • indicatorBMReal hS -
      (m + 1 : ℝ) • mulIndicatorBMReal hS hsub - indicatorBMReal hS :
        boundedMeasurableReal ℝ) : ℝ → ℝ) x := fun x => by
    change 0 ≤ ((m + 1 : ℝ) * c) * (semiboundSet c m).indicator (fun _ => (1 : ℝ)) x -
      (m + 1 : ℝ) * (x * (semiboundSet c m).indicator (fun _ => (1 : ℝ)) x) -
        (semiboundSet c m).indicator (fun _ => (1 : ℝ)) x
    by_cases hx : x ∈ semiboundSet c m
    · have h2 : 1 < (m + 1) * (c - x) := hx.2
      rw [Set.indicator_of_mem hx]
      linarith
    · rw [Set.indicator_of_notMem hx]
      simp
  have hpos := (isPositive_realCalc hA ht).inner_nonneg_left ψ
  rw [map_sub, map_sub, map_smul, map_smul] at hpos
  simp only [sub_apply, smul_apply, inner_sub_left, real_inner_smul_left] at hpos
  have hPP : ⟪realCalc hA (indicatorBMReal hS) ψ, ψ⟫_ℝ =
      ‖realCalc hA (indicatorBMReal hS) ψ‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    have hid : realCalc hA (indicatorBMReal hS) (realCalc hA (indicatorBMReal hS) ψ) =
        realCalc hA (indicatorBMReal hS) ψ :=
      congrArg (fun T => T ψ) (isStarProjection_realSpectralProjection hA hS).isIdempotentElem
    conv_lhs => rw [← hid]
    exact (isSelfAdjoint_realCalc hA _).isSymmetric _ _
  have hMP : ⟪realCalc hA (mulIndicatorBMReal hS hsub) ψ, ψ⟫_ℝ =
      ⟪A ⟨realCalc hA (indicatorBMReal hS) ψ, hw'⟩, realCalc hA (indicatorBMReal hS) ψ⟫_ℝ := by
    rw [hAw']
    have hPM : realCalc hA (indicatorBMReal hS) (realCalc hA (mulIndicatorBMReal hS hsub) ψ) =
        realCalc hA (mulIndicatorBMReal hS hsub) ψ := by
      have e := congrArg (fun T => T ψ)
        (map_mul (realCalc hA) (indicatorBMReal hS) (mulIndicatorBMReal hS hsub))
      rw [indicatorBMReal_mul_mulIndicatorBMReal] at e
      exact e.symm
    conv_lhs => rw [← hPM]
    exact (isSelfAdjoint_realCalc hA _).isSymmetric _ _
  have hsemi := hc _ hw'
  rw [hPP, hMP] at hpos
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hn : ‖realCalc hA (indicatorBMReal hS) ψ‖ ^ 2 ≤ 0 := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ m + 1) (sub_nonneg.mpr hsemi)]
  have h0 : ‖realCalc hA (indicatorBMReal hS) ψ‖ = 0 :=
    pow_eq_zero_iff (n := 2) two_ne_zero |>.mp (le_antisymm hn (sq_nonneg _))
  rw [norm_eq_zero] at h0
  exact h0

/-- **Semibounded operators**: if `c ‖ψ‖² ≤ ⟪A ψ, ψ⟫` on `D(A)`, then `P_{(-∞, c)} = 0`. -/
theorem realSpectralProjection_Iio_eq_zero {c : ℝ}
    (hc : ∀ (ψ : E) (hψ : ψ ∈ A.domain), c * ‖ψ‖ ^ 2 ≤ ⟪A ⟨ψ, hψ⟩, ψ⟫_ℝ) :
    realSpectralProjection hA (measurableSet_Iio : MeasurableSet (Set.Iio c)) = 0 := by
  ext ψ
  have h1 := tendsto_realCalc_apply hA (fun m => indicatorBMReal (measurableSet_semiboundSet c m))
    (indicatorBMReal (measurableSet_Iio : MeasurableSet (Set.Iio c))) 1 (fun m x => ?_)
    (fun x => ?_) ψ
  · have h0 : ∀ m, realCalc hA (indicatorBMReal (measurableSet_semiboundSet c m)) ψ = 0 :=
      fun m => congrArg (fun T => T ψ) (realSpectralProjection_semiboundSet_eq_zero hA hc m)
    simp only [h0] at h1
    exact tendsto_nhds_unique h1 tendsto_const_nhds
  · change |(semiboundSet c m).indicator (fun _ => (1 : ℝ)) x| ≤ 1
    by_cases hx : x ∈ semiboundSet c m <;> simp [hx]
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_indicator_semiboundSet c x] with m hm
    exact hm.symm

/-- For semibounded `A`, `h(A)` depends only on `h` on `[c, ∞)`. -/
theorem realCalc_eq_of_eqOn_Ici {c : ℝ}
    (hc : ∀ (ψ : E) (hψ : ψ ∈ A.domain), c * ‖ψ‖ ^ 2 ≤ ⟪A ⟨ψ, hψ⟩, ψ⟫_ℝ)
    {h₁ h₂ : boundedMeasurableReal ℝ} (heq : ∀ x, c ≤ x → (h₁ : ℝ → ℝ) x = (h₂ : ℝ → ℝ) x) :
    realCalc hA h₁ = realCalc hA h₂ := by
  have hprod : h₁ - h₂ =
      (h₁ - h₂) * indicatorBMReal (measurableSet_Iio : MeasurableSet (Set.Iio c)) :=
    Subtype.ext (funext fun x => by
      change (h₁ : ℝ → ℝ) x - (h₂ : ℝ → ℝ) x =
        ((h₁ : ℝ → ℝ) x - (h₂ : ℝ → ℝ) x) * (Set.Iio c).indicator (fun _ => (1 : ℝ)) x
      by_cases hx : x < c
      · rw [Set.indicator_of_mem (show x ∈ Set.Iio c from hx), mul_one]
      · rw [heq x (not_lt.mp hx), sub_self, zero_mul])
  have e := congrArg (realCalc hA) hprod
  have hz : realCalc hA (indicatorBMReal (measurableSet_Iio : MeasurableSet (Set.Iio c))) = 0 :=
    realSpectralProjection_Iio_eq_zero hA hc
  rw [map_mul, map_sub, hz, mul_zero, sub_eq_zero] at e
  exact e

end Semibounded

end SpectralTheorem
