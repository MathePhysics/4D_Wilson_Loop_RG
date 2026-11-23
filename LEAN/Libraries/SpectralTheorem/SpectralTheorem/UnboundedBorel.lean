import SpectralTheorem.UnitaryConj
import SpectralTheorem.SelfAdjointCalculus

/-!
# Unbounded Borel functions of a self-adjoint operator

**Reed–Simon I, pp. 263–264.**  Let `A` be self-adjoint with spectral projections `P_Ω`.  Then
`Ω ↦ (φ, P_Ω φ)` is a Borel measure on `ℝ` (the spectral measure `μ_φ` of `φ`), and
`(φ, g(A) φ) = ∫ g(λ) d(φ, P_λ φ)` for bounded Borel `g` (VIII.4).  If `g` is an unbounded
complex-valued Borel function, let `D_g = {φ | ∫ |g(λ)|² d(φ, P_λ φ) < ∞}` (VIII.5).  Then `D_g`
is dense in `H` and an operator `g(A)` is defined on `D_g` by `(φ, g(A) φ) = ∫ g(λ) d(φ, P_λ φ)`.
In particular, for `φ ∈ D(A)`, `(φ, A φ) = ∫ λ d(φ, P_λ φ)`.  **Theorem VIII.6** (second part,
p. 264): if `g` is a real-valued Borel function on `ℝ`, then `g(A) = ∫ g(λ) dP_λ` defined on
`D_g` is self-adjoint.  If `g` is bounded, `g(A)` coincides with `φ̂(g)` of Theorem VIII.5.

Construction and proof.  The spectral measure of `ψ` is the image of the spectral measure of `ψ`
for `R = (A + i)⁻¹` under `z ↦ (z⁻¹ - i).re`; it does not depend on any choice.  For a cyclic
decomposition of `R`, with unitary `U : H → L²(M, μ)` and `f = λ⁻¹ - i`
(`SpectralTheorem.UnboundedMultiplicationForm`), the spectral measure of `ψ` is the image of
`|U ψ|² μ` under `f`: both give `(ψ, χ_Ω(A) ψ)` on a Borel set `Ω`.  Put
`g(A) = U⁻¹ T_{g ∘ f} U`, with `T_{g ∘ f}` the maximal multiplication operator.  Then
`ψ ∈ D(g(A))` iff `(g ∘ f) U ψ ∈ L²(μ)` iff `∫ |g|² dμ_ψ < ∞`, i.e. `D(g(A)) = D_g`.  With the
truncations `gₙ = g · 1_{|g| ≤ n}`, dominated convergence in `L²(μ)` gives `gₙ(A) ψ → g(A) ψ` for
`ψ ∈ D_g`; hence `g(A)` does not depend on the decomposition.  Density of `D_g`, the adjoint
`g(A)† = ḡ(A)` and self-adjointness for real `g` follow from the corresponding facts for
multiplication operators (`SpectralTheorem.MultiplicationUnbounded`), transported by `U`
(`SpectralTheorem.UnitaryConj`).

## Main definitions and results

* `SpectralTheorem.saMeasure hA ψ`: the spectral measure `μ_ψ` of `ψ` for `A`, a finite measure
  on `ℝ` of total mass `‖ψ‖²` (`saMeasure_univ`).
* `SpectralTheorem.inner_selfAdjointCalc`: `(ψ, h(A) ψ) = ∫ h dμ_ψ` for bounded Borel `h`
  (Reed–Simon's (VIII.4)); `inner_selfAdjointCalc_indicatorReal`: `(ψ, χ_Ω(A) ψ) = μ_ψ(Ω)`.
* `SpectralTheorem.CyclicDecomposition.saMeasure_eq`: `μ_ψ = f_*(|U ψ|² μ)`;
  `CyclicDecomposition.lintegral_saMeasure`: `∫⁻ G dμ_ψ = ∫⁻ |U ψ|² (G ∘ f) dμ`.
* `SpectralTheorem.CyclicDecomposition.borelPMap`: `U⁻¹ T_{g ∘ f} U` for one decomposition;
  `CyclicDecomposition.borelPMap_eq`: it does not depend on the decomposition.
* `SpectralTheorem.borelTrunc`: the truncations `gₙ = g · 1_{‖g‖ ≤ n}`.
* `SpectralTheorem.borelPMap hA g`: the operator `g(A)` for a Borel function `g : ℝ → ℂ`.
* `SpectralTheorem.mem_borelPMap_domain`: `D(g(A)) = D_g = {ψ | g ∈ L²(μ_ψ)}` (VIII.5).
* `SpectralTheorem.tendsto_trunc_borelPMap`: `gₙ(A) ψ → g(A) ψ` for the truncations `gₙ`.
* `SpectralTheorem.enorm_borelPMap_sq`: `‖g(A) ψ‖² = ∫ |g|² dμ_ψ` for `ψ ∈ D_g`.
* `SpectralTheorem.dense_borelPMap_domain`: `D_g` is dense.
* `SpectralTheorem.inner_borelPMap`: `(ψ, g(A) ψ) = ∫ g dμ_ψ` for `ψ ∈ D_g`;
  `SpectralTheorem.eq_borelPMap_of_inner`: this formula on `D_g` determines `g(A)`.
* `SpectralTheorem.adjoint_borelPMap`: `g(A)† = ḡ(A)`.
* `SpectralTheorem.isSelfAdjoint_borelPMap`: **Reed–Simon I, Theorem VIII.6** (second part):
  `g(A)` is self-adjoint for real-valued Borel `g`.
* `SpectralTheorem.borelPMap_bounded`: for bounded Borel `h`, `h(A)` is `selfAdjointCalc hA h`.
* `SpectralTheorem.borelPMap_id`: `A = ∫ λ dP_λ`, i.e. `g(A) = A` for `g(x) = x`;
  `SpectralTheorem.mem_domain_iff_memLp`: `D(A) = {ψ | ∫ λ² dμ_ψ < ∞}`.
* `SpectralTheorem.inner_self_selfAdjoint`: `(ψ, A ψ) = ∫ λ dμ_ψ` for `ψ ∈ D(A)`.
-/

noncomputable section

open scoped InnerProductSpace ComplexConjugate ENNReal Topology LinearPMap
open MeasureTheory Filter KatoRellich

namespace SpectralTheorem

universe u

section General

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- An a.e. strongly measurable `F` is in `L²` iff `∫⁻ ‖F‖ₑ² < ∞`. -/
theorem memLp_two_iff_lintegral_lt_top {F : α → ℂ} (hF : AEStronglyMeasurable F μ) :
    MemLp F 2 μ ↔ ∫⁻ a, ‖F a‖ₑ ^ 2 ∂μ < ∞ := by
  have h := eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (μ := μ) (p := 2) two_ne_zero
    ENNReal.ofNat_ne_top hF
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two] at h
  exact memLp_iff.trans h

/-- `‖F‖₂² = ∫⁻ ‖F‖ₑ²` for a.e. strongly measurable `F`. -/
theorem eLpNorm_two_sq {F : α → ℂ} (hF : AEStronglyMeasurable F μ) :
    eLpNorm F 2 μ ^ 2 = ∫⁻ a, ‖F a‖ₑ ^ 2 ∂μ := by
  have h := eLpNorm_nnreal_pow_eq_lintegral (μ := μ) (p := 2) two_ne_zero hF
  simpa [ENNReal.rpow_two] using h

/-- `∫⁻ ‖u‖ₑ² < ∞` for `u ∈ L²`. -/
theorem lintegral_enorm_sq_lt_top (u : Lp ℂ 2 μ) : ∫⁻ a, ‖u a‖ₑ ^ 2 ∂μ < ∞ :=
  (memLp_two_iff_lintegral_lt_top (Lp.aestronglyMeasurable u)).1 (Lp.memLp u)

/-- **Polarization**: two operators on a complex Hilbert space with the same dense domain and the
same values of `⟪ψ, T ψ⟫` coincide. -/
theorem eq_of_inner_self_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] {S T : E →ₗ.[ℂ] E} (hdom : S.domain = T.domain)
    (hd : Dense (S.domain : Set E))
    (h : ∀ (ψ : E) (h₁ : ψ ∈ S.domain) (h₂ : ψ ∈ T.domain),
      ⟪ψ, S ⟨ψ, h₁⟩⟫_ℂ = ⟪ψ, T ⟨ψ, h₂⟩⟫_ℂ) : S = T := by
  let L : S.domain →ₗ[ℂ] E := S.toFun - T.toFun ∘ₗ (LinearEquiv.ofEq _ _ hdom).toLinearMap
  have hL : ∀ x : S.domain, L x = S x - T ⟨x, hdom ▸ x.2⟩ := fun _ => rfl
  have hq : ∀ x : S.domain, ⟪(x : E), L x⟫_ℂ = 0 := fun x => by
    rw [hL, inner_sub_right, h x x.2 (hdom ▸ x.2), sub_self]
  have hpol : ∀ x y : S.domain, ⟪(x : E), L y⟫_ℂ = 0 := fun x y => by
    have h1 := hq (x + y)
    have h2 := hq (x + Complex.I • y)
    simp only [map_add, map_smul, Submodule.coe_add, Submodule.coe_smul, inner_add_left,
      inner_add_right, inner_smul_left, inner_smul_right, hq x, hq y, Complex.conj_I] at h1 h2
    have h3 : (2 : ℂ) * ⟪(x : E), L y⟫_ℂ = 0 := by
      linear_combination h1 - Complex.I * h2 +
        (⟪(x : E), L y⟫_ℂ - ⟪(y : E), L x⟫_ℂ) * Complex.I_sq
    exact (mul_eq_zero.1 h3).resolve_left two_ne_zero
  refine LinearPMap.ext hdom fun ψ h₁ h₂ => ?_
  have hv : L ⟨ψ, h₁⟩ ∈ S.domainᗮ := fun x hx => hpol ⟨x, hx⟩ ⟨ψ, h₁⟩
  rw [Submodule.topologicalClosure_eq_top_iff.1
    (Submodule.dense_iff_topologicalClosure_eq_top.1 hd), Submodule.mem_bot, hL] at hv
  exact sub_eq_zero.1 hv

end General

/-- The indicator `χ_Ω` of a Borel set `Ω ⊆ ℝ`, as a bounded measurable function. -/
def indicatorReal {Ω : Set ℝ} (hΩ : MeasurableSet Ω) : boundedMeasurable ℝ :=
  ⟨Ω.indicator fun _ => (1 : ℂ), measurable_const.indicator hΩ, 1, fun x => by
    by_cases hx : x ∈ Ω <;> simp [hx]⟩

/-- `χ_Ω` as a function. -/
theorem coe_indicatorReal {Ω : Set ℝ} (hΩ : MeasurableSet Ω) :
    (indicatorReal hΩ : ℝ → ℂ) = Ω.indicator fun _ => (1 : ℂ) :=
  rfl

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)

/-! ### The spectral measure of a vector -/

/-- **The spectral measure `μ_ψ` of `ψ` for the self-adjoint operator `A`** (Reed–Simon I,
p. 263: `Ω ↦ (ψ, P_Ω ψ)`): the image of the spectral measure of `ψ` for `R = (A + i)⁻¹` under
`z ↦ (z⁻¹ - i).re`. -/
def saMeasure (ψ : H) : Measure ℝ :=
  (spectralMeasure (resolvent hA) ψ).map (spectrumToReal hA)

instance (ψ : H) : IsFiniteMeasure (saMeasure hA ψ) := by
  unfold saMeasure
  infer_instance

/-- `μ_ψ(Ω)` is the spectral measure of `ψ` for `R` of the preimage of `Ω`. -/
theorem saMeasure_apply (ψ : H) {Ω : Set ℝ} (hΩ : MeasurableSet Ω) :
    saMeasure hA ψ Ω = spectralMeasure (resolvent hA) ψ (spectrumToReal hA ⁻¹' Ω) :=
  Measure.map_apply (measurable_spectrumToReal hA) hΩ

/-- **Total mass**: `μ_ψ(ℝ) = ‖ψ‖²`. -/
theorem saMeasure_univ (ψ : H) : saMeasure hA ψ Set.univ = ‖ψ‖ₑ ^ 2 := by
  rw [saMeasure_apply hA ψ MeasurableSet.univ, Set.preimage_univ, spectralMeasure_univ,
    ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

/-- **Reed–Simon's (VIII.4)**: `(ψ, h(A) ψ) = ∫ h dμ_ψ` for bounded Borel `h : ℝ → ℂ`. -/
theorem inner_selfAdjointCalc (h : boundedMeasurable ℝ) (ψ : H) :
    ⟪ψ, selfAdjointCalc hA h ψ⟫_ℂ =
      ∫ x, (h : ℝ → ℂ) x ∂(saMeasure hA ψ) := by -- totalisation-audit: allow bounded measurable
  rw [selfAdjointCalc_def, inner_borelCalc_eq_integral, saMeasure,
    integral_map (measurable_spectrumToReal hA).aemeasurable
      (boundedMeasurable.measurable h).aestronglyMeasurable]
  rfl

/-- `(ψ, χ_Ω(A) ψ) = μ_ψ(Ω)`. -/
theorem inner_selfAdjointCalc_indicatorReal (ψ : H) {Ω : Set ℝ} (hΩ : MeasurableSet Ω) :
    ⟪ψ, selfAdjointCalc hA (indicatorReal hΩ) ψ⟫_ℂ = ((saMeasure hA ψ).real Ω : ℂ) := by
  rw [inner_selfAdjointCalc, coe_indicatorReal, integral_indicator_const _ hΩ, Complex.real_smul,
    mul_one]

/-! ### The spectral measure in the multiplication form -/

namespace CyclicDecomposition

variable {hA} (D : CyclicDecomposition (resolvent hA))

/-- The density `|U ψ|²` is measurable. -/
theorem measurable_enorm_sq (ψ : H) : Measurable fun p => ‖D.unitary ψ p‖ₑ ^ 2 :=
  (Lp.stronglyMeasurable (D.unitary ψ)).measurable.enorm.pow_const 2

/-- `(ψ, χ_Ω(A) ψ) = ∫_{f⁻¹ Ω} |U ψ|² dμ` in the multiplication form. -/
theorem inner_selfAdjointCalc_indicatorReal_eq (ψ : H) {Ω : Set ℝ} (hΩ : MeasurableSet Ω) :
    ⟪ψ, selfAdjointCalc hA (indicatorReal hΩ) ψ⟫_ℂ =
      ((∫ p, (D.realCoord ⁻¹' Ω).indicator -- totalisation-audit: allow L¹ as |U ψ|² ∈ L¹
        (fun p => ‖D.unitary ψ p‖ ^ 2) p ∂D.measure : ℝ) : ℂ) := by
  have hm : MemLp (fun p => (indicatorReal hΩ : ℝ → ℂ) (D.realCoord p)) ∞ D.measure :=
    memLp_top_comp D.measure D.measurable_snd
      (boundedMeasurable.comap (spectrumToReal hA) (measurable_spectrumToReal hA)
        (indicatorReal hΩ))
  have e : selfAdjointCalc hA (indicatorReal hΩ) ψ =
      D.unitary.symm (mulL _ hm (D.unitary ψ)) :=
    selfAdjointCalc_apply _ D _ _
  rw [e, ← LinearIsometryEquiv.inner_map_eq_flip, L2.inner_def]
  refine (integral_congr_ae ?_).trans integral_ofReal
  filter_upwards [coeFn_mulL hm (D.unitary ψ)] with p hp
  rw [hp, coe_indicatorReal]
  by_cases hx : D.realCoord p ∈ Ω
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (show p ∈ D.realCoord ⁻¹' Ω from hx),
      one_mul, inner_self_eq_norm_sq_to_K]
    push_cast
    rfl
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (show p ∉ D.realCoord ⁻¹' Ω from hx),
      zero_mul, inner_zero_right]
    simp

/-- **The spectral measure in the multiplication form**: `μ_ψ` is the image of `|U ψ|² μ` under
`f = λ⁻¹ - i`, for every cyclic decomposition.  Both sides give `(ψ, χ_Ω(A) ψ)` on a Borel set
`Ω`. -/
theorem saMeasure_eq (ψ : H) :
    saMeasure hA ψ =
      (D.measure.withDensity fun p => ‖D.unitary ψ p‖ₑ ^ 2).map D.realCoord := by
  refine Measure.ext fun Ω hΩ => ?_
  have hS : MeasurableSet (D.realCoord ⁻¹' Ω) := D.measurable_realCoord hΩ
  rw [Measure.map_apply D.measurable_realCoord hΩ, withDensity_apply _ hS]
  have h1 := (inner_selfAdjointCalc_indicatorReal hA ψ hΩ).symm.trans
    (D.inner_selfAdjointCalc_indicatorReal_eq ψ hΩ)
  have hnn : 0 ≤ᵐ[D.measure.restrict (D.realCoord ⁻¹' Ω)] fun p => ‖D.unitary ψ p‖ ^ 2 :=
    .of_forall fun p => by positivity
  rw [Complex.ofReal_inj, integral_indicator hS, integral_eq_lintegral_of_nonneg_ae hnn
    ((Lp.aestronglyMeasurable (D.unitary ψ)).norm.pow 2).restrict, measureReal_def] at h1
  have h2 : ∫⁻ p in D.realCoord ⁻¹' Ω, ENNReal.ofReal (‖D.unitary ψ p‖ ^ 2) ∂D.measure =
      ∫⁻ p in D.realCoord ⁻¹' Ω, ‖D.unitary ψ p‖ₑ ^ 2 ∂D.measure :=
    lintegral_congr fun p => by rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  have hfin : ∫⁻ p in D.realCoord ⁻¹' Ω, ‖D.unitary ψ p‖ₑ ^ 2 ∂D.measure ≠ ∞ :=
    ((setLIntegral_le_lintegral _ _).trans_lt (lintegral_enorm_sq_lt_top _)).ne
  rw [h2] at h1
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) hfin).1 h1

/-- The spectral measure in the multiplication form, integrated:
`∫⁻ G dμ_ψ = ∫⁻ |U ψ|² (G ∘ f) dμ` for measurable `G : ℝ → ℝ≥0∞`. -/
theorem lintegral_saMeasure (ψ : H) {G : ℝ → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ x, G x ∂(saMeasure hA ψ) =
      ∫⁻ p, ‖D.unitary ψ p‖ₑ ^ 2 * G (D.realCoord p) ∂D.measure := by
  rw [D.saMeasure_eq ψ, lintegral_map hG D.measurable_realCoord]
  exact lintegral_withDensity_eq_lintegral_mul _ (D.measurable_enorm_sq ψ)
    (hG.comp D.measurable_realCoord)

/-! ### `g(A)` in the multiplication form -/

/-- **`g(A)` in the multiplication form of a cyclic decomposition**: `U⁻¹ T_{g ∘ f} U`, with
`T_{g ∘ f}` multiplication by `g ∘ f` on its maximal domain (Reed–Simon I, p. 261). -/
def borelPMap (g : ℝ → ℂ) : H →ₗ.[ℂ] H :=
  unitaryConj D.unitary (mulPMap D.measure fun p => g (D.realCoord p))

/-- `g(A) ψ = U⁻¹ (T_{g ∘ f} (U ψ))`. -/
theorem borelPMap_apply (g : ℝ → ℂ) (ψ : (D.borelPMap g).domain) :
    D.borelPMap g ψ = D.unitary.symm
      (mulPMap D.measure (fun p => g (D.realCoord p)) ⟨D.unitary ψ, ψ.2⟩) :=
  rfl

/-- **The domain of `g(A)` is `D_g`** (Reed–Simon I, (VIII.5)): `ψ ∈ D(g(A))` iff
`∫ |g|² dμ_ψ < ∞`, i.e. `g ∈ L²(μ_ψ)`. -/
theorem mem_borelPMap_domain_iff {g : ℝ → ℂ} (hg : Measurable g) {ψ : H} :
    ψ ∈ (D.borelPMap g).domain ↔ MemLp g 2 (saMeasure hA ψ) := by
  rw [borelPMap, mem_unitaryConj_domain, mem_mulPMap_domain]
  have hF : AEStronglyMeasurable (fun p => g (D.realCoord p) * D.unitary ψ p) D.measure :=
    (hg.comp D.measurable_realCoord).aestronglyMeasurable.mul (Lp.aestronglyMeasurable _)
  rw [memLp_two_iff_lintegral_lt_top hF, memLp_two_iff_lintegral_lt_top hg.aestronglyMeasurable,
    D.lintegral_saMeasure ψ (hg.enorm.pow_const 2)]
  refine Iff.of_eq (congrArg (· < ∞) (lintegral_congr fun p => ?_))
  rw [enorm_mul, mul_pow, mul_comm]

/-- `‖g(A) ψ‖² = ∫ |g|² dμ_ψ` for `ψ ∈ D_g`, in the multiplication form. -/
theorem enorm_borelPMap_sq {g : ℝ → ℂ} (hg : Measurable g) (ψ : (D.borelPMap g).domain) :
    ‖D.borelPMap g ψ‖ₑ ^ 2 = ∫⁻ x, ‖g x‖ₑ ^ 2 ∂(saMeasure hA ψ) := by
  have hF : AEStronglyMeasurable (fun p => g (D.realCoord p) * D.unitary ψ p) D.measure :=
    (hg.comp D.measurable_realCoord).aestronglyMeasurable.mul (Lp.aestronglyMeasurable _)
  rw [borelPMap_apply, LinearIsometryEquiv.enorm_map, Lp.enorm_def,
    eLpNorm_congr_ae (coeFn_mulPMap _), eLpNorm_two_sq hF,
    D.lintegral_saMeasure ψ (hg.enorm.pow_const 2)]
  refine lintegral_congr fun p => ?_
  rw [enorm_mul, mul_pow, mul_comm]

end CyclicDecomposition

/-! ### Truncations -/

/-- The truncation `gₙ = g · 1_{‖g‖ ≤ n}` of a measurable `g : ℝ → ℂ`, a bounded measurable
function. -/
def borelTrunc {g : ℝ → ℂ} (hg : Measurable g) (n : ℕ) : boundedMeasurable ℝ :=
  ⟨{x | ‖g x‖ ≤ n}.indicator g, hg.indicator (measurableSet_le hg.norm measurable_const), n,
    fun x => by
      by_cases hx : ‖g x‖ ≤ n
      · rw [Set.indicator_of_mem (show x ∈ {x | ‖g x‖ ≤ n} from hx)]
        exact hx
      · rw [Set.indicator_of_notMem (show x ∉ {x | ‖g x‖ ≤ n} from hx), norm_zero]
        exact Nat.cast_nonneg n⟩

/-- `gₙ` as a function. -/
theorem coe_borelTrunc {g : ℝ → ℂ} (hg : Measurable g) (n : ℕ) :
    (borelTrunc hg n : ℝ → ℂ) = {x | ‖g x‖ ≤ n}.indicator g :=
  rfl

/-- `‖gₙ‖ ≤ ‖g‖` pointwise. -/
theorem norm_borelTrunc_le {g : ℝ → ℂ} (hg : Measurable g) (n : ℕ) (x : ℝ) :
    ‖(borelTrunc hg n : ℝ → ℂ) x‖ ≤ ‖g x‖ := by
  rw [coe_borelTrunc]
  exact norm_indicator_le_norm_self _ _

/-- `gₙ → g` pointwise (the sequence is eventually constant). -/
theorem tendsto_borelTrunc {g : ℝ → ℂ} (hg : Measurable g) (x : ℝ) :
    Tendsto (fun n => (borelTrunc hg n : ℝ → ℂ) x) atTop (𝓝 (g x)) := by
  obtain ⟨N, hN⟩ := exists_nat_ge ‖g x‖
  refine tendsto_const_nhds.congr' (eventually_atTop.2 ⟨N, fun n hn => ?_⟩)
  change g x = {x | ‖g x‖ ≤ n}.indicator g x
  rw [Set.indicator_of_mem]
  exact hN.trans (Nat.cast_le.2 hn)

namespace CyclicDecomposition

variable {hA} (D : CyclicDecomposition (resolvent hA))

/-- **Truncation limit**: `gₙ(A) ψ → g(A) ψ` for `ψ ∈ D_g`, by dominated convergence in
`L²(μ)` (`tendsto_mulL_apply_mulPMap`). -/
theorem tendsto_trunc_borelPMap {g : ℝ → ℂ} (hg : Measurable g)
    (ψ : (D.borelPMap g).domain) :
    Tendsto (fun n => selfAdjointCalc hA (borelTrunc hg n) ψ) atTop (𝓝 (D.borelPMap g ψ)) := by
  have hF : ∀ n : ℕ, MemLp (fun p => (borelTrunc hg n : ℝ → ℂ) (D.realCoord p)) ∞ D.measure :=
    fun n => memLp_top_comp D.measure D.measurable_snd
      (boundedMeasurable.comap (spectrumToReal hA) (measurable_spectrumToReal hA)
        (borelTrunc hg n))
  have e : ∀ n : ℕ, selfAdjointCalc hA (borelTrunc hg n) ψ =
      D.unitary.symm (mulL _ (hF n) (D.unitary ψ)) :=
    fun n => selfAdjointCalc_apply _ D _ _
  have h := tendsto_mulL_apply_mulPMap (F := fun n p => (borelTrunc hg n : ℝ → ℂ) (D.realCoord p))
    (f := fun p => g (D.realCoord p)) hF
    (fun n => .of_forall fun p => norm_borelTrunc_le hg n _)
    (.of_forall fun p => tendsto_borelTrunc hg _) ⟨D.unitary ψ, ψ.2⟩
  exact (((D.unitary.symm.continuous.tendsto _).comp h).congr fun n => (e n).symm)

/-- **Independence of the decomposition**: for measurable `g`, `U⁻¹ T_{g ∘ f} U` is the same
operator for any two cyclic decompositions: the domains are both `D_g`, and the values are both
limits of `gₙ(A) ψ`. -/
theorem borelPMap_eq {g : ℝ → ℂ} (hg : Measurable g) (D' : CyclicDecomposition (resolvent hA)) :
    D.borelPMap g = D'.borelPMap g := by
  refine LinearPMap.ext ?_ fun ψ h h' => ?_
  · ext ψ
    rw [D.mem_borelPMap_domain_iff hg, D'.mem_borelPMap_domain_iff hg]
  · exact tendsto_nhds_unique (D.tendsto_trunc_borelPMap hg ⟨ψ, h⟩)
      (D'.tendsto_trunc_borelPMap hg ⟨ψ, h'⟩)

end CyclicDecomposition

/-! ### The operator `g(A)` -/

/-- **The operator `g(A) = ∫ g(λ) dP_λ`** for a Borel function `g : ℝ → ℂ` (Reed–Simon I,
pp. 263–264), with domain `D_g`: `U⁻¹ T_{g ∘ f} U` for a chosen cyclic decomposition of
`(A + i)⁻¹`.  By `CyclicDecomposition.borelPMap_eq`, the choice does not matter when `g` is
measurable (`borelPMap_eq`). -/
def borelPMap (g : ℝ → ℂ) : H →ₗ.[ℂ] H :=
  (CyclicDecomposition.nonempty (resolvent hA)).some.borelPMap g

/-- `g(A)` is `U⁻¹ T_{g ∘ f} U` for every cyclic decomposition. -/
theorem borelPMap_eq (D : CyclicDecomposition (resolvent hA)) {g : ℝ → ℂ} (hg : Measurable g) :
    borelPMap hA g = D.borelPMap g :=
  CyclicDecomposition.borelPMap_eq _ hg D

/-- **The domain of `g(A)` is `D_g = {ψ | ∫ |g|² dμ_ψ < ∞}`** (Reed–Simon I, (VIII.5)). -/
theorem mem_borelPMap_domain {g : ℝ → ℂ} (hg : Measurable g) {ψ : H} :
    ψ ∈ (borelPMap hA g).domain ↔ MemLp g 2 (saMeasure hA ψ) :=
  CyclicDecomposition.mem_borelPMap_domain_iff _ hg

/-- `gₙ(A) ψ → g(A) ψ` for `ψ ∈ D_g`, with the truncations `gₙ = g · 1_{‖g‖ ≤ n}`. -/
theorem tendsto_trunc_borelPMap {g : ℝ → ℂ} (hg : Measurable g) (ψ : (borelPMap hA g).domain) :
    Tendsto (fun n => selfAdjointCalc hA (borelTrunc hg n) ψ) atTop (𝓝 (borelPMap hA g ψ)) :=
  CyclicDecomposition.tendsto_trunc_borelPMap _ hg ψ

/-- `‖g(A) ψ‖² = ∫ |g|² dμ_ψ` for `ψ ∈ D_g`. -/
theorem enorm_borelPMap_sq {g : ℝ → ℂ} (hg : Measurable g) (ψ : (borelPMap hA g).domain) :
    ‖borelPMap hA g ψ‖ₑ ^ 2 = ∫⁻ x, ‖g x‖ₑ ^ 2 ∂(saMeasure hA ψ) :=
  CyclicDecomposition.enorm_borelPMap_sq _ hg ψ

/-- **`D_g` is dense** (Reed–Simon I, p. 263). -/
theorem dense_borelPMap_domain {g : ℝ → ℂ} (hg : Measurable g) :
    Dense ((borelPMap hA g).domain : Set H) :=
  dense_unitaryConj_domain _ _ (dense_mulPMap_domain
    (hg.comp (CyclicDecomposition.measurable_realCoord _)).aestronglyMeasurable)

/-- **Reed–Simon's defining formula** (p. 263): `(ψ, g(A) ψ) = ∫ g dμ_ψ` for `ψ ∈ D_g`.  Here
`g ∈ L²(μ_ψ) ⊆ L¹(μ_ψ)`, as `μ_ψ` is finite; the formula follows from `(ψ, gₙ(A) ψ) = ∫ gₙ dμ_ψ`
by dominated convergence. -/
theorem inner_borelPMap {g : ℝ → ℂ} (hg : Measurable g) (ψ : (borelPMap hA g).domain) :
    ⟪(ψ : H), borelPMap hA g ψ⟫_ℂ =
      ∫ x, g x ∂(saMeasure hA ψ) := by -- totalisation-audit: allow g ∈ L² ⊆ L¹, finite measure
  have hint : Integrable g (saMeasure hA ψ) :=
    ((mem_borelPMap_domain hA hg).1 ψ.2).integrable one_le_two
  have h1 : Tendsto (fun n => ⟪(ψ : H), selfAdjointCalc hA (borelTrunc hg n) ψ⟫_ℂ) atTop
      (𝓝 ⟪(ψ : H), borelPMap hA g ψ⟫_ℂ) :=
    ((continuous_const.inner continuous_id).tendsto _).comp (tendsto_trunc_borelPMap hA hg ψ)
  have h2 : Tendsto (fun n => ∫ x, -- totalisation-audit: allow bounded measurable
      (borelTrunc hg n : ℝ → ℂ) x ∂(saMeasure hA ψ)) atTop
      (𝓝 (∫ x, g x ∂(saMeasure hA ψ))) := -- totalisation-audit: allow g ∈ L¹
    tendsto_integral_of_dominated_convergence (fun x => ‖g x‖)
      (fun n => (boundedMeasurable.measurable _).aestronglyMeasurable) hint.norm
      (fun n => .of_forall (norm_borelTrunc_le hg n)) (.of_forall (tendsto_borelTrunc hg))
  exact tendsto_nhds_unique h1 (h2.congr fun n => (inner_selfAdjointCalc hA _ ψ).symm)

/-- **`g(A)` is determined by Reed–Simon's defining formula** (p. 263): an operator `T` with
domain `D_g` and `(ψ, T ψ) = ∫ g dμ_ψ` for every `ψ ∈ D_g` is `g(A)` (by polarization, as
`D_g` is dense). -/
theorem eq_borelPMap_of_inner {g : ℝ → ℂ} (hg : Measurable g) {T : H →ₗ.[ℂ] H}
    (hdom : ∀ ψ, ψ ∈ T.domain ↔ MemLp g 2 (saMeasure hA ψ))
    (h : ∀ ψ : T.domain, ⟪(ψ : H), T ψ⟫_ℂ =
      ∫ x, g x ∂(saMeasure hA ψ)) : -- totalisation-audit: allow g ∈ L² ⊆ L¹, finite measure
    T = borelPMap hA g := by
  have hdom' : T.domain = (borelPMap hA g).domain := by
    ext ψ
    rw [hdom, mem_borelPMap_domain hA hg]
  have hd : Dense (T.domain : Set H) := by
    rw [hdom']
    exact dense_borelPMap_domain hA hg
  refine eq_of_inner_self_eq hdom' hd fun ψ h₁ h₂ => ?_
  rw [h ⟨ψ, h₁⟩, inner_borelPMap hA hg ⟨ψ, h₂⟩]

/-- **The adjoint of `g(A)`**: `g(A)† = ḡ(A)`. -/
theorem adjoint_borelPMap {g : ℝ → ℂ} (hg : Measurable g) :
    (borelPMap hA g)† = borelPMap hA (star g) := by
  have hm : Measurable fun p =>
      g ((CyclicDecomposition.nonempty (resolvent hA)).some.realCoord p) :=
    hg.comp (CyclicDecomposition.measurable_realCoord _)
  rw [borelPMap, CyclicDecomposition.borelPMap,
    adjoint_unitaryConj _ _ (dense_mulPMap_domain hm.aestronglyMeasurable),
    adjoint_mulPMap hm.aestronglyMeasurable]
  rfl

/-- **Reed–Simon I, Theorem VIII.6** (second part, p. 264): if `g` is a real-valued Borel
function on `ℝ`, then `g(A) = ∫ g(λ) dP_λ`, defined on `D_g`, is self-adjoint. -/
theorem isSelfAdjoint_borelPMap {r : ℝ → ℝ} (hr : Measurable r) :
    IsSelfAdjoint (borelPMap hA fun x => (r x : ℂ)) :=
  isSelfAdjoint_unitaryConj _ _ (isSelfAdjoint_mulPMap_ofReal
    (r := fun p => r (CyclicDecomposition.realCoord
      (CyclicDecomposition.nonempty (resolvent hA)).some p))
    (hr.comp (CyclicDecomposition.measurable_realCoord _)).aestronglyMeasurable)

/-- **Bounded `g`** (Reed–Simon I, p. 264): if `h` is a bounded Borel function, `h(A)` is the
everywhere defined operator `φ̂(h) = selfAdjointCalc hA h` of Theorem VIII.5. -/
theorem borelPMap_bounded (h : boundedMeasurable ℝ) :
    borelPMap hA (h : ℝ → ℂ) = ((selfAdjointCalc hA h : H →L[ℂ] H) : H →ₗ[ℂ] H).toPMap ⊤ := by
  obtain ⟨D⟩ := CyclicDecomposition.nonempty (resolvent hA)
  have hm : MemLp (fun p => (h : ℝ → ℂ) (D.realCoord p)) ∞ D.measure :=
    memLp_top_comp D.measure D.measurable_snd
      (boundedMeasurable.comap (spectrumToReal hA) (measurable_spectrumToReal hA) h)
  rw [borelPMap_eq hA D (boundedMeasurable.measurable h), CyclicDecomposition.borelPMap,
    mulPMap_eq_toPMap_mulL hm]
  exact unitaryConj_toPMap _ _ _ fun ψ => selfAdjointCalc_apply _ D h ψ

/-- **`A = ∫ λ dP_λ`** (Reed–Simon I, p. 263): `g(A) = A` for `g(x) = x`, by Theorem VIII.4:
`D(A) = {ψ | f · U ψ ∈ L²}` and `U A U⁻¹ = T_f`. -/
theorem borelPMap_id : borelPMap hA (fun x => (x : ℂ)) = A := by
  obtain ⟨D⟩ := CyclicDecomposition.nonempty (resolvent hA)
  rw [borelPMap_eq hA D Complex.measurable_ofReal]
  refine LinearPMap.ext ?_ fun ψ h h' => ?_
  · ext ψ
    exact (D.mem_domain_iff ψ).symm
  · change D.unitary.symm (mulPMap D.measure (fun p => (D.realCoord p : ℂ)) ⟨D.unitary ψ, h⟩) =
      A ⟨ψ, h'⟩
    rw [← D.unitary_apply_selfAdjoint ψ h', LinearIsometryEquiv.symm_apply_apply]

/-- **The domain of `A`**: `ψ ∈ D(A)` iff `∫ λ² dμ_ψ < ∞`. -/
theorem mem_domain_iff_memLp {ψ : H} :
    ψ ∈ A.domain ↔ MemLp (fun x : ℝ => (x : ℂ)) 2 (saMeasure hA ψ) := by
  conv_lhs => rw [← borelPMap_id hA]
  exact mem_borelPMap_domain hA Complex.measurable_ofReal

/-- **`(ψ, A ψ) = ∫ λ dμ_ψ`** for `ψ ∈ D(A)` (Reed–Simon I, p. 263). -/
theorem inner_self_selfAdjoint {ψ : H} (hψ : ψ ∈ A.domain) :
    ⟪ψ, A ⟨ψ, hψ⟩⟫_ℂ =
      ∫ x, (x : ℂ) ∂(saMeasure hA ψ) := by -- totalisation-audit: allow λ ∈ L² ⊆ L¹ on D(A)
  have key : ∀ (T : H →ₗ.[ℂ] H) (_ : T = A) (h1 : ψ ∈ T.domain), T ⟨ψ, h1⟩ = A ⟨ψ, hψ⟩ := by
    rintro T rfl h1
    rfl
  have h1 : ψ ∈ (borelPMap hA fun x => (x : ℂ)).domain := by
    rw [borelPMap_id hA]
    exact hψ
  rw [← key _ (borelPMap_id hA) h1]
  exact inner_borelPMap hA Complex.measurable_ofReal ⟨ψ, h1⟩

end SpectralTheorem
