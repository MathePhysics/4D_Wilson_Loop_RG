import SpectralTheorem.PVMUnbounded

/-!
# The spectral theorem for self-adjoint operators, projection-valued measure form

**Reed–Simon I, Theorem VIII.6, p. 263.**  "There is a one-to-one correspondence between
self-adjoint operators `A` and projection-valued measures `{P_Ω}` on `H`, the correspondence
being given by `A = ∫ λ dP_λ`.  If `g(·)` is a real-valued Borel function on `ℝ`, then
`g(A) = ∫ g(λ) dP_λ` defined on `D_g` (VIII.5) is self-adjoint.  If `g` is bounded, `g(A)`
coincides with `φ̂(g)` in Theorem VIII.5."

Here, for self-adjoint `A`, `P_Ω = χ_Ω(A)` (Reed–Simon I, p. 262), with
`χ_Ω(A) = selfAdjointCalc hA χ_Ω` the functional calculus of Theorem VIII.5.

Proof.
* **`P_Ω` is a projection-valued measure**: `χ_Ω` is a self-adjoint idempotent and
  `selfAdjointCalc hA` a `⋆`-homomorphism (a); `χ_∅ = 0`, `χ_ℝ = 1` (b); for pairwise disjoint
  `Ωₙ` the partial sums `Σ_{n<N} χ_{Ωₙ} = χ_{⋃_{n<N} Ωₙ}` converge pointwise and boundedly to
  `χ_{⋃ Ωₙ}`, so (d) of Theorem VIII.5 gives (c).
* **Measures**: `⟪ψ, P_Ω ψ⟫ = μ_ψ(Ω)` for both `P.measure ψ` and the spectral measure
  `saMeasure hA ψ`, so they agree; hence `∫ h dP = h(A)` for bounded `h` (both have the quadratic
  form `ψ ↦ ∫ h dμ_ψ`), and `∫ g dP = g(A) = borelPMap hA g` for measurable `g` (same domain `D_g`
  and same quadratic form, `eq_borelPMap_of_inner`).  In particular `∫ λ dP_λ = A`.
* **The inverse map**: for a projection-valued measure `P` on `ℝ`, `A_P = ∫ λ dP_λ` is
  self-adjoint (`ProjectionValuedMeasure.isSelfAdjoint_integralPMap`).  The map
  `h ↦ ∫ h dP` has properties (b)–(d) of Theorem VIII.5 for `A_P` ((c): for `hₙ(x) → x` with
  `|hₙ(x)| ≤ |x|`, `(∫ hₙ dP) ψ → A_P ψ` by dominated convergence with the bound `|x| ∈ L²(μ_ψ)`),
  so it is `selfAdjointCalc` of `A_P` by the uniqueness in Theorem VIII.5.  Evaluating at
  indicators, the projection-valued measure of `A_P` is `P`.

## Main definitions and results

* `SpectralTheorem.pvm hA`: the projection-valued measure `Ω ↦ χ_Ω(A)`, with `pvm_apply`.
* `SpectralTheorem.measure_pvm`: `(pvm hA).measure ψ = saMeasure hA ψ`.
* `SpectralTheorem.integral_pvm`: `(pvm hA).integral = selfAdjointCalc hA` ((VIII.4) coincides
  with Theorem VIII.4/VIII.5).
* `SpectralTheorem.integralPMap_pvm`: `∫ g d(pvm hA) = borelPMap hA g`; `integralPMap_pvm_id`:
  `∫ λ d(pvm hA) = A`.
* `ProjectionValuedMeasure.selfAdjointOp P`: `∫ λ dP_λ`, self-adjoint, with
  `mem_selfAdjointOp_domain`, `inner_selfAdjointOp`; `pvm_selfAdjointOp`: the projection-valued
  measure of `∫ λ dP_λ` is `P`.
* `SpectralTheorem.selfAdjointEquivPVM`: **Reed–Simon I, Theorem VIII.6**, the bijection between
  self-adjoint operators and projection-valued measures on `ℝ`; `existsUnique_selfAdjointOp_eq`:
  `pvm hA` is the only `P` with `∫ λ dP_λ = A`.
* `SpectralTheorem.isSelfAdjoint_integralPMap_pvm`, `integralPMap_pvm_bounded`: the remaining
  statements of Theorem VIII.6.
-/

noncomputable section

open scoped InnerProductSpace ENNReal Topology
open MeasureTheory Filter Set

namespace SpectralTheorem

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### Indicators -/

/-- `χ_Ω` is a self-adjoint idempotent. -/
theorem isStarProjection_indicatorReal {Ω : Set ℝ} (hΩ : MeasurableSet Ω) :
    IsStarProjection (indicatorReal hΩ) := by
  refine ⟨Subtype.ext (funext fun x => ?_), Subtype.ext (funext fun x => ?_)⟩
  · change Ω.indicator (fun _ => (1 : ℂ)) x * Ω.indicator (fun _ => (1 : ℂ)) x =
      Ω.indicator (fun _ => (1 : ℂ)) x
    by_cases hx : x ∈ Ω <;> simp [hx]
  · change star (Ω.indicator (fun _ => (1 : ℂ)) x) = Ω.indicator (fun _ => (1 : ℂ)) x
    by_cases hx : x ∈ Ω <;> simp [hx]

/-- `Σ_{n<N} χ_{Ωₙ} = χ_{⋃_{n<N} Ωₙ}` for pairwise disjoint `Ωₙ`. -/
theorem coe_sum_indicatorReal {s : ℕ → Set ℝ} (hs : ∀ n, MeasurableSet (s n))
    (hd : Pairwise (Function.onFun Disjoint s)) (N : ℕ) (x : ℝ) :
    ((∑ n ∈ Finset.range N, indicatorReal (hs n) : boundedMeasurable ℝ) : ℝ → ℂ) x =
      (⋃ n ∈ Finset.range N, s n).indicator (fun _ => (1 : ℂ)) x := by
  rw [Finset.indicator_biUnion_apply _ _ (hd.set_pairwise _)]
  simp [coe_indicatorReal]

variable {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)

/-! ### The projection-valued measure of a self-adjoint operator -/

open Classical in
/-- `χ_Ω(A)` for Borel `Ω`, and `0` for the other sets. -/
def pvmFun (Ω : Set ℝ) : H →L[ℂ] H :=
  if hΩ : MeasurableSet Ω then selfAdjointCalc hA (indicatorReal hΩ) else 0

theorem pvmFun_of_measurableSet {Ω : Set ℝ} (hΩ : MeasurableSet Ω) :
    pvmFun hA Ω = selfAdjointCalc hA (indicatorReal hΩ) := by
  simp [pvmFun, hΩ]

/-- **The projection-valued measure of a self-adjoint operator `A`** (Reed–Simon I, pp. 262–263):
`P_Ω = χ_Ω(A)` for Borel sets `Ω`.  Properties (a)–(c) follow from Theorem VIII.5 (a), (d). -/
def pvm : ProjectionValuedMeasure ℝ H where
  toFun := pvmFun hA
  isStarProjection' Ω hΩ := by
    rw [pvmFun_of_measurableSet hA hΩ]
    exact (isStarProjection_indicatorReal hΩ).map (selfAdjointCalc hA)
  empty' := by
    rw [pvmFun_of_measurableSet hA MeasurableSet.empty]
    have h : indicatorReal (MeasurableSet.empty : MeasurableSet (∅ : Set ℝ)) = 0 :=
      Subtype.ext (funext fun x => by simp [coe_indicatorReal])
    rw [h, map_zero]
  univ' := by
    rw [pvmFun_of_measurableSet hA MeasurableSet.univ]
    have h : indicatorReal (MeasurableSet.univ : MeasurableSet (univ : Set ℝ)) = 1 :=
      Subtype.ext (funext fun x => by simp [coe_indicatorReal])
    rw [h, map_one]
  tendsto_sum' s hs hd ψ := by
    have e : ∀ n, pvmFun hA (s n) = selfAdjointCalc hA (indicatorReal (hs n)) := fun n =>
      pvmFun_of_measurableSet hA (hs n)
    have hU : MeasurableSet (⋃ n, s n) := MeasurableSet.iUnion hs
    simp only [e, pvmFun_of_measurableSet hA hU]
    have hb : ∀ (N : ℕ) x,
        ‖((∑ n ∈ Finset.range N, indicatorReal (hs n) : boundedMeasurable ℝ) : ℝ → ℂ) x‖ ≤ 1 :=
      fun N x => by
        rw [coe_sum_indicatorReal hs hd]
        by_cases hx : x ∈ ⋃ n ∈ Finset.range N, s n
        · rw [Set.indicator_of_mem hx, norm_one]
        · rw [Set.indicator_of_notMem hx, norm_zero]
          exact zero_le_one
    have hl : ∀ x, Tendsto (fun N =>
        ((∑ n ∈ Finset.range N, indicatorReal (hs n) : boundedMeasurable ℝ) : ℝ → ℂ) x) atTop
        (𝓝 ((indicatorReal hU : ℝ → ℂ) x)) := fun x => by
      simp only [coe_sum_indicatorReal hs hd, coe_indicatorReal]
      exact ((tendsto_indicator_biUnion_finset s _ x).comp tendsto_finset_range).mono_right
        (pure_le_nhds _)
    have h := tendsto_selfAdjointCalc_apply hA _ _ 1 hb hl ψ
    simpa [map_sum] using h
  apply_of_not_measurableSet' Ω hΩ := by
    simp [pvmFun, hΩ]

/-- `P_Ω = χ_Ω(A)` for Borel `Ω`. -/
theorem pvm_apply {Ω : Set ℝ} (hΩ : MeasurableSet Ω) :
    pvm hA Ω = selfAdjointCalc hA (indicatorReal hΩ) :=
  pvmFun_of_measurableSet hA hΩ

/-- **The measures of `pvm hA` are the spectral measures**: `(pvm hA).measure ψ = μ_ψ`, as both
give `⟪ψ, χ_Ω(A) ψ⟫` on Borel sets `Ω`. -/
theorem measure_pvm (ψ : H) : (pvm hA).measure ψ = saMeasure hA ψ := by
  refine Measure.ext fun Ω hΩ => ?_
  have h1 := (pvm hA).inner_apply_eq_measureReal ψ hΩ
  rw [pvm_apply hA hΩ, inner_selfAdjointCalc_indicatorReal, Complex.ofReal_inj, measureReal_def,
    measureReal_def] at h1
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1 h1.symm

/-- **`∫ h dP = h(A)`** for bounded Borel `h` (Reed–Simon I, p. 263: "`g(A)` as defined by
(VIII.4) coincides with the definition of `g(A)` given by Theorem VIII.4"): both operators have
the quadratic form `ψ ↦ ∫ h dμ_ψ`. -/
theorem integral_pvm : (pvm hA).integral = selfAdjointCalc hA :=
  StarAlgHom.ext fun h => ext_inner_self fun ψ => by
    rw [ProjectionValuedMeasure.inner_integral, measure_pvm, inner_selfAdjointCalc]

/-- **`∫ g d(pvm hA) = g(A)`** for measurable `g : ℝ → ℂ`: both have the domain `D_g` and the
quadratic form `ψ ↦ ∫ g dμ_ψ` (`eq_borelPMap_of_inner`). -/
theorem integralPMap_pvm {g : ℝ → ℂ} (hg : Measurable g) :
    (pvm hA).integralPMap hg = borelPMap hA g :=
  eq_borelPMap_of_inner hA hg
    (fun ψ => by rw [ProjectionValuedMeasure.mem_integralPMap_domain, measure_pvm])
    fun ψ => by rw [ProjectionValuedMeasure.inner_integralPMap, measure_pvm]

/-- **`A = ∫ λ dP_λ`** for `P = pvm hA` (Reed–Simon I, p. 263). -/
theorem integralPMap_pvm_id :
    (pvm hA).integralPMap (g := fun x : ℝ => (x : ℂ)) Complex.measurable_ofReal = A := by
  rw [integralPMap_pvm]
  exact borelPMap_id hA

/-! ### From a projection-valued measure to a self-adjoint operator -/

namespace ProjectionValuedMeasure

variable (P : ProjectionValuedMeasure ℝ H)

/-- **The operator `∫ λ dP_λ`** of a projection-valued measure `P` on `ℝ`, with domain
`{ψ | ∫ λ² dμ_ψ < ∞}`. -/
def selfAdjointOp : H →ₗ.[ℂ] H :=
  P.integralPMap (g := fun x : ℝ => (x : ℂ)) Complex.measurable_ofReal

/-- The domain of `∫ λ dP_λ` is `{ψ | ∫ λ² dμ_ψ < ∞}`. -/
theorem mem_selfAdjointOp_domain {ψ : H} :
    ψ ∈ P.selfAdjointOp.domain ↔ MemLp (fun x : ℝ => (x : ℂ)) 2 (P.measure ψ) :=
  Iff.rfl

/-- `(ψ, (∫ λ dP_λ) ψ) = ∫ λ dμ_ψ` on the domain. -/
theorem inner_selfAdjointOp (ψ : P.selfAdjointOp.domain) :
    ⟪(ψ : H), P.selfAdjointOp ψ⟫_ℂ =
      ∫ x : ℝ, (x : ℂ) ∂(P.measure ψ) := -- totalisation-audit: allow λ ∈ L² ⊆ L¹ on the domain
  P.inner_integralPMap Complex.measurable_ofReal ψ

/-- `∫ λ dP_λ` is self-adjoint. -/
theorem isSelfAdjoint_selfAdjointOp : IsSelfAdjoint P.selfAdjointOp :=
  P.isSelfAdjoint_integralPMap (r := fun x => x) Complex.measurable_ofReal

/-- `h ↦ ∫ h dP` has properties (b)–(d) of Theorem VIII.5 for `∫ λ dP_λ`.  For (c):
`(∫ hₙ dP) ψ → (∫ λ dP_λ) ψ` if `hₙ(x) → x` and `|hₙ(x)| ≤ |x|`, by dominated convergence with
the bound `|x| ∈ L²(μ_ψ)` for `ψ` in the domain. -/
theorem isSelfAdjointCalculus_integral :
    IsSelfAdjointCalculus P.isSelfAdjoint_selfAdjointOp P.integral where
  norm_le h _ hC0 hC := P.norm_integral_le h hC0 hC
  tendsto_self h hb hl ψ hψ := by
    have hG : MemLp (fun x : ℝ => |x|) 2 (P.measure ψ) :=
      ((P.mem_integralPMap_domain Complex.measurable_ofReal).1 hψ).congr_norm
        continuous_abs.measurable.aestronglyMeasurable (Eventually.of_forall fun x => by simp)
    exact P.tendsto_integral_integralPMap Complex.measurable_ofReal h ⟨ψ, hψ⟩ hG hb hl
  tendsto h h₀ C hC hl ψ := P.tendsto_integral_apply h h₀ C hC hl ψ

/-- `∫ h dP = h(∫ λ dP_λ)` for bounded Borel `h`, by the uniqueness in Theorem VIII.5. -/
theorem integral_eq_selfAdjointCalc :
    P.integral = selfAdjointCalc P.isSelfAdjoint_selfAdjointOp :=
  P.isSelfAdjointCalculus_integral.eq_selfAdjointCalc

/-- **The projection-valued measure of `∫ λ dP_λ` is `P`**: `χ_Ω(∫ λ dP_λ) = ∫ χ_Ω dP = P_Ω`. -/
theorem pvm_selfAdjointOp : pvm P.isSelfAdjoint_selfAdjointOp = P := by
  refine ProjectionValuedMeasure.ext fun Ω hΩ => ?_
  rw [pvm_apply _ hΩ, ← P.integral_eq_selfAdjointCalc, ← P.integral_indicator hΩ]
  rfl

end ProjectionValuedMeasure

/-- `∫ λ d(pvm hA) = A`. -/
theorem selfAdjointOp_pvm : (pvm hA).selfAdjointOp = A :=
  integralPMap_pvm_id hA

/-- **Reed–Simon I, Theorem VIII.6, p. 263** (first part): there is a one-to-one correspondence
between self-adjoint operators `A` and projection-valued measures `P` on `ℝ`, given by
`A = ∫ λ dP_λ`.  The map `A ↦ P` is `Ω ↦ χ_Ω(A)`. -/
def selfAdjointEquivPVM : {A : H →ₗ.[ℂ] H // IsSelfAdjoint A} ≃ ProjectionValuedMeasure ℝ H where
  toFun A := pvm A.2
  invFun P := ⟨P.selfAdjointOp, P.isSelfAdjoint_selfAdjointOp⟩
  left_inv A := Subtype.ext (selfAdjointOp_pvm A.2)
  right_inv P := P.pvm_selfAdjointOp

@[simp]
theorem selfAdjointEquivPVM_apply (A : {A : H →ₗ.[ℂ] H // IsSelfAdjoint A}) :
    selfAdjointEquivPVM A = pvm A.2 :=
  rfl

@[simp]
theorem selfAdjointEquivPVM_symm_apply (P : ProjectionValuedMeasure ℝ H) :
    (selfAdjointEquivPVM.symm P : H →ₗ.[ℂ] H) = P.selfAdjointOp :=
  rfl

include hA in
/-- **Theorem VIII.6**, existence and uniqueness form: a self-adjoint `A` is `∫ λ dP_λ` for exactly
one projection-valued measure `P` on `ℝ`, namely `pvm hA`. -/
theorem existsUnique_selfAdjointOp_eq :
    ∃! P : ProjectionValuedMeasure ℝ H, P.selfAdjointOp = A := by
  refine ⟨pvm hA, selfAdjointOp_pvm hA, fun P hP => ?_⟩
  have h : selfAdjointEquivPVM.symm P = ⟨A, hA⟩ := Subtype.ext hP
  rw [← selfAdjointEquivPVM.apply_symm_apply P, h]
  rfl

/-! ### Functions of `A` -/

/-- **Reed–Simon I, Theorem VIII.6** (second part): for a real-valued Borel function `r`,
`r(A) = ∫ r(λ) dP_λ`, defined on `D_r`, is self-adjoint. -/
theorem isSelfAdjoint_integralPMap_pvm {r : ℝ → ℝ} (hr : Measurable fun x => (r x : ℂ)) :
    IsSelfAdjoint ((pvm hA).integralPMap hr) :=
  (pvm hA).isSelfAdjoint_integralPMap hr

/-- **Reed–Simon I, Theorem VIII.6** (third part): for bounded Borel `h`, `∫ h(λ) dP_λ` is the
everywhere defined operator `φ̂(h) = selfAdjointCalc hA h` of Theorem VIII.5. -/
theorem integralPMap_pvm_bounded (h : boundedMeasurable ℝ) :
    (pvm hA).integralPMap (boundedMeasurable.measurable h) =
      ((selfAdjointCalc hA h : H →L[ℂ] H) : H →ₗ[ℂ] H).toPMap ⊤ := by
  rw [ProjectionValuedMeasure.integralPMap_bounded, integral_pvm]

end SpectralTheorem
