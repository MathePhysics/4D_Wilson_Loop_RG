import SpectralTheorem.RepDecomposition
import SpectralTheorem.PVMIntegral
import Mathlib.Topology.MetricSpace.ThickenedIndicator

/-!
# The projection-valued measure of a representation of `C(X)`

Let `X` be a compact Hausdorff space with its Borel `σ`-algebra and
`π : C(X, ℂ) → 𝓛(H)` a unital `⋆`-homomorphism.  **Statement (R).**  There is a
projection-valued measure `P` on `X` with `π f = ∫ f dP` for all continuous `f`, whose measures
`μ_ψ(Ω) = ⟪ψ, P_Ω ψ⟫` are regular; it is unique among p.v.m.'s with regular measures, and unique
outright when `X` is metrizable.  Every `P_Ω` commutes with every operator commuting with all
`π f`.  Conversely every p.v.m. `P` gives a representation `f ↦ ∫ f dP`, and the two
constructions are inverse bijections between representations and regular p.v.m.'s (all p.v.m.'s
when `X` is metrizable).

This is Reed–Simon I, Theorem VII.8 (p. 235; p.v.m.'s as defined on pp. 234–235), with the
continuous functional calculus of one operator replaced by a representation of `C(X)`, as in
Rudin, *Functional Analysis*, Chapter 12.  It applies to the Gelfand spectrum of a
commutative `C⋆`-algebra of operators.

Proof sketch.
* **Existence.**  A cyclic decomposition (`SpectralTheorem.RepDecomposition`) gives a unitary
  `U : H ≃ L²(M, μ)`, `M = Σ_ψ X`, and `F(ψ, x) = x` with `U π(f) U⁻¹ = M_{f ∘ F}`.  The map
  `Φ(g) = U⁻¹ M_{g ∘ F} U` on bounded Borel functions is a `⋆`-homomorphism taking bounded
  pointwise convergence to strong convergence (dominated convergence), so `P_Ω = Φ(1_Ω)` is a
  p.v.m. (`pvmOfHom`), with `∫ g dP = Φ(g)` (`ProjectionValuedMeasure.eq_integral_of_indicator`)
  and hence `∫ f dP = π(f)` for continuous `f`.
* **Regularity.**  `μ_ψ(Ω) = ‖M_{1_Ω ∘ F} U ψ‖² = Σ_φ ∫_Ω |U ψ(φ, ·)|² dμ_φ` is a sum of
  measures with integrable densities with respect to the regular spectral measures `μ_φ`; these
  are inner regular by absolute continuity of the integral, so is their sum, and a finite inner
  regular measure on a compact Hausdorff space is regular.
* **Uniqueness.**  If `∫ f dP = π(f)` and `μ_ψ` is regular, then `μ_ψ` is the spectral measure
  of `ψ` (uniqueness in the Riesz–Markov–Kakutani theorem, `eq_repMeasure`), so
  `⟪ψ, P_Ω ψ⟫` is determined for all `ψ`, and so is `P_Ω`.  On a compact metrizable space every
  finite Borel measure is regular.
* **Commutant.**  For a unitary `W` commuting with all `π f`, `W⁻¹ P W` is a p.v.m. with the same
  integrals and regular measures `μ_{W ψ}`, so it is `P`.  For self-adjoint `A` commuting with all
  `π f`, the unitaries `exp(i t A)` do, and differentiating `exp(i t A) P_Ω = P_Ω exp(i t A)` at
  `t = 0` gives `A P_Ω = P_Ω A`.  A general operator is `Re B + i Im B`.  (A second proof for
  metrizable `X`, by a Dynkin argument from closed sets:
  `ProjectionValuedMeasure.commute_apply`.)

## Main definitions and results

* `SpectralTheorem.pvmOfHom`, `integral_pvmOfHom`: the p.v.m. `Ω ↦ Φ(1_Ω)` of a `⋆`-homomorphism
  on bounded Borel functions taking bounded pointwise to strong convergence, and `∫ g dP = Φ(g)`.
* `SpectralTheorem.ProjectionValuedMeasure.toRep`: the representation `f ↦ ∫ f dP` of `C(X)`.
* `SpectralTheorem.repPVM π`: the p.v.m. of `π`; `toRep_repPVM`, `integral_repPVM`:
  `π f = ∫ f dP`; `regular_repPVM_measure`: its measures are regular; `measure_repPVM`: they are
  the spectral measures `repMeasure π ψ`.
* `SpectralTheorem.eq_repPVM_of_regular`, `existsUnique_regular_pvm`: uniqueness among
  p.v.m.'s with regular measures; `ProjectionValuedMeasure.ext_of_toRep`.
* `SpectralTheorem.eq_repPVM`, `existsUnique_pvm_toRep_eq`: uniqueness for metrizable `X`.
* `SpectralTheorem.commute_repPVM`, `commute_integral_repPVM`: the commutant;
  `ProjectionValuedMeasure.commute_apply_of_regular` for any regular p.v.m.
* `SpectralTheorem.repPVMEquivRegular`: representations of `C(X)` `≃` regular p.v.m.'s on `X`;
  `SpectralTheorem.repPVMEquiv`: representations `≃` p.v.m.'s, for metrizable `X`.
-/

noncomputable section

open scoped InnerProductSpace ENNReal Topology NNReal
open MeasureTheory Filter Set

namespace SpectralTheorem

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### The projection-valued measure of a `σ`-normal `⋆`-homomorphism -/

section OfHom

variable {X : Type*} [MeasurableSpace X]

/-- A `⋆`-homomorphism `Φ` on bounded measurable functions **takes bounded pointwise
convergence to strong convergence**: if `fₙ → f₀` pointwise with `‖fₙ‖ ≤ C`, then
`Φ(fₙ) ψ → Φ(f₀) ψ` for every `ψ`. -/
def IsBoundedPointwiseStrong (Φ : boundedMeasurable X →⋆ₐ[ℂ] (H →L[ℂ] H)) : Prop :=
  ∀ (f : ℕ → boundedMeasurable X) (f₀ : boundedMeasurable X) (C : ℝ),
    (∀ n x, ‖(f n : X → ℂ) x‖ ≤ C) →
    (∀ x, Tendsto (fun n => (f n : X → ℂ) x) atTop (𝓝 ((f₀ : X → ℂ) x))) →
    ∀ ψ : H, Tendsto (fun n => Φ (f n) ψ) atTop (𝓝 (Φ f₀ ψ))

/-- The indicator of a measurable set is a projection in the `⋆`-algebra of bounded measurable
functions. -/
theorem boundedMeasurable.isStarProjection_indicator {s : Set X} (hs : MeasurableSet s) :
    IsStarProjection (boundedMeasurable.indicator hs) where
  isIdempotentElem := Subtype.ext (funext fun x => by
    by_cases hx : x ∈ s <;> simp [hx])
  isSelfAdjoint := Subtype.ext (funext fun x => by
    by_cases hx : x ∈ s <;> simp [hx])

variable (Φ : boundedMeasurable X →⋆ₐ[ℂ] (H →L[ℂ] H))

open Classical in
/-- **The projection-valued measure of a `⋆`-homomorphism** `Φ` on bounded measurable functions
taking bounded pointwise convergence to strong convergence: `P_s = Φ(1_s)` for measurable `s`
(and `0` on the other sets). -/
def pvmOfHom (hΦ : IsBoundedPointwiseStrong Φ) : ProjectionValuedMeasure X H where
  toFun s := if hs : MeasurableSet s then Φ (boundedMeasurable.indicator hs) else 0
  isStarProjection' s hs := by
    rw [dite_eq_left hs]
    exact (boundedMeasurable.isStarProjection_indicator hs).map Φ
  empty' := by
    rw [dite_eq_left MeasurableSet.empty]
    have h : boundedMeasurable.indicator (MeasurableSet.empty : MeasurableSet (∅ : Set X)) = 0 :=
      Subtype.ext (funext fun x => by simp)
    rw [h, map_zero]
  univ' := by
    rw [dite_eq_left MeasurableSet.univ, boundedMeasurable.indicator_univ, map_one]
  tendsto_sum' s hs hd ψ := by
    beta_reduce
    rw [dite_eq_left (MeasurableSet.iUnion hs)]
    have hsum : ∀ N, ∑ n ∈ Finset.range N,
        (if h : MeasurableSet (s n) then Φ (boundedMeasurable.indicator h) else 0) ψ =
        Φ (∑ n ∈ Finset.range N, boundedMeasurable.indicator (hs n)) ψ := fun N => by
      rw [map_sum, sum_apply]
      exact Finset.sum_congr rfl fun n _ => by rw [dite_eq_left (hs n)]
    simp only [hsum]
    have hcoe : ∀ N x, ((∑ n ∈ Finset.range N, boundedMeasurable.indicator (hs n) :
        boundedMeasurable X) : X → ℂ) x =
          ∑ n ∈ Finset.range N, (s n).indicator (fun _ => (1 : ℂ)) x := fun N x => by
      rw [AddSubmonoidClass.coe_finsetSum, Finset.sum_apply]
      rfl
    refine hΦ _ _ 1 (fun N x => ?_) (fun x => ?_) ψ
    · rw [hcoe]
      exact (sum_indicator_disjoint s hd x).1 N
    · simp only [hcoe]
      exact (sum_indicator_disjoint s hd x).2
  apply_of_not_measurableSet' s hs := dite_eq_right hs

variable (hΦ : IsBoundedPointwiseStrong Φ)

/-- `P_s = Φ(1_s)` for the p.v.m. of `Φ`. -/
theorem pvmOfHom_apply {s : Set X} (hs : MeasurableSet s) :
    pvmOfHom Φ hΦ s = Φ (boundedMeasurable.indicator hs) := by
  classical
  exact dite_eq_left hs

/-- **`∫ f dP = Φ(f)`** for the p.v.m. `P` of `Φ` and every bounded measurable `f`: both sides
are linear, agree on indicators and take bounded pointwise convergence to strong convergence
(`ProjectionValuedMeasure.eq_integral_of_indicator`). -/
theorem integral_pvmOfHom (f : boundedMeasurable X) :
    (pvmOfHom Φ hΦ).integral f = Φ f :=
  ((pvmOfHom Φ hΦ).eq_integral_of_indicator Φ.toAlgHom.toLinearMap
    (fun _ hs => (pvmOfHom_apply Φ hΦ hs).symm) hΦ f).symm

end OfHom

/-! ### Multiplication operators conjugated by a unitary -/

section MulConj

variable {X : Type*} [MeasurableSpace X] {M : Type*} [MeasurableSpace M] {μ : Measure M}
variable (U : H ≃ₗᵢ[ℂ] Lp ℂ 2 μ) {F : M → X} (hF : Measurable F)

/-- `g ↦ U⁻¹ M_{g ∘ F} U`: multiplication by `g ∘ F` on `L²(M, μ)`, transported to `H` by a
unitary `U : H ≃ L²(M, μ)`, as a `⋆`-homomorphism on bounded measurable functions. -/
def mulConjHom : boundedMeasurable X →⋆ₐ[ℂ] (H →L[ℂ] H) :=
  (U.conjStarAlgEquiv.symm : (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) ≃⋆ₐ[ℂ] (H →L[ℂ] H)).toStarAlgHom.comp
    (mulHom μ hF)

theorem mulConjHom_apply (g : boundedMeasurable X) (ψ : H) :
    mulConjHom U hF g ψ = U.symm (mulL ((g : X → ℂ) ∘ F) (memLp_top_comp μ hF g) (U ψ)) :=
  rfl

/-- `g ↦ U⁻¹ M_{g ∘ F} U` takes bounded pointwise convergence to strong convergence
(dominated convergence in `L²`, `tendsto_mulL_apply`). -/
theorem isBoundedPointwiseStrong_mulConjHom : IsBoundedPointwiseStrong (mulConjHom U hF) := by
  intro f f₀ C hC hlim ψ
  simp only [mulConjHom_apply]
  exact (U.symm.continuous.tendsto _).comp (tendsto_mulL_apply
    (fun n => memLp_top_comp μ hF (f n)) (memLp_top_comp μ hF f₀)
    (fun n => Eventually.of_forall fun m => hC n (F m))
    (Eventually.of_forall fun m => hlim (F m)) (U ψ))

end MulConj

/-! ### The representation of a projection-valued measure -/

section ToRep

variable {X : Type u} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

namespace ProjectionValuedMeasure

variable (P : ProjectionValuedMeasure X H)

/-- **The representation of `C(X)` given by a projection-valued measure**: `f ↦ ∫ f dP`, a
unital `⋆`-homomorphism `C(X, ℂ) → 𝓛(H)`. -/
def toRep : C(X, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H) :=
  P.integral.comp continuousMapToBoundedMeasurable

theorem toRep_apply (f : C(X, ℂ)) :
    P.toRep f = P.integral (continuousMapToBoundedMeasurable f) :=
  rfl

/-- `⟪ψ, (∫ f dP) ψ⟫ = ∫ f dμ_ψ` for continuous `f`. -/
theorem inner_toRep (ψ : H) (f : C(X, ℂ)) :
    ⟪ψ, P.toRep f ψ⟫_ℂ = ∫ x, f x ∂(P.measure ψ) := -- totalisation-audit: allow continuous
  P.inner_integral ψ _

/-- For real continuous `f`, `re ⟪ψ, (∫ f dP) ψ⟫ = ∫ f dμ_ψ`. -/
theorem re_inner_toRep_ofRealCM (ψ : H) (f : C(X, ℝ)) :
    RCLike.re ⟪ψ, P.toRep (ofRealCM f) ψ⟫_ℂ =
      ∫ x, f x ∂(P.measure ψ) := by -- totalisation-audit: allow continuous
  rw [inner_toRep]
  simp only [ofRealCM_apply]
  rw [integral_complex_ofReal]
  exact Complex.ofReal_re _

variable [T2Space X]

/-- **The measures of a regular p.v.m. representing `π` are the spectral measures of `π`**: if
`∫ f dP = π(f)` for continuous `f` and `μ_ψ` is regular, then `μ_ψ = repMeasure π ψ`
(uniqueness in the Riesz–Markov–Kakutani theorem, `eq_repMeasure`). -/
theorem measure_eq_repMeasure {π : C(X, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)} (hP : P.toRep = π) (ψ : H)
    [(P.measure ψ).Regular] : P.measure ψ = repMeasure π ψ :=
  eq_repMeasure π ψ _ fun f => by rw [← hP, re_inner_toRep_ofRealCM]

/-- **Uniqueness of regular projection-valued measures**: two p.v.m.'s on a compact Hausdorff
space with the same integrals of continuous functions and with regular measures `μ_ψ` are
equal.  Their measures are the same spectral measures (`measure_eq_repMeasure`), so
`⟪ψ, P_s ψ⟫ = ⟪ψ, Q_s ψ⟫` for all `ψ`. -/
theorem ext_of_toRep {P Q : ProjectionValuedMeasure X H} (h : P.toRep = Q.toRep)
    (hP : ∀ ψ, (P.measure ψ).Regular) (hQ : ∀ ψ, (Q.measure ψ).Regular) : P = Q := by
  refine ProjectionValuedMeasure.ext fun s hs => ext_inner_self fun ψ => ?_
  have := hP ψ
  have := hQ ψ
  have e1 := P.measure_eq_repMeasure h ψ
  have e2 := Q.measure_eq_repMeasure (π := Q.toRep) rfl ψ
  rw [P.inner_apply_eq_measureReal ψ hs, Q.inner_apply_eq_measureReal ψ hs, e1, e2]

end ProjectionValuedMeasure

end ToRep

/-! ### Existence -/

section Existence

variable {X : Type u} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X]
  [BorelSpace X]
variable {π : C(X, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)}

namespace RepDecomposition

variable (D : RepDecomposition π)

/-- **The projection-valued measure of a cyclic decomposition** `D` of `π`:
`P_Ω = U⁻¹ M_{1_Ω ∘ F} U`, for the unitary `U : H ≃ L²(Σ_ψ X, Σ_ψ μ_ψ)` of `D` and the
projection `F(ψ, x) = x`. -/
def pvm : ProjectionValuedMeasure X H :=
  pvmOfHom (mulConjHom D.unitary D.measurable_point)
    (isBoundedPointwiseStrong_mulConjHom D.unitary D.measurable_point)

/-- `∫ g dP = U⁻¹ M_{g ∘ F} U` for bounded Borel `g`. -/
theorem integral_pvm_apply (g : boundedMeasurable X) (h : H) :
    D.pvm.integral g h = D.unitary.symm (mulL ((g : X → ℂ) ∘ D.point)
      (memLp_top_comp D.measure D.measurable_point g) (D.unitary h)) := by
  rw [pvm, integral_pvmOfHom, mulConjHom_apply]

/-- **`π f = ∫ f dP`** for the p.v.m. of a cyclic decomposition and continuous `f`
(`RepDecomposition.unitary_apply`: `U π(f) U⁻¹` is multiplication by `f(x)`). -/
theorem toRep_pvm : D.pvm.toRep = π := by
  refine StarAlgHom.ext fun g => ContinuousLinearMap.ext fun h => ?_
  rw [ProjectionValuedMeasure.toRep_apply, integral_pvm_apply]
  change D.unitary.symm (mulL (fun p : D.Space => g p.2) (D.memLp_top_continuousMap g)
    (D.unitary h)) = _
  rw [← D.unitary_apply, LinearIsometryEquiv.symm_apply_apply]

end RepDecomposition

variable (π) in
/-- **The projection-valued measure of a representation** `π` of `C(X)`: the p.v.m. of a
cyclic decomposition of `π`, chosen once and for all. -/
def repPVM : ProjectionValuedMeasure X H :=
  (Classical.choice (RepDecomposition.nonempty π)).pvm

variable (π) in
/-- **`π f = ∫ f dP`** for the p.v.m. `P` of `π` and every continuous `f` (Rudin, *Functional
Analysis*, Chapter 12). -/
theorem toRep_repPVM : (repPVM π).toRep = π :=
  RepDecomposition.toRep_pvm _

variable (π) in
/-- `π f = ∫ f dP` for the p.v.m. `P` of `π` and continuous `f`, applied form. -/
theorem integral_repPVM (f : C(X, ℂ)) :
    (repPVM π).integral (continuousMapToBoundedMeasurable f) = π f := by
  rw [← ProjectionValuedMeasure.toRep_apply, toRep_repPVM]

variable (π) in
/-- **Existence** of a projection-valued measure representing `π`: `π f = ∫ f dP` for all
continuous `f`. -/
theorem exists_pvm_toRep_eq : ∃ P : ProjectionValuedMeasure X H, P.toRep = π :=
  ⟨repPVM π, toRep_repPVM π⟩

/-- **Uniqueness among regular projection-valued measures**: two p.v.m.'s representing `π`
whose measures `μ_ψ` are all regular are equal. -/
theorem eq_of_toRep_eq_of_regular {P Q : ProjectionValuedMeasure X H} (hP : P.toRep = π)
    (hQ : Q.toRep = π) (hPr : ∀ ψ, (P.measure ψ).Regular) (hQr : ∀ ψ, (Q.measure ψ).Regular) :
    P = Q :=
  ProjectionValuedMeasure.ext_of_toRep (hP.trans hQ.symm) hPr hQr

end Existence

/-! ### Regularity -/

/-- **A measure with an integrable density with respect to a finite inner regular measure is
inner regular**: for measurable `s` and `r < ν(s)`, absolute continuity of `A ↦ ∫_A f dμ`
gives `δ > 0` with `ν(A) < ν(s) - r` whenever `μ(A) < δ`, and a compact `K ⊆ s` with
`μ(s \ K) < δ` then has `r < ν(K)`. -/
theorem innerRegular_withDensity {X : Type*} [TopologicalSpace X] [T2Space X]
    [MeasurableSpace X] [OpensMeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    [μ.InnerRegularCompactLTTop] {f : X → ℝ≥0∞} (hf : ∫⁻ x, f x ∂μ ≠ ∞) :
    (μ.withDensity f).InnerRegular := by
  refine ⟨fun s hs r hr => ?_⟩
  have hε : μ.withDensity f s - r ≠ 0 := (tsub_pos_of_lt hr).ne'
  obtain ⟨δ, hδ, hδε⟩ := exists_pos_setLIntegral_lt_of_measure_lt hf hε
  obtain ⟨K, hKs, hK, hμK⟩ := hs.exists_isCompact_sdiff_lt (measure_ne_top μ s) hδ.ne'
  refine ⟨K, hKs, hK, ?_⟩
  have h1 : μ.withDensity f (s \ K) < μ.withDensity f s - r := by
    rw [withDensity_apply f (hs.diff hK.measurableSet)]
    exact hδε _ hμK
  have h2 : μ.withDensity f s ≤ μ.withDensity f K + μ.withDensity f (s \ K) := by
    calc μ.withDensity f s ≤ μ.withDensity f (K ∪ (s \ K)) := by
          refine measure_mono fun x hx => ?_
          by_cases hxK : x ∈ K
          exacts [Or.inl hxK, Or.inr ⟨hx, hxK⟩]
      _ ≤ _ := measure_union_le _ _
  by_contra hcon
  push Not at hcon
  have h3 : μ.withDensity f K + μ.withDensity f (s \ K) < r + (μ.withDensity f s - r) :=
    ENNReal.add_lt_add_of_le_of_lt (ne_top_of_le_ne_top hr.ne_top hcon) hcon h1
  rw [add_tsub_cancel_of_le hr.le] at h3
  exact lt_irrefl _ (h2.trans_lt h3)

section Regularity

variable {X : Type u} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X]
  [BorelSpace X]
variable {π : C(X, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)}

namespace RepDecomposition

variable (D : RepDecomposition π)

/-- The density `x ↦ |(U ψ)(φ, x)|²` of `μ_ψ` on the `φ`-th copy of `X`. -/
def density (ψ : H) (φ : D.vectors) (x : X) : ℝ≥0∞ :=
  ‖(D.unitary ψ : D.Space → ℂ) ⟨φ, x⟩‖ₑ ^ 2

/-- **The measures of the p.v.m. of a cyclic decomposition**: `μ_ψ = Σ_φ |U ψ(φ, ·)|² μ_φ`,
since `μ_ψ(Ω) = ‖M_{1_Ω ∘ F} U ψ‖² = ∫_{F⁻¹ Ω} |U ψ|² d(Σ_φ μ_φ)`. -/
theorem pvm_measure (ψ : H) :
    D.pvm.measure ψ = Measure.sum fun φ : D.vectors =>
      (repMeasure π (φ : H)).withDensity (D.density ψ φ) := by
  ext Ω hΩ
  rw [ProjectionValuedMeasure.measure_apply _ ψ hΩ, Measure.sum_apply _ hΩ]
  simp only [withDensity_apply _ hΩ]
  have hP : D.pvm Ω ψ = D.unitary.symm (mulL (Ω.indicator (fun _ => (1 : ℂ)) ∘ D.point)
      (memLp_top_comp D.measure D.measurable_point (boundedMeasurable.indicator hΩ))
      (D.unitary ψ)) := by
    rw [pvm, pvmOfHom_apply _ _ hΩ, mulConjHom_apply]
    rfl
  rw [hP, LinearIsometryEquiv.norm_map]
  set v := mulL (Ω.indicator (fun _ => (1 : ℂ)) ∘ D.point)
    (memLp_top_comp D.measure D.measurable_point (boundedMeasurable.indicator hΩ))
    (D.unitary ψ) with hv
  have h1 : ENNReal.ofReal (‖v‖ ^ 2) = eLpNorm v 2 D.measure ^ 2 := by
    rw [Lp.norm_def, ENNReal.ofReal_pow ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top v)]
  rw [h1, eLpNorm_two_sq_eq_lintegral (Lp.aestronglyMeasurable v)]
  have h2 : ∫⁻ p, ‖(v : D.Space → ℂ) p‖ₑ ^ 2 ∂D.measure =
      ∫⁻ p, ‖(Ω.indicator (fun _ => (1 : ℂ)) ∘ D.point) p *
        (D.unitary ψ : D.Space → ℂ) p‖ₑ ^ 2 ∂D.measure := by
    refine lintegral_congr_ae ?_
    filter_upwards [coeFn_mulL (memLp_top_comp D.measure D.measurable_point
      (boundedMeasurable.indicator hΩ)) (D.unitary ψ)] with p hp
    exact congrArg (fun z : ℂ => ‖z‖ₑ ^ 2) hp
  rw [h2, lintegral_sigmaMeasure]
  refine tsum_congr fun φ => ?_
  rw [← lintegral_indicator hΩ]
  refine lintegral_congr fun x => ?_
  by_cases hx : x ∈ Ω <;> simp [hx, density, point]

/-- **The measures of the p.v.m. of a cyclic decomposition are regular**: each
`|U ψ(φ, ·)|² μ_φ` is inner regular (`innerRegular_withDensity`), hence so is their sum, and a
finite inner regular measure on a compact Hausdorff space is regular. -/
instance regular_pvm_measure (ψ : H) : (D.pvm.measure ψ).Regular := by
  have hfin : ∀ φ : D.vectors, ∫⁻ x, D.density ψ φ x ∂(repMeasure π (φ : H)) ≠ ∞ := by
    intro φ
    have h := D.pvm_measure ψ
    have h' := congrArg (fun m : Measure X => m Set.univ) h
    simp only [Measure.sum_apply _ MeasurableSet.univ, withDensity_apply _ MeasurableSet.univ,
      Measure.restrict_univ] at h'
    refine ne_top_of_le_ne_top (measure_ne_top (D.pvm.measure ψ) Set.univ) ?_
    rw [h']
    exact ENNReal.le_tsum (f := fun φ : D.vectors =>
      ∫⁻ x, D.density ψ φ x ∂(repMeasure π (φ : H))) φ
  have : ∀ φ : D.vectors, ((repMeasure π (φ : H)).withDensity (D.density ψ φ)).InnerRegular :=
    fun φ => innerRegular_withDensity _ (hfin φ)
  have hI : (D.pvm.measure ψ).InnerRegular := by
    rw [D.pvm_measure ψ]
    infer_instance
  infer_instance

end RepDecomposition

/-- **The measures of the p.v.m. of `π` are regular.** -/
instance regular_repPVM_measure (ψ : H) : ((repPVM π).measure ψ).Regular :=
  RepDecomposition.regular_pvm_measure _ ψ

variable (π) in
/-- **The measures of the p.v.m. of `π` are the spectral measures of `π`**:
`⟪ψ, P_Ω ψ⟫ = μ_ψ(Ω)`. -/
theorem measure_repPVM (ψ : H) : (repPVM π).measure ψ = repMeasure π ψ :=
  (repPVM π).measure_eq_repMeasure (toRep_repPVM π) ψ

/-- **Uniqueness among regular projection-valued measures**: a p.v.m. representing `π` whose
measures are all regular is the p.v.m. of `π`. -/
theorem eq_repPVM_of_regular {P : ProjectionValuedMeasure X H} (hP : P.toRep = π)
    (hreg : ∀ ψ, (P.measure ψ).Regular) : P = repPVM π :=
  eq_of_toRep_eq_of_regular hP (toRep_repPVM π) hreg fun ψ => regular_repPVM_measure ψ

/-- The p.v.m. of any cyclic decomposition of `π` is the p.v.m. of `π`. -/
theorem RepDecomposition.pvm_eq_repPVM (D : RepDecomposition π) : D.pvm = repPVM π :=
  eq_repPVM_of_regular D.toRep_pvm fun ψ => D.regular_pvm_measure ψ

/-- **Multiplication operator form of `∫ g dP`**: for any cyclic decomposition `D` of `π`, with
unitary `U : H ≃ L²(Σ_ψ X, Σ_ψ μ_ψ)` and projection `F(ψ, x) = x`, `∫ g dP = U⁻¹ M_{g ∘ F} U`
for the p.v.m. `P` of `π` and every bounded Borel `g`. -/
theorem integral_repPVM_apply (D : RepDecomposition π) (g : boundedMeasurable X) (h : H) :
    (repPVM π).integral g h = D.unitary.symm (mulL ((g : X → ℂ) ∘ D.point)
      (memLp_top_comp D.measure D.measurable_point g) (D.unitary h)) := by
  rw [← D.pvm_eq_repPVM, D.integral_pvm_apply]

variable (π) in
/-- **Statement (R), existence and uniqueness**: there is exactly one
projection-valued measure `P` on `X` with `π f = ∫ f dP` for all continuous `f` and with all
measures `μ_ψ(Ω) = ⟪ψ, P_Ω ψ⟫` regular. -/
theorem existsUnique_regular_pvm :
    ∃! P : ProjectionValuedMeasure X H, P.toRep = π ∧ ∀ ψ, (P.measure ψ).Regular :=
  ⟨repPVM π, ⟨toRep_repPVM π, fun ψ => regular_repPVM_measure ψ⟩,
    fun _ hP => eq_repPVM_of_regular hP.1 hP.2⟩

variable (π) in
/-- `⟪ψ, P_Ω ψ⟫ = μ_ψ(Ω)` for the p.v.m. `P` of `π` and the spectral measure `μ_ψ` of `π`. -/
theorem inner_repPVM_apply (ψ : H) {Ω : Set X} (hΩ : MeasurableSet Ω) :
    ⟪ψ, repPVM π Ω ψ⟫_ℂ = ((repMeasure π ψ).real Ω : ℂ) := by
  rw [(repPVM π).inner_apply_eq_measureReal ψ hΩ, measure_repPVM]

variable (X H) in
/-- **Representations of `C(X)` and regular projection-valued measures** (`X` compact
Hausdorff): `π ↦ repPVM π` and `P ↦ (f ↦ ∫ f dP)` are inverse bijections between unital
`⋆`-homomorphisms `C(X, ℂ) → 𝓛(H)` and projection-valued measures on `X` with regular measures
`μ_ψ`. -/
def repPVMEquivRegular : (C(X, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) ≃
    {P : ProjectionValuedMeasure X H // ∀ ψ, (P.measure ψ).Regular} where
  toFun π := ⟨repPVM π, fun ψ => regular_repPVM_measure ψ⟩
  invFun P := P.1.toRep
  left_inv := toRep_repPVM
  right_inv P := Subtype.ext (eq_repPVM_of_regular rfl P.2).symm

end Regularity

/-! ### Conjugation by a unitary -/

namespace ProjectionValuedMeasure

section Conj

variable {X : Type*} [MeasurableSpace X] (P : ProjectionValuedMeasure X H) (W : H ≃ₗᵢ[ℂ] H)

/-- **The conjugate of a projection-valued measure** by a unitary `W`: `s ↦ W⁻¹ P_s W`. -/
def conj : ProjectionValuedMeasure X H where
  toFun s := W.conjStarAlgEquiv.symm (P s)
  isStarProjection' s hs := (P.isStarProjection hs).map W.conjStarAlgEquiv.symm
  empty' := by rw [P.empty, map_zero]
  univ' := by rw [P.univ, map_one]
  tendsto_sum' s hs hd ψ := by
    simp only [LinearIsometryEquiv.symm_conjStarAlgEquiv_apply_apply]
    have h : ∀ N, ∑ n ∈ Finset.range N, W.symm (P (s n) (W ψ)) =
        W.symm (∑ n ∈ Finset.range N, P (s n) (W ψ)) := fun N => (map_sum W.symm _ _).symm
    simp only [h]
    exact (W.symm.continuous.tendsto _).comp (P.tendsto_sum s hs hd (W ψ))
  apply_of_not_measurableSet' s hs := by
    rw [P.apply_of_not_measurableSet hs, map_zero]

theorem conj_apply (s : Set X) (ψ : H) : P.conj W s ψ = W.symm (P s (W ψ)) :=
  rfl

/-- The measures of the conjugate: `μ^{W⁻¹ P W}_ψ = μ^P_{W ψ}`. -/
theorem measure_conj (ψ : H) : (P.conj W).measure ψ = P.measure (W ψ) :=
  Measure.ext fun s hs => by
    rw [measure_apply _ _ hs, measure_apply _ _ hs, conj_apply, LinearIsometryEquiv.norm_map]

/-- `∫ g d(W⁻¹ P W) = W⁻¹ (∫ g dP) W`. -/
theorem integral_conj (g : boundedMeasurable X) :
    (P.conj W).integral g = W.conjStarAlgEquiv.symm (P.integral g) :=
  ext_inner_self fun ψ => by
    rw [inner_integral, measure_conj, ← inner_integral,
      LinearIsometryEquiv.symm_conjStarAlgEquiv_apply_apply, ← W.inner_map_map ψ,
      W.apply_symm_apply]

end Conj

section ConjRep

variable {X : Type u} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X]
  [BorelSpace X] (P : ProjectionValuedMeasure X H)

/-- **A unitary commuting with all `∫ f dP` leaves a regular `P` invariant**: `W⁻¹ P W` is a
p.v.m. with the same integrals of continuous functions and regular measures `μ_{W ψ}`, so it is
`P` by uniqueness (`ext_of_toRep`). -/
theorem conj_eq_self (hreg : ∀ ψ, (P.measure ψ).Regular) {W : H ≃ₗᵢ[ℂ] H}
    (hW : ∀ f, Commute (W : H →L[ℂ] H) (P.toRep f)) : P.conj W = P := by
  refine ext_of_toRep ?_ (fun ψ => by rw [measure_conj]; exact hreg _) hreg
  refine StarAlgHom.ext fun f => ContinuousLinearMap.ext fun ψ => ?_
  rw [toRep_apply, integral_conj, LinearIsometryEquiv.symm_conjStarAlgEquiv_apply_apply,
    ← toRep_apply]
  have h : W (P.toRep f ψ) = P.toRep f (W ψ) := DFunLike.congr_fun (hW f).eq ψ
  rw [← h, W.symm_apply_apply]

/-- A unitary commuting with all `∫ f dP` commutes with every `P_s`, for regular `P`. -/
theorem commute_apply_of_unitary (hreg : ∀ ψ, (P.measure ψ).Regular) {W : H ≃ₗᵢ[ℂ] H}
    (hW : ∀ f, Commute (W : H →L[ℂ] H) (P.toRep f)) (s : Set X) :
    Commute (W : H →L[ℂ] H) (P s) := by
  refine ContinuousLinearMap.ext fun ψ => ?_
  have h := DFunLike.congr_fun (DFunLike.congr_fun (P.conj_eq_self hreg hW) s) ψ
  rw [conj_apply] at h
  change W (P s ψ) = P s (W ψ)
  rw [← h, W.apply_symm_apply]

open Complex in
/-- **A self-adjoint operator `A` commuting with all `∫ f dP` commutes with every `P_s`**, for
regular `P`.  The unitaries `exp(i t A)`, `t ∈ ℝ`, commute with all `∫ f dP`, hence with `P_s`
(`commute_apply_of_unitary`); differentiating `t ↦ exp(i t A) P_s - P_s exp(i t A) = 0` at
`t = 0` gives `i (A P_s - P_s A) = 0`. -/
theorem commute_apply_of_isSelfAdjoint (hreg : ∀ ψ, (P.measure ψ).Regular) {A : H →L[ℂ] H}
    (hA : IsSelfAdjoint A) (hB : ∀ f, Commute A (P.toRep f)) (s : Set X) :
    Commute A (P s) := by
  let E : ℂ → H →L[ℂ] H := fun u => NormedSpace.exp (u • (I • A))
  have hE : ∀ t : ℝ, Commute (E t) (P s) := by
    intro t
    let a : selfAdjoint (H →L[ℂ] H) := t • (⟨A, hA⟩ : selfAdjoint (H →L[ℂ] H))
    let W : H ≃ₗᵢ[ℂ] H := Unitary.linearIsometryEquiv (selfAdjoint.expUnitary a)
    have hW : (W : H →L[ℂ] H) = E t := by
      change NormedSpace.exp (I • (t • A)) = NormedSpace.exp ((t : ℂ) • (I • A))
      rw [smul_comm, Complex.coe_smul]
    rw [← hW]
    refine P.commute_apply_of_unitary hreg (fun f => ?_) s
    rw [hW]
    exact (((hB f).smul_left I).smul_left (t : ℂ)).exp_left
  let L : (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H) :=
    (ContinuousLinearMap.mul ℂ (H →L[ℂ] H)).flip (P s) - ContinuousLinearMap.mul ℂ (H →L[ℂ] H) (P s)
  have hL : ∀ T, L T = T * P s - P s * T := fun T => rfl
  have hd : HasDerivAt (fun u : ℂ => L (E u))
      (L (NormedSpace.exp (((0 : ℝ) : ℂ) • (I • A)) * (I • A))) ((0 : ℝ) : ℂ) :=
    L.hasFDerivAt.comp_hasDerivAt _ (hasDerivAt_exp_smul_const (I • A) _)
  have hd' : HasDerivAt (fun _ : ℝ => (0 : H →L[ℂ] H))
      (ofRealCLM 1 • L (NormedSpace.exp (((0 : ℝ) : ℂ) • (I • A)) * (I • A))) 0 :=
    (hd.scomp (0 : ℝ) ofRealCLM.hasDerivAt).congr_of_eventuallyEq
      (Eventually.of_forall fun t => by
        change (0 : H →L[ℂ] H) = L (E t)
        rw [hL, (hE t).eq, sub_self])
  have h0 := hd'.unique (hasDerivAt_const _ _)
  rw [ofRealCLM_apply, Complex.ofReal_one, one_smul, hL, Complex.ofReal_zero, zero_smul,
    NormedSpace.exp_zero, one_mul, smul_mul_assoc, mul_smul_comm, ← smul_sub, smul_eq_zero,
    sub_eq_zero] at h0
  exact h0.resolve_left I_ne_zero

open ComplexStarModule in
/-- **The commutant for regular `P`**: an operator `B` commuting with all `∫ f dP`, `f`
continuous, commutes with every `P_s`.  `B^*` also commutes with all `∫ f dP` (a
`⋆`-homomorphism), so do the self-adjoint real and imaginary parts of `B`, and
`commute_apply_of_isSelfAdjoint` applies to them. -/
theorem commute_apply_of_regular (hreg : ∀ ψ, (P.measure ψ).Regular) {B : H →L[ℂ] H}
    (hB : ∀ f, Commute B (P.toRep f)) (s : Set X) : Commute B (P s) := by
  have hB' : ∀ f, Commute (star B) (P.toRep f) := fun f => by
    have h := (hB (star f)).star_star
    rwa [← map_star, star_star] at h
  have h1 : ∀ f, Commute (ℜ B : H →L[ℂ] H) (P.toRep f) := fun f => by
    rw [realPart_apply_coe]
    exact ((hB f).add_left (hB' f)).smul_left _
  have h2 : ∀ f, Commute (ℑ B : H →L[ℂ] H) (P.toRep f) := fun f => by
    rw [imaginaryPart_apply_coe]
    exact (((hB f).sub_left (hB' f)).smul_left _).smul_left _
  have e1 := P.commute_apply_of_isSelfAdjoint hreg (ℜ B).2 h1 s
  have e2 := P.commute_apply_of_isSelfAdjoint hreg (ℑ B).2 h2 s
  rw [← realPart_add_I_smul_imaginaryPart B]
  exact e1.add_left (e2.smul_left Complex.I)

end ConjRep

end ProjectionValuedMeasure

/-! ### Metrizable `X`: uniqueness and the correspondence -/

section Metrizable

variable {X : Type u} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X]
  [BorelSpace X] [TopologicalSpace.MetrizableSpace X]
variable (π : C(X, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H))

omit [T2Space X] in
/-- On a compact metrizable space every finite Borel measure is regular, in particular every
measure `μ_ψ` of a projection-valued measure. -/
theorem ProjectionValuedMeasure.regular_measure (P : ProjectionValuedMeasure X H) (ψ : H) :
    (P.measure ψ).Regular :=
  inferInstance

/-- **Uniqueness** (`X` metrizable): every projection-valued measure `P` with `∫ f dP = π f`
for all continuous `f` is the p.v.m. of `π`. -/
theorem eq_repPVM {P : ProjectionValuedMeasure X H} (hP : P.toRep = π) : P = repPVM π :=
  eq_of_toRep_eq_of_regular hP (toRep_repPVM π) P.regular_measure (repPVM π).regular_measure

/-- **Existence and uniqueness** (`X` metrizable): there is exactly one projection-valued
measure `P` with `π f = ∫ f dP` for all continuous `f`. -/
theorem existsUnique_pvm_toRep_eq : ∃! P : ProjectionValuedMeasure X H, P.toRep = π :=
  ⟨repPVM π, toRep_repPVM π, fun _ hP => eq_repPVM π hP⟩

variable (X H) in
/-- **Representations of `C(X)` and projection-valued measures** (`X` compact metrizable):
`π ↦ repPVM π` and `P ↦ (f ↦ ∫ f dP)` are inverse bijections between unital `⋆`-homomorphisms
`C(X, ℂ) → 𝓛(H)` and projection-valued measures on `X`. -/
def repPVMEquiv : (C(X, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) ≃ ProjectionValuedMeasure X H where
  toFun := repPVM
  invFun P := P.toRep
  left_inv := toRep_repPVM
  right_inv P := (eq_repPVM P.toRep rfl).symm

theorem repPVMEquiv_apply : repPVMEquiv H X π = repPVM π :=
  rfl

theorem repPVMEquiv_symm_apply (P : ProjectionValuedMeasure X H) :
    (repPVMEquiv H X).symm P = P.toRep :=
  rfl

end Metrizable

/-! ### The commutant -/

omit [CompleteSpace H] in
/-- An operator commuting with each `Aₙ` commutes with their strong limit. -/
theorem commute_of_tendsto_apply {B A₀ : H →L[ℂ] H} {A : ℕ → H →L[ℂ] H}
    (hA : ∀ ψ, Tendsto (fun n => A n ψ) atTop (𝓝 (A₀ ψ))) (hB : ∀ n, Commute B (A n)) :
    Commute B A₀ := by
  refine ContinuousLinearMap.ext fun ψ => ?_
  have h1 : Tendsto (fun n => B (A n ψ)) atTop (𝓝 (B (A₀ ψ))) :=
    (B.continuous.tendsto _).comp (hA ψ)
  have h3 : (fun n => B (A n ψ)) = fun n => A n (B ψ) :=
    funext fun n => DFunLike.congr_fun (hB n).eq ψ
  rw [h3] at h1
  exact tendsto_nhds_unique h1 (hA (B ψ))

section Commutant

variable {X : Type u} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  [HasOuterApproxClosed X]

namespace ProjectionValuedMeasure

variable (P : ProjectionValuedMeasure X H) {B : H →L[ℂ] H}

/-- The continuous functions `X → [0, 1]` tending to the indicator of a closed set, as
complex-valued continuous functions. -/
def apprSeqCM {F : Set X} (hF : IsClosed F) (n : ℕ) : C(X, ℂ) :=
  ⟨fun x => ((hF.apprSeq n x : ℝ) : ℂ),
    Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp (hF.apprSeq n).continuous)⟩

omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
theorem norm_apprSeqCM_le {F : Set X} (hF : IsClosed F) (n : ℕ) (x : X) :
    ‖apprSeqCM hF n x‖ ≤ 1 := by
  change ‖((hF.apprSeq n x : ℝ) : ℂ)‖ ≤ 1
  rw [Complex.norm_real, Real.norm_of_nonneg (NNReal.coe_nonneg _)]
  exact_mod_cast HasOuterApproxClosed.apprSeq_apply_le_one hF n x

omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
theorem tendsto_apprSeqCM {F : Set X} (hF : IsClosed F) (x : X) :
    Tendsto (fun n => apprSeqCM hF n x) atTop (𝓝 (F.indicator (fun _ => (1 : ℂ)) x)) := by
  have h := ((Complex.continuous_ofReal.comp NNReal.continuous_coe).tendsto _).comp
    (tendsto_pi_nhds.mp (HasOuterApproxClosed.tendsto_apprSeq hF) x)
  have e : (Complex.ofReal ∘ ((↑) : ℝ≥0 → ℝ)) (F.indicator (fun _ => (1 : ℝ≥0)) x) =
      F.indicator (fun _ => (1 : ℂ)) x := by
    by_cases hx : x ∈ F <;> simp [hx]
  rw [e] at h
  exact h

/-- **`P_F` commutes with every operator commuting with all `∫ f dP`**, for closed `F`: the
indicator of `F` is a bounded pointwise limit of continuous functions, so `P_F` is a strong
limit of operators `∫ fₙ dP`. -/
theorem commute_apply_of_isClosed (hB : ∀ f, Commute B (P.toRep f)) {F : Set X}
    (hF : IsClosed F) : Commute B (P F) := by
  rw [← P.integral_indicator hF.measurableSet]
  exact commute_of_tendsto_apply (A := fun n => P.toRep (apprSeqCM hF n))
    (fun ψ => P.tendsto_integral_apply
      (fun n => continuousMapToBoundedMeasurable (apprSeqCM hF n))
      (boundedMeasurable.indicator hF.measurableSet) 1
      (fun n x => norm_apprSeqCM_le hF n x) (fun x => tendsto_apprSeqCM hF x) ψ)
    fun n => hB _

/-- **The commutant** (`X` metrizable, or more generally with closed sets approximable by
continuous functions): every `P_Ω` commutes with every operator commuting with all `∫ f dP`,
`f` continuous.  The sets `Ω` with `B P_Ω = P_Ω B` form a Dynkin system (`P_{Ωᶜ} = 1 - P_Ω`,
strong countable additivity) containing the closed sets, a `π`-system generating the Borel
sets. -/
theorem commute_apply (hB : ∀ f, Commute B (P.toRep f)) (s : Set X) : Commute B (P s) := by
  by_cases hs : MeasurableSet s
  swap
  · rw [P.apply_of_not_measurableSet hs]
    exact Commute.zero_right B
  refine MeasurableSpace.induction_on_inter (C := fun t _ => Commute B (P t))
    (s := {t : Set X | IsClosed t}) ?_ isPiSystem_isClosed ?_ ?_ ?_ ?_ s hs
  · rw [BorelSpace.measurable_eq (α := X)]
    exact borel_eq_generateFrom_isClosed
  · rw [P.empty]
    exact Commute.zero_right B
  · exact fun t ht => P.commute_apply_of_isClosed hB ht
  · intro t ht h
    rw [P.compl ht]
    exact (Commute.one_right B).sub_right h
  · intro f hd hf h
    refine commute_of_tendsto_apply (A := fun N => ∑ n ∈ Finset.range N, P (f n))
      (fun ψ => ?_) fun N => Commute.sum_right _ _ _ fun n _ => h n
    simp only [sum_apply]
    exact P.tendsto_sum f hf hd ψ

end ProjectionValuedMeasure

end Commutant

/-! ### The commutant of a representation -/

section CommutantGeneral

variable {X : Type*} [MeasurableSpace X]

/-- **The commutant, integral form**: an operator commuting with every `P_s` commutes with
`∫ g dP` for every bounded measurable `g` (monotone class theorem,
`IsBoundedLimitClosed.of_indicator`). -/
theorem ProjectionValuedMeasure.commute_integral_of_forall_commute
    (P : ProjectionValuedMeasure X H) {B : H →L[ℂ] H} (hB : ∀ s, Commute B (P s))
    (g : boundedMeasurable X) : Commute B (P.integral g) := by
  let Q : (X → ℂ) → Prop := fun g =>
    ∃ hg : g ∈ boundedMeasurable X, Commute B (P.integral ⟨g, hg⟩)
  have hQ : IsBoundedLimitClosed Q := by
    refine ⟨⟨zero_mem _, ?_⟩, ?_, ?_, ?_⟩
    · rw [show (⟨0, zero_mem _⟩ : boundedMeasurable X) = 0 from rfl, map_zero]
      exact Commute.zero_right B
    · rintro g₁ g₂ ⟨h₁, e₁⟩ ⟨h₂, e₂⟩
      refine ⟨add_mem h₁ h₂, ?_⟩
      have h := map_add P.integral ⟨g₁, h₁⟩ ⟨g₂, h₂⟩
      rw [show (⟨g₁ + g₂, add_mem h₁ h₂⟩ : boundedMeasurable X) = ⟨g₁, h₁⟩ + ⟨g₂, h₂⟩ from rfl, h]
      exact e₁.add_right e₂
    · rintro c g ⟨h, e⟩
      refine ⟨SMulMemClass.smul_mem c h, ?_⟩
      have h' := map_smul P.integral c ⟨g, h⟩
      rw [show (⟨c • g, SMulMemClass.smul_mem c h⟩ : boundedMeasurable X) = c • ⟨g, h⟩ from rfl,
        h']
      exact e.smul_right c
    · rintro f₁ g C hC hlim' hf
      choose hmem heq using hf
      have hg : g ∈ boundedMeasurable X :=
        ⟨measurable_of_tendsto_metrizable (fun n => (hmem n).1) (tendsto_pi_nhds.mpr hlim'), C,
          fun x => le_of_tendsto' ((continuous_norm.tendsto _).comp (hlim' x)) fun n => hC n x⟩
      exact ⟨hg, commute_of_tendsto_apply (fun ψ => P.tendsto_integral_apply
        (fun n => ⟨f₁ n, hmem n⟩) ⟨g, hg⟩ C hC hlim' ψ) heq⟩
  obtain ⟨C, -, hC⟩ := boundedMeasurable.exists_bound g
  obtain ⟨_, h⟩ := hQ.of_indicator (fun s hs => ⟨(boundedMeasurable.indicator hs).2,
    (P.integral_indicator hs).symm ▸ hB s⟩) (boundedMeasurable.measurable g) hC
  exact h

end CommutantGeneral

section CommutantRep

variable {X : Type u} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X]
  [BorelSpace X] {π : C(X, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)} {B : H →L[ℂ] H}

/-- **The commutant** (statement (R)): every `P_Ω` of the p.v.m. of `π` commutes with every
operator commuting with all `π f` (`commute_apply_of_regular`). -/
theorem commute_repPVM (hB : ∀ f, Commute B (π f)) (s : Set X) : Commute B (repPVM π s) :=
  (repPVM π).commute_apply_of_regular (fun ψ => regular_repPVM_measure ψ)
    (by rwa [toRep_repPVM]) s

/-- An operator commuting with all `π f` commutes with `∫ g dP` for the p.v.m. `P` of `π` and
every bounded Borel `g`. -/
theorem commute_integral_repPVM (hB : ∀ f, Commute B (π f)) (g : boundedMeasurable X) :
    Commute B ((repPVM π).integral g) :=
  (repPVM π).commute_integral_of_forall_commute (commute_repPVM hB) g

end CommutantRep

end SpectralTheorem
