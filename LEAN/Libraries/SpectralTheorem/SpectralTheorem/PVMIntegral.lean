import SpectralTheorem.ProjectionValuedMeasure
import SpectralTheorem.BoundedMeasurable
import SpectralTheorem.MonotoneClass
import Mathlib.MeasureTheory.Integral.FinMeasAdditive
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.LocallyConvex.Barrelled
import Mathlib.Topology.Baire.CompleteMetrizable

/-!
# The integral against a projection-valued measure

**Reed–Simon I, Theorem VII.7, p. 235.**  If `P_Ω` is a projection-valued measure and `f` is a
bounded Borel function on `supp P_Ω`, then there is a unique operator `B`, denoted
`∫ f(λ) dP_λ`, so that `(φ, B φ) = ∫ f(λ) d(φ, P_λ φ)` for all `φ`.

Here `P` is a projection-valued measure on a measurable space `X`
(`SpectralTheorem.ProjectionValuedMeasure`) and `f` a bounded measurable function on `X`.

Construction.  For a simple function `g = Σ_c c 1_{g⁻¹(c)}` put
`I(g) = Σ_c c P_{g⁻¹(c)}` (mathlib's `SimpleFunc.setToSimpleFunc`).  By (d),
`⟪I(g) ψ, I(h) ψ⟫ = ∫ ḡ h dμ_ψ` with `μ_ψ = P.measure ψ`.  For bounded measurable `f` the
simple functions `sₙ = f.simpleApprox n` converge to `f` boundedly, so
`‖I(sₙ) ψ - I(sₘ) ψ‖² = ∫ |sₙ - sₘ|² dμ_ψ → 0` by dominated convergence, and `∫ f dP` is the
strong limit of the `I(sₙ)` (a continuous linear map by Banach–Steinhaus,
`continuousLinearMapOfTendsto`).  Every other bounded approximating sequence of simple functions
gives the same limit, which gives linearity and `∫ 1_s dP = P_s`, and in the limit
`⟪(∫ f dP) ψ, (∫ g dP) ψ⟫ = ∫ f̄ g dμ_ψ`.  This identity gives the `⋆`-homomorphism property
(two operators with the same quadratic form are equal), the norm bound, the formula of
Theorem VII.7, and the strong convergence `(∫ fₙ dP) ψ → (∫ f dP) ψ` for bounded pointwise
convergent `fₙ → f` (dominated convergence again).

Every Bochner integral below is of a bounded measurable function against the finite measure
`P.measure ψ`, hence of an integrable function; those lines carry an audit marker.

## Main definitions and results

* `SpectralTheorem.boundedMeasurable.indicator hs`: the indicator of a measurable set.
* `SpectralTheorem.ProjectionValuedMeasure.integral P`: `f ↦ ∫ f dP`, a `⋆`-homomorphism
  `boundedMeasurable X →⋆ₐ[ℂ] 𝓛(H)`, with `integral_indicator`, `inner_integral`,
  `norm_integral_apply_sq`, `norm_integral_le`, `tendsto_integral_apply`, `commute_integral`.
* `ProjectionValuedMeasure.existsUnique_inner_integral`: **Reed–Simon I, Theorem VII.7**.
* `ProjectionValuedMeasure.eq_integral_of_indicator`: a linear map sending indicators to the
  projections and bounded pointwise limits to strong limits is `∫ · dP`.
* `ProjectionValuedMeasure.integral_map`: `∫ f d(F_* P) = ∫ f ∘ F dP`.
-/

noncomputable section

open scoped InnerProductSpace ENNReal Topology ComplexConjugate
open MeasureTheory Filter Set

namespace SpectralTheorem

universe u

variable {X : Type*} [MeasurableSpace X]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### Preliminaries -/

namespace boundedMeasurable

/-- The indicator function of a measurable set, as a bounded measurable function. -/
def indicator {s : Set X} (hs : MeasurableSet s) : boundedMeasurable X :=
  ⟨s.indicator fun _ => (1 : ℂ), (measurable_const.indicator hs), 1, fun x => by
    by_cases hx : x ∈ s <;> simp [hx]⟩

@[simp]
theorem coe_indicator {s : Set X} (hs : MeasurableSet s) :
    ((indicator hs : boundedMeasurable X) : X → ℂ) = s.indicator fun _ => (1 : ℂ) :=
  rfl

theorem indicator_univ : indicator (MeasurableSet.univ : MeasurableSet (univ : Set X)) = 1 :=
  Subtype.ext (funext fun x => by simp)

/-- A bound for `‖f‖`, chosen once and for all. -/
def normBound (f : boundedMeasurable X) : ℝ :=
  (exists_bound f).choose

theorem normBound_nonneg (f : boundedMeasurable X) : 0 ≤ normBound f :=
  (exists_bound f).choose_spec.1

theorem norm_le_normBound (f : boundedMeasurable X) (x : X) :
    ‖(f : X → ℂ) x‖ ≤ normBound f :=
  (exists_bound f).choose_spec.2 x

/-- Simple functions converging to `f` pointwise, with `‖sₙ x‖ ≤ normBound f`. -/
def simpleApprox (f : boundedMeasurable X) (n : ℕ) : SimpleFunc X ℂ :=
  (boundedMeasurable.measurable f).stronglyMeasurable.approxBounded (normBound f) n

theorem norm_simpleApprox_le (f : boundedMeasurable X) (n : ℕ) (x : X) :
    ‖simpleApprox f n x‖ ≤ normBound f :=
  StronglyMeasurable.norm_approxBounded_le _ (normBound_nonneg f) n x

theorem tendsto_simpleApprox (f : boundedMeasurable X) (x : X) :
    Tendsto (fun n => simpleApprox f n x) atTop (𝓝 ((f : X → ℂ) x)) :=
  StronglyMeasurable.tendsto_approxBounded_of_norm_le _ (norm_le_normBound f x)

theorem integrable {μ : Measure X} [IsFiniteMeasure μ] (f : boundedMeasurable X) :
    Integrable (f : X → ℂ) μ :=
  Integrable.of_bound (boundedMeasurable.measurable f).aestronglyMeasurable (normBound f)
    (Eventually.of_forall (norm_le_normBound f))

end boundedMeasurable

/-- Dominated convergence for `∫ ā b dμ` with bounded measurable `a`, `b`. -/
theorem tendsto_integral_conj_mul {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    (μ : Measure X) [IsFiniteMeasure μ] {a b : ι → X → ℂ} {a₀ b₀ : X → ℂ} {Ca Cb : ℝ}
    (ha : ∀ i, Measurable (a i)) (hb : ∀ i, Measurable (b i))
    (haC : ∀ i x, ‖a i x‖ ≤ Ca) (hbC : ∀ i x, ‖b i x‖ ≤ Cb)
    (ha₀ : ∀ x, Tendsto (fun i => a i x) l (𝓝 (a₀ x)))
    (hb₀ : ∀ x, Tendsto (fun i => b i x) l (𝓝 (b₀ x))) :
    Tendsto (fun i => ∫ x, conj (a i x) * b i x ∂μ) -- totalisation-audit: allow bounded
      l (𝓝 (∫ x, conj (a₀ x) * b₀ x ∂μ)) := by -- totalisation-audit: allow bounded
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => Ca * Cb) ?_ ?_
    (integrable_const _) ?_
  · exact Eventually.of_forall fun i =>
      ((Complex.continuous_conj.measurable.comp (ha i)).mul (hb i)).aestronglyMeasurable
  · refine Eventually.of_forall fun i => Eventually.of_forall fun x => ?_
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul (haC i x) (hbC i x) (norm_nonneg _) ((norm_nonneg _).trans (haC i x))
  · exact Eventually.of_forall fun x =>
      ((Complex.continuous_conj.tendsto _).comp (ha₀ x)).mul (hb₀ x)

omit [CompleteSpace H] in
/-- If `⟪wᵢ, wᵢ⟫ → 0` then `wᵢ → 0`. -/
theorem tendsto_zero_of_inner_self {ι : Type*} {l : Filter ι} {w : ι → H}
    (h : Tendsto (fun i => ⟪w i, w i⟫_ℂ) l (𝓝 0)) : Tendsto w l (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h2 : Tendsto (fun i => ‖w i‖ ^ 2) l (𝓝 0) := by
    simpa [inner_self_eq_norm_sq_to_K] using h.norm
  rw [Metric.tendsto_nhds] at h2 ⊢
  intro ε hε
  filter_upwards [h2 (ε ^ 2) (by positivity)] with i hi
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (sq_nonneg _)] at hi
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
  exact lt_of_pow_lt_pow_left₀ 2 hε.le hi

omit [CompleteSpace H] in
/-- Two operators with the same quadratic form `ψ ↦ ⟪ψ, A ψ⟫` are equal. -/
theorem ext_inner_self {A B : H →L[ℂ] H} (h : ∀ ψ, ⟪ψ, A ψ⟫_ℂ = ⟪ψ, B ψ⟫_ℂ) : A = B :=
  ContinuousLinearMap.coe_injective ((ext_inner_map _ _).mp fun x => by
    simp only [ContinuousLinearMap.coe_coe]
    rw [← inner_conj_symm, h x, inner_conj_symm])

theorem SimpleFunc.coe_piecewise_const (c : ℂ) {s : Set X} (hs : MeasurableSet s) :
    ⇑(SimpleFunc.piecewise s hs (SimpleFunc.const X c) (SimpleFunc.const X 0)) =
      s.indicator fun _ => c := by
  funext x
  by_cases hx : x ∈ s <;> simp [hx]

namespace ProjectionValuedMeasure

variable (P : ProjectionValuedMeasure X H)

/-! ### Simple functions -/

/-- The set function `s ↦ (c ↦ c • P_s)`; its `setToSimpleFunc` is `g ↦ Σ_c c P_{g⁻¹(c)}`. -/
def weight (s : Set X) : ℂ →L[ℝ] (H →L[ℂ] H) :=
  (ContinuousLinearMap.toSpanSingleton ℂ (P s)).restrictScalars ℝ

theorem weight_apply (s : Set X) (c : ℂ) : P.weight s c = c • P s :=
  ContinuousLinearMap.toSpanSingleton_apply ℂ (P s) c

theorem finMeasAdditive_weight : FinMeasAdditive (0 : Measure X) P.weight := by
  intro s t hs ht _ _ hst
  refine ContinuousLinearMap.ext fun c => ?_
  rw [add_apply, P.weight_apply, P.weight_apply, P.weight_apply,
    P.union hs ht hst, smul_add]

/-- **The integral of a simple function**: `I(g) = Σ_c c P_{g⁻¹(c)}`. -/
def simpleIntegral : SimpleFunc X ℂ →ₗ[ℂ] (H →L[ℂ] H) where
  toFun g := SimpleFunc.setToSimpleFunc P.weight g
  map_add' f g := SimpleFunc.setToSimpleFunc_add _ P.finMeasAdditive_weight
    integrable_zero_measure integrable_zero_measure
  map_smul' c f := SimpleFunc.setToSimpleFunc_smul _ P.finMeasAdditive_weight
    (fun c s x => by rw [P.weight_apply, P.weight_apply, smul_eq_mul, mul_smul]) c
    integrable_zero_measure

theorem simpleIntegral_piecewise (c : ℂ) {s : Set X} (hs : MeasurableSet s) :
    P.simpleIntegral (SimpleFunc.piecewise s hs (SimpleFunc.const X c) (SimpleFunc.const X 0)) =
      c • P s := by
  rw [← P.weight_apply]
  exact SimpleFunc.setToSimpleFunc_indicator _ (ContinuousLinearMap.ext fun c => by
    simp [P.weight_apply]) hs c

/-- `⟪c P_s ψ, d P_t ψ⟫ = c̄ d μ_ψ(s ∩ t)`, as an integral. -/
theorem inner_smul_apply_smul_apply (ψ : H) (c d : ℂ) {s t : Set X} (hs : MeasurableSet s)
    (ht : MeasurableSet t) :
    ⟪c • P s ψ, d • P t ψ⟫_ℂ =
      ∫ x, conj (s.indicator (fun _ => c) x) * -- totalisation-audit: allow bounded
        t.indicator (fun _ => d) x ∂(P.measure ψ) := by
  have h1 : ⟪P s ψ, P t ψ⟫_ℂ = ((P.measure ψ).real (s ∩ t) : ℂ) := by
    calc ⟪P s ψ, P t ψ⟫_ℂ = ⟪ψ, P s (P t ψ)⟫_ℂ := (P.isSelfAdjoint hs).isSymmetric ψ (P t ψ)
      _ = ⟪ψ, P (s ∩ t) ψ⟫_ℂ := by rw [← P.mul_apply hs ht]; rfl
      _ = _ := P.inner_apply_eq_measureReal ψ (hs.inter ht)
  have h2 : (fun x => conj (s.indicator (fun _ => c) x) * t.indicator (fun _ => d) x) =
      (s ∩ t).indicator fun _ => conj c * d := by
    funext x
    by_cases hx : x ∈ s <;> by_cases hy : x ∈ t <;> simp [hx, hy]
  rw [inner_smul_left, inner_smul_right, h1, h2, integral_indicator_const _ (hs.inter ht),
    Complex.real_smul]
  ring

/-- **`⟪I(g) ψ, I(h) ψ⟫ = ∫ ḡ h dμ_ψ`** for simple `g`, `h`. -/
theorem inner_simpleIntegral (ψ : H) (g h : SimpleFunc X ℂ) :
    ⟪P.simpleIntegral g ψ, P.simpleIntegral h ψ⟫_ℂ =
      ∫ x, conj (g x) * h x ∂(P.measure ψ) := by -- totalisation-audit: allow bounded
  have hint : ∀ g h : SimpleFunc X ℂ, Integrable (fun x => conj (g x) * h x) (P.measure ψ) :=
    fun g h => (SimpleFunc.integrable_of_isFiniteMeasure (μ := P.measure ψ)
      ((g.map conj) * h)).congr (Eventually.of_forall fun x => by simp)
  induction g using SimpleFunc.induction with
  | @const c s hs =>
    induction h using SimpleFunc.induction with
    | @const d t ht =>
      rw [P.simpleIntegral_piecewise, P.simpleIntegral_piecewise,
        SimpleFunc.coe_piecewise_const, SimpleFunc.coe_piecewise_const]
      exact P.inner_smul_apply_smul_apply ψ c d hs ht
    | @add h₁ h₂ _ ih₁ ih₂ =>
      rw [map_add, add_apply, inner_add_right, ih₁, ih₂,
        ← integral_add (hint _ _) (hint _ _)]
      congr 1
      funext x
      rw [SimpleFunc.coe_add, Pi.add_apply, mul_add]
  | @add g₁ g₂ _ ih₁ ih₂ =>
    rw [map_add, add_apply, inner_add_left, ih₁, ih₂,
      ← integral_add (hint _ _) (hint _ _)]
    congr 1
    funext x
    rw [SimpleFunc.coe_add, Pi.add_apply, map_add, add_mul]

/-! ### The integral of a bounded measurable function -/

open boundedMeasurable in
/-- `I(sₙ) ψ` is a Cauchy sequence: `‖I(sₙ) ψ - I(sₘ) ψ‖² = ∫ |sₙ - sₘ|² dμ_ψ → 0`. -/
theorem cauchySeq_simpleIntegral (f : boundedMeasurable X) (ψ : H) :
    CauchySeq fun n => P.simpleIntegral (simpleApprox f n) ψ := by
  rw [cauchySeq_iff_tendsto_dist_atTop_0]
  have hfst : Tendsto (fun p : ℕ × ℕ => p.1) atTop atTop := by
    rw [← prod_atTop_atTop_eq]
    exact tendsto_fst
  have hsnd : Tendsto (fun p : ℕ × ℕ => p.2) atTop atTop := by
    rw [← prod_atTop_atTop_eq]
    exact tendsto_snd
  let u : ℕ × ℕ → SimpleFunc X ℂ := fun p => simpleApprox f p.1 - simpleApprox f p.2
  have hu : ∀ p x, ‖u p x‖ ≤ normBound f + normBound f := fun p x => by
    simp only [u, SimpleFunc.coe_sub, Pi.sub_apply]
    exact (norm_sub_le _ _).trans
      (add_le_add (norm_simpleApprox_le f p.1 x) (norm_simpleApprox_le f p.2 x))
  have hu0 : ∀ x, Tendsto (fun p => u p x) atTop (𝓝 0) := fun x => by
    simpa [u] using
      ((tendsto_simpleApprox f x).comp hfst).sub ((tendsto_simpleApprox f x).comp hsnd)
  have h0 : Tendsto (fun p => P.simpleIntegral (u p) ψ) atTop (𝓝 0) := by
    refine tendsto_zero_of_inner_self ?_
    simp only [P.inner_simpleIntegral]
    simpa using tendsto_integral_conj_mul (P.measure ψ) (a₀ := 0) (b₀ := 0)
      (fun p => (u p).measurable) (fun p => (u p).measurable) hu hu hu0 hu0
  simpa [u, dist_eq_norm, map_sub] using h0.norm

/-- **`∫ f dP`**, as a continuous linear map: the strong limit of the `I(sₙ)` for the simple
approximations `sₙ = simpleApprox f n` (Banach–Steinhaus gives continuity). -/
def integralCLM (f : boundedMeasurable X) : H →L[ℂ] H :=
  continuousLinearMapOfTendsto (fun n => P.simpleIntegral (boundedMeasurable.simpleApprox f n))
    (tendsto_pi_nhds.mpr fun ψ => (P.cauchySeq_simpleIntegral f ψ).tendsto_limUnder)

theorem tendsto_integralCLM (f : boundedMeasurable X) (ψ : H) :
    Tendsto (fun n => P.simpleIntegral (boundedMeasurable.simpleApprox f n) ψ) atTop
      (𝓝 (P.integralCLM f ψ)) :=
  (P.cauchySeq_simpleIntegral f ψ).tendsto_limUnder

open boundedMeasurable in
/-- Every bounded sequence of simple functions converging pointwise to `f` gives `∫ f dP` as the
strong limit. -/
theorem tendsto_simpleIntegral (f : boundedMeasurable X) (t : ℕ → SimpleFunc X ℂ) {C : ℝ}
    (htC : ∀ n x, ‖t n x‖ ≤ C) (ht : ∀ x, Tendsto (fun n => t n x) atTop (𝓝 ((f : X → ℂ) x)))
    (ψ : H) : Tendsto (fun n => P.simpleIntegral (t n) ψ) atTop (𝓝 (P.integralCLM f ψ)) := by
  let u : ℕ → SimpleFunc X ℂ := fun n => t n - simpleApprox f n
  have hu : ∀ n x, ‖u n x‖ ≤ C + normBound f := fun n x => by
    simp only [u, SimpleFunc.coe_sub, Pi.sub_apply]
    exact (norm_sub_le _ _).trans (add_le_add (htC n x) (norm_simpleApprox_le f n x))
  have hu0 : ∀ x, Tendsto (fun n => u n x) atTop (𝓝 0) := fun x => by
    simpa [u] using (ht x).sub (tendsto_simpleApprox f x)
  have h0 : Tendsto (fun n => P.simpleIntegral (u n) ψ) atTop (𝓝 0) := by
    refine tendsto_zero_of_inner_self ?_
    simp only [P.inner_simpleIntegral]
    simpa using tendsto_integral_conj_mul (P.measure ψ) (a₀ := 0) (b₀ := 0)
      (fun n => (u n).measurable) (fun n => (u n).measurable) hu hu hu0 hu0
  simpa [u, map_sub] using h0.add (P.tendsto_integralCLM f ψ)

open boundedMeasurable in
theorem integralCLM_add (f g : boundedMeasurable X) :
    P.integralCLM (f + g) = P.integralCLM f + P.integralCLM g := by
  ext ψ
  refine tendsto_nhds_unique (P.tendsto_simpleIntegral (f + g)
    (fun n => simpleApprox f n + simpleApprox g n) (C := normBound f + normBound g)
    (fun n x => ?_) (fun x => ?_) ψ) ?_
  · rw [SimpleFunc.coe_add, Pi.add_apply]
    exact (norm_add_le _ _).trans
      (add_le_add (norm_simpleApprox_le f n x) (norm_simpleApprox_le g n x))
  · simpa using (tendsto_simpleApprox f x).add (tendsto_simpleApprox g x)
  · simpa [map_add] using (P.tendsto_integralCLM f ψ).add (P.tendsto_integralCLM g ψ)

open boundedMeasurable in
theorem integralCLM_smul (c : ℂ) (f : boundedMeasurable X) :
    P.integralCLM (c • f) = c • P.integralCLM f := by
  ext ψ
  refine tendsto_nhds_unique (P.tendsto_simpleIntegral (c • f) (fun n => c • simpleApprox f n)
    (C := ‖c‖ * normBound f) (fun n x => ?_) (fun x => ?_) ψ) ?_
  · rw [SimpleFunc.coe_smul, Pi.smul_apply, norm_smul]
    exact mul_le_mul_of_nonneg_left (norm_simpleApprox_le f n x) (norm_nonneg c)
  · simpa using (tendsto_simpleApprox f x).const_smul c
  · simpa [map_smul] using (P.tendsto_integralCLM f ψ).const_smul c

theorem integralCLM_indicator {s : Set X} (hs : MeasurableSet s) :
    P.integralCLM (boundedMeasurable.indicator hs) = P s := by
  ext ψ
  refine tendsto_nhds_unique (P.tendsto_simpleIntegral _
    (fun _ => SimpleFunc.piecewise s hs (SimpleFunc.const X 1) (SimpleFunc.const X 0)) (C := 1)
    (fun n x => ?_) (fun x => ?_) ψ) ?_
  · rw [SimpleFunc.coe_piecewise_const]
    by_cases hx : x ∈ s <;> simp [hx]
  · rw [SimpleFunc.coe_piecewise_const, boundedMeasurable.coe_indicator]
    exact tendsto_const_nhds
  · rw [P.simpleIntegral_piecewise, one_smul]
    exact tendsto_const_nhds

theorem integralCLM_one : P.integralCLM 1 = 1 := by
  rw [← boundedMeasurable.indicator_univ, integralCLM_indicator, P.univ]

/-- **`⟪(∫ f dP) ψ, (∫ g dP) ψ⟫ = ∫ f̄ g dμ_ψ`**. -/
theorem inner_integralCLM (f g : boundedMeasurable X) (ψ : H) :
    ⟪P.integralCLM f ψ, P.integralCLM g ψ⟫_ℂ =
      ∫ x, conj ((f : X → ℂ) x) * (g : X → ℂ) x -- totalisation-audit: allow bounded
        ∂(P.measure ψ) := by
  have h := (P.tendsto_integralCLM f ψ).inner (𝕜 := ℂ) (P.tendsto_integralCLM g ψ)
  simp only [P.inner_simpleIntegral] at h
  exact tendsto_nhds_unique h (tendsto_integral_conj_mul (P.measure ψ)
    (fun n => (boundedMeasurable.simpleApprox f n).measurable)
    (fun n => (boundedMeasurable.simpleApprox g n).measurable)
    (boundedMeasurable.norm_simpleApprox_le f) (boundedMeasurable.norm_simpleApprox_le g)
    (boundedMeasurable.tendsto_simpleApprox f) (boundedMeasurable.tendsto_simpleApprox g))

theorem inner_integralCLM_self (f : boundedMeasurable X) (ψ : H) :
    ⟪ψ, P.integralCLM f ψ⟫_ℂ =
      ∫ x, (f : X → ℂ) x ∂(P.measure ψ) := by -- totalisation-audit: allow bounded
  have h := P.inner_integralCLM 1 f ψ
  rw [P.integralCLM_one, one_apply_eq_self] at h
  simpa using h

theorem integralCLM_star (f : boundedMeasurable X) :
    P.integralCLM (star f) = star (P.integralCLM f) := by
  refine ext_inner_self fun ψ => ?_
  rw [P.inner_integralCLM_self, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right, ← inner_conj_symm, P.inner_integralCLM_self,
    ← integral_conj]
  rfl

theorem integralCLM_mul (f g : boundedMeasurable X) :
    P.integralCLM (f * g) = P.integralCLM f * P.integralCLM g := by
  refine ext_inner_self fun ψ => ?_
  have h : ⟪ψ, (P.integralCLM f * P.integralCLM g) ψ⟫_ℂ =
      ⟪P.integralCLM (star f) ψ, P.integralCLM g ψ⟫_ℂ := by
    rw [P.integralCLM_star, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_left]
    rfl
  rw [h, P.inner_integralCLM, P.inner_integralCLM_self]
  congr 1
  funext x
  simp

/-- **The integral `∫ f dP`** of a bounded measurable function against the projection-valued
measure `P`, as a `⋆`-homomorphism `boundedMeasurable X →⋆ₐ[ℂ] 𝓛(H)` (Reed–Simon I,
Theorem VII.7, p. 235). -/
def integral : boundedMeasurable X →⋆ₐ[ℂ] (H →L[ℂ] H) where
  toFun := P.integralCLM
  map_one' := P.integralCLM_one
  map_mul' := P.integralCLM_mul
  map_zero' := by simpa using P.integralCLM_smul 0 0
  map_add' := P.integralCLM_add
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, P.integralCLM_smul,
      P.integralCLM_one]
  map_star' := P.integralCLM_star

theorem integral_apply (f : boundedMeasurable X) : P.integral f = P.integralCLM f :=
  rfl

/-- `∫ 1_s dP = P_s`. -/
@[simp]
theorem integral_indicator {s : Set X} (hs : MeasurableSet s) :
    P.integral (boundedMeasurable.indicator hs) = P s :=
  P.integralCLM_indicator hs

/-- `⟪(∫ f dP) ψ, (∫ g dP) ψ⟫ = ∫ f̄ g dμ_ψ`. -/
theorem inner_integral_integral (f g : boundedMeasurable X) (ψ : H) :
    ⟪P.integral f ψ, P.integral g ψ⟫_ℂ =
      ∫ x, conj ((f : X → ℂ) x) * (g : X → ℂ) x -- totalisation-audit: allow bounded
        ∂(P.measure ψ) :=
  P.inner_integralCLM f g ψ

/-- **`⟪ψ, (∫ f dP) ψ⟫ = ∫ f dμ_ψ`** (Reed–Simon I, Theorem VII.7, p. 235). -/
theorem inner_integral (ψ : H) (f : boundedMeasurable X) :
    ⟪ψ, P.integral f ψ⟫_ℂ =
      ∫ x, (f : X → ℂ) x ∂(P.measure ψ) := -- totalisation-audit: allow bounded
  P.inner_integralCLM_self f ψ

/-- `‖(∫ f dP) ψ‖² = ∫ |f|² dμ_ψ`. -/
theorem norm_integral_apply_sq (f : boundedMeasurable X) (ψ : H) :
    ‖P.integral f ψ‖ ^ 2 =
      ∫ x, ‖(f : X → ℂ) x‖ ^ 2 ∂(P.measure ψ) := by -- totalisation-audit: allow bounded
  have h := P.inner_integral_integral f f ψ
  have h2 : ∫ x, conj ((f : X → ℂ) x) * (f : X → ℂ) x -- totalisation-audit: allow bounded
      ∂(P.measure ψ) =
      ((∫ x, ‖(f : X → ℂ) x‖ ^ 2 ∂(P.measure ψ) : ℝ) : ℂ) := by -- totalisation-audit: allow bounded
    rw [← integral_complex_ofReal]
    congr 1
    funext x
    rw [Complex.conj_mul']
    push_cast
    rfl
  have h3 := congrArg Complex.re (h.trans h2)
  rw [Complex.ofReal_re] at h3
  rw [← h3]
  exact (inner_self_eq_norm_sq (𝕜 := ℂ) _).symm

/-- **`‖∫ f dP‖ ≤ C`** when `‖f‖ ≤ C`. -/
theorem norm_integral_le (f : boundedMeasurable X) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ x, ‖(f : X → ℂ) x‖ ≤ C) : ‖P.integral f‖ ≤ C := by
  refine ContinuousLinearMap.opNorm_le_bound _ hC0 fun ψ => ?_
  have h1 : ∫ x, ‖(f : X → ℂ) x‖ ^ 2 ∂(P.measure ψ) ≤ -- totalisation-audit: allow bounded
      ∫ _, C ^ 2 ∂(P.measure ψ) := -- totalisation-audit: allow bounded
    integral_mono_of_nonneg (Eventually.of_forall fun x => sq_nonneg _) (integrable_const _)
      (Eventually.of_forall fun x => pow_le_pow_left₀ (norm_nonneg _) (hC x) 2)
  rw [integral_const, smul_eq_mul, P.measureReal_apply ψ MeasurableSet.univ, P.univ,
    one_apply_eq_self, ← P.norm_integral_apply_sq] at h1
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp ?_
  rw [mul_pow]
  linarith

/-- **Bounded pointwise convergence gives strong convergence**: if `fₙ → f` pointwise with
`‖fₙ‖ ≤ C`, then `(∫ fₙ dP) ψ → (∫ f dP) ψ`, since
`‖(∫ fₙ dP) ψ - (∫ f dP) ψ‖² = ∫ |fₙ - f|² dμ_ψ → 0`. -/
theorem tendsto_integral_apply (f : ℕ → boundedMeasurable X) (f₀ : boundedMeasurable X) (C : ℝ)
    (hC : ∀ n x, ‖(f n : X → ℂ) x‖ ≤ C)
    (hlim : ∀ x, Tendsto (fun n => (f n : X → ℂ) x) atTop (𝓝 ((f₀ : X → ℂ) x))) (ψ : H) :
    Tendsto (fun n => P.integral (f n) ψ) atTop (𝓝 (P.integral f₀ ψ)) := by
  have hb : ∀ n x, ‖((f n - f₀ : boundedMeasurable X) : X → ℂ) x‖ ≤
      C + boundedMeasurable.normBound f₀ := fun n x => by
    change ‖(f n : X → ℂ) x - (f₀ : X → ℂ) x‖ ≤ _
    exact (norm_sub_le _ _).trans (add_le_add (hC n x) (boundedMeasurable.norm_le_normBound f₀ x))
  have ht : ∀ x, Tendsto (fun n => ((f n - f₀ : boundedMeasurable X) : X → ℂ) x) atTop
      (𝓝 0) := fun x => by
    have h := (hlim x).sub (tendsto_const_nhds (x := (f₀ : X → ℂ) x))
    rw [sub_self] at h
    exact h
  have h0 : Tendsto (fun n => P.integral (f n - f₀) ψ) atTop (𝓝 0) := by
    refine tendsto_zero_of_inner_self ?_
    simp only [P.inner_integral_integral]
    simpa using tendsto_integral_conj_mul (P.measure ψ) (a₀ := 0) (b₀ := 0)
      (fun n => boundedMeasurable.measurable (f n - f₀))
      (fun n => boundedMeasurable.measurable (f n - f₀)) hb hb ht ht
  simpa [map_sub] using h0.add (tendsto_const_nhds (x := P.integral f₀ ψ))

/-- `∫ f dP` commutes with every `P_s`. -/
theorem commute_integral (f : boundedMeasurable X) (s : Set X) :
    Commute (P.integral f) (P s) := by
  by_cases hs : MeasurableSet s
  · rw [← P.integral_indicator hs]
    exact (show Commute f (boundedMeasurable.indicator hs) from
      Subtype.ext (mul_comm _ _)).map P.integral
  · rw [P.apply_of_not_measurableSet hs]
    exact Commute.zero_right _

/-- **Reed–Simon I, Theorem VII.7, p. 235.**  For a projection-valued measure `P` and a bounded
measurable function `f` there is a unique operator `B = ∫ f dP` with
`⟪ψ, B ψ⟫ = ∫ f dμ_ψ` for all `ψ`, where `μ_ψ(s) = ⟪ψ, P_s ψ⟫`. -/
theorem existsUnique_inner_integral (f : boundedMeasurable X) :
    ∃! B : H →L[ℂ] H, ∀ ψ, ⟪ψ, B ψ⟫_ℂ =
      ∫ x, (f : X → ℂ) x ∂(P.measure ψ) := -- totalisation-audit: allow bounded
  ⟨P.integral f, fun ψ => P.inner_integral ψ f,
    fun B hB => ext_inner_self fun ψ => by rw [hB ψ, P.inner_integral]⟩

end ProjectionValuedMeasure

/-! ### Uniqueness -/

namespace IsBoundedLimitClosed

variable {Q : (X → ℂ) → Prop} (hQ : IsBoundedLimitClosed Q)
  (hind : ∀ s, MeasurableSet s → Q (s.indicator fun _ => 1))
include hQ hind

/-- A property closed under bounded pointwise limits holding for indicators of measurable sets
holds for simple functions. -/
theorem simpleFunc_of_indicator (g : SimpleFunc X ℂ) : Q g := by
  induction g using SimpleFunc.induction with
  | @const c E hE =>
    rw [SimpleFunc.coe_piecewise_const]
    have h : (E.indicator fun _ => c) = c • E.indicator (fun _ => (1 : ℂ)) := by
      funext x
      by_cases hx : x ∈ E <;> simp [hx]
    rw [h]
    exact hQ.smul c _ (hind E hE)
  | @add f g _ hf hg =>
    rw [SimpleFunc.coe_add]
    exact hQ.add _ _ hf hg

/-- **Monotone class theorem, measurable-set form.**  A property of functions `X → ℂ` closed
under `0`, sums, scalar multiples and bounded pointwise limits, and holding for indicators of
measurable sets, holds for every bounded measurable function. -/
theorem of_indicator {g : X → ℂ} (hg : Measurable g) {C : ℝ} (hC : ∀ x, ‖g x‖ ≤ C) : Q g := by
  have hgs : StronglyMeasurable g := hg.stronglyMeasurable
  exact hQ.lim (fun n => hgs.approxBounded (max C 0) n) g (max C 0)
    (fun n x => hgs.norm_approxBounded_le (le_max_right C 0) n x)
    (fun x => hgs.tendsto_approxBounded_of_norm_le ((hC x).trans (le_max_left C 0)))
    fun n => hQ.simpleFunc_of_indicator hind _

end IsBoundedLimitClosed

namespace ProjectionValuedMeasure

variable (P : ProjectionValuedMeasure X H)

/-- **Uniqueness of `∫ · dP`**: a linear map `Φ` from bounded measurable functions to operators
with `Φ(1_s) = P_s` for measurable `s`, taking bounded pointwise convergence to strong
convergence, is `f ↦ ∫ f dP`.  Both sides are linear and continuous for bounded pointwise
limits, and agree on indicators; the monotone class theorem (`IsBoundedLimitClosed.of_indicator`)
concludes. -/
theorem eq_integral_of_indicator (Φ : boundedMeasurable X →ₗ[ℂ] (H →L[ℂ] H))
    (hind : ∀ s (hs : MeasurableSet s), Φ (boundedMeasurable.indicator hs) = P s)
    (hlim : ∀ (f : ℕ → boundedMeasurable X) (f₀ : boundedMeasurable X) (C : ℝ),
      (∀ n x, ‖(f n : X → ℂ) x‖ ≤ C) →
      (∀ x, Tendsto (fun n => (f n : X → ℂ) x) atTop (𝓝 ((f₀ : X → ℂ) x))) →
      ∀ ψ : H, Tendsto (fun n => Φ (f n) ψ) atTop (𝓝 (Φ f₀ ψ)))
    (f : boundedMeasurable X) : Φ f = P.integral f := by
  let Q : (X → ℂ) → Prop := fun g =>
    ∃ hg : g ∈ boundedMeasurable X, Φ ⟨g, hg⟩ = P.integral ⟨g, hg⟩
  have hQ : IsBoundedLimitClosed Q := by
    refine ⟨⟨zero_mem _, (map_zero Φ).trans (map_zero P.integral).symm⟩, ?_, ?_, ?_⟩
    · rintro g₁ g₂ ⟨h₁, e₁⟩ ⟨h₂, e₂⟩
      exact ⟨add_mem h₁ h₂, (map_add Φ ⟨g₁, h₁⟩ ⟨g₂, h₂⟩).trans
        (by rw [e₁, e₂]; exact (map_add P.integral _ _).symm)⟩
    · rintro c g ⟨h, e⟩
      exact ⟨SMulMemClass.smul_mem c h, (map_smul Φ c ⟨g, h⟩).trans
        (by rw [e]; exact (map_smul P.integral c _).symm)⟩
    · rintro f₁ g C hC hlim' hf
      choose hmem heq using hf
      have hg : g ∈ boundedMeasurable X :=
        ⟨measurable_of_tendsto_metrizable (fun n => (hmem n).1) (tendsto_pi_nhds.mpr hlim'), C,
          fun x => le_of_tendsto' ((continuous_norm.tendsto _).comp (hlim' x)) fun n => hC n x⟩
      refine ⟨hg, ContinuousLinearMap.ext fun ψ => tendsto_nhds_unique
        (hlim (fun n => ⟨f₁ n, hmem n⟩) ⟨g, hg⟩ C hC hlim' ψ) ?_⟩
      simp only [heq]
      exact P.tendsto_integral_apply (fun n => ⟨f₁ n, hmem n⟩) ⟨g, hg⟩ C hC hlim' ψ
  obtain ⟨C, -, hC⟩ := boundedMeasurable.exists_bound f
  obtain ⟨_, h⟩ := hQ.of_indicator (fun s hs => ⟨(boundedMeasurable.indicator hs).2,
    (hind s hs).trans (P.integral_indicator hs).symm⟩) (boundedMeasurable.measurable f) hC
  exact h

/-! ### Pushforward -/

theorem _root_.SpectralTheorem.boundedMeasurable.comp_mem {Y : Type*} [MeasurableSpace Y]
    (f : boundedMeasurable Y) {F : X → Y} (hF : Measurable F) :
    (f : Y → ℂ) ∘ F ∈ boundedMeasurable X :=
  ⟨(boundedMeasurable.measurable f).comp hF, boundedMeasurable.normBound f,
    fun x => boundedMeasurable.norm_le_normBound f (F x)⟩

/-- **`∫ f d(F_* P) = ∫ f ∘ F dP`**. -/
theorem integral_map {Y : Type*} [MeasurableSpace Y] {F : X → Y} (hF : Measurable F)
    (f : boundedMeasurable Y) :
    (P.map F hF).integral f = P.integral ⟨(f : Y → ℂ) ∘ F, boundedMeasurable.comp_mem f hF⟩ :=
  ext_inner_self fun ψ => by
    rw [ProjectionValuedMeasure.inner_integral, ProjectionValuedMeasure.inner_integral,
      measure_map, MeasureTheory.integral_map hF.aemeasurable
        (boundedMeasurable.measurable f).aestronglyMeasurable]
    rfl

end ProjectionValuedMeasure

end SpectralTheorem
