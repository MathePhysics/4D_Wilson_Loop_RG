import SpectralTheorem.PVMIntegral
import SpectralTheorem.SpectralProjection
import Mathlib.Analysis.CStarAlgebra.Spectrum

/-!
# The spectral theorem in projection-valued measure form (bounded operators)

**Reed–Simon I, Theorem VII.8, p. 235.**  There is a one-one correspondence between (bounded)
self-adjoint operators `A` and (bounded) projection-valued measures `{P_Ω}` given by
`A ↦ {P_Ω} = {χ_Ω(A)}`, `{P_Ω} ↦ A = ∫ λ dP_λ`.  A p.v.m. is *bounded* (p. 234) if
`P_(-a,a) = I` for some `a`.  The two halves of the correspondence are Reed–Simon's
Problem VII.23: `f(A) = ∫ f(λ) dP_λ` for the p.v.m. of `A`, and the p.v.m. of `∫ λ dP_λ` is `P`.

As elsewhere in the library, the main version is for **normal** operators and p.v.m.'s on `ℂ`
(boundedness: `P_{B̄(0, r)} = I` for some `r`); Reed–Simon's self-adjoint version on `ℝ` is
derived from it by pushing p.v.m.'s forward along `Complex.re` and `Complex.ofReal`.

Proof sketch.
* For bounded `P`, `∫ λ dP_λ` is `∫ f dP` for `f(z) = z · 1_{‖z‖ ≤ r}`; any radius `r` with
  `P_{B̄(0, r)} = I` gives the same operator, since `∫ f dP` only depends on `f` on a set `s`
  with `P_s = I`.  It is normal, as `∫ · dP` is a `⋆`-homomorphism on a commutative algebra.
* For normal `T`, `Ω ↦ χ_Ω(T)` is a p.v.m. by the Proposition on p. 234
  (`SpectralTheorem.SpectralProjection`); its measures are the spectral measures pushed to `ℂ`,
  so `⟪ψ, (∫ f dP) ψ⟫ = ∫ f dμ_ψ = ⟪ψ, f(T) ψ⟫` and `∫ f dP = f(T)`; with `f(z) = z`,
  `∫ λ dP_λ = T`.
* Support: for bounded `P` and `T = ∫ λ dP_λ`, `P_{σ(T)ᶜ} = 0`.  If `z₀ ∉ σ(T)` and `R` is the
  inverse of `z₀ - T`, then for `B = B(z₀, ε)`, `(z₀ - T) P_B = ∫ (z₀ - λ) 1_B dP` has norm
  `≤ ε`, so `‖P_B‖ = ‖R (z₀ - T) P_B P_B‖ ≤ ‖R‖ ε ‖P_B‖` and `P_B = 0` when `‖R‖ ε < 1`.  The
  open set `σ(T)ᶜ` is covered by countably many such balls (second countability of `ℂ`).
* Hence `g ↦ ∫ g̃ dP`, with `g̃` the extension by `0` of a bounded Borel `g` on `σ(T)`, is a
  `⋆`-homomorphism with the properties (b)–(d) of Theorem VII.2, so it is `g ↦ g(T)`
  (uniqueness, `SpectralTheorem.IsBorelCalculus.eq_borelCalc`); for `g = χ_Ω` this gives
  `χ_Ω(T) = P_{Ω ∩ σ(T)} = P_Ω`.

## Main definitions and results

* `SpectralTheorem.ProjectionValuedMeasure.IsBounded`: `P_{B̄(0, r)} = I` for some `r`.
* `SpectralTheorem.ProjectionValuedMeasure.toOperator`: `∫ λ dP_λ` for a bounded `P` on `ℂ`,
  with `toOperator_eq` (any radius), `isStarNormal_toOperator`, `norm_toOperator_le`.
* `SpectralTheorem.ProjectionValuedMeasure.integral_congr_of_eqOn`: `∫ f dP = ∫ g dP` when
  `f = g` on a set `s` with `P_s = I`.
* `SpectralTheorem.spectralPVM T`: the p.v.m. `Ω ↦ χ_Ω(T)` of a bounded normal `T`, with
  `spectralPVM_apply`, `spectralPVM_isBounded`, `spectralPVM_measure` (`μ_ψ` pushed to `ℂ`).
* `SpectralTheorem.spectralPVM_integral`, `SpectralTheorem.toOperator_spectralPVM`:
  **Problem VII.23, first half**, `∫ f dP = f(T)` and `∫ λ dP_λ = T`.
* `SpectralTheorem.ProjectionValuedMeasure.apply_compl_spectrum`: `P_{σ(T)ᶜ} = 0` for
  `T = ∫ λ dP_λ`; `mem_spectrum_toOperator_iff`: `σ(T)` is the support of `P`.
* `SpectralTheorem.ProjectionValuedMeasure.spectralPVM_toOperator`: **Problem VII.23, second
  half**, the p.v.m. of `∫ λ dP_λ` is `P`; `integral_eq_borelCalc`: `∫ f dP = f(∫ λ dP_λ)`.
* `SpectralTheorem.spectralPVMEquiv`: **Theorem VII.8** for normal operators and p.v.m.'s on `ℂ`.
* `SpectralTheorem.isSelfAdjoint_iff_spectralPVM`: `T` is self-adjoint iff `P_ℝ = I`.
* `SpectralTheorem.selfAdjointPVMEquiv`: **Theorem VII.8** as stated by Reed–Simon, for
  self-adjoint operators and p.v.m.'s on `ℝ`; `integral_map_re_spectralPVM`: `∫ f dP = f(A)`.
-/

noncomputable section

open scoped InnerProductSpace ENNReal Topology ComplexConjugate
open MeasureTheory Filter Set

namespace SpectralTheorem

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### Bounded projection-valued measures and `∫ λ dP_λ` -/

/-- The function `z ↦ z · 1_{‖z‖ ≤ r}`, a bounded Borel version of `λ ↦ λ`. -/
def ballId (r : ℝ) : boundedMeasurable ℂ :=
  ⟨(Metric.closedBall (0 : ℂ) r).indicator id,
    measurable_id.indicator measurableSet_closedBall, |r|, fun z => by
      by_cases hz : z ∈ Metric.closedBall (0 : ℂ) r
      · rw [indicator_of_mem hz, id]
        rw [mem_closedBall_zero_iff] at hz
        exact hz.trans (le_abs_self r)
      · rw [indicator_of_notMem hz, norm_zero]
        exact abs_nonneg r⟩

theorem coe_ballId (r : ℝ) :
    ((ballId r : boundedMeasurable ℂ) : ℂ → ℂ) = (Metric.closedBall (0 : ℂ) r).indicator id :=
  rfl

theorem ballId_apply_of_mem {r : ℝ} {z : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) r) :
    ((ballId r : boundedMeasurable ℂ) : ℂ → ℂ) z = z := by
  rw [coe_ballId, indicator_of_mem hz, id]

theorem norm_ballId_le {r : ℝ} (hr : 0 ≤ r) (z : ℂ) :
    ‖((ballId r : boundedMeasurable ℂ) : ℂ → ℂ) z‖ ≤ r := by
  by_cases hz : z ∈ Metric.closedBall (0 : ℂ) r
  · rw [ballId_apply_of_mem hz]
    exact mem_closedBall_zero_iff.mp hz
  · rw [coe_ballId, indicator_of_notMem hz, norm_zero]
    exact hr

namespace ProjectionValuedMeasure

section General

variable {X : Type*} [MeasurableSpace X] (P : ProjectionValuedMeasure X H)

/-- **`∫ f dP` only depends on `f` on a set of full measure**: if `f = g` on a measurable `s`
with `P_s = I`, then `∫ f dP = ∫ g dP`.  Indeed `∫ f dP = (∫ f dP) P_s = ∫ f 1_s dP`. -/
theorem integral_congr_of_eqOn {s : Set X} (hs : MeasurableSet s) (hPs : P s = 1)
    {f g : boundedMeasurable X} (hfg : ∀ x ∈ s, (f : X → ℂ) x = (g : X → ℂ) x) :
    P.integral f = P.integral g := by
  have h : f * boundedMeasurable.indicator hs = g * boundedMeasurable.indicator hs :=
    Subtype.ext (funext fun x => by
      change (f : X → ℂ) x * s.indicator (fun _ => (1 : ℂ)) x =
        (g : X → ℂ) x * s.indicator (fun _ => (1 : ℂ)) x
      by_cases hx : x ∈ s
      · rw [hfg x hx]
      · simp [hx])
  calc P.integral f = P.integral f * P s := by rw [hPs, mul_one]
    _ = P.integral g * P s := by rw [← P.integral_indicator hs, ← map_mul, h, map_mul]
    _ = P.integral g := by rw [hPs, mul_one]

/-- If `P_s = I` then `P_{s ∩ t} = P_t`. -/
theorem apply_inter_of_eq_one {s t : Set X} (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hPs : P s = 1) : P (s ∩ t) = P t := by
  rw [← P.mul_apply hs ht, hPs, one_mul]

end General

/-- **A bounded projection-valued measure** (Reed–Simon I, p. 234): `P_{B̄(0, r)} = I` for some
`r`.  Reed–Simon use the intervals `(-a, a)` on `ℝ`; closed balls give the same notion. -/
def IsBounded {X : Type*} [PseudoMetricSpace X] [Zero X] [MeasurableSpace X]
    (P : ProjectionValuedMeasure X H) : Prop :=
  ∃ r : ℝ, P (Metric.closedBall 0 r) = 1

variable (P : ProjectionValuedMeasure ℂ H)

/-- **`∫ λ dP_λ`** for a bounded p.v.m. `P` on `ℂ` (Reed–Simon I, p. 235): the integral of
`z ↦ z · 1_{‖z‖ ≤ r}` for a radius `r` with `P_{B̄(0, r)} = I`, chosen once and for all; by
`toOperator_eq` the choice does not matter. -/
def toOperator (hP : P.IsBounded) : H →L[ℂ] H :=
  P.integral (ballId hP.choose)

/-- `∫ λ dP_λ = ∫ f dP` for every bounded Borel `f` with `f(z) = z` on a set `s` with
`P_s = I`. -/
theorem toOperator_eq_of_eqOn (hP : P.IsBounded) {s : Set ℂ} (hs : MeasurableSet s)
    (hPs : P s = 1) {f : boundedMeasurable ℂ} (hf : ∀ z ∈ s, (f : ℂ → ℂ) z = z) :
    P.toOperator hP = P.integral f := by
  have hB : MeasurableSet (Metric.closedBall (0 : ℂ) hP.choose) := measurableSet_closedBall
  refine P.integral_congr_of_eqOn (hB.inter hs) ?_ fun z hz => ?_
  · rw [P.apply_inter_of_eq_one hB hs hP.choose_spec, hPs]
  · rw [ballId_apply_of_mem hz.1, hf z hz.2]

/-- **Any radius gives `∫ λ dP_λ`**: `∫ λ dP_λ = ∫ z · 1_{‖z‖ ≤ r} dP` whenever
`P_{B̄(0, r)} = I`. -/
theorem toOperator_eq (hP : P.IsBounded) {r : ℝ} (hr : P (Metric.closedBall 0 r) = 1) :
    P.toOperator hP = P.integral (ballId r) :=
  P.toOperator_eq_of_eqOn hP measurableSet_closedBall hr fun _ hz => ballId_apply_of_mem hz

/-- **`∫ λ dP_λ` is normal.** -/
instance isStarNormal_toOperator (hP : P.IsBounded) : IsStarNormal (P.toOperator hP) :=
  ⟨by
    rw [toOperator, ← map_star]
    exact (show Commute (star (ballId hP.choose)) (ballId hP.choose) from
      Subtype.ext (mul_comm _ _)).map P.integral⟩

/-- `‖∫ λ dP_λ‖ ≤ r` when `P_{B̄(0, r)} = I` and `r ≥ 0`. -/
theorem norm_toOperator_le (hP : P.IsBounded) {r : ℝ} (hr0 : 0 ≤ r)
    (hr : P (Metric.closedBall 0 r) = 1) : ‖P.toOperator hP‖ ≤ r := by
  rw [P.toOperator_eq hP hr]
  exact P.norm_integral_le _ hr0 (norm_ballId_le hr0)

end ProjectionValuedMeasure

/-! ### The p.v.m. of a bounded normal operator -/

/-- `σ(T) ⊆ B̄(0, ‖T‖)`. -/
theorem spectrum_subset_closedBall_norm (T : H →L[ℂ] H) :
    spectrum ℂ T ⊆ Metric.closedBall 0 ‖T‖ := fun z hz => by
  have h := spectrum.subset_closedBall_norm_mul T hz
  rw [Metric.mem_closedBall, dist_zero_right] at h ⊢
  exact h.trans (mul_le_of_le_one_right (norm_nonneg T) ContinuousLinearMap.norm_id_le)

section SpectralPVM

variable (T : H →L[ℂ] H) [IsStarNormal T]

open Classical in
/-- `Ω ↦ χ_Ω(T)` on measurable sets, `0` on the others. -/
def spectralPVMFun (Ω : Set ℂ) : H →L[ℂ] H :=
  if hΩ : MeasurableSet Ω then spectralProjection T hΩ else 0

theorem spectralPVMFun_of_measurableSet {Ω : Set ℂ} (hΩ : MeasurableSet Ω) :
    spectralPVMFun T Ω = spectralProjection T hΩ := by
  classical
  exact dite_eq_left hΩ

/-- **The projection-valued measure of a bounded normal operator** `T`: `Ω ↦ χ_Ω(T)`
(Reed–Simon I, p. 234, Proposition, and Theorem VII.8, p. 235). -/
def spectralPVM : ProjectionValuedMeasure ℂ H where
  toFun := spectralPVMFun T
  isStarProjection' Ω hΩ := by
    rw [spectralPVMFun_of_measurableSet T hΩ]
    exact isStarProjection_spectralProjection hΩ
  empty' := by
    rw [spectralPVMFun_of_measurableSet T MeasurableSet.empty]
    exact spectralProjection_empty
  univ' := by
    rw [spectralPVMFun_of_measurableSet T MeasurableSet.univ]
    exact spectralProjection_of_subset _ (subset_univ _)
  tendsto_sum' Ω hΩ hd ψ := by
    have h : ∀ N, ∑ n ∈ Finset.range N, spectralPVMFun T (Ω n) ψ =
        ∑ n ∈ Finset.range N, spectralProjection T (hΩ n) ψ := fun N =>
      Finset.sum_congr rfl fun n _ => by rw [spectralPVMFun_of_measurableSet T (hΩ n)]
    simp only [h, spectralPVMFun_of_measurableSet T (MeasurableSet.iUnion hΩ)]
    exact tendsto_sum_spectralProjection Ω hΩ hd ψ
  apply_of_not_measurableSet' Ω hΩ := by
    classical
    exact dite_eq_right hΩ

/-- `P_Ω = χ_Ω(T)` for the p.v.m. of `T`. -/
theorem spectralPVM_apply {Ω : Set ℂ} (hΩ : MeasurableSet Ω) :
    spectralPVM T Ω = spectralProjection T hΩ :=
  spectralPVMFun_of_measurableSet T hΩ

/-- `P_Ω = I` for the p.v.m. of `T` when `Ω ⊇ σ(T)`. -/
theorem spectralPVM_of_subset {Ω : Set ℂ} (hΩ : MeasurableSet Ω) (hsub : spectrum ℂ T ⊆ Ω) :
    spectralPVM T Ω = 1 := by
  rw [spectralPVM_apply T hΩ]
  exact spectralProjection_of_subset hΩ hsub

theorem spectralPVM_closedBall_norm : spectralPVM T (Metric.closedBall 0 ‖T‖) = 1 :=
  spectralPVM_of_subset T measurableSet_closedBall (spectrum_subset_closedBall_norm T)

/-- **The p.v.m. of a bounded normal operator is bounded**: `P_{B̄(0, ‖T‖)} = I`. -/
theorem spectralPVM_isBounded : (spectralPVM T).IsBounded :=
  ⟨‖T‖, spectralPVM_closedBall_norm T⟩

/-- **The measures of the p.v.m. of `T` are the spectral measures**, pushed forward from `σ(T)`
to `ℂ`: `⟪ψ, P_Ω ψ⟫ = μ_ψ(Ω ∩ σ(T))`. -/
theorem spectralPVM_measure (ψ : H) :
    (spectralPVM T).measure ψ = (spectralMeasure T ψ).map Subtype.val := by
  refine Measure.ext fun Ω hΩ => ?_
  rw [Measure.map_apply measurable_subtype_coe hΩ]
  have h := (spectralPVM T).inner_apply_eq_measureReal ψ hΩ
  rw [spectralPVM_apply T hΩ, inner_spectralProjection] at h
  have h' := Complex.ofReal_injective h
  rw [measureReal_def, measureReal_def] at h'
  exact ((ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp h').symm

/-- The restriction to `σ(T)` of a bounded Borel function on `ℂ`. -/
def restrictSpectrum (f : boundedMeasurable ℂ) : boundedMeasurable (spectrum ℂ T) :=
  ⟨(f : ℂ → ℂ) ∘ Subtype.val, boundedMeasurable.comp_mem f measurable_subtype_coe⟩

omit [CompleteSpace H] [IsStarNormal T] in
theorem coe_restrictSpectrum (f : boundedMeasurable ℂ) :
    ((restrictSpectrum T f : boundedMeasurable (spectrum ℂ T)) : spectrum ℂ T → ℂ) =
      (f : ℂ → ℂ) ∘ Subtype.val :=
  rfl

/-- **Reed–Simon I, Problem VII.23, first half**: `∫ f(λ) dP_λ = f(T)` for the p.v.m. `P` of
`T` and every bounded Borel `f` on `ℂ` (restricted to `σ(T)` on the right).  Both sides have
the quadratic form `ψ ↦ ∫ f dμ_ψ`. -/
theorem spectralPVM_integral (f : boundedMeasurable ℂ) :
    (spectralPVM T).integral f = borelCalc T (restrictSpectrum T f) :=
  ext_inner_self fun ψ => by
    rw [ProjectionValuedMeasure.inner_integral, spectralPVM_measure, inner_borelCalc_eq_integral,
      MeasureTheory.integral_map measurable_subtype_coe.aemeasurable
        (boundedMeasurable.measurable f).aestronglyMeasurable]
    rfl

/-- **`T = ∫ λ dP_λ`** for the p.v.m. `P` of `T` (Reed–Simon I, p. 235). -/
theorem toOperator_spectralPVM :
    (spectralPVM T).toOperator (spectralPVM_isBounded T) = T := by
  have h : restrictSpectrum T (ballId ‖T‖) = idBM T :=
    Subtype.ext (funext fun z => ballId_apply_of_mem (spectrum_subset_closedBall_norm T z.2))
  rw [(spectralPVM T).toOperator_eq _ (spectralPVM_closedBall_norm T), spectralPVM_integral, h,
    borelCalc_id]

end SpectralPVM

/-! ### The support of a bounded p.v.m. -/

namespace ProjectionValuedMeasure

/-- `P_s = 0` if all the measures `μ_ψ(s) = ‖P_s ψ‖²` vanish. -/
theorem eq_zero_of_measure {X : Type*} [MeasurableSpace X]
    (P : ProjectionValuedMeasure X H) {s : Set X} (hs : MeasurableSet s)
    (h : ∀ ψ, P.measure ψ s = 0) : P s = 0 := by
  refine ContinuousLinearMap.ext fun ψ => ?_
  have h1 := h ψ
  rw [P.measure_apply ψ hs, ENNReal.ofReal_eq_zero] at h1
  have h2 : ‖P s ψ‖ = 0 := le_antisymm (by nlinarith [norm_nonneg (P s ψ)]) (norm_nonneg _)
  rw [norm_eq_zero] at h2
  rw [h2, zero_apply]

variable (P : ProjectionValuedMeasure ℂ H)

/-- **Balls around points of the resolvent set are `P`-null.**  If `z₀ ∉ σ(T)` for
`T = ∫ λ dP_λ` and `R = (z₀ - T)⁻¹`, choose `ε > 0` with `‖R‖ ε < 1`.  For `B = B(z₀, ε)`,
`(z₀ - T) P_B = ∫ (z₀ - λ) 1_B 1_{B̄(0, r)} dP` has norm `≤ ε`, and
`‖P_B‖ = ‖R (z₀ - T) P_B P_B‖ ≤ ‖R‖ ε ‖P_B‖`, so `P_B = 0`. -/
theorem exists_ball_eq_zero (hP : P.IsBounded) {z₀ : ℂ}
    (hz : z₀ ∉ spectrum ℂ (P.toOperator hP)) : ∃ ε > 0, P (Metric.ball z₀ ε) = 0 := by
  obtain ⟨u, hu⟩ := spectrum.notMem_iff.mp hz
  obtain ⟨ε, hε, hεR⟩ := exists_pos_mul_lt one_pos ‖((u⁻¹ : (H →L[ℂ] H)ˣ) : H →L[ℂ] H)‖
  refine ⟨ε, hε, ?_⟩
  have hB : MeasurableSet (Metric.ball z₀ ε) := measurableSet_ball
  have hD : MeasurableSet (Metric.closedBall (0 : ℂ) hP.choose) := measurableSet_closedBall
  set A : H →L[ℂ] H := algebraMap ℂ (H →L[ℂ] H) z₀ - P.toOperator hP
  set Q : H →L[ℂ] H := P (Metric.ball z₀ ε) with hQ
  have h1 : P.integral ((algebraMap ℂ (boundedMeasurable ℂ) z₀ - ballId hP.choose) *
      boundedMeasurable.indicator hB * boundedMeasurable.indicator hD) = A * Q := by
    rw [map_mul, map_mul, map_sub, AlgHomClass.commutes, P.integral_indicator,
      P.integral_indicator, hP.choose_spec, mul_one]
    rfl
  have h2 : ‖A * Q‖ ≤ ε := by
    rw [← h1]
    refine P.norm_integral_le _ hε.le fun z => ?_
    change ‖(z₀ - ((ballId hP.choose : boundedMeasurable ℂ) : ℂ → ℂ) z) *
      (Metric.ball z₀ ε).indicator (fun _ => (1 : ℂ)) z *
      (Metric.closedBall (0 : ℂ) hP.choose).indicator (fun _ => (1 : ℂ)) z‖ ≤ ε
    by_cases hzB : z ∈ Metric.ball z₀ ε
    · by_cases hzD : z ∈ Metric.closedBall (0 : ℂ) hP.choose
      · rw [ballId_apply_of_mem hzD, indicator_of_mem hzB, indicator_of_mem hzD, mul_one,
          mul_one, ← dist_eq_norm, dist_comm]
        exact (Metric.mem_ball.mp hzB).le
      · rw [indicator_of_notMem hzD, mul_zero, norm_zero]
        exact hε.le
    · rw [indicator_of_notMem hzB, mul_zero, zero_mul, norm_zero]
      exact hε.le
  have h3 : Q = ((u⁻¹ : (H →L[ℂ] H)ˣ) : H →L[ℂ] H) * (A * Q) * Q := by
    rw [← hu, ← mul_assoc, Units.inv_mul, one_mul, hQ, P.mul_self hB]
  have h4 : ‖Q‖ ≤ ‖((u⁻¹ : (H →L[ℂ] H)ˣ) : H →L[ℂ] H)‖ * ε * ‖Q‖ := by
    calc ‖Q‖ = ‖((u⁻¹ : (H →L[ℂ] H)ˣ) : H →L[ℂ] H) * (A * Q) * Q‖ := congrArg norm h3
      _ ≤ ‖((u⁻¹ : (H →L[ℂ] H)ˣ) : H →L[ℂ] H)‖ * ‖A * Q‖ * ‖Q‖ :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ ‖((u⁻¹ : (H →L[ℂ] H)ˣ) : H →L[ℂ] H)‖ * ε * ‖Q‖ := by gcongr
  have h5 : ‖Q‖ = 0 :=
    le_antisymm (by nlinarith [norm_nonneg Q, norm_nonneg ((u⁻¹ : (H →L[ℂ] H)ˣ) : H →L[ℂ] H)])
      (norm_nonneg _)
  exact norm_eq_zero.mp h5

/-- **The support of a bounded p.v.m.**: `P_{σ(T)ᶜ} = 0` for `T = ∫ λ dP_λ`.  The open set
`σ(T)ᶜ` is covered by `P`-null balls (`exists_ball_eq_zero`), hence by countably many of them
(second countability of `ℂ`), and each measure `μ_ψ` vanishes on their union. -/
theorem apply_compl_spectrum (hP : P.IsBounded) :
    P (spectrum ℂ (P.toOperator hP))ᶜ = 0 := by
  let s : {p : ℂ × ℝ // P (Metric.ball p.1 p.2) = 0} → Set ℂ := fun i => Metric.ball i.1.1 i.1.2
  obtain ⟨J, hJ, hJU⟩ := TopologicalSpace.isOpen_iUnion_countable s fun _ => Metric.isOpen_ball
  have hsub : (spectrum ℂ (P.toOperator hP))ᶜ ⊆ ⋃ i ∈ J, s i := fun z hz => by
    obtain ⟨ε, hε, h⟩ := P.exists_ball_eq_zero hP hz
    rw [hJU]
    exact mem_iUnion.mpr ⟨⟨(z, ε), h⟩, Metric.mem_ball_self hε⟩
  refine P.eq_zero_of_measure (spectrum.isClosed (𝕜 := ℂ) _).isOpen_compl.measurableSet
    fun ψ => measure_mono_null hsub ((measure_biUnion_null_iff hJ).mpr fun i _ => ?_)
  rw [P.measure_apply ψ Metric.isOpen_ball.measurableSet, i.2]
  simp

/-- `P_{σ(T)} = I` for `T = ∫ λ dP_λ`. -/
theorem apply_spectrum (hP : P.IsBounded) : P (spectrum ℂ (P.toOperator hP)) = 1 := by
  have h := P.compl (spectrum.isClosed (𝕜 := ℂ) (P.toOperator hP)).measurableSet
  rw [P.apply_compl_spectrum hP] at h
  exact (sub_eq_zero.mp h.symm).symm

/-- **Points with a `P`-null neighbourhood are in the resolvent set of `T = ∫ λ dP_λ`**: if
`P_{B(z₀, ε)} = 0` then `S = ∫ (z₀ - λ)⁻¹ 1_{B(z₀, ε)ᶜ} dP` inverts `z₀ - T`, as
`(z₀ - λ) (z₀ - λ)⁻¹ 1_{B(z₀, ε)ᶜ} = 1` on `B̄(0, r) ∩ B(z₀, ε)ᶜ`, a set of full measure. -/
theorem notMem_spectrum_of_ball_eq_zero (hP : P.IsBounded) {z₀ : ℂ} {ε : ℝ} (hε : 0 < ε)
    (h0 : P (Metric.ball z₀ ε) = 0) : z₀ ∉ spectrum ℂ (P.toOperator hP) := by
  have hB : MeasurableSet (Metric.ball z₀ ε) := measurableSet_ball
  have hD : MeasurableSet (Metric.closedBall (0 : ℂ) hP.choose) := measurableSet_closedBall
  have hg : ((Metric.ball z₀ ε)ᶜ.indicator fun z => (z₀ - z)⁻¹) ∈ -- totalisation-audit: allow z ∉ B
      boundedMeasurable ℂ := by
    refine ⟨(measurable_const.sub measurable_id).inv.indicator hB.compl,
      ε⁻¹, fun z => ?_⟩ -- totalisation-audit: allow ε > 0
    by_cases hz : z ∈ (Metric.ball z₀ ε)ᶜ
    · rw [indicator_of_mem hz, norm_inv]
      have hz' : ¬ dist z z₀ < ε := hz
      have h1 : ε ≤ ‖z₀ - z‖ := by
        rw [← dist_eq_norm, dist_comm]
        exact not_lt.mp hz'
      exact inv_anti₀ hε h1
    · rw [indicator_of_notMem hz, norm_zero]
      positivity
  let g : boundedMeasurable ℂ := ⟨_, hg⟩
  let a : boundedMeasurable ℂ := algebraMap ℂ (boundedMeasurable ℂ) z₀ - ballId hP.choose
  have hs : MeasurableSet (Metric.closedBall (0 : ℂ) hP.choose ∩ (Metric.ball z₀ ε)ᶜ) :=
    hD.inter hB.compl
  have hPs : P (Metric.closedBall (0 : ℂ) hP.choose ∩ (Metric.ball z₀ ε)ᶜ) = 1 := by
    rw [P.apply_inter_of_eq_one hD hB.compl hP.choose_spec, P.compl hB, h0, sub_zero]
  have hag : P.integral (a * g) = 1 := by
    refine (P.integral_congr_of_eqOn hs hPs fun z hz => ?_).trans (map_one P.integral)
    change (z₀ - ((ballId hP.choose : boundedMeasurable ℂ) : ℂ → ℂ) z) *
      (Metric.ball z₀ ε)ᶜ.indicator (fun z => (z₀ - z)⁻¹) z = 1 -- totalisation-audit: allow z ∉ B
    rw [ballId_apply_of_mem hz.1, indicator_of_mem hz.2]
    refine mul_inv_cancel₀ (sub_ne_zero.mpr fun h => hz.2 ?_)
    rw [← h]
    exact Metric.mem_ball_self hε
  have hA : algebraMap ℂ (H →L[ℂ] H) z₀ - P.toOperator hP = P.integral a := by
    rw [map_sub, AlgHomClass.commutes]
    rfl
  have h1 : (algebraMap ℂ (H →L[ℂ] H) z₀ - P.toOperator hP) * P.integral g = 1 := by
    rw [hA, ← map_mul, hag]
  have h2 : P.integral g * (algebraMap ℂ (H →L[ℂ] H) z₀ - P.toOperator hP) = 1 := by
    rw [hA, ← map_mul, show g * a = a * g from Subtype.ext (mul_comm _ _), hag]
  exact spectrum.notMem_iff.mpr ⟨⟨_, P.integral g, h1, h2⟩, rfl⟩

/-- **The spectrum of `∫ λ dP_λ` is the support of `P`**: `z ∈ σ(T)` iff `P_{B(z, ε)} ≠ 0` for
every `ε > 0`. -/
theorem mem_spectrum_toOperator_iff (hP : P.IsBounded) {z : ℂ} :
    z ∈ spectrum ℂ (P.toOperator hP) ↔ ∀ ε > 0, P (Metric.ball z ε) ≠ 0 := by
  refine ⟨fun hz ε hε h0 => P.notMem_spectrum_of_ball_eq_zero hP hε h0 hz, fun h => ?_⟩
  by_contra hz
  obtain ⟨ε, hε, h0⟩ := P.exists_ball_eq_zero hP hz
  exact h ε hε h0

end ProjectionValuedMeasure

/-! ### Extension by zero -/

namespace boundedMeasurable

variable {X : Type*} [MeasurableSpace X] {s : Set X} (hs : MeasurableSet s)

open Classical in
/-- The extension by `0` of a bounded measurable function on a measurable set `s`. -/
def extendByZero (g : boundedMeasurable s) : boundedMeasurable X :=
  ⟨fun x => if hx : x ∈ s then (g : s → ℂ) ⟨x, hx⟩ else 0,
    Measurable.dite (boundedMeasurable.measurable g) measurable_const hs, normBound g,
    fun x => by
      dsimp only
      split_ifs
      · exact norm_le_normBound g _
      · rw [norm_zero]
        exact normBound_nonneg g⟩

theorem extendByZero_apply_of_mem (g : boundedMeasurable s) {x : X} (hx : x ∈ s) :
    (extendByZero hs g : X → ℂ) x = (g : s → ℂ) ⟨x, hx⟩ :=
  dite_eq_left hx

theorem extendByZero_apply_of_notMem (g : boundedMeasurable s) {x : X} (hx : x ∉ s) :
    (extendByZero hs g : X → ℂ) x = 0 :=
  dite_eq_right hx

/-- Two bounded measurable functions agreeing on `s` and off `s` are equal. -/
theorem ext_of_mem_of_notMem {F G : boundedMeasurable X}
    (h₁ : ∀ x, x ∈ s → (F : X → ℂ) x = (G : X → ℂ) x)
    (h₂ : ∀ x, x ∉ s → (F : X → ℂ) x = (G : X → ℂ) x) : F = G :=
  Subtype.ext (funext fun x => by
    by_cases hx : x ∈ s
    exacts [h₁ x hx, h₂ x hx])

theorem extendByZero_one : extendByZero hs 1 = indicator hs :=
  ext_of_mem_of_notMem (s := s)
    (fun x hx => by
      rw [extendByZero_apply_of_mem hs _ hx, coe_indicator, indicator_of_mem hx]
      rfl)
    (fun x hx => by
      rw [extendByZero_apply_of_notMem hs _ hx, coe_indicator, indicator_of_notMem hx])

theorem extendByZero_mul (f g : boundedMeasurable s) :
    extendByZero hs (f * g) = extendByZero hs f * extendByZero hs g :=
  ext_of_mem_of_notMem (s := s)
    (fun x hx => by
      change _ = (extendByZero hs f : X → ℂ) x * (extendByZero hs g : X → ℂ) x
      rw [extendByZero_apply_of_mem hs _ hx, extendByZero_apply_of_mem hs _ hx,
        extendByZero_apply_of_mem hs _ hx]
      rfl)
    (fun x hx => by
      change _ = (extendByZero hs f : X → ℂ) x * (extendByZero hs g : X → ℂ) x
      rw [extendByZero_apply_of_notMem hs _ hx, extendByZero_apply_of_notMem hs _ hx,
        extendByZero_apply_of_notMem hs _ hx, zero_mul])

theorem extendByZero_add (f g : boundedMeasurable s) :
    extendByZero hs (f + g) = extendByZero hs f + extendByZero hs g :=
  ext_of_mem_of_notMem (s := s)
    (fun x hx => by
      change _ = (extendByZero hs f : X → ℂ) x + (extendByZero hs g : X → ℂ) x
      rw [extendByZero_apply_of_mem hs _ hx, extendByZero_apply_of_mem hs _ hx,
        extendByZero_apply_of_mem hs _ hx]
      rfl)
    (fun x hx => by
      change _ = (extendByZero hs f : X → ℂ) x + (extendByZero hs g : X → ℂ) x
      rw [extendByZero_apply_of_notMem hs _ hx, extendByZero_apply_of_notMem hs _ hx,
        extendByZero_apply_of_notMem hs _ hx, zero_add])

theorem extendByZero_smul (c : ℂ) (g : boundedMeasurable s) :
    extendByZero hs (c • g) = c • extendByZero hs g :=
  ext_of_mem_of_notMem (s := s)
    (fun x hx => by
      change _ = c * (extendByZero hs g : X → ℂ) x
      rw [extendByZero_apply_of_mem hs _ hx, extendByZero_apply_of_mem hs _ hx]
      rfl)
    (fun x hx => by
      change _ = c * (extendByZero hs g : X → ℂ) x
      rw [extendByZero_apply_of_notMem hs _ hx, extendByZero_apply_of_notMem hs _ hx, mul_zero])

theorem extendByZero_zero : extendByZero hs (0 : boundedMeasurable s) = 0 := by
  simpa using extendByZero_smul hs 0 0

theorem extendByZero_star (g : boundedMeasurable s) :
    extendByZero hs (star g) = star (extendByZero hs g) :=
  ext_of_mem_of_notMem (s := s)
    (fun x hx => by
      change _ = star ((extendByZero hs g : X → ℂ) x)
      rw [extendByZero_apply_of_mem hs _ hx, extendByZero_apply_of_mem hs _ hx]
      rfl)
    (fun x hx => by
      change _ = star ((extendByZero hs g : X → ℂ) x)
      rw [extendByZero_apply_of_notMem hs _ hx, extendByZero_apply_of_notMem hs _ hx, star_zero])

end boundedMeasurable

/-! ### The p.v.m. of `∫ λ dP_λ` is `P` -/

namespace ProjectionValuedMeasure

variable (P : ProjectionValuedMeasure ℂ H)

theorem measurableSet_spectrum (hP : P.IsBounded) :
    MeasurableSet (spectrum ℂ (P.toOperator hP)) :=
  (spectrum.isClosed (𝕜 := ℂ) (P.toOperator hP)).measurableSet

/-- For bounded `P` and `T = ∫ λ dP_λ`: `g ↦ ∫ g̃ dP` on bounded Borel functions on `σ(T)`,
with `g̃` the extension of `g` by `0`.  It is a `⋆`-homomorphism since `P_{σ(T)} = I`. -/
def extendIntegral (hP : P.IsBounded) :
    boundedMeasurable (spectrum ℂ (P.toOperator hP)) →⋆ₐ[ℂ] (H →L[ℂ] H) where
  toFun g := P.integral (boundedMeasurable.extendByZero (P.measurableSet_spectrum hP) g)
  map_one' := by
    rw [boundedMeasurable.extendByZero_one, P.integral_indicator, P.apply_spectrum hP]
  map_mul' f g := by
    rw [boundedMeasurable.extendByZero_mul, map_mul]
  map_zero' := by
    rw [boundedMeasurable.extendByZero_zero, map_zero]
  map_add' f g := by
    rw [boundedMeasurable.extendByZero_add, map_add]
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one, boundedMeasurable.extendByZero_smul,
      boundedMeasurable.extendByZero_one, map_smul, P.integral_indicator, P.apply_spectrum hP,
      Algebra.algebraMap_eq_smul_one]
  map_star' g := by
    rw [boundedMeasurable.extendByZero_star, map_star]

theorem extendIntegral_apply (hP : P.IsBounded)
    (g : boundedMeasurable (spectrum ℂ (P.toOperator hP))) :
    P.extendIntegral hP g =
      P.integral (boundedMeasurable.extendByZero (P.measurableSet_spectrum hP) g) :=
  rfl

/-- `g ↦ ∫ g̃ dP` is a Borel functional calculus for `T = ∫ λ dP_λ` (properties (b)–(d) of
Reed–Simon I, Theorem VII.2): (b) and (d) are those of `∫ · dP`, and (c) holds since `λ̃ = λ` on
`σ(T)`, where `P` is concentrated. -/
theorem isBorelCalculus_extendIntegral (hP : P.IsBounded) :
    IsBorelCalculus (P.toOperator hP) (P.extendIntegral hP) where
  norm_le g C hC0 hC := by
    rw [extendIntegral_apply]
    refine P.norm_integral_le _ hC0 fun x => ?_
    by_cases hx : x ∈ spectrum ℂ (P.toOperator hP)
    · rw [boundedMeasurable.extendByZero_apply_of_mem _ _ hx]
      exact hC _
    · rw [boundedMeasurable.extendByZero_apply_of_notMem _ _ hx, norm_zero]
      exact hC0
  map_id := by
    rw [extendIntegral_apply]
    refine (P.toOperator_eq_of_eqOn hP (P.measurableSet_spectrum hP) (P.apply_spectrum hP)
      fun z hz => ?_).symm
    rw [boundedMeasurable.extendByZero_apply_of_mem _ _ hz]
    rfl
  tendsto g g₀ C hC hlim ψ := by
    simp only [extendIntegral_apply]
    refine P.tendsto_integral_apply _ _ (max C 0) (fun n x => ?_) (fun x => ?_) ψ
    · by_cases hx : x ∈ spectrum ℂ (P.toOperator hP)
      · rw [boundedMeasurable.extendByZero_apply_of_mem _ _ hx]
        exact (hC n _).trans (le_max_left C 0)
      · rw [boundedMeasurable.extendByZero_apply_of_notMem _ _ hx, norm_zero]
        exact le_max_right C 0
    · by_cases hx : x ∈ spectrum ℂ (P.toOperator hP)
      · simp only [boundedMeasurable.extendByZero_apply_of_mem _ _ hx]
        exact hlim _
      · simp only [boundedMeasurable.extendByZero_apply_of_notMem _ _ hx]
        exact tendsto_const_nhds

/-- For bounded `P` with `T = ∫ λ dP_λ`: `g(T) = ∫ g̃ dP` for bounded Borel `g` on `σ(T)`, by
the uniqueness of the Borel functional calculus. -/
theorem borelCalc_toOperator (hP : P.IsBounded)
    (g : boundedMeasurable (spectrum ℂ (P.toOperator hP))) :
    borelCalc (P.toOperator hP) g =
      P.integral (boundedMeasurable.extendByZero (P.measurableSet_spectrum hP) g) := by
  rw [← (P.isBorelCalculus_extendIntegral hP).eq_borelCalc, extendIntegral_apply]

/-- **Reed–Simon I, Problem VII.23, second half**: for a bounded p.v.m. `P` on `ℂ`, the p.v.m.
of `∫ λ dP_λ` is `P`: `χ_Ω(T) = ∫ χ̃_Ω dP = P_Ω`, since `χ̃_Ω = χ_Ω` on `σ(T)` and
`P_{σ(T)} = I`. -/
theorem spectralPVM_toOperator (hP : P.IsBounded) : spectralPVM (P.toOperator hP) = P := by
  refine ProjectionValuedMeasure.ext fun Ω hΩ => ?_
  rw [spectralPVM_apply _ hΩ, spectralProjection, borelCalc_toOperator, ← P.integral_indicator hΩ]
  refine P.integral_congr_of_eqOn (P.measurableSet_spectrum hP) (P.apply_spectrum hP)
    fun z hz => ?_
  rw [boundedMeasurable.extendByZero_apply_of_mem _ _ hz]
  rfl

/-- For bounded `P` with `T = ∫ λ dP_λ`: `∫ f dP = f(T)` for every bounded Borel `f` on `ℂ`. -/
theorem integral_eq_borelCalc (hP : P.IsBounded) (f : boundedMeasurable ℂ) :
    P.integral f = borelCalc (P.toOperator hP) (restrictSpectrum (P.toOperator hP) f) := by
  have h := spectralPVM_integral (P.toOperator hP) f
  rw [P.spectralPVM_toOperator hP] at h
  exact h

end ProjectionValuedMeasure

/-- **`σ(T)` is the support of the p.v.m. of `T`**: for normal `T`, `z ∈ σ(T)` iff
`χ_{B(z, ε)}(T) ≠ 0` for every `ε > 0`. -/
theorem mem_spectrum_iff_spectralPVM_ball (T : H →L[ℂ] H) [IsStarNormal T] {z : ℂ} :
    z ∈ spectrum ℂ T ↔ ∀ ε > 0, spectralPVM T (Metric.ball z ε) ≠ 0 := by
  have h := (spectralPVM T).mem_spectrum_toOperator_iff (spectralPVM_isBounded T) (z := z)
  rwa [toOperator_spectralPVM] at h

/-! ### Theorem VII.8 -/

/-- **Reed–Simon I, Theorem VII.8 (spectral theorem, projection-valued measure form), p. 235,
for normal operators**: `T ↦ {χ_Ω(T)}` and `P ↦ ∫ λ dP_λ` are inverse bijections between the
bounded normal operators and the bounded projection-valued measures on `ℂ`. -/
def spectralPVMEquiv :
    {T : H →L[ℂ] H // IsStarNormal T} ≃ {P : ProjectionValuedMeasure ℂ H // P.IsBounded} where
  toFun T :=
    haveI := T.2
    ⟨spectralPVM T.1, spectralPVM_isBounded T.1⟩
  invFun P := ⟨P.1.toOperator P.2, P.1.isStarNormal_toOperator P.2⟩
  left_inv T := by
    have := T.2
    exact Subtype.ext (toOperator_spectralPVM T.1)
  right_inv P := Subtype.ext (P.1.spectralPVM_toOperator P.2)

theorem spectralPVMEquiv_apply (T : {T : H →L[ℂ] H // IsStarNormal T}) :
    ((spectralPVMEquiv T : {P : ProjectionValuedMeasure ℂ H // P.IsBounded}) :
      ProjectionValuedMeasure ℂ H) = @spectralPVM H _ _ _ T.1 T.2 :=
  rfl

theorem spectralPVMEquiv_symm_apply (P : {P : ProjectionValuedMeasure ℂ H // P.IsBounded}) :
    ((spectralPVMEquiv.symm P : {T : H →L[ℂ] H // IsStarNormal T}) : H →L[ℂ] H) =
      P.1.toOperator P.2 :=
  rfl

/-! ### The self-adjoint version -/

namespace ProjectionValuedMeasure

section Map

variable {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]

/-- `G_* (F_* P) = (G ∘ F)_* P`. -/
theorem map_map (P : ProjectionValuedMeasure X H) {F : X → Y} (hF : Measurable F) {G : Y → Z}
    (hG : Measurable G) : (P.map F hF).map G hG = P.map (G ∘ F) (hG.comp hF) :=
  ProjectionValuedMeasure.ext fun t ht => by
    rw [(P.map F hF).map_apply hG ht, P.map_apply hF (hG ht), P.map_apply (hG.comp hF) ht]
    rfl

/-- `id_* P = P`. -/
theorem map_id' (P : ProjectionValuedMeasure X H) : P.map id measurable_id = P :=
  ProjectionValuedMeasure.ext fun t ht => by
    rw [P.map_apply measurable_id ht]
    rfl

end Map

/-- `∫ λ dP_λ` does not depend on the proof of boundedness, and is transported along equalities
of p.v.m.'s. -/
theorem toOperator_congr {P P' : ProjectionValuedMeasure ℂ H} (h : P = P') (hP : P.IsBounded)
    (hP' : P'.IsBounded) : P.toOperator hP = P'.toOperator hP' := by
  subst h
  rfl

/-- The pushforward along `Complex.ofReal` of a bounded p.v.m. on `ℝ` is bounded. -/
theorem isBounded_map_ofReal {Q : ProjectionValuedMeasure ℝ H} (hQ : Q.IsBounded) :
    (Q.map Complex.ofReal Complex.measurable_ofReal).IsBounded := by
  obtain ⟨r, hr⟩ := hQ
  refine ⟨r, ?_⟩
  rw [Q.map_apply Complex.measurable_ofReal measurableSet_closedBall]
  convert hr using 2
  ext x
  simp [Complex.norm_real]

/-- `∫ λ d(ι_* Q)_λ` is self-adjoint for the pushforward of a bounded p.v.m. `Q` on `ℝ` along
`ι = Complex.ofReal`: it is `∫ ι(x) 1_{|x| ≤ r} dQ`, with a real integrand. -/
theorem isSelfAdjoint_toOperator_map_ofReal (Q : ProjectionValuedMeasure ℝ H)
    (hQ : (Q.map Complex.ofReal Complex.measurable_ofReal).IsBounded) :
    IsSelfAdjoint ((Q.map Complex.ofReal Complex.measurable_ofReal).toOperator hQ) := by
  rw [IsSelfAdjoint, toOperator, ← map_star, integral_map, integral_map]
  congr 1
  refine Subtype.ext (funext fun x => ?_)
  change star (((ballId hQ.choose : boundedMeasurable ℂ) : ℂ → ℂ) x) =
    ((ballId hQ.choose : boundedMeasurable ℂ) : ℂ → ℂ) x
  by_cases hx : (x : ℂ) ∈ Metric.closedBall (0 : ℂ) hQ.choose
  · rw [ballId_apply_of_mem hx]
    exact Complex.conj_ofReal x
  · rw [coe_ballId, indicator_of_notMem hx, star_zero]

/-- The real axis `{z | Im z = 0}` is measurable. -/
theorem _root_.SpectralTheorem.measurableSet_im_eq_zero :
    MeasurableSet (Complex.im ⁻¹' {0} : Set ℂ) :=
  Complex.measurable_im (measurableSet_singleton 0)

/-- **A p.v.m. on `ℂ` carried by `ℝ`** (`P_{ℝ} = I`) is the pushforward along `Complex.ofReal`
of its pushforward to `ℝ` along `Complex.re`. -/
theorem map_ofReal_map_re {P : ProjectionValuedMeasure ℂ H} (hP : P (Complex.im ⁻¹' {0}) = 1) :
    (P.map Complex.re Complex.measurable_re).map Complex.ofReal Complex.measurable_ofReal = P := by
  refine ProjectionValuedMeasure.ext fun Ω hΩ => ?_
  have hΩ' : MeasurableSet (Complex.re ⁻¹' (Complex.ofReal ⁻¹' Ω)) :=
    Complex.measurable_re (Complex.measurable_ofReal hΩ)
  rw [map_apply _ _ hΩ, map_apply _ _ (Complex.measurable_ofReal hΩ),
    ← P.apply_inter_of_eq_one measurableSet_im_eq_zero hΩ' hP,
    ← P.apply_inter_of_eq_one measurableSet_im_eq_zero hΩ hP]
  congr 1
  refine Set.ext fun z => and_congr_right fun hz => ?_
  have h : ((z.re : ℂ)) = z := Complex.ext (Complex.ofReal_re _) (by
    rw [Complex.ofReal_im]
    exact (show z.im = 0 from hz).symm)
  rw [mem_preimage, mem_preimage, h]

end ProjectionValuedMeasure

section SelfAdjoint

variable {T : H →L[ℂ] H}

/-- The p.v.m. of a normal `T` pushed to `ℝ` along `Complex.re` is bounded. -/
theorem isBounded_map_re_spectralPVM [IsStarNormal T] :
    ((spectralPVM T).map Complex.re Complex.measurable_re).IsBounded := by
  refine ⟨‖T‖, ?_⟩
  rw [(spectralPVM T).map_apply Complex.measurable_re measurableSet_closedBall]
  refine spectralPVM_of_subset T (Complex.measurable_re measurableSet_closedBall) fun z hz => ?_
  have h := spectrum_subset_closedBall_norm T hz
  rw [mem_closedBall_zero_iff] at h
  rw [mem_preimage, mem_closedBall_zero_iff, Real.norm_eq_abs]
  exact (Complex.abs_re_le_norm z).trans h

/-- **`A = ∫ f(λ) dP_λ` for the p.v.m. on `ℝ`** (Reed–Simon I, p. 235, Problem VII.23): for the
p.v.m. `Q` of `T` pushed to `ℝ` along `Complex.re`, `∫ f dQ = (f ∘ Re)(T)` for every bounded Borel
`f` on `ℝ`; for self-adjoint `T` this is `f(T)`, as `σ(T) ⊆ ℝ`. -/
theorem integral_map_re_spectralPVM [IsStarNormal T] (f : boundedMeasurable ℝ) :
    ((spectralPVM T).map Complex.re Complex.measurable_re).integral f =
      borelCalc T (restrictSpectrum T
        ⟨(f : ℝ → ℂ) ∘ Complex.re, boundedMeasurable.comp_mem f Complex.measurable_re⟩) := by
  rw [ProjectionValuedMeasure.integral_map, spectralPVM_integral]

/-- `σ(T) ⊆ ℝ` for self-adjoint `T`. -/
theorem spectrum_subset_im_eq_zero (hT : IsSelfAdjoint T) :
    spectrum ℂ T ⊆ Complex.im ⁻¹' {0} := fun _ hz => hT.im_eq_zero_of_mem_spectrum hz

/-- For self-adjoint `T`, the p.v.m. of `T` is carried by `ℝ`: pushing it to `ℝ` along
`Complex.re` and back along `Complex.ofReal` gives it back, since `σ(T) ⊆ ℝ`. -/
theorem map_ofReal_map_re_spectralPVM [IsStarNormal T] (hT : IsSelfAdjoint T) :
    ((spectralPVM T).map Complex.re Complex.measurable_re).map Complex.ofReal
      Complex.measurable_ofReal = spectralPVM T :=
  (spectralPVM T).map_ofReal_map_re
    (spectralPVM_of_subset T measurableSet_im_eq_zero (spectrum_subset_im_eq_zero hT))

/-- **A normal operator is self-adjoint iff its p.v.m. is carried by `ℝ`**, i.e.
`P_{ℝ} = I`. -/
theorem isSelfAdjoint_iff_spectralPVM [IsStarNormal T] :
    IsSelfAdjoint T ↔ spectralPVM T (Complex.im ⁻¹' {0}) = 1 := by
  refine ⟨fun hT => spectralPVM_of_subset T measurableSet_im_eq_zero
    (spectrum_subset_im_eq_zero hT), fun h => ?_⟩
  have hP := (spectralPVM T).map_ofReal_map_re h
  have hb : (((spectralPVM T).map Complex.re Complex.measurable_re).map Complex.ofReal
      Complex.measurable_ofReal).IsBounded := by
    rw [hP]
    exact spectralPVM_isBounded T
  have h2 := ProjectionValuedMeasure.isSelfAdjoint_toOperator_map_ofReal _ hb
  rwa [ProjectionValuedMeasure.toOperator_congr hP hb (spectralPVM_isBounded T),
    toOperator_spectralPVM] at h2

end SelfAdjoint

/-- **Reed–Simon I, Theorem VII.8 (spectral theorem, projection-valued measure form), p. 235**:
there is a one-one correspondence between bounded self-adjoint operators `A` and bounded
projection-valued measures `{P_Ω}` on `ℝ`, given by `A ↦ {χ_Ω(A)}` (the p.v.m. of `A` pushed to
`ℝ` along `Complex.re`) and `{P_Ω} ↦ ∫ λ dP_λ` (computed after pushing `P` to `ℂ`). -/
def selfAdjointPVMEquiv :
    {T : H →L[ℂ] H // IsSelfAdjoint T} ≃ {Q : ProjectionValuedMeasure ℝ H // Q.IsBounded} where
  toFun T :=
    have := T.2.isStarNormal
    ⟨(spectralPVM T.1).map Complex.re Complex.measurable_re, isBounded_map_re_spectralPVM⟩
  invFun Q :=
    ⟨(Q.1.map Complex.ofReal Complex.measurable_ofReal).toOperator
      (ProjectionValuedMeasure.isBounded_map_ofReal Q.2),
      Q.1.isSelfAdjoint_toOperator_map_ofReal _⟩
  left_inv T := by
    have := T.2.isStarNormal
    exact Subtype.ext ((ProjectionValuedMeasure.toOperator_congr
      (map_ofReal_map_re_spectralPVM T.2) _ (spectralPVM_isBounded T.1)).trans
        (toOperator_spectralPVM T.1))
  right_inv Q := by
    refine Subtype.ext ?_
    change (spectralPVM ((Q.1.map Complex.ofReal Complex.measurable_ofReal).toOperator
      (ProjectionValuedMeasure.isBounded_map_ofReal Q.2))).map Complex.re
        Complex.measurable_re = Q.1
    rw [ProjectionValuedMeasure.spectralPVM_toOperator, ProjectionValuedMeasure.map_map]
    exact Q.1.map_id'

theorem selfAdjointPVMEquiv_apply (T : {T : H →L[ℂ] H // IsSelfAdjoint T}) :
    ((selfAdjointPVMEquiv T : {Q : ProjectionValuedMeasure ℝ H // Q.IsBounded}) :
      ProjectionValuedMeasure ℝ H) =
      (@spectralPVM H _ _ _ T.1 T.2.isStarNormal).map Complex.re Complex.measurable_re :=
  rfl

theorem selfAdjointPVMEquiv_symm_apply (Q : {Q : ProjectionValuedMeasure ℝ H // Q.IsBounded}) :
    ((selfAdjointPVMEquiv.symm Q : {T : H →L[ℂ] H // IsSelfAdjoint T}) : H →L[ℂ] H) =
      (Q.1.map Complex.ofReal Complex.measurable_ofReal).toOperator
        (ProjectionValuedMeasure.isBounded_map_ofReal Q.2) :=
  rfl

end SpectralTheorem
