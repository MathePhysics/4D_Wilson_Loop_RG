import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Algebra.Module.Torsion.Free
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Projection-valued measures

**Reed–Simon I, p. 234 (Proposition) and p. 235 (Definition).**  A *projection-valued measure*
is a family `{P_Ω}` of operators indexed by the Borel sets with (a) each `P_Ω` an orthogonal
projection; (b) `P_∅ = 0` and `P_(-a,a) = I` for some `a`; (c) if `Ω = ⋃ₙ Ωₙ` with the `Ωₙ`
pairwise disjoint, then `P_Ω = s-lim_{N→∞} Σ_{n=1}^N P_{Ωₙ}`.  Reed–Simon add that
(d) `P_Ω₁ P_Ω₂ = P_{Ω₁ ∩ Ω₂}` follows from (a) and (c) "by abstract considerations"
(Problem VII.22), and that `(φ, P_Ω φ)` is an ordinary measure for every `φ`.

For unbounded operators (p. 263) the condition `P_(-a,a) = I` is replaced by `P_ℝ = I`.  This
is the notion formalised here, on an arbitrary measurable space `X`, with `P_X = I`.

The proof of (d) (Problem VII.22): for disjoint `s`, `t`, finite additivity (from (b), (c))
gives `P_s + P_t = P_{s ∪ t}`, an idempotent, so `P_s P_t + P_t P_s = 0`, and an idempotent
anticommuting with an element annihilates it: `P_s P_t = 0`.  For general `s`, `t` split
`s = (s \ t) ∪ (s ∩ t)` and `t = (t \ s) ∪ (s ∩ t)`.  The measure `Ω ↦ (ψ, P_Ω ψ) = ‖P_Ω ψ‖²`
is countably additive by (c) and the continuity of `φ ↦ (ψ, φ)`.

## Main definitions and results

* `SpectralTheorem.ProjectionValuedMeasure X H`: projection-valued measures on `X`.
* `ProjectionValuedMeasure.ext`: p.v.m.'s agreeing on measurable sets are equal.
* `ProjectionValuedMeasure.union`: finite additivity.
* `ProjectionValuedMeasure.mul_apply`: (d) `P_s P_t = P_{s ∩ t}`; `commute`, `compl`, `mono`.
* `ProjectionValuedMeasure.measure P ψ`: the finite measure `s ↦ ‖P_s ψ‖²`, with
  `inner_apply_eq_measureReal : ⟪ψ, P_s ψ⟫ = (P.measure ψ).real s`.
* `ProjectionValuedMeasure.map`: the pushforward `t ↦ P_{F⁻¹(t)}` along a measurable map.
-/

noncomputable section

open scoped InnerProductSpace ENNReal Topology
open MeasureTheory Filter Set

namespace SpectralTheorem

universe u

/-- **A projection-valued measure** on `X` (Reed–Simon I, pp. 234–235 and 263): (a) `P_s` is an
orthogonal projection for measurable `s`; (b) `P_∅ = 0` and `P_X = 1`; (c) strong countable
additivity on pairwise disjoint measurable sets.  The last field normalises the values on
non-measurable sets, which play no role, to `0`; with it two p.v.m.'s agreeing on measurable
sets are equal (`ProjectionValuedMeasure.ext`). -/
structure ProjectionValuedMeasure (X : Type*) [MeasurableSpace X] (H : Type u)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] where
  /-- The operator `P_s` attached to a set `s`. -/
  toFun : Set X → H →L[ℂ] H
  isStarProjection' : ∀ s, MeasurableSet s → IsStarProjection (toFun s)
  empty' : toFun ∅ = 0
  univ' : toFun Set.univ = 1
  tendsto_sum' : ∀ s : ℕ → Set X, (∀ n, MeasurableSet (s n)) →
    Pairwise (Function.onFun Disjoint s) → ∀ ψ : H,
    Tendsto (fun N => ∑ n ∈ Finset.range N, toFun (s n) ψ) atTop (𝓝 (toFun (⋃ n, s n) ψ))
  apply_of_not_measurableSet' : ∀ s, ¬ MeasurableSet s → toFun s = 0

namespace ProjectionValuedMeasure

variable {X : Type*} [MeasurableSpace X]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

instance : FunLike (ProjectionValuedMeasure X H) (Set X) (H →L[ℂ] H) where
  coe P := P.toFun
  coe_injective P Q h := by
    cases P
    cases Q
    congr

variable (P : ProjectionValuedMeasure X H)

@[simp]
theorem toFun_eq_coe : P.toFun = ⇑P :=
  rfl

/-- (a) `P_s` is an orthogonal projection. -/
theorem isStarProjection {s : Set X} (hs : MeasurableSet s) : IsStarProjection (P s) :=
  P.isStarProjection' s hs

/-- (b) `P_∅ = 0`. -/
@[simp]
theorem empty : P ∅ = 0 :=
  P.empty'

/-- (b) `P_X = 1`. -/
@[simp]
theorem univ : P Set.univ = 1 :=
  P.univ'

/-- (c) Strong countable additivity. -/
theorem tendsto_sum (s : ℕ → Set X) (hs : ∀ n, MeasurableSet (s n))
    (hd : Pairwise (Function.onFun Disjoint s)) (ψ : H) :
    Tendsto (fun N => ∑ n ∈ Finset.range N, P (s n) ψ) atTop (𝓝 (P (⋃ n, s n) ψ)) :=
  P.tendsto_sum' s hs hd ψ

theorem apply_of_not_measurableSet {s : Set X} (hs : ¬ MeasurableSet s) : P s = 0 :=
  P.apply_of_not_measurableSet' s hs

/-- Two projection-valued measures agreeing on measurable sets are equal. -/
@[ext]
theorem ext {P Q : ProjectionValuedMeasure X H} (h : ∀ s, MeasurableSet s → P s = Q s) :
    P = Q := by
  refine DFunLike.coe_injective (funext fun s => ?_)
  by_cases hs : MeasurableSet s
  · exact h s hs
  · rw [P.apply_of_not_measurableSet hs, Q.apply_of_not_measurableSet hs]

theorem isSelfAdjoint {s : Set X} (hs : MeasurableSet s) : IsSelfAdjoint (P s) :=
  (P.isStarProjection hs).isSelfAdjoint

theorem mul_self {s : Set X} (hs : MeasurableSet s) : P s * P s = P s :=
  (P.isStarProjection hs).isIdempotentElem.eq

/-- **Finite additivity**: `P_{s ∪ t} = P_s + P_t` for disjoint measurable `s`, `t`. -/
theorem union {s t : Set X} (hs : MeasurableSet s) (ht : MeasurableSet t) (hst : Disjoint s t) :
    P (s ∪ t) = P s + P t := by
  classical
  let f : ℕ → Set X := fun n => if n = 0 then s else if n = 1 then t else ∅
  have hf : ∀ n, MeasurableSet (f n) := fun n => by
    simp only [f]
    split_ifs
    exacts [hs, ht, MeasurableSet.empty]
  have hd : Pairwise (Function.onFun Disjoint f) := by
    intro i j hij
    simp only [Function.onFun, f]
    split_ifs <;> first | omega | exact hst | exact hst.symm | simp
  have hU : (⋃ n, f n) = s ∪ t := by
    ext x
    simp only [mem_iUnion, mem_union, f]
    constructor
    · rintro ⟨n, hn⟩
      split_ifs at hn
      exacts [Or.inl hn, Or.inr hn, absurd hn (notMem_empty x)]
    · rintro (hx | hx)
      exacts [⟨0, by simpa using hx⟩, ⟨1, by simpa using hx⟩]
  refine ContinuousLinearMap.ext fun ψ => ?_
  have h := P.tendsto_sum f hf hd ψ
  rw [hU] at h
  refine tendsto_nhds_unique h (tendsto_const_nhds.congr' ?_)
  filter_upwards [eventually_ge_atTop 2] with N hN
  obtain ⟨k, rfl⟩ : ∃ k, N = k + 2 := ⟨N - 2, by omega⟩
  rw [Finset.sum_range_succ', Finset.sum_range_succ', Finset.sum_eq_zero fun n _ => by
    simp [f]]
  simp [f, add_comm]

/-- For disjoint measurable `s`, `t`: `P_s P_t = 0`.  `P_s + P_t = P_{s ∪ t}` is idempotent, so
`P_s P_t + P_t P_s = 0`, and an idempotent anticommuting with an element annihilates it. -/
theorem mul_eq_zero_of_disjoint {s t : Set X} (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hst : Disjoint s t) : P s * P t = 0 := by
  have := IsAddTorsionFree.of_isTorsionFree ℂ (H →L[ℂ] H)
  have h : IsIdempotentElem (P s + P t) := by
    rw [← P.union hs ht hst]
    exact (P.isStarProjection (hs.union ht)).isIdempotentElem
  have hs' := (P.isStarProjection hs).isIdempotentElem
  exact hs'.mul_eq_zero_of_anticommute
    ((hs'.add_iff (P.isStarProjection ht).isIdempotentElem).mp h)

/-- **(d) `P_s P_t = P_{s ∩ t}`** (Reed–Simon I, p. 235, Problem VII.22). -/
theorem mul_apply {s t : Set X} (hs : MeasurableSet s) (ht : MeasurableSet t) :
    P s * P t = P (s ∩ t) := by
  have h1 : P s = P (s \ t) + P (s ∩ t) := by
    rw [← P.union (hs.diff ht) (hs.inter ht) disjoint_sdiff_inter, sdiff_union_inter]
  have h2 : P t = P (t \ s) + P (s ∩ t) := by
    rw [inter_comm, ← P.union (ht.diff hs) (ht.inter hs) disjoint_sdiff_inter,
      sdiff_union_inter]
  have hA : P (s \ t) * P (t \ s) = 0 :=
    P.mul_eq_zero_of_disjoint (hs.diff ht) (ht.diff hs) disjoint_sdiff_sdiff
  have hB : P (s \ t) * P (s ∩ t) = 0 :=
    P.mul_eq_zero_of_disjoint (hs.diff ht) (hs.inter ht) disjoint_sdiff_inter
  have hC : P (s ∩ t) * P (t \ s) = 0 := by
    refine P.mul_eq_zero_of_disjoint (hs.inter ht) (ht.diff hs) ?_
    rw [inter_comm]
    exact disjoint_sdiff_inter.symm
  rw [h1, h2, add_mul, mul_add, mul_add, hA, hB, hC, P.mul_self (hs.inter ht)]
  simp

theorem commute {s t : Set X} (hs : MeasurableSet s) (ht : MeasurableSet t) :
    Commute (P s) (P t) := by
  change P s * P t = P t * P s
  rw [P.mul_apply hs ht, P.mul_apply ht hs, inter_comm]

/-- `P_{sᶜ} = 1 - P_s`. -/
theorem compl {s : Set X} (hs : MeasurableSet s) : P sᶜ = 1 - P s := by
  rw [eq_sub_iff_add_eq', ← P.union hs hs.compl disjoint_compl_right, union_compl_self, P.univ]

/-- Monotonicity: `P_s P_t = P_s` for `s ⊆ t`. -/
theorem mono {s t : Set X} (hs : MeasurableSet s) (ht : MeasurableSet t) (hst : s ⊆ t) :
    P s * P t = P s := by
  rw [P.mul_apply hs ht, inter_eq_left.mpr hst]

/-- `⟪ψ, P_s ψ⟫ = ‖P_s ψ‖²`. -/
theorem inner_apply_self (ψ : H) {s : Set X} (hs : MeasurableSet s) :
    ⟪ψ, P s ψ⟫_ℂ = ((‖P s ψ‖ ^ 2 : ℝ) : ℂ) := by
  have h : P s (P s ψ) = P s ψ := DFunLike.congr_fun (P.mul_self hs) ψ
  calc ⟪ψ, P s ψ⟫_ℂ = ⟪ψ, P s (P s ψ)⟫_ℂ := by rw [h]
    _ = ⟪P s ψ, P s ψ⟫_ℂ := ((P.isSelfAdjoint hs).isSymmetric ψ (P s ψ)).symm
    _ = ((‖P s ψ‖ ^ 2 : ℝ) : ℂ) := by
      rw [inner_self_eq_norm_sq_to_K]
      push_cast
      rfl

theorem norm_apply_sq_eq_re_inner (ψ : H) {s : Set X} (hs : MeasurableSet s) :
    ‖P s ψ‖ ^ 2 = (⟪ψ, P s ψ⟫_ℂ).re := by
  rw [P.inner_apply_self ψ hs, Complex.ofReal_re]

/-- `‖P_s ψ‖ ≤ ‖ψ‖`. -/
theorem norm_apply_le (ψ : H) (s : Set X) : ‖P s ψ‖ ≤ ‖ψ‖ := by
  by_cases hs : MeasurableSet s
  · have h := norm_inner_le_norm (𝕜 := ℂ) ψ (P s ψ)
    rw [P.inner_apply_self ψ hs, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)] at h
    nlinarith [norm_nonneg ψ, norm_nonneg (P s ψ)]
  · simp [P.apply_of_not_measurableSet hs]

/-! ### The measures `s ↦ ⟪ψ, P_s ψ⟫` -/

/-- **The measure `s ↦ ⟪ψ, P_s ψ⟫ = ‖P_s ψ‖²`** (Reed–Simon I, p. 235: "`(φ, P_Ω φ)` is an
ordinary measure").  Countable additivity: `Σ_{n<N} ⟪ψ, P_{sₙ} ψ⟫ = ⟪ψ, Σ_{n<N} P_{sₙ} ψ⟫`
converges to `⟪ψ, P_{⋃ sₙ} ψ⟫` by (c). -/
def measure (ψ : H) : Measure X :=
  Measure.ofMeasurable (fun s _ => ENNReal.ofReal (‖P s ψ‖ ^ 2)) (by simp) fun f hf hd => by
    have hsum : ∀ N, ∑ n ∈ Finset.range N, ENNReal.ofReal (‖P (f n) ψ‖ ^ 2) =
        ENNReal.ofReal (⟪ψ, ∑ n ∈ Finset.range N, P (f n) ψ⟫_ℂ).re := fun N => by
      rw [inner_sum, Complex.re_sum,
        ← ENNReal.ofReal_sum_of_nonneg fun n _ => sq_nonneg ‖P (f n) ψ‖]
      exact congrArg ENNReal.ofReal
        (Finset.sum_congr rfl fun n _ => P.norm_apply_sq_eq_re_inner ψ (hf n))
    have h1 := ENNReal.tendsto_ofReal ((Complex.continuous_re.tendsto _).comp
      ((tendsto_const_nhds (x := ψ)).inner (P.tendsto_sum f hf hd ψ)))
    rw [← P.norm_apply_sq_eq_re_inner ψ (MeasurableSet.iUnion hf)] at h1
    refine tendsto_nhds_unique ?_ (ENNReal.tendsto_nat_tsum _)
    simp only [hsum]
    exact h1

theorem measure_apply (ψ : H) {s : Set X} (hs : MeasurableSet s) :
    P.measure ψ s = ENNReal.ofReal (‖P s ψ‖ ^ 2) :=
  Measure.ofMeasurable_apply s hs

/-- The total mass of `P.measure ψ` is `‖ψ‖²`. -/
theorem measure_univ (ψ : H) : P.measure ψ Set.univ = ENNReal.ofReal (‖ψ‖ ^ 2) := by
  rw [P.measure_apply ψ MeasurableSet.univ, P.univ, one_apply_eq_self]

instance isFiniteMeasure (ψ : H) : IsFiniteMeasure (P.measure ψ) :=
  ⟨by rw [P.measure_univ]; exact ENNReal.ofReal_lt_top⟩

theorem measureReal_apply (ψ : H) {s : Set X} (hs : MeasurableSet s) :
    (P.measure ψ).real s = ‖P s ψ‖ ^ 2 := by
  rw [measureReal_def, P.measure_apply ψ hs, ENNReal.toReal_ofReal (sq_nonneg _)]

/-- **`⟪ψ, P_s ψ⟫ = μ_ψ(s)`**. -/
theorem inner_apply_eq_measureReal (ψ : H) {s : Set X} (hs : MeasurableSet s) :
    ⟪ψ, P s ψ⟫_ℂ = ((P.measure ψ).real s : ℂ) := by
  rw [P.inner_apply_self ψ hs, P.measureReal_apply ψ hs]

/-! ### Pushforward -/

variable {Y : Type*} [MeasurableSpace Y]

open Classical in
/-- **The pushforward** of `P` along a measurable map `F : X → Y`: `t ↦ P_{F⁻¹(t)}` on
measurable `t` (and `0` on the other sets). -/
def map (F : X → Y) (hF : Measurable F) : ProjectionValuedMeasure Y H where
  toFun t := if MeasurableSet t then P (F ⁻¹' t) else 0
  isStarProjection' t ht := by
    rw [ite_eq_left ht]
    exact P.isStarProjection (hF ht)
  empty' := by simp
  univ' := by simp
  tendsto_sum' s hs hd ψ := by
    simp only [hs, MeasurableSet.iUnion hs, ite_true, preimage_iUnion]
    exact P.tendsto_sum _ (fun n => hF (hs n)) (fun i j hij => (hd hij).preimage F) ψ
  apply_of_not_measurableSet' t ht := ite_eq_right ht

theorem map_apply {F : X → Y} (hF : Measurable F) {t : Set Y} (ht : MeasurableSet t) :
    P.map F hF t = P (F ⁻¹' t) := by
  classical
  exact ite_eq_left ht

/-- The measures of the pushforward are the pushforwards of the measures. -/
theorem measure_map {F : X → Y} (hF : Measurable F) (ψ : H) :
    (P.map F hF).measure ψ = (P.measure ψ).map F :=
  Measure.ext fun t ht => by
    rw [measure_apply _ ψ ht, Measure.map_apply hF ht, P.measure_apply ψ (hF ht),
      P.map_apply hF ht]

end ProjectionValuedMeasure

end SpectralTheorem
