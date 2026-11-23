import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.PiSystem

/-!
# A monotone class theorem for bounded Borel functions

Let `P` be a property of functions `X → ℂ` that holds for every bounded continuous function and
is preserved by sums, scalar multiples and **bounded pointwise limits** of sequences.  Then `P`
holds for every bounded Borel function.

This is the argument behind the uniqueness statements of the Borel functional calculus
(Reed–Simon I, Theorem VII.2, p. 225, and Theorem VIII.5, p. 262): two calculi that agree on
continuous functions and both satisfy (d) ("bounded pointwise limits go to strong limits") agree
on every bounded Borel function.  Reed–Simon note this on p. 225: `𝓑(ℝ)` is the smallest family
closed under limits of form (d) containing `C(ℝ)`.

The proof: indicators of closed sets are bounded pointwise limits of continuous functions
(`HasOuterApproxClosed`, which holds in pseudo-metrizable spaces); the measurable sets whose
indicator has the property form a Dynkin system, so by the π-λ theorem
(`MeasurableSpace.induction_on_inter`) they are all Borel sets; hence simple functions have the
property, and bounded measurable functions are bounded pointwise limits of simple functions
(`StronglyMeasurable.approxBounded`).

## Main definitions and results

* `SpectralTheorem.IsBoundedLimitClosed P`: `P` holds at `0` and is closed under `+`, scalar
  multiplication and bounded pointwise limits of sequences.
* `SpectralTheorem.IsBoundedLimitClosed.of_continuous`: such a `P` that holds for bounded
  continuous functions holds for bounded measurable functions.
-/

open MeasureTheory Filter Set Function
open scoped Topology NNReal

namespace SpectralTheorem

variable {X : Type*}

/-- A property of functions `X → ℂ` closed under `0`, sums, scalar multiples and bounded
pointwise limits of sequences. -/
structure IsBoundedLimitClosed (P : (X → ℂ) → Prop) : Prop where
  zero : P 0
  add : ∀ f g, P f → P g → P (f + g)
  smul : ∀ (c : ℂ) f, P f → P (c • f)
  lim : ∀ (f : ℕ → X → ℂ) (g : X → ℂ) (C : ℝ), (∀ n x, ‖f n x‖ ≤ C) →
    (∀ x, Tendsto (fun n => f n x) atTop (𝓝 (g x))) → (∀ n, P (f n)) → P g

/-- Partial sums of indicators of pairwise disjoint sets: at a point, they are eventually the
indicator of the union, and they take values in `{0, 1}`. -/
theorem sum_indicator_disjoint (f : ℕ → Set X) (hdisj : Pairwise (Disjoint on f)) (x : X) :
    (∀ n, ‖∑ i ∈ Finset.range n, (f i).indicator (fun _ => (1 : ℂ)) x‖ ≤ 1) ∧
      Tendsto (fun n => ∑ i ∈ Finset.range n, (f i).indicator (fun _ => (1 : ℂ)) x) atTop
        (𝓝 ((⋃ i, f i).indicator (fun _ => (1 : ℂ)) x)) := by
  by_cases hx : ∃ j, x ∈ f j
  · obtain ⟨j, hj⟩ := hx
    have hother : ∀ i, i ≠ j → x ∉ f i := fun i hij hi =>
      Set.disjoint_left.mp (hdisj hij) hi hj
    have hsum : ∀ n, ∑ i ∈ Finset.range n, (f i).indicator (fun _ => (1 : ℂ)) x =
        if j < n then 1 else 0 := fun n => by
      split_ifs with hjn
      · rw [Finset.sum_eq_single j (fun i _ hij => indicator_of_notMem (hother i hij) _)
          (fun h => absurd (Finset.mem_range.mpr hjn) h), indicator_of_mem hj]
      · refine Finset.sum_eq_zero fun i hi => indicator_of_notMem (hother i ?_) _
        rintro rfl
        exact hjn (Finset.mem_range.mp hi)
    have hU : (⋃ i, f i).indicator (fun _ => (1 : ℂ)) x = 1 :=
      indicator_of_mem (mem_iUnion.mpr ⟨j, hj⟩) _
    refine ⟨fun n => by rw [hsum n]; split_ifs <;> simp, ?_⟩
    rw [hU]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop j] with n hn
    rw [hsum n, ite_eq_left_iff.mpr fun h => absurd hn h]
  · push Not at hx
    have hsum : ∀ n, ∑ i ∈ Finset.range n, (f i).indicator (fun _ => (1 : ℂ)) x = 0 :=
      fun n => Finset.sum_eq_zero fun i _ => indicator_of_notMem (hx i) _
    have hU : (⋃ i, f i).indicator (fun _ => (1 : ℂ)) x = 0 :=
      indicator_of_notMem (by simpa using hx) _
    refine ⟨fun n => by simp [hsum n], ?_⟩
    rw [hU]
    exact tendsto_const_nhds.congr fun n => (hsum n).symm

namespace IsBoundedLimitClosed

variable {P : (X → ℂ) → Prop} (hP : IsBoundedLimitClosed P)
include hP

/-- Finite sums. -/
theorem sum {ι : Type*} (s : Finset ι) (f : ι → X → ℂ) (hf : ∀ i ∈ s, P (f i)) :
    P (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hP.zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact hP.add _ _ (hf a (Finset.mem_insert_self a s))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

/-- Indicators of closed sets: they are bounded pointwise limits of continuous functions with
values in `[0, 1]`. -/
theorem indicator_isClosed [TopologicalSpace X] [HasOuterApproxClosed X]
    (hcont : ∀ f : X → ℂ, Continuous f → (∃ C, ∀ x, ‖f x‖ ≤ C) → P f)
    {F : Set X} (hF : IsClosed F) : P (F.indicator fun _ => 1) := by
  let f : ℕ → X → ℂ := fun n x => ((hF.apprSeq n x : ℝ) : ℂ)
  have hbound : ∀ n x, ‖f n x‖ ≤ 1 := fun n x => by
    simp only [f, Complex.norm_real, Real.norm_eq_abs, NNReal.abs_eq]
    exact_mod_cast HasOuterApproxClosed.apprSeq_apply_le_one hF n x
  refine hP.lim f _ 1 hbound (fun x => ?_) fun n => hcont _ (by fun_prop) ⟨1, hbound n⟩
  have h := (tendsto_pi_nhds.mp (HasOuterApproxClosed.tendsto_apprSeq hF)) x
  have h' := ((Complex.continuous_ofReal.comp NNReal.continuous_coe).tendsto _).comp h
  have hlim : F.indicator (fun _ => (1 : ℂ)) x =
      (fun r : ℝ≥0 => ((r : ℝ) : ℂ)) (F.indicator (fun _ => (1 : ℝ≥0)) x) := by
    by_cases hx : x ∈ F <;> simp [hx]
  rw [hlim]
  exact h'

variable [TopologicalSpace X] [HasOuterApproxClosed X] [MeasurableSpace X] [BorelSpace X]
  (hcont : ∀ f : X → ℂ, Continuous f → (∃ C, ∀ x, ‖f x‖ ≤ C) → P f)
include hcont

/-- Indicators of Borel sets: the measurable sets whose indicator has the property form a Dynkin
system containing the closed sets, a π-system generating the Borel σ-algebra. -/
theorem indicator_measurableSet {E : Set X} (hE : MeasurableSet E) :
    P (E.indicator fun _ => 1) := by
  have hone : P (fun _ => 1) := hcont _ continuous_const ⟨1, fun _ => by simp⟩
  have h_eq : ‹MeasurableSpace X› = MeasurableSpace.generateFrom {F : Set X | IsClosed F} :=
    BorelSpace.measurable_eq.trans borel_eq_generateFrom_isClosed
  have h_pi : IsPiSystem {F : Set X | IsClosed F} := fun s hs t ht _ => IsClosed.inter hs ht
  refine MeasurableSpace.induction_on_inter (C := fun E _ => P (E.indicator fun _ => 1)) h_eq
    h_pi ?_ (fun F hF => hP.indicator_isClosed hcont hF) (fun t _ ht => ?_)
    (fun f hdisj _ hf => ?_) E hE
  · rw [Set.indicator_empty]
    exact hP.zero
  · have h : tᶜ.indicator (fun _ => (1 : ℂ)) =
        (fun _ => (1 : ℂ)) + (-1 : ℂ) • t.indicator (fun _ => (1 : ℂ)) := by
      funext x
      by_cases hx : x ∈ t <;> simp [hx]
    rw [h]
    exact hP.add _ _ hone (hP.smul _ _ ht)
  · refine hP.lim (fun n x => ∑ i ∈ Finset.range n, (f i).indicator (fun _ => (1 : ℂ)) x) _ 1
      (fun n x => (sum_indicator_disjoint f hdisj x).1 n)
      (fun x => (sum_indicator_disjoint f hdisj x).2) fun n => ?_
    have h := hP.sum (Finset.range n) (fun i => (f i).indicator fun _ => (1 : ℂ))
      fun i _ => hf i
    convert h using 1
    funext x
    simp

/-- Simple functions. -/
theorem simpleFunc (s : SimpleFunc X ℂ) : P s := by
  induction s using SimpleFunc.induction with
  | @const c E hE =>
    have h : ⇑(SimpleFunc.piecewise E hE (SimpleFunc.const X c) (SimpleFunc.const X 0)) =
        c • E.indicator (fun _ => (1 : ℂ)) := by
      funext x
      by_cases hx : x ∈ E <;> simp [hx]
    rw [h]
    exact hP.smul c _ (hP.indicator_measurableSet hcont hE)
  | @add f g _ hf hg =>
    rw [SimpleFunc.coe_add]
    exact hP.add _ _ hf hg

/-- **The monotone class theorem for bounded Borel functions.**  A property of functions `X → ℂ`
that holds for bounded continuous functions and is closed under `0`, sums, scalar multiples and
bounded pointwise limits of sequences holds for every bounded measurable function. -/
theorem of_continuous {g : X → ℂ} (hg : Measurable g) {C : ℝ} (hC : ∀ x, ‖g x‖ ≤ C) :
    P g := by
  have hgs : StronglyMeasurable g := hg.stronglyMeasurable
  refine hP.lim (fun n => hgs.approxBounded (max C 0) n) g (max C 0)
    (fun n x => hgs.norm_approxBounded_le (le_max_right C 0) n x)
    (fun x => hgs.tendsto_approxBounded_of_norm_le ((hC x).trans (le_max_left C 0)))
    fun n => hP.simpleFunc hcont _

end IsBoundedLimitClosed

end SpectralTheorem
