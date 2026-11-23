/-
`def:distance` and `lem:distance` of BALABAN_CORE.tex: the weighted distance.

Setting. The torus is `𝕋 = (ℝ/pℤ)⁴` with the distance `|·|_∞`. The proof of `lem:distance` uses of a
sequence of domains only that `𝕋 = Ω₀ ⊃ Ω₁ ⊃ ⋯ ⊃ Ω_k`, `Ω_{k+1} = ∅`, are closed, that the
spacings satisfy `0 < η = a₀ ≤ a_j ≤ a_k = 1`, and, for (ii), the separation
`dist(Ω_i^c, Ω_{i+1}) ≥ RMa_i` (the core's `eq:separation` is the strict inequality between the
sets, which implies this); these are the hypotheses here.

Modelling (as `Manifold.pathELength` of Mathlib, whose definition was checked: the length is
`∫⁻ t in Icc a b` of the norm of the derivative, valued in `ℝ≥0∞`):
* a path from `z` to `z'` is given by a Lipschitz lift `γ̃ : ℝ → ℝ⁴` on a parameter interval
  `[0, T]` with `π(γ̃ 0) = z`, `π(γ̃ T) = z'`. The core takes Lipschitz paths `[0, 1] → 𝕋`; every such
  path has a Lipschitz lift, and the weighted length does not change under the affine change of the
  parameter interval (neither fact is formalised here);
* `|γ̇(t)|₁ = Σ_ν |γ̃_ν'(t)|`, with the derivative of each coordinate (which exists a.e.);
* `ℓ(γ) = ∫⁻_{[0, T]} a_{j(γ(t))}⁻¹ |γ̇(t)|₁ dt` and `d(z, z') = inf ℓ(γ)` in `ℝ≥0∞`.
-/
import CoreLean.Tour
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal

noncomputable section

namespace CoreLean

variable {p : ℝ}

/-- The torus `(ℝ/pℤ)⁴` with the distance `|·|_∞`. -/
abbrev Tor (p : ℝ) := Fin 4 → AddCircle p

/-- The projection `ℝ⁴ → 𝕋`. -/
def projT (p : ℝ) (x : Fin 4 → ℝ) : Tor p := fun ν => (x ν : AddCircle p)

/-- The distance `|z - z'|₁` of the torus. -/
def dist1 (z z' : Tor p) : ℝ := ∑ ν, ‖z ν - z' ν‖

lemma dist1_nonneg (z z' : Tor p) : 0 ≤ dist1 z z' :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

lemma norm_coe_sub_le (x y : ℝ) : ‖((x : AddCircle p) - (y : AddCircle p))‖ ≤ |x - y| := by
  rw [← AddCircle.coe_sub]; exact QuotientAddGroup.norm_mk_le_norm

lemma dist1_projT_le (x y : Fin 4 → ℝ) : dist1 (projT p x) (projT p y) ≤ ∑ ν, |x ν - y ν| :=
  Finset.sum_le_sum fun ν _ => norm_coe_sub_le _ _

lemma continuous_projT : Continuous (projT p) :=
  continuous_pi fun ν => (AddCircle.continuous_mk' p).comp (continuous_apply ν)

/-! ### The data of a sequence of domains and the weight -/

/-- The data of `lem:distance`: closed decreasing domains and the spacings. -/
structure DomainData (p : ℝ) where
  k : ℕ
  Ω : ℕ → Set (Tor p)
  a : ℕ → ℝ
  Ω_zero : Ω 0 = univ
  Ω_succ : ∀ j, Ω (j + 1) ⊆ Ω j
  Ω_closed : ∀ j, IsClosed (Ω j)
  Ω_top : Ω (k + 1) = ∅
  a_pos : 0 < a 0
  a_mono : ∀ i j, i ≤ j → a i ≤ a j
  a_top : a k = 1

namespace DomainData

variable (D : DomainData p)

lemma Ω_anti {i j : ℕ} (h : i ≤ j) : D.Ω j ⊆ D.Ω i := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact (D.Ω_succ _).trans ih

/-- `j(z)`: the largest `j ≤ k` with `z ∈ Ω_j`. -/
def scale (z : Tor p) : ℕ := by
  classical exact Nat.findGreatest (fun j => z ∈ D.Ω j) D.k

lemma scale_le (z : Tor p) : D.scale z ≤ D.k := by
  classical exact Nat.findGreatest_le _

lemma scale_eq {z : Tor p} {i : ℕ} (hi : i ≤ D.k) (hz : z ∈ D.Ω i) (hz' : z ∉ D.Ω (i + 1)) :
    D.scale z = i := by
  classical
  unfold scale
  exact Nat.findGreatest_eq_iff.2 ⟨hi, fun _ => hz, fun n hn _ hzn => hz' (D.Ω_anti hn hzn)⟩

lemma mem_scale (z : Tor p) : z ∈ D.Ω (D.scale z) ∧ z ∉ D.Ω (D.scale z + 1) := by
  classical
  have h := (Nat.findGreatest_eq_iff (P := fun j => z ∈ D.Ω j) (k := D.k)
    (m := D.scale z)).1 rfl
  refine ⟨?_, fun hz => ?_⟩
  · rcases Nat.eq_zero_or_pos (D.scale z) with h0 | h0
    · rw [h0, D.Ω_zero]; exact mem_univ _
    · exact h.2.1 h0.ne'
  · rcases lt_or_ge (D.scale z) D.k with hk | hk
    · exact h.2.2 (Nat.lt_succ_self _) hk hz
    · have : D.scale z = D.k := le_antisymm (D.scale_le z) hk
      rw [this, D.Ω_top] at hz; exact hz

lemma a_pos' (j : ℕ) : 0 < D.a j := lt_of_lt_of_le D.a_pos (D.a_mono 0 j (Nat.zero_le j))

/-- The weight `a_{j(z)}⁻¹`. -/
def weight (z : Tor p) : ℝ := (D.a (D.scale z))⁻¹

lemma one_le_weight (z : Tor p) : 1 ≤ D.weight z := by
  unfold weight
  rw [one_le_inv₀ (D.a_pos' _), ← D.a_top]
  exact D.a_mono _ _ (D.scale_le z)

lemma weight_le (z : Tor p) : D.weight z ≤ (D.a 0)⁻¹ :=
  inv_anti₀ D.a_pos (D.a_mono _ _ (Nat.zero_le _))

/-- The weight is a finite sum of multiples of indicators of the Borel sets `Ω_i \ Ω_{i+1}`. -/
lemma weight_eq_sum (z : Tor p) :
    D.weight z = ∑ i ∈ Finset.range (D.k + 1), (D.Ω i \ D.Ω (i + 1)).indicator
      (fun _ => (D.a i)⁻¹) z := by
  rw [Finset.sum_eq_single (D.scale z)]
  · rw [indicator_of_mem (show z ∈ D.Ω (D.scale z) \ D.Ω (D.scale z + 1) from
      ⟨(D.mem_scale z).1, (D.mem_scale z).2⟩)]
    rfl
  · intro i _ hi
    refine indicator_of_notMem (fun hz => hi ?_) _
    exact (D.scale_eq (Nat.lt_succ_iff.1 (Finset.mem_range.1 ‹_›)) hz.1 hz.2).symm
  · intro h; exact absurd (Finset.mem_range.2 (Nat.lt_succ_of_le (D.scale_le z))) h

lemma measurable_weight : Measurable D.weight := by
  rw [show D.weight = fun z => ∑ i ∈ Finset.range (D.k + 1), (D.Ω i \ D.Ω (i + 1)).indicator
      (fun _ => (D.a i)⁻¹) z from funext D.weight_eq_sum]
  exact Finset.measurable_sum _ fun i _ => measurable_const.indicator
    ((D.Ω_closed i).measurableSet.diff (D.Ω_closed (i + 1)).measurableSet)

end DomainData

/-! ### Paths and the weighted length -/

/-- A path from `z` to `z'`: a Lipschitz lift `γ̃ : ℝ → ℝ⁴` on `[0, T]`. -/
structure TPath (p : ℝ) (z z' : Tor p) where
  T : ℝ
  T_nonneg : 0 ≤ T
  γ : ℝ → (Fin 4 → ℝ)
  K : ℝ≥0
  lip : LipschitzWith K γ
  start : projT p (γ 0) = z
  stop : projT p (γ T) = z'

/-- The integrand `a_{j(γ(t))}⁻¹ |γ̇(t)|₁`. -/
def wIntegrand (D : DomainData p) (γ : ℝ → (Fin 4 → ℝ)) (t : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (D.weight (projT p (γ t))) * ∑ ν, ‖deriv (fun s => γ s ν) t‖ₑ

/-- The weighted length `∫⁻_{[a, b]} a_{j(γ(t))}⁻¹ |γ̇(t)|₁ dt` (`eq:weighted-length`). -/
def wlen (D : DomainData p) (γ : ℝ → (Fin 4 → ℝ)) (a b : ℝ) : ℝ≥0∞ :=
  ∫⁻ t in Icc a b, wIntegrand D γ t

/-- The weighted distance (`def:distance`). -/
def wdist (D : DomainData p) (z z' : Tor p) : ℝ≥0∞ := ⨅ P : TPath p z z', wlen D P.γ 0 P.T

lemma measurable_wIntegrand (D : DomainData p) {γ : ℝ → (Fin 4 → ℝ)} (hγ : Continuous γ) :
    Measurable (wIntegrand D γ) :=
  (ENNReal.measurable_ofReal.comp (D.measurable_weight.comp
    (continuous_projT.comp hγ).measurable)).mul
    (Finset.measurable_sum _ fun ν _ => (measurable_deriv _).enorm)

/-! ### The fundamental theorem of calculus for a Lipschitz coordinate -/

/-- `|f(b) - f(a)| ≤ ∫⁻_{[a, b]} |f'|` for a Lipschitz `f : ℝ → ℝ`. -/
lemma ofReal_abs_sub_le_lintegral {f : ℝ → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) {a b : ℝ}
    (hab : a ≤ b) : ENNReal.ofReal |f b - f a| ≤ ∫⁻ t in Icc a b, ‖deriv f t‖ₑ := by
  have hac := (hf.lipschitzOnWith (s := uIcc a b)).absolutelyContinuousOnInterval
  have hftc := hac.integral_deriv_eq_sub
  have hint : IntegrableOn (deriv f) (Icc a b) := by
    refine Integrable.mono' (integrableOn_const (C := (K : ℝ)) (measure_Icc_lt_top).ne)
      (measurable_deriv f).aestronglyMeasurable (Eventually.of_forall fun t => ?_)
    exact norm_deriv_le_of_lipschitz hf
  have h1 : f b - f a = ∫ t in Ioc a b, deriv f t := by
    rw [← hftc, intervalIntegral.integral_of_le hab]
  have hint' : IntegrableOn (deriv f) (Ioc a b) := hint.mono_set Ioc_subset_Icc_self
  rw [h1]
  calc ENNReal.ofReal |∫ t in Ioc a b, deriv f t| ≤ ENNReal.ofReal (∫ t in Ioc a b, |deriv f t|) :=
        ENNReal.ofReal_le_ofReal (abs_integral_le_integral_abs)
    _ = ∫⁻ t in Ioc a b, ‖deriv f t‖ₑ := by
        rw [ofReal_integral_eq_lintegral_ofReal hint'.abs
          (Eventually.of_forall fun t => abs_nonneg _)]
        refine lintegral_congr fun t => ?_
        rw [← Real.norm_eq_abs, ofReal_norm]
    _ ≤ ∫⁻ t in Icc a b, ‖deriv f t‖ₑ := lintegral_mono_set Ioc_subset_Icc_self

/-- `Σ_ν |γ̃_ν(b) - γ̃_ν(a)| ≤ ∫⁻_{[a, b]} |γ̇|₁`. -/
lemma ofReal_sum_abs_sub_le {γ : ℝ → (Fin 4 → ℝ)} {K : ℝ≥0} (hγ : LipschitzWith K γ) {a b : ℝ}
    (hab : a ≤ b) : ENNReal.ofReal (∑ ν, |γ b ν - γ a ν|) ≤
      ∫⁻ t in Icc a b, ∑ ν, ‖deriv (fun s => γ s ν) t‖ₑ := by
  rw [ENNReal.ofReal_sum_of_nonneg (fun ν _ => abs_nonneg _),
    lintegral_finsetSum _ fun ν _ => (measurable_deriv _).enorm]
  refine Finset.sum_le_sum fun ν _ =>
    ofReal_abs_sub_le_lintegral (f := fun s => γ s ν) (K := K) ?_ hab
  have := (LipschitzWith.eval (α := fun _ : Fin 4 => ℝ) ν).comp hγ
  rw [one_mul] at this
  exact this

/-! ### `lem:distance`(i): the two bounds -/

/-- The lower bound `|z - z'|₁ ≤ ℓ(γ)` for every path. -/
lemma dist1_le_wlen (D : DomainData p) {z z' : Tor p} (P : TPath p z z') :
    ENNReal.ofReal (dist1 z z') ≤ wlen D P.γ 0 P.T := by
  have h1 := ofReal_sum_abs_sub_le P.lip P.T_nonneg
  have h2 : dist1 z z' ≤ ∑ ν, |P.γ P.T ν - P.γ 0 ν| := by
    calc dist1 z z' = dist1 (projT p (P.γ 0)) (projT p (P.γ P.T)) := by rw [P.start, P.stop]
      _ ≤ ∑ ν, |P.γ 0 ν - P.γ P.T ν| := dist1_projT_le _ _
      _ = ∑ ν, |P.γ P.T ν - P.γ 0 ν| := Finset.sum_congr rfl fun ν _ => abs_sub_comm _ _
  refine (ENNReal.ofReal_le_ofReal h2).trans (h1.trans (lintegral_mono fun t => ?_))
  unfold wIntegrand
  refine le_mul_of_one_le_left zero_le ?_
  rw [← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal (D.one_le_weight _)

theorem dist1_le_wdist (D : DomainData p) (z z' : Tor p) :
    ENNReal.ofReal (dist1 z z') ≤ wdist D z z' :=
  le_iInf fun P => dist1_le_wlen D P

/-- A lift of `z'` whose coordinates are within the circle distance of those of a lift of `z`. -/
lemma exists_close_lift (x : Fin 4 → ℝ) (z' : Tor p) :
    ∃ x' : Fin 4 → ℝ, projT p x' = z' ∧ ∀ ν, |x' ν - x ν| = ‖z' ν - (x ν : AddCircle p)‖ := by
  choose u hu using fun ν => QuotientAddGroup.mk_surjective (z' ν)
  refine ⟨fun ν => u ν - round (p⁻¹ * (u ν - x ν)) * p, ?_, fun ν => ?_⟩
  · funext ν
    simp only [projT]
    rw [AddCircle.coe_sub, ← hu ν]
    have : ((round (p⁻¹ * (u ν - x ν)) * p : ℝ) : AddCircle p) = 0 := by
      rw [AddCircle.coe_eq_zero_iff]; exact ⟨round (p⁻¹ * (u ν - x ν)), by simp⟩
    rw [this, sub_zero]
  · rw [← hu ν]
    change |u ν - round (p⁻¹ * (u ν - x ν)) * p - x ν| =
      ‖((u ν : AddCircle p) - (x ν : AddCircle p))‖
    rw [← AddCircle.coe_sub, AddCircle.norm_eq]
    ring_nf

/-- The upper bound `d(z, z') ≤ η⁻¹ |z - z'|₁`, by a straight path. -/
theorem wdist_le (D : DomainData p) (z z' : Tor p) :
    wdist D z z' ≤ ENNReal.ofReal ((D.a 0)⁻¹ * dist1 z z') := by
  obtain ⟨x, hx⟩ : ∃ x, projT p x = z := by
    choose u hu using fun ν => QuotientAddGroup.mk_surjective (z ν)
    exact ⟨u, funext fun ν => hu ν⟩
  obtain ⟨x', hx', hd⟩ := exists_close_lift (p := p) x z'
  set v := x' - x
  have hlip : LipschitzWith ‖v‖₊ (fun t : ℝ => x + t • v) :=
    LipschitzWith.of_dist_le_mul fun s t => by
      rw [dist_eq_norm, add_sub_add_left_eq_sub, ← sub_smul, norm_smul, Real.dist_eq,
        Real.norm_eq_abs, mul_comm]
      simp
  let P : TPath p z z' := ⟨1, zero_le_one, fun t => x + t • v, _, hlip,
    by simpa using hx, by simp [v, hx']⟩
  refine (iInf_le _ P).trans ?_
  have hderiv : ∀ (ν : Fin 4) (t : ℝ), deriv (fun s : ℝ => (x + s • v) ν) t = v ν :=
    fun ν t => by
      have h := ((hasDerivAt_id t).mul_const (v ν)).const_add (x ν)
      simp only [id, one_mul] at h
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      exact h.deriv
  have hsum : ∑ ν, |v ν| = dist1 z z' := by
    rw [dist1, ← hx]
    refine Finset.sum_congr rfl fun ν _ => ?_
    simp only [v, Pi.sub_apply, hd ν, projT]
    rw [norm_sub_rev]
  calc wlen D P.γ 0 P.T ≤ ∫⁻ t in Icc (0 : ℝ) 1, ENNReal.ofReal ((D.a 0)⁻¹ * dist1 z z') := by
        refine lintegral_mono fun t => ?_
        unfold wIntegrand
        simp only [P, hderiv]
        rw [← hsum, ENNReal.ofReal_mul (inv_nonneg.2 D.a_pos.le),
          ENNReal.ofReal_sum_of_nonneg (fun ν _ => abs_nonneg _)]
        refine mul_le_mul' (ENNReal.ofReal_le_ofReal (D.weight_le _)) (le_of_eq ?_)
        refine Finset.sum_congr rfl fun ν _ => ?_
        rw [← Real.norm_eq_abs, ofReal_norm]
    _ = ENNReal.ofReal ((D.a 0)⁻¹ * dist1 z z') := by
        rw [setLIntegral_const, Real.volume_Icc, sub_zero, ENNReal.ofReal_one, mul_one]

/-! ### Changes of variables and additivity -/

/-- `∫⁻_{[0, T]} F(T - t) dt = ∫⁻_{[0, T]} F`. -/
lemma lintegral_Icc_reflect (F : ℝ → ℝ≥0∞) (T : ℝ) :
    ∫⁻ t in Icc 0 T, F (T - t) = ∫⁻ t in Icc 0 T, F t := by
  rw [← lintegral_indicator measurableSet_Icc, ← lintegral_indicator measurableSet_Icc]
  have : (Icc 0 T).indicator (fun t => F (T - t)) = fun t => (Icc 0 T).indicator F (T - t) := by
    funext t
    by_cases ht : t ∈ Icc 0 T
    · have ht' : T - t ∈ Icc 0 T := ⟨by linarith [ht.2], by linarith [ht.1]⟩
      rw [indicator_of_mem ht, indicator_of_mem ht']
    · have ht' : T - t ∉ Icc 0 T := fun h => ht ⟨by linarith [h.2], by linarith [h.1]⟩
      rw [indicator_of_notMem ht, indicator_of_notMem ht']
  rw [this, lintegral_sub_left_eq_self]

/-- `∫⁻_{[a, b]} F(t - c) dt = ∫⁻_{[a - c, b - c]} F`. -/
lemma lintegral_Icc_shift (F : ℝ → ℝ≥0∞) (a b c : ℝ) :
    ∫⁻ t in Icc a b, F (t - c) = ∫⁻ t in Icc (a - c) (b - c), F t := by
  rw [← lintegral_indicator measurableSet_Icc, ← lintegral_indicator measurableSet_Icc]
  have : (Icc a b).indicator (fun t => F (t - c)) =
      fun t => (Icc (a - c) (b - c)).indicator F (t - c) := by
    funext t
    by_cases ht : t ∈ Icc a b
    · have ht' : t - c ∈ Icc (a - c) (b - c) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
      rw [indicator_of_mem ht, indicator_of_mem ht']
    · have ht' : t - c ∉ Icc (a - c) (b - c) := fun h => ht ⟨by linarith [h.1], by linarith [h.2]⟩
      rw [indicator_of_notMem ht, indicator_of_notMem ht']
  rw [this, lintegral_sub_right_eq_self]

/-- Additivity over adjacent intervals (the proof of `Manifold.pathELength_add`). -/
lemma wlen_add (D : DomainData p) (γ : ℝ → (Fin 4 → ℝ)) {a b c : ℝ} (h : a ≤ b) (h' : b ≤ c) :
    wlen D γ a b + wlen D γ b c = wlen D γ a c := by
  symm
  have : Icc a c = Icc a b ∪ Ioc b c := (Icc_union_Ioc_eq_Icc h h').symm
  rw [wlen, this, lintegral_union measurableSet_Ioc]
  · rw [restrict_Ioc_eq_restrict_Icc]; rfl
  · exact disjoint_iff_forall_ne.mpr fun x hx y hy => (hx.2.trans_lt hy.1).ne

/-- The weighted length depends only on the path on the open interval. -/
lemma wlen_congr_Ioo (D : DomainData p) {γ γ' : ℝ → (Fin 4 → ℝ)} {a b : ℝ}
    (h : ∀ t ∈ Ioo a b, wIntegrand D γ t = wIntegrand D γ' t) : wlen D γ a b = wlen D γ' a b := by
  unfold wlen
  rw [← restrict_Ioo_eq_restrict_Icc]
  exact setLIntegral_congr_fun measurableSet_Ioo h

/-- Paths which agree near `t` have the same integrand at `t`. -/
lemma wIntegrand_congr (D : DomainData p) {γ γ' : ℝ → (Fin 4 → ℝ)} {t : ℝ}
    (h : γ =ᶠ[𝓝 t] γ') : wIntegrand D γ t = wIntegrand D γ' t := by
  unfold wIntegrand
  rw [h.eq_of_nhds]
  congr 1
  refine Finset.sum_congr rfl fun ν _ => ?_
  have := Filter.EventuallyEq.deriv_eq (h.fun_comp fun x => x ν)
  exact congrArg enorm this

/-! ### `lem:distance`(i): symmetry and the triangle inequality -/

/-- The reversed path. -/
def TPath.reverse {z z' : Tor p} (P : TPath p z z') : TPath p z' z where
  T := P.T
  T_nonneg := P.T_nonneg
  γ := fun t => P.γ (P.T - t)
  K := P.K
  lip := by
    refine LipschitzWith.of_dist_le_mul fun s t => ?_
    refine (P.lip.dist_le_mul _ _).trans (le_of_eq ?_)
    rw [Real.dist_eq, Real.dist_eq, show P.T - s - (P.T - t) = -(s - t) by ring, abs_neg]
  start := by simpa using P.stop
  stop := by simpa using P.start

lemma wlen_reverse (D : DomainData p) {z z' : Tor p} (P : TPath p z z') :
    wlen D P.reverse.γ 0 P.reverse.T = wlen D P.γ 0 P.T := by
  have h : ∀ t, wIntegrand D P.reverse.γ t = wIntegrand D P.γ (P.T - t) := fun t => by
    unfold wIntegrand
    congr 1
    refine Finset.sum_congr rfl fun ν _ => ?_
    have h := deriv_comp_const_sub (fun s => P.γ s ν) P.T t
    change ‖deriv (fun s => P.γ (P.T - s) ν) t‖ₑ = _
    rw [h, enorm_neg]
  simp only [wlen, h]
  exact lintegral_Icc_reflect _ _

theorem wdist_comm (D : DomainData p) (z z' : Tor p) : wdist D z z' = wdist D z' z := by
  refine le_antisymm (le_iInf fun P => ?_) (le_iInf fun P => ?_)
  · rw [← wlen_reverse]; exact iInf_le _ P.reverse
  · rw [← wlen_reverse]; exact iInf_le _ P.reverse

/-- `f` up to `a`, then `g`: Lipschitz with the larger constant. -/
lemma lipschitzWith_glue_le {E : Type*} [MetricSpace E] {a : ℝ} {f g : ℝ → E} {K : ℝ≥0}
    (hf : LipschitzWith K f) (hg : LipschitzWith K g) (hfg : f a = g a) :
    LipschitzWith K (glue a f g) := by
  refine LipschitzWith.of_dist_le_mul fun t t' => ?_
  wlog htt : t ≤ t' generalizing t t'
  · rw [dist_comm, dist_comm t]; exact this t' t (le_of_not_ge htt)
  rcases le_total t' a with h | h
  · rw [glue_of_le (htt.trans h), glue_of_le h]; exact hf.dist_le_mul t t'
  rcases le_total t a with h' | h'
  · rw [glue_of_le h', glue_of_ge hfg h]
    calc dist (f t) (g t') ≤ dist (f t) (f a) + dist (g a) (g t') := by
          rw [hfg]; exact dist_triangle _ _ _
      _ ≤ K * dist t a + K * dist a t' := add_le_add (hf.dist_le_mul t a) (hg.dist_le_mul a t')
      _ = K * dist t t' := by
          rw [Real.dist_eq, Real.dist_eq, Real.dist_eq, abs_of_nonpos (by linarith),
            abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; ring
  · rw [glue_of_ge hfg h', glue_of_ge hfg h]; exact hg.dist_le_mul t t'

/-- The derivative of a coordinate of the shifted path `γ(· - c) + w`. -/
lemma deriv_coord_shift (γ : ℝ → (Fin 4 → ℝ)) (c : ℝ) (w : Fin 4 → ℝ) (ν : Fin 4) (t : ℝ) :
    deriv (fun s => (γ (s - c) + w) ν) t = deriv (fun s => γ s ν) (t - c) := by
  have h := deriv_comp_sub_const (fun s => γ s ν) c t
  simp only [Pi.add_apply]
  rw [deriv_add_const]
  exact h

lemma projT_add_eq {x v : Fin 4 → ℝ} (hv : projT p v = 0) : projT p (x + v) = projT p x := by
  funext ν
  have := congrFun hv ν
  simp only [projT, Pi.add_apply, Pi.zero_apply] at this ⊢
  rw [AddCircle.coe_add, this, add_zero]

/-- The concatenation of two paths, the second shifted by a lattice vector to match. -/
def TPath.trans {z z' z'' : Tor p} (P : TPath p z z') (Q : TPath p z' z'') : TPath p z z'' where
  T := P.T + Q.T
  T_nonneg := add_nonneg P.T_nonneg Q.T_nonneg
  γ := glue P.T P.γ (fun t => Q.γ (t - P.T) + (P.γ P.T - Q.γ 0))
  K := max P.K Q.K
  lip := by
    refine lipschitzWith_glue_le (E := Fin 4 → ℝ) (f := P.γ)
      (g := fun t => Q.γ (t - P.T) + (P.γ P.T - Q.γ 0)) (P.lip.weaken (le_max_left _ _)) ?_
      (by simp)
    refine LipschitzWith.of_dist_le_mul fun s t => ?_
    rw [dist_add_right]
    refine (Q.lip.dist_le_mul _ _).trans ?_
    rw [Real.dist_eq, Real.dist_eq, sub_sub_sub_cancel_right]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast le_max_right _ _) (abs_nonneg _)
  start := by rw [glue_of_le P.T_nonneg]; exact P.start
  stop := by
    rw [glue_of_ge (by simp) (by linarith [Q.T_nonneg]), add_sub_cancel_left,
      projT_add_eq, Q.stop]
    funext ν
    have h1 := congrFun P.stop ν
    have h2 := congrFun Q.start ν
    simp only [projT, Pi.sub_apply, Pi.zero_apply] at h1 h2 ⊢
    rw [AddCircle.coe_sub, h1, h2, sub_self]

lemma wlen_trans (D : DomainData p) {z z' z'' : Tor p} (P : TPath p z z') (Q : TPath p z' z'') :
    wlen D (P.trans Q).γ 0 (P.trans Q).T = wlen D P.γ 0 P.T + wlen D Q.γ 0 Q.T := by
  set v := P.γ P.T - Q.γ 0
  have hv : projT p v = 0 := by
    funext ν
    have h1 := congrFun P.stop ν
    have h2 := congrFun Q.start ν
    simp only [projT, v, Pi.sub_apply, Pi.zero_apply] at h1 h2 ⊢
    rw [AddCircle.coe_sub, h1, h2, sub_self]
  have hmatch : P.γ P.T = (fun t => Q.γ (t - P.T) + v) P.T := by simp [v]
  rw [show (P.trans Q).T = P.T + Q.T from rfl,
    ← wlen_add D _ P.T_nonneg (le_add_of_nonneg_right Q.T_nonneg)]
  congr 1
  · -- on `(0, T₁)` the concatenation is `γ₁`
    refine wlen_congr_Ioo D fun t ht => wIntegrand_congr D ?_
    filter_upwards [Iio_mem_nhds ht.2] with s hs
    exact glue_of_le (f := P.γ) (g := fun t => Q.γ (t - P.T) + v) (le_of_lt hs)
  · -- on `(T₁, T₁ + T₂)` it is `γ₂(· - T₁) + v`
    have h1 : ∀ t ∈ Ioo P.T (P.T + Q.T), wIntegrand D (P.trans Q).γ t =
        wIntegrand D Q.γ (t - P.T) := fun t ht => by
      rw [wIntegrand_congr D (γ' := fun s => Q.γ (s - P.T) + v) ?_]
      · simp only [wIntegrand]
        rw [projT_add_eq hv]
        congr 1
        exact Finset.sum_congr rfl fun ν _ => by rw [deriv_coord_shift]
      · filter_upwards [Ioi_mem_nhds ht.1] with s hs
        exact glue_of_ge (f := P.γ) (g := fun t => Q.γ (t - P.T) + v) hmatch (le_of_lt hs)
    unfold wlen
    rw [← restrict_Ioo_eq_restrict_Icc, setLIntegral_congr_fun measurableSet_Ioo h1,
      restrict_Ioo_eq_restrict_Icc, lintegral_Icc_shift (fun t => wIntegrand D Q.γ t), sub_self,
      add_sub_cancel_left]

theorem wdist_triangle (D : DomainData p) (z z' z'' : Tor p) :
    wdist D z z'' ≤ wdist D z z' + wdist D z' z'' :=
  ENNReal.le_iInf_add_iInf fun P Q => by
    rw [← wlen_trans]; exact iInf_le _ (P.trans Q)

theorem wdist_self (D : DomainData p) (z : Tor p) : wdist D z z = 0 := by
  refine le_antisymm ((wdist_le D z z).trans (le_of_eq ?_)) zero_le
  simp [dist1]

theorem eq_of_wdist_eq_zero (D : DomainData p) {z z' : Tor p} (h : wdist D z z' = 0) : z = z' := by
  have h1 := dist1_le_wdist D z z'
  rw [h, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at h1
  have h0 : dist1 z z' = 0 := le_antisymm h1 (dist1_nonneg _ _)
  funext ν
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun ν _ => norm_nonneg (z ν - z' ν))).1 h0 ν
    (Finset.mem_univ ν)
  exact sub_eq_zero.1 (norm_eq_zero.1 this)

theorem wdist_ne_top (D : DomainData p) (z z' : Tor p) : wdist D z z' ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (wdist_le D z z')

/-! ### `lem:distance`(ii): the cost of crossing a layer -/

/-- The arc of a path in the layer `Ω_i \ Ω_{i+1}` (the core's `t₀`, `t₁`). -/
lemma exists_layer_arc (D : DomainData p) {R M : ℝ}
    (hsep : ∀ i, 1 ≤ i → i < D.k → ∀ x ∉ D.Ω i, ∀ y ∈ D.Ω (i + 1), R * M * D.a i ≤ dist x y)
    {z z' : Tor p} (P : TPath p z z') {i : ℕ} (hi1 : 1 ≤ i) (hik : i < D.k)
    (hz : z ∉ D.Ω i) (hz' : z' ∈ D.Ω (i + 1)) :
    ∃ t0 t1, 0 ≤ t0 ∧ t0 ≤ t1 ∧ t1 ≤ P.T ∧
      (∀ t ∈ Ioo t0 t1, projT p (P.γ t) ∈ D.Ω i ∧ projT p (P.γ t) ∉ D.Ω (i + 1)) ∧
      R * M * D.a i ≤ dist (projT p (P.γ t0)) (projT p (P.γ t1)) := by
  set g := fun t => projT p (P.γ t) with hg
  have hgc : Continuous g := continuous_projT.comp P.lip.continuous
  -- `t₁`: the first time in `Ω_{i+1}`
  set S1 := Icc 0 P.T ∩ g ⁻¹' D.Ω (i + 1)
  have hS1c : IsClosed S1 := isClosed_Icc.inter ((D.Ω_closed _).preimage hgc)
  have hS1n : S1.Nonempty := ⟨P.T, ⟨P.T_nonneg, le_rfl⟩, by simp [g, P.stop, hz']⟩
  have hS1b : BddBelow S1 := ⟨0, fun t ht => ht.1.1⟩
  set t1 := sInf S1
  have ht1 : t1 ∈ S1 := hS1c.csInf_mem hS1n hS1b
  have hbefore : ∀ t, 0 ≤ t → t < t1 → g t ∉ D.Ω (i + 1) := fun t h0 h1 hgt =>
    absurd (csInf_le hS1b ⟨⟨h0, h1.le.trans ht1.1.2⟩, hgt⟩) (not_le.2 h1)
  -- `t₀`: the last time before `t₁` in the closure of `Ω_i^c`
  set S0 := Icc 0 t1 ∩ g ⁻¹' closure (D.Ω i)ᶜ
  have hS0c : IsClosed S0 := isClosed_Icc.inter (isClosed_closure.preimage hgc)
  have hS0n : S0.Nonempty :=
    ⟨0, ⟨le_rfl, ht1.1.1⟩, subset_closure (show g 0 ∈ (D.Ω i)ᶜ by simp [g, P.start, hz])⟩
  have hS0b : BddAbove S0 := ⟨t1, fun t ht => ht.1.2⟩
  set t0 := sSup S0
  have ht0 : t0 ∈ S0 := hS0c.csSup_mem hS0n hS0b
  have hafter : ∀ t, t0 < t → t ≤ t1 → g t ∈ D.Ω i := fun t h0 h1 => by
    by_contra hgt
    exact absurd (le_csSup hS0b ⟨⟨ht0.1.1.trans h0.le, h1⟩, subset_closure hgt⟩) (not_le.2 h0)
  refine ⟨t0, t1, ht0.1.1, ht0.1.2, ht1.1.2, fun t ht => ⟨hafter t ht.1 ht.2.le,
    hbefore t (ht0.1.1.trans ht.1.le) ht.2⟩, ?_⟩
  -- the separation, extended to the closure of `Ω_i^c`
  have hcl : closure (D.Ω i)ᶜ ⊆ {x | R * M * D.a i ≤ dist x (g t1)} :=
    closure_minimal (fun x hx => hsep i hi1 hik x hx (g t1) ht1.2)
      (isClosed_le continuous_const (continuous_id.dist continuous_const))
  exact hcl ht0.2

/-- The weighted length of an arc in the layer `Ω_i \ Ω_{i+1}` whose ends are `RMa_i` apart is at
least `RM`. -/
lemma lintegral_layer_arc (D : DomainData p) {R M : ℝ} {z z' : Tor p} (P : TPath p z z') {i : ℕ}
    (hik : i ≤ D.k) {t0 t1 : ℝ} (h01 : t0 ≤ t1)
    (hin : ∀ t ∈ Ioo t0 t1, projT p (P.γ t) ∈ D.Ω i ∧ projT p (P.γ t) ∉ D.Ω (i + 1))
    (hd : R * M * D.a i ≤ dist (projT p (P.γ t0)) (projT p (P.γ t1))) :
    ENNReal.ofReal (R * M) ≤ ∫⁻ t in Ioo t0 t1, wIntegrand D P.γ t := by
  have ha := D.a_pos' i
  have hw : ∀ t ∈ Ioo t0 t1, wIntegrand D P.γ t =
      ENNReal.ofReal (D.a i)⁻¹ * ∑ ν, ‖deriv (fun s => P.γ s ν) t‖ₑ := fun t ht => by
    unfold wIntegrand DomainData.weight
    rw [D.scale_eq hik (hin t ht).1 (hin t ht).2]
  rw [setLIntegral_congr_fun measurableSet_Ioo hw,
    lintegral_const_mul _ (Finset.measurable_sum _ fun ν _ => (measurable_deriv _).enorm),
    restrict_Ioo_eq_restrict_Icc]
  have h1 := ofReal_sum_abs_sub_le P.lip h01
  have h2 : dist (projT p (P.γ t0)) (projT p (P.γ t1)) ≤ ∑ ν, |P.γ t1 ν - P.γ t0 ν| := by
    refine (dist_pi_le_iff (Finset.sum_nonneg fun ν _ => abs_nonneg _)).2 fun ν => ?_
    rw [dist_eq_norm]
    refine (norm_coe_sub_le _ _).trans ?_
    rw [abs_sub_comm]
    exact Finset.single_le_sum (f := fun ν => |P.γ t1 ν - P.γ t0 ν|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ ν)
  calc ENNReal.ofReal (R * M) = ENNReal.ofReal (D.a i)⁻¹ * ENNReal.ofReal (R * M * D.a i) := by
        rw [← ENNReal.ofReal_mul (inv_nonneg.2 ha.le)]
        congr 1; field_simp
    _ ≤ ENNReal.ofReal (D.a i)⁻¹ * ENNReal.ofReal (∑ ν, |P.γ t1 ν - P.γ t0 ν|) := by
        gcongr; exact hd.trans h2
    _ ≤ _ := by gcongr

/-- `lem:distance`(ii) for `j < j'` and one path: `ℓ(γ) ≥ RM(j' - j - 1)`. -/
lemma wlen_ge_layers (D : DomainData p) {R M : ℝ}
    (hsep : ∀ i, 1 ≤ i → i < D.k → ∀ x ∉ D.Ω i, ∀ y ∈ D.Ω (i + 1), R * M * D.a i ≤ dist x y)
    {z z' : Tor p} {j j' : ℕ} (hjj : j < j') (hj' : j' ≤ D.k) (hz : z ∉ D.Ω (j + 1))
    (hz' : z' ∈ D.Ω j') (P : TPath p z z') :
    ENNReal.ofReal (R * M * ((j' : ℝ) - j - 1)) ≤ wlen D P.γ 0 P.T := by
  -- one arc for each `j < i < j'`
  have harc : ∀ i ∈ Finset.Ioo j j', ∃ t0 t1, 0 ≤ t0 ∧ t0 ≤ t1 ∧ t1 ≤ P.T ∧
      (∀ t ∈ Ioo t0 t1, projT p (P.γ t) ∈ D.Ω i ∧ projT p (P.γ t) ∉ D.Ω (i + 1)) ∧
      R * M * D.a i ≤ dist (projT p (P.γ t0)) (projT p (P.γ t1)) := fun i hi => by
    obtain ⟨h1, h2⟩ := Finset.mem_Ioo.1 hi
    exact exists_layer_arc D hsep P (by omega) (by omega)
      (fun h => hz (D.Ω_anti (by omega) h)) (D.Ω_anti (by omega) hz')
  choose! t0 t1 h0 h01 h1T hin hd using harc
  set I := fun i => Ioo (t0 i) (t1 i)
  have hdisj : Set.Pairwise (↑(Finset.Ioo j j')) (fun a b => AEDisjoint volume (I a) (I b)) := by
    intro i _ i' _ hii'
    refine Disjoint.aedisjoint (Set.disjoint_left.2 fun t hti hti' => ?_)
    rcases lt_or_gt_of_ne hii' with h | h
    · exact (hin i ‹_› t hti).2 (D.Ω_anti (by omega) (hin i' ‹_› t hti').1)
    · exact (hin i' ‹_› t hti').2 (D.Ω_anti (by omega) (hin i ‹_› t hti).1)
  have hsub : (⋃ i ∈ Finset.Ioo j j', I i) ⊆ Icc 0 P.T := by
    intro t ht
    simp only [mem_iUnion] at ht
    obtain ⟨i, hi, ht⟩ := ht
    exact ⟨(h0 i hi).trans ht.1.le, ht.2.le.trans (h1T i hi)⟩
  have hcard : ((Finset.Ioo j j').card : ℝ) = (j' : ℝ) - j - 1 := by
    rw [Nat.card_Ioo]; push_cast [Nat.cast_sub (by omega : 1 ≤ j' - j), Nat.cast_sub hjj.le]
    ring
  calc ENNReal.ofReal (R * M * ((j' : ℝ) - j - 1))
      ≤ ∑ i ∈ Finset.Ioo j j', ENNReal.ofReal (R * M) := by
        rw [Finset.sum_const, nsmul_eq_mul, ← hcard, mul_comm (R * M),
          ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    _ ≤ ∑ i ∈ Finset.Ioo j j', ∫⁻ t in I i, wIntegrand D P.γ t :=
        Finset.sum_le_sum fun i hi => lintegral_layer_arc D P
          (by have := Finset.mem_Ioo.1 hi; omega) (h01 i hi) (hin i hi) (hd i hi)
    _ = ∫⁻ t in ⋃ i ∈ Finset.Ioo j j', I i, wIntegrand D P.γ t :=
        (lintegral_biUnion_finset₀ hdisj (fun i _ => measurableSet_Ioo.nullMeasurableSet) _).symm
    _ ≤ wlen D P.γ 0 P.T := lintegral_mono_set hsub

/-- `lem:distance`(ii): if `z ∈ Ω_j \ Ω_{j+1}` and `z' ∈ Ω_{j'} \ Ω_{j'+1}`, then
`d(z, z') ≥ RM max{|j - j'| - 1, 0}`. -/
theorem wdist_ge_layers (D : DomainData p) {R M : ℝ}
    (hsep : ∀ i, 1 ≤ i → i < D.k → ∀ x ∉ D.Ω i, ∀ y ∈ D.Ω (i + 1), R * M * D.a i ≤ dist x y)
    {z z' : Tor p} {j j' : ℕ} (hz : z ∈ D.Ω j) (hz1 : z ∉ D.Ω (j + 1)) (hz' : z' ∈ D.Ω j')
    (hz1' : z' ∉ D.Ω (j' + 1)) :
    ENNReal.ofReal (R * M * max (|(j : ℝ) - j'| - 1) 0) ≤ wdist D z z' := by
  have hk : ∀ {i : ℕ} {x : Tor p}, x ∈ D.Ω i → i ≤ D.k := fun {i x} hx => by
    by_contra h
    have := D.Ω_anti (by omega : D.k + 1 ≤ i) hx
    rw [D.Ω_top] at this; exact this
  rcases lt_trichotomy j j' with h | h | h
  · rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 (by exact_mod_cast h.le : (j : ℝ) ≤ j'))]
    rcases le_total ((j' : ℝ) - j - 1) 0 with h0 | h0
    · rw [max_eq_right h0, mul_zero, ENNReal.ofReal_zero]; exact zero_le
    · rw [max_eq_left h0]
      exact le_iInf fun P => wlen_ge_layers D hsep h (hk hz') hz1 hz' P
  · subst h; simp
  · rw [abs_of_nonneg (sub_nonneg.2 (by exact_mod_cast h.le : (j' : ℝ) ≤ j)), wdist_comm]
    rcases le_total ((j : ℝ) - j' - 1) 0 with h0 | h0
    · rw [max_eq_right h0, mul_zero, ENNReal.ofReal_zero]; exact zero_le
    · rw [max_eq_left h0]
      exact le_iInf fun P => wlen_ge_layers D hsep h (hk hz) hz1' hz P

end CoreLean
