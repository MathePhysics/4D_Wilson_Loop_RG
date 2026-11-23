import SpectralTheorem.PVMIntegral
import SpectralTheorem.UnboundedBorel
import KatoRellich.Criterion

/-!
# The integral of an unbounded function against a projection-valued measure

**Reed–Simon I, pp. 263–264.**  "Now, suppose `g` is an unbounded complex-valued Borel function
and let `D_g = {φ | ∫ |g(λ)|² d(φ, P_λ φ) < ∞}` (VIII.5).  Then `D_g` is dense in `H` and an
operator `g(A)` is defined on `D_g` by `(φ, g(A) φ) = ∫ g(λ) d(φ, P_λ φ)`. ... If `g` is
real-valued, then `g(A)` is self-adjoint on `D_g`."  Theorem VIII.6 (p. 264) writes this operator
as `∫ g(λ) dP_λ`.

Here `P` is an arbitrary projection-valued measure on a measurable space `X`
(`SpectralTheorem.ProjectionValuedMeasure`), `μ_ψ = P.measure ψ` and `g : X → ℂ` is measurable.

Construction and proof.
* `D_g = {ψ | g ∈ L²(μ_ψ)}` is a submodule: `μ_{ψ + φ} ≤ 2 μ_ψ + 2 μ_φ` and
  `μ_{c ψ} = |c|² μ_ψ` setwise.
* With the truncations `gₙ = g · 1_{‖g‖ ≤ n}`, for `ψ ∈ D_g` the vectors `(∫ gₙ dP) ψ` form a
  Cauchy sequence, since `‖(∫ (gₙ - gₘ) dP) ψ‖² = ∫ |gₙ - gₘ|² dμ_ψ → 0` by dominated
  convergence (bound `4 |g|²`).  `(∫ g dP) ψ` is the limit.  More generally, for bounded `hₙ → g`
  pointwise with `|hₙ| ≤ G` and `G ∈ L²(μ_ψ)`, `(∫ hₙ dP) ψ → (∫ g dP) ψ`.
* Passing to the limit in the bounded identities gives `‖(∫ g dP) ψ‖² = ∫ |g|² dμ_ψ` and
  Reed–Simon's defining formula `(ψ, (∫ g dP) ψ) = ∫ g dμ_ψ`.
* `D_g` is dense: `P_{‖g‖ ≤ n} ψ ∈ D_g`, as `μ_{P_s ψ}` is the restriction of `μ_ψ` to `s`, and
  `P_{‖g‖ ≤ n} ψ → ψ`.
* For bounded `f` with `g f` bounded, `μ_{(∫ f dP) ψ} = |f|² μ_ψ`, so `(∫ f dP) ψ ∈ D_g` and
  `(∫ g dP) (∫ f dP) ψ = (∫ g f dP) ψ`.
* For real `r`, `∫ r dP` is symmetric (a limit of the self-adjoint `∫ rₙ dP`), and for
  `z ∉ ℝ`, `η = (∫ r dP + z) (∫ (r + z)⁻¹ dP) η` by the previous item; so `∫ r dP ± i` are
  onto and `∫ r dP` is self-adjoint (`KatoRellich.isSelfAdjoint_of_range_addScalar`).
* The adjoint: `∫ ḡ dP ⊆ (∫ g dP)†` by passing to the limit in `(∫ gₙ dP)† = ∫ ḡₙ dP`.
  Conversely, for `φ` in the domain of `(∫ g dP)†` and `η = (∫ g dP)† φ`,
  `(∫ ḡₙ dP) φ = P_{‖g‖ ≤ n} η`, so `∫ |gₙ|² dμ_φ ≤ ‖η‖²` and `φ ∈ D_g` by Fatou's lemma.

## Main definitions and results

* `SpectralTheorem.boundedTrunc hg n`: the truncation `g · 1_{‖g‖ ≤ n}`.
* `ProjectionValuedMeasure.integralDomain P hg`: the domain `D_g` (VIII.5).
* `ProjectionValuedMeasure.integralPMap P hg`: the operator `∫ g dP`, with
  `mem_integralPMap_domain`, `tendsto_integral_trunc` (the defining limit),
  `tendsto_integral_integralPMap` (other approximations), `enorm_integralPMap_apply_sq`,
  `inner_integralPMap` (Reed–Simon's formula), `dense_integralPMap_domain`.
* `ProjectionValuedMeasure.integralPMap_bounded`: for bounded `f`, `∫ f dP` is `P.integral f`.
* `ProjectionValuedMeasure.integralPMap_add_bounded`, `integral_mem_integralPMap_domain`.
* `ProjectionValuedMeasure.isSelfAdjoint_integralPMap`: `∫ r dP` is self-adjoint for real `r`.
* `ProjectionValuedMeasure.adjoint_integralPMap`: `(∫ g dP)† = ∫ ḡ dP`.
-/

noncomputable section

open scoped InnerProductSpace ENNReal Topology ComplexConjugate
open MeasureTheory Filter Set KatoRellich

namespace SpectralTheorem

universe u

variable {X : Type*} [MeasurableSpace X]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### Truncations -/

/-- The truncation `gₙ = g · 1_{‖g‖ ≤ n}` of a measurable `g : X → ℂ`, a bounded measurable
function. -/
def boundedTrunc {g : X → ℂ} (hg : Measurable g) (n : ℕ) : boundedMeasurable X :=
  ⟨{x | ‖g x‖ ≤ n}.indicator g, hg.indicator (measurableSet_le hg.norm measurable_const), n,
    fun x => by
      by_cases hx : ‖g x‖ ≤ n
      · rw [Set.indicator_of_mem (show x ∈ {x | ‖g x‖ ≤ n} from hx)]
        exact hx
      · rw [Set.indicator_of_notMem (show x ∉ {x | ‖g x‖ ≤ n} from hx), norm_zero]
        exact Nat.cast_nonneg n⟩

/-- `gₙ` as a function. -/
theorem coe_boundedTrunc {g : X → ℂ} (hg : Measurable g) (n : ℕ) :
    (boundedTrunc hg n : X → ℂ) = {x | ‖g x‖ ≤ n}.indicator g :=
  rfl

/-- `‖gₙ‖ ≤ ‖g‖` pointwise. -/
theorem norm_boundedTrunc_le {g : X → ℂ} (hg : Measurable g) (n : ℕ) (x : X) :
    ‖(boundedTrunc hg n : X → ℂ) x‖ ≤ ‖g x‖ := by
  rw [coe_boundedTrunc]
  exact norm_indicator_le_norm_self _ _

/-- `gₙ → g` pointwise (the sequence is eventually constant). -/
theorem tendsto_boundedTrunc {g : X → ℂ} (hg : Measurable g) (x : X) :
    Tendsto (fun n => (boundedTrunc hg n : X → ℂ) x) atTop (𝓝 (g x)) := by
  obtain ⟨N, hN⟩ := exists_nat_ge ‖g x‖
  refine tendsto_const_nhds.congr' (eventually_atTop.2 ⟨N, fun n hn => ?_⟩)
  change g x = {x | ‖g x‖ ≤ n}.indicator g x
  rw [Set.indicator_of_mem]
  exact hN.trans (Nat.cast_le.2 hn)

omit [CompleteSpace H] in
/-- If `‖wᵢ‖² → 0` then `wᵢ → 0`. -/
theorem tendsto_zero_of_norm_sq {ι : Type*} {l : Filter ι} {w : ι → H}
    (h : Tendsto (fun i => ‖w i‖ ^ 2) l (𝓝 0)) : Tendsto w l (𝓝 0) := by
  refine tendsto_zero_of_inner_self ?_
  have h' := (Complex.continuous_ofReal.tendsto 0).comp h
  rw [Complex.ofReal_zero] at h'
  refine h'.congr fun i => ?_
  simp [inner_self_eq_norm_sq_to_K]

namespace ProjectionValuedMeasure

variable (P : ProjectionValuedMeasure X H)

/-! ### Bounded functions -/

/-- `‖(∫ f dP) ψ‖² = ∫ |f|² dμ_ψ` for bounded `f`, as an equality in `ℝ≥0∞`. -/
theorem enorm_integral_apply_sq (f : boundedMeasurable X) (ψ : H) :
    ‖P.integral f ψ‖ₑ ^ 2 = ∫⁻ x, ‖(f : X → ℂ) x‖ₑ ^ 2 ∂(P.measure ψ) := by
  obtain ⟨C, -, hC⟩ := boundedMeasurable.exists_bound f
  have hm : Measurable fun x => ‖(f : X → ℂ) x‖ ^ 2 :=
    (boundedMeasurable.measurable f).norm.pow_const 2
  have hi : Integrable (fun x => ‖(f : X → ℂ) x‖ ^ 2) (P.measure ψ) :=
    Integrable.of_bound hm.aestronglyMeasurable (C ^ 2) (Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hC x) 2)
  rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), P.norm_integral_apply_sq,
    ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun x => sq_nonneg _)]
  refine lintegral_congr fun x => ?_
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

/-- **Dominated convergence for `∫ · dP`**: if bounded `fᵢ → 0` pointwise with `‖fᵢ‖ ≤ G` and
`G ∈ L²(μ_ψ)`, then `(∫ fᵢ dP) ψ → 0`, as `‖(∫ fᵢ dP) ψ‖² = ∫ |fᵢ|² dμ_ψ`. -/
theorem tendsto_integral_apply_zero {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    (f : ι → boundedMeasurable X) {G : X → ℝ} (ψ : H) (hG : MemLp G 2 (P.measure ψ))
    (hfG : ∀ i x, ‖(f i : X → ℂ) x‖ ≤ G x)
    (hf0 : ∀ x, Tendsto (fun i => (f i : X → ℂ) x) l (𝓝 0)) :
    Tendsto (fun i => P.integral (f i) ψ) l (𝓝 0) := by
  refine tendsto_zero_of_norm_sq ?_
  simp only [P.norm_integral_apply_sq]
  have h := tendsto_integral_filter_of_dominated_convergence (μ := P.measure ψ) (l := l)
    (F := fun i x => ‖(f i : X → ℂ) x‖ ^ 2) (f := fun _ => 0) (fun x => G x ^ 2)
    (Eventually.of_forall fun i =>
      ((boundedMeasurable.measurable (f i)).norm.pow_const 2).aestronglyMeasurable)
    (Eventually.of_forall fun i => Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hfG i x) 2)
    hG.integrable_sq
    (Eventually.of_forall fun x => by simpa using ((hf0 x).norm).pow 2)
  simpa using h

/-! ### The domain `D_g` -/

/-- `μ_{ψ + φ} ≤ 2 μ_ψ + 2 μ_φ`. -/
theorem measure_add_le (ψ φ : H) :
    P.measure (ψ + φ) ≤ (2 : ℝ≥0∞) • P.measure ψ + (2 : ℝ≥0∞) • P.measure φ := by
  refine Measure.le_iff.2 fun s hs => ?_
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply, P.measure_apply _ hs,
    P.measure_apply _ hs, P.measure_apply _ hs, map_add, smul_eq_mul, smul_eq_mul]
  have h : ‖P s ψ + P s φ‖ ^ 2 ≤ 2 * ‖P s ψ‖ ^ 2 + 2 * ‖P s φ‖ ^ 2 := by
    nlinarith [norm_add_le (P s ψ) (P s φ), norm_nonneg (P s ψ), norm_nonneg (P s φ),
      norm_nonneg (P s ψ + P s φ), sq_nonneg (‖P s ψ‖ - ‖P s φ‖)]
  calc ENNReal.ofReal (‖P s ψ + P s φ‖ ^ 2)
      ≤ ENNReal.ofReal (2 * ‖P s ψ‖ ^ 2 + 2 * ‖P s φ‖ ^ 2) := ENNReal.ofReal_le_ofReal h
    _ = 2 * ENNReal.ofReal (‖P s ψ‖ ^ 2) + 2 * ENNReal.ofReal (‖P s φ‖ ^ 2) := by
      rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by norm_num),
        ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]

/-- `μ_{c ψ} = |c|² μ_ψ`. -/
theorem measure_smul (c : ℂ) (ψ : H) :
    P.measure (c • ψ) = ENNReal.ofReal (‖c‖ ^ 2) • P.measure ψ := by
  refine Measure.ext fun s hs => ?_
  rw [Measure.smul_apply, P.measure_apply _ hs, P.measure_apply _ hs, map_smul, norm_smul,
    mul_pow, smul_eq_mul, ENNReal.ofReal_mul (sq_nonneg _)]

/-- **The domain `D_g = {ψ | ∫ |g|² dμ_ψ < ∞}`** (Reed–Simon I, (VIII.5)), a submodule. -/
def integralDomain {g : X → ℂ} (hg : Measurable g) : Submodule ℂ H where
  carrier := {ψ | MemLp g 2 (P.measure ψ)}
  zero_mem' := by
    have h0 : P.measure 0 = 0 := Measure.ext fun s hs => by simp [P.measure_apply _ hs]
    simp [h0]
  add_mem' {ψ φ} hψ hφ := by
    simp only [Set.mem_ofPred_eq, memLp_two_iff_lintegral_lt_top hg.aestronglyMeasurable] at *
    refine (lintegral_mono' (P.measure_add_le ψ φ) le_rfl).trans_lt ?_
    rw [lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure, smul_eq_mul,
      smul_eq_mul]
    exact ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top (by simp) hψ, ENNReal.mul_lt_top (by simp) hφ⟩
  smul_mem' c ψ hψ := by
    simp only [Set.mem_ofPred_eq] at *
    rw [P.measure_smul]
    exact hψ.smul_measure ENNReal.ofReal_ne_top

theorem mem_integralDomain {g : X → ℂ} (hg : Measurable g) {ψ : H} :
    ψ ∈ P.integralDomain hg ↔ MemLp g 2 (P.measure ψ) :=
  Iff.rfl

/-! ### The operator `∫ g dP` -/

/-- For `ψ ∈ D_g`, `(∫ gₙ dP) ψ` is a Cauchy sequence:
`‖(∫ (gₙ - gₘ) dP) ψ‖² = ∫ |gₙ - gₘ|² dμ_ψ → 0` by dominated convergence. -/
theorem cauchySeq_integral_trunc {g : X → ℂ} (hg : Measurable g) {ψ : H}
    (hψ : ψ ∈ P.integralDomain hg) :
    CauchySeq fun n => P.integral (boundedTrunc hg n) ψ := by
  rw [cauchySeq_iff_tendsto_dist_atTop_0]
  have hfst : Tendsto (fun p : ℕ × ℕ => p.1) atTop atTop := by
    rw [← prod_atTop_atTop_eq]
    exact tendsto_fst
  have hsnd : Tendsto (fun p : ℕ × ℕ => p.2) atTop atTop := by
    rw [← prod_atTop_atTop_eq]
    exact tendsto_snd
  have hb : ∀ (p : ℕ × ℕ) x,
      ‖((boundedTrunc hg p.1 - boundedTrunc hg p.2 : boundedMeasurable X) : X → ℂ) x‖ ≤
        2 * ‖g x‖ := fun p x => by
    change ‖(boundedTrunc hg p.1 : X → ℂ) x - (boundedTrunc hg p.2 : X → ℂ) x‖ ≤ 2 * ‖g x‖
    linarith [norm_sub_le ((boundedTrunc hg p.1 : X → ℂ) x) ((boundedTrunc hg p.2 : X → ℂ) x),
      norm_boundedTrunc_le hg p.1 x, norm_boundedTrunc_le hg p.2 x]
  have hl : ∀ x, Tendsto (fun p : ℕ × ℕ =>
      ((boundedTrunc hg p.1 - boundedTrunc hg p.2 : boundedMeasurable X) : X → ℂ) x) atTop
      (𝓝 0) := fun x => by
    have h2 := ((tendsto_boundedTrunc hg x).comp hfst).sub
      ((tendsto_boundedTrunc hg x).comp hsnd)
    rw [sub_self] at h2
    exact h2
  have h := P.tendsto_integral_apply_zero
    (fun p : ℕ × ℕ => boundedTrunc hg p.1 - boundedTrunc hg p.2) (G := fun x => 2 * ‖g x‖) ψ
    (((P.mem_integralDomain hg).1 hψ).norm.const_mul 2) hb hl
  simpa [dist_eq_norm, map_sub] using h.norm

/-- **The operator `∫ g dP`** for a measurable `g : X → ℂ` (Reed–Simon I, pp. 263–264), with
domain `D_g = {ψ | ∫ |g|² dμ_ψ < ∞}` and value `(∫ g dP) ψ = lim_n (∫ gₙ dP) ψ` for the
truncations `gₙ = g · 1_{‖g‖ ≤ n}`. -/
def integralPMap {g : X → ℂ} (hg : Measurable g) : H →ₗ.[ℂ] H where
  domain := P.integralDomain hg
  toFun :=
    { toFun := fun ψ => limUnder atTop fun n => P.integral (boundedTrunc hg n) (ψ : H)
      map_add' := fun ψ φ => by
        refine tendsto_nhds_unique
          (P.cauchySeq_integral_trunc hg (ψ + φ).2).tendsto_limUnder ?_
        refine ((P.cauchySeq_integral_trunc hg ψ.2).tendsto_limUnder.add
          (P.cauchySeq_integral_trunc hg φ.2).tendsto_limUnder).congr fun n => ?_
        rw [Submodule.coe_add, map_add]
      map_smul' := fun c ψ => by
        refine tendsto_nhds_unique
          (P.cauchySeq_integral_trunc hg (c • ψ).2).tendsto_limUnder ?_
        refine ((P.cauchySeq_integral_trunc hg ψ.2).tendsto_limUnder.const_smul c).congr
          fun n => ?_
        rw [Submodule.coe_smul, map_smul] }

/-- **The domain of `∫ g dP` is `D_g`** (Reed–Simon I, (VIII.5)). -/
theorem mem_integralPMap_domain {g : X → ℂ} (hg : Measurable g) {ψ : H} :
    ψ ∈ (P.integralPMap hg).domain ↔ MemLp g 2 (P.measure ψ) :=
  Iff.rfl

/-- **The defining limit**: `(∫ gₙ dP) ψ → (∫ g dP) ψ` for `ψ ∈ D_g`. -/
theorem tendsto_integral_trunc {g : X → ℂ} (hg : Measurable g)
    (ψ : (P.integralPMap hg).domain) :
    Tendsto (fun n => P.integral (boundedTrunc hg n) ψ) atTop (𝓝 (P.integralPMap hg ψ)) :=
  (P.cauchySeq_integral_trunc hg ψ.2).tendsto_limUnder

/-- **Other approximations**: if bounded `hₙ → g` pointwise with `‖hₙ‖ ≤ G` and
`G ∈ L²(μ_ψ)`, then `(∫ hₙ dP) ψ → (∫ g dP) ψ` for `ψ ∈ D_g`. -/
theorem tendsto_integral_integralPMap {g : X → ℂ} (hg : Measurable g)
    (h : ℕ → boundedMeasurable X) {G : X → ℝ} (ψ : (P.integralPMap hg).domain)
    (hG : MemLp G 2 (P.measure ψ)) (hhG : ∀ n x, ‖(h n : X → ℂ) x‖ ≤ G x)
    (hlim : ∀ x, Tendsto (fun n => (h n : X → ℂ) x) atTop (𝓝 (g x))) :
    Tendsto (fun n => P.integral (h n) ψ) atTop (𝓝 (P.integralPMap hg ψ)) := by
  have hgG : ∀ x, ‖g x‖ ≤ G x := fun x => le_of_tendsto' (hlim x).norm fun n => hhG n x
  have hb : ∀ n x, ‖((h n - boundedTrunc hg n : boundedMeasurable X) : X → ℂ) x‖ ≤
      2 * G x := fun n x => by
    change ‖(h n : X → ℂ) x - (boundedTrunc hg n : X → ℂ) x‖ ≤ 2 * G x
    linarith [norm_sub_le ((h n : X → ℂ) x) ((boundedTrunc hg n : X → ℂ) x), hhG n x,
      norm_boundedTrunc_le hg n x, hgG x]
  have hl : ∀ x, Tendsto (fun n => ((h n - boundedTrunc hg n : boundedMeasurable X) : X → ℂ) x)
      atTop (𝓝 0) := fun x => by
    have h2 := (hlim x).sub (tendsto_boundedTrunc hg x)
    rw [sub_self] at h2
    exact h2
  have h0 := P.tendsto_integral_apply_zero (fun n => h n - boundedTrunc hg n)
    (G := fun x => 2 * G x) (ψ : H) (hG.const_mul 2) hb hl
  simpa [map_sub] using h0.add (P.tendsto_integral_trunc hg ψ)

/-- **`‖(∫ g dP) ψ‖² = ∫ |g|² dμ_ψ`** for `ψ ∈ D_g`, in `ℝ≥0∞`. -/
theorem enorm_integralPMap_apply_sq {g : X → ℂ} (hg : Measurable g)
    (ψ : (P.integralPMap hg).domain) :
    ‖P.integralPMap hg ψ‖ₑ ^ 2 = ∫⁻ x, ‖g x‖ₑ ^ 2 ∂(P.measure ψ) := by
  have h1 : Tendsto (fun n => ‖P.integral (boundedTrunc hg n) ψ‖ₑ ^ 2) atTop
      (𝓝 (‖P.integralPMap hg ψ‖ₑ ^ 2)) :=
    ((ENNReal.continuous_pow 2).tendsto _).comp
      ((continuous_enorm.tendsto _).comp (P.tendsto_integral_trunc hg ψ))
  have hfin : ∫⁻ x, ‖g x‖ₑ ^ 2 ∂(P.measure ψ) ≠ ∞ :=
    ((memLp_two_iff_lintegral_lt_top hg.aestronglyMeasurable).1 ψ.2).ne
  have h2 : Tendsto (fun n => ∫⁻ x, ‖(boundedTrunc hg n : X → ℂ) x‖ₑ ^ 2 ∂(P.measure ψ))
      atTop (𝓝 (∫⁻ x, ‖g x‖ₑ ^ 2 ∂(P.measure ψ))) := by
    refine tendsto_lintegral_of_dominated_convergence (fun x => ‖g x‖ₑ ^ 2)
      (fun n => (boundedMeasurable.measurable _).enorm.pow_const 2)
      (fun n => Eventually.of_forall fun x => ?_) hfin
      (Eventually.of_forall fun x => ((ENNReal.continuous_pow 2).tendsto _).comp
        ((continuous_enorm.tendsto _).comp (tendsto_boundedTrunc hg x)))
    refine pow_le_pow_left₀ zero_le ?_ 2
    rw [← ofReal_norm, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (norm_boundedTrunc_le hg n x)
  exact tendsto_nhds_unique h1 (h2.congr fun n => (P.enorm_integral_apply_sq _ _).symm)

/-- **Reed–Simon's defining formula** (p. 263): `(ψ, (∫ g dP) ψ) = ∫ g dμ_ψ` for `ψ ∈ D_g`.
Here `g ∈ L²(μ_ψ) ⊆ L¹(μ_ψ)`, as `μ_ψ` is finite. -/
theorem inner_integralPMap {g : X → ℂ} (hg : Measurable g) (ψ : (P.integralPMap hg).domain) :
    ⟪(ψ : H), P.integralPMap hg ψ⟫_ℂ =
      ∫ x, g x ∂(P.measure ψ) := by -- totalisation-audit: allow g ∈ L² ⊆ L¹, finite measure
  have hint : Integrable g (P.measure ψ) :=
    ((P.mem_integralPMap_domain hg).1 ψ.2).integrable one_le_two
  have h1 : Tendsto (fun n => ⟪(ψ : H), P.integral (boundedTrunc hg n) ψ⟫_ℂ) atTop
      (𝓝 ⟪(ψ : H), P.integralPMap hg ψ⟫_ℂ) :=
    ((continuous_const.inner continuous_id).tendsto _).comp (P.tendsto_integral_trunc hg ψ)
  have h2 : Tendsto (fun n => ∫ x, -- totalisation-audit: allow bounded measurable
      (boundedTrunc hg n : X → ℂ) x ∂(P.measure ψ)) atTop
      (𝓝 (∫ x, g x ∂(P.measure ψ))) := -- totalisation-audit: allow g ∈ L¹
    tendsto_integral_of_dominated_convergence (fun x => ‖g x‖)
      (fun n => (boundedMeasurable.measurable _).aestronglyMeasurable) hint.norm
      (fun n => .of_forall (norm_boundedTrunc_le hg n)) (.of_forall (tendsto_boundedTrunc hg))
  exact tendsto_nhds_unique h1 (h2.congr fun n => (P.inner_integral _ _).symm)

/-! ### Density of `D_g` -/

/-- `μ_{P_s ψ}` is the restriction of `μ_ψ` to `s`. -/
theorem measure_apply_apply {s : Set X} (hs : MeasurableSet s) (ψ : H) :
    P.measure (P s ψ) = (P.measure ψ).restrict s := by
  refine Measure.ext fun t ht => ?_
  have h : P t (P s ψ) = P (t ∩ s) ψ := DFunLike.congr_fun (P.mul_apply ht hs) ψ
  rw [Measure.restrict_apply ht, P.measure_apply _ ht, P.measure_apply _ (ht.inter hs), h]

/-- `P_{‖g‖ ≤ n} ψ ∈ D_g`. -/
theorem apply_mem_integralPMap_domain {g : X → ℂ} (hg : Measurable g) (n : ℕ) (ψ : H) :
    P {x | ‖g x‖ ≤ n} ψ ∈ (P.integralPMap hg).domain := by
  have hs : MeasurableSet {x | ‖g x‖ ≤ (n : ℝ)} := measurableSet_le hg.norm measurable_const
  rw [P.mem_integralPMap_domain, P.measure_apply_apply hs]
  exact (memLp_top_of_bound hg.aestronglyMeasurable n
    (ae_restrict_of_forall_mem hs fun x hx => hx)).mono_exponent le_top

/-- `P_{‖g‖ ≤ n} ψ → ψ`. -/
theorem tendsto_apply_norm_le {g : X → ℂ} (hg : Measurable g) (ψ : H) :
    Tendsto (fun n : ℕ => P {x | ‖g x‖ ≤ n} ψ) atTop (𝓝 ψ) := by
  have hs : ∀ n : ℕ, MeasurableSet {x | ‖g x‖ ≤ (n : ℝ)} := fun n =>
    measurableSet_le hg.norm measurable_const
  have hb : ∀ (n : ℕ) x, ‖((boundedMeasurable.indicator (hs n) : boundedMeasurable X) :
      X → ℂ) x‖ ≤ 1 := fun n x => by
    rw [boundedMeasurable.coe_indicator]
    by_cases hx : x ∈ {x | ‖g x‖ ≤ (n : ℝ)} <;> simp [hx]
  have hl : ∀ x, Tendsto (fun n => ((boundedMeasurable.indicator (hs n) : boundedMeasurable X) :
      X → ℂ) x) atTop (𝓝 (((1 : boundedMeasurable X) : X → ℂ) x)) := fun x => by
    obtain ⟨N, hN⟩ := exists_nat_ge ‖g x‖
    refine tendsto_const_nhds.congr' (eventually_atTop.2 ⟨N, fun n hn => ?_⟩)
    dsimp only
    rw [boundedMeasurable.coe_indicator, Set.indicator_of_mem
      (show x ∈ {x | ‖g x‖ ≤ (n : ℝ)} from hN.trans (Nat.cast_le.2 hn))]
    rfl
  have h := P.tendsto_integral_apply (fun n => boundedMeasurable.indicator (hs n)) 1 1 hb hl ψ
  simpa [P.integral_indicator] using h

/-- **`D_g` is dense** (Reed–Simon I, p. 263). -/
theorem dense_integralPMap_domain {g : X → ℂ} (hg : Measurable g) :
    Dense ((P.integralPMap hg).domain : Set H) := fun ψ =>
  mem_closure_of_tendsto (P.tendsto_apply_norm_le hg ψ)
    (Eventually.of_forall fun n => P.apply_mem_integralPMap_domain hg n ψ)

/-! ### Bounded functions and bounded perturbations -/

/-- **Bounded `f`**: `∫ f dP`, defined on `D_f = H`, is the operator `P.integral f` of
Theorem VII.7. -/
theorem integralPMap_bounded (f : boundedMeasurable X) :
    P.integralPMap (boundedMeasurable.measurable f) =
      ((P.integral f : H →L[ℂ] H) : H →ₗ[ℂ] H).toPMap ⊤ := by
  obtain ⟨C, -, hC⟩ := boundedMeasurable.exists_bound f
  have hdom : ∀ ψ : H, ψ ∈ (P.integralPMap (boundedMeasurable.measurable f)).domain := fun ψ =>
    (memLp_top_of_bound (boundedMeasurable.measurable f).aestronglyMeasurable C
      (Eventually.of_forall hC)).mono_exponent le_top
  refine LinearPMap.ext ?_ fun ψ h _ => ?_
  · change P.integralDomain (boundedMeasurable.measurable f) = ⊤
    exact eq_top_iff.2 fun ψ _ => hdom ψ
  · exact tendsto_nhds_unique (P.tendsto_integral_integralPMap (boundedMeasurable.measurable f)
      (fun _ => f) ⟨ψ, h⟩
      (G := fun _ => C) (memLp_const C) (fun _ x => hC x) (fun _ => tendsto_const_nhds))
      tendsto_const_nhds

/-- For bounded `f`, `D_{g + f} = D_g`. -/
theorem integralPMap_add_bounded_domain {g : X → ℂ} (hg : Measurable g)
    (f : boundedMeasurable X) :
    (P.integralPMap (hg.add (boundedMeasurable.measurable f))).domain =
      (P.integralPMap hg).domain := by
  obtain ⟨C, -, hC⟩ := boundedMeasurable.exists_bound f
  have hf : ∀ ψ : H, MemLp (f : X → ℂ) 2 (P.measure ψ) := fun ψ =>
    (memLp_top_of_bound (boundedMeasurable.measurable f).aestronglyMeasurable C
      (Eventually.of_forall hC)).mono_exponent le_top
  ext ψ
  rw [P.mem_integralPMap_domain, P.mem_integralPMap_domain]
  refine ⟨fun h => ?_, fun h => h.add (hf ψ)⟩
  have h' := h.sub (hf ψ)
  rwa [add_sub_cancel_right] at h'

/-- **Bounded perturbations**: for bounded `f` and `ψ ∈ D_g`,
`(∫ (g + f) dP) ψ = (∫ g dP) ψ + (∫ f dP) ψ`. -/
theorem integralPMap_add_bounded {g : X → ℂ} (hg : Measurable g) (f : boundedMeasurable X)
    (ψ : (P.integralPMap hg).domain)
    (h : (ψ : H) ∈ (P.integralPMap (hg.add (boundedMeasurable.measurable f))).domain) :
    P.integralPMap (hg.add (boundedMeasurable.measurable f)) ⟨ψ, h⟩ =
      P.integralPMap hg ψ + P.integral f ψ := by
  obtain ⟨C, -, hC⟩ := boundedMeasurable.exists_bound f
  have hG : MemLp (fun x => ‖g x‖ + C) 2 (P.measure ψ) :=
    ((P.mem_integralPMap_domain hg).1 ψ.2).norm.add (memLp_const C)
  have hb : ∀ n x, ‖((boundedTrunc hg n + f : boundedMeasurable X) : X → ℂ) x‖ ≤
      ‖g x‖ + C := fun n x => by
    change ‖(boundedTrunc hg n : X → ℂ) x + (f : X → ℂ) x‖ ≤ ‖g x‖ + C
    exact (norm_add_le _ _).trans (add_le_add (norm_boundedTrunc_le hg n x) (hC x))
  have hl : ∀ x, Tendsto (fun n => ((boundedTrunc hg n + f : boundedMeasurable X) : X → ℂ) x)
      atTop (𝓝 ((g + (f : X → ℂ)) x)) := fun x =>
    (tendsto_boundedTrunc hg x).add tendsto_const_nhds
  refine tendsto_nhds_unique (P.tendsto_integral_integralPMap _
    (fun n => boundedTrunc hg n + f) ⟨ψ, h⟩ hG hb hl) ?_
  simpa [map_add] using
    (P.tendsto_integral_trunc hg ψ).add (tendsto_const_nhds (x := P.integral f ψ))

/-! ### Products with bounded functions -/

/-- `μ_{(∫ f dP) ψ} = |f|² μ_ψ`. -/
theorem measure_integral_apply (f : boundedMeasurable X) (ψ : H) :
    P.measure (P.integral f ψ) =
      (P.measure ψ).withDensity fun x => ‖(f : X → ℂ) x‖ₑ ^ 2 := by
  refine Measure.ext fun s hs => ?_
  have h1 : P s (P.integral f ψ) = P.integral (boundedMeasurable.indicator hs * f) ψ := by
    rw [map_mul, P.integral_indicator hs]
    rfl
  rw [P.measure_apply _ hs, withDensity_apply _ hs, h1, ENNReal.ofReal_pow (norm_nonneg _),
    ofReal_norm, P.enorm_integral_apply_sq, ← lintegral_indicator hs]
  refine lintegral_congr fun x => ?_
  by_cases hx : x ∈ s <;> simp [hx]

/-- If `g f = k` with `f`, `k` bounded, then `(∫ f dP) ψ ∈ D_g`. -/
theorem integral_mem_integralPMap_domain {g : X → ℂ} (hg : Measurable g)
    (f k : boundedMeasurable X) (hk : ∀ x, (k : X → ℂ) x = g x * (f : X → ℂ) x) (ψ : H) :
    P.integral f ψ ∈ (P.integralPMap hg).domain := by
  rw [P.mem_integralPMap_domain, memLp_two_iff_lintegral_lt_top hg.aestronglyMeasurable,
    P.measure_integral_apply, lintegral_withDensity_eq_lintegral_mul _
      ((boundedMeasurable.measurable f).enorm.pow_const 2) (hg.enorm.pow_const 2)]
  have e : ∫⁻ x, ((fun x => ‖(f : X → ℂ) x‖ₑ ^ 2) * fun x => ‖g x‖ₑ ^ 2) x ∂(P.measure ψ) =
      ‖P.integral k ψ‖ₑ ^ 2 := by
    rw [P.enorm_integral_apply_sq]
    refine lintegral_congr fun x => ?_
    rw [Pi.mul_apply, hk, enorm_mul, mul_pow, mul_comm]
  rw [e]
  exact ENNReal.pow_lt_top enorm_lt_top

/-- **`(∫ g dP) (∫ f dP) ψ = (∫ g f dP) ψ`** when `f` and `k = g f` are bounded. -/
theorem integralPMap_integral {g : X → ℂ} (hg : Measurable g) (f k : boundedMeasurable X)
    (hk : ∀ x, (k : X → ℂ) x = g x * (f : X → ℂ) x) (ψ : H) :
    P.integralPMap hg ⟨P.integral f ψ, P.integral_mem_integralPMap_domain hg f k hk ψ⟩ =
      P.integral k ψ := by
  obtain ⟨C, -, hC⟩ := boundedMeasurable.exists_bound k
  have hb : ∀ n x, ‖((boundedTrunc hg n * f : boundedMeasurable X) : X → ℂ) x‖ ≤ C :=
    fun n x => by
      change ‖(boundedTrunc hg n : X → ℂ) x * (f : X → ℂ) x‖ ≤ C
      rw [norm_mul]
      calc ‖(boundedTrunc hg n : X → ℂ) x‖ * ‖(f : X → ℂ) x‖ ≤ ‖g x‖ * ‖(f : X → ℂ) x‖ :=
            mul_le_mul_of_nonneg_right (norm_boundedTrunc_le hg n x) (norm_nonneg _)
        _ = ‖(k : X → ℂ) x‖ := by rw [hk, norm_mul]
        _ ≤ C := hC x
  have hl : ∀ x, Tendsto (fun n => ((boundedTrunc hg n * f : boundedMeasurable X) : X → ℂ) x)
      atTop (𝓝 ((k : X → ℂ) x)) := fun x => by
    rw [hk]
    exact (tendsto_boundedTrunc hg x).mul tendsto_const_nhds
  have h := P.tendsto_integral_apply (fun n => boundedTrunc hg n * f) k C hb hl ψ
  refine tendsto_nhds_unique (P.tendsto_integral_trunc hg _) (h.congr fun n => ?_)
  rw [map_mul]
  rfl

/-! ### Self-adjointness for real `g` -/

/-- The truncations of a real-valued function are real: `star gₙ = gₙ`. -/
theorem star_boundedTrunc_ofReal {r : X → ℝ} (hr : Measurable fun x => (r x : ℂ)) (n : ℕ) :
    star (boundedTrunc hr n) = boundedTrunc hr n := by
  refine Subtype.ext (funext fun x => ?_)
  change star ((boundedTrunc hr n : X → ℂ) x) = (boundedTrunc hr n : X → ℂ) x
  rw [coe_boundedTrunc]
  by_cases hx : x ∈ {x | ‖(r x : ℂ)‖ ≤ (n : ℝ)}
  · rw [Set.indicator_of_mem hx, Complex.star_def, Complex.conj_ofReal]
  · rw [Set.indicator_of_notMem hx, star_zero]

/-- **`∫ r dP` is symmetric** for real `r`: `⟪(∫ r dP) φ, ψ⟫ = lim ⟪(∫ rₙ dP) φ, ψ⟫ =
lim ⟪φ, (∫ rₙ dP) ψ⟫ = ⟪φ, (∫ r dP) ψ⟫`, as the `∫ rₙ dP` are self-adjoint. -/
theorem isSymmetric_integralPMap {r : X → ℝ} (hr : Measurable fun x => (r x : ℂ)) :
    IsSymmetric (P.integralPMap hr) := by
  refine ⟨P.dense_integralPMap_domain hr, fun φ ψ => ?_⟩
  have hsa : ∀ (n : ℕ) (u v : H), ⟪P.integral (boundedTrunc hr n) u, v⟫_ℂ =
      ⟪u, P.integral (boundedTrunc hr n) v⟫_ℂ := fun n u v => by
    have e : ContinuousLinearMap.adjoint (P.integral (boundedTrunc hr n)) =
        P.integral (boundedTrunc hr n) := by
      rw [← ContinuousLinearMap.star_eq_adjoint, ← map_star, star_boundedTrunc_ofReal]
    rw [← ContinuousLinearMap.adjoint_inner_left, e]
  have h1 : Tendsto (fun n => ⟪P.integral (boundedTrunc hr n) φ, (ψ : H)⟫_ℂ) atTop
      (𝓝 ⟪P.integralPMap hr φ, (ψ : H)⟫_ℂ) :=
    (P.tendsto_integral_trunc hr φ).inner tendsto_const_nhds
  have h2 : Tendsto (fun n => ⟪(φ : H), P.integral (boundedTrunc hr n) ψ⟫_ℂ) atTop
      (𝓝 ⟪(φ : H), P.integralPMap hr ψ⟫_ℂ) :=
    tendsto_const_nhds.inner (P.tendsto_integral_trunc hr ψ)
  exact tendsto_nhds_unique h1 (h2.congr fun n => (hsa n φ ψ).symm)

/-- **`∫ r dP + z` is onto** for real `r` and `z ∉ ℝ`:
`η = (∫ r dP + z) (∫ (r + z)⁻¹ dP) η`, since `r (r + z)⁻¹ = 1 - z (r + z)⁻¹` is bounded. -/
theorem range_addScalar_integralPMap {r : X → ℝ} (hr : Measurable fun x => (r x : ℂ)) {z : ℂ}
    (hz : z.im ≠ 0) : LinearMap.range (addScalar (P.integralPMap hr) z).toFun = ⊤ := by
  have hne : ∀ x, (r x : ℂ) + z ≠ 0 := fun x h => hz (by simpa using congrArg Complex.im h)
  have hk : (fun x => ((r x : ℂ) + z)⁻¹) ∈ -- totalisation-audit: allow r x + z ≠ 0
      boundedMeasurable X := by
    refine ⟨(hr.add_const z).inv, |z.im|⁻¹, fun x => ?_⟩ -- totalisation-audit: allow z.im ≠ 0
    rw [norm_inv]
    refine inv_anti₀ (abs_pos.2 hz) ?_
    simpa using Complex.abs_im_le_norm ((r x : ℂ) + z)
  let k : boundedMeasurable X := ⟨_, hk⟩
  let k' : boundedMeasurable X := 1 - z • k
  have hk' : ∀ x, (k' : X → ℂ) x = (r x : ℂ) * (k : X → ℂ) x := fun x => by
    change 1 - z * ((r x : ℂ) + z)⁻¹ = -- totalisation-audit: allow r x + z ≠ 0
      (r x : ℂ) * ((r x : ℂ) + z)⁻¹ -- totalisation-audit: allow r x + z ≠ 0
    calc 1 - z * ((r x : ℂ) + z)⁻¹ -- totalisation-audit: allow r x + z ≠ 0
        = ((r x : ℂ) + z) * ((r x : ℂ) + z)⁻¹ - -- totalisation-audit: allow r x + z ≠ 0
          z * ((r x : ℂ) + z)⁻¹ := by -- totalisation-audit: allow r x + z ≠ 0
          rw [mul_inv_cancel₀ (hne x)]
      _ = (r x : ℂ) * ((r x : ℂ) + z)⁻¹ := by ring -- totalisation-audit: allow r x + z ≠ 0
  refine eq_top_iff.2 fun η _ => LinearMap.mem_range.2
    ⟨⟨P.integral k η, P.integral_mem_integralPMap_domain hr k k' hk' η⟩, ?_⟩
  change P.integralPMap hr ⟨P.integral k η, P.integral_mem_integralPMap_domain hr k k' hk' η⟩ +
    z • P.integral k η = η
  rw [P.integralPMap_integral hr k k' hk' η]
  simp [k', map_sub, map_smul]

/-- **Reed–Simon I, Theorem VIII.6** (p. 264, for an arbitrary projection-valued measure): if `r`
is real-valued, then `∫ r dP`, defined on `D_r`, is self-adjoint. -/
theorem isSelfAdjoint_integralPMap {r : X → ℝ} (hr : Measurable fun x => (r x : ℂ)) :
    IsSelfAdjoint (P.integralPMap hr) :=
  isSelfAdjoint_of_range_addScalar (P.isSymmetric_integralPMap hr) Complex.I
    (P.range_addScalar_integralPMap hr (by simp)) (P.range_addScalar_integralPMap hr (by simp))

/-! ### The adjoint -/

/-- `ḡ` is measurable. -/
theorem measurable_star_of_measurable {g : X → ℂ} (hg : Measurable g) : Measurable (star g) :=
  continuous_star.measurable.comp hg

/-- `D_ḡ = D_g`. -/
theorem integralPMap_star_domain {g : X → ℂ} (hg : Measurable g) :
    (P.integralPMap (measurable_star_of_measurable hg)).domain = (P.integralPMap hg).domain := by
  ext ψ
  rw [P.mem_integralPMap_domain, P.mem_integralPMap_domain]
  exact ⟨fun h => h.congr_norm hg.aestronglyMeasurable (Eventually.of_forall fun x => by simp),
    fun h => h.congr_norm (measurable_star_of_measurable hg).aestronglyMeasurable
      (Eventually.of_forall fun x => by simp)⟩

/-- The truncations of `ḡ` are the conjugates of the truncations of `g`. -/
theorem boundedTrunc_star {g : X → ℂ} (hg : Measurable g) (n : ℕ) :
    boundedTrunc (measurable_star_of_measurable hg) n = star (boundedTrunc hg n) := by
  refine Subtype.ext (funext fun x => ?_)
  change {x | ‖(star g) x‖ ≤ n}.indicator (star g) x = star ({x | ‖g x‖ ≤ n}.indicator g x)
  by_cases hx : ‖g x‖ ≤ n
  · rw [Set.indicator_of_mem (show x ∈ {x | ‖(star g) x‖ ≤ (n : ℝ)} by simpa using hx),
      Set.indicator_of_mem (show x ∈ {x | ‖g x‖ ≤ (n : ℝ)} from hx)]
    rfl
  · rw [Set.indicator_of_notMem (show x ∉ {x | ‖(star g) x‖ ≤ (n : ℝ)} by simpa using hx),
      Set.indicator_of_notMem (show x ∉ {x | ‖g x‖ ≤ (n : ℝ)} from hx), star_zero]

/-- `⟪(∫ f̄ dP) u, v⟫ = ⟪u, (∫ f dP) v⟫` for bounded `f`. -/
theorem inner_integral_star_left (f : boundedMeasurable X) (u v : H) :
    ⟪P.integral (star f) u, v⟫_ℂ = ⟪u, P.integral f v⟫_ℂ := by
  rw [map_star, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]

/-- `∫ ḡ dP ⊆ (∫ g dP)†`: `⟪(∫ g dP) ψ, φ⟫ = ⟪ψ, (∫ ḡ dP) φ⟫` on `D_g`, as a limit of the
bounded identities. -/
theorem integralPMap_star_le {g : X → ℂ} (hg : Measurable g) :
    P.integralPMap (measurable_star_of_measurable hg) ≤
      LinearPMap.adjoint (P.integralPMap hg) := by
  refine LinearPMap.IsFormalAdjoint.le_adjoint (P.dense_integralPMap_domain hg) fun ψ φ => ?_
  have h1 : Tendsto (fun n => ⟪P.integral (boundedTrunc hg n) ψ, (φ : H)⟫_ℂ) atTop
      (𝓝 ⟪P.integralPMap hg ψ, (φ : H)⟫_ℂ) :=
    (P.tendsto_integral_trunc hg ψ).inner tendsto_const_nhds
  have h2 : Tendsto (fun n => ⟪(ψ : H),
      P.integral (boundedTrunc (measurable_star_of_measurable hg) n) φ⟫_ℂ) atTop
      (𝓝 ⟪(ψ : H), P.integralPMap (measurable_star_of_measurable hg) φ⟫_ℂ) :=
    tendsto_const_nhds.inner (P.tendsto_integral_trunc _ φ)
  refine tendsto_nhds_unique h1 (h2.congr fun n => ?_)
  rw [boundedTrunc_star, ← P.inner_integral_star_left, star_star]

/-- `D((∫ g dP)†) ⊆ D_g`.  For `φ` in the domain of the adjoint, with `η = (∫ g dP)† φ` and
`sₙ = {‖g‖ ≤ n}`: `(∫ ḡₙ dP) φ = P_{sₙ} η`, since `(∫ g dP) P_{sₙ} = ∫ gₙ dP`; so
`∫ |gₙ|² dμ_φ = ‖P_{sₙ} η‖² ≤ ‖η‖²`, and Fatou's lemma gives `∫ |g|² dμ_φ ≤ ‖η‖²`. -/
theorem adjoint_integralPMap_domain_le {g : X → ℂ} (hg : Measurable g) :
    (LinearPMap.adjoint (P.integralPMap hg)).domain ≤ (P.integralPMap hg).domain := by
  intro φ hφ
  let η := LinearPMap.adjoint (P.integralPMap hg) ⟨φ, hφ⟩
  have hadj := LinearPMap.adjoint_isFormalAdjoint (P.dense_integralPMap_domain hg)
  have hs : ∀ n : ℕ, MeasurableSet {x | ‖g x‖ ≤ (n : ℝ)} := fun n =>
    measurableSet_le hg.norm measurable_const
  have hk : ∀ (n : ℕ) x, (boundedTrunc hg n : X → ℂ) x =
      g x * (boundedMeasurable.indicator (hs n) : X → ℂ) x := fun n x => by
    rw [coe_boundedTrunc, boundedMeasurable.coe_indicator]
    by_cases hx : x ∈ {x | ‖g x‖ ≤ (n : ℝ)}
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, mul_one]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, mul_zero]
  have key : ∀ n : ℕ, P.integral (star (boundedTrunc hg n)) φ = P {x | ‖g x‖ ≤ n} η :=
    fun n => ext_inner_right ℂ fun v => by
      have hsym : ⟪P {x | ‖g x‖ ≤ (n : ℝ)} η, v⟫_ℂ = ⟪η, P {x | ‖g x‖ ≤ (n : ℝ)} v⟫_ℂ :=
        (P.isSelfAdjoint (hs n)).isSymmetric η v
      rw [P.inner_integral_star_left, hsym]
      have hv := hadj ⟨φ, hφ⟩ ⟨P.integral (boundedMeasurable.indicator (hs n)) v,
        P.integral_mem_integralPMap_domain hg _ _ (hk n) v⟩
      rw [P.integralPMap_integral hg _ _ (hk n) v] at hv
      have e : P.integral (boundedMeasurable.indicator (hs n)) v = P {x | ‖g x‖ ≤ (n : ℝ)} v := by
        rw [P.integral_indicator]
      exact hv.symm.trans (congrArg (fun w => ⟪η, w⟫_ℂ) e)
  have hbound : ∀ n : ℕ,
      ∫⁻ x, ‖(boundedTrunc hg n : X → ℂ) x‖ₑ ^ 2 ∂(P.measure φ) ≤ ‖η‖ₑ ^ 2 := fun n => by
    have e1 : ∫⁻ x, ‖(boundedTrunc hg n : X → ℂ) x‖ₑ ^ 2 ∂(P.measure φ) =
        ‖P.integral (star (boundedTrunc hg n)) φ‖ₑ ^ 2 := by
      rw [P.enorm_integral_apply_sq]
      refine lintegral_congr fun x => ?_
      change _ = ‖star ((boundedTrunc hg n : X → ℂ) x)‖ₑ ^ 2
      rw [← ofReal_norm, ← ofReal_norm, norm_star]
    rw [e1, key n]
    refine pow_le_pow_left₀ zero_le ?_ 2
    rw [← ofReal_norm, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (P.norm_apply_le η _)
  have hfin : ∫⁻ x, ‖g x‖ₑ ^ 2 ∂(P.measure φ) ≤ ‖η‖ₑ ^ 2 :=
    calc ∫⁻ x, ‖g x‖ₑ ^ 2 ∂(P.measure φ)
        = ∫⁻ x, liminf (fun n : ℕ => ‖(boundedTrunc hg n : X → ℂ) x‖ₑ ^ 2) atTop
            ∂(P.measure φ) :=
          lintegral_congr fun x => (((ENNReal.continuous_pow 2).tendsto _).comp
            ((continuous_enorm.tendsto _).comp (tendsto_boundedTrunc hg x))).liminf_eq.symm
      _ ≤ liminf (fun n : ℕ => ∫⁻ x, ‖(boundedTrunc hg n : X → ℂ) x‖ₑ ^ 2 ∂(P.measure φ))
            atTop :=
          lintegral_liminf_le fun n => (boundedMeasurable.measurable _).enorm.pow_const 2
      _ ≤ ‖η‖ₑ ^ 2 := liminf_le_of_frequently_le (Eventually.of_forall hbound).frequently
  exact (P.mem_integralPMap_domain hg).2 ((memLp_two_iff_lintegral_lt_top
    hg.aestronglyMeasurable).2 (hfin.trans_lt (ENNReal.pow_lt_top enorm_lt_top)))

/-- **The adjoint of `∫ g dP`**: `(∫ g dP)† = ∫ ḡ dP`. -/
theorem adjoint_integralPMap {g : X → ℂ} (hg : Measurable g) :
    LinearPMap.adjoint (P.integralPMap hg) = P.integralPMap (measurable_star_of_measurable hg) := by
  refine (LinearPMap.eq_of_le_of_domain_eq (P.integralPMap_star_le hg) ?_).symm
  refine le_antisymm (P.integralPMap_star_le hg).1 ?_
  rw [P.integralPMap_star_domain hg]
  exact P.adjoint_integralPMap_domain_le hg

end ProjectionValuedMeasure

end SpectralTheorem
