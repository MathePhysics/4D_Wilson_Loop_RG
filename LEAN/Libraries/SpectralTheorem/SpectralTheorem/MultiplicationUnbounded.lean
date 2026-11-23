import SpectralTheorem.MultiplicationBounded
import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-!
# Unbounded multiplication operators on `L²`

Let `μ` be a measure on a measurable space `α` (not assumed finite or σ-finite) and let
`f : α → ℂ` be almost everywhere strongly measurable.  Multiplication by `f` is the partially
defined operator `T_f` on `L²(α, μ) = Lp ℂ 2 μ` with domain `D(T_f) = {φ ∈ L² | f φ ∈ L²}` and
`T_f φ = f φ`.  Since `f` takes values in `ℂ`, it is finite everywhere, so Reed–Simon's
hypothesis "finite a.e." holds automatically.

Source: Reed–Simon, *Methods of Modern Mathematical Physics I* (1972), §VIII.3, Proposition 1
and its proof, pp. 259–260; the operators are used in Theorems VIII.4 and VIII.5 (pp. 260–262).
Reed–Simon assume `μ` finite; this is not needed here.  Their Proposition 1 also identifies the
spectrum of `T_f` with the essential range of `f`, which is not proved here.

## Main definitions

* `SpectralTheorem.mulPMap μ f : Lp ℂ 2 μ →ₗ.[ℂ] Lp ℂ 2 μ`: the maximal multiplication operator
  `T_f`, with domain `{φ | MemLp (fun x => f x * φ x) 2 μ}`.

## Main results

* `SpectralTheorem.coeFn_mulPMap`: `T_f φ =ᵐ[μ] fun x => f x * φ x`;
  `mulPMap_apply_of_ae_eq`: `T_f φ = η` whenever `η` represents `f φ`.
* `SpectralTheorem.mulPMap_congr_ae`: `T_f` only depends on the a.e. class of `f`.
* `SpectralTheorem.mulPMap_mulL`, `mulPMap_mulL_of_mem`: `T_f M_g = M_{fg}` when `fg` is
  bounded, and `M_g` maps `D(T_f)` into itself with `T_f M_g = M_g T_f` there.
* `SpectralTheorem.mulPMap_eq_toPMap_mulL`: for essentially bounded `f`, `T_f` is everywhere
  defined and equals `M_f`.
* `SpectralTheorem.mulPMap_add_le`: `T_f + T_g ⊆ T_{f+g}`.
* `SpectralTheorem.exists_truncation`: truncations `χₙ` with `‖χₙ‖ ≤ 1`, `f χₙ` bounded and
  `χₙ → 1` pointwise.
* `SpectralTheorem.dense_mulPMap_domain`: `T_f` is densely defined.
* `SpectralTheorem.adjoint_mulPMap`: `T_f† = T_{f̄}` (by truncation, as in Reed–Simon).
* `SpectralTheorem.isSelfAdjoint_mulPMap`, `isSelfAdjoint_mulPMap_ofReal`: **Reed–Simon I,
  §VIII.3, Proposition 1**: `T_f` is self-adjoint when `f` is real-valued.
* `SpectralTheorem.tendsto_mulPMap_apply_of_dominated`: if `Fₙ → f` a.e. and `‖Fₙ‖ ≤ ‖G‖` a.e.,
  then `T_{Fₙ} φ → T_f φ` for `φ ∈ D(T_G)`; `tendsto_mulL_apply_mulPMap`: the case of bounded
  `Fₙ` with `‖Fₙ‖ ≤ ‖f‖`, used for Reed–Simon I, Theorem VIII.5 (c), p. 262.
-/

open MeasureTheory Filter Topology ComplexConjugate
open scoped ENNReal InnerProductSpace LinearPMap

noncomputable section

namespace SpectralTheorem

variable {α : Type*} [MeasurableSpace α] (μ : Measure α)

/-- The natural domain `{φ ∈ L² | f φ ∈ L²}` of multiplication by `f`. -/
def mulDomain (f : α → ℂ) : Submodule ℂ (Lp ℂ 2 μ) where
  carrier := {φ | MemLp (fun x => f x * φ x) 2 μ}
  add_mem' {φ ψ} hφ hψ := by
    refine (MemLp.add hφ hψ).ae_eq ?_
    filter_upwards [Lp.coeFn_add φ ψ] with x hx
    rw [Pi.add_apply, hx, Pi.add_apply, mul_add]
  zero_mem' := by
    refine (MemLp.zero : MemLp (0 : α → ℂ) 2 μ).ae_eq ?_
    filter_upwards [Lp.coeFn_zero ℂ 2 μ] with x hx
    rw [hx, Pi.zero_apply, mul_zero]
  smul_mem' c φ hφ := by
    refine (MemLp.const_smul hφ c).ae_eq ?_
    filter_upwards [Lp.coeFn_smul c φ] with x hx
    rw [Pi.smul_apply, hx, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_left_comm]

variable {μ} in
/-- Membership in `D(T_f)`. -/
theorem mem_mulDomain {f : α → ℂ} {φ : Lp ℂ 2 μ} :
    φ ∈ mulDomain μ f ↔ MemLp (fun x => f x * φ x) 2 μ :=
  Iff.rfl

/-- The multiplication operator `T_f` on `L²(μ)`, with its maximal domain
`D(T_f) = {φ ∈ L² | f φ ∈ L²}` (Reed–Simon I, §VIII.3, p. 259). -/
def mulPMap (f : α → ℂ) : Lp ℂ 2 μ →ₗ.[ℂ] Lp ℂ 2 μ where
  domain := mulDomain μ f
  toFun :=
    { toFun := fun φ => (mem_mulDomain.1 φ.2).toLp _
      map_add' := fun φ ψ => by
        rw [← MemLp.toLp_add]
        apply MemLp.toLp_congr
        filter_upwards [Lp.coeFn_add (φ : Lp ℂ 2 μ) ψ] with x hx
        rw [Submodule.coe_add, Pi.add_apply, hx, Pi.add_apply, mul_add]
      map_smul' := fun c φ => by
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
        apply MemLp.toLp_congr
        filter_upwards [Lp.coeFn_smul c (φ : Lp ℂ 2 μ)] with x hx
        rw [Submodule.coe_smul, hx, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
          mul_left_comm] }

variable {μ}

/-- The domain of `T_f` is `{φ | f φ ∈ L²}`. -/
theorem mem_mulPMap_domain {f : α → ℂ} {φ : Lp ℂ 2 μ} :
    φ ∈ (mulPMap μ f).domain ↔ MemLp (fun x => f x * φ x) 2 μ :=
  Iff.rfl

/-- `T_f φ` is the `L²` class of `f φ`. -/
theorem mulPMap_apply {f : α → ℂ} (φ : (mulPMap μ f).domain) :
    mulPMap μ f φ = (mem_mulPMap_domain.1 φ.2).toLp _ :=
  rfl

/-- `T_f φ` is represented by the pointwise product `f φ`. -/
theorem coeFn_mulPMap {f : α → ℂ} (φ : (mulPMap μ f).domain) :
    mulPMap μ f φ =ᵐ[μ] fun x => f x * (φ : Lp ℂ 2 μ) x :=
  MemLp.coeFn_toLp (mem_mulPMap_domain.1 φ.2)

/-- If `η ∈ L²` represents `f φ`, then `φ ∈ D(T_f)`. -/
theorem mem_mulPMap_domain_of_ae_eq {f : α → ℂ} {φ η : Lp ℂ 2 μ}
    (h : (η : α → ℂ) =ᵐ[μ] fun x => f x * φ x) : φ ∈ (mulPMap μ f).domain :=
  (Lp.memLp η).ae_eq h

/-- If `η ∈ L²` represents `f φ`, then `T_f φ = η`. -/
theorem mulPMap_apply_of_ae_eq {f : α → ℂ} {φ η : Lp ℂ 2 μ}
    (h : (η : α → ℂ) =ᵐ[μ] fun x => f x * φ x) :
    mulPMap μ f ⟨φ, mem_mulPMap_domain_of_ae_eq h⟩ = η :=
  Lp.ext ((coeFn_mulPMap _).trans h.symm)

/-! ### Relation with bounded multiplication operators -/

/-- If `f g` is essentially bounded, then `M_g` maps `L²` into `D(T_f)`. -/
theorem mulL_mem_mulPMap_domain {f g : α → ℂ} (hg : MemLp g ∞ μ) (hfg : MemLp (f * g) ∞ μ)
    (φ : Lp ℂ 2 μ) : mulL g hg φ ∈ (mulPMap μ f).domain := by
  refine mem_mulPMap_domain_of_ae_eq (η := mulL (f * g) hfg φ) ?_
  filter_upwards [coeFn_mulL hfg φ, coeFn_mulL hg φ] with x h1 h2
  rw [h1, h2, Pi.mul_apply, mul_assoc]

/-- `T_f M_g = M_{fg}` when `f g` is essentially bounded. -/
theorem mulPMap_mulL {f g : α → ℂ} (hg : MemLp g ∞ μ) (hfg : MemLp (f * g) ∞ μ)
    (φ : Lp ℂ 2 μ) :
    mulPMap μ f ⟨mulL g hg φ, mulL_mem_mulPMap_domain hg hfg φ⟩ = mulL (f * g) hfg φ := by
  refine Lp.ext ((coeFn_mulPMap _).trans ?_)
  filter_upwards [coeFn_mulL hfg φ, coeFn_mulL hg φ] with x h1 h2
  rw [h1, h2, Pi.mul_apply, mul_assoc]

/-- A bounded multiplication operator `M_g` maps `D(T_f)` into itself. -/
theorem mulL_mem_mulPMap_domain_of_mem {f g : α → ℂ} (hg : MemLp g ∞ μ) {φ : Lp ℂ 2 μ}
    (hφ : φ ∈ (mulPMap μ f).domain) : mulL g hg φ ∈ (mulPMap μ f).domain := by
  refine mem_mulPMap_domain_of_ae_eq (η := mulL g hg (mulPMap μ f ⟨φ, hφ⟩)) ?_
  filter_upwards [coeFn_mulL hg (mulPMap μ f ⟨φ, hφ⟩), coeFn_mulPMap ⟨φ, hφ⟩,
    coeFn_mulL hg φ] with x h1 h2 h3
  rw [h1, h2, h3, mul_left_comm]

/-- Bounded and unbounded multiplication operators commute: `T_f M_g φ = M_g T_f φ` for
`φ ∈ D(T_f)`. -/
theorem mulPMap_mulL_of_mem {f g : α → ℂ} (hg : MemLp g ∞ μ) {φ : Lp ℂ 2 μ}
    (hφ : φ ∈ (mulPMap μ f).domain) :
    mulPMap μ f ⟨mulL g hg φ, mulL_mem_mulPMap_domain_of_mem hg hφ⟩ =
      mulL g hg (mulPMap μ f ⟨φ, hφ⟩) := by
  refine Lp.ext ((coeFn_mulPMap _).trans ?_)
  filter_upwards [coeFn_mulL hg (mulPMap μ f ⟨φ, hφ⟩), coeFn_mulPMap ⟨φ, hφ⟩,
    coeFn_mulL hg φ] with x h1 h2 h3
  rw [h1, h2, h3, mul_left_comm]

/-- For essentially bounded `f`, the domain of `T_f` is all of `L²`. -/
theorem mulPMap_domain_eq_top {f : α → ℂ} (hf : MemLp f ∞ μ) : (mulPMap μ f).domain = ⊤ :=
  eq_top_iff.2 fun φ _ => memLp_two_mul hf φ

/-- For essentially bounded `f`, `T_f φ = M_f φ`. -/
theorem mulPMap_apply_eq_mulL {f : α → ℂ} (hf : MemLp f ∞ μ) (φ : (mulPMap μ f).domain) :
    mulPMap μ f φ = mulL f hf φ :=
  Lp.ext ((coeFn_mulPMap _).trans (coeFn_mulL hf φ).symm)

/-- For essentially bounded `f`, `T_f` is the everywhere defined operator `M_f`. -/
theorem mulPMap_eq_toPMap_mulL {f : α → ℂ} (hf : MemLp f ∞ μ) :
    mulPMap μ f = (mulL f hf : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ).toPMap ⊤ := by
  refine LinearPMap.ext (by rw [mulPMap_domain_eq_top hf, LinearMap.toPMap_domain]) ?_
  intro φ hφ _
  exact mulPMap_apply_eq_mulL hf ⟨φ, hφ⟩

/-- `T_f + T_g ⊆ T_{f+g}`: on `D(T_f) ∩ D(T_g)`, the sum `T_f + T_g` agrees with `T_{f+g}`. -/
theorem mulPMap_add_le (f g : α → ℂ) : mulPMap μ f + mulPMap μ g ≤ mulPMap μ (f + g) := by
  have key : ∀ (φ : Lp ℂ 2 μ) (h1 : φ ∈ (mulPMap μ f).domain) (h2 : φ ∈ (mulPMap μ g).domain),
      ((mulPMap μ f ⟨φ, h1⟩ + mulPMap μ g ⟨φ, h2⟩ : Lp ℂ 2 μ) : α → ℂ) =ᵐ[μ]
        fun x => (f + g) x * φ x := fun φ h1 h2 => by
    filter_upwards [Lp.coeFn_add (mulPMap μ f ⟨φ, h1⟩) (mulPMap μ g ⟨φ, h2⟩),
      coeFn_mulPMap ⟨φ, h1⟩, coeFn_mulPMap ⟨φ, h2⟩] with x ha hb hc
    rw [ha, Pi.add_apply, hb, hc, Pi.add_apply, add_mul]
  refine ⟨fun φ hφ => mem_mulPMap_domain_of_ae_eq (key φ hφ.1 hφ.2), fun φ ψ hφψ => ?_⟩
  rw [LinearPMap.add_apply]
  refine Lp.ext ((key _ _ _).trans ?_)
  rw [hφψ]
  exact (coeFn_mulPMap ψ).symm

/-! ### Truncations and density of the domain -/

/-- Truncations of `f` (Reed–Simon I, p. 259): there are functions `χₙ` with `‖χₙ‖ ≤ 1`, real
values, `f χₙ` essentially bounded, and `χₙ x → 1` for every `x`.  One can take `χₙ` to be the
indicator of `{‖f̃‖ ≤ n}` for a strongly measurable version `f̃` of `f`. -/
theorem exists_truncation {f : α → ℂ} (hf : AEStronglyMeasurable f μ) :
    ∃ χ : ℕ → α → ℂ, (∀ n, MemLp (χ n) ∞ μ) ∧ (∀ n, MemLp (f * χ n) ∞ μ) ∧
      (∀ n x, ‖χ n x‖ ≤ 1) ∧ (∀ n, star (χ n) = χ n) ∧
      ∀ x, Tendsto (fun n => χ n x) atTop (𝓝 1) := by
  set f' := hf.mk f
  have hf' : StronglyMeasurable f' := hf.stronglyMeasurable_mk
  have hS : ∀ n : ℕ, MeasurableSet {x | ‖f' x‖ ≤ n} := fun n =>
    measurableSet_le hf'.measurable.norm measurable_const
  set χ : ℕ → α → ℂ := fun n => Set.indicator {x | ‖f' x‖ ≤ n} 1 with hχ
  have hχm : ∀ n, StronglyMeasurable (χ n) := fun n =>
    stronglyMeasurable_const.indicator (hS n)
  have hχle : ∀ n x, ‖χ n x‖ ≤ 1 := fun n x =>
    (norm_indicator_le_norm_self _ _).trans (by simp)
  have hχ1 : ∀ (n : ℕ) x, ‖f' x‖ ≤ n → χ n x = 1 := fun n x h => by
    simp only [hχ]
    rw [Set.indicator_of_mem (by exact h), Pi.one_apply]
  have hχ0 : ∀ (n : ℕ) x, ¬‖f' x‖ ≤ n → χ n x = 0 := fun n x h => by
    simp only [hχ]
    rw [Set.indicator_of_notMem (by exact h)]
  refine ⟨χ, fun n => ?_, fun n => ?_, hχle, fun n => ?_, fun x => ?_⟩
  · exact memLp_top_of_bound (hχm n).aestronglyMeasurable 1 (.of_forall (hχle n))
  · refine memLp_top_of_bound (hf.mul (hχm n).aestronglyMeasurable) n ?_
    filter_upwards [hf.ae_eq_mk] with x hx
    rw [Pi.mul_apply, norm_mul, hx]
    by_cases h : ‖f' x‖ ≤ n
    · rw [hχ1 n x h, norm_one, mul_one]
      exact h
    · rw [hχ0 n x h, norm_zero, mul_zero]
      exact Nat.cast_nonneg n
  · ext x
    by_cases h : ‖f' x‖ ≤ n
    · rw [Pi.star_apply, hχ1 n x h, star_one]
    · rw [Pi.star_apply, hχ0 n x h, star_zero]
  · obtain ⟨N, hN⟩ := exists_nat_ge ‖f' x‖
    refine tendsto_const_nhds.congr' (eventually_atTop.2 ⟨N, fun n hn => ?_⟩)
    exact (hχ1 n x (hN.trans (Nat.cast_le.2 hn))).symm

/-- `T_f` is densely defined (Reed–Simon I, p. 259). -/
theorem dense_mulPMap_domain {f : α → ℂ} (hf : AEStronglyMeasurable f μ) :
    Dense ((mulPMap μ f).domain : Set (Lp ℂ 2 μ)) := by
  obtain ⟨χ, hχ, hfχ, hχ1, -, hlim⟩ := exists_truncation hf
  intro φ
  have ht := tendsto_mulL_apply hχ (memLp_top_const (1 : ℂ)) (C := 1)
    (fun n => .of_forall (hχ1 n)) (.of_forall hlim) φ
  rw [mulL_const, one_smul, one_apply_eq_self] at ht
  exact mem_closure_of_tendsto ht (.of_forall fun n => mulL_mem_mulPMap_domain (hχ n) (hfχ n) φ)

/-- `T_f` only depends on the almost-everywhere class of `f`. -/
theorem mulPMap_congr_ae {f g : α → ℂ} (h : f =ᵐ[μ] g) : mulPMap μ f = mulPMap μ g := by
  have hfg : ∀ φ : Lp ℂ 2 μ, (fun x => f x * φ x) =ᵐ[μ] fun x => g x * φ x := fun φ => by
    filter_upwards [h] with x hx
    rw [hx]
  refine LinearPMap.ext ?_ fun φ hφ hφ' => ?_
  · ext φ
    exact ⟨fun hφ => (mem_mulPMap_domain.1 hφ).ae_eq (hfg φ),
      fun hφ => (mem_mulPMap_domain.1 hφ).ae_eq (hfg φ).symm⟩
  · exact Lp.ext ((coeFn_mulPMap _).trans ((hfg φ).trans (coeFn_mulPMap ⟨φ, hφ'⟩).symm))

/-! ### The adjoint -/

/-- `T_{f̄}` is a formal adjoint of `T_f`: `⟪T_f φ, ψ⟫ = ⟪φ, T_{f̄} ψ⟫` for `φ ∈ D(T_f)` and
`ψ ∈ D(T_{f̄})`. -/
theorem isFormalAdjoint_mulPMap (f : α → ℂ) :
    (mulPMap μ f).IsFormalAdjoint (mulPMap μ (star f)) := by
  intro φ ψ
  rw [L2.inner_def, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_mulPMap φ, coeFn_mulPMap ψ] with x h1 h2
  rw [h1, h2, Pi.star_apply, RCLike.inner_apply, RCLike.inner_apply, map_mul, Complex.star_def]
  ring

/-- The domain of `T_f†` is contained in `D(T_{f̄})`, by truncation (Reed–Simon I,
pp. 259–260).  For `ψ ∈ D(T_f†)` and a truncation `χₙ`, testing against `φ = χₙ ζ` gives
`χₙ T_f† ψ = f̄ χₙ ψ`; letting `n → ∞` pointwise gives `T_f† ψ = f̄ ψ`.  (Reed–Simon instead bound
`‖χₙ f ψ‖` by `‖T_f† ψ‖` and use monotone convergence.) -/
theorem adjoint_mulPMap_domain_le {f : α → ℂ} (hf : AEStronglyMeasurable f μ) :
    (mulPMap μ f)†.domain ≤ (mulPMap μ (star f)).domain := by
  intro ψ hψ
  obtain ⟨χ, hχ, hfχ, -, hχs, hlim⟩ := exists_truncation hf
  set η := (mulPMap μ f)† ⟨ψ, hψ⟩ with hη
  have hform := LinearPMap.adjoint_isFormalAdjoint (dense_mulPMap_domain hf)
  have key : ∀ n, mulL (χ n) (hχ n) η = mulL (star (f * χ n)) (hfχ n).star ψ := by
    intro n
    have hadj : ContinuousLinearMap.adjoint (mulL (χ n) (hχ n)) = mulL (χ n) (hχ n) := by
      rw [adjoint_mulL]
      exact mulL_congr_ae _ _ (.of_forall fun x => congrFun (hχs n) x)
    refine ext_inner_right ℂ fun ζ => ?_
    rw [← ContinuousLinearMap.adjoint_inner_right, hadj, ← adjoint_mulL (hfχ n),
      ContinuousLinearMap.adjoint_inner_left, ← mulPMap_mulL (hχ n) (hfχ n) ζ, hη]
    exact hform ⟨ψ, hψ⟩ ⟨mulL (χ n) (hχ n) ζ, mulL_mem_mulPMap_domain (hχ n) (hfχ n) ζ⟩
  have h : ∀ n, ∀ᵐ x ∂μ, χ n x * η x = star (f * χ n) x * ψ x := fun n => by
    filter_upwards [coeFn_mulL (hχ n) η, coeFn_mulL (hfχ n).star ψ] with x h1 h2
    rw [← h1, ← h2, key n]
  refine mem_mulPMap_domain_of_ae_eq (η := η) ?_
  filter_upwards [ae_all_iff.2 h] with x hx
  have h1 : Tendsto (fun n => χ n x * η x) atTop (𝓝 (η x)) := by
    simpa using (hlim x).mul_const (η x)
  have h2 : Tendsto (fun n => χ n x * η x) atTop (𝓝 (star f x * ψ x)) := by
    have hrw : ∀ n, star (f * χ n) x * ψ x = star f x * ψ x * χ n x := fun n => by
      have hs := congrFun (hχs n) x
      rw [Pi.star_apply] at hs
      rw [Pi.star_apply, Pi.mul_apply, star_mul', hs, Pi.star_apply]
      ring
    refine Tendsto.congr (fun n => ((hx n).trans (hrw n)).symm) ?_
    simpa using (hlim x).const_mul (star f x * ψ x)
  exact tendsto_nhds_unique h1 h2

/-- **The adjoint of a multiplication operator**: `T_f† = T_{f̄}` (for real `f`, this is the
content of the proof of Reed–Simon I, §VIII.3, Proposition 1, pp. 259–260). -/
theorem adjoint_mulPMap {f : α → ℂ} (hf : AEStronglyMeasurable f μ) :
    (mulPMap μ f)† = mulPMap μ (star f) := by
  have hle := (isFormalAdjoint_mulPMap (μ := μ) f).le_adjoint (dense_mulPMap_domain hf)
  exact (LinearPMap.eq_of_le_of_domain_eq hle
    (le_antisymm hle.1 (adjoint_mulPMap_domain_le hf))).symm

/-- **Reed–Simon I, §VIII.3, Proposition 1** (p. 259): multiplication by an almost everywhere
real-valued measurable function `f` is self-adjoint on `D(T_f) = {φ | f φ ∈ L²}`. -/
theorem isSelfAdjoint_mulPMap {f : α → ℂ} (hf : AEStronglyMeasurable f μ)
    (hreal : ∀ᵐ x ∂μ, conj (f x) = f x) : IsSelfAdjoint (mulPMap μ f) := by
  rw [LinearPMap.isSelfAdjoint_def, adjoint_mulPMap hf]
  exact mulPMap_congr_ae hreal

/-- Multiplication by a measurable real-valued function `r` is self-adjoint on its maximal
domain (Reed–Simon I, §VIII.3, Proposition 1, p. 259). -/
theorem isSelfAdjoint_mulPMap_ofReal {r : α → ℝ} (hr : AEStronglyMeasurable r μ) :
    IsSelfAdjoint (mulPMap μ fun x => (r x : ℂ)) :=
  isSelfAdjoint_mulPMap (Complex.continuous_ofReal.comp_aestronglyMeasurable hr)
    (.of_forall fun x => Complex.conj_ofReal (r x))

/-! ### Dominated convergence on the domain -/

/-- Domination of multipliers gives inclusion of domains: if `‖g‖ ≤ ‖G‖` almost everywhere,
then `D(T_G) ⊆ D(T_g)`. -/
theorem mulPMap_domain_mono {g G : α → ℂ} (hg : AEStronglyMeasurable g μ)
    (h : ∀ᵐ x ∂μ, ‖g x‖ ≤ ‖G x‖) : (mulPMap μ G).domain ≤ (mulPMap μ g).domain := by
  intro φ hφ
  refine (mem_mulPMap_domain.1 hφ).of_le (hg.mul (Lp.aestronglyMeasurable φ)) ?_
  filter_upwards [h] with x hx
  rw [norm_mul, norm_mul]
  exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)

/-- **Dominated convergence on the domain**: if `Fₙ → f` almost everywhere and
`‖Fₙ x‖ ≤ ‖G x‖` almost everywhere, then `T_{Fₙ} φ → T_f φ` in `L²` for every `φ ∈ D(T_G)`
(used for Reed–Simon I, Theorem VIII.5 (c), p. 262). -/
theorem tendsto_mulPMap_apply_of_dominated {F : ℕ → α → ℂ} {f G : α → ℂ} {φ : Lp ℂ 2 μ}
    (hFφ : ∀ n, φ ∈ (mulPMap μ (F n)).domain) (hfφ : φ ∈ (mulPMap μ f).domain)
    (hGφ : φ ∈ (mulPMap μ G).domain) (h_bound : ∀ n, ∀ᵐ x ∂μ, ‖F n x‖ ≤ ‖G x‖)
    (h_lim : ∀ᵐ x ∂μ, Tendsto (fun n => F n x) atTop (𝓝 (f x))) :
    Tendsto (fun n => mulPMap μ (F n) ⟨φ, hFφ n⟩) atTop (𝓝 (mulPMap μ f ⟨φ, hfφ⟩)) := by
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
  have key := tendsto_eLpNorm_two_sub_of_dominated (F := fun n x => F n x * φ x)
    (f := fun x => f x * φ x) (B := fun x => ‖G x * φ x‖)
    (fun n => (mem_mulPMap_domain.1 (hFφ n)).aestronglyMeasurable)
    (mem_mulPMap_domain.1 hGφ).norm (fun n => ?_) ?_
  · refine key.congr' (.of_forall fun n => eLpNorm_congr_ae ?_)
    filter_upwards [coeFn_mulPMap ⟨φ, hFφ n⟩, coeFn_mulPMap ⟨φ, hfφ⟩] with x h1 h2
    simp [h1, h2]
  · filter_upwards [h_bound n] with x hx
    rw [norm_mul, norm_mul]
    exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)
  · filter_upwards [h_lim] with x hx
    exact hx.mul_const _

/-- **Dominated convergence for bounded approximants** (Reed–Simon I, Theorem VIII.5 (c),
p. 262): if `fₙ` are essentially bounded, `fₙ → f` almost everywhere and `‖fₙ x‖ ≤ ‖f x‖`
almost everywhere, then `M_{fₙ} φ → T_f φ` in `L²` for every `φ ∈ D(T_f)`. -/
theorem tendsto_mulL_apply_mulPMap {F : ℕ → α → ℂ} {f : α → ℂ} (hF : ∀ n, MemLp (F n) ∞ μ)
    (h_bound : ∀ n, ∀ᵐ x ∂μ, ‖F n x‖ ≤ ‖f x‖)
    (h_lim : ∀ᵐ x ∂μ, Tendsto (fun n => F n x) atTop (𝓝 (f x))) (φ : (mulPMap μ f).domain) :
    Tendsto (fun n => mulL (F n) (hF n) φ) atTop (𝓝 (mulPMap μ f φ)) := by
  have hFφ : ∀ n, (φ : Lp ℂ 2 μ) ∈ (mulPMap μ (F n)).domain := fun n =>
    mem_mulPMap_domain.2 (memLp_two_mul (hF n) φ)
  have h := tendsto_mulPMap_apply_of_dominated (F := F) (f := f) (G := f) hFφ φ.2 φ.2
    h_bound h_lim
  have e : ∀ n, mulPMap μ (F n) ⟨φ, hFφ n⟩ = mulL (F n) (hF n) φ := fun n =>
    mulPMap_apply_eq_mulL (hF n) _
  have e2 : (⟨(φ : Lp ℂ 2 μ), φ.2⟩ : (mulPMap μ f).domain) = φ := rfl
  rw [e2] at h
  exact h.congr e

end SpectralTheorem
