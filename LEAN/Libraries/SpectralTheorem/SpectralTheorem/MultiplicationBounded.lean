import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Bounded multiplication operators on `L²`

Let `μ` be a measure on a measurable space `α` (not assumed finite or σ-finite) and let
`g : α → ℂ` be essentially bounded, i.e. `MemLp g ∞ μ`.  Multiplication by `g` is a bounded
operator `M_g` on the Hilbert space `L²(α, μ) = Lp ℂ 2 μ`.  This file sets up these operators as
infrastructure for the bounded and unbounded spectral theorem, following Reed–Simon,
*Methods of Modern Mathematical Physics I* (1972): the operators of Theorem VII.3 and its
corollary (multiplication operator form, p. 227), and the bounded functions of an operator in
Theorem VII.2 (functional calculus form, p. 225).

## Main definitions

* `SpectralTheorem.mulL g hg : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ`: multiplication by `g`, for
  `hg : MemLp g ∞ μ`.

## Main results

* `SpectralTheorem.coeFn_mulL`: `mulL g hg φ =ᵐ[μ] fun x => g x * φ x`.
* `SpectralTheorem.norm_mulL_le`: `‖mulL g hg‖ ≤ C` when `‖g x‖ ≤ C` almost everywhere;
  `enorm_mulL_le`: `‖mulL g hg‖ ≤ ‖g‖∞`.
* `SpectralTheorem.mulL_congr_ae`: `mulL g hg` only depends on the a.e. class of `g`.
* `SpectralTheorem.mulL_mul`, `mulL_one`, `mulL_zero`, `mulL_add`, `mulL_smul`, `mulL_neg`,
  `mulL_sub`, `mulL_const`: `g ↦ M_g` is an algebra homomorphism; `mulL_comp_comm`: the `M_g`
  commute.
* `SpectralTheorem.adjoint_mulL`, `star_mulL`: `(M_g)† = M_{star g}`; hence `M_g` is normal
  (`isStarNormal_mulL`) and self-adjoint when `g` is real-valued (`isSelfAdjoint_mulL`,
  `isSelfAdjoint_mulL_ofReal`).
* `SpectralTheorem.tendsto_eLpNorm_two_sub_of_dominated`: dominated convergence in `L²`.
* `SpectralTheorem.tendsto_mulL_apply`: if `gₙ → g` a.e. with `‖gₙ x‖ ≤ C` for all `n`, then
  `M_{gₙ} φ → M_g φ` in `L²` for every `φ` (strong convergence, by dominated convergence).
-/

open MeasureTheory Filter Topology ComplexConjugate
open scoped ENNReal NNReal InnerProductSpace

noncomputable section

namespace SpectralTheorem

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- An essentially bounded function is bounded almost everywhere by its essential supremum
`C = ‖g‖∞`, a finite nonnegative real number. -/
theorem exists_ae_norm_le_of_memLp_top {g : α → ℂ} (hg : MemLp g ∞ μ) :
    ∃ C : ℝ≥0, eLpNorm g ∞ μ = C ∧ ∀ᵐ x ∂μ, ‖g x‖ ≤ C := by
  obtain ⟨C, hC⟩ : ∃ C : ℝ≥0, (C : ℝ≥0∞) = eLpNorm g ∞ μ :=
    ⟨_, ENNReal.coe_toNNReal hg.eLpNorm_lt_top.ne⟩
  refine ⟨C, hC.symm, ?_⟩
  have h := enorm_ae_le_eLpNormEssSup g μ
  rw [← eLpNorm_exponent_top hg.aestronglyMeasurable, ← hC] at h
  filter_upwards [h] with x hx
  rw [enorm_eq_nnnorm, ENNReal.coe_le_coe] at hx
  exact_mod_cast hx

/-- The product of an essentially bounded function and an `L²` function is in `L²`. -/
theorem memLp_two_mul {g : α → ℂ} (hg : MemLp g ∞ μ) (φ : Lp ℂ 2 μ) :
    MemLp (fun x => g x * φ x) 2 μ :=
  hg.fun_mul (Lp.memLp φ)

/-- Multiplication by an essentially bounded function `g`, as a linear map on `L²(μ)`. -/
def mulₗ (g : α → ℂ) (hg : MemLp g ∞ μ) : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ where
  toFun φ := (memLp_two_mul hg φ).toLp _
  map_add' φ ψ := by
    rw [← MemLp.toLp_add]
    apply MemLp.toLp_congr
    filter_upwards [Lp.coeFn_add φ ψ] with x hx
    rw [Pi.add_apply, hx, Pi.add_apply, mul_add]
  map_smul' c φ := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    apply MemLp.toLp_congr
    filter_upwards [Lp.coeFn_smul c φ] with x hx
    simp [hx, mul_left_comm]

/-- `‖g φ‖₂ ≤ C ‖φ‖₂` when `‖g x‖ ≤ C` almost everywhere. -/
theorem norm_mulₗ_apply_le {g : α → ℂ} (hg : MemLp g ∞ μ) {C : ℝ} (hC : ∀ᵐ x ∂μ, ‖g x‖ ≤ C)
    (φ : Lp ℂ 2 μ) : ‖mulₗ g hg φ‖ ≤ C * ‖φ‖ := by
  refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
  filter_upwards [MemLp.coeFn_toLp (memLp_two_mul hg φ), hC] with x hx hCx
  change ‖(memLp_two_mul hg φ).toLp _ x‖ ≤ _
  rw [hx, norm_mul]
  exact mul_le_mul_of_nonneg_right hCx (norm_nonneg _)

/-- The bounded multiplication operator `M_g : L²(μ) → L²(μ)`, `φ ↦ g · φ`, for an essentially
bounded function `g` (as in Reed–Simon I, Theorem VII.3 and its corollary, p. 227). -/
def mulL (g : α → ℂ) (hg : MemLp g ∞ μ) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  (mulₗ g hg).mkContinuousOfExistsBound <| by
    obtain ⟨C, -, hC⟩ := exists_ae_norm_le_of_memLp_top hg
    exact ⟨C, norm_mulₗ_apply_le hg hC⟩

/-- `M_g φ` is represented by the pointwise product `g · φ`. -/
theorem coeFn_mulL {g : α → ℂ} (hg : MemLp g ∞ μ) (φ : Lp ℂ 2 μ) :
    mulL g hg φ =ᵐ[μ] fun x => g x * φ x :=
  MemLp.coeFn_toLp (memLp_two_mul hg φ)

/-- `M_g φ` is the `L²` class of the pointwise product `g · φ`. -/
theorem mulL_apply {g : α → ℂ} (hg : MemLp g ∞ μ) (φ : Lp ℂ 2 μ) :
    mulL g hg φ = (memLp_two_mul hg φ).toLp _ :=
  rfl

/-- `‖M_g φ‖ ≤ C ‖φ‖` when `‖g x‖ ≤ C` almost everywhere. -/
theorem norm_mulL_apply_le {g : α → ℂ} (hg : MemLp g ∞ μ) {C : ℝ} (hC : ∀ᵐ x ∂μ, ‖g x‖ ≤ C)
    (φ : Lp ℂ 2 μ) : ‖mulL g hg φ‖ ≤ C * ‖φ‖ :=
  norm_mulₗ_apply_le hg hC φ

/-- `‖M_g‖ ≤ C` when `0 ≤ C` and `‖g x‖ ≤ C` almost everywhere. -/
theorem norm_mulL_le {g : α → ℂ} (hg : MemLp g ∞ μ) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ᵐ x ∂μ, ‖g x‖ ≤ C) : ‖mulL g hg‖ ≤ C :=
  ContinuousLinearMap.opNorm_le_bound _ hC0 (norm_mulL_apply_le hg hC)

/-- `‖M_g‖ ≤ ‖g‖∞`, stated with extended norms. -/
theorem enorm_mulL_le {g : α → ℂ} (hg : MemLp g ∞ μ) : ‖mulL g hg‖ₑ ≤ eLpNorm g ∞ μ := by
  obtain ⟨C, hCeq, hC⟩ := exists_ae_norm_le_of_memLp_top hg
  rw [hCeq, enorm_eq_nnnorm, ENNReal.coe_le_coe, ← NNReal.coe_le_coe, coe_nnnorm]
  exact norm_mulL_le hg C.2 hC

/-- `M_g` only depends on the almost-everywhere class of `g`. -/
theorem mulL_congr_ae {g g' : α → ℂ} (hg : MemLp g ∞ μ) (hg' : MemLp g' ∞ μ)
    (h : g =ᵐ[μ] g') : mulL g hg = mulL g' hg' := by
  ext1 φ
  refine Lp.ext ?_
  filter_upwards [coeFn_mulL hg φ, coeFn_mulL hg' φ, h] with x h1 h2 h3
  rw [h1, h2, h3]

/-- `M_{gh} = M_g M_h`. -/
theorem mulL_mul {g h : α → ℂ} (hg : MemLp g ∞ μ) (hh : MemLp h ∞ μ) :
    mulL (g * h) (hg.mul hh) = mulL g hg ∘L mulL h hh := by
  ext1 φ
  refine Lp.ext ?_
  filter_upwards [coeFn_mulL (hg.mul hh) φ, coeFn_mulL hg (mulL h hh φ), coeFn_mulL hh φ]
    with x h1 h2 h3
  rw [ContinuousLinearMap.comp_apply, h1, h2, h3, Pi.mul_apply, mul_assoc]

/-- `M_1 = 1`. -/
theorem mulL_one (h1 : MemLp (1 : α → ℂ) ∞ μ) : mulL 1 h1 = 1 := by
  ext1 φ
  refine Lp.ext ?_
  filter_upwards [coeFn_mulL h1 φ] with x hx
  rw [hx, Pi.one_apply, one_mul, one_apply_eq_self]

/-- `M_0 = 0`. -/
theorem mulL_zero (h0 : MemLp (0 : α → ℂ) ∞ μ) : mulL 0 h0 = 0 := by
  ext1 φ
  refine Lp.ext ?_
  filter_upwards [coeFn_mulL h0 φ, Lp.coeFn_zero ℂ 2 μ] with x h1 h2
  rw [h1, zero_apply, h2, Pi.zero_apply, zero_mul]

/-- `M_{g+h} = M_g + M_h`. -/
theorem mulL_add {g h : α → ℂ} (hg : MemLp g ∞ μ) (hh : MemLp h ∞ μ) :
    mulL (g + h) (hg.add hh) = mulL g hg + mulL h hh := by
  ext1 φ
  refine Lp.ext ?_
  filter_upwards [coeFn_mulL (hg.add hh) φ, Lp.coeFn_add (mulL g hg φ) (mulL h hh φ),
    coeFn_mulL hg φ, coeFn_mulL hh φ] with x h1 h2 h3 h4
  rw [add_apply, h2, h1, Pi.add_apply, Pi.add_apply, h3, h4, add_mul]

/-- `M_{c g} = c M_g`. -/
theorem mulL_smul (c : ℂ) {g : α → ℂ} (hg : MemLp g ∞ μ) :
    mulL (c • g) (hg.const_smul c) = c • mulL g hg := by
  ext1 φ
  refine Lp.ext ?_
  filter_upwards [coeFn_mulL (hg.const_smul c) φ, Lp.coeFn_smul c (mulL g hg φ),
    coeFn_mulL hg φ] with x h1 h2 h3
  rw [smul_apply, h2, h1, Pi.smul_apply, Pi.smul_apply, h3, smul_eq_mul,
    smul_eq_mul, mul_assoc]

/-- Multiplication by a constant `c` is `c • 1`. -/
theorem mulL_const (c : ℂ) (hc : MemLp (fun _ : α => c) ∞ μ) : mulL (fun _ => c) hc = c • 1 := by
  ext1 φ
  refine Lp.ext ?_
  filter_upwards [coeFn_mulL hc φ, Lp.coeFn_smul c φ] with x h1 h2
  rw [h1, smul_apply, one_apply_eq_self, h2, Pi.smul_apply,
    smul_eq_mul]

/-- `M_{-g} = -M_g`. -/
theorem mulL_neg {g : α → ℂ} (hg : MemLp g ∞ μ) : mulL (-g) hg.neg = -mulL g hg := by
  rw [← neg_one_smul ℂ (mulL g hg), ← mulL_smul]
  exact mulL_congr_ae _ _ (.of_forall fun x => by simp)

/-- `M_{g-h} = M_g - M_h`. -/
theorem mulL_sub {g h : α → ℂ} (hg : MemLp g ∞ μ) (hh : MemLp h ∞ μ) :
    mulL (g - h) (hg.sub hh) = mulL g hg - mulL h hh := by
  rw [sub_eq_add_neg (mulL g hg), ← mulL_neg, ← mulL_add]
  exact mulL_congr_ae _ _ (.of_forall fun x => by simp [sub_eq_add_neg])

/-- Multiplication operators commute: `M_g M_h = M_h M_g`. -/
theorem mulL_comp_comm {g h : α → ℂ} (hg : MemLp g ∞ μ) (hh : MemLp h ∞ μ) :
    mulL g hg ∘L mulL h hh = mulL h hh ∘L mulL g hg := by
  rw [← mulL_mul, ← mulL_mul]
  exact mulL_congr_ae _ _ (.of_forall fun x => mul_comm _ _)

/-- The adjoint of `M_g` is `M_{ḡ}`. -/
theorem adjoint_mulL {g : α → ℂ} (hg : MemLp g ∞ μ) :
    ContinuousLinearMap.adjoint (mulL g hg) = mulL (star g) hg.star := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro φ ψ
  rw [L2.inner_def, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_mulL hg.star φ, coeFn_mulL hg ψ] with x h1 h2
  rw [h1, h2, Pi.star_apply, RCLike.inner_apply, RCLike.inner_apply, map_mul, Complex.star_def,
    Complex.conj_conj]
  ring

/-- `star M_g = M_{ḡ}`, where `star` is the adjoint. -/
theorem star_mulL {g : α → ℂ} (hg : MemLp g ∞ μ) : star (mulL g hg) = mulL (star g) hg.star := by
  rw [ContinuousLinearMap.star_eq_adjoint, adjoint_mulL]

/-- `M_g` is a normal operator. -/
theorem isStarNormal_mulL {g : α → ℂ} (hg : MemLp g ∞ μ) : IsStarNormal (mulL g hg) := by
  refine ⟨?_⟩
  rw [ContinuousLinearMap.star_eq_adjoint, adjoint_mulL, Commute, SemiconjBy,
    ContinuousLinearMap.mul_def, ContinuousLinearMap.mul_def]
  exact mulL_comp_comm _ _

/-- `M_g` is self-adjoint when `g` is real-valued almost everywhere. -/
theorem isSelfAdjoint_mulL {g : α → ℂ} (hg : MemLp g ∞ μ)
    (hreal : ∀ᵐ x ∂μ, conj (g x) = g x) : IsSelfAdjoint (mulL g hg) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff', adjoint_mulL]
  exact mulL_congr_ae _ _ hreal

/-- Multiplication by an essentially bounded real function is self-adjoint. -/
theorem isSelfAdjoint_mulL_ofReal {r : α → ℝ} (hr : MemLp (fun x => (r x : ℂ)) ∞ μ) :
    IsSelfAdjoint (mulL _ hr) :=
  isSelfAdjoint_mulL hr (.of_forall fun x => Complex.conj_ofReal (r x))

/-! ### Strong convergence under bounded pointwise convergence -/

/-- **Dominated convergence in `L²`**: if `F n → f` almost everywhere and `‖F n x‖ ≤ B x`
almost everywhere for a square-integrable `B`, then `‖F n - f‖₂ → 0`. -/
theorem tendsto_eLpNorm_two_sub_of_dominated {F : ℕ → α → ℂ} {f : α → ℂ} {B : α → ℝ}
    (hF : ∀ n, AEStronglyMeasurable (F n) μ) (hB : MemLp B 2 μ)
    (h_bound : ∀ n, ∀ᵐ x ∂μ, ‖F n x‖ ≤ B x)
    (h_lim : ∀ᵐ x ∂μ, Tendsto (fun n => F n x) atTop (𝓝 (f x))) :
    Tendsto (fun n => eLpNorm (F n - f) 2 μ) atTop (𝓝 0) := by
  have hf : AEStronglyMeasurable f μ := aestronglyMeasurable_of_tendsto_ae atTop hF h_lim
  have hfB : ∀ᵐ x ∂μ, ‖f x‖ ≤ B x := by
    filter_upwards [ae_all_iff.2 h_bound, h_lim] with x hb hx
    exact le_of_tendsto' ((continuous_norm.tendsto _).comp hx) hb
  have h2 : (2 : ℝ≥0∞) ≠ 0 := two_ne_zero
  have h2t : (2 : ℝ≥0∞) ≠ ∞ := ENNReal.ofNat_ne_top
  have hpow : ∀ r : ℝ, 0 < r → Tendsto (fun t : ℝ≥0∞ => t ^ r) (𝓝 0) (𝓝 0) := fun r hr => by
    have := (ENNReal.continuous_rpow_const (y := r)).tendsto 0
    rwa [ENNReal.zero_rpow_of_pos hr] at this
  simp_rw [fun n => eLpNorm_eq_lintegral_rpow_enorm_toReal h2 h2t ((hF n).sub hf),
    ENNReal.toReal_ofNat]
  refine (hpow _ (by norm_num)).comp ?_
  have hB2 : ∫⁻ x, ‖B x‖ₑ ^ (2 : ℝ) ∂μ < ∞ := by
    simpa using lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top h2 h2t hB.eLpNorm_lt_top
  have hfin : ∫⁻ x, (2 * ‖B x‖ₑ) ^ (2 : ℝ) ∂μ ≠ ∞ := by
    simp_rw [ENNReal.mul_rpow_of_nonneg _ _ zero_le_two]
    rw [lintegral_const_mul' _ _ (by finiteness)]
    exact ENNReal.mul_ne_top (by finiteness) hB2.ne
  have := tendsto_lintegral_of_dominated_convergence' (f := fun _ => 0)
    (F := fun n x => ‖(F n - f) x‖ₑ ^ (2 : ℝ))
    (fun x => (2 * ‖B x‖ₑ) ^ (2 : ℝ))
    (fun n => ((hF n).sub hf).enorm.pow_const _) (fun n => ?_) hfin ?_
  · simpa using this
  · filter_upwards [h_bound n, hfB] with x h1 h2
    refine ENNReal.rpow_le_rpow ?_ zero_le_two
    rw [two_mul, Pi.sub_apply]
    refine enorm_sub_le.trans (add_le_add ?_ ?_)
    · exact enorm_le_iff_norm_le.2 (h1.trans (Real.le_norm_self _))
    · exact enorm_le_iff_norm_le.2 (h2.trans (Real.le_norm_self _))
  · filter_upwards [h_lim] with x hx
    have h0 : Tendsto (fun n => ‖F n x - f x‖ₑ) atTop (𝓝 0) := by
      have := (continuous_enorm.tendsto (0 : ℂ)).comp (tendsto_sub_nhds_zero_iff.2 hx)
      rwa [enorm_zero] at this
    exact (hpow _ two_pos).comp h0

/-- **Strong continuity** of `g ↦ M_g` under bounded pointwise convergence (Reed–Simon I,
Theorem VII.2 (d), p. 225): if `gₙ → g` almost everywhere and `‖gₙ x‖ ≤ C` almost everywhere
for all `n`, then `M_{gₙ} φ → M_g φ` in `L²` for every `φ`. -/
theorem tendsto_mulL_apply {g : ℕ → α → ℂ} {g₀ : α → ℂ} (hg : ∀ n, MemLp (g n) ∞ μ)
    (hg₀ : MemLp g₀ ∞ μ) {C : ℝ} (hC : ∀ n, ∀ᵐ x ∂μ, ‖g n x‖ ≤ C)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => g n x) atTop (𝓝 (g₀ x))) (φ : Lp ℂ 2 μ) :
    Tendsto (fun n => mulL (g n) (hg n) φ) atTop (𝓝 (mulL g₀ hg₀ φ)) := by
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
  have key := tendsto_eLpNorm_two_sub_of_dominated (F := fun n x => g n x * φ x)
    (f := fun x => g₀ x * φ x) (B := fun x => C * ‖φ x‖)
    (fun n => (hg n).aestronglyMeasurable.mul (Lp.aestronglyMeasurable φ))
    ((Lp.memLp φ).norm.const_mul C) (fun n => ?_) ?_
  · refine key.congr' (.of_forall fun n => eLpNorm_congr_ae ?_)
    filter_upwards [coeFn_mulL (hg n) φ, coeFn_mulL hg₀ φ] with x h1 h2
    simp [h1, h2]
  · filter_upwards [hC n] with x hx
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)
  · filter_upwards [hlim] with x hx
    exact hx.mul_const _

end SpectralTheorem
