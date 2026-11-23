import SpectralTheorem.PVMUnbounded

/-!
# Unbounded normal operators and the integral of a function against a p.v.m.

**Rudin, *Functional Analysis*, Chapter 13 (Definition 13.31 and Theorem 13.33).**  A densely
defined operator `N` on a Hilbert space is *normal* when `D(N†) = D(N)` and `‖N ψ‖ = ‖N† ψ‖`
for `ψ ∈ D(N)`.  Reed–Simon I treat only the self-adjoint case; the normal case is what the
integral `∫ g dP` of a complex-valued Borel function against a projection-valued measure
produces (Reed–Simon I, pp. 263–264, restrict to real `g` for exactly this reason).

Here `P` is a projection-valued measure on a measurable space `X`, `μ_ψ = P.measure ψ`,
`g : X → ℂ` is measurable and `∫ g dP = P.integralPMap hg` is the operator of
`SpectralTheorem.PVMUnbounded`, with domain `D_g = {ψ | g ∈ L²(μ_ψ)}`.

Proofs.
* **A normal operator is closed.**  Let `ψₙ ∈ D(N)` with `ψₙ → ψ` and `N ψₙ → η`.  Then
  `‖N† (ψₙ - ψₘ)‖ = ‖N (ψₙ - ψₘ)‖`, so `N† ψₙ` is Cauchy, say `N† ψₙ → ζ`; as `N†` is closed
  (`LinearPMap.adjoint_isClosed`), `ψ ∈ D(N†) = D(N)`.  Finally `⟪N χ, η⟫ = lim ⟪N χ, N ψₙ⟫`
  cannot be used directly, but for `χ ∈ D(N)`, `⟪η, χ⟫ = lim ⟪N ψₙ, χ⟫ = lim ⟪ψₙ, N† χ⟫ =
  `⟪ψ, N† χ⟫ = ⟪N ψ, χ⟫`, and `D(N)` is dense, so `η = N ψ`.
* **`∫ g dP` is normal**: `(∫ g dP)† = ∫ ḡ dP` (`adjoint_integralPMap`), `D_ḡ = D_g`
  (`integralPMap_star_domain`), and `‖(∫ g dP) ψ‖² = ∫ |g|² dμ_ψ = ‖(∫ ḡ dP) ψ‖²`.
* **Products**: for bounded `f` and `ψ ∈ D_g`, `(∫ f dP) ((∫ g dP) ψ) = (∫ f g dP) ψ` whenever
  `f g` is again bounded, by passing to the limit in `(∫ f dP) (∫ gₙ dP) = ∫ f gₙ dP`.  With
  `f = ḡₙ` this gives `(∫ ḡₙ dP) ((∫ g dP) ψ) = (∫ |gₙ|² dP) ψ`, since `ḡₙ g = ḡₙ gₙ = |gₙ|²`.
  Letting `n → ∞`: the left-hand side tends to `(∫ ḡ dP) ((∫ g dP) ψ)` and the right-hand side
  to `(∫ |g|² dP) ψ` for `ψ ∈ D_{|g|²}`, which also gives `(∫ g dP) ψ ∈ D_ḡ` by Fatou's lemma.

## Main definitions and results

* `SpectralTheorem.IsNormalPMap N`: `N` is densely defined, `D(N†) = D(N)` and
  `‖N ψ‖ = ‖N† ψ‖` on `D(N)`.
* `IsSelfAdjoint.isNormalPMap`: a self-adjoint operator is normal.
* `SpectralTheorem.IsNormalPMap.isClosed`: a normal operator is closed.
* `ProjectionValuedMeasure.isNormalPMap_integralPMap`: `∫ g dP` is normal.
* `ProjectionValuedMeasure.integral_integralPMap_bounded`:
  `(∫ f dP) ((∫ g dP) ψ) = (∫ f g dP) ψ` for bounded `f` and bounded `f g`.
* `ProjectionValuedMeasure.integralPMap_normSq_mem_domain`,
  `ProjectionValuedMeasure.integralPMap_star_integralPMap`: the product formula
  `(∫ ḡ dP) ((∫ g dP) ψ) = (∫ |g|² dP) ψ` on `D_{|g|²}`.
-/

noncomputable section

open scoped InnerProductSpace ENNReal Topology ComplexConjugate
open MeasureTheory Filter Set KatoRellich

namespace SpectralTheorem

universe u

variable {X : Type*} [MeasurableSpace X]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### Normal unbounded operators -/

/-- **A normal unbounded operator** (Rudin, *Functional Analysis*, Definition 13.31): `N` is
densely defined, the domain of `N†` is the domain of `N`, and `‖N ψ‖ = ‖N† ψ‖` there.  For a
closed densely defined `N` this is equivalent to `N† N = N N†`. -/
structure IsNormalPMap (N : H →ₗ.[ℂ] H) : Prop where
  /-- A normal operator is densely defined. -/
  dense_domain : Dense (N.domain : Set H)
  /-- The adjoint has the same domain. -/
  adjoint_domain : (LinearPMap.adjoint N).domain = N.domain
  /-- `‖N ψ‖ = ‖N† ψ‖` on the common domain. -/
  norm_apply : ∀ ψ : N.domain,
    ‖N ψ‖ = ‖LinearPMap.adjoint N ⟨(ψ : H), adjoint_domain.ge ψ.2⟩‖

namespace IsNormalPMap

variable {N : H →ₗ.[ℂ] H}

/-- A vector of `D(N)` lies in `D(N†)`. -/
theorem mem_adjoint_domain (hN : IsNormalPMap N) {ψ : H} (h : ψ ∈ N.domain) :
    ψ ∈ (LinearPMap.adjoint N).domain :=
  hN.adjoint_domain.ge h

/-- `‖N ψ‖ = ‖N† ψ‖`, with the membership proofs spelled out. -/
theorem norm_apply_mem (hN : IsNormalPMap N) (ψ : H) (h : ψ ∈ N.domain) :
    ‖N ⟨ψ, h⟩‖ = ‖LinearPMap.adjoint N ⟨ψ, hN.mem_adjoint_domain h⟩‖ :=
  hN.norm_apply ⟨ψ, h⟩

/-- **A normal operator is closed.**  If `ψₙ → ψ` and `N ψₙ → η` with `ψₙ ∈ D(N)`, then
`N† ψₙ` is Cauchy because `‖N† (ψₙ - ψₘ)‖ = ‖N (ψₙ - ψₘ)‖`; since `N†` is closed, `ψ` lies in
`D(N†) = D(N)`, and `⟪η, χ⟫ = lim ⟪N ψₙ, χ⟫ = lim ⟪ψₙ, N† χ⟫ = ⟪N ψ, χ⟫` for `χ ∈ D(N)`
forces `η = N ψ` by density. -/
theorem isClosed (hN : IsNormalPMap N) : N.IsClosed := by
  have hfa := LinearPMap.adjoint_isFormalAdjoint hN.dense_domain
  refine IsSeqClosed.isClosed fun p q hp hq => ?_
  choose y hy using fun n => (LinearPMap.mem_graph_iff N).1 (hp n)
  have hy1 : Tendsto (fun n => ((y n : H))) atTop (𝓝 q.1) := by
    exact ((continuous_fst.tendsto q).comp hq).congr fun n => (hy n).1.symm
  have hy2 : Tendsto (fun n => N (y n)) atTop (𝓝 q.2) := by
    exact ((continuous_snd.tendsto q).comp hq).congr fun n => (hy n).2.symm
  set z : ℕ → H := fun n => LinearPMap.adjoint N ⟨(y n : H), hN.mem_adjoint_domain (y n).2⟩
    with hz_def
  have hdiff : ∀ n m : ℕ, dist (z n) (z m) = dist (N (y n)) (N (y m)) := fun n m => by
    have e1 : z n - z m = LinearPMap.adjoint N
        ⟨((y n - y m : N.domain) : H), hN.mem_adjoint_domain (y n - y m).2⟩ := by
      rw [hz_def, ← LinearPMap.map_sub]
      rfl
    have e2 : N (y n) - N (y m) = N (y n - y m) := (LinearPMap.map_sub N _ _).symm
    rw [dist_eq_norm, dist_eq_norm, e1, e2, hN.norm_apply (y n - y m)]
  have hz : CauchySeq z := by
    rw [cauchySeq_iff_tendsto_dist_atTop_0]
    have h := hy2.cauchySeq
    rw [cauchySeq_iff_tendsto_dist_atTop_0] at h
    exact h.congr fun pr => (hdiff pr.1 pr.2).symm
  obtain ⟨ζ, hζ⟩ := cauchySeq_tendsto_of_complete hz
  have hgr : (q.1, ζ) ∈ ((LinearPMap.adjoint N).graph : Set (H × H)) := by
    refine (LinearPMap.adjoint_isClosed hN.dense_domain).mem_of_tendsto (hy1.prodMk_nhds hζ)
      (Eventually.of_forall fun n => ?_)
    exact LinearPMap.mem_graph _ ⟨(y n : H), hN.mem_adjoint_domain (y n).2⟩
  obtain ⟨v, hv⟩ := (LinearPMap.mem_graph_iff _).1 hgr
  have hq1 : q.1 ∈ N.domain := hN.adjoint_domain.le (hv.1 ▸ v.2)
  have hval : q.2 = N ⟨q.1, hq1⟩ := by
    refine hN.dense_domain.eq_of_inner_left ℂ fun χ hχ => ?_
    have hχ' : χ ∈ (LinearPMap.adjoint N).domain := hN.mem_adjoint_domain hχ
    have h1 : Tendsto (fun n => ⟪N (y n), χ⟫_ℂ) atTop (𝓝 ⟪q.2, χ⟫_ℂ) :=
      hy2.inner tendsto_const_nhds
    have h2 : Tendsto (fun n => ⟪((y n : H)), LinearPMap.adjoint N ⟨χ, hχ'⟩⟫_ℂ) atTop
        (𝓝 ⟪q.1, LinearPMap.adjoint N ⟨χ, hχ'⟩⟫_ℂ) := hy1.inner tendsto_const_nhds
    have h3 := tendsto_nhds_unique h1 (h2.congr fun n => (hfa.symm (y n) ⟨χ, hχ'⟩).symm)
    rw [h3]
    exact (hfa.symm ⟨q.1, hq1⟩ ⟨χ, hχ'⟩).symm
  exact (LinearPMap.mem_graph_iff N).2 ⟨⟨q.1, hq1⟩, rfl, hval.symm⟩

end IsNormalPMap

/-- **A self-adjoint operator is normal**: `N† = N`, so the domains agree and
`‖N ψ‖ = ‖N† ψ‖`. -/
theorem _root_.IsSelfAdjoint.isNormalPMap {N : H →ₗ.[ℂ] H} (hN : IsSelfAdjoint N) :
    IsNormalPMap N where
  dense_domain := hN.dense_domain
  adjoint_domain := congrArg LinearPMap.domain (LinearPMap.isSelfAdjoint_def.1 hN)
  norm_apply ψ := by
    refine (congrArg norm (LinearPMap.adjoint_apply_eq hN.dense_domain _ fun x => ?_)).symm
    exact (IsSymmetric.of_isSelfAdjoint hN).isFormalAdjoint ψ x

omit [CompleteSpace H] in
/-- Equal partially defined operators take equal values. -/
theorem linearPMap_apply_eq_of_eq {S T : H →ₗ.[ℂ] H} (h : S = T) {ψ : H} (hS : ψ ∈ S.domain)
    (hT : ψ ∈ T.domain) : S ⟨ψ, hS⟩ = T ⟨ψ, hT⟩ := by
  subst h
  rfl

/-- Equal squared extended norms give equal norms. -/
theorem norm_eq_of_enorm_sq_eq {E : Type*} [NormedAddCommGroup E] {a b : E}
    (h : ‖a‖ₑ ^ 2 = ‖b‖ₑ ^ 2) : ‖a‖ = ‖b‖ := by
  have h' : ENNReal.ofReal (‖a‖ ^ 2) = ENNReal.ofReal (‖b‖ ^ 2) := by
    rwa [ENNReal.ofReal_pow (norm_nonneg _), ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm,
      ofReal_norm]
  have h2 : ‖a‖ ^ 2 = ‖b‖ ^ 2 :=
    (ENNReal.ofReal_eq_ofReal_iff (by positivity) (by positivity)).1 h'
  exact (pow_left_inj₀ (norm_nonneg a) (norm_nonneg b) two_ne_zero).1 h2

/-- `|g|²`, as a complex-valued function, is measurable. -/
theorem measurable_normSq {g : X → ℂ} (hg : Measurable g) :
    Measurable fun x => ((‖g x‖ ^ 2 : ℝ) : ℂ) :=
  Complex.measurable_ofReal.comp (hg.norm.pow_const 2)

/-- `z̄ z = |z|²`. -/
theorem star_mul_self_complex (z : ℂ) : star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]

namespace ProjectionValuedMeasure

variable (P : ProjectionValuedMeasure X H)

/-! ### `∫ g dP` is normal -/

/-- **`∫ g dP` is a normal operator** (Rudin, *Functional Analysis*, Theorem 13.33): its domain
`D_g` is dense, its adjoint is `∫ ḡ dP` with the same domain `D_ḡ = D_g`, and
`‖(∫ g dP) ψ‖² = ∫ |g|² dμ_ψ = ‖(∫ ḡ dP) ψ‖²`. -/
theorem isNormalPMap_integralPMap {g : X → ℂ} (hg : Measurable g) :
    IsNormalPMap (P.integralPMap hg) where
  dense_domain := P.dense_integralPMap_domain hg
  adjoint_domain := by
    rw [P.adjoint_integralPMap hg]
    exact P.integralPMap_star_domain hg
  norm_apply ψ := by
    have hmem : (ψ : H) ∈ (P.integralPMap (measurable_star_of_measurable hg)).domain :=
      (P.integralPMap_star_domain hg).ge ψ.2
    refine (norm_eq_of_enorm_sq_eq ?_).trans
      (congrArg norm (linearPMap_apply_eq_of_eq (P.adjoint_integralPMap hg) _ hmem)).symm
    rw [P.enorm_integralPMap_apply_sq hg ψ,
      P.enorm_integralPMap_apply_sq (measurable_star_of_measurable hg) ⟨(ψ : H), hmem⟩]
    refine lintegral_congr fun x => ?_
    congr 1
    rw [← ofReal_norm, ← ofReal_norm]
    change ENNReal.ofReal ‖g x‖ = ENNReal.ofReal ‖star (g x)‖
    rw [norm_star]

/-- `∫ g dP` is closed. -/
theorem isClosed_integralPMap {g : X → ℂ} (hg : Measurable g) : (P.integralPMap hg).IsClosed :=
  (P.isNormalPMap_integralPMap hg).isClosed

/-! ### Products with a bounded function -/

/-- **`(∫ f dP) ((∫ g dP) ψ) = (∫ F dP) ψ`** for a bounded `f` such that `F = f g` is again
bounded: pass to the limit in `(∫ f dP) (∫ gₙ dP) = ∫ f gₙ dP`, where `f gₙ = 1_{‖g‖ ≤ n} F`
is bounded by a bound for `F`. -/
theorem integral_integralPMap_bounded {g : X → ℂ} (hg : Measurable g) (f F : boundedMeasurable X)
    (hF : ∀ x, (F : X → ℂ) x = (f : X → ℂ) x * g x) (ψ : (P.integralPMap hg).domain) :
    P.integral f (P.integralPMap hg ψ) = P.integral F ψ := by
  obtain ⟨C, hC0, hC⟩ := boundedMeasurable.exists_bound F
  have hb : ∀ n x, ‖((f * boundedTrunc hg n : boundedMeasurable X) : X → ℂ) x‖ ≤ C :=
    fun n x => by
      change ‖(f : X → ℂ) x * (boundedTrunc hg n : X → ℂ) x‖ ≤ C
      rw [coe_boundedTrunc]
      by_cases hx : x ∈ {x | ‖g x‖ ≤ (n : ℝ)}
      · rw [Set.indicator_of_mem hx, ← hF]
        exact hC x
      · rw [Set.indicator_of_notMem hx, mul_zero, norm_zero]
        exact hC0
  have hl : ∀ x, Tendsto (fun n => ((f * boundedTrunc hg n : boundedMeasurable X) : X → ℂ) x)
      atTop (𝓝 ((F : X → ℂ) x)) := fun x => by
    rw [hF]
    exact tendsto_const_nhds.mul (tendsto_boundedTrunc hg x)
  refine tendsto_nhds_unique ?_ (P.tendsto_integral_apply (fun n => f * boundedTrunc hg n) F C
    hb hl ψ)
  refine Tendsto.congr (fun n => ?_)
    (((P.integral f).continuous.tendsto _).comp (P.tendsto_integral_trunc hg ψ))
  rw [map_mul]
  rfl

/-! ### The product `(∫ ḡ dP) (∫ g dP) = ∫ |g|² dP` -/

/-- `ḡₙ gₙ = ḡₙ g`, both being `1_{‖g‖ ≤ n} |g|²`. -/
theorem coe_star_boundedTrunc_mul {g : X → ℂ} (hg : Measurable g) (n : ℕ) (x : X) :
    ((star (boundedTrunc hg n) * boundedTrunc hg n : boundedMeasurable X) : X → ℂ) x =
      ((star (boundedTrunc hg n) : boundedMeasurable X) : X → ℂ) x * g x := by
  change star ((boundedTrunc hg n : X → ℂ) x) * (boundedTrunc hg n : X → ℂ) x =
    star ((boundedTrunc hg n : X → ℂ) x) * g x
  rw [coe_boundedTrunc]
  by_cases hx : x ∈ {x | ‖g x‖ ≤ (n : ℝ)}
  · rw [Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem hx, star_zero, zero_mul, zero_mul]

/-- `‖ḡₙ gₙ‖ ≤ |g|²` pointwise. -/
theorem norm_star_boundedTrunc_mul_le {g : X → ℂ} (hg : Measurable g) (n : ℕ) (x : X) :
    ‖((star (boundedTrunc hg n) * boundedTrunc hg n : boundedMeasurable X) : X → ℂ) x‖ ≤
      ‖g x‖ ^ 2 := by
  change ‖star ((boundedTrunc hg n : X → ℂ) x) * (boundedTrunc hg n : X → ℂ) x‖ ≤ ‖g x‖ ^ 2
  rw [norm_mul, norm_star, sq]
  exact mul_le_mul (norm_boundedTrunc_le hg n x) (norm_boundedTrunc_le hg n x) (norm_nonneg _)
    (norm_nonneg _)

/-- `ḡₙ gₙ → |g|²` pointwise. -/
theorem tendsto_star_boundedTrunc_mul {g : X → ℂ} (hg : Measurable g) (x : X) :
    Tendsto (fun n => ((star (boundedTrunc hg n) * boundedTrunc hg n : boundedMeasurable X) :
      X → ℂ) x) atTop (𝓝 ((‖g x‖ ^ 2 : ℝ) : ℂ)) := by
  rw [← star_mul_self_complex (g x)]
  exact ((continuous_star.tendsto _).comp (tendsto_boundedTrunc hg x)).mul
    (tendsto_boundedTrunc hg x)

/-- `ψ ∈ D_{|g|²}` means `∫ |g|⁴ dμ_ψ < ∞`. -/
theorem lintegral_enorm_pow_four_lt_top {g : X → ℂ} (hg : Measurable g) {ψ : H}
    (hψ : ψ ∈ (P.integralPMap (measurable_normSq hg)).domain) :
    ∫⁻ x, ‖g x‖ₑ ^ 4 ∂(P.measure ψ) < ⊤ := by
  have e : ∀ x, ‖((‖g x‖ ^ 2 : ℝ) : ℂ)‖ₑ ^ 2 = ‖g x‖ₑ ^ 4 := fun x => by
    have h1 : ‖((‖g x‖ ^ 2 : ℝ) : ℂ)‖ₑ = ‖g x‖ₑ ^ 2 := by
      rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _), ← ofReal_norm,
        ← ENNReal.ofReal_pow (norm_nonneg _)]
    rw [h1]
    ring
  rw [P.mem_integralPMap_domain, memLp_two_iff_lintegral_lt_top
    (measurable_normSq hg).aestronglyMeasurable] at hψ
  rw [← lintegral_congr e]
  exact hψ

/-- **`D_{|g|²} ⊆ D_g`**: `μ_ψ` is a finite measure and `|g|² ≤ 1 + |g|⁴`. -/
theorem mem_domain_of_mem_normSq_domain {g : X → ℂ} (hg : Measurable g) {ψ : H}
    (hψ : ψ ∈ (P.integralPMap (measurable_normSq hg)).domain) :
    ψ ∈ (P.integralPMap hg).domain := by
  rw [P.mem_integralPMap_domain, memLp_two_iff_lintegral_lt_top hg.aestronglyMeasurable]
  have hfin := P.lintegral_enorm_pow_four_lt_top hg hψ
  have key : ∀ x, ‖g x‖ₑ ^ 2 ≤ 1 + ‖g x‖ₑ ^ 4 := fun x => by
    rcases le_total (‖g x‖ₑ) 1 with h | h
    · refine le_trans ?_ le_self_add
      calc ‖g x‖ₑ ^ 2 ≤ 1 ^ 2 := by gcongr
        _ = 1 := one_pow 2
    · refine le_trans ?_ le_add_self
      have h1 : (1 : ℝ≥0∞) ≤ ‖g x‖ₑ ^ 2 := by
        calc (1 : ℝ≥0∞) = 1 ^ 2 := (one_pow 2).symm
          _ ≤ ‖g x‖ₑ ^ 2 := by gcongr
      calc ‖g x‖ₑ ^ 2 = 1 * ‖g x‖ₑ ^ 2 := (one_mul _).symm
        _ ≤ ‖g x‖ₑ ^ 2 * ‖g x‖ₑ ^ 2 := by gcongr
        _ = ‖g x‖ₑ ^ 4 := by ring
  calc ∫⁻ x, ‖g x‖ₑ ^ 2 ∂(P.measure ψ) ≤ ∫⁻ x, (1 + ‖g x‖ₑ ^ 4) ∂(P.measure ψ) :=
        lintegral_mono key
    _ = P.measure ψ Set.univ + ∫⁻ x, ‖g x‖ₑ ^ 4 ∂(P.measure ψ) := by
        rw [lintegral_add_left measurable_const, lintegral_const, one_mul]
    _ < ⊤ := ENNReal.add_lt_top.2 ⟨measure_lt_top _ _, hfin⟩

/-- **`(∫ g dP) ψ ∈ D_g` for `ψ ∈ D_{|g|²}`**: `∫ |gₙ|² dμ_u = ‖(∫ ḡₙ dP) u‖² =
‖(∫ ḡₙ gₙ dP) ψ‖² = ∫ |gₙ|⁴ dμ_ψ ≤ ∫ |g|⁴ dμ_ψ` for `u = (∫ g dP) ψ`, and Fatou's lemma passes
to the limit. -/
theorem integralPMap_mem_domain {g : X → ℂ} (hg : Measurable g) {ψ : H}
    (hψ : ψ ∈ (P.integralPMap (measurable_normSq hg)).domain)
    (hψg : ψ ∈ (P.integralPMap hg).domain) :
    P.integralPMap hg ⟨ψ, hψg⟩ ∈ (P.integralPMap hg).domain := by
  have hstep : ∀ n : ℕ, ∫⁻ x, ‖(boundedTrunc hg n : X → ℂ) x‖ₑ ^ 2
      ∂(P.measure (P.integralPMap hg ⟨ψ, hψg⟩)) ≤ ∫⁻ x, ‖g x‖ₑ ^ 4 ∂(P.measure ψ) := fun n => by
    have e1 : ∫⁻ x, ‖(boundedTrunc hg n : X → ℂ) x‖ₑ ^ 2
        ∂(P.measure (P.integralPMap hg ⟨ψ, hψg⟩)) =
        ‖P.integral (star (boundedTrunc hg n)) (P.integralPMap hg ⟨ψ, hψg⟩)‖ₑ ^ 2 := by
      rw [P.enorm_integral_apply_sq]
      refine lintegral_congr fun x => ?_
      congr 1
      change _ = ‖star ((boundedTrunc hg n : X → ℂ) x)‖ₑ
      rw [← ofReal_norm, ← ofReal_norm, norm_star]
    rw [e1, P.integral_integralPMap_bounded hg _ _ (coe_star_boundedTrunc_mul hg n) ⟨ψ, hψg⟩,
      P.enorm_integral_apply_sq]
    refine lintegral_mono fun x => ?_
    have h1 : ‖((star (boundedTrunc hg n) * boundedTrunc hg n : boundedMeasurable X) :
        X → ℂ) x‖ₑ ≤ ‖g x‖ₑ ^ 2 := by
      rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
      exact ENNReal.ofReal_le_ofReal (norm_star_boundedTrunc_mul_le hg n x)
    calc ‖((star (boundedTrunc hg n) * boundedTrunc hg n : boundedMeasurable X) : X → ℂ) x‖ₑ ^ 2
        ≤ (‖g x‖ₑ ^ 2) ^ 2 := by gcongr
      _ = ‖g x‖ₑ ^ 4 := by ring
  rw [P.mem_integralPMap_domain, memLp_two_iff_lintegral_lt_top hg.aestronglyMeasurable]
  refine lt_of_le_of_lt ?_ (P.lintegral_enorm_pow_four_lt_top hg hψ)
  calc ∫⁻ x, ‖g x‖ₑ ^ 2 ∂(P.measure (P.integralPMap hg ⟨ψ, hψg⟩))
      = ∫⁻ x, liminf (fun n : ℕ => ‖(boundedTrunc hg n : X → ℂ) x‖ₑ ^ 2) atTop
          ∂(P.measure (P.integralPMap hg ⟨ψ, hψg⟩)) :=
        lintegral_congr fun x => (((ENNReal.continuous_pow 2).tendsto _).comp
          ((continuous_enorm.tendsto _).comp (tendsto_boundedTrunc hg x))).liminf_eq.symm
    _ ≤ liminf (fun n : ℕ => ∫⁻ x, ‖(boundedTrunc hg n : X → ℂ) x‖ₑ ^ 2
          ∂(P.measure (P.integralPMap hg ⟨ψ, hψg⟩))) atTop :=
        lintegral_liminf_le fun n => (boundedMeasurable.measurable _).enorm.pow_const 2
    _ ≤ ∫⁻ x, ‖g x‖ₑ ^ 4 ∂(P.measure ψ) :=
        liminf_le_of_frequently_le (Eventually.of_forall hstep).frequently

/-- `(∫ g dP) ψ ∈ D_ḡ` for `ψ ∈ D_{|g|²}`, as `D_ḡ = D_g`. -/
theorem integralPMap_mem_star_domain {g : X → ℂ} (hg : Measurable g) {ψ : H}
    (hψ : ψ ∈ (P.integralPMap (measurable_normSq hg)).domain)
    (hψg : ψ ∈ (P.integralPMap hg).domain) :
    P.integralPMap hg ⟨ψ, hψg⟩ ∈
      (P.integralPMap (measurable_star_of_measurable hg)).domain :=
  (P.integralPMap_star_domain hg).ge (P.integralPMap_mem_domain hg hψ hψg)

/-- **The product formula `(∫ ḡ dP) ((∫ g dP) ψ) = (∫ |g|² dP) ψ`** on `D_{|g|²}`.  Both sides
are the limit of `(∫ ḡₙ gₙ dP) ψ`: on the left because `(∫ ḡₙ dP) ((∫ g dP) ψ) =
(∫ ḡₙ g dP) ψ = (∫ ḡₙ gₙ dP) ψ` and `∫ ḡₙ dP → ∫ ḡ dP` on `D_ḡ`, on the right by dominated
convergence with the bound `|gₙ|² ≤ |g|² ∈ L²(μ_ψ)`. -/
theorem integralPMap_star_integralPMap {g : X → ℂ} (hg : Measurable g) {ψ : H}
    (hψ : ψ ∈ (P.integralPMap (measurable_normSq hg)).domain)
    (hψg : ψ ∈ (P.integralPMap hg).domain) :
    P.integralPMap (measurable_star_of_measurable hg)
        ⟨P.integralPMap hg ⟨ψ, hψg⟩, P.integralPMap_mem_star_domain hg hψ hψg⟩ =
      P.integralPMap (measurable_normSq hg) ⟨ψ, hψ⟩ := by
  have hG : MemLp (fun x => ‖g x‖ ^ 2) 2 (P.measure ψ) :=
    ((P.mem_integralPMap_domain (measurable_normSq hg)).1 hψ).congr_norm
      (hg.norm.pow_const 2).aestronglyMeasurable
      (Eventually.of_forall fun x => by rw [Complex.norm_real])
  have h1 := P.tendsto_integral_trunc (measurable_star_of_measurable hg)
    ⟨P.integralPMap hg ⟨ψ, hψg⟩, P.integralPMap_mem_star_domain hg hψ hψg⟩
  have h2 := P.tendsto_integral_integralPMap (measurable_normSq hg)
    (fun n => star (boundedTrunc hg n) * boundedTrunc hg n) ⟨ψ, hψ⟩ hG
    (fun n x => norm_star_boundedTrunc_mul_le hg n x) fun x => tendsto_star_boundedTrunc_mul hg x
  refine tendsto_nhds_unique (h1.congr fun n => ?_) h2
  rw [boundedTrunc_star]
  exact P.integral_integralPMap_bounded hg _ _ (coe_star_boundedTrunc_mul hg n) ⟨ψ, hψg⟩

end ProjectionValuedMeasure

end SpectralTheorem
