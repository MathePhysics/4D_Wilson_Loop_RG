import SpectralTheorem.NormalSpectral

/-!
# Self-adjointness of `∫ g dP`, the mirror product formula, and the support of `P`

**Reed–Simon I, Theorem VIII.6 (p. 264)**: "If `g` is real-valued, then `g(A)` is self-adjoint on
`D_g`."  This module proves the converse, so that `∫ g dP` is self-adjoint exactly when `g` is
real almost everywhere for each of the measures `μ_ψ = P.measure ψ`, together with the product
formula of `SpectralTheorem.NormalPMap` with `g` and `ḡ` exchanged, and the statement that the
projection-valued measure `P` of a normal operator `N = ∫ z dP` is carried by the reals exactly
when `N` is self-adjoint.

Here `P` is a projection-valued measure on a measurable space `X`, `g : X → ℂ` is measurable and
`∫ g dP = P.integralPMap hg` is the operator of `SpectralTheorem.PVMUnbounded`.

Proofs.
* **`∫ g dP` depends only on the a.e. classes of `g`.**  If `g = h` almost everywhere for every
  `μ_ψ`, then the truncations `gₙ` and `hₙ` also agree `μ_ψ`-a.e., so
  `‖(∫ (gₙ - hₙ) dP) ψ‖² = ∫ |gₙ - hₙ|² dμ_ψ = 0`; the domains agree because `MemLp` depends only
  on the a.e. class, and the values are limits of the `(∫ gₙ dP) ψ = (∫ hₙ dP) ψ`.
* **Self-adjointness.**  If `g` is a.e. real for every `μ_ψ` then `(∫ g dP)† = ∫ ḡ dP = ∫ g dP`
  by the previous item.  Conversely, if `∫ g dP` is self-adjoint then `(∫ ḡₙ dP) u - (∫ gₙ dP) u`
  tends to `0` for `u ∈ D_g`, and its squared norm is `∫ |ḡₙ - gₙ|² dμ_u`, so Fatou's lemma gives
  `∫ |ḡ - g|² dμ_u = 0`, that is, `g` is a.e. real for `μ_u`.  For an arbitrary `ψ` apply this to
  `u = P_{‖g‖ ≤ n} ψ`, whose measure is `μ_ψ` restricted to `{‖g‖ ≤ n}`, and let `n → ∞`.
* **The mirror product formula** `(∫ g dP) ((∫ ḡ dP) ψ) = (∫ |g|² dP) ψ` on `D_{|g|²}` is
  `ProjectionValuedMeasure.integralPMap_star_integralPMap` applied to `ḡ`, whose conjugate is `g`
  and whose modulus is that of `g`.
* **The support.**  `P` is carried by a measurable set `s` (`P sᶜ = 0`) exactly when `μ_ψ sᶜ = 0`
  for every `ψ`, since `μ_ψ sᶜ = ‖P sᶜ ψ‖²`.  With `s = ℝ ⊆ ℂ` and `g = id` this turns the
  self-adjointness criterion into: `∫ z dP` is self-adjoint iff `P` is carried by the reals.

## Main definitions and results

* `ProjectionValuedMeasure.integralPMap_congr_ae`: `∫ g dP = ∫ h dP` when `g = h` a.e. for every
  `μ_ψ`.
* `ProjectionValuedMeasure.isSelfAdjoint_integralPMap_iff`: `∫ g dP` is self-adjoint iff `g` is
  a.e. real for every `μ_ψ`.
* `ProjectionValuedMeasure.integralPMap_integralPMap_star`: the product formula
  `(∫ g dP) ((∫ ḡ dP) ψ) = (∫ |g|² dP) ψ` on `D_{|g|²}`.
* `ProjectionValuedMeasure.apply_eq_zero_iff`, `ProjectionValuedMeasure.apply_compl_eq_zero_iff`:
  `P t = 0` iff `μ_ψ t = 0` for every `ψ`, and `P sᶜ = 0` iff `P s = 1`.
* `ProjectionValuedMeasure.isSelfAdjoint_integralPMap_id_iff`,
  `SpectralTheorem.isSelfAdjoint_iff_apply_real_eq_one`: `∫ z dP` is self-adjoint iff `P` is
  carried by the reals.
* `SpectralTheorem.spectralPVM_apply_compl_spectrum`,
  `SpectralTheorem.map_apply_compl_preimage_spectrum`: `P_R` is carried by `σ(R)`, and the
  pushforward of `P_R` along `w ↦ w⁻¹ + z₀` is carried by `{z | (z - z₀)⁻¹ ∈ σ(R)}`.
-/

noncomputable section

open scoped InnerProductSpace ENNReal Topology ComplexConjugate
open MeasureTheory Filter Set

namespace SpectralTheorem

universe u

variable {X : Type*} [MeasurableSpace X]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### Functions agreeing almost everywhere -/

/-- The truncations of two functions agreeing `μ`-a.e. agree `μ`-a.e. -/
theorem boundedTrunc_ae_eq {g h : X → ℂ} (hg : Measurable g) (hh : Measurable h)
    {μ : Measure X} (hgh : g =ᵐ[μ] h) (n : ℕ) :
    ((boundedTrunc hg n : boundedMeasurable X) : X → ℂ) =ᵐ[μ]
      ((boundedTrunc hh n : boundedMeasurable X) : X → ℂ) := by
  filter_upwards [hgh] with x hx
  simp only [coe_boundedTrunc]
  by_cases hx1 : ‖g x‖ ≤ (n : ℝ)
  · have hx2 : ‖h x‖ ≤ (n : ℝ) := by rwa [← hx]
    rw [Set.indicator_of_mem (show x ∈ {x | ‖g x‖ ≤ (n : ℝ)} from hx1),
      Set.indicator_of_mem (show x ∈ {x | ‖h x‖ ≤ (n : ℝ)} from hx2), hx]
  · have hx2 : ¬ ‖h x‖ ≤ (n : ℝ) := by rwa [← hx]
    rw [Set.indicator_of_notMem (show x ∉ {x | ‖g x‖ ≤ (n : ℝ)} from hx1),
      Set.indicator_of_notMem (show x ∉ {x | ‖h x‖ ≤ (n : ℝ)} from hx2)]

namespace ProjectionValuedMeasure

variable (P : ProjectionValuedMeasure X H)

/-- For bounded `f` and `f'` agreeing `μ_ψ`-a.e., `(∫ f dP) ψ = (∫ f' dP) ψ`, because
`‖(∫ (f - f') dP) ψ‖² = ∫ |f - f'|² dμ_ψ = 0`. -/
theorem integral_apply_eq_of_ae_eq {f f' : boundedMeasurable X} (ψ : H)
    (h : (f : X → ℂ) =ᵐ[P.measure ψ] (f' : X → ℂ)) :
    P.integral f ψ = P.integral f' ψ := by
  have h0 : ∫⁻ x, ‖((f - f' : boundedMeasurable X) : X → ℂ) x‖ₑ ^ 2 ∂(P.measure ψ) = 0 := by
    refine (lintegral_eq_zero_iff ((boundedMeasurable.measurable _).enorm.pow_const 2)).2 ?_
    filter_upwards [h] with x hx
    have e : ((f - f' : boundedMeasurable X) : X → ℂ) x = 0 := by
      change (f : X → ℂ) x - (f' : X → ℂ) x = 0
      rw [hx, sub_self]
    rw [e]
    simp
  have h1 : ‖P.integral (f - f') ψ‖ₑ = 0 :=
    pow_eq_zero_iff two_ne_zero |>.1 ((P.enorm_integral_apply_sq (f - f') ψ).trans h0)
  have h2 : P.integral (f - f') ψ = 0 := by simpa using h1
  have e : P.integral (f - f') ψ = P.integral f ψ - P.integral f' ψ := by
    rw [map_sub]
    rfl
  rw [e] at h2
  exact sub_eq_zero.1 h2

/-- **`∫ g dP` depends only on the a.e. classes of `g`**: if `g = h` almost everywhere for every
measure `μ_ψ`, then `∫ g dP = ∫ h dP`.  The truncations then also agree `μ_ψ`-a.e., so
`(∫ gₙ dP) ψ = (∫ hₙ dP) ψ` for every `ψ`, and the domains agree because membership of `L²`
depends only on the a.e. class. -/
theorem integralPMap_congr_ae {g h : X → ℂ} (hg : Measurable g) (hh : Measurable h)
    (hgh : ∀ ψ : H, g =ᵐ[P.measure ψ] h) : P.integralPMap hg = P.integralPMap hh := by
  have hn : ∀ (n : ℕ) (ψ : H),
      P.integral (boundedTrunc hg n) ψ = P.integral (boundedTrunc hh n) ψ := fun n ψ =>
    P.integral_apply_eq_of_ae_eq ψ (boundedTrunc_ae_eq hg hh (hgh ψ) n)
  refine LinearPMap.ext ?_ fun ψ h1 h2 => ?_
  · refine Submodule.ext fun ψ => ?_
    rw [P.mem_integralPMap_domain, P.mem_integralPMap_domain]
    exact ⟨fun hψ => hψ.ae_eq (hgh ψ), fun hψ => hψ.ae_eq (hgh ψ).symm⟩
  · exact tendsto_nhds_unique (P.tendsto_integral_trunc hg ⟨ψ, h1⟩)
      ((P.tendsto_integral_trunc hh ⟨ψ, h2⟩).congr fun n => (hn n ψ).symm)

/-! ### Self-adjointness of `∫ g dP` -/

/-- **If `g` is a.e. real for every `μ_ψ`, then `∫ g dP` is self-adjoint**: its adjoint is
`∫ ḡ dP`, which is `∫ g dP` by `integralPMap_congr_ae`. -/
theorem isSelfAdjoint_integralPMap_of_ae_real {g : X → ℂ} (hg : Measurable g)
    (hae : ∀ ψ : H, ∀ᵐ x ∂(P.measure ψ), star (g x) = g x) :
    IsSelfAdjoint (P.integralPMap hg) := by
  rw [LinearPMap.isSelfAdjoint_def, P.adjoint_integralPMap hg]
  refine P.integralPMap_congr_ae (measurable_star_of_measurable hg) hg fun ψ => ?_
  filter_upwards [hae ψ] with x hx using hx

/-- **If `∫ g dP` is self-adjoint then `g` is a.e. real for `μ_u` with `u ∈ D_g`**: the vectors
`(∫ ḡₙ dP) u - (∫ gₙ dP) u` tend to `(∫ ḡ dP) u - (∫ g dP) u = 0`, their squared norms are
`∫ |ḡₙ - gₙ|² dμ_u`, and Fatou's lemma gives `∫ |ḡ - g|² dμ_u = 0`. -/
theorem ae_real_of_isSelfAdjoint_of_mem_domain {g : X → ℂ} (hg : Measurable g)
    (hsa : IsSelfAdjoint (P.integralPMap hg)) {u : H} (hu : u ∈ (P.integralPMap hg).domain) :
    ∀ᵐ x ∂(P.measure u), star (g x) = g x := by
  have hgs : Measurable (star g) := measurable_star_of_measurable hg
  have hE : P.integralPMap hgs = P.integralPMap hg := by
    rw [← P.adjoint_integralPMap hg]
    exact LinearPMap.isSelfAdjoint_def.1 hsa
  have hu' : u ∈ (P.integralPMap hgs).domain := (P.integralPMap_star_domain hg).ge hu
  have hval : P.integralPMap hgs ⟨u, hu'⟩ = P.integralPMap hg ⟨u, hu⟩ :=
    linearPMap_apply_eq_of_eq hE hu' hu
  have hv : Tendsto (fun n : ℕ => P.integral (boundedTrunc hgs n) u -
      P.integral (boundedTrunc hg n) u) atTop (𝓝 0) := by
    have h3 := (P.tendsto_integral_trunc hgs ⟨u, hu'⟩).sub (P.tendsto_integral_trunc hg ⟨u, hu⟩)
    rw [hval, sub_self] at h3
    exact h3
  have hnorm : ∀ n : ℕ, ∫⁻ x, ‖(boundedTrunc hgs n : X → ℂ) x -
      (boundedTrunc hg n : X → ℂ) x‖ₑ ^ 2 ∂(P.measure u) =
      ‖P.integral (boundedTrunc hgs n) u - P.integral (boundedTrunc hg n) u‖ₑ ^ 2 := fun n => by
    have e : P.integral (boundedTrunc hgs n - boundedTrunc hg n) u =
        P.integral (boundedTrunc hgs n) u - P.integral (boundedTrunc hg n) u := by
      rw [map_sub]
      rfl
    rw [← e, P.enorm_integral_apply_sq]
    exact lintegral_congr fun x => rfl
  have hlim : ∀ x, Tendsto (fun n : ℕ => ‖(boundedTrunc hgs n : X → ℂ) x -
      (boundedTrunc hg n : X → ℂ) x‖ₑ ^ 2) atTop (𝓝 (‖star (g x) - g x‖ₑ ^ 2)) := fun x =>
    ((ENNReal.continuous_pow 2).tendsto _).comp ((continuous_enorm.tendsto _).comp
      ((tendsto_boundedTrunc hgs x).sub (tendsto_boundedTrunc hg x)))
  have hlim0 : Tendsto (fun n : ℕ => ‖P.integral (boundedTrunc hgs n) u -
      P.integral (boundedTrunc hg n) u‖ₑ ^ 2) atTop (𝓝 0) := by
    have h := (continuous_enorm.tendsto (0 : H)).comp hv
    rw [enorm_zero] at h
    have h2 := ((ENNReal.continuous_pow 2).tendsto (0 : ℝ≥0∞)).comp h
    simpa [Function.comp_def] using h2
  have hzero : ∫⁻ x, ‖star (g x) - g x‖ₑ ^ 2 ∂(P.measure u) = 0 := by
    refine le_antisymm (le_of_le_of_eq ?_ hlim0.liminf_eq) zero_le
    calc ∫⁻ x, ‖star (g x) - g x‖ₑ ^ 2 ∂(P.measure u)
        = ∫⁻ x, liminf (fun n : ℕ => ‖(boundedTrunc hgs n : X → ℂ) x -
            (boundedTrunc hg n : X → ℂ) x‖ₑ ^ 2) atTop ∂(P.measure u) :=
          lintegral_congr fun x => (hlim x).liminf_eq.symm
      _ ≤ liminf (fun n : ℕ => ∫⁻ x, ‖(boundedTrunc hgs n : X → ℂ) x -
            (boundedTrunc hg n : X → ℂ) x‖ₑ ^ 2 ∂(P.measure u)) atTop :=
          lintegral_liminf_le fun n => (((boundedMeasurable.measurable (boundedTrunc hgs n)).sub
            (boundedMeasurable.measurable (boundedTrunc hg n))).enorm.pow_const 2)
      _ = liminf (fun n : ℕ => ‖P.integral (boundedTrunc hgs n) u -
            P.integral (boundedTrunc hg n) u‖ₑ ^ 2) atTop :=
          congrArg (fun f => liminf f atTop) (funext hnorm)
  have hmeas : Measurable fun x => ‖star (g x) - g x‖ₑ ^ 2 := (hgs.sub hg).enorm.pow_const 2
  filter_upwards [(lintegral_eq_zero_iff hmeas).1 hzero] with x hx
  simp only [Pi.zero_apply] at hx
  have hx' : star (g x) - g x = 0 := by
    simpa using (pow_eq_zero_iff two_ne_zero).1 hx
  exact sub_eq_zero.1 hx'

/-- **If `∫ g dP` is self-adjoint then `g` is a.e. real for every `μ_ψ`**: apply the previous
lemma to `u = P_{‖g‖ ≤ n} ψ`, whose measure is `μ_ψ` restricted to `{‖g‖ ≤ n}`, and cover `X` by
the sets `{‖g‖ ≤ n}`. -/
theorem ae_real_of_isSelfAdjoint_integralPMap {g : X → ℂ} (hg : Measurable g)
    (hsa : IsSelfAdjoint (P.integralPMap hg)) (ψ : H) :
    ∀ᵐ x ∂(P.measure ψ), star (g x) = g x := by
  have hs : ∀ n : ℕ, MeasurableSet {x | ‖g x‖ ≤ (n : ℝ)} := fun n =>
    measurableSet_le hg.norm measurable_const
  have hstep : ∀ n : ℕ,
      P.measure ψ ({x | ¬ star (g x) = g x} ∩ {x | ‖g x‖ ≤ (n : ℝ)}) = 0 := fun n => by
    have h := P.ae_real_of_isSelfAdjoint_of_mem_domain hg hsa
      (P.apply_mem_integralPMap_domain hg n ψ)
    rwa [ae_iff, P.measure_apply_apply (hs n), Measure.restrict_apply' (hs n)] at h
  rw [ae_iff]
  refine measure_mono_null (fun x hx => ?_) (measure_iUnion_null hstep)
  obtain ⟨n, hn⟩ := exists_nat_ge ‖g x‖
  exact Set.mem_iUnion.2 ⟨n, hx, hn⟩

/-- **Self-adjointness of `∫ g dP`** (the converse of Reed–Simon I, Theorem VIII.6, p. 264):
`∫ g dP` is self-adjoint if and only if `g` is real almost everywhere for every measure `μ_ψ`. -/
theorem isSelfAdjoint_integralPMap_iff {g : X → ℂ} (hg : Measurable g) :
    IsSelfAdjoint (P.integralPMap hg) ↔ ∀ ψ : H, ∀ᵐ x ∂(P.measure ψ), star (g x) = g x :=
  ⟨P.ae_real_of_isSelfAdjoint_integralPMap hg, P.isSelfAdjoint_integralPMap_of_ae_real hg⟩

/-! ### The product `(∫ g dP) (∫ ḡ dP) = ∫ |g|² dP` -/

/-- `∫ |ḡ|² dP = ∫ |g|² dP`. -/
theorem integralPMap_normSq_star {g : X → ℂ} (hg : Measurable g) :
    P.integralPMap (measurable_normSq (measurable_star_of_measurable hg)) =
      P.integralPMap (measurable_normSq hg) :=
  P.integralPMap_congr _ _ fun x => by simp

/-- `∫ (ḡ)‾ dP = ∫ g dP`. -/
theorem integralPMap_star_star {g : X → ℂ} (hg : Measurable g) :
    P.integralPMap (measurable_star_of_measurable (measurable_star_of_measurable hg)) =
      P.integralPMap hg :=
  P.integralPMap_congr _ _ fun x => by simp

/-- **`(∫ ḡ dP) ψ ∈ D_g` for `ψ ∈ D_{|g|²}`**, the mirror of
`ProjectionValuedMeasure.integralPMap_mem_star_domain`. -/
theorem integralPMap_star_mem_domain {g : X → ℂ} (hg : Measurable g) {ψ : H}
    (hψ : ψ ∈ (P.integralPMap (measurable_normSq hg)).domain)
    (hψs : ψ ∈ (P.integralPMap (measurable_star_of_measurable hg)).domain) :
    P.integralPMap (measurable_star_of_measurable hg) ⟨ψ, hψs⟩ ∈
      (P.integralPMap hg).domain := by
  have hψ' := (congrArg LinearPMap.domain (P.integralPMap_normSq_star hg)).ge hψ
  exact (P.integralPMap_star_domain hg).le
    (P.integralPMap_mem_domain (measurable_star_of_measurable hg) hψ' hψs)

/-- **The product formula `(∫ g dP) ((∫ ḡ dP) ψ) = (∫ |g|² dP) ψ`** on `D_{|g|²}`, the mirror of
`ProjectionValuedMeasure.integralPMap_star_integralPMap`: apply that theorem to `ḡ`, whose
conjugate is `g` and whose modulus is the modulus of `g`. -/
theorem integralPMap_integralPMap_star {g : X → ℂ} (hg : Measurable g) {ψ : H}
    (hψ : ψ ∈ (P.integralPMap (measurable_normSq hg)).domain)
    (hψs : ψ ∈ (P.integralPMap (measurable_star_of_measurable hg)).domain) :
    P.integralPMap hg ⟨P.integralPMap (measurable_star_of_measurable hg) ⟨ψ, hψs⟩,
        P.integralPMap_star_mem_domain hg hψ hψs⟩ =
      P.integralPMap (measurable_normSq hg) ⟨ψ, hψ⟩ := by
  have hψ' := (congrArg LinearPMap.domain (P.integralPMap_normSq_star hg)).ge hψ
  have hv' := P.integralPMap_mem_star_domain (measurable_star_of_measurable hg) hψ' hψs
  calc P.integralPMap hg ⟨P.integralPMap (measurable_star_of_measurable hg) ⟨ψ, hψs⟩,
        P.integralPMap_star_mem_domain hg hψ hψs⟩
      = P.integralPMap (measurable_star_of_measurable (measurable_star_of_measurable hg))
          ⟨P.integralPMap (measurable_star_of_measurable hg) ⟨ψ, hψs⟩, hv'⟩ :=
        (linearPMap_apply_eq_of_eq (P.integralPMap_star_star hg) hv' _).symm
    _ = P.integralPMap (measurable_normSq (measurable_star_of_measurable hg)) ⟨ψ, hψ'⟩ :=
        P.integralPMap_star_integralPMap (measurable_star_of_measurable hg) hψ' hψs
    _ = P.integralPMap (measurable_normSq hg) ⟨ψ, hψ⟩ :=
        linearPMap_apply_eq_of_eq (P.integralPMap_normSq_star hg) hψ' hψ

/-! ### The sets carrying `P` -/

/-- **`P t = 0` iff every measure `μ_ψ` gives `t` mass zero**, since `μ_ψ t = ‖P_t ψ‖². -/
theorem apply_eq_zero_iff {t : Set X} (ht : MeasurableSet t) :
    P t = 0 ↔ ∀ ψ : H, P.measure ψ t = 0 := by
  refine ⟨fun h ψ => by rw [P.measure_apply ψ ht, h]; simp, fun h => ?_⟩
  refine ContinuousLinearMap.ext fun ψ => ?_
  have h1 := h ψ
  rw [P.measure_apply ψ ht, ENNReal.ofReal_eq_zero] at h1
  have h2 : ‖P t ψ‖ = 0 :=
    pow_eq_zero_iff two_ne_zero |>.1 (le_antisymm h1 (sq_nonneg _))
  rw [norm_eq_zero] at h2
  simpa using h2

/-- **`P` is carried by a measurable set `s` iff `P sᶜ = 0`**, as `P sᶜ = 1 - P s`. -/
theorem apply_compl_eq_zero_iff {s : Set X} (hs : MeasurableSet s) : P sᶜ = 0 ↔ P s = 1 := by
  rw [P.compl hs, sub_eq_zero, eq_comm]

end ProjectionValuedMeasure

/-! ### Self-adjointness and the reals -/

/-- The complement of the real axis is the set where `z̄ ≠ z`. -/
theorem compl_preimage_im_eq_zero :
    {z : ℂ | ¬ star (id z) = id z} = (Complex.im ⁻¹' {0})ᶜ := by
  ext z
  simp [Complex.conj_eq_iff_im]

namespace ProjectionValuedMeasure

/-- **`∫ z dP` is self-adjoint exactly when `P` is carried by the reals**: by the
self-adjointness criterion, `∫ z dP` is self-adjoint iff `z̄ = z` for `μ_ψ`-almost every `z` and
every `ψ`, that is, iff `μ_ψ` gives the complement of the real axis mass zero for every `ψ`. -/
theorem isSelfAdjoint_integralPMap_id_iff (P : ProjectionValuedMeasure ℂ H) :
    IsSelfAdjoint (P.integralPMap (measurable_id : Measurable (id : ℂ → ℂ))) ↔
      P (Complex.im ⁻¹' {0}) = 1 := by
  rw [← P.apply_compl_eq_zero_iff measurableSet_im_eq_zero,
    P.isSelfAdjoint_integralPMap_iff measurable_id,
    P.apply_eq_zero_iff measurableSet_im_eq_zero.compl]
  exact forall_congr' fun ψ => by rw [ae_iff, compl_preimage_im_eq_zero]

end ProjectionValuedMeasure

/-- **A normal operator given by a projection-valued measure is self-adjoint exactly when that
measure is carried by the reals.**  For an operator `N` with a bounded normal resolvent, such a
`P` is provided by `SpectralTheorem.exists_pvm_integralPMap_eq`. -/
theorem isSelfAdjoint_iff_apply_real_eq_one {N : H →ₗ.[ℂ] H}
    {P : ProjectionValuedMeasure ℂ H} (hP : P.integralPMap measurable_id = N) :
    IsSelfAdjoint N ↔ P (Complex.im ⁻¹' {0}) = 1 := by
  rw [← hP]
  exact P.isSelfAdjoint_integralPMap_id_iff

/-! ### The support of the p.v.m. of an operator with a bounded normal resolvent -/

variable (R : H →L[ℂ] H) [IsStarNormal R]

/-- **`P_R` is carried by `σ(R)`**, the p.v.m. version of
`ProjectionValuedMeasure.apply_compl_spectrum` for `R = ∫ w dP_R`. -/
theorem spectralPVM_apply_compl_spectrum : spectralPVM R (spectrum ℂ R)ᶜ = 0 := by
  have h := (spectralPVM R).apply_compl_spectrum (spectralPVM_isBounded R)
  rwa [toOperator_spectralPVM] at h

/-- **The projection-valued measure of an operator with a bounded normal resolvent is carried by
the spectrum**: the p.v.m. `F_* P_R` built in `SpectralTheorem.exists_pvm_integralPMap_eq` from
`F w = w⁻¹ + z₀` gives mass zero to the complement of `{z | (z - z₀)⁻¹ ∈ σ(R)}`, because that
complement pulls back along `F` to `σ(R)ᶜ`. -/
theorem map_apply_compl_preimage_spectrum {z₀ : ℂ}
    (hFm : Measurable fun w : ℂ => w⁻¹ + z₀) : -- totalisation-audit: allow P_R{0} = 0
    ((spectralPVM R).map (fun w : ℂ => w⁻¹ + z₀) hFm) -- totalisation-audit: allow P_R{0} = 0
      {z : ℂ | (z - z₀)⁻¹ ∈ spectrum ℂ R}ᶜ = 0 := by -- totalisation-audit: allow larger carrier
  have hspec : MeasurableSet (spectrum ℂ R) := (spectrum.isClosed (𝕜 := ℂ) R).measurableSet
  have hsm : MeasurableSet {z : ℂ | (z - z₀)⁻¹ ∈ -- totalisation-audit: allow larger carrier
      spectrum ℂ R} := (measurable_inv.comp (measurable_id.sub_const z₀)) hspec
  have hset : (fun w : ℂ => w⁻¹ + z₀) ⁻¹' -- totalisation-audit: allow P_R{0} = 0
      {z : ℂ | (z - z₀)⁻¹ ∈ spectrum ℂ R}ᶜ = -- totalisation-audit: allow larger carrier
      (spectrum ℂ R)ᶜ := by
    ext w
    simp [add_sub_cancel_right, inv_inv]
  rw [(spectralPVM R).map_apply hFm hsm.compl, hset]
  exact spectralPVM_apply_compl_spectrum R

end SpectralTheorem
