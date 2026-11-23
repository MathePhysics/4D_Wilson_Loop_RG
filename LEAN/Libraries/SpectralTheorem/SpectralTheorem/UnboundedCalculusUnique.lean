import SpectralTheorem.UnboundedCalculus

/-!
# Uniqueness of the functional calculus of an unbounded self-adjoint operator

**Reed–Simon I, Theorem VIII.5, p. 262** (the uniqueness half).  Let `A` be self-adjoint.  A
`⋆`-homomorphism `Φ` from the bounded Borel functions on `ℝ` to `𝓛(H)` with (b)
`‖Φ(h)‖ ≤ ‖h‖∞`, (c) `Φ(hₙ) ψ → A ψ` for `ψ ∈ D(A)` when `hₙ(x) → x` and `|hₙ(x)| ≤ |x|`, and
(d) `Φ(hₙ) → Φ(h)` strongly when `hₙ → h` pointwise with `‖hₙ‖∞` bounded, is the functional
calculus `SpectralTheorem.selfAdjointCalc hA` of `SpectralTheorem.UnboundedCalculus`.

Reed–Simon leave the uniqueness to the reader.  The proof here reduces it to the uniqueness of
the continuous functional calculus of the resolvent `R = (A + i)⁻¹`:

1. **`Φ(κ) = R`** for `κ(x) = (x + i)⁻¹`.  With `hₙ = x · χ_{[-n, n]}`, (c) gives
   `Φ(κ) Φ(hₙ) ψ → Φ(κ) A ψ`, and (d) gives `Φ(κ hₙ) ψ → Φ(x κ) ψ = ψ - i Φ(κ) ψ`, since
   `x κ(x) = 1 - i κ(x)` and `|κ hₙ| ≤ 1`.  So `Φ(κ) (A + i) ψ = ψ` on `D(A)`, and
   `Φ(κ) = R` because `A + i` maps `D(A)` onto `H`.
2. **Continuous functions of `κ`.**  `K = {z | |z|² + Im z = 0}` is compact, contains `σ(R)`
   (`SpectralTheorem.normSq_add_im_eq_zero_of_mem_spectrum`) and the values of `κ`.  The maps
   `k ↦ Φ(k ∘ κ)` and `k ↦ (k|σ(R))(R)` are continuous `⋆`-homomorphisms `C(K, ℂ) → 𝓛(H)`
   sending `z ↦ z` to `R`, so they agree (Stone–Weierstrass,
   `ContinuousMap.starAlgHom_ext_map_X`).
3. **Bounded Borel functions on `K`.**  Both maps satisfy (d), so they agree on all bounded Borel
   functions on `K` by the monotone class theorem (`IsBoundedLimitClosed.of_continuous`).
4. **Conclusion.**  For bounded Borel `h` on `ℝ`, `k = h ∘ ρ` with `ρ(z) = (z⁻¹ - i).re` satisfies
   `k ∘ κ = h` and `k|σ(R) = h ∘ ρ`, so `Φ(h) = (h ∘ ρ)(R) = selfAdjointCalc hA h`.

## Main definitions and results

* `SpectralTheorem.IsSelfAdjointCalculus hA Φ`: properties (b)–(d) of Theorem VIII.5.
* `SpectralTheorem.IsSelfAdjointCalculus.map_resolventFn`: `Φ((x + i)⁻¹) = (A + i)⁻¹`.
* `SpectralTheorem.IsSelfAdjointCalculus.eq_selfAdjointCalc`: **uniqueness**,
  `Φ = selfAdjointCalc hA`.
-/

noncomputable section

open scoped InnerProductSpace Topology
open MeasureTheory Filter KatoRellich

namespace SpectralTheorem

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {A : H →ₗ.[ℂ] H}

/-- **A functional calculus for the self-adjoint operator `A`** (Reed–Simon I, Theorem VIII.5
(b)–(d), p. 262), for a `⋆`-homomorphism `Φ` from bounded Borel functions on `ℝ` to `𝓛(H)`:
(b) `‖Φ(h)‖ ≤ ‖h‖∞`; (c) if `hₙ(x) → x` and `|hₙ(x)| ≤ |x|`, then `Φ(hₙ) ψ → A ψ` for
`ψ ∈ D(A)`; (d) if `hₙ → h` pointwise with `‖hₙ‖∞` bounded, then `Φ(hₙ) → Φ(h)` strongly. -/
structure IsSelfAdjointCalculus (hA : IsSelfAdjoint A)
    (Φ : boundedMeasurable ℝ →⋆ₐ[ℂ] (H →L[ℂ] H)) : Prop where
  norm_le : ∀ (h : boundedMeasurable ℝ) (C : ℝ), 0 ≤ C → (∀ x, ‖(h : ℝ → ℂ) x‖ ≤ C) →
    ‖Φ h‖ ≤ C
  tendsto_self : ∀ (h : ℕ → boundedMeasurable ℝ), (∀ n x, ‖(h n : ℝ → ℂ) x‖ ≤ |x|) →
    (∀ x, Tendsto (fun n => (h n : ℝ → ℂ) x) atTop (𝓝 (x : ℂ))) →
    ∀ (ψ : H) (hψ : ψ ∈ A.domain), Tendsto (fun n => Φ (h n) ψ) atTop (𝓝 (A ⟨ψ, hψ⟩))
  tendsto : ∀ (h : ℕ → boundedMeasurable ℝ) (h₀ : boundedMeasurable ℝ) (C : ℝ),
    (∀ n x, ‖(h n : ℝ → ℂ) x‖ ≤ C) →
    (∀ x, Tendsto (fun n => (h n : ℝ → ℂ) x) atTop (𝓝 ((h₀ : ℝ → ℂ) x))) →
    ∀ ψ : H, Tendsto (fun n => Φ (h n) ψ) atTop (𝓝 (Φ h₀ ψ))

/-! ### The function `κ(x) = (x + i)⁻¹` and the truncations `x · χ_{[-n, n]}` -/

/-- `x + i ≠ 0` for real `x`. -/
theorem ofReal_add_I_ne_zero (x : ℝ) : (x : ℂ) + Complex.I ≠ 0 := by
  intro h
  have h' := congrArg Complex.im h
  simp at h'

/-- `κ(x) = (x + i)⁻¹`, the function of `A` that is `(A + i)⁻¹`. -/
def resolventFn (x : ℝ) : ℂ :=
  ((x : ℂ) + Complex.I)⁻¹ -- totalisation-audit: allow x + i ≠ 0 (ofReal_add_I_ne_zero)

/-- `κ` is continuous. -/
theorem continuous_resolventFn : Continuous resolventFn :=
  (Complex.continuous_ofReal.add continuous_const).inv₀ ofReal_add_I_ne_zero

/-- `|x| ≤ |x + i|`. -/
theorem abs_le_norm_ofReal_add_I (x : ℝ) : |x| ≤ ‖(x : ℂ) + Complex.I‖ := by
  simpa using Complex.abs_re_le_norm ((x : ℂ) + Complex.I)

/-- `1 ≤ |x + i|`. -/
theorem one_le_norm_ofReal_add_I (x : ℝ) : 1 ≤ ‖(x : ℂ) + Complex.I‖ := by
  simpa using Complex.abs_im_le_norm ((x : ℂ) + Complex.I)

/-- `|κ(x)| ≤ 1`. -/
theorem norm_resolventFn_le (x : ℝ) : ‖resolventFn x‖ ≤ 1 := by
  rw [resolventFn, norm_inv]
  exact inv_le_one_of_one_le₀ (one_le_norm_ofReal_add_I x)

/-- `|κ(x)| |x| ≤ 1`. -/
theorem norm_resolventFn_mul_abs_le (x : ℝ) : ‖resolventFn x‖ * |x| ≤ 1 := by
  rw [resolventFn, norm_inv]
  have hpos : 0 < ‖(x : ℂ) + Complex.I‖ := norm_pos_iff.mpr (ofReal_add_I_ne_zero x)
  rw [inv_mul_le_iff₀ hpos, mul_one]
  exact abs_le_norm_ofReal_add_I x

/-- `x κ(x) = 1 - i κ(x)`. -/
theorem ofReal_mul_resolventFn (x : ℝ) :
    (x : ℂ) * resolventFn x = 1 - Complex.I * resolventFn x := by
  rw [eq_sub_iff_add_eq, ← add_mul, resolventFn, mul_inv_cancel₀ (ofReal_add_I_ne_zero x)]

/-- `κ` as a bounded Borel function. -/
def resolventFnBM : boundedMeasurable ℝ :=
  ⟨resolventFn, continuous_resolventFn.measurable, 1, norm_resolventFn_le⟩

/-- The underlying function of `resolventFnBM` is `κ`. -/
@[simp]
theorem coe_resolventFnBM : ((resolventFnBM : boundedMeasurable ℝ) : ℝ → ℂ) = resolventFn :=
  rfl

/-- The truncation `x · χ_{[-n, n]}(x)` of the identity, a bounded Borel function. -/
def truncId (n : ℕ) : boundedMeasurable ℝ :=
  ⟨(Set.Icc (-(n : ℝ)) n).indicator (fun x => (x : ℂ)),
    Complex.measurable_ofReal.indicator measurableSet_Icc, n, fun x => by
      by_cases hx : x ∈ Set.Icc (-(n : ℝ)) n
      · rw [Set.indicator_of_mem hx, Complex.norm_real, Real.norm_eq_abs]
        exact abs_le.mpr hx
      · rw [Set.indicator_of_notMem hx, norm_zero]
        exact Nat.cast_nonneg n⟩

/-- The underlying function of `truncId n` is `x · χ_{[-n, n]}(x)`. -/
theorem coe_truncId (n : ℕ) : ((truncId n : boundedMeasurable ℝ) : ℝ → ℂ) =
    (Set.Icc (-(n : ℝ)) n).indicator (fun x => (x : ℂ)) :=
  rfl

/-- `|x · χ_{[-n, n]}(x)| ≤ |x|`. -/
theorem norm_truncId_le (n : ℕ) (x : ℝ) : ‖(truncId n : ℝ → ℂ) x‖ ≤ |x| := by
  rw [coe_truncId]
  refine (norm_indicator_le_norm_self _ _).trans ?_
  rw [Complex.norm_real, Real.norm_eq_abs]

/-- `x · χ_{[-n, n]}(x) → x` as `n → ∞`. -/
theorem tendsto_truncId (x : ℝ) :
    Tendsto (fun n => (truncId n : ℝ → ℂ) x) atTop (𝓝 (x : ℂ)) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop ⌈|x|⌉₊] with n hn
  have hx : |x| ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hn)
  rw [coe_truncId, Set.indicator_of_mem (Set.mem_Icc.mpr (abs_le.mp hx))]

/-! ### Step 1: `Φ(κ) = (A + i)⁻¹` -/

namespace IsSelfAdjointCalculus

variable {hA : IsSelfAdjoint A} {Φ : boundedMeasurable ℝ →⋆ₐ[ℂ] (H →L[ℂ] H)}

/-- `Φ(κ) (A + i) ψ = ψ` for `ψ ∈ D(A)`: by (c), `Φ(κ) Φ(x χ_{[-n, n]}) ψ → Φ(κ) A ψ`, and by
(d), `Φ(κ · x χ_{[-n, n]}) ψ → Φ(1 - i κ) ψ`. -/
theorem apply_resolventFn_addScalar (hΦ : IsSelfAdjointCalculus hA Φ) (ψ : H)
    (hψ : ψ ∈ A.domain) :
    Φ resolventFnBM (A ⟨ψ, hψ⟩ + Complex.I • ψ) = ψ := by
  have h1 := ((Φ resolventFnBM).continuous.tendsto _).comp
    (hΦ.tendsto_self truncId norm_truncId_le tendsto_truncId ψ hψ)
  have h2 := hΦ.tendsto (fun n => resolventFnBM * truncId n) (1 - Complex.I • resolventFnBM) 1
    (fun n x => ?_) (fun x => ?_) ψ
  · have heq : Φ resolventFnBM (A ⟨ψ, hψ⟩) = Φ (1 - Complex.I • resolventFnBM) ψ := by
      refine tendsto_nhds_unique h1 (h2.congr fun n => ?_)
      rw [map_mul, mul_apply_eq_comp]
      rfl
    rw [map_sub, map_one, map_smul, sub_apply, one_apply_eq_self, FunLike.coe_smul,
      Pi.smul_apply] at heq
    rw [map_add, map_smul, heq, sub_add_cancel]
  · change ‖resolventFn x * (truncId n : ℝ → ℂ) x‖ ≤ 1
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left (norm_truncId_le n x) (norm_nonneg _)).trans
      (norm_resolventFn_mul_abs_le x)
  · change Tendsto (fun n => resolventFn x * (truncId n : ℝ → ℂ) x) atTop
      (𝓝 (1 - Complex.I * resolventFn x))
    rw [← ofReal_mul_resolventFn, mul_comm]
    exact (tendsto_truncId x).const_mul _

/-- **Step 1: `Φ((x + i)⁻¹) = (A + i)⁻¹`.**  For `f ∈ H`, `ψ = R f ∈ D(A)` and
`(A + i) ψ = f`, so `Φ(κ) f = ψ` by `apply_resolventFn_addScalar`. -/
theorem map_resolventFn (hΦ : IsSelfAdjointCalculus hA Φ) :
    Φ resolventFnBM = resolvent hA := by
  ext1 f
  have hadd := addScalar_resolventI hA abs_one f
  simp only [Complex.ofReal_one, one_mul, RCLike.I_to_complex] at hadd
  have h := hΦ.apply_resolventFn_addScalar _ (resolventI_mem_domain hA abs_one f)
  rw [hadd] at h
  exact h

end IsSelfAdjointCalculus

/-! ### The compact set `K = {z | |z|² + Im z = 0}` -/

/-- The circle `K = {z | |z|² + Im z = 0}` (centre `-i/2`, radius `1/2`), which contains
`σ((A + i)⁻¹)` and the values of `κ`. -/
def resolventCircle : Set ℂ :=
  {z | ‖z‖ ^ 2 + z.im = 0}

/-- `K` is closed. -/
theorem isClosed_resolventCircle : IsClosed resolventCircle :=
  isClosed_eq ((continuous_norm.pow 2).add Complex.continuous_im) continuous_const

/-- `K` lies in the closed unit disc: `|z|² = -Im z ≤ |z|`. -/
theorem norm_le_one_of_mem_resolventCircle {z : ℂ} (hz : z ∈ resolventCircle) : ‖z‖ ≤ 1 := by
  have hz' : ‖z‖ ^ 2 = -z.im := eq_neg_of_add_eq_zero_left hz
  have h1 : ‖z‖ ^ 2 ≤ ‖z‖ := hz' ▸ (neg_le_abs _).trans (Complex.abs_im_le_norm z)
  nlinarith [norm_nonneg z]

/-- `K` is compact. -/
theorem isCompact_resolventCircle : IsCompact resolventCircle :=
  (isCompact_closedBall (0 : ℂ) 1).of_isClosed_subset isClosed_resolventCircle fun _ hz =>
    mem_closedBall_zero_iff.mpr (norm_le_one_of_mem_resolventCircle hz)

/-- `K` is a compact space. -/
instance : CompactSpace resolventCircle :=
  isCompact_iff_compactSpace.mp isCompact_resolventCircle

/-- `κ(x) ∈ K`. -/
theorem resolventFn_mem_resolventCircle (x : ℝ) : resolventFn x ∈ resolventCircle := by
  change ‖resolventFn x‖ ^ 2 + (resolventFn x).im = 0
  rw [resolventFn, Complex.inv_im, norm_inv, inv_pow, ← Complex.normSq_eq_norm_sq]
  simp only [Complex.add_im, Complex.ofReal_im, Complex.I_im, zero_add]
  ring

/-- `κ` as a map into `K`. -/
def resolventFnCircle (x : ℝ) : resolventCircle :=
  ⟨resolventFn x, resolventFn_mem_resolventCircle x⟩

/-- `κ : ℝ → K` is measurable. -/
theorem measurable_resolventFnCircle : Measurable resolventFnCircle :=
  continuous_resolventFn.measurable.subtype_mk

/-- `ρ(κ(x)) = x` for `ρ(z) = (z⁻¹ - i).re`. -/
theorem resolventCoord_resolventFn (x : ℝ) : resolventCoord (resolventFn x) = x := by
  simp [resolventCoord, resolventFn]

section Spectrum

variable (hA : IsSelfAdjoint A)

/-- The inclusion `σ((A + i)⁻¹) → K` (`normSq_add_im_eq_zero_of_mem_spectrum`). -/
def spectrumToCircle (z : spectrum ℂ (resolvent hA)) : resolventCircle :=
  ⟨z, normSq_add_im_eq_zero_of_mem_spectrum hA z.2⟩

/-- The inclusion `σ(R) → K` is measurable. -/
theorem measurable_spectrumToCircle : Measurable (spectrumToCircle hA) :=
  measurable_subtype_coe.subtype_mk

end Spectrum

/-! ### Uniqueness from continuous functions (monotone class) -/

section MonotoneClass

variable {X : Type*} [MeasurableSpace X]

/-- Property (d) for a `⋆`-homomorphism `Φ` from bounded measurable functions on `X` to `𝓛(H)`:
if `gₙ → g` pointwise and `‖gₙ‖∞ ≤ C`, then `Φ(gₙ) → Φ(g)` strongly. -/
def BoundedLimitsStrong (Φ : boundedMeasurable X →⋆ₐ[ℂ] (H →L[ℂ] H)) : Prop :=
  ∀ (g : ℕ → boundedMeasurable X) (g₀ : boundedMeasurable X) (C : ℝ),
    (∀ n x, ‖(g n : X → ℂ) x‖ ≤ C) →
    (∀ x, Tendsto (fun n => (g n : X → ℂ) x) atTop (𝓝 ((g₀ : X → ℂ) x))) →
    ∀ ψ : H, Tendsto (fun n => Φ (g n) ψ) atTop (𝓝 (Φ g₀ ψ))

/-- **Two `⋆`-homomorphisms with property (d) that agree on bounded continuous functions are
equal**: the functions on which they agree are closed under bounded pointwise limits, so they
are all bounded Borel functions (`IsBoundedLimitClosed.of_continuous`), as in
`IsBorelCalculus.unique`. -/
theorem BoundedLimitsStrong.ext [TopologicalSpace X] [HasOuterApproxClosed X] [BorelSpace X]
    {Φ Ψ : boundedMeasurable X →⋆ₐ[ℂ] (H →L[ℂ] H)} (hΦ : BoundedLimitsStrong Φ)
    (hΨ : BoundedLimitsStrong Ψ)
    (hcont : ∀ g : boundedMeasurable X, Continuous (g : X → ℂ) → Φ g = Ψ g) : Φ = Ψ := by
  let P : (X → ℂ) → Prop := fun f => ∃ hf : f ∈ boundedMeasurable X, Φ ⟨f, hf⟩ = Ψ ⟨f, hf⟩
  have hP : IsBoundedLimitClosed P := by
    refine ⟨⟨zero_mem _, ?_⟩, fun f g ⟨hf, hfe⟩ ⟨hg, hge⟩ => ⟨add_mem hf hg, ?_⟩,
      fun c f ⟨hf, hfe⟩ => ⟨SMulMemClass.smul_mem c hf, ?_⟩, fun f g C hC hlim hPf => ?_⟩
    · exact (map_zero Φ).trans (map_zero Ψ).symm
    · have hsum : (⟨f + g, add_mem hf hg⟩ : boundedMeasurable X) = ⟨f, hf⟩ + ⟨g, hg⟩ := rfl
      rw [hsum, map_add, map_add, hfe, hge]
    · have hsmul : (⟨c • f, SMulMemClass.smul_mem c hf⟩ : boundedMeasurable X) =
          c • ⟨f, hf⟩ := rfl
      rw [hsmul, map_smul, map_smul, hfe]
    · choose hf hfe using hPf
      have hgm : Measurable g :=
        measurable_of_tendsto_metrizable (fun n => (hf n).1) (tendsto_pi_nhds.mpr hlim)
      have hgb : ∀ x, ‖g x‖ ≤ C := fun x =>
        le_of_tendsto (hlim x).norm (Eventually.of_forall fun n => hC n x)
      have hg : g ∈ boundedMeasurable X := ⟨hgm, C, hgb⟩
      refine ⟨hg, ContinuousLinearMap.ext fun ψ => ?_⟩
      have h1 := hΦ (fun n => ⟨f n, hf n⟩) ⟨g, hg⟩ C hC hlim ψ
      have h2 := hΨ (fun n => ⟨f n, hf n⟩) ⟨g, hg⟩ C hC hlim ψ
      simp only [hfe] at h1
      exact tendsto_nhds_unique h1 h2
  have hc : ∀ f : X → ℂ, Continuous f → (∃ C, ∀ x, ‖f x‖ ≤ C) → P f :=
    fun f hf hbd => ⟨continuous_mem_boundedMeasurable hf hbd, hcont _ hf⟩
  ext1 g
  obtain ⟨C, -, hC⟩ := boundedMeasurable.exists_bound g
  obtain ⟨_, h⟩ := hP.of_continuous hc (boundedMeasurable.measurable g) hC
  exact h

end MonotoneClass

/-! ### Steps 2 and 3: the two calculi on `K` -/

/-- `k ↦ Φ(k ∘ κ)`, for bounded Borel `k` on `K`. -/
def resolventFnHom (Φ : boundedMeasurable ℝ →⋆ₐ[ℂ] (H →L[ℂ] H)) :
    boundedMeasurable resolventCircle →⋆ₐ[ℂ] (H →L[ℂ] H) :=
  Φ.comp (boundedMeasurable.comap resolventFnCircle measurable_resolventFnCircle)

/-- `k ↦ (k|σ(R))(R)`, for bounded Borel `k` on `K`, with `R = (A + i)⁻¹`. -/
def resolventCircleCalc (hA : IsSelfAdjoint A) :
    boundedMeasurable resolventCircle →⋆ₐ[ℂ] (H →L[ℂ] H) :=
  (borelCalc (resolvent hA)).comp
    (boundedMeasurable.comap (spectrumToCircle hA) (measurable_spectrumToCircle hA))

/-- `resolventCircleCalc` has property (d), by (d) for the Borel calculus of `R`. -/
theorem boundedLimitsStrong_resolventCircleCalc (hA : IsSelfAdjoint A) :
    BoundedLimitsStrong (resolventCircleCalc hA) := fun _ _ C hC hlim ψ =>
  tendsto_borelCalc_apply _ _ C (fun n _ => hC n _) (fun _ => hlim _) ψ

/-- `‖(k|σ(R))(R)‖ ≤ C` when `|k| ≤ C` on `K`. -/
theorem norm_resolventCircleCalc_le (hA : IsSelfAdjoint A)
    (g : boundedMeasurable resolventCircle) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ z, ‖(g : resolventCircle → ℂ) z‖ ≤ C) : ‖resolventCircleCalc hA g‖ ≤ C :=
  norm_borelCalc_le _ hC0 fun _ => hC _

/-- `z ↦ z` goes to `R` under `resolventCircleCalc`. -/
theorem resolventCircleCalc_X (hA : IsSelfAdjoint A) :
    resolventCircleCalc hA (continuousMapToBoundedMeasurable
      (Polynomial.toContinuousMapOnAlgHom resolventCircle Polynomial.X)) = resolvent hA := by
  have h : boundedMeasurable.comap (spectrumToCircle hA) (measurable_spectrumToCircle hA)
      (continuousMapToBoundedMeasurable
        (Polynomial.toContinuousMapOnAlgHom resolventCircle Polynomial.X)) =
      idBM (resolvent hA) :=
    Subtype.ext (funext fun z => by simp [spectrumToCircle])
  rw [resolventCircleCalc, StarAlgHom.comp_apply, h, borelCalc_id]

namespace IsSelfAdjointCalculus

variable {hA : IsSelfAdjoint A} {Φ : boundedMeasurable ℝ →⋆ₐ[ℂ] (H →L[ℂ] H)}

/-- `resolventFnHom Φ` has property (d), by (d) for `Φ`. -/
theorem boundedLimitsStrong_resolventFnHom (hΦ : IsSelfAdjointCalculus hA Φ) :
    BoundedLimitsStrong (resolventFnHom Φ) := fun _ _ C hC hlim ψ =>
  hΦ.tendsto _ _ C (fun n _ => hC n _) (fun _ => hlim _) ψ

/-- `‖Φ(k ∘ κ)‖ ≤ C` when `|k| ≤ C` on `K`, by (b) for `Φ`. -/
theorem norm_resolventFnHom_le (hΦ : IsSelfAdjointCalculus hA Φ)
    (g : boundedMeasurable resolventCircle) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ z, ‖(g : resolventCircle → ℂ) z‖ ≤ C) : ‖resolventFnHom Φ g‖ ≤ C :=
  hΦ.norm_le _ C hC0 fun _ => hC _

/-- `z ↦ z` goes to `Φ(κ) = R` under `resolventFnHom`. -/
theorem resolventFnHom_X (hΦ : IsSelfAdjointCalculus hA Φ) :
    resolventFnHom Φ (continuousMapToBoundedMeasurable
      (Polynomial.toContinuousMapOnAlgHom resolventCircle Polynomial.X)) = resolvent hA := by
  have h : boundedMeasurable.comap resolventFnCircle measurable_resolventFnCircle
      (continuousMapToBoundedMeasurable
        (Polynomial.toContinuousMapOnAlgHom resolventCircle Polynomial.X)) =
      resolventFnBM :=
    Subtype.ext (funext fun x => by simp [resolventFnCircle])
  rw [resolventFnHom, StarAlgHom.comp_apply, h, hΦ.map_resolventFn]

/-- **Step 2: the two calculi agree on continuous functions on `K`**: both are continuous
`⋆`-homomorphisms on `C(K, ℂ)` sending `z ↦ z` to `R` (Stone–Weierstrass). -/
theorem resolventFnHom_comp_continuousMap (hΦ : IsSelfAdjointCalculus hA Φ) :
    (resolventFnHom Φ).comp continuousMapToBoundedMeasurable =
      (resolventCircleCalc hA).comp continuousMapToBoundedMeasurable := by
  refine ContinuousMap.starAlgHom_ext_map_X ?_ ?_ ?_
  · refine AddMonoidHomClass.continuous_of_bound
      ((resolventFnHom Φ).comp continuousMapToBoundedMeasurable) 1 fun g => ?_
    rw [one_mul]
    exact hΦ.norm_resolventFnHom_le _ (norm_nonneg g) g.norm_coe_le_norm
  · refine AddMonoidHomClass.continuous_of_bound
      ((resolventCircleCalc hA).comp continuousMapToBoundedMeasurable) 1 fun g => ?_
    rw [one_mul]
    exact norm_resolventCircleCalc_le hA _ (norm_nonneg g) g.norm_coe_le_norm
  · rw [StarAlgHom.comp_apply, StarAlgHom.comp_apply, hΦ.resolventFnHom_X,
      resolventCircleCalc_X]

/-- **Step 3: the two calculi agree on bounded Borel functions on `K`** (monotone class). -/
theorem resolventFnHom_eq (hΦ : IsSelfAdjointCalculus hA Φ) :
    resolventFnHom Φ = resolventCircleCalc hA :=
  BoundedLimitsStrong.ext hΦ.boundedLimitsStrong_resolventFnHom
    (boundedLimitsStrong_resolventCircleCalc hA) fun g hg =>
      DFunLike.congr_fun hΦ.resolventFnHom_comp_continuousMap ⟨g, hg⟩

end IsSelfAdjointCalculus

/-! ### Step 4: uniqueness -/

/-- `ρ(z) = (z⁻¹ - i).re` on `K`. -/
def circleToReal (z : resolventCircle) : ℝ :=
  resolventCoord z

/-- `ρ : K → ℝ` is measurable. -/
theorem measurable_circleToReal : Measurable circleToReal :=
  measurable_resolventCoord.comp measurable_subtype_coe

/-- **Uniqueness of the functional calculus of a self-adjoint operator** (Reed–Simon I,
Theorem VIII.5, p. 262): a `⋆`-homomorphism with (b)–(d) is `selfAdjointCalc hA`.  For bounded
Borel `h` on `ℝ`, `k = h ∘ ρ` on `K` has `k ∘ κ = h` and `k|σ(R) = h ∘ ρ`, so
`Φ(h) = Φ(k ∘ κ) = (k|σ(R))(R) = selfAdjointCalc hA h` by `resolventFnHom_eq`. -/
theorem IsSelfAdjointCalculus.eq_selfAdjointCalc {hA : IsSelfAdjoint A}
    {Φ : boundedMeasurable ℝ →⋆ₐ[ℂ] (H →L[ℂ] H)} (hΦ : IsSelfAdjointCalculus hA Φ) :
    Φ = selfAdjointCalc hA := by
  ext1 h
  let k := boundedMeasurable.comap circleToReal measurable_circleToReal h
  have hk : boundedMeasurable.comap resolventFnCircle measurable_resolventFnCircle k = h :=
    Subtype.ext (funext fun x => by
      change (h : ℝ → ℂ) (resolventCoord (resolventFn x)) = (h : ℝ → ℂ) x
      rw [resolventCoord_resolventFn])
  have h1 : resolventFnHom Φ k = Φ h := by
    rw [resolventFnHom, StarAlgHom.comp_apply, hk]
  have h2 : resolventCircleCalc hA k = selfAdjointCalc hA h :=
    rfl
  rw [← h1, ← h2, hΦ.resolventFnHom_eq]

end SpectralTheorem
