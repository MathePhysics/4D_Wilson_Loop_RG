import SpectralTheorem.RealCyclic

/-!
# The multiplication operator form of the spectral theorem on a real Hilbert space

Reed–Simon I, Theorem VIII.4 (pp. 260–261), over `ℝ`: for a self-adjoint `A` on a real Hilbert
space `E` there are a measure space `(M, μ)`, an orthogonal (real unitary) map
`V : E ≃ L²(M, μ; ℝ)` and a real measurable function `f` on `M` such that (a) `ψ ∈ D(A)` if and
only if `f · V ψ ∈ L²(M, μ; ℝ)`, and (b) `V (A ψ) = f · V ψ` for `ψ ∈ D(A)`; `μ` can be taken
finite when `E` is separable.  Also Theorem VII.3 (p. 227) over `ℝ`: a bounded self-adjoint `T`
on `E` is orthogonally equivalent to multiplication by a bounded real measurable function.

Proof sketch.  Apply the complex construction to `B = (A_ℂ + i)⁻¹` (resp. `B = T_ℂ`) on the
complexification `E_ℂ`, with a cyclic decomposition whose vectors are real
(`CyclicDecomposition.exists_real`).  Its unitary `U : E_ℂ ≃ L²(M, μ; ℂ)` commutes with the
conjugations (`CyclicDecomposition.unitary_conj`), so `U` maps the real vectors `ofReal x` onto
the real-valued elements of `L²(M, μ; ℂ)`, which are the classes of the elements of
`L²(M, μ; ℝ)`: `V x = re (U (ofReal x))` is an orthogonal map `E ≃ L²(M, μ; ℝ)`.  The statements
(a) and (b) for `A` follow from those for `A_ℂ` on real vectors, since `A_ℂ (ofReal ψ) =
ofReal (A ψ)` and `ofReal ψ ∈ D(A_ℂ) ↔ ψ ∈ D(A)`.

## Main definitions and results

* `SpectralTheorem.ofRealLp`, `SpectralTheorem.reLp`: `L²(μ; ℝ) → L²(μ; ℂ)` and back.
* `SpectralTheorem.CyclicDecomposition.realUnitary`: the orthogonal map `E ≃ L²(M, μ; ℝ)` of a
  real cyclic decomposition, with `ofRealLp_realUnitary`.
* `SpectralTheorem.exists_orthogonal_mulReal`: Reed–Simon I, Theorem VIII.4 over `ℝ`.
* `SpectralTheorem.exists_orthogonal_mulReal_finite`: the same with a finite measure, for
  separable `E`.
* `SpectralTheorem.exists_orthogonal_mulReal_bounded`: Reed–Simon I, Theorem VII.3 over `ℝ`.
-/

noncomputable section

open scoped InnerProductSpace ENNReal
open MeasureTheory Filter

namespace SpectralTheorem

universe u

open Complexification

/-! ### Real and complex `L²` -/

section RealLp

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

/-- The inclusion `L²(μ; ℝ) → L²(μ; ℂ)`. -/
def ofRealLp : Lp ℝ 2 μ →L[ℝ] Lp ℂ 2 μ :=
  Complex.ofRealCLM.compLpL 2 μ

/-- The real part `L²(μ; ℂ) → L²(μ; ℝ)`. -/
def reLp : Lp ℂ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  Complex.reCLM.compLpL 2 μ

variable {μ}

theorem coeFn_ofRealLp (g : Lp ℝ 2 μ) : (ofRealLp μ g : X → ℂ) =ᵐ[μ] fun x => (g x : ℂ) :=
  ContinuousLinearMap.coeFn_compLpL _ g

theorem coeFn_reLp (f : Lp ℂ 2 μ) : (reLp μ f : X → ℝ) =ᵐ[μ] fun x => (f x).re :=
  ContinuousLinearMap.coeFn_compLpL _ f

@[simp]
theorem reLp_ofRealLp (g : Lp ℝ 2 μ) : reLp μ (ofRealLp μ g) = g := by
  refine Lp.ext ?_
  filter_upwards [coeFn_reLp (ofRealLp μ g), coeFn_ofRealLp g] with x h1 h2
  rw [h1, h2, Complex.ofReal_re]

/-- An element of `L²(μ; ℝ)`, seen in `L²(μ; ℂ)`, is real. -/
@[simp]
theorem conjLp_ofRealLp (g : Lp ℝ 2 μ) : conjLp μ (ofRealLp μ g) = ofRealLp μ g := by
  refine Lp.ext ?_
  filter_upwards [coeFn_conjLp (ofRealLp μ g), coeFn_ofRealLp g] with x h1 h2
  rw [h1, h2, Complex.conj_ofReal]

/-- A real element of `L²(μ; ℂ)` is its real part. -/
theorem ofRealLp_reLp {f : Lp ℂ 2 μ} (hf : conjLp μ f = f) : ofRealLp μ (reLp μ f) = f := by
  refine Lp.ext ?_
  have h := coeFn_conjLp f
  rw [hf] at h
  filter_upwards [coeFn_ofRealLp (reLp μ f), coeFn_reLp f, h] with x h1 h2 h3
  rw [h1, h2]
  exact Complex.conj_eq_iff_re.mp h3.symm

/-- The inclusion `L²(μ; ℝ) → L²(μ; ℂ)` is isometric. -/
@[simp]
theorem norm_ofRealLp (g : Lp ℝ 2 μ) : ‖ofRealLp μ g‖ = ‖g‖ := by
  have h : ∀ᵐ x ∂μ, ‖(ofRealLp μ g : X → ℂ) x‖ = ‖g x‖ := by
    filter_upwards [coeFn_ofRealLp g] with x h1
    rw [h1, Complex.norm_real]
  exact le_antisymm (Lp.norm_le_norm_of_ae_le (h.mono fun x hx => hx.le))
    (Lp.norm_le_norm_of_ae_le (h.mono fun x hx => hx.ge))

theorem ofRealLp_injective : Function.Injective (ofRealLp μ) := fun g h e => by
  rw [← reLp_ofRealLp g, e, reLp_ofRealLp]

end RealLp

/-! ### The orthogonal map of a real cyclic decomposition -/

section RealUnitary

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {B : Complexification E →L[ℂ] Complexification E} [hB : IsStarNormal B]

namespace CyclicDecomposition

variable (D : CyclicDecomposition B) (hBc : IsConjAdjoint B)
  (hD : ∀ ψ ∈ D.vectors, conj ψ = ψ)

include hBc hD in
/-- `U (ofReal x)` is real: `conj (U (ofReal x)) = U (conj (ofReal x)) = U (ofReal x)`. -/
theorem conjLp_unitary_ofReal (x : E) :
    conjLp _ (D.unitary (ofReal x)) = D.unitary (ofReal x) := by
  rw [← D.unitary_conj hBc hD, conj_ofReal]

/-- The isometry `x ↦ re (U (ofReal x))` from `E` to `L²(Σ_ψ σ(B); ℝ)`. -/
def realIsometry : E →ₗᵢ[ℝ] Lp ℝ 2 D.measure where
  toFun x := reLp _ (D.unitary (ofReal x))
  map_add' x y := by rw [map_add, map_add, map_add]
  map_smul' r x := by
    rw [RingHom.id_apply, ← map_smul (reLp D.measure), map_smul ofReal,
      ← algebraMap_smul ℂ r (ofReal x), LinearIsometryEquiv.map_smul, algebraMap_smul]
  norm_map' x := by
    change ‖reLp _ (D.unitary (ofReal x))‖ = ‖x‖
    rw [← norm_ofRealLp, ofRealLp_reLp (D.conjLp_unitary_ofReal hBc hD x),
      LinearIsometryEquiv.norm_map, norm_ofReal]

theorem ofRealLp_realIsometry (x : E) :
    ofRealLp _ (D.realIsometry hBc hD x) = D.unitary (ofReal x) :=
  ofRealLp_reLp (D.conjLp_unitary_ofReal hBc hD x)

/-- Every element of `L²(Σ_ψ σ(B); ℝ)` is `re (U (ofReal x))`: its preimage `z` under `U` is
fixed by the conjugation, because `U` commutes with the conjugations. -/
theorem realIsometry_surjective : Function.Surjective (D.realIsometry hBc hD) := by
  intro g
  set z := D.unitary.symm (ofRealLp _ g) with hz
  have hc : conj z = z := by
    apply D.unitary.injective
    rw [D.unitary_conj hBc hD, hz, LinearIsometryEquiv.apply_symm_apply, conjLp_ofRealLp]
  obtain ⟨x, hx⟩ := conj_eq_self_iff_exists.mp hc
  refine ⟨x, ofRealLp_injective ?_⟩
  rw [ofRealLp_realIsometry, hx, hz, LinearIsometryEquiv.apply_symm_apply]

/-- **The orthogonal map `V : E ≃ L²(Σ_ψ σ(B); ℝ)`** of a real cyclic decomposition,
`V x = re (U (ofReal x))`. -/
def realUnitary : E ≃ₗᵢ[ℝ] Lp ℝ 2 D.measure :=
  LinearIsometryEquiv.ofSurjective (D.realIsometry hBc hD) (D.realIsometry_surjective hBc hD)

/-- `V x`, seen in `L²(Σ_ψ σ(B); ℂ)`, is `U (ofReal x)`. -/
theorem ofRealLp_realUnitary (x : E) :
    ofRealLp _ (D.realUnitary hBc hD x) = D.unitary (ofReal x) :=
  D.ofRealLp_realIsometry hBc hD x

/-- `U (ofReal x) = V x` almost everywhere. -/
theorem coeFn_unitary_ofReal (x : E) :
    (D.unitary (ofReal x) : D.Space → ℂ) =ᵐ[D.measure]
      fun p => ((D.realUnitary hBc hD x p : ℝ) : ℂ) := by
  rw [← D.ofRealLp_realUnitary hBc hD x]
  exact coeFn_ofRealLp _

end CyclicDecomposition

end RealUnitary

/-! ### The unbounded case: Theorem VIII.4 over `ℝ` -/

section Unbounded

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {A : E →ₗ.[ℝ] E} {hAc : IsSelfAdjoint (complexifyPMap A)}

namespace CyclicDecomposition

variable (D : CyclicDecomposition (resolvent hAc)) (hD : ∀ ψ ∈ D.vectors, conj ψ = ψ)

/-- `f · U (ofReal ψ) ∈ L²(μ; ℂ)` if and only if `f · V ψ ∈ L²(μ; ℝ)`: the two functions have
the same norm almost everywhere. -/
theorem memLp_realCoord_mul_iff (ψ : E) :
    MemLp (fun p => (D.realCoord p : ℂ) * D.unitary (ofReal ψ) p) 2 D.measure ↔
      MemLp (fun p => D.realCoord p * D.realUnitary (isConjAdjoint_resolvent hAc) hD ψ p) 2
        D.measure := by
  have hn : ∀ᵐ p ∂D.measure, ‖(D.realCoord p : ℂ) * D.unitary (ofReal ψ) p‖ =
      ‖D.realCoord p * D.realUnitary (isConjAdjoint_resolvent hAc) hD ψ p‖ := by
    filter_upwards [D.coeFn_unitary_ofReal (isConjAdjoint_resolvent hAc) hD ψ] with p hp
    rw [hp, ← Complex.ofReal_mul, Complex.norm_real]
  constructor
  · intro h
    exact h.congr_norm
      (D.measurable_realCoord.aestronglyMeasurable.mul (Lp.aestronglyMeasurable _)) hn
  · intro h
    exact h.congr_norm
      ((Complex.measurable_ofReal.comp D.measurable_realCoord).aestronglyMeasurable.mul
        (Lp.aestronglyMeasurable _)) (hn.mono fun p hp => hp.symm)

/-- **Reed–Simon I, Theorem VIII.4 (a) over `ℝ`**: `ψ ∈ D(A)` if and only if `f · V ψ ∈ L²`. -/
theorem mem_domain_iff_real (ψ : E) :
    ψ ∈ A.domain ↔
      MemLp (fun p => D.realCoord p * D.realUnitary (isConjAdjoint_resolvent hAc) hD ψ p) 2
        D.measure := by
  rw [← D.memLp_realCoord_mul_iff hD ψ]
  have h := D.mem_domain_iff (ofReal ψ)
  rw [mem_complexifyPMap_domain, ofReal_re, ofReal_im, mem_mulPMap_domain] at h
  exact (and_iff_left A.domain.zero_mem).symm.trans h

/-- **Reed–Simon I, Theorem VIII.4 (b) over `ℝ`**: `V (A ψ) = f · V ψ` almost everywhere, for
`ψ ∈ D(A)`. -/
theorem coeFn_realUnitary_selfAdjoint (ψ : E) (hψ : ψ ∈ A.domain) :
    (D.realUnitary (isConjAdjoint_resolvent hAc) hD (A ⟨ψ, hψ⟩) : D.Space → ℝ) =ᵐ[D.measure]
      fun p => D.realCoord p * D.realUnitary (isConjAdjoint_resolvent hAc) hD ψ p := by
  have h := D.coeFn_unitary_selfAdjoint (ofReal ψ) (ofReal_mem_complexifyPMap_domain hψ)
  rw [complexifyPMap_ofReal hψ] at h
  filter_upwards [h, D.coeFn_unitary_ofReal (isConjAdjoint_resolvent hAc) hD (A ⟨ψ, hψ⟩),
    D.coeFn_unitary_ofReal (isConjAdjoint_resolvent hAc) hD ψ] with p h1 h2 h3
  rw [h2, h3, ← Complex.ofReal_mul] at h1
  exact Complex.ofReal_injective h1

end CyclicDecomposition

/-- **The spectral theorem for unbounded self-adjoint operators on a real Hilbert space,
multiplication operator form** (Reed–Simon I, Theorem VIII.4, pp. 260–261, over `ℝ`): there are
a measure space `(M, μ)`, an orthogonal map `V : E ≃ L²(M, μ; ℝ)` and a measurable function
`f : M → ℝ` such that (a) `ψ ∈ D(A) ↔ f · V ψ ∈ L²(M, μ; ℝ)`, and (b) `V (A ψ) = f · V ψ` for
`ψ ∈ D(A)`.  This is the complex theorem for `A_ℂ`, with a cyclic decomposition of
`(A_ℂ + i)⁻¹` by real vectors, restricted to the real vectors. -/
theorem exists_orthogonal_mulReal (hA : IsSelfAdjoint A) :
    ∃ (M : Type u) (_ : MeasurableSpace M) (μ : Measure M) (V : E ≃ₗᵢ[ℝ] Lp ℝ 2 μ)
      (f : M → ℝ), Measurable f ∧
      (∀ ψ : E, ψ ∈ A.domain ↔ MemLp (fun m => f m * V ψ m) 2 μ) ∧
      ∀ (ψ : E) (hψ : ψ ∈ A.domain), (V (A ⟨ψ, hψ⟩) : M → ℝ) =ᵐ[μ] fun m => f m * V ψ m := by
  obtain ⟨D, hD⟩ := CyclicDecomposition.exists_real (isConjAdjoint_resolvent hA.complexifyPMap)
  exact ⟨D.Space, inferInstance, D.measure, D.realUnitary _ hD, D.realCoord,
    D.measurable_realCoord, D.mem_domain_iff_real hD, D.coeFn_realUnitary_selfAdjoint hD⟩

end Unbounded

/-! ### A finite measure for separable `E` -/

section Finite

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The complexification of a separable space is separable: it is the image of `E × E` under
the continuous surjection `(x, y) ↦ x + i y`. -/
instance Complexification.separableSpace [TopologicalSpace.SeparableSpace E] :
    TopologicalSpace.SeparableSpace (Complexification E) := by
  have hc : Continuous fun p : E × E => ofReal p.1 + Complex.I • ofReal p.2 :=
    (ofReal.continuous.comp continuous_fst).add
      ((ofReal.continuous.comp continuous_snd).const_smul Complex.I)
  have hs : Function.Surjective fun p : E × E => ofReal p.1 + Complex.I • ofReal p.2 :=
    fun z => ⟨(z.re, z.im), ofReal_add_I_smul z⟩
  exact hs.denseRange.separableSpace hc

variable [CompleteSpace E] [TopologicalSpace.SeparableSpace E]
variable {B : Complexification E →L[ℂ] Complexification E} [hB : IsStarNormal B]

/-- **A real cyclic decomposition with a finite measure** for separable `E`: rescale the nonzero
vectors of a real cyclic decomposition by real positive scalars, as in
`CyclicDecomposition.exists_isFiniteMeasure` (Reed–Simon I, proof of the Corollary to Theorem
VII.3, p. 227); a real multiple of a real vector is real. -/
theorem CyclicDecomposition.exists_real_isFiniteMeasure (hBc : IsConjAdjoint B) :
    ∃ D : CyclicDecomposition B, (∀ ψ ∈ D.vectors, conj ψ = ψ) ∧ IsFiniteMeasure D.measure := by
  obtain ⟨D, hD⟩ := CyclicDecomposition.exists_real hBc
  let _ : Encodable D.nonzeroVectors := D.countable_nonzeroVectors.toEncodable
  obtain ⟨r, hr0, hr1, hr⟩ : ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ ENNReal.ofReal r = 2⁻¹ :=
    ⟨2⁻¹, by norm_num, by norm_num, by -- totalisation-audit: allow inverse of 2 ≠ 0
      rw [ENNReal.ofReal_inv_of_pos two_pos, ENNReal.ofReal_ofNat]⟩
  have hpos : ∀ ψ : D.nonzeroVectors, 0 < ‖(ψ : Complexification E)‖ := fun ψ =>
    norm_pos_iff.mpr ψ.2.2
  set c : D.nonzeroVectors → ℂ := fun ψ =>
    ((r ^ Encodable.encode ψ / ‖ψ.1‖ : ℝ) : ℂ) with hc_def -- totalisation-audit: allow ‖ψ‖ > 0
  have hc : ∀ ψ, c ψ ≠ 0 := fun ψ =>
    Complex.ofReal_ne_zero.mpr (div_ne_zero (pow_ne_zero _ hr0.ne') (hpos ψ).ne')
  have hnorm : ∀ ψ, ‖c ψ • (ψ : Complexification E)‖ = r ^ Encodable.encode ψ := fun ψ => by
    rw [norm_smul, hc_def, Complex.norm_real, Real.norm_of_nonneg (by positivity),
      div_mul_cancel₀ _ (hpos ψ).ne']
  refine ⟨D.rescale c hc, ?_, ⟨?_⟩⟩
  · rintro _ ⟨ψ, rfl⟩
    change conj (c ψ • (ψ : Complexification E)) = c ψ • (ψ : Complexification E)
    rw [LinearIsometryEquiv.map_smulₛₗ, hD ψ ψ.2.1]
    simp only [hc_def, Complex.conj_ofReal]
  · rw [D.rescale_measure_univ c hc]
    refine lt_of_le_of_lt (ENNReal.tsum_le_tsum fun ψ => ?_)
      (lt_of_le_of_lt ENNReal.tsum_geometric_two_encode_le_two ENNReal.ofNat_lt_top)
    rw [hnorm, ← hr, ← ENNReal.ofReal_pow hr0.le]
    exact ENNReal.ofReal_le_ofReal
      (pow_le_of_le_one (by positivity) (pow_le_one₀ hr0.le hr1) two_ne_zero)

variable {A : E →ₗ.[ℝ] E}

/-- **Reed–Simon I, Theorem VIII.4 over `ℝ`, with a finite measure** for separable `E`:
`exists_orthogonal_mulReal` with, in addition, `μ` finite. -/
theorem exists_orthogonal_mulReal_finite (hA : IsSelfAdjoint A) :
    ∃ (M : Type u) (_ : MeasurableSpace M) (μ : Measure M) (_ : IsFiniteMeasure μ)
      (V : E ≃ₗᵢ[ℝ] Lp ℝ 2 μ) (f : M → ℝ), Measurable f ∧
      (∀ ψ : E, ψ ∈ A.domain ↔ MemLp (fun m => f m * V ψ m) 2 μ) ∧
      ∀ (ψ : E) (hψ : ψ ∈ A.domain), (V (A ⟨ψ, hψ⟩) : M → ℝ) =ᵐ[μ] fun m => f m * V ψ m := by
  obtain ⟨D, hD, hfin⟩ :=
    CyclicDecomposition.exists_real_isFiniteMeasure (isConjAdjoint_resolvent hA.complexifyPMap)
  exact ⟨D.Space, inferInstance, D.measure, hfin, D.realUnitary _ hD, D.realCoord,
    D.measurable_realCoord, D.mem_domain_iff_real hD, D.coeFn_realUnitary_selfAdjoint hD⟩

end Finite

/-! ### The bounded case: Theorem VII.3 over `ℝ` -/

section Bounded

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {T : E →L[ℝ] E}

namespace CyclicDecomposition

variable [IsStarNormal (complexifyCLM T)] (D : CyclicDecomposition (complexifyCLM T))

/-- The real part of the spectral variable is measurable. -/
theorem measurable_re_coord : Measurable fun p : D.Space => (D.coord p).re :=
  Complex.measurable_re.comp (measurable_sigma_iff.mpr fun _ => measurable_subtype_coe)

/-- The real part of the spectral variable is bounded by `‖T‖`, since `σ(T_ℂ)` lies in the
closed disc of radius `‖T_ℂ‖ = ‖T‖`. -/
theorem abs_re_coord_le (p : D.Space) : |(D.coord p).re| ≤ ‖T‖ := by
  have h1 := spectrum.subset_closedBall_norm_mul (𝕜 := ℂ) (complexifyCLM T) p.2.2
  rw [Metric.mem_closedBall, dist_zero_right] at h1
  calc |(D.coord p).re| ≤ ‖D.coord p‖ := Complex.abs_re_le_norm _
    _ ≤ ‖complexifyCLM T‖ * ‖(1 : Complexification E →L[ℂ] Complexification E)‖ := h1
    _ ≤ ‖complexifyCLM T‖ * 1 :=
        mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (norm_nonneg _)
    _ = ‖T‖ := by rw [mul_one, norm_complexifyCLM]

/-- **Reed–Simon I, Theorem VII.3 over `ℝ`**: `V (T ψ) = re λ · V ψ` almost everywhere.  From
`U T_ℂ U⁻¹ = λ` on real vectors, and `λ` is real on `σ(T_ℂ) ⊆ ℝ`. -/
theorem coeFn_realUnitary_T (hT : IsSelfAdjoint T) (hD : ∀ ψ ∈ D.vectors, conj ψ = ψ) (ψ : E) :
    (D.realUnitary (isConjAdjoint_complexifyCLM hT) hD (T ψ) : D.Space → ℝ) =ᵐ[D.measure]
      fun p => (D.coord p).re * D.realUnitary (isConjAdjoint_complexifyCLM hT) hD ψ p := by
  have h := D.unitary_apply_T (ofReal ψ)
  rw [complexifyCLM_ofReal] at h
  have h' := coeFn_mulL (μ := D.measure) D.memLp_top_coord (D.unitary (ofReal ψ))
  rw [← h] at h'
  filter_upwards [h', D.coeFn_unitary_ofReal (isConjAdjoint_complexifyCLM hT) hD (T ψ),
    D.coeFn_unitary_ofReal (isConjAdjoint_complexifyCLM hT) hD ψ] with p h1 h2 h3
  rw [h2, h3] at h1
  have hre : D.coord p = ((D.coord p).re : ℂ) :=
    (isSelfAdjoint_complexifyCLM_iff.mpr hT).mem_spectrum_eq_re p.2.2
  rw [hre, ← Complex.ofReal_mul] at h1
  exact Complex.ofReal_injective h1

end CyclicDecomposition

/-- **The spectral theorem for bounded self-adjoint operators on a real Hilbert space,
multiplication operator form** (Reed–Simon I, Theorem VII.3, p. 227, over `ℝ`): there are a
measure space `(M, μ)`, an orthogonal map `V : E ≃ L²(M, μ; ℝ)` and a measurable function
`F : M → ℝ` with `|F| ≤ ‖T‖` such that `V T V⁻¹` is multiplication by `F`. -/
theorem exists_orthogonal_mulReal_bounded (hT : IsSelfAdjoint T) :
    ∃ (M : Type u) (_ : MeasurableSpace M) (μ : Measure M) (V : E ≃ₗᵢ[ℝ] Lp ℝ 2 μ)
      (F : M → ℝ), Measurable F ∧ (∀ m, |F m| ≤ ‖T‖) ∧
      ∀ ψ : E, (V (T ψ) : M → ℝ) =ᵐ[μ] fun m => F m * V ψ m := by
  have : IsStarNormal (complexifyCLM T) := (isSelfAdjoint_complexifyCLM_iff.mpr hT).isStarNormal
  obtain ⟨D, hD⟩ := CyclicDecomposition.exists_real (isConjAdjoint_complexifyCLM hT)
  exact ⟨D.Space, inferInstance, D.measure, D.realUnitary _ hD, fun p => (D.coord p).re,
    D.measurable_re_coord, D.abs_re_coord_le, D.coeFn_realUnitary_T hT hD⟩

/-- **Reed–Simon I, Theorem VII.3 and its Corollary over `ℝ`, with a finite measure** for
separable `E`: `exists_orthogonal_mulReal_bounded` with, in addition, `μ` finite. -/
theorem exists_orthogonal_mulReal_bounded_finite [TopologicalSpace.SeparableSpace E]
    (hT : IsSelfAdjoint T) :
    ∃ (M : Type u) (_ : MeasurableSpace M) (μ : Measure M) (_ : IsFiniteMeasure μ)
      (V : E ≃ₗᵢ[ℝ] Lp ℝ 2 μ) (F : M → ℝ), Measurable F ∧ (∀ m, |F m| ≤ ‖T‖) ∧
      ∀ ψ : E, (V (T ψ) : M → ℝ) =ᵐ[μ] fun m => F m * V ψ m := by
  have : IsStarNormal (complexifyCLM T) := (isSelfAdjoint_complexifyCLM_iff.mpr hT).isStarNormal
  obtain ⟨D, hD, hfin⟩ :=
    CyclicDecomposition.exists_real_isFiniteMeasure (isConjAdjoint_complexifyCLM hT)
  exact ⟨D.Space, inferInstance, D.measure, hfin, D.realUnitary _ hD, fun p => (D.coord p).re,
    D.measurable_re_coord, D.abs_re_coord_le, D.coeFn_realUnitary_T hT hD⟩

end Bounded

end SpectralTheorem
