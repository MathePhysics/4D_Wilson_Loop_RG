import SpectralTheorem.MultiplicationForm
import SpectralTheorem.BoundedMeasurable
import SpectralTheorem.MonotoneClass

/-!
# The Borel functional calculus of a bounded normal operator

**Reed–Simon I, Theorem VII.2 (spectral theorem, functional calculus form), p. 225.**  Let `A` be
a bounded self-adjoint operator.  There is a unique map `φ̂ : 𝓑(ℝ) → 𝓛(H)` such that
(a) `φ̂` is an algebraic `⋆`-homomorphism; (b) `‖φ̂(f)‖ ≤ ‖f‖∞`; (c) `φ̂(x) = A`; (d) if
`fₙ(x) → f(x)` for each `x` and `‖fₙ‖∞` is bounded, then `φ̂(fₙ) → φ̂(f)` strongly.  Moreover
(e)–(g) hold (proved in `SpectralTheorem.BorelCalculusProperties`).

Here `T` is a bounded **normal** operator and the functions are bounded Borel functions on
`σ(T)` (`boundedMeasurable (spectrum ℂ T)`); only the values on `σ(T)` matter, and this is how
(c) makes sense for the unbounded function `x`.  For a cyclic decomposition `D` with spectral
representation `U : H ≃ L²(Σ_ψ σ(T), Σ_ψ μ_ψ)` (`SpectralTheorem.MultiplicationForm`),
`g(T) = U⁻¹ M_{g(λ)} U` (`CyclicDecomposition.borelHom`); (a) holds because multiplication and
conjugation by a unitary are `⋆`-homomorphisms, and (b)–(d) are the corresponding properties of
multiplication operators.  Uniqueness (`IsBorelCalculus.unique`): two such maps agree on
continuous functions by the uniqueness of the continuous functional calculus, and the functions
on which they agree are closed under bounded pointwise limits by (d), so they agree on all bounded
Borel functions (`SpectralTheorem.MonotoneClass`).  In particular `g(T)` does not depend on the
decomposition, and extends mathlib's continuous functional calculus `cfcHom`.

## Main definitions and results

* `SpectralTheorem.IsBorelCalculus T Φ`: properties (b)–(d) for a `⋆`-homomorphism `Φ`.
* `SpectralTheorem.CyclicDecomposition.borelHom D`: `g ↦ U⁻¹ M_{g(λ)} U`.
* `SpectralTheorem.IsBorelCalculus.unique`: uniqueness.
* `SpectralTheorem.borelCalc T`: **the Borel functional calculus** of `T`.
* `SpectralTheorem.existsUnique_isBorelCalculus`: **Reed–Simon I, Theorem VII.2** (a)–(d).
* `SpectralTheorem.borelCalc_continuousMap`: `borelCalc` extends `cfcHom`.
-/

noncomputable section

open scoped InnerProductSpace ENNReal Topology
open MeasureTheory Filter

namespace SpectralTheorem

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {T : H →L[ℂ] H}

variable (T) in
/-- The function `λ ↦ λ` on `σ(T)`, as a bounded measurable function. -/
def idBM : boundedMeasurable (spectrum ℂ T) :=
  continuousMapToBoundedMeasurable ((ContinuousMap.id ℂ).restrict (spectrum ℂ T))

@[simp]
theorem coe_idBM : ((idBM T : boundedMeasurable (spectrum ℂ T)) : spectrum ℂ T → ℂ) =
    Subtype.val :=
  rfl

variable [hT : IsStarNormal T]

variable (T) in
/-- **A Borel functional calculus** for `T` (Reed–Simon I, Theorem VII.2 (b)–(d), p. 225): a
`⋆`-homomorphism `Φ` from bounded Borel functions on `σ(T)` to `𝓛(H)` with (b)
`‖Φ(g)‖ ≤ ‖g‖∞`, (c) `Φ(λ ↦ λ) = T`, and (d) `Φ(gₙ) → Φ(g)` strongly when `gₙ → g` pointwise
with `‖gₙ‖∞` bounded. -/
structure IsBorelCalculus (Φ : boundedMeasurable (spectrum ℂ T) →⋆ₐ[ℂ] (H →L[ℂ] H)) : Prop where
  norm_le : ∀ (g : boundedMeasurable (spectrum ℂ T)) (C : ℝ), 0 ≤ C →
    (∀ x, ‖(g : spectrum ℂ T → ℂ) x‖ ≤ C) → ‖Φ g‖ ≤ C
  map_id : Φ (idBM T) = T
  tendsto : ∀ (g : ℕ → boundedMeasurable (spectrum ℂ T)) (g₀ : boundedMeasurable (spectrum ℂ T))
    (C : ℝ), (∀ n x, ‖(g n : spectrum ℂ T → ℂ) x‖ ≤ C) →
    (∀ x, Tendsto (fun n => (g n : spectrum ℂ T → ℂ) x) atTop
      (𝓝 ((g₀ : spectrum ℂ T → ℂ) x))) →
    ∀ h : H, Tendsto (fun n => Φ (g n) h) atTop (𝓝 (Φ g₀ h))

namespace CyclicDecomposition

variable (D : CyclicDecomposition T)

theorem measurable_snd : Measurable fun p : D.Space => p.2 :=
  measurable_sigma_iff.mpr fun _ => measurable_id

/-- **The Borel functional calculus built from a cyclic decomposition**:
`g(T) = U⁻¹ M_{g(λ)} U`. -/
def borelHom : boundedMeasurable (spectrum ℂ T) →⋆ₐ[ℂ] (H →L[ℂ] H) :=
  D.unitary.symm.conjStarAlgEquiv.toStarAlgHom.comp (mulHom D.measure D.measurable_snd)

theorem borelHom_apply (g : boundedMeasurable (spectrum ℂ T)) (h : H) :
    D.borelHom g h = D.unitary.symm (mulL ((g : spectrum ℂ T → ℂ) ∘ fun p : D.Space => p.2)
      (memLp_top_comp D.measure D.measurable_snd g) (D.unitary h)) :=
  rfl

/-- `borelHom` extends the continuous functional calculus: `g(T) = cfcHom g` for continuous
`g`, by `unitary_cfcHom`. -/
theorem borelHom_continuousMap (g : C(spectrum ℂ T, ℂ)) :
    D.borelHom (continuousMapToBoundedMeasurable g) = cfcHom hT g := by
  ext1 h
  rw [borelHom_apply, ← D.unitary.symm_apply_apply (cfcHom hT g h), D.unitary_cfcHom g h]
  rfl

/-- (c) `borelHom (λ ↦ λ) = T`. -/
theorem borelHom_id : D.borelHom (idBM T) = T := by
  rw [idBM, borelHom_continuousMap, cfcHom_id]

/-- (b) `‖g(T) h‖ ≤ C ‖h‖` when `‖g‖ ≤ C` on `σ(T)`. -/
theorem norm_borelHom_apply_le (g : boundedMeasurable (spectrum ℂ T)) {C : ℝ}
    (hC : ∀ x, ‖(g : spectrum ℂ T → ℂ) x‖ ≤ C) (h : H) : ‖D.borelHom g h‖ ≤ C * ‖h‖ := by
  have hC' : ∀ᵐ p ∂D.measure, ‖((g : spectrum ℂ T → ℂ) ∘ fun p : D.Space => p.2) p‖ ≤ C :=
    Eventually.of_forall fun p => hC p.2
  have h1 := norm_mulL_apply_le (μ := D.measure) (memLp_top_comp D.measure D.measurable_snd g)
    hC' (D.unitary h)
  rw [LinearIsometryEquiv.norm_map] at h1
  rw [borelHom_apply, LinearIsometryEquiv.norm_map]
  exact h1

/-- (d) Bounded pointwise convergence gives strong convergence. -/
theorem tendsto_borelHom_apply (g : ℕ → boundedMeasurable (spectrum ℂ T))
    (g₀ : boundedMeasurable (spectrum ℂ T)) (C : ℝ)
    (hC : ∀ n x, ‖(g n : spectrum ℂ T → ℂ) x‖ ≤ C)
    (hlim : ∀ x, Tendsto (fun n => (g n : spectrum ℂ T → ℂ) x) atTop
      (𝓝 ((g₀ : spectrum ℂ T → ℂ) x))) (h : H) :
    Tendsto (fun n => D.borelHom (g n) h) atTop (𝓝 (D.borelHom g₀ h)) := by
  have hC' : ∀ n, ∀ᵐ p ∂D.measure,
      ‖((g n : spectrum ℂ T → ℂ) ∘ fun p : D.Space => p.2) p‖ ≤ C :=
    fun n => Eventually.of_forall fun p => hC n p.2
  have hlim' : ∀ᵐ p ∂D.measure,
      Tendsto (fun n => ((g n : spectrum ℂ T → ℂ) ∘ fun p : D.Space => p.2) p) atTop
        (𝓝 (((g₀ : spectrum ℂ T → ℂ) ∘ fun p : D.Space => p.2) p)) :=
    Eventually.of_forall fun p => hlim p.2
  have h1 := tendsto_mulL_apply (μ := D.measure)
    (fun n => memLp_top_comp D.measure D.measurable_snd (g n))
    (memLp_top_comp D.measure D.measurable_snd g₀) hC' hlim' (D.unitary h)
  exact (D.unitary.symm.continuous.tendsto _).comp h1

/-- `borelHom D` is a Borel functional calculus. -/
theorem isBorelCalculus : IsBorelCalculus T D.borelHom where
  norm_le g _C hC0 hC := ContinuousLinearMap.opNorm_le_bound _ hC0 (D.norm_borelHom_apply_le g hC)
  map_id := D.borelHom_id
  tendsto := D.tendsto_borelHom_apply

end CyclicDecomposition

namespace IsBorelCalculus

variable {Φ Ψ : boundedMeasurable (spectrum ℂ T) →⋆ₐ[ℂ] (H →L[ℂ] H)}

/-- A Borel calculus is continuous on continuous functions, hence equals the continuous
functional calculus there (mathlib's uniqueness of `cfcHom`). -/
theorem comp_continuousMap (hΦ : IsBorelCalculus T Φ) :
    Φ.comp continuousMapToBoundedMeasurable = cfcHom hT := by
  refine (cfcHom_eq_of_continuous_of_map_id hT _ ?_ hΦ.map_id).symm
  refine AddMonoidHomClass.continuous_of_bound (Φ.comp continuousMapToBoundedMeasurable) 1
    fun g => ?_
  rw [one_mul]
  exact hΦ.norm_le _ ‖g‖ (norm_nonneg g) g.norm_coe_le_norm

/-- A Borel calculus extends the continuous functional calculus. -/
theorem apply_continuousMap (hΦ : IsBorelCalculus T Φ) (g : C(spectrum ℂ T, ℂ)) :
    Φ (continuousMapToBoundedMeasurable g) = cfcHom hT g :=
  DFunLike.congr_fun hΦ.comp_continuousMap g

/-- **Uniqueness of the Borel functional calculus** (Reed–Simon I, Theorem VII.2, p. 225).  The
bounded Borel functions on which two calculi agree contain the continuous ones
(`apply_continuousMap`) and are closed under bounded pointwise limits (property (d)), so they are
all bounded Borel functions (`IsBoundedLimitClosed.of_continuous`). -/
theorem unique (hΦ : IsBorelCalculus T Φ) (hΨ : IsBorelCalculus T Ψ) : Φ = Ψ := by
  let P : (spectrum ℂ T → ℂ) → Prop := fun f =>
    ∃ hf : f ∈ boundedMeasurable (spectrum ℂ T), Φ ⟨f, hf⟩ = Ψ ⟨f, hf⟩
  have hP : IsBoundedLimitClosed P := by
    refine ⟨⟨zero_mem _, ?_⟩, fun f g ⟨hf, hfe⟩ ⟨hg, hge⟩ => ⟨add_mem hf hg, ?_⟩,
      fun c f ⟨hf, hfe⟩ => ⟨SMulMemClass.smul_mem c hf, ?_⟩, fun f g C hC hlim hPf => ?_⟩
    · exact (map_zero Φ).trans (map_zero Ψ).symm
    · have hsum : (⟨f + g, add_mem hf hg⟩ : boundedMeasurable (spectrum ℂ T)) =
          ⟨f, hf⟩ + ⟨g, hg⟩ := rfl
      rw [hsum, map_add, map_add, hfe, hge]
    · have hsmul : (⟨c • f, SMulMemClass.smul_mem c hf⟩ : boundedMeasurable (spectrum ℂ T)) =
          c • ⟨f, hf⟩ := rfl
      rw [hsmul, map_smul, map_smul, hfe]
    · choose hf hfe using hPf
      have hgm : Measurable g :=
        measurable_of_tendsto_metrizable (fun n => (hf n).1) (tendsto_pi_nhds.mpr hlim)
      have hgb : ∀ x, ‖g x‖ ≤ C := fun x =>
        le_of_tendsto (hlim x).norm (Eventually.of_forall fun n => hC n x)
      have hg : g ∈ boundedMeasurable (spectrum ℂ T) := ⟨hgm, C, hgb⟩
      refine ⟨hg, ContinuousLinearMap.ext fun h => ?_⟩
      have h1 := hΦ.tendsto (fun n => ⟨f n, hf n⟩) ⟨g, hg⟩ C hC hlim h
      have h2 := hΨ.tendsto (fun n => ⟨f n, hf n⟩) ⟨g, hg⟩ C hC hlim h
      simp only [hfe] at h1
      exact tendsto_nhds_unique h1 h2
  have hcont : ∀ f : spectrum ℂ T → ℂ, Continuous f → (∃ C, ∀ x, ‖f x‖ ≤ C) → P f :=
    fun f hf hbd => ⟨continuous_mem_boundedMeasurable hf hbd,
      (hΦ.apply_continuousMap ⟨f, hf⟩).trans (hΨ.apply_continuousMap ⟨f, hf⟩).symm⟩
  ext1 g
  obtain ⟨C, -, hC⟩ := boundedMeasurable.exists_bound g
  obtain ⟨_, h⟩ := hP.of_continuous hcont (boundedMeasurable.measurable g) hC
  exact h

end IsBorelCalculus

variable (T) in
/-- **The Borel functional calculus** of a bounded normal operator `T`: `g ↦ g(T)` for bounded
Borel functions `g` on `σ(T)`.  It is built from some cyclic decomposition, and by uniqueness it
does not depend on the choice (`borelCalc_eq_borelHom`). -/
def borelCalc : boundedMeasurable (spectrum ℂ T) →⋆ₐ[ℂ] (H →L[ℂ] H) :=
  (CyclicDecomposition.nonempty T).some.borelHom

/-- `borelCalc T` is a Borel functional calculus. -/
theorem isBorelCalculus_borelCalc : IsBorelCalculus T (borelCalc T) :=
  (CyclicDecomposition.nonempty T).some.isBorelCalculus

/-- Every Borel functional calculus is `borelCalc T`. -/
theorem IsBorelCalculus.eq_borelCalc {Φ : boundedMeasurable (spectrum ℂ T) →⋆ₐ[ℂ] (H →L[ℂ] H)}
    (hΦ : IsBorelCalculus T Φ) : Φ = borelCalc T :=
  hΦ.unique isBorelCalculus_borelCalc

/-- `borelCalc T` is `g ↦ U⁻¹ M_{g(λ)} U` for **every** cyclic decomposition. -/
theorem borelCalc_eq_borelHom (D : CyclicDecomposition T) : borelCalc T = D.borelHom :=
  D.isBorelCalculus.eq_borelCalc.symm

variable (T) in
/-- **Reed–Simon I, Theorem VII.2 (spectral theorem, functional calculus form), p. 225**, for a
bounded normal operator: there is a unique `⋆`-homomorphism `Φ` from bounded Borel functions on
`σ(T)` to `𝓛(H)` with (b) `‖Φ(g)‖ ≤ ‖g‖∞`, (c) `Φ(λ ↦ λ) = T` and (d) bounded pointwise
convergence goes to strong convergence. -/
theorem existsUnique_isBorelCalculus :
    ∃! Φ : boundedMeasurable (spectrum ℂ T) →⋆ₐ[ℂ] (H →L[ℂ] H), IsBorelCalculus T Φ :=
  ⟨borelCalc T, isBorelCalculus_borelCalc, fun _ hΦ => hΦ.eq_borelCalc⟩

/-- `borelCalc T` extends the continuous functional calculus: `g(T) = cfcHom g` for continuous
`g` (Reed–Simon I, p. 225: "`φ̂` extends `φ`"). -/
theorem borelCalc_continuousMap (g : C(spectrum ℂ T, ℂ)) :
    borelCalc T (continuousMapToBoundedMeasurable g) = cfcHom hT g :=
  isBorelCalculus_borelCalc.apply_continuousMap g

/-- (c) `borelCalc T (λ ↦ λ) = T`. -/
theorem borelCalc_id : borelCalc T (idBM T) = T :=
  isBorelCalculus_borelCalc.map_id

/-- (b) `‖g(T)‖ ≤ C` when `‖g‖ ≤ C` on `σ(T)`. -/
theorem norm_borelCalc_le (g : boundedMeasurable (spectrum ℂ T)) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ x, ‖(g : spectrum ℂ T → ℂ) x‖ ≤ C) : ‖borelCalc T g‖ ≤ C :=
  isBorelCalculus_borelCalc.norm_le g C hC0 hC

/-- (d) If `gₙ → g` pointwise on `σ(T)` with `‖gₙ‖ ≤ C`, then `gₙ(T) h → g(T) h`. -/
theorem tendsto_borelCalc_apply (g : ℕ → boundedMeasurable (spectrum ℂ T))
    (g₀ : boundedMeasurable (spectrum ℂ T)) (C : ℝ)
    (hC : ∀ n x, ‖(g n : spectrum ℂ T → ℂ) x‖ ≤ C)
    (hlim : ∀ x, Tendsto (fun n => (g n : spectrum ℂ T → ℂ) x) atTop
      (𝓝 ((g₀ : spectrum ℂ T → ℂ) x))) (h : H) :
    Tendsto (fun n => borelCalc T (g n) h) atTop (𝓝 (borelCalc T g₀ h)) :=
  isBorelCalculus_borelCalc.tendsto g g₀ C hC hlim h

/-- `g(T) h = U⁻¹ (g(λ) · U h)` for any cyclic decomposition. -/
theorem borelCalc_apply (D : CyclicDecomposition T) (g : boundedMeasurable (spectrum ℂ T))
    (h : H) :
    borelCalc T g h = D.unitary.symm (mulL ((g : spectrum ℂ T → ℂ) ∘ fun p : D.Space => p.2)
      (memLp_top_comp D.measure D.measurable_snd g) (D.unitary h)) := by
  rw [borelCalc_eq_borelHom D]
  rfl

end SpectralTheorem
