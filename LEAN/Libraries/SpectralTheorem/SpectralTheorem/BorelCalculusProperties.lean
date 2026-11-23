import SpectralTheorem.BorelCalculus
import Mathlib.Analysis.InnerProductSpace.StarOrder

/-!
# Properties (e)–(g) of the Borel functional calculus

**Reed–Simon I, Theorem VII.2, p. 225**, properties (e)–(g) of the Borel functional calculus
`φ̂(f) = f(A)` of a bounded self-adjoint operator `A`:
(e) if `A ψ = λ ψ`, then `φ̂(f) ψ = f(λ) ψ`;
(f) if `f ≥ 0`, then `φ̂(f) ≥ 0`;
(g) if `B A = A B`, then `φ̂(f) B = B φ̂(f)`.

Here `T` is a bounded **normal** operator and `g(T) = borelCalc T g` for bounded Borel functions
`g` on `σ(T)` (`SpectralTheorem.BorelCalculus`).  The proofs:

* (e) through the multiplication form `g(T) = U⁻¹ M_{g(λ)} U`: from `U T U⁻¹ = M_λ` and
  `T ψ = λ₀ ψ`, `(λ - λ₀) · U ψ = 0` almost everywhere, so `U ψ` vanishes almost everywhere off
  `{λ = λ₀}` and `g(λ) · U ψ = g(λ₀) · U ψ` almost everywhere.
* (f) `g = s̄ s` with `s = √g` bounded Borel, so `g(T) = s(T)† s(T) ≥ 0`, since `borelCalc T` is
  a `⋆`-homomorphism.  Nonnegativity of complex numbers is the order of `ComplexOrder`
  (`0 ≤ z ↔ z` is real and nonnegative).
* (g) by the monotone class theorem (`SpectralTheorem.MonotoneClass`): `g(T)` commutes with `B`
  for continuous `g` by mathlib's `Commute.cfcHom`, and the bounded Borel functions `g` for which
  `g(T)` commutes with `B` are closed under bounded pointwise limits by (d).  For normal `T` the
  hypothesis is that `B` commutes with `T` and `T†` (Fuglede's theorem, not proved here, makes the
  second condition redundant); for self-adjoint `T`, as in Reed–Simon, the first suffices.

## Main results

* `SpectralTheorem.borelCalc_apply_of_apply_eq_smul`: (e), for `c ∈ σ(T)`;
  `SpectralTheorem.borelCalc_apply_of_apply_eq_smul'`: (e) for an eigenvector `ψ ≠ 0`, with
  `SpectralTheorem.mem_spectrum_of_apply_eq_smul` (eigenvalues lie in the spectrum).
* `SpectralTheorem.borelCalc_nonneg`, `SpectralTheorem.isPositive_borelCalc`: (f);
  `SpectralTheorem.borelCalc_mono`: monotonicity.
* `SpectralTheorem.commute_borelCalc_of_commute`,
  `SpectralTheorem.commute_borelCalc_of_isSelfAdjoint`: (g);
  `SpectralTheorem.commute_star_borelCalc_of_commute`: `B` also commutes with `g(T)†`.
* `SpectralTheorem.commute_borelCalc`, `SpectralTheorem.isStarNormal_borelCalc`,
  `SpectralTheorem.isSelfAdjoint_borelCalc_of_im_eq_zero`: the operators `g(T)` commute with
  each other, are normal, and are self-adjoint for real `g`.
-/

noncomputable section

open scoped InnerProductSpace ComplexOrder Topology
open MeasureTheory Filter

namespace SpectralTheorem

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {T : H →L[ℂ] H} [hT : IsStarNormal T]

section Algebra

/-- Bounded Borel functions commute with each other. -/
theorem boundedMeasurable.commute {X : Type*} [MeasurableSpace X] (f g : boundedMeasurable X) :
    Commute f g :=
  Subtype.ext (mul_comm (f : X → ℂ) g)

/-- The operators `f(T)` and `g(T)` commute. -/
theorem commute_borelCalc (f g : boundedMeasurable (spectrum ℂ T)) :
    Commute (borelCalc T f) (borelCalc T g) :=
  (boundedMeasurable.commute f g).map (borelCalc T)

/-- `g(T)` is normal. -/
instance isStarNormal_borelCalc (g : boundedMeasurable (spectrum ℂ T)) :
    IsStarNormal (borelCalc T g) :=
  ⟨by simpa only [map_star] using commute_borelCalc (star g) g⟩

/-- `g(T)` is self-adjoint when `g` is. -/
theorem isSelfAdjoint_borelCalc {g : boundedMeasurable (spectrum ℂ T)} (hg : IsSelfAdjoint g) :
    IsSelfAdjoint (borelCalc T g) :=
  hg.map (borelCalc T)

/-- `g(T)` is self-adjoint when `g` is real-valued. -/
theorem isSelfAdjoint_borelCalc_of_im_eq_zero {g : boundedMeasurable (spectrum ℂ T)}
    (hg : ∀ x, ((g : spectrum ℂ T → ℂ) x).im = 0) : IsSelfAdjoint (borelCalc T g) := by
  refine isSelfAdjoint_borelCalc (Subtype.ext (funext fun x => ?_))
  exact Complex.conj_eq_iff_im.mpr (hg x)

end Algebra

section Positivity

/-- The square root `√g` of a bounded Borel function with nonnegative values is bounded Borel,
and `g = s̄ s`. -/
theorem boundedMeasurable.exists_eq_star_mul_self {X : Type*} [MeasurableSpace X]
    {g : boundedMeasurable X} (hg : ∀ x, 0 ≤ (g : X → ℂ) x) :
    ∃ s : boundedMeasurable X, g = star s * s := by
  obtain ⟨C, -, hC⟩ := boundedMeasurable.exists_bound g
  let s : X → ℂ := fun x => ((Real.sqrt ((g : X → ℂ) x).re : ℝ) : ℂ)
  have hs : s ∈ boundedMeasurable X := by
    refine ⟨?_, Real.sqrt C, fun x => ?_⟩
    · exact Complex.measurable_ofReal.comp (Real.continuous_sqrt.measurable.comp
        (Complex.measurable_re.comp (boundedMeasurable.measurable g)))
    · simp only [s, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      exact Real.sqrt_le_sqrt ((Complex.re_le_norm _).trans (hC x))
  refine ⟨⟨s, hs⟩, Subtype.ext (funext fun x => ?_)⟩
  change (g : X → ℂ) x = star (s x) * s x
  obtain ⟨hre, him⟩ := Complex.nonneg_iff.mp (hg x)
  simp only [s, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
    Real.mul_self_sqrt hre]
  exact Complex.ext (by simp) (by simp [him])

/-- **(f) Positivity** (Reed–Simon I, Theorem VII.2 (f), p. 225): if `g ≥ 0` on `σ(T)`, then
`g(T) ≥ 0`.  Here `0 ≤ z` for `z : ℂ` means that `z` is real and nonnegative (`ComplexOrder`),
and the order on operators is the Loewner order. -/
theorem borelCalc_nonneg {g : boundedMeasurable (spectrum ℂ T)}
    (hg : ∀ x, 0 ≤ (g : spectrum ℂ T → ℂ) x) : 0 ≤ borelCalc T g := by
  obtain ⟨s, rfl⟩ := boundedMeasurable.exists_eq_star_mul_self hg
  rw [map_mul, map_star]
  exact star_mul_self_nonneg _

/-- **(f) Positivity**: if `g ≥ 0` on `σ(T)`, then `g(T)` is a positive operator,
`⟪g(T) h, h⟫ ≥ 0`. -/
theorem isPositive_borelCalc {g : boundedMeasurable (spectrum ℂ T)}
    (hg : ∀ x, 0 ≤ (g : spectrum ℂ T → ℂ) x) : (borelCalc T g).IsPositive :=
  ContinuousLinearMap.nonneg_iff_isPositive.mp (borelCalc_nonneg hg)

/-- **Monotonicity**: if `f ≤ g` on `σ(T)`, then `f(T) ≤ g(T)`. -/
theorem borelCalc_mono {f g : boundedMeasurable (spectrum ℂ T)}
    (hfg : ∀ x, (f : spectrum ℂ T → ℂ) x ≤ (g : spectrum ℂ T → ℂ) x) :
    borelCalc T f ≤ borelCalc T g := by
  have h := borelCalc_nonneg (T := T) (g := g - f) fun x => sub_nonneg.mpr (hfg x)
  rwa [map_sub, sub_nonneg] at h

end Positivity

section Eigenvector

omit hT [CompleteSpace H] in
/-- An eigenvalue of `T` lies in the spectrum of `T`. -/
theorem mem_spectrum_of_apply_eq_smul {ψ : H} (hψ : ψ ≠ 0) {c : ℂ} (h : T ψ = c • ψ) :
    c ∈ spectrum ℂ T := by
  rw [spectrum.mem_iff]
  rintro ⟨u, hu⟩
  apply hψ
  have h0 : (u : H →L[ℂ] H) ψ = 0 := by
    rw [hu, Algebra.algebraMap_eq_smul_one]
    change c • ψ - T ψ = 0
    rw [h, sub_self]
  have h1 : ((↑u⁻¹ : H →L[ℂ] H) * (u : H →L[ℂ] H)) ψ = ψ := by
    rw [Units.inv_mul]
    rfl
  rw [← h1]
  change (↑u⁻¹ : H →L[ℂ] H) ((u : H →L[ℂ] H) ψ) = 0
  rw [h0, map_zero]

/-- **(e) Eigenvectors** (Reed–Simon I, Theorem VII.2 (e), p. 225): if `T ψ = c ψ` for `c` in
the spectrum, then `g(T) ψ = g(c) ψ`.  In the multiplication form, `(λ - c) · U ψ = 0` almost
everywhere, so `g(λ) · U ψ = g(c) · U ψ` almost everywhere. -/
theorem borelCalc_apply_of_apply_eq_smul (g : boundedMeasurable (spectrum ℂ T)) {ψ : H}
    (c : spectrum ℂ T) (h : T ψ = (c : ℂ) • ψ) :
    borelCalc T g ψ = (g : spectrum ℂ T → ℂ) c • ψ := by
  obtain ⟨D⟩ := CyclicDecomposition.nonempty T
  rw [borelCalc_apply D]
  have h1 : mulL D.coord D.memLp_top_coord (D.unitary ψ) = (c : ℂ) • D.unitary ψ := by
    rw [← D.unitary_apply_T, h, map_smul]
  generalize hφ : D.unitary ψ = φ at h1 ⊢
  have h2 : ∀ᵐ p ∂D.measure, D.coord p * φ p = (c : ℂ) * φ p := by
    have h3 := coeFn_mulL (μ := D.measure) D.memLp_top_coord φ
    rw [h1] at h3
    filter_upwards [h3, Lp.coeFn_smul (c : ℂ) φ] with p hp hps
    rw [← hp, hps]
    rfl
  have h4 : mulL ((g : spectrum ℂ T → ℂ) ∘ fun p : D.Space => p.2)
      (memLp_top_comp D.measure D.measurable_snd g) φ = (g : spectrum ℂ T → ℂ) c • φ := by
    refine Lp.ext ?_
    filter_upwards [coeFn_mulL (μ := D.measure) (memLp_top_comp D.measure D.measurable_snd g) φ,
      Lp.coeFn_smul ((g : spectrum ℂ T → ℂ) c) φ, h2] with p hp hps hp2
    rw [hp, hps]
    change (g : spectrum ℂ T → ℂ) p.2 * φ p = (g : spectrum ℂ T → ℂ) c * φ p
    by_cases hφp : φ p = 0
    · rw [hφp, mul_zero, mul_zero]
    · rw [Subtype.ext (mul_right_cancel₀ hφp hp2)]
  rw [h4, map_smul, ← hφ, LinearIsometryEquiv.symm_apply_apply]

/-- **(e) Eigenvectors**, for an eigenvalue `c : ℂ` with eigenvector `ψ ≠ 0`: `c ∈ σ(T)` and
`g(T) ψ = g(c) ψ`. -/
theorem borelCalc_apply_of_apply_eq_smul' (g : boundedMeasurable (spectrum ℂ T)) {ψ : H}
    (hψ : ψ ≠ 0) {c : ℂ} (h : T ψ = c • ψ) :
    borelCalc T g ψ = (g : spectrum ℂ T → ℂ) ⟨c, mem_spectrum_of_apply_eq_smul hψ h⟩ • ψ :=
  borelCalc_apply_of_apply_eq_smul g ⟨c, mem_spectrum_of_apply_eq_smul hψ h⟩ h

end Eigenvector

section Commutation

/-- **(g) Commutation** (Reed–Simon I, Theorem VII.2 (g), p. 225), for normal `T`: if `B`
commutes with `T` and with `T†`, then `B` commutes with `g(T)` for every bounded Borel `g`.  The
bounded Borel functions `g` with `g(T) B = B g(T)` contain the continuous ones (`Commute.cfcHom`)
and are closed under bounded pointwise limits by (d), so they are all bounded Borel functions
(`IsBoundedLimitClosed.of_continuous`). -/
theorem commute_borelCalc_of_commute {B : H →L[ℂ] H} (hB : Commute T B)
    (hB' : Commute (star T) B) (g : boundedMeasurable (spectrum ℂ T)) :
    Commute (borelCalc T g) B := by
  let P : (spectrum ℂ T → ℂ) → Prop := fun f =>
    ∃ hf : f ∈ boundedMeasurable (spectrum ℂ T), Commute (borelCalc T ⟨f, hf⟩) B
  have hP : IsBoundedLimitClosed P := by
    refine ⟨⟨zero_mem _, ?_⟩, fun f g ⟨hf, hfe⟩ ⟨hg, hge⟩ => ⟨add_mem hf hg, ?_⟩,
      fun c f ⟨hf, hfe⟩ => ⟨SMulMemClass.smul_mem c hf, ?_⟩, fun f g C hC hlim hPf => ?_⟩
    · have h0 : (⟨0, zero_mem _⟩ : boundedMeasurable (spectrum ℂ T)) = 0 := rfl
      rw [h0, map_zero]
      exact Commute.zero_left B
    · have hsum : (⟨f + g, add_mem hf hg⟩ : boundedMeasurable (spectrum ℂ T)) =
          ⟨f, hf⟩ + ⟨g, hg⟩ := rfl
      rw [hsum, map_add]
      exact hfe.add_left hge
    · have hsmul : (⟨c • f, SMulMemClass.smul_mem c hf⟩ : boundedMeasurable (spectrum ℂ T)) =
          c • ⟨f, hf⟩ := rfl
      rw [hsmul, map_smul]
      exact hfe.smul_left c
    · choose hf hfe using hPf
      have hgm : Measurable g :=
        measurable_of_tendsto_metrizable (fun n => (hf n).1) (tendsto_pi_nhds.mpr hlim)
      have hgb : ∀ x, ‖g x‖ ≤ C := fun x =>
        le_of_tendsto (hlim x).norm (Eventually.of_forall fun n => hC n x)
      have hg : g ∈ boundedMeasurable (spectrum ℂ T) := ⟨hgm, C, hgb⟩
      refine ⟨hg, ContinuousLinearMap.ext fun h => ?_⟩
      change borelCalc T ⟨g, hg⟩ (B h) = B (borelCalc T ⟨g, hg⟩ h)
      have h1 := tendsto_borelCalc_apply (fun n => ⟨f n, hf n⟩) ⟨g, hg⟩ C hC hlim (B h)
      have h2 := (B.continuous.tendsto _).comp
        (tendsto_borelCalc_apply (fun n => ⟨f n, hf n⟩) ⟨g, hg⟩ C hC hlim h)
      have heq : ∀ n, borelCalc T ⟨f n, hf n⟩ (B h) = B (borelCalc T ⟨f n, hf n⟩ h) :=
        fun n => DFunLike.congr_fun (hfe n).eq h
      exact tendsto_nhds_unique (h1.congr heq) h2
  have hcont : ∀ f : spectrum ℂ T → ℂ, Continuous f → (∃ C, ∀ x, ‖f x‖ ≤ C) → P f := by
    intro f hf hbd
    refine ⟨continuous_mem_boundedMeasurable hf hbd, ?_⟩
    have hc : (⟨f, continuous_mem_boundedMeasurable hf hbd⟩ : boundedMeasurable (spectrum ℂ T)) =
        continuousMapToBoundedMeasurable ⟨f, hf⟩ := rfl
    rw [hc, borelCalc_continuousMap]
    exact hB.cfcHom hT hB' _
  obtain ⟨C, -, hC⟩ := boundedMeasurable.exists_bound g
  obtain ⟨_, h⟩ := hP.of_continuous hcont (boundedMeasurable.measurable g) hC
  exact h

/-- **(g) Commutation**, Reed–Simon's form for self-adjoint `T`: if `B T = T B`, then
`g(T) B = B g(T)` for every bounded Borel `g`. -/
theorem commute_borelCalc_of_isSelfAdjoint (hsa : IsSelfAdjoint T) {B : H →L[ℂ] H}
    (hB : Commute T B) (g : boundedMeasurable (spectrum ℂ T)) : Commute (borelCalc T g) B :=
  commute_borelCalc_of_commute hB (hsa.star_eq.symm ▸ hB) g

/-- If `B` commutes with `T` and `T†`, then `B` also commutes with `g(T)† = ḡ(T)`. -/
theorem commute_star_borelCalc_of_commute {B : H →L[ℂ] H} (hB : Commute T B)
    (hB' : Commute (star T) B) (g : boundedMeasurable (spectrum ℂ T)) :
    Commute (star (borelCalc T g)) B := by
  rw [← map_star]
  exact commute_borelCalc_of_commute hB hB' (star g)

end Commutation

end SpectralTheorem
