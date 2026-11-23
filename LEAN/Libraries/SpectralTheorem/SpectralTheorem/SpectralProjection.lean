import SpectralTheorem.BorelCalculus

/-!
# Spectral measures of Borel functions and spectral projections

**The spectral measure represents the Borel calculus.**  Reed–Simon I, p. 225, motivate the
Borel functional calculus by `(ψ, g(A) ψ) = ∫ g dμ_ψ`, which for continuous `g` is the defining
property of the spectral measure `μ_ψ`.  `inner_borelCalc_eq_integral` proves it for every
bounded Borel `g`: both sides are linear in `g`, agree on continuous functions, and pass to
bounded pointwise limits (property (d) on the left, dominated convergence on the right), so the
monotone class theorem applies.

**Spectral projections** (Reed–Simon I, §VII.3, p. 234): for a Borel set `Ω`,
`P_Ω = χ_Ω(T)`.  The Proposition on p. 234: (a) each `P_Ω` is an orthogonal projection;
(b) `P_∅ = 0` and `P_Ω = I` when `Ω ⊇ σ(T)` (Reed–Simon: `P_(−a, a) = I` for some `a`);
(c) if `Ω = ⋃ₙ Ωₙ` with the `Ωₙ` pairwise disjoint, then `P_Ω = s-lim_N Σ_{n<N} P_Ωₙ`;
(d) `P_Ω₁ P_Ω₂ = P_{Ω₁ ∩ Ω₂}`.  Here `Ω ⊆ ℂ`, since `T` is normal.

Every Bochner integral below is of a bounded measurable function against the finite spectral
measure, hence of an integrable function; those lines carry the totalisation-audit marker
"bounded".

## Main results

* `SpectralTheorem.inner_borelCalc_eq_integral`: `⟪ψ, g(T) ψ⟫ = ∫ g dμ_ψ`.
* `SpectralTheorem.spectralProjection T hΩ`: `P_Ω = χ_Ω(T)`.
* `SpectralTheorem.isStarProjection_spectralProjection`, `spectralProjection_empty`,
  `spectralProjection_of_subset`, `tendsto_sum_spectralProjection`,
  `spectralProjection_mul`: (a)–(d).
* `SpectralTheorem.inner_spectralProjection`: `⟪ψ, P_Ω ψ⟫ = μ_ψ(Ω)`.
-/

noncomputable section

open scoped InnerProductSpace ENNReal Topology
open MeasureTheory Filter

namespace SpectralTheorem

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {T : H →L[ℂ] H} [hT : IsStarNormal T]

/-- Bounded measurable functions are integrable for a spectral measure. -/
theorem integrable_boundedMeasurable (ψ : H) (g : boundedMeasurable (spectrum ℂ T)) :
    Integrable (g : spectrum ℂ T → ℂ) (spectralMeasure T ψ) := by
  obtain ⟨C, -, hC⟩ := boundedMeasurable.exists_bound g
  exact Integrable.of_bound (boundedMeasurable.measurable g).aestronglyMeasurable C
    (Eventually.of_forall hC)

/-- **`⟪ψ, g(T) ψ⟫ = ∫ g dμ_ψ`** for every bounded Borel function `g` on `σ(T)` (Reed–Simon I,
p. 225). -/
theorem inner_borelCalc_eq_integral (ψ : H) (g : boundedMeasurable (spectrum ℂ T)) :
    ⟪ψ, borelCalc T g ψ⟫_ℂ =
      ∫ x, (g : spectrum ℂ T → ℂ) x -- totalisation-audit: allow bounded
        ∂(spectralMeasure T ψ) := by
  let P : (spectrum ℂ T → ℂ) → Prop := fun f => ∃ hf : f ∈ boundedMeasurable (spectrum ℂ T),
    ⟪ψ, borelCalc T ⟨f, hf⟩ ψ⟫_ℂ =
      ∫ x, f x ∂(spectralMeasure T ψ) -- totalisation-audit: allow bounded
  have hP : IsBoundedLimitClosed P := by
    refine ⟨⟨zero_mem _, ?_⟩, fun f g ⟨hf, hfe⟩ ⟨hg, hge⟩ => ⟨add_mem hf hg, ?_⟩,
      fun c f ⟨hf, hfe⟩ => ⟨SMulMemClass.smul_mem c hf, ?_⟩, fun f g C hC hlim hPf => ?_⟩
    · change ⟪ψ, borelCalc T 0 ψ⟫_ℂ = _
      simp
    · have hsum : (⟨f + g, add_mem hf hg⟩ : boundedMeasurable (spectrum ℂ T)) =
          ⟨f, hf⟩ + ⟨g, hg⟩ := rfl
      rw [hsum, map_add, add_apply, inner_add_right, hfe, hge, Pi.add_def,
        integral_add (integrable_boundedMeasurable ψ ⟨f, hf⟩)
          (integrable_boundedMeasurable ψ ⟨g, hg⟩)]
    · have hsmul : (⟨c • f, SMulMemClass.smul_mem c hf⟩ : boundedMeasurable (spectrum ℂ T)) =
          c • ⟨f, hf⟩ := rfl
      rw [hsmul, map_smul, FunLike.coe_smul, Pi.smul_apply, inner_smul_right, hfe, Pi.smul_def,
        integral_smul]
      rfl
    · choose hf hfe using hPf
      have hgm : Measurable g :=
        measurable_of_tendsto_metrizable (fun n => (hf n).1) (tendsto_pi_nhds.mpr hlim)
      have hgb : ∀ x, ‖g x‖ ≤ C := fun x =>
        le_of_tendsto (hlim x).norm (Eventually.of_forall fun n => hC n x)
      have hg : g ∈ boundedMeasurable (spectrum ℂ T) := ⟨hgm, C, hgb⟩
      refine ⟨hg, tendsto_nhds_unique
        (f := fun n => ⟪ψ, borelCalc T ⟨f n, hf n⟩ ψ⟫_ℂ) (l := atTop) ?_ ?_⟩
      · exact ((continuous_const.inner continuous_id).tendsto _).comp
          (tendsto_borelCalc_apply (fun n => ⟨f n, hf n⟩) ⟨g, hg⟩ C hC hlim ψ)
      · simp only [hfe]
        exact tendsto_integral_of_dominated_convergence (fun _ => C)
          (fun n => (hf n).1.aestronglyMeasurable) (integrable_const C)
          (fun n => Eventually.of_forall (hC n)) (Eventually.of_forall hlim)
  have hcont : ∀ f : spectrum ℂ T → ℂ, Continuous f → (∃ C, ∀ x, ‖f x‖ ≤ C) → P f :=
    fun f hf hbd => ⟨continuous_mem_boundedMeasurable hf hbd, by
      change ⟪ψ, borelCalc T (continuousMapToBoundedMeasurable ⟨f, hf⟩) ψ⟫_ℂ = _
      rw [borelCalc_continuousMap, ← integral_spectralMeasure]
      rfl⟩
  obtain ⟨C, -, hC⟩ := boundedMeasurable.exists_bound g
  obtain ⟨_, h⟩ := hP.of_continuous hcont (boundedMeasurable.measurable g) hC
  exact h

section Projections

variable (T) in
/-- The indicator `χ_Ω` of a Borel set `Ω ⊆ ℂ`, restricted to `σ(T)`. -/
def indicatorBM {Ω : Set ℂ} (hΩ : MeasurableSet Ω) : boundedMeasurable (spectrum ℂ T) :=
  ⟨fun x => Ω.indicator (fun _ => (1 : ℂ)) (x : ℂ),
    (measurable_const.indicator hΩ).comp measurable_subtype_coe, 1, fun x => by
      by_cases hx : (x : ℂ) ∈ Ω <;> simp [hx]⟩

omit [CompleteSpace H] hT in
theorem coe_indicatorBM {Ω : Set ℂ} (hΩ : MeasurableSet Ω) :
    (indicatorBM T hΩ : spectrum ℂ T → ℂ) =
      fun x : spectrum ℂ T => Ω.indicator (fun _ => (1 : ℂ)) (x : ℂ) :=
  rfl

omit [CompleteSpace H] hT in
/-- `χ_Ω` on `σ(T)` is the indicator of the preimage of `Ω`. -/
theorem coe_indicatorBM_eq {Ω : Set ℂ} (hΩ : MeasurableSet Ω) :
    (indicatorBM T hΩ : spectrum ℂ T → ℂ) =
      (Subtype.val ⁻¹' Ω : Set (spectrum ℂ T)).indicator fun _ => (1 : ℂ) := by
  funext x
  change Ω.indicator (fun _ => (1 : ℂ)) (x : ℂ) =
    (Subtype.val ⁻¹' Ω : Set (spectrum ℂ T)).indicator (fun _ => (1 : ℂ)) x
  by_cases hx : (x : ℂ) ∈ Ω <;> simp [hx]

omit [CompleteSpace H] hT in
theorem indicatorBM_mul {Ω₁ Ω₂ : Set ℂ} (h₁ : MeasurableSet Ω₁) (h₂ : MeasurableSet Ω₂) :
    indicatorBM T h₁ * indicatorBM T h₂ = indicatorBM T (h₁.inter h₂) := by
  refine Subtype.ext (funext fun x => ?_)
  change Ω₁.indicator (fun _ => (1 : ℂ)) (x : ℂ) * Ω₂.indicator (fun _ => (1 : ℂ)) (x : ℂ) =
    (Ω₁ ∩ Ω₂).indicator (fun _ => (1 : ℂ)) (x : ℂ)
  by_cases hx₁ : (x : ℂ) ∈ Ω₁ <;> by_cases hx₂ : (x : ℂ) ∈ Ω₂ <;> simp [hx₁, hx₂]

omit [CompleteSpace H] hT in
theorem star_indicatorBM {Ω : Set ℂ} (hΩ : MeasurableSet Ω) :
    star (indicatorBM T hΩ) = indicatorBM T hΩ := by
  refine Subtype.ext (funext fun x => ?_)
  change star (Ω.indicator (fun _ => (1 : ℂ)) (x : ℂ)) = Ω.indicator (fun _ => (1 : ℂ)) (x : ℂ)
  by_cases hx : (x : ℂ) ∈ Ω <;> simp [hx]

variable (T) in
/-- **The spectral projection** `P_Ω = χ_Ω(T)` of a Borel set `Ω ⊆ ℂ` (Reed–Simon I, §VII.3,
p. 234). -/
def spectralProjection {Ω : Set ℂ} (hΩ : MeasurableSet Ω) : H →L[ℂ] H :=
  borelCalc T (indicatorBM T hΩ)

theorem spectralProjection_congr {Ω₁ Ω₂ : Set ℂ} (h₁ : MeasurableSet Ω₁) (h₂ : MeasurableSet Ω₂)
    (h : Ω₁ = Ω₂) : spectralProjection T h₁ = spectralProjection T h₂ := by
  subst h
  rfl

/-- (d) `P_Ω₁ P_Ω₂ = P_{Ω₁ ∩ Ω₂}` (Reed–Simon I, Proposition, p. 234). -/
theorem spectralProjection_mul {Ω₁ Ω₂ : Set ℂ} (h₁ : MeasurableSet Ω₁) (h₂ : MeasurableSet Ω₂) :
    spectralProjection T h₁ * spectralProjection T h₂ = spectralProjection T (h₁.inter h₂) := by
  rw [spectralProjection, spectralProjection, ← map_mul, indicatorBM_mul]
  rfl

/-- (a) **`P_Ω` is an orthogonal projection** (Reed–Simon I, Proposition, p. 234). -/
theorem isStarProjection_spectralProjection {Ω : Set ℂ} (hΩ : MeasurableSet Ω) :
    IsStarProjection (spectralProjection T hΩ) where
  isIdempotentElem := by
    rw [IsIdempotentElem, spectralProjection_mul]
    exact spectralProjection_congr _ _ (Set.inter_self Ω)
  isSelfAdjoint := by
    rw [IsSelfAdjoint, spectralProjection, ← map_star, star_indicatorBM]

/-- (b) `P_∅ = 0`. -/
theorem spectralProjection_empty : spectralProjection T MeasurableSet.empty = 0 := by
  have h : indicatorBM T MeasurableSet.empty = 0 := Subtype.ext (funext fun x => by
    change (∅ : Set ℂ).indicator (fun _ => (1 : ℂ)) (x : ℂ) = 0
    simp)
  rw [spectralProjection, h, map_zero]

/-- (b) `P_Ω = I` when `Ω ⊇ σ(T)`. -/
theorem spectralProjection_of_subset {Ω : Set ℂ} (hΩ : MeasurableSet Ω)
    (hsub : spectrum ℂ T ⊆ Ω) : spectralProjection T hΩ = 1 := by
  have h : indicatorBM T hΩ = 1 := Subtype.ext (funext fun x => by
    change Ω.indicator (fun _ => (1 : ℂ)) (x : ℂ) = 1
    simp [hsub x.2])
  rw [spectralProjection, h, map_one]

/-- (b) `P_{B(0, a)} = I` for `a > ‖T‖` (Reed–Simon: `P_(−a, a) = I` for some `a`). -/
theorem spectralProjection_ball {a : ℝ} (ha : ‖T‖ < a) :
    spectralProjection T (Metric.isOpen_ball (x := (0 : ℂ)) (ε := a)).measurableSet = 1 :=
  spectralProjection_of_subset _ fun z hz => by
    have h := spectrum.subset_closedBall_norm_mul T hz
    rw [Metric.mem_closedBall, dist_zero_right] at h
    rw [Metric.mem_ball, dist_zero_right]
    exact lt_of_le_of_lt (h.trans (mul_le_of_le_one_right (norm_nonneg T)
      ContinuousLinearMap.norm_id_le)) ha

/-- **`⟪ψ, P_Ω ψ⟫ = μ_ψ(Ω)`**: the spectral measure of `ψ` is `Ω ↦ ⟪ψ, P_Ω ψ⟫`. -/
theorem inner_spectralProjection (ψ : H) {Ω : Set ℂ} (hΩ : MeasurableSet Ω) :
    ⟪ψ, spectralProjection T hΩ ψ⟫_ℂ =
      ((spectralMeasure T ψ).real (Subtype.val ⁻¹' Ω : Set (spectrum ℂ T)) : ℂ) := by
  rw [spectralProjection, inner_borelCalc_eq_integral, coe_indicatorBM_eq,
    integral_indicator_const _ (measurable_subtype_coe hΩ), Complex.real_smul, mul_one]

/-- (c) **Strong countable additivity**: if the `Ωₙ` are pairwise disjoint, then
`Σ_{n<N} P_Ωₙ h → P_{⋃ Ωₙ} h` (Reed–Simon I, Proposition, p. 234). -/
theorem tendsto_sum_spectralProjection (Ω : ℕ → Set ℂ) (hΩ : ∀ n, MeasurableSet (Ω n))
    (hdisj : Pairwise (Function.onFun Disjoint Ω)) (h : H) :
    Tendsto (fun N => ∑ n ∈ Finset.range N, spectralProjection T (hΩ n) h) atTop
      (𝓝 (spectralProjection T (MeasurableSet.iUnion hΩ) h)) := by
  let f : ℕ → Set (spectrum ℂ T) := fun n => Subtype.val ⁻¹' Ω n
  have hdisj' : Pairwise (Function.onFun Disjoint f) := fun i j hij =>
    (hdisj hij).preimage Subtype.val
  have hsum : ∀ N, ∑ n ∈ Finset.range N, spectralProjection T (hΩ n) h =
      borelCalc T (∑ n ∈ Finset.range N, indicatorBM T (hΩ n)) h := fun N => by
    rw [map_sum, sum_apply]
    rfl
  simp only [hsum]
  have hcoe : ∀ N x, ((∑ n ∈ Finset.range N, indicatorBM T (hΩ n) :
      boundedMeasurable (spectrum ℂ T)) : spectrum ℂ T → ℂ) x =
        ∑ n ∈ Finset.range N, (f n).indicator (fun _ => (1 : ℂ)) x := fun N x => by
    rw [AddSubmonoidClass.coe_finsetSum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [coe_indicatorBM_eq]
  have hU : (indicatorBM T (MeasurableSet.iUnion hΩ) : spectrum ℂ T → ℂ) =
      (⋃ n, f n).indicator fun _ => (1 : ℂ) := by
    rw [coe_indicatorBM_eq, Set.preimage_iUnion]
  refine tendsto_borelCalc_apply _ _ 1 (fun N x => ?_) (fun x => ?_) h
  · rw [hcoe]
    exact (sum_indicator_disjoint f hdisj' x).1 N
  · simp only [hcoe, hU]
    exact (sum_indicator_disjoint f hdisj' x).2

end Projections

end SpectralTheorem
