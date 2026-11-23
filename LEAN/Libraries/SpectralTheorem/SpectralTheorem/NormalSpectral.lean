import SpectralTheorem.NormalPMap
import SpectralTheorem.SpectralPVM

/-!
# The spectral theorem for a normal operator with a bounded normal resolvent

**Rudin, *Functional Analysis*, Theorem 13.33**, in the restricted form where the resolvent set
of the operator is known to be nonempty.  Let `N` be densely defined with a point `z₀` of the
resolvent set whose resolvent `R = (N - z₀)⁻¹` is a bounded **normal** operator: `R` is defined
everywhere, its range is `D(N)`, `(N - z₀) R = 1` and `R (N - z₀) = 1` on `D(N)`
(`SpectralTheorem.IsResolventAt`).  Then `N = ∫ z dP` for a projection-valued measure `P` on
`ℂ`, and `N` is normal by `SpectralTheorem.ProjectionValuedMeasure.isNormalPMap_integralPMap`.

For a general closed normal operator the spectrum can be all of `ℂ`, so the hypothesis is a
genuine restriction; removing it needs von Neumann's theorem on `(1 + N† N)⁻¹`.

Proof (mirroring `SpectralTheorem.ResolventSpectrum` and `SpectralTheorem.UnboundedBorel` for
the self-adjoint case).  Write `P_R` for the projection-valued measure of the bounded normal
operator `R` (`SpectralTheorem.spectralPVM`), so that `R = ∫ w dP_R` with `P_R` carried by
`B̄(0, ‖R‖)`.
* `R` is injective, since `φ = (N - z₀) R φ`.  Hence `P_R{0} = 0`: `R P_R{0} = ∫ w 1_{0} dP_R = 0`.
  So `P_R` is carried by `s = B̄(0, ‖R‖) \ {0}`, on which `w ↦ w⁻¹` is the reciprocal of `w`.
* Let `P = F_* P_R` for `F(w) = w⁻¹ + z₀`, and `M = ∫ z dP = ∫ F dP_R`
  (`ProjectionValuedMeasure.integralPMap_map`).
* `D(N) ⊆ D(M)` and `M = N` there: `F(w) · w · 1_{B̄} = 1_s + z₀ w 1_{B̄}` is bounded, so
  `R φ = (∫ w 1_{B̄} dP_R) φ ∈ D_F` and `M (R φ) = (∫ (1_s + z₀ w 1_{B̄}) dP_R) φ = φ + z₀ R φ`,
  which is `N (R φ)` by the resolvent equation.
* `D(M) ⊆ D(N) = Ran R`: for `ψ ∈ D_F` also `ψ ∈ D_{w⁻¹}` (constants are square integrable for
  the finite measures `μ_ψ`), and `R ((∫ w⁻¹ dP_R) ψ) = (∫ w 1_{B̄} w⁻¹ dP_R) ψ = P_R(s) ψ = ψ`.

## Main definitions and results

* `SpectralTheorem.IsResolventAt N z₀ R`: `R` is a bounded normal inverse of `N - z₀`.
* `ProjectionValuedMeasure.integralPMap_congr`, `ProjectionValuedMeasure.integralPMap_map`:
  `∫ g dP` depends only on the function `g`, and `∫ g d(F_* P) = ∫ (g ∘ F) dP`.
* `SpectralTheorem.spectralPVM_singleton_zero`: `P_R{0} = 0` for injective normal `R`.
* `SpectralTheorem.exists_pvm_integralPMap_eq`: `N = ∫ z dP` for some projection-valued measure
  `P` on `ℂ`.
* `SpectralTheorem.IsResolventAt.isNormalPMap`: such an `N` is normal, hence closed.
-/

noncomputable section

open scoped InnerProductSpace ENNReal Topology ComplexConjugate
open MeasureTheory Filter Set

namespace SpectralTheorem

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### Operators with a bounded normal resolvent -/

/-- **`R` is a bounded normal resolvent of `N` at `z₀`**: `R` is everywhere defined and normal,
its range is `D(N)`, and it inverts `N - z₀` on both sides. -/
structure IsResolventAt (N : H →ₗ.[ℂ] H) (z₀ : ℂ) (R : H →L[ℂ] H) : Prop where
  /-- The resolvent is a normal operator. -/
  isStarNormal : IsStarNormal R
  /-- The range of the resolvent is the domain of `N`. -/
  range_eq : Set.range R = (N.domain : Set H)
  /-- `(N - z₀) R = 1`. -/
  apply_inv : ∀ (φ : H) (h : R φ ∈ N.domain), N ⟨R φ, h⟩ - z₀ • R φ = φ
  /-- `R (N - z₀) = 1` on `D(N)`. -/
  inv_apply : ∀ ψ : N.domain, R (N ψ - z₀ • (ψ : H)) = (ψ : H)

namespace IsResolventAt

variable {N : H →ₗ.[ℂ] H} {z₀ : ℂ} {R : H →L[ℂ] H}

/-- `R φ` lies in `D(N)`. -/
theorem apply_mem (h : IsResolventAt N z₀ R) (φ : H) : R φ ∈ N.domain := by
  rw [← SetLike.mem_coe, ← h.range_eq]
  exact Set.mem_range_self φ

/-- A resolvent is injective: `φ = (N - z₀) R φ`. -/
theorem injective (h : IsResolventAt N z₀ R) : Function.Injective R := fun a b hab => by
  have e : (⟨R a, h.apply_mem a⟩ : N.domain) = ⟨R b, h.apply_mem b⟩ := Subtype.ext hab
  calc a = N ⟨R a, h.apply_mem a⟩ - z₀ • R a := (h.apply_inv a _).symm
    _ = N ⟨R b, h.apply_mem b⟩ - z₀ • R b := by rw [e, hab]
    _ = b := h.apply_inv b _

end IsResolventAt

/-! ### Two general facts about `∫ g dP` -/

namespace ProjectionValuedMeasure

variable {X : Type*} [MeasurableSpace X] (P : ProjectionValuedMeasure X H)

/-- `∫ g dP` depends only on the function `g`. -/
theorem integralPMap_congr {g₁ g₂ : X → ℂ} (hg₁ : Measurable g₁) (hg₂ : Measurable g₂)
    (h : ∀ x, g₁ x = g₂ x) : P.integralPMap hg₁ = P.integralPMap hg₂ := by
  obtain rfl : g₁ = g₂ := funext h
  rfl

/-- **`∫ g d(F_* P) = ∫ (g ∘ F) dP`**: the domains agree because the measures of `F_* P` are the
pushforwards of the measures of `P`, and the truncations of `g ∘ F` are the truncations of `g`
composed with `F`. -/
theorem integralPMap_map {Y : Type*} [MeasurableSpace Y] {F : X → Y} (hF : Measurable F)
    {g : Y → ℂ} (hg : Measurable g) :
    (P.map F hF).integralPMap hg = P.integralPMap (hg.comp hF) := by
  have htr : ∀ n : ℕ, boundedTrunc (hg.comp hF) n =
      ⟨(boundedTrunc hg n : Y → ℂ) ∘ F, boundedMeasurable.comp_mem _ hF⟩ := fun n => by
    refine Subtype.ext (funext fun x => ?_)
    change {x | ‖g (F x)‖ ≤ (n : ℝ)}.indicator (g ∘ F) x =
      {w | ‖g w‖ ≤ (n : ℝ)}.indicator g (F x)
    by_cases hx : ‖g (F x)‖ ≤ (n : ℝ)
    · rw [Set.indicator_of_mem (show x ∈ {x | ‖g (F x)‖ ≤ (n : ℝ)} from hx),
        Set.indicator_of_mem (show F x ∈ {w | ‖g w‖ ≤ (n : ℝ)} from hx)]
      rfl
    · rw [Set.indicator_of_notMem (show x ∉ {x | ‖g (F x)‖ ≤ (n : ℝ)} from hx),
        Set.indicator_of_notMem (show F x ∉ {w | ‖g w‖ ≤ (n : ℝ)} from hx)]
  refine LinearPMap.ext ?_ fun ψ h1 h2 => ?_
  · refine Submodule.ext fun ψ => ?_
    rw [P.mem_integralPMap_domain, (P.map F hF).mem_integralPMap_domain, P.measure_map,
      memLp_map_measure_iff hg.aestronglyMeasurable hF.aemeasurable]
  · refine tendsto_nhds_unique ((P.map F hF).tendsto_integral_trunc hg ⟨ψ, h1⟩) ?_
    refine Tendsto.congr (fun n => ?_) (P.tendsto_integral_trunc (hg.comp hF) ⟨ψ, h2⟩)
    rw [htr n, ← P.integral_map hF]

end ProjectionValuedMeasure

/-! ### The p.v.m. of an injective normal operator does not charge `0` -/

variable (R : H →L[ℂ] H) [IsStarNormal R]

/-- `∫ w dP_R = R`, with the radius `‖R‖`. -/
theorem integral_ballId_spectralPVM :
    (spectralPVM R).integral (ballId ‖R‖) = R := by
  rw [← (spectralPVM R).toOperator_eq (spectralPVM_isBounded R)
    (spectralPVM_closedBall_norm R), toOperator_spectralPVM]

omit [CompleteSpace H] in
/-- `(A * B) ψ = A (B ψ)`. -/
theorem clm_mul_apply (A B : H →L[ℂ] H) (ψ : H) : (A * B) ψ = A (B ψ) :=
  rfl

/-- **`P_R{0} = 0` for an injective normal `R`** (as in
`SpectralTheorem.spectralProjection_resolvent_zero`): `R P_R{0} = ∫ w 1_{0} dP_R = 0`. -/
theorem spectralPVM_singleton_zero (hR : Function.Injective R) :
    spectralPVM R {0} = 0 := by
  have h0 : MeasurableSet ({0} : Set ℂ) := measurableSet_singleton 0
  have key : R * spectralPVM R {0} = 0 := by
    have e : (ballId ‖R‖ * boundedMeasurable.indicator h0 : boundedMeasurable ℂ) = 0 := by
      refine Subtype.ext (funext fun w => ?_)
      change (ballId ‖R‖ : ℂ → ℂ) w * ({0} : Set ℂ).indicator (fun _ => (1 : ℂ)) w = 0
      by_cases hw : w ∈ ({0} : Set ℂ)
      · rw [Set.mem_singleton_iff] at hw
        subst hw
        rw [coe_ballId]
        by_cases hb : (0 : ℂ) ∈ Metric.closedBall (0 : ℂ) ‖R‖
        · rw [Set.indicator_of_mem hb]
          simp
        · rw [Set.indicator_of_notMem hb, zero_mul]
      · rw [Set.indicator_of_notMem hw, mul_zero]
    have h3 : (spectralPVM R).integral (ballId ‖R‖) *
        (spectralPVM R).integral (boundedMeasurable.indicator h0) = 0 := by
      rw [← map_mul, e, map_zero]
    rwa [integral_ballId_spectralPVM R, (spectralPVM R).integral_indicator h0] at h3
  refine ContinuousLinearMap.ext fun ψ => ?_
  have h1 : R (spectralPVM R {0} ψ) = R 0 := by
    rw [map_zero, ← clm_mul_apply, key]
    rfl
  rw [hR h1]
  rfl

/-! ### The spectral theorem -/

/-- **The spectral theorem for a normal operator with a bounded normal resolvent**: `N = ∫ z dP`
for the pushforward `P` of the projection-valued measure of `R` along `w ↦ w⁻¹ + z₀`. -/
theorem exists_pvm_integralPMap_eq {N : H →ₗ.[ℂ] H} {z₀ : ℂ} {R : H →L[ℂ] H}
    (hR : IsResolventAt N z₀ R) :
    ∃ P : ProjectionValuedMeasure ℂ H, P.integralPMap measurable_id = N := by
  have := hR.isStarNormal
  have hFm : Measurable fun w : ℂ => w⁻¹ + z₀ := -- totalisation-audit: allow P_R{0} = 0
    measurable_inv.add_const z₀
  have hinv : Measurable fun w : ℂ => w⁻¹ := -- totalisation-audit: allow P_R{0} = 0
    measurable_inv
  refine ⟨(spectralPVM R).map (fun w : ℂ => w⁻¹ + z₀) hFm, ?_⟩ -- totalisation-audit: allow
  rw [ProjectionValuedMeasure.integralPMap_map,
    (spectralPVM R).integralPMap_congr (measurable_id.comp hFm) hFm fun w => rfl]
  -- the carrier of `P_R`
  have hs : MeasurableSet (Metric.closedBall (0 : ℂ) ‖R‖ \ {0}) :=
    measurableSet_closedBall.diff (measurableSet_singleton 0)
  have hPs : spectralPVM R (Metric.closedBall (0 : ℂ) ‖R‖ \ {0}) = 1 := by
    rw [Set.sdiff_eq, ← (spectralPVM R).mul_apply measurableSet_closedBall
      (measurableSet_singleton 0).compl, (spectralPVM R).compl (measurableSet_singleton 0),
      spectralPVM_singleton_zero R hR.injective, spectralPVM_closedBall_norm]
    simp
  have hRint : (spectralPVM R).integral (ballId ‖R‖) = R := integral_ballId_spectralPVM R
  -- the two bounded functions
  have hk : ∀ w : ℂ, ((boundedMeasurable.indicator hs + z₀ • ballId ‖R‖ :
      boundedMeasurable ℂ) : ℂ → ℂ) w =
      (w⁻¹ + z₀) * (ballId ‖R‖ : ℂ → ℂ) w := fun w => by -- totalisation-audit: allow P_R{0} = 0
    change (Metric.closedBall (0 : ℂ) ‖R‖ \ {0}).indicator (fun _ => (1 : ℂ)) w +
      z₀ • (ballId ‖R‖ : ℂ → ℂ) w = (w⁻¹ + z₀) * -- totalisation-audit: allow P_R{0} = 0
        (ballId ‖R‖ : ℂ → ℂ) w
    rw [coe_ballId]
    by_cases hw : w ∈ Metric.closedBall (0 : ℂ) ‖R‖
    · rw [Set.indicator_of_mem hw]
      by_cases hw0 : w = 0
      · subst hw0
        rw [Set.indicator_of_notMem (fun h => h.2 rfl)]
        simp
      · rw [Set.indicator_of_mem (show w ∈ Metric.closedBall (0 : ℂ) ‖R‖ \ {0} from ⟨hw, hw0⟩)]
        simp only [id_eq, smul_eq_mul]
        field_simp
    · rw [Set.indicator_of_notMem hw, Set.indicator_of_notMem (fun h => hw h.1), smul_zero,
        mul_zero, add_zero]
  have he : ∀ w : ℂ, ((boundedMeasurable.indicator hs : boundedMeasurable ℂ) : ℂ → ℂ) w =
      (ballId ‖R‖ : ℂ → ℂ) w * w⁻¹ := fun w => by -- totalisation-audit: allow P_R{0} = 0
    change (Metric.closedBall (0 : ℂ) ‖R‖ \ {0}).indicator (fun _ => (1 : ℂ)) w =
      (ballId ‖R‖ : ℂ → ℂ) w * w⁻¹ -- totalisation-audit: allow P_R{0} = 0
    rw [coe_ballId]
    by_cases hw : w ∈ Metric.closedBall (0 : ℂ) ‖R‖
    · rw [Set.indicator_of_mem hw]
      by_cases hw0 : w = 0
      · subst hw0
        rw [Set.indicator_of_notMem (fun h => h.2 rfl)]
        simp
      · rw [Set.indicator_of_mem (show w ∈ Metric.closedBall (0 : ℂ) ‖R‖ \ {0} from ⟨hw, hw0⟩)]
        simp only [id_eq]
        rw [mul_inv_cancel₀ hw0]
    · rw [Set.indicator_of_notMem hw, Set.indicator_of_notMem (fun h => hw h.1), zero_mul]
  -- `Ran R ⊆ D(M)`, with the value of `M` there
  have hmemM : ∀ φ : H, R φ ∈ ((spectralPVM R).integralPMap hFm).domain := fun φ => by
    have h := (spectralPVM R).integral_mem_integralPMap_domain hFm (ballId ‖R‖) _ hk φ
    rwa [hRint] at h
  have hvalue : ∀ (φ : H) (h : R φ ∈ ((spectralPVM R).integralPMap hFm).domain),
      (spectralPVM R).integralPMap hFm ⟨R φ, h⟩ = φ + z₀ • R φ := fun φ h => by
    have h2 := (spectralPVM R).integralPMap_integral hFm (ballId ‖R‖) _ hk φ
    have e : (⟨R φ, h⟩ : ((spectralPVM R).integralPMap hFm).domain) =
        ⟨(spectralPVM R).integral (ballId ‖R‖) φ,
          (spectralPVM R).integral_mem_integralPMap_domain hFm (ballId ‖R‖) _ hk φ⟩ :=
      Subtype.ext (by
        show R φ = (spectralPVM R).integral (ballId ‖R‖) φ
        rw [hRint])
    rw [e, h2, map_add, map_smul, (spectralPVM R).integral_indicator hs, hPs, hRint]
    rfl
  -- `D(M) ⊆ Ran R`
  have hinvmem : ∀ ψ : H, ψ ∈ ((spectralPVM R).integralPMap hFm).domain →
      ψ ∈ ((spectralPVM R).integralPMap hinv).domain := fun ψ hψ => by
    rw [ProjectionValuedMeasure.mem_integralPMap_domain] at hψ ⊢
    have e : (fun w : ℂ => w⁻¹) = -- totalisation-audit: allow P_R{0} = 0
        (fun w : ℂ => w⁻¹ + z₀) - fun _ => z₀ := by -- totalisation-audit: allow P_R{0} = 0
      funext w
      simp
    rw [e]
    exact hψ.sub (memLp_const z₀)
  have hrange : ∀ (ψ : H) (hψ : ψ ∈ ((spectralPVM R).integralPMap hFm).domain),
      R ((spectralPVM R).integralPMap hinv ⟨ψ, hinvmem ψ hψ⟩) = ψ := fun ψ hψ => by
    have h := (spectralPVM R).integral_integralPMap_bounded hinv (ballId ‖R‖) _ he
      ⟨ψ, hinvmem ψ hψ⟩
    rw [hRint] at h
    rw [h, (spectralPVM R).integral_indicator hs, hPs]
    rfl
  -- comparison
  refine LinearPMap.ext ?_ fun ψ h1 h2 => ?_
  · refine Submodule.ext fun ψ => ⟨fun hψ => ?_, fun hψ => ?_⟩
    · rw [← SetLike.mem_coe, ← hR.range_eq]
      exact ⟨_, hrange ψ hψ⟩
    · rw [← SetLike.mem_coe, ← hR.range_eq] at hψ
      obtain ⟨φ, rfl⟩ := hψ
      exact hmemM φ
  · obtain ⟨φ, rfl⟩ : ∃ φ, R φ = ψ := ⟨_, hrange ψ h1⟩
    rw [hvalue φ h1]
    exact (sub_eq_iff_eq_add.1 (hR.apply_inv φ h2)).symm

/-- **An operator with a bounded normal resolvent is normal**, hence closed. -/
theorem IsResolventAt.isNormalPMap {N : H →ₗ.[ℂ] H} {z₀ : ℂ} {R : H →L[ℂ] H}
    (hR : IsResolventAt N z₀ R) : IsNormalPMap N := by
  obtain ⟨P, hP⟩ := exists_pvm_integralPMap_eq hR
  rw [← hP]
  exact P.isNormalPMap_integralPMap measurable_id

end SpectralTheorem
