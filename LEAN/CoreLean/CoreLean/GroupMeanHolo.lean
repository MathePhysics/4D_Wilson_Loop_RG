/-
`lem:group-mean` of BALABAN_CORE.tex (`7208ecf96768`): the holomorphy of the mean.

"`Z` is a holomorphic function of `(Y_1, …, Y_n)`": the solution `Z = meanV Y` of `Σ_iΨ(Y_i, -Z) = 0` in the
ball `‖Z‖ ≤ 1/256` is complex differentiable on `‖Y‖ = max_i‖Y_i‖ < 1/512`. The core argues by uniform limits
of the iterates of the contraction; Mathlib proves that holomorphic limits are holomorphic only for maps of
one complex variable, and the proof here uses the inverse function theorem over `ℂ` instead.
* `Fm`, `Φm`: `F(Y, Z) = Σ_iΨ(Y_i, -Z)` and `Φ(Y, Z) = (Y, F(Y, Z))`, analytic near the solution
  (`analyticAt_Fm`, from `analyticOnNhd_psi`).
* The derivative of `Φ` at `(Y₀, Z₀)` is invertible: `F(Y₀, Z) = Σ_iY₀_i - nZ + H(Z)` with
  `H(Z) = Σ_iΦ(Y₀_i, -Z)` Lipschitz with the constant `256 Σ_i‖Y₀_i‖ ≤ n/2` (`Phi_lip`), so that `‖H'‖ ≤ n/2`
  and `∂_ZF = -n·id + H'` is injective; in finite dimensions injective linear maps are bijective.
* `meanV_differentiableAt`: the second component of the local inverse of `Φ` at `(Y, 0)` is complex
  differentiable at `Y₀`, solves the equation, is continuous with the value `Z₀` at `Y₀`, and therefore equals
  `meanV` near `Y₀` by the uniqueness in the ball.
* `meanV_differentiableOn`: `meanV` is holomorphic on the ball `‖Y‖ < 1/512`.
-/
import CoreLean.MeanTransports

open NormedSpace Filter Topology
open scoped Matrix.Norms.L2Operator NNReal

noncomputable section

namespace CoreLean

namespace MeanTransports

open GroupMean

variable {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ

variable {n : ℕ}

/-- `F(Y, Z) = Σ_iΨ(Y_i, -Z)`. -/
def Fm (p : (Fin n → Mat) × Mat) : Mat := ∑ i, psi (p.1 i) (-p.2)

/-- `Φ(Y, Z) = (Y, F(Y, Z))`. -/
def Φm (p : (Fin n → Mat) × Mat) : (Fin n → Mat) × Mat := (p.1, Fm p)

lemma analyticAt_Fm {p : (Fin n → Mat) × Mat} (hp : ∀ i, ‖p.1 i‖ + ‖p.2‖ < Real.log 2) :
    AnalyticAt ℂ (Fm (N := N) (n := n)) p := by
  have e : (Fm (N := N) (n := n)) =
      ∑ i ∈ (Finset.univ : Finset (Fin n)), fun q : (Fin n → Mat) × Mat => psi (q.1 i) (-q.2) := by
    funext q; simp [Fm, Finset.sum_apply]
  rw [e]
  apply Finset.analyticAt_sum
  intro i _
  set ℓ : (Fin n → Mat) × Mat →L[ℂ] Mat × Mat :=
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => Mat) i).comp
      (ContinuousLinearMap.fst ℂ (Fin n → Mat) Mat)).prod
      (-(ContinuousLinearMap.snd ℂ (Fin n → Mat) Mat)) with hℓ
  have hℓa : AnalyticAt ℂ ℓ p := ℓ.analyticAt p
  have hpsi := analyticOnNhd_psi (N := N) (ℓ p) (by simp [hℓ, norm_neg, hp i])
  exact hpsi.comp hℓa

/-- **`lem:group-mean`, the holomorphy**: `meanV` is complex differentiable at every `Y₀` with
`‖Y₀‖ < 1/512`. -/
theorem meanV_differentiableAt (hn : 0 < n) {Y₀ : Fin n → Mat} (hY₀ : ‖Y₀‖ < 1 / 512) :
    DifferentiableAt ℂ (meanV (N := N)) Y₀ := by
  have hl2 := Real.log_two_gt_d9
  have hY512 : ∀ i, ‖Y₀ i‖ ≤ 1 / 512 := fun i => (norm_le_pi_norm Y₀ i).trans hY₀.le
  set Z₀ := meanV Y₀ with hZ₀d
  have hZ₀ : ‖Z₀‖ < 1 / 256 := by
    have := norm_meanV_le hn hY512 ‖Y₀‖ fun i => norm_le_pi_norm Y₀ i
    linarith
  set p : (Fin n → Mat) × Mat := (Y₀, Z₀) with hpd
  have hp : ∀ i, ‖p.1 i‖ + ‖p.2‖ < Real.log 2 := fun i => by
    show ‖Y₀ i‖ + ‖Z₀‖ < Real.log 2
    linarith [hY512 i]
  have hF := analyticAt_Fm hp
  set DF := fderiv ℂ (Fm (N := N) (n := n)) p with hDF
  set D : (Fin n → Mat) × Mat →L[ℂ] (Fin n → Mat) × Mat :=
    (ContinuousLinearMap.fst ℂ (Fin n → Mat) Mat).prod DF with hDd
  have hΦd : HasFDerivAt (Φm (N := N) (n := n)) D p := hasFDerivAt_fst.prodMk hF.differentiableAt.hasFDerivAt
  have hΦa : AnalyticAt ℂ (Φm (N := N) (n := n)) p := analyticAt_fst.prod hF
  have hstrict : HasStrictFDerivAt (Φm (N := N) (n := n)) D p := by
    have := hΦa.hasStrictFDerivAt
    rwa [hΦd.fderiv] at this
  -- `∂_Z F` is injective
  set H : Mat → Mat := fun Z => ∑ i, Phi (Y₀ i) (-Z) with hHd
  have hHeq : H = fun Z => Fm (Y₀, Z) - ∑ i, Y₀ i + (n : ℂ) • Z := by
    funext Z
    simp only [hHd, Fm, Phi, sub_neg_eq_add, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ]
  set ι : Mat →L[ℂ] (Fin n → Mat) × Mat := (0 : Mat →L[ℂ] (Fin n → Mat)).prod (ContinuousLinearMap.id ℂ Mat)
    with hιd
  have hFZ : HasFDerivAt (fun Z : Mat => Fm (Y₀, Z)) (DF.comp ι) Z₀ := by
    have h1 : HasFDerivAt (fun Z : Mat => ((Y₀, Z) : (Fin n → Mat) × Mat)) ι Z₀ :=
      (hasFDerivAt_const Y₀ Z₀).prodMk (hasFDerivAt_id Z₀)
    exact hF.differentiableAt.hasFDerivAt.comp Z₀ h1
  have hH' : HasFDerivAt H (DF.comp ι + (n : ℂ) • ContinuousLinearMap.id ℂ Mat) Z₀ := by
    rw [hHeq]
    exact (hFZ.sub_const _).add ((hasFDerivAt_id Z₀).const_smul (n : ℂ))
  have hlip : LipschitzOnWith ((n : ℝ≥0) / 2) H (Metric.ball 0 (1 / 32)) := by
    refine LipschitzOnWith.of_dist_le_mul fun Z hZ Z' hZ' => ?_
    rw [Metric.mem_ball, dist_zero_right] at hZ hZ'
    rw [dist_eq_norm, dist_eq_norm, hHd]
    simp only
    rw [← Finset.sum_sub_distrib]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ i, ‖Phi (Y₀ i) (-Z) - Phi (Y₀ i) (-Z')‖ ≤ ∑ _i : Fin n, 256 * (1 / 512) * ‖Z - Z'‖ := by
          refine Finset.sum_le_sum fun i _ => ?_
          refine (Phi_lip (by linarith [hY512 i]) (by rw [norm_neg]; linarith)
            (by rw [norm_neg]; linarith)).trans ?_
          rw [show -Z - -Z' = -(Z - Z') by abel, norm_neg]
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hY512 i) (by norm_num))
            (norm_nonneg _)
      _ = ((n : ℝ≥0) / 2 : ℝ≥0) * ‖Z - Z'‖ := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast; ring
  have hball : Metric.ball (0 : Mat) (1 / 32) ∈ 𝓝 Z₀ :=
    Metric.isOpen_ball.mem_nhds (by rw [Metric.mem_ball, dist_zero_right]; linarith)
  have hnorm : ‖DF.comp ι + (n : ℂ) • ContinuousLinearMap.id ℂ Mat‖ ≤ (n : ℝ) / 2 := by
    have := norm_fderiv_le_of_lipschitzOn ℂ hball hlip
    rw [hH'.fderiv] at this
    simpa using this
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have key : ∀ δ : Mat, DF (0, δ) = 0 → δ = 0 := fun δ hδ => by
    have h1 : (DF.comp ι + (n : ℂ) • ContinuousLinearMap.id ℂ Mat) δ = (n : ℂ) • δ := by
      simp [hιd, hδ]
    have h2 := (DF.comp ι + (n : ℂ) • ContinuousLinearMap.id ℂ Mat).le_opNorm δ
    rw [h1, norm_smul, Complex.norm_natCast] at h2
    have h3 : (n : ℝ) * ‖δ‖ ≤ (n : ℝ) / 2 * ‖δ‖ :=
      h2.trans (mul_le_mul_of_nonneg_right hnorm (norm_nonneg _))
    have : ‖δ‖ = 0 := by nlinarith [norm_nonneg δ]
    exact norm_eq_zero.1 this
  have hinj : Function.Injective D := by
    intro a b hab
    have hab' : D (a - b) = 0 := by rw [map_sub, hab, sub_self]
    have e1 : (a - b).1 = 0 := congrArg Prod.fst hab'
    have e2 : DF (a - b) = 0 := congrArg Prod.snd hab'
    have e3 : a - b = (0, (a - b).2) := Prod.ext e1 rfl
    rw [e3] at e2
    have := key _ e2
    exact sub_eq_zero.1 (Prod.ext e1 this)
  have hker : LinearMap.ker (D : (Fin n → Mat) × Mat →ₗ[ℂ] (Fin n → Mat) × Mat) = ⊥ :=
    LinearMap.ker_eq_bot.2 hinj
  have hsurj : Function.Surjective (D : (Fin n → Mat) × Mat →ₗ[ℂ] (Fin n → Mat) × Mat) :=
    LinearMap.injective_iff_surjective.1 hinj
  have hrange : LinearMap.range (D : (Fin n → Mat) × Mat →ₗ[ℂ] (Fin n → Mat) × Mat) = ⊤ :=
    LinearMap.range_eq_top.2 hsurj
  set Φ' := ContinuousLinearEquiv.ofBijective D hker hrange with hΦ'd
  have hs : HasStrictFDerivAt (Φm (N := N) (n := n)) (Φ' : _ →L[ℂ] _) p := by
    rw [hΦ'd, ContinuousLinearEquiv.coe_ofBijective]; exact hstrict
  -- the local inverse
  set ψ := hs.localInverse (Φm (N := N) (n := n)) Φ' p with hψd
  have hΦp : Φm p = (Y₀, (0 : Mat)) := Prod.ext rfl (meanV_spec hn hY512).2
  set g : (Fin n → Mat) → Mat := fun Y => (ψ (Y, 0)).2 with hgd
  have hψd' : DifferentiableAt ℂ ψ (Y₀, 0) := by
    have := hs.to_localInverse.differentiableAt
    rwa [hΦp] at this
  have hemb : DifferentiableAt ℂ (fun Y : Fin n → Mat => ((Y, (0 : Mat)) : (Fin n → Mat) × Mat)) Y₀ :=
    differentiableAt_id.prodMk (differentiableAt_const _)
  have hg : DifferentiableAt ℂ g Y₀ := by
    have := hψd'.comp Y₀ hemb
    exact differentiableAt_snd.comp Y₀ this
  have hgY₀ : g Y₀ = Z₀ := by
    show (ψ (Y₀, 0)).2 = Z₀
    rw [← hΦp, hψd, hs.localInverse_apply_image]
  have htend : Tendsto (fun Y : Fin n → Mat => ((Y, (0 : Mat)) : (Fin n → Mat) × Mat)) (𝓝 Y₀) (𝓝 (Φm p)) := by
    rw [hΦp]; exact hemb.continuousAt.tendsto
  have hright : ∀ᶠ Y in 𝓝 Y₀, Φm (ψ (Y, 0)) = (Y, 0) := htend.eventually hs.eventually_right_inverse
  have hgsmall : ∀ᶠ Y in 𝓝 Y₀, ‖g Y‖ < 1 / 256 := by
    have hc : ContinuousAt (fun Y => ‖g Y‖) Y₀ := continuous_norm.continuousAt.comp hg.continuousAt
    exact hc.eventually_lt continuousAt_const (by simpa [hgY₀] using hZ₀)
  have hYsmall : ∀ᶠ Y in 𝓝 Y₀, ‖Y‖ < 1 / 512 :=
    Filter.eventually_of_mem (Metric.isOpen_ball.mem_nhds
      (show Y₀ ∈ Metric.ball (0 : Fin n → Mat) (1 / 512) by rwa [Metric.mem_ball, dist_zero_right]))
      fun Y hY => by rwa [Metric.mem_ball, dist_zero_right] at hY
  have heq : meanV =ᶠ[𝓝 Y₀] g := by
    filter_upwards [hright, hgsmall, hYsmall] with Y h1 h2 h3
    have e1 : (ψ (Y, 0)).1 = Y := congrArg Prod.fst h1
    have e2 : Fm (ψ (Y, 0)) = 0 := congrArg Prod.snd h1
    have hsol : ∑ i, psi (Y i) (-g Y) = 0 := by
      have := e2
      unfold Fm at this
      rw [e1] at this
      exact this
    have hY' : ∀ i, ‖Y i‖ ≤ 1 / 512 := fun i => (norm_le_pi_norm Y i).trans h3.le
    exact (meanV_unique hn hY' h2.le hsol).symm
  exact hg.congr_of_eventuallyEq heq

/-- `meanV` is holomorphic on the ball `‖Y‖ < 1/512`. -/
theorem meanV_differentiableOn (hn : 0 < n) :
    DifferentiableOn ℂ (meanV (N := N) (n := n)) (Metric.ball 0 (1 / 512)) := fun Y hY => by
  rw [Metric.mem_ball, dist_zero_right] at hY
  exact (meanV_differentiableAt hn hY).differentiableWithinAt

end MeanTransports

end CoreLean

end
