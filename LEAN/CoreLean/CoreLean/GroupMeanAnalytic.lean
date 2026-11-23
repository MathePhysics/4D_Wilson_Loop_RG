/-
`lem:group-mean` of BALABAN_CORE.tex (`615c66b253fe`): the mean `Z = meanV Y` is an analytic function of
`(Y_1, …, Y_n)` on `‖Y‖ < 1/512` ("`Z` is a holomorphic function"), the first link of the analyticity of the relative
average in `prop:relative-average`(i).

The proof is that of `meanV_differentiableAt` (`GroupMeanHolo.lean`), with the analytic inverse function theorem
(`OpenPartialHomeomorph.analyticAt_symm'`) in place of the differentiable one: `Φ(Y, Z) = (Y, Σ_iΨ(Y_i, -Z))` is
analytic with an invertible derivative at `(Y₀, meanV Y₀)`, so its local inverse is analytic at `(Y₀, 0)`, and
`meanV` agrees near `Y₀` with the second component of the local inverse on `{Z = 0}`.

* `meanV_analyticAt`, `meanV_analyticOnNhd`.
-/
import CoreLean.GroupMeanHolo

open NormedSpace Filter Topology
open scoped Matrix.Norms.L2Operator NNReal

noncomputable section

namespace CoreLean

namespace MeanTransports

open GroupMean

variable {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ

variable {n : ℕ}

/-- **`lem:group-mean`, the analyticity**: `meanV` is analytic at every `Y₀` with `‖Y₀‖ < 1/512`. -/
theorem meanV_analyticAt (hn : 0 < n) {Y₀ : Fin n → Mat} (hY₀ : ‖Y₀‖ < 1 / 512) :
    AnalyticAt ℂ (meanV (N := N)) Y₀ := by
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
  -- the analytic inverse function theorem
  have hψa : AnalyticAt ℂ ψ (Y₀, 0) := by
    have hcoe : ⇑(hs.toOpenPartialHomeomorph (Φm (N := N) (n := n))) = Φm (N := N) (n := n) :=
      hs.toOpenPartialHomeomorph_coe
    have hfa : AnalyticAt ℂ (hs.toOpenPartialHomeomorph (Φm (N := N) (n := n))) p := by rw [hcoe]; exact hΦa
    have hfd : fderiv ℂ (hs.toOpenPartialHomeomorph (Φm (N := N) (n := n))) p = (Φ' : _ →L[ℂ] _) := by
      rw [hcoe]; exact hs.hasFDerivAt.fderiv
    have := (hs.toOpenPartialHomeomorph (Φm (N := N) (n := n))).analyticAt_symm'
      hs.mem_toOpenPartialHomeomorph_source hfa hfd
    rw [hcoe, hΦp] at this
    exact this
  have hψd' : DifferentiableAt ℂ ψ (Y₀, 0) := hψa.differentiableAt
  have hemb : DifferentiableAt ℂ (fun Y : Fin n → Mat => ((Y, (0 : Mat)) : (Fin n → Mat) × Mat)) Y₀ :=
    differentiableAt_id.prodMk (differentiableAt_const _)
  have hembA : AnalyticAt ℂ (fun Y : Fin n → Mat => ((Y, (0 : Mat)) : (Fin n → Mat) × Mat)) Y₀ :=
    analyticAt_id.prod analyticAt_const
  have h2 : AnalyticAt ℂ (fun Y : Fin n → Mat => ψ (Y, 0)) Y₀ := hψa.comp_of_eq hembA rfl
  have hgA : AnalyticAt ℂ g Y₀ := analyticAt_snd.comp h2
  have hg : DifferentiableAt ℂ g Y₀ := hgA.differentiableAt
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
  exact hgA.congr heq.symm

/-- `meanV` is analytic on the ball `‖Y‖ < 1/512`. -/
theorem meanV_analyticOnNhd (hn : 0 < n) :
    AnalyticOnNhd ℂ (meanV (N := N) (n := n)) (Metric.ball 0 (1 / 512)) := fun Y hY => by
  rw [Metric.mem_ball, dist_zero_right] at hY
  exact meanV_analyticAt hn hY

end MeanTransports

end CoreLean

end
