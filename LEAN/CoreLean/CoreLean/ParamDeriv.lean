/-
The derivative in one variable of a jointly holomorphic map is holomorphic in the other: for `f` holomorphic on
`{‖x‖ < r₁} × {‖y‖ < r₂}` and bounded, `x ↦ ∂_y f(x, 0)v` is holomorphic on `{‖x‖ < r₁/2}` (`deriv_param_differentiableOn`).
This is the input of the holomorphy in `A'` of `Q`, `Q'`, and `C` in `prop:relative-average`(viii) of BALABAN_CORE.tex
(`fe7d249fe3af`), whose proof says that `Q_n(e^{ia_iA'}U)` is the derivative at `A = 0` of a function which is
holomorphic in `(A', A)`, and so holomorphic in `A'`.

The difference quotients `q_s(x) = s⁻¹(f(x, sv) - f(x, 0))` are holomorphic in `x` and converge uniformly to
`∂_y f(x, 0)v` as `s → 0`, by the lemma of Schwarz of the second order in `s`; by Cauchy's estimate their derivatives in `x`
are uniformly Cauchy on the smaller ball, and the uniform limit of derivatives is the derivative of the limit.
-/
import CoreLean.SchwarzCauchy
import Mathlib.Analysis.Calculus.UniformLimitsDeriv

open Filter Topology Metric

noncomputable section

namespace CoreLean
namespace ParamDeriv

variable {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [NormedAddCommGroup Y] [NormedSpace ℂ Y]
  [NormedAddCommGroup Z] [NormedSpace ℂ Z]

set_option maxHeartbeats 4000000 in
/-- **The derivative in `y` of a jointly holomorphic map is holomorphic in `x`.** -/
theorem deriv_param_differentiableOn [CompleteSpace Z] {f : X × Y → Z} {r₁ r₂ M : ℝ} (hr₁ : 0 < r₁)
    (hr₂ : 0 < r₂) (hf : DifferentiableOn ℂ f (ball (0 : X) r₁ ×ˢ ball (0 : Y) r₂))
    (hM : ∀ x ∈ ball (0 : X) r₁, ∀ y ∈ ball (0 : Y) r₂, ‖f (x, y)‖ ≤ M) (v : Y) :
    DifferentiableOn ℂ (fun x => fderiv ℂ (fun y => f (x, y)) 0 v) (ball (0 : X) (r₁ / 2)) := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp only [map_zero]; exact differentiableOn_const _
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (mem_ball_self hr₁) 0 (mem_ball_self hr₂))
  have hv0 : 0 < ‖v‖ := norm_pos_iff.2 hv
  set R := r₂ / ‖v‖ with hR
  have hR0 : 0 < R := div_pos hr₂ hv0
  -- the slices
  have hsy : ∀ x ∈ ball (0 : X) r₁, DifferentiableOn ℂ (fun y => f (x, y)) (ball 0 r₂) := fun x hx y hy =>
    (hf (x, y) ⟨hx, hy⟩).comp y ((differentiableAt_const x).prodMk differentiableAt_id).differentiableWithinAt
      (fun y' hy' => Set.mk_mem_prod hx hy')
  have hsx : ∀ y ∈ ball (0 : Y) r₂, DifferentiableOn ℂ (fun x => f (x, y)) (ball 0 r₁) := fun y hy x hx =>
    (hf (x, y) ⟨hx, hy⟩).comp x (differentiableAt_id.prodMk (differentiableAt_const y)).differentiableWithinAt
      (fun x' hx' => Set.mk_mem_prod hx' hy)
  have htv : ∀ t : ℂ, t ∈ ball (0 : ℂ) R → t • v ∈ ball (0 : Y) r₂ := fun t ht => by
    rw [mem_ball_zero_iff] at ht ⊢
    rw [norm_smul]
    calc ‖t‖ * ‖v‖ < R * ‖v‖ := mul_lt_mul_of_pos_right ht hv0
      _ = r₂ := by rw [hR]; field_simp
  set D : X → Z := fun x => fderiv ℂ (fun y => f (x, y)) 0 v with hD
  -- the derivative of `t ↦ f(x, tv)` at `0`
  have hDt : ∀ x ∈ ball (0 : X) r₁, HasDerivAt (fun t : ℂ => f (x, t • v)) (D x) 0 := fun x hx => by
    have h1 : HasFDerivAt (fun y => f (x, y)) (fderiv ℂ (fun y => f (x, y)) 0) ((0 : ℂ) • v) := by
      rw [zero_smul]
      exact ((hsy x hx).differentiableAt (ball_mem_nhds 0 hr₂)).hasFDerivAt
    have h2 : HasDerivAt (fun t : ℂ => t • v) v 0 := by simpa using (hasDerivAt_id (0 : ℂ)).smul_const v
    exact h1.comp_hasDerivAt (0 : ℂ) h2
  have hDb : ∀ x ∈ ball (0 : X) r₁, ‖D x‖ ≤ M * ‖v‖ / r₂ := fun x hx => by
    have := SchwarzCauchy.cauchy_fderiv (hsy x hx) (fun y hy => hM x hx y hy) (mem_ball_self hr₂) v
    simpa using this
  -- the uniform approximation by the difference quotients
  set q : ℂ → X → Z := fun s x => s⁻¹ • (f (x, s • v) - f (x, 0)) with hq
  have happrox : ∀ x ∈ ball (0 : X) r₁, ∀ s : ℂ, s ≠ 0 → s ∈ ball (0 : ℂ) R →
      ‖q s x - D x‖ ≤ 3 * M / R ^ 2 * ‖s‖ := fun x hx s hs0 hs => by
    set φ : ℂ → Z := fun t => f (x, t • v) - f (x, 0) - t • D x with hφ
    have hφd : DifferentiableOn ℂ φ (ball 0 R) := by
      refine (DifferentiableOn.sub ?_ (differentiableOn_const _)).sub
        ((differentiable_id.smul_const (D x)).differentiableOn)
      exact (hsy x hx).comp (differentiable_id.smul_const v).differentiableOn fun t ht => htv t ht
    have hφ0 : φ 0 = 0 := by simp [hφ]
    have hφD : HasFDerivAt φ (0 : ℂ →L[ℂ] Z) 0 := by
      have h := ((hDt x hx).sub (hasDerivAt_const (0 : ℂ) (f (x, 0)))).sub
        ((hasDerivAt_id (0 : ℂ)).smul_const (D x))
      simp only [sub_zero, one_smul, sub_self] at h
      have h2 := h.hasFDerivAt
      rw [show ContinuousLinearMap.toSpanSingleton ℂ (0 : Z) = 0 by ext; simp] at h2
      exact h2
    have hφK : ∀ t ∈ ball (0 : ℂ) R, ‖φ t - φ 0‖ ≤ 3 * M := fun t ht => by
      rw [hφ0, sub_zero]
      have h1 := hM x hx _ (htv t ht)
      have h2 := hM x hx 0 (mem_ball_self hr₂)
      have h3 : ‖t • D x‖ ≤ M := by
        rw [norm_smul]
        have ht' : ‖t‖ ≤ R := (mem_ball_zero_iff.1 ht).le
        calc ‖t‖ * ‖D x‖ ≤ R * (M * ‖v‖ / r₂) :=
              mul_le_mul ht' (hDb x hx) (norm_nonneg _) hR0.le
          _ = M := by rw [hR]; field_simp
      calc ‖φ t‖ ≤ ‖f (x, t • v) - f (x, 0)‖ + ‖t • D x‖ := norm_sub_le _ _
        _ ≤ ‖f (x, t • v)‖ + ‖f (x, 0)‖ + ‖t • D x‖ := by gcongr; exact norm_sub_le _ _
        _ ≤ 3 * M := by linarith
    have hs2 := SchwarzCauchy.schwarz_two hφd hφK hφD hs
    rw [hφ0, sub_zero, sub_zero] at hs2
    have e : q s x - D x = s⁻¹ • φ s := by
      simp only [hq, hφ, smul_sub, smul_smul, inv_mul_cancel₀ hs0, one_smul]
    rw [e, norm_smul, norm_inv]
    have hsn : 0 < ‖s‖ := norm_pos_iff.2 hs0
    calc ‖s‖⁻¹ * ‖φ s‖ ≤ ‖s‖⁻¹ * (3 * M * (‖s‖ / R) ^ 2) := by gcongr
      _ = 3 * M / R ^ 2 * ‖s‖ := by field_simp
  -- the sequence of the difference quotients
  set s : ℕ → ℂ := fun n => (((R / 2) / ((n : ℝ) + 2) : ℝ) : ℂ) with hs
  have hsn : ∀ n, ‖s n‖ = (R / 2) / ((n : ℝ) + 2) := fun n => by
    simp only [hs, Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_pos (by positivity)
  have hs0 : ∀ n, s n ≠ 0 := fun n => by
    rw [← norm_pos_iff, hsn]; positivity
  have hsR : ∀ n, s n ∈ ball (0 : ℂ) R := fun n => by
    rw [mem_ball_zero_iff, hsn]
    rw [div_lt_iff₀ (by positivity)]
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  have hslim : Tendsto (fun n => ‖s n‖) atTop (𝓝 0) := by
    simp only [hsn]
    refine tendsto_const_nhds.div_atTop ?_
    exact tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
  set Q : ℕ → X → Z := fun n => q (s n) with hQ
  have hQd : ∀ n, DifferentiableOn ℂ (Q n) (ball 0 r₁) := fun n =>
    ((hsx _ (htv _ (hsR n))).sub (hsx 0 (mem_ball_self hr₂))).const_smul _
  have hQD : ∀ n, ∀ x ∈ ball (0 : X) r₁, ‖Q n x - D x‖ ≤ 3 * M / R ^ 2 * ‖s n‖ := fun n x hx =>
    happrox x hx (s n) (hs0 n) (hsR n)
  -- the derivatives are uniformly Cauchy on the smaller ball
  have hsub : ∀ x ∈ ball (0 : X) (r₁ / 2), ball x (r₁ / 2) ⊆ ball (0 : X) r₁ := fun x hx z hz => by
    rw [mem_ball_zero_iff] at hx ⊢
    rw [mem_ball, dist_eq_norm] at hz
    calc ‖z‖ ≤ ‖z - x‖ + ‖x‖ := by simpa using norm_add_le (z - x) x
      _ < r₁ := by linarith
  have hderiv : ∀ m n, ∀ x ∈ ball (0 : X) (r₁ / 2),
      ‖fderiv ℂ (Q m) x - fderiv ℂ (Q n) x‖ ≤ 3 * M / R ^ 2 * (‖s m‖ + ‖s n‖) / (r₁ / 2) := fun m n x hx => by
    have hx1 : x ∈ ball (0 : X) r₁ := hsub x hx (mem_ball_self (by linarith))
    have hdm := (hQd m).differentiableAt (isOpen_ball.mem_nhds hx1)
    have hdn := (hQd n).differentiableAt (isOpen_ball.mem_nhds hx1)
    have hK : ∀ z ∈ ball x (r₁ / 2), ‖(Q m - Q n) z‖ ≤ 3 * M / R ^ 2 * (‖s m‖ + ‖s n‖) := fun z hz => by
      have hz1 := hsub x hx hz
      have e : (Q m - Q n) z = (Q m z - D z) - (Q n z - D z) := by simp only [Pi.sub_apply]; abel
      rw [e]
      calc ‖(Q m z - D z) - (Q n z - D z)‖ ≤ ‖Q m z - D z‖ + ‖Q n z - D z‖ := norm_sub_le _ _
        _ ≤ 3 * M / R ^ 2 * ‖s m‖ + 3 * M / R ^ 2 * ‖s n‖ := add_le_add (hQD m z hz1) (hQD n z hz1)
        _ = _ := by ring
    have hdiff : DifferentiableOn ℂ (Q m - Q n) (ball x (r₁ / 2)) :=
      ((hQd m).sub (hQd n)).mono (hsub x hx)
    have hfd : fderiv ℂ (Q m - Q n) x = fderiv ℂ (Q m) x - fderiv ℂ (Q n) x := fderiv_sub hdm hdn
    have hC0 : 0 ≤ 3 * M / R ^ 2 * (‖s m‖ + ‖s n‖) / (r₁ / 2) := by positivity
    refine ContinuousLinearMap.opNorm_le_bound _ hC0 fun w => ?_
    have := SchwarzCauchy.cauchy_fderiv hdiff hK (mem_ball_self (by linarith)) w
    rw [hfd, sub_self, norm_zero, sub_zero] at this
    calc ‖(fderiv ℂ (Q m) x - fderiv ℂ (Q n) x) w‖ ≤ 3 * M / R ^ 2 * (‖s m‖ + ‖s n‖) * ‖w‖ / (r₁ / 2) := this
      _ = _ := by ring
  have hUC : UniformCauchySeqOn (fun n => fderiv ℂ (Q n)) atTop (ball (0 : X) (r₁ / 2)) := by
    rw [Metric.uniformCauchySeqOn_iff]
    intro ε hε
    set A := 3 * M / R ^ 2 * 2 / (r₁ / 2) + 1 with hA
    have hA0 : 0 < A := by positivity
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hslim) (ε / A) (by positivity)
    refine ⟨N, fun m hm n hn x hx => ?_⟩
    have hm' : ‖s m‖ < ε / A := by
      have := hN m hm; rwa [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] at this
    have hn' : ‖s n‖ < ε / A := by
      have := hN n hn; rwa [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] at this
    rw [dist_eq_norm]
    refine (hderiv m n x hx).trans_lt ?_
    have hδ : ε / A * A = ε := by field_simp
    have hB : 0 ≤ 3 * M / R ^ 2 / (r₁ / 2) := by positivity
    have hδ0 : 0 < ε / A := by positivity
    calc 3 * M / R ^ 2 * (‖s m‖ + ‖s n‖) / (r₁ / 2) = 3 * M / R ^ 2 / (r₁ / 2) * (‖s m‖ + ‖s n‖) := by ring
      _ ≤ 3 * M / R ^ 2 / (r₁ / 2) * (2 * (ε / A)) := by
          apply mul_le_mul_of_nonneg_left _ hB; linarith
      _ = ε / A * (A - 1) := by rw [hA]; ring
      _ < ε / A * A := by nlinarith
      _ = ε := hδ
  -- the limit of the derivatives
  set g' : X → X →L[ℂ] Z := fun x => limUnder atTop (fun n => fderiv ℂ (Q n) x) with hg'
  have hlim : ∀ x ∈ ball (0 : X) (r₁ / 2), Tendsto (fun n => fderiv ℂ (Q n) x) atTop (𝓝 (g' x)) := fun x hx =>
    (hUC.cauchySeq hx).tendsto_limUnder
  have hTU : TendstoUniformlyOn (fun n => fderiv ℂ (Q n)) g' atTop (ball (0 : X) (r₁ / 2)) :=
    hUC.tendstoUniformlyOn_of_tendsto hlim
  have hQlim : ∀ x ∈ ball (0 : X) (r₁ / 2), Tendsto (fun n => Q n x) atTop (𝓝 (D x)) := fun x hx => by
    have hx1 : x ∈ ball (0 : X) r₁ := hsub x hx (mem_ball_self (by linarith))
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => hQD n x hx1) ?_
    simpa using hslim.const_mul (3 * M / R ^ 2)
  intro x hx
  refine (hasFDerivAt_of_tendstoUniformlyOn isOpen_ball hTU (fun n z hz => ?_) hQlim hx).differentiableAt
    |>.differentiableWithinAt
  have hz1 : z ∈ ball (0 : X) r₁ := hsub z hz (mem_ball_self (by linarith))
  exact ((hQd n).differentiableAt (isOpen_ball.mem_nhds hz1)).hasFDerivAt

set_option maxHeartbeats 4000000 in
/-- **The derivative of a holomorphic map is holomorphic**: for `φ` holomorphic on `{‖x‖ < R}` and bounded,
`x ↦ φ'(x)v` is holomorphic on `{‖x‖ < R/4}`, by `deriv_param_differentiableOn` for `(x, y) ↦ φ(x + y)`. -/
theorem fderiv_apply_differentiableOn [CompleteSpace Z] {φ : X → Z} {R M : ℝ} (hR : 0 < R)
    (hφ : DifferentiableOn ℂ φ (ball (0 : X) R)) (hM : ∀ x ∈ ball (0 : X) R, ‖φ x‖ ≤ M) (v : X) :
    DifferentiableOn ℂ (fun x => fderiv ℂ φ x v) (ball (0 : X) (R / 2 / 2)) := by
  have hR2 : 0 < R / 2 := by positivity
  have hsum : ∀ p : X × X, p ∈ ball (0 : X) (R / 2) ×ˢ ball (0 : X) (R / 2) → p.1 + p.2 ∈ ball (0 : X) R :=
    fun p hp => by
      obtain ⟨h1, h2⟩ := hp
      rw [mem_ball_zero_iff] at h1 h2 ⊢
      calc ‖p.1 + p.2‖ ≤ ‖p.1‖ + ‖p.2‖ := norm_add_le _ _
        _ < R := by linarith
  set F : X × X → Z := fun p => φ (p.1 + p.2) with hF
  have hFd : DifferentiableOn ℂ F (ball (0 : X) (R / 2) ×ˢ ball (0 : X) (R / 2)) := fun p hp =>
    DifferentiableWithinAt.comp (g := φ) p (hφ _ (hsum p hp))
      ((differentiableAt_fst.add differentiableAt_snd).differentiableWithinAt) (fun q hq => hsum q hq)
  have hFM : ∀ a ∈ ball (0 : X) (R / 2), ∀ b ∈ ball (0 : X) (R / 2), ‖F (a, b)‖ ≤ M := fun a ha b hb =>
    hM _ (hsum (a, b) ⟨ha, hb⟩)
  have hD := deriv_param_differentiableOn hR2 hR2 hFd hFM v
  refine hD.congr fun x hx => ?_
  have hx' : x ∈ ball (0 : X) R := by
    rw [mem_ball_zero_iff] at hx ⊢; linarith
  have hφx : HasFDerivAt φ (fderiv ℂ φ x) (x + 0) := by
    rw [add_zero]; exact (hφ.differentiableAt (isOpen_ball.mem_nhds hx')).hasFDerivAt
  have hadd : HasFDerivAt (fun y : X => x + y) (ContinuousLinearMap.id ℂ X) 0 :=
    (hasFDerivAt_id 0).const_add x
  have hc := hφx.comp (0 : X) hadd
  rw [ContinuousLinearMap.comp_id] at hc
  show fderiv ℂ φ x v = fderiv ℂ (fun y => F (x, y)) 0 v
  rw [show (fun y => F (x, y)) = φ ∘ (fun y => x + y) from rfl, hc.fderiv]

set_option maxHeartbeats 4000000 in
/-- **The second derivative of a map of the second order**: for `φ` holomorphic on `{‖x‖ < r}` with `‖φ(x)‖ ≤ K‖x‖²`
there, the mixed second derivative at `0` satisfies `‖∂_X(φ'(·)Y)(0)‖ ≤ (16/3)K‖X‖‖Y‖`: on `{‖x‖ < R}`, `R < r`, the map is
at most `KR²`, so `‖φ'(x)Y‖ ≤ (4/3)KR‖Y‖` for `‖x‖ < R/4` by Cauchy's estimate, and Cauchy's estimate again on
`{‖x‖ < R/4}` for the holomorphic `x ↦ φ'(x)Y` (`fderiv_apply_differentiableOn`). This is the bound of the symmetric
bilinear map whose diagonal is the part of the second order (`lem:average-kernels`, the quadratic part). -/
theorem second_deriv_bound [CompleteSpace Z] {φ : X → Z} {r K : ℝ} (hr : 0 < r) (hK0 : 0 ≤ K)
    (hφ : DifferentiableOn ℂ φ (ball (0 : X) r)) (hK : ∀ x ∈ ball (0 : X) r, ‖φ x‖ ≤ K * ‖x‖ ^ 2) (Xv Yv : X) :
    ‖fderiv ℂ (fun x => fderiv ℂ φ x Yv) 0 Xv‖ ≤ 16 / 3 * K * ‖Xv‖ * ‖Yv‖ := by
  set R := r / 2 with hRdef
  have hR : 0 < R := by positivity
  have hRr : R < r := by linarith
  have hsubR : ball (0 : X) R ⊆ ball (0 : X) r := ball_subset_ball hRr.le
  have hMR : ∀ x ∈ ball (0 : X) R, ‖φ x‖ ≤ K * R ^ 2 := fun x hx => by
    have hxR : ‖x‖ < R := mem_ball_zero_iff.1 hx
    calc ‖φ x‖ ≤ K * ‖x‖ ^ 2 := hK x (hsubR hx)
      _ ≤ K * R ^ 2 := by gcongr
  have hh := fderiv_apply_differentiableOn hR (hφ.mono hsubR) hMR Yv
  have hhb : ∀ x ∈ ball (0 : X) (R / 2 / 2), ‖fderiv ℂ φ x Yv‖ ≤ 4 / 3 * K * R * ‖Yv‖ := fun x hx => by
    have hx4 : ‖x‖ < R / 4 := by have := mem_ball_zero_iff.1 hx; linarith
    have hxR : x ∈ ball (0 : X) R := mem_ball_zero_iff.2 (by linarith)
    have hc := SchwarzCauchy.cauchy_fderiv (hφ.mono hsubR) hMR hxR Yv
    rw [sub_zero] at hc
    have hden : 3 * R / 4 ≤ R - ‖x‖ := by linarith
    have hnum : 0 ≤ K * R ^ 2 * ‖Yv‖ := by positivity
    calc ‖fderiv ℂ φ x Yv‖ ≤ K * R ^ 2 * ‖Yv‖ / (R - ‖x‖) := hc
      _ ≤ K * R ^ 2 * ‖Yv‖ / (3 * R / 4) := div_le_div_of_nonneg_left hnum (by positivity) hden
      _ = 4 / 3 * K * R * ‖Yv‖ := by field_simp
  have hc2 := SchwarzCauchy.cauchy_fderiv hh hhb (mem_ball_self (by positivity)) Xv
  rw [sub_zero, norm_zero, sub_zero] at hc2
  calc ‖fderiv ℂ (fun x => fderiv ℂ φ x Yv) 0 Xv‖ ≤ 4 / 3 * K * R * ‖Yv‖ * ‖Xv‖ / (R / 2 / 2) := hc2
    _ = 16 / 3 * K * ‖Xv‖ * ‖Yv‖ := by field_simp; ring

/-- Cauchy's estimate on the half ball: a map holomorphic on `{‖x‖ < R}` and at most `K` is Lipschitz with the constant
`2K/R` on `{‖x‖ ≤ R/2}`. -/
theorem half_ball_lip {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F]
    [NormedSpace ℂ F] {f : E → F} {R K : ℝ} (hR : 0 < R) (hf : DifferentiableOn ℂ f (ball 0 R))
    (hK : ∀ y ∈ ball (0 : E) R, ‖f y‖ ≤ K) {x y : E} (hx : ‖x‖ ≤ R / 2) (hy : ‖y‖ ≤ R / 2) :
    ‖f x - f y‖ ≤ 2 * K / R * ‖x - y‖ := by
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0 (mem_ball_self hR))
  have hsub : closedBall (0 : E) (R / 2) ⊆ ball 0 R := closedBall_subset_ball (by linarith)
  have hder : ∀ z ∈ closedBall (0 : E) (R / 2), ‖fderiv ℂ f z‖ ≤ 2 * K / R := fun z hz => by
    have hzb := hsub hz
    rw [mem_closedBall, dist_zero_right] at hz
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
    have := SchwarzCauchy.cauchy_fderiv hf hK hzb v
    rw [sub_zero] at this
    calc _ ≤ K * ‖v‖ / (R - ‖z‖) := this
      _ ≤ 2 * K / R * ‖v‖ := by
          rw [div_le_iff₀ (by linarith)]
          have e : 2 * K / R * ‖v‖ * (R - ‖z‖) = K * ‖v‖ * (2 * (R - ‖z‖) / R) := by field_simp
          rw [e]
          have : 1 ≤ 2 * (R - ‖z‖) / R := by rw [le_div_iff₀ hR]; linarith
          nlinarith [mul_nonneg hK0 (norm_nonneg v)]
  exact (convex_closedBall (0 : E) (R / 2)).norm_image_sub_le_of_norm_fderiv_le
    (fun z hz => hf.differentiableAt (isOpen_ball.mem_nhds (hsub hz))) hder
    (by rw [mem_closedBall, dist_zero_right]; exact hy) (by rw [mem_closedBall, dist_zero_right]; exact hx)

set_option maxHeartbeats 4000000 in
/-- **The derivative of a holomorphic map is Lipschitz in the operator norm**: for `φ` holomorphic on `{‖x‖ < r}` and at
most `M`, `‖φ'(x) - φ'(x')‖ ≤ (32/3)(M/r²)‖x - x'‖` for `‖x‖, ‖x'‖ ≤ r/8`, from Cauchy's estimate for the holomorphic
maps `x ↦ φ'(x)w` (`fderiv_apply_differentiableOn`, `lip_half_ball`). -/
theorem fderiv_lip [CompleteSpace Z] {φ : X → Z} {r M : ℝ} (hr : 0 < r)
    (hφ : DifferentiableOn ℂ φ (ball (0 : X) r)) (hM : ∀ x ∈ ball (0 : X) r, ‖φ x‖ ≤ M) {x x' : X}
    (hx : ‖x‖ ≤ r / 8) (hx' : ‖x'‖ ≤ r / 8) :
    ‖fderiv ℂ φ x - fderiv ℂ φ x'‖ ≤ 32 / 3 * (M / r ^ 2) * ‖x - x'‖ := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (mem_ball_self hr))
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w => ?_
  have hkd := fderiv_apply_differentiableOn hr hφ hM w
  have hR : 0 < r / 2 / 2 := by positivity
  have hK : ∀ y ∈ ball (0 : X) (r / 2 / 2), ‖fderiv ℂ φ y w‖ ≤ 4 / 3 * M * ‖w‖ / r := fun y hy => by
    have hy4 : ‖y‖ < r / 4 := by have := mem_ball_zero_iff.1 hy; linarith
    have hyr : y ∈ ball (0 : X) r := mem_ball_zero_iff.2 (by linarith)
    have hc := SchwarzCauchy.cauchy_fderiv hφ hM hyr w
    rw [sub_zero] at hc
    have hden : 3 * r / 4 ≤ r - ‖y‖ := by linarith
    have hnum : 0 ≤ M * ‖w‖ := by positivity
    calc ‖fderiv ℂ φ y w‖ ≤ M * ‖w‖ / (r - ‖y‖) := hc
      _ ≤ M * ‖w‖ / (3 * r / 4) := div_le_div_of_nonneg_left hnum (by positivity) hden
      _ = 4 / 3 * M * ‖w‖ / r := by field_simp
  have hr8 : r / 2 / 2 / 2 = r / 8 := by ring
  have hl := half_ball_lip hR hkd hK (hr8 ▸ hx) (hr8 ▸ hx')
  show ‖fderiv ℂ φ x w - fderiv ℂ φ x' w‖ ≤ _
  calc ‖fderiv ℂ φ x w - fderiv ℂ φ x' w‖ ≤ 2 * (4 / 3 * M * ‖w‖ / r) / (r / 2 / 2) * ‖x - x'‖ := hl
    _ = 32 / 3 * (M / r ^ 2) * ‖x - x'‖ * ‖w‖ := by field_simp; ring

set_option maxHeartbeats 4000000 in
/-- **The chain rule of the second order** along a curve through `0`: for `φ` holomorphic and bounded on `{‖x‖ < r}`
and `b` with `b(0) = 0`, `b'(0) = b₁`, `(b')'(0) = b₂`, the map `s ↦ φ'(b(s))b'(s)` has the derivative
`∂_{b₁}(φ'(·)b₁)(0) + φ'(0)b₂` at `0`. The decomposition `φ'(b(s))b'(s) = φ'(b(s))b₁ + φ'(0)(b'(s) - b₁) +
(φ'(b(s)) - φ'(0))(b'(s) - b₁)` has a holomorphic first term, a linear second term, and a third term of the order `s²`
by `fderiv_lip`. -/
theorem second_chain [CompleteSpace Z] {φ : X → Z} {r M : ℝ} (hr : 0 < r)
    (hφ : DifferentiableOn ℂ φ (ball (0 : X) r)) (hM : ∀ x ∈ ball (0 : X) r, ‖φ x‖ ≤ M) {b : ℂ → X} {b₁ b₂ : X}
    (hb0 : b 0 = 0) (hb1 : HasDerivAt b b₁ 0) (hb2 : HasDerivAt (deriv b) b₂ 0) :
    HasDerivAt (fun s => fderiv ℂ φ (b s) (deriv b s))
      (fderiv ℂ (fun x => fderiv ℂ φ x b₁) 0 b₁ + fderiv ℂ φ 0 b₂) 0 := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (mem_ball_self hr))
  set k : X → Z := fun x => fderiv ℂ φ x b₁ with hk
  have hkd : DifferentiableAt ℂ k 0 :=
    (fderiv_apply_differentiableOn hr hφ hM b₁).differentiableAt (isOpen_ball.mem_nhds (mem_ball_self (by positivity)))
  have hd1 : HasDerivAt (fun s => k (b s)) (fderiv ℂ k 0 b₁) 0 := by
    have h0 : HasFDerivAt k (fderiv ℂ k 0) (b 0) := by rw [hb0]; exact hkd.hasFDerivAt
    exact h0.comp_hasDerivAt (0 : ℂ) hb1
  have hdb0 : deriv b 0 = b₁ := hb1.deriv
  set w : ℂ → X := fun s => deriv b s - b₁ with hw
  have hw2 : HasDerivAt w b₂ 0 := hb2.sub_const b₁
  have hw0 : w 0 = 0 := by simp [hw, hdb0]
  have hd2 : HasDerivAt (fun s => fderiv ℂ φ 0 (w s)) (fderiv ℂ φ 0 b₂) 0 :=
    (fderiv ℂ φ 0).hasFDerivAt.comp_hasDerivAt (0 : ℂ) hw2
  -- the term of the second order
  set F : ℂ → Z := fun s => (fderiv ℂ φ (b s) - fderiv ℂ φ 0) (w s) with hF
  have hbO : b =O[𝓝 (0 : ℂ)] (fun s => s) := by
    have := hb1.isBigO_sub
    simpa [hb0] using this
  have hwO : w =O[𝓝 (0 : ℂ)] (fun s => s) := by
    have := hw2.isBigO_sub
    simpa [hw0] using this
  have hbsmall : ∀ᶠ s in 𝓝 (0 : ℂ), ‖b s‖ ≤ r / 8 := by
    have hc : ContinuousAt b 0 := hb1.continuousAt
    have : ∀ᶠ s in 𝓝 (0 : ℂ), b s ∈ ball (0 : X) (r / 8) := by
      have hb0' : b 0 ∈ ball (0 : X) (r / 8) := by rw [hb0]; exact mem_ball_self (by positivity)
      exact hc.preimage_mem_nhds (isOpen_ball.mem_nhds hb0')
    filter_upwards [this] with s hs using (mem_ball_zero_iff.1 hs).le
  have hLO : (fun s => fderiv ℂ φ (b s) - fderiv ℂ φ 0) =O[𝓝 (0 : ℂ)] b := by
    refine Asymptotics.IsBigO.of_bound (32 / 3 * (M / r ^ 2)) ?_
    filter_upwards [hbsmall] with s hs
    have := fderiv_lip hr hφ hM hs (by simp; positivity : ‖(0 : X)‖ ≤ r / 8)
    simpa using this
  have hprod : (fun s => ‖fderiv ℂ φ (b s) - fderiv ℂ φ 0‖ * ‖w s‖) =O[𝓝 (0 : ℂ)] (fun s : ℂ => s * s) :=
    ((hLO.trans hbO).norm_left).mul hwO.norm_left
  have hFO : F =O[𝓝 (0 : ℂ)] (fun s => ‖fderiv ℂ φ (b s) - fderiv ℂ φ 0‖ * ‖w s‖) :=
    Asymptotics.IsBigO.of_bound 1 (Filter.Eventually.of_forall fun s => by
      rw [one_mul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact ContinuousLinearMap.le_opNorm _ _)
  have hFo : F =o[𝓝 (0 : ℂ)] (fun s => s) := by
    have hsq : (fun s : ℂ => s * s) =o[𝓝 (0 : ℂ)] (fun s => s) := by
      have := Asymptotics.isLittleO_pow_id (𝕜 := ℂ) (n := 2) (by norm_num)
      simpa [pow_two] using this
    exact (hFO.trans hprod).trans_isLittleO hsq
  have hF0 : F 0 = 0 := by simp [hF, hw0]
  have hd3 : HasDerivAt F 0 0 := by
    rw [hasDerivAt_iff_isLittleO_nhds_zero]
    simpa [hF0] using hFo
  have hsum := (hd1.add hd2).add hd3
  rw [add_zero] at hsum
  refine hsum.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
  simp only [Pi.add_apply, hF, hw, hk, ContinuousLinearMap.sub_apply, map_sub]
  abel

end ParamDeriv
end CoreLean

end
