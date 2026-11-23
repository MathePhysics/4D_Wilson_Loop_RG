/-
`lem:ward` of BALABAN_CORE.tex, the master identity `eq:ward-master` up to the fourth order.

Setting. Configurations on a finite set of bonds `Bd`, with the ends `b₋ = mn b`, `b₊ = pl b` in a finite set
of sites `St`, take values in a complete normed `ℂ`-algebra `𝔸` with `‖1‖ = 1` (`M_N(ℂ)` with the operator
norm in the core). `E` is analytic on a ball about the trivial configuration (the core's "holomorphic";
the two notions agree in finite dimensions by the Cauchy formula in several variables, which Mathlib does
not have), and invariant under the complex gauge transformations `e^{iλ}` near `id`
(`(U^{e^{iλ}})(b) = e^{iλ(b₋)}U(b)e^{-iλ(b₊)}`; this invariance is derived from the real one in
`WardComplex.lean`). With `F(B) = E(e^{iB})`, `X_b = -ad(iB(b))`, and
`H₃(B)(b) = Q₋(X_b)λ(b₋) + Q₊(X_b)λ(b₊) = -dλ(b) + ½i[λ(b₋) + λ(b₊), B(b)] + (1/12)[B(b), [B(b), dλ(b)]]`,
the derivative of the invariance with respect to `λ` gives `DF(B)[H₃(B)] = O(‖B‖⁴)` (`master`), which is
`eq:ward-master` to the order which the lemma uses.
-/
import CoreLean.WardSeries

open NormedSpace BakerCampbellHausdorff Filter Asymptotics
open scoped Topology

noncomputable section

namespace CoreLean

namespace Ward

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸] [CompleteSpace 𝔸] [NormOneClass 𝔸]
variable {Bd St : Type*} [Fintype Bd] [Fintype St]

/-- The configuration `e^{iB}`. -/
def expI (B : Bd → 𝔸) : Bd → 𝔸 := fun b => exp (Complex.I • B b)

/-- The complex gauge transform of `U` by `e^{iλ}`: `e^{iλ(b₋)}U(b)e^{-iλ(b₊)}`. -/
def gauge (mn pl : Bd → St) (l : St → 𝔸) (U : Bd → 𝔸) : Bd → 𝔸 :=
  fun b => exp (Complex.I • l (mn b)) * U b * exp (-(Complex.I • l (pl b)))

/-- `X_b = -ad(iB(b))`. -/
def adX (B : Bd → 𝔸) (b : Bd) : 𝔸 →L[ℂ] 𝔸 := -ad ℂ (Complex.I • B b)

/-- The approximate solution `H₃(B)(b) = Q₋(X_b)λ(b₋) + Q₊(X_b)λ(b₊)`. -/
def H3 (mn pl : Bd → St) (l : St → 𝔸) (B : Bd → 𝔸) : Bd → 𝔸 :=
  fun b => Qm (adX B b) (l (mn b)) + Qp (adX B b) (l (pl b))

/-- The derivative of `B ↦ e^{iB}`: `V ↦ (e^{iB(b)}φ(X_b)(iV(b)))_b`. -/
def dExpI (B : Bd → 𝔸) : (Bd → 𝔸) →L[ℂ] (Bd → 𝔸) :=
  ContinuousLinearMap.pi fun b =>
    (mulLeft ℂ (exp (Complex.I • B b)) * expSubOneDiv ℂ (adX B b)).comp
      (Complex.I • ContinuousLinearMap.proj b)

lemma dExpI_apply (B V : Bd → 𝔸) (b : Bd) :
    dExpI B V b = exp (Complex.I • B b) * (Complex.I • expSubOneDiv ℂ (adX B b) (V b)) := by
  simp [dExpI, ContinuousLinearMap.mul_apply, mulLeft_apply, map_smul]

lemma hasFDerivAt_expI (B : Bd → 𝔸) : HasFDerivAt (expI (Bd := Bd) (𝔸 := 𝔸)) (dExpI B) B := by
  refine hasFDerivAt_pi'.mpr fun b => ?_
  have h1 : HasFDerivAt (fun B : Bd → 𝔸 => Complex.I • B b)
      (Complex.I • ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Bd => 𝔸) b) B :=
    (hasFDerivAt_apply b B).const_smul Complex.I
  have h2 := hasFDerivAt_exp (𝕂 := ℂ) (Complex.I • B b)
  have h3 := h2.comp B h1
  convert h3 using 1
  ext V
  · rfl
  · simp [dExpI, adX]

lemma expI_zero : expI (0 : Bd → 𝔸) = 1 := by
  funext b; simp [expI]

lemma continuous_expI : Continuous (expI (Bd := Bd) (𝔸 := 𝔸)) :=
  continuous_pi fun b => (continuous_iff_continuousAt.mpr fun x =>
    (NormedSpace.exp_analytic (𝕂 := ℂ) x).continuousAt).comp ((continuous_apply b).const_smul _)

/-- The derivative of the invariance with respect to `t` at `t = 0`, for the gauge function `tλ`:
`DE(U)[(iλ(b₋)U(b) - U(b)iλ(b₊))_b] = 0`. -/
lemma fderiv_gauge_eq_zero (mn pl : Bd → St) (E : (Bd → 𝔸) → ℂ) (l : St → 𝔸) (U : Bd → 𝔸)
    (hdiff : DifferentiableAt ℂ E U)
    (hconst : ∀ᶠ t in 𝓝 (0 : ℂ), E (gauge mn pl (t • l) U) = E U) :
    fderiv ℂ E U (fun b => Complex.I • l (mn b) * U b - U b * (Complex.I • l (pl b))) = 0 := by
  set g : ℂ → Bd → 𝔸 := fun t => gauge mn pl (t • l) U
  have hg : HasDerivAt g (fun b => Complex.I • l (mn b) * U b - U b * (Complex.I • l (pl b))) 0 := by
    refine hasDerivAt_pi.mpr fun b => ?_
    have e : (fun t : ℂ => g t b) = fun t => exp (t • (Complex.I • l (mn b))) * U b *
        exp (t • (-(Complex.I • l (pl b)))) := by
      funext t
      simp only [g, gauge, Pi.smul_apply, smul_neg]
      rw [smul_comm t Complex.I, smul_comm t Complex.I]
    rw [e]
    have h := ((hasDerivAt_exp_smul_const (𝕂 := ℂ) (Complex.I • l (mn b)) 0).mul_const (U b)).mul
      (hasDerivAt_exp_smul_const (𝕂 := ℂ) (-(Complex.I • l (pl b))) 0)
    convert h using 1
    simp only [zero_smul, exp_zero, one_mul, mul_one, mul_neg, sub_eq_add_neg]
  have hg0 : g 0 = U := by funext b; simp [g, gauge]
  have h1 : HasDerivAt (E ∘ g) (fderiv ℂ E U
      (fun b => Complex.I • l (mn b) * U b - U b * (Complex.I • l (pl b)))) 0 :=
    (hdiff.hasFDerivAt).comp_hasDerivAt_of_eq 0 hg hg0.symm
  have h2 : HasDerivAt (E ∘ g) 0 0 :=
    (hasDerivAt_const (0 : ℂ) (E U)).congr_of_eventuallyEq (hconst.mono fun t ht => ht)
  exact h1.unique h2

/-- The derivative of `B ↦ e^{iB}` applied to `H₃(B)`, minus the tangent vector of the gauge
transformations, is `e^{iB(b)}i((φQ₋ - e^X)λ(b₋) + (φQ₊ + 1)λ(b₊))`. -/
lemma dExpI_H3_sub (mn pl : Bd → St) (l : St → 𝔸) (B : Bd → 𝔸) (b : Bd) :
    dExpI B (H3 mn pl l B) b -
        (Complex.I • l (mn b) * expI B b - expI B b * (Complex.I • l (pl b))) =
      exp (Complex.I • B b) * (Complex.I •
        ((expSubOneDiv ℂ (adX B b) * Qm (adX B b) - exp (adX B b)) (l (mn b)) +
          (expSubOneDiv ℂ (adX B b) * Qp (adX B b) + 1) (l (pl b)))) := by
  rw [dExpI_apply]
  simp only [H3, map_add, ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply, expI]
  -- `e^{X}λ = e^{-iB}λe^{iB}`
  have hX : exp (adX B b) (l (mn b)) =
      exp (-(Complex.I • B b)) * l (mn b) * exp (Complex.I • B b) := by
    rw [adX, ← ad_neg, exp_ad_apply, neg_neg]
  rw [hX]
  have hu : exp (Complex.I • B b) * exp (-(Complex.I • B b)) = 1 := exp_mul_exp_neg ℂ _
  simp only [smul_add, smul_sub, mul_add, mul_sub, mul_smul_comm, smul_mul_assoc]
  have e : exp (Complex.I • B b) * (exp (-(Complex.I • B b)) * l (mn b) * exp (Complex.I • B b)) =
      l (mn b) * exp (Complex.I • B b) := by
    rw [← mul_assoc, ← mul_assoc, hu, one_mul]
  rw [e]
  abel

/-- `‖e^x‖ ≤ e^{‖x‖}` when `‖1‖ = 1`. -/
lemma norm_exp_le_exp_norm (x : 𝔸) : ‖exp x‖ ≤ Real.exp ‖x‖ := by
  have h := norm_exp_sub_one_le (𝕂 := ℂ) x
  calc ‖exp x‖ = ‖(exp x - 1) + 1‖ := by rw [sub_add_cancel]
    _ ≤ ‖exp x - 1‖ + ‖(1 : 𝔸)‖ := norm_add_le _ _
    _ ≤ Real.exp ‖x‖ := by rw [norm_one]; linarith

/-- The pointwise bound of the difference, for `‖B‖ ≤ ½`. -/
lemma norm_dExpI_H3_sub_le (mn pl : Bd → St) (l : St → 𝔸) (B : Bd → 𝔸) (hB : ‖B‖ ≤ 1 / 2) :
    ‖dExpI B (H3 mn pl l B) -
        (fun b => Complex.I • l (mn b) * expI B b - expI B b * (Complex.I • l (pl b)))‖ ≤
      640 * ‖l‖ * ‖B‖ ^ 4 := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun b => ?_
  simp only [Pi.sub_apply]
  rw [dExpI_H3_sub]
  set X := adX B b
  have hBb : ‖B b‖ ≤ ‖B‖ := norm_le_pi_norm B b
  have hX : ‖X‖ ≤ 2 * ‖B‖ := by
    simp only [X, adX, norm_neg]
    refine (norm_ad_le _).trans ?_
    rw [norm_smul, Complex.norm_I, one_mul]
    linarith
  have hX1 : ‖X‖ ≤ 1 := by linarith
  have h1 : ‖(1 : 𝔸 →L[ℂ] 𝔸)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  have hm := norm_φQm_sub_exp_le h1 hX1
  have hp := norm_φQp_add_one_le h1 hX1
  have hlm : ‖l (mn b)‖ ≤ ‖l‖ := norm_le_pi_norm l _
  have hlp : ‖l (pl b)‖ ≤ ‖l‖ := norm_le_pi_norm l _
  have hU : ‖exp (Complex.I • B b)‖ ≤ 2 := by
    refine (norm_exp_le_exp_norm _).trans ?_
    rw [norm_smul, Complex.norm_I, one_mul]
    calc Real.exp ‖B b‖ ≤ Real.exp (1 / 2) := Real.exp_le_exp.mpr (by linarith)
      _ ≤ 2 := by
        have := Real.exp_one_lt_d9
        have h2 : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by
          rw [← Real.exp_nat_mul]; norm_num
        nlinarith [Real.exp_pos (1 / 2)]
  have hX4 : ‖X‖ ^ 4 ≤ 16 * ‖B‖ ^ 4 := by
    calc ‖X‖ ^ 4 ≤ (2 * ‖B‖) ^ 4 := pow_le_pow_left₀ (norm_nonneg _) hX 4
      _ = 16 * ‖B‖ ^ 4 := by ring
  have hw : ‖(expSubOneDiv ℂ X * Qm X - exp X) (l (mn b)) +
      (expSubOneDiv ℂ X * Qp X + 1) (l (pl b))‖ ≤ 10 * ‖X‖ ^ 4 * (2 * ‖l‖) := by
    refine (norm_add_le _ _).trans ?_
    have a1 := (ContinuousLinearMap.le_opNorm (expSubOneDiv ℂ X * Qm X - exp X) (l (mn b))).trans
      (mul_le_mul hm hlm (norm_nonneg _) (by positivity))
    have a2 := (ContinuousLinearMap.le_opNorm (expSubOneDiv ℂ X * Qp X + 1) (l (pl b))).trans
      (mul_le_mul hp hlp (norm_nonneg _) (by positivity))
    linarith
  calc ‖exp (Complex.I • B b) * (Complex.I • ((expSubOneDiv ℂ X * Qm X - exp X) (l (mn b)) +
        (expSubOneDiv ℂ X * Qp X + 1) (l (pl b))))‖
      ≤ ‖exp (Complex.I • B b)‖ * ‖(expSubOneDiv ℂ X * Qm X - exp X) (l (mn b)) +
          (expSubOneDiv ℂ X * Qp X + 1) (l (pl b))‖ := by
        refine (norm_mul_le _ _).trans (le_of_eq ?_)
        rw [norm_smul, Complex.norm_I, one_mul]
    _ ≤ 2 * (10 * (16 * ‖B‖ ^ 4) * (2 * ‖l‖)) := by
        refine mul_le_mul hU (hw.trans ?_) (norm_nonneg _) (by norm_num)
        have := norm_nonneg l
        nlinarith
    _ = 640 * ‖l‖ * ‖B‖ ^ 4 := by ring

/-- `eq:ward-master` to the fourth order: `DF(B)[H₃(B)] = O(‖B‖⁴)` for `F(B) = E(e^{iB})`. -/
theorem master (mn pl : Bd → St) (gc : Submodule ℂ 𝔸) (E : (Bd → 𝔸) → ℂ) {ρ ε : ℝ} (hρ : 0 < ρ)
    (hε : 0 < ε)
    (hE : AnalyticOnNhd ℂ E (Metric.ball 1 ρ))
    (hinv : ∀ (B : Bd → 𝔸) (l : St → 𝔸), (∀ x, l x ∈ gc) → ‖B‖ < ε → ‖l‖ < ε →
      E (gauge mn pl l (expI B)) = E (expI B))
    (l : St → 𝔸) (hl : ∀ x, l x ∈ gc) :
    (fun B => fderiv ℂ (E ∘ expI) B (H3 mn pl l B)) =O[𝓝 0] fun B => ‖B‖ ^ 4 := by
  -- the configurations `e^{iB}` near `1`
  have hcont : ContinuousAt (expI (Bd := Bd) (𝔸 := 𝔸)) 0 := continuous_expI.continuousAt
  have hball : ∀ᶠ B in 𝓝 (0 : Bd → 𝔸), expI B ∈ Metric.ball (1 : Bd → 𝔸) ρ := by
    have := hcont (Metric.ball_mem_nhds _ hρ)
    rwa [expI_zero] at this
  -- the derivative of `E` is bounded near `1`
  have hfd := (hE.fderiv 1 (Metric.mem_ball_self hρ)).continuousAt
  have hM : ∀ᶠ B in 𝓝 (0 : Bd → 𝔸), ‖fderiv ℂ E (expI B)‖ < ‖fderiv ℂ E 1‖ + 1 := by
    have h := hfd.norm.comp_of_eq hcont expI_zero
    have h' : ((fun x => ‖fderiv ℂ E x‖) ∘ expI) (0 : Bd → 𝔸) < ‖fderiv ℂ E 1‖ + 1 := by
      simp only [Function.comp, expI_zero]; exact lt_add_one _
    simpa only [Function.comp] using h.eventually (gt_mem_nhds h')
  have hsmall : ∀ᶠ B in 𝓝 (0 : Bd → 𝔸), ‖B‖ < min ε (1 / 2) := by
    have := Metric.ball_mem_nhds (0 : Bd → 𝔸) (lt_min hε (by norm_num : (0 : ℝ) < 1 / 2))
    filter_upwards [this] with B hB
    simpa using hB
  refine IsBigO.of_bound ((‖fderiv ℂ E (1 : Bd → 𝔸)‖ + 1) * (640 * ‖l‖)) ?_
  filter_upwards [hball, hM, hsmall] with B hB hMB hsB
  have hBε : ‖B‖ < ε := lt_of_lt_of_le hsB (min_le_left _ _)
  have hB2 : ‖B‖ ≤ 1 / 2 := (lt_of_lt_of_le hsB (min_le_right _ _)).le
  have hdiff : DifferentiableAt ℂ E (expI B) := (hE _ hB).differentiableAt
  -- the chain rule
  have hchain : fderiv ℂ (E ∘ expI) B = (fderiv ℂ E (expI B)).comp (dExpI B) :=
    (hdiff.hasFDerivAt.comp B (hasFDerivAt_expI B)).fderiv
  -- the invariance in the direction `λ`
  have hconst : ∀ᶠ t in 𝓝 (0 : ℂ), E (gauge mn pl (t • l) (expI B)) = E (expI B) := by
    have hlim : Tendsto (fun t : ℂ => ‖t • l‖) (𝓝 0) (𝓝 0) := by
      have : Continuous fun t : ℂ => ‖t • l‖ := (continuous_id.smul continuous_const).norm
      simpa using this.tendsto 0
    filter_upwards [hlim (gt_mem_nhds hε)] with t ht
    exact hinv B (t • l) (fun x => gc.smul_mem t (hl x)) hBε ht
  have h0 := fderiv_gauge_eq_zero mn pl E l (expI B) hdiff hconst
  have hW := norm_dExpI_H3_sub_le mn pl l B hB2
  rw [hchain, ContinuousLinearMap.comp_apply, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  set T : Bd → 𝔸 := fun b => Complex.I • l (mn b) * expI B b - expI B b * (Complex.I • l (pl b))
  have e : dExpI B (H3 mn pl l B) = (dExpI B (H3 mn pl l B) - T) + T := by abel
  rw [e, map_add, h0, add_zero]
  calc ‖fderiv ℂ E (expI B) (dExpI B (H3 mn pl l B) - T)‖
      ≤ ‖fderiv ℂ E (expI B)‖ * ‖dExpI B (H3 mn pl l B) - T‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ (‖fderiv ℂ E 1‖ + 1) * (640 * ‖l‖ * ‖B‖ ^ 4) :=
        mul_le_mul hMB.le hW (norm_nonneg _) (by positivity)
    _ = (‖fderiv ℂ E 1‖ + 1) * (640 * ‖l‖) * ‖B‖ ^ 4 := by ring

end Ward

end CoreLean
