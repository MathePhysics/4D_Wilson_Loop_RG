/-
`lem:product` of BALABAN_CORE.tex, the function `Ψ(X, Y) = i⁻¹ Log(e^{iX} e^{iY})`.

`Log W = Σ_{n ≥ 1} (-1)^{n+1} n⁻¹ (W - 1)ⁿ` (`def:chart`) is `log1p ℂ (W - 1)` of the library
`BakerCampbellHausdorff` (its coefficients `logCoeff (n+1) = (-1)ⁿ/(n+1)` were checked), so that
`Ψ(X, Y) = -i bch(iX, iY)`. From the library (statements rechecked): `exp_bch_of_norm_lt`,
`bch_zero_left`, `bch_zero_right` (`‖·‖ < 1/4`), `analyticOnNhd_bch` (`‖X‖ + ‖Y‖ < log 2`),
`norm_bch_le`, and `bch_mem_of_isScalarTower` (a closed real submodule closed under commutators,
`‖X‖ + ‖Y‖ < 1/10`).

That `Ψ` takes values in `𝔤^c` is proved here by the Lie-algebraic BCH theorem applied to the closed
real Lie subalgebra `𝔤^c`, and not, as in the core, through `lem:chart`(ii) and the vanishing of the
holomorphic function `(1 - π)Ψ`; `lem:chart`(ii) is therefore not used.
-/
import CoreLean.ProductExp
import BakerCampbellHausdorff.Lie

open NormedSpace BakerCampbellHausdorff
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace CoreLean

variable {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "GLN" => (Matrix (Fin N) (Fin N) ℂ)ˣ

/-- `Log W = Σ_{n ≥ 1} (-1)^{n+1} n⁻¹ (W - 1)ⁿ` (`def:chart`). -/
def LogM (W : Mat) : Mat := log1p ℂ (W - 1)

/-- `Ψ(X, Y) = i⁻¹ Log(e^{iX} e^{iY})` (`eq:product`). -/
def psi (X Y : Mat) : Mat := (-Complex.I) • bch ℂ (Complex.I • X) (Complex.I • Y)

lemma psi_eq_Log (X Y : Mat) :
    psi X Y = (Complex.I)⁻¹ • LogM (exp (Complex.I • X) * exp (Complex.I • Y)) := by
  rw [psi, LogM, bch, Complex.inv_I]

lemma norm_I_smul' (X : Mat) : ‖Complex.I • X‖ = ‖X‖ := norm_I_smul X

/-- `e^{iΨ(X, Y)} = e^{iX} e^{iY}` for `‖X‖ + ‖Y‖ < log 2`. -/
theorem exp_I_psi {X Y : Mat} (h : ‖X‖ + ‖Y‖ < Real.log 2) :
    exp (Complex.I • psi X Y) = exp (Complex.I • X) * exp (Complex.I • Y) := by
  rw [psi, smul_smul, mul_neg, Complex.I_mul_I, neg_neg, one_smul]
  exact exp_bch (𝕂 := ℂ) (by rwa [norm_I_smul', norm_I_smul'])

theorem psi_zero_right {X : Mat} (hX : ‖X‖ < 1 / 4) : psi X 0 = X := by
  rw [psi, smul_zero, bch_zero_right (by rwa [norm_I_smul']), smul_smul, neg_mul,
    Complex.I_mul_I, neg_neg, one_smul]

theorem psi_zero_left {Y : Mat} (hY : ‖Y‖ < 1 / 4) : psi 0 Y = Y := by
  rw [psi, smul_zero, bch_zero_left (by rwa [norm_I_smul']), smul_smul, neg_mul,
    Complex.I_mul_I, neg_neg, one_smul]

/-- `Ψ` is holomorphic on `‖X‖ + ‖Y‖ < log 2`. -/
theorem analyticOnNhd_psi :
    AnalyticOnNhd ℂ (fun w : Mat × Mat => psi w.1 w.2) {v | ‖v.1‖ + ‖v.2‖ < Real.log 2} := by
  set L : Mat × Mat →L[ℂ] Mat × Mat :=
    (ContinuousLinearMap.prodMap (Complex.I • ContinuousLinearMap.id ℂ Mat)
      (Complex.I • ContinuousLinearMap.id ℂ Mat))
  have hL : ∀ w, L w = (Complex.I • w.1, Complex.I • w.2) := fun w => rfl
  have hB := analyticOnNhd_bch (𝕂 := ℂ) (𝔸 := Mat)
  have hcomp : AnalyticOnNhd ℂ (fun w : Mat × Mat => bch ℂ (L w).1 (L w).2)
      {v | ‖v.1‖ + ‖v.2‖ < Real.log 2} :=
    hB.comp (L.analyticOnNhd _) fun w hw => by
      simp only [Set.mem_setOf_eq, hL, norm_I_smul'] at hw ⊢; exact hw
  intro w hw
  exact (hcomp w hw).const_smul (c := -Complex.I)

/-! ### `Ψ` takes values in `𝔤^c` -/

variable {G : GaugeGroup N}

/-- `𝔤^c` as a real subspace. -/
def lieCReal (hG : G.LieInput) : Submodule ℝ Mat := (GaugeGroup.lieCSubmodule hG).restrictScalars ℝ

theorem psi_mem (hG : G.LieInput) {X Y : Mat} (hX : X ∈ G.lieC) (hY : Y ∈ G.lieC)
    (h : ‖X‖ + ‖Y‖ < 1 / 10) : psi X Y ∈ G.lieC := by
  have hcl : IsClosed (lieCReal hG : Set Mat) := Submodule.closed_of_finiteDimensional _
  have hlie : ∀ x ∈ lieCReal hG, ∀ y ∈ lieCReal hG, x * y - y * x ∈ lieCReal hG :=
    fun x hx y hy => GaugeGroup.commutator_mem_lieC hG hx hy
  have hIX : Complex.I • X ∈ lieCReal hG := (GaugeGroup.lieCSubmodule hG).smul_mem _ hX
  have hIY : Complex.I • Y ∈ lieCReal hG := (GaugeGroup.lieCSubmodule hG).smul_mem _ hY
  have hb := bch_mem_of_isScalarTower (𝕂 := ℂ) hcl hlie hIX hIY
    (by rwa [norm_I_smul', norm_I_smul'])
  exact (GaugeGroup.lieCSubmodule hG).smul_mem _ hb

/-! ### Covariance -/

/-- `Ad_W` as a continuous linear equivalence of `M_N(ℂ)`. -/
def AdCLE (W : GLN) : Mat ≃L[ℂ] Mat :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := Ad W
      invFun := Ad W⁻¹
      map_add' := fun X Y => by simp [Ad, mul_add, add_mul]
      map_smul' := fun c X => by simp [Ad]
      left_inv := fun X => by simp [Ad, ← mul_assoc]
      right_inv := fun X => by simp [Ad, ← mul_assoc] }

lemma Ad_pow (W : GLN) (A : Mat) (n : ℕ) : Ad W A ^ n = Ad W (A ^ n) := by
  induction n with
  | zero => simp [Ad]
  | succ n ih =>
    rw [pow_succ, ih, pow_succ]
    simp only [Ad, mul_assoc, Units.inv_mul_cancel_left]

lemma Ad_sub_one (W : GLN) (A : Mat) : Ad W A - 1 = Ad W (A - 1) := by
  simp [Ad, mul_sub, sub_mul]

/-- `Log(W A W⁻¹) = Ad_W Log A`, unconditionally (the series is mapped termwise by the linear
equivalence `Ad_W`). -/
theorem LogM_Ad (W : GLN) (A : Mat) : LogM (Ad W A) = Ad W (LogM A) := by
  rw [LogM, LogM, Ad_sub_one, log1p_eq_tsum, log1p_eq_tsum]
  have h := (AdCLE W).map_tsum (L := SummationFilter.unconditional ℕ)
    (f := fun n => logCoeff ℂ n • (A - 1) ^ n)
  change _ = AdCLE W _
  rw [h]
  refine tsum_congr fun n => ?_
  change _ = Ad W (logCoeff ℂ n • (A - 1) ^ n)
  rw [Ad_pow]
  simp [Ad]

/-- The covariance of `Ψ`: `Ad_W Ψ(X, Y) = Ψ(Ad_W X, Ad_W Y)` for every invertible `W` (the core
states it for `W ∈ G`). -/
theorem Ad_psi (W : GLN) (X Y : Mat) : Ad W (psi X Y) = psi (Ad W X) (Ad W Y) := by
  have hX : Complex.I • Ad W X = Ad W (Complex.I • X) := by simp [Ad]
  have hY : Complex.I • Ad W Y = Ad W (Complex.I • Y) := by simp [Ad]
  have hexp : ∀ Z : Mat, exp (Ad W Z) = Ad W (exp Z) := fun Z => by
    rw [← expU_val, ← expU_conj]; simp [Ad]
  rw [psi, psi, bch, bch, hX, hY, hexp, hexp,
    show Ad W (exp (Complex.I • X)) * Ad W (exp (Complex.I • Y)) =
      Ad W (exp (Complex.I • X) * exp (Complex.I • Y)) by simp [Ad, mul_assoc],
    ← LogM, ← LogM, LogM_Ad]
  simp [Ad]

/-! ### `eq:product-lipschitz` -/

lemma log_two_gt_eighth : (1 : ℝ) / 8 < Real.log 2 := by
  have := Real.log_two_gt_d9; norm_num at this ⊢; linarith

/-- `|Log W| ≤ 1/4` for `W = e^{iX}e^{iY}`, `‖X‖, ‖Y‖ ≤ 1/16`: `‖Ψ(X, Y)‖ ≤ 1/4`. -/
theorem norm_psi_le {X Y : Mat} (hX : ‖X‖ ≤ 1 / 16) (hY : ‖Y‖ ≤ 1 / 16) : ‖psi X Y‖ ≤ 1 / 4 := by
  have hs : ‖Complex.I • X‖ + ‖Complex.I • Y‖ ≤ 1 / 8 := by
    rw [norm_I_smul', norm_I_smul']; linarith
  have hlt : ‖Complex.I • X‖ + ‖Complex.I • Y‖ < Real.log 2 := lt_of_le_of_lt hs log_two_gt_eighth
  have hb := norm_bch_le (𝕂 := ℂ) hlt
  rw [psi, norm_smul, norm_neg, Complex.norm_I, one_mul]
  refine hb.trans ?_
  set s := ‖Complex.I • X‖ + ‖Complex.I • Y‖
  -- `e^s ≤ e^{1/8} ≤ 1 + 1/8 + 1/64`, by `Real.exp_bound` with `n = 2`
  have he : Real.exp s ≤ 1 + 1 / 8 + 1 / 64 := by
    have h2 := Real.exp_bound (x := 1 / 8) (by norm_num) (n := 2) (by norm_num)
    simp only [Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton, pow_zero,
      Nat.factorial_zero, Nat.cast_one, div_one, pow_one, Nat.factorial_one] at h2
    have h3 := (abs_le.1 h2).2
    norm_num at h3
    have := Real.exp_le_exp.2 hs
    linarith
  -- `e^{-1/4} ≤ 4/5 ≤ 2 - e^s`
  have h1 : Real.exp (-(1 / 4 : ℝ)) ≤ 2 - Real.exp s := by
    have h4 := Real.add_one_le_exp (1 / 4 : ℝ)
    rw [Real.exp_neg]
    have : (Real.exp (1 / 4))⁻¹ ≤ 4 / 5 := by
      rw [inv_le_comm₀ (Real.exp_pos _) (by norm_num)]; linarith
    linarith
  have := Real.log_le_log (Real.exp_pos _) h1
  rw [Real.log_exp] at this
  linarith

/-- The core's argument for `eq:product-lipschitz`, for a holomorphic `F` of two variables which is
bounded by `1/2` and vanishes on `Y = 0`: Cauchy's estimate in the first variable and the lemma of
Schwarz in the second give `‖∂₁F(X, Y)‖ ≤ 256 ‖Y‖`, and the mean value inequality the claim. -/
theorem norm_sub_le_of_vanish {F : Mat × Mat → Mat}
    (hA : AnalyticOnNhd ℂ F {v | ‖v.1‖ + ‖v.2‖ < Real.log 2})
    (hB : ∀ X Y : Mat, ‖X‖ ≤ 1 / 16 → ‖Y‖ ≤ 1 / 16 → ‖F (X, Y)‖ ≤ 1 / 2)
    (h0 : ∀ X : Mat, ‖X‖ < 1 / 4 → F (X, 0) = 0)
    {X X' Y : Mat} (hX : ‖X‖ ≤ 1 / 32) (hX' : ‖X'‖ ≤ 1 / 32) (hY : ‖Y‖ ≤ 1 / 32) :
    ‖F (X', Y) - F (X, Y)‖ ≤ 256 * ‖Y‖ * ‖X' - X‖ := by
  set U := {v : Mat × Mat | ‖v.1‖ + ‖v.2‖ < Real.log 2}
  have hl2 := log_two_gt_eighth
  have hU : ∀ X Y : Mat, ‖X‖ ≤ 1 / 16 → ‖Y‖ ≤ 1 / 16 → (X, Y) ∈ U := fun X Y hX hY => by
    simp only [U, Set.mem_setOf_eq]; linarith
  -- the partial derivative in the first variable
  have hpart : ∀ X Y : Mat, (X, Y) ∈ U → HasFDerivAt (fun Z => F (Z, Y))
      ((fderiv ℂ F (X, Y)).comp (ContinuousLinearMap.inl ℂ Mat Mat)) X :=
    fun X Y h => (hA _ h).differentiableAt.hasFDerivAt.comp X (hasFDerivAt_prodMk_left X Y)
  -- Cauchy's estimate: `‖∂₁F(X, Y) δ‖ ≤ 16‖δ‖` for `‖X‖ ≤ 1/32`, `‖Y‖ ≤ 1/16`
  have hcauchy : ∀ X Y δ : Mat, ‖X‖ ≤ 1 / 32 → ‖Y‖ ≤ 1 / 16 →
      ‖fderiv ℂ F (X, Y) (δ, 0)‖ ≤ 16 * ‖δ‖ := by
    intro X Y δ hX hY
    rcases eq_or_ne δ 0 with rfl | hδ
    · have : ((0 : Mat), (0 : Mat)) = 0 := rfl
      rw [this, map_zero]; simp
    have hδp : 0 < ‖δ‖ := norm_pos_iff.2 hδ
    set R := 1 / (32 * ‖δ‖) with hRdef
    have hR : 0 < R := by positivity
    have hRδ : R * ‖δ‖ = 1 / 32 := by rw [hRdef]; field_simp
    have hline : ∀ t : ℂ, ‖t‖ ≤ R → ‖X + t • δ‖ ≤ 1 / 16 := fun t ht => by
      calc ‖X + t • δ‖ ≤ ‖X‖ + ‖t‖ * ‖δ‖ := by
            refine (norm_add_le _ _).trans ?_; rw [norm_smul]
        _ ≤ 1 / 32 + R * ‖δ‖ := by gcongr
        _ = 1 / 16 := by rw [hRδ]; norm_num
    -- `g(t) = F(X + tδ, Y)`; the types are inferred from the chain rule, in the normed structure
    have hl := fun t : ℂ => ((hasDerivAt_id t).smul_const δ).const_add X
    have hgd := fun (t : ℂ) (ht : ‖t‖ ≤ R) =>
      (hpart _ Y (hU _ Y (hline t ht) hY)).comp_hasDerivAt t (hl t)
    have hdc : DiffContOnCl ℂ ((fun Z => F (Z, Y)) ∘ fun t : ℂ => X + id t • δ)
        (Metric.ball 0 R) := by
      refine DifferentiableOn.diffContOnCl ?_
      rw [closure_ball 0 hR.ne']
      intro t ht
      exact (hgd t (mem_closedBall_zero_iff.1 ht)).differentiableAt.differentiableWithinAt
    have hsph : ∀ t ∈ Metric.sphere (0 : ℂ) R,
        ‖((fun Z => F (Z, Y)) ∘ fun t : ℂ => X + id t • δ) t‖ ≤ 1 / 2 := fun t ht =>
      hB _ _ (hline t (le_of_eq (mem_sphere_zero_iff_norm.1 ht))) hY
    have hc := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hR hdc hsph
    rw [(hgd 0 (by simpa using hR.le)).deriv] at hc
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply, one_smul, id,
      zero_smul, add_zero] at hc
    calc _ ≤ 1 / 2 / R := hc
      _ = 16 * ‖δ‖ := by rw [hRdef]; field_simp; ring
  -- the lemma of Schwarz: `‖∂₁F(X, Y) δ‖ ≤ 256‖Y‖‖δ‖` for `‖X‖ ≤ 1/32`, `‖Y‖ < 1/16`
  have hschwarz : ∀ X Y δ : Mat, ‖X‖ ≤ 1 / 32 → ‖Y‖ < 1 / 16 →
      ‖fderiv ℂ F (X, Y) (δ, 0)‖ ≤ 256 * ‖Y‖ * ‖δ‖ := by
    intro X Y δ hX hY
    set h : Mat → Mat := fun Y => fderiv ℂ F (X, Y) (δ, 0) with hh
    have hdiff : DifferentiableOn ℂ h (Metric.ball 0 (1 / 16)) := by
      intro Y' hY'
      have hYU : (X, Y') ∈ U := hU X Y' (by linarith) (le_of_lt (mem_ball_zero_iff.1 hY'))
      have h1 : AnalyticAt ℂ (fderiv ℂ F) (X, Y') := hA.fderiv _ hYU
      have h2 : AnalyticAt ℂ (fun Y'' : Mat => fderiv ℂ F (X, Y'')) Y' :=
        h1.comp (analyticAt_const.prod analyticAt_id)
      have h3 := ((ContinuousLinearMap.apply ℂ Mat ((δ, 0) : Mat × Mat)).analyticAt _).comp h2
      exact h3.differentiableAt.differentiableWithinAt
    have h0' : h 0 = 0 := by
      have hev : (fun Z => F (Z, 0)) =ᶠ[nhds X] fun _ => 0 := by
        filter_upwards [Metric.ball_mem_nhds X (show (0 : ℝ) < 1 / 8 by norm_num)] with Z hZ
        refine h0 Z ?_
        have h1 := mem_ball_iff_norm.1 hZ
        have h2 := norm_sub_norm_le Z X
        linarith
      have hd := (hpart X 0 (hU X 0 (by linarith) (by simp))).fderiv
      have h3 := Filter.EventuallyEq.fderiv_eq (𝕜 := ℂ) hev
      rw [hd, fderiv_const_apply] at h3
      have h4 := congrArg (fun L : Mat →L[ℂ] Mat => L δ) h3
      simpa [hh] using h4
    have hmaps : Set.MapsTo h (Metric.ball 0 (1 / 16)) (Metric.closedBall (h 0) (16 * ‖δ‖)) := by
      intro Y' hY'
      rw [h0', mem_closedBall_zero_iff]
      exact hcauchy X Y' δ hX (le_of_lt (mem_ball_zero_iff.1 hY'))
    have hs := Complex.dist_le_div_mul_dist_of_mapsTo_ball hdiff hmaps (mem_ball_zero_iff.2 hY)
    rw [h0', dist_zero_right, dist_zero_right] at hs
    calc ‖h Y‖ ≤ 16 * ‖δ‖ / (1 / 16) * ‖Y‖ := hs
      _ = 256 * ‖Y‖ * ‖δ‖ := by ring
  -- the mean value inequality along `[X, X']`
  have hmv := (convex_closedBall (0 : Mat) (1 / 32)).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (f := fun Z => F (Z, Y))
    (f' := fun Z => (fderiv ℂ F (Z, Y)).comp (ContinuousLinearMap.inl ℂ Mat Mat))
    (C := 256 * ‖Y‖)
    (fun Z hZ => (hpart Z Y (hU Z Y (by linarith [mem_closedBall_zero_iff.1 hZ])
      (by linarith))).hasFDerivWithinAt)
    (fun Z hZ => ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun δ => by
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply]
      exact hschwarz Z Y δ (mem_closedBall_zero_iff.1 hZ) (by linarith))
    (mem_closedBall_zero_iff.2 hX) (mem_closedBall_zero_iff.2 hX')
  exact hmv

/-- `eq:product-lipschitz` with `C_Ψ = 256`, for all matrices of norm at most `1/32`:
`‖Ψ(X', Y') - Ψ(X, Y) - (X' - X) - (Y' - Y)‖ ≤ 256 (‖Y'‖‖X' - X‖ + ‖X‖‖Y' - Y‖)`. -/
theorem psi_lipschitz {X Y X' Y' : Mat} (hX : ‖X‖ ≤ 1 / 32) (hY : ‖Y‖ ≤ 1 / 32)
    (hX' : ‖X'‖ ≤ 1 / 32) (hY' : ‖Y'‖ ≤ 1 / 32) :
    ‖psi X' Y' - psi X Y - (X' - X) - (Y' - Y)‖ ≤
      256 * (‖Y'‖ * ‖X' - X‖ + ‖X‖ * ‖Y' - Y‖) := by
  set Φ : Mat × Mat → Mat := fun w => psi w.1 w.2 - w.1 - w.2 with hΦ
  have hA : AnalyticOnNhd ℂ Φ {v | ‖v.1‖ + ‖v.2‖ < Real.log 2} := fun w hw =>
    ((analyticOnNhd_psi w hw).sub analyticAt_fst).sub analyticAt_snd
  have hB : ∀ X Y : Mat, ‖X‖ ≤ 1 / 16 → ‖Y‖ ≤ 1 / 16 → ‖Φ (X, Y)‖ ≤ 1 / 2 := fun X Y hX hY => by
    have h := norm_psi_le hX hY
    have h1 := norm_sub_le (psi X Y - X) Y
    have h2 := norm_sub_le (psi X Y) X
    show ‖psi X Y - X - Y‖ ≤ 1 / 2
    linarith
  have h0 : ∀ X : Mat, ‖X‖ < 1 / 4 → Φ (X, 0) = 0 := fun X hX => by
    simp [hΦ, psi_zero_right hX]
  set Φs : Mat × Mat → Mat := fun w => Φ (w.2, w.1) with hΦs
  have hAs : AnalyticOnNhd ℂ Φs {v | ‖v.1‖ + ‖v.2‖ < Real.log 2} := fun w hw =>
    (hA (w.2, w.1) (by simp only [Set.mem_setOf_eq] at hw ⊢; linarith)).comp
      (f := fun v : Mat × Mat => (v.2, v.1)) (analyticAt_snd.prod analyticAt_fst)
  have hBs : ∀ X Y : Mat, ‖X‖ ≤ 1 / 16 → ‖Y‖ ≤ 1 / 16 → ‖Φs (X, Y)‖ ≤ 1 / 2 :=
    fun X Y hX hY => hB Y X hY hX
  have h0s : ∀ Y : Mat, ‖Y‖ < 1 / 4 → Φs (Y, 0) = 0 := fun Y hY => by
    simp [hΦs, hΦ, psi_zero_left hY]
  have e : psi X' Y' - psi X Y - (X' - X) - (Y' - Y) =
      (Φ (X', Y') - Φ (X, Y')) + (Φs (Y', X) - Φs (Y, X)) := by
    simp only [hΦs, hΦ]; abel
  rw [e]
  have h1 := norm_sub_le_of_vanish hA hB h0 hX hX' hY'
  have h2 := norm_sub_le_of_vanish hAs hBs h0s hY hY' hX
  calc _ ≤ ‖Φ (X', Y') - Φ (X, Y')‖ + ‖Φs (Y', X) - Φs (Y, X)‖ := norm_add_le _ _
    _ ≤ 256 * ‖Y'‖ * ‖X' - X‖ + 256 * ‖X‖ * ‖Y' - Y‖ := add_le_add h1 h2
    _ = 256 * (‖Y'‖ * ‖X' - X‖ + ‖X‖ * ‖Y' - Y‖) := by ring

end CoreLean
