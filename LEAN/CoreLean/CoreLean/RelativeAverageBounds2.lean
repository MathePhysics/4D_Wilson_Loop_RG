/-
`prop:relative-average`(vi), the site factors, and (vii) of BALABAN_CORE.tex (`d8bdc4ac1777`), for the configurations
`𝐔_X = e^{iX}` of the polydisc.

* `sExp V B y h`: the exponent `L⁻⁴ Σ_x Log(𝐔_A(y, x)𝐔(y, x)⁻¹)` of the site factor, `v = e^{sExp}` (`eq:site-factor`).
* `restrictF B S`: the form equal to `B` on the positive bonds with both ends in `S` and to `0` elsewhere; its norm is
  the supremum of `B` over these bonds.
* `site_bound_UX`: `‖sExp(𝐔_X, B, y)‖ ≤ C‖B‖_{∞,B(y)}`, the supremum over the bonds with both ends in `B(y)`
  (locality, `siteFactor_local`, and the lemma of Schwarz); so `‖(1/i) Log v_{𝐔_X}(A)(y)‖ ≤ C‖aA‖_{∞,B(y)}` where
  `‖sExp‖ < log 2` (`LogM_exp`).
* `relLog_lip_UX`: `X ↦ (1/i) Log 𝓜_{𝐔_X}(B)(c)` is Lipschitz on the polydisc of radius `r/2` (Cauchy's estimate and
  the mean value inequality); `Qlin_lip_UX`: `‖L(Q(𝐔_{X₁}) - Q(𝐔_{X₂}))B‖ ≤ (4K/r²)‖X₁ - X₂‖‖B‖`, (vii) for `Q`.
-/
import CoreLean.RelativeAverageUniform

open Matrix NormedSpace Filter Topology Metric
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace CoreLean
namespace RelativeAverage

open LatticePaths LatticeKappa RegularAverages BlockPaths AverageHolo MeanTransports AxialReference

variable {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "GLN" => (Matrix (Fin N) (Fin N) ℂ)ˣ

variable {n : ℕ} [NeZero n]

/-! ### (vii) for the linear part -/

/-- `X ↦ (1/i) Log 𝓜_{𝐔_X}(B)(c)` is holomorphic on the ball of radius `r`, for `‖B‖ ≤ r`. -/
lemma relLog_X_differentiableOn {y : Site n} {μ : Fin 4} {h : ℕ} {r : ℝ}
    (hc : ∀ X B : Fin 4 → Site n → Mat, ‖X‖ ≤ r → ‖B‖ ≤ r → Cond (N := N) y μ h (X, B))
    {B : Fin 4 → Site n → Mat} (hB : ‖B‖ ≤ r) :
    DifferentiableOn ℂ (fun X => relLog (UX (N := N) X) B y μ h) (ball 0 r) := fun X hX => by
  rw [mem_ball, dist_zero_right] at hX
  have hd := relLog_pair_differentiableAt (hc X B hX.le hB)
  have hpair : DifferentiableAt ℂ (fun X : Fin 4 → Site n → Mat => ((X, B) : PairSp N n)) X :=
    differentiableAt_id.prodMk (differentiableAt_const B)
  exact (DifferentiableAt.comp (f := fun X : Fin 4 → Site n → Mat => ((X, B) : PairSp N n)) X hd hpair).differentiableWithinAt

/-- `X ↦ (1/i) Log 𝓜_{𝐔_X}(B)(c)` is `2K/r`-Lipschitz on the polydisc of radius `r/2`. -/
theorem relLog_lip_UX {y : Site n} {μ : Fin 4} {h : ℕ} {r K : ℝ} (hr : 0 < r)
    (hc : ∀ X B : Fin 4 → Site n → Mat, ‖X‖ ≤ r → ‖B‖ ≤ r → Cond (N := N) y μ h (X, B))
    (hK : ∀ X B : Fin 4 → Site n → Mat, ‖X‖ ≤ r → ‖B‖ ≤ r → ‖relLog (UX (N := N) X) B y μ h‖ ≤ K)
    {B : Fin 4 → Site n → Mat} (hB : ‖B‖ ≤ r) {X₁ X₂ : Fin 4 → Site n → Mat} (h1 : ‖X₁‖ ≤ r / 2) (h2 : ‖X₂‖ ≤ r / 2) :
    ‖relLog (UX (N := N) X₁) B y μ h - relLog (UX (N := N) X₂) B y μ h‖ ≤ 2 * K / r * ‖X₁ - X₂‖ := by
  have hd := relLog_X_differentiableOn hc hB
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0 B (by simp; exact hr.le) hB)
  have hsub : closedBall (0 : Fin 4 → Site n → Mat) (r / 2) ⊆ ball 0 r := closedBall_subset_ball (by linarith)
  have hder : ∀ X ∈ closedBall (0 : Fin 4 → Site n → Mat) (r / 2),
      ‖fderiv ℂ (fun X => relLog (UX (N := N) X) B y μ h) X‖ ≤ 2 * K / r := fun X hX => by
    have hXb := hsub hX
    rw [mem_closedBall, dist_zero_right] at hX
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
    have := SchwarzCauchy.cauchy_fderiv hd (fun X' hX' => hK X' B
      (by rw [mem_ball, dist_zero_right] at hX'; exact hX'.le) hB) hXb v
    rw [sub_zero] at this
    calc _ ≤ K * ‖v‖ / (r - ‖X‖) := this
      _ ≤ 2 * K / r * ‖v‖ := by
          rw [div_le_iff₀ (by linarith)]
          have e : 2 * K / r * ‖v‖ * (r - ‖X‖) = K * ‖v‖ * (2 * (r - ‖X‖) / r) := by field_simp
          rw [e]
          have : 1 ≤ 2 * (r - ‖X‖) / r := by rw [le_div_iff₀ hr]; linarith
          nlinarith [mul_nonneg hK0 (norm_nonneg v)]
  have := (convex_closedBall (0 : Fin 4 → Site n → Mat) (r / 2)).norm_image_sub_le_of_norm_fderiv_le
    (fun X hX => (hd.differentiableAt (isOpen_ball.mem_nhds (hsub hX)))) hder
    (by rw [mem_closedBall, dist_zero_right]; exact h2) (by rw [mem_closedBall, dist_zero_right]; exact h1)
  exact this

/-- **(vii) for the linear part**: `‖L(Q(𝐔_{X₁}) - Q(𝐔_{X₂}))B‖ ≤ (4K/r²)‖X₁ - X₂‖‖B‖` on the polydisc of radius
`r/2`. -/
theorem Qlin_lip_UX {y : Site n} {μ : Fin 4} {h : ℕ} {r K : ℝ} (hr : 0 < r)
    (hc : ∀ X B : Fin 4 → Site n → Mat, ‖X‖ ≤ r → ‖B‖ ≤ r → Cond (N := N) y μ h (X, B))
    (hK : ∀ X B : Fin 4 → Site n → Mat, ‖X‖ ≤ r → ‖B‖ ≤ r → ‖relLog (UX (N := N) X) B y μ h‖ ≤ K)
    {X₁ X₂ : Fin 4 → Site n → Mat} (h1 : ‖X₁‖ ≤ r / 2) (h2 : ‖X₂‖ ≤ r / 2) (B : Fin 4 → Site n → Mat) :
    ‖((2 * h + 1 : ℕ) : ℂ) • (Qlin (UX (N := N) X₁) y μ h B - Qlin (UX (N := N) X₂) y μ h B)‖ ≤
      4 * K / r ^ 2 * ‖X₁ - X₂‖ * ‖B‖ := by
  have hL : (((2 * h + 1 : ℕ) : ℂ)) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  set F := fun B' => relLog (UX (N := N) X₁) B' y μ h - relLog (UX (N := N) X₂) B' y μ h with hF
  have hX1 : ‖X₁‖ ≤ r := by linarith [norm_nonneg X₁]
  have hX2 : ‖X₂‖ ≤ r := by linarith [norm_nonneg X₂]
  have hd1 := relLog_UX_differentiableOn hc hX1
  have hd2 := relLog_UX_differentiableOn hc hX2
  have hFd : DifferentiableOn ℂ F (ball 0 r) := hd1.sub hd2
  have hFb : ∀ B' ∈ ball (0 : Fin 4 → Site n → Mat) r, ‖F B'‖ ≤ 2 * K / r * ‖X₁ - X₂‖ := fun B' hB' => by
    rw [mem_ball, dist_zero_right] at hB'
    exact relLog_lip_UX hr hc hK hB'.le h1 h2
  have hfd : fderiv ℂ F 0 = fderiv ℂ (fun B' => relLog (UX (N := N) X₁) B' y μ h) 0 -
      fderiv ℂ (fun B' => relLog (UX (N := N) X₂) B' y μ h) 0 :=
    fderiv_sub (hd1.differentiableAt (ball_mem_nhds 0 hr)) (hd2.differentiableAt (ball_mem_nhds 0 hr))
  have e : ((2 * h + 1 : ℕ) : ℂ) • (Qlin (UX (N := N) X₁) y μ h B - Qlin (UX (N := N) X₂) y μ h B) =
      fderiv ℂ F 0 B := by
    rw [hfd]
    simp only [Qlin, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply, smul_sub, smul_smul,
      mul_inv_cancel₀ hL, one_smul]
  rw [e]
  have := SchwarzCauchy.cauchy_fderiv hFd hFb (mem_ball_self hr) B
  rw [sub_zero, norm_zero, sub_zero] at this
  calc _ ≤ 2 * K / r * ‖X₁ - X₂‖ * ‖B‖ / r := this
    _ ≤ 4 * K / r ^ 2 * ‖X₁ - X₂‖ * ‖B‖ := by
        have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0 0 (by simp; exact hr.le) (by simp; exact hr.le))
        rw [div_le_iff₀ hr]
        have : 4 * K / r ^ 2 * ‖X₁ - X₂‖ * ‖B‖ * r = 2 * (2 * K / r * ‖X₁ - X₂‖ * ‖B‖) := by field_simp; ring
        rw [this]
        nlinarith [mul_nonneg (mul_nonneg (div_nonneg (mul_nonneg zero_le_two hK0) hr.le) (norm_nonneg (X₁ - X₂)))
          (norm_nonneg B)]

/-! ### The site factors -/

/-- The exponent of the site factor. -/
def sExp (V : Config N n) (B : Fin 4 → Site n → Mat) (y : Site n) (h : ℕ) : Mat :=
  (((2 * h + 1 : ℕ) : ℂ) ^ 4)⁻¹ • ∑ x : Pts h, LogM ((trans (moveC V B) y h x * (trans V y h x)⁻¹ : GLN) : Mat)

lemma siteFactor_eq_sExp (V : Config N n) (B : Fin 4 → Site n → Mat) (y : Site n) (h : ℕ) :
    siteFactor V B y h = expU (sExp V B y h) := rfl

/-- The form equal to `B` on the positive bonds with both ends in `S` and to `0` elsewhere. -/
def restrictF (B : Fin 4 → Site n → Mat) (S : Site n → Prop) [DecidablePred S] : Fin 4 → Site n → Mat :=
  fun ν z => if S z ∧ S (z + unit n ν) then B ν z else 0

lemma sExp_local {h : ℕ} (hn : 4 * h + 2 ≤ n) {y : Site n} (V : Config N n) (B : Fin 4 → Site n → Mat)
    [DecidablePred (Bm y h)] : sExp V B y h = sExp V (restrictF B (Bm y h)) y h := by
  have h2 : ∀ x, trans (moveC V B) y h x = trans (moveC V (restrictF B (Bm y h))) y h x :=
    trans_local hn fun μ z hz hz' => by simp [moveC, restrictF, hz, hz']
  simp only [sExp, h2]

/-- `B ↦ sExp(𝐔_X, B, y')` is holomorphic on the ball of radius `r` where the conditions hold. -/
lemma sExp_UX_differentiableOn {y : Site n} {μ : Fin 4} {h : ℕ} {r : ℝ}
    (hc : ∀ X B : Fin 4 → Site n → Mat, ‖X‖ ≤ r → ‖B‖ ≤ r → Cond (N := N) y μ h (X, B))
    {X : Fin 4 → Site n → Mat} (hX : ‖X‖ ≤ r) :
    DifferentiableOn ℂ (fun B => sExp (UX (N := N) X) B y h) (ball 0 r) := fun B hB => by
  rw [mem_ball, dist_zero_right] at hB
  have hcB := hc X B hX hB.le
  have htA : ∀ x : Pts h, DifferentiableAt ℂ (fun B' : Fin 4 → Site n → Mat =>
      ((trans (moveC (UX (N := N) X) B') y h x : GLN) : Mat)) B := fun x =>
    trans_differentiableAt (fun B' => moveC (UX (N := N) X) B') (moveC_hV _ B) y h x (hcB.gA0.1 x)
      ((hcB.gA0.2 x).trans (by norm_num))
  refine (DifferentiableAt.fun_const_smul ?_ _).differentiableWithinAt
  refine DifferentiableAt.fun_sum fun x _ => ?_
  have hL := (analyticOnNhd_LogM (N := N) _ (hcB.q0 x)).differentiableAt
  have hm : DifferentiableAt ℂ (fun B' : Fin 4 → Site n → Mat =>
      ((trans (moveC (UX (N := N) X) B') y h x * (trans (UX (N := N) X) y h x)⁻¹ : GLN) : Mat)) B := by
    simp only [Units.val_mul]
    exact (htA x).mul (differentiableAt_const _)
  exact DifferentiableAt.comp (g := LogM (N := N)) B hL hm

lemma sExp_zero (V : Config N n) (y : Site n) (h : ℕ) : sExp V 0 y h = 0 := by
  simp [sExp, moveC_zero, LogM_one]

/-- **The site factors, (vi)**: `‖sExp(𝐔_X, B, y)‖ ≤ (K'/r)‖B‖_{∞,B(y)}` on the polydisc, for a bound `K'` of `sExp`
on it. -/
theorem site_bound_UX {h : ℕ} (hn : 4 * h + 2 ≤ n) {y : Site n} {μ : Fin 4} {r K' : ℝ} (hr : 0 < r)
    (hc : ∀ X B : Fin 4 → Site n → Mat, ‖X‖ ≤ r → ‖B‖ ≤ r → Cond (N := N) y μ h (X, B))
    (hK' : ∀ X B : Fin 4 → Site n → Mat, ‖X‖ ≤ r → ‖B‖ ≤ r → ‖sExp (UX (N := N) X) B y h‖ ≤ K')
    [DecidablePred (Bm y h)] {X B : Fin 4 → Site n → Mat} (hX : ‖X‖ ≤ r) (hB : ‖restrictF B (Bm y h)‖ < r) :
    ‖sExp (UX (N := N) X) B y h‖ ≤ K' / r * ‖restrictF B (Bm y h)‖ := by
  rw [sExp_local hn]
  have := SchwarzCauchy.schwarz_one (sExp_UX_differentiableOn hc hX)
    (fun B' hB' => by
      rw [sExp_zero, sub_zero]
      rw [mem_ball, dist_zero_right] at hB'
      exact hK' X B' hX hB'.le)
    (by rw [mem_ball, dist_zero_right]; exact hB)
  rwa [sExp_zero, sub_zero, sub_zero] at this

/-- `sExp(𝐔_X, B, y)` is holomorphic in the pair where the conditions hold. -/
lemma sExp_pair_differentiableAt {y : Site n} {μ : Fin 4} {h : ℕ} {p₀ : PairSp N n}
    (hcp : Cond (N := N) y μ h p₀) :
    DifferentiableAt ℂ (fun p : PairSp N n => sExp (UX (N := N) p.1) p.2 y h) p₀ := by
  have htA : ∀ x : Pts h, DifferentiableAt ℂ (fun p : PairSp N n =>
      ((trans (moveC (UX (N := N) p.1) p.2) y h x : GLN) : Mat)) p₀ := fun x =>
    trans_differentiableAt (fun p : PairSp N n => moveC (UX (N := N) p.1) p.2)
      (UXB_hV p₀) y h x (hcp.gA0.1 x) ((hcp.gA0.2 x).trans (by norm_num))
  have ht : ∀ x : Pts h, DifferentiableAt ℂ (fun p : PairSp N n =>
      ((trans (UX (N := N) p.1) y h x : GLN) : Mat)) p₀ := fun x =>
    trans_differentiableAt (fun p : PairSp N n => UX (N := N) p.1)
      (UX_hV p₀) y h x (hcp.g0.1 x) ((hcp.g0.2 x).trans (by norm_num))
  unfold sExp
  have hs : DifferentiableAt ℂ (fun p : PairSp N n => ∑ x : Pts h,
      LogM ((trans (moveC (UX (N := N) p.1) p.2) y h x * (trans (UX (N := N) p.1) y h x)⁻¹ : GLN) : Mat)) p₀ := by
    refine DifferentiableAt.fun_sum fun x _ => ?_
    have hL := (analyticOnNhd_LogM (N := N) _ (hcp.q0 x)).differentiableAt
    have hm : DifferentiableAt ℂ (fun p : PairSp N n =>
        ((trans (moveC (UX (N := N) p.1) p.2) y h x * (trans (UX (N := N) p.1) y h x)⁻¹ : GLN) : Mat)) p₀ := by
      simp only [Units.val_mul]
      exact (htA x).mul (inv_differentiableAt (ht x))
    exact DifferentiableAt.comp (g := LogM (N := N)) p₀ hL hm
  exact hs.fun_const_smul _

/-- The bound `K'` of the exponents of the site factors on the polydisc exists (compactness). -/
theorem exists_site_bound {y : Site n} {μ : Fin 4} {h : ℕ} {r : ℝ}
    (hc : ∀ X B : Fin 4 → Site n → Mat, ‖X‖ ≤ r → ‖B‖ ≤ r → Cond (N := N) y μ h (X, B)) :
    ∃ K' : ℝ, ∀ X B : Fin 4 → Site n → Mat, ‖X‖ ≤ r → ‖B‖ ≤ r → ‖sExp (UX (N := N) X) B y h‖ ≤ K' := by
  have hcont : ContinuousOn (fun p : PairSp N n => sExp (UX (N := N) p.1) p.2 y h) (closedBall 0 r) := by
    intro p hp
    rw [mem_closedBall, dist_zero_right, Prod.norm_def] at hp
    exact (sExp_pair_differentiableAt (hc p.1 p.2 (le_of_max_le_left hp)
      (le_of_max_le_right hp))).continuousAt.continuousWithinAt
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : PairSp N n) r).exists_bound_of_continuousOn hcont
  refine ⟨C, fun X B hX hB => ?_⟩
  have hmem : ((X, B) : PairSp N n) ∈ closedBall 0 r := by
    rw [mem_closedBall, dist_zero_right, Prod.norm_def]; exact max_le hX hB
  exact hC ((X, B) : PairSp N n) hmem

end RelativeAverage
end CoreLean

end
