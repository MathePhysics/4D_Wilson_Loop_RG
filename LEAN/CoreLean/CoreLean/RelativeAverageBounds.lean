/-
`prop:relative-average`(vi) of BALABAN_CORE.tex (`d8bdc4ac1777`) for the configurations `𝐔_X = e^{iX}` of the
polydisc: the bounds of the linear part and of the remainder.

On a torus, for the bond `(y, y + Le_μ)`:
* `bounds_UX`: there are `r > 0` and `K` such that the conditions of holomorphy hold for `‖X‖ ≤ r`, `‖B‖ < r`, and
  `‖(1/i) Log 𝓜_{𝐔_X}(B)(c)‖ ≤ K` for `‖X‖, ‖B‖ ≤ r` (compactness of the closed polydisc, as in the core);
* `linear_bound_UX`: `‖L·Q(𝐔_X)B‖ ≤ (K/r)‖B‖` (Cauchy's estimate);
* `remainder_bound_UX`: `‖C(𝐔_X; B)‖ ≤ (2K/r²)‖B‖²` for `‖B‖ < r` (the lemma of Schwarz applied twice);
* `remainder_deriv_bound_UX`: `‖DC(𝐔_X; B)δ‖ ≤ (8K/r²)‖B‖‖δ‖` for `‖B‖ < r/2` (Cauchy's estimate on the ball of
  radius `‖B‖` about `B`).
On the reference torus of (viii) the numbers depend on `L` and `N` only.
-/
import CoreLean.RelativeAverageRef
import CoreLean.SchwarzCauchy
import Mathlib.Analysis.Complex.CauchyIntegral

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

lemma norm_pair_lt {X B : Fin 4 → Site n → Mat} {c : ℝ} (hX : ‖X‖ < c) (hB : ‖B‖ < c) : ‖((X, B) : PairSp N n)‖ < c :=
  by rw [Prod.norm_def]; exact max_lt hX hB

/-- **The constant of compactness**: the conditions hold on the polydisc of radius `r` and `(1/i) Log 𝓜` is bounded
there. -/
theorem bounds_UX (y : Site n) (μ : Fin 4) (h : ℕ) :
    ∃ r K : ℝ, 0 < r ∧ 0 ≤ K ∧ (∀ X B : Fin 4 → Site n → Mat, ‖X‖ ≤ r → ‖B‖ ≤ r → Cond (N := N) y μ h (X, B)) ∧
      ∀ X B : Fin 4 → Site n → Mat, ‖X‖ ≤ r → ‖B‖ ≤ r → ‖relLog (UX (N := N) X) B y μ h‖ ≤ K := by
  obtain ⟨ci, hci, hcond⟩ := exists_polydisc (N := N) y μ h
  set r := ci / 2 with hr
  have hr0 : 0 < r := by positivity
  have hc : ∀ X B : Fin 4 → Site n → Mat, ‖X‖ ≤ r → ‖B‖ ≤ r → Cond (N := N) y μ h (X, B) := fun X B hX hB =>
    hcond _ (norm_pair_lt (by linarith) (by linarith))
  have hcont : ContinuousOn (fun p : PairSp N n => relLog (UX (N := N) p.1) p.2 y μ h) (closedBall 0 r) := by
    intro p hp
    rw [mem_closedBall, dist_zero_right, Prod.norm_def] at hp
    have hcp : Cond (N := N) y μ h p := hc p.1 p.2 (le_of_max_le_left hp) (le_of_max_le_right hp)
    exact (relLog_pair_differentiableAt hcp).continuousAt.continuousWithinAt
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : PairSp N n) r).exists_bound_of_continuousOn hcont
  refine ⟨r, max C 0, hr0, le_max_right _ _, hc, fun X B hX hB => ?_⟩
  have hmem : ((X, B) : PairSp N n) ∈ closedBall 0 r := by
    rw [mem_closedBall, dist_zero_right, Prod.norm_def]; exact max_le hX hB
  exact (hC _ hmem).trans (le_max_left _ _)

/-- `B ↦ (1/i) Log 𝓜_{𝐔_X}(B)(c)` is holomorphic on the ball of radius `r`. -/
lemma relLog_UX_differentiableOn {y : Site n} {μ : Fin 4} {h : ℕ} {r : ℝ}
    (hc : ∀ X B : Fin 4 → Site n → Mat, ‖X‖ ≤ r → ‖B‖ ≤ r → Cond (N := N) y μ h (X, B))
    {X : Fin 4 → Site n → Mat} (hX : ‖X‖ ≤ r) :
    DifferentiableOn ℂ (fun B => relLog (UX (N := N) X) B y μ h) (ball 0 r) := fun B hB => by
  rw [mem_ball, dist_zero_right] at hB
  have hd := relLog_pair_differentiableAt (hc X B hX hB.le)
  have hpair : DifferentiableAt ℂ (fun B : Fin 4 → Site n → Mat => ((X, B) : PairSp N n)) B :=
    (differentiableAt_const X).prodMk differentiableAt_id
  exact (DifferentiableAt.comp (f := fun B : Fin 4 → Site n → Mat => ((X, B) : PairSp N n)) B hd hpair).differentiableWithinAt

/-- **The linear part**: `‖L·Q(𝐔_X)B‖ ≤ (K/r)‖B‖`. -/
theorem linear_bound_UX {y : Site n} {μ : Fin 4} {h : ℕ} {r K : ℝ} (hr : 0 < r)
    (hc : ∀ X B : Fin 4 → Site n → Mat, ‖X‖ ≤ r → ‖B‖ ≤ r → Cond (N := N) y μ h (X, B))
    (hK : ∀ X B : Fin 4 → Site n → Mat, ‖X‖ ≤ r → ‖B‖ ≤ r → ‖relLog (UX (N := N) X) B y μ h‖ ≤ K)
    {X : Fin 4 → Site n → Mat} (hX : ‖X‖ ≤ r) (B : Fin 4 → Site n → Mat) :
    ‖((2 * h + 1 : ℕ) : ℂ) • Qlin (UX (N := N) X) y μ h B‖ ≤ K / r * ‖B‖ := by
  have hL : (((2 * h + 1 : ℕ) : ℂ)) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have e : ((2 * h + 1 : ℕ) : ℂ) • Qlin (UX (N := N) X) y μ h B =
      fderiv ℂ (fun B => relLog (UX (N := N) X) B y μ h) 0 B := by
    simp only [Qlin, ContinuousLinearMap.smul_apply, smul_smul, mul_inv_cancel₀ hL, one_smul]
  rw [e]
  have := SchwarzCauchy.cauchy_fderiv (relLog_UX_differentiableOn hc hX)
    (fun B' hB' => hK X B' hX (by rw [mem_ball, dist_zero_right] at hB'; exact hB'.le))
    (mem_ball_self hr) B
  rw [sub_zero, norm_zero, sub_zero] at this
  calc _ ≤ K * ‖B‖ / r := this
    _ = K / r * ‖B‖ := by ring

/-- The remainder is holomorphic on the ball of radius `r`. -/
lemma Crem_UX_differentiableOn {y : Site n} {μ : Fin 4} {h : ℕ} {r : ℝ}
    (hc : ∀ X B : Fin 4 → Site n → Mat, ‖X‖ ≤ r → ‖B‖ ≤ r → Cond (N := N) y μ h (X, B))
    {X : Fin 4 → Site n → Mat} (hX : ‖X‖ ≤ r) :
    DifferentiableOn ℂ (fun B => Crem (UX (N := N) X) B y μ h) (ball 0 r) := by
  unfold Crem
  exact (relLog_UX_differentiableOn hc hX).sub
    ((((2 * h + 1 : ℕ) : ℂ) • Qlin (UX (N := N) X) y μ h).differentiable.differentiableOn)

/-- **The remainder**: `‖C(𝐔_X; B)‖ ≤ (2K/r²)‖B‖²` for `‖B‖ < r`. -/
theorem remainder_bound_UX {y : Site n} {μ : Fin 4} {h : ℕ} {r K : ℝ} (hr : 0 < r)
    (hc : ∀ X B : Fin 4 → Site n → Mat, ‖X‖ ≤ r → ‖B‖ ≤ r → Cond (N := N) y μ h (X, B))
    (hK : ∀ X B : Fin 4 → Site n → Mat, ‖X‖ ≤ r → ‖B‖ ≤ r → ‖relLog (UX (N := N) X) B y μ h‖ ≤ K)
    {X : Fin 4 → Site n → Mat} (hX : ‖X‖ ≤ r) {B : Fin 4 → Site n → Mat} (hB : ‖B‖ < r) :
    ‖Crem (UX (N := N) X) B y μ h‖ ≤ 2 * K / r ^ 2 * ‖B‖ ^ 2 := by
  have hbd : ∀ B' ∈ ball (0 : Fin 4 → Site n → Mat) r,
      ‖Crem (UX (N := N) X) B' y μ h - Crem (UX (N := N) X) 0 y μ h‖ ≤ 2 * K := fun B' hB' => by
    rw [Crem_zero, sub_zero]
    rw [mem_ball, dist_zero_right] at hB'
    have h1 := hK X B' hX hB'.le
    have h2 := linear_bound_UX hr hc hK hX B'
    have h3 : K / r * ‖B'‖ ≤ K := by
      have hK0 : 0 ≤ K := (norm_nonneg _).trans h1
      rw [div_mul_eq_mul_div, div_le_iff₀ hr]; nlinarith [norm_nonneg B']
    unfold Crem
    calc _ ≤ ‖relLog (UX (N := N) X) B' y μ h‖ + ‖((2 * h + 1 : ℕ) : ℂ) • Qlin (UX (N := N) X) y μ h B'‖ :=
          norm_sub_le _ _
      _ ≤ 2 * K := by linarith
  have hd0 : HasFDerivAt (fun B => Crem (UX (N := N) X) B y μ h) (0 : (Fin 4 → Site n → Mat) →L[ℂ] Mat) 0 :=
    Crem_hasFDerivAt _ y μ h ((relLog_UX_differentiableOn hc hX).differentiableAt (ball_mem_nhds 0 hr))
  have := SchwarzCauchy.schwarz_two (Crem_UX_differentiableOn hc hX) hbd hd0
    (by rw [mem_ball, dist_zero_right]; exact hB)
  rw [Crem_zero, sub_zero, sub_zero] at this
  calc _ ≤ 2 * K * (‖B‖ / r) ^ 2 := this
    _ = 2 * K / r ^ 2 * ‖B‖ ^ 2 := by field_simp

/-- **The derivative of the remainder**: `‖DC(𝐔_X; B)δ‖ ≤ (8K/r²)‖B‖‖δ‖` for `‖B‖ < r/2`: Cauchy's estimate on the
ball of radius `‖B‖` about `B`, with the bound of the remainder on it. -/
theorem remainder_deriv_bound_UX {y : Site n} {μ : Fin 4} {h : ℕ} {r K : ℝ} (hr : 0 < r)
    (hc : ∀ X B : Fin 4 → Site n → Mat, ‖X‖ ≤ r → ‖B‖ ≤ r → Cond (N := N) y μ h (X, B))
    (hK : ∀ X B : Fin 4 → Site n → Mat, ‖X‖ ≤ r → ‖B‖ ≤ r → ‖relLog (UX (N := N) X) B y μ h‖ ≤ K)
    {X : Fin 4 → Site n → Mat} (hX : ‖X‖ ≤ r) {B : Fin 4 → Site n → Mat} (hB : ‖B‖ < r / 2)
    (δ : Fin 4 → Site n → Mat) :
    ‖fderiv ℂ (fun B => Crem (UX (N := N) X) B y μ h) B δ‖ ≤ 8 * K / r ^ 2 * ‖B‖ * ‖δ‖ := by
  have hgd := Crem_UX_differentiableOn hc hX
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK X 0 hX (by simp; exact hr.le))
  rcases eq_or_ne B 0 with rfl | hB0
  · have hd0 : fderiv ℂ (fun B => Crem (UX (N := N) X) B y μ h) 0 = 0 :=
      (Crem_hasFDerivAt _ y μ h ((relLog_UX_differentiableOn hc hX).differentiableAt (ball_mem_nhds 0 hr))).fderiv
    rw [hd0]; simp
  have hBp : 0 < ‖B‖ := norm_pos_iff.2 hB0
  have hsub : ball B ‖B‖ ⊆ ball (0 : Fin 4 → Site n → Mat) r := fun y' hy' => by
    rw [mem_ball] at hy' ⊢
    rw [dist_zero_right]
    have := norm_le_norm_add_norm_sub' y' B
    rw [dist_eq_norm] at hy'
    linarith [norm_sub_rev y' B]
  have hbd : ∀ y' ∈ ball B ‖B‖, ‖Crem (UX (N := N) X) y' y μ h‖ ≤ 2 * K / r ^ 2 * (2 * ‖B‖) ^ 2 := fun y' hy' => by
    have hy'r := hsub hy'
    rw [mem_ball, dist_zero_right] at hy'r
    rw [mem_ball, dist_eq_norm] at hy'
    have h1 := remainder_bound_UX hr hc hK hX hy'r
    have h2 : ‖y'‖ ≤ 2 * ‖B‖ := by linarith [norm_le_norm_add_norm_sub' y' B, norm_sub_rev y' B]
    calc _ ≤ 2 * K / r ^ 2 * ‖y'‖ ^ 2 := h1
      _ ≤ 2 * K / r ^ 2 * (2 * ‖B‖) ^ 2 := by gcongr
  have := SchwarzCauchy.cauchy_fderiv (hgd.mono hsub) hbd (mem_ball_self hBp) δ
  rw [sub_self, norm_zero, sub_zero] at this
  calc _ ≤ 2 * K / r ^ 2 * (2 * ‖B‖) ^ 2 * ‖δ‖ / ‖B‖ := this
    _ = 8 * K / r ^ 2 * ‖B‖ * ‖δ‖ := by field_simp; ring

end RelativeAverage
end CoreLean

end
