/-
`prop:relative-average`(v) of BALABAN_CORE.tex (`d8bdc4ac1777`) for the configurations `𝐔_X = e^{iX}`.

* `Q0L V y μ h`: `L` times the straight average `Q₀(𝐔)` of `eq:straight-average`,
  `L·(Q₀(𝐔)A)(c) = L⁻⁴ Σ_{x ∈ B(c₋)} |𝐆(c₋, x)|⁻¹ Σ_Γ Σ_{b ∈ [x, x']} Ad_{𝐔(Γ_b)}A(b)`, `Γ_b` the path `Γ` followed by
  the part of the line `[x, x']` from `x` to `b₋`.
* `Q0L_oneC`: `Q₀(id) = Q(id)` (`Qlin_oneC`).
* `Q_sub_Q0_UX`: `‖L(Q(𝐔_X) - Q₀(𝐔_X))B‖ ≤ ((4K/r²) + K₀/r)‖X‖‖B‖` on the polydisc of radius `r/2`, from (vii)
  (`Qlin_lip_UX`) and the lemma of Schwarz for `X ↦ Q₀(𝐔_X)` (`exists_Q0_bound`, compactness).
-/
import CoreLean.RelativeAverageTrivial

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

/-- The path `Γ_b`: `Γ ∈ 𝐆(c₋, x)` followed by `j` steps of the line `[x, x']`. -/
def pathGb (y : Site n) (μ : Fin 4) (h : ℕ) (x : Pts h) (Γ : Ords (offP h x)) (j : ℕ) : List (Bond n) :=
  stair y (offP h x) (ordG h x Γ) 0 ++ seg μ true (ofs y (offP h x)) j

/-- `L·Q₀(𝐔)`, the straight average of `eq:straight-average` times `L`. -/
def Q0L (V : Config N n) (y : Site n) (μ : Fin 4) (h : ℕ) : (Fin 4 → Site n → Mat) →L[ℂ] Mat :=
  (((2 * h + 1 : ℕ) : ℂ) ^ 4)⁻¹ • ∑ x : Pts h, ((((nG h x : ℕ) : ℂ))⁻¹ • ∑ Γ : Ords (offP h x),
    ∑ j ∈ Finset.range (2 * h + 1), (AdL (V.hol (pathGb y μ h x Γ j))).comp
      (evalL μ (ofs y (offP h x) + j • unit n μ)))

lemma BsumL_seg_true (μ : Fin 4) : ∀ (k : ℕ) (z : Site n),
    BsumL (N := N) (seg μ true z k) = ∑ j ∈ Finset.range k, evalL μ (z + j • unit n μ)
  | 0, _ => by simp [seg, BsumL]
  | k + 1, z => by
    rw [seg, BsumL_cons, BsumL_seg_true μ k, Finset.sum_range_succ']
    simp only [bondL, ↓reduceIte, dvec, zero_smul, add_zero]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [succ_nsmul', add_assoc]

/-- **`Q₀(id) = Q(id)`**. -/
theorem Q0L_oneC (y : Site n) (μ : Fin 4) (h : ℕ) : Q0L (oneC (N := N)) y μ h = TsumL y μ h := by
  have hx : ∀ x : Pts h, (((nG h x : ℕ) : ℂ))⁻¹ • ∑ Γ : Ords (offP h x), ∑ j ∈ Finset.range (2 * h + 1),
      (AdL ((oneC (N := N)).hol (pathGb y μ h x Γ j))).comp (evalL μ (ofs y (offP h x) + j • unit n μ)) =
      BsumL (N := N) (segZ μ (ofs y (offP h x)) ((2 * h + 1 : ℕ) : ℤ)) := fun x => by
    have hk : (((nG h x : ℕ) : ℂ)) ≠ 0 := by exact_mod_cast (card_ords_pos (offP h x)).ne'
    have e1 : ∀ (Γ : Ords (offP h x)) j, (AdL ((oneC (N := N)).hol (pathGb y μ h x Γ j))).comp
        (evalL μ (ofs y (offP h x) + j • unit n μ)) = evalL μ (ofs y (offP h x) + j • unit n μ) := fun Γ j => by
      ext1 v; simp [hol_oneC]
    simp only [e1, Finset.sum_const, Finset.card_univ]
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hk, one_smul]
    rw [segZ, if_pos (by positivity), Int.toNat_natCast, BsumL_seg_true]
  simp only [Q0L, TsumL, hx]

/-- `X ↦ Q₀(𝐔_X)B` is holomorphic. -/
lemma Q0L_UX_differentiable (y : Site n) (μ : Fin 4) (h : ℕ) (B : Fin 4 → Site n → Mat) :
    Differentiable ℂ (fun X : Fin 4 → Site n → Mat => Q0L (UX (N := N) X) y μ h B) := fun X₀ => by
  have hterm : ∀ (x : Pts h) (Γ : Ords (offP h x)) (j : ℕ), DifferentiableAt ℂ (fun X : Fin 4 → Site n → Mat =>
      Ad ((UX (N := N) X).hol (pathGb y μ h x Γ j)) (B μ (ofs y (offP h x) + j • unit n μ))) X₀ := fun x Γ j => by
    have hW := hol_differentiableAt (fun X : Fin 4 → Site n → Mat => UX (N := N) X) (moveC_hV oneC X₀)
      (pathGb y μ h x Γ j)
    simp only [Ad]
    exact (hW.mul (differentiableAt_const _)).mul (inv_differentiableAt hW)
  simp only [Q0L, ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_sum', Finset.sum_apply,
    ContinuousLinearMap.comp_apply, AdL_apply, evalL_apply]
  refine DifferentiableAt.fun_const_smul (DifferentiableAt.fun_sum fun x _ => ?_) _
  refine DifferentiableAt.fun_const_smul (DifferentiableAt.fun_sum fun Γ _ => ?_) _
  exact DifferentiableAt.fun_sum fun j _ => hterm x Γ j

/-- The bound `K₀` of `Q₀(𝐔_X) - Q₀(id)` on the polydisc and the unit ball (compactness). -/
theorem exists_Q0_bound (y : Site n) (μ : Fin 4) (h : ℕ) (r : ℝ) :
    ∃ K₀ : ℝ, ∀ X B : Fin 4 → Site n → Mat, ‖X‖ ≤ r → ‖B‖ ≤ 1 →
      ‖Q0L (UX (N := N) X) y μ h B - Q0L (oneC (N := N)) y μ h B‖ ≤ K₀ := by
  set S : Set (PairSp N n) := closedBall (0 : Fin 4 → Site n → Mat) r ×ˢ closedBall 0 1
  have hS : IsCompact S := (isCompact_closedBall _ _).prod (isCompact_closedBall _ _)
  have hcont : ContinuousOn (fun p : PairSp N n => Q0L (UX (N := N) p.1) y μ h p.2 - Q0L (oneC (N := N)) y μ h p.2)
      S := by
    refine Continuous.continuousOn ?_
    have h1 : Continuous fun p : PairSp N n => Q0L (UX (N := N) p.1) y μ h p.2 := by
      simp only [Q0L, ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_sum', Finset.sum_apply,
        ContinuousLinearMap.comp_apply, AdL_apply, evalL_apply]
      refine Continuous.const_smul (continuous_finsetSum (M := Mat) (X := PairSp N n) _ fun x _ => ?_)
        ((((2 * h + 1 : ℕ) : ℂ) ^ 4)⁻¹)
      refine Continuous.const_smul (continuous_finsetSum (M := Mat) (X := PairSp N n) _ fun Γ _ => ?_)
        ((((nG h x : ℕ) : ℂ))⁻¹)
      refine continuous_finsetSum (M := Mat) (X := PairSp N n) _ fun j _ => ?_
      have hW : Continuous fun p : PairSp N n => (((UX (N := N) p.1).hol (pathGb y μ h x Γ j) : GLN) : Mat) :=
        continuous_iff_continuousAt.2 fun p => (hol_differentiableAt (fun p : PairSp N n => UX (N := N) p.1)
          (UX_hV p) (pathGb y μ h x Γ j)).continuousAt
      have hWi : Continuous fun p : PairSp N n => ((((UX (N := N) p.1).hol (pathGb y μ h x Γ j))⁻¹ : GLN) : Mat) :=
        continuous_iff_continuousAt.2 fun p => (inv_differentiableAt (hol_differentiableAt
          (fun p : PairSp N n => UX (N := N) p.1) (UX_hV p) (pathGb y μ h x Γ j))).continuousAt
      have hB : Continuous fun p : PairSp N n => p.2 μ (ofs y (offP h x) + j • unit n μ) :=
        (evalL (N := N) μ (ofs y (offP h x) + j • unit n μ)).continuous.comp continuous_snd
      simp only [Ad]
      exact (hW.mul hB).mul hWi
    exact h1.sub ((Q0L (oneC (N := N)) y μ h).continuous.comp continuous_snd)
  obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn hcont
  refine ⟨C, fun X B hX hB => ?_⟩
  have hmem : ((X, B) : PairSp N n) ∈ S :=
    ⟨by rw [mem_closedBall, dist_zero_right]; exact hX, by rw [mem_closedBall, dist_zero_right]; exact hB⟩
  exact hC ((X, B) : PairSp N n) hmem

/-- `‖Q₀(𝐔_X)B - Q₀(id)B‖ ≤ (K₀/r)‖X‖‖B‖` on the polydisc (the lemma of Schwarz). -/
theorem Q0_lip_UX {y : Site n} {μ : Fin 4} {h : ℕ} {r K₀ : ℝ} (hr : 0 < r)
    (hK₀ : ∀ X B : Fin 4 → Site n → Mat, ‖X‖ ≤ r → ‖B‖ ≤ 1 →
      ‖Q0L (UX (N := N) X) y μ h B - Q0L (oneC (N := N)) y μ h B‖ ≤ K₀)
    {X : Fin 4 → Site n → Mat} (hX : ‖X‖ < r) (B : Fin 4 → Site n → Mat) :
    ‖Q0L (UX (N := N) X) y μ h B - Q0L (oneC (N := N)) y μ h B‖ ≤ K₀ / r * ‖X‖ * ‖B‖ := by
  rcases eq_or_ne B 0 with rfl | hB
  · simp
  have hBp : 0 < ‖B‖ := norm_pos_iff.2 hB
  set B' := (‖B‖⁻¹ : ℂ) • B with hB'
  have hB'n : ‖B'‖ = 1 := by
    rw [hB', norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hBp.le, inv_mul_cancel₀ hBp.ne']
  have hBB : B = (‖B‖ : ℂ) • B' := by
    rw [hB', smul_smul, mul_inv_cancel₀ (by exact_mod_cast hBp.ne'), one_smul]
  have hS := SchwarzCauchy.schwarz_one (f := fun X : Fin 4 → Site n → Mat => Q0L (UX (N := N) X) y μ h B')
    ((Q0L_UX_differentiable y μ h B').differentiableOn) (c := 0) (R := r) (K := K₀)
    (fun X' hX' => by
      rw [mem_ball, dist_zero_right] at hX'
      rw [UX_zero]
      exact hK₀ X' B' hX'.le hB'n.le)
    (by rw [mem_ball, dist_zero_right]; exact hX)
  rw [UX_zero, sub_zero] at hS
  have hlin : ∀ F : (Fin 4 → Site n → Mat) →L[ℂ] Mat, F B = (‖B‖ : ℂ) • F B' := fun F => by
    conv_lhs => rw [hBB]
    exact map_smul F _ _
  rw [hlin (Q0L (UX (N := N) X) y μ h), hlin (Q0L (oneC (N := N)) y μ h), ← smul_sub, norm_smul,
    Complex.norm_real, Real.norm_of_nonneg hBp.le]
  calc ‖B‖ * ‖Q0L (UX (N := N) X) y μ h B' - Q0L (oneC (N := N)) y μ h B'‖ ≤ ‖B‖ * (K₀ / r * ‖X‖) :=
        mul_le_mul_of_nonneg_left hS hBp.le
    _ = K₀ / r * ‖X‖ * ‖B‖ := by ring

/-- **`prop:relative-average`(v) for `𝐔_X`**: `‖L(Q(𝐔_X) - Q₀(𝐔_X))B‖ ≤ ((4K/r²) + K₀/r)‖X‖‖B‖`. -/
theorem Q_sub_Q0_UX {y : Site n} {μ : Fin 4} {h : ℕ} {r K K₀ : ℝ} (hr : 0 < r)
    (hc : ∀ X B : Fin 4 → Site n → Mat, ‖X‖ ≤ r → ‖B‖ ≤ r → Cond (N := N) y μ h (X, B))
    (hK : ∀ X B : Fin 4 → Site n → Mat, ‖X‖ ≤ r → ‖B‖ ≤ r → ‖relLog (UX (N := N) X) B y μ h‖ ≤ K)
    (hK₀ : ∀ X B : Fin 4 → Site n → Mat, ‖X‖ ≤ r → ‖B‖ ≤ 1 →
      ‖Q0L (UX (N := N) X) y μ h B - Q0L (oneC (N := N)) y μ h B‖ ≤ K₀)
    {X : Fin 4 → Site n → Mat} (hX : ‖X‖ ≤ r / 2) (B : Fin 4 → Site n → Mat) :
    ‖((2 * h + 1 : ℕ) : ℂ) • Qlin (UX (N := N) X) y μ h B - Q0L (UX (N := N) X) y μ h B‖ ≤
      (4 * K / r ^ 2 + K₀ / r) * ‖X‖ * ‖B‖ := by
  have h0 : ‖(0 : Fin 4 → Site n → Mat)‖ ≤ r / 2 := by simp; linarith
  have h1 := Qlin_lip_UX hr hc hK hX h0 B
  rw [sub_zero, UX_zero] at h1
  have hQ0 : ((2 * h + 1 : ℕ) : ℂ) • Qlin (oneC (N := N)) y μ h B = Q0L (oneC (N := N)) y μ h B := by
    rw [← ContinuousLinearMap.smul_apply, Qlin_oneC, Q0L_oneC]
  have h2 := Q0_lip_UX hr hK₀ (X := X) (by linarith [norm_nonneg X]) B
  have e : ((2 * h + 1 : ℕ) : ℂ) • Qlin (UX (N := N) X) y μ h B - Q0L (UX (N := N) X) y μ h B =
      ((2 * h + 1 : ℕ) : ℂ) • (Qlin (UX (N := N) X) y μ h B - Qlin (oneC (N := N)) y μ h B) -
        (Q0L (UX (N := N) X) y μ h B - Q0L (oneC (N := N)) y μ h B) := by
    rw [smul_sub, hQ0]; abel
  rw [e]
  calc _ ≤ ‖((2 * h + 1 : ℕ) : ℂ) • (Qlin (UX (N := N) X) y μ h B - Qlin (oneC (N := N)) y μ h B)‖ +
        ‖Q0L (UX (N := N) X) y μ h B - Q0L (oneC (N := N)) y μ h B‖ := norm_sub_le _ _
    _ ≤ 4 * K / r ^ 2 * ‖X‖ * ‖B‖ + K₀ / r * ‖X‖ * ‖B‖ := add_le_add h1 h2
    _ = (4 * K / r ^ 2 + K₀ / r) * ‖X‖ * ‖B‖ := by ring

end RelativeAverage
end CoreLean

end
