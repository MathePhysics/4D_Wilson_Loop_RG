/-
`prop:relative-average`(iv) of BALABAN_CORE.tex (`d8bdc4ac1777`), the gauge directions:

* `Qpl_D`: `Q^{pl}(𝐔)D_𝐔λ = D_{M(𝐔)}(λ|_{T^{(j)}})`;
* `Lam_D`: `Λ(𝐔)D_𝐔λ = Q'(𝐔)λ - λ|_{T^{(j)}}`;
* `Qlin_D`: `Q(𝐔)D_𝐔λ = D_{M(𝐔)}Q'(𝐔)λ`;

with `aD_𝐔λ = Dfine` on the fine lattice and `(D_Mν)(c) = L⁻¹(Ad_{M(c)}ν(c₊) - ν(c₋))` on the coarse one. The proof is
the core's: along `u_t = e^{itλ}`, `𝐔^{u_t} = e^{iB_t}𝐔` with `B_t = -t aD_𝐔λ + O(t²)` (`RelativeAverageGauge.lean`);
by the covariance of the average and of the transports the two sides are computed from `u_t` directly, and the
derivatives at `t = 0` are compared; the first identity follows from (iii) and the other two.
-/
import CoreLean.RelativeAverageGauge

open Matrix NormedSpace Filter Topology
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace CoreLean
namespace RelativeAverage

open LatticePaths LatticeKappa RegularAverages BlockPaths AverageHolo MeanTransports AxialReference

variable {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "GLN" => (Matrix (Fin N) (Fin N) ℂ)ˣ

variable {n : ℕ} [NeZero n]

/-- The derivative of `t ↦ u_t(a)Wu_t(b)⁻¹W⁻¹` at `t = 0`. -/
theorem hasDerivAt_conj (lam : Site n → Mat) (a b : Site n) (W : GLN) :
    HasDerivAt (fun t => ((ut lam t a * W * (ut lam t b)⁻¹ * W⁻¹ : GLN) : Mat))
      (Complex.I • (lam a - Ad W (lam b))) 0 := by
  have h := (((hasDerivAt_expU_smul (Complex.I • lam a)).fun_mul (hasDerivAt_const (0 : ℂ) ((W : GLN) : Mat))).fun_mul
    (hasDerivAt_expU_smul_inv (Complex.I • lam b))).fun_mul (hasDerivAt_const (0 : ℂ) (((W)⁻¹ : GLN) : Mat))
  have hfun : (fun t => ((ut lam t a * W * (ut lam t b)⁻¹ * W⁻¹ : GLN) : Mat)) = fun t =>
      ((expU (t • (Complex.I • lam a)) : GLN) : Mat) * ((W : GLN) : Mat) *
      (((expU (t • (Complex.I • lam b)))⁻¹ : GLN) : Mat) * (((W)⁻¹ : GLN) : Mat) := by
    funext t; simp only [ut, Units.val_mul]
  rw [hfun]
  convert h using 1
  have hWW : ((W : GLN) : Mat) * (((W)⁻¹ : GLN) : Mat) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have e1 : ((expU ((0 : ℂ) • (Complex.I • lam a)) : GLN) : Mat) = 1 := by simp
  have e2 : (((expU ((0 : ℂ) • (Complex.I • lam b)))⁻¹ : GLN) : Mat) = 1 := by simp
  rw [e1, e2]
  simp only [mul_zero, add_zero, mul_one, one_mul]
  simp only [Ad, Matrix.smul_mul, Matrix.mul_smul, add_mul, neg_mul, Matrix.mul_assoc, hWW,
    Matrix.mul_one, sub_eq_add_neg]
  rw [smul_add, smul_neg, Matrix.mul_neg, Matrix.mul_smul]

lemma ut_zero_val (lam : Site n → Mat) (a : Site n) : ut lam 0 a = 1 := by simp [ut]

/-- The derivative of `(1/i) Log(u_t(a)Wu_t(b)⁻¹W⁻¹)` at `t = 0` is `λ(a) - Ad_Wλ(b)`. -/
lemma hasDerivAt_logConj (lam : Site n → Mat) (a b : Site n) (W : GLN) :
    HasDerivAt (fun t => (1 / Complex.I : ℂ) • LogM ((ut lam t a * W * (ut lam t b)⁻¹ * W⁻¹ : GLN) : Mat))
      (lam a - Ad W (lam b)) 0 := by
  have hL := hasFDerivAt_LogM_one (N := N)
  have h0 : ((ut lam 0 a * W * (ut lam 0 b)⁻¹ * W⁻¹ : GLN) : Mat) = 1 := by
    simp [ut_zero_val]
  rw [← h0] at hL
  have h := (hL.comp_hasDerivAt (0 : ℂ) (hasDerivAt_conj lam a b W)).const_smul (1 / Complex.I : ℂ)
  have e : (1 / Complex.I : ℂ) • (ContinuousLinearMap.id ℂ Mat) (Complex.I • (lam a - Ad W (lam b))) =
      lam a - Ad W (lam b) := by
    simp only [ContinuousLinearMap.id_apply, smul_smul]
    rw [show (1 / Complex.I * Complex.I : ℂ) = 1 by field_simp, one_smul]
  rw [← e]
  exact h

/-! ### The third identity -/

/-- **`prop:relative-average`(iv), third identity**: `Q^{pl}(𝐔)D_𝐔λ = D_{M(𝐔)}(λ|_{T^{(j)}})`. -/
theorem Qpl_D {U : Config N n} {y : Site n} {μ : Fin 4} {h : ℕ} (hl : LoopsGood U y μ h) (lam : Site n → Mat) :
    Qpl U y μ h (Dfine U lam) =
      (((2 * h + 1 : ℕ) : ℂ))⁻¹ • (Ad (avgM U y μ h) (lam (cPlus y μ h)) - lam y) := by
  set M := avgM U y μ h with hM
  set F : (Fin 4 → Site n → Mat) → Mat :=
    fun B => (1 / Complex.I : ℂ) • LogM ((avgM (moveC U B) y μ h * M⁻¹ : GLN) : Mat) with hF
  -- `F` is holomorphic at `0`
  have hMA : DifferentiableAt ℂ (fun B => ((avgM (moveC U B) y μ h : GLN) : Mat)) 0 :=
    avgM_differentiableAt (fun B => moveC U B) (moveC_hV U 0) y μ h (by rw [moveC_zero]; exact hl)
  have hF0 : ((avgM (moveC U 0) y μ h * M⁻¹ : GLN) : Mat) = 1 := by simp [moveC_zero, hM]
  have hFd : DifferentiableAt ℂ F 0 := by
    have h1 : DifferentiableAt ℂ (fun B => ((avgM (moveC U B) y μ h * M⁻¹ : GLN) : Mat)) 0 := by
      simp only [Units.val_mul]; exact hMA.mul (differentiableAt_const _)
    have hL := (analyticOnNhd_LogM (N := N) ((avgM (moveC U 0) y μ h * M⁻¹ : GLN) : Mat)
      (by simp only [Set.mem_setOf_eq]; rw [hF0]; simp)).differentiableAt
    exact (DifferentiableAt.comp (f := fun B => ((avgM (moveC U B) y μ h * M⁻¹ : GLN) : Mat))
      (0 : Fin 4 → Site n → Mat) hL h1).fun_const_smul (1 / Complex.I : ℂ)
  -- the chain rule along `B_t`
  have hC : HasDerivAt (fun t => F (Bt U lam t)) (fderiv ℂ F 0 (-Dfine U lam)) 0 := by
    have h1 : HasFDerivAt F (fderiv ℂ F 0) (Bt U lam 0) := by rw [Bt_zero]; exact hFd.hasFDerivAt
    exact h1.comp_hasDerivAt (0 : ℂ) (hasDerivAt_Bt U lam)
  -- the same function from the covariance of the average
  have hev : (fun t => F (Bt U lam t)) =ᶠ[𝓝 0] fun t => (1 / Complex.I : ℂ) •
      LogM ((ut lam t y * M * (ut lam t (cPlus y μ h))⁻¹ * M⁻¹ : GLN) : Mat) := by
    filter_upwards [eventually_moveC_Bt U lam] with t ht
    simp only [hF, ht, avgM_gauge, ← hM]
  have hG := hasDerivAt_logConj lam y (cPlus y μ h) M
  have hval := (hC.congr_of_eventuallyEq hev.symm).unique hG
  -- conclusion
  have hlin : fderiv ℂ F 0 (Dfine U lam) = Ad M (lam (cPlus y μ h)) - lam y := by
    rw [map_neg] at hval
    rw [← neg_neg (fderiv ℂ F 0 (Dfine U lam)), hval, neg_sub]
  simp only [Qpl, ContinuousLinearMap.smul_apply]
  rw [← hF, hlin]

/-! ### The second identity -/

/-- **`prop:relative-average`(iv), second identity**: `Λ(𝐔)D_𝐔λ = Q'(𝐔)λ - λ|_{T^{(j)}}`. -/
theorem Lam_D {U : Config N n} {y : Site n} {h : ℕ} (hg : GoodAt U y h) (lam : Site n → Mat) :
    Lam U y h (Dfine U lam) = blockAvg U lam y h - lam y := by
  set F : (Fin 4 → Site n → Mat) → Mat :=
    fun B => (1 / Complex.I : ℂ) • LogM ((siteFactor U B y h : GLN) : Mat) with hF
  have hFd : DifferentiableAt ℂ F 0 := by
    have hL := (analyticOnNhd_LogM (N := N) ((siteFactor U 0 y h : GLN) : Mat)
      (by simp only [Set.mem_setOf_eq]; rw [siteFactor_zero]; simp)).differentiableAt
    exact (DifferentiableAt.comp (f := fun B => ((siteFactor U B y h : GLN) : Mat))
      (0 : Fin 4 → Site n → Mat) hL (siteFactor_differentiableAt_zero hg)).fun_const_smul (1 / Complex.I : ℂ)
  have hC : HasDerivAt (fun t => F (Bt U lam t)) (fderiv ℂ F 0 (-Dfine U lam)) 0 := by
    have h1 : HasFDerivAt F (fderiv ℂ F 0) (Bt U lam 0) := by rw [Bt_zero]; exact hFd.hasFDerivAt
    exact h1.comp_hasDerivAt (0 : ℂ) (hasDerivAt_Bt U lam)
  -- the exponent of the site factor along `u_t`
  set S : ℂ → Mat := fun t => (((2 * h + 1 : ℕ) : ℂ) ^ 4)⁻¹ • ∑ x : Pts h,
    LogM ((ut lam t y * trans U y h x * (ut lam t (ofs y (offP h x)))⁻¹ * (trans U y h x)⁻¹ : GLN) : Mat)
    with hS
  have hSd : HasDerivAt (fun t => (1 / Complex.I : ℂ) • S t) (lam y - blockAvg U lam y h) 0 := by
    have hsum : HasDerivAt (fun t => ∑ x : Pts h, (1 / Complex.I : ℂ) •
        LogM ((ut lam t y * trans U y h x * (ut lam t (ofs y (offP h x)))⁻¹ * (trans U y h x)⁻¹ : GLN) : Mat))
        (∑ x : Pts h, (lam y - Ad (trans U y h x) (lam (ofs y (offP h x))))) 0 :=
      HasDerivAt.fun_sum fun x _ => hasDerivAt_logConj lam y (ofs y (offP h x)) (trans U y h x)
    have hL4 : (((2 * h + 1 : ℕ) : ℂ) ^ 4) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (by omega))
    have e : (fun t => (1 / Complex.I : ℂ) • S t) = fun t => (((2 * h + 1 : ℕ) : ℂ) ^ 4)⁻¹ •
        ∑ x : Pts h, (1 / Complex.I : ℂ) • LogM ((ut lam t y * trans U y h x *
          (ut lam t (ofs y (offP h x)))⁻¹ * (trans U y h x)⁻¹ : GLN) : Mat) := by
      funext t; simp only [hS, Finset.smul_sum, smul_smul, mul_comm]
    rw [e]
    convert hsum.const_smul ((((2 * h + 1 : ℕ) : ℂ) ^ 4)⁻¹) using 1
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, card_pts, smul_sub, blockAvg]
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, Nat.cast_pow, inv_mul_cancel₀ hL4, one_smul]
  have hS0 : S 0 = 0 := by simp [hS, ut_zero_val, LogM_one]
  have hSc : ∀ᶠ t in 𝓝 (0 : ℂ), ‖S t‖ < Real.log 2 := by
    have hSdiff : HasDerivAt S (Complex.I • (lam y - blockAvg U lam y h)) 0 := by
      have e : (fun t => Complex.I • ((1 / Complex.I : ℂ) • S t)) = S := by
        funext t; rw [smul_smul, show (Complex.I * (1 / Complex.I) : ℂ) = 1 by field_simp, one_smul]
      have := hSd.fun_const_smul Complex.I
      rwa [e] at this
    refine ContinuousAt.eventually_lt (f := fun t => ‖S t‖) (g := fun _ => Real.log 2)
      hSdiff.continuousAt.norm continuousAt_const ?_
    rw [hS0, norm_zero]; exact Real.log_pos one_lt_two
  -- along `u_t` the site factor is `e^{S_t}`
  have hev : (fun t => F (Bt U lam t)) =ᶠ[𝓝 0] fun t => (1 / Complex.I : ℂ) • S t := by
    have hAd := eventually_Ad_le lam y
    filter_upwards [eventually_moveC_Bt U lam, hAd, hSc] with t ht hAdt hSt
    have hsf : siteFactor U (Bt U lam t) y h = expU (S t) := by
      have hsum : ∀ x : Pts h, LogM ((trans (moveC U (Bt U lam t)) y h x * (trans U y h x)⁻¹ : GLN) : Mat) =
          LogM ((ut lam t y * trans U y h x * (ut lam t (ofs y (offP h x)))⁻¹ * (trans U y h x)⁻¹ : GLN) :
            Mat) := fun x => by
        rw [ht, trans_gauge U (ut lam t) y h x hAdt (hg.expsG_le x)]
      unfold siteFactor
      rw [Finset.sum_congr rfl fun x _ => hsum x]
    simp only [hF, hsf, expU_val, LogM_exp hSt]
  have hval := (hC.congr_of_eventuallyEq hev.symm).unique hSd
  rw [map_neg] at hval
  show fderiv ℂ F 0 (Dfine U lam) = _
  rw [← neg_neg (fderiv ℂ F 0 (Dfine U lam)), hval, neg_sub]

/-! ### The first identity -/

/-- **`prop:relative-average`(iv), first identity**: `Q(𝐔)D_𝐔λ = D_{M(𝐔)}Q'(𝐔)λ`. -/
theorem Qlin_D {U : Config N n} {y : Site n} {μ : Fin 4} {h : ℕ} (hg : GoodAt U y h)
    (hg' : GoodAt U (cPlus y μ h) h) (hl : LoopsGood U y μ h) (lam : Site n → Mat) :
    Qlin U y μ h (Dfine U lam) = (((2 * h + 1 : ℕ) : ℂ))⁻¹ •
      (Ad (avgM U y μ h) (blockAvg U lam (cPlus y μ h) h) - blockAvg U lam y h) := by
  have h3 := two_linear_parts hg hg' hl
  have e : Qlin U y μ h = Qpl U y μ h +
      (((2 * h + 1 : ℕ) : ℂ))⁻¹ • ((AdL (avgM U y μ h)).comp (Lam U (cPlus y μ h) h) - Lam U y h) := by
    rw [h3]; abel
  rw [e]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.comp_apply, AdL_apply, Qpl_D hl, Lam_D hg, Lam_D hg', Ad_sub]
  rw [← smul_add]
  congr 1
  abel

end RelativeAverage
end CoreLean

end
