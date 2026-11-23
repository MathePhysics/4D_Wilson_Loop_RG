/-
`prop:relative-average`(iv) of BALABAN_CORE.tex (`d8bdc4ac1777`), the gauge directions: the family of the proof.

For a `0`-form `λ` and `u_t = e^{itλ}`, `𝐔^{u_t} = e^{iB_t}𝐔` with `B_t(b) = (1/i) Log(e^{itλ(b₋)}𝐔(b)e^{-itλ(b₊)}𝐔(b)⁻¹)`
(`Bt`), holomorphic in `t`, and `B_t = -t(aD_𝐔λ) + O(t²)` (`hasDerivAt_Bt`), `aD_𝐔λ(b) = Ad_{𝐔(b)}λ(b₊) - λ(b₋)`
(`Dfine`, `eq:forward-difference` times the spacing).

* `hasDerivAt_Wt`, `hasDerivAt_Bt`, `Bt_zero`;
* `eventually_moveC_Bt`: `e^{iB_t}𝐔 = 𝐔^{u_t}` for `t` near `0`;
* `eventually_Ad_le`: `‖Ad_{u_t(z)}X‖ ≤ 2‖X‖` for `t` near `0`.
-/
import CoreLean.RelativeAverageParts

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

/-- `u_t = e^{itλ}`. -/
def ut (lam : Site n → Mat) (t : ℂ) : Site n → GLN := fun z => expU (t • (Complex.I • lam z))

/-- `e^{itλ(z)}𝐔_μ(z)e^{-itλ(z + e_μ)}𝐔_μ(z)⁻¹`. -/
def Wt (U : Config N n) (lam : Site n → Mat) (t : ℂ) (μ : Fin 4) (z : Site n) : Mat :=
  ((ut lam t z * U μ z * (ut lam t (z + unit n μ))⁻¹ * (U μ z)⁻¹ : GLN) : Mat)

/-- `B_t = (1/i) Log W_t`. -/
def Bt (U : Config N n) (lam : Site n → Mat) (t : ℂ) : Fin 4 → Site n → Mat :=
  fun μ z => (1 / Complex.I : ℂ) • LogM (Wt U lam t μ z)

/-- `aD_𝐔λ` on the positive bonds: `Ad_{𝐔_μ(z)}λ(z + e_μ) - λ(z)`. -/
def Dfine (U : Config N n) (lam : Site n → Mat) : Fin 4 → Site n → Mat :=
  fun μ z => Ad (U μ z) (lam (z + unit n μ)) - lam z

lemma ut_zero (lam : Site n → Mat) : ut lam 0 = fun _ => (1 : GLN) := by
  funext z; simp [ut]

lemma Wt_zero (U : Config N n) (lam : Site n → Mat) (μ : Fin 4) (z : Site n) : Wt U lam 0 μ z = 1 := by
  simp [Wt, ut_zero]

lemma Bt_zero (U : Config N n) (lam : Site n → Mat) : Bt U lam 0 = 0 := by
  funext μ z; simp [Bt, Wt_zero, LogM_one]

lemma hasDerivAt_expU_smul (v : Mat) : HasDerivAt (fun t : ℂ => ((expU (t • v) : GLN) : Mat)) v 0 := by
  simpa using hasDerivAt_exp_smul_const (𝕂 := ℂ) v 0

lemma hasDerivAt_expU_smul_inv (v : Mat) :
    HasDerivAt (fun t : ℂ => (((expU (t • v))⁻¹ : GLN) : Mat)) (-v) 0 := by
  have e : (fun t : ℂ => (((expU (t • v))⁻¹ : GLN) : Mat)) = fun t => exp (t • (-v)) := by
    funext t; rw [expU_inv, expU_val, smul_neg]
  rw [e]
  simpa using hasDerivAt_exp_smul_const (𝕂 := ℂ) (-v) 0

/-- The derivative of `W_t` at `t = 0`. -/
theorem hasDerivAt_Wt (U : Config N n) (lam : Site n → Mat) (μ : Fin 4) (z : Site n) :
    HasDerivAt (fun t => Wt U lam t μ z) (Complex.I • (lam z - Ad (U μ z) (lam (z + unit n μ)))) 0 := by
  have h := (((hasDerivAt_expU_smul (Complex.I • lam z)).fun_mul (hasDerivAt_const (0 : ℂ) ((U μ z : GLN) : Mat))).fun_mul
    (hasDerivAt_expU_smul_inv (Complex.I • lam (z + unit n μ)))).fun_mul
    (hasDerivAt_const (0 : ℂ) (((U μ z)⁻¹ : GLN) : Mat))
  have hfun : (fun t => Wt U lam t μ z) = fun t => ((expU (t • (Complex.I • lam z)) : GLN) : Mat) *
      ((U μ z : GLN) : Mat) * (((expU (t • (Complex.I • lam (z + unit n μ))))⁻¹ : GLN) : Mat) *
      (((U μ z)⁻¹ : GLN) : Mat) := by
    funext t; simp only [Wt, ut, Units.val_mul]
  rw [hfun]
  convert h using 1
  have hUU : ((U μ z : GLN) : Mat) * (((U μ z)⁻¹ : GLN) : Mat) = 1 := by rw [← Units.val_mul, mul_inv_cancel,
    Units.val_one]
  have e1 : ((expU ((0 : ℂ) • (Complex.I • lam z)) : GLN) : Mat) = 1 := by simp
  have e2 : (((expU ((0 : ℂ) • (Complex.I • lam (z + unit n μ))))⁻¹ : GLN) : Mat) = 1 := by simp
  rw [e1, e2]
  simp only [mul_zero, add_zero, mul_one, one_mul]
  simp only [Ad, smul_sub, Matrix.smul_mul, Matrix.mul_smul, add_mul, neg_mul, Matrix.mul_assoc, hUU,
    Matrix.mul_one, sub_eq_add_neg]
  rw [smul_add, smul_neg, Matrix.mul_neg, Matrix.mul_smul]

/-- `B_t = -t(aD_𝐔λ) + O(t²)`. -/
theorem hasDerivAt_Bt (U : Config N n) (lam : Site n → Mat) :
    HasDerivAt (fun t => Bt U lam t) (-Dfine U lam) 0 := by
  refine hasDerivAt_pi.2 fun μ => hasDerivAt_pi.2 fun z => ?_
  have hL := hasFDerivAt_LogM_one (N := N)
  rw [← Wt_zero U lam μ z] at hL
  have h := (hL.comp_hasDerivAt (0 : ℂ) (hasDerivAt_Wt U lam μ z)).const_smul (1 / Complex.I : ℂ)
  have e : (1 / Complex.I : ℂ) • (ContinuousLinearMap.id ℂ Mat)
      (Complex.I • (lam z - Ad (U μ z) (lam (z + unit n μ)))) = (-Dfine U lam) μ z := by
    simp only [ContinuousLinearMap.id_apply, smul_smul, Dfine, Pi.neg_apply, neg_sub]
    rw [show (1 / Complex.I * Complex.I : ℂ) = 1 by field_simp, one_smul]
  rw [← e]
  exact h

/-- `e^{iB_t}𝐔 = 𝐔^{u_t}` for `t` near `0`. -/
theorem eventually_moveC_Bt (U : Config N n) (lam : Site n → Mat) :
    ∀ᶠ t in 𝓝 (0 : ℂ), moveC U (Bt U lam t) = U.gauge (ut lam t) := by
  have hW : ∀ μ z, ∀ᶠ t in 𝓝 (0 : ℂ), ‖Wt U lam t μ z - 1‖ < 1 := fun μ z => by
    refine ContinuousAt.eventually_lt (f := fun t => ‖Wt U lam t μ z - 1‖) (g := fun _ => (1 : ℝ))
      ((hasDerivAt_Wt U lam μ z).continuousAt.sub continuousAt_const).norm continuousAt_const ?_
    simp [Wt_zero]
  filter_upwards [eventually_all.2 fun μ => eventually_all.2 fun z => hW μ z] with t ht
  funext μ z
  ext1
  have hI : Complex.I • ((1 / Complex.I : ℂ) • LogM (Wt U lam t μ z)) = LogM (Wt U lam t μ z) := by
    rw [smul_smul, show (Complex.I * (1 / Complex.I) : ℂ) = 1 by field_simp, one_smul]
  have hUU : (((U μ z)⁻¹ : GLN) : Mat) * ((U μ z : GLN) : Mat) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  simp only [moveC, Bt, Config.gauge, Units.val_mul, expU_val, hI, exp_LogM (ht μ z)]
  simp only [Wt, Units.val_mul, Matrix.mul_assoc, hUU, Matrix.mul_one]

/-- `‖Ad_{u_t(z)}X‖ ≤ 2‖X‖` for `t` near `0`. -/
theorem eventually_Ad_le (lam : Site n → Mat) (z : Site n) :
    ∀ᶠ t in 𝓝 (0 : ℂ), ∀ X : Mat, ‖Ad (ut lam t z) X‖ ≤ 2 * ‖X‖ := by
  have hc : ContinuousAt (fun t : ℂ => ‖((ut lam t z : GLN) : Mat)‖ * ‖(((ut lam t z)⁻¹ : GLN) : Mat)‖) 0 :=
    ((hasDerivAt_expU_smul (Complex.I • lam z)).continuousAt.norm).mul
      ((hasDerivAt_expU_smul_inv (Complex.I • lam z)).continuousAt.norm)
  have h1 : ‖((ut lam 0 z : GLN) : Mat)‖ * ‖(((ut lam 0 z)⁻¹ : GLN) : Mat)‖ < 2 := by
    have e1 : ((ut lam 0 z : GLN) : Mat) = 1 := by simp [ut]
    have e2 : (((ut lam 0 z)⁻¹ : GLN) : Mat) = 1 := by simp [ut]
    rw [e1, e2]
    have : ‖(1 : Mat)‖ ≤ 1 := by
      rcases subsingleton_or_nontrivial Mat with hs | hs
      · rw [Subsingleton.elim (1 : Mat) 0, norm_zero]; norm_num
      · rw [norm_one]
    nlinarith [norm_nonneg (1 : Mat)]
  filter_upwards [hc.eventually_lt continuousAt_const h1] with t ht X
  calc ‖Ad (ut lam t z) X‖ ≤ ‖((ut lam t z : GLN) : Mat)‖ * ‖X‖ * ‖(((ut lam t z)⁻¹ : GLN) : Mat)‖ :=
        GroupMean.norm_Ad_le _ _
    _ = (‖((ut lam t z : GLN) : Mat)‖ * ‖(((ut lam t z)⁻¹ : GLN) : Mat)‖) * ‖X‖ := by ring
    _ ≤ 2 * ‖X‖ := mul_le_mul_of_nonneg_right ht.le (norm_nonneg _)

end RelativeAverage
end CoreLean

end
