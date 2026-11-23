/-
`prop:relative-average`(iii) of BALABAN_CORE.tex (`d8bdc4ac1777`), the two linear parts.

With `B = aA` and the coarse spacing `La = L`:
* `Lam V y' h`: `Λ(𝐔)A`, the linear part in `A` of `(1/i) Log v_𝐔(A)(y')`;
* `Qpl V y μ h`: `Q^{pl}(𝐔)`, `L⁻¹` times the linear part of `(1/i) Log(M(e^{iaA}𝐔)(c)M(𝐔)(c)⁻¹)`;
* `two_linear_parts`: `Q^{pl}(𝐔) = Q(𝐔) - D_{M(𝐔)}Λ(𝐔)`, `(D_Mλ)(c) = L⁻¹(Ad_{M(c)}λ(c₊) - λ(c₋))`
  (`eq:forward-difference` on the coarse lattice).

The proof is the core's: by `eq:average-of-product`, `M(𝐔_A)(c)M(𝐔)(c)⁻¹ = v(c₋) 𝓜(A)(c) Ad_{M(c)}v(c₊)⁻¹`, three
matrices equal to `id` at `A = 0`, and the linear part of the logarithm of their product is the sum of the linear
parts of the three (`hasFDerivAt_LogM_one`: the derivative of `Log` at `id` is the identity, from `Log e^Z = Z`).
-/
import CoreLean.RelativeAverageLinear
import Mathlib.Analysis.SpecialFunctions.Exponential

open Matrix NormedSpace Filter Topology
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace CoreLean
namespace RelativeAverage

open LatticePaths LatticeKappa RegularAverages BlockPaths AverageHolo MeanTransports AxialReference

variable {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "GLN" => (Matrix (Fin N) (Fin N) ℂ)ˣ

variable {n : ℕ} [NeZero n] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The derivative of `Log` at `id` is the identity. -/
theorem hasFDerivAt_LogM_one : HasFDerivAt (LogM (N := N)) (ContinuousLinearMap.id ℂ Mat) 1 := by
  have hd : DifferentiableAt ℂ (LogM (N := N)) 1 :=
    (analyticOnNhd_LogM (N := N) 1 (by simp)).differentiableAt
  have hexp : HasFDerivAt (exp : Mat → Mat) (1 : Mat →L[ℂ] Mat) 0 := hasFDerivAt_exp_zero
  have hcomp : HasFDerivAt (fun Z : Mat => LogM (exp Z)) ((fderiv ℂ LogM 1).comp (1 : Mat →L[ℂ] Mat)) 0 := by
    have h1 : HasFDerivAt (LogM (N := N)) (fderiv ℂ LogM 1) (exp (0 : Mat)) := by
      rw [exp_zero]; exact hd.hasFDerivAt
    exact h1.comp 0 hexp
  have hev : (fun Z : Mat => LogM (exp Z)) =ᶠ[𝓝 0] fun Z => Z := by
    filter_upwards [Metric.ball_mem_nhds (0 : Mat) (Real.log_pos one_lt_two)] with Z hZ
    rw [Metric.mem_ball, dist_zero_right] at hZ
    exact LogM_exp hZ
  have hid : HasFDerivAt (fun Z : Mat => LogM (exp Z)) (ContinuousLinearMap.id ℂ Mat) 0 :=
    (hasFDerivAt_id (0 : Mat)).congr_of_eventuallyEq hev
  have e := hcomp.unique hid
  have e2 : fderiv ℂ (LogM (N := N)) 1 = ContinuousLinearMap.id ℂ Mat := by
    rw [← e]; ext1 v; simp
  rw [← e2]; exact hd.hasFDerivAt

/-- The linear part of `Log X` at a point where `X = id` is the linear part of `X`. -/
lemma LogM_comp_one {X : E → Mat} {dX : E →L[ℂ] Mat} {p₀ : E} (hX : HasFDerivAt X dX p₀) (h1 : X p₀ = 1) :
    HasFDerivAt (fun p => LogM (X p)) dX p₀ := by
  have h := hasFDerivAt_LogM_one (N := N)
  rw [← h1] at h
  exact h.comp p₀ hX

/-- The linear part of a product of three matrices equal to `id` at `p₀` is the sum of their linear parts. -/
lemma prod3_one {X Y Z : E → Mat} {dX dY dZ : E →L[ℂ] Mat} {p₀ : E} (hX : HasFDerivAt X dX p₀)
    (hY : HasFDerivAt Y dY p₀) (hZ : HasFDerivAt Z dZ p₀) (hX1 : X p₀ = 1) (hY1 : Y p₀ = 1) (hZ1 : Z p₀ = 1) :
    HasFDerivAt (fun p => X p * Y p * Z p) (dX + dY + dZ) p₀ := by
  have h := (hX.mul' hY).mul' hZ
  convert h using 1
  ext1 v
  simp [hX1, hY1, hZ1, add_comm, add_left_comm]

/-- The derivative of the inverse of a family equal to `id` at `p₀` is the negative of its derivative. -/
lemma inv_one {W : E → GLN} {dW : E →L[ℂ] Mat} {p₀ : E} (hW : HasFDerivAt (fun p => ((W p : GLN) : Mat)) dW p₀)
    (h1 : W p₀ = 1) : HasFDerivAt (fun p => (((W p)⁻¹ : GLN) : Mat)) (-dW) p₀ := by
  have e : (fun p => (((W p)⁻¹ : GLN) : Mat)) = fun p => Ring.inverse ((W p : GLN) : Mat) := by
    funext p; rw [Ring.inverse_unit]
  rw [e]
  have hinv := hasFDerivAt_ringInverse (𝕜 := ℂ) (W p₀)
  have hc := hinv.comp p₀ hW
  have hD : (-((ContinuousLinearMap.mulLeftRight ℂ Mat) ((W p₀)⁻¹ : GLN) ((W p₀)⁻¹ : GLN))).comp dW = -dW := by
    ext1 v; simp [h1]
  rw [hD] at hc
  exact hc

/-! ### The two linear parts -/

/-- `Λ(𝐔)`: the linear part of `(1/i) Log v_𝐔(·)(y')`. -/
def Lam (V : Config N n) (y' : Site n) (h : ℕ) : (Fin 4 → Site n → Mat) →L[ℂ] Mat :=
  fderiv ℂ (fun B => (1 / Complex.I : ℂ) • LogM ((siteFactor V B y' h : GLN) : Mat)) 0

/-- `Q^{pl}(𝐔)`: `L⁻¹` times the linear part of `(1/i) Log(M(e^{iB}𝐔)(c)M(𝐔)(c)⁻¹)`. -/
def Qpl (V : Config N n) (y : Site n) (μ : Fin 4) (h : ℕ) : (Fin 4 → Site n → Mat) →L[ℂ] Mat :=
  (((2 * h + 1 : ℕ) : ℂ))⁻¹ •
    fderiv ℂ (fun B => (1 / Complex.I : ℂ) • LogM ((avgM (moveC V B) y μ h * (avgM V y μ h)⁻¹ : GLN) : Mat)) 0

/-- The site factor is holomorphic at `A = 0` under the conditions at `y'`. -/
lemma siteFactor_differentiableAt_zero {V : Config N n} {y' : Site n} {h : ℕ} (hg : GoodAt V y' h) :
    DifferentiableAt ℂ (fun B => ((siteFactor V B y' h : GLN) : Mat)) 0 := by
  refine siteFactor_differentiableAt (fun _ => V) (fun B => B) y' h (fun x => ?_)
    (fun x => differentiableAt_const _) (fun x => by simp [moveC_zero])
  exact trans_moveC_differentiableAt (B₀ := 0) (by rw [moveC_zero]; exact hg) x

/-- `𝓜` is holomorphic at `A = 0` under the conditions at both ends and on the loops. -/
lemma relAvg_differentiableAt_zero {V : Config N n} {y : Site n} {μ : Fin 4} {h : ℕ} (hg : GoodAt V y h)
    (hg' : GoodAt V (cPlus y μ h) h) (hl : LoopsGood V y μ h) :
    DifferentiableAt ℂ (fun B => ((relAvg V B y μ h : GLN) : Mat)) 0 :=
  relAvg_differentiableAt (fun _ => V) (fun B => B) y μ h (siteFactor_differentiableAt_zero hg)
    (siteFactor_differentiableAt_zero hg')
    (avgM_differentiableAt (fun B => moveC V B) (moveC_hV V 0) y μ h (by rw [moveC_zero]; exact hl))
    (differentiableAt_const _)

/-- **`prop:relative-average`(iii)**: `Q^{pl}(𝐔) = Q(𝐔) - D_{M(𝐔)}Λ(𝐔)`. -/
theorem two_linear_parts {V : Config N n} {y : Site n} {μ : Fin 4} {h : ℕ} (hg : GoodAt V y h)
    (hg' : GoodAt V (cPlus y μ h) h) (hl : LoopsGood V y μ h) :
    Qpl V y μ h = Qlin V y μ h -
      (((2 * h + 1 : ℕ) : ℂ))⁻¹ • ((AdL (avgM V y μ h)).comp (Lam V (cPlus y μ h) h) - Lam V y h) := by
  have hL : (((2 * h + 1 : ℕ) : ℂ)) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  set M := avgM V y μ h
  -- the three factors and their linear parts
  have hX := (siteFactor_differentiableAt_zero hg).hasFDerivAt
  have hY := (relAvg_differentiableAt_zero hg hg' hl).hasFDerivAt
  have hW := (siteFactor_differentiableAt_zero hg').hasFDerivAt
  have hZ : HasFDerivAt (fun B => ((M * (siteFactor V B (cPlus y μ h) h)⁻¹ * M⁻¹ : GLN) : Mat))
      ((AdL M).comp (-fderiv ℂ (fun B => ((siteFactor V B (cPlus y μ h) h : GLN) : Mat)) 0)) 0 := by
    have hi := inv_one hW (siteFactor_zero V _ h)
    have e : (fun B => ((M * (siteFactor V B (cPlus y μ h) h)⁻¹ * M⁻¹ : GLN) : Mat)) =
        fun B => AdL M (((siteFactor V B (cPlus y μ h) h)⁻¹ : GLN) : Mat) := by
      funext B; simp [Ad]
    rw [e]
    exact (AdL M).hasFDerivAt.comp 0 hi
  have hprod := prod3_one hX hY hZ (by simp [siteFactor_zero]) (by simp [relAvg_zero]) (by simp [siteFactor_zero])
  -- the identity `M(𝐔_A)M(𝐔)⁻¹ = v(c₋) 𝓜 (M v(c₊)⁻¹ M⁻¹)`
  have hid : (fun B => ((avgM (moveC V B) y μ h * M⁻¹ : GLN) : Mat)) = fun B =>
      ((siteFactor V B y h : GLN) : Mat) * ((relAvg V B y μ h : GLN) : Mat) *
        ((M * (siteFactor V B (cPlus y μ h) h)⁻¹ * M⁻¹ : GLN) : Mat) := by
    funext B
    have hG : avgM (moveC V B) y μ h * M⁻¹ =
        siteFactor V B y h * relAvg V B y μ h * (M * (siteFactor V B (cPlus y μ h) h)⁻¹ * M⁻¹) := by
      rw [average_of_product, show avgM V y μ h = M from rfl]; group
    rw [hG, Units.val_mul, Units.val_mul]
  have hone : ((siteFactor V 0 y h : GLN) : Mat) * ((relAvg V 0 y μ h : GLN) : Mat) *
      ((M * (siteFactor V 0 (cPlus y μ h) h)⁻¹ * M⁻¹ : GLN) : Mat) = 1 := by
    rw [siteFactor_zero, relAvg_zero, siteFactor_zero]; simp
  have hlogP0 := LogM_comp_one hprod hone
  have hlogP : HasFDerivAt (fun B => LogM ((avgM (moveC V B) y μ h * M⁻¹ : GLN) : Mat)) _ 0 :=
    hlogP0.congr_of_eventuallyEq (Filter.Eventually.of_forall fun B => by
      show LogM _ = LogM _
      rw [congrFun hid B])
  have hQpl : fderiv ℂ (fun B => (1 / Complex.I : ℂ) • LogM ((avgM (moveC V B) y μ h * M⁻¹ : GLN) : Mat)) 0 =
      (1 / Complex.I : ℂ) • (fderiv ℂ (fun B => ((siteFactor V B y h : GLN) : Mat)) 0 +
        fderiv ℂ (fun B => ((relAvg V B y μ h : GLN) : Mat)) 0 +
        (AdL M).comp (-fderiv ℂ (fun B => ((siteFactor V B (cPlus y μ h) h : GLN) : Mat)) 0)) :=
    (hlogP.const_smul (1 / Complex.I : ℂ)).fderiv
  have hLam : ∀ y', GoodAt V y' h → Lam V y' h =
      (1 / Complex.I : ℂ) • fderiv ℂ (fun B => ((siteFactor V B y' h : GLN) : Mat)) 0 := fun y' hy' =>
    ((LogM_comp_one (siteFactor_differentiableAt_zero hy').hasFDerivAt
      (by simp [siteFactor_zero])).const_smul (1 / Complex.I : ℂ)).fderiv
  have hQ : ((2 * h + 1 : ℕ) : ℂ) • Qlin V y μ h =
      (1 / Complex.I : ℂ) • fderiv ℂ (fun B => ((relAvg V B y μ h : GLN) : Mat)) 0 := by
    have : fderiv ℂ (fun B => relLog V B y μ h) 0 =
        (1 / Complex.I : ℂ) • fderiv ℂ (fun B => ((relAvg V B y μ h : GLN) : Mat)) 0 :=
      ((LogM_comp_one hY (by simp [relAvg_zero])).const_smul (1 / Complex.I : ℂ)).fderiv
    rw [Qlin, smul_smul, mul_inv_cancel₀ hL, one_smul, this]
  have hQ' : Qlin V y μ h = (((2 * h + 1 : ℕ) : ℂ))⁻¹ •
      ((1 / Complex.I : ℂ) • fderiv ℂ (fun B => ((relAvg V B y μ h : GLN) : Mat)) 0) := by
    rw [← hQ, smul_smul, inv_mul_cancel₀ hL, one_smul]
  rw [Qpl, hQpl, hQ', hLam y hg, hLam _ hg']
  ext1 B
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply, AdL_apply, Ad_smul, Ad_neg]
  module

end RelativeAverage
end CoreLean

end
