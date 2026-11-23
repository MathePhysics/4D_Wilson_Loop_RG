/-
The linear part and the remainder of the relative average, `eq:linear-part` of BALABAN_CORE.tex (`d8bdc4ac1777`).

`(1/i) Log 𝓜_𝐔(A)(c) = La(Q(𝐔)A)(c) + C(𝐔; aA)(c)`; with `B = aA` (spacing one, `prop:relative-average`(viii)) the
linear part is `Q(𝐔) = L⁻¹ D[(1/i) Log 𝓜_𝐔(·)(c)](0)` (`Qlin`) and the remainder `C(𝐔; B) = (1/i) Log 𝓜_𝐔(B)(c) -
L·Q(𝐔)B` (`Crem`).

* `relAvg_zero`: `𝓜_𝐔(0)(c) = id`, so that `C(𝐔; 0) = 0` (`Crem_zero`).
* `GoodAt`, `LoopsGood`: the background conditions under which the objects are holomorphic (the quotients of the
  holonomies in the domain of `Log`, the exponents in the ball of radius `ϱ_m = 2^{-10}`, the loops in the domain of
  `Log`); they persist for `𝐔_A` with `A` near `0` (`eventually_goodAt`, `eventually_loopsGood`).
* `relLog_differentiableAt`: at such a background `B ↦ (1/i) Log 𝓜_𝐔(B)(c)` is holomorphic at `0`, so that `Q` is its
  derivative and `C` vanishes to the second order (`Crem_hasFDerivAt`).
-/
import CoreLean.RelativeAverageCov

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

/-- `(1/i) Log 𝓜_𝐔(A)(c)`. -/
def relLog (V : Config N n) (B : Fin 4 → Site n → Mat) (y : Site n) (μ : Fin 4) (h : ℕ) : Mat :=
  (1 / Complex.I : ℂ) • LogM ((relAvg V B y μ h : GLN) : Mat)

/-- The linear part `Q(𝐔)` of `eq:linear-part`. -/
def Qlin (V : Config N n) (y : Site n) (μ : Fin 4) (h : ℕ) : (Fin 4 → Site n → Mat) →L[ℂ] Mat :=
  (((2 * h + 1 : ℕ) : ℂ))⁻¹ • fderiv ℂ (fun B => relLog V B y μ h) 0

/-- The remainder `C(𝐔; aA)` of `eq:linear-part`. -/
def Crem (V : Config N n) (B : Fin 4 → Site n → Mat) (y : Site n) (μ : Fin 4) (h : ℕ) : Mat :=
  relLog V B y μ h - ((2 * h + 1 : ℕ) : ℂ) • Qlin V y μ h B

/-- `eq:linear-part`. -/
theorem linear_part (V : Config N n) (B : Fin 4 → Site n → Mat) (y : Site n) (μ : Fin 4) (h : ℕ) :
    relLog V B y μ h = ((2 * h + 1 : ℕ) : ℂ) • Qlin V y μ h B + Crem V B y μ h := by
  simp [Crem]

lemma moveC_zero (V : Config N n) : moveC V 0 = V := by
  funext μ z; simp [moveC]

lemma siteFactor_zero (V : Config N n) (y : Site n) (h : ℕ) : siteFactor V 0 y h = 1 := by
  simp [siteFactor, moveC_zero, LogM_one]

/-- `𝓜_𝐔(0)(c) = id`. -/
theorem relAvg_zero (V : Config N n) (y : Site n) (μ : Fin 4) (h : ℕ) : relAvg V 0 y μ h = 1 := by
  simp [relAvg, siteFactor_zero, moveC_zero]

lemma relLog_zero (V : Config N n) (y : Site n) (μ : Fin 4) (h : ℕ) : relLog V 0 y μ h = 0 := by
  simp [relLog, relAvg_zero, LogM_one]

/-- `C(𝐔; 0) = 0`. -/
theorem Crem_zero (V : Config N n) (y : Site n) (μ : Fin 4) (h : ℕ) : Crem V 0 y μ h = 0 := by
  simp [Crem, relLog_zero]

/-- `C(𝐔; ·)` vanishes to the second order at `0` where `(1/i) Log 𝓜_𝐔(·)(c)` is holomorphic at `0`. -/
theorem Crem_hasFDerivAt (V : Config N n) (y : Site n) (μ : Fin 4) (h : ℕ)
    (hd : DifferentiableAt ℂ (fun B => relLog V B y μ h) 0) :
    HasFDerivAt (fun B => Crem V B y μ h) (0 : (Fin 4 → Site n → Mat) →L[ℂ] Mat) (0 : Fin 4 → Site n → Mat) := by
  have hL : (((2 * h + 1 : ℕ) : ℂ)) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have h1 := hd.hasFDerivAt
  have h2 : HasFDerivAt (fun B => ((2 * h + 1 : ℕ) : ℂ) • Qlin V y μ h B)
      (((2 * h + 1 : ℕ) : ℂ) • Qlin V y μ h) 0 := by
    exact (((2 * h + 1 : ℕ) : ℂ) • Qlin V y μ h).hasFDerivAt (x := (0 : Fin 4 → Site n → Mat))
  have h3 := h1.sub h2
  have e : fderiv ℂ (fun B => relLog V B y μ h) 0 - ((2 * h + 1 : ℕ) : ℂ) • Qlin V y μ h = 0 := by
    simp only [Qlin, smul_smul, mul_inv_cancel₀ hL, one_smul, sub_self]
  rw [e] at h3
  exact h3

/-! ### The conditions on the background -/

/-- The quotients `𝐔(Γᵢ)𝐔(Γ₀)⁻¹` of the paths of `𝐆(y, x)`. -/
def quotG (V : Config N n) (y : Site n) (h : ℕ) (x : Pts h) (i : Fin (nG h x)) : GLN :=
  holG V y h x (enumG h x i) * (holG V y h x (firstG h x))⁻¹

/-- The transports from `y` are holomorphic and covariant at `𝐔`: the quotients lie in the domain of `Log` and the
exponents in the ball of radius `ϱ_m = 2^{-10}`. -/
def GoodAt (V : Config N n) (y : Site n) (h : ℕ) : Prop :=
  (∀ x i, ‖((quotG V y h x i : GLN) : Mat) - 1‖ < 1) ∧ ∀ x, ‖expsG V y h x‖ < 1 / 1024

/-- The loops of the bond `c = (y, y + Le_μ)` lie in the domain of `Log` at `𝐔`. -/
def LoopsGood (V : Config N n) (y : Site n) (μ : Fin 4) (h : ℕ) : Prop :=
  ∀ x Γ Γ', ‖(((V.hol (lpath (ι := Pts h) (P := fun x => Ords (offP h x)) y μ (2 * h + 1) (offP h) (ordG h)
    x Γ Γ')) : GLN) : Mat) - 1‖ < 1

lemma GoodAt.expsG_le {V : Config N n} {y : Site n} {h : ℕ} (hg : GoodAt V y h) (x : Pts h) (i : Fin (nG h x)) :
    ‖expsG V y h x i‖ ≤ 1 / 1024 :=
  (norm_le_pi_norm (expsG V y h x) i).trans (hg.2 x).le

lemma moveC_hV (V : Config N n) (B₀ : Fin 4 → Site n → Mat) :
    ∀ μ z, DifferentiableAt ℂ (fun B : Fin 4 → Site n → Mat => (((moveC V B) μ z : GLN) : Mat)) B₀ :=
  fun μ z => moveC_differentiableAt V B₀ μ z

lemma quotG_continuousAt (V : Config N n) (y : Site n) (h : ℕ) (x : Pts h) (i : Fin (nG h x))
    (B₀ : Fin 4 → Site n → Mat) :
    ContinuousAt (fun B => ((quotG (moveC V B) y h x i : GLN) : Mat)) B₀ := by
  simp only [quotG, Units.val_mul]
  exact ((hol_differentiableAt (fun B => moveC V B) (moveC_hV V B₀) _).mul
    (inv_differentiableAt (hol_differentiableAt (fun B => moveC V B) (moveC_hV V B₀) _))).continuousAt

/-- The conditions on the transports persist for `𝐔_A` with `A` near `0`. -/
theorem eventually_goodAt {V : Config N n} {y : Site n} {h : ℕ} (hg : GoodAt V y h) :
    ∀ᶠ B in 𝓝 (0 : Fin 4 → Site n → Mat), GoodAt (moveC V B) y h := by
  have h1 : ∀ x i, ∀ᶠ B in 𝓝 (0 : Fin 4 → Site n → Mat),
      ‖((quotG (moveC V B) y h x i : GLN) : Mat) - 1‖ < 1 := fun x i => by
    refine ContinuousAt.eventually_lt (f := fun B => ‖((quotG (moveC V B) y h x i : GLN) : Mat) - 1‖)
      (g := fun _ => (1 : ℝ)) ((quotG_continuousAt V y h x i 0).sub continuousAt_const).norm
      continuousAt_const ?_
    show ‖((quotG (moveC V 0) y h x i : GLN) : Mat) - 1‖ < 1
    rw [moveC_zero]; exact hg.1 x i
  have h2 : ∀ x, ∀ᶠ B in 𝓝 (0 : Fin 4 → Site n → Mat), ‖expsG (moveC V B) y h x‖ < 1 / 1024 := fun x => by
    have hd := expsG_differentiableAt (fun B => moveC V B) (moveC_hV V 0) y h x
      (by rw [moveC_zero]; exact fun i => hg.1 x i)
    refine ContinuousAt.eventually_lt (f := fun B => ‖expsG (moveC V B) y h x‖) (g := fun _ => (1 / 1024 : ℝ))
      hd.continuousAt.norm continuousAt_const ?_
    show ‖expsG (moveC V 0) y h x‖ < 1 / 1024
    rw [moveC_zero]; exact hg.2 x
  exact (eventually_all.2 fun x => eventually_all.2 fun i => h1 x i).and (eventually_all.2 h2)

/-- The condition on the loops persists for `𝐔_A` with `A` near `0`. -/
theorem eventually_loopsGood {V : Config N n} {y : Site n} {μ : Fin 4} {h : ℕ} (hl : LoopsGood V y μ h) :
    ∀ᶠ B in 𝓝 (0 : Fin 4 → Site n → Mat), LoopsGood (moveC V B) y μ h := by
  refine eventually_all.2 fun x => eventually_all.2 fun Γ => eventually_all.2 fun Γ' => ?_
  refine ContinuousAt.eventually_lt (g := fun _ => (1 : ℝ)) (((hol_differentiableAt (fun B => moveC V B)
    (moveC_hV V 0) _).continuousAt).sub continuousAt_const).norm continuousAt_const ?_
  show ‖(((moveC V 0).hol (lpath (ι := Pts h) (P := fun x => Ords (offP h x)) y μ (2 * h + 1) (offP h) (ordG h)
    x Γ Γ') : GLN) : Mat) - 1‖ < 1
  rw [moveC_zero]; exact hl x Γ Γ'

/-- The transports of `𝐔_A` are holomorphic in `A` where the conditions hold. -/
lemma trans_moveC_differentiableAt {V : Config N n} {y : Site n} {h : ℕ} {B₀ : Fin 4 → Site n → Mat}
    (hg : GoodAt (moveC V B₀) y h) (x : Pts h) :
    DifferentiableAt ℂ (fun B => ((trans (moveC V B) y h x : GLN) : Mat)) B₀ :=
  trans_differentiableAt (fun B => moveC V B) (moveC_hV V B₀) y h x (hg.1 x) ((hg.2 x).trans (by norm_num))

/-- **Holomorphy of `(1/i) Log 𝓜_𝐔(·)(c)` at `0`**, at a background which satisfies the conditions at both ends of
the bond and on its loops. -/
theorem relLog_differentiableAt {V : Config N n} {y : Site n} {μ : Fin 4} {h : ℕ} (hg : GoodAt V y h)
    (hg' : GoodAt V (cPlus y μ h) h) (hl : LoopsGood V y μ h) :
    DifferentiableAt ℂ (fun B => relLog V B y μ h) 0 := by
  have hv : ∀ y', GoodAt V y' h →
      DifferentiableAt ℂ (fun B => ((siteFactor V B y' h : GLN) : Mat)) 0 := fun y' hy' => by
    refine siteFactor_differentiableAt (fun _ => V) (fun B => B) y' h (fun x => ?_)
      (fun x => differentiableAt_const _) (fun x => by simp [moveC_zero])
    exact trans_moveC_differentiableAt (B₀ := 0) (by rw [moveC_zero]; exact hy') x
  have hMA : DifferentiableAt ℂ (fun B => ((avgM (moveC V B) y μ h : GLN) : Mat)) 0 :=
    avgM_differentiableAt (fun B => moveC V B) (moveC_hV V 0) y μ h (by rw [moveC_zero]; exact hl)
  have hR := relAvg_differentiableAt (fun _ => V) (fun B => B) y μ h (hv y hg) (hv _ hg') hMA
    (differentiableAt_const _)
  have hdom : ‖((relAvg V 0 y μ h : GLN) : Mat) - 1‖ < 1 := by simp [relAvg_zero]
  have hL := (analyticOnNhd_LogM (N := N) _ hdom).differentiableAt
  exact (DifferentiableAt.comp (f := fun B => ((relAvg V B y μ h : GLN) : Mat)) (0 : Fin 4 → Site n → Mat)
    hL hR).fun_const_smul (1 / Complex.I : ℂ)

/-! ### The covariance of the linear part -/

/-- `X ↦ Ad_WX` as a continuous linear map. -/
def AdL (W : GLN) : Mat →L[ℂ] Mat :=
  LinearMap.toContinuousLinearMap
    { toFun := Ad W, map_add' := Ad_add W, map_smul' := fun c X => Ad_smul W c X }

@[simp] lemma AdL_apply (W : GLN) (X : Mat) : AdL W X = Ad W X := rfl

/-- `A ↦ Ad_uA` as a continuous linear map. -/
def AdFL (u : Site n → GLN) : (Fin 4 → Site n → Mat) →L[ℂ] (Fin 4 → Site n → Mat) :=
  LinearMap.toContinuousLinearMap
    { toFun := AdF u
      map_add' := fun B B' => by funext μ z; simp [AdF, Ad_add]
      map_smul' := fun c B => by funext μ z; simp [AdF, Ad_smul] }

@[simp] lemma AdFL_apply (u : Site n → GLN) (B : Fin 4 → Site n → Mat) : AdFL u B = AdF u B := rfl

lemma AdF_inv (u : Site n → GLN) (B : Fin 4 → Site n → Mat) : AdF u (AdF (fun z => (u z)⁻¹) B) = B := by
  funext μ z; simp only [AdF, ← Ad_mul, mul_inv_cancel, Ad_one]

lemma AdF_inv' (u : Site n → GLN) (B : Fin 4 → Site n → Mat) : AdF (fun z => (u z)⁻¹) (AdF u B) = B := by
  funext μ z; simp only [AdF, ← Ad_mul, inv_mul_cancel, Ad_one]

/-- `(1/i) Log 𝓜` is covariant where `𝓜` is. -/
lemma relLog_of_relAvg {V V' : Config N n} {B B' : Fin 4 → Site n → Mat} {y : Site n} {μ : Fin 4} {h : ℕ}
    (w : GLN) (he : relAvg V' B' y μ h = w * relAvg V B y μ h * w⁻¹) :
    relLog V' B' y μ h = Ad w (relLog V B y μ h) := by
  simp only [relLog, he]
  rw [show ((w * relAvg V B y μ h * w⁻¹ : GLN) : Mat) = Ad w ((relAvg V B y μ h : GLN) : Mat) by
    simp only [Ad, Units.val_mul], LogM_conj, Ad_smul]

/-- **The covariance of the linear part**: `Q(𝐔^u)Ad_uA = Ad_{u(c₋)}Q(𝐔)A`, at a background with the conditions at
both ends of the bond and on its loops, for `u` with `‖Ad_{u}X‖ ≤ 2‖X‖` at `c₋` and `c₊`. -/
theorem Qlin_gauge {V : Config N n} {y : Site n} {μ : Fin 4} {h : ℕ} (u : Site n → GLN)
    (hg : GoodAt V y h) (hg' : GoodAt V (cPlus y μ h) h) (hl : LoopsGood V y μ h)
    (hu : ∀ X : Mat, ‖Ad (u y) X‖ ≤ 2 * ‖X‖) (hu' : ∀ X : Mat, ‖Ad (u (cPlus y μ h)) X‖ ≤ 2 * ‖X‖)
    (B : Fin 4 → Site n → Mat) :
    Qlin (V.gauge u) y μ h (AdF u B) = Ad (u y) (Qlin V y μ h B) := by
  set ui : Site n → GLN := fun z => (u z)⁻¹ with hui
  -- the identity near `0`
  have htend : Tendsto (AdFL ui) (𝓝 0) (𝓝 0) := by
    have := (AdFL ui).continuous.tendsto 0
    rwa [map_zero] at this
  have hev : (fun B => relLog (V.gauge u) B y μ h) =ᶠ[𝓝 0]
      (fun B => AdL (u y) (relLog V (AdFL ui B) y μ h)) := by
    have h1 := htend.eventually (eventually_goodAt hg)
    have h2 := htend.eventually (eventually_goodAt hg')
    filter_upwards [h1, h2] with B hB1 hB2
    have he := relAvg_gauge V u (AdF ui B) y μ h hu hu' hg.expsG_le hB1.expsG_le hg'.expsG_le hB2.expsG_le
    rw [AdF_inv] at he
    exact relLog_of_relAvg (u y) he
  -- the derivative of the right side
  have hd := relLog_differentiableAt hg hg' hl
  have hD : HasFDerivAt (fun B => AdL (u y) (relLog V (AdFL ui B) y μ h))
      ((AdL (u y)).comp ((fderiv ℂ (fun B => relLog V B y μ h) 0).comp (AdFL ui))) 0 := by
    have h1 : HasFDerivAt (fun B => relLog V B y μ h) (fderiv ℂ (fun B => relLog V B y μ h) 0) (AdFL ui 0) := by
      rw [map_zero]; exact hd.hasFDerivAt
    exact (AdL (u y)).hasFDerivAt.comp 0 (h1.comp 0 (AdFL ui).hasFDerivAt)
  have hfd : fderiv ℂ (fun B => relLog (V.gauge u) B y μ h) 0 =
      (AdL (u y)).comp ((fderiv ℂ (fun B => relLog V B y μ h) 0).comp (AdFL ui)) := by
    rw [hev.fderiv_eq]; exact hD.fderiv
  simp only [Qlin, ContinuousLinearMap.smul_apply, hfd, ContinuousLinearMap.comp_apply, AdFL_apply, AdL_apply,
    hui, AdF_inv', Ad_smul]

end RelativeAverage
end CoreLean

end
