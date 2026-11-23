/-
`prop:relative-average`(i) of BALABAN_CORE.tex (`d8bdc4ac1777`), first part: the holomorphy of the transports.

The configurations are a family `p ↦ V p` over a normed space `E` over `ℂ` whose values on the positive bonds are
holomorphic in `p` (for `𝐔 = e^{iaA'}U` and `𝐔_A = e^{iaA}𝐔` the parameter is `p = (A', A)`).

* `hol_differentiableAt`: the holonomies `V(p)(γ)` are holomorphic (the values on the negative bonds are inverses,
  holomorphic at invertible matrices).
* `expsG_differentiableAt`, `trans_differentiableAt`: where the quotients `𝐔(Γᵢ)𝐔(Γ₀)⁻¹` lie in the domain
  `‖W - 1‖ < 1` of `Log` and the exponents `Yᵢ` in the ball `‖Y‖ < 1/512` of `lem:group-mean` (`meanV`), the transport
  `𝐔(y, x) = e^{iV(Y)}𝐔(Γ₀)` is holomorphic (`lem:group-mean`: `meanV_differentiableAt`).
* `moveC2_differentiableAt`: the family `(A', B) ↦ e^{iB}e^{iA'}U` has holomorphic values.
-/
import CoreLean.RelativeAverageDefs

open Matrix NormedSpace
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace CoreLean
namespace RelativeAverage

open LatticePaths LatticeKappa RegularAverages BlockPaths AverageHolo MeanTransports

variable {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "GLN" => (Matrix (Fin N) (Fin N) ℂ)ˣ

variable {n : ℕ} [NeZero n] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The inverse of a holomorphic family of invertible matrices is holomorphic. -/
lemma inv_differentiableAt {W : E → GLN} {p₀ : E} (hW : DifferentiableAt ℂ (fun p => ((W p : GLN) : Mat)) p₀) :
    DifferentiableAt ℂ (fun p => (((W p)⁻¹ : GLN) : Mat)) p₀ := by
  have e : (fun p => (((W p)⁻¹ : GLN) : Mat)) = fun p => Ring.inverse ((W p : GLN) : Mat) := by
    funext p; rw [Ring.inverse_unit]
  rw [e]
  exact hW.inverse (W p₀).isUnit

/-- The holonomies of a holomorphic family of configurations are holomorphic. -/
theorem hol_differentiableAt (V : E → Config N n) {p₀ : E}
    (hV : ∀ μ z, DifferentiableAt ℂ (fun p => ((V p μ z : GLN) : Mat)) p₀) :
    ∀ γ : List (Bond n), DifferentiableAt ℂ (fun p => (((V p).hol γ : GLN) : Mat)) p₀
  | [] => by simp only [Config.hol, List.map_nil, List.prod_nil, Units.val_one]; exact differentiableAt_const _
  | t :: γ => by
    have hrest := hol_differentiableAt V hV γ
    have hval : DifferentiableAt ℂ (fun p => (((V p).val t : GLN) : Mat)) p₀ := by
      obtain ⟨z, ρ, s⟩ := t
      cases s
      · simp only [Config.val, Bool.false_eq_true, ↓reduceIte]
        exact inv_differentiableAt (hV _ _)
      · simp only [Config.val, ↓reduceIte]
        exact hV _ _
    have e : (fun p => (((V p).hol (t :: γ) : GLN) : Mat)) =
        fun p => (((V p).val t : GLN) : Mat) * (((V p).hol γ : GLN) : Mat) := by
      funext p; rw [hol_cons, Units.val_mul]
    rw [e]
    exact hval.mul hrest

/-- The family `(A', B) ↦ e^{iB}e^{iA'}U` has holomorphic values. -/
lemma moveC2_differentiableAt (U : Config N n) (p₀ : (Fin 4 → Site n → Mat) × (Fin 4 → Site n → Mat))
    (μ : Fin 4) (z : Site n) :
    DifferentiableAt ℂ (fun p : (Fin 4 → Site n → Mat) × (Fin 4 → Site n → Mat) =>
      (((moveC (moveC U p.1) p.2) μ z : GLN) : Mat)) p₀ := by
  have hev : ∀ (q : (Fin 4 → Site n → Mat) × (Fin 4 → Site n → Mat) → Fin 4 → Site n → Mat),
      DifferentiableAt ℂ q p₀ →
      DifferentiableAt ℂ (fun p => exp (Complex.I • q p μ z)) p₀ := fun q hq => by
    have h1 : DifferentiableAt ℂ (fun p => q p μ z) p₀ := by
      have hμ : DifferentiableAt ℂ (fun F : Fin 4 → Site n → Mat => F μ z) (q p₀) :=
        ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Site n => Mat) z).comp
          (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 4 => Site n → Mat) μ)).differentiableAt
      exact hμ.comp p₀ hq
    exact (exp_analytic _).differentiableAt.comp p₀ (h1.const_smul Complex.I)
  simp only [moveC, Units.val_mul, expU_val]
  exact (hev _ differentiableAt_snd).mul ((hev _ differentiableAt_fst).mul (differentiableAt_const _))

/-- The family `B ↦ e^{iB}V` has holomorphic values. -/
lemma moveC_differentiableAt (V : Config N n) (B₀ : Fin 4 → Site n → Mat) (μ : Fin 4) (z : Site n) :
    DifferentiableAt ℂ (fun B : Fin 4 → Site n → Mat => (((moveC V B) μ z : GLN) : Mat)) B₀ := by
  have h1 : DifferentiableAt ℂ (fun B : Fin 4 → Site n → Mat => B μ z) B₀ :=
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Site n => Mat) z).comp
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 4 => Site n → Mat) μ)).differentiableAt
  simp only [moveC, Units.val_mul, expU_val]
  exact ((exp_analytic _).differentiableAt.comp B₀ (h1.const_smul Complex.I)).mul (differentiableAt_const _)

/-- The exponents of the transports are holomorphic where the quotients lie in the domain of `Log`. -/
theorem expsG_differentiableAt (V : E → Config N n) {p₀ : E}
    (hV : ∀ μ z, DifferentiableAt ℂ (fun p => ((V p μ z : GLN) : Mat)) p₀) (y : Site n) (h : ℕ) (x : Pts h)
    (hlog : ∀ i, ‖((holG (V p₀) y h x (enumG h x i) * (holG (V p₀) y h x (firstG h x))⁻¹ : GLN) : Mat) - 1‖ < 1) :
    DifferentiableAt ℂ (fun p => expsG (V p) y h x) p₀ := by
  refine differentiableAt_pi.2 fun i => ?_
  have hq : DifferentiableAt ℂ
      (fun p => ((holG (V p) y h x (enumG h x i) * (holG (V p) y h x (firstG h x))⁻¹ : GLN) : Mat)) p₀ := by
    simp only [Units.val_mul]
    exact (hol_differentiableAt V hV _).mul (inv_differentiableAt (hol_differentiableAt V hV _))
  have hL := (analyticOnNhd_LogM (N := N) _ (hlog i)).differentiableAt
  exact (hL.comp p₀ hq).const_smul (1 / Complex.I : ℂ)

/-- **`prop:relative-average`(i), the transports**: `𝐔(y, x)` is holomorphic where the quotients `𝐔(Γᵢ)𝐔(Γ₀)⁻¹`
lie in the domain of `Log` and the exponents in the ball of `lem:group-mean`. -/
theorem trans_differentiableAt (V : E → Config N n) {p₀ : E}
    (hV : ∀ μ z, DifferentiableAt ℂ (fun p => ((V p μ z : GLN) : Mat)) p₀) (y : Site n) (h : ℕ) (x : Pts h)
    (hlog : ∀ i, ‖((holG (V p₀) y h x (enumG h x i) * (holG (V p₀) y h x (firstG h x))⁻¹ : GLN) : Mat) - 1‖ < 1)
    (hexp : ‖expsG (V p₀) y h x‖ < 1 / 512) :
    DifferentiableAt ℂ (fun p => ((trans (V p) y h x : GLN) : Mat)) p₀ := by
  simp only [trans, mean, Units.val_mul, expU_val]
  have hm : DifferentiableAt ℂ (fun p => meanV (expsG (V p) y h x)) p₀ :=
    DifferentiableAt.comp (g := meanV (N := N) (n := nG h x)) p₀
      (MeanTransports.meanV_differentiableAt (N := N) (n := nG h x) (card_ords_pos _) hexp)
      (expsG_differentiableAt V hV y h x hlog)
  exact ((exp_analytic _).differentiableAt.comp p₀ (hm.const_smul Complex.I)).mul
    (hol_differentiableAt V hV _)

/-! ### The average, the site factors, and the relative average -/

/-- The average `M(𝐔)(c)` is holomorphic where the holonomies of all loops of `c` lie in the domain of `Log`. -/
theorem avgM_differentiableAt (V : E → Config N n) {p₀ : E}
    (hV : ∀ μ z, DifferentiableAt ℂ (fun p => ((V p μ z : GLN) : Mat)) p₀) (y : Site n) (μ : Fin 4) (h : ℕ)
    (hloop : ∀ x Γ Γ', ‖(((V p₀).hol (lpath (ι := Pts h) (P := fun x => Ords (offP h x)) y μ (2 * h + 1)
      (offP h) (ordG h) x Γ Γ') : GLN) : Mat) - 1‖ < 1) :
    DifferentiableAt ℂ (fun p => ((avgM (V p) y μ h : GLN) : Mat)) p₀ := by
  unfold avgM avgLogU
  simp only [Units.val_mul, expU_val]
  have hβ : DifferentiableAt ℂ (fun p => betaLog (ι := Pts h) (P := fun x => Ords (offP h x)) (V p) y μ
      (2 * h + 1) (offP h) (ordG h)) p₀ := by
    unfold betaLog
    refine DifferentiableAt.fun_sum fun x _ => DifferentiableAt.fun_sum fun Γ _ =>
      DifferentiableAt.fun_sum fun Γ' _ => ?_
    set W0 : Mat := (((V p₀).hol (lpath (ι := Pts h) (P := fun x => Ords (offP h x)) y μ (2 * h + 1)
      (offP h) (ordG h) x Γ Γ') : GLN) : Mat) with hW0
    have hL : DifferentiableAt ℂ (LogM (N := N)) W0 :=
      (analyticOnNhd_LogM (N := N) W0 (hloop x Γ Γ')).differentiableAt
    have hh := hol_differentiableAt V hV
      (lpath (ι := Pts h) (P := fun x => Ords (offP h x)) y μ (2 * h + 1) (offP h) (ordG h) x Γ Γ')
    have key : DifferentiableAt ℂ (fun p => LogM ((((V p).hol (lpath (ι := Pts h)
        (P := fun x => Ords (offP h x)) y μ (2 * h + 1) (offP h) (ordG h) x Γ Γ')) : GLN) : Mat)) p₀ :=
      DifferentiableAt.comp (f := fun p => (((V p).hol (lpath (ι := Pts h)
        (P := fun x => Ords (offP h x)) y μ (2 * h + 1) (offP h) (ordG h) x Γ Γ') : GLN) : Mat)) p₀ hL hh
    exact (key.fun_const_smul (1 / Complex.I : ℂ)).fun_const_smul _
  exact ((exp_analytic _).differentiableAt.comp p₀ (hβ.fun_const_smul Complex.I)).mul
    (hol_differentiableAt V hV (segZ μ y ((2 * h + 1 : ℕ) : ℤ)))

/-- The site factor `v_𝐔(A)(y)` is holomorphic in `(𝐔, 𝐔_A)` where the transports of both are holomorphic and the
quotients `𝐔_A(y, x)𝐔(y, x)⁻¹` lie in the domain of `Log`. -/
theorem siteFactor_differentiableAt (V : E → Config N n) (B : E → Fin 4 → Site n → Mat) {p₀ : E}
    (y : Site n) (h : ℕ)
    (htA : ∀ x, DifferentiableAt ℂ (fun p => ((trans (moveC (V p) (B p)) y h x : GLN) : Mat)) p₀)
    (ht : ∀ x, DifferentiableAt ℂ (fun p => ((trans (V p) y h x : GLN) : Mat)) p₀)
    (hq : ∀ x, ‖((trans (moveC (V p₀) (B p₀)) y h x * (trans (V p₀) y h x)⁻¹ : GLN) : Mat) - 1‖ < 1) :
    DifferentiableAt ℂ (fun p => ((siteFactor (V p) (B p) y h : GLN) : Mat)) p₀ := by
  simp only [siteFactor, expU_val]
  have hs : DifferentiableAt ℂ (fun p => ∑ x : Pts h,
      LogM ((trans (moveC (V p) (B p)) y h x * (trans (V p) y h x)⁻¹ : GLN) : Mat)) p₀ := by
    refine DifferentiableAt.fun_sum fun x _ => ?_
    have hL := (analyticOnNhd_LogM (N := N) _ (hq x)).differentiableAt
    have hm : DifferentiableAt ℂ
        (fun p => ((trans (moveC (V p) (B p)) y h x * (trans (V p) y h x)⁻¹ : GLN) : Mat)) p₀ := by
      simp only [Units.val_mul]
      exact (htA x).mul (inv_differentiableAt (ht x))
    exact DifferentiableAt.comp (g := LogM (N := N)) p₀ hL hm
  exact (exp_analytic _).differentiableAt.comp p₀ (hs.fun_const_smul _)

omit [NeZero n] in
/-- **`prop:relative-average`(i), the relative average**: `𝓜_𝐔(A)(c)` is holomorphic where its four factors are. -/
theorem relAvg_differentiableAt (V : E → Config N n) (B : E → Fin 4 → Site n → Mat) {p₀ : E}
    (y : Site n) (μ : Fin 4) (h : ℕ)
    (hv : DifferentiableAt ℂ (fun p => ((siteFactor (V p) (B p) y h : GLN) : Mat)) p₀)
    (hv' : DifferentiableAt ℂ (fun p => ((siteFactor (V p) (B p) (cPlus y μ h) h : GLN) : Mat)) p₀)
    (hMA : DifferentiableAt ℂ (fun p => ((avgM (moveC (V p) (B p)) y μ h : GLN) : Mat)) p₀)
    (hM : DifferentiableAt ℂ (fun p => ((avgM (V p) y μ h : GLN) : Mat)) p₀) :
    DifferentiableAt ℂ (fun p => ((relAvg (V p) (B p) y μ h : GLN) : Mat)) p₀ := by
  simp only [relAvg, Units.val_mul]
  exact (((inv_differentiableAt hv).mul hMA).mul hv').mul (inv_differentiableAt hM)

end RelativeAverage
end CoreLean

end
