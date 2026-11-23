/-
`prop:relative-average`(i) of BALABAN_CORE.tex (`615c66b253fe`), the analyticity: the transports, the site factors, the
averages, and `𝓜_𝐔(A)(c)` are analytic functions of the parameters, and `B ↦ (1/i)log𝓜_𝐔(B)(c)` is analytic at `0`
under the background conditions `GoodAt`, `LoopsGood`.

The chain is that of `RelativeAverageHolo.lean` and `RelativeAverageLinear.lean` with `AnalyticAt` in place of
`DifferentiableAt`: products, inverses (`analyticAt_inverse`), `exp` (`exp_analytic`), `LogM = log1p(· - 1)`
(`analyticOnNhd_LogM`), and the group mean `meanV` (`MeanTransports.meanV_analyticAt`, the analytic inverse function
theorem). Several complex variables enter only through these compositions; no theorem of Hartogs type is used.

* `inv_analyticAt`, `hol_analyticAt`, `moveC_analyticAt`, `expsG_analyticAt`, `trans_analyticAt`, `avgM_analyticAt`,
  `siteFactor_analyticAt`, `relAvg_analyticAt`, `trans_moveC_analyticAt`.
* `relLog_analyticAt`: the analyticity of `B ↦ (1/i)log𝓜_𝐔(B)(c)` at `0`.
-/
import CoreLean.RelativeAverageLinear
import CoreLean.GroupMeanAnalytic

open Matrix NormedSpace Filter Topology
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace CoreLean
namespace RelativeAverage

open LatticePaths LatticeKappa RegularAverages BlockPaths AverageHolo MeanTransports

variable {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "GLN" => (Matrix (Fin N) (Fin N) ℂ)ˣ

variable {n : ℕ} [NeZero n] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

omit [NeZero n] in
/-- The inverse of an analytic family of invertible matrices is analytic. -/
lemma inv_analyticAt {W : E → GLN} {p₀ : E} (hW : AnalyticAt ℂ (fun p => ((W p : GLN) : Mat)) p₀) :
    AnalyticAt ℂ (fun p => (((W p)⁻¹ : GLN) : Mat)) p₀ := by
  have e : (fun p => (((W p)⁻¹ : GLN) : Mat)) = fun p => Ring.inverse ((W p : GLN) : Mat) := by
    funext p; rw [Ring.inverse_unit]
  rw [e]
  exact (analyticAt_inverse (𝕜 := ℂ) (W p₀)).comp_of_eq hW rfl

/-- The holonomies of an analytic family of configurations are analytic. -/
theorem hol_analyticAt (V : E → Config N n) {p₀ : E}
    (hV : ∀ μ z, AnalyticAt ℂ (fun p => ((V p μ z : GLN) : Mat)) p₀) :
    ∀ γ : List (Bond n), AnalyticAt ℂ (fun p => (((V p).hol γ : GLN) : Mat)) p₀
  | [] => by simp only [Config.hol, List.map_nil, List.prod_nil, Units.val_one]; exact analyticAt_const
  | t :: γ => by
    have hrest := hol_analyticAt V hV γ
    have hval : AnalyticAt ℂ (fun p => (((V p).val t : GLN) : Mat)) p₀ := by
      obtain ⟨z, ρ, s⟩ := t
      cases s
      · simp only [Config.val, Bool.false_eq_true, ↓reduceIte]
        exact inv_analyticAt (hV _ _)
      · simp only [Config.val, ↓reduceIte]
        exact hV _ _
    have e : (fun p => (((V p).hol (t :: γ) : GLN) : Mat)) =
        fun p => (((V p).val t : GLN) : Mat) * (((V p).hol γ : GLN) : Mat) := by
      funext p; rw [hol_cons, Units.val_mul]
    rw [e]
    exact hval.fun_mul hrest

/-- The family `B ↦ e^{iB}V` has analytic values. -/
lemma moveC_analyticAt (V : Config N n) (B₀ : Fin 4 → Site n → Mat) (μ : Fin 4) (z : Site n) :
    AnalyticAt ℂ (fun B : Fin 4 → Site n → Mat => (((moveC V B) μ z : GLN) : Mat)) B₀ := by
  have h1 : AnalyticAt ℂ (fun B : Fin 4 → Site n → Mat => B μ z) B₀ :=
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Site n => Mat) z).comp
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 4 => Site n → Mat) μ)).analyticAt B₀
  simp only [moveC, Units.val_mul, expU_val]
  exact ((exp_analytic _).comp_of_eq (h1.fun_const_smul (c := Complex.I)) rfl).fun_mul analyticAt_const

lemma moveC_hVa (V : Config N n) (B₀ : Fin 4 → Site n → Mat) :
    ∀ μ z, AnalyticAt ℂ (fun B : Fin 4 → Site n → Mat => (((moveC V B) μ z : GLN) : Mat)) B₀ :=
  fun μ z => moveC_analyticAt V B₀ μ z

/-- The exponents of the transports are analytic where the quotients lie in the domain of `Log`. -/
theorem expsG_analyticAt (V : E → Config N n) {p₀ : E}
    (hV : ∀ μ z, AnalyticAt ℂ (fun p => ((V p μ z : GLN) : Mat)) p₀) (y : Site n) (h : ℕ) (x : Pts h)
    (hlog : ∀ i, ‖((holG (V p₀) y h x (enumG h x i) * (holG (V p₀) y h x (firstG h x))⁻¹ : GLN) : Mat) - 1‖ < 1) :
    AnalyticAt ℂ (fun p => expsG (V p) y h x) p₀ := by
  refine analyticAt_pi_iff.2 fun i => ?_
  have hq : AnalyticAt ℂ
      (fun p => ((holG (V p) y h x (enumG h x i) * (holG (V p) y h x (firstG h x))⁻¹ : GLN) : Mat)) p₀ := by
    simp only [Units.val_mul]
    exact (hol_analyticAt V hV _).fun_mul (inv_analyticAt (hol_analyticAt V hV _))
  have hL := analyticOnNhd_LogM (N := N) _ (hlog i)
  exact (hL.comp_of_eq hq rfl).fun_const_smul (c := (1 / Complex.I : ℂ))

/-- **The transports are analytic** where the quotients lie in the domain of `Log` and the exponents in the ball of
`lem:group-mean`. -/
theorem trans_analyticAt (V : E → Config N n) {p₀ : E}
    (hV : ∀ μ z, AnalyticAt ℂ (fun p => ((V p μ z : GLN) : Mat)) p₀) (y : Site n) (h : ℕ) (x : Pts h)
    (hlog : ∀ i, ‖((holG (V p₀) y h x (enumG h x i) * (holG (V p₀) y h x (firstG h x))⁻¹ : GLN) : Mat) - 1‖ < 1)
    (hexp : ‖expsG (V p₀) y h x‖ < 1 / 512) :
    AnalyticAt ℂ (fun p => ((trans (V p) y h x : GLN) : Mat)) p₀ := by
  simp only [trans, mean, Units.val_mul, expU_val]
  have hm : AnalyticAt ℂ (fun p => meanV (expsG (V p) y h x)) p₀ :=
    (MeanTransports.meanV_analyticAt (N := N) (n := nG h x) (card_ords_pos _) hexp).comp_of_eq
      (expsG_analyticAt V hV y h x hlog) rfl
  exact ((exp_analytic _).comp_of_eq (hm.fun_const_smul (c := Complex.I)) rfl).fun_mul (hol_analyticAt V hV _)

/-- **The average `M(𝐔)(c)` is analytic** where the holonomies of the loops of `c` lie in the domain of `Log`. -/
theorem avgM_analyticAt (V : E → Config N n) {p₀ : E}
    (hV : ∀ μ z, AnalyticAt ℂ (fun p => ((V p μ z : GLN) : Mat)) p₀) (y : Site n) (μ : Fin 4) (h : ℕ)
    (hloop : ∀ x Γ Γ', ‖(((V p₀).hol (lpath (ι := Pts h) (P := fun x => Ords (offP h x)) y μ (2 * h + 1)
      (offP h) (ordG h) x Γ Γ') : GLN) : Mat) - 1‖ < 1) :
    AnalyticAt ℂ (fun p => ((avgM (V p) y μ h : GLN) : Mat)) p₀ := by
  unfold avgM avgLogU
  simp only [Units.val_mul, expU_val]
  have hβ : AnalyticAt ℂ (fun p => betaLog (ι := Pts h) (P := fun x => Ords (offP h x)) (V p) y μ
      (2 * h + 1) (offP h) (ordG h)) p₀ := by
    unfold betaLog
    refine Finset.analyticAt_fun_sum _ fun x _ => Finset.analyticAt_fun_sum _ fun Γ _ =>
      Finset.analyticAt_fun_sum _ fun Γ' _ => ?_
    have hL := analyticOnNhd_LogM (N := N) _ (hloop x Γ Γ')
    have hh := hol_analyticAt V hV
      (lpath (ι := Pts h) (P := fun x => Ords (offP h x)) y μ (2 * h + 1) (offP h) (ordG h) x Γ Γ')
    exact ((hL.comp_of_eq hh rfl).fun_const_smul (c := (1 / Complex.I : ℂ))).fun_const_smul
  exact ((exp_analytic _).comp_of_eq (hβ.fun_const_smul (c := Complex.I)) rfl).fun_mul
    (hol_analyticAt V hV (segZ μ y ((2 * h + 1 : ℕ) : ℤ)))

/-- **The site factor is analytic** where the transports of both configurations are and the quotients lie in the
domain of `Log`. -/
theorem siteFactor_analyticAt (V : E → Config N n) (B : E → Fin 4 → Site n → Mat) {p₀ : E}
    (y : Site n) (h : ℕ)
    (htA : ∀ x, AnalyticAt ℂ (fun p => ((trans (moveC (V p) (B p)) y h x : GLN) : Mat)) p₀)
    (ht : ∀ x, AnalyticAt ℂ (fun p => ((trans (V p) y h x : GLN) : Mat)) p₀)
    (hq : ∀ x, ‖((trans (moveC (V p₀) (B p₀)) y h x * (trans (V p₀) y h x)⁻¹ : GLN) : Mat) - 1‖ < 1) :
    AnalyticAt ℂ (fun p => ((siteFactor (V p) (B p) y h : GLN) : Mat)) p₀ := by
  simp only [siteFactor, expU_val]
  have hs : AnalyticAt ℂ (fun p => ∑ x : Pts h,
      LogM ((trans (moveC (V p) (B p)) y h x * (trans (V p) y h x)⁻¹ : GLN) : Mat)) p₀ := by
    refine Finset.analyticAt_fun_sum _ fun x _ => ?_
    have hL := analyticOnNhd_LogM (N := N) _ (hq x)
    have hm : AnalyticAt ℂ
        (fun p => ((trans (moveC (V p) (B p)) y h x * (trans (V p) y h x)⁻¹ : GLN) : Mat)) p₀ := by
      simp only [Units.val_mul]
      exact (htA x).fun_mul (inv_analyticAt (ht x))
    exact hL.comp_of_eq hm rfl
  exact (exp_analytic _).comp_of_eq hs.fun_const_smul rfl

omit [NeZero n] in
/-- **`𝓜_𝐔(A)(c)` is analytic** where its four factors are. -/
theorem relAvg_analyticAt (V : E → Config N n) (B : E → Fin 4 → Site n → Mat) {p₀ : E}
    (y : Site n) (μ : Fin 4) (h : ℕ)
    (hv : AnalyticAt ℂ (fun p => ((siteFactor (V p) (B p) y h : GLN) : Mat)) p₀)
    (hv' : AnalyticAt ℂ (fun p => ((siteFactor (V p) (B p) (cPlus y μ h) h : GLN) : Mat)) p₀)
    (hMA : AnalyticAt ℂ (fun p => ((avgM (moveC (V p) (B p)) y μ h : GLN) : Mat)) p₀)
    (hM : AnalyticAt ℂ (fun p => ((avgM (V p) y μ h : GLN) : Mat)) p₀) :
    AnalyticAt ℂ (fun p => ((relAvg (V p) (B p) y μ h : GLN) : Mat)) p₀ := by
  simp only [relAvg, Units.val_mul]
  exact (((inv_analyticAt hv).fun_mul hMA).fun_mul hv').fun_mul (inv_analyticAt hM)

/-- The transports of `𝐔_A` are analytic in `A` where the conditions hold. -/
lemma trans_moveC_analyticAt {V : Config N n} {y : Site n} {h : ℕ} {B₀ : Fin 4 → Site n → Mat}
    (hg : GoodAt (moveC V B₀) y h) (x : Pts h) :
    AnalyticAt ℂ (fun B => ((trans (moveC V B) y h x : GLN) : Mat)) B₀ :=
  trans_analyticAt (fun B => moveC V B) (moveC_hVa V B₀) y h x (hg.1 x) ((hg.2 x).trans (by norm_num))

/-- **`prop:relative-average`(i): `B ↦ (1/i)log𝓜_𝐔(B)(c)` is analytic at `0`**, at a background which satisfies the
conditions at both ends of the bond and on its loops. -/
theorem relLog_analyticAt {V : Config N n} {y : Site n} {μ : Fin 4} {h : ℕ} (hg : GoodAt V y h)
    (hg' : GoodAt V (cPlus y μ h) h) (hl : LoopsGood V y μ h) :
    AnalyticAt ℂ (fun B => relLog V B y μ h) 0 := by
  have hv : ∀ y', GoodAt V y' h → AnalyticAt ℂ (fun B => ((siteFactor V B y' h : GLN) : Mat)) 0 := fun y' hy' => by
    refine siteFactor_analyticAt (fun _ => V) (fun B => B) y' h (fun x => ?_)
      (fun x => analyticAt_const) (fun x => by simp [moveC_zero])
    exact trans_moveC_analyticAt (B₀ := 0) (by rw [moveC_zero]; exact hy') x
  have hMA : AnalyticAt ℂ (fun B => ((avgM (moveC V B) y μ h : GLN) : Mat)) 0 :=
    avgM_analyticAt (fun B => moveC V B) (moveC_hVa V 0) y μ h (by rw [moveC_zero]; exact hl)
  have hR := relAvg_analyticAt (fun _ => V) (fun B => B) y μ h (hv y hg) (hv _ hg') hMA analyticAt_const
  have hdom : ‖((relAvg V 0 y μ h : GLN) : Mat) - 1‖ < 1 := by simp [relAvg_zero]
  have hL := analyticOnNhd_LogM (N := N) _ hdom
  exact (hL.comp_of_eq hR rfl).fun_const_smul (c := (1 / Complex.I : ℂ))

end RelativeAverage
end CoreLean

end
