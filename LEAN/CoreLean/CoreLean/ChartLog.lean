/-
`lem:chart`(iv) of BALABAN_CORE.tex (`b1ff7d2601a1`): the matrix logarithm
`Log W = Σ_{n ≥ 1} (-1)^{n+1} n⁻¹ (W - 1)ⁿ` (`LogM`, `def:chart`).

* `analyticOnNhd_LogM`: `Log` is holomorphic on `{‖W - 1‖ < 1}`.
* `exp_LogM`: `e^{Log W} = W` there (`exp_log1p` of the library `BakerCampbellHausdorff`).
* `LogM_conj`: `Log(uWu⁻¹) = Ad_u Log W` for every invertible `u` (`LogM_Ad` of `Psi.lean`; the core
  states it under `‖uWu⁻¹ - 1‖ < 1`, which is not needed for the series identity).
* `LogM_exp`: `Log e^Z = Z` for `‖Z‖ < log 2`. The library gives it for `‖Z‖ < 1/4`
  (`log1p_exp_sub_one`); both sides are holomorphic on the ball of radius `log 2`, where
  `‖e^Z - 1‖ ≤ e^{‖Z‖} - 1 < 1`, and the identity theorem on the connected ball extends it. (The core
  argues with the substituted double series.)
* `LogM_exp_I_mem`: `Log W ∈ i𝔤^c` for `W = e^{iX}`, `X ∈ 𝔤^c`, `‖X‖ < log 2`.
-/
import CoreLean.Psi
import BakerCampbellHausdorff.LogExp
import BakerCampbellHausdorff.AnalyticLog

open NormedSpace Filter BakerCampbellHausdorff
open scoped Matrix.Norms.L2Operator Topology

noncomputable section

namespace CoreLean

variable {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "GLN" => (Matrix (Fin N) (Fin N) ℂ)ˣ

/-- `lem:chart`(iv): `Log` is holomorphic on `{‖W - 1‖ < 1}`. -/
theorem analyticOnNhd_LogM : AnalyticOnNhd ℂ (LogM (N := N)) {W | ‖W - 1‖ < 1} :=
  fun W hW => (analyticAt_id).log1p_sub_one' ℂ hW

/-- `lem:chart`(iv): `e^{Log W} = W` for `‖W - 1‖ < 1`. -/
theorem exp_LogM {W : Mat} (hW : ‖W - 1‖ < 1) : exp (LogM W) = W := by
  rw [LogM, exp_log1p ℂ hW, add_sub_cancel]

/-- `lem:chart`(iv): `Log(uWu⁻¹) = Ad_u Log W` for every invertible `u`. -/
theorem LogM_conj (u : GLN) (W : Mat) : LogM (Ad u W) = Ad u (LogM W) := LogM_Ad u W

lemma norm_exp_sub_one_lt_one {Z : Mat} (hZ : ‖Z‖ < Real.log 2) : ‖exp Z - 1‖ < 1 := by
  have h := norm_exp_sub_one_le ℂ Z
  have : Real.exp ‖Z‖ < 2 := by
    calc Real.exp ‖Z‖ < Real.exp (Real.log 2) := Real.exp_lt_exp.mpr hZ
      _ = 2 := Real.exp_log (by norm_num)
  linarith

/-- `lem:chart`(iv): `Log e^Z = Z` for `‖Z‖ < log 2`. -/
theorem LogM_exp {Z : Mat} (hZ : ‖Z‖ < Real.log 2) : LogM (exp Z) = Z := by
  set U : Set Mat := Metric.ball 0 (Real.log 2)
  have hF : AnalyticOnNhd ℂ (fun Y : Mat => log1p ℂ (exp Y - 1)) U :=
    AnalyticOnNhd.log1p_sub_one ℂ (fun Y _ => NormedSpace.exp_analytic (𝕂 := ℂ) Y)
      (fun Y hY => norm_exp_sub_one_lt_one (mem_ball_zero_iff.mp hY))
  have hid : AnalyticOnNhd ℂ (fun Y : Mat => Y) U := fun _ _ => analyticAt_id
  have hU : IsPreconnected U := (convex_ball _ _).isPreconnected
  have h0 : (0 : Mat) ∈ U := Metric.mem_ball_self (Real.log_pos (by norm_num))
  have hev : (fun Y : Mat => log1p ℂ (exp Y - 1)) =ᶠ[𝓝 0] fun Y => Y := by
    filter_upwards [Metric.ball_mem_nhds (0 : Mat) (by norm_num : (0 : ℝ) < 1 / 4)] with Y hY
    exact log1p_exp_sub_one ℂ (mem_ball_zero_iff.mp hY)
  exact hF.eqOn_of_preconnected_of_eventuallyEq hid hU h0 hev (mem_ball_zero_iff.mpr hZ)

/-- `lem:chart`(iv): `Log W ∈ i𝔤^c` if `W = e^{iX}` with `X ∈ 𝔤^c`, `‖X‖ < log 2`; indeed
`Log W = iX`. -/
theorem LogM_exp_I_mem {G : GaugeGroup N} {X : Mat} (hX : X ∈ G.lieC) (h : ‖X‖ < Real.log 2) :
    LogM (exp (Complex.I • X)) = Complex.I • X ∧ ∃ Y ∈ G.lieC, LogM (exp (Complex.I • X)) = Complex.I • Y :=
  have e : LogM (exp (Complex.I • X)) = Complex.I • X := LogM_exp (by rwa [norm_I_smul'])
  ⟨e, X, hX, e⟩

end CoreLean

end
