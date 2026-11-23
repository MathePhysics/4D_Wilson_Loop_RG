/-
`lem:current-plaquettes` of BALABAN_CORE.tex (`50787904c4ef`): the current of a gauge field by its plaquettes. If
`|U(∂p) - id| ≤ ε` for the plaquettes `p_{νμ}(x)` and `p_{νμ}(x - ae_ν)`, `ν ≠ μ`, then `‖J(U)(b)‖ ≤ 6√N ε|a|⁻³` for the
bond `b = (x, x + ae_μ)`.
-/
import CoreLean.CubicBound
import CoreLean.BlockHolonomies

open Matrix Complex
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace CoreLean

variable {N n : ℕ} [NeZero n] (a : ℂ)

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "GLN" => (Matrix (Fin N) (Fin N) ℂ)ˣ

variable {G : GaugeGroup N}

/-- `|Im W| ≤ |W - id|` for a unitary `W`, `Im W = (W - W⁻¹)/(2i)`. -/
lemma hs_imW_le {W : GLN} (hW : (W : Mat) ∈ unitaryGroup (Fin N) ℂ) : hs (imW W) ≤ hs ((W : Mat) - 1) := by
  have e : imW W = (1 / (2 * I) : ℂ) • (((W : Mat) - 1) - (((W⁻¹ : GLN) : Mat) - 1)) := by
    rw [imW]; congr 1; abel
  rw [e, RegularAverages.hs_smul]
  have h1 := RegularAverages.hs_sub_le' ((W : Mat) - 1) (((W⁻¹ : GLN) : Mat) - 1)
  rw [BlockHolonomies.hs_inv_sub_one hW] at h1
  have h2 : ‖(1 / (2 * I) : ℂ)‖ = 1 / 2 := by simp
  rw [h2]
  linarith [hs_nonneg ((W : Mat) - 1)]

/-- **`lem:current-plaquettes`**: for a gauge field `U` with `|U(∂p) - id| ≤ ε` for the plaquettes `p_{νμ}(x)` and
`p_{νμ}(x - ae_ν)`, `ν ≠ μ`, `‖J(U)_μ(x)‖ ≤ 6√N ε|a|⁻³`. Each `F(U)_{νμ}` there is at most `√N|a|⁻²ε` (`|π Im X| ≤ |Im X| ≤
|X - id|` for unitary `X`, `‖Y‖ ≤ √N|Y|`), the backward difference adds two of them transported by a unitary matrix, and
there are three `ν ≠ μ`. -/
theorem current_plaquettes [NeZero N] (hG : G.LieInput) {U : Config N n} (hU : U.IsGaugeField) (μ : Fin 4)
    (x : Site n) {ε : ℝ}
    (hP : ∀ ν, ν ≠ μ → ∀ y ∈ ({x, x - unit n ν} : Finset (Site n)),
      hs (((plaq U ν μ y : GLN) : Mat) - 1) ≤ ε) :
    ‖current a hG U μ x‖ ≤ 6 * Real.sqrt N * ε * ‖a‖⁻¹ ^ 3 := by
  have hc : ∀ ν, ν ≠ μ → ∀ y ∈ ({x, x - unit n ν} : Finset (Site n)),
      ‖curv a hG U ν μ y‖ ≤ ‖a‖⁻¹ ^ 2 * (Real.sqrt N * ε) := by
    intro ν hν y hy
    simp only [curv]
    rw [norm_smul, norm_inv, norm_pow, ← inv_pow]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine (opNorm_le_sqrt_mul_hs _).trans (mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _))
    exact (hs_proj_le hG _).trans ((hs_imW_le (LatticePaths.hol_isU hU _)).trans (hP ν hν y hy))
  have hterm : ∀ ν, ν ≠ μ → ‖Dbw a U ν (curv a hG U ν μ) x‖ ≤ 2 * Real.sqrt N * ε * ‖a‖⁻¹ ^ 3 := by
    intro ν hν
    have h1 := hc ν hν (x - unit n ν) (by simp)
    have h2 := hc ν hν x (by simp)
    have hAd : ‖Ad (U.val ⟨x, ν, false⟩) (curv a hG U ν μ (x - unit n ν))‖ =
        ‖curv a hG U ν μ (x - unit n ν)‖ :=
      SupportCont.opNorm_Ad_unitary (LatticePaths.val_isU hU _) _
    simp only [Dbw]
    rw [norm_smul, norm_inv]
    calc ‖a‖⁻¹ * ‖Ad (U.val ⟨x, ν, false⟩) (curv a hG U ν μ (x - unit n ν)) - curv a hG U ν μ x‖
        ≤ ‖a‖⁻¹ * (‖curv a hG U ν μ (x - unit n ν)‖ + ‖curv a hG U ν μ x‖) := by
          rw [← hAd]; exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by positivity)
      _ ≤ ‖a‖⁻¹ * (‖a‖⁻¹ ^ 2 * (Real.sqrt N * ε) + ‖a‖⁻¹ ^ 2 * (Real.sqrt N * ε)) := by gcongr
      _ = 2 * Real.sqrt N * ε * ‖a‖⁻¹ ^ 3 := by ring
  show ‖∑ ν, (if ν ≠ μ then Dbw a U ν (curv a hG U ν μ) x else 0)‖ ≤ _
  exact (norm_sum_ne_le hterm).trans (le_of_eq (by ring))

end CoreLean

end
