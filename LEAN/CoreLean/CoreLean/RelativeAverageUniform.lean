/-
`prop:relative-average`(vi) of BALABAN_CORE.tex (`d8bdc4ac1777`) for the configurations `𝐔_X = e^{iX}`, with constants
which depend on `L` and `N` only (by (viii)): the numbers of `RelativeAverageBounds.lean` on the reference torus of
size `4h + 2` serve every torus and every bond, because `(1/i) Log 𝓜_{𝐔_X}(B)(c)` is the reference function of the
box data (`relAvg_reference`), and the box data `T B` of a form `B` have `‖T B‖ ≤ ‖B‖`.

* `remainder_uniform`: `‖C(𝐔_X; B)‖ ≤ C₂‖B‖²` for `‖X‖ ≤ r`, `‖B‖ < r`;
* `linear_uniform`: `‖L·Q(𝐔_X)B‖ ≤ C₁‖B‖` for `‖X‖ ≤ r`.
-/
import CoreLean.RelativeAverageBounds

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

/-- The box data of a form, as a continuous linear map to the forms of the reference torus. -/
def refFormL (h : ℕ) (y : Site n) :
    (Fin 4 → Site n → Mat) →L[ℂ] (Fin 4 → Site (4 * h + 2) → Mat) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun B => refForm h B y
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

@[simp] lemma refFormL_apply (h : ℕ) (y : Site n) (B : Fin 4 → Site n → Mat) : refFormL h y B = refForm h B y := rfl

lemma norm_refForm_le (h : ℕ) (y : Site n) (B : Fin 4 → Site n → Mat) : ‖refForm h B y‖ ≤ ‖B‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun ν => (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun z => ?_
  exact (norm_le_pi_norm (B ν) _).trans (norm_le_pi_norm B ν)

lemma refConfig_UX (h : ℕ) (X : Fin 4 → Site n → Mat) (y : Site n) :
    refConfig h (UX (N := N) X) y = UX (refForm h X y) := by
  funext ν z; simp [refConfig, refForm, UX, moveC, oneC]

/-- `(1/i) Log 𝓜_{𝐔_X}(B)(c)` is the reference function of the box data. -/
lemma relLog_reference (h : ℕ) (X B : Fin 4 → Site n → Mat) (y : Site n) (μ : Fin 4) :
    relLog (UX (N := N) X) B y μ h = relLog (UX (refForm h X y)) (refForm h B y) 0 μ h := by
  simp only [relLog, relAvg_reference h (UX X) B y μ, refConfig_UX]

/-- **(vi), uniformly**: constants on the reference torus bound the remainder and the linear part on every torus. -/
theorem uniform_vi (h : ℕ) (μ : Fin 4) :
    ∃ r C₁ C₂ : ℝ, 0 < r ∧ 0 ≤ C₁ ∧ 0 ≤ C₂ ∧ ∀ {n : ℕ} [NeZero n] (y : Site n) (X B : Fin 4 → Site n → Mat),
      ‖X‖ ≤ r →
        ‖((2 * h + 1 : ℕ) : ℂ) • Qlin (UX (N := N) X) y μ h B‖ ≤ C₁ * ‖B‖ ∧
        (‖B‖ < r → ‖Crem (UX (N := N) X) B y μ h‖ ≤ C₂ * ‖B‖ ^ 2) := by
  obtain ⟨r, K, hr, hK0, hc, hK⟩ := bounds_UX (N := N) (n := 4 * h + 2) 0 μ h
  refine ⟨r, K / r, 2 * K / r ^ 2, hr, by positivity, by positivity, fun {n} _ y X B hX => ?_⟩
  set T := refFormL (N := N) h y
  have hX0 : ‖refForm h X y‖ ≤ r := (norm_refForm_le h y X).trans hX
  -- the derivatives through the box data
  have hd : DifferentiableAt ℂ (fun B' => relLog (UX (N := N) (refForm h X y)) B' 0 μ h) (T 0) := by
    rw [map_zero]
    exact (relLog_UX_differentiableOn hc hX0).differentiableAt (ball_mem_nhds 0 hr)
  have hfd : fderiv ℂ (fun B' => relLog (UX (N := N) X) B' y μ h) 0 =
      (fderiv ℂ (fun B' => relLog (UX (N := N) (refForm h X y)) B' 0 μ h) 0).comp T := by
    have e : (fun B' => relLog (UX (N := N) X) B' y μ h) =
        (fun B' => relLog (UX (N := N) (refForm h X y)) B' 0 μ h) ∘ T := by
      funext B'; simp only [Function.comp_apply]; rw [relLog_reference]; rfl
    rw [e, fderiv_comp 0 hd T.differentiableAt, T.fderiv, map_zero]
  have hL : (((2 * h + 1 : ℕ) : ℂ)) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hQ : ((2 * h + 1 : ℕ) : ℂ) • Qlin (UX (N := N) X) y μ h B =
      ((2 * h + 1 : ℕ) : ℂ) • Qlin (UX (N := N) (refForm h X y)) 0 μ h (T B) := by
    simp only [Qlin, ContinuousLinearMap.smul_apply, smul_smul, mul_inv_cancel₀ hL, one_smul, hfd,
      ContinuousLinearMap.comp_apply]
  have hC : Crem (UX (N := N) X) B y μ h = Crem (UX (N := N) (refForm h X y)) (T B) 0 μ h := by
    unfold Crem
    rw [hQ, relLog_reference]; rfl
  constructor
  · rw [hQ]
    calc _ ≤ K / r * ‖T B‖ := linear_bound_UX hr hc hK hX0 (T B)
      _ ≤ K / r * ‖B‖ := by gcongr; exact norm_refForm_le h y B
  · intro hB
    have hTB : ‖T B‖ < r := (norm_refForm_le h y B).trans_lt hB
    rw [hC]
    calc _ ≤ 2 * K / r ^ 2 * ‖T B‖ ^ 2 := remainder_bound_UX hr hc hK hX0 hTB
      _ ≤ 2 * K / r ^ 2 * ‖B‖ ^ 2 := by
          gcongr; exact norm_refForm_le h y B

end RelativeAverage
end CoreLean

end
