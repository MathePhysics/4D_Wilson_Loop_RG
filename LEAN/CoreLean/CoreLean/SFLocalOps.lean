/-
`lem:sf-local` of BALABAN_CORE.tex (`4252790331fd`), the steps "The covariant Laplacian" and "The rescaled equation".

* `norm_Kf_le`, `norm_Kb_le`: `‖K_μ(n)‖, ‖K'_μ(n)‖ ≤ 6‖Ã‖` (`eq:adjoint-lipschitz`, `hs_Ad_exp_sub_le`);
  `norm_Kf_sub_le`, `norm_Kb_sub_le`: `‖K_μ(n) - K_μ(n')‖ ≤ 8‖Ã_μ(n) - Ã_μ(n')‖` and likewise for `K'_μ`
  (`hs_Ad_exp_sub_Ad_exp_le`).
* `lip_box`: in a box, a function whose differences along the bonds are at most `B` changes by at most `B|n' - n|₁`
  (the sum along a path which changes the coordinates one after the other and stays in the box).
* `toLData`: the data of `eq:local-equation`, `h = f + Σ_μK'_μg_μ(· - e_μ) + 𝒩u`, `c = 𝒵 - 𝒞` (the coefficient at `e = 0`
  carries `-𝒞`), `𝒢'_μ = -𝒢_μ`; `eqn_of`: the equation `Δ_𝐔u = f + D^*_𝐔g + 𝒵u + 𝒩u` at a point gives
  `eq:local-equation` there.
-/
import CoreLean.SFLocalSetup
import CoreLean.RegularAverages

open Finset Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace CoreLean
namespace SFLocal

open LocalLaplacian InteriorSchauder

variable {N m : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "GLN" => (Matrix (Fin N) (Fin N) ℂ)ˣ

lemma liftV_sub_apply (φ ψ : Mat →ₗ[ℂ] Mat) (v : VS N m) : liftV φ v - liftV ψ v = liftV (φ - ψ) v := by
  ext p; simp [liftV_apply, vecOf, matOf]

lemma opnorm_liftV_sub_le (φ ψ : Mat →ₗ[ℂ] Mat) {c : ℝ} (hc : 0 ≤ c) (h : ∀ Z, hs (φ Z - ψ Z) ≤ c * hs Z) :
    ‖(liftV φ - liftV ψ : VS N m →L[ℝ] VS N m)‖ ≤ c := by
  refine ContinuousLinearMap.opNorm_le_bound _ hc fun v => ?_
  rw [ContinuousLinearMap.sub_apply, liftV_sub_apply]
  exact ((liftV (φ - ψ)).le_opNorm v).trans (mul_le_mul_of_nonneg_right
    (norm_liftV_le _ hc fun Z => by simpa using h Z) (norm_nonneg v))

lemma hs_KL (ε : ℝ) (hε : 0 < ε) (W : GLN) (Z : Mat) : hs (KL ε W Z) = ε⁻¹ * hs (Ad W Z - Z) := by
  simp only [KL, AdL, LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.id_apply]
  rw [RegularAverages.hs_smul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.2 hε.le)]

lemma hs_KL_sub (ε : ℝ) (hε : 0 < ε) (W W' : GLN) (Z : Mat) :
    hs (KL ε W Z - KL ε W' Z) = ε⁻¹ * hs (Ad W Z - Ad W' Z) := by
  simp only [KL, AdL, LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.id_apply]
  rw [← smul_sub, show Ad W Z - Z - (Ad W' Z - Z) = Ad W Z - Ad W' Z by abel, RegularAverages.hs_smul,
    Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.2 hε.le)]

/-! ### The bounds along one bond, with the Hilbert–Schmidt norm -/

lemma hs_Ad_Uf_sub_le {ε : ℝ} (hε : 0 < ε) {A : Fin 4 → (Fin 4 → ℤ) → Mat} {μ : Fin 4} {n : Fin 4 → ℤ}
    (hA : ε * ‖A μ n‖ ≤ 1 / 32) (Z : Mat) : hs (Ad (Uf ε A μ n) Z - Z) ≤ 6 * (ε * ‖A μ n‖) * hs Z := by
  have hX : ‖ε • A μ n‖ ≤ 1 / 32 := by rw [norm_smul, Real.norm_of_nonneg hε.le]; exact hA
  have h := hs_Ad_exp_sub_le hX Z
  rwa [norm_smul, Real.norm_of_nonneg hε.le] at h

lemma hs_Ad_Ub_sub_le {ε : ℝ} (hε : 0 < ε) {A : Fin 4 → (Fin 4 → ℤ) → Mat} {μ : Fin 4} {n : Fin 4 → ℤ}
    (hA : ε * ‖A μ (n - e4 μ)‖ ≤ 1 / 32) (Z : Mat) :
    hs (Ad (Ub ε A μ n) Z - Z) ≤ 6 * (ε * ‖A μ (n - e4 μ)‖) * hs Z := by
  have hX : ‖-(ε • A μ (n - e4 μ))‖ ≤ 1 / 32 := by rw [norm_neg, norm_smul, Real.norm_of_nonneg hε.le]; exact hA
  have h := hs_Ad_exp_sub_le hX Z
  rwa [norm_neg, norm_smul, Real.norm_of_nonneg hε.le] at h

lemma hs_Ad_Uf_diff_le {ε : ℝ} (hε : 0 < ε) {A : Fin 4 → (Fin 4 → ℤ) → Mat} {μ : Fin 4} {n n' : Fin 4 → ℤ}
    (hA : ε * ‖A μ n‖ ≤ 1 / 32) (hA' : ε * ‖A μ n'‖ ≤ 1 / 32) (Z : Mat) :
    hs (Ad (Uf ε A μ n) Z - Ad (Uf ε A μ n') Z) ≤ 8 * (ε * ‖A μ n - A μ n'‖) * hs Z := by
  have hX : ‖ε • A μ n‖ ≤ 1 / 32 := by rw [norm_smul, Real.norm_of_nonneg hε.le]; exact hA
  have hX' : ‖ε • A μ n'‖ ≤ 1 / 32 := by rw [norm_smul, Real.norm_of_nonneg hε.le]; exact hA'
  have h := hs_Ad_exp_sub_Ad_exp_le hX' hX Z
  rwa [← smul_sub, norm_smul, Real.norm_of_nonneg hε.le] at h

lemma hs_Ad_Ub_diff_le {ε : ℝ} (hε : 0 < ε) {A : Fin 4 → (Fin 4 → ℤ) → Mat} {μ : Fin 4} {n n' : Fin 4 → ℤ}
    (hA : ε * ‖A μ (n - e4 μ)‖ ≤ 1 / 32) (hA' : ε * ‖A μ (n' - e4 μ)‖ ≤ 1 / 32) (Z : Mat) :
    hs (Ad (Ub ε A μ n) Z - Ad (Ub ε A μ n') Z) ≤ 8 * (ε * ‖A μ (n - e4 μ) - A μ (n' - e4 μ)‖) * hs Z := by
  have hX : ‖-(ε • A μ (n - e4 μ))‖ ≤ 1 / 32 := by rw [norm_neg, norm_smul, Real.norm_of_nonneg hε.le]; exact hA
  have hX' : ‖-(ε • A μ (n' - e4 μ))‖ ≤ 1 / 32 := by
    rw [norm_neg, norm_smul, Real.norm_of_nonneg hε.le]; exact hA'
  have h := hs_Ad_exp_sub_Ad_exp_le hX' hX Z
  rwa [neg_sub_neg, ← smul_sub, norm_smul, Real.norm_of_nonneg hε.le, ← norm_neg, neg_sub] at h

/-! ### The operators -/

lemma mul_cancel_aux {ε c : ℝ} (hε : 0 < ε) (x y : ℝ) : ε⁻¹ * (c * (ε * x) * y) = c * x * y := by
  field_simp

/-- `‖K_μ(n)‖ ≤ 6‖Ã_μ(n)‖`. -/
theorem norm_Kf_le {ε : ℝ} (hε : 0 < ε) {A : Fin 4 → (Fin 4 → ℤ) → Mat} {μ : Fin 4} {n : Fin 4 → ℤ}
    (hA : ε * ‖A μ n‖ ≤ 1 / 32) : ‖(Kf ε A μ n : VS N m →L[ℝ] VS N m)‖ ≤ 6 * ‖A μ n‖ := by
  refine norm_liftV_le _ (by positivity) fun Z => ?_
  rw [hs_KL ε hε, ← mul_cancel_aux hε]
  exact mul_le_mul_of_nonneg_left (hs_Ad_Uf_sub_le hε hA Z) (inv_nonneg.2 hε.le)

/-- `‖K'_μ(n)‖ ≤ 6‖Ã_μ(n - e_μ)‖`. -/
theorem norm_Kb_le {ε : ℝ} (hε : 0 < ε) {A : Fin 4 → (Fin 4 → ℤ) → Mat} {μ : Fin 4} {n : Fin 4 → ℤ}
    (hA : ε * ‖A μ (n - e4 μ)‖ ≤ 1 / 32) : ‖(Kb ε A μ n : VS N m →L[ℝ] VS N m)‖ ≤ 6 * ‖A μ (n - e4 μ)‖ := by
  refine norm_liftV_le _ (by positivity) fun Z => ?_
  rw [hs_KL ε hε, ← mul_cancel_aux hε]
  exact mul_le_mul_of_nonneg_left (hs_Ad_Ub_sub_le hε hA Z) (inv_nonneg.2 hε.le)

/-- `‖K_μ(n) - K_μ(n')‖ ≤ 8‖Ã_μ(n) - Ã_μ(n')‖`. -/
theorem norm_Kf_sub_le {ε : ℝ} (hε : 0 < ε) {A : Fin 4 → (Fin 4 → ℤ) → Mat} {μ : Fin 4} {n n' : Fin 4 → ℤ}
    (hA : ε * ‖A μ n‖ ≤ 1 / 32) (hA' : ε * ‖A μ n'‖ ≤ 1 / 32) :
    ‖(Kf ε A μ n - Kf ε A μ n' : VS N m →L[ℝ] VS N m)‖ ≤ 8 * ‖A μ n - A μ n'‖ := by
  refine opnorm_liftV_sub_le _ _ (by positivity) fun Z => ?_
  rw [hs_KL_sub ε hε, ← mul_cancel_aux hε]
  exact mul_le_mul_of_nonneg_left (hs_Ad_Uf_diff_le hε hA hA' Z) (inv_nonneg.2 hε.le)

/-- `‖K'_μ(n) - K'_μ(n')‖ ≤ 8‖Ã_μ(n - e_μ) - Ã_μ(n' - e_μ)‖`. -/
theorem norm_Kb_sub_le {ε : ℝ} (hε : 0 < ε) {A : Fin 4 → (Fin 4 → ℤ) → Mat} {μ : Fin 4} {n n' : Fin 4 → ℤ}
    (hA : ε * ‖A μ (n - e4 μ)‖ ≤ 1 / 32) (hA' : ε * ‖A μ (n' - e4 μ)‖ ≤ 1 / 32) :
    ‖(Kb ε A μ n - Kb ε A μ n' : VS N m →L[ℝ] VS N m)‖ ≤ 8 * ‖A μ (n - e4 μ) - A μ (n' - e4 μ)‖ := by
  refine opnorm_liftV_sub_le _ _ (by positivity) fun Z => ?_
  rw [hs_KL_sub ε hε, ← mul_cancel_aux hε]
  exact mul_le_mul_of_nonneg_left (hs_Ad_Ub_diff_le hε hA hA' Z) (inv_nonneg.2 hε.le)

end SFLocal
end CoreLean

end
