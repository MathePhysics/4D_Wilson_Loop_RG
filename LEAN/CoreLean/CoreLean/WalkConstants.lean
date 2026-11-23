/-
The arithmetic of the constants in the proofs of `lem:walk-small`, `lem:walk-factor`, and
`lem:vector-commutator` of BALABAN_CORE.tex (`bf6b2bc552ba`): each lemma below is the last inequality
of a step, with the bounds of the terms which the step collects as hypotheses.
-/
import Mathlib

namespace CoreLean
namespace WalkConstants

lemma le_cube {L : ℝ} (hL : 1 ≤ L) : L ≤ L ^ 3 := by
  have : 0 ≤ L * (L - 1) * (L + 1) :=
    mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
  nlinarith

/-- `lem:walk-small`, the gauge field: `(s/a_i)α₀(a_j/a_i + a_j²/a_i²) ≤ 20LMα₀(L + L²) ≤ 40L³Mα₀`
for `s/a_i ≤ 20LM` and `a_j/a_i ≤ L`, `L ≥ 1`. -/
theorem walk_small_gauge (L M α₀ x r : ℝ) (hL : 1 ≤ L) (hM : 0 ≤ M) (hα : 0 ≤ α₀) (hx0 : 0 ≤ x)
    (hx : x ≤ 20 * L * M) (hr0 : 0 ≤ r) (hr : r ≤ L) :
    x * α₀ * (r + r ^ 2) ≤ 40 * L ^ 3 * M * α₀ := by
  have h1 : r + r ^ 2 ≤ L + L ^ 2 := by nlinarith
  have h2 : L + L ^ 2 ≤ 2 * L ^ 2 := by nlinarith
  have h3 : 0 ≤ r + r ^ 2 := by positivity
  calc x * α₀ * (r + r ^ 2) ≤ (20 * L * M) * α₀ * (2 * L ^ 2) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_right hx hα) (h1.trans h2) h3 (by positivity)
    _ = 40 * L ^ 3 * M * α₀ := by ring

/-- `lem:walk-small`, the total: `40L³Mα₀ + 2L²α₁ ≤ 40L³(Mα₀ + α₁) ≤ 40L³a_w = c_sf`. -/
theorem walk_small_total (L M α₀ α₁ a_w : ℝ) (hL : 1 ≤ L) (hM : 0 ≤ M) (hα₀ : 0 ≤ α₀)
    (hα₁ : 0 ≤ α₁) (h : M * α₀ + α₁ ≤ a_w) :
    40 * L ^ 3 * M * α₀ + 2 * L ^ 2 * α₁ ≤ 40 * L ^ 3 * a_w := by
  have hL2 : 2 * L ^ 2 ≤ 40 * L ^ 3 := by nlinarith
  have : 2 * L ^ 2 * α₁ ≤ 40 * L ^ 3 * α₁ := mul_le_mul_of_nonneg_right hL2 hα₁
  have hL3 : 0 ≤ 40 * L ^ 3 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h hL3]

/-- `lem:walk-factor`(ii): `12mS_∇ + 4m(Ma_j)^{-1}S + 16m a_n^{-1}S ≤ 20m(S_∇ + a_n^{-1}S)`, with
`m = C_h(Ma_j)^{-1}` and `(Ma_j)^{-1} ≤ a_n^{-1}`. -/
theorem walk_factor_ii (m S_D S A an_inv : ℝ) (hm : 0 ≤ m) (hSD : 0 ≤ S_D) (hS : 0 ≤ S)
    (hA : A ≤ an_inv) :
    4 * (3 * m) * S_D + 4 * m * A * S + 16 * m * an_inv * S ≤ 20 * m * (S_D + an_inv * S) := by
  have : m * A * S ≤ m * an_inv * S := by
    apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hA hm) hS
  nlinarith [mul_nonneg hm hSD, this]

/-- `lem:walk-factor`(iii): `20C_h e^{5δ}B(L + L³) ≤ 40L³N_bC_he^{5δ}B = C_f`. -/
theorem walk_factor_iii (L N_b C_h E B : ℝ) (hL : 1 ≤ L) (hN : 1 ≤ N_b) (hC : 0 ≤ C_h) (hE : 0 ≤ E)
    (hB : 0 ≤ B) : 20 * C_h * E * B * (L + L ^ 3) ≤ 40 * L ^ 3 * N_b * C_h * E * B := by
  have h1 : L + L ^ 3 ≤ 2 * L ^ 3 := by linarith [le_cube hL]
  have h2 : 2 * L ^ 3 ≤ 2 * L ^ 3 * N_b := by nlinarith
  have hp : 0 ≤ C_h * E * B := by positivity
  nlinarith [mul_le_mul_of_nonneg_left (h1.trans h2) hp]

/-- `lem:walk-factor`(v): `2L + 16L³ + 8L²N_be^{5δ} ≤ 40L³N_be^{5δ}`. -/
theorem walk_factor_v (L N_b E : ℝ) (hL : 1 ≤ L) (hN : 1 ≤ N_b) (hE : 1 ≤ E) :
    2 * L + 16 * L ^ 3 + 8 * L ^ 2 * N_b * E ≤ 40 * L ^ 3 * N_b * E := by
  have hNE : 1 ≤ N_b * E := by nlinarith
  have hL3 : L ≤ L ^ 3 := le_cube hL
  have hL2 : L ^ 2 ≤ L ^ 3 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hL2 (by linarith : (0 : ℝ) ≤ 8 * (N_b * E)),
    mul_le_mul_of_nonneg_left hNE (by positivity : (0 : ℝ) ≤ L ^ 3)]

/-- `lem:vector-commutator`, `eq:cube-plaquettes`: `36c + 1296c² ≤ 40c ≤ 1/16` for `640c ≤ 1`. -/
theorem cube_plaquettes (c : ℝ) (hc : 0 ≤ c) (h : 640 * c ≤ 1) :
    36 * c + 1296 * c ^ 2 ≤ 40 * c ∧ 40 * c ≤ 1 / 16 := by
  constructor <;> nlinarith

/-- `lem:vector-commutator`(ii): `80 + 40 + 10L + C_ΔL + 2⁷NC_Q ≤ C_cm = 2⁹L² + L²C_Δ + 2⁷NLC_Q`. -/
theorem vector_commutator_ii (L N C_Δ C_Q : ℝ) (hL : 1 ≤ L) (hN : 0 ≤ N) (hΔ : 0 ≤ C_Δ)
    (hQ : 0 ≤ C_Q) :
    80 + 40 + 10 * L + C_Δ * L + 2 ^ 7 * N * C_Q ≤
      2 ^ 9 * L ^ 2 + L ^ 2 * C_Δ + 2 ^ 7 * N * L * C_Q := by
  have h1 : L ≤ L ^ 2 := by nlinarith
  have h2 : C_Δ * L ≤ L ^ 2 * C_Δ := by nlinarith
  have h3 : 2 ^ 7 * N * C_Q ≤ 2 ^ 7 * N * L * C_Q := by
    have : 0 ≤ 2 ^ 7 * N * C_Q := by positivity
    nlinarith
  nlinarith

/-- `lem:vector-commutator`(i): the coefficients `80` and `10 + C_ΔL² + 2⁷NC_QL` are at most `C_cm`,
the second after `a_n^{-1} ≤ La_j^{-1}` and `(Ma_j)^{-1} ≤ a_j^{-1}`. -/
theorem vector_commutator_i (L N C_Δ C_Q : ℝ) (hL : 1 ≤ L) (hN : 0 ≤ N) (hΔ : 0 ≤ C_Δ)
    (hQ : 0 ≤ C_Q) :
    80 ≤ 2 ^ 9 * L ^ 2 + L ^ 2 * C_Δ + 2 ^ 7 * N * L * C_Q ∧
      10 + C_Δ * L * L + 2 ^ 7 * N * C_Q * L ≤ 2 ^ 9 * L ^ 2 + L ^ 2 * C_Δ + 2 ^ 7 * N * L * C_Q := by
  have hL2 : 1 ≤ L ^ 2 := by nlinarith
  have : 0 ≤ L ^ 2 * C_Δ := by positivity
  have : 0 ≤ 2 ^ 7 * N * L * C_Q := by positivity
  constructor
  · nlinarith
  · nlinarith

end WalkConstants
end CoreLean
