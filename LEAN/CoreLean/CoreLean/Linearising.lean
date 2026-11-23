/-
`prop:linearising-pair` of BALABAN_CORE.tex (statements (i) and (ii) of `prop:linearising`), in abstract form.

The `1`-forms are a normed space `X` with the norm `‖·‖_{∞,(-1)}` and a second function `st` (the norm
`‖·‖_{∞,*}`, with `‖A‖ ≤ st A`); the functions on the bonds of the layers are a complete normed space `Y`.
The data are `H : Y → X` with `‖Hν‖ ≤ B‖ν‖` and `st(Hν) ≤ B‖ν‖` (`eq:linearising-hypothesis` for the weight `1`),
the remainder `𝖢 : X → Y` with `‖𝖢(A)‖ ≤ κ‖A‖²` and a derivative `𝖢'(A)` with `‖𝖢'(A)‖ ≤ κ'‖A‖` on the ball
`‖A‖ ≤ r₀` (`eq:remainder-bounds` for the weight `1`, `r₀ = c'₄/(2L)`), and the conditions of
`eq:linearising-constants` on `a₃`: `(1 + B)a₃ ≤ r₀`, `κ(1 + B)²a₃ ≤ 1`, `2κ'(1 + B)²a₃ ≤ 1`.

* `linearising_exists`, `linearising_unique`: the map `𝒯(𝖣) = 𝖢(A' - H𝖣)` is a contraction of the ball
  `‖𝖣‖ ≤ a₃` (by the mean value inequality on the ball of radius `(1 + B)a₃`), with exactly one fixed point
  `𝖣(A')` there, and `‖𝖣(A')‖ ≤ 2κ‖A'‖²` (`prop:linearising`(i), without the holomorphy).
* `linearising_relative_average`, `linearising_star`, `linearising_injective`, `linearising_surjective`: for
  `T(A') = A' - H𝖣(A')`: `𝖷(T(A')) = QA'` when `QH = I` and `𝖷 = Q + 𝖢`; `st(T(A') - A') ≤ 2κB‖A'‖²`; `T` is
  injective on the ball; every `A` with `‖A‖ ≤ a₃/4` is `T(A')` with `‖A'‖ ≤ 2‖A‖`, `st A' ≤ 2 st A`
  (`prop:linearising`(ii)).
* `hasFDerivAt_fix`: when `𝖢` is strictly differentiable on the ball, `𝖣` is complex differentiable at every
  `A₀` with `‖A₀‖ < a₃`, with the derivative `𝖣'(A₀) = (I + 𝖢'(T(A₀))H)⁻¹𝖢'(T(A₀))` (`dfix`); the proof uses the
  Lipschitz bound `fix_lipschitz` and `‖𝖢'(T(A₀))H‖ ≤ ½`, not the implicit function theorem. `dfix_eq` is the
  differentiated `eq:linearising-equation`, `𝔡 = 𝖢'(T(A₀))(δ - H𝔡)`.
* `dfix_weighted`, `dfix3_weighted`: `prop:linearising`(iii) in every pair of weighted norms `w`, `v` for which
  the weighted forms of `eq:remainder-bounds`, `eq:remainder-second`, `eq:remainder-third` and
  `eq:linearising-hypothesis` hold: `w(𝔡) ≤ 6κ'‖A₀‖v(δ)`, `v(δ - H𝔡) ≤ 4v(δ)`, and for `𝖣₃ = 𝖣 - 𝖢⁽²⁾`
  `w(𝔡₃) ≤ κ'(2κB + 18κ'B + 36q)‖A₀‖²v(δ)`, `q = 2L/c'₄`, the core's bracket of `C₅`.
-/
import Mathlib

noncomputable section

namespace CoreLean

namespace Linearising

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [NormedAddCommGroup Y] [NormedSpace ℂ Y]
  [CompleteSpace Y]

/-- The data of `prop:linearising-pair` (for the weight `1`). -/
structure Data (X Y : Type*) [NormedAddCommGroup X] [NormedSpace ℂ X] [NormedAddCommGroup Y]
    [NormedSpace ℂ Y] where
  H : Y →L[ℂ] X
  C : X → Y
  C' : X → X →L[ℂ] Y
  B : ℝ
  κ : ℝ
  κ' : ℝ
  r₀ : ℝ
  a₃ : ℝ
  B_nonneg : 0 ≤ B
  κ_nonneg : 0 ≤ κ
  κ'_nonneg : 0 ≤ κ'
  a₃_pos : 0 < a₃
  norm_H : ∀ ν, ‖H ν‖ ≤ B * ‖ν‖
  norm_C : ∀ A, ‖A‖ ≤ r₀ → ‖C A‖ ≤ κ * ‖A‖ ^ 2
  deriv_C : ∀ A, ‖A‖ ≤ r₀ → HasFDerivAt C (C' A) A
  norm_C' : ∀ A, ‖A‖ ≤ r₀ → ‖C' A‖ ≤ κ' * ‖A‖
  cond₁ : (1 + B) * a₃ ≤ r₀
  cond₂ : κ * (1 + B) ^ 2 * a₃ ≤ 1
  cond₃ : 2 * κ' * (1 + B) ^ 2 * a₃ ≤ 1

variable (P : Data X Y)

namespace Data

lemma norm_arg_le {A' : X} (hA' : ‖A'‖ ≤ P.a₃) {D : Y} (hD : ‖D‖ ≤ P.a₃) :
    ‖A' - P.H D‖ ≤ (1 + P.B) * P.a₃ := by
  have := P.norm_H D
  calc ‖A' - P.H D‖ ≤ ‖A'‖ + ‖P.H D‖ := norm_sub_le _ _
    _ ≤ P.a₃ + P.B * P.a₃ := by nlinarith [P.B_nonneg]
    _ = (1 + P.B) * P.a₃ := by ring

/-- `𝖢` is Lipschitz with the constant `κ'(1 + B)a₃` on the ball of radius `(1 + B)a₃`. -/
lemma lipschitz_C {A₁ A₂ : X} (h₁ : ‖A₁‖ ≤ (1 + P.B) * P.a₃) (h₂ : ‖A₂‖ ≤ (1 + P.B) * P.a₃) :
    ‖P.C A₁ - P.C A₂‖ ≤ P.κ' * ((1 + P.B) * P.a₃) * ‖A₁ - A₂‖ := by
  have hs : Convex ℝ (Metric.closedBall (0 : X) ((1 + P.B) * P.a₃)) := convex_closedBall _ _
  refine hs.norm_image_sub_le_of_norm_hasFDerivWithin_le (f' := P.C') (fun A hA => ?_) (fun A hA => ?_)
    (by simpa using h₂) (by simpa using h₁)
  · have hA' : ‖A‖ ≤ P.r₀ := (by simpa using hA : ‖A‖ ≤ (1 + P.B) * P.a₃).trans P.cond₁
    exact (P.deriv_C A hA').hasFDerivWithinAt
  · have hA1 : ‖A‖ ≤ (1 + P.B) * P.a₃ := by simpa using hA
    exact (P.norm_C' A (hA1.trans P.cond₁)).trans (mul_le_mul_of_nonneg_left hA1 P.κ'_nonneg)

/-- The map `𝒯(𝖣) = 𝖢(A' - H𝖣)` maps the ball `‖𝖣‖ ≤ a₃` into itself. -/
lemma maps_ball {A' : X} (hA' : ‖A'‖ ≤ P.a₃) {D : Y} (hD : ‖D‖ ≤ P.a₃) :
    ‖P.C (A' - P.H D)‖ ≤ P.a₃ := by
  have h := P.norm_arg_le hA' hD
  have hpos : 0 ≤ (1 + P.B) * P.a₃ := by have := P.B_nonneg; have := P.a₃_pos; positivity
  refine (P.norm_C _ (h.trans P.cond₁)).trans ?_
  calc P.κ * ‖A' - P.H D‖ ^ 2 ≤ P.κ * ((1 + P.B) * P.a₃) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) h 2) P.κ_nonneg
    _ = (P.κ * (1 + P.B) ^ 2 * P.a₃) * P.a₃ := by ring
    _ ≤ 1 * P.a₃ := mul_le_mul_of_nonneg_right P.cond₂ P.a₃_pos.le
    _ = P.a₃ := one_mul _

/-- `𝒯` is a contraction with the constant `½` on the ball. -/
lemma contraction {A' : X} (hA' : ‖A'‖ ≤ P.a₃) {D₁ D₂ : Y} (h₁ : ‖D₁‖ ≤ P.a₃) (h₂ : ‖D₂‖ ≤ P.a₃) :
    ‖P.C (A' - P.H D₁) - P.C (A' - P.H D₂)‖ ≤ 1 / 2 * ‖D₁ - D₂‖ := by
  have hL := P.lipschitz_C (P.norm_arg_le hA' h₁) (P.norm_arg_le hA' h₂)
  have e : A' - P.H D₁ - (A' - P.H D₂) = P.H (D₂ - D₁) := by rw [map_sub]; abel
  rw [e] at hL
  have hH := P.norm_H (D₂ - D₁)
  rw [norm_sub_rev D₂ D₁] at hH
  have hB := P.B_nonneg
  have hk : P.κ' * ((1 + P.B) * P.a₃) * P.B ≤ 1 / 2 := by
    have : P.κ' * ((1 + P.B) * P.a₃) * P.B ≤ P.κ' * (1 + P.B) ^ 2 * P.a₃ := by
      have h0 : 0 ≤ P.κ' * ((1 + P.B) * P.a₃) := by have := P.κ'_nonneg; have := P.a₃_pos; positivity
      nlinarith
    linarith [P.cond₃]
  have h0 : 0 ≤ P.κ' * ((1 + P.B) * P.a₃) := by have := P.κ'_nonneg; have := P.a₃_pos; positivity
  calc ‖P.C (A' - P.H D₁) - P.C (A' - P.H D₂)‖ ≤ P.κ' * ((1 + P.B) * P.a₃) * ‖P.H (D₂ - D₁)‖ := hL
    _ ≤ P.κ' * ((1 + P.B) * P.a₃) * (P.B * ‖D₁ - D₂‖) := mul_le_mul_of_nonneg_left hH h0
    _ = P.κ' * ((1 + P.B) * P.a₃) * P.B * ‖D₁ - D₂‖ := by ring
    _ ≤ 1 / 2 * ‖D₁ - D₂‖ := mul_le_mul_of_nonneg_right hk (norm_nonneg _)

/-- `prop:linearising`(i), uniqueness: two fixed points of `𝒯` in the ball agree. -/
theorem linearising_unique {A' : X} (hA' : ‖A'‖ ≤ P.a₃) {D₁ D₂ : Y} (h₁ : ‖D₁‖ ≤ P.a₃)
    (h₂ : ‖D₂‖ ≤ P.a₃) (e₁ : D₁ = P.C (A' - P.H D₁)) (e₂ : D₂ = P.C (A' - P.H D₂)) : D₁ = D₂ := by
  have h := P.contraction hA' h₁ h₂
  rw [← e₁, ← e₂] at h
  have : ‖D₁ - D₂‖ ≤ 0 := by linarith [norm_nonneg (D₁ - D₂)]
  exact sub_eq_zero.mp (norm_le_zero_iff.mp this)

/-- `prop:linearising`(i), existence and the bound: `𝒯` has a fixed point `𝖣` in the ball, and
`‖𝖣‖ ≤ 2κ‖A'‖²`. -/
theorem linearising_exists {A' : X} (hA' : ‖A'‖ ≤ P.a₃) :
    ∃ D : Y, ‖D‖ ≤ P.a₃ ∧ D = P.C (A' - P.H D) ∧ ‖D‖ ≤ 2 * P.κ * ‖A'‖ ^ 2 := by
  set S := Metric.closedBall (0 : Y) P.a₃
  haveI : CompleteSpace S := Metric.isClosed_closedBall.completeSpace_coe
  haveI : Nonempty S := ⟨⟨0, Metric.mem_closedBall_self P.a₃_pos.le⟩⟩
  let f : S → S := fun D => ⟨P.C (A' - P.H D), by
    exact mem_closedBall_zero_iff.mpr (P.maps_ball hA' (mem_closedBall_zero_iff.mp D.2))⟩
  have hf : ContractingWith (1 / 2 : NNReal) f := by
    refine ⟨by norm_num, LipschitzWith.of_dist_le_mul fun D₁ D₂ => ?_⟩
    simp only [Subtype.dist_eq, dist_eq_norm, f]
    have := P.contraction hA' (mem_closedBall_zero_iff.mp D₁.2) (mem_closedBall_zero_iff.mp D₂.2)
    simpa using this
  set D := ContractingWith.fixedPoint f hf
  have hfix : f D = D := ContractingWith.fixedPoint_isFixedPt hf
  have hD : ‖(D : Y)‖ ≤ P.a₃ := mem_closedBall_zero_iff.mp D.2
  have e : (D : Y) = P.C (A' - P.H D) := by
    have := congrArg Subtype.val hfix
    exact this.symm
  refine ⟨D, hD, e, ?_⟩
  -- `‖𝖣‖ ≤ ‖𝒯(𝖣) - 𝒯(0)‖ + ‖𝖢(A')‖ ≤ ½‖𝖣‖ + κ‖A'‖²`
  have h0 := P.contraction hA' hD (by simpa using P.a₃_pos.le : ‖(0 : Y)‖ ≤ P.a₃)
  rw [map_zero, sub_zero, sub_zero, ← e] at h0
  have hC := P.norm_C A' (hA'.trans ((le_mul_of_one_le_left P.a₃_pos.le
    (by linarith [P.B_nonneg])).trans P.cond₁))
  have : ‖(D : Y)‖ ≤ ‖(D : Y) - P.C A'‖ + ‖P.C A'‖ := by
    have := norm_add_le ((D : Y) - P.C A') (P.C A'); simpa using this
  linarith

/-- The fixed point `𝖣(A')` (for `‖A'‖ ≤ a₃`; `0` otherwise). -/
def fix (A' : X) : Y :=
  if h : ‖A'‖ ≤ P.a₃ then Classical.choose (P.linearising_exists h) else 0

lemma fix_spec {A' : X} (hA' : ‖A'‖ ≤ P.a₃) :
    ‖P.fix A'‖ ≤ P.a₃ ∧ P.fix A' = P.C (A' - P.H (P.fix A')) ∧ ‖P.fix A'‖ ≤ 2 * P.κ * ‖A'‖ ^ 2 := by
  unfold fix
  rw [dif_pos hA']
  exact Classical.choose_spec (P.linearising_exists hA')

/-- The linearising transformation `T(A') = A' - H𝖣(A')`. -/
def T (A' : X) : X := A' - P.H (P.fix A')

/-- `prop:linearising`(ii): `𝖷(T(A')) = QA'` for `𝖷 = Q + 𝖢` and `QH = I`. -/
theorem linearising_relative_average (Q : X →ₗ[ℂ] Y) (hQH : ∀ ν, Q (P.H ν) = ν) {A' : X}
    (hA' : ‖A'‖ ≤ P.a₃) : Q (P.T A') + P.C (P.T A') = Q A' := by
  obtain ⟨-, e, -⟩ := P.fix_spec hA'
  unfold T
  rw [← e, map_sub, hQH]
  abel

/-- `prop:linearising`(ii): `st(T(A') - A') ≤ 2κB‖A'‖²` when `st(Hν) ≤ B‖ν‖`. -/
theorem linearising_star (st : X → ℝ) (hst : ∀ ν, st (P.H ν) ≤ P.B * ‖ν‖) (hst_neg : ∀ x, st (-x) = st x)
    {A' : X} (hA' : ‖A'‖ ≤ P.a₃) : st (P.T A' - A') ≤ 2 * P.κ * P.B * ‖A'‖ ^ 2 := by
  obtain ⟨-, -, hb⟩ := P.fix_spec hA'
  have e : P.T A' - A' = -P.H (P.fix A') := by unfold T; abel
  rw [e, hst_neg]
  calc st (P.H (P.fix A')) ≤ P.B * ‖P.fix A'‖ := hst _
    _ ≤ P.B * (2 * P.κ * ‖A'‖ ^ 2) := mul_le_mul_of_nonneg_left hb P.B_nonneg
    _ = 2 * P.κ * P.B * ‖A'‖ ^ 2 := by ring

/-- `prop:linearising`(ii): `T` is injective on the ball `‖A'‖ ≤ a₃`. -/
theorem linearising_injective {A₁ A₂ : X} (h₁ : ‖A₁‖ ≤ P.a₃) (h₂ : ‖A₂‖ ≤ P.a₃)
    (h : P.T A₁ = P.T A₂) : A₁ = A₂ := by
  obtain ⟨-, e₁, -⟩ := P.fix_spec h₁
  obtain ⟨-, e₂, -⟩ := P.fix_spec h₂
  have hD : P.fix A₁ = P.fix A₂ := by
    rw [e₁, e₂]; unfold T at h; rw [h]
  have := congrArg (· + P.H (P.fix A₁)) h
  simp only [T, sub_add_cancel] at this
  rw [this, hD, sub_add_cancel]

/-- `prop:linearising`(ii): every `A` with `‖A‖ ≤ a₃/4` is `T(A')` with `‖A'‖ ≤ 2‖A‖` and `st A' ≤ 2 st A`,
for a subadditive `st` with `‖·‖ ≤ st` and `st(Hν) ≤ B‖ν‖`. -/
theorem linearising_surjective (st : X → ℝ) (hst : ∀ ν, st (P.H ν) ≤ P.B * ‖ν‖)
    (hst_add : ∀ x y, st (x + y) ≤ st x + st y) (hst_ge : ∀ x, ‖x‖ ≤ st x) {A : X}
    (hA : ‖A‖ ≤ P.a₃ / 4) :
    ∃ A' : X, ‖A'‖ ≤ P.a₃ ∧ P.T A' = A ∧ ‖A'‖ ≤ 2 * ‖A‖ ∧ st A' ≤ 2 * st A := by
  have ha := P.a₃_pos
  have hB := P.B_nonneg
  have hκ := P.κ_nonneg
  have hAr : ‖A‖ ≤ P.r₀ := by
    have : P.a₃ / 4 ≤ (1 + P.B) * P.a₃ := by nlinarith
    linarith [P.cond₁]
  have hC := P.norm_C A hAr
  -- `κBa₃ ≤ 1` and `κa₃ ≤ 1`
  have hκB : P.κ * P.B * P.a₃ ≤ 1 := by
    have : P.κ * P.B * P.a₃ ≤ P.κ * (1 + P.B) ^ 2 * P.a₃ := by
      have : P.B ≤ (1 + P.B) ^ 2 := by nlinarith
      have h0 : 0 ≤ P.κ * P.a₃ := by positivity
      nlinarith
    linarith [P.cond₂]
  have hκ1 : P.κ * P.a₃ ≤ 1 := by
    have : P.κ * P.a₃ ≤ P.κ * (1 + P.B) ^ 2 * P.a₃ := by
      have : 1 ≤ (1 + P.B) ^ 2 := by nlinarith
      have h0 : 0 ≤ P.κ * P.a₃ := by positivity
      nlinarith
    linarith [P.cond₂]
  have hA0 := norm_nonneg A
  -- `‖𝖢(A)‖ ≤ a₃` and `‖H𝖢(A)‖ ≤ ‖A‖/4`
  have hCa : ‖P.C A‖ ≤ P.a₃ := by
    have : P.κ * ‖A‖ ^ 2 ≤ P.a₃ := by
      have h1 : ‖A‖ ^ 2 ≤ P.a₃ * P.a₃ := by nlinarith
      nlinarith
    linarith
  have hHC : ‖P.H (P.C A)‖ ≤ ‖A‖ / 4 := by
    have h1 := P.norm_H (P.C A)
    have h2 : P.B * ‖P.C A‖ ≤ P.B * (P.κ * ‖A‖ ^ 2) := mul_le_mul_of_nonneg_left hC hB
    have h3 : P.B * (P.κ * ‖A‖ ^ 2) ≤ ‖A‖ / 4 := by
      have : P.κ * P.B * ‖A‖ ≤ 1 / 4 := by
        have : P.κ * P.B * ‖A‖ ≤ P.κ * P.B * (P.a₃ / 4) :=
          mul_le_mul_of_nonneg_left hA (by positivity)
        linarith
      nlinarith
    linarith
  have hstC : st (P.H (P.C A)) ≤ ‖A‖ / 4 := by
    have h1 := hst (P.C A)
    have h2 : P.B * ‖P.C A‖ ≤ P.B * (P.κ * ‖A‖ ^ 2) := mul_le_mul_of_nonneg_left hC hB
    have h3 : P.B * (P.κ * ‖A‖ ^ 2) ≤ ‖A‖ / 4 := by
      have : P.κ * P.B * ‖A‖ ≤ 1 / 4 := by
        have : P.κ * P.B * ‖A‖ ≤ P.κ * P.B * (P.a₃ / 4) :=
          mul_le_mul_of_nonneg_left hA (by positivity)
        linarith
      nlinarith
    linarith
  set A' := A + P.H (P.C A)
  have hA'n : ‖A'‖ ≤ 2 * ‖A‖ := by
    have := norm_add_le A (P.H (P.C A)); linarith
  have hA'a : ‖A'‖ ≤ P.a₃ := by linarith
  refine ⟨A', hA'a, ?_, hA'n, ?_⟩
  · -- `𝖢(A)` is the fixed point at `A'`
    have hfix : P.C A = P.C (A' - P.H (P.C A)) := by simp [A']
    obtain ⟨hb, e, -⟩ := P.fix_spec hA'a
    have := P.linearising_unique hA'a hb hCa e hfix
    unfold T
    rw [this]
    simp [A']
  · have := hst_add A (P.H (P.C A))
    have := hst_ge A
    linarith

/-! ### The derivative of `𝖣` (`prop:linearising`(i), the holomorphy, and (iii)) -/

/-- `𝖣` is Lipschitz on the ball, with the constant `2κ'(1 + B)a₃`. -/
lemma fix_lipschitz {A₁ A₂ : X} (h₁ : ‖A₁‖ ≤ P.a₃) (h₂ : ‖A₂‖ ≤ P.a₃) :
    ‖P.fix A₁ - P.fix A₂‖ ≤ 2 * (P.κ' * ((1 + P.B) * P.a₃)) * ‖A₁ - A₂‖ := by
  obtain ⟨hb₁, e₁, -⟩ := P.fix_spec h₁
  obtain ⟨hb₂, e₂, -⟩ := P.fix_spec h₂
  have hL := P.lipschitz_C (P.norm_arg_le h₁ hb₁) (P.norm_arg_le h₂ hb₁)
  have e : A₁ - P.H (P.fix A₁) - (A₂ - P.H (P.fix A₁)) = A₁ - A₂ := by abel
  rw [e] at hL
  have hc := P.contraction h₂ hb₁ hb₂
  have h12 : P.C (A₁ - P.H (P.fix A₁)) - P.C (A₂ - P.H (P.fix A₂)) = P.fix A₁ - P.fix A₂ := by
    rw [← e₁, ← e₂]
  have hsplit : P.fix A₁ - P.fix A₂ = (P.C (A₁ - P.H (P.fix A₁)) - P.C (A₂ - P.H (P.fix A₁))) +
      (P.C (A₂ - P.H (P.fix A₁)) - P.C (A₂ - P.H (P.fix A₂))) := by
    rw [← h12]; abel
  have := norm_add_le (P.C (A₁ - P.H (P.fix A₁)) - P.C (A₂ - P.H (P.fix A₁)))
    (P.C (A₂ - P.H (P.fix A₁)) - P.C (A₂ - P.H (P.fix A₂)))
  rw [← hsplit] at this
  linarith

/-- `‖𝖢'(T(A₀))H‖ ≤ ½`. -/
lemma norm_CH_le {A₀ : X} (hA₀ : ‖A₀‖ ≤ P.a₃) : ‖(P.C' (P.T A₀)).comp P.H‖ ≤ 1 / 2 := by
  obtain ⟨hb, -, -⟩ := P.fix_spec hA₀
  have hT : ‖P.T A₀‖ ≤ (1 + P.B) * P.a₃ := P.norm_arg_le hA₀ hb
  have hC' := P.norm_C' _ (hT.trans P.cond₁)
  have hH : ‖P.H‖ ≤ P.B := ContinuousLinearMap.opNorm_le_bound _ P.B_nonneg P.norm_H
  have hB := P.B_nonneg
  have hk : P.κ' * ((1 + P.B) * P.a₃) * P.B ≤ 1 / 2 := by
    have : P.κ' * ((1 + P.B) * P.a₃) * P.B ≤ P.κ' * (1 + P.B) ^ 2 * P.a₃ := by
      have h0 : 0 ≤ P.κ' * ((1 + P.B) * P.a₃) := by have := P.κ'_nonneg; have := P.a₃_pos; positivity
      nlinarith
    linarith [P.cond₃]
  calc ‖(P.C' (P.T A₀)).comp P.H‖ ≤ ‖P.C' (P.T A₀)‖ * ‖P.H‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (P.κ' * ((1 + P.B) * P.a₃)) * P.B :=
        mul_le_mul (hC'.trans (mul_le_mul_of_nonneg_left hT P.κ'_nonneg)) hH (norm_nonneg _)
          (by have := P.κ'_nonneg; have := P.a₃_pos; positivity)
    _ ≤ 1 / 2 := hk

/-- The derivative of `𝖣` at `A₀`: `(I + 𝖢'(T(A₀))H)⁻¹𝖢'(T(A₀))`. -/
def dfix (A₀ : X) : X →L[ℂ] Y :=
  (Ring.inverse (1 + (P.C' (P.T A₀)).comp P.H)).comp (P.C' (P.T A₀))

lemma one_add_comp_dfix {A₀ : X} (hA₀ : ‖A₀‖ ≤ P.a₃) :
    (1 + (P.C' (P.T A₀)).comp P.H).comp (P.dfix A₀) = P.C' (P.T A₀) := by
  have hu : IsUnit (1 + (P.C' (P.T A₀)).comp P.H) := by
    have h := IsUnit.one_sub_of_norm_lt_one (x := -((P.C' (P.T A₀)).comp P.H))
      (by rw [norm_neg]; linarith [P.norm_CH_le hA₀])
    rwa [sub_neg_eq_add] at h
  unfold dfix
  rw [← ContinuousLinearMap.comp_assoc, ← ContinuousLinearMap.mul_def, Ring.mul_inverse_cancel _ hu,
    ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp]

/-- The derivative `𝔡 = 𝖣'(A₀)δ` satisfies `𝔡 = 𝖢'(T(A₀))(δ - H𝔡)` (the core's differentiated
`eq:linearising-equation`). -/
lemma dfix_eq {A₀ : X} (hA₀ : ‖A₀‖ ≤ P.a₃) (δ : X) :
    P.dfix A₀ δ = P.C' (P.T A₀) (δ - P.H (P.dfix A₀ δ)) := by
  have h := congrArg (fun L : X →L[ℂ] Y => L δ) (P.one_add_comp_dfix hA₀)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.one_apply] at h
  rw [map_sub, ← h]
  abel

/-- `prop:linearising`(i), the holomorphy: `𝖣` is complex differentiable at every `A₀` with `‖A₀‖ < a₃`,
when `𝖢` is strictly differentiable on the ball `‖A‖ ≤ r₀`. -/
theorem hasFDerivAt_fix (hstrict : ∀ A, ‖A‖ ≤ P.r₀ → HasStrictFDerivAt P.C (P.C' A) A) {A₀ : X}
    (hA₀ : ‖A₀‖ < P.a₃) : HasFDerivAt P.fix (P.dfix A₀) A₀ := by
  have hA₀' := hA₀.le
  obtain ⟨hb₀, e₀, -⟩ := P.fix_spec hA₀'
  set T₀ := P.T A₀ with hT₀
  set K := (P.C' T₀).comp P.H with hK
  set c := 2 * (P.κ' * ((1 + P.B) * P.a₃)) with hc
  have hB := P.B_nonneg
  have hc0 : 0 ≤ c := by have := P.κ'_nonneg; have := P.a₃_pos; positivity
  have hT₀r : ‖T₀‖ ≤ P.r₀ := (P.norm_arg_le hA₀' hb₀).trans P.cond₁
  have hKn : ‖K‖ ≤ 1 / 2 := P.norm_CH_le hA₀'
  have hKL := P.one_add_comp_dfix hA₀'
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  refine Asymptotics.IsLittleO.of_bound fun ε hε => ?_
  set ε' := ε / (2 * (1 + P.B * c)) with hε'
  have hε'0 : 0 < ε' := by positivity
  -- the strict derivative of `𝖢` at `T₀`
  have hs := ((hstrict T₀ hT₀r).isLittleO).def hε'0
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff.mp hs
  set r := min (P.a₃ - ‖A₀‖) (ρ / (1 + P.B * c)) with hr
  have hr0 : 0 < r := lt_min (by linarith) (by positivity)
  filter_upwards [Metric.ball_mem_nhds (0 : X) hr0] with h hh
  have hh' : ‖h‖ < r := by simpa using hh
  have hA₁ : ‖A₀ + h‖ ≤ P.a₃ := by
    have := norm_add_le A₀ h; have := min_le_left (P.a₃ - ‖A₀‖) (ρ / (1 + P.B * c)); linarith
  obtain ⟨hb₁, e₁, -⟩ := P.fix_spec hA₁
  set Δ := P.fix (A₀ + h) - P.fix A₀ with hΔ
  have hΔn : ‖Δ‖ ≤ c * ‖h‖ := by
    have := P.fix_lipschitz hA₁ hA₀'
    simpa [hΔ] using this
  -- the two arguments of `𝖢`
  set x := A₀ + h - P.H (P.fix (A₀ + h)) with hx
  have hxT : x - T₀ = h - P.H Δ := by rw [hx, hT₀, T, hΔ, map_sub]; abel
  have hxTn : ‖x - T₀‖ ≤ (1 + P.B * c) * ‖h‖ := by
    rw [hxT]
    have := P.norm_H Δ
    have := norm_sub_le h (P.H Δ)
    nlinarith
  have hdist : dist (x, T₀) (T₀, T₀) < ρ := by
    rw [Prod.dist_eq, dist_self, max_eq_left dist_nonneg, dist_eq_norm]
    have h1 : (1 + P.B * c) * ‖h‖ < ρ := by
      have := min_le_right (P.a₃ - ‖A₀‖) (ρ / (1 + P.B * c))
      have hpos : 0 < 1 + P.B * c := by positivity
      rw [← lt_div_iff₀' hpos]; linarith
    linarith
  have hrem := hball hdist
  simp only at hrem
  -- `Δ = 𝖢(x) - 𝖢(T₀)`, and `E = Δ - 𝖣'(A₀)h` satisfies `E + KE = r`
  have hΔC : Δ = P.C x - P.C T₀ := by rw [hΔ, ← e₁, hT₀, T, ← e₀]
  set ρ' := P.C x - P.C T₀ - P.C' T₀ (x - T₀) with hρ'
  set E := Δ - P.dfix A₀ h with hE
  have h1 : P.dfix A₀ h + K (P.dfix A₀ h) = P.C' T₀ h := by
    have := congrArg (fun L : X →L[ℂ] Y => L h) hKL
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.one_apply] at this
    rw [hK, hT₀, ContinuousLinearMap.comp_apply]
    exact this
  have hEq : E + K E = ρ' := by
    calc E + K E = Δ + K Δ - (P.dfix A₀ h + K (P.dfix A₀ h)) := by rw [hE, map_sub]; abel
      _ = Δ + K Δ - P.C' T₀ h := by rw [h1]
      _ = ρ' := by
          rw [hρ', ← hΔC, hxT]
          simp only [map_sub, hK, ContinuousLinearMap.comp_apply, hΔ]
          abel
  have hKE : ‖K E‖ ≤ 1 / 2 * ‖E‖ := (K.le_opNorm E).trans (mul_le_mul_of_nonneg_right hKn (norm_nonneg _))
  have hEn : ‖E‖ ≤ 2 * ‖ρ'‖ := by
    have : E = ρ' - K E := by rw [← hEq]; abel
    have := norm_sub_le ρ' (K E)
    rw [← ‹E = ρ' - K E›] at this
    linarith
  have hρn : ‖ρ'‖ ≤ ε' * ((1 + P.B * c) * ‖h‖) :=
    hrem.trans (mul_le_mul_of_nonneg_left (by simpa using hxTn) hε'0.le)
  have hfin : 2 * (ε' * ((1 + P.B * c) * ‖h‖)) = ε * ‖h‖ := by
    rw [hε']; field_simp
  show ‖P.fix (A₀ + h) - P.fix A₀ - P.dfix A₀ h‖ ≤ ε * ‖h‖
  calc ‖P.fix (A₀ + h) - P.fix A₀ - P.dfix A₀ h‖ = ‖E‖ := rfl
    _ ≤ 2 * ‖ρ'‖ := hEn
    _ ≤ 2 * (ε' * ((1 + P.B * c) * ‖h‖)) := by linarith
    _ = ε * ‖h‖ := hfin

/-- `prop:linearising`(iii) for the derivative of `𝖣`, in any pair of weighted norms `w` (functions on the
bonds) and `v` (forms) for which `eq:remainder-bounds` and `eq:linearising-hypothesis` hold:
`w(𝔡) ≤ 6κ'‖A₀‖v(δ)` and `v(δ - H𝔡) ≤ 4v(δ)`, `𝔡 = 𝖣'(A₀)δ`. -/
theorem dfix_weighted (w : Y → ℝ) (v : X → ℝ) {A₀ : X} (hA₀ : ‖A₀‖ ≤ P.a₃)
    (hw : ∀ δ, w (P.C' (P.T A₀) δ) ≤ P.κ' * ‖P.T A₀‖ * v δ) (hvH : ∀ ν, v (P.H ν) ≤ P.B * w ν)
    (hv_sub : ∀ x y, v (x - y) ≤ v x + v y) (hv0 : ∀ x, 0 ≤ v x) (hw0 : ∀ y, 0 ≤ w y) (δ : X) :
    w (P.dfix A₀ δ) ≤ 6 * P.κ' * ‖A₀‖ * v δ ∧ v (δ - P.H (P.dfix A₀ δ)) ≤ 4 * v δ := by
  obtain ⟨hb, -, hD⟩ := P.fix_spec hA₀
  have hB := P.B_nonneg
  have hκ' := P.κ'_nonneg
  have ha := P.a₃_pos
  -- `‖T(A₀)‖ ≤ 3‖A₀‖`
  have hκB : P.κ * P.B * P.a₃ ≤ 1 := by
    have : P.κ * P.B * P.a₃ ≤ P.κ * (1 + P.B) ^ 2 * P.a₃ := by
      have : P.B ≤ (1 + P.B) ^ 2 := by nlinarith
      have h0 : 0 ≤ P.κ * P.a₃ := by have := P.κ_nonneg; positivity
      nlinarith
    linarith [P.cond₂]
  have hT3 : ‖P.T A₀‖ ≤ 3 * ‖A₀‖ := by
    have h1 : ‖P.T A₀‖ ≤ ‖A₀‖ + P.B * ‖P.fix A₀‖ := by
      unfold T
      exact (norm_sub_le _ _).trans (add_le_add le_rfl (P.norm_H _))
    have h2 : P.B * ‖P.fix A₀‖ ≤ 2 * ‖A₀‖ := by
      have : P.B * ‖P.fix A₀‖ ≤ P.B * (2 * P.κ * ‖A₀‖ ^ 2) := mul_le_mul_of_nonneg_left hD hB
      have h3 : P.κ * P.B * ‖A₀‖ ≤ 1 := by
        have : P.κ * P.B * ‖A₀‖ ≤ P.κ * P.B * P.a₃ :=
          mul_le_mul_of_nonneg_left hA₀ (by have := P.κ_nonneg; positivity)
        linarith
      nlinarith [norm_nonneg A₀]
    linarith
  -- `κ'‖T(A₀)‖B ≤ ½`
  have hTB : P.κ' * ‖P.T A₀‖ * P.B ≤ 1 / 2 := by
    have hT : ‖P.T A₀‖ ≤ (1 + P.B) * P.a₃ := P.norm_arg_le hA₀ hb
    have : P.κ' * ‖P.T A₀‖ * P.B ≤ P.κ' * (1 + P.B) ^ 2 * P.a₃ := by
      have h1 : P.κ' * ‖P.T A₀‖ * P.B ≤ P.κ' * ((1 + P.B) * P.a₃) * P.B :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hT hκ') hB
      have h2 : P.κ' * ((1 + P.B) * P.a₃) * P.B ≤ P.κ' * (1 + P.B) ^ 2 * P.a₃ := by
        have h0 : 0 ≤ P.κ' * ((1 + P.B) * P.a₃) := by positivity
        nlinarith
      linarith
    linarith [P.cond₃]
  set d := P.dfix A₀ δ
  have hd : w d ≤ P.κ' * ‖P.T A₀‖ * (v δ + P.B * w d) := by
    have := hw (δ - P.H d)
    rw [← P.dfix_eq hA₀ δ] at this
    refine this.trans (mul_le_mul_of_nonneg_left ((hv_sub _ _).trans (add_le_add le_rfl (hvH d)))
      (by positivity))
  have hd2 : w d ≤ 2 * P.κ' * ‖P.T A₀‖ * v δ := by
    have := mul_le_mul_of_nonneg_right hTB (hw0 d)
    linarith
  have hd6 : w d ≤ 6 * P.κ' * ‖A₀‖ * v δ := by
    have : 2 * P.κ' * ‖P.T A₀‖ * v δ ≤ 2 * P.κ' * (3 * ‖A₀‖) * v δ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hT3 (by positivity)) (hv0 δ)
    linarith
  refine ⟨hd6, ?_⟩
  -- `v(ε) ≤ v(δ) + Bw(𝔡) ≤ 4v(δ)`
  have h6 : 6 * P.κ' * P.B * ‖A₀‖ ≤ 3 := by
    have hκ'B : P.κ' * P.B * P.a₃ ≤ 1 / 2 := by
      have : P.κ' * P.B * P.a₃ ≤ P.κ' * (1 + P.B) ^ 2 * P.a₃ := by
        have : P.B ≤ (1 + P.B) ^ 2 := by nlinarith
        have h0 : 0 ≤ P.κ' * P.a₃ := by positivity
        nlinarith
      linarith [P.cond₃]
    have : P.κ' * P.B * ‖A₀‖ ≤ P.κ' * P.B * P.a₃ := mul_le_mul_of_nonneg_left hA₀ (by positivity)
    linarith
  have hv1 := (hv_sub δ (P.H d)).trans (add_le_add le_rfl (hvH d))
  have h7 : P.B * w d ≤ P.B * (6 * P.κ' * ‖A₀‖ * v δ) := mul_le_mul_of_nonneg_left hd6 hB
  have h8 := mul_le_mul_of_nonneg_right h6 (hv0 δ)
  linarith

/-- `prop:linearising`(i): `𝖣(A')` vanishes where `𝖢` does (on the bonds of `Γ₀`), for a linear `π₀` (the
restriction to those bonds) with `π₀𝖢 = 0` on the ball. -/
theorem fix_vanishes (π₀ : Y →ₗ[ℂ] Y) (hC₀ : ∀ A, ‖A‖ ≤ P.r₀ → π₀ (P.C A) = 0) {A' : X}
    (hA' : ‖A'‖ ≤ P.a₃) : π₀ (P.fix A') = 0 := by
  obtain ⟨hb, e, -⟩ := P.fix_spec hA'
  rw [e]
  exact hC₀ _ ((P.norm_arg_le hA' hb).trans P.cond₁)

/-- `‖T(A₀) - A₀‖ ≤ 2κB‖A₀‖²` and `‖T(A₀)‖ ≤ 3‖A₀‖`. -/
lemma norm_T_le {A₀ : X} (hA₀ : ‖A₀‖ ≤ P.a₃) :
    ‖P.T A₀ - A₀‖ ≤ 2 * P.κ * P.B * ‖A₀‖ ^ 2 ∧ ‖P.T A₀‖ ≤ 3 * ‖A₀‖ := by
  obtain ⟨-, -, hD⟩ := P.fix_spec hA₀
  have hB := P.B_nonneg
  have hκ := P.κ_nonneg
  have ha := P.a₃_pos
  have h1 : ‖P.T A₀ - A₀‖ ≤ 2 * P.κ * P.B * ‖A₀‖ ^ 2 := by
    have e : P.T A₀ - A₀ = -P.H (P.fix A₀) := by unfold T; abel
    rw [e, norm_neg]
    calc ‖P.H (P.fix A₀)‖ ≤ P.B * ‖P.fix A₀‖ := P.norm_H _
      _ ≤ P.B * (2 * P.κ * ‖A₀‖ ^ 2) := mul_le_mul_of_nonneg_left hD hB
      _ = 2 * P.κ * P.B * ‖A₀‖ ^ 2 := by ring
  refine ⟨h1, ?_⟩
  have hκB : P.κ * P.B * P.a₃ ≤ 1 := by
    have : P.κ * P.B * P.a₃ ≤ P.κ * (1 + P.B) ^ 2 * P.a₃ := by
      have : P.B ≤ (1 + P.B) ^ 2 := by nlinarith
      have h0 : 0 ≤ P.κ * P.a₃ := by positivity
      nlinarith
    linarith [P.cond₂]
  have h3 : P.κ * P.B * ‖A₀‖ ≤ 1 := by
    have : P.κ * P.B * ‖A₀‖ ≤ P.κ * P.B * P.a₃ := mul_le_mul_of_nonneg_left hA₀ (by positivity)
    linarith
  have h4 : 2 * P.κ * P.B * ‖A₀‖ ^ 2 ≤ 2 * ‖A₀‖ := by
    have := mul_le_mul_of_nonneg_right h3 (norm_nonneg A₀)
    nlinarith [norm_nonneg A₀]
  have := norm_add_le (P.T A₀ - A₀) A₀
  rw [sub_add_cancel] at this
  linarith

/-- `prop:linearising`(iii) for `𝖣₃ = 𝖣 - 𝖢⁽²⁾`, with `𝖢⁽²⁾(A) = B₂(A, A)` for a bilinear `B₂` and
`𝖢'(A) = 𝖢₃'(A) + 2B₂(A, ·)`: the derivative `𝔡₃ = 𝔡 - 2B₂(A₀, δ)` is
`2B₂(T(A₀) - A₀, δ) - 2B₂(T(A₀), H𝔡) + 𝖢₃'(T(A₀))(δ - H𝔡)`, and in a pair of weighted norms for which
`eq:remainder-second` (`w(2B₂(A, δ)) ≤ κ'‖A‖v(δ)`) and `eq:remainder-third`
(`w(𝖢₃'(T(A₀))δ) ≤ qκ'‖T(A₀)‖²v(δ)`, `q = 2L/c'₄`) hold,
`w(𝔡₃) ≤ κ'(2κB + 18κ'B + 36q)‖A₀‖²v(δ)`. -/
theorem dfix3_weighted (B₂ : X →L[ℂ] X →L[ℂ] Y) (C₃' : X → X →L[ℂ] Y)
    (hsplit : ∀ A δ, P.C' A δ = C₃' A δ + (2 : ℂ) • B₂ A δ) (w : Y → ℝ) (v : X → ℝ) {q : ℝ}
    (hq : 0 ≤ q) {A₀ : X} (hA₀ : ‖A₀‖ ≤ P.a₃)
    (hw : ∀ δ, w (P.C' (P.T A₀) δ) ≤ P.κ' * ‖P.T A₀‖ * v δ)
    (hB₂ : ∀ A δ, w ((2 : ℂ) • B₂ A δ) ≤ P.κ' * ‖A‖ * v δ)
    (hC₃ : ∀ δ, w (C₃' (P.T A₀) δ) ≤ q * P.κ' * ‖P.T A₀‖ ^ 2 * v δ)
    (hvH : ∀ ν, v (P.H ν) ≤ P.B * w ν) (hv_sub : ∀ x y, v (x - y) ≤ v x + v y) (hv0 : ∀ x, 0 ≤ v x)
    (hw0 : ∀ y, 0 ≤ w y) (hw_add : ∀ x y, w (x + y) ≤ w x + w y) (hw_neg : ∀ x, w (-x) = w x)
    (δ : X) :
    P.dfix A₀ δ - (2 : ℂ) • B₂ A₀ δ = (2 : ℂ) • B₂ (P.T A₀ - A₀) δ -
        (2 : ℂ) • B₂ (P.T A₀) (P.H (P.dfix A₀ δ)) + C₃' (P.T A₀) (δ - P.H (P.dfix A₀ δ)) ∧
      w (P.dfix A₀ δ - (2 : ℂ) • B₂ A₀ δ) ≤
        P.κ' * (2 * P.κ * P.B + 18 * P.κ' * P.B + 36 * q) * ‖A₀‖ ^ 2 * v δ := by
  set d := P.dfix A₀ δ
  set T₀ := P.T A₀
  have hform : d - (2 : ℂ) • B₂ A₀ δ = (2 : ℂ) • B₂ (T₀ - A₀) δ - (2 : ℂ) • B₂ T₀ (P.H d) +
      C₃' T₀ (δ - P.H d) := by
    have h : d = P.C' T₀ (δ - P.H d) := P.dfix_eq hA₀ δ
    rw [hsplit] at h
    conv_lhs => rw [h]
    simp only [map_sub, ContinuousLinearMap.sub_apply, smul_sub]
    abel
  refine ⟨hform, ?_⟩
  obtain ⟨hd6, hε4⟩ := P.dfix_weighted w v hA₀ hw hvH hv_sub hv0 hw0 δ
  obtain ⟨hTA, hT3⟩ := P.norm_T_le hA₀
  have hB := P.B_nonneg
  have hκ' := P.κ'_nonneg
  have hκ := P.κ_nonneg
  have hvδ := hv0 δ
  have hA := norm_nonneg A₀
  -- the three terms
  have t1 : w ((2 : ℂ) • B₂ (T₀ - A₀) δ) ≤ P.κ' * (2 * P.κ * P.B * ‖A₀‖ ^ 2) * v δ :=
    (hB₂ _ _).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hTA hκ') hvδ)
  have t2 : w ((2 : ℂ) • B₂ T₀ (P.H d)) ≤ P.κ' * (3 * ‖A₀‖) * (P.B * (6 * P.κ' * ‖A₀‖ * v δ)) := by
    refine (hB₂ _ _).trans ?_
    have hv : v (P.H d) ≤ P.B * (6 * P.κ' * ‖A₀‖ * v δ) :=
      (hvH d).trans (mul_le_mul_of_nonneg_left hd6 hB)
    exact mul_le_mul (mul_le_mul_of_nonneg_left hT3 hκ') hv (hv0 _) (by positivity)
  have t3 : w (C₃' T₀ (δ - P.H d)) ≤ q * P.κ' * (3 * ‖A₀‖) ^ 2 * (4 * v δ) := by
    refine (hC₃ _).trans ?_
    have hT2 : ‖T₀‖ ^ 2 ≤ (3 * ‖A₀‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hT3 2
    exact mul_le_mul (mul_le_mul_of_nonneg_left hT2 (by positivity)) hε4 (hv0 _) (by positivity)
  have hsum : w ((2 : ℂ) • B₂ (T₀ - A₀) δ - (2 : ℂ) • B₂ T₀ (P.H d) + C₃' T₀ (δ - P.H d)) ≤
      w ((2 : ℂ) • B₂ (T₀ - A₀) δ) + w ((2 : ℂ) • B₂ T₀ (P.H d)) + w (C₃' T₀ (δ - P.H d)) := by
    refine (hw_add _ _).trans (add_le_add ?_ le_rfl)
    rw [sub_eq_add_neg]
    exact (hw_add _ _).trans (add_le_add le_rfl (le_of_eq (hw_neg _)))
  rw [hform]
  refine hsum.trans ?_
  have e : P.κ' * (2 * P.κ * P.B * ‖A₀‖ ^ 2) * v δ +
      P.κ' * (3 * ‖A₀‖) * (P.B * (6 * P.κ' * ‖A₀‖ * v δ)) + q * P.κ' * (3 * ‖A₀‖) ^ 2 * (4 * v δ) =
      P.κ' * (2 * P.κ * P.B + 18 * P.κ' * P.B + 36 * q) * ‖A₀‖ ^ 2 * v δ := by ring
  linarith

end Data

end Linearising

end CoreLean
