/-
`lem:current-expansion`(i) of BALABAN_CORE.tex, the matrix estimates of the step "the curvature of the
product".

With `E = e^{iY₁}e^{iY₂}`, `E' = e^{iY₃}e^{iY₄}`, `s = Σ‖Y_k‖ ≤ 1/8`, and `W` with `‖W - 1‖ ≤ ω`,
`‖W⁻¹ - 1‖ ≤ 2ω`:
`‖Im(EWE') - Im W - Im(EE')‖ ≤ 4sω` (`norm_imW_three_le`, from the identities
`EWE' - W - (EE' - 1) = (E - 1)(W - 1)E' + (W - 1)(E' - 1)` and the same for the inverses), and
`‖Im(EE') - S - (i/2)C‖ ≤ φ₃(s) ≤ s³/5` with `S = ΣY_k`, `C = Σ_{k<l}[Y_k, Y_l]` (`norm_imW_four_le`,
from `eq:four-exponentials` for the product and its inverse); `Im X = (X - X⁻¹)/(2i)`.
-/
import CoreLean.ProductExp
import CoreLean.CurrentExpansion
import CoreLean.Hessian

open NormedSpace Matrix
open scoped Nat
open scoped Matrix.Norms.L2Operator

namespace CoreLean

/-! ### Scalar bounds -/

lemma exp_eighth_le : Real.exp (1 / 8) ≤ 8 / 7 := by
  have h := Real.add_one_le_exp (-(1 / 8))
  have hpos := Real.exp_pos (1 / 8)
  have e : Real.exp (-(1 / 8)) * Real.exp (1 / 8) = 1 := by rw [← Real.exp_add]; norm_num
  nlinarith

/-- `e^s - 1 ≤ (8/7)s` for `0 ≤ s ≤ 1/8`. -/
lemma exp_sub_one_le_eighth {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1 / 8) : Real.exp s - 1 ≤ 8 / 7 * s := by
  have h := Real.add_one_le_exp (-s)
  have hpos := Real.exp_pos s
  have e : Real.exp (-s) * Real.exp s = 1 := by rw [← Real.exp_add]; norm_num
  have hes : Real.exp s ≤ 8 / 7 := (Real.exp_le_exp.mpr h1).trans exp_eighth_le
  -- `(1 - s)e^s ≤ 1`, so `e^s - 1 ≤ se^s ≤ (8/7)s`
  have h2 : (1 - s) * Real.exp s ≤ 1 := by nlinarith
  nlinarith

/-- `φ₃(s) = e^s - 1 - s - s²/2 ≤ s³/5` for `0 ≤ s ≤ 1/8`. -/
lemma phi3_le_fifth {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1 / 8) : phi3 s ≤ s ^ 3 / 5 := by
  have hE := BakerCampbellHausdorff.hasSum_real_exp s
  have h3 := (hasSum_nat_add_iff' 3).mpr hE
  have e3 : ∑ i ∈ Finset.range 3, (i ! : ℝ)⁻¹ • s ^ i = 1 + s + s ^ 2 / 2 := by
    simp [Finset.sum_range_succ, Nat.factorial]; ring
  rw [e3] at h3
  have hB := (BakerCampbellHausdorff.hasSum_real_exp s).mul_left (s ^ 3 / 6)
  have hphi : phi3 s = Real.exp s - (1 + s + s ^ 2 / 2) := by unfold phi3; ring
  have hle : phi3 s ≤ s ^ 3 / 6 * Real.exp s := by
    rw [hphi]
    refine hasSum_le (fun k => ?_) h3 hB
    simp only [smul_eq_mul]
    have hk : ((k + 3)! : ℝ)⁻¹ ≤ (6 : ℝ)⁻¹ * (k ! : ℝ)⁻¹ := by
      rw [← mul_inv]
      refine inv_anti₀ (by positivity) ?_
      have : 6 * k ! ≤ (k + 3)! := by
        have e : (k + 3)! = (k + 3) * ((k + 2) * ((k + 1) * k !)) := by
          rw [show k + 3 = (k + 2) + 1 from rfl, Nat.factorial_succ,
            show k + 2 = (k + 1) + 1 from rfl, Nat.factorial_succ, Nat.factorial_succ]
        rw [e]
        have h6 : 6 ≤ (k + 3) * ((k + 2) * (k + 1)) :=
          Nat.mul_le_mul (by omega : 3 ≤ k + 3) (Nat.mul_le_mul (by omega : 2 ≤ k + 2) (by omega : 1 ≤ k + 1))
        calc 6 * k ! ≤ ((k + 3) * ((k + 2) * (k + 1))) * k ! := Nat.mul_le_mul_right _ h6
          _ = (k + 3) * ((k + 2) * ((k + 1) * k !)) := by ring
      exact_mod_cast this
    have hsk : 0 ≤ s ^ (k + 3) := by positivity
    calc ((k + 3)! : ℝ)⁻¹ * s ^ (k + 3) ≤ (6 : ℝ)⁻¹ * (k ! : ℝ)⁻¹ * s ^ (k + 3) :=
          mul_le_mul_of_nonneg_right hk hsk
      _ = s ^ 3 / 6 * ((k ! : ℝ)⁻¹ * s ^ k) := by ring
  have hes : Real.exp s ≤ 6 / 5 :=
    (Real.exp_le_exp.mpr h1).trans (exp_eighth_le.trans (by norm_num))
  have hs3 : 0 ≤ s ^ 3 := by positivity
  calc phi3 s ≤ s ^ 3 / 6 * Real.exp s := hle
    _ ≤ s ^ 3 / 6 * (6 / 5) := by gcongr
    _ = s ^ 3 / 5 := by ring

variable {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "GLN" => (Matrix (Fin N) (Fin N) ℂ)ˣ

/-! ### The three factors -/

lemma norm_inv_two_I : ‖(1 / (2 * Complex.I) : ℂ)‖ = 1 / 2 := by
  rw [norm_div, norm_one, norm_mul, Complex.norm_I]; norm_num

/-- `‖Im(EWE') - Im W - Im(EE')‖ ≤ 4sω`. -/
theorem norm_imW_three_le (E W E' : GLN) {s ω : ℝ} (hs : 0 ≤ s) (hω : 0 ≤ ω)
    (hE : ‖(E : Mat)‖ ≤ 8 / 7) (hE' : ‖(E' : Mat)‖ ≤ 8 / 7) (hEi : ‖((E⁻¹ : GLN) : Mat)‖ ≤ 8 / 7)
    (hE1 : ‖(E : Mat) - 1‖ ≤ 8 / 7 * s) (hE'1 : ‖(E' : Mat) - 1‖ ≤ 8 / 7 * s)
    (hEi1 : ‖((E⁻¹ : GLN) : Mat) - 1‖ ≤ 8 / 7 * s) (hE'i1 : ‖((E'⁻¹ : GLN) : Mat) - 1‖ ≤ 8 / 7 * s)
    (hW : ‖(W : Mat) - 1‖ ≤ ω) (hWi : ‖((W⁻¹ : GLN) : Mat) - 1‖ ≤ 2 * ω) :
    ‖imW (E * W * E') - imW W - imW (E * E')‖ ≤ 4 * s * ω := by
  have hinv1 : (((E * W * E')⁻¹ : GLN) : Mat) =
      ((E'⁻¹ : GLN) : Mat) * ((W⁻¹ : GLN) : Mat) * ((E⁻¹ : GLN) : Mat) := by
    simp only [_root_.mul_inv_rev, Units.val_mul, mul_assoc]
  have hinv2 : (((E * E')⁻¹ : GLN) : Mat) = ((E'⁻¹ : GLN) : Mat) * ((E⁻¹ : GLN) : Mat) := by
    simp only [_root_.mul_inv_rev, Units.val_mul]
  have hkey : imW (E * W * E') - imW W - imW (E * E') = (1 / (2 * Complex.I) : ℂ) •
      (((E : Mat) * W * E' - W - ((E : Mat) * E' - 1)) -
        (((E'⁻¹ : GLN) : Mat) * ((W⁻¹ : GLN) : Mat) * ((E⁻¹ : GLN) : Mat) - ((W⁻¹ : GLN) : Mat) -
          (((E'⁻¹ : GLN) : Mat) * ((E⁻¹ : GLN) : Mat) - 1))) := by
    simp only [imW, Units.val_mul, hinv1, hinv2]
    rw [← smul_sub, ← smul_sub]
    congr 1
    abel
  rw [hkey, norm_smul, norm_inv_two_I]
  generalize (E : Mat) = e at hE hE1 ⊢
  generalize (E' : Mat) = e' at hE' hE'1 ⊢
  generalize (W : Mat) = w at hW ⊢
  generalize ((E⁻¹ : GLN) : Mat) = ei at hEi hEi1 ⊢
  generalize ((E'⁻¹ : GLN) : Mat) = ei' at hE'i1 ⊢
  generalize ((W⁻¹ : GLN) : Mat) = wi at hWi ⊢
  have e1 : e * w * e' - w - (e * e' - 1) = (e - 1) * (w - 1) * e' + (w - 1) * (e' - 1) := by
    noncomm_ring
  have e2 : ei' * wi * ei - wi - (ei' * ei - 1) =
      (ei' - 1) * (wi - 1) * ei + (wi - 1) * (ei - 1) := by noncomm_ring
  rw [e1, e2]
  have b1 : ‖(e - 1) * (w - 1) * e' + (w - 1) * (e' - 1)‖ ≤ 120 / 49 * s * ω := by
    refine (norm_add_le _ _).trans ?_
    have t1 : ‖(e - 1) * (w - 1) * e'‖ ≤ 8 / 7 * s * ω * (8 / 7) :=
      (opNorm_mul_le _ _).trans (mul_le_mul ((opNorm_mul_le _ _).trans
        (mul_le_mul hE1 hW (norm_nonneg _) (by positivity))) hE' (norm_nonneg _) (by positivity))
    have t2 : ‖(w - 1) * (e' - 1)‖ ≤ ω * (8 / 7 * s) :=
      (opNorm_mul_le _ _).trans (mul_le_mul hW hE'1 (norm_nonneg _) hω)
    nlinarith
  have b2 : ‖(ei' - 1) * (wi - 1) * ei + (wi - 1) * (ei - 1)‖ ≤ 240 / 49 * s * ω := by
    refine (norm_add_le _ _).trans ?_
    have t1 : ‖(ei' - 1) * (wi - 1) * ei‖ ≤ 8 / 7 * s * (2 * ω) * (8 / 7) :=
      (opNorm_mul_le _ _).trans (mul_le_mul ((opNorm_mul_le _ _).trans
        (mul_le_mul hE'i1 hWi (norm_nonneg _) (by positivity))) hEi (norm_nonneg _) (by positivity))
    have t2 : ‖(wi - 1) * (ei - 1)‖ ≤ 2 * ω * (8 / 7 * s) :=
      (opNorm_mul_le _ _).trans (mul_le_mul hWi hEi1 (norm_nonneg _) (by positivity))
    nlinarith
  calc 1 / 2 * ‖(e - 1) * (w - 1) * e' + (w - 1) * (e' - 1) -
        ((ei' - 1) * (wi - 1) * ei + (wi - 1) * (ei - 1))‖
      ≤ 1 / 2 * (120 / 49 * s * ω + 240 / 49 * s * ω) := by
        gcongr
        exact (norm_sub_le _ _).trans (add_le_add b1 b2)
    _ ≤ 4 * s * ω := by nlinarith [mul_nonneg hs hω]

/-! ### The four exponentials -/

/-- `Im(e^{iY₁}e^{iY₂}e^{iY₃}e^{iY₄}) = S + (i/2)C` up to `φ₃(Σ‖Y_k‖)`. -/
theorem norm_imW_four_le (Y₁ Y₂ Y₃ Y₄ : Mat) :
    ‖imW (expU (Complex.I • Y₁) * expU (Complex.I • Y₂) * expU (Complex.I • Y₃) *
        expU (Complex.I • Y₄)) -
      ((Y₁ + Y₂ + Y₃ + Y₄) + (Complex.I / 2) •
        ((Y₁ * Y₂ - Y₂ * Y₁) + (Y₁ * Y₃ - Y₃ * Y₁) + (Y₁ * Y₄ - Y₄ * Y₁) +
          (Y₂ * Y₃ - Y₃ * Y₂) + (Y₂ * Y₄ - Y₄ * Y₂) + (Y₃ * Y₄ - Y₄ * Y₃)))‖ ≤
      phi3 (‖Y₁‖ + ‖Y₂‖ + ‖Y₃‖ + ‖Y₄‖) := by
  set P : GLN := expU (Complex.I • Y₁) * expU (Complex.I • Y₂) * expU (Complex.I • Y₃) *
    expU (Complex.I • Y₄)
  set S := Y₁ + Y₂ + Y₃ + Y₄
  set C := (Y₁ * Y₂ - Y₂ * Y₁) + (Y₁ * Y₃ - Y₃ * Y₁) + (Y₁ * Y₄ - Y₄ * Y₁) +
    (Y₂ * Y₃ - Y₃ * Y₂) + (Y₂ * Y₄ - Y₄ * Y₂) + (Y₃ * Y₄ - Y₄ * Y₃)
  set Q : Mat := exp (Complex.I • -Y₄) * exp (Complex.I • -Y₃) * exp (Complex.I • -Y₂) *
    exp (Complex.I • -Y₁)
  have hPval : (P : Mat) = exp (Complex.I • Y₁) * exp (Complex.I • Y₂) * exp (Complex.I • Y₃) *
      exp (Complex.I • Y₄) := by simp [P]
  have hPinv : ((P⁻¹ : GLN) : Mat) = Q :=
    Units.inv_eq_of_mul_eq_one_right (by rw [hPval]; exact four_exp_inv Y₁ Y₂ Y₃ Y₄)
  have h1 := norm_four_exp_sub_le Y₁ Y₂ Y₃ Y₄
  have h2 := norm_four_exp_inv_sub_le Y₁ Y₂ Y₃ Y₄
  rw [← hPval] at h1
  set T₁ : Mat := 1 + Complex.I • S - (2 : ℂ)⁻¹ • S ^ 2 - (2 : ℂ)⁻¹ • C
  set T₂ : Mat := 1 + Complex.I • -S - (2 : ℂ)⁻¹ • (-S) ^ 2 - (2 : ℂ)⁻¹ • -C
  -- `(T₁ - T₂)/(2i) = S + (i/2)C`, since `T₁ - T₂ = 2iS - C` and `-1/(2i) = i/2`
  have e : (1 / (2 * Complex.I) : ℂ) • (T₁ - T₂) = S + (Complex.I / 2) • C := by
    have hT : T₁ - T₂ = (2 * Complex.I) • S - C := by
      simp only [T₁, T₂, neg_sq, smul_neg, mul_smul, two_smul]
      module
    have hc1 : (1 / (2 * Complex.I) : ℂ) * (2 * Complex.I) = 1 := by
      rw [one_div, inv_mul_cancel₀ (by simp [Complex.I_ne_zero])]
    have hc2 : -(1 / (2 * Complex.I) : ℂ) = Complex.I / 2 := by
      rw [one_div, mul_inv, Complex.inv_I]; ring
    rw [hT, smul_sub, smul_smul, hc1, one_smul, sub_eq_add_neg, ← neg_smul, hc2]
  have hkey : imW P - (S + (Complex.I / 2) • C) =
      (1 / (2 * Complex.I) : ℂ) • (((P : Mat) - T₁) - (Q - T₂)) := by
    rw [← e]
    simp only [imW, hPinv]
    rw [← smul_sub]
    congr 1
    abel
  rw [hkey, norm_smul, norm_inv_two_I]
  have hT₂ : ‖Q - T₂‖ ≤ phi3 (‖Y₁‖ + ‖Y₂‖ + ‖Y₃‖ + ‖Y₄‖) := by
    convert h2 using 2
  calc 1 / 2 * ‖(P : Mat) - T₁ - (Q - T₂)‖
      ≤ 1 / 2 * (phi3 (‖Y₁‖ + ‖Y₂‖ + ‖Y₃‖ + ‖Y₄‖) + phi3 (‖Y₁‖ + ‖Y₂‖ + ‖Y₃‖ + ‖Y₄‖)) := by
        gcongr
        exact (norm_sub_le _ _).trans (add_le_add h1 hT₂)
    _ = phi3 (‖Y₁‖ + ‖Y₂‖ + ‖Y₃‖ + ‖Y₄‖) := by ring

/-! ### The bounds of `e^{iY₁}e^{iY₂}` -/

lemma norm_exp_pair_sub_one {Y₁ Y₂ : Mat} {s : ℝ} (hs : ‖Y₁‖ + ‖Y₂‖ ≤ s) (hs8 : s ≤ 1 / 8) :
    ‖exp (Complex.I • Y₁) * exp (Complex.I • Y₂) - 1‖ ≤ 8 / 7 * s := by
  have h := BakerCampbellHausdorff.norm_exp_mul_exp_sub_one_le ℂ (Complex.I • Y₁) (Complex.I • Y₂)
  rw [norm_I_smul, norm_I_smul] at h
  have h0 : 0 ≤ ‖Y₁‖ + ‖Y₂‖ := by positivity
  exact h.trans ((sub_le_sub_right (Real.exp_le_exp.mpr hs) 1).trans
    (exp_sub_one_le_eighth (h0.trans hs) hs8))

/-- `E = e^{iY₁}e^{iY₂}` and `E⁻¹` have norms at most `8/7` and differ from `1` by at most `(8/7)s`. -/
lemma exp_pair_bounds (Y₁ Y₂ : Mat) {s : ℝ} (hs : ‖Y₁‖ + ‖Y₂‖ ≤ s) (hs8 : s ≤ 1 / 8) :
    ‖((expU (Complex.I • Y₁) * expU (Complex.I • Y₂) : GLN) : Mat)‖ ≤ 8 / 7 ∧
      ‖((expU (Complex.I • Y₁) * expU (Complex.I • Y₂) : GLN) : Mat) - 1‖ ≤ 8 / 7 * s ∧
      ‖(((expU (Complex.I • Y₁) * expU (Complex.I • Y₂))⁻¹ : GLN) : Mat)‖ ≤ 8 / 7 ∧
      ‖(((expU (Complex.I • Y₁) * expU (Complex.I • Y₂))⁻¹ : GLN) : Mat) - 1‖ ≤ 8 / 7 * s := by
  have h0 : 0 ≤ s := (by positivity : (0 : ℝ) ≤ ‖Y₁‖ + ‖Y₂‖).trans hs
  have hinv : (((expU (Complex.I • Y₁) * expU (Complex.I • Y₂))⁻¹ : GLN) : Mat) =
      exp (Complex.I • -Y₂) * exp (Complex.I • -Y₁) := by
    rw [_root_.mul_inv_rev, expU_inv, expU_inv, Units.val_mul, expU_val, expU_val, smul_neg,
      smul_neg]
  have h1 : ‖((expU (Complex.I • Y₁) * expU (Complex.I • Y₂) : GLN) : Mat) - 1‖ ≤ 8 / 7 * s := by
    rw [Units.val_mul, expU_val, expU_val]
    exact norm_exp_pair_sub_one hs hs8
  have h2 : ‖(((expU (Complex.I • Y₁) * expU (Complex.I • Y₂))⁻¹ : GLN) : Mat) - 1‖ ≤ 8 / 7 * s := by
    rw [hinv]
    exact norm_exp_pair_sub_one (by rw [norm_neg, norm_neg]; linarith) hs8
  have hb : ∀ X : Mat, ‖X - 1‖ ≤ 8 / 7 * s → ‖X‖ ≤ 8 / 7 := fun X hX => by
    calc ‖X‖ = ‖(X - 1) + 1‖ := by rw [sub_add_cancel]
      _ ≤ ‖X - 1‖ + ‖(1 : Mat)‖ := norm_add_le _ _
      _ ≤ 8 / 7 * s + 1 := add_le_add hX opNorm_one_le
      _ ≤ 8 / 7 := by linarith
  exact ⟨hb _ h1, h1, hb _ h2, h2⟩

/-! ### The curvature of the product at a plaquette -/

section Plaquette

variable {n : ℕ} [NeZero n] (a : ℂ) {G : GaugeGroup N}

lemma proj_of_mem [NeZero N] (hG : G.LieInput) {Y : Mat} (hY : Y ∈ G.lieC) : piProj hG Y = Y :=
  proj_eq hG hY fun Z _ => by simp [ntr]

set_option maxHeartbeats 2000000 in
/-- `eq:curvature-product`: at the plaquette `p = p_{μν}(x)`, with `‖A_μ(x)‖, ‖A_ν(x)‖ ≤ m₀`, the
transported values `A₂, A₃` of norms at most `2m₀`, `‖D_{𝐔,μ}A_ν(x)‖, ‖D_{𝐔,ν}A_μ(x)‖ ≤ m₁`,
`‖𝐔(∂p) - 1‖ ≤ ω ≤ 1/48`, and `|a|m₀ ≤ 1/48`,
`Θ_{μν}(x) = F(e^{iaA}𝐔)_{μν}(x) - F(𝐔)_{μν}(x) - (D_𝐔A)_{μν}(x) = i[A_μ(x), A_ν(x)] + Θ'` with
`‖Θ'‖ ≤ √N|a|(6m₀m₁ + |a|m₁² + 44m₀³ + 24m₀|a|⁻²ω)`. -/
theorem curvature_product [NeZero N] (hG : G.LieInput) (ha : a ≠ 0) (U : Config N n)
    (hU : ∀ μ x, U μ x ∈ G.complexified) (A : Form1 N n) (hA : ∀ μ x, A μ x ∈ G.lieC)
    (μ ν : Fin 4) (x : Site n) {m₀ m₁ ω : ℝ}
    (h1 : ‖A μ x‖ ≤ m₀) (h4 : ‖A ν x‖ ≤ m₀) (h2 : ‖Ad (U μ x) (A ν (x + unit n μ))‖ ≤ 2 * m₀)
    (h3 : ‖Ad (U ν x) (-A μ (x + unit n ν))‖ ≤ 2 * m₀)
    (hd1 : ‖Dfw a U μ (A ν) x‖ ≤ m₁) (hd2 : ‖Dfw a U ν (A μ) x‖ ≤ m₁)
    (hω : ‖((plaq U μ ν x : GLN) : Mat) - 1‖ ≤ ω) (hω1 : ω ≤ 1 / 48) (hηm : ‖a‖ * m₀ ≤ 1 / 48) :
    ‖curv a hG (expMul a A U) μ ν x - curv a hG U μ ν x - D1 a U A μ ν x -
        Complex.I • (A μ x * A ν x - A ν x * A μ x)‖ ≤
      Real.sqrt N * ‖a‖ * (6 * m₀ * m₁ + ‖a‖ * m₁ ^ 2 + 44 * m₀ ^ 3 + 24 * m₀ * (‖a‖⁻¹ ^ 2 * ω)) := by
  -- the exponents and the matrices `E`, `E'`, `W`
  set A₁ := A μ x
  set A₂ := Ad (U μ x) (A ν (x + unit n μ))
  set A₃ := Ad (U ν x) (-A μ (x + unit n ν))
  set A₄ := -A ν x
  set Y₁ := a • A₁
  set Y₂ := a • A₂
  set Y₃ := a • A₃
  set Y₄ := a • A₄
  set W := plaq U μ ν x
  set E : GLN := expU (Complex.I • Y₁) * expU (Complex.I • Y₂)
  set E' : GLN := expU (Complex.I • Y₃) * expU (Complex.I • Y₄)
  have hm0 : 0 ≤ m₀ := (norm_nonneg _).trans h1
  have hω0 : 0 ≤ ω := (norm_nonneg _).trans hω
  have hη : 0 < ‖a‖ := norm_pos_iff.mpr ha
  set s := ‖Y₁‖ + ‖Y₂‖ + ‖Y₃‖ + ‖Y₄‖
  have hs : s ≤ 6 * (‖a‖ * m₀) := by
    simp only [s, Y₁, Y₂, Y₃, Y₄, norm_smul, A₄, norm_neg]
    nlinarith [norm_nonneg a]
  have hs0 : 0 ≤ s := by positivity
  have hs8 : s ≤ 1 / 8 := by linarith
  -- `𝐔'(∂p) = EWE'`
  have hplaq : plaq (expMul a A U) μ ν x = E * W * E' := by
    rw [plaq_expMul]
    simp only [E, E', W, Y₁, Y₂, Y₃, Y₄, A₁, A₂, A₃, A₄, mul_smul, mul_assoc]
  -- the bounds of `E`, `E'`, `W⁻¹`
  obtain ⟨hE, hE1, hEi, hEi1⟩ := exp_pair_bounds Y₁ Y₂ (s := s) (by simp only [s]; linarith [norm_nonneg Y₃, norm_nonneg Y₄]) hs8
  obtain ⟨hE', hE'1, hE'i, hE'i1⟩ := exp_pair_bounds Y₃ Y₄ (s := s) (by simp only [s]; linarith [norm_nonneg Y₁, norm_nonneg Y₂]) hs8
  have hWi : ‖((W⁻¹ : GLN) : Mat) - 1‖ ≤ 2 * ω := by
    have hinv := norm_inv_le W (by linarith)
    have e : ((W⁻¹ : GLN) : Mat) - 1 = -(((W⁻¹ : GLN) : Mat) * ((W : Mat) - 1)) := by
      rw [mul_sub, mul_one, ← Units.val_mul, inv_mul_cancel, Units.val_one]; abel
    rw [e, norm_neg]
    have hWin : ‖((W⁻¹ : GLN) : Mat)‖ ≤ 2 := by
      have : (0 : ℝ) < 1 - ‖(W : Mat) - 1‖ := by linarith
      nlinarith [norm_nonneg ((W⁻¹ : GLN) : Mat)]
    calc ‖((W⁻¹ : GLN) : Mat) * ((W : Mat) - 1)‖ ≤ ‖((W⁻¹ : GLN) : Mat)‖ * ‖(W : Mat) - 1‖ :=
          opNorm_mul_le _ _
      _ ≤ 2 * ω := mul_le_mul hWin hω (norm_nonneg _) (by norm_num)
  -- the two estimates of the imaginary parts
  have hR₁ := norm_imW_three_le E W E' hs0 hω0 hE hE' hEi hE1 hE'1 hEi1 hE'i1 hω hWi
  have hR₂ := norm_imW_four_le Y₁ Y₂ Y₃ Y₄
  have hEE' : E * E' = expU (Complex.I • Y₁) * expU (Complex.I • Y₂) * expU (Complex.I • Y₃) *
      expU (Complex.I • Y₄) := by simp only [E, E', mul_assoc]
  rw [← hEE'] at hR₂
  -- the sum of the exponents and the commutators
  have hS : Y₁ + Y₂ + Y₃ + Y₄ = (a * a) • D1 a U A μ ν x := by
    have := productExponent_sum a ha A U μ ν x
    simp only [Y₁, Y₂, Y₃, Y₄, A₁, A₂, A₃, A₄, ← smul_add, this, smul_smul]
  set Cm : Mat := (A₁ * A₂ - A₂ * A₁) + (A₁ * A₃ - A₃ * A₁) + (A₁ * A₄ - A₄ * A₁) +
    (A₂ * A₃ - A₃ * A₂) + (A₂ * A₄ - A₄ * A₂) + (A₃ * A₄ - A₄ * A₃)
  have hC : (Y₁ * Y₂ - Y₂ * Y₁) + (Y₁ * Y₃ - Y₃ * Y₁) + (Y₁ * Y₄ - Y₄ * Y₁) +
      (Y₂ * Y₃ - Y₃ * Y₂) + (Y₂ * Y₄ - Y₄ * Y₂) + (Y₃ * Y₄ - Y₄ * Y₃) = (a * a) • Cm := by
    simp only [Y₁, Y₂, Y₃, Y₄, Cm, smul_mul_smul_comm, ← smul_sub, ← smul_add]
  rw [hS, hC] at hR₂
  -- the members of `𝔤^c`
  have hmem1 : A₁ ∈ G.lieC := hA μ x
  have hmem2 : A₂ ∈ G.lieC := GaugeGroup.Ad_mem_lieC hG (hU μ x) (hA ν _)
  have hmem3 : A₃ ∈ G.lieC := GaugeGroup.Ad_mem_lieC hG (hU ν x)
    ((GaugeGroup.lieCSubmodule hG).neg_mem (hA μ _))
  have hmem4 : A₄ ∈ G.lieC := (GaugeGroup.lieCSubmodule hG).neg_mem (hA ν x)
  have hcm : ∀ X Y : Mat, X ∈ G.lieC → Y ∈ G.lieC → X * Y - Y * X ∈ G.lieC :=
    fun X Y hX hY => GaugeGroup.commutator_mem_lieC hG hX hY
  have hCm : Cm ∈ G.lieC := by
    have L := GaugeGroup.lieCSubmodule hG
    simp only [Cm]
    exact (GaugeGroup.lieCSubmodule hG).add_mem ((GaugeGroup.lieCSubmodule hG).add_mem
      ((GaugeGroup.lieCSubmodule hG).add_mem ((GaugeGroup.lieCSubmodule hG).add_mem
        ((GaugeGroup.lieCSubmodule hG).add_mem (hcm _ _ hmem1 hmem2) (hcm _ _ hmem1 hmem3))
        (hcm _ _ hmem1 hmem4)) (hcm _ _ hmem2 hmem3)) (hcm _ _ hmem2 hmem4)) (hcm _ _ hmem3 hmem4)
  have hD1 : D1 a U A μ ν x ∈ G.lieC := D1_mem a hG hU hA μ ν x
  -- `Θ - i[A_μ, A_ν] = a⁻²π(R₁ + R₂) + (i/2)(Cm - 2[A_μ, A_ν])`
  set R₁ := imW (E * W * E') - imW W - imW (E * E')
  set R₂ := imW (E * E') - ((a * a) • D1 a U A μ ν x + (Complex.I / 2) • ((a * a) • Cm))
  have ha2 : a ^ 2 ≠ 0 := pow_ne_zero 2 ha
  have hpsub : ∀ X Y : Mat, piProj hG X - piProj hG Y = piProj hG (X - Y) := by
    intro X Y
    rw [sub_eq_add_neg X Y, ← neg_one_smul ℂ Y, proj_add, proj_smul, neg_one_smul, ← sub_eq_add_neg]
  have hdiff : imW (E * W * E') - imW W =
      (R₁ + R₂) + (a ^ 2) • D1 a U A μ ν x + (Complex.I / 2) • ((a ^ 2) • Cm) := by
    simp only [R₁, R₂, sq]
    abel
  have hθ : curv a hG (expMul a A U) μ ν x - curv a hG U μ ν x - D1 a U A μ ν x -
      Complex.I • (A μ x * A ν x - A ν x * A μ x) =
      (a ^ 2)⁻¹ • piProj hG (R₁ + R₂) +
        (Complex.I / 2) • (Cm - (2 : ℂ) • (A μ x * A ν x - A ν x * A μ x)) := by
    simp only [curv]
    rw [hplaq, ← smul_sub, hpsub, hdiff, proj_add, proj_add, proj_smul, proj_smul, proj_smul,
      proj_of_mem hG hD1, proj_of_mem hG hCm, smul_add, smul_add, inv_smul_smul₀ ha2,
      smul_comm (a ^ 2)⁻¹ (Complex.I / 2), inv_smul_smul₀ ha2]
    module
  -- the commutators: `Cm - 2[A_μ, A_ν] = a X - a²[D_μA_ν, D_νA_μ]`
  set P := A μ x
  set Q := A ν x
  set dQ := Dfw a U μ (A ν) x
  set dP := Dfw a U ν (A μ) x
  have hA2 : A₂ = Q + a • dQ := productExponent_two a ha A U μ ν x
  have hA3 : A₃ = -P - a • dP := productExponent_three a ha A U μ ν x
  set Xc : Mat := (2 : ℂ) • (P * dQ - dQ * P) + (2 : ℂ) • (dP * Q - Q * dP) - (P * dP - dP * P) -
    (dQ * Q - Q * dQ)
  have hCm2 : Cm - (2 : ℂ) • (P * Q - Q * P) = a • Xc - (a * a) • (dQ * dP - dP * dQ) := by
    simp only [Cm, hA2, hA3, A₁, A₄, Xc]
    simp only [add_mul, mul_add, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, neg_mul, mul_neg,
      smul_sub, smul_add, smul_smul, neg_neg]
    module
  -- the norms
  have hcomm : ∀ X Y : Mat, ‖X * Y - Y * X‖ ≤ 2 * ‖X‖ * ‖Y‖ := fun X Y => by
    calc ‖X * Y - Y * X‖ ≤ ‖X * Y‖ + ‖Y * X‖ := norm_sub_le _ _
      _ ≤ ‖X‖ * ‖Y‖ + ‖Y‖ * ‖X‖ := add_le_add (opNorm_mul_le _ _) (opNorm_mul_le _ _)
      _ = 2 * ‖X‖ * ‖Y‖ := by ring
  have hm1 : 0 ≤ m₁ := (norm_nonneg _).trans hd1
  have hXc : ‖Xc‖ ≤ 12 * m₀ * m₁ := by
    have t1 := hcomm P dQ
    have t2 := hcomm dP Q
    have t3 := hcomm P dP
    have t4 := hcomm dQ Q
    simp only [Xc]
    have e2 : ‖(2 : ℂ)‖ = 2 := by norm_num
    calc ‖(2 : ℂ) • (P * dQ - dQ * P) + (2 : ℂ) • (dP * Q - Q * dP) - (P * dP - dP * P) -
          (dQ * Q - Q * dQ)‖
        ≤ 2 * ‖P * dQ - dQ * P‖ + 2 * ‖dP * Q - Q * dP‖ + ‖P * dP - dP * P‖ +
            ‖dQ * Q - Q * dQ‖ := by
          refine (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add
            ((norm_add_le _ _).trans (le_of_eq ?_)) le_rfl)) le_rfl)
          rw [norm_smul, norm_smul, e2]
      _ ≤ 2 * (2 * m₀ * m₁) + 2 * (2 * m₁ * m₀) + 2 * m₀ * m₁ + 2 * m₁ * m₀ := by
          gcongr
          · exact t1.trans (by gcongr)
          · exact t2.trans (by gcongr)
          · exact t3.trans (by gcongr)
          · exact t4.trans (by gcongr)
      _ = 12 * m₀ * m₁ := by ring
  have hYc : ‖dQ * dP - dP * dQ‖ ≤ 2 * m₁ ^ 2 :=
    (hcomm dQ dP).trans (by nlinarith [norm_nonneg dQ, norm_nonneg dP])
  have hsqrt : 1 ≤ Real.sqrt N := by
    rw [Real.one_le_sqrt]; exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hphi := phi3_le_fifth hs0 hs8
  have hRs : ‖R₁ + R₂‖ ≤ 4 * s * ω + s ^ 3 / 5 :=
    (norm_add_le _ _).trans (add_le_add hR₁ (hR₂.trans hphi))
  rw [hθ, hCm2]
  calc ‖(a ^ 2)⁻¹ • piProj hG (R₁ + R₂) +
        (Complex.I / 2) • (a • Xc - (a * a) • (dQ * dP - dP * dQ))‖
      ≤ ‖a‖⁻¹ ^ 2 * (Real.sqrt N * (4 * s * ω + s ^ 3 / 5)) +
          1 / 2 * (‖a‖ * (12 * m₀ * m₁) + ‖a‖ * ‖a‖ * (2 * m₁ ^ 2)) := by
        refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [norm_smul, norm_inv, norm_pow, inv_pow]
          exact mul_le_mul_of_nonneg_left ((opNorm_proj_le hG _).trans
            (mul_le_mul_of_nonneg_left hRs (Real.sqrt_nonneg _))) (by positivity)
        · rw [norm_smul, show ‖Complex.I / 2‖ = 1 / 2 by
            rw [norm_div, Complex.norm_I]; norm_num]
          refine mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (add_le_add ?_ ?_)) (by norm_num)
          · rw [norm_smul]; exact mul_le_mul_of_nonneg_left hXc (norm_nonneg _)
          · rw [norm_smul, norm_mul]; exact mul_le_mul_of_nonneg_left hYc (by positivity)
    _ ≤ Real.sqrt N * ‖a‖ * (6 * m₀ * m₁ + ‖a‖ * m₁ ^ 2 + 44 * m₀ ^ 3 +
          24 * m₀ * (‖a‖⁻¹ ^ 2 * ω)) := by
        -- `4sω ≤ 24|a|m₀ω` and `s³/5 ≤ 44|a|³m₀³`
        have hs3 : s ^ 3 / 5 ≤ 44 * (‖a‖ * m₀) ^ 3 := by
          have : s ^ 3 ≤ (6 * (‖a‖ * m₀)) ^ 3 := pow_le_pow_left₀ hs0 hs 3
          nlinarith [pow_nonneg (mul_nonneg hη.le hm0) 3]
        have h4 : 4 * s * ω ≤ 24 * (‖a‖ * m₀) * ω := by nlinarith
        have hainv : ‖a‖⁻¹ ^ 2 * ‖a‖ ^ 2 = 1 := by
          rw [← mul_pow, inv_mul_cancel₀ hη.ne']; norm_num
        have hfirst : ‖a‖⁻¹ ^ 2 * (Real.sqrt N * (4 * s * ω + s ^ 3 / 5)) ≤
            Real.sqrt N * ‖a‖ * (44 * m₀ ^ 3 + 24 * m₀ * (‖a‖⁻¹ ^ 2 * ω)) := by
          have hb : 4 * s * ω + s ^ 3 / 5 ≤ 24 * (‖a‖ * m₀) * ω + 44 * (‖a‖ * m₀) ^ 3 := by linarith
          calc ‖a‖⁻¹ ^ 2 * (Real.sqrt N * (4 * s * ω + s ^ 3 / 5))
              ≤ ‖a‖⁻¹ ^ 2 * (Real.sqrt N * (24 * (‖a‖ * m₀) * ω + 44 * (‖a‖ * m₀) ^ 3)) := by
                gcongr
            _ = Real.sqrt N * ‖a‖ * (44 * m₀ ^ 3 + 24 * m₀ * (‖a‖⁻¹ ^ 2 * ω)) := by
                have : ‖a‖⁻¹ ^ 2 * ‖a‖ ^ 3 = ‖a‖ := by
                  rw [show ‖a‖ ^ 3 = ‖a‖ ^ 2 * ‖a‖ by ring, ← mul_assoc, hainv, one_mul]
                have h' : ‖a‖⁻¹ ^ 2 * ‖a‖ = ‖a‖ * ‖a‖⁻¹ ^ 2 := by ring
                calc ‖a‖⁻¹ ^ 2 * (Real.sqrt N * (24 * (‖a‖ * m₀) * ω + 44 * (‖a‖ * m₀) ^ 3))
                    = Real.sqrt N * (24 * m₀ * ω * (‖a‖⁻¹ ^ 2 * ‖a‖) +
                        44 * m₀ ^ 3 * (‖a‖⁻¹ ^ 2 * ‖a‖ ^ 3)) := by ring
                  _ = _ := by rw [this, h']; ring
        have hsecond : 1 / 2 * (‖a‖ * (12 * m₀ * m₁) + ‖a‖ * ‖a‖ * (2 * m₁ ^ 2)) ≤
            Real.sqrt N * ‖a‖ * (6 * m₀ * m₁ + ‖a‖ * m₁ ^ 2) := by
          have h0 : 0 ≤ ‖a‖ * (6 * m₀ * m₁ + ‖a‖ * m₁ ^ 2) := by positivity
          calc 1 / 2 * (‖a‖ * (12 * m₀ * m₁) + ‖a‖ * ‖a‖ * (2 * m₁ ^ 2))
              = 1 * (‖a‖ * (6 * m₀ * m₁ + ‖a‖ * m₁ ^ 2)) := by ring
            _ ≤ Real.sqrt N * (‖a‖ * (6 * m₀ * m₁ + ‖a‖ * m₁ ^ 2)) :=
                mul_le_mul_of_nonneg_right hsqrt h0
            _ = Real.sqrt N * ‖a‖ * (6 * m₀ * m₁ + ‖a‖ * m₁ ^ 2) := by ring
        nlinarith [hfirst, hsecond]

end Plaquette

end CoreLean
