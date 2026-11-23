/-
`lem:current-expansion`(i) of BALABAN_CORE.tex, the remainder.

`𝐅(𝐔, A) = J(𝐔') - J(𝐔) - D^*_𝐔D_𝐔A`, `𝐔' = e^{iaA}𝐔`, is `(D^*_{𝐔'} - D^*_𝐔)F(𝐔') + D^*_𝐔Θ` with
`Θ = F(𝐔') - F(𝐔) - D_𝐔A` (`remainder_eq`, `eq:current-remainder-form`). At the bond `b = (x, x + ae_μ)`:
`‖((D^*_{𝐔',ν} - D^*_{𝐔,ν})f)(x)‖ ≤ 12‖A_ν(x - ae_ν)‖‖f(x - ae_ν)‖` (`norm_dbw_diff_le`, by `eq:adjoint-lipschitz`),
the rule of Leibniz gives `‖(D^*_{𝐔,ν}[A_ν, A_μ])(x)‖ ≤ 12m₀m₁` (`norm_dbw_comm_le`), and
`‖(D^*_{𝐔,ν}g)(x)‖ ≤ |a|⁻¹(2‖g(x - ae_ν)‖ + ‖g(x)‖)` (`norm_dbw_le`). With the bound `T` of the parts `Θ'` of
`eq:curvature-product` at the plaquettes of `st(b)` this gives (`norm_remainder_le`)
`‖𝐅(b)‖ ≤ 54√Nm₀|a|⁻²ω + 108m₀m₁ + 72m₀³ + 10|a|⁻¹T`.
-/
import CoreLean.CurvatureProduct

open NormedSpace Matrix
open scoped Matrix.Norms.L2Operator

namespace CoreLean

variable {N n : ℕ} [NeZero n] (a : ℂ) {G : GaugeGroup N}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "GLN" => (Matrix (Fin N) (Fin N) ℂ)ˣ

/-- `eq:current-remainder-form`. -/
theorem remainder_eq (hG : G.LieInput) (U : Config N n) (A : Form1 N n) (μ : Fin 4) (x : Site n) :
    current a hG (expMul a A U) μ x - current a hG U μ x - Ds2 a U (D1 a U A) μ x =
      ∑ ν, if ν ≠ μ then
        ((Dbw a (expMul a A U) ν (curv a hG (expMul a A U) ν μ) x -
            Dbw a U ν (curv a hG (expMul a A U) ν μ) x) +
          Dbw a U ν (fun y => curv a hG (expMul a A U) ν μ y - curv a hG U ν μ y -
            D1 a U A ν μ y) x) else 0 := by
  simp only [current, Ds2]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun ν _ => ?_
  split_ifs
  · rw [Dbw_fun_sub, Dbw_fun_sub]
    abel
  · simp

lemma Ad_mul_mul (W : GLN) (X Y : Mat) : Ad W (X * Y) = Ad W X * Ad W Y := by
  simp only [Ad, mul_assoc]
  rw [← mul_assoc ((W⁻¹ : GLN) : Mat), ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]

/-- `(D^*_{𝐔,ν}f)(x) = -Ad_{𝐔(x, x - ae_ν)}(D_{𝐔,ν}f)(x - ae_ν)`. -/
lemma Dbw_eq_neg_Ad_Dfw (U : Config N n) (ν : Fin 4) (f : Form0 N n) (x : Site n) :
    Dbw a U ν f x = -Ad (U.val ⟨x, ν, false⟩) (Dfw a U ν f (x - unit n ν)) := by
  have e : x - unit n ν + unit n ν = x := by abel
  have hV : U.val ⟨x, ν, false⟩ = (U ν (x - unit n ν))⁻¹ := by simp [Config.val]
  simp only [Dbw, Dfw, e, Ad_smul, Ad_sub, hV, Ad_inv_Ad]
  rw [smul_sub, smul_sub]
  abel

/-- `‖((D^*_{𝐔',ν} - D^*_{𝐔,ν})f)(x)‖ ≤ 12‖A_ν(x - ae_ν)‖‖f(x - ae_ν)‖`. -/
theorem norm_dbw_diff_le (ha : a ≠ 0) (U : Config N n) (A : Form1 N n) (ν : Fin 4) (x : Site n)
    (f : Form0 N n) (hX : ‖a • A ν (x - unit n ν)‖ ≤ 1 / 32)
    (hV : ∀ Z : Mat, ‖Ad (U.val ⟨x, ν, false⟩) Z‖ ≤ 2 * ‖Z‖) :
    ‖Dbw a (expMul a A U) ν f x - Dbw a U ν f x‖ ≤
      12 * ‖A ν (x - unit n ν)‖ * ‖f (x - unit n ν)‖ := by
  set X := -(a • A ν (x - unit n ν))
  have hval : (expMul a A U).val ⟨x, ν, false⟩ = U.val ⟨x, ν, false⟩ * expU (Complex.I • X) := by
    simp only [Config.val, Bool.false_eq_true, if_false, expMul, _root_.mul_inv_rev, expU_inv, X,
      smul_neg, mul_smul]
  have hXn : ‖X‖ ≤ 1 / 32 := by rw [norm_neg]; exact hX
  have e : Dbw a (expMul a A U) ν f x - Dbw a U ν f x =
      a⁻¹ • Ad (U.val ⟨x, ν, false⟩) (Ad (expU (Complex.I • X)) (f (x - unit n ν)) -
        f (x - unit n ν)) := by
    simp only [Dbw, hval, Ad_mul, Ad_sub, smul_sub]
    abel
  rw [e, norm_smul, norm_inv]
  have hη : 0 < ‖a‖ := norm_pos_iff.mpr ha
  calc ‖a‖⁻¹ * ‖Ad (U.val ⟨x, ν, false⟩) (Ad (expU (Complex.I • X)) (f (x - unit n ν)) -
        f (x - unit n ν))‖
      ≤ ‖a‖⁻¹ * (2 * (6 * ‖X‖ * ‖f (x - unit n ν)‖)) :=
        mul_le_mul_of_nonneg_left ((hV _).trans
          (mul_le_mul_of_nonneg_left (norm_Ad_exp_sub_le hXn _) (by norm_num))) (by positivity)
    _ = 12 * ‖A ν (x - unit n ν)‖ * ‖f (x - unit n ν)‖ := by
        rw [norm_neg, norm_smul]
        field_simp
        ring

/-- `‖(D^*_{𝐔,ν}g)(x)‖ ≤ |a|⁻¹(2‖g(x - ae_ν)‖ + ‖g(x)‖)`. -/
lemma norm_dbw_le (U : Config N n) (ν : Fin 4) (x : Site n) (g : Form0 N n)
    (hV : ∀ Z : Mat, ‖Ad (U.val ⟨x, ν, false⟩) Z‖ ≤ 2 * ‖Z‖) :
    ‖Dbw a U ν g x‖ ≤ ‖a‖⁻¹ * (2 * ‖g (x - unit n ν)‖ + ‖g x‖) := by
  simp only [Dbw]
  rw [norm_smul, norm_inv]
  exact mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (add_le_add (hV _) le_rfl))
    (inv_nonneg.mpr (norm_nonneg _))

/-- The rule of Leibniz: `‖(D^*_{𝐔,ν}[f, h])(x)‖ ≤ 12m₀m₁`. -/
theorem norm_dbw_comm_le (ha : a ≠ 0) (U : Config N n) (ν : Fin 4) (x : Site n) (f h : Form0 N n)
    {m₀ m₁ : ℝ} (hf : ‖f x‖ ≤ m₀) (hh : ‖Ad (U.val ⟨x, ν, false⟩) (h (x - unit n ν))‖ ≤ 2 * m₀)
    (hdf : ‖Dbw a U ν f x‖ ≤ 2 * m₁) (hdh : ‖Dbw a U ν h x‖ ≤ 2 * m₁) :
    ‖Dbw a U ν (fun y => f y * h y - h y * f y) x‖ ≤ 12 * m₀ * m₁ := by
  set V := U.val ⟨x, ν, false⟩
  set F' := Ad V (f (x - unit n ν))
  set H' := Ad V (h (x - unit n ν))
  have hm0 : 0 ≤ m₀ := (norm_nonneg _).trans hf
  have hm1 : 0 ≤ m₁ := by linarith [norm_nonneg (Dbw a U ν f x)]
  have hF : Dbw a U ν f x = a⁻¹ • (F' - f x) := rfl
  have hH : Dbw a U ν h x = a⁻¹ • (H' - h x) := rfl
  have e : Dbw a U ν (fun y => f y * h y - h y * f y) x =
      (Dbw a U ν f x * H' - H' * Dbw a U ν f x) + (f x * Dbw a U ν h x - Dbw a U ν h x * f x) := by
    rw [hF, hH]
    simp only [Dbw, Ad_sub, Ad_mul_mul]
    simp only [smul_mul_assoc, mul_smul_comm, sub_mul, mul_sub, smul_sub]
    abel
  have hcomm : ∀ X Y : Mat, ‖X * Y - Y * X‖ ≤ 2 * ‖X‖ * ‖Y‖ := fun X Y => by
    calc ‖X * Y - Y * X‖ ≤ ‖X * Y‖ + ‖Y * X‖ := norm_sub_le _ _
      _ ≤ ‖X‖ * ‖Y‖ + ‖Y‖ * ‖X‖ := add_le_add (opNorm_mul_le _ _) (opNorm_mul_le _ _)
      _ = 2 * ‖X‖ * ‖Y‖ := by ring
  rw [e]
  calc ‖(Dbw a U ν f x * H' - H' * Dbw a U ν f x) + (f x * Dbw a U ν h x - Dbw a U ν h x * f x)‖
      ≤ 2 * ‖Dbw a U ν f x‖ * ‖H'‖ + 2 * ‖f x‖ * ‖Dbw a U ν h x‖ :=
        (norm_add_le _ _).trans (add_le_add (hcomm _ _) (hcomm _ _))
    _ ≤ 2 * (2 * m₁) * (2 * m₀) + 2 * m₀ * (2 * m₁) := by gcongr
    _ = 12 * m₀ * m₁ := by ring

/-- `‖Im W‖ ≤ (3/2)ω` for `‖W - 1‖ ≤ ω ≤ 1/48`. -/
lemma norm_imW_le (W : GLN) {ω : ℝ} (hω : ‖(W : Mat) - 1‖ ≤ ω) (hω1 : ω ≤ 1 / 48) :
    ‖imW W‖ ≤ 3 / 2 * ω := by
  have hinv := norm_inv_le W (by linarith)
  have hWin : ‖((W⁻¹ : GLN) : Mat)‖ ≤ 2 := by
    have : (0 : ℝ) < 1 - ‖(W : Mat) - 1‖ := by linarith
    nlinarith [norm_nonneg ((W⁻¹ : GLN) : Mat)]
  have hWi : ‖((W⁻¹ : GLN) : Mat) - 1‖ ≤ 2 * ω := by
    have e : ((W⁻¹ : GLN) : Mat) - 1 = -(((W⁻¹ : GLN) : Mat) * ((W : Mat) - 1)) := by
      rw [mul_sub, mul_one, ← Units.val_mul, inv_mul_cancel, Units.val_one]; abel
    rw [e, norm_neg]
    exact (opNorm_mul_le _ _).trans (mul_le_mul hWin hω (norm_nonneg _) (by norm_num))
  have e : imW W = (1 / (2 * Complex.I) : ℂ) • (((W : Mat) - 1) - (((W⁻¹ : GLN) : Mat) - 1)) := by
    simp only [imW]; congr 1; abel
  rw [e, norm_smul, norm_inv_two_I]
  calc 1 / 2 * ‖(W : Mat) - 1 - (((W⁻¹ : GLN) : Mat) - 1)‖ ≤ 1 / 2 * (ω + 2 * ω) := by
        gcongr; exact (norm_sub_le _ _).trans (add_le_add hω hWi)
    _ = 3 / 2 * ω := by ring

/-- The bound of the remainder at the bond `b = (x, x + ae_μ)` from the bound `T` of the parts `Θ'` of
`eq:curvature-product` at the plaquettes `p_{νμ}(x)`, `p_{νμ}(x - ae_ν)`, `ν ≠ μ`. -/
theorem norm_remainder_le [NeZero N] (hG : G.LieInput) (ha : a ≠ 0) (U : Config N n) (A : Form1 N n)
    (μ : Fin 4) (x : Site n) {m₀ m₁ ω T : ℝ} (hm0 : 0 ≤ m₀) (hm1 : 0 ≤ m₁) (hT : 0 ≤ T)
    (hηm : ‖a‖ * m₀ ≤ 1 / 48)
    (hV : ∀ ν, ν ≠ μ → ∀ Z : Mat, ‖Ad (U.val ⟨x, ν, false⟩) Z‖ ≤ 2 * ‖Z‖)
    (hAν : ∀ ν, ν ≠ μ → ‖A ν (x - unit n ν)‖ ≤ m₀ ∧ ‖A μ (x - unit n ν)‖ ≤ m₀ ∧ ‖A ν x‖ ≤ m₀)
    (hAd : ∀ ν, ν ≠ μ → ‖Ad (U.val ⟨x, ν, false⟩) (A μ (x - unit n ν))‖ ≤ 2 * m₀)
    (hDf : ∀ ν, ν ≠ μ → ‖Dfw a U ν (A ν) (x - unit n ν)‖ ≤ m₁ ∧
      ‖Dfw a U ν (A μ) (x - unit n ν)‖ ≤ m₁)
    (hD1 : ∀ ν, ν ≠ μ → ‖D1 a U A ν μ (x - unit n ν)‖ ≤ 2 * m₁)
    (hF : ∀ ν, ν ≠ μ → ‖curv a hG U ν μ (x - unit n ν)‖ ≤ 3 / 2 * Real.sqrt N * (‖a‖⁻¹ ^ 2 * ω))
    (hθ : ∀ ν, ν ≠ μ → ∀ y ∈ ({x, x - unit n ν} : Finset (Site n)),
      ‖curv a hG (expMul a A U) ν μ y - curv a hG U ν μ y - D1 a U A ν μ y -
        Complex.I • (A ν y * A μ y - A μ y * A ν y)‖ ≤ T) :
    ‖current a hG (expMul a A U) μ x - current a hG U μ x - Ds2 a U (D1 a U A) μ x‖ ≤
      3 * (12 * m₀ * (3 / 2 * Real.sqrt N * (‖a‖⁻¹ ^ 2 * ω) + 2 * m₁ + 2 * m₀ ^ 2 + T) +
        12 * m₀ * m₁ + 3 * (‖a‖⁻¹ * T)) := by
  have hη : 0 < ‖a‖ := norm_pos_iff.mpr ha
  rw [remainder_eq]
  -- the term of one direction
  have hterm : ∀ ν, ν ≠ μ →
      ‖(Dbw a (expMul a A U) ν (curv a hG (expMul a A U) ν μ) x -
            Dbw a U ν (curv a hG (expMul a A U) ν μ) x) +
          Dbw a U ν (fun y => curv a hG (expMul a A U) ν μ y - curv a hG U ν μ y -
            D1 a U A ν μ y) x‖ ≤
        12 * m₀ * (3 / 2 * Real.sqrt N * (‖a‖⁻¹ ^ 2 * ω) + 2 * m₁ + 2 * m₀ ^ 2 + T) +
          12 * m₀ * m₁ + 3 * (‖a‖⁻¹ * T) := by
    intro ν hν
    obtain ⟨hA1, hA2, hA3⟩ := hAν ν hν
    set Θ' : Form0 N n := fun y => curv a hG (expMul a A U) ν μ y - curv a hG U ν μ y -
      D1 a U A ν μ y - Complex.I • (A ν y * A μ y - A μ y * A ν y)
    have hθx : ‖Θ' x‖ ≤ T := hθ ν hν x (by simp)
    have hθx' : ‖Θ' (x - unit n ν)‖ ≤ T := hθ ν hν (x - unit n ν) (by simp)
    -- the first term
    have hX : ‖a • A ν (x - unit n ν)‖ ≤ 1 / 32 := by
      rw [norm_smul]; nlinarith [norm_nonneg a]
    have h1 := norm_dbw_diff_le a ha U A ν x (curv a hG (expMul a A U) ν μ) hX (hV ν hν)
    have hcomm' : ‖A ν (x - unit n ν) * A μ (x - unit n ν) - A μ (x - unit n ν) * A ν (x - unit n ν)‖
        ≤ 2 * m₀ ^ 2 := by
      calc _ ≤ ‖A ν (x - unit n ν) * A μ (x - unit n ν)‖ + ‖A μ (x - unit n ν) * A ν (x - unit n ν)‖ :=
            norm_sub_le _ _
        _ ≤ m₀ * m₀ + m₀ * m₀ := add_le_add
            ((opNorm_mul_le _ _).trans (mul_le_mul hA1 hA2 (norm_nonneg _) hm0))
            ((opNorm_mul_le _ _).trans (mul_le_mul hA2 hA1 (norm_nonneg _) hm0))
        _ = 2 * m₀ ^ 2 := by ring
    have hf : ‖curv a hG (expMul a A U) ν μ (x - unit n ν)‖ ≤
        3 / 2 * Real.sqrt N * (‖a‖⁻¹ ^ 2 * ω) + 2 * m₁ + 2 * m₀ ^ 2 + T := by
      have e : curv a hG (expMul a A U) ν μ (x - unit n ν) = curv a hG U ν μ (x - unit n ν) +
          D1 a U A ν μ (x - unit n ν) + Complex.I • (A ν (x - unit n ν) * A μ (x - unit n ν) -
            A μ (x - unit n ν) * A ν (x - unit n ν)) + Θ' (x - unit n ν) := by
        simp only [Θ']; abel
      rw [e]
      refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add
        ((norm_add_le _ _).trans (add_le_add (hF ν hν) (hD1 ν hν))) ?_)) hθx')
      rw [norm_smul, Complex.norm_I, one_mul]; exact hcomm'
    have hT1 : ‖Dbw a (expMul a A U) ν (curv a hG (expMul a A U) ν μ) x -
        Dbw a U ν (curv a hG (expMul a A U) ν μ) x‖ ≤
        12 * m₀ * (3 / 2 * Real.sqrt N * (‖a‖⁻¹ ^ 2 * ω) + 2 * m₁ + 2 * m₀ ^ 2 + T) :=
      h1.trans (mul_le_mul (mul_le_mul_of_nonneg_left hA1 (by norm_num)) hf (norm_nonneg _)
        (by positivity))
    -- the second term: `D^*_ν(i[A_ν, A_μ]) + D^*_νΘ'`
    have hsplit : Dbw a U ν (fun y => curv a hG (expMul a A U) ν μ y - curv a hG U ν μ y -
        D1 a U A ν μ y) x = Complex.I • Dbw a U ν (fun y => A ν y * A μ y - A μ y * A ν y) x +
          Dbw a U ν Θ' x := by
      have e : (fun y => curv a hG (expMul a A U) ν μ y - curv a hG U ν μ y - D1 a U A ν μ y) =
          fun y => Complex.I • (A ν y * A μ y - A μ y * A ν y) + Θ' y := by
        funext y; simp only [Θ']; abel
      rw [e]
      simp only [Dbw, Pi.add_apply, Ad_add, Ad_smul]
      simp only [smul_add, smul_sub, smul_comm a⁻¹ Complex.I]
      abel
    have hdf : ‖Dbw a U ν (A ν) x‖ ≤ 2 * m₁ := by
      rw [Dbw_eq_neg_Ad_Dfw, norm_neg]
      exact (hV ν hν _).trans (by linarith [(hDf ν hν).1])
    have hdh : ‖Dbw a U ν (A μ) x‖ ≤ 2 * m₁ := by
      rw [Dbw_eq_neg_Ad_Dfw, norm_neg]
      exact (hV ν hν _).trans (by linarith [(hDf ν hν).2])
    have hL := norm_dbw_comm_le a ha U ν x (A ν) (A μ) hA3 (hAd ν hν) hdf hdh
    have hΘ := norm_dbw_le a U ν x Θ' (hV ν hν)
    have hT2 : ‖Dbw a U ν (fun y => curv a hG (expMul a A U) ν μ y - curv a hG U ν μ y -
        D1 a U A ν μ y) x‖ ≤ 12 * m₀ * m₁ + 3 * (‖a‖⁻¹ * T) := by
      rw [hsplit]
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_smul, Complex.norm_I, one_mul]; exact hL
      · refine hΘ.trans ?_
        have : 2 * ‖Θ' (x - unit n ν)‖ + ‖Θ' x‖ ≤ 3 * T := by linarith
        calc ‖a‖⁻¹ * (2 * ‖Θ' (x - unit n ν)‖ + ‖Θ' x‖) ≤ ‖a‖⁻¹ * (3 * T) :=
              mul_le_mul_of_nonneg_left this (by positivity)
          _ = 3 * (‖a‖⁻¹ * T) := by ring
    calc _ ≤ _ := norm_add_le _ _
      _ ≤ _ := add_le_add hT1 hT2
      _ = _ := by ring
  -- the sum over the three directions `ν ≠ μ`
  have hsum : ‖∑ ν, (if ν ≠ μ then
        ((Dbw a (expMul a A U) ν (curv a hG (expMul a A U) ν μ) x -
            Dbw a U ν (curv a hG (expMul a A U) ν μ) x) +
          Dbw a U ν (fun y => curv a hG (expMul a A U) ν μ y - curv a hG U ν μ y -
            D1 a U A ν μ y) x) else 0)‖ ≤
      ∑ ν, (if ν ≠ μ then 12 * m₀ * (3 / 2 * Real.sqrt N * (‖a‖⁻¹ ^ 2 * ω) + 2 * m₁ +
        2 * m₀ ^ 2 + T) + 12 * m₀ * m₁ + 3 * (‖a‖⁻¹ * T) else 0) := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ν _ => ?_)
    split_ifs with h
    · exact hterm ν h
    · simp
  refine hsum.trans (le_of_eq ?_)
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  have hcard : (Finset.univ.filter fun ν : Fin 4 => ν ≠ μ).card = 3 := by
    rw [Finset.filter_ne' Finset.univ μ, Finset.card_erase_of_mem (Finset.mem_univ μ),
      Finset.card_univ, Fintype.card_fin]
  rw [hcard]
  push_cast
  ring

set_option maxHeartbeats 2000000 in
/-- `lem:current-expansion`(i), `eq:current-remainder`. Let `b = (x, x + ae_μ)`, and for `ν ≠ μ` and
`y ∈ {x, x - ae_ν}` (the plaquettes `p_{νμ}(y)` of `st(b)`) let `|𝐔(∂p_{νμ}(y)) - 1| ≤ h ≤ c₆ = (48√N)⁻¹`, the
transports along the bonds `(y, y + ae_ν)`, `(y, y + ae_μ)`, `(x, x - ae_ν)` change the operator norm by a factor
of at most `2`, the values of `A` on the bonds of these plaquettes have norms at most `m₀` with
`|a|m₀ ≤ c₆`, and the differences `D_{𝐔,ν}A_μ(y)`, `D_{𝐔,μ}A_ν(y)`, `D_{𝐔,ν}A_ν(x - ae_ν)` have norms at most
`m₁`. Then `‖𝐅(𝐔, A)(b)‖ ≤ C₈((m₀ + |a|m₁)(m₁ + |a|⁻²h) + m₀³)`, `C₈ = 512N`. -/
theorem current_remainder [NeZero N] (hG : G.LieInput) (ha : a ≠ 0) (U : Config N n)
    (hU : ∀ μ x, U μ x ∈ G.complexified) (A : Form1 N n) (hA : ∀ μ x, A μ x ∈ G.lieC)
    (μ : Fin 4) (x : Site n) {m₀ m₁ h : ℝ} (hm0 : 0 ≤ m₀) (hm1 : 0 ≤ m₁)
    (hh : h ≤ 1 / (48 * Real.sqrt N)) (hηm : ‖a‖ * m₀ ≤ 1 / (48 * Real.sqrt N))
    (hP : ∀ ν, ν ≠ μ → ∀ y ∈ ({x, x - unit n ν} : Finset (Site n)),
      hs (((plaq U ν μ y : GLN) : Mat) - 1) ≤ h)
    (hAm : ∀ ν, ν ≠ μ → ∀ y ∈ ({x, x - unit n ν} : Finset (Site n)),
      ‖A ν y‖ ≤ m₀ ∧ ‖A μ y‖ ≤ m₀ ∧ ‖A μ (y + unit n ν)‖ ≤ m₀ ∧ ‖A ν (y + unit n μ)‖ ≤ m₀)
    (hTr : ∀ ν, ν ≠ μ → ∀ y ∈ ({x, x - unit n ν} : Finset (Site n)), ∀ Z : Mat,
      ‖Ad (U ν y) Z‖ ≤ 2 * ‖Z‖ ∧ ‖Ad (U μ y) Z‖ ≤ 2 * ‖Z‖)
    (hV : ∀ ν, ν ≠ μ → ∀ Z : Mat, ‖Ad (U.val ⟨x, ν, false⟩) Z‖ ≤ 2 * ‖Z‖)
    (hDm : ∀ ν, ν ≠ μ → ∀ y ∈ ({x, x - unit n ν} : Finset (Site n)),
      ‖Dfw a U ν (A μ) y‖ ≤ m₁ ∧ ‖Dfw a U μ (A ν) y‖ ≤ m₁)
    (hDν : ∀ ν, ν ≠ μ → ‖Dfw a U ν (A ν) (x - unit n ν)‖ ≤ m₁) :
    ‖current a hG (expMul a A U) μ x - current a hG U μ x - Ds2 a U (D1 a U A) μ x‖ ≤
      512 * N * ((m₀ + ‖a‖ * m₁) * (m₁ + ‖a‖⁻¹ ^ 2 * h) + m₀ ^ 3) := by
  have hη : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hsqrt : 1 ≤ Real.sqrt N := by
    rw [Real.one_le_sqrt]; exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hN : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt (Nat.cast_nonneg N)
  have hh0 : 0 ≤ h := by
    obtain ⟨ν, hν⟩ : ∃ ν : Fin 4, ν ≠ μ := ⟨μ + 1, by simp⟩
    exact (hs_nonneg _).trans (hP ν hν x (by simp))
  set ω := Real.sqrt N * h
  have hω0 : 0 ≤ ω := by positivity
  have hω1 : ω ≤ 1 / 48 := by
    have : Real.sqrt N * h ≤ Real.sqrt N * (1 / (48 * Real.sqrt N)) :=
      mul_le_mul_of_nonneg_left hh (Real.sqrt_nonneg _)
    rw [show Real.sqrt N * (1 / (48 * Real.sqrt N)) = 1 / 48 by field_simp] at this
    exact this
  have hηm' : ‖a‖ * m₀ ≤ 1 / 48 :=
    hηm.trans (one_div_le_one_div_of_le (by norm_num) (by nlinarith))
  have hωp : ∀ ν, ν ≠ μ → ∀ y ∈ ({x, x - unit n ν} : Finset (Site n)),
      ‖((plaq U ν μ y : GLN) : Mat) - 1‖ ≤ ω := fun ν hν y hy =>
    (opNorm_le_sqrt_mul_hs _).trans (mul_le_mul_of_nonneg_left (hP ν hν y hy) (Real.sqrt_nonneg _))
  -- the bound `T` of the parts `Θ'`
  set T := Real.sqrt N * ‖a‖ * (6 * m₀ * m₁ + ‖a‖ * m₁ ^ 2 + 44 * m₀ ^ 3 + 24 * m₀ * (‖a‖⁻¹ ^ 2 * ω))
  have hT0 : 0 ≤ T := by positivity
  have hθ : ∀ ν, ν ≠ μ → ∀ y ∈ ({x, x - unit n ν} : Finset (Site n)),
      ‖curv a hG (expMul a A U) ν μ y - curv a hG U ν μ y - D1 a U A ν μ y -
        Complex.I • (A ν y * A μ y - A μ y * A ν y)‖ ≤ T := by
    intro ν hν y hy
    obtain ⟨a1, a2, a3, a4⟩ := hAm ν hν y hy
    have t := hTr ν hν y hy
    exact curvature_product a hG ha U hU A hA ν μ y a1 a2
      ((t _).1.trans (by linarith)) ((t _).2.trans (by rw [norm_neg]; linarith))
      (hDm ν hν y hy).1 (hDm ν hν y hy).2 (hωp ν hν y hy) hω1 hηm'
  -- the inputs of `norm_remainder_le`
  have hAν : ∀ ν, ν ≠ μ → ‖A ν (x - unit n ν)‖ ≤ m₀ ∧ ‖A μ (x - unit n ν)‖ ≤ m₀ ∧ ‖A ν x‖ ≤ m₀ :=
    fun ν hν => ⟨(hAm ν hν _ (by simp)).1, (hAm ν hν _ (by simp)).2.1, (hAm ν hν x (by simp)).1⟩
  have hAd : ∀ ν, ν ≠ μ → ‖Ad (U.val ⟨x, ν, false⟩) (A μ (x - unit n ν))‖ ≤ 2 * m₀ :=
    fun ν hν => (hV ν hν _).trans (by linarith [(hAν ν hν).2.1])
  have hDf : ∀ ν, ν ≠ μ → ‖Dfw a U ν (A ν) (x - unit n ν)‖ ≤ m₁ ∧
      ‖Dfw a U ν (A μ) (x - unit n ν)‖ ≤ m₁ :=
    fun ν hν => ⟨hDν ν hν, (hDm ν hν _ (by simp)).1⟩
  have hD1 : ∀ ν, ν ≠ μ → ‖D1 a U A ν μ (x - unit n ν)‖ ≤ 2 * m₁ := by
    intro ν hν
    simp only [D1]
    have := hDm ν hν _ (show x - unit n ν ∈ ({x, x - unit n ν} : Finset (Site n)) by simp)
    exact (norm_sub_le _ _).trans (by linarith [this.1, this.2])
  have hF : ∀ ν, ν ≠ μ → ‖curv a hG U ν μ (x - unit n ν)‖ ≤
      3 / 2 * Real.sqrt N * (‖a‖⁻¹ ^ 2 * ω) := by
    intro ν hν
    simp only [curv]
    rw [norm_smul, norm_inv, norm_pow]
    have him := norm_imW_le _ (hωp ν hν (x - unit n ν) (by simp)) hω1
    calc (‖a‖ ^ 2)⁻¹ * ‖piProj hG (imW (plaq U ν μ (x - unit n ν)))‖
        ≤ (‖a‖ ^ 2)⁻¹ * (Real.sqrt N * (3 / 2 * ω)) :=
          mul_le_mul_of_nonneg_left ((opNorm_proj_le hG _).trans
            (mul_le_mul_of_nonneg_left him (Real.sqrt_nonneg _))) (by positivity)
      _ = 3 / 2 * Real.sqrt N * (‖a‖⁻¹ ^ 2 * ω) := by rw [inv_pow]; ring
  have hR := norm_remainder_le a hG ha U A μ x hm0 hm1 hT0 hηm' hV hAν hAd hDf hD1 hF hθ
  refine hR.trans ?_
  -- the arithmetic: `36m₀ ≤ |a|⁻¹`, `|a|⁻¹T = √N(…)`, `ω = √Nh`
  have h36 : 36 * m₀ ≤ ‖a‖⁻¹ := by
    have h1 : 36 * m₀ * ‖a‖ ≤ 1 := by nlinarith
    calc 36 * m₀ = 36 * m₀ * ‖a‖ * ‖a‖⁻¹ := by field_simp
      _ ≤ 1 * ‖a‖⁻¹ := mul_le_mul_of_nonneg_right h1 (inv_nonneg.mpr hη.le)
      _ = ‖a‖⁻¹ := one_mul _
  have hinvT : ‖a‖⁻¹ * T = Real.sqrt N * (6 * m₀ * m₁ + ‖a‖ * m₁ ^ 2 + 44 * m₀ ^ 3 +
      24 * m₀ * (‖a‖⁻¹ ^ 2 * ω)) := by
    simp only [T]; field_simp
  have hmT : 36 * m₀ * T ≤ ‖a‖⁻¹ * T := mul_le_mul_of_nonneg_right h36 hT0
  have hω' : ‖a‖⁻¹ ^ 2 * ω = Real.sqrt N * (‖a‖⁻¹ ^ 2 * h) := by simp only [ω]; ring
  set k := ‖a‖⁻¹ ^ 2 * h
  have hk0 : 0 ≤ k := by positivity
  rw [hω'] at hinvT ⊢
  have hP1 : 0 ≤ ‖a‖ * m₁ := by positivity
  -- the final comparison, term by term
  have hsqN : Real.sqrt N ≤ N := by nlinarith
  nlinarith [mul_nonneg hm0 hm1, mul_nonneg hm0 hk0, mul_nonneg hP1 hm1, mul_nonneg hP1 hk0,
    pow_nonneg hm0 3, mul_nonneg (mul_nonneg hm0 hm1) (Real.sqrt_nonneg N),
    mul_nonneg (mul_nonneg hm0 hk0) (Real.sqrt_nonneg N), hsqrt, hN,
    mul_nonneg (pow_nonneg hm0 3) (Real.sqrt_nonneg N), mul_nonneg (mul_nonneg hP1 hm1) (Real.sqrt_nonneg N)]

end CoreLean
