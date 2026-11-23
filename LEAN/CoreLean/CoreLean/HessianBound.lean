/-
`lem:hessian`(ii) of BALABAN_CORE.tex: `(Δ'(U)A)(b)` depends only on the plaquettes of `st(b)`, and
`‖(Δ'(U)A)(b)‖ ≤ C_Δ η⁻² max_p |U(∂p) - 1| max_{b'} ‖A(b')‖` with `C_Δ = 252 N^{3/2}`.

The proof is the core's. `a⁴ tr(Z (Δ'A)(b)) = β(A, δ_b Z)` for `Z ∈ 𝔤^c` (`hessOp'_spec`); the summand of
a plaquette vanishes unless the plaquette contains `b` (`hessTermBil_single_eq_zero`), and for one
which contains `b` it is at most `42 |a|² m₀ ω ‖Z‖`; at most six positive plaquettes contain `b`.
With `Z = Y^*`, `|Y|² ≤ 252 |a|⁻² m₀ ω ‖Y‖`, and `‖Y‖ ≤ √N |Y|`, used twice, gives the bound.
The lattice is assumed to have at least two sites in each direction (`1 < n`), so that a bond occurs
at most once in the boundary of a plaquette.
-/
import CoreLean.HessianOperator

open NormedSpace Complex
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace CoreLean

variable {N n : ℕ} [NeZero n] (a : ℂ)

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "GLN" => (Matrix (Fin N) (Fin N) ℂ)ˣ

variable {G : GaugeGroup N}

lemma single1_apply (μ : Fin 4) (x : Site n) (Z : Mat) (ν : Fin 4) (y : Site n) :
    single1 μ x Z ν y = if ν = μ ∧ y = x then Z else 0 := by
  by_cases h1 : ν = μ
  · subst h1; by_cases h2 : y = x
    · subst h2; simp [single1]
    · simp [single1, h2]
  · simp [single1, h1]

/-- The plaquette `p_{μ'ν'}(y)` has the positive bond `(x, x + ae_μ)` in its boundary. -/
def Contains (μ' ν' : Fin 4) (y : Site n) (μ : Fin 4) (x : Site n) : Prop :=
  (μ' = μ ∧ (y = x ∨ y + unit n ν' = x)) ∨ (ν' = μ ∧ (y + unit n μ' = x ∨ y = x))

lemma not_contains {μ' ν' : Fin 4} {y : Site n} {μ : Fin 4} {x : Site n}
    (h : ¬Contains μ' ν' y μ x) :
    ¬(μ' = μ ∧ y = x) ∧ ¬(ν' = μ ∧ y + unit n μ' = x) ∧ ¬(μ' = μ ∧ y + unit n ν' = x) ∧
      ¬(ν' = μ ∧ y = x) :=
  ⟨fun h' => h (Or.inl ⟨h'.1, Or.inl h'.2⟩), fun h' => h (Or.inr ⟨h'.1, Or.inl h'.2⟩),
    fun h' => h (Or.inl ⟨h'.1, Or.inr h'.2⟩), fun h' => h (Or.inr ⟨h'.1, Or.inr h'.2⟩)⟩

/-- If the plaquette does not contain `b`, the exponents of `δ_b Z` vanish on it. -/
lemma pexp_single_eq_zero (U : Config N n) {μ' ν' : Fin 4} {y : Site n} {μ : Fin 4} {x : Site n}
    (h : ¬Contains μ' ν' y μ x) (Z : Mat) : pexp (single1 μ x Z) U μ' ν' y = 0 := by
  obtain ⟨c1, c2, c3, c4⟩ := not_contains h
  funext k
  fin_cases k <;> simp [pexp, single1_apply, if_neg c1, if_neg c2, if_neg c3, if_neg c4, Ad]

/-- If the plaquette does not contain `b`, `(D_U δ_b Z)(p) = 0`. -/
lemma D1_single_eq_zero (U : Config N n) {μ' ν' : Fin 4} {y : Site n} {μ : Fin 4} {x : Site n}
    (h : ¬Contains μ' ν' y μ x) (Z : Mat) : D1 a U (single1 μ x Z) μ' ν' y = 0 := by
  obtain ⟨c1, c2, c3, c4⟩ := not_contains h
  simp [D1, Dfw, single1_apply, if_neg c1, if_neg c2, if_neg c3, if_neg c4, Ad]

lemma commPBil_zero_right (B : Fin 4 → Mat) : commPBil B 0 = 0 := by
  have := commPBil_smul_right (0 : ℂ) B 0
  simpa using this

/-- The summand of `β(A, δ_b Z)` vanishes for a plaquette which does not contain `b`. -/
lemma hessTermBil_single_eq_zero (A : Form1 N n) (U : Config N n) {μ' ν' : Fin 4} {y : Site n}
    {μ : Fin 4} {x : Site n} (h : ¬Contains μ' ν' y μ x) (Z : Mat) :
    hessTermBil a A (single1 μ x Z) U μ' ν' y = 0 := by
  rw [hessTermBil, D1_single_eq_zero a U h, pexp_single_eq_zero U h, commPBil_zero_right]
  simp [ntr]

/-! ### The norms of the pieces of one plaquette -/

lemma norm_brk_le (X Y : Mat) : ‖brk X Y‖ ≤ 2 * ‖X‖ * ‖Y‖ := by
  calc ‖brk X Y‖ ≤ ‖X * Y‖ + ‖Y * X‖ := norm_sub_le _ _
    _ ≤ ‖X‖ * ‖Y‖ + ‖Y‖ * ‖X‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ = 2 * ‖X‖ * ‖Y‖ := by ring

/-- `‖C_p(B, B')‖ ≤ 3 M Σ_k ‖B'_k‖` if `‖B_k‖ ≤ M`: each index occurs in three of the six pairs. -/
lemma norm_commPBil_le {B B' : Fin 4 → Mat} {M : ℝ} (hB : ∀ k, ‖B k‖ ≤ M) :
    ‖commPBil B B'‖ ≤ 3 * M * (‖B' 0‖ + ‖B' 1‖ + ‖B' 2‖ + ‖B' 3‖) := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (hB 0)
  have h1 : ∀ k l, ‖brk (B k) (B' l)‖ ≤ 2 * M * ‖B' l‖ := fun k l =>
    (norm_brk_le _ _).trans (by gcongr; exact hB k)
  have h2 : ∀ k l, ‖brk (B' k) (B l)‖ ≤ 2 * M * ‖B' k‖ := fun k l =>
    (norm_brk_le _ _).trans (by rw [mul_assoc, mul_comm ‖B' k‖, ← mul_assoc]; gcongr; exact hB l)
  simp only [commPBil, plaqPairs, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    add_zero, norm_smul, norm_inv, Complex.norm_ofNat]
  have e : ∀ (p q : Mat), ‖p + q‖ ≤ ‖p‖ + ‖q‖ := fun p q => norm_add_le p q
  have t1 := e (brk (B 2) (B' 3)) (brk (B' 2) (B 3))
  have t2 := e (brk (B 2) (B' 0)) (brk (B' 2) (B 0))
  have t3 := e (brk (B 2) (B' 1)) (brk (B' 2) (B 1))
  have t4 := e (brk (B 3) (B' 0)) (brk (B' 3) (B 0))
  have t5 := e (brk (B 3) (B' 1)) (brk (B' 3) (B 1))
  have t6 := e (brk (B 0) (B' 1)) (brk (B' 0) (B 1))
  have s1 := e (brk (B 2) (B' 1) + brk (B' 2) (B 1)) (brk (B 3) (B' 0) + brk (B' 3) (B 0) +
      (brk (B 3) (B' 1) + brk (B' 3) (B 1) + (brk (B 0) (B' 1) + brk (B' 0) (B 1))))
  have s2 := e (brk (B 3) (B' 0) + brk (B' 3) (B 0)) (brk (B 3) (B' 1) + brk (B' 3) (B 1) +
      (brk (B 0) (B' 1) + brk (B' 0) (B 1)))
  have s3 := e (brk (B 3) (B' 1) + brk (B' 3) (B 1)) (brk (B 0) (B' 1) + brk (B' 0) (B 1))
  have := h1 2 3; have := h2 2 3; have := h1 2 0; have := h2 2 0; have := h1 2 1; have := h2 2 1
  have := h1 3 0; have := h2 3 0; have := h1 3 1; have := h2 3 1; have := h1 0 1; have := h2 0 1
  have hsum : ‖brk (B 2) (B' 3) + brk (B' 2) (B 3) + (brk (B 2) (B' 0) + brk (B' 2) (B 0) +
      (brk (B 2) (B' 1) + brk (B' 2) (B 1) + (brk (B 3) (B' 0) + brk (B' 3) (B 0) +
        (brk (B 3) (B' 1) + brk (B' 3) (B 1) + (brk (B 0) (B' 1) + brk (B' 0) (B 1))))))‖ ≤
      6 * M * (‖B' 0‖ + ‖B' 1‖ + ‖B' 2‖ + ‖B' 3‖) := by
    have s0 := e (brk (B 2) (B' 3) + brk (B' 2) (B 3)) (brk (B 2) (B' 0) + brk (B' 2) (B 0) +
      (brk (B 2) (B' 1) + brk (B' 2) (B 1) + (brk (B 3) (B' 0) + brk (B' 3) (B 0) +
        (brk (B 3) (B' 1) + brk (B' 3) (B 1) + (brk (B 0) (B' 1) + brk (B' 0) (B 1))))))
    have s0' := e (brk (B 2) (B' 0) + brk (B' 2) (B 0)) (brk (B 2) (B' 1) + brk (B' 2) (B 1) +
      (brk (B 3) (B' 0) + brk (B' 3) (B 0) +
        (brk (B 3) (B' 1) + brk (B' 3) (B 1) + (brk (B 0) (B' 1) + brk (B' 0) (B 1)))))
    linarith
  calc 2⁻¹ * _ ≤ 2⁻¹ * (6 * M * (‖B' 0‖ + ‖B' 1‖ + ‖B' 2‖ + ‖B' 3‖)) := by gcongr
    _ = 3 * M * (‖B' 0‖ + ‖B' 1‖ + ‖B' 2‖ + ‖B' 3‖) := by ring

/-- `‖(D_U A)(p)‖ ≤ |a|⁻¹ Σ_k ‖A_k‖`, from `Σ_k A_k = a (D_U A)(p)`. -/
lemma norm_D1_le (ha : a ≠ 0) (A : Form1 N n) (U : Config N n) (μ ν : Fin 4) (x : Site n) :
    ‖D1 a U A μ ν x‖ ≤ ‖a‖⁻¹ * (‖pexp A U μ ν x 0‖ + ‖pexp A U μ ν x 1‖ + ‖pexp A U μ ν x 2‖ +
      ‖pexp A U μ ν x 3‖) := by
  have h := productExponent_sum a ha A U μ ν x
  have hD : D1 a U A μ ν x = a⁻¹ • (pexp A U μ ν x 0 + pexp A U μ ν x 1 + pexp A U μ ν x 2 +
      pexp A U μ ν x 3) := by
    simp only [pexp, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    rw [h, smul_smul, inv_mul_cancel₀ ha, one_smul]
  rw [hD, norm_smul, norm_inv]
  gcongr
  have := norm_add_le (pexp A U μ ν x 0 + pexp A U μ ν x 1 + pexp A U μ ν x 2)
    (pexp A U μ ν x 3)
  have := norm_add_le (pexp A U μ ν x 0 + pexp A U μ ν x 1) (pexp A U μ ν x 2)
  have := norm_add_le (pexp A U μ ν x 0) (pexp A U μ ν x 1)
  linarith

/-- For `‖W - 1‖ ≤ ω ≤ 1/2`: `‖W⁻¹ - 1‖ ≤ 2ω`, `‖Re W - 1‖ ≤ 3ω/2`, `‖Im W‖ ≤ 3ω/2`. -/
lemma norm_reW_imW_le (W : GLN) {ω : ℝ} (hW : ‖(W : Mat) - 1‖ ≤ ω) (hω : ω ≤ 1 / 2) :
    ‖reW W - 1‖ ≤ 3 / 2 * ω ∧ ‖imW W‖ ≤ 3 / 2 * ω := by
  set P : Mat := (W : Mat)
  set Q : Mat := ((W⁻¹ : GLN) : Mat)
  have hQP : Q * P = 1 := by simp [P, Q]
  have hω0 : 0 ≤ ω := (norm_nonneg _).trans hW
  -- `‖Q‖ ≤ 2` and `‖Q - 1‖ ≤ 2ω`
  have hQ1 : Q - 1 = -(Q * (P - 1)) := by rw [mul_sub, hQP, mul_one]; abel
  have hQ : ‖Q‖ ≤ 2 := by
    have h1 : ‖Q‖ ≤ ‖(1 : Mat)‖ + ‖Q‖ * ω := by
      calc ‖Q‖ = ‖1 + (Q - 1)‖ := by rw [add_sub_cancel]
        _ ≤ ‖(1 : Mat)‖ + ‖Q - 1‖ := norm_add_le _ _
        _ ≤ ‖(1 : Mat)‖ + ‖Q‖ * ω := by
            rw [hQ1, norm_neg]; gcongr; exact (norm_mul_le _ _).trans (by gcongr)
    have := norm_one_mat_le (N := N)
    nlinarith [norm_nonneg Q]
  have hQ2 : ‖Q - 1‖ ≤ 2 * ω := by
    rw [hQ1, norm_neg]; exact (norm_mul_le _ _).trans (by gcongr)
  constructor
  · have e : reW W - 1 = (2 : ℂ)⁻¹ • ((P - 1) + (Q - 1)) := by
      simp only [reW, P, Q]; module
    rw [e, norm_smul, norm_inv, Complex.norm_ofNat]
    have := norm_add_le (P - 1) (Q - 1)
    linarith
  · have e : imW W = (1 / (2 * I)) • ((P - 1) - (Q - 1)) := by
      simp only [imW, P, Q, sub_sub_sub_cancel_right]
    rw [e, norm_smul, norm_div, norm_one, norm_mul, Complex.norm_ofNat, Complex.norm_I, mul_one]
    have := norm_sub_le (P - 1) (Q - 1)
    linarith

lemma unit_ne_zero (hn : 1 < n) (ν : Fin 4) : unit n ν ≠ 0 := by
  intro h
  have h1 : (1 : ZMod n) = 0 := by simpa [unit] using congrFun h ν
  have : Fact (1 < n) := ⟨hn⟩
  exact one_ne_zero h1

lemma add_unit_ne (hn : 1 < n) (y : Site n) (ν : Fin 4) : y + unit n ν ≠ y := by
  intro h
  exact unit_ne_zero hn ν (by simpa using h)

/-- The exponents of `δ_b Z` on a plaquette: at most one is nonzero, so their norms add up to at
most `2‖Z‖`. -/
lemma sum_norm_pexp_single_le (hn : 1 < n) (U : Config N n) {μ' ν' : Fin 4} (hlt : μ' < ν')
    (y : Site n) (μ : Fin 4) (x : Site n) (Z : Mat)
    (hAd : ∀ X : Mat, ‖Ad (U μ' y) X‖ ≤ 2 * ‖X‖ ∧ ‖Ad (U ν' y) X‖ ≤ 2 * ‖X‖) :
    ‖pexp (single1 μ x Z) U μ' ν' y 0‖ + ‖pexp (single1 μ x Z) U μ' ν' y 1‖ +
      ‖pexp (single1 μ x Z) U μ' ν' y 2‖ + ‖pexp (single1 μ x Z) U μ' ν' y 3‖ ≤ 2 * ‖Z‖ := by
  have hne : μ' ≠ ν' := ne_of_lt hlt
  have hZ := norm_nonneg Z
  simp only [pexp, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, single1_apply]
  have hA1 := (hAd Z).1
  have hA2 := (hAd (-Z)).2
  rw [norm_neg] at hA2
  have h0 : Ad (U μ' y) 0 = 0 := by simp [Ad]
  have h0' : Ad (U ν' y) (-0) = 0 := by simp [Ad]
  have h0'' : Ad (U ν' y) 0 = 0 := by simp [Ad]
  by_cases c1 : μ' = μ ∧ y = x
  · have n2 : ¬(ν' = μ ∧ y + unit n μ' = x) := fun h => hne (c1.1.trans h.1.symm)
    have n3 : ¬(μ' = μ ∧ y + unit n ν' = x) := fun h =>
      add_unit_ne hn y ν' (h.2.trans c1.2.symm)
    have n4 : ¬(ν' = μ ∧ y = x) := fun h => hne (c1.1.trans h.1.symm)
    rw [if_pos c1, if_neg n2, if_neg n3, if_neg n4]
    simp only [h0, h0', h0'', neg_zero, norm_zero]
    linarith
  · by_cases c3 : μ' = μ ∧ y + unit n ν' = x
    · have n2 : ¬(ν' = μ ∧ y + unit n μ' = x) := fun h => hne (c3.1.trans h.1.symm)
      have n4 : ¬(ν' = μ ∧ y = x) := fun h => hne (c3.1.trans h.1.symm)
      rw [if_neg c1, if_neg n2, if_pos c3, if_neg n4]
      simp only [h0, h0'', neg_zero, norm_zero]
      linarith
    · by_cases c2 : ν' = μ ∧ y + unit n μ' = x
      · have n4 : ¬(ν' = μ ∧ y = x) := fun h => add_unit_ne hn y μ' (c2.2.trans h.2.symm)
        rw [if_neg c1, if_pos c2, if_neg c3, if_neg n4]
        simp only [h0', h0'', neg_zero, norm_zero]
        linarith
      · by_cases c4 : ν' = μ ∧ y = x
        · rw [if_neg c1, if_neg c2, if_neg c3, if_pos c4]
          simp only [h0, h0', h0'', neg_zero, norm_zero, norm_neg]
          linarith
        · rw [if_neg c1, if_neg c2, if_neg c3, if_neg c4]
          simp only [h0, h0', h0'', neg_zero, norm_zero]
          linarith

/-- The exponents of `A` on a plaquette have norms at most `2 m₀`. -/
lemma norm_pexp_le (U : Config N n) (A : Form1 N n) (μ' ν' : Fin 4) (y : Site n) {m₀ : ℝ}
    (hAd : ∀ X : Mat, ‖Ad (U μ' y) X‖ ≤ 2 * ‖X‖ ∧ ‖Ad (U ν' y) X‖ ≤ 2 * ‖X‖)
    (hA : ‖A μ' y‖ ≤ m₀ ∧ ‖A ν' (y + unit n μ')‖ ≤ m₀ ∧ ‖A μ' (y + unit n ν')‖ ≤ m₀ ∧
      ‖A ν' y‖ ≤ m₀) (k : Fin 4) : ‖pexp A U μ' ν' y k‖ ≤ 2 * m₀ := by
  obtain ⟨h1, h2, h3, h4⟩ := hA
  have hm : 0 ≤ m₀ := (norm_nonneg _).trans h1
  fin_cases k
  · show ‖A μ' y‖ ≤ 2 * m₀; linarith
  · show ‖Ad (U μ' y) (A ν' (y + unit n μ'))‖ ≤ 2 * m₀
    exact (hAd _).1.trans (by linarith)
  · show ‖Ad (U ν' y) (-A μ' (y + unit n ν'))‖ ≤ 2 * m₀
    exact (hAd _).2.trans (by rw [norm_neg]; linarith)
  · show ‖-A ν' y‖ ≤ 2 * m₀
    rw [norm_neg]; linarith

/-- The summand of `β(A, δ_b Z)` for a plaquette: at most `42 |a|² m₀ ω ‖Z‖`. -/
lemma norm_hessTermBil_single_le [NeZero N] (ha : a ≠ 0) (hn : 1 < n) (U : Config N n)
    (A : Form1 N n) {μ' ν' : Fin 4} (hlt : μ' < ν') (y : Site n) (μ : Fin 4) (x : Site n)
    (Z : Mat) {m₀ ω : ℝ} (hP : ‖(plaq U μ' ν' y : Mat) - 1‖ ≤ ω) (hω : ω ≤ 1 / 2)
    (hAd : ∀ X : Mat, ‖Ad (U μ' y) X‖ ≤ 2 * ‖X‖ ∧ ‖Ad (U ν' y) X‖ ≤ 2 * ‖X‖)
    (hA : ‖A μ' y‖ ≤ m₀ ∧ ‖A ν' (y + unit n μ')‖ ≤ m₀ ∧ ‖A μ' (y + unit n ν')‖ ≤ m₀ ∧
      ‖A ν' y‖ ≤ m₀) :
    ‖hessTermBil a A (single1 μ x Z) U μ' ν' y‖ ≤ 42 * ‖a‖ ^ 2 * m₀ * ω * ‖Z‖ := by
  have hm : 0 ≤ m₀ := (norm_nonneg _).trans hA.1
  have hω0 : 0 ≤ ω := (norm_nonneg _).trans hP
  have hpA := norm_pexp_le U A μ' ν' y hAd hA
  have hsB := sum_norm_pexp_single_le hn U hlt y μ x Z hAd
  obtain ⟨hre, him⟩ := norm_reW_imW_le (plaq U μ' ν' y) hP hω
  have ha0 : 0 < ‖a‖ := norm_pos_iff.2 ha
  -- `‖(D_U A)(p)‖ ≤ 8m₀/|a|` and `‖(D_U δ_b Z)(p)‖ ≤ 2‖Z‖/|a|`
  have hDA : ‖D1 a U A μ' ν' y‖ ≤ ‖a‖⁻¹ * (8 * m₀) := by
    refine (norm_D1_le a ha A U μ' ν' y).trans ?_
    gcongr
    linarith [hpA 0, hpA 1, hpA 2, hpA 3]
  have hDB : ‖D1 a U (single1 μ x Z) μ' ν' y‖ ≤ ‖a‖⁻¹ * (2 * ‖Z‖) :=
    (norm_D1_le a ha _ U μ' ν' y).trans (by gcongr)
  have hC := norm_commPBil_le (B' := pexp (single1 μ x Z) U μ' ν' y) hpA
  rw [hessTermBil]
  have t1 : ‖a ^ 4 * ntr ((2 : ℂ)⁻¹ • (D1 a U A μ' ν' y * D1 a U (single1 μ x Z) μ' ν' y +
      D1 a U (single1 μ x Z) μ' ν' y * D1 a U A μ' ν' y) * (reW (plaq U μ' ν' y) - 1))‖ ≤
      ‖a‖ ^ 4 * ((‖a‖⁻¹ * (8 * m₀)) * (‖a‖⁻¹ * (2 * ‖Z‖)) * (3 / 2 * ω)) := by
    rw [norm_mul, norm_pow]
    gcongr
    refine (norm_ntr_le_opNorm _).trans ((norm_mul_le _ _).trans ?_)
    gcongr
    rw [norm_smul, norm_inv, Complex.norm_ofNat]
    have h1 := (norm_mul_le (D1 a U A μ' ν' y) (D1 a U (single1 μ x Z) μ' ν' y)).trans
      (mul_le_mul hDA hDB (norm_nonneg _) (by positivity))
    have h2 := (norm_mul_le (D1 a U (single1 μ x Z) μ' ν' y) (D1 a U A μ' ν' y)).trans
      (mul_le_mul hDB hDA (norm_nonneg _) (by positivity))
    have h3 := norm_add_le (D1 a U A μ' ν' y * D1 a U (single1 μ x Z) μ' ν' y)
      (D1 a U (single1 μ x Z) μ' ν' y * D1 a U A μ' ν' y)
    nlinarith
  have t2 : ‖I * a ^ 2 * ntr (commPBil (pexp A U μ' ν' y) (pexp (single1 μ x Z) U μ' ν' y) *
      imW (plaq U μ' ν' y))‖ ≤ ‖a‖ ^ 2 * ((3 * (2 * m₀) * (2 * ‖Z‖)) * (3 / 2 * ω)) := by
    rw [norm_mul, norm_mul, Complex.norm_I, one_mul, norm_pow]
    gcongr
    refine (norm_ntr_le_opNorm _).trans ((norm_mul_le _ _).trans ?_)
    gcongr
    exact hC.trans (by gcongr)
  calc _ ≤ _ := norm_add_le _ _
    _ ≤ ‖a‖ ^ 4 * ((‖a‖⁻¹ * (8 * m₀)) * (‖a‖⁻¹ * (2 * ‖Z‖)) * (3 / 2 * ω)) +
        ‖a‖ ^ 2 * ((3 * (2 * m₀) * (2 * ‖Z‖)) * (3 / 2 * ω)) := add_le_add t1 t2
    _ = 42 * ‖a‖ ^ 2 * m₀ * ω * ‖Z‖ := by field_simp; ring

/-! ### The six plaquettes of `st(b)` and the bound -/

/-- The positive plaquettes `(y, μ', ν')` which contain the bond `(x, μ)`: for each `ν ≠ μ`, the two
plaquettes in the directions `μ, ν` at `x` and at `x - ae_ν`. -/
def starPlaq (μ : Fin 4) (x : Site n) : Finset (Site n × Fin 4 × Fin 4) :=
  (Finset.univ.erase μ).biUnion fun ν =>
    {(x, min μ ν, max μ ν), (x - unit n ν, min μ ν, max μ ν)}

lemma card_starPlaq_le (μ : Fin 4) (x : Site n) : (starPlaq μ x).card ≤ 6 := by
  refine Finset.card_biUnion_le.trans ?_
  calc ∑ ν ∈ Finset.univ.erase μ, ({(x, min μ ν, max μ ν), (x - unit n ν, min μ ν, max μ ν)} :
        Finset (Site n × Fin 4 × Fin 4)).card ≤ ∑ _ν ∈ Finset.univ.erase μ, 2 :=
        Finset.sum_le_sum fun ν _ => Finset.card_insert_le _ _
    _ = 6 := by simp [Finset.card_erase_of_mem]

lemma mem_starPlaq {μ' ν' : Fin 4} {y : Site n} {μ : Fin 4} {x : Site n} (hlt : μ' < ν')
    (h : Contains μ' ν' y μ x) : (y, μ', ν') ∈ starPlaq μ x := by
  simp only [starPlaq, Finset.mem_biUnion, Finset.mem_erase, Finset.mem_univ, and_true,
    Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
  rcases h with ⟨rfl, hy⟩ | ⟨rfl, hy⟩
  · refine ⟨ν', (ne_of_lt hlt).symm, ?_⟩
    rw [min_eq_left hlt.le, max_eq_right hlt.le]
    rcases hy with rfl | hy
    · left; simp
    · right; refine ⟨eq_sub_of_add_eq hy, rfl, rfl⟩
  · refine ⟨μ', ne_of_lt hlt, ?_⟩
    rw [min_eq_right hlt.le, max_eq_left hlt.le]
    rcases hy with hy | rfl
    · right; exact ⟨eq_sub_of_add_eq hy, rfl, rfl⟩
    · left; simp

/-- `lem:hessian`(ii), the bound `eq:hessian`, with `C_Δ = 252 N^{3/2}`: if for the plaquettes
`p ∋ b` we have `‖U(∂p) - 1‖ ≤ 1/2`, `|U(∂p) - 1| ≤ ω`, the transports `Ad_{U(b')}` of the bonds
which enter change the operator norm by a factor of at most `2`, and `‖A(b')‖ ≤ m₀` on their bonds,
then `‖(Δ'(U)A)(b)‖ ≤ C_Δ a⁻² ω m₀`. -/
theorem norm_hessOp'_le [NeZero N] (hG : G.LieInput) (ha : a ≠ 0) (hn : 1 < n) (U : Config N n)
    (A : Form1 N n) (μ : Fin 4) (x : Site n) {m₀ ω : ℝ}
    (hP : ∀ μ' ν' y, μ' < ν' → Contains μ' ν' y μ x →
      ‖(plaq U μ' ν' y : Mat) - 1‖ ≤ 1 / 2 ∧ hs ((plaq U μ' ν' y : Mat) - 1) ≤ ω)
    (hAd : ∀ μ' ν' y, μ' < ν' → Contains μ' ν' y μ x →
      ∀ X : Mat, ‖Ad (U μ' y) X‖ ≤ 2 * ‖X‖ ∧ ‖Ad (U ν' y) X‖ ≤ 2 * ‖X‖)
    (hA : ∀ μ' ν' y, μ' < ν' → Contains μ' ν' y μ x →
      ‖A μ' y‖ ≤ m₀ ∧ ‖A ν' (y + unit n μ')‖ ≤ m₀ ∧ ‖A μ' (y + unit n ν')‖ ≤ m₀ ∧
        ‖A ν' y‖ ≤ m₀) :
    ‖hessOp' a hG U A μ x‖ ≤ 252 * ((N : ℝ) * Real.sqrt N) * (‖a‖ ^ 2)⁻¹ * ω * m₀ := by
  have ha0 : 0 < ‖a‖ := norm_pos_iff.2 ha
  have hsN : 0 ≤ Real.sqrt N := Real.sqrt_nonneg _
  -- `m₀, ω ≥ 0`, from a plaquette of `st(b)`
  obtain ⟨ν₀, hν₀⟩ : ∃ ν₀ : Fin 4, ν₀ ≠ μ := by
    by_cases h : μ = 0
    · exact ⟨1, by rw [h]; decide⟩
    · exact ⟨0, fun e => h e.symm⟩
  have hc₀ : Contains (min μ ν₀) (max μ ν₀) x μ x := by
    rcases lt_or_gt_of_ne hν₀ with h | h
    · right; exact ⟨max_eq_left h.le, Or.inr rfl⟩
    · left; exact ⟨min_eq_left h.le, Or.inl rfl⟩
  have hlt₀ : min μ ν₀ < max μ ν₀ := min_lt_max.2 hν₀.symm
  have hm0 : 0 ≤ m₀ := (norm_nonneg _).trans (hA _ _ _ hlt₀ hc₀).1
  have hω0 : 0 ≤ ω := (hs_nonneg _).trans (hP _ _ _ hlt₀ hc₀).2
  -- the bound on `β(A, δ_b Z)`
  have hβ : ∀ Z : Mat, ‖hessBil a A (single1 μ x Z) U‖ ≤
      252 * ‖a‖ ^ 2 * m₀ * (Real.sqrt N * ω) * ‖Z‖ := fun Z => by
    set g : Site n × Fin 4 × Fin 4 → ℂ := fun q =>
      if q.2.1 < q.2.2 then hessTermBil a A (single1 μ x Z) U q.2.1 q.2.2 q.1 else 0
    have hsum : hessBil a A (single1 μ x Z) U = ∑ q ∈ starPlaq μ x, g q := by
      rw [hessBil]
      rw [show (∑ y : Site n, ∑ μ' : Fin 4, ∑ ν' : Fin 4, if μ' < ν' then
          hessTermBil a A (single1 μ x Z) U μ' ν' y else 0) = ∑ q, g q by
        symm
        rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [Fintype.sum_prod_type]]
      refine (Finset.sum_subset (Finset.subset_univ _) fun q _ hq => ?_).symm
      simp only [g]
      split_ifs with hlt
      · by_contra hne
        exact hq (mem_starPlaq hlt (by_contra fun hc =>
          hne (hessTermBil_single_eq_zero a A U hc Z)))
      · rfl
    rw [hsum]
    have hZ := norm_nonneg Z
    calc ‖∑ q ∈ starPlaq μ x, g q‖ ≤ ∑ q ∈ starPlaq μ x, ‖g q‖ := norm_sum_le _ _
      _ ≤ ∑ _q ∈ starPlaq μ x, 42 * ‖a‖ ^ 2 * m₀ * (Real.sqrt N * ω) * ‖Z‖ := by
          refine Finset.sum_le_sum fun q hq => ?_
          simp only [g]
          split_ifs with hlt
          · by_cases hc : Contains q.2.1 q.2.2 q.1 μ x
            · obtain ⟨hP1, hP2⟩ := hP _ _ _ hlt hc
              have h := norm_hessTermBil_single_le a ha hn U A hlt q.1 μ x Z le_rfl hP1
                (hAd _ _ _ hlt hc) (hA _ _ _ hlt hc)
              refine h.trans ?_
              gcongr
              exact (opNorm_le_sqrt_mul_hs _).trans (by gcongr)
            · rw [hessTermBil_single_eq_zero a A U hc Z, norm_zero]; positivity
          · rw [norm_zero]; positivity
      _ = (starPlaq μ x).card * (42 * ‖a‖ ^ 2 * m₀ * (Real.sqrt N * ω) * ‖Z‖) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 6 * (42 * ‖a‖ ^ 2 * m₀ * (Real.sqrt N * ω) * ‖Z‖) := by
          gcongr; exact_mod_cast card_starPlaq_le μ x
      _ = 252 * ‖a‖ ^ 2 * m₀ * (Real.sqrt N * ω) * ‖Z‖ := by ring
  -- `|tr ZY| ≤ C₂ ‖Z‖` for `Z ∈ 𝔤^c`, with `Y = (Δ'A)(b)`
  set Y := hessOp' a hG U A μ x
  set C₂ := 252 * (‖a‖ ^ 2)⁻¹ * m₀ * (Real.sqrt N * ω)
  have hC₂ : 0 ≤ C₂ := by positivity
  have htr : ∀ Z ∈ G.lieC, ‖ntr (Z * Y)‖ ≤ C₂ * ‖Z‖ := fun Z hZ => by
    have h := hessOp'_spec a hG ha U A μ x hZ
    have h4 : ‖a ^ 4 * ntr (Z * Y)‖ ≤ 252 * ‖a‖ ^ 2 * m₀ * (Real.sqrt N * ω) * ‖Z‖ := by
      rw [h]; exact hβ Z
    rw [norm_mul, norm_pow] at h4
    have hpos : 0 < ‖a‖ ^ 4 := by positivity
    have e : C₂ * ‖Z‖ * ‖a‖ ^ 4 = 252 * ‖a‖ ^ 2 * m₀ * (Real.sqrt N * ω) * ‖Z‖ := by
      simp only [C₂]; field_simp
    refine le_of_mul_le_mul_right ?_ hpos
    rw [e]; linarith
  -- `Z = Y^*`: `|Y|² ≤ C₂ ‖Y‖ ≤ C₂ √N |Y|`
  have hYs := htr (Matrix.conjTranspose Y) (GaugeGroup.conjTranspose_mem_lieC (hessOp'_mem a hG U A μ x))
  rw [opNorm_conjTranspose] at hYs
  have hre : hs Y ^ 2 ≤ ‖ntr (Matrix.conjTranspose Y * Y)‖ := by
    rw [hs_sq, hs2]; exact Complex.re_le_norm _
  have h1 : hs Y ^ 2 ≤ C₂ * (Real.sqrt N * hs Y) :=
    hre.trans (hYs.trans (mul_le_mul_of_nonneg_left (opNorm_le_sqrt_mul_hs Y) hC₂))
  have hhs : hs Y ≤ C₂ * Real.sqrt N := by
    rcases (hs_nonneg Y).eq_or_lt with h0 | h0
    · rw [← h0]; positivity
    · nlinarith
  calc ‖Y‖ ≤ Real.sqrt N * hs Y := opNorm_le_sqrt_mul_hs Y
    _ ≤ Real.sqrt N * (C₂ * Real.sqrt N) := by gcongr
    _ = 252 * ((N : ℝ) * Real.sqrt N) * (‖a‖ ^ 2)⁻¹ * ω * m₀ := by
        simp only [C₂]
        rw [show Real.sqrt N * (252 * (‖a‖ ^ 2)⁻¹ * m₀ * (Real.sqrt N * ω) * Real.sqrt N) =
          252 * (Real.sqrt N * Real.sqrt N) * Real.sqrt N * (‖a‖ ^ 2)⁻¹ * ω * m₀ by ring,
          Real.mul_self_sqrt (Nat.cast_nonneg N)]
        ring

/-- `lem:hessian`(ii), the dependence: `(Δ'(U)A)(b)` depends only on the values of `U` and of `A`
on the bonds of the plaquettes of `st(b)`. -/
theorem hessOp'_local [NeZero N] (hG : G.LieInput) (ha : a ≠ 0) (U U' : Config N n)
    (A A' : Form1 N n) (μ : Fin 4) (x : Site n)
    (hU : ∀ μ' ν' y, μ' < ν' → Contains μ' ν' y μ x →
      U μ' y = U' μ' y ∧ U ν' (y + unit n μ') = U' ν' (y + unit n μ') ∧
        U μ' (y + unit n ν') = U' μ' (y + unit n ν') ∧ U ν' y = U' ν' y)
    (hA : ∀ μ' ν' y, μ' < ν' → Contains μ' ν' y μ x →
      A μ' y = A' μ' y ∧ A ν' (y + unit n μ') = A' ν' (y + unit n μ') ∧
        A μ' (y + unit n ν') = A' μ' (y + unit n ν') ∧ A ν' y = A' ν' y) :
    hessOp' a hG U A μ x = hessOp' a hG U' A' μ x := by
  -- the functionals `Z ↦ β(A, δ_b Z)` agree
  have key : ∀ Z : Mat, hessBil a A (single1 μ x Z) U = hessBil a A' (single1 μ x Z) U' := by
    intro Z
    unfold hessBil
    refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun μ' _ =>
      Finset.sum_congr rfl fun ν' _ => ?_
    split_ifs with hlt
    · by_cases hc : Contains μ' ν' y μ x
      · obtain ⟨u1, u2, u3, u4⟩ := hU μ' ν' y hlt hc
        obtain ⟨a1, a2, a3, a4⟩ := hA μ' ν' y hlt hc
        simp only [hessTermBil, D1, Dfw, pexp, plaq_eq, u1, u2, u3, u4, a1, a2, a3, a4]
      · rw [hessTermBil_single_eq_zero a A U hc Z, hessTermBil_single_eq_zero a A' U' hc Z]
    · rfl
  -- uniqueness of the representing element of `𝔤^c`
  have h1 := hessOp'_mem a hG U A μ x
  have h2 := hessOp'_mem a hG U' A' μ x
  have heq : trPairing hG ⟨_, h1⟩ = trPairing hG ⟨_, h2⟩ := by
    ext Z
    simp only [trPairing, LinearMap.coe_mk, AddHom.coe_mk]
    have e1 := hessOp'_spec a hG ha U A μ x Z.2
    have e2 := hessOp'_spec a hG ha U' A' μ x Z.2
    rw [key] at e1
    have ha4 : a ^ 4 ≠ 0 := pow_ne_zero 4 ha
    exact mul_left_cancel₀ ha4 (e1.trans e2.symm)
  exact congrArg Subtype.val (trPairing_injective hG heq)

end CoreLean
