/-
`def:hessian`, `eq:action-expansion` and `eq:hessian-form` of BALABAN_CORE.tex, along a ray: for a
configuration `U` with values in `G^c` and a form `A` with values in `𝔤^c`,
`A(e^{isaA}U) = A(U) + s⟨A, J(U)⟩ + (s²/2)(⟨A, D^*_U D_U A⟩ + β(A, A)) + O(s³)`, with
`β(A, A) = Σ_p (a⁴ tr((D_U A)(p)²(Re U(∂p) - 1)) + i a² tr(C_p(A) Im U(∂p)))` the right side of
`eq:hessian-form`.

The proof is the core's: by `lem:product-plaquette` and the cyclicity of the trace the plaquette term
is `tr(U(∂p)V)` with `V = e^{iY₃}e^{iY₄}e^{iY₁}e^{iY₂}`, and similarly for the inverse, and
`eq:four-exponentials` (`norm_four_exp_sub_le`, `norm_four_exp_inv_sub_le`) expands `V` to the second
order with the remainder `e^t - 1 - t - t²/2 ≤ t³ e^t`.
-/
import CoreLean.Hessian

open NormedSpace Complex
open scoped Matrix.Norms.L2Operator Nat

noncomputable section

namespace CoreLean

variable {N n : ℕ} [NeZero n] (a : ℂ)

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "GLN" => (Matrix (Fin N) (Fin N) ℂ)ˣ

variable {G : GaugeGroup N}

/-! ### The remainder of the exponential series -/

/-- `e^t - 1 - t - t²/2 ≤ t³ e^t` for `t ≥ 0`. -/
lemma phi3_le {t : ℝ} (ht : 0 ≤ t) : phi3 t ≤ t ^ 3 * Real.exp t := by
  have h1 := (hasSum_nat_add_iff' 3).mpr (BakerCampbellHausdorff.hasSum_real_exp t)
  have h2 := (BakerCampbellHausdorff.hasSum_real_exp t).mul_left (t ^ 3)
  have e : ∑ i ∈ Finset.range 3, (i !⁻¹ : ℝ) • t ^ i = 1 + t + t ^ 2 / 2 := by
    simp [Finset.sum_range_succ, Nat.factorial]; ring
  rw [e] at h1
  have := hasSum_le (fun m => ?_) h1 h2
  · unfold phi3; linarith
  · simp only [smul_eq_mul]
    rw [pow_add, mul_comm (t ^ m), ← mul_assoc, mul_comm _ (t ^ 3), mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg ht 3)
    refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg ht m)
    exact inv_anti₀ (by positivity) (by exact_mod_cast Nat.factorial_le (by omega))

/-! ### The exponents of a plaquette and the bilinear term -/

/-- The four exponents `A₁, …, A₄` of `eq:product-exponents` for the plaquette `p_{μν}(x)`. -/
def pexp (A : Form1 N n) (U : Config N n) (μ ν : Fin 4) (x : Site n) : Fin 4 → Mat :=
  ![A μ x, Ad (U μ x) (A ν (x + unit n μ)), Ad (U ν x) (-A μ (x + unit n ν)), -A ν x]

/-- `C_p(A)`: the sum of the six commutators `[A_k, A_l]` with `A_k` before `A_l` in the order
`A₃, A₄, A₁, A₂`. -/
def commP (B : Fin 4 → Mat) : Mat :=
  (B 2 * B 3 - B 3 * B 2) + (B 2 * B 0 - B 0 * B 2) + (B 2 * B 1 - B 1 * B 2) +
    (B 3 * B 0 - B 0 * B 3) + (B 3 * B 1 - B 1 * B 3) + (B 0 * B 1 - B 1 * B 0)

/-- The summand of `eq:hessian-form` for the plaquette `p_{μν}(x)`. -/
def hessTerm (A : Form1 N n) (U : Config N n) (μ ν : Fin 4) (x : Site n) : ℂ :=
  a ^ 4 * ntr (D1 a U A μ ν x ^ 2 * (reW (plaq U μ ν x) - 1)) +
    I * a ^ 2 * ntr (commP (pexp A U μ ν x) * imW (plaq U μ ν x))

/-- The right side of `eq:hessian-form`, `β(A, A) = ⟨A, Δ'(U)A⟩`. -/
def hessForm (A : Form1 N n) (U : Config N n) : ℂ :=
  ∑ x : Site n, ∑ μ : Fin 4, ∑ ν : Fin 4, if μ < ν then hessTerm a A U μ ν x else 0

lemma commP_smul (c : ℂ) (B : Fin 4 → Mat) : commP (fun k => c • B k) = c ^ 2 • commP B := by
  simp only [commP, smul_mul_smul_comm, ← smul_sub, ← smul_add, sq]

lemma ntr_neg (X : Mat) : ntr (-X) = -ntr X := by
  simp [ntr, Matrix.trace_neg]

lemma norm_ntr_le_opNorm [NeZero N] (X : Mat) : ‖ntr X‖ ≤ ‖X‖ :=
  (norm_ntr_le_hs (NeZero.pos N) X).trans (hs_le_opNorm (NeZero.pos N) X)

/-! ### The expansion of one plaquette -/

/-- The expansion of the summand of the action for one plaquette, to the second order with a cubic
remainder: the first-order coefficient is `a² tr(Im U(∂p) (D_U A)(p))`, the second-order one
`a⁴ tr((D_U A)(p)²) + (summand of eq:hessian-form)`. -/
theorem actionTerm_expansion [NeZero N] (ha : a ≠ 0) (A : Form1 N n) (U : Config N n)
    (μ ν : Fin 4) (x : Site n) : ∃ K : ℝ, ∀ s : ℂ, ‖s‖ ≤ 1 →
      ‖actionTerm (expMul a (s • A) U) μ ν x - actionTerm U μ ν x -
        s * (a ^ 2 * ntr (imW (plaq U μ ν x) * D1 a U A μ ν x)) -
        s ^ 2 / 2 * (a ^ 4 * ntr (D1 a U A μ ν x ^ 2) + hessTerm a A U μ ν x)‖ ≤ K * ‖s‖ ^ 3 := by
  set B := pexp A U μ ν x with hB
  set P : Mat := (plaq U μ ν x : Mat)
  set Pinv : Mat := (((plaq U μ ν x)⁻¹ : GLN) : Mat)
  set D := D1 a U A μ ν x
  set c : ℝ := ‖a‖ * (‖B 2‖ + ‖B 3‖ + ‖B 0‖ + ‖B 1‖) with hc
  have hc0 : 0 ≤ c := by positivity
  refine ⟨(‖P‖ + ‖Pinv‖) / 2 * (c ^ 3 * Real.exp c), fun s hs => ?_⟩
  set Y : Fin 4 → Mat := fun k => (s * a) • B k with hY
  -- the plaquette and its inverse in terms of the `Y_k`
  have hexp : ∀ k, exp (s • ((I * a) • B k)) = exp (I • Y k) ∧
      exp (s • -((I * a) • B k)) = exp (I • -Y k) := fun k => by
    constructor <;> · simp only [hY, smul_neg, smul_smul]; congr 2; ring
  obtain ⟨h1, h2⟩ := plaq_expMul_smul a A U μ ν x s
  have e0 := hexp 0; have e1 := hexp 1; have e2 := hexp 2; have e3 := hexp 3
  simp only [hB, pexp, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] at e0 e1 e2 e3
  rw [e0.1, e1.1, e2.1, e3.1] at h1
  rw [e0.2, e1.2, e2.2, e3.2] at h2
  set V := exp (I • Y 2) * exp (I • Y 3) * exp (I • Y 0) * exp (I • Y 1) with hV
  set V' := exp (I • -Y 1) * exp (I • -Y 0) * exp (I • -Y 3) * exp (I • -Y 2) with hV'
  -- the traces of the plaquette and of its inverse, by the cyclicity of the trace
  have hW : ntr ((plaq (expMul a (s • A) U) μ ν x : GLN) : Mat) = ntr (P * V) := by
    rw [h1, show exp (I • Y 0) * exp (I • Y 1) * P * exp (I • Y 2) * exp (I • Y 3) =
      (exp (I • Y 0) * exp (I • Y 1)) * (P * exp (I • Y 2) * exp (I • Y 3)) by noncomm_ring,
      ntr_mul_comm]
    simp only [hV, mul_assoc]
  have hWi : ntr (((plaq (expMul a (s • A) U) μ ν x)⁻¹ : GLN) : Mat) = ntr (Pinv * V') := by
    rw [h2, show exp (I • -Y 3) * exp (I • -Y 2) * Pinv * exp (I • -Y 1) * exp (I • -Y 0) =
      (exp (I • -Y 3) * exp (I • -Y 2)) * (Pinv * exp (I • -Y 1) * exp (I • -Y 0)) by
        noncomm_ring, ntr_mul_comm]
    simp only [hV', mul_assoc]
  -- `eq:four-exponentials` for `V` and `V'`
  have hT := norm_four_exp_sub_le (Y 2) (Y 3) (Y 0) (Y 1)
  have hT' := norm_four_exp_inv_sub_le (Y 2) (Y 3) (Y 0) (Y 1)
  rw [← hV] at hT
  rw [← hV'] at hT'
  have hS : Y 2 + Y 3 + Y 0 + Y 1 = (s * a * a) • D := by
    have := productExponent_sum a ha A U μ ν x
    simp only [hY, ← smul_add, smul_smul]
    rw [show B 2 + B 3 + B 0 + B 1 = B 0 + B 1 + B 2 + B 3 by abel]
    simp only [hB, pexp, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    rw [this, smul_smul]
  have hC : (Y 2 * Y 3 - Y 3 * Y 2) + (Y 2 * Y 0 - Y 0 * Y 2) + (Y 2 * Y 1 - Y 1 * Y 2) +
      (Y 3 * Y 0 - Y 0 * Y 3) + (Y 3 * Y 1 - Y 1 * Y 3) + (Y 0 * Y 1 - Y 1 * Y 0) =
      (s * a) ^ 2 • commP B := by
    rw [← commP_smul]; rfl
  rw [hS, hC] at hT hT'
  -- the norms of the exponents
  have hYn : ‖Y 2‖ + ‖Y 3‖ + ‖Y 0‖ + ‖Y 1‖ = ‖s‖ * c := by
    simp only [hY, norm_smul, norm_mul, hc]; ring
  rw [hYn] at hT hT'
  have hφ : phi3 (‖s‖ * c) ≤ ‖s‖ ^ 3 * (c ^ 3 * Real.exp c) := by
    have hs0 := norm_nonneg s
    refine (phi3_le (by positivity)).trans ?_
    have he : Real.exp (‖s‖ * c) ≤ Real.exp c := Real.exp_le_exp.2 (by nlinarith)
    calc (‖s‖ * c) ^ 3 * Real.exp (‖s‖ * c) = ‖s‖ ^ 3 * c ^ 3 * Real.exp (‖s‖ * c) := by ring
      _ ≤ ‖s‖ ^ 3 * c ^ 3 * Real.exp c := by gcongr
      _ = _ := by ring
  -- the remainder
  set R := V - (1 + I • ((s * a * a) • D) - (2 : ℂ)⁻¹ • ((s * a * a) • D) ^ 2 -
    (2 : ℂ)⁻¹ • ((s * a) ^ 2 • commP B)) with hR
  set R' := V' - (1 + I • -((s * a * a) • D) - (2 : ℂ)⁻¹ • (-((s * a * a) • D)) ^ 2 -
    (2 : ℂ)⁻¹ • -((s * a) ^ 2 • commP B)) with hR'
  -- the left side equals `-½(tr(P R) + tr(P⁻¹ R'))`
  have key : actionTerm (expMul a (s • A) U) μ ν x - actionTerm U μ ν x -
      s * (a ^ 2 * ntr (imW (plaq U μ ν x) * D)) -
      s ^ 2 / 2 * (a ^ 4 * ntr (D ^ 2) + hessTerm a A U μ ν x) =
      -(2 : ℂ)⁻¹ * (ntr (P * R) + ntr (Pinv * R')) := by
    have hVR : V = R + (1 + I • ((s * a * a) • D) - (2 : ℂ)⁻¹ • ((s * a * a) • D) ^ 2 -
        (2 : ℂ)⁻¹ • ((s * a) ^ 2 • commP B)) := by rw [hR]; abel
    have hVR' : V' = R' + (1 + I • -((s * a * a) • D) - (2 : ℂ)⁻¹ • (-((s * a * a) • D)) ^ 2 -
        (2 : ℂ)⁻¹ • -((s * a) ^ 2 • commP B)) := by rw [hR']; abel
    have hre : ∀ W : GLN, ntr (reW W) = (2 : ℂ)⁻¹ * (ntr (W : Mat) + ntr ((W⁻¹ : GLN) : Mat)) :=
      fun W => by simp only [reW, ntr_smul, ntr_add']; norm_num
    have hIm : ntr (imW (plaq U μ ν x) * D) = (2 * I)⁻¹ * (ntr (P * D) - ntr (Pinv * D)) := by
      simp only [imW, Matrix.smul_mul, ntr_smul, Matrix.sub_mul, ntr_sub, P, Pinv]; norm_num
    have hRe : ntr (D ^ 2 * (reW (plaq U μ ν x) - 1)) =
        (2 : ℂ)⁻¹ * (ntr (P * D ^ 2) + ntr (Pinv * D ^ 2)) - ntr (D ^ 2) := by
      simp only [reW, mul_sub, mul_one, ntr_sub, Matrix.mul_smul, ntr_smul, mul_add, ntr_add',
        P, Pinv]
      rw [ntr_mul_comm (D ^ 2), ntr_mul_comm (D ^ 2)]; norm_num
    have hCm : ntr (commP B * imW (plaq U μ ν x)) =
        (2 * I)⁻¹ * (ntr (P * commP B) - ntr (Pinv * commP B)) := by
      simp only [imW, Matrix.mul_smul, ntr_smul, mul_sub, ntr_sub, P, Pinv]
      rw [ntr_mul_comm (commP B), ntr_mul_comm (commP B)]; norm_num
    rw [actionTerm, actionTerm, hre, hre, hW, hWi, hessTerm, hRe, hCm, hIm, hVR, hVR']
    simp only [mul_add, mul_sub, mul_one, Matrix.mul_smul, ntr_add', ntr_sub, ntr_smul, neg_sq,
      smul_pow, smul_neg, mul_neg, ntr_neg]
    field_simp
    ring_nf
    rw [I_sq]
    ring
  rw [key, norm_mul, norm_neg, norm_inv, Complex.norm_ofNat]
  have hPR := (norm_ntr_le_opNorm (P * R)).trans (norm_mul_le P R)
  have hPR' := (norm_ntr_le_opNorm (Pinv * R')).trans (norm_mul_le Pinv R')
  have hRn : ‖R‖ ≤ ‖s‖ ^ 3 * (c ^ 3 * Real.exp c) := by
    refine le_trans ?_ hφ
    convert hT using 2
  have hRn' : ‖R'‖ ≤ ‖s‖ ^ 3 * (c ^ 3 * Real.exp c) := by
    refine le_trans ?_ hφ
    convert hT' using 2
  calc 2⁻¹ * ‖ntr (P * R) + ntr (Pinv * R')‖ ≤ 2⁻¹ * (‖P‖ * ‖R‖ + ‖Pinv‖ * ‖R'‖) := by
        gcongr; exact (norm_add_le _ _).trans (add_le_add hPR hPR')
    _ ≤ 2⁻¹ * (‖P‖ * (‖s‖ ^ 3 * (c ^ 3 * Real.exp c)) +
          ‖Pinv‖ * (‖s‖ ^ 3 * (c ^ 3 * Real.exp c))) := by gcongr
    _ = (‖P‖ + ‖Pinv‖) / 2 * (c ^ 3 * Real.exp c) * ‖s‖ ^ 3 := by ring

/-! ### The sums over the plaquettes -/

/-- A sum over the positive plaquettes of a pairing of `2`-form components. -/
lemma sum_plaq_eq_pair2 (F F' : Form2 N n) :
    (∑ x : Site n, ∑ μ : Fin 4, ∑ ν : Fin 4,
      if μ < ν then a ^ 4 * ntr (F μ ν x * F' μ ν x) else 0) = pair2 a F F' := by
  unfold pair2 pair0
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ν _ => ?_
  split_ifs <;> simp

lemma D1_antisymm (U : Config N n) (A : Form1 N n) (μ ν : Fin 4) :
    D1 a U A ν μ = fun x => -D1 a U A μ ν x := by
  funext x; simp only [D1, neg_sub]

/-- The first-order terms: `Σ_p a² tr(Im U(∂p) (D_U A)(p)) = ⟨A, J(U)⟩`. -/
lemma sum_first_order [NeZero N] (hG : G.LieInput) (ha : a ≠ 0) {U : Config N n}
    (hU : ∀ μ x, U μ x ∈ G.complexified) {A : Form1 N n} (hA : ∀ μ x, A μ x ∈ G.lieC) :
    (∑ x : Site n, ∑ μ : Fin 4, ∑ ν : Fin 4,
      if μ < ν then a ^ 2 * ntr (imW (plaq U μ ν x) * D1 a U A μ ν x) else 0) =
      pair1 a A (current a hG U) := by
  rw [current, ← pair2_D1 a U A (curv a hG U) (fun μ ν _ => curv_antisymm a hG U μ ν),
    ← sum_plaq_eq_pair2]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun μ _ =>
    Finset.sum_congr rfl fun ν _ => ?_
  split_ifs
  · simp only [curv, Matrix.mul_smul, ntr_smul]
    rw [ntr_mul_proj hG (D1_mem a hG hU hA μ ν x), ntr_mul_comm]
    have ha2 : a ^ 2 ≠ 0 := pow_ne_zero 2 ha
    field_simp
  · rfl

/-- The terms with `(D_U A)(p)²`: `Σ_p a⁴ tr((D_U A)(p)²) = ⟨A, D^*_U D_U A⟩`. -/
lemma sum_second_order (U : Config N n) (A : Form1 N n) :
    (∑ x : Site n, ∑ μ : Fin 4, ∑ ν : Fin 4,
      if μ < ν then a ^ 4 * ntr (D1 a U A μ ν x ^ 2) else 0) =
      pair1 a A (Ds2 a U (D1 a U A)) := by
  rw [← pair2_D1 a U A (D1 a U A) (fun μ ν _ => D1_antisymm a U A μ ν), ← sum_plaq_eq_pair2]
  simp only [sq]

/-- `eq:action-expansion` along the ray `s ↦ sA`, with `⟨A, Δ(U)A⟩ = ⟨A, D^*D A⟩ + β(A, A)` and
`β(A, A)` the right side of `eq:hessian-form`: there is `K` with
`|A(e^{isaA}U) - A(U) - s⟨A, J(U)⟩ - (s²/2)(⟨A, D^*_U D_U A⟩ + β(A, A))| ≤ K|s|³` for `|s| ≤ 1`. -/
theorem action_expansion [NeZero N] (hG : G.LieInput) (ha : a ≠ 0) {U : Config N n}
    (hU : ∀ μ x, U μ x ∈ G.complexified) {A : Form1 N n} (hA : ∀ μ x, A μ x ∈ G.lieC) :
    ∃ K : ℝ, ∀ s : ℂ, ‖s‖ ≤ 1 →
      ‖action (expMul a (s • A) U) - action U - s * pair1 a A (current a hG U) -
        s ^ 2 / 2 * (pair1 a A (Ds2 a U (D1 a U A)) + hessForm a A U)‖ ≤ K * ‖s‖ ^ 3 := by
  choose K hK using fun (p : Site n × Fin 4 × Fin 4) =>
    actionTerm_expansion a ha A U p.2.1 p.2.2 p.1
  refine ⟨∑ x : Site n, ∑ μ : Fin 4, ∑ ν : Fin 4, |K (x, μ, ν)|, fun s hs => ?_⟩
  set E : Site n → Fin 4 → Fin 4 → ℂ := fun x μ ν =>
    actionTerm (expMul a (s • A) U) μ ν x - actionTerm U μ ν x -
      s * (a ^ 2 * ntr (imW (plaq U μ ν x) * D1 a U A μ ν x)) -
      s ^ 2 / 2 * (a ^ 4 * ntr (D1 a U A μ ν x ^ 2) + hessTerm a A U μ ν x)
  have key : action (expMul a (s • A) U) - action U - s * pair1 a A (current a hG U) -
      s ^ 2 / 2 * (pair1 a A (Ds2 a U (D1 a U A)) + hessForm a A U) =
      ∑ x : Site n, ∑ μ : Fin 4, ∑ ν : Fin 4, if μ < ν then E x μ ν else 0 := by
    rw [← sum_first_order a hG ha hU hA, ← sum_second_order, action, action, hessForm]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun μ _ =>
      Finset.sum_congr rfl fun ν _ => ?_
    split_ifs
    · simp only [E]
    · ring
  rw [key]
  have hs3 : 0 ≤ ‖s‖ ^ 3 := by positivity
  calc _ ≤ ∑ x : Site n, ∑ μ : Fin 4, ∑ ν : Fin 4, ‖if μ < ν then E x μ ν else 0‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => (norm_sum_le _ _).trans
          (Finset.sum_le_sum fun μ _ => norm_sum_le _ _))
    _ ≤ ∑ x : Site n, ∑ μ : Fin 4, ∑ ν : Fin 4, |K (x, μ, ν)| * ‖s‖ ^ 3 := by
        refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun μ _ =>
          Finset.sum_le_sum fun ν _ => ?_
        split_ifs
        · exact (hK (x, μ, ν) s hs).trans
            (mul_le_mul_of_nonneg_right (le_abs_self _) hs3)
        · simp only [norm_zero]; positivity
    _ = (∑ x : Site n, ∑ μ : Fin 4, ∑ ν : Fin 4, |K (x, μ, ν)|) * ‖s‖ ^ 3 := by
        simp only [Finset.sum_mul]

end CoreLean
