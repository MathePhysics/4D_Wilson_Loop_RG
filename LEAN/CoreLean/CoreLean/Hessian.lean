/-
`def:current` and `lem:hessian`(i) of BALABAN_CORE.tex: the part of the first order of
`A(e^{iηA}U)` is `⟨A, J(U)⟩`.

The part of the first order in `A` of the entire function `A ↦ A(e^{iηA}U)` is its derivative along
the ray: `d/ds A(e^{isηA}U)|_{s=0}`. The proof is the core's: by `lem:product-plaquette` the plaquette
of `e^{isηA}U` is `E₁E₂ U(∂p) E₃E₄` with `E_k = e^{isηB_k}`, whose derivative at `s = 0` is
`iη(B₁ + B₂)U(∂p) + U(∂p) iη(B₃ + B₄)`; with the cyclicity of the trace and `ΣB_k = η(D_U A)(p)`
the derivative of `1 - tr Re U(∂p)` is `η² tr((D_U A)(p) Im U(∂p))`; since `(D_U A)(p) ∈ 𝔤^c`,
`Im` may be replaced by `π Im`, and `lem:covariance`(i) gives `⟨A, D^*_U F(U)⟩`.
-/
import CoreLean.Psi

open NormedSpace Complex
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace CoreLean

variable {N n : ℕ} [NeZero n] (a : ℂ)

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "GLN" => (Matrix (Fin N) (Fin N) ℂ)ˣ

variable {G : GaugeGroup N}

/-- The curvature `F(U)_{μν}(x) = a⁻² π Im U(∂p_{μν}(x))` (`def:current`(i)). -/
def curv (hG : G.LieInput) (U : Config N n) : Form2 N n :=
  fun μ ν x => (a ^ 2)⁻¹ • piProj hG (imW (plaq U μ ν x))

/-- The current `J(U) = D^*_U F(U)` (`eq:current`). -/
def current (hG : G.LieInput) (U : Config N n) : Form1 N n := Ds2 a U (curv a hG U)

lemma plaq_swap (U : Config N n) (μ ν : Fin 4) (x : Site n) :
    plaq U ν μ x = (plaq U μ ν x)⁻¹ := by
  rw [plaq_eq, plaq_eq]; group

lemma imW_inv (W : GLN) : imW W⁻¹ = -imW W := by
  rw [imW, imW, inv_inv, ← smul_neg, neg_sub]

lemma curv_antisymm (hG : G.LieInput) (U : Config N n) (μ ν : Fin 4) :
    curv a hG U ν μ = fun x => -curv a hG U μ ν x := by
  funext x
  have h : piProj hG (-imW (plaq U μ ν x)) = -piProj hG (imW (plaq U μ ν x)) := by
    rw [← neg_one_smul ℂ (imW _), proj_smul, neg_one_smul]
  show (a ^ 2)⁻¹ • piProj hG (imW (plaq U ν μ x)) = -((a ^ 2)⁻¹ • piProj hG (imW (plaq U μ ν x)))
  rw [plaq_swap, imW_inv, h, smul_neg]

/-- `tr Z πY = tr Z Y` for `Z ∈ 𝔤^c`. -/
lemma ntr_mul_proj [NeZero N] (hG : G.LieInput) {Z : Mat} (hZ : Z ∈ G.lieC) (Y : Mat) :
    ntr (Z * piProj hG Y) = ntr (Z * Y) := by
  have h := (orth_iff G).mp (fun Z hZ => proj_orth hG Y hZ) Z hZ
  rw [mul_sub, ntr_sub, sub_eq_zero] at h
  exact h.symm

/-- `(D_U A)(p) ∈ 𝔤^c` for a configuration with values in `G^c` and a form with values in `𝔤^c`. -/
lemma D1_mem (hG : G.LieInput) {U : Config N n} (hU : ∀ μ x, U μ x ∈ G.complexified)
    {A : Form1 N n} (hA : ∀ μ x, A μ x ∈ G.lieC) (μ ν : Fin 4) (x : Site n) :
    D1 a U A μ ν x ∈ G.lieC := by
  have hD : ∀ μ' ν' : Fin 4, Dfw a U μ' (A ν') x ∈ G.lieC := fun μ' ν' => by
    simp only [Dfw]
    refine (GaugeGroup.lieCSubmodule hG).smul_mem a⁻¹ ?_
    exact (GaugeGroup.lieCSubmodule hG).sub_mem
      (GaugeGroup.Ad_mem_lieC hG (hU μ' x) (hA ν' _)) (hA ν' x)
  exact (GaugeGroup.lieCSubmodule hG).sub_mem (hD μ ν) (hD ν μ)

/-! ### The derivative of one plaquette -/

/-- The normalised trace as a continuous linear functional. -/
def ntrL : Mat →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap ((N : ℂ)⁻¹ • Matrix.traceLinearMap (Fin N) ℂ ℂ)

lemma ntrL_apply (X : Mat) : ntrL X = ntr X := by
  simp [ntrL, ntr]

lemma ntr_add' (X Y : Mat) : ntr (X + Y) = ntr X + ntr Y := by
  simp [ntr, Matrix.trace_add, mul_add]

lemma ntr_mul_comm (X Y : Mat) : ntr (X * Y) = ntr (Y * X) := by
  rw [ntr, ntr, Matrix.trace_mul_comm]

/-- The value of the plaquette of `e^{isaA}U` and of its inverse, as products of exponentials. -/
lemma plaq_expMul_smul (A : Form1 N n) (U : Config N n) (μ ν : Fin 4) (x : Site n) (s : ℂ) :
    ((plaq (expMul a (s • A) U) μ ν x : GLN) : Mat) =
      exp (s • ((I * a) • A μ x)) * exp (s • ((I * a) • Ad (U μ x) (A ν (x + unit n μ)))) *
        (plaq U μ ν x : Mat) * exp (s • ((I * a) • Ad (U ν x) (-A μ (x + unit n ν)))) *
        exp (s • ((I * a) • -A ν x)) ∧
    ((((plaq (expMul a (s • A) U) μ ν x)⁻¹ : GLN) : Mat)) =
      exp (s • -((I * a) • -A ν x)) * exp (s • -((I * a) • Ad (U ν x) (-A μ (x + unit n ν)))) *
        ((plaq U μ ν x)⁻¹ : GLN) * exp (s • -((I * a) • Ad (U μ x) (A ν (x + unit n μ)))) *
        exp (s • -((I * a) • A μ x)) := by
  have hc : ∀ B : Mat, (I * a) • (s • B) = s • ((I * a) • B) := fun B => smul_comm _ _ _
  have hp := plaq_expMul a (s • A) U μ ν x
  simp only [Pi.smul_apply, Ad_smul, ← smul_neg, hc] at hp
  constructor
  · rw [hp]; simp only [Units.val_mul, expU_val]
  · rw [hp]
    simp only [mul_inv_rev, expU_inv, Units.val_mul, expU_val, smul_neg]
    simp only [mul_assoc]

/-- The derivative at `s = 0` of `s ↦ exp(sC₁) exp(sC₂) P exp(sC₃) exp(sC₄)`. -/
lemma hasDerivAt_prod_exp (C₁ C₂ C₃ C₄ P : Mat) :
    HasDerivAt (fun s : ℂ => exp (s • C₁) * exp (s • C₂) * P * exp (s • C₃) * exp (s • C₄))
      ((C₁ + C₂) * P + P * (C₃ + C₄)) 0 := by
  have h1 := hasDerivAt_exp_smul_const (𝕂 := ℂ) C₁ 0
  have h2 := hasDerivAt_exp_smul_const (𝕂 := ℂ) C₂ 0
  have h3 := hasDerivAt_exp_smul_const (𝕂 := ℂ) C₃ 0
  have h4 := hasDerivAt_exp_smul_const (𝕂 := ℂ) C₄ 0
  have hP := hasDerivAt_const (0 : ℂ) P
  have h := (((h1.mul h2).mul hP).mul h3).mul h4
  refine h.congr_deriv ?_
  simp only [Pi.mul_apply, zero_smul, NormedSpace.exp_zero, one_mul, mul_one, mul_zero, add_zero]
  noncomm_ring

/-- The derivative of `tr Re` of the plaquette of `e^{isaA}U` at `s = 0`:
`-a² tr(Im U(∂p) (D_U A)(p))`. -/
lemma hasDerivAt_ntr_reW (ha : a ≠ 0) (A : Form1 N n) (U : Config N n) (μ ν : Fin 4)
    (x : Site n) :
    HasDerivAt (fun s : ℂ => ntr (reW (plaq (expMul a (s • A) U) μ ν x)))
      (-((a : ℂ) ^ 2 * ntr (imW (plaq U μ ν x) * D1 a U A μ ν x))) 0 := by
  set C₁ := (I * a) • A μ x
  set C₂ := (I * a) • Ad (U μ x) (A ν (x + unit n μ))
  set C₃ := (I * a) • Ad (U ν x) (-A μ (x + unit n ν))
  set C₄ := (I * a) • -A ν x
  set P : Mat := (plaq U μ ν x : Mat)
  set Pinv : Mat := (((plaq U μ ν x)⁻¹ : GLN) : Mat)
  -- the derivatives of the two traces
  have hW := (ntrL.hasFDerivAt.comp_hasDerivAt 0 (hasDerivAt_prod_exp C₁ C₂ C₃ C₄ P))
  have hWi := (ntrL.hasFDerivAt.comp_hasDerivAt 0
    (hasDerivAt_prod_exp (-C₄) (-C₃) (-C₂) (-C₁) Pinv))
  have h := (hW.add hWi).const_mul ((1 / 2 : ℂ))
  -- the sum of the four exponents
  have hsum : C₁ + C₂ + C₃ + C₄ = (I * a * a) • D1 a U A μ ν x := by
    have := productExponent_sum a ha A U μ ν x
    simp only [C₁, C₂, C₃, C₄, ← smul_add]
    rw [this, smul_smul]
  set D := D1 a U A μ ν x
  -- `Im P = (2i)⁻¹(P - P⁻¹)`, so `tr(P⁻¹ D) = tr(P D) - 2i tr(Im P · D)`
  have hPinv : ntr (Pinv * D) = ntr (P * D) - (2 * I) * ntr (imW (plaq U μ ν x) * D) := by
    have hP : Pinv = P - (2 * I) • imW (plaq U μ ν x) := by
      simp only [imW, smul_smul, P, Pinv]
      rw [show 2 * I * (1 / (2 * I)) = 1 by field_simp, one_smul]
      abel
    rw [hP, Matrix.sub_mul, ntr_sub, Matrix.smul_mul, ntr_smul]
  refine (h.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
  · simp only [Function.comp_apply, ntrL_apply]
    -- `tr((C₁ + C₂)P + P(C₃ + C₄)) = tr(P ΣC)`, and the same for the inverse
    have e1 : ntr ((C₁ + C₂) * P + P * (C₃ + C₄)) = ntr (P * (C₁ + C₂ + C₃ + C₄)) := by
      rw [ntr_add', ntr_mul_comm (C₁ + C₂), ← ntr_add', ← mul_add, add_assoc (C₁ + C₂)]
    have e2 : ntr ((-C₄ + -C₃) * Pinv + Pinv * (-C₂ + -C₁)) =
        -ntr (Pinv * (C₁ + C₂ + C₃ + C₄)) := by
      rw [ntr_add', ntr_mul_comm (-C₄ + -C₃), ← ntr_add', ← mul_add,
        show -C₄ + -C₃ + (-C₂ + -C₁) = -(C₁ + C₂ + C₃ + C₄) by abel, mul_neg]
      simp [ntr, Matrix.trace_neg]
    rw [e1, e2, hsum, Matrix.mul_smul, Matrix.mul_smul, ntr_smul, ntr_smul, hPinv]
    linear_combination (a ^ 2 * ntr (imW (plaq U μ ν x) * D)) * I_mul_I
  · simp only [reW, ntr_smul, ntr_add']
    obtain ⟨h1, h2⟩ := plaq_expMul_smul a A U μ ν x s
    rw [h1, h2]
    simp only [Function.comp_apply, ntrL_apply, Pinv, P, smul_neg, neg_neg, C₁, C₂, C₃, C₄,
      Pi.add_apply]

/-! ### `lem:hessian`(i) -/

/-- `lem:hessian`(i): the part of the first order in `A` of `A(e^{iaA}U)` is `⟨A, J(U)⟩`, for a
configuration with values in `G^c` and a form with values in `𝔤^c`. -/
theorem hasDerivAt_action_expMul [NeZero N] (hG : G.LieInput) (ha : a ≠ 0) {U : Config N n}
    (hU : ∀ μ x, U μ x ∈ G.complexified) {A : Form1 N n} (hA : ∀ μ x, A μ x ∈ G.lieC) :
    HasDerivAt (fun s : ℂ => action (expMul a (s • A) U)) (pair1 a A (current a hG U)) 0 := by
  -- each term of the action
  have hterm : ∀ (x : Site n) (μ ν : Fin 4), HasDerivAt
      (fun s : ℂ => if μ < ν then actionTerm (expMul a (s • A) U) μ ν x else 0)
      (if μ < ν then (a : ℂ) ^ 4 * ntr (D1 a U A μ ν x * curv a hG U μ ν x) else 0) 0 := by
    intro x μ ν
    split_ifs with h
    · have h1 := (hasDerivAt_ntr_reW a ha A U μ ν x).const_sub 1
      refine h1.congr_deriv ?_
      simp only [neg_neg, curv, Matrix.mul_smul, ntr_smul]
      rw [ntr_mul_proj hG (D1_mem a hG hU hA μ ν x), ntr_mul_comm]
      have ha2 : (a : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 (by exact_mod_cast ha)
      push_cast
      field_simp
    · exact hasDerivAt_const _ _
  have hsum := HasDerivAt.sum (u := Finset.univ) fun x _ =>
    HasDerivAt.sum (u := Finset.univ) fun μ _ =>
      HasDerivAt.sum (u := Finset.univ) fun ν _ => hterm x μ ν
  refine hsum.congr_deriv ?_ |>.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun s => by simp [action, Finset.sum_apply])
  -- the value: `Σ_x Σ_{μ<ν} a⁴ tr((D_U A)_{μν}(x) F_{μν}(x)) = ⟨D_U A, F⟩ = ⟨A, D^*_U F⟩`
  rw [current, ← pair2_D1 a U A (curv a hG U) (fun μ ν _ => curv_antisymm a hG U μ ν)]
  unfold pair2 pair0
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ν _ => ?_
  split_ifs <;> simp

end CoreLean
