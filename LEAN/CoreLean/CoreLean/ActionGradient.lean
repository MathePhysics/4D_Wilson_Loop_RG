/-
`lem:cubic-gradient` of BALABAN_CORE.tex, the derivative of the action along a curve of configurations.

`lem:hessian`(i) (`hasDerivAt_action_expMul`) differentiates the action along `s ↦ e^{isaB}𝐔`. The derivative
depends only on the velocities of the values on the bonds at `s = 0`: if `t ↦ Γ_t` is a curve of
configurations with `Γ₀ = 𝐔` and `d/dt Γ_t(b)|_{t=0} = iaB(b)𝐔(b)` on the positive bonds, the plaquettes have
the derivative `(C₁ + C₂)P + P(C₃ + C₄)` of the exponential curve (`hasDerivAt_plaq_curve`, with the inverses
differentiated by `hasFDerivAt_ringInverse`), and the derivative of the action is `⟨B, J(𝐔)⟩`
(`hasDerivAt_action_curve`). This is the step of the proof of `lem:cubic-gradient` in which the curves
`e^{iη(A + tδ)}𝐔` and `e^{iηtEδ}(e^{iηA}𝐔)` are compared.
-/
import CoreLean.Hessian

open Matrix Complex
open scoped Matrix.Norms.L2Operator

namespace CoreLean

variable {N n : ℕ} [NeZero n] (a : ℂ)

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "GLN" => (Matrix (Fin N) (Fin N) ℂ)ˣ

variable {G : GaugeGroup N}

/-- The derivative of `t ↦ Γ_t⁻¹` for a curve of units with `Γ'₀ = XΓ₀`: `-Γ₀⁻¹X`. -/
lemma hasDerivAt_inv_curve (Γ : ℂ → GLN) (X : Mat)
    (h : HasDerivAt (fun t => ((Γ t : GLN) : Mat)) (X * (Γ 0 : Mat)) 0) :
    HasDerivAt (fun t => (((Γ t)⁻¹ : GLN) : Mat)) (-((((Γ 0)⁻¹ : GLN) : Mat) * X)) 0 := by
  have hinv := hasFDerivAt_ringInverse (𝕜 := ℂ) (Γ 0)
  have hc := hinv.comp_hasDerivAt 0 h
  have e : (fun t => (((Γ t)⁻¹ : GLN) : Mat)) = Ring.inverse ∘ fun t => ((Γ t : GLN) : Mat) := by
    funext t; simp [Ring.inverse_unit]
  rw [e]
  refine hc.congr_deriv ?_
  simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.mulLeftRight_apply]
  simp only [mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]

/-- The plaquettes along a curve with the velocities `iaB(b)𝐔(b)`. -/
lemma hasDerivAt_plaq_curve (Γ : ℂ → Config N n) (B : Form1 N n)
    (hΓ : ∀ μ x, HasDerivAt (fun t => ((Γ t μ x : GLN) : Mat))
      (((I * a) • B μ x) * ((Γ 0 μ x : GLN) : Mat)) 0) (μ ν : Fin 4) (x : Site n) :
    HasDerivAt (fun t => ((plaq (Γ t) μ ν x : GLN) : Mat))
      ((((I * a) • B μ x) + ((I * a) • Ad (Γ 0 μ x) (B ν (x + unit n μ)))) *
          ((plaq (Γ 0) μ ν x : GLN) : Mat) +
        ((plaq (Γ 0) μ ν x : GLN) : Mat) *
          (((I * a) • Ad (Γ 0 ν x) (-B μ (x + unit n ν))) + ((I * a) • -B ν x))) 0 := by
  set U := Γ 0
  have e : (fun t => ((plaq (Γ t) μ ν x : GLN) : Mat)) = fun t =>
      ((Γ t μ x : GLN) : Mat) * ((Γ t ν (x + unit n μ) : GLN) : Mat) *
        (((Γ t μ (x + unit n ν))⁻¹ : GLN) : Mat) * (((Γ t ν x)⁻¹ : GLN) : Mat) := by
    funext t; rw [plaq_eq]; simp only [Units.val_mul]
  rw [e]
  have h1 := hΓ μ x
  have h2 := hΓ ν (x + unit n μ)
  have h3 := hasDerivAt_inv_curve (fun t => Γ t μ (x + unit n ν)) _ (hΓ μ (x + unit n ν))
  have h4 := hasDerivAt_inv_curve (fun t => Γ t ν x) _ (hΓ ν x)
  have h := ((h1.mul h2).mul h3).mul h4
  refine h.congr_deriv ?_
  have hP : ((plaq U μ ν x : GLN) : Mat) = (U μ x : Mat) * (U ν (x + unit n μ) : Mat) *
      (((U μ (x + unit n ν))⁻¹ : GLN) : Mat) * (((U ν x)⁻¹ : GLN) : Mat) := by
    rw [plaq_eq]; simp only [Units.val_mul]
  have hUU : ∀ W : GLN, ((W : Mat)) * (((W⁻¹ : GLN) : Mat)) = 1 := fun W => by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hUU' : ∀ W : GLN, (((W⁻¹ : GLN) : Mat)) * ((W : Mat)) = 1 := fun W => by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  simp only [hP, Ad, smul_mul_assoc, mul_smul_comm, Pi.mul_apply, Matrix.mul_neg, Matrix.neg_mul,
    smul_neg, mul_add, add_mul, mul_assoc]
  simp only [← mul_assoc, hUU, hUU', one_mul, mul_one]
  simp only [mul_assoc]
  abel

/-- The derivative of `t ↦ Γ_t⁻¹` for a curve of units with `Γ'₀ = D`: `-Γ₀⁻¹DΓ₀⁻¹`. -/
lemma hasDerivAt_inv_curve' (Γ : ℂ → GLN) (D : Mat)
    (h : HasDerivAt (fun t => ((Γ t : GLN) : Mat)) D 0) :
    HasDerivAt (fun t => (((Γ t)⁻¹ : GLN) : Mat))
      (-((((Γ 0)⁻¹ : GLN) : Mat) * D * (((Γ 0)⁻¹ : GLN) : Mat))) 0 := by
  have hinv := hasFDerivAt_ringInverse (𝕜 := ℂ) (Γ 0)
  have hc := hinv.comp_hasDerivAt 0 h
  have e : (fun t => (((Γ t)⁻¹ : GLN) : Mat)) = Ring.inverse ∘ fun t => ((Γ t : GLN) : Mat) := by
    funext t; simp
  rw [e]
  refine hc.congr_deriv ?_
  simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.mulLeftRight_apply]

/-- The derivative of `tr Re` of a plaquette along a curve with the velocities `iaB(b)𝐔(b)`:
`-a² tr(Im 𝐔(∂p) (D_𝐔B)(p))`, as for the exponential curve. -/
lemma hasDerivAt_ntr_reW_curve (ha : a ≠ 0) (Γ : ℂ → Config N n) (B : Form1 N n)
    (hΓ : ∀ μ x, HasDerivAt (fun t => ((Γ t μ x : GLN) : Mat))
      (((I * a) • B μ x) * ((Γ 0 μ x : GLN) : Mat)) 0) (μ ν : Fin 4) (x : Site n) :
    HasDerivAt (fun t : ℂ => ntr (reW (plaq (Γ t) μ ν x)))
      (-((a : ℂ) ^ 2 * ntr (imW (plaq (Γ 0) μ ν x) * D1 a (Γ 0) B μ ν x))) 0 := by
  set U := Γ 0
  set C₁ := (I * a) • B μ x
  set C₂ := (I * a) • Ad (U μ x) (B ν (x + unit n μ))
  set C₃ := (I * a) • Ad (U ν x) (-B μ (x + unit n ν))
  set C₄ := (I * a) • -B ν x
  set P : Mat := (plaq U μ ν x : Mat)
  set Pinv : Mat := (((plaq U μ ν x)⁻¹ : GLN) : Mat)
  have hplaq := hasDerivAt_plaq_curve a Γ B hΓ μ ν x
  have hW := ntrL.hasFDerivAt.comp_hasDerivAt 0 hplaq
  have hWi := ntrL.hasFDerivAt.comp_hasDerivAt 0
    (hasDerivAt_inv_curve' (fun t => plaq (Γ t) μ ν x) _ hplaq)
  have h := (hW.add hWi).const_mul ((1 / 2 : ℂ))
  have hsum : C₁ + C₂ + C₃ + C₄ = (I * a * a) • D1 a U B μ ν x := by
    have := productExponent_sum a ha B U μ ν x
    simp only [C₁, C₂, C₃, C₄, ← smul_add]
    rw [this, smul_smul]
  set D := D1 a U B μ ν x
  have hPinv : ntr (Pinv * D) = ntr (P * D) - (2 * I) * ntr (imW (plaq U μ ν x) * D) := by
    have hP : Pinv = P - (2 * I) • imW (plaq U μ ν x) := by
      simp only [imW, smul_smul, P, Pinv]
      rw [show 2 * I * (1 / (2 * I)) = 1 by field_simp, one_smul]
      abel
    rw [hP, Matrix.sub_mul, ntr_sub, Matrix.smul_mul, ntr_smul]
  have hPP : P * Pinv = 1 := by
    simp only [P, Pinv]; rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hPP' : Pinv * P = 1 := by
    simp only [P, Pinv]; rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  refine (h.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
  · simp only [Function.comp_apply, ntrL_apply]
    have e1 : ntr ((C₁ + C₂) * P + P * (C₃ + C₄)) = ntr (P * (C₁ + C₂ + C₃ + C₄)) := by
      rw [ntr_add', ntr_mul_comm (C₁ + C₂), ← ntr_add', ← mul_add, add_assoc (C₁ + C₂)]
    have e2 : ntr (-(Pinv * ((C₁ + C₂) * P + P * (C₃ + C₄)) * Pinv)) =
        -ntr (Pinv * (C₁ + C₂ + C₃ + C₄)) := by
      have hm : Pinv * ((C₁ + C₂) * P + P * (C₃ + C₄)) * Pinv =
          Pinv * (C₁ + C₂) + (C₃ + C₄) * Pinv := by
        calc Pinv * ((C₁ + C₂) * P + P * (C₃ + C₄)) * Pinv
            = Pinv * (C₁ + C₂) * (P * Pinv) + (Pinv * P) * (C₃ + C₄) * Pinv := by noncomm_ring
          _ = Pinv * (C₁ + C₂) + (C₃ + C₄) * Pinv := by rw [hPP, hPP', mul_one, one_mul]
      have hneg : ∀ X : Mat, ntr (-X) = -ntr X := fun X => by simp [ntr, Matrix.trace_neg]
      have hs : ntr (Pinv * (C₁ + C₂) + (C₃ + C₄) * Pinv) = ntr (Pinv * (C₁ + C₂ + C₃ + C₄)) := by
        rw [ntr_add', ntr_mul_comm (C₃ + C₄), ← ntr_add', ← mul_add, ← add_assoc]
      rw [hm, hneg, hs]
    rw [e1, e2, hsum, Matrix.mul_smul, Matrix.mul_smul, ntr_smul, ntr_smul, hPinv]
    linear_combination (a ^ 2 * ntr (imW (plaq U μ ν x) * D)) * I_mul_I
  · simp [reW, ntr_smul, ntr_add', ntrL_apply]
    ring

/-- The derivative of the action along a curve with the velocities `iaB(b)𝐔(b)`: `⟨B, J(𝐔)⟩`
(`lem:hessian`(i) for curves). -/
theorem hasDerivAt_action_curve [NeZero N] (hG : G.LieInput) (ha : a ≠ 0) (Γ : ℂ → Config N n)
    (hU : ∀ μ x, Γ 0 μ x ∈ G.complexified) (B : Form1 N n) (hB : ∀ μ x, B μ x ∈ G.lieC)
    (hΓ : ∀ μ x, HasDerivAt (fun t => ((Γ t μ x : GLN) : Mat))
      (((I * a) • B μ x) * ((Γ 0 μ x : GLN) : Mat)) 0) :
    HasDerivAt (fun t : ℂ => action (Γ t)) (pair1 a B (current a hG (Γ 0))) 0 := by
  have hterm : ∀ (x : Site n) (μ ν : Fin 4), HasDerivAt
      (fun t : ℂ => if μ < ν then actionTerm (Γ t) μ ν x else 0)
      (if μ < ν then (a : ℂ) ^ 4 * ntr (D1 a (Γ 0) B μ ν x * curv a hG (Γ 0) μ ν x) else 0) 0 := by
    intro x μ ν
    split_ifs with h
    · have h1 := (hasDerivAt_ntr_reW_curve a ha Γ B hΓ μ ν x).const_sub 1
      refine h1.congr_deriv ?_
      simp only [neg_neg, curv, Matrix.mul_smul, ntr_smul]
      rw [ntr_mul_proj hG (D1_mem a hG hU hB μ ν x), ntr_mul_comm]
      have ha2 : (a : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 (by exact_mod_cast ha)
      push_cast
      field_simp
    · exact hasDerivAt_const _ _
  have hsum := HasDerivAt.sum (u := Finset.univ) fun x _ =>
    HasDerivAt.sum (u := Finset.univ) fun μ _ =>
      HasDerivAt.sum (u := Finset.univ) fun ν _ => hterm x μ ν
  refine hsum.congr_deriv ?_ |>.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun s => by simp [action, Finset.sum_apply])
  rw [current, ← pair2_D1 a (Γ 0) B (curv a hG (Γ 0)) (fun μ ν _ => curv_antisymm a hG (Γ 0) μ ν)]
  unfold pair2 pair0
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ν _ => ?_
  split_ifs <;> simp

/-! ### The velocity of `t ↦ e^{ia(A + tδ)}𝐔` -/

section Velocity

variable {𝔹 : Type*} [NormedRing 𝔹] [NormedAlgebra ℂ 𝔹] [CompleteSpace 𝔹]

/-- `e^Tφ(-T) = φ(T)` for `φ(T) = (e^T - 1)/T = Σ T^p/(p + 1)!`. -/
lemma exp_mul_expSubOneDiv_neg (T : 𝔹) :
    NormedSpace.exp T * BakerCampbellHausdorff.expSubOneDiv ℂ (-T) =
      BakerCampbellHausdorff.expSubOneDiv ℂ T := by
  have h := BakerCampbellHausdorff.hasSum_exp_mul_expSubOneDiv (𝕂 := ℂ) (Commute.neg_right
    (Commute.refl T))
  have e : ∀ p : ℕ, ((p + 1).factorial : ℂ)⁻¹ • ∑ i ∈ Finset.range (p + 1), T ^ i * (T + -T) ^ (p - i) =
      ((p + 1).factorial : ℂ)⁻¹ • T ^ p := by
    intro p
    congr 1
    rw [add_neg_cancel, Finset.sum_range_succ, Nat.sub_self, pow_zero, mul_one]
    rw [Finset.sum_eq_zero fun i hi => by
      rw [zero_pow (by have := Finset.mem_range.mp hi; omega), mul_zero], zero_add]
  simp only [e] at h
  exact h.unique (BakerCampbellHausdorff.hasSum_expSubOneDiv (𝕂 := ℂ) T)

end Velocity

/-- `E_Z δ = φ(ad Z)δ`, the operator `∫₀¹ Ad_{e^{sZ}} ds` of the core with `Z = iaA(b)`. -/
noncomputable def Eop (Z : Mat) : Mat →L[ℂ] Mat :=
  BakerCampbellHausdorff.expSubOneDiv ℂ (BakerCampbellHausdorff.ad ℂ Z)

/-- The velocity: `d/dt e^{ia(A + tδ)(b)}𝐔(b)|_{t=0} = ia(E_{iaA(b)}δ(b))·e^{iaA(b)}𝐔(b)`. -/
lemma hasDerivAt_expMul_add (A δ : Form1 N n) (U : Config N n) (μ : Fin 4) (x : Site n) :
    HasDerivAt (fun t : ℂ => ((expMul a (A + t • δ) U μ x : GLN) : Mat))
      (((I * a) • Eop ((I * a) • A μ x) (δ μ x)) * ((expMul a A U μ x : GLN) : Mat)) 0 := by
  set Z := (I * a) • A μ x
  set W := (I * a) • δ μ x
  have e : (fun t : ℂ => ((expMul a (A + t • δ) U μ x : GLN) : Mat)) =
      fun t => NormedSpace.exp (Z + t • W) * ((U μ x : GLN) : Mat) := by
    funext t
    simp only [expMul, Units.val_mul, expU_val, Pi.add_apply, Pi.smul_apply, Z, W, smul_add,
      smul_comm (I * a) t]
  rw [e]
  have h := (BakerCampbellHausdorff.hasDerivAt_exp_add_smul (𝕂 := ℂ) Z W).mul_const
    ((U μ x : GLN) : Mat)
  refine h.congr_deriv ?_
  -- `e^Zφ(-ad Z)W = (φ(ad Z)W)e^Z`
  have hop : NormedSpace.exp (BakerCampbellHausdorff.ad ℂ Z) *
      BakerCampbellHausdorff.expSubOneDiv ℂ (-BakerCampbellHausdorff.ad ℂ Z) =
      BakerCampbellHausdorff.expSubOneDiv ℂ (BakerCampbellHausdorff.ad ℂ Z) :=
    exp_mul_expSubOneDiv_neg _
  have hY : ∀ Y : Mat, NormedSpace.exp Z * Y =
      (NormedSpace.exp (BakerCampbellHausdorff.ad ℂ Z) Y) * NormedSpace.exp Z := by
    intro Y
    rw [BakerCampbellHausdorff.exp_ad_apply, mul_assoc, mul_assoc,
      BakerCampbellHausdorff.exp_neg_mul_exp ℂ Z, mul_one]
  rw [hY, ← ContinuousLinearMap.mul_apply, hop]
  simp only [Eop, W, map_smul, expMul, Units.val_mul, expU_val, smul_mul_assoc, mul_assoc]
  rfl

end CoreLean
