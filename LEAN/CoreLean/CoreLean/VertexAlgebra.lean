/-
`lem:vertex` of BALABAN_CORE.tex, the exact identities of its proof.

* `leibniz_fw`, `leibniz_bw` (`eq:leibniz`): since `Ad_{𝐔(b)}` is an automorphism of the algebra,
  `D_μ[f, g] = [D_μf, g] + [f, D_μg] + η[D_μf, D_μg]`, and the same for `D^*_μ`.
* `gaugeDefect_eq`: with `Ad_{𝐔(b)}λ(b₊) = λ(b₋) + η(D_μλ)(b₋)`, the gauge defect `X(A)` of `eq:gauge-defect` is the
  value at `A₁ = A₂ = A` of the bilinear expression `2i[λ₁, A₂] - iη[A₂, Dλ₁] - i[λ₁, Dλ₂]`.
* `vertex_polarised` (`eq:vertex-polarised`): for a symmetric linear `Δ'_π` with `⟨A, Δ'_πA⟩ = ⟨X(A), 𝐉⟩` and a
  linear gauge function `λ_A = ΛA`, `2⟨A₁, Δ'_πA₂⟩ = ⟨Ξᵃ, 𝐉⟩ + ⟨Ξ, 𝐉⟩` with
  `Ξᵃ = 2i[λ₂, A₁] - iη[A₁, Dλ₂]` and `Ξ = 2i[λ₁, A₂] - iη[A₂, Dλ₁] - i[λ₁, Dλ₂] - i[λ₂, Dλ₁]`.
* `pair_Xi_a` (the terms with `A₁`, first step): `⟨Ξᵃ, 𝐉⟩ = ⟨A₁, m⟩`, `m_μ = 2i[𝐉_μ, λ₂] - iη[D_μλ₂, 𝐉_μ]`, by the
  invariance of the trace.
* `mVert_decomp` (the terms with `A₁`): for `𝐉 = D^*K + Dψ + p`, `m = D^*(2i[K, λ]) + D(2i[ψ, λ]) + m̃`, with `m̃`
  (`mTilde`) the commutators of `p` with `λ`, of `K_{νμ}` and `ηD^*_νK_{νμ}` with `D^*_νλ`, of `ψ` and `ηD_μψ` with
  `D_μλ`, and `-iη[D_μλ, 𝐉_μ]`, by `eq:leibniz` applied to `[D^*_νK_{νμ}, λ]` and `[D_μψ, λ]`.
-/
import CoreLean.Potentials
import CoreLean.CubicBound

open Matrix Complex
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace CoreLean

variable {N n : ℕ} [NeZero n] (a : ℂ)

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "GLN" => (Matrix (Fin N) (Fin N) ℂ)ˣ

variable {G : GaugeGroup N}

lemma Ad_brk (W : GLN) (X Y : Mat) : Ad W (brk X Y) = brk (Ad W X) (Ad W Y) := by
  have h : ∀ X Y : Mat, Ad W (X * Y) = Ad W X * Ad W Y := fun X Y => by
    simp only [Ad, mul_assoc]
    rw [← mul_assoc ((W⁻¹ : GLN) : Mat), ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
  simp only [brk, Ad_sub, h]

lemma brk_sub_left (X X' Y : Mat) : brk (X - X') Y = brk X Y - brk X' Y := by
  simp only [brk, sub_mul, mul_sub]; abel

lemma brk_sub_right (X Y Y' : Mat) : brk X (Y - Y') = brk X Y - brk X Y' := by
  simp only [brk, sub_mul, mul_sub]; abel

lemma brk_smul_left' (c : ℂ) (X Y : Mat) : brk (c • X) Y = c • brk X Y := by
  simp only [brk, Matrix.mul_smul, Matrix.smul_mul, smul_sub]

/-- The unscaled rule: `[F, G] - [f, g] = [F - f, g] + [f, G - g] + [F - f, G - g]`. -/
lemma brk_diff (F G f g : Mat) :
    brk F G - brk f g = brk (F - f) g + brk f (G - g) + brk (F - f) (G - g) := by
  simp only [brk]; noncomm_ring

lemma leibniz_scaled (ha : a ≠ 0) (F G f g : Mat) :
    a⁻¹ • (brk F G - brk f g) = brk (a⁻¹ • (F - f)) g + brk f (a⁻¹ • (G - g)) +
      a • brk (a⁻¹ • (F - f)) (a⁻¹ • (G - g)) := by
  rw [brk_diff, brk_smul_left', brk_smul_right, brk_smul_left', brk_smul_right, smul_smul, smul_smul,
    smul_add, smul_add]
  congr 2
  field_simp

/-- `eq:leibniz` for the forward difference. -/
theorem leibniz_fw (ha : a ≠ 0) (U : Config N n) (μ : Fin 4) (f g : Form0 N n) (x : Site n) :
    Dfw a U μ (fun y => brk (f y) (g y)) x =
      brk (Dfw a U μ f x) (g x) + brk (f x) (Dfw a U μ g x) + a • brk (Dfw a U μ f x) (Dfw a U μ g x) := by
  simp only [Dfw, Ad_brk]
  exact leibniz_scaled a ha _ _ _ _

/-- `eq:leibniz` for the backward difference. -/
theorem leibniz_bw (ha : a ≠ 0) (U : Config N n) (μ : Fin 4) (f g : Form0 N n) (x : Site n) :
    Dbw a U μ (fun y => brk (f y) (g y)) x =
      brk (Dbw a U μ f x) (g x) + brk (f x) (Dbw a U μ g x) + a • brk (Dbw a U μ f x) (Dbw a U μ g x) := by
  simp only [Dbw, Ad_brk]
  exact leibniz_scaled a ha _ _ _ _

/-- `Ad_{𝐔(b)}λ(b₊) = λ(b₋) + η(D_μλ)(b₋)`. -/
lemma Ad_eq_add_Dfw (ha : a ≠ 0) (U : Config N n) (μ : Fin 4) (l : Form0 N n) (x : Site n) :
    Ad (U μ x) (l (x + unit n μ)) = l x + a • Dfw a U μ l x := by
  simp only [Dfw, smul_smul, mul_inv_cancel₀ ha, one_smul]
  abel

/-- The bilinear expression of the gauge defect: `2i[λ₁, A₂] - iη[A₂, Dλ₁] - i[λ₁, Dλ₂]`. -/
def defectBil (U : Config N n) (l₁ l₂ : Form0 N n) (A₂ : Form1 N n) : Form1 N n :=
  fun μ x => (2 * I) • brk (l₁ x) (A₂ μ x) - (I * a) • brk (A₂ μ x) (Dfw a U μ l₁ x) -
    I • brk (l₁ x) (Dfw a U μ l₂ x)

/-- `X(A)` is the value of the bilinear expression at `A₁ = A₂ = A`. -/
theorem gaugeDefect_eq (ha : a ≠ 0) (U : Config N n) (l : Form0 N n) (A : Form1 N n) :
    gaugeDefect a U l A = defectBil a U l l A := by
  funext μ x
  simp only [gaugeDefect, defectBil, D0, Ad_eq_add_Dfw a ha, brk_add_right, brk_smul_right]
  have h : brk (A μ x) (l x) = -brk (l x) (A μ x) := by simp only [brk]; abel
  rw [h]
  module

lemma defectBil_add (U : Config N n) (l₁ l₂ m₁ m₂ : Form0 N n) (A B : Form1 N n) :
    defectBil a U (l₁ + m₁) (l₂ + m₂) (A + B) =
      defectBil a U l₁ l₂ A + defectBil a U m₁ m₂ B + defectBil a U l₁ m₂ B + defectBil a U m₁ l₂ A := by
  have hD : ∀ (μ : Fin 4) (f g : Form0 N n) (x : Site n), Dfw a U μ (f + g) x = Dfw a U μ f x + Dfw a U μ g x :=
    fun μ f g x => by simp only [Dfw, Pi.add_apply, Ad_add, smul_sub, smul_add]; abel
  funext μ x
  simp only [defectBil, Pi.add_apply, hD, brk_add_left, brk_add_right, smul_add]
  abel

/-- `eq:vertex-polarised`: `2⟨A₁, Δ'_πA₂⟩ = ⟨Ξᵃ, 𝐉⟩ + ⟨Ξ, 𝐉⟩`. -/
theorem vertex_polarised (ha : a ≠ 0) (hG : G.LieInput) (U : Config N n) (J : Form1 N n)
    (Λ : Form1 N n →ₗ[ℂ] Form0 N n) (Δ'π : Form1 N n →ₗ[ℂ] Form1 N n)
    (hΔ : ∀ A ∈ lieForms hG, pair1 a A (Δ'π A) = pair1 a (gaugeDefect a U (Λ A) A) J)
    (hsym : ∀ X ∈ lieForms hG, ∀ Y ∈ lieForms hG, pair1 a X (Δ'π Y) = pair1 a Y (Δ'π X))
    {A₁ A₂ : Form1 N n} (h₁ : A₁ ∈ lieForms hG) (h₂ : A₂ ∈ lieForms hG) :
    2 * pair1 a A₁ (Δ'π A₂) =
      pair1 a (fun μ x => (2 * I) • brk (Λ A₂ x) (A₁ μ x) - (I * a) • brk (A₁ μ x) (Dfw a U μ (Λ A₂) x)) J +
      pair1 a (fun μ x => (2 * I) • brk (Λ A₁ x) (A₂ μ x) - (I * a) • brk (A₂ μ x) (Dfw a U μ (Λ A₁) x) -
        I • brk (Λ A₁ x) (Dfw a U μ (Λ A₂) x) - I • brk (Λ A₂ x) (Dfw a U μ (Λ A₁) x)) J := by
  have hs := hΔ (A₁ + A₂) ((lieForms hG).add_mem h₁ h₂)
  have hs₁ := hΔ A₁ h₁
  have hs₂ := hΔ A₂ h₂
  have hsy := hsym A₂ h₂ A₁ h₁
  rw [gaugeDefect_eq a ha, LinearMap.map_add Λ, defectBil_add] at hs
  rw [gaugeDefect_eq a ha] at hs₁ hs₂
  rw [LinearMap.map_add Δ'π, pair1_add_left, pair1_add_right, pair1_add_right, pair1_add_left, pair1_add_left,
    pair1_add_left] at hs
  -- the cross terms of the bilinear expression are `Ξᵃ + Ξ`
  have hcross : pair1 a (defectBil a U (Λ A₁) (Λ A₂) A₂) J + pair1 a (defectBil a U (Λ A₂) (Λ A₁) A₁) J =
      pair1 a (fun μ x => (2 * I) • brk (Λ A₂ x) (A₁ μ x) - (I * a) • brk (A₁ μ x) (Dfw a U μ (Λ A₂) x)) J +
      pair1 a (fun μ x => (2 * I) • brk (Λ A₁ x) (A₂ μ x) - (I * a) • brk (A₂ μ x) (Dfw a U μ (Λ A₁) x) -
        I • brk (Λ A₁ x) (Dfw a U μ (Λ A₂) x) - I • brk (Λ A₂ x) (Dfw a U μ (Λ A₁) x)) J := by
    rw [← pair1_add_left, ← pair1_add_left]
    congr 1
    funext μ x
    simp only [defectBil, Pi.add_apply]
    abel
  linear_combination hs - hs₁ - hs₂ - hsy + hcross

/-- The terms with `A₁`, first step: `⟨Ξᵃ, 𝐉⟩ = ⟨A₁, m⟩`, `m_μ = 2i[𝐉_μ, λ₂] - iη[D_μλ₂, 𝐉_μ]`. -/
theorem pair_Xi_a (U : Config N n) (J A₁ : Form1 N n) (l₂ : Form0 N n) :
    pair1 a (fun μ x => (2 * I) • brk (l₂ x) (A₁ μ x) - (I * a) • brk (A₁ μ x) (Dfw a U μ l₂ x)) J =
      pair1 a A₁ (fun μ x => (2 * I) • brk (J μ x) (l₂ x) - (I * a) • brk (Dfw a U μ l₂ x) (J μ x)) := by
  unfold pair1 pair0
  refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun x _ => ?_
  congr 1
  simp only [brk, sub_mul, mul_sub, smul_mul_assoc, Matrix.mul_smul, ntr_sub, ntr_smul]
  have t1 : ntr (l₂ x * A₁ μ x * J μ x) = ntr (A₁ μ x * (J μ x * l₂ x)) := by
    rw [Matrix.mul_assoc, ntr_mul_comm, Matrix.mul_assoc]
  have t2 : ntr (A₁ μ x * l₂ x * J μ x) = ntr (A₁ μ x * (l₂ x * J μ x)) := by rw [Matrix.mul_assoc]
  have t3 : ntr (A₁ μ x * Dfw a U μ l₂ x * J μ x) = ntr (A₁ μ x * (Dfw a U μ l₂ x * J μ x)) := by
    rw [Matrix.mul_assoc]
  have t4 : ntr (Dfw a U μ l₂ x * A₁ μ x * J μ x) = ntr (A₁ μ x * (J μ x * Dfw a U μ l₂ x)) := by
    rw [Matrix.mul_assoc, ntr_mul_comm, Matrix.mul_assoc]
  rw [t1, t2, t3, t4]

/-! ### The terms with `A₁`: the decomposition of `m` -/

lemma Dbw_smul' (U : Config N n) (ν : Fin 4) (c : ℂ) (f : Form0 N n) (x : Site n) :
    Dbw a U ν (fun y => c • f y) x = c • Dbw a U ν f x := by
  simp only [Dbw, Ad_smul, smul_sub, smul_comm c a⁻¹]

lemma Dfw_smul' (U : Config N n) (μ : Fin 4) (c : ℂ) (f : Form0 N n) (x : Site n) :
    Dfw a U μ (fun y => c • f y) x = c • Dfw a U μ f x := by
  simp only [Dfw, Ad_smul, smul_sub, smul_comm c a⁻¹]

/-- `m_μ = 2i[𝐉_μ, λ] - iη[D_μλ, 𝐉_μ]`. -/
def mVert (U : Config N n) (J : Form1 N n) (l : Form0 N n) : Form1 N n :=
  fun μ x => (2 * I) • brk (J μ x) (l x) - (I * a) • brk (Dfw a U μ l x) (J μ x)

/-- `m̃`: the commutators of `p` with `λ`, of `K_{νμ}` and `ηD^*_νK_{νμ}` with `D^*_νλ`, of `ψ` and `ηD_μψ` with
`D_μλ`, and `-iη[D_μλ, 𝐉_μ]`. -/
def mTilde (U : Config N n) (K : Form2 N n) (ψ : Form0 N n) (p J : Form1 N n) (l : Form0 N n) :
    Form1 N n :=
  fun μ x => (2 * I) • brk (p μ x) (l x) -
    (2 * I) • ∑ ν, (if ν ≠ μ then brk (K ν μ x) (Dbw a U ν l x) +
      a • brk (Dbw a U ν (K ν μ) x) (Dbw a U ν l x) else 0) -
    (2 * I) • (brk (ψ x) (Dfw a U μ l x) + a • brk (Dfw a U μ ψ x) (Dfw a U μ l x)) -
    (I * a) • brk (Dfw a U μ l x) (J μ x)

/-- The terms with `A₁`: for `𝐉 = D^*K + Dψ + p`, `m = D^*(2i[K, λ]) + D(2i[ψ, λ]) + m̃`, by `eq:leibniz`. -/
theorem mVert_decomp (ha : a ≠ 0) (U : Config N n) (K : Form2 N n) (ψ : Form0 N n) (p : Form1 N n)
    (l : Form0 N n) :
    mVert a U (Ds2 a U K + D0 a U ψ + p) l =
      Ds2 a U (fun ν μ y => (2 * I) • brk (K ν μ y) (l y)) + D0 a U (fun y => (2 * I) • brk (ψ y) (l y)) +
        mTilde a U K ψ p (Ds2 a U K + D0 a U ψ + p) l := by
  funext μ x
  -- `[D^*_νK_{νμ}, λ] = D^*_ν[K_{νμ}, λ] - [K_{νμ}, D^*_νλ] - η[D^*_νK_{νμ}, D^*_νλ]`
  have hK : ∀ ν, brk (Dbw a U ν (K ν μ) x) (l x) = Dbw a U ν (fun y => brk (K ν μ y) (l y)) x -
      (brk (K ν μ x) (Dbw a U ν l x) + a • brk (Dbw a U ν (K ν μ) x) (Dbw a U ν l x)) := fun ν => by
    rw [leibniz_bw a ha]; abel
  have hψ : brk (Dfw a U μ ψ x) (l x) = Dfw a U μ (fun y => brk (ψ y) (l y)) x -
      (brk (ψ x) (Dfw a U μ l x) + a • brk (Dfw a U μ ψ x) (Dfw a U μ l x)) := by
    rw [leibniz_fw a ha]; abel
  have hsum : brk (∑ ν, (if ν ≠ μ then Dbw a U ν (K ν μ) x else 0)) (l x) =
      ∑ ν, (if ν ≠ μ then Dbw a U ν (fun y => brk (K ν μ y) (l y)) x else 0) -
      ∑ ν, (if ν ≠ μ then brk (K ν μ x) (Dbw a U ν l x) +
        a • brk (Dbw a U ν (K ν μ) x) (Dbw a U ν l x) else 0) := by
    simp only [brk, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun ν _ => ?_
    split_ifs
    · have := hK ν; simp only [brk] at this; rw [this]
    · simp
  have hDs2 : Ds2 a U (fun ν μ y => (2 * I) • brk (K ν μ y) (l y)) μ x =
      (2 * I) • ∑ ν, (if ν ≠ μ then Dbw a U ν (fun y => brk (K ν μ y) (l y)) x else 0) := by
    simp only [Ds2, Finset.smul_sum]
    refine Finset.sum_congr rfl fun ν _ => ?_
    split_ifs
    · exact Dbw_smul' a U ν (2 * I) (fun y => brk (K ν μ y) (l y)) x
    · simp
  have hD0 : D0 a U (fun y => (2 * I) • brk (ψ y) (l y)) μ x =
      (2 * I) • Dfw a U μ (fun y => brk (ψ y) (l y)) x := Dfw_smul' a U μ (2 * I) _ x
  simp only [mVert, mTilde, Pi.add_apply, hDs2, hD0]
  simp only [Ds2, D0, brk_add_left, hsum, hψ]
  module

/-! ### The bound of `m̃` -/

lemma norm_brk_le' (X Y : Mat) : ‖brk X Y‖ ≤ 2 * ‖X‖ * ‖Y‖ := by
  unfold brk
  calc ‖X * Y - Y * X‖ ≤ ‖X * Y‖ + ‖Y * X‖ := norm_sub_le _ _
    _ ≤ ‖X‖ * ‖Y‖ + ‖Y‖ * ‖X‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ = 2 * ‖X‖ * ‖Y‖ := by ring

/-- `‖ηD^*_νf(x)‖ ≤ 2‖f(x - ηe_ν)‖ + ‖f(x)‖` when the transport doubles the norm at most. -/
lemma norm_a_dbw_le (ha : a ≠ 0) (U : Config N n) (ν : Fin 4) (x : Site n) (f : Form0 N n)
    (hV : ∀ Z : Mat, ‖Ad (U.val ⟨x, ν, false⟩) Z‖ ≤ 2 * ‖Z‖) :
    ‖a‖ * ‖Dbw a U ν f x‖ ≤ 2 * ‖f (x - unit n ν)‖ + ‖f x‖ := by
  have h := norm_dbw_le a U ν x f hV
  have hη : 0 < ‖a‖ := norm_pos_iff.mpr ha
  calc ‖a‖ * ‖Dbw a U ν f x‖ ≤ ‖a‖ * (‖a‖⁻¹ * (2 * ‖f (x - unit n ν)‖ + ‖f x‖)) :=
        mul_le_mul_of_nonneg_left h hη.le
    _ = 2 * ‖f (x - unit n ν)‖ + ‖f x‖ := by field_simp

/-- `‖ηD_μf(x)‖ ≤ 2‖f(x + ηe_μ)‖ + ‖f(x)‖` when the transport doubles the norm at most. -/
lemma norm_a_dfw_le (ha : a ≠ 0) (U : Config N n) (μ : Fin 4) (x : Site n) (f : Form0 N n)
    (hT : ∀ Z : Mat, ‖Ad (U μ x) Z‖ ≤ 2 * ‖Z‖) :
    ‖a‖ * ‖Dfw a U μ f x‖ ≤ 2 * ‖f (x + unit n μ)‖ + ‖f x‖ := by
  have hη : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have e : ‖a‖ * ‖Dfw a U μ f x‖ = ‖Ad (U μ x) (f (x + unit n μ)) - f x‖ := by
    simp only [Dfw, norm_smul, norm_inv, ← mul_assoc, mul_inv_cancel₀ hη.ne', one_mul]
  rw [e]
  exact (norm_sub_le _ _).trans (add_le_add (hT _) le_rfl)

/-- The bound of `m̃` at a bond, in the local quantities: with `‖p‖ ≤ P`, `‖λ‖ ≤ Λ₀`, the differences of `λ` at
most `Λ₁`, `K` and `ψ` at most `K̄` and `Ψ` at the sites concerned, and transports which double the norm at most,
`‖m̃_μ(x)‖ ≤ 66(P(Λ₀ + ηΛ₁) + (K̄ + Ψ)Λ₁)` (the core's `‖m̃‖ ≤ C_Vw₁`, `C_V = 400`, since `ηΛ₁ ≤ 3Λ₀` for the
differences of `λ`). -/
theorem norm_mTilde_le (ha : a ≠ 0) (U : Config N n) (K : Form2 N n) (ψ : Form0 N n) (p : Form1 N n)
    (l : Form0 N n) (μ : Fin 4) (x : Site n) {P Λ₀ Λ₁ Kb Ψ : ℝ}
    (hP : ‖p μ x‖ ≤ P) (hl₀ : ‖l x‖ ≤ Λ₀) (hl₁b : ∀ ν, ν ≠ μ → ‖Dbw a U ν l x‖ ≤ Λ₁)
    (hl₁f : ‖Dfw a U μ l x‖ ≤ Λ₁)
    (hK : ∀ ν, ν ≠ μ → ‖K ν μ x‖ ≤ Kb ∧ ‖K ν μ (x - unit n ν)‖ ≤ Kb)
    (hψ : ‖ψ x‖ ≤ Ψ ∧ ‖ψ (x + unit n μ)‖ ≤ Ψ)
    (hV : ∀ ν, ν ≠ μ → ∀ Z : Mat, ‖Ad (U.val ⟨x, ν, false⟩) Z‖ ≤ 2 * ‖Z‖)
    (hT : ∀ Z : Mat, ‖Ad (U μ x) Z‖ ≤ 2 * ‖Z‖) :
    ‖mTilde a U K ψ p (Ds2 a U K + D0 a U ψ + p) l μ x‖ ≤
      66 * (P * (Λ₀ + ‖a‖ * Λ₁) + (Kb + Ψ) * Λ₁) := by
  have hη := norm_nonneg a
  have hP0 : 0 ≤ P := (norm_nonneg _).trans hP
  have hΛ₀ : 0 ≤ Λ₀ := (norm_nonneg _).trans hl₀
  have hΛ₁ : 0 ≤ Λ₁ := (norm_nonneg _).trans hl₁f
  have hΨ : 0 ≤ Ψ := (norm_nonneg _).trans hψ.1
  obtain ⟨ν₀, hν₀⟩ : ∃ ν : Fin 4, ν ≠ μ := ⟨μ + 1, by simp⟩
  have hKb : 0 ≤ Kb := (norm_nonneg _).trans (hK ν₀ hν₀).1
  have hI : ‖(2 * I : ℂ)‖ = 2 := by simp
  have hIa : ‖(I * a : ℂ)‖ = ‖a‖ := by simp
  -- `‖ηD^*_νK_{νμ}(x)‖ ≤ 3K̄`, `‖ηD_μψ(x)‖ ≤ 3Ψ`
  have hDK : ∀ ν, ν ≠ μ → ‖a‖ * ‖Dbw a U ν (K ν μ) x‖ ≤ 3 * Kb := fun ν hν => by
    have := norm_a_dbw_le a ha U ν x (K ν μ) (hV ν hν)
    linarith [(hK ν hν).1, (hK ν hν).2]
  have hDψ : ‖a‖ * ‖Dfw a U μ ψ x‖ ≤ 3 * Ψ := by
    have := norm_a_dfw_le a ha U μ x ψ hT
    linarith [hψ.1, hψ.2]
  -- `‖η𝐉_μ(x)‖ ≤ 9K̄ + 3Ψ + ηP`
  have hJ : ‖a‖ * ‖(Ds2 a U K + D0 a U ψ + p) μ x‖ ≤ 9 * Kb + 3 * Ψ + ‖a‖ * P := by
    simp only [Pi.add_apply, Ds2, D0]
    have h1 : ‖a‖ * ‖∑ ν, (if ν ≠ μ then Dbw a U ν (K ν μ) x else 0)‖ ≤ 9 * Kb := by
      have := norm_sum_ne_le (μ := μ) (f := fun ν => (a • Dbw a U ν (K ν μ) x)) (B := 3 * Kb)
        fun ν hν => by rw [norm_smul]; exact hDK ν hν
      rw [← norm_smul, Finset.smul_sum]
      refine le_trans (le_of_eq ?_) (this.trans (le_of_eq (by ring)))
      congr 1
      refine Finset.sum_congr rfl fun ν _ => ?_
      split_ifs <;> simp
    calc ‖a‖ * ‖∑ ν, (if ν ≠ μ then Dbw a U ν (K ν μ) x else 0) + Dfw a U μ ψ x + p μ x‖
        ≤ ‖a‖ * (‖∑ ν, (if ν ≠ μ then Dbw a U ν (K ν μ) x else 0)‖ + ‖Dfw a U μ ψ x‖ + ‖p μ x‖) :=
          mul_le_mul_of_nonneg_left (norm_add₃_le) hη
      _ ≤ 9 * Kb + 3 * Ψ + ‖a‖ * P := by nlinarith [norm_nonneg (p μ x)]
  -- the four groups of terms
  have t1 : ‖(2 * I : ℂ) • brk (p μ x) (l x)‖ ≤ 4 * (P * Λ₀) := by
    rw [norm_smul, hI]
    have := norm_brk_le' (p μ x) (l x)
    have := mul_le_mul hP hl₀ (norm_nonneg _) hP0
    nlinarith [norm_nonneg (p μ x), norm_nonneg (l x)]
  have t2 : ‖(2 * I : ℂ) • ∑ ν, (if ν ≠ μ then brk (K ν μ x) (Dbw a U ν l x) +
      a • brk (Dbw a U ν (K ν μ) x) (Dbw a U ν l x) else 0)‖ ≤ 48 * (Kb * Λ₁) := by
    rw [norm_smul, hI]
    have h := norm_sum_ne_le (μ := μ) (B := 8 * (Kb * Λ₁))
      (f := fun ν => brk (K ν μ x) (Dbw a U ν l x) + a • brk (Dbw a U ν (K ν μ) x) (Dbw a U ν l x))
      fun ν hν => by
        have b1 := norm_brk_le' (K ν μ x) (Dbw a U ν l x)
        have b2 := norm_brk_le' (Dbw a U ν (K ν μ) x) (Dbw a U ν l x)
        have hk := (hK ν hν).1
        have hd := hl₁b ν hν
        have hdk := hDK ν hν
        calc ‖brk (K ν μ x) (Dbw a U ν l x) + a • brk (Dbw a U ν (K ν μ) x) (Dbw a U ν l x)‖
            ≤ ‖brk (K ν μ x) (Dbw a U ν l x)‖ + ‖a‖ * ‖brk (Dbw a U ν (K ν μ) x) (Dbw a U ν l x)‖ := by
              rw [← norm_smul]; exact norm_add_le _ _
          _ ≤ 2 * Kb * Λ₁ + ‖a‖ * (2 * ‖Dbw a U ν (K ν μ) x‖ * Λ₁) := by
              refine add_le_add (b1.trans ?_) (mul_le_mul_of_nonneg_left (b2.trans ?_) hη)
              · exact mul_le_mul (mul_le_mul_of_nonneg_left hk (by norm_num)) hd (norm_nonneg _)
                  (by positivity)
              · exact mul_le_mul_of_nonneg_left hd (by positivity)
          _ = 2 * Kb * Λ₁ + 2 * (‖a‖ * ‖Dbw a U ν (K ν μ) x‖) * Λ₁ := by ring
          _ ≤ 2 * Kb * Λ₁ + 2 * (3 * Kb) * Λ₁ := by gcongr
          _ = 8 * (Kb * Λ₁) := by ring
    linarith
  have t3 : ‖(2 * I : ℂ) • (brk (ψ x) (Dfw a U μ l x) + a • brk (Dfw a U μ ψ x) (Dfw a U μ l x))‖ ≤
      16 * (Ψ * Λ₁) := by
    rw [norm_smul, hI]
    have b1 := norm_brk_le' (ψ x) (Dfw a U μ l x)
    have b2 := norm_brk_le' (Dfw a U μ ψ x) (Dfw a U μ l x)
    have h : ‖brk (ψ x) (Dfw a U μ l x) + a • brk (Dfw a U μ ψ x) (Dfw a U μ l x)‖ ≤ 8 * (Ψ * Λ₁) := by
      calc ‖brk (ψ x) (Dfw a U μ l x) + a • brk (Dfw a U μ ψ x) (Dfw a U μ l x)‖
          ≤ ‖brk (ψ x) (Dfw a U μ l x)‖ + ‖a‖ * ‖brk (Dfw a U μ ψ x) (Dfw a U μ l x)‖ := by
            rw [← norm_smul]; exact norm_add_le _ _
        _ ≤ 2 * Ψ * Λ₁ + ‖a‖ * (2 * ‖Dfw a U μ ψ x‖ * Λ₁) := by
            refine add_le_add (b1.trans ?_) (mul_le_mul_of_nonneg_left (b2.trans ?_) hη)
            · exact mul_le_mul (mul_le_mul_of_nonneg_left hψ.1 (by norm_num)) hl₁f (norm_nonneg _)
                (by positivity)
            · exact mul_le_mul_of_nonneg_left hl₁f (by positivity)
        _ = 2 * Ψ * Λ₁ + 2 * (‖a‖ * ‖Dfw a U μ ψ x‖) * Λ₁ := by ring
        _ ≤ 2 * Ψ * Λ₁ + 2 * (3 * Ψ) * Λ₁ := by gcongr
        _ = 8 * (Ψ * Λ₁) := by ring
    linarith
  have t4 : ‖(I * a : ℂ) • brk (Dfw a U μ l x) ((Ds2 a U K + D0 a U ψ + p) μ x)‖ ≤
      2 * Λ₁ * (9 * Kb + 3 * Ψ + ‖a‖ * P) := by
    rw [norm_smul, hIa]
    have b := norm_brk_le' (Dfw a U μ l x) ((Ds2 a U K + D0 a U ψ + p) μ x)
    calc ‖a‖ * ‖brk (Dfw a U μ l x) ((Ds2 a U K + D0 a U ψ + p) μ x)‖
        ≤ ‖a‖ * (2 * ‖Dfw a U μ l x‖ * ‖(Ds2 a U K + D0 a U ψ + p) μ x‖) :=
          mul_le_mul_of_nonneg_left b hη
      _ = 2 * ‖Dfw a U μ l x‖ * (‖a‖ * ‖(Ds2 a U K + D0 a U ψ + p) μ x‖) := by ring
      _ ≤ 2 * Λ₁ * (9 * Kb + 3 * Ψ + ‖a‖ * P) := by gcongr
  have hsum4 := norm_sub_le ((2 * I : ℂ) • brk (p μ x) (l x) -
      (2 * I : ℂ) • ∑ ν, (if ν ≠ μ then brk (K ν μ x) (Dbw a U ν l x) +
        a • brk (Dbw a U ν (K ν μ) x) (Dbw a U ν l x) else 0) -
      (2 * I : ℂ) • (brk (ψ x) (Dfw a U μ l x) + a • brk (Dfw a U μ ψ x) (Dfw a U μ l x)))
    ((I * a : ℂ) • brk (Dfw a U μ l x) ((Ds2 a U K + D0 a U ψ + p) μ x))
  have hsum3 := norm_sub_le ((2 * I : ℂ) • brk (p μ x) (l x) -
      (2 * I : ℂ) • ∑ ν, (if ν ≠ μ then brk (K ν μ x) (Dbw a U ν l x) +
        a • brk (Dbw a U ν (K ν μ) x) (Dbw a U ν l x) else 0))
    ((2 * I : ℂ) • (brk (ψ x) (Dfw a U μ l x) + a • brk (Dfw a U μ ψ x) (Dfw a U μ l x)))
  have hsum2 := norm_sub_le ((2 * I : ℂ) • brk (p μ x) (l x))
    ((2 * I : ℂ) • ∑ ν, (if ν ≠ μ then brk (K ν μ x) (Dbw a U ν l x) +
        a • brk (Dbw a U ν (K ν μ) x) (Dbw a U ν l x) else 0))
  simp only [mTilde]
  nlinarith [mul_nonneg hP0 hΛ₀, mul_nonneg hKb hΛ₁, mul_nonneg hΨ hΛ₁, mul_nonneg hP0 hΛ₁,
    mul_nonneg hη (mul_nonneg hP0 hΛ₁)]

end CoreLean
