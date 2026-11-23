/-
`lem:cubic-gradient` of BALABAN_CORE.tex, the gradient of the action.

With `E_Z = φ(ad Z)` (`Eop`, the core's `𝖤_X = ∫₀¹ Ad_{e^{isX}} ds` for `Z = iX`), the derivative of
`t ↦ A(e^{ia(A + tδ)}𝐔)` at `t = 0` is `⟨E_{iaA}δ, J(e^{iaA}𝐔)⟩` (`hasDerivAt_action_curve` with the velocity of
`hasDerivAt_expMul_add`), and since `tr((φ(ad Z)X)Y) = tr(Xφ(ad(-Z))Y)` (`ntr_Eop_mul`) it is `⟨δ, 𝒥(A)⟩` with
`𝒥(A)(b) = E_{-iaA(b)}J(e^{iaA}𝐔)(b)` (`hasDerivAt_action_add`): this is the gradient of the action of the
proof of `lem:cubic-gradient`.
-/
import CoreLean.ActionGradient
import CoreLean.HessianOperator

open Matrix Complex BakerCampbellHausdorff
open scoped Matrix.Norms.L2Operator

namespace CoreLean

variable {N n : ℕ} [NeZero n] (a : ℂ)

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "GLN" => (Matrix (Fin N) (Fin N) ℂ)ˣ

variable {G : GaugeGroup N}

/-- `e^{iaA}𝐔` has values in `G^c` if `𝐔` does and `A` has values in `𝔤^c`. -/
lemma expMul_mem (hG : G.LieInput) {U : Config N n} (hU : ∀ μ x, U μ x ∈ G.complexified)
    {A : Form1 N n} (hA : ∀ μ x, A μ x ∈ G.lieC) (μ : Fin 4) (x : Site n) :
    expMul a A U μ x ∈ G.complexified := by
  refine G.complexified.mul_mem (Subgroup.subset_closure ⟨a • A μ x, ?_, ?_⟩) (hU μ x)
  · exact (GaugeGroup.lieCSubmodule hG).smul_mem a (hA μ x)
  · simp only [mul_smul]

/-- `(ad Z)^k` maps `𝔤^c` into itself for `Z ∈ 𝔤^c`. -/
lemma ad_pow_mem (hG : G.LieInput) {Z : Mat} (hZ : Z ∈ G.lieC) (k : ℕ) {X : Mat} (hX : X ∈ G.lieC) :
    (ad ℂ Z ^ k) X ∈ G.lieC := by
  induction k with
  | zero => simpa using hX
  | succ k ih =>
    rw [pow_succ', ContinuousLinearMap.mul_apply, ad_apply]
    exact GaugeGroup.commutator_mem_lieC hG hZ ih

/-- `E_Z` maps `𝔤^c` into itself for `Z ∈ 𝔤^c`. -/
lemma Eop_mem (hG : G.LieInput) {Z : Mat} (hZ : Z ∈ G.lieC) {X : Mat} (hX : X ∈ G.lieC) :
    Eop Z X ∈ G.lieC := by
  have hsum := (hasSum_expSubOneDiv (𝕂 := ℂ) (ad ℂ Z)).mapL (ContinuousLinearMap.apply ℂ Mat X)
  have hclosed : IsClosed (G.lieC : Set Mat) := by
    have hset : ((GaugeGroup.lieCSubmodule hG : Submodule ℂ Mat) : Set Mat) = G.lieC :=
      Set.ext fun X => GaugeGroup.mem_lieCSubmodule hG
    rw [← hset]
    exact (GaugeGroup.lieCSubmodule hG).closed_of_finiteDimensional
  refine hclosed.mem_of_tendsto hsum.tendsto_sum_nat (Filter.Eventually.of_forall fun m => ?_)
  refine (GaugeGroup.lieCSubmodule hG).sum_mem fun k _ => ?_
  simp only [ContinuousLinearMap.apply_apply, ContinuousLinearMap.smul_apply]
  exact (GaugeGroup.lieCSubmodule hG).smul_mem _ (ad_pow_mem hG hZ k hX)

/-- `tr(((ad Z)^k X)Y) = tr(X((ad(-Z))^k Y))`. -/
lemma ntr_ad_pow_mul (Z : Mat) (k : ℕ) (X Y : Mat) :
    ntr ((ad ℂ Z ^ k) X * Y) = ntr (X * (ad ℂ (-Z) ^ k) Y) := by
  induction k generalizing Y with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', ContinuousLinearMap.mul_apply, ad_apply, pow_succ,
      ContinuousLinearMap.mul_apply, ← ih (ad ℂ (-Z) Y), ad_apply]
    simp only [sub_mul, mul_sub, ntr_sub, neg_mul, mul_neg]
    rw [ntr_mul_comm (Z * _) Y, ntr_mul_comm ((ad ℂ Z ^ k) X * Z) Y]
    simp only [← mul_assoc, ntr, Matrix.trace_neg]
    have c1 : (Y * Z * (ad ℂ Z ^ k) X).trace = ((ad ℂ Z ^ k) X * Y * Z).trace :=
      Matrix.trace_mul_cycle Y Z _
    have c2 : (Y * (ad ℂ Z ^ k) X * Z).trace = ((ad ℂ Z ^ k) X * Z * Y).trace := by
      rw [Matrix.trace_mul_cycle Y _ Z, Matrix.trace_mul_cycle Z Y _]
    rw [c1, c2]
    ring

/-- `tr((E_Z X)Y) = tr(X(E_{-Z}Y))`. -/
lemma ntr_Eop_mul (Z X Y : Mat) : ntr (Eop Z X * Y) = ntr (X * Eop (-Z) Y) := by
  set f : (Mat →L[ℂ] Mat) →L[ℂ] ℂ :=
    ntrL.comp ((ContinuousLinearMap.mul ℂ Mat).flip Y |>.comp (ContinuousLinearMap.apply ℂ Mat X))
  set g : (Mat →L[ℂ] Mat) →L[ℂ] ℂ :=
    ntrL.comp ((ContinuousLinearMap.mul ℂ Mat X).comp (ContinuousLinearMap.apply ℂ Mat Y))
  have h1 := (hasSum_expSubOneDiv (𝕂 := ℂ) (ad ℂ Z)).mapL f
  have h2 := (hasSum_expSubOneDiv (𝕂 := ℂ) (ad ℂ (-Z))).mapL g
  have hf : ∀ S : Mat →L[ℂ] Mat, f S = ntr (S X * Y) := fun S => by
    simp [f, ntrL_apply]
  have hg : ∀ S : Mat →L[ℂ] Mat, g S = ntr (X * S Y) := fun S => by
    simp [g, ntrL_apply]
  have e : (fun k : ℕ => f ((((k + 1).factorial : ℂ)⁻¹) • ad ℂ Z ^ k)) =
      fun k => g ((((k + 1).factorial : ℂ)⁻¹) • ad ℂ (-Z) ^ k) := by
    funext k
    rw [hf, hg]
    simp only [ContinuousLinearMap.smul_apply, smul_mul_assoc, mul_smul_comm, ntr_smul]
    rw [ntr_ad_pow_mul]
  rw [e] at h1
  have := h1.unique h2
  rw [hf, hg] at this
  exact this

/-- `𝒥(A)(b) = E_{-iaA(b)}J(e^{iaA}𝐔)(b)`, the gradient of the action at `A`. -/
noncomputable def gradAction [NeZero N] (hG : G.LieInput) (U : Config N n) (A : Form1 N n) :
    Form1 N n :=
  fun μ x => Eop (-((I * a) • A μ x)) (current a hG (expMul a A U) μ x)

/-- The gradient of the action: `d/dt A(e^{ia(A + tδ)}𝐔)|_{t=0} = ⟨δ, 𝒥(A)⟩`. -/
theorem hasDerivAt_action_add [NeZero N] (hG : G.LieInput) (ha : a ≠ 0) {U : Config N n}
    (hU : ∀ μ x, U μ x ∈ G.complexified) {A : Form1 N n} (hA : ∀ μ x, A μ x ∈ G.lieC)
    {δ : Form1 N n} (hδ : ∀ μ x, δ μ x ∈ G.lieC) :
    HasDerivAt (fun t : ℂ => action (expMul a (A + t • δ) U))
      (pair1 a δ (gradAction a hG U A)) 0 := by
  set Γ : ℂ → Config N n := fun t => expMul a (A + t • δ) U
  have hΓ0 : Γ 0 = expMul a A U := by simp [Γ]
  set B : Form1 N n := fun μ x => Eop ((I * a) • A μ x) (δ μ x)
  have hB : ∀ μ x, B μ x ∈ G.lieC := fun μ x =>
    Eop_mem hG ((GaugeGroup.lieCSubmodule hG).smul_mem _ (hA μ x)) (hδ μ x)
  have hU' : ∀ μ x, Γ 0 μ x ∈ G.complexified := fun μ x => by
    rw [hΓ0]; exact expMul_mem a hG hU hA μ x
  have hvel : ∀ μ x, HasDerivAt (fun t => ((Γ t μ x : GLN) : Mat))
      (((I * a) • B μ x) * ((Γ 0 μ x : GLN) : Mat)) 0 := fun μ x => by
    rw [hΓ0]; exact hasDerivAt_expMul_add a A δ U μ x
  have h := hasDerivAt_action_curve a hG ha Γ hU' B hB hvel
  rw [hΓ0] at h
  refine h.congr_deriv ?_
  unfold pair1 pair0
  refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun x _ => ?_
  simp only [B, gradAction]
  rw [ntr_Eop_mul]

/-! ### The gradient of `𝖵₀` -/

lemma pair1_add_left (X Y F : Form1 N n) : pair1 a (X + Y) F = pair1 a X F + pair1 a Y F := by
  simp only [pair1, pair0, Pi.add_apply, add_mul, ntr_add', mul_add, Finset.sum_add_distrib]

lemma pair1_smul_left (c : ℂ) (X F : Form1 N n) : pair1 a (c • X) F = c * pair1 a X F := by
  simp only [pair1, pair0, Pi.smul_apply, smul_mul_assoc, ntr_smul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun x _ => by ring

lemma pair1_add_right (X F F' : Form1 N n) : pair1 a X (F + F') = pair1 a X F + pair1 a X F' := by
  simp only [pair1, pair0, Pi.add_apply, mul_add, ntr_add', Finset.sum_add_distrib]

lemma pair1_sub_right (X F F' : Form1 N n) : pair1 a X (F - F') = pair1 a X F - pair1 a X F' := by
  simp only [pair1, pair0, Pi.sub_apply, mul_sub, ntr_sub, Finset.sum_sub_distrib]

lemma pair2_add_left (F F' G : Form2 N n) : pair2 a (F + F') G = pair2 a F G + pair2 a F' G := by
  simp only [pair2, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => ?_
  split_ifs
  · simp only [pair0, Pi.add_apply, add_mul, ntr_add', mul_add, Finset.sum_add_distrib]
  · simp

lemma pair2_smul_left (c : ℂ) (F G : Form2 N n) : pair2 a (c • F) G = c * pair2 a F G := by
  simp only [pair2, Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => ?_
  split_ifs
  · simp only [pair0, Pi.smul_apply, smul_mul_assoc, ntr_smul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by ring
  · simp

lemma pair2_comm (F G : Form2 N n) : pair2 a F G = pair2 a G F := by
  simp only [pair2, pair0]
  refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => ?_
  split_ifs
  · exact Finset.sum_congr rfl fun x _ => by rw [ntr_mul_comm]
  · rfl

lemma pair2_add_right (F G G' : Form2 N n) : pair2 a F (G + G') = pair2 a F G + pair2 a F G' := by
  rw [pair2_comm, pair2_add_left, pair2_comm a G, pair2_comm a G']

lemma pair2_smul_right (c : ℂ) (F G : Form2 N n) : pair2 a F (c • G) = c * pair2 a F G := by
  rw [pair2_comm, pair2_smul_left, pair2_comm]

lemma D1_add_smul (U : Config N n) (A δ : Form1 N n) (t : ℂ) :
    D1 a U (A + t • δ) = D1 a U A + t • D1 a U δ := by
  funext μ ν x
  rw [D1_add, D1_smul]; rfl

lemma hessBil_add_smul_left (A δ B : Form1 N n) (U : Config N n) (t : ℂ) :
    hessBil a (A + t • δ) B U = hessBil a A B U + t * hessBil a δ B U := by
  rw [hessBil_comm, ← hessBilL_apply, map_add, map_smul, hessBilL_apply, hessBilL_apply,
    hessBil_comm a B A, hessBil_comm a B δ, smul_eq_mul]

lemma hessBil_add_smul_right (A δ B : Form1 N n) (U : Config N n) (t : ℂ) :
    hessBil a B (A + t • δ) U = hessBil a B A U + t * hessBil a B δ U := by
  rw [← hessBilL_apply, map_add, map_smul, hessBilL_apply, hessBilL_apply, smul_eq_mul]

/-- `⟨B, Δ(𝐔)X⟩ = ⟨D_𝐔B, D_𝐔X⟩ + β(X, B)` for `B` with values in `𝔤^c`. -/
lemma pair1_hessOp_eq [NeZero N] (hG : G.LieInput) (ha : a ≠ 0) (U : Config N n) (X : Form1 N n)
    {B : Form1 N n} (hB : ∀ μ x, B μ x ∈ G.lieC) :
    pair1 a B (hessOp a hG U X) = pair2 a (D1 a U B) (D1 a U X) + hessBil a X B U := by
  rw [hessOp, pair1_add_right, pair1_hessOp' a hG ha U X hB,
    ← pair2_D1 a U B (D1 a U X) (fun μ ν _ => D1_antisymm a U X μ ν)]

/-- `𝖵₀(A) = A(e^{iaA}𝐔) - A(𝐔) - ⟨A, J(𝐔)⟩ - ½⟨A, Δ(𝐔)A⟩` (`def:potential`(i)). -/
noncomputable def V0 [NeZero N] (hG : G.LieInput) (U : Config N n) (A : Form1 N n) : ℂ :=
  action (expMul a A U) - action U - pair1 a A (current a hG U) -
    1 / 2 * pair1 a A (hessOp a hG U A)

/-- `𝖭₀(A) = 𝒥(A) - J(𝐔) - Δ(𝐔)A`. -/
noncomputable def N0 [NeZero N] (hG : G.LieInput) (U : Config N n) (A : Form1 N n) : Form1 N n :=
  gradAction a hG U A - current a hG U - hessOp a hG U A

/-- `def:potential`(iii) for `𝖵₀`: `𝖭₀(A)` is the gradient of `𝖵₀` at `A`,
`d/dt 𝖵₀(A + tδ)|_{t=0} = ⟨δ, 𝖭₀(A)⟩` for all `δ` with values in `𝔤^c`. -/
theorem hasDerivAt_V0 [NeZero N] (hG : G.LieInput) (ha : a ≠ 0) {U : Config N n}
    (hU : ∀ μ x, U μ x ∈ G.complexified) {A : Form1 N n} (hA : ∀ μ x, A μ x ∈ G.lieC)
    {δ : Form1 N n} (hδ : ∀ μ x, δ μ x ∈ G.lieC) :
    HasDerivAt (fun t : ℂ => V0 a hG U (A + t • δ)) (pair1 a δ (N0 a hG U A)) 0 := by
  -- the action
  have h1 := hasDerivAt_action_add a hG ha hU hA hδ
  -- the linear term
  have h2 : HasDerivAt (fun t : ℂ => pair1 a (A + t • δ) (current a hG U))
      (pair1 a δ (current a hG U)) 0 := by
    have e : (fun t : ℂ => pair1 a (A + t • δ) (current a hG U)) =
        fun t => pair1 a A (current a hG U) + t * pair1 a δ (current a hG U) := by
      funext t; rw [pair1_add_left, pair1_smul_left]
    rw [e]
    simpa using ((hasDerivAt_id (0 : ℂ)).mul_const (pair1 a δ (current a hG U))).const_add
      (pair1 a A (current a hG U))
  -- the quadratic term, `Q(X, Y) = ⟨D_𝐔X, D_𝐔Y⟩ + β(X, Y)`
  set Q : Form1 N n → Form1 N n → ℂ := fun X Y => pair2 a (D1 a U X) (D1 a U Y) + hessBil a X Y U
  have hAδ : ∀ t : ℂ, ∀ μ x, (A + t • δ) μ x ∈ G.lieC := fun t μ x =>
    (GaugeGroup.lieCSubmodule hG).add_mem (hA μ x) ((GaugeGroup.lieCSubmodule hG).smul_mem t (hδ μ x))
  have hQ : ∀ t : ℂ, pair1 a (A + t • δ) (hessOp a hG U (A + t • δ)) =
      Q A A + t * (Q A δ + Q δ A) + t ^ 2 * Q δ δ := by
    intro t
    rw [pair1_hessOp_eq a hG ha U _ (hAδ t)]
    simp only [Q, D1_add_smul, pair2_add_left, pair2_smul_left, pair2_add_right, pair2_smul_right,
      hessBil_add_smul_left, hessBil_add_smul_right]
    rw [pair2_comm a (D1 a U A) (D1 a U δ)]
    ring
  have h3 : HasDerivAt (fun t : ℂ => 1 / 2 * pair1 a (A + t • δ) (hessOp a hG U (A + t • δ)))
      (pair1 a δ (hessOp a hG U A)) 0 := by
    have e : (fun t : ℂ => 1 / 2 * pair1 a (A + t • δ) (hessOp a hG U (A + t • δ))) =
        fun t => 1 / 2 * (Q A A + t * (Q A δ + Q δ A) + t ^ 2 * Q δ δ) := by
      funext t; rw [hQ]
    rw [e]
    have hp : HasDerivAt (fun t : ℂ => Q A A + t * (Q A δ + Q δ A) + t ^ 2 * Q δ δ)
        (Q A δ + Q δ A) 0 := by
      have := (((hasDerivAt_id (0 : ℂ)).mul_const (Q A δ + Q δ A)).const_add (Q A A)).add
        ((hasDerivAt_pow 2 (0 : ℂ)).mul_const (Q δ δ))
      exact this.congr_deriv (by simp)
    refine (hp.const_mul (1 / 2 : ℂ)).congr_deriv ?_
    rw [pair1_hessOp_eq a hG ha U A hδ]
    simp only [Q]
    rw [pair2_comm a (D1 a U A) (D1 a U δ), hessBil_comm a δ A]
    ring
  have h := ((h1.sub_const (action U)).sub h2).sub h3
  refine (h.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => rfl)
  simp only [N0, pair1_sub_right]

/-! ### Linearity of `Δ(𝐔)` -/

/-- `Δ'(𝐔)` is linear: `Δ'(A + tδ) = Δ'A + tΔ'δ` (from its defining property and the nondegeneracy of
`(Z, Y) ↦ tr ZY` on `𝔤^c`). -/
lemma hessOp'_add_smul [NeZero N] (hG : G.LieInput) (ha : a ≠ 0) (U : Config N n) (A δ : Form1 N n)
    (t : ℂ) : hessOp' a hG U (A + t • δ) = hessOp' a hG U A + t • hessOp' a hG U δ := by
  funext μ x
  set D := hessOp' a hG U (A + t • δ) μ x - (hessOp' a hG U A μ x + t • hessOp' a hG U δ μ x)
  have hD : D ∈ GaugeGroup.lieCSubmodule hG := by
    rw [GaugeGroup.mem_lieCSubmodule]
    exact (GaugeGroup.lieCSubmodule hG).sub_mem (hessOp'_mem a hG U _ μ x)
      ((GaugeGroup.lieCSubmodule hG).add_mem (hessOp'_mem a hG U _ μ x)
        ((GaugeGroup.lieCSubmodule hG).smul_mem t (hessOp'_mem a hG U _ μ x)))
  have hpair : ∀ Z ∈ G.lieC, ntr (Z * D) = 0 := by
    intro Z hZ
    have h1 := hessOp'_spec a hG ha U (A + t • δ) μ x hZ
    have h2 := hessOp'_spec a hG ha U A μ x hZ
    have h3 := hessOp'_spec a hG ha U δ μ x hZ
    rw [hessBil_add_smul_left] at h1
    have h4 : a ^ 4 * ntr (Z * D) = 0 := by
      simp only [D, mul_sub, mul_add, Matrix.mul_smul, ntr_sub, ntr_add', ntr_smul]
      linear_combination h1 - h2 - t * h3
    exact (mul_eq_zero.mp h4).resolve_left (pow_ne_zero 4 ha)
  have hzero : trPairing hG ⟨D, hD⟩ = trPairing hG 0 := by
    ext ⟨Z, hZ⟩
    simp only [trPairing, LinearMap.coe_mk, AddHom.coe_mk, map_zero, LinearMap.zero_apply]
    exact hpair Z ((GaugeGroup.mem_lieCSubmodule hG).mp hZ)
  have := congrArg Subtype.val (trPairing_injective hG hzero)
  simp only [ZeroMemClass.coe_zero] at this
  simp only [Pi.add_apply, Pi.smul_apply]
  exact sub_eq_zero.mp this

lemma Ds2_add_smul (U : Config N n) (F G : Form2 N n) (t : ℂ) :
    Ds2 a U (F + t • G) = Ds2 a U F + t • Ds2 a U G := by
  funext μ x
  simp only [Ds2, Dbw, Pi.add_apply, Pi.smul_apply, Ad_add, Ad_smul, Finset.smul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ν _ => ?_
  split_ifs
  · simp only [smul_sub, smul_add, smul_comm t a⁻¹]; abel
  · simp

/-- `Δ(𝐔)` is linear. -/
lemma hessOp_add_smul [NeZero N] (hG : G.LieInput) (ha : a ≠ 0) (U : Config N n) (A δ : Form1 N n)
    (t : ℂ) : hessOp a hG U (A + t • δ) = hessOp a hG U A + t • hessOp a hG U δ := by
  simp only [hessOp, D1_add_smul, Ds2_add_smul, hessOp'_add_smul a hG ha, smul_add]
  abel

/-- `Δ(𝐔)` as a linear map of the `1`-forms. -/
noncomputable def hessLin [NeZero N] (hG : G.LieInput) (ha : a ≠ 0) (U : Config N n) :
    Form1 N n →ₗ[ℂ] Form1 N n where
  toFun := hessOp a hG U
  map_add' A δ := by simpa using hessOp_add_smul a hG ha U A δ 1
  map_smul' t δ := by
    have h0 : hessOp a hG U 0 = 0 := by
      have := hessOp_add_smul a hG ha U 0 0 1
      simp only [add_zero, one_smul] at this
      exact left_eq_add.mp this
    simpa [h0] using hessOp_add_smul a hG ha U 0 δ t

/-! ### Analyticity of `𝖵₀` -/

lemma analyticAt_exp_comp {f : Form1 N n → Mat} {A₀ : Form1 N n} (hf : AnalyticAt ℂ f A₀) :
    AnalyticAt ℂ (fun A => NormedSpace.exp (f A)) A₀ :=
  (NormedSpace.exp_analytic (𝕂 := ℂ) (f A₀)).comp hf

lemma analyticAt_coord (μ : Fin 4) (x : Site n) (A₀ : Form1 N n) :
    AnalyticAt ℂ (fun A : Form1 N n => A μ x) A₀ :=
  ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Site n => Mat) x).comp
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 4 => Site n → Mat) μ)).analyticAt A₀

lemma analyticAt_Ad_coord (W : GLN) (c : ℂ) (μ : Fin 4) (x : Site n) (A₀ : Form1 N n) :
    AnalyticAt ℂ (fun A : Form1 N n => c • Ad W (A μ x)) A₀ := by
  simp only [Ad]
  exact ((analyticAt_const.mul (analyticAt_coord μ x A₀)).mul analyticAt_const).const_smul (c := c)

/-- `A ↦ A(e^{iaA}𝐔)` is entire. -/
theorem analyticAt_action_expMul (U : Config N n) (A₀ : Form1 N n) :
    AnalyticAt ℂ (fun A : Form1 N n => action (expMul a A U)) A₀ := by
  unfold action
  refine Finset.analyticAt_fun_sum _ fun x _ => Finset.analyticAt_fun_sum _ fun μ _ =>
    Finset.analyticAt_fun_sum _ fun ν _ => ?_
  split_ifs with h
  · simp only [actionTerm, reW, ntr_smul, ntr_add']
    have hP : ∀ A : Form1 N n, ((plaq (expMul a A U) μ ν x : GLN) : Mat) =
        NormedSpace.exp ((I * a) • A μ x) * NormedSpace.exp ((I * a) • Ad (U μ x) (A ν (x + unit n μ))) *
          (plaq U μ ν x : Mat) * NormedSpace.exp ((I * a) • Ad (U ν x) (-A μ (x + unit n ν))) *
          NormedSpace.exp ((I * a) • -A ν x) := fun A => by
      have := (plaq_expMul_smul a A U μ ν x 1).1
      simpa only [one_smul] using this
    have hPi : ∀ A : Form1 N n, (((plaq (expMul a A U) μ ν x)⁻¹ : GLN) : Mat) =
        NormedSpace.exp (-((I * a) • -A ν x)) *
          NormedSpace.exp (-((I * a) • Ad (U ν x) (-A μ (x + unit n ν)))) *
          ((plaq U μ ν x)⁻¹ : GLN) * NormedSpace.exp (-((I * a) • Ad (U μ x) (A ν (x + unit n μ)))) *
          NormedSpace.exp (-((I * a) • A μ x)) := fun A => by
      have := (plaq_expMul_smul a A U μ ν x 1).2
      simpa only [one_smul] using this
    simp only [hP, hPi]
    have hc1 := analyticAt_exp_comp ((analyticAt_coord μ x A₀).const_smul (c := I * a))
    have hc2 := analyticAt_exp_comp (analyticAt_Ad_coord (U μ x) (I * a) ν (x + unit n μ) A₀)
    have hc3 : AnalyticAt ℂ (fun A : Form1 N n =>
        NormedSpace.exp ((I * a) • Ad (U ν x) (-A μ (x + unit n ν)))) A₀ := by
      simp only [Ad_neg, smul_neg]
      exact analyticAt_exp_comp (analyticAt_Ad_coord (U ν x) (I * a) μ (x + unit n ν) A₀).neg
    have hc4 : AnalyticAt ℂ (fun A : Form1 N n => NormedSpace.exp ((I * a) • -A ν x)) A₀ :=
      analyticAt_exp_comp ((analyticAt_coord ν x A₀).neg.const_smul (c := I * a))
    have hd1 : AnalyticAt ℂ (fun A : Form1 N n => NormedSpace.exp (-((I * a) • -A ν x))) A₀ :=
      analyticAt_exp_comp ((analyticAt_coord ν x A₀).neg.const_smul (c := I * a)).neg
    have hd2 : AnalyticAt ℂ (fun A : Form1 N n =>
        NormedSpace.exp (-((I * a) • Ad (U ν x) (-A μ (x + unit n ν))))) A₀ := by
      simp only [Ad_neg, smul_neg, neg_neg]
      exact analyticAt_exp_comp (analyticAt_Ad_coord (U ν x) (I * a) μ (x + unit n ν) A₀)
    have hd3 := analyticAt_exp_comp (analyticAt_Ad_coord (U μ x) (I * a) ν (x + unit n μ) A₀).neg
    have hd4 := analyticAt_exp_comp ((analyticAt_coord μ x A₀).const_smul (c := I * a)).neg
    have hntr : ∀ {f : Form1 N n → Mat}, AnalyticAt ℂ f A₀ → AnalyticAt ℂ (fun A => ntr (f A)) A₀ :=
      fun hf => (ntrL.analyticAt _).comp hf
    exact analyticAt_const.sub (analyticAt_const.mul
      ((hntr ((((hc1.mul hc2).mul analyticAt_const).mul hc3).mul hc4)).add
        (hntr ((((hd1.mul hd2).mul analyticAt_const).mul hd3).mul hd4))))
  · exact analyticAt_const

end CoreLean
