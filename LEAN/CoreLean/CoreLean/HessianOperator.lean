/-
`def:hessian` of BALABAN_CORE.tex: the operator `Δ(U) = D^*_U D_U + Δ'(U)` on `1`-forms with values in
`𝔤^c`.

`β(A, B)` is the symmetric bilinear form whose quadratic form is the right side of `eq:hessian-form`
(`hessForm`). Since the bilinear pairing `(Z, Y) ↦ tr ZY` is nondegenerate on `𝔤^c` (for `Y ∈ 𝔤^c`,
`Y^* ∈ 𝔤^c` and `tr Y^*Y = |Y|²`), there is for every bond `b` exactly one `(Δ'A)(b) ∈ 𝔤^c` with
`a⁴ tr(Z (Δ'A)(b)) = β(A, δ_b Z)` for all `Z ∈ 𝔤^c`; then `⟨B, Δ'A⟩ = β(A, B)` for all `𝔤^c`-valued
`B`, and with `action_expansion` the operator `Δ = D^*D + Δ'` satisfies `eq:action-expansion`.
-/
import CoreLean.HessianExpansion

open NormedSpace Complex
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace CoreLean

variable {N n : ℕ} [NeZero n] (a : ℂ)

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "GLN" => (Matrix (Fin N) (Fin N) ℂ)ˣ

variable {G : GaugeGroup N}

/-! ### Linearity of the differences and of the exponents -/

lemma D1_add (U : Config N n) (A A' : Form1 N n) (μ ν : Fin 4) (x : Site n) :
    D1 a U (A + A') μ ν x = D1 a U A μ ν x + D1 a U A' μ ν x := by
  simp only [D1, Dfw, Pi.add_apply, Ad_add, smul_sub, smul_add]; abel

lemma D1_smul (U : Config N n) (c : ℂ) (A : Form1 N n) (μ ν : Fin 4) (x : Site n) :
    D1 a U (c • A) μ ν x = c • D1 a U A μ ν x := by
  simp only [D1, Dfw, Pi.smul_apply, Ad_smul, smul_sub, smul_comm a⁻¹ c]

lemma pexp_add (U : Config N n) (A A' : Form1 N n) (μ ν : Fin 4) (x : Site n) (k : Fin 4) :
    pexp (A + A') U μ ν x k = pexp A U μ ν x k + pexp A' U μ ν x k := by
  fin_cases k <;> simp [pexp, Ad_add, Ad_neg, neg_add] <;> abel

lemma pexp_smul (U : Config N n) (c : ℂ) (A : Form1 N n) (μ ν : Fin 4) (x : Site n) (k : Fin 4) :
    pexp (c • A) U μ ν x k = c • pexp A U μ ν x k := by
  fin_cases k <;> simp [pexp, Ad_smul, Ad_neg, smul_neg]

/-! ### The bilinear form -/

/-- The commutator `[X, Y]`. -/
def brk (X Y : Mat) : Mat := X * Y - Y * X

/-- The six ordered pairs `(k, l)` with `A_k` before `A_l` in the order `A₃, A₄, A₁, A₂`. -/
def plaqPairs : List (Fin 4 × Fin 4) := [(2, 3), (2, 0), (2, 1), (3, 0), (3, 1), (0, 1)]

lemma commP_eq_sum (B : Fin 4 → Mat) :
    commP B = (plaqPairs.map fun p => brk (B p.1) (B p.2)).sum := by
  simp only [commP, plaqPairs, brk, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    add_zero]
  abel

/-- The symmetrised commutator form: `commPBil B B = commP B`. -/
def commPBil (B B' : Fin 4 → Mat) : Mat :=
  (2 : ℂ)⁻¹ • (plaqPairs.map fun p => brk (B p.1) (B' p.2) + brk (B' p.1) (B p.2)).sum

lemma list_sum_map_smul {ι : Type*} (l : List ι) (f : ι → Mat) (c : ℂ) :
    (l.map fun p => c • f p).sum = c • (l.map f).sum := by
  induction l with
  | nil => simp
  | cons p l ih => simp [ih, smul_add]

lemma commPBil_self (B : Fin 4 → Mat) : commPBil B B = commP B := by
  rw [commPBil, commP_eq_sum]
  have h : (plaqPairs.map fun p => brk (B p.1) (B p.2) + brk (B p.1) (B p.2)) =
      plaqPairs.map fun p => (2 : ℂ) • brk (B p.1) (B p.2) := by
    simp only [two_smul]
  rw [h, list_sum_map_smul, smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]

lemma brk_add_right (X Y Y' : Mat) : brk X (Y + Y') = brk X Y + brk X Y' := by
  simp only [brk, mul_add, add_mul]; abel

lemma brk_add_left (X X' Y : Mat) : brk (X + X') Y = brk X Y + brk X' Y := by
  simp only [brk, mul_add, add_mul]; abel

lemma brk_smul_right (c : ℂ) (X Y : Mat) : brk X (c • Y) = c • brk X Y := by
  simp only [brk, Matrix.mul_smul, Matrix.smul_mul, smul_sub]

lemma brk_smul_left (c : ℂ) (X Y : Mat) : brk (c • X) Y = c • brk X Y := by
  simp only [brk, Matrix.mul_smul, Matrix.smul_mul, smul_sub]

lemma commPBil_add_right (B B' B'' : Fin 4 → Mat) :
    commPBil B (B' + B'') = commPBil B B' + commPBil B B'' := by
  simp only [commPBil, Pi.add_apply, brk_add_right, brk_add_left, ← smul_add]
  congr 1
  rw [← List.sum_map_add]
  congr 1
  refine List.map_congr_left fun p _ => ?_
  abel

lemma commPBil_smul_right (c : ℂ) (B B' : Fin 4 → Mat) :
    commPBil B (c • B') = c • commPBil B B' := by
  simp only [commPBil, Pi.smul_apply, brk_smul_right, brk_smul_left, ← smul_add]
  rw [list_sum_map_smul, smul_comm c]

lemma commPBil_comm (B B' : Fin 4 → Mat) : commPBil B B' = commPBil B' B := by
  simp only [commPBil]
  congr 2
  refine List.map_congr_left fun p _ => ?_
  rw [add_comm]

/-- The summand of `β(A, B)` for the plaquette `p_{μν}(x)`. -/
def hessTermBil (A B : Form1 N n) (U : Config N n) (μ ν : Fin 4) (x : Site n) : ℂ :=
  a ^ 4 * ntr ((2 : ℂ)⁻¹ • (D1 a U A μ ν x * D1 a U B μ ν x + D1 a U B μ ν x * D1 a U A μ ν x) *
      (reW (plaq U μ ν x) - 1)) +
    I * a ^ 2 * ntr (commPBil (pexp A U μ ν x) (pexp B U μ ν x) * imW (plaq U μ ν x))

/-- `β(A, B)`, the symmetric bilinear form of `eq:hessian-form`. -/
def hessBil (A B : Form1 N n) (U : Config N n) : ℂ :=
  ∑ x : Site n, ∑ μ : Fin 4, ∑ ν : Fin 4, if μ < ν then hessTermBil a A B U μ ν x else 0

lemma hessBil_self (A : Form1 N n) (U : Config N n) : hessBil a A A U = hessForm a A U := by
  unfold hessBil hessForm hessTermBil hessTerm
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun μ _ =>
    Finset.sum_congr rfl fun ν _ => ?_
  rw [commPBil_self, ← two_smul ℂ (D1 a U A μ ν x * D1 a U A μ ν x), smul_smul,
    inv_mul_cancel₀ two_ne_zero, one_smul, ← sq]

lemma hessBil_comm (A B : Form1 N n) (U : Config N n) : hessBil a A B U = hessBil a B A U := by
  unfold hessBil hessTermBil
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun μ _ =>
    Finset.sum_congr rfl fun ν _ => ?_
  rw [commPBil_comm, add_comm (D1 a U A μ ν x * D1 a U B μ ν x)]

lemma hessTermBil_add (A B B' : Form1 N n) (U : Config N n) (μ ν : Fin 4) (x : Site n) :
    hessTermBil a A (B + B') U μ ν x = hessTermBil a A B U μ ν x + hessTermBil a A B' U μ ν x := by
  have hp : pexp (B + B') U μ ν x = pexp B U μ ν x + pexp B' U μ ν x :=
    funext (pexp_add U B B' μ ν x)
  have hD : ∀ X Y Z : Mat, Z * (X + Y) + (X + Y) * Z = (Z * X + X * Z) + (Z * Y + Y * Z) :=
    fun X Y Z => by noncomm_ring
  rw [hessTermBil, hessTermBil, hessTermBil, D1_add, hp, commPBil_add_right, hD, smul_add,
    Matrix.add_mul, ntr_add', Matrix.add_mul, ntr_add']
  ring

lemma hessTermBil_smul (c : ℂ) (A B : Form1 N n) (U : Config N n) (μ ν : Fin 4) (x : Site n) :
    hessTermBil a A (c • B) U μ ν x = c * hessTermBil a A B U μ ν x := by
  have hp : pexp (c • B) U μ ν x = c • pexp B U μ ν x := funext (pexp_smul U c B μ ν x)
  have hD : ∀ X Z : Mat, Z * (c • X) + (c • X) * Z = c • (Z * X + X * Z) :=
    fun X Z => by rw [Matrix.mul_smul, Matrix.smul_mul, smul_add]
  rw [hessTermBil, hessTermBil, D1_smul, hp, commPBil_smul_right, hD, smul_comm (2 : ℂ)⁻¹ c]
  simp only [Matrix.smul_mul, ntr_smul]
  ring

/-- `β(A, ·)` as a linear functional. -/
def hessBilL (A : Form1 N n) (U : Config N n) : Form1 N n →ₗ[ℂ] ℂ where
  toFun B := hessBil a A B U
  map_add' B B' := by
    simp only [hessBil, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun μ _ =>
      Finset.sum_congr rfl fun ν _ => ?_
    split_ifs
    · exact hessTermBil_add a A B B' U μ ν x
    · simp
  map_smul' c B := by
    simp only [hessBil, RingHom.id_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun μ _ =>
      Finset.sum_congr rfl fun ν _ => ?_
    split_ifs
    · exact hessTermBil_smul a c A B U μ ν x
    · simp

lemma hessBilL_apply (A B : Form1 N n) (U : Config N n) : hessBilL a A U B = hessBil a A B U := rfl

/-! ### Nondegeneracy of `(Z, Y) ↦ tr ZY` on `𝔤^c` -/

/-- `|X| = 0` only for `X = 0`. -/
lemma eq_zero_of_hs [NeZero N] {X : Mat} (h : hs X = 0) : X = 0 := by
  have h1 := norm_flat X
  rw [h, mul_zero, norm_eq_zero] at h1
  exact flat.map_eq_zero_iff.1 h1

/-- `Y ↦ (Z ↦ tr ZY)` from `𝔤^c` to its dual. -/
def trPairing (hG : G.LieInput) :
    GaugeGroup.lieCSubmodule hG →ₗ[ℂ] Module.Dual ℂ (GaugeGroup.lieCSubmodule hG) where
  toFun Y :=
    { toFun := fun Z => ntr ((Z : Mat) * (Y : Mat))
      map_add' := fun Z Z' => by simp [add_mul, ntr_add']
      map_smul' := fun c Z => by simp [Matrix.smul_mul, ntr_smul] }
  map_add' Y Y' := by ext Z; simp [mul_add, ntr_add']
  map_smul' c Y := by ext Z; simp [Matrix.mul_smul, ntr_smul]

lemma trPairing_injective [NeZero N] (hG : G.LieInput) : Function.Injective (trPairing hG) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro Y hY
  have hYs : Matrix.conjTranspose (Y : Mat) ∈ GaugeGroup.lieCSubmodule hG :=
    GaugeGroup.conjTranspose_mem_lieC Y.2
  have h := LinearMap.congr_fun hY ⟨_, hYs⟩
  simp only [trPairing, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.zero_apply] at h
  -- `tr Y^*Y = |Y|²`
  have h2 : hs2 (Y : Mat) = 0 := by simp [hs2, h]
  have h3 : hs (Y : Mat) = 0 := by rw [hs, h2, Real.sqrt_zero]
  exact Subtype.ext (eq_zero_of_hs h3)

lemma trPairing_surjective [NeZero N] (hG : G.LieInput) : Function.Surjective (trPairing hG) := by
  haveI : FiniteDimensional ℂ (GaugeGroup.lieCSubmodule hG) :=
    FiniteDimensional.finiteDimensional_submodule _
  have hd : Module.finrank ℂ (GaugeGroup.lieCSubmodule hG) =
      Module.finrank ℂ (Module.Dual ℂ (GaugeGroup.lieCSubmodule hG)) :=
    (Subspace.dual_finrank_eq (K := ℂ) (V := GaugeGroup.lieCSubmodule hG)).symm
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).1 (trPairing_injective hG)

/-- The pairing as a linear equivalence of `𝔤^c` with its dual. -/
def trEquiv [NeZero N] (hG : G.LieInput) :
    GaugeGroup.lieCSubmodule hG ≃ₗ[ℂ] Module.Dual ℂ (GaugeGroup.lieCSubmodule hG) :=
  LinearEquiv.ofBijective (trPairing hG) ⟨trPairing_injective hG, trPairing_surjective hG⟩

lemma trEquiv_symm_spec [NeZero N] (hG : G.LieInput)
    (ℓ : Module.Dual ℂ (GaugeGroup.lieCSubmodule hG)) (Z : GaugeGroup.lieCSubmodule hG) :
    ntr ((Z : Mat) * ((trEquiv hG).symm ℓ : Mat)) = ℓ Z := by
  have h := (trEquiv hG).apply_symm_apply ℓ
  have := LinearMap.congr_fun h Z
  exact this

/-! ### The operator `Δ'(U)` -/

/-- `δ_{μ,x} Z`: the `1`-form with the value `Z` on the bond `(x, x + ae_μ)` and `0` elsewhere. -/
def single1 (μ : Fin 4) (x : Site n) (Z : Mat) : Form1 N n := Pi.single μ (Pi.single x Z)

/-- `Δ'(U)`: `(Δ'A)_μ(x) ∈ 𝔤^c` with `a⁴ tr(Z (Δ'A)_μ(x)) = β(A, δ_{μ,x} Z)` for `Z ∈ 𝔤^c`. -/
def hessOp' [NeZero N] (hG : G.LieInput) (U : Config N n) (A : Form1 N n) : Form1 N n :=
  fun μ x => ((trEquiv hG).symm ((a ^ 4)⁻¹ •
    ((hessBilL a A U).comp ((LinearMap.single ℂ (fun _ : Fin 4 => Site n → Mat) μ).comp
      ((LinearMap.single ℂ (fun _ : Site n => Mat) x).comp
        (GaugeGroup.lieCSubmodule hG).subtype)))) : Mat)

lemma hessOp'_mem [NeZero N] (hG : G.LieInput) (U : Config N n) (A : Form1 N n) (μ : Fin 4)
    (x : Site n) : hessOp' a hG U A μ x ∈ G.lieC := Subtype.mem _

lemma hessOp'_spec [NeZero N] (hG : G.LieInput) (ha : a ≠ 0) (U : Config N n) (A : Form1 N n)
    (μ : Fin 4) (x : Site n) {Z : Mat} (hZ : Z ∈ G.lieC) :
    a ^ 4 * ntr (Z * hessOp' a hG U A μ x) = hessBil a A (single1 μ x Z) U := by
  have h := trEquiv_symm_spec hG ((a ^ 4)⁻¹ •
    ((hessBilL a A U).comp ((LinearMap.single ℂ (fun _ : Fin 4 => Site n → Mat) μ).comp
      ((LinearMap.single ℂ (fun _ : Site n => Mat) x).comp
        (GaugeGroup.lieCSubmodule hG).subtype)))) ⟨Z, hZ⟩
  rw [hessOp']
  change a ^ 4 * ntr (Z * _) = _
  rw [h]
  simp only [LinearMap.smul_apply, LinearMap.comp_apply, Submodule.coe_subtype, smul_eq_mul,
    hessBilL_apply]
  rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero 4 ha), one_mul]
  rfl

/-- A `1`-form is the sum of its values on the bonds. -/
lemma form1_eq_sum (B : Form1 N n) : B = ∑ μ : Fin 4, ∑ x : Site n, single1 μ x (B μ x) := by
  funext ν y
  simp only [single1, Finset.sum_apply]
  rw [Finset.sum_eq_single ν (fun μ _ h => by simp [Pi.single_apply, Ne.symm h])
    (fun h => absurd (Finset.mem_univ ν) h)]
  rw [Finset.sum_eq_single y (fun x _ h => by simp [Pi.single_apply, Ne.symm h])
    (fun h => absurd (Finset.mem_univ y) h)]
  simp

/-- `⟨B, Δ'(U)A⟩ = β(A, B)` for every `1`-form `B` with values in `𝔤^c`. -/
theorem pair1_hessOp' [NeZero N] (hG : G.LieInput) (ha : a ≠ 0) (U : Config N n)
    (A : Form1 N n) {B : Form1 N n} (hB : ∀ μ x, B μ x ∈ G.lieC) :
    pair1 a B (hessOp' a hG U A) = hessBil a A B U := by
  conv_rhs => rw [form1_eq_sum B]
  rw [← hessBilL_apply, map_sum]
  unfold pair1 pair0
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [hessBilL_apply, hessOp'_spec a hG ha U A μ x (hB μ x)]

/-- `Δ(U) = D^*_U D_U + Δ'(U)` (`def:hessian`). -/
def hessOp [NeZero N] (hG : G.LieInput) (U : Config N n) (A : Form1 N n) : Form1 N n :=
  Ds2 a U (D1 a U A) + hessOp' a hG U A

/-- `def:hessian`: `Δ(U)` satisfies `eq:action-expansion` along every ray:
`|A(e^{isaA}U) - A(U) - s⟨A, J(U)⟩ - (s²/2)⟨A, Δ(U)A⟩| ≤ K|s|³` for `|s| ≤ 1`. -/
theorem action_expansion_hessOp [NeZero N] (hG : G.LieInput) (ha : a ≠ 0) {U : Config N n}
    (hU : ∀ μ x, U μ x ∈ G.complexified) {A : Form1 N n} (hA : ∀ μ x, A μ x ∈ G.lieC) :
    ∃ K : ℝ, ∀ s : ℂ, ‖s‖ ≤ 1 →
      ‖action (expMul a (s • A) U) - action U - s * pair1 a A (current a hG U) -
        s ^ 2 / 2 * pair1 a A (hessOp a hG U A)‖ ≤ K * ‖s‖ ^ 3 := by
  obtain ⟨K, hK⟩ := action_expansion a hG ha hU hA
  refine ⟨K, fun s hs => ?_⟩
  have e : pair1 a A (hessOp a hG U A) = pair1 a A (Ds2 a U (D1 a U A)) + hessForm a A U := by
    rw [← hessBil_self, ← pair1_hessOp' a hG ha U A hA, hessOp]
    unfold pair1 pair0
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Pi.add_apply, Pi.add_apply, mul_add, ntr_add', mul_add]
  rw [e]
  exact hK s hs

end CoreLean
