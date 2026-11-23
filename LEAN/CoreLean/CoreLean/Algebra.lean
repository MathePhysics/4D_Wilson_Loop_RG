/-
The Lie algebra, its complexification, and the complexified group of BALABAN_CORE.tex
(`def:group`(i)), `lem:lie-algebra`, and the parts of `lem:norms`(iii) which do not involve the
projection `π`.

The group `G` is given as a subgroup of `GL(N, ℂ)` of unitary matrices; the core's `G` is moreover
a compact connected Lie subgroup of `U(N)`, which is not used here. The first sentence of
`lem:lie-algebra` (`𝔤` is a real linear subspace with `i[A, B] ∈ 𝔤`) is stated in the core without
a proof; it is the named input `GaugeGroup.LieInput`, and the rest of the lemma is derived from it.
-/
import CoreLean.Hadamard

open Matrix Complex

namespace CoreLean

variable {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "GLN" => (Matrix (Fin N) (Fin N) ℂ)ˣ

@[simp] lemma expU_zero : expU (0 : Mat) = 1 := by
  ext1; simp

/-- The gauge group: a subgroup of `GL(N, ℂ)` whose elements are unitary. -/
structure GaugeGroup (N : ℕ) where
  carrier : Subgroup (Matrix (Fin N) (Fin N) ℂ)ˣ
  unitary : ∀ U ∈ carrier,
    ((U : (Matrix (Fin N) (Fin N) ℂ)ˣ) : Matrix (Fin N) (Fin N) ℂ) ∈ unitaryGroup (Fin N) ℂ

namespace GaugeGroup

variable (G : GaugeGroup N)

/-- `𝔤 = {A ∈ M_N(ℂ) | A^* = A, ∀ t ∈ ℝ : e^{itA} ∈ G}` (`def:group`(i)). -/
def lie : Set Mat := {A | Aᴴ = A ∧ ∀ t : ℝ, expU ((I * t) • A) ∈ G.carrier}

/-- The first sentence of `lem:lie-algebra`: `𝔤` is closed under addition and under
`(A, B) ↦ i[A, B]`. Stated in the core without a proof; a named input here. -/
structure LieInput : Prop where
  add_mem : ∀ A ∈ G.lie, ∀ B ∈ G.lie, A + B ∈ G.lie
  bracket_mem : ∀ A ∈ G.lie, ∀ B ∈ G.lie, I • (A * B - B * A) ∈ G.lie

lemma zero_mem_lie : (0 : Mat) ∈ G.lie :=
  ⟨by simp, fun t => by simp [G.carrier.one_mem]⟩

lemma smul_mem_lie {A : Mat} (hA : A ∈ G.lie) (r : ℝ) : (r : ℂ) • A ∈ G.lie := by
  refine ⟨?_, fun t => ?_⟩
  · rw [Matrix.conjTranspose_smul, hA.1]; simp
  · rw [smul_smul, show I * (t : ℂ) * (r : ℂ) = I * ((t * r : ℝ) : ℂ) by push_cast; ring]
    exact hA.2 (t * r)

lemma neg_mem_lie {A : Mat} (hA : A ∈ G.lie) : -A ∈ G.lie := by
  simpa using G.smul_mem_lie hA (-1)

/-- `𝔤^c = 𝔤 ⊕ i𝔤` (`def:group`(i)). -/
def lieC : Set Mat := {X | ∃ A ∈ G.lie, ∃ B ∈ G.lie, X = A + I • B}

variable {G}

lemma lie_subset_lieC {A : Mat} (hA : A ∈ G.lie) : A ∈ G.lieC :=
  ⟨A, hA, 0, G.zero_mem_lie, by simp⟩

/-- `lem:lie-algebra`: `𝔤^c` is a complex linear subspace. -/
def lieCSubmodule (hG : G.LieInput) : Submodule ℂ Mat where
  carrier := G.lieC
  zero_mem' := ⟨0, G.zero_mem_lie, 0, G.zero_mem_lie, by simp⟩
  add_mem' := by
    rintro _ _ ⟨A, hA, B, hB, rfl⟩ ⟨A', hA', B', hB', rfl⟩
    exact ⟨A + A', hG.add_mem _ hA _ hA', B + B', hG.add_mem _ hB _ hB', by
      rw [smul_add]; abel⟩
  smul_mem' := by
    rintro c _ ⟨A, hA, B, hB, rfl⟩
    refine ⟨(c.re : ℂ) • A + ((-c.im : ℝ) : ℂ) • B,
      hG.add_mem _ (G.smul_mem_lie hA _) _ (G.smul_mem_lie hB _),
      (c.im : ℂ) • A + (c.re : ℂ) • B,
      hG.add_mem _ (G.smul_mem_lie hA _) _ (G.smul_mem_lie hB _), ?_⟩
    ext i j
    simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

lemma mem_lieCSubmodule (hG : G.LieInput) {X : Mat} : X ∈ lieCSubmodule hG ↔ X ∈ G.lieC :=
  Iff.rfl

/-- The commutator of two elements of `𝔤` lies in `𝔤^c`. -/
lemma commutator_lie_mem (hG : G.LieInput) {A B : Mat} (hA : A ∈ G.lie) (hB : B ∈ G.lie) :
    A * B - B * A ∈ G.lieC := by
  refine ⟨0, G.zero_mem_lie, -(I • (A * B - B * A)), G.neg_mem_lie (hG.bracket_mem _ hA _ hB),
    ?_⟩
  rw [smul_neg, smul_smul, Complex.I_mul_I]
  simp

/-- `lem:lie-algebra`: `𝔤^c` is closed under the commutator. -/
theorem commutator_mem_lieC (hG : G.LieInput) {X Y : Mat} (hX : X ∈ G.lieC)
    (hY : Y ∈ G.lieC) : X * Y - Y * X ∈ G.lieC := by
  obtain ⟨A, hA, B, hB, rfl⟩ := hX
  obtain ⟨C, hC, D, hD, rfl⟩ := hY
  have e : (A + I • B) * (C + I • D) - (C + I • D) * (A + I • B) =
      (A * C - C * A) + I • (A * D - D * A) + I • (B * C - C * B) +
        (-1 : ℂ) • (B * D - D * B) := by
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_add,
      smul_smul, Complex.I_mul_I]
    module
  rw [e]
  exact (lieCSubmodule hG).add_mem ((lieCSubmodule hG).add_mem ((lieCSubmodule hG).add_mem
    (commutator_lie_mem hG hA hC) ((lieCSubmodule hG).smul_mem _ (commutator_lie_mem hG hA hD)))
    ((lieCSubmodule hG).smul_mem _ (commutator_lie_mem hG hB hC)))
    ((lieCSubmodule hG).smul_mem _ (commutator_lie_mem hG hB hD))

/-- `lem:lie-algebra`: `𝔤^c` is closed under `X ↦ X^*`. -/
theorem conjTranspose_mem_lieC {X : Mat} (hX : X ∈ G.lieC) : Xᴴ ∈ G.lieC := by
  obtain ⟨A, hA, B, hB, rfl⟩ := hX
  refine ⟨A, hA, -B, G.neg_mem_lie hB, ?_⟩
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, hA.1, hB.1]
  simp

/-- `lem:lie-algebra`: `𝔤 ∩ i𝔤 = {0}`. -/
theorem lie_inter_I_lie {A B : Mat} (hA : A ∈ G.lie) (hB : B ∈ G.lie) (h : A = I • B) :
    A = 0 := by
  have h1 : Aᴴ = -A := by
    rw [h, Matrix.conjTranspose_smul, hB.1]; simp
  rw [hA.1] at h1
  have : (2 : ℂ) • A = 0 := by rw [two_smul]; nth_rewrite 1 [h1]; simp
  exact (smul_eq_zero.mp this).resolve_left two_ne_zero

variable (G)

/-- The complexified group `G^c`, generated by `e^{iA}`, `A ∈ 𝔤^c` (`def:group`(i)). -/
def complexified : Subgroup GLN :=
  Subgroup.closure {U | ∃ A ∈ G.lieC, U = expU (I • A)}

variable {G}

/-- `Ad_{e^{iA}}` maps `𝔤^c` into itself, for `A ∈ 𝔤^c`. -/
lemma Ad_expU_mem (hG : G.LieInput) {A X : Mat} (hA : A ∈ G.lieC) (hX : X ∈ G.lieC) :
    Ad (expU (I • A)) X ∈ G.lieC := by
  have h := exp_conj_mem (lieCSubmodule hG) (I • A) (fun Y hY => by
      rw [Matrix.smul_mul, Matrix.mul_smul, ← smul_sub]
      exact (lieCSubmodule hG).smul_mem _ (commutator_mem_lieC hG hA hY)) hX
  rw [show Ad (expU (I • A)) X = NormedSpace.exp (I • A) * X * NormedSpace.exp (-(I • A)) by
    simp [Ad, expU_inv]]
  exact h

/-- `lem:norms`(iii): for `U ∈ G^c`, `Ad_U` maps `𝔤^c` into itself. -/
theorem Ad_mem_lieC (hG : G.LieInput) {U : GLN} (hU : U ∈ G.complexified) {X : Mat}
    (hX : X ∈ G.lieC) : Ad U X ∈ G.lieC := by
  induction hU using Subgroup.closure_induction'' generalizing X with
  | mem U hU =>
    obtain ⟨A, hA, rfl⟩ := hU
    exact Ad_expU_mem hG hA hX
  | inv_mem U hU =>
    obtain ⟨A, hA, rfl⟩ := hU
    rw [expU_inv, show -(I • A) = I • (-A) by rw [smul_neg]]
    exact Ad_expU_mem hG ((lieCSubmodule hG).neg_mem hA) hX
  | one => simpa using hX
  | mul U V _ _ hU hV => rw [Ad_mul]; exact hU (hV hX)

/-- `lem:norms`(iii): for `U ∈ G^c`, `Ad_U` maps `𝔤^c` onto itself. -/
theorem Ad_surj_lieC (hG : G.LieInput) {U : GLN} (hU : U ∈ G.complexified) {X : Mat}
    (hX : X ∈ G.lieC) : ∃ Y ∈ G.lieC, Ad U Y = X :=
  ⟨Ad U⁻¹ X, Ad_mem_lieC hG (G.complexified.inv_mem hU) hX, by rw [← Ad_mul, mul_inv_cancel,
    Ad_one]⟩

/-- `lem:norms`(iii): for `U ∈ G`, `Ad_U` maps `𝔤` into itself. -/
theorem Ad_mem_lie {U : GLN} (hU : U ∈ G.carrier) {A : Mat} (hA : A ∈ G.lie) :
    Ad U A ∈ G.lie := by
  have hUu := G.unitary U hU
  have hinv : ((U⁻¹ : GLN) : Mat) = (U : Mat)ᴴ := by
    have h1 : (U : Mat) * star (U : Mat) = 1 := hUu.2
    calc ((U⁻¹ : GLN) : Mat) = ((U⁻¹ : GLN) : Mat) * ((U : Mat) * star (U : Mat)) := by
          rw [h1, Matrix.mul_one]
      _ = (U : Mat)ᴴ := by rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]; rfl
  refine ⟨?_, fun t => ?_⟩
  · simp only [Ad, hinv, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hA.1,
      Matrix.mul_assoc]
  · rw [← Ad_smul, ← expU_conj]
    exact G.carrier.mul_mem (G.carrier.mul_mem hU (hA.2 t)) (G.carrier.inv_mem hU)

/-- `lem:norms`(iii): for `U ∈ G`, `Ad_U` maps `𝔤` onto itself. -/
theorem Ad_surj_lie {U : GLN} (hU : U ∈ G.carrier) {A : Mat} (hA : A ∈ G.lie) :
    ∃ B ∈ G.lie, Ad U B = A :=
  ⟨Ad U⁻¹ A, Ad_mem_lie (G.carrier.inv_mem hU) hA, by rw [← Ad_mul, mul_inv_cancel, Ad_one]⟩

/-- `lem:norms`(iii): for `U ∈ G`, `Ad_U` preserves the Hilbert–Schmidt norm. -/
theorem hs_Ad {U : GLN} (hU : U ∈ G.carrier) (X : Mat) : hs (Ad U X) = hs X :=
  hs_unitary_mul _ _ _ (G.unitary U hU) (G.unitary _ (G.carrier.inv_mem hU))

open scoped Matrix.Norms.L2Operator in
/-- `lem:norms`(iii): for `U ∈ G`, `Ad_U` preserves the operator norm. -/
theorem opNorm_Ad {U : GLN} (hU : U ∈ G.carrier) (X : Mat) : ‖Ad U X‖ = ‖X‖ :=
  opNorm_unitary_mul _ _ _ (G.unitary U hU) (G.unitary _ (G.carrier.inv_mem hU))

end GaugeGroup

end CoreLean
