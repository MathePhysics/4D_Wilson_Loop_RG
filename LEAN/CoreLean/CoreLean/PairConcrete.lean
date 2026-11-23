/-
The concrete layer, step C6 (`CONCRETE_LAYER.md`): the operators at a pair of BALABAN_CORE.tex (`615c66b253fe`,
`def:landau-operators`, `def:fluctuation-propagator`, `def:second-operators`), on the operators of a sequence of
`SequenceOperators`, with the inverses on the compressed forms (`CompressedInverse`). (The abstract steps of the proof of
`prop:pair-operators` are in `PairOperators.lean`.)

* `symOp`: the symmetric operator `S` of a bilinear form `β` with respect to a symmetric nondegenerate pairing,
  `⟨SA, B⟩ = ½(β(A, B) + β(B, A))`; it is symmetric and `⟨SA, A⟩ = β(A, A)` (`symOp_spec`, `symOp_diag`,
  `symOp_symm`); this is how the core defines `Δ'_π` and `Δ^{(2)}` from their quadratic forms.
* `Data S N`: a pair `(U, J)` with the parameters of the operators (the group mean `inN`, `log`, the constant `𝖺`, the
  Dirichlet domain `Ω_D`).
* `lamL`: `λ_A = G'RD^*A`, with `Q'λ_A = 0` (`Qp_lam`); `gaugeDefect`: the bilinear map whose diagonal is `X(A)` of
  `eq:gauge-defect` (`gaugeDefect_diag`); `DeltaPi`: `Δ'_π`, with `⟨A, Δ'_πA⟩ = ⟨X(A), J⟩` (`DeltaPi_form`).
* `Gpi`, `Hpi`: `G_π = (Δ_𝖺 - Δ'_π)^{-1}`, `H = G_πQ^*(QG_πQ^*)^{-1}`.
* `Bseq`: the dimensionless forms `B^{(l)} = a_lA^{(l)}` of `def:relative-average-order`, `B^{(0)} = a₀A`,
  `B^{(l+1)} = (1/i)log𝓜_{U^{(l)}}(B^{(l)})` (`RelativeAverage.relLog`); since `a_jA^{(j)} = a_jQ_jA + C_j(U; a_jA)` with
  `Q_j` linear, the part of the second order of `C_j(U; a_jA)(c)` is that of `B^{(j)}(c)`, and `C2` is the bilinear map
  `𝖢^{(2)}(A₁, A₂)(c) = (2a_j)^{-1}D²B^{(j)}(c)(0)(A₁, A₂)` of `def:landau-operators`(iii) and the remark after it.
* `Delta2`: `Δ^{(2)}`, with `⟨A, Δ^{(2)}A⟩ = 2⟨H𝖢^{(2)}(A), J⟩` (`Delta2_form`); `Pcal`, `PcalT`: `𝒫 = I - DG'RD^*`
  and `𝒫^T = I - DRG'D^*`; `Delta2pi = 𝒫^TΔ^{(2)}𝒫`; `G1`, `H1`: `G_1`, `H_1` of `def:landau-operators`(iv).
* `Pfrak`, `Gfrak`: `𝔓` and `𝔊` of `eq:fluctuation-propagator`.
* `H0`, `Gc`, `Gtil`: `H_0`, `G_c`, `G̃` of `eq:second-operators`, with `QH_0 = I`, `QG̃ = 0`, `G̃Q^* = 0` on the
  compressed functions (`Q_H0`, `Q_Gtil`, `Gtil_Qs`) and their identification with the operators of
  `CriticalTheorem` (`H0_eq`, `Gtil_eq`).
-/
import CoreLean.SequenceOperators

open LinearMap (BilinForm)

noncomputable section

namespace CoreLean
namespace PairConcrete

open Lattices SequenceIndex MultiscaleAverages ConcretePairing SequenceAverages SequenceOperators CompressedInverse
  RelativeAverage

variable {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "GLN" => (Matrix (Fin N) (Fin N) ℂ)ˣ

/-! ### The symmetric operator of a bilinear form -/

section SymOp

variable {E : Type*} [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]

/-- The symmetric operator `S` with `⟨SA, B⟩ = ½(β(A, B) + β(B, A))`. -/
def symOp (BE : BilinForm ℂ E) (hE : BE.Nondegenerate) (β : BilinForm ℂ E) : E →ₗ[ℂ] E :=
  (BE.toDual hE).symm.toLinearMap ∘ₗ ((2 : ℂ)⁻¹ • (β + β.flip))

variable {BE : BilinForm ℂ E} {hE : BE.Nondegenerate} {β : BilinForm ℂ E}

theorem symOp_spec (A B : E) : BE (symOp BE hE β A) B = (2 : ℂ)⁻¹ * (β A B + β B A) := by
  simp only [symOp, LinearMap.comp_apply, LinearEquiv.coe_coe, BilinForm.apply_toDual_symm_apply,
    LinearMap.smul_apply, LinearMap.add_apply, smul_eq_mul]
  rfl

theorem symOp_diag (A : E) : BE (symOp BE hE β A) A = β A A := by
  rw [symOp_spec]; ring

theorem symOp_symm (hBE : ∀ x y, BE x y = BE y x) (A B : E) :
    BE (symOp BE hE β A) B = BE A (symOp BE hE β B) := by
  rw [hBE A, symOp_spec, symOp_spec]; ring

end SymOp

/-! ### The data of a pair -/

/-- A pair `(U, J)` on `T^{(0)}` with the parameters of the operators. -/
structure Data (S : SeqDom) (N : ℕ) where
  inN : (Matrix (Fin N) (Fin N) ℂ)ˣ → Prop
  log : (Matrix (Fin N) (Fin N) ℂ)ˣ → Matrix (Fin N) (Fin N) ℂ
  U : Config N (SequenceAverages.N0 S)
  J : Form1 N (SequenceAverages.N0 S)
  aa : ℝ
  ΩD : Set (Site (SequenceAverages.N0 S))

variable (S : SeqDom)

/-- The spacing `a₀ = L^{-k}` as a complex number. -/
abbrev aC : ℂ := ((a0 S : ℝ) : ℂ)

lemma aC_ne : aC S ≠ 0 := Complex.ofReal_ne_zero.mpr (a0_pos S).ne'

/-! ### The gauge defect and `Δ'_π` -/

section GaugeDefect

variable {n : ℕ} [NeZero n]

/-- `(λ, B) ↦ i[λ(b_-), B(b)] - i[B(b), Ad_{U(b)}λ(b_+)]`. -/
def defect1 (U : Config N n) : Form0 N n →ₗ[ℂ] Form1 N n →ₗ[ℂ] Form1 N n :=
  LinearMap.mk₂ ℂ
    (fun l B μ x => Complex.I • brk (l x) (B μ x) - Complex.I • brk (B μ x) (Ad (U μ x) (l (x + unit n μ))))
    (fun l l' B => by
      funext μ x
      simp only [Pi.add_apply, brk_add_left, brk_add_right, Ad_add, smul_add]
      abel)
    (fun c l B => by
      funext μ x
      simp only [Pi.smul_apply, brk_smul_left, brk_smul_right, Ad_smul, smul_sub, smul_comm Complex.I c])
    (fun l B B' => by
      funext μ x
      simp only [Pi.add_apply, brk_add_left, brk_add_right, smul_add]
      abel)
    (fun c l B => by
      funext μ x
      simp only [Pi.smul_apply, brk_smul_left, brk_smul_right, smul_sub, smul_comm Complex.I c])

/-- `(λ, λ') ↦ -i[λ(b_-), (D_Uλ')(b)]`. -/
def defect3 (a : ℂ) (U : Config N n) : Form0 N n →ₗ[ℂ] Form0 N n →ₗ[ℂ] Form1 N n :=
  LinearMap.mk₂ ℂ (fun l l' μ x => -(Complex.I • brk (l x) (D0 a U l' μ x)))
    (fun l l' l'' => by
      funext μ x
      simp only [Pi.add_apply, brk_add_left, smul_add, neg_add])
    (fun c l l' => by
      funext μ x
      simp only [Pi.smul_apply, brk_smul_left, smul_neg, smul_comm Complex.I c])
    (fun l l' l'' => by
      funext μ x
      have h := congrFun (congrFun ((D0L a U).map_add l' l'') μ) x
      simp only [D0L_apply] at h
      simp only [Pi.add_apply, h, brk_add_right, smul_add, neg_add])
    (fun c l l' => by
      funext μ x
      have h := congrFun (congrFun ((D0L a U).map_smul c l') μ) x
      simp only [D0L_apply] at h
      simp only [Pi.smul_apply, h, brk_smul_right, smul_neg, smul_comm Complex.I c])

end GaugeDefect

section Operators

variable [NeZero N] {G : GaugeGroup N} (hG : G.LieInput)

/-- `λ_A = G'RD^*A`. -/
def lamL (d : Data S N) : Form1 N (SequenceAverages.N0 S) →ₗ[ℂ] Form0 N (SequenceAverages.N0 S) :=
  Gp S hG d.inN d.log d.U d.aa d.ΩD ∘ₗ Rs S hG d.inN d.log d.U d.aa d.ΩD ∘ₗ Ds1L (aC S) d.U

/-- **`Q'λ_A = 0`**, on the compressed functions on `𝐁`. -/
theorem Qp_lam (d : Data S N)
    (hK : IsUnit (ckern (piFun hG (BPt S)) (Mop (Gp S hG d.inN d.log d.U d.aa d.ΩD) (Qpseq S d.inN d.log d.U)
      (QpseqStar S d.inN d.log d.U)))) (A : Form1 N (SequenceAverages.N0 S)) :
    piFun hG (BPt S) (Qpseq S d.inN d.log d.U (lamL S hG d A)) = 0 :=
  Qp_Gp_Rs S hG d.U d.aa d.ΩD d.inN d.log hK (Ds1L (aC S) d.U A)

/-- The bilinear map `X(A, B)` whose diagonal is `X(A)` of `eq:gauge-defect`. -/
def gaugeDefect (d : Data S N) :
    Form1 N (SequenceAverages.N0 S) →ₗ[ℂ] Form1 N (SequenceAverages.N0 S) →ₗ[ℂ] Form1 N (SequenceAverages.N0 S) :=
  (defect1 d.U).compl₁₂ (lamL S hG d) LinearMap.id + (defect3 (aC S) d.U).compl₁₂ (lamL S hG d) (lamL S hG d)

omit [NeZero N] in
/-- **`eq:gauge-defect`**: `X(A)(b) = i[λ_A(b_-), A(b)] - i[A(b), Ad_{U(b)}λ_A(b_+)] - i[λ_A(b_-), (Dλ_A)(b)]`. -/
theorem gaugeDefect_diag (d : Data S N) (A : Form1 N (SequenceAverages.N0 S)) (μ : Fin 4)
    (x : Site (SequenceAverages.N0 S)) :
    gaugeDefect S hG d A A μ x =
      Complex.I • brk (lamL S hG d A x) (A μ x) -
        Complex.I • brk (A μ x) (Ad (d.U μ x) (lamL S hG d A (x + unit _ μ))) -
        Complex.I • brk (lamL S hG d A x) (D0 (aC S) d.U (lamL S hG d A) μ x) := by
  simp only [gaugeDefect, defect1, defect3, LinearMap.add_apply, LinearMap.compl₁₂_apply, LinearMap.mk₂_apply,
    LinearMap.id_apply, Pi.add_apply]
  abel

/-- The bilinear form `(A, B) ↦ ⟨X(A, B), J⟩`. -/
def betaPi (d : Data S N) : BilinForm ℂ (Form1 N (SequenceAverages.N0 S)) :=
  (gaugeDefect S hG d).compr₂ ((pairForm1 (aC S)).flip d.J)

/-- **`Δ'_π`**, the symmetric operator with `⟨A, Δ'_πA⟩ = ⟨X(A), J⟩`. -/
def DeltaPi (d : Data S N) : Module.End ℂ (Form1 N (SequenceAverages.N0 S)) :=
  symOp (pairForm1 (aC S)) (pairForm1_nondegenerate (a0_pos S)) (betaPi S hG d)

theorem DeltaPi_form (d : Data S N) (A : Form1 N (SequenceAverages.N0 S)) :
    pairForm1 (aC S) A (DeltaPi S hG d A) = pairForm1 (aC S) (gaugeDefect S hG d A A) d.J := by
  rw [pairForm1_symm, DeltaPi, symOp_diag]
  rfl

theorem DeltaPi_symm (d : Data S N) (A B : Form1 N (SequenceAverages.N0 S)) :
    pairForm1 (aC S) (DeltaPi S hG d A) B = pairForm1 (aC S) A (DeltaPi S hG d B) :=
  symOp_symm (pairForm1_symm _) A B

/-- `Δ_𝖺` at the pair. -/
abbrev DA (d : Data S N) : Module.End ℂ (Form1 N (SequenceAverages.N0 S)) :=
  DeltaA S hG d.inN d.log d.U d.aa d.ΩD (aC_ne S)

/-- **`G_π = (Δ_𝖺 - Δ'_π)^{-1}`**. -/
def Gpi (d : Data S N) : Module.End ℂ (Form1 N (SequenceAverages.N0 S)) :=
  cinv (piF1 hG d.ΩD) (DA S hG d - DeltaPi S hG d)

/-- **`H = G_πQ^*(QG_πQ^*)^{-1}`**. -/
def Hpi (d : Data S N) : (LBond S → Mat) →ₗ[ℂ] Form1 N (SequenceAverages.N0 S) :=
  Hop (piFun hG (LBond S)) (Gpi S hG d) (Qseq S d.inN d.log d.U) (QseqStar S d.inN d.log d.U)

end Operators

/-! ### The part of the second order of the remainder -/

/-- The dimensionless forms `B^{(l)} = a_lA^{(l)}`: `B^{(0)} = B₀`, `B^{(l+1)} = (1/i)log𝓜_{U^{(l)}}(B^{(l)})`. -/
def Bseq (h m k : ℕ) (inN : GLN → Prop) (log : GLN → Mat) (U : Config N (nn h m k 0))
    (B0 : Form1 N (nn h m k 0)) : ∀ j, Form1 N (nn h m k j)
  | 0 => B0
  | j + 1 => fun κ y => relLog (Mpow h m k inN log U j) (Bseq h m k inN log U B0 j) (up h m k j y) κ h

/-- `A ↦ B^{(j)}(c)` with `B^{(0)} = a₀A`, at a bond `c` of `Γ_j`. -/
def remMap (inN : GLN → Prop) (log : GLN → Mat) (U : Config N (SequenceAverages.N0 S)) (c : LBond S) :
    Form1 N (SequenceAverages.N0 S) → Mat :=
  fun A => Bseq (hS S) S.mT S.k inN log U (aC S • A) c.1.1 c.1.2.2 (crd S c.1.1 c.1.2.1)

/-- **`𝖢^{(2)}(A₁, A₂)(c) = (2a_j)^{-1}D²B^{(j)}(c)(0)(A₁, A₂)`**. -/
def C2 (inN : GLN → Prop) (log : GLN → Mat) (U : Config N (SequenceAverages.N0 S)) :
    Form1 N (SequenceAverages.N0 S) →ₗ[ℂ] Form1 N (SequenceAverages.N0 S) →ₗ[ℂ] (LBond S → Mat) :=
  LinearMap.mk₂ ℂ
    (fun A₁ A₂ c => (((2 * c.ac : ℝ) : ℂ))⁻¹ • fderiv ℂ (fderiv ℂ (remMap S inN log U c)) 0 A₁ A₂)
    (fun A A' B => by funext c; simp only [map_add, ContinuousLinearMap.add_apply, smul_add, Pi.add_apply])
    (fun t A B => by
      funext c
      simp only [map_smul, ContinuousLinearMap.smul_apply, Pi.smul_apply, smul_comm t])
    (fun A B B' => by funext c; simp only [map_add, smul_add, Pi.add_apply])
    (fun t A B => by funext c; simp only [map_smul, Pi.smul_apply, smul_comm t])

/-- The diagonal: `𝖢^{(2)}(A)(c) = a_j^{-1}·½D²B^{(j)}(c)(0)(A, A)`, `a_j^{-1}` times the part of the second order. -/
theorem C2_diag (inN : GLN → Prop) (log : GLN → Mat) (U : Config N (SequenceAverages.N0 S))
    (A : Form1 N (SequenceAverages.N0 S)) (c : LBond S) :
    C2 S inN log U A A c =
      ((c.ac : ℝ) : ℂ)⁻¹ • ((2 : ℂ)⁻¹ • fderiv ℂ (fderiv ℂ (remMap S inN log U c)) 0 A A) := by
  simp only [C2, LinearMap.mk₂_apply, smul_smul]
  congr 1
  push_cast
  rw [mul_inv, mul_comm]

section Second

variable [NeZero N] {G : GaugeGroup N} (hG : G.LieInput)

/-- The bilinear form `(A₁, A₂) ↦ 2⟨H𝖢^{(2)}(A₁, A₂), J⟩`. -/
def beta2 (d : Data S N) : BilinForm ℂ (Form1 N (SequenceAverages.N0 S)) :=
  (C2 S d.inN d.log d.U).compr₂ (((pairForm1 (aC S)).flip d.J) ∘ₗ ((2 : ℂ) • Hpi S hG d))

/-- **`Δ^{(2)}`**, the symmetric operator with `⟨A, Δ^{(2)}A⟩ = 2⟨H𝖢^{(2)}(A), J⟩`. -/
def Delta2 (d : Data S N) : Module.End ℂ (Form1 N (SequenceAverages.N0 S)) :=
  symOp (pairForm1 (aC S)) (pairForm1_nondegenerate (a0_pos S)) (beta2 S hG d)

theorem Delta2_form (d : Data S N) (A : Form1 N (SequenceAverages.N0 S)) :
    pairForm1 (aC S) A (Delta2 S hG d A) = 2 * pairForm1 (aC S) (Hpi S hG d (C2 S d.inN d.log d.U A A)) d.J := by
  rw [pairForm1_symm, Delta2, symOp_diag]
  simp only [beta2, LinearMap.compr₂_apply, LinearMap.comp_apply, LinearMap.smul_apply, map_smul, smul_eq_mul]
  rfl

theorem Delta2_symm (d : Data S N) (A B : Form1 N (SequenceAverages.N0 S)) :
    pairForm1 (aC S) (Delta2 S hG d A) B = pairForm1 (aC S) A (Delta2 S hG d B) :=
  symOp_symm (pairForm1_symm _) A B

/-- `DRD^*` at the pair. -/
abbrev DRD (d : Data S N) : Module.End ℂ (Form1 N (SequenceAverages.N0 S)) :=
  D0L (aC S) d.U ∘ₗ Rs S hG d.inN d.log d.U d.aa d.ΩD ∘ₗ Ds1L (aC S) d.U

/-- **`𝒫 = I - DG'RD^*`**, `𝒫A = A - Dλ_A`. -/
def Pcal (d : Data S N) : Module.End ℂ (Form1 N (SequenceAverages.N0 S)) :=
  1 - D0L (aC S) d.U ∘ₗ lamL S hG d

/-- **`𝒫^T = I - DRG'D^*`**. -/
def PcalT (d : Data S N) : Module.End ℂ (Form1 N (SequenceAverages.N0 S)) :=
  1 - D0L (aC S) d.U ∘ₗ Rs S hG d.inN d.log d.U d.aa d.ΩD ∘ₗ Gp S hG d.inN d.log d.U d.aa d.ΩD ∘ₗ Ds1L (aC S) d.U

/-- **`Δ^{(2)}_π = 𝒫^TΔ^{(2)}𝒫`**. -/
def Delta2pi (d : Data S N) : Module.End ℂ (Form1 N (SequenceAverages.N0 S)) :=
  PcalT S hG d ∘ₗ Delta2 S hG d ∘ₗ Pcal S hG d

/-- **`G_1 = (Δ_𝖺 - Δ'_π - Δ^{(2)}_π)^{-1}`**. -/
def G1 (d : Data S N) : Module.End ℂ (Form1 N (SequenceAverages.N0 S)) :=
  cinv (piF1 hG d.ΩD) (DA S hG d - DeltaPi S hG d - Delta2pi S hG d)

/-- **`H_1 = G_1Q^*(QG_1Q^*)^{-1}`**. -/
def H1 (d : Data S N) : (LBond S → Mat) →ₗ[ℂ] Form1 N (SequenceAverages.N0 S) :=
  Hop (piFun hG (LBond S)) (G1 S hG d) (Qseq S d.inN d.log d.U) (QseqStar S d.inN d.log d.U)

/-- **`𝔓 = I - G_1Q^*(QG_1Q^*)^{-1}Q - G_1DRD^*`** (`eq:fluctuation-propagator`). -/
def Pfrak (d : Data S N) : Module.End ℂ (Form1 N (SequenceAverages.N0 S)) :=
  1 - H1 S hG d ∘ₗ Qseq S d.inN d.log d.U - G1 S hG d ∘ₗ DRD S hG d

/-- **`𝔊 = G_1 - G_1DRD^*G_1 - G_1Q^*(QG_1Q^*)^{-1}QG_1`** (`eq:fluctuation-propagator`). -/
def Gfrak (d : Data S N) : Module.End ℂ (Form1 N (SequenceAverages.N0 S)) :=
  G1 S hG d - G1 S hG d ∘ₗ DRD S hG d ∘ₗ G1 S hG d - H1 S hG d ∘ₗ Qseq S d.inN d.log d.U ∘ₗ G1 S hG d

/-- **`H_0 = GQ^*(QGQ^*)^{-1}`** (`eq:second-operators`). -/
def H0 (d : Data S N) : (LBond S → Mat) →ₗ[ℂ] Form1 N (SequenceAverages.N0 S) :=
  Hop (piFun hG (LBond S)) (Gs S hG d.inN d.log d.U d.aa d.ΩD (aC_ne S)) (Qseq S d.inN d.log d.U)
    (QseqStar S d.inN d.log d.U)

/-- **`G_c = (Δ_𝖺 - Δ^{(2)})^{-1}`** (`eq:second-operators`). -/
def Gc (d : Data S N) : Module.End ℂ (Form1 N (SequenceAverages.N0 S)) :=
  cinv (piF1 hG d.ΩD) (DA S hG d - Delta2 S hG d)

/-- **`G̃ = G_c - G_cQ^*(QG_cQ^*)^{-1}QG_c`** (`eq:second-operators`). -/
def Gtil (d : Data S N) : Module.End ℂ (Form1 N (SequenceAverages.N0 S)) :=
  Gtop (piFun hG (LBond S)) (Gc S hG d) (Qseq S d.inN d.log d.U) (QseqStar S d.inN d.log d.U)

/-- **`QH_0 = I`** on the compressed functions, whenever `(QGQ^*)^{-1}` exists. -/
theorem Q_H0 (d : Data S N)
    (hK : IsUnit (ckern (piFun hG (LBond S)) (Qseq S d.inN d.log d.U ∘ₗ Gs S hG d.inN d.log d.U d.aa d.ΩD (aC_ne S) ∘ₗ
      QseqStar S d.inN d.log d.U))) (μ : LBond S → Mat) :
    piFun hG (LBond S) (Qseq S d.inN d.log d.U (H0 S hG d μ)) = piFun hG (LBond S) μ :=
  Q_Hop (piFun_idem hG _) hK μ

/-- **`QG̃ = 0`** on the compressed functions, whenever `(QG_cQ^*)^{-1}` exists. -/
theorem Q_Gtil (d : Data S N)
    (hK : IsUnit (ckern (piFun hG (LBond S)) (Qseq S d.inN d.log d.U ∘ₗ Gc S hG d ∘ₗ QseqStar S d.inN d.log d.U)))
    (A : Form1 N (SequenceAverages.N0 S)) : piFun hG (LBond S) (Qseq S d.inN d.log d.U (Gtil S hG d A)) = 0 :=
  Q_Gtop (piFun_idem hG _) hK A

/-- **`G̃Q^* = 0`** on the compressed functions, whenever `(QG_cQ^*)^{-1}` exists. -/
theorem Gtil_Qs (d : Data S N)
    (hK : IsUnit (ckern (piFun hG (LBond S)) (Qseq S d.inN d.log d.U ∘ₗ Gc S hG d ∘ₗ QseqStar S d.inN d.log d.U)))
    (μ : LBond S → Mat) : Gtil S hG d (QseqStar S d.inN d.log d.U (piFun hG (LBond S) μ)) = 0 :=
  Gtop_Qs (piFun_idem hG _) hK μ

/-- `H_0` is the operator `H0` of `CriticalTheorem` with `M_0^{-1} = (QGQ^*)^{-1}`. -/
theorem H0_eq (d : Data S N) :
    H0 S hG d = CriticalTheorem.H0 (QseqStar S d.inN d.log d.U) (Gs S hG d.inN d.log d.U d.aa d.ΩD (aC_ne S))
      (cinv (piFun hG (LBond S)) (Qseq S d.inN d.log d.U ∘ₗ Gs S hG d.inN d.log d.U d.aa d.ΩD (aC_ne S) ∘ₗ
        QseqStar S d.inN d.log d.U)) := rfl

/-- `G̃` is the operator `Gt` of `CriticalTheorem` with `M^{-1} = (QG_cQ^*)^{-1}`. -/
theorem Gtil_eq (d : Data S N) :
    Gtil S hG d = CriticalTheorem.Gt (Qseq S d.inN d.log d.U) (QseqStar S d.inN d.log d.U) (Gc S hG d)
      (cinv (piFun hG (LBond S)) (Qseq S d.inN d.log d.U ∘ₗ Gc S hG d ∘ₗ QseqStar S d.inN d.log d.U)) := rfl

end Second

end PairConcrete
end CoreLean

end
