/-
The linear part and the remainder of higher order (BALABAN_CORE.tex `615c66b253fe`, `def:relative-average-order`,
`eq:composite-linear-part`) for the concrete objects: the dimensionless forms `B^{(j)} = a_jA^{(j)}` of
`PairConcrete.Bseq` have the derivative `a_jQ_j(U)` at `0`, so that `C_j(U; a_jA) = B^{(j)} - a_jQ_jA` vanishes to the
first order, and `𝖢^{(2)}` of `PairConcrete.C2` is `a_j^{-1}` times the part of the second order of `C_j`.

* `DiffLevel V h`: `B ↦ (1/i)log𝓜_V(B)(c)` is differentiable at `0` at every coarse bond; it holds under the
  background conditions `GoodAt`, `LoopsGood` (`diffLevel_of_good`, from `relLog_differentiableAt`).
* `Bseq_zero`: `B^{(j)} = 0` for `B^{(0)} = 0` (`relLog_zero`).
* `Bseq_hasFDerivAt`: `D B^{(j)}(0) = L^jQ_j(U)` (the chain rule along the levels, `Q(V) = L^{-1}D relLog(0)`).
* `remMap_hasFDerivAt`: `D(A ↦ B^{(j)}(c))(0) = a_c(Q·)(c)` with `B^{(0)} = a₀A`, `a_c = L^ja₀`.
* `Cseq`: the remainder `C_j(U; a_jA)(c) = B^{(j)}(c) - a_c(QA)(c)`; `Cseq_zero`, `Cseq_hasFDerivAt` (it vanishes to the
  first order); `C2_eq_remainder`: `𝖢^{(2)}(A₁, A₂)(c) = (2a_c)^{-1}D²C_j(c)(0)(A₁, A₂)` when `A ↦ B^{(j)}(c)` is
  differentiable near `0` (its analyticity, `prop:relative-average`(i)).
-/
import CoreLean.PairConcrete

open Filter Topology
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace CoreLean
namespace RemainderLink

open Lattices SequenceIndex MultiscaleAverages SequenceAverages PairConcrete RelativeAverage ConcretePairing

variable {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "GLN" => (Matrix (Fin N) (Fin N) ℂ)ˣ

/-- `B ↦ (1/i)log𝓜_V(B)(c)` is differentiable at `0` at every coarse bond. -/
def DiffLevel {n : ℕ} [NeZero n] (V : Config N n) (h : ℕ) : Prop :=
  ∀ y κ, DifferentiableAt ℂ (fun B => relLog V B y κ h) 0

theorem diffLevel_of_good {n : ℕ} [NeZero n] {V : Config N n} {h : ℕ} (hg : ∀ y, GoodAt V y h)
    (hl : ∀ y μ, LoopsGood V y μ h) : DiffLevel V h :=
  fun y κ => relLog_differentiableAt (hg y) (hg _) (hl y κ)

/-- `B^{(j)} = 0` for `B^{(0)} = 0`. -/
lemma Bseq_zero (h m k : ℕ) (inN : GLN → Prop) (log : GLN → Mat) (U : Config N (nn h m k 0)) :
    ∀ j, Bseq h m k inN log U 0 j = 0
  | 0 => rfl
  | j + 1 => by
      funext κ y
      simp only [Bseq, Bseq_zero h m k inN log U j, relLog_zero, Pi.zero_apply]

/-- The map of one level, `B ↦ ((1/i)log𝓜_V(B)(Ly, κ))_{κ, y}`. -/
def Phi (h m k j : ℕ) (V : Config N (nn h m k j)) (B : Form1 N (nn h m k j)) : Form1 N (nn h m k (j + 1)) :=
  fun κ y => relLog V B (up h m k j y) κ h

lemma Lc_ne (h : ℕ) : (((2 * h + 1 : ℕ) : ℂ)) ≠ 0 := by exact_mod_cast (show 2 * h + 1 ≠ 0 by omega)

/-- `DΦ(0) = L·Q(V)` at every coarse bond. -/
lemma Phi_hasFDerivAt (h m k j : ℕ) {V : Config N (nn h m k j)} (hV : DiffLevel V h) :
    HasFDerivAt (Phi h m k j V) (LinearMap.toContinuousLinearMap (((2 * h + 1 : ℕ) : ℂ) • Qstep h m k j V)) 0 := by
  refine hasFDerivAt_pi'' fun κ => hasFDerivAt_pi'' fun y => ?_
  refine (hV (up h m k j y) κ).hasFDerivAt.congr_fderiv ?_
  ext B : 1
  change fderiv ℂ (fun B => relLog V B (up h m k j y) κ h) 0 B =
    ((((2 * h + 1 : ℕ) : ℂ)) • Qstep h m k j V) B κ y
  rw [LinearMap.smul_apply, Pi.smul_apply, Pi.smul_apply, Qstep_apply, Qlin, ContinuousLinearMap.smul_apply,
    smul_smul, mul_inv_cancel₀ (Lc_ne h), one_smul]

/-- **`D B^{(j)}(0) = L^jQ_j(U)`**, when the levels `i < K` are differentiable. -/
theorem Bseq_hasFDerivAt (h m k : ℕ) (inN : GLN → Prop) (log : GLN → Mat) (U : Config N (nn h m k 0)) (K : ℕ)
    (hlev : ∀ i < K, DiffLevel (Mpow h m k inN log U i) h) :
    ∀ j ≤ K, HasFDerivAt (fun B0 => Bseq h m k inN log U B0 j)
      (LinearMap.toContinuousLinearMap ((((2 * h + 1 : ℕ) : ℂ)) ^ j • Qcomp h m k inN log U j)) 0
  | 0, _ => by
      refine (hasFDerivAt_id (0 : Form1 N (nn h m k 0))).congr_fderiv ?_
      ext B : 1
      change B = ((((2 * h + 1 : ℕ) : ℂ)) ^ 0 • Qcomp h m k inN log U 0) B
      rw [pow_zero, one_smul, Qcomp_zero, LinearMap.id_apply]
  | j + 1, hj => by
      have hin := Bseq_hasFDerivAt h m k inN log U K hlev j (by omega)
      have hΦ : HasFDerivAt (Phi h m k j (Mpow h m k inN log U j))
          (LinearMap.toContinuousLinearMap (((2 * h + 1 : ℕ) : ℂ) • Qstep h m k j (Mpow h m k inN log U j)))
          (Bseq h m k inN log U 0 j) := by
        rw [Bseq_zero]; exact Phi_hasFDerivAt h m k j (hlev j (by omega))
      refine (hΦ.comp (0 : Form1 N (nn h m k 0)) hin).congr_fderiv ?_
      ext B : 1
      change (((2 * h + 1 : ℕ) : ℂ) • Qstep h m k j (Mpow h m k inN log U j))
          (((((2 * h + 1 : ℕ) : ℂ)) ^ j • Qcomp h m k inN log U j) B) =
        ((((2 * h + 1 : ℕ) : ℂ)) ^ (j + 1) • Qcomp h m k inN log U (j + 1)) B
      rw [LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.smul_apply, map_smul, smul_smul, Qcomp_succ,
        LinearMap.comp_apply, pow_succ, mul_comm]

variable (S : SeqDom)

/-- The derivative `A ↦ a_c(QA)(c)` at a bond `c` of the layers. -/
def Lseq (inN : GLN → Prop) (log : GLN → Mat) (U : Config N (SequenceAverages.N0 S)) (c : LBond S) :
    Form1 N (SequenceAverages.N0 S) →L[ℂ] Mat :=
  LinearMap.toContinuousLinearMap ((((c.ac : ℝ) : ℂ)) • ((LinearMap.proj c) ∘ₗ Qseq S inN log U))

lemma Lseq_apply (inN : GLN → Prop) (log : GLN → Mat) (U : Config N (SequenceAverages.N0 S)) (c : LBond S)
    (A : Form1 N (SequenceAverages.N0 S)) : Lseq S inN log U c A = ((c.ac : ℝ) : ℂ) • Qseq S inN log U A c := rfl

lemma ac_eq (c : LBond S) : (((c.ac : ℝ) : ℂ)) = (((2 * hS S + 1 : ℕ) : ℂ)) ^ c.1.1 * aC S := by
  rw [← L_eq]
  simp only [LBond.ac, sp, aC, a0]
  push_cast
  rfl

/-- **`D(A ↦ B^{(j)}(c))(0) = a_c(Q·)(c)`** (`eq:composite-linear-part`). -/
theorem remMap_hasFDerivAt (inN : GLN → Prop) (log : GLN → Mat) (U : Config N (SequenceAverages.N0 S))
    (hlev : ∀ j < S.k, DiffLevel (Mpow (hS S) S.mT S.k inN log U j) (hS S)) (c : LBond S) :
    HasFDerivAt (remMap S inN log U c) (Lseq S inN log U c) 0 := by
  have hB := Bseq_hasFDerivAt (hS S) S.mT S.k inN log U S.k hlev c.1.1 c.2.1
  have hs : HasFDerivAt (fun A : Form1 N (SequenceAverages.N0 S) => aC S • A)
      (aC S • ContinuousLinearMap.id ℂ (Form1 N (SequenceAverages.N0 S))) 0 :=
    (hasFDerivAt_id (0 : Form1 N (SequenceAverages.N0 S))).const_smul (aC S)
  have hB' : HasFDerivAt (fun B0 => Bseq (hS S) S.mT S.k inN log U B0 c.1.1)
      (LinearMap.toContinuousLinearMap ((((2 * hS S + 1 : ℕ) : ℂ)) ^ c.1.1 • Qcomp (hS S) S.mT S.k inN log U c.1.1))
      (aC S • (0 : Form1 N (SequenceAverages.N0 S))) := by
    rw [smul_zero]; exact hB
  have he := ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Site (nn (hS S) S.mT S.k c.1.1) => Mat)
    (crd S c.1.1 c.1.2.1)).comp (ContinuousLinearMap.proj (R := ℂ)
      (φ := fun _ : Fin 4 => Site (nn (hS S) S.mT S.k c.1.1) → Mat) c.1.2.2)).hasFDerivAt
    (x := Bseq (hS S) S.mT S.k inN log U (aC S • (0 : Form1 N (SequenceAverages.N0 S))) c.1.1)
  refine (he.comp (0 : Form1 N (SequenceAverages.N0 S))
    (hB'.comp (0 : Form1 N (SequenceAverages.N0 S)) hs)).congr_fderiv ?_
  ext A : 1
  change ((((2 * hS S + 1 : ℕ) : ℂ)) ^ c.1.1 • Qcomp (hS S) S.mT S.k inN log U c.1.1) (aC S • A) c.1.2.2
      (crd S c.1.1 c.1.2.1) =
    ((c.ac : ℝ) : ℂ) • Qcomp (hS S) S.mT S.k inN log U c.1.1 A c.1.2.2 (crd S c.1.1 c.1.2.1)
  rw [LinearMap.smul_apply, map_smul, smul_smul, Pi.smul_apply, Pi.smul_apply, ac_eq]

/-- **The remainder** `C_j(U; a_jA)(c) = B^{(j)}(c) - a_c(QA)(c)`. -/
def Cseq (inN : GLN → Prop) (log : GLN → Mat) (U : Config N (SequenceAverages.N0 S)) (c : LBond S)
    (A : Form1 N (SequenceAverages.N0 S)) : Mat :=
  remMap S inN log U c A - Lseq S inN log U c A

theorem Cseq_zero (inN : GLN → Prop) (log : GLN → Mat) (U : Config N (SequenceAverages.N0 S)) (c : LBond S) :
    Cseq S inN log U c 0 = 0 := by
  have h0 : remMap S inN log U c 0 = 0 := by
    simp only [remMap, smul_zero, Bseq_zero, Pi.zero_apply]
  simp only [Cseq, h0, (Lseq S inN log U c).map_zero, sub_zero]

/-- **The remainder vanishes to the first order.** -/
theorem Cseq_hasFDerivAt (inN : GLN → Prop) (log : GLN → Mat) (U : Config N (SequenceAverages.N0 S))
    (hlev : ∀ j < S.k, DiffLevel (Mpow (hS S) S.mT S.k inN log U j) (hS S)) (c : LBond S) :
    HasFDerivAt (Cseq S inN log U c) (0 : Form1 N (SequenceAverages.N0 S) →L[ℂ] Mat) 0 := by
  have h := (remMap_hasFDerivAt S inN log U hlev c).sub ((Lseq S inN log U c).hasFDerivAt (x := 0))
  rw [sub_self] at h
  exact h

/-- **`𝖢^{(2)}` is `a_c^{-1}` times the part of the second order of the remainder**:
`𝖢^{(2)}(A₁, A₂)(c) = (2a_c)^{-1}D²C_j(c)(0)(A₁, A₂)`, when `A ↦ B^{(j)}(c)` is differentiable near `0`. -/
theorem C2_eq_remainder (inN : GLN → Prop) (log : GLN → Mat) (U : Config N (SequenceAverages.N0 S)) (c : LBond S)
    (hdiff : ∀ᶠ A in 𝓝 (0 : Form1 N (SequenceAverages.N0 S)), DifferentiableAt ℂ (remMap S inN log U c) A)
    (A₁ A₂ : Form1 N (SequenceAverages.N0 S)) :
    C2 S inN log U A₁ A₂ c = (((2 * c.ac : ℝ) : ℂ))⁻¹ • fderiv ℂ (fderiv ℂ (Cseq S inN log U c)) 0 A₁ A₂ := by
  have hev : fderiv ℂ (Cseq S inN log U c) =ᶠ[𝓝 0]
      fun A => fderiv ℂ (remMap S inN log U c) A - Lseq S inN log U c := by
    filter_upwards [hdiff] with A hA
    show fderiv ℂ (fun A => remMap S inN log U c A - Lseq S inN log U c A) A = _
    rw [fderiv_fun_sub hA (Lseq S inN log U c).differentiableAt, ContinuousLinearMap.fderiv]
  have e : fderiv ℂ (fderiv ℂ (Cseq S inN log U c)) 0 = fderiv ℂ (fderiv ℂ (remMap S inN log U c)) 0 := by
    rw [hev.fderiv_eq]
    exact fderiv_sub_const (f := fderiv ℂ (remMap S inN log U c)) (Lseq S inN log U c)
  rw [e]
  rfl

/-- **`𝖢^{(2)}` is symmetric** when `A ↦ B^{(j)}(c)` is `C²` at `0` (over `ℂ` the symmetry of the second derivative
needs `C²` only, `ContDiffAt.isSymmSndFDerivAt`; the core's holomorphy, `prop:relative-average`(i), gives it). -/
theorem C2_symm (inN : GLN → Prop) (log : GLN → Mat) (U : Config N (SequenceAverages.N0 S)) (c : LBond S)
    (h2 : ContDiffAt ℂ 2 (remMap S inN log U c) 0) (A₁ A₂ : Form1 N (SequenceAverages.N0 S)) :
    C2 S inN log U A₁ A₂ c = C2 S inN log U A₂ A₁ c := by
  have hs := h2.isSymmSndFDerivAt (by simp)
  simp only [C2, LinearMap.mk₂_apply]
  rw [hs A₁ A₂]

/-- **The polarisation of `Δ^{(2)}`** (the remark after `def:landau-operators`):
`⟨Δ^{(2)}A₁, A₂⟩ = 2⟨H𝖢^{(2)}(A₁, A₂), J⟩`, when the maps `A ↦ B^{(j)}(c)` are `C²` at `0`. -/
theorem Delta2_polar [NeZero N] {G : GaugeGroup N} (hG : G.LieInput) (d : Data S N)
    (h2 : ∀ c, ContDiffAt ℂ 2 (remMap S d.inN d.log d.U c) 0) (A₁ A₂ : Form1 N (SequenceAverages.N0 S)) :
    pairForm1 (aC S) (Delta2 S hG d A₁) A₂ =
      2 * pairForm1 (aC S) (Hpi S hG d (C2 S d.inN d.log d.U A₁ A₂)) d.J := by
  have hC : C2 S d.inN d.log d.U A₂ A₁ = C2 S d.inN d.log d.U A₁ A₂ := by
    funext c; exact C2_symm S d.inN d.log d.U c (h2 c) A₂ A₁
  have hb : ∀ X Y : Form1 N (SequenceAverages.N0 S),
      beta2 S hG d X Y = 2 * pairForm1 (aC S) (Hpi S hG d (C2 S d.inN d.log d.U X Y)) d.J := fun X Y => by
    simp only [beta2, LinearMap.compr₂_apply, LinearMap.comp_apply, LinearMap.smul_apply, map_smul, smul_eq_mul]
    rfl
  rw [Delta2, symOp_spec, hb, hb, hC]
  ring

end RemainderLink
end CoreLean

end
