/-
The analyticity of the remainders of higher order (BALABAN_CORE.tex `615c66b253fe`, `prop:relative-average`(i),
`def:relative-average-order`): when every level `M^i(U)`, `i < k`, satisfies the background conditions, the maps
`A ↦ B^{(j)}(c)` are analytic at `0`, and the regularity hypotheses of `RemainderLink` (`C²` at `0`, differentiability
near `0`) are discharged.

* `AnLevel V h`: `B ↦ (1/i)log𝓜_V(B)(c)` is analytic at `0` at every coarse bond; `anLevel_of_good` (from `GoodAt`,
  `LoopsGood`, `RelativeAverage.relLog_analyticAt`); `AnLevel.diffLevel`.
* `Phi_analyticAt`, `Bseq_analyticAt`, `remMap_analyticAt`.
* `C2_symm_of_levels`, `Delta2_polar_of_levels`, `C2_eq_remainder_of_levels`: `𝖢^{(2)}` symmetric, the polarisation of
  `Δ^{(2)}`, and `𝖢^{(2)} = (2a_c)^{-1}D²C_j(0)`, under `AnLevel` at the levels `j < k`.
-/
import CoreLean.RemainderLink
import CoreLean.RelativeAverageAnalytic

open Filter Topology
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace CoreLean
namespace RemainderLink

open Lattices SequenceIndex MultiscaleAverages SequenceAverages PairConcrete RelativeAverage ConcretePairing

variable {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "GLN" => (Matrix (Fin N) (Fin N) ℂ)ˣ

/-- `B ↦ (1/i)log𝓜_V(B)(c)` is analytic at `0` at every coarse bond. -/
def AnLevel {n : ℕ} [NeZero n] (V : Config N n) (h : ℕ) : Prop :=
  ∀ y κ, AnalyticAt ℂ (fun B => relLog V B y κ h) 0

theorem anLevel_of_good {n : ℕ} [NeZero n] {V : Config N n} {h : ℕ} (hg : ∀ y, GoodAt V y h)
    (hl : ∀ y μ, LoopsGood V y μ h) : AnLevel V h :=
  fun y κ => relLog_analyticAt (hg y) (hg _) (hl y κ)

lemma AnLevel.diffLevel {n : ℕ} [NeZero n] {V : Config N n} {h : ℕ} (hA : AnLevel V h) : DiffLevel V h :=
  fun y κ => (hA y κ).differentiableAt

lemma Phi_analyticAt (h m k j : ℕ) {V : Config N (nn h m k j)} (hV : AnLevel V h) :
    AnalyticAt ℂ (Phi h m k j V) 0 :=
  analyticAt_pi_iff.2 fun κ => analyticAt_pi_iff.2 fun y => hV (up h m k j y) κ

/-- **`B^{(j)}` is analytic at `0`** when the levels `i < K` are. -/
theorem Bseq_analyticAt (h m k : ℕ) (inN : GLN → Prop) (log : GLN → Mat) (U : Config N (nn h m k 0)) (K : ℕ)
    (hlev : ∀ i < K, AnLevel (Mpow h m k inN log U i) h) :
    ∀ j ≤ K, AnalyticAt ℂ (fun B0 => Bseq h m k inN log U B0 j) 0
  | 0, _ => analyticAt_id
  | j + 1, hj =>
      (Phi_analyticAt h m k j (hlev j (by omega))).comp_of_eq
        (Bseq_analyticAt h m k inN log U K hlev j (by omega)) (Bseq_zero h m k inN log U j)

variable (S : SeqDom)

/-- **`A ↦ B^{(j)}(c)` is analytic at `0`** when the levels `j < k` are. -/
theorem remMap_analyticAt (inN : GLN → Prop) (log : GLN → Mat) (U : Config N (SequenceAverages.N0 S))
    (hlev : ∀ j < S.k, AnLevel (Mpow (hS S) S.mT S.k inN log U j) (hS S)) (c : LBond S) :
    AnalyticAt ℂ (remMap S inN log U c) 0 := by
  have hB := Bseq_analyticAt (hS S) S.mT S.k inN log U S.k hlev c.1.1 c.2.1
  have hs : AnalyticAt ℂ (fun A : Form1 N (SequenceAverages.N0 S) => aC S • A) 0 :=
    analyticAt_id.fun_const_smul (c := aC S)
  have hBs := hB.comp_of_eq hs (smul_zero _)
  have he := ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Site (nn (hS S) S.mT S.k c.1.1) => Mat)
    (crd S c.1.1 c.1.2.1)).comp (ContinuousLinearMap.proj (R := ℂ)
      (φ := fun _ : Fin 4 => Site (nn (hS S) S.mT S.k c.1.1) → Mat) c.1.2.2)).analyticAt
    (Bseq (hS S) S.mT S.k inN log U (aC S • (0 : Form1 N (SequenceAverages.N0 S))) c.1.1)
  exact he.comp hBs

/-- **`𝖢^{(2)}` is symmetric** when the levels `j < k` satisfy `AnLevel`. -/
theorem C2_symm_of_levels (inN : GLN → Prop) (log : GLN → Mat) (U : Config N (SequenceAverages.N0 S))
    (hlev : ∀ j < S.k, AnLevel (Mpow (hS S) S.mT S.k inN log U j) (hS S)) (c : LBond S)
    (A₁ A₂ : Form1 N (SequenceAverages.N0 S)) :
    C2 S inN log U A₁ A₂ c = C2 S inN log U A₂ A₁ c :=
  C2_symm S inN log U c (remMap_analyticAt S inN log U hlev c).contDiffAt A₁ A₂

/-- **The polarisation of `Δ^{(2)}`**, `⟨Δ^{(2)}A₁, A₂⟩ = 2⟨H𝖢^{(2)}(A₁, A₂), J⟩`, when the levels `j < k` satisfy
`AnLevel`. -/
theorem Delta2_polar_of_levels [NeZero N] {G : GaugeGroup N} (hG : G.LieInput) (d : Data S N)
    (hlev : ∀ j < S.k, AnLevel (Mpow (hS S) S.mT S.k d.inN d.log d.U j) (hS S))
    (A₁ A₂ : Form1 N (SequenceAverages.N0 S)) :
    pairForm1 (aC S) (Delta2 S hG d A₁) A₂ =
      2 * pairForm1 (aC S) (Hpi S hG d (C2 S d.inN d.log d.U A₁ A₂)) d.J :=
  Delta2_polar S hG d (fun c => (remMap_analyticAt S d.inN d.log d.U hlev c).contDiffAt) A₁ A₂

/-- **`𝖢^{(2)}(A₁, A₂)(c) = (2a_c)^{-1}D²C_j(c)(0)(A₁, A₂)`** when the levels `j < k` satisfy `AnLevel`. -/
theorem C2_eq_remainder_of_levels (inN : GLN → Prop) (log : GLN → Mat) (U : Config N (SequenceAverages.N0 S))
    (hlev : ∀ j < S.k, AnLevel (Mpow (hS S) S.mT S.k inN log U j) (hS S)) (c : LBond S)
    (A₁ A₂ : Form1 N (SequenceAverages.N0 S)) :
    C2 S inN log U A₁ A₂ c = (((2 * c.ac : ℝ) : ℂ))⁻¹ • fderiv ℂ (fderiv ℂ (Cseq S inN log U c)) 0 A₁ A₂ :=
  C2_eq_remainder S inN log U c
    ((remMap_analyticAt S inN log U hlev c).eventually_analyticAt.mono fun _ hA => hA.differentiableAt) A₁ A₂

/-- **The remainder vanishes to the first order** when the levels `j < k` satisfy `AnLevel`. -/
theorem Cseq_hasFDerivAt_of_levels (inN : GLN → Prop) (log : GLN → Mat) (U : Config N (SequenceAverages.N0 S))
    (hlev : ∀ j < S.k, AnLevel (Mpow (hS S) S.mT S.k inN log U j) (hS S)) (c : LBond S) :
    HasFDerivAt (Cseq S inN log U c) (0 : Form1 N (SequenceAverages.N0 S) →L[ℂ] Mat) 0 :=
  Cseq_hasFDerivAt S inN log U (fun j hj => (hlev j hj).diffLevel) c

end RemainderLink
end CoreLean

end
