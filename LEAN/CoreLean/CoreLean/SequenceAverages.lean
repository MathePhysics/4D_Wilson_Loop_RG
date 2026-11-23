/-
The concrete layer, step C3 completed (`CONCRETE_LAYER.md`): the average `Q` of a sequence of domains of
BALABAN_CORE.tex (`615c66b253fe`, `def:operators`(i)), its transpose `Q^*` (`def:operators`(iii)), and the constraint
operator `Q^*𝖺Q` (`eq:constraint-forms`).

* `hS S = (L - 1)/2`, so that `L = 2hS + 1` (`L_eq`); the lattices `T^{(j)}` are `Site (nn (hS S) m_𝕋 k j)`
  (`MultiscaleAverages`), the fine lattice `T^{(0)}` being identified with the points of the torus by
  `Lattices.emb` (`LatticesTorus.lean`).
* `crd S j y`: the site of `T^{(j)}`, in the units of the scale `j`, of a point `y` of `T^{(j)} ⊂ T^{(0)}` of the
  torus: the fine point `x = emb⁻¹y` divided by `L^j`.
* `Qseq S inN log U`: `(QA)(c) = (Q_j(U)A)(c)` for a positive bond `c = (y, y + a_je_μ)` of the layer `Γ_j`, with the
  composite `Q_j(U)` of `eq:composite-linear-part` (`MultiscaleAverages.Qcomp`); `Q_0 = I` (`Qseq_scale_zero`).
* `QseqStar`: the transpose with respect to `⟨·,·⟩` of `eq:pairing` at the spacing `a₀ = L^{-k}` and `(·,·)_w`
  (`QseqStar_spec`); `constraintOp`: `Q^*𝖺Q = Q^* ∘ (𝖺a_c^{-2}) ∘ Q` with the constraint form of `eq:constraint-forms`
  (`constraintOp_form`).
-/
import CoreLean.SequenceIndex
import CoreLean.MultiscaleAverages

noncomputable section

namespace CoreLean
namespace SequenceAverages

open Lattices SequenceIndex MultiscaleAverages ConcretePairing

variable {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "GLN" => (Matrix (Fin N) (Fin N) ℂ)ˣ

variable (S : SeqDom)

/-- `L = 2hS + 1`. -/
def hS : ℕ := (S.L - 1) / 2

lemma L_eq : S.L = 2 * hS S + 1 := by
  obtain ⟨r, hr⟩ := S.L_odd
  unfold hS; omega

/-- The fine lattice `T^{(0)}` as `Site (nn hS m_𝕋 k 0)`. -/
abbrev N0 : ℕ := nn (hS S) S.mT S.k 0

lemma N0_eq : N0 S = 2 * S.L ^ (S.mT + S.k) := by
  simp only [N0, nn, Nat.sub_zero, ← L_eq]

/-- The site of `T^{(j)}` of a point `y` of the torus in `T^{(j)}`: `emb⁻¹y` divided by `L^j`. -/
def crd (j : ℕ) (y : Tor (ellT S.L S.mT)) : Site (nn (hS S) S.mT S.k j) :=
  let x : Site (N0 S) := Function.invFun (emb (N := N0 S) S.L S.k S.mT) y
  fun ν => (((x ν).val / S.L ^ j : ℕ) : ZMod (nn (hS S) S.mT S.k j))

/-- `crd 0` inverts `emb` on `T^{(0)}`. -/
lemma crd_zero_emb (x : Site (N0 S)) : crd S 0 (emb (N := N0 S) S.L S.k S.mT x) = x := by
  have hinj := emb_injective (N := N0 S) (L := S.L) (k := S.k) (m := S.mT) S.Lpos (N0_eq S)
  funext ν
  simp only [crd, pow_zero, Nat.div_one, Function.leftInverse_invFun hinj x, ZMod.natCast_val,
    ZMod.cast_id', id_eq]

/-- **The average of a sequence**, `(QA)(c) = (Q_j(U)A)(c)` for a positive bond `c` of `Γ_j`. -/
def Qseq (inN : GLN → Prop) (log : GLN → Mat) (U : Config N (N0 S)) : Form1 N (N0 S) →ₗ[ℂ] (LBond S → Mat) :=
  LinearMap.pi fun c => (LinearMap.proj (crd S c.1.1 c.1.2.1)) ∘ₗ (LinearMap.proj c.1.2.2) ∘ₗ
    Qcomp (hS S) S.mT S.k inN log U c.1.1

lemma Qseq_apply (inN : GLN → Prop) (log : GLN → Mat) (U : Config N (N0 S)) (A : Form1 N (N0 S)) (c : LBond S) :
    Qseq S inN log U A c = Qcomp (hS S) S.mT S.k inN log U c.1.1 A c.1.2.2 (crd S c.1.1 c.1.2.1) := rfl

/-- `Q_0 = I`: at a bond of the layer `Γ₀`, `(QA)(c) = A(c)`. -/
theorem Qseq_scale_zero (inN : GLN → Prop) (log : GLN → Mat) (U : Config N (N0 S)) (A : Form1 N (N0 S))
    (c : LBond S) (hc : c.1.1 = 0) :
    Qseq S inN log U A c = A c.1.2.2 (crd S 0 c.1.2.1) := by
  obtain ⟨⟨j, y, μ⟩, hq⟩ := c
  simp only at hc
  subst hc
  rfl

/-- `a₀ = L^{-k}`. -/
abbrev a0 : ℝ := eta S.L S.k

lemma a0_pos : 0 < a0 S := eta_pos S.Lpos

/-- **`Q^*`**, the transpose of `Q` with respect to `⟨·,·⟩` at `a₀` and `(·,·)_w`. -/
def QseqStar (inN : GLN → Prop) (log : GLN → Mat) (U : Config N (N0 S)) : (LBond S → Mat) →ₗ[ℂ] Form1 N (N0 S) :=
  transpose (pairForm1 ((a0 S : ℝ) : ℂ)) (pairLB S N) (pairForm1_nondegenerate (a0_pos S)) (Qseq S inN log U)

theorem QseqStar_spec (inN : GLN → Prop) (log : GLN → Mat) (U : Config N (N0 S)) (μ : LBond S → Mat)
    (A : Form1 N (N0 S)) :
    pairForm1 ((a0 S : ℝ) : ℂ) (QseqStar S inN log U μ) A = pairLB S N μ (Qseq S inN log U A) :=
  transpose_spec _ _ _ _ μ A

/-- **The constraint operator** `Q^*𝖺Q = Q^* ∘ (𝖺a_c^{-2}) ∘ Q`. -/
def constraintOp (inN : GLN → Prop) (log : GLN → Mat) (U : Config N (N0 S)) (aa : ℂ) :
    Form1 N (N0 S) →ₗ[ℂ] Form1 N (N0 S) :=
  QseqStar S inN log U ∘ₗ mulW (fun c : LBond S => aa * (((c.ac : ℝ) : ℂ) ^ 2)⁻¹) ∘ₗ Qseq S inN log U

/-- **`eq:constraint-forms`**: `⟨A, Q^*𝖺QA⟩ = 𝖺Σ_c a_c²tr((QA)(c))²`, the sum over the positive bonds of the
layers. -/
theorem constraintOp_form (inN : GLN → Prop) (log : GLN → Mat) (U : Config N (N0 S)) (aa : ℂ)
    (A : Form1 N (N0 S)) :
    pairForm1 ((a0 S : ℝ) : ℂ) (constraintOp S inN log U aa A) A =
      aa * ∑ c : LBond S, ((c.ac : ℝ) : ℂ) ^ 2 * ntr (Qseq S inN log U A c * Qseq S inN log U A c) := by
  have h := constraint_form (pairForm1 ((a0 S : ℝ) : ℂ)) (pairForm1_nondegenerate (a0_pos S))
    (fun c : LBond S => ((c.ac : ℝ) : ℂ)) (fun c => by have := LBond.ac_pos c; exact_mod_cast this.ne')
    (Qseq S inN log U) aa A
  have e : (pairLB S N) = wpair (fun c : LBond S => ((c.ac : ℝ) : ℂ) ^ 4) := by
    simp only [pairLB, CriticalConcrete.pairF]; push_cast; rfl
  simp only [constraintOp, LinearMap.comp_apply, QseqStar]
  rw [e]
  exact h

end SequenceAverages
end CoreLean

end
