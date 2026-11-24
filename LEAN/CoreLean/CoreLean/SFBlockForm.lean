/-
`prop:sf-block` of BALABAN_CORE.tex (`d4ef86a9a5fd`): the form of the scaled block operator at the trivial
configuration, on the fine lattice of a sequence of domains (`a₀ = 1`):
`Σ_y tr(μ̂(y)^*(Q'G'²Q'^*μ)(y)) = ‖G'Q'^*μ‖₂²` with `μ̂(y) = a_y⁴μ(y)` (the step "The lower bound at the trivial field":
the averages at the trivial configuration are means, `Q'` is the transpose of `Q'^*`, and `G'` is symmetric and commutes
with `X ↦ X^*`), and with `lower_triv` the coercivity `Re Σ_y tr(μ̂(y)^*(T̂₀μ̂)(y)) ≥ c_lo²Σ_y|μ̂(y)|²`.

* `avg_pair_triv`: `Σ_y a_y⁴tr(A(y)(Q'g)(y)) = ⟨Q'^*A, g⟩` at the trivial transports.
* `form_triv`: the identity; `coercive_triv`: the coercivity.
-/
import CoreLean.SFBlockLower
import CoreLean.SchurII

open Finset Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace CoreLean
namespace SFBounds

open Lattices SeqDom Blocks SmallFieldBlocks SFBox SFBox.SeqDomBox SmallFieldDecay SmallFieldCoercivity
  SequenceOperators CompressedInverse

variable (S : SeqDom) {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "GLN" => (Matrix (Fin N) (Fin N) ℂ)ˣ
local notation "NF" => SequenceAverages.N0 S
set_option quotPrecheck false in
local notation "jj" => (S.toDomSeq).sc

/-- **`Q'` is the transpose of `Q'^*`** at the trivial transports. -/
lemma avg_pair_triv (A g : Site NF → Mat) :
    ∑ y ∈ detB S.toDomSeq, (((S.L : ℝ) ^ (4 * jj y) : ℝ) : ℂ) * ntr (A y * avgW S.toDomSeq (W1 S) y g) =
      P0 (QpStar S (W1 S) A) g := by
  have hL : (0 : ℝ) < S.L := by exact_mod_cast S.Lpos
  simp only [P0, pairForm0, ConcretePairing.wpair_apply, a1, Complex.ofReal_one, one_pow, one_mul, QpStar_triv]
  rw [sum_blocks S.toDomSeq]
  refine sum_congr rfl fun y hy => ?_
  rw [avgW_blk S.toDomSeq (W1 S) hy g]
  simp only [toDomSeq_L]
  have hc : (((S.L : ℝ) ^ (4 * jj y) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (pow_pos hL _).ne'
  rw [mul_smul_comm, ntr_smul, ← mul_assoc, mul_inv_cancel₀ hc, one_mul, mul_sum, ntr_sum]
  refine sum_congr rfl fun x hx => ?_
  rw [(sc_mem_blk S.toDomSeq hy hx).2]
  simp [Ad]

lemma unitary_one : ((1 : GLN) : Mat) ∈ unitaryGroup (Fin N) ℂ := by simp

/-- **The form at the trivial configuration**: `Σ_y a_y⁴tr(μ(y)^*(Q'G'²Q'^*μ)(y)) = ‖G'Q'^*μ‖₂²`. -/
theorem form_triv [NeZero N] (ΩD : Set (Site NF)) (μ : Site NF → Mat) :
    ∑ y ∈ detB S.toDomSeq, (((S.L : ℝ) ^ (4 * jj y) : ℝ) : ℂ) * ntr ((μ y)ᴴ * avgW S.toDomSeq (W1 S) y
      (Gp' S.toDomSeq (cfgX (X0 S)) (W1 S) ΩD (Gp' S.toDomSeq (cfgX (X0 S)) (W1 S) ΩD (QpStar S (W1 S) μ)))) =
      ((∑ x, hs2 (Gp' S.toDomSeq (cfgX (X0 S)) (W1 S) ΩD (QpStar S (W1 S) μ) x) : ℝ) : ℂ) := by
  set G := Gp' S.toDomSeq (cfgX (N := N) (X0 S)) (W1 S) ΩD
  set v := QpStar S (W1 S) μ
  have hK := hK_triv (N := N) S ΩD
  have hU : ∀ ν x, ((cfgX (X0 S) ν x : GLN) : Mat) ∈ unitaryGroup (Fin N) ℂ := fun ν x => by
    simp [cfgX, X0]
  have hW : ∀ y x, ((W1 S y x : GLN) : Mat) ∈ unitaryGroup (Fin N) ℂ := fun _ _ => unitary_one
  rw [avg_pair_triv S (fun y => (μ y)ᴴ)]
  have hv : QpStar S (W1 S) (fun y => (μ y)ᴴ) = cstar v := by
    funext x; simp only [QpStar_triv, cstar, v]
  rw [hv, ← Gp'_symm S.toDomSeq _ _ _ hK, Gp'_cstar S.toDomSeq _ _ _ hU hW hK]
  simp only [P0, pairForm0, ConcretePairing.wpair_apply, a1, Complex.ofReal_one, one_pow, one_mul, cstar]
  push_cast
  refine sum_congr rfl fun x _ => ?_
  rw [Schur.ntr_conj_self, hs_sq]

/-- **The coercivity at the trivial configuration**:
`Re Σ_y a_y⁴tr(μ(y)^*(Q'G'²Q'^*μ)(y)) ≥ c_lo²Σ_y a_y⁸|μ(y)|²` for `μ` on the points of `𝐁` whose blocks lie in `Ω_D`. -/
theorem coercive_triv [NeZero N] (ΩD : Set (Site NF)) (μ : Site NF → Mat)
    (hμ : ∀ y ∈ detB S.toDomSeq, μ y ≠ 0 → ∀ x ∈ Blk S.toDomSeq (jj y) y, x ∈ ΩD) :
    ((9 / 32) ^ 4 / (864 + 4 * N)) ^ 2 * Ssq S μ ≤
      (∑ y ∈ detB S.toDomSeq, (((S.L : ℝ) ^ (4 * jj y) : ℝ) : ℂ) * ntr ((μ y)ᴴ * avgW S.toDomSeq (W1 S) y
        (Gp' S.toDomSeq (cfgX (X0 S)) (W1 S) ΩD (Gp' S.toDomSeq (cfgX (X0 S)) (W1 S) ΩD (QpStar S (W1 S) μ))))).re := by
  rw [form_triv, Complex.ofReal_re]
  have h := lower_triv S ΩD μ hμ
  have hS := Ssq_nonneg S μ
  have hc : 0 ≤ (9 / 32 : ℝ) ^ 4 / (864 + 4 * N) := by positivity
  have hsum : 0 ≤ ∑ x, hs (Gp' S.toDomSeq (cfgX (X0 S)) (W1 S) ΩD (QpStar S (W1 S) μ) x) ^ 2 :=
    sum_nonneg fun _ _ => sq_nonneg _
  have h2 := pow_le_pow_left₀ (mul_nonneg hc (Real.sqrt_nonneg _)) h 2
  rw [mul_pow, Real.sq_sqrt hS, Real.sq_sqrt hsum] at h2
  simpa only [hs_sq] using h2

end SFBounds
end CoreLean

end
