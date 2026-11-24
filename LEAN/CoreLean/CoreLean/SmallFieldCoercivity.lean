/-
`lem:sf-coercivity` of BALABAN_CORE.tex (`542c68192a44`), in the model `Blocks.DomSeq` (fine lattice, `η = 1`,
`a_j = Lʲ`).

* `aseq_mem`: the numbers `𝖺_j` of `def:operators` at `𝖺 = 1` lie in `[1 - L^{-2}, 1]` (the step "The coefficients":
  `t ↦ t/(L^{-2} + t)` maps `[1 - L^{-2}, 1]` into itself).
* `sf_coercivity`: `eq:sf-coercivity` in the form `‖∂λ‖₂² + ‖λ‖_w² ≤ 3(‖∂λ‖₂² + Σ_{y ∈ 𝐁}𝖺_{j(y)}a_{j(y)}²|m_y|²)`,
  with the mean `m_y = (Q'_{j(y)}(id)λ)(y)` of `λ` over the block `Δ(y)` and the norms `‖∂λ‖₂² = Σ_x Σ_μ
  |λ(x + e_μ) - λ(x)|²`, `‖λ‖_w² = Σ_x a_{j(x)}^{-2}|λ(x)|²`, for `λ` with values in a real inner product space (the
  matrices with the Hilbert–Schmidt norm). The right side is `3⟨λ^*, Δ'_𝖺(id)λ⟩` by `eq:scalar-form`. The proof is
  the core's: on each block the Poincaré inequality (`DiscretePoincare.block_ineq`, with the constant `n²` for the
  core's `2n²`), and the sum over the blocks, which partition the lattice and whose bonds are bonds of the lattice.
-/
import CoreLean.SequenceOperators
import CoreLean.SmallFieldBlocks

open Finset
open scoped Classical

noncomputable section

namespace CoreLean
namespace SmallFieldCoercivity

open SequenceOperators

/-- **`𝖺_j ∈ [1 - L^{-2}, 1]`** for `𝖺 = 1` and `L ≥ 1`. -/
theorem aseq_mem (L : ℕ) (hL : 1 ≤ L) :
    ∀ j, 1 - ((L : ℝ) ^ 2)⁻¹ ≤ aseq 1 L j ∧ aseq 1 L j ≤ 1
  | 0 => ⟨by simp only [aseq]; have : (0 : ℝ) ≤ ((L : ℝ) ^ 2)⁻¹ := by positivity
             linarith, le_rfl⟩
  | 1 => ⟨by simp only [aseq]; have : (0 : ℝ) ≤ ((L : ℝ) ^ 2)⁻¹ := by positivity
             linarith, le_rfl⟩
  | j + 2 => by
      obtain ⟨h1, h2⟩ := aseq_mem L hL (j + 1)
      have hpos := aseq_pos (aa := 1) one_pos L (j + 1)
      set a := aseq 1 L (j + 1)
      set q : ℝ := ((L : ℝ) ^ 2)⁻¹
      have hq : 0 ≤ q := by positivity
      have hden : 0 < 1 * q + a := by linarith
      have e : aseq 1 L (j + 2) = 1 * a / (1 * q + a) := rfl
      rw [e]
      refine ⟨?_, ?_⟩
      · rw [le_div_iff₀ hden]
        nlinarith
      · rw [div_le_one hden]
        linarith

/-! ### The coercivity at the trivial configuration -/

open Blocks SmallFieldBlocks DiscretePoincare

variable {n : ℕ} [NeZero n] (S : DomSeq n) {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- `‖∂λ‖₂² = Σ_x Σ_μ |λ(x + e_μ) - λ(x)|²`, the sum over all the bonds. -/
def dsq (lam : Site n → E) : ℝ := ∑ x, ∑ μ : Fin 4, ‖lam (x + unit n μ) - lam x‖ ^ 2

/-- `‖λ‖_w² = Σ_x a_{j(x)}^{-2}|λ(x)|²`. -/
def wnorm (lam : Site n → E) : ℝ := ∑ x, (((S.L : ℝ) ^ (2 * S.sc x))⁻¹) * ‖lam x‖ ^ 2

/-- The mean of `λ` over the block of `y ∈ 𝐁`, `(Q'_{j(y)}(id)λ)(y)`. -/
def mBlk (y : Site n) (lam : Site n → E) : E :=
  meanB 4 (S.L ^ S.sc y) (fun o => lam (phi S (S.sc y) y o))

/-- The constraint form at the trivial configuration, `Σ_{y ∈ 𝐁}𝖺_{j(y)}a_{j(y)}²|(Q'_{j(y)}λ)(y)|²`. -/
def cform (lam : Site n → E) : ℝ :=
  ∑ y ∈ detB S, aseq 1 S.L (S.sc y) * (S.L : ℝ) ^ (2 * S.sc y) * ‖mBlk S y lam‖ ^ 2

lemma sc_of_mem_Blk {x y : Site n} (hy : y ∈ detB S) (hx : x ∈ Blk S (S.sc y) y) : S.sc x = S.sc y := by
  obtain ⟨x0, -, rfl⟩ := mem_image.1 hy
  simp only [Blk, mem_filter, mem_univ, true_and] at hx
  have h := (fiber_eq S x0 x).mpr hx
  rw [← sc_bc S x, h]

/-- The bonds of the box of a block are bonds of the lattice in the block. -/
lemma grad_le (y : Site n) (hy : y ∈ detB S) (lam : Site n → E) :
    grad 4 (S.L ^ S.sc y) (fun o => lam (phi S (S.sc y) y o)) ≤
      ∑ x ∈ Blk S (S.sc y) y, ∑ μ : Fin 4, ‖lam (x + unit n μ) - lam x‖ ^ 2 := by
  obtain ⟨x0, -, rfl⟩ := mem_image.1 hy
  have hlat := inLat_bc (S := S) x0
  have hjk : S.sc (bc S x0) ≤ S.k := S.sc_le _
  rw [sum_Blk _ hjk hlat, grad, Finset.sum_comm]
  refine sum_le_sum fun o _ => sum_le_sum fun μ _ => ?_
  split_ifs
  · rw [phi_update]
  · positivity

/-- **`lem:sf-coercivity`**: `‖∂λ‖₂² + ‖λ‖_w² ≤ 3(‖∂λ‖₂² + Σ_{y ∈ 𝐁}𝖺_{j(y)}a_{j(y)}²|m_y|²)`. -/
theorem sf_coercivity (lam : Site n → E) : dsq lam + wnorm S lam ≤ 3 * (dsq lam + cform S lam) := by
  have hL3 : (3 : ℝ) ≤ S.L := by exact_mod_cast S.three_le_L
  have hLpos : (0 : ℝ) < S.L := by linarith
  -- the weighted norm, block by block
  have hw : wnorm S lam ≤ ∑ y ∈ detB S, (∑ x ∈ Blk S (S.sc y) y, ∑ μ : Fin 4, ‖lam (x + unit n μ) - lam x‖ ^ 2 +
      (S.L : ℝ) ^ (2 * S.sc y) * ‖mBlk S y lam‖ ^ 2) := by
    rw [wnorm, sum_blocks S]
    refine sum_le_sum fun y hy => ?_
    obtain ⟨x0, -, rfl⟩ := mem_image.1 hy
    set j := S.sc (bc S x0)
    have hlat := inLat_bc (S := S) x0
    have hjk : j ≤ S.k := S.sc_le _
    have hpos : 0 < S.L ^ j := by have := S.three_le_L; positivity
    have e1 : ∑ x ∈ Blk S j (bc S x0), ((S.L : ℝ) ^ (2 * S.sc x))⁻¹ * ‖lam x‖ ^ 2 =
        ((S.L : ℝ) ^ (2 * j))⁻¹ * ∑ o ∈ box 4 (S.L ^ j), ‖lam (phi S j (bc S x0) o)‖ ^ 2 := by
      rw [mul_sum, sum_Blk _ hjk hlat]
      refine sum_congr rfl fun o ho => ?_
      rw [sc_of_mem_Blk S hy (phi_mem j hjk hlat ho)]
    rw [e1]
    have hb := block_ineq hpos 4 (fun o => lam (phi S j (bc S x0) o))
    have hg := grad_le S (bc S x0) hy lam
    have hpow : ((S.L ^ j : ℕ) : ℝ) ^ 2 = (S.L : ℝ) ^ (2 * j) := by push_cast; rw [← pow_mul, mul_comm]
    have hpow4 : ((S.L ^ j : ℕ) : ℝ) ^ 4 = (S.L : ℝ) ^ (2 * j) * (S.L : ℝ) ^ (2 * j) := by
      push_cast; rw [← pow_mul, ← pow_add]; ring_nf
    rw [hpow, hpow4] at hb
    have hP : (0 : ℝ) < (S.L : ℝ) ^ (2 * j) := by positivity
    rw [inv_mul_le_iff₀ hP]
    calc ∑ o ∈ box 4 (S.L ^ j), ‖lam (phi S j (bc S x0) o)‖ ^ 2
        ≤ (S.L : ℝ) ^ (2 * j) * grad 4 (S.L ^ j) (fun o => lam (phi S j (bc S x0) o)) +
          (S.L : ℝ) ^ (2 * j) * (S.L : ℝ) ^ (2 * j) * ‖mBlk S (bc S x0) lam‖ ^ 2 := hb
      _ ≤ (S.L : ℝ) ^ (2 * j) * (∑ x ∈ Blk S j (bc S x0), ∑ μ : Fin 4, ‖lam (x + unit n μ) - lam x‖ ^ 2 +
          (S.L : ℝ) ^ (2 * j) * ‖mBlk S (bc S x0) lam‖ ^ 2) := by
        rw [mul_add, ← mul_assoc]
        exact add_le_add (mul_le_mul_of_nonneg_left hg hP.le) le_rfl
  -- the bonds of the blocks are bonds of the lattice
  have hbonds : ∑ y ∈ detB S, ∑ x ∈ Blk S (S.sc y) y, ∑ μ : Fin 4, ‖lam (x + unit n μ) - lam x‖ ^ 2 = dsq lam := by
    rw [dsq, sum_blocks S]
  -- the means, with `𝖺_j ≥ 8/9`
  have hmeans : ∑ y ∈ detB S, (S.L : ℝ) ^ (2 * S.sc y) * ‖mBlk S y lam‖ ^ 2 ≤ 9 / 8 * cform S lam := by
    rw [cform, mul_sum]
    refine sum_le_sum fun y _ => ?_
    have ha := (aseq_mem S.L (by have := S.three_le_L; omega) (S.sc y)).1
    have hq : ((S.L : ℝ) ^ 2)⁻¹ ≤ 1 / 9 := by
      rw [inv_le_comm₀ (by positivity) (by norm_num)]; nlinarith
    have h89 : (8 : ℝ) / 9 ≤ aseq 1 S.L (S.sc y) := by linarith
    have hnn : 0 ≤ (S.L : ℝ) ^ (2 * S.sc y) * ‖mBlk S y lam‖ ^ 2 := by positivity
    nlinarith
  have hdsq : 0 ≤ dsq lam := by unfold dsq; positivity
  have hcf : 0 ≤ cform S lam := by
    unfold cform
    refine sum_nonneg fun y _ => ?_
    have := aseq_pos (aa := 1) one_pos S.L (S.sc y)
    positivity
  rw [sum_add_distrib, hbonds] at hw
  linarith

end SmallFieldCoercivity
end CoreLean

end
