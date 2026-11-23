/-
`lem:walk-calculus`(i) of BALABAN_CORE.tex (`a021c13be348`), in the abstract setting of `WalkProduct.lean`. A map
`𝒯_□` with the block bound `(b, p, δ)` in the cube `□̃^{r+4}` (the points `S` of `𝐁` in it: block norms vanishing
outside `S`, and `[𝒯_□f]_y ≤ ba_{j(y)}^pΣ_{y' ∈ S}e^{-δd(y, y')}[f]_{y'}` for `y ∈ S`), with the walk `(□)` of the
radius `r` whose first and last points are `S` and whose distance is at most `d` on `S` (`d_{(□)}(y, y') = d(y, y')`
for `y ∈ □̃^{r+4}`, the point `z = y` being admissible), satisfies (W1) with the constants `(b, p, δ)`
(`one_cube_decay`).
-/
import CoreLean.WalkProduct

open Finset

noncomputable section

namespace CoreLean
namespace WalkProduct

open Composition

variable {β Ω : Type*} [Fintype β] [DecidableEq β] {B : Setting β} {W : Walks β Ω}

/-- **`lem:walk-calculus`(i)**: a term of one cube with decay is a walk term. -/
theorem one_cube_decay {V V' : Type*} {nrm : V → β → ℝ} {nrm' : V' → β → ℝ} (hn : ∀ f y, 0 ≤ nrm f y)
    {T : V → V'} {ω : Ω} {S : Finset β} (hSf : W.first ω = S) (hSl : W.last ω = S)
    (hdw : ∀ y ∈ S, ∀ y' ∈ S, W.dw ω y y' ≤ B.d y y') {b : ℝ} (hb : 0 ≤ b) {p : ℤ} {δ : ℝ} (hδ : 0 ≤ δ)
    (hT0 : ∀ f, ∀ y ∉ S, nrm' (T f) y = 0)
    (hT : ∀ f, ∀ y ∈ S, nrm' (T f) y ≤ b * B.a (B.j y) ^ p *
      ∑ y' ∈ S, Real.exp (-(δ * B.d y y')) * nrm f y') :
    Bound B W nrm nrm' T ω b p δ 0 := by
  intro f
  refine ⟨fun y hy => hT0 f y (hSf ▸ hy), fun y hy => ?_⟩
  rw [hSf] at hy
  refine (hT f y hy).trans ?_
  rw [hSl]
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun y' hy' => ?_)
    (mul_nonneg hb (zpow_pos (B.a_pos _) _).le)
  refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) (hn f y')
  have := hdw y hy y' hy'
  nlinarith

end WalkProduct
end CoreLean

end
