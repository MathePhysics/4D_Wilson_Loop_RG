import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# A Neumann-series surjectivity lemma

Let `S, B : D → H` be linear, with `S` bijective onto the Banach space `H` and
`‖B x‖ ≤ q ‖S x‖` for some `q < 1`.  Then `S + B` is onto.  Indeed `C = B S⁻¹` is a bounded
operator on `H` with `‖C‖ ≤ q < 1`, so `I + C` is invertible by the Neumann series, and
`(S + B) (S⁻¹ (I + C)⁻¹ f) = f`.

This is the step "`‖C‖ < 1` implies `-1 ∉ σ(C)`, so `Ran(I + C) = H`, and `(I + C)(A + iμ₀) φ =
(A + B + iμ₀) φ`" in the proof of the Kato–Rellich theorem, Reed–Simon II, Theorem X.12, p. 163.

## Main result

* `KatoRellich.exists_add_eq_of_norm_le`: `∀ f, ∃ x, S x + B x = f`.
-/

noncomputable section

namespace KatoRellich

variable {𝕜 D E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [CompleteSpace E] [AddCommGroup D] [Module 𝕜 D]

/-- **Neumann series**: if `S : D → E` is a linear bijection and `‖B x‖ ≤ q ‖S x‖` with
`0 ≤ q < 1`, then `S + B` is onto. -/
theorem exists_add_eq_of_norm_le (S B : D →ₗ[𝕜] E) (hS : Function.Bijective S) {q : ℝ}
    (hq0 : 0 ≤ q) (hq : q < 1) (hB : ∀ x, ‖B x‖ ≤ q * ‖S x‖) (f : E) :
    ∃ x, S x + B x = f := by
  let e : D ≃ₗ[𝕜] E := LinearEquiv.ofBijective S hS
  have he : ∀ g, S (e.symm g) = g := fun g => e.apply_symm_apply g
  let C₀ : E →ₗ[𝕜] E := B ∘ₗ e.symm.toLinearMap
  have hC₀ : ∀ g, ‖C₀ g‖ ≤ q * ‖g‖ := fun g => by
    have h := hB (e.symm g)
    rw [he] at h
    exact h
  let C : E →L[𝕜] E := C₀.mkContinuous q hC₀
  have hCn : ‖-C‖ < 1 := by
    rw [norm_neg]
    exact (C₀.mkContinuous_norm_le hq0 hC₀).trans_lt hq
  let u := Units.oneSub (-C) hCn
  let g : E := (↑u⁻¹ : E →L[𝕜] E) f
  refine ⟨e.symm g, ?_⟩
  have hu : (1 - -C) * (↑u⁻¹ : E →L[𝕜] E) = 1 := by
    rw [← Units.val_oneSub (-C) hCn]
    exact u.mul_inv
  have hg : g + C g = f := by
    have h := congrArg (fun L : E →L[𝕜] E => L f) hu
    simpa [sub_neg_eq_add, add_mul] using h
  rw [he]
  exact hg

end KatoRellich
