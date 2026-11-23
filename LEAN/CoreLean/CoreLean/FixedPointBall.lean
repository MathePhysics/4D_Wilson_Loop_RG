/-
The fixed-point arguments of `prop:fixed-points`, `prop:divergence-fixed-points`(iii), and
`prop:triple-fixed-points`(ii)–(iii) of BALABAN_CORE.tex (`a021c13be348`), in abstract form. On a Banach space:

* a map of the closed ball of the radius `a` into itself with the Lipschitz constant `½` has exactly one fixed point
  in the ball (`fixed_point_ball`), and the fixed point satisfies `‖𝒜‖ ≤ 2‖Φ(0)‖` (`fixed_point_bound`), which with
  `‖Φ(0)‖ ≤ ½C(γ + ‖𝔄‖²)` is `eq:fixed-point-bound`;
* the fixed points in two balls agree when the map is a contraction of the larger one (`fixed_point_agree`, the step
  "the two families of functions agree" of the proof of `prop:fixed-points`);
* a map with values in the kernel of `Q` has its fixed point there (`fixed_point_ker`, `Q𝒜₀ = 0`);
* the derivative of the fixed point, `𝒜' = Φ_A'𝒜' + r` with `w(Φ_A'𝒜') ≤ ½w(𝒜')`, satisfies `w(𝒜') ≤ 2w(r)` for every
  norm `w` (`derivative_bound`, the form of `eq:triple-decay`).
-/
import Mathlib

open Metric

noncomputable section

namespace CoreLean
namespace FixedPointBall

variable {X : Type*} [NormedAddCommGroup X] [CompleteSpace X]

/-- **The fixed point** of a contraction of a closed ball into itself. -/
theorem fixed_point_ball (Φ : X → X) {a : ℝ} (ha : 0 ≤ a) (hmaps : ∀ A, ‖A‖ ≤ a → ‖Φ A‖ ≤ a)
    (hlip : ∀ A B, ‖A‖ ≤ a → ‖B‖ ≤ a → ‖Φ A - Φ B‖ ≤ 1 / 2 * ‖A - B‖) :
    ∃! A, ‖A‖ ≤ a ∧ Φ A = A := by
  set S := closedBall (0 : X) a
  haveI : CompleteSpace S := (isClosed_closedBall).completeSpace_coe
  haveI : Nonempty S := ⟨⟨0, mem_closedBall_self ha⟩⟩
  have hmem : ∀ A : S, ‖(A : X)‖ ≤ a := fun A => mem_closedBall_zero_iff.1 A.2
  set f : S → S := fun A => ⟨Φ A, mem_closedBall_zero_iff.2 (hmaps A (hmem A))⟩
  have hf : ContractingWith (1 / 2 : NNReal) f := by
    refine ⟨by rw [div_lt_one (by norm_num)]; norm_num, LipschitzWith.of_dist_le_mul fun A B => ?_⟩
    rw [Subtype.dist_eq, Subtype.dist_eq, dist_eq_norm, dist_eq_norm]
    simpa using hlip A B (hmem A) (hmem B)
  obtain ⟨A, hA⟩ := hf.exists_fixedPoint (⟨0, mem_closedBall_self ha⟩ : S) (edist_ne_top _ _)
  refine ⟨A, ⟨hmem A, congrArg Subtype.val hA.1⟩, fun B ⟨hB, hfix⟩ => ?_⟩
  have hBS : B ∈ S := mem_closedBall_zero_iff.2 hB
  have : (⟨B, hBS⟩ : S) = A := hf.fixedPoint_unique' (Subtype.ext hfix) hA.1
  exact congrArg Subtype.val this

/-- **The bound** `‖𝒜‖ ≤ 2‖Φ(0)‖`. -/
theorem fixed_point_bound (Φ : X → X) {a : ℝ} (ha : 0 ≤ a)
    (hlip : ∀ A B, ‖A‖ ≤ a → ‖B‖ ≤ a → ‖Φ A - Φ B‖ ≤ 1 / 2 * ‖A - B‖) {A : X} (hA : ‖A‖ ≤ a)
    (hfix : Φ A = A) : ‖A‖ ≤ 2 * ‖Φ 0‖ := by
  have h0 : ‖(0 : X)‖ ≤ a := by simpa using ha
  have h1 : ‖A‖ ≤ ‖Φ A - Φ 0‖ + ‖Φ 0‖ := by
    calc ‖A‖ = ‖Φ A‖ := by rw [hfix]
      _ = ‖(Φ A - Φ 0) + Φ 0‖ := by rw [sub_add_cancel]
      _ ≤ ‖Φ A - Φ 0‖ + ‖Φ 0‖ := norm_add_le _ _
  have h2 := hlip A 0 hA h0
  rw [sub_zero] at h2
  linarith

/-- **The fixed points in two balls agree**. -/
theorem fixed_point_agree (Φ : X → X) {a a' : ℝ} (ha : 0 ≤ a) (haa : a ≤ a')
    (hmaps' : ∀ A, ‖A‖ ≤ a' → ‖Φ A‖ ≤ a')
    (hlip' : ∀ A B, ‖A‖ ≤ a' → ‖B‖ ≤ a' → ‖Φ A - Φ B‖ ≤ 1 / 2 * ‖A - B‖) {A A' : X} (hA : ‖A‖ ≤ a)
    (hfix : Φ A = A) (hA' : ‖A'‖ ≤ a') (hfix' : Φ A' = A') : A = A' := by
  obtain ⟨B, -, huniq⟩ := fixed_point_ball Φ (ha.trans haa) hmaps' hlip'
  rw [huniq A ⟨hA.trans haa, hfix⟩, huniq A' ⟨hA', hfix'⟩]

/-- **`Q𝒜 = 0`** when `Φ` has values in the kernel of `Q`. -/
theorem fixed_point_ker {Y : Type*} [AddCommGroup Y] (Q : X →+ Y) (Φ : X → X) (hQ : ∀ A, Q (Φ A) = 0)
    {A : X} (hfix : Φ A = A) : Q A = 0 := by
  rw [← hfix, hQ]

/-- **The derivative of the fixed point**: `w(𝒜') ≤ ½w(𝒜') + w(r)` gives `w(𝒜') ≤ 2w(r)`. -/
theorem derivative_bound {w wd wr : ℝ} (h : w ≤ wd + wr) (hd : wd ≤ 1 / 2 * w) : w ≤ 2 * wr := by
  linarith

end FixedPointBall
end CoreLean

end
