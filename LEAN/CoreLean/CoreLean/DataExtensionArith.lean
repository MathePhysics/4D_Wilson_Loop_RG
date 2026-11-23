/-
`lem:data-extension` of BALABAN_CORE.tex (`a021c13be348`), the estimates of its proof.

* `norm_list_prod_sub_le`: in a normed ring with `‖1‖ = 1`, for factors of norm at most one (unitary matrices),
  `‖Π aᵢ - Π bᵢ‖ ≤ Σ‖aᵢ - bᵢ‖`; with four bonds this is `|V''(∂p) - Ṽ(∂p)| ≤ 4C_axL²ε₁` (`plaquette_four`).
* `plaquette_constant`: `ε₁ + 4C_axL²ε₁ = C'_bε₁`, `C'_b = 1 + 4C_axL²`.
* `transports_diff`: six exchanges of coordinates, each across at most `¼L²` plaquettes of at most `√Nε₁`, give
  `(3/2)√NL²ε₁`.
* `average_constant`: `C'₃·2LC_axL²ε₁ ≤ C₁ε₁` with `C₁ = 4LC'₃C_axL²`, and `(π/2)LC_axL²ε₁ < c'₄` from
  `πLC_axL²ε₁ < c'₄`.
-/
import Mathlib

noncomputable section

namespace CoreLean
namespace DataExtensionArith

variable {R : Type*} [NormedRing R] [NormOneClass R]

/-- **The telescoping bound**: `‖Π aᵢ - Π bᵢ‖ ≤ Σ‖aᵢ - bᵢ‖` for factors of norm at most one. -/
theorem norm_list_prod_sub_le : ∀ (l : List (R × R)), (∀ p ∈ l, ‖p.1‖ ≤ 1 ∧ ‖p.2‖ ≤ 1) →
    ‖(l.map Prod.fst).prod - (l.map Prod.snd).prod‖ ≤ (l.map fun p => ‖p.1 - p.2‖).sum
  | [], _ => by simp
  | (a, b) :: l, h => by
    have hab := h (a, b) (List.mem_cons_self ..)
    have hl : ∀ p ∈ l, ‖p.1‖ ≤ 1 ∧ ‖p.2‖ ≤ 1 := fun p hp => h p (List.mem_cons_of_mem _ hp)
    have ih := norm_list_prod_sub_le l hl
    have hP : ‖(l.map Prod.snd).prod‖ ≤ 1 := by
      have : ∀ m : List (R × R), (∀ p ∈ m, ‖p.2‖ ≤ 1) → ‖(m.map Prod.snd).prod‖ ≤ 1 := by
        intro m
        induction m with
        | nil => intro _; simp only [List.map_nil, List.prod_nil, norm_one, le_refl]
        | cons q m ihm =>
          intro hm
          simp only [List.map_cons, List.prod_cons]
          calc ‖q.2 * (m.map Prod.snd).prod‖ ≤ ‖q.2‖ * ‖(m.map Prod.snd).prod‖ := norm_mul_le _ _
            _ ≤ 1 * 1 := mul_le_mul (hm q (List.mem_cons_self ..))
                (ihm fun p hp => hm p (List.mem_cons_of_mem _ hp)) (norm_nonneg _) zero_le_one
            _ = 1 := one_mul 1
      exact this l fun p hp => (hl p hp).2
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    have e : a * (l.map Prod.fst).prod - b * (l.map Prod.snd).prod =
        a * ((l.map Prod.fst).prod - (l.map Prod.snd).prod) + (a - b) * (l.map Prod.snd).prod := by
      noncomm_ring
    rw [e]
    calc ‖a * ((l.map Prod.fst).prod - (l.map Prod.snd).prod) + (a - b) * (l.map Prod.snd).prod‖
        ≤ ‖a‖ * ‖(l.map Prod.fst).prod - (l.map Prod.snd).prod‖ + ‖a - b‖ * ‖(l.map Prod.snd).prod‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
      _ ≤ 1 * (l.map fun p => ‖p.1 - p.2‖).sum + ‖a - b‖ * 1 :=
          add_le_add (mul_le_mul hab.1 ih (norm_nonneg _) zero_le_one)
            (mul_le_mul_of_nonneg_left hP (norm_nonneg _))
      _ = ‖a - b‖ + (l.map fun p => ‖p.1 - p.2‖).sum := by ring

/-- With four bonds: `|V''(∂p) - Ṽ(∂p)| ≤ 4t` when each `‖V''(b) - Ṽ(b)‖ ≤ t`. -/
theorem plaquette_four (a b : Fin 4 → R) (ha : ∀ i, ‖a i‖ ≤ 1) (hb : ∀ i, ‖b i‖ ≤ 1) {t : ℝ}
    (ht : ∀ i, ‖a i - b i‖ ≤ t) : ‖a 0 * a 1 * a 2 * a 3 - b 0 * b 1 * b 2 * b 3‖ ≤ 4 * t := by
  have h := norm_list_prod_sub_le [(a 0, b 0), (a 1, b 1), (a 2, b 2), (a 3, b 3)]
    (by intro p hp; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl <;> exact ⟨ha _, hb _⟩)
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, List.sum_cons,
    List.sum_nil, add_zero] at h
  rw [show a 0 * a 1 * a 2 * a 3 = a 0 * (a 1 * (a 2 * a 3)) by noncomm_ring,
    show b 0 * b 1 * b 2 * b 3 = b 0 * (b 1 * (b 2 * b 3)) by noncomm_ring]
  linarith [ht 0, ht 1, ht 2, ht 3]

/-- `ε₁ + 4C_axL²ε₁ = (1 + 4C_axL²)ε₁`. -/
theorem plaquette_constant (Cax L ε : ℝ) : ε + 4 * (Cax * L ^ 2 * ε) = (1 + 4 * Cax * L ^ 2) * ε := by ring

/-- Six exchanges across at most `¼L²` plaquettes of at most `√Nε₁` each: `(3/2)√NL²ε₁`. -/
theorem transports_diff (N L ε : ℝ) : 6 * (1 / 4 * L ^ 2) * (Real.sqrt N * ε) = 3 / 2 * Real.sqrt N * L ^ 2 * ε := by
  ring

/-- `C'₃·2LC_axL²ε₁ ≤ C₁ε₁` and `(π/2)LC_axL²ε₁ < c'₄`. -/
theorem average_constant {C₃ L Cax ε c₄ : ℝ} (hC : 0 ≤ C₃ * L * Cax * L ^ 2 * ε)
    (hπ : Real.pi * L * (Cax * L ^ 2 * ε) < c₄) (hp : 0 ≤ L * (Cax * L ^ 2 * ε)) :
    C₃ * (2 * L * (Cax * L ^ 2 * ε)) ≤ 4 * L * C₃ * Cax * L ^ 2 * ε ∧
      Real.pi / 2 * L * (Cax * L ^ 2 * ε) < c₄ := by
  refine ⟨by nlinarith, ?_⟩
  have : Real.pi / 2 * L * (Cax * L ^ 2 * ε) ≤ Real.pi * L * (Cax * L ^ 2 * ε) := by
    have h := mul_le_mul_of_nonneg_right (by linarith [Real.pi_pos] : Real.pi / 2 ≤ Real.pi) hp
    linarith
  linarith

end DataExtensionArith
end CoreLean

end
