/-
`lem:unit-form-trivial` of BALABAN_CORE.tex (`a021c13be348`), the analytic steps of its proof in abstract form.

* (i), `eq:circulation-step`: `(∂𝔩W)(p') = L^{-4}Σ_{x ∈ B(y)}Σ_{p ⊂ □_x}(∂W)(p)` is a sum of `L^4·L^2 = L^6` terms, and by
  Cauchy–Schwarz `|L^{-4}Σ w|² ≤ L^{-2}Σ|w|²` (`circulation_step`); and since every plaquette `p` of `T^{(m-1)}` enters the
  sums of exactly `L²` plaquettes `p'` of `T^{(m)}` (through the squares `□_x` and the blocks), the energy does not
  increase, `Σ_{p'}|(∂W_m)(p')|² ≤ Σ_p|(∂W_{m-1})(p)|²` (`energy_step`, by the fibres of the map to `p`).
* (ii): finitely many positive definite quadratic forms on a finite-dimensional space have a common lower bound
  `q_c(B) ≥ γ'‖B‖²`, `γ' > 0` (`uniform_lower_bound`, by the minimum over the unit sphere of each form).
* (iii): `γ'Σ_b ≤ Σ_c q_c ≤ 8(Σ_p + 𝐆^{(2)})` gives the bound with `γ_f = min{γ'/8, 1}` (`conclusion`).

The kernel argument of (ii) (`q_c(B) = 0` forces `B = 0`, through the closed paths in a box) is the hypothesis of
positive definiteness here.
-/
import Mathlib

open Finset Metric

noncomputable section

namespace CoreLean
namespace UnitFormTrivial

/-- **`eq:circulation-step`**: Cauchy–Schwarz over the `L^6` terms. -/
theorem circulation_step {E ι : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] {L : ℕ} (hL : 0 < L)
    (s : Finset ι) (hs : s.card = L ^ 6) (w : ι → E) :
    ‖(1 / (L : ℝ) ^ 4) • ∑ i ∈ s, w i‖ ^ 2 ≤ 1 / (L : ℝ) ^ 2 * ∑ i ∈ s, ‖w i‖ ^ 2 := by
  have hL' : (0 : ℝ) < L := Nat.cast_pos.2 hL
  have h1 : ‖∑ i ∈ s, w i‖ ≤ ∑ i ∈ s, ‖w i‖ := norm_sum_le _ _
  have h2 : (∑ i ∈ s, ‖w i‖) ^ 2 ≤ s.card * ∑ i ∈ s, ‖w i‖ ^ 2 := sq_sum_le_card_mul_sum_sq
  rw [norm_smul, Real.norm_of_nonneg (by positivity), mul_pow]
  have h3 : ‖∑ i ∈ s, w i‖ ^ 2 ≤ (L : ℝ) ^ 6 * ∑ i ∈ s, ‖w i‖ ^ 2 := by
    calc ‖∑ i ∈ s, w i‖ ^ 2 ≤ (∑ i ∈ s, ‖w i‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ s.card * ∑ i ∈ s, ‖w i‖ ^ 2 := h2
      _ = (L : ℝ) ^ 6 * ∑ i ∈ s, ‖w i‖ ^ 2 := by rw [hs]; push_cast; ring
  calc (1 / (L : ℝ) ^ 4) ^ 2 * ‖∑ i ∈ s, w i‖ ^ 2 ≤ (1 / (L : ℝ) ^ 4) ^ 2 * ((L : ℝ) ^ 6 * ∑ i ∈ s, ‖w i‖ ^ 2) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = 1 / (L : ℝ) ^ 2 * ∑ i ∈ s, ‖w i‖ ^ 2 := by field_simp

/-- **The energy does not increase**: every plaquette `p` is reached from exactly `L²` pairs `(p', (x, p))`. -/
theorem energy_step {α β γ : Type*} [DecidableEq β] {L : ℕ} (hL : 0 < L) (P' : Finset α) (P : Finset β)
    (T : α → Finset γ) (π : γ → β) (hmap : ∀ x ∈ P'.sigma T, π x.2 ∈ P)
    (hfib : ∀ p ∈ P, ((P'.sigma T).filter fun x => π x.2 = p).card = L ^ 2)
    (c : α → ℝ) (a : β → ℝ) (ha : ∀ p, 0 ≤ a p)
    (hc : ∀ p' ∈ P', c p' ≤ 1 / (L : ℝ) ^ 2 * ∑ t ∈ T p', a (π t)) :
    ∑ p' ∈ P', c p' ≤ ∑ p ∈ P, a p := by
  have hL' : (0 : ℝ) < L := Nat.cast_pos.2 hL
  calc ∑ p' ∈ P', c p' ≤ ∑ p' ∈ P', 1 / (L : ℝ) ^ 2 * ∑ t ∈ T p', a (π t) := Finset.sum_le_sum hc
    _ = 1 / (L : ℝ) ^ 2 * ∑ x ∈ P'.sigma T, a (π x.2) := by rw [← Finset.mul_sum, Finset.sum_sigma]
    _ = 1 / (L : ℝ) ^ 2 * ∑ p ∈ P, ∑ x ∈ (P'.sigma T).filter (fun x => π x.2 = p), a (π x.2) := by
        rw [Finset.sum_fiberwise_of_maps_to hmap]
    _ = 1 / (L : ℝ) ^ 2 * ∑ p ∈ P, (L : ℝ) ^ 2 * a p := by
        congr 1
        refine Finset.sum_congr rfl fun p hp => ?_
        rw [Finset.sum_congr rfl (g := fun _ => a p) fun x hx => by rw [(Finset.mem_filter.1 hx).2],
          Finset.sum_const, hfib p hp, nsmul_eq_mul]
        push_cast; ring
    _ = ∑ p ∈ P, a p := by rw [← Finset.mul_sum]; field_simp

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- One positive definite form has a lower bound `γ‖B‖²`, `γ > 0`. -/
lemma lower_bound (q : E →L[ℝ] E →L[ℝ] ℝ) (hq : ∀ B, B ≠ 0 → 0 < q B B) :
    ∃ γ > 0, ∀ B, γ * ‖B‖ ^ 2 ≤ q B B := by
  by_cases hE : ∃ B : E, B ≠ 0
  · obtain ⟨B₀, hB₀⟩ := hE
    have hS : IsCompact (sphere (0 : E) 1) := isCompact_sphere 0 1
    have hSne : (sphere (0 : E) 1).Nonempty := ⟨‖B₀‖⁻¹ • B₀, by
      simp [norm_smul, inv_mul_cancel₀ (norm_ne_zero_iff.2 hB₀)]⟩
    have hc : Continuous fun B : E => q B B := (q.continuous.clm_apply continuous_id).comp continuous_id |>.congr
      fun _ => rfl
    obtain ⟨u, hu, hmin⟩ := hS.exists_isMinOn hSne hc.continuousOn
    have hu0 : u ≠ 0 := by rintro rfl; simp at hu
    refine ⟨q u u, hq u hu0, fun B => ?_⟩
    rcases eq_or_ne B 0 with rfl | hB
    · simp
    · have hn : ‖B‖ ≠ 0 := norm_ne_zero_iff.2 hB
      have hv : ‖B‖⁻¹ • B ∈ sphere (0 : E) 1 := by simp [norm_smul, inv_mul_cancel₀ hn]
      have h1 := hmin hv
      simp only [Set.mem_setOf_eq] at h1
      have e : q B B = ‖B‖ ^ 2 * q (‖B‖⁻¹ • B) (‖B‖⁻¹ • B) := by
        simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
        field_simp
      rw [e, mul_comm]
      exact mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
  · push_neg at hE
    refine ⟨1, one_pos, fun B => ?_⟩
    rw [hE B]; simp

/-- **(ii)**: finitely many positive definite forms have a common lower bound. -/
theorem uniform_lower_bound {ι : Type*} [Fintype ι] (q : ι → E →L[ℝ] E →L[ℝ] ℝ)
    (hq : ∀ i B, B ≠ 0 → 0 < q i B B) : ∃ γ > 0, ∀ i B, γ * ‖B‖ ^ 2 ≤ q i B B := by
  choose γ hγ hb using fun i => lower_bound (q i) (hq i)
  classical
  set S : Finset ℝ := insert 1 (Finset.univ.image γ)
  have hSne : S.Nonempty := Finset.insert_nonempty _ _
  refine ⟨S.min' hSne, ?_, fun i B => ?_⟩
  · show 0 < S.min' hSne
    rw [Finset.lt_min'_iff]
    intro y hy
    rcases Finset.mem_insert.1 hy with rfl | hy
    · exact one_pos
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hy
      exact hγ i
  · have : S.min' hSne ≤ γ i := Finset.min'_le _ _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (by simp)))
    exact (mul_le_mul_of_nonneg_right this (sq_nonneg _)).trans (hb i B)

/-- **(iii)**, the conclusion with `γ_f = min{γ'/8, 1}`. -/
theorem conclusion {γ' N Q X : ℝ} (hγ' : 0 < γ') (hN : 0 ≤ N) (h1 : γ' * N ≤ Q) (h2 : Q ≤ 8 * X) :
    min (γ' / 8) 1 * N ≤ X ∧ 0 < min (γ' / 8) 1 ∧ min (γ' / 8) 1 ≤ 1 := by
  refine ⟨?_, lt_min (by positivity) one_pos, min_le_right _ _⟩
  calc min (γ' / 8) 1 * N ≤ γ' / 8 * N := mul_le_mul_of_nonneg_right (min_le_left _ _) hN
    _ ≤ X := by linarith

end UnitFormTrivial
end CoreLean

end
