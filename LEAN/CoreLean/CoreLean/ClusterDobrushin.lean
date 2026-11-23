/-
The polymer sum and the criterion of Kotecký and Preiss in the inductive form of Dobrushin, for `lem:cluster-bounds` and
`thm:polymer-logarithm` of BALABAN_CORE.tex (`5bbe1bc62521`). For a finite set `Λ` of polymers with a symmetric relation
of incompatibility `≁` with `Z ≁ Z`, the polymer sum is `Ξ_Λ(z) = Σ_SΠ_{Z ∈ S}z(Z)` over the pairwise compatible subsets
`S ⊆ Λ` (the sequences of `eq:polymer-sum` with all pairs compatible have distinct entries). It satisfies
`Ξ_Λ = Ξ_{Λ∖Z} + z(Z)Ξ_{Λ∖N[Z]}`, `N[Z]` the polymers `≁ Z`. Under the condition `Σ_{Z' ≁ Z}w(Z')e^{a(Z')} ≤ a(Z)`
(`eq:kotecky-preiss`) and `|z| ≤ w`, `Ξ_Λ(z) ≠ 0` and `|Ξ_{Λ∖Z}(z)| ≤ e^{c(Z)}|Ξ_Λ(z)|` with `c = we^a`.
-/
import Mathlib

open Finset

noncomputable section

namespace CoreLean
namespace Cluster

open Classical

variable {P : Type*}

/-- The pairwise compatible sets. -/
def Compat (inc : P → P → Prop) (S : Finset P) : Prop := ∀ Z ∈ S, ∀ Z' ∈ S, Z ≠ Z' → ¬inc Z Z'

/-- The polymer sum `Ξ_Λ(z) = Σ_SΠ_{Z ∈ S}z(Z)` over the pairwise compatible `S ⊆ Λ`. -/
def Xi (inc : P → P → Prop) (Λ : Finset P) (z : P → ℂ) : ℂ :=
  ∑ S ∈ Λ.powerset.filter (Compat inc), ∏ Z ∈ S, z Z

/-- The polymers of `Λ` compatible with `Z`: `Λ ∖ N[Z]`. -/
def compatPart (inc : P → P → Prop) (Λ : Finset P) (Z : P) : Finset P := Λ.filter fun Z' => ¬inc Z Z'

/-- **The recursion** `Ξ_Λ = Ξ_{Λ∖Z} + z(Z)Ξ_{Λ∖N[Z]}` for `Z ∈ Λ`, `Z ≁ Z`. -/
lemma Xi_rec (inc : P → P → Prop) (hrefl : ∀ Z, inc Z Z) (hsymm : ∀ Z Z', inc Z Z' → inc Z' Z)
    {Λ : Finset P} {Z : P} (hZ : Z ∈ Λ) (z : P → ℂ) :
    Xi inc Λ z = Xi inc (Λ.erase Z) z + z Z * Xi inc (compatPart inc Λ Z) z := by
  unfold Xi
  conv_lhs => rw [Finset.sum_filter, ← Finset.insert_erase hZ, Finset.sum_powerset_insert (Finset.notMem_erase Z Λ)]
  rw [Finset.sum_filter]
  congr 1
  rw [Finset.mul_sum, Finset.sum_filter]
  -- the subsets containing `Z`: `insert Z S'` with `S' ⊆ Λ ∖ N[Z]` compatible
  have hsub : (compatPart inc Λ Z).powerset ⊆ (Λ.erase Z).powerset := by
    intro S hS
    rw [Finset.mem_powerset] at hS ⊢
    intro x hx
    have := hS hx
    simp only [compatPart, Finset.mem_filter] at this
    exact Finset.mem_erase.2 ⟨fun h => this.2 (h ▸ hrefl Z), this.1⟩
  symm
  rw [← Finset.sum_subset hsub]
  · refine Finset.sum_congr rfl fun S hS => ?_
    have hS' := Finset.mem_powerset.1 hS
    have hZS : Z ∉ S := fun h => by
      have := hS' h; simp only [compatPart, Finset.mem_filter] at this; exact this.2 (hrefl Z)
    have hiff : Compat inc (insert Z S) ↔ Compat inc S := by
      constructor
      · intro h x hx y hy hxy; exact h x (Finset.mem_insert_of_mem hx) y (Finset.mem_insert_of_mem hy) hxy
      · intro h x hx y hy hxy
        rcases Finset.mem_insert.1 hx with hxZ | hx <;> rcases Finset.mem_insert.1 hy with hyZ | hy
        · exact absurd (hxZ.trans hyZ.symm) hxy
        · have := hS' hy; simp only [compatPart, Finset.mem_filter] at this; rw [hxZ]; exact this.2
        · have := hS' hx; simp only [compatPart, Finset.mem_filter] at this
          rw [hyZ]; exact fun h' => this.2 (hsymm _ _ h')
        · exact h x hx y hy hxy
    rw [Finset.prod_insert hZS]
    by_cases hc : Compat inc S
    · rw [if_pos hc, if_pos (hiff.2 hc)]
    · rw [if_neg hc, if_neg (fun h => hc (hiff.1 h))]
  · intro S hS hnS
    have hS' := Finset.mem_powerset.1 hS
    have hZS : Z ∉ S := fun h => Finset.notMem_erase Z Λ (hS' h)
    -- `insert Z S` is not compatible: some element of `S` is incompatible with `Z`
    have : ¬Compat inc (insert Z S) := by
      intro hc
      apply hnS
      rw [Finset.mem_powerset]
      intro x hx
      simp only [compatPart, Finset.mem_filter]
      refine ⟨Finset.mem_of_mem_erase (hS' hx), fun h => ?_⟩
      exact hc Z (Finset.mem_insert_self Z S) x (Finset.mem_insert_of_mem hx)
        (fun he => hZS (he ▸ hx)) h
    rw [if_neg this]

lemma Xi_empty (inc : P → P → Prop) (z : P → ℂ) : Xi inc ∅ z = 1 := by
  unfold Xi
  have hc : Compat inc (∅ : Finset P) := fun _ h => absurd h (Finset.notMem_empty _)
  rw [Finset.powerset_empty, Finset.filter_singleton, if_pos hc]
  simp

/-- `eq:kotecky-preiss` on `Λ₀`: `Σ_{Z' ∈ Λ₀, Z' ≁ Z}w(Z')e^{a(Z')} ≤ a(Z)` for `Z ∈ Λ₀`. -/
def KP (inc : P → P → Prop) (Λ0 : Finset P) (w a : P → ℝ) : Prop :=
  ∀ Z ∈ Λ0, ∑ Z' ∈ Λ0.filter (fun Z' => inc Z' Z), w Z' * Real.exp (a Z') ≤ a Z

lemma compatPart_eq (inc : P → P → Prop) (hrefl : ∀ Z, inc Z Z) (hsymm : ∀ Z Z', inc Z Z' → inc Z' Z)
    (Λ : Finset P) (Z : P) :
    compatPart inc Λ Z = Λ.erase Z \ (Λ.erase Z).filter (fun Z' => inc Z' Z) := by
  ext x
  simp only [compatPart, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_erase]
  constructor
  · rintro ⟨hx, hn⟩
    exact ⟨⟨fun h => hn (h ▸ hrefl Z), hx⟩, fun ⟨_, h⟩ => hn (hsymm _ _ h)⟩
  · rintro ⟨⟨hne, hx⟩, hn⟩
    exact ⟨hx, fun h => hn ⟨⟨hne, hx⟩, hsymm _ _ h⟩⟩

/-- **The criterion of Kotecký and Preiss, in the inductive form of Dobrushin**: under `eq:kotecky-preiss` on `Λ₀` and
`|z| ≤ w` on `Λ₀`, every `Λ ⊆ Λ₀` has `Ξ_Λ(z) ≠ 0` and `|Ξ_{Λ∖Z}(z)| ≤ e^{w(Z)e^{a(Z)}}|Ξ_Λ(z)|` for `Z ∈ Λ`. -/
theorem dobrushin (inc : P → P → Prop) (hrefl : ∀ Z, inc Z Z) (hsymm : ∀ Z Z', inc Z Z' → inc Z' Z)
    (Λ0 : Finset P) (w a : P → ℝ) (hw : ∀ Z, 0 ≤ w Z) (hKP : KP inc Λ0 w a) (z : P → ℂ)
    (hz : ∀ Z ∈ Λ0, ‖z Z‖ ≤ w Z) :
    ∀ n, ∀ Λ ⊆ Λ0, Λ.card = n → Xi inc Λ z ≠ 0 ∧
      ∀ Z ∈ Λ, ‖Xi inc (Λ.erase Z) z‖ ≤ Real.exp (w Z * Real.exp (a Z)) * ‖Xi inc Λ z‖ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro Λ hΛ hn
  set c : P → ℝ := fun Z => w Z * Real.exp (a Z) with hc
  have hc0 : ∀ Z, 0 ≤ c Z := fun Z => mul_nonneg (hw Z) (Real.exp_pos _).le
  -- removing a set `A ⊆ B` from a smaller set `B` multiplies `|Ξ|` by at most `e^{Σ_Ac}`
  have tele : ∀ B ⊆ Λ0, B.card < n → ∀ A ⊆ B,
      ‖Xi inc (B \ A) z‖ ≤ Real.exp (∑ x ∈ A, c x) * ‖Xi inc B z‖ := by
    intro B hB hBn A
    induction A using Finset.induction_on with
    | empty => intro _; simp
    | insert x A' hxA' ihA =>
      intro hAB
      have hA'B : A' ⊆ B := (Finset.subset_insert x A').trans hAB
      have hxB : x ∈ B := hAB (Finset.mem_insert_self x A')
      have hsub : B \ insert x A' = (B \ A').erase x := by
        ext y; simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]; tauto
      have hcard : (B \ A').card < n := lt_of_le_of_lt (Finset.card_le_card Finset.sdiff_subset) hBn
      have hstep := (ih _ hcard (B \ A') (Finset.sdiff_subset.trans hB) rfl).2 x
        (Finset.mem_sdiff.2 ⟨hxB, hxA'⟩)
      rw [hsub, Finset.sum_insert hxA', Real.exp_add, mul_assoc]
      exact hstep.trans (mul_le_mul_of_nonneg_left (ihA hA'B) (Real.exp_pos _).le)
  -- the ratio bound at every `Z ∈ Λ`
  have hratio : ∀ Z ∈ Λ, ‖Xi inc (Λ.erase Z) z‖ ≤ Real.exp (c Z) * ‖Xi inc Λ z‖ ∧
      0 < ‖Xi inc (Λ.erase Z) z‖ := by
    intro Z hZ
    set B := Λ.erase Z with hB
    set A := B.filter (fun Z' => inc Z' Z) with hA
    have hBn : B.card < n := by rw [hB, Finset.card_erase_of_mem hZ, ← hn]; have := Finset.card_pos.2 ⟨Z, hZ⟩; omega
    have hB0 : B ⊆ Λ0 := (Finset.erase_subset Z Λ).trans hΛ
    have hXB := (ih _ hBn B hB0 rfl).1
    have htel := tele B hB0 hBn A (Finset.filter_subset _ _)
    -- `Σ_Ac ≤ a(Z) - c(Z)`
    have hsumA : ∑ x ∈ A, c x ≤ a Z - c Z := by
      have hZf : Z ∈ Λ0.filter (fun Z' => inc Z' Z) := Finset.mem_filter.2 ⟨hΛ hZ, hrefl Z⟩
      have hAsub : A ⊆ (Λ0.filter (fun Z' => inc Z' Z)).erase Z := by
        intro x hx
        simp only [hA, hB, Finset.mem_filter, Finset.mem_erase] at hx ⊢
        exact ⟨hx.1.1, hΛ hx.1.2, hx.2⟩
      calc ∑ x ∈ A, c x ≤ ∑ x ∈ (Λ0.filter (fun Z' => inc Z' Z)).erase Z, c x :=
            Finset.sum_le_sum_of_subset_of_nonneg hAsub fun x _ _ => hc0 x
        _ = ∑ x ∈ Λ0.filter (fun Z' => inc Z' Z), c x - c Z := Finset.sum_erase_eq_sub hZf
        _ ≤ a Z - c Z := by linarith [hKP Z (hΛ hZ)]
    have hrec := Xi_rec inc hrefl hsymm hZ z
    rw [compatPart_eq inc hrefl hsymm Λ Z] at hrec
    -- `|Ξ_Λ| ≥ |Ξ_B|(1 - c(Z)e^{-c(Z)}) ≥ e^{-c(Z)}|Ξ_B|`
    have hzZ := hz Z (hΛ hZ)
    have hXBpos : 0 < ‖Xi inc B z‖ := norm_pos_iff.2 hXB
    have h1 : ‖z Z * Xi inc (B \ A) z‖ ≤ c Z * Real.exp (-c Z) * ‖Xi inc B z‖ := by
      rw [norm_mul]
      calc ‖z Z‖ * ‖Xi inc (B \ A) z‖ ≤ w Z * (Real.exp (∑ x ∈ A, c x) * ‖Xi inc B z‖) :=
            mul_le_mul hzZ htel (norm_nonneg _) (hw Z)
        _ ≤ w Z * (Real.exp (a Z - c Z) * ‖Xi inc B z‖) := by
            gcongr
            exact hw Z
        _ = c Z * Real.exp (-c Z) * ‖Xi inc B z‖ := by
            rw [hc, sub_eq_add_neg, Real.exp_add]; ring
    have h2 : Real.exp (-c Z) * ‖Xi inc B z‖ ≤ ‖Xi inc Λ z‖ := by
      have hge : ‖Xi inc B z‖ - ‖z Z * Xi inc (B \ A) z‖ ≤ ‖Xi inc Λ z‖ := by
        rw [hrec]
        have := norm_sub_le (Xi inc B z + z Z * Xi inc (B \ A) z) (z Z * Xi inc (B \ A) z)
        rw [add_sub_cancel_right] at this
        linarith
      have hexp : Real.exp (-c Z) ≤ 1 - c Z * Real.exp (-c Z) := by
        have := Real.add_one_le_exp (c Z)
        have hpos := Real.exp_pos (-c Z)
        have e : Real.exp (c Z) * Real.exp (-c Z) = 1 := by rw [← Real.exp_add]; simp
        nlinarith
      nlinarith
    refine ⟨?_, hXBpos⟩
    calc ‖Xi inc B z‖ = Real.exp (c Z) * (Real.exp (-c Z) * ‖Xi inc B z‖) := by
          rw [← mul_assoc, ← Real.exp_add]; simp
      _ ≤ Real.exp (c Z) * ‖Xi inc Λ z‖ := mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
  refine ⟨?_, fun Z hZ => (hratio Z hZ).1⟩
  rcases Λ.eq_empty_or_nonempty with hE | ⟨Z, hZ⟩
  · rw [hE, Xi_empty]; exact one_ne_zero
  · obtain ⟨h1, h2⟩ := hratio Z hZ
    intro h0
    rw [h0, norm_zero, mul_zero] at h1
    linarith

end Cluster
end CoreLean

end
