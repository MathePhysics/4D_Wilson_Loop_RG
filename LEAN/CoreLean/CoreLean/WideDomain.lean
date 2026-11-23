/-
**`lem:wide-domain`** of BALABAN_CORE.tex (`a021c13be348`), for the sequences of domains of `SequencesTorus.lean`. A
Dirichlet domain `Ω_D` is wide if it is the torus or contains the points within the `ℓ^∞`-distance `5a₁` of `Ω₁`
(`def:dirichlet-domain`(iii)). (i) A site outside `Ω_D`, or within `2a₀` of its complement, is a point of `Γ₀` and of
`𝐁`, and two sites at the `ℓ¹`-distance `a₀` are at a weighted distance of at most `1` (`wide_domain_i`).
(ii) If `RM ≥ 5L`, the points within `4a_j + 2a₀` of a point of `Γ_j`, `j ≥ 1`, lie in `Ω_D` (`wide_domain_ii`). The
proof is the core's; the weighted distance is bounded by `a₀⁻¹|z - z'|₁` (`wdist_le`).
-/
import CoreLean.LayerBonds

open Set

noncomputable section

namespace CoreLean
namespace Lattices
namespace SeqDom

variable (S : SeqDom)

/-- A wide Dirichlet domain. -/
def IsWide (ΩD : Set (Tor (ellT S.L S.mT))) : Prop :=
  ΩD = univ ∨ ∀ z, (∃ y ∈ S.Ω 1, dist z y ≤ 5 * sp S.L S.k 1) → z ∈ ΩD

lemma sp_mono_one : sp S.L S.k 0 ≤ sp S.L S.k 1 := by
  rw [sp_succ]
  have := sp_pos (k := S.k) S.Lpos 0
  have hL : (1 : ℝ) ≤ S.L := by exact_mod_cast (show 1 ≤ S.L by have := S.three_le_L; omega)
  nlinarith

lemma sp_ge_three (j : ℕ) (hj : 1 ≤ j) : 3 * sp S.L S.k 0 ≤ sp S.L S.k j := by
  have hL : (3 : ℝ) ≤ S.L := by exact_mod_cast S.three_le_L
  have h0 := sp_pos (k := S.k) S.Lpos 0
  have hmono : ∀ i, sp S.L S.k 1 ≤ sp S.L S.k (i + 1) := by
    intro i
    induction i with
    | zero => exact le_rfl
    | succ i ih =>
      rw [sp_succ S.L S.k (i + 1)]
      have := sp_pos (k := S.k) S.Lpos (i + 1)
      nlinarith
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  refine le_trans ?_ (hmono i)
  rw [sp_succ]; nlinarith

/-- **`lem:wide-domain`(i)**. -/
theorem wide_domain_i {ΩD : Set (Tor (ellT S.L S.mT))} (hD : S.IsWide ΩD) {x : Tor (ellT S.L S.mT)}
    (hx0 : x ∈ S.TL 0) (hx : x ∉ ΩD ∨ ∃ w, w ∉ ΩD ∧ dist x w ≤ 2 * sp S.L S.k 0) :
    x ∈ S.Γ 0 ∧ x ∈ (S.toContSeq).BF := by
  have hx1 : x ∉ S.Ω 1 := by
    intro hx1
    rcases hD with hD | hD
    · rcases hx with hx | ⟨w, hw, -⟩
      · exact hx (hD ▸ mem_univ x)
      · exact hw (hD ▸ mem_univ w)
    · rcases hx with hx | ⟨w, hw, hxw⟩
      · exact hx (hD x ⟨x, hx1, by rw [dist_self]; nlinarith [sp_pos (k := S.k) S.Lpos 1]⟩)
      · refine hw (hD w ⟨x, hx1, ?_⟩)
        have := S.sp_mono_one
        have h0 := sp_pos (k := S.k) S.Lpos 0
        rw [dist_comm]; linarith
  have hΓ : x ∈ S.Γ 0 := ⟨⟨by rw [S.Ω_zero]; exact mem_univ x, hx0⟩, hx1⟩
  exact ⟨hΓ, S.mem_BF.2 ⟨0, Nat.zero_le _, hΓ⟩⟩

/-- **`lem:wide-domain`(i)**, the weighted distance: points at the `ℓ¹`-distance at most `a₀` are at a weighted
distance of at most `1`. -/
theorem wide_domain_dist {x x' : Tor (ellT S.L S.mT)} (h : dist1 x x' ≤ sp S.L S.k 0) :
    wdist (S.toContSeq).D x x' ≤ 1 := by
  refine (wdist_le _ x x').trans ?_
  have ha : (S.toContSeq).D.a 0 = sp S.L S.k 0 := (S.sp_eq_aa 0).symm
  rw [ha]
  have h0 := sp_pos (k := S.k) S.Lpos 0
  rw [ENNReal.ofReal_le_one, inv_mul_le_iff₀ h0, mul_one]
  exact h

/-- **`lem:wide-domain`(ii)**. -/
theorem wide_domain_ii {ΩD : Set (Tor (ellT S.L S.mT))} (hD : S.IsWide ΩD)
    (hRM : 5 * S.L ≤ S.R * S.L ^ S.mM) {j : ℕ} (hj : 1 ≤ j) (hjk : j ≤ S.k) {y z : Tor (ellT S.L S.mT)}
    (hy : y ∈ S.Γ j) (hz : dist z y ≤ 4 * sp S.L S.k j + 2 * sp S.L S.k 0) : z ∈ ΩD := by
  rcases hD with hD | hD
  · rw [hD]; exact mem_univ z
  have hyΩ : y ∈ S.Ω j := hy.1.1
  have h3 := S.sp_ge_three j hj
  have h0 := sp_pos (k := S.k) S.Lpos 0
  rcases eq_or_lt_of_le hj with rfl | hj2
  · refine hD z ⟨y, hyΩ, ?_⟩
    linarith
  · -- `z` lies within `5a_j` of `Ω_j`, hence in `Ω_{j-1} ⊂ Ω₁ ⊂ Ω_D`
    have hz' : dist z y < 5 * sp S.L S.k j := by linarith
    have hzΩ := S.layer_bonds_i (c := 5) (by exact_mod_cast hRM) hjk hyΩ hz'
    have hz1 : z ∈ S.Ω 1 := S.Ω_anti (by omega) hzΩ
    exact hD z ⟨z, hz1, by rw [dist_self]; nlinarith [sp_pos (k := S.k) S.Lpos 1]⟩

end SeqDom
end Lattices
end CoreLean

end
