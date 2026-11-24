/-
`lem:sf-components` of BALABAN_CORE.tex (`aaaa938bb57d`), the step "A bond of the layer at each block", on the sequences
of domains of `SequencesTorus.lean`: for `y ∈ Γ_j` and a direction `μ`, one of the bonds `(y, y + a_je_μ)` and
`(y - a_je_μ, y)` of `T^{(j)}` is a bond of the layer `Γ_j`.

* `two_cells_1d`: on the circle `ℝ/pℤ`, `p = Ms`, `M ≥ 2`, if `t - a` and `t + a` lie in closed intervals of length `s`
  centred at points of `sℤ` and `2a < s`, then so does `t` (in one of the two).
* `not_both_near`: the four-dimensional statement for the cubes of `Ω_{j+1}`: `y ∉ Ω_{j+1}` excludes
  `y ± a_je_μ ∈ Ω_{j+1}`.
* `exists_layer_bond`: the step.
-/
import CoreLean.LayerBonds2

open Set

noncomputable section

namespace CoreLean
namespace Lattices

variable {p : ℝ}

/-- **Two cells of a line**: if `t ∓ a` lie in the cells of `c₁`, `c₂` of side `s > 2a`, then `t` lies in one of them. -/
lemma two_cells_1d {s a : ℝ} (hs : 0 < s) (ha : 0 < a) (has : 2 * a < s) {M : ℕ} (hM : 2 ≤ M) (hp : p = M * s)
    {t c1 c2 : AddCircle p} (hc1 : c1 ∈ LatC p s) (hc2 : c2 ∈ LatC p s)
    (h1 : ‖t - (a : AddCircle p) - c1‖ ≤ s / 2) (h2 : ‖t + (a : AddCircle p) - c2‖ ≤ s / 2) :
    ‖t - c1‖ ≤ s / 2 ∨ ‖t - c2‖ ≤ s / 2 := by
  by_contra H
  push_neg at H
  obtain ⟨H1, H2⟩ := H
  have hM2 : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hp0 : 0 < p := by rw [hp]; nlinarith
  have hp2 : 2 * s ≤ p := by rw [hp]; nlinarith
  obtain ⟨u, hu, hun⟩ := exists_rep (t - c1)
  have hu_le : |u| ≤ p / 2 := by
    rw [hun]; have := AddCircle.norm_le_half_period p (x := t - c1) hp0.ne'; rwa [abs_of_pos hp0] at this
  have hu_gt : s / 2 < |u| := by rw [hun]; exact H1
  -- `|u - a| ≤ s/2`
  have e1 : t - (a : AddCircle p) - c1 = ((u - a : ℝ) : AddCircle p) := by
    rw [sub_right_comm, hu, AddCircle.coe_sub]
  rw [e1, AddCircle.norm_eq p] at h1
  set m := round (p⁻¹ * (u - a))
  have hm0 : m = 0 := by
    by_contra hm
    have hm1 : (1 : ℝ) ≤ |(m : ℝ)| := by
      have : (1 : ℤ) ≤ |m| := Int.one_le_abs hm
      exact_mod_cast this
    have hmp : p ≤ |(m : ℝ) * p| := by rw [abs_mul, abs_of_pos hp0]; nlinarith
    have := abs_sub_abs_le_abs_sub ((m : ℝ) * p) (u - a)
    have hua : |u - a| ≤ p / 2 + a := by
      calc |u - a| ≤ |u| + |a| := abs_sub _ _
        _ = |u| + a := by rw [abs_of_pos ha]
        _ ≤ p / 2 + a := by linarith
    rw [abs_sub_comm] at h1
    have : |(m : ℝ) * p - (u - a)| ≥ p / 2 - a := by linarith
    linarith
  rw [hm0] at h1
  simp only [Int.cast_zero, zero_mul, sub_zero] at h1
  -- `s/2 < u ≤ s/2 + a`
  have hu_pos : s / 2 < u := by
    rcases le_or_gt 0 u with h | h
    · rw [abs_of_nonneg h] at hu_gt; exact hu_gt
    · rw [abs_of_neg h] at hu_gt
      have := (abs_le.1 h1).1
      linarith
  have hu_up : u ≤ s / 2 + a := by have := (abs_le.1 h1).2; linarith
  -- `c₂ - c₁ = rs`
  obtain ⟨r, hr⟩ := latC_sub hc2 hc1
  have e2 : t + (a : AddCircle p) - c2 = ((u + a - r * s : ℝ) : AddCircle p) := by
    have : c2 = c1 + (((r : ℝ) * s : ℝ) : AddCircle p) := by rw [← hr]; abel
    rw [this, AddCircle.coe_sub, AddCircle.coe_add, ← hu]; abel
  rw [e2, AddCircle.norm_eq p] at h2
  set m' := round (p⁻¹ * (u + a - r * s))
  set R : ℤ := r + m' * M
  have eR : u + a - r * s - m' * p = u + a - R * s := by simp only [R, hp]; push_cast; ring
  rw [eR] at h2
  have hR1 : (0 : ℝ) < R * s := by have := (abs_le.1 h2).2; linarith
  have hR2 : (R : ℝ) * s < 2 * s := by have := (abs_le.1 h2).1; linarith
  have hR : R = 1 := by
    have h0 : (0 : ℝ) < R := by by_contra hc; push_neg at hc; nlinarith
    have h2' : (R : ℝ) < 2 := by nlinarith
    have : (0 : ℤ) < R := by exact_mod_cast h0
    have : R < 2 := by exact_mod_cast h2'
    omega
  -- `t - c₂ = u - s`
  have e3 : t - c2 = ((u - s : ℝ) : AddCircle p) := by
    have hc2' : c2 = c1 + (((r : ℝ) * s : ℝ) : AddCircle p) := by rw [← hr]; abel
    have hrs : (((r : ℝ) * s : ℝ) : AddCircle p) = ((s : ℝ) : AddCircle p) := by
      have : (r : ℝ) * s = s - (m' : ℝ) * p := by
        have : ((R : ℤ) : ℝ) = 1 := by exact_mod_cast hR
        simp only [R] at this; push_cast at this; rw [hp]; nlinarith
      rw [this, AddCircle.coe_sub, coe_int_mul_period, sub_zero]
    rw [hc2', hrs, AddCircle.coe_sub, ← hu]; abel
  have : ‖t - c2‖ ≤ s / 2 := by
    rw [e3]
    refine (norm_coe_le _).trans ?_
    rw [abs_le]; constructor <;> linarith
  linarith

namespace SeqDom

variable (S : SeqDom)

/-- The step `a_je_μ` of `T^{(j)}`. -/
def shj (j : ℕ) (μ : Fin 4) : Tor (ellT S.L S.mT) := Pi.single μ ((sp S.L S.k j : ℝ) : AddCircle (ellT S.L S.mT))

/-- A point which lies in a cell after the shift by `v` in the direction `μ` only: the other coordinates. -/
lemma coord_cell_of_shift {side : ℝ} {y c v : Tor (ellT S.L S.mT)} {μ : Fin 4} (hv : ∀ ν, ν ≠ μ → v ν = 0)
    (h : ‖y + v - c‖ ≤ side / 2) (hμ : ‖y μ - c μ‖ ≤ side / 2) : ‖y - c‖ ≤ side / 2 := by
  have hs : 0 ≤ side / 2 := (norm_nonneg _).trans h
  refine (pi_norm_le_iff_of_nonneg hs).2 fun ν => ?_
  by_cases hν : ν = μ
  · subst hν; exact hμ
  · have : (y - c) ν = (y + v - c) ν := by simp [hv ν hν]
    rw [this]; exact (norm_le_pi_norm _ ν).trans h

/-- **Not both neighbours in `Ω_{j+1}`**: for `y ∉ Ω_{j+1}`, the points `y ± a_je_μ` are not both in `Ω_{j+1}`, the cubes of
`Ω_{j+1}` having the side `Ma_{j+1} > 2a_j`. -/
theorem not_both_near {j : ℕ} (hjk : j + 1 ≤ S.k) {y : Tor (ellT S.L S.mT)} (hy : y ∉ S.Ω (j + 1)) (μ : Fin 4) :
    ¬ (y + S.shj j μ ∈ S.Ω (j + 1) ∧ y - S.shj j μ ∈ S.Ω (j + 1)) := by
  rintro ⟨h2, h1⟩
  obtain ⟨C, hC, hΩ⟩ := S.cubes (j + 1) (by omega) hjk
  set side := ((S.L ^ S.mM : ℕ) : ℝ) * sp S.L S.k (j + 1) with hside
  rw [hΩ] at h1 h2 hy
  obtain ⟨c1, hc1, hy1⟩ := mem_iUnion₂.1 h1
  obtain ⟨c2, hc2, hy2⟩ := mem_iUnion₂.1 h2
  rw [mem_cell] at hy1 hy2
  have hL : (3 : ℝ) ≤ S.L := by exact_mod_cast S.three_le_L
  have hsp := sp_pos (k := S.k) S.Lpos j
  have hsp1 : sp S.L S.k (j + 1) = S.L * sp S.L S.k j := by
    have := sp_sub (L := S.L) (k := S.k) (j + 1) 1 (by omega)
    simpa using this
  have hLM : (1 : ℝ) ≤ ((S.L ^ S.mM : ℕ) : ℝ) := by exact_mod_cast Nat.one_le_pow _ _ S.Lpos
  have has : 2 * sp S.L S.k j < side := by
    rw [hside, hsp1]
    have h3 : 3 * sp S.L S.k j ≤ S.L * sp S.L S.k j := by nlinarith
    have h4 : (S.L : ℝ) * sp S.L S.k j ≤ ((S.L ^ S.mM : ℕ) : ℝ) * (S.L * sp S.L S.k j) :=
      le_mul_of_one_le_left (by positivity) hLM
    linarith
  -- the period is a multiple `M'` of the side, `M' ≥ 2`
  set e := S.mT + (S.k - (j + 1)) - S.mM
  have hper : ellT S.L S.mT = ((2 * S.L ^ e : ℕ) : ℝ) * side := by
    rw [ellT_eq S.Lpos hjk, hside, ← mul_assoc]
    congr 1
    have he : S.mT + (S.k - (j + 1)) = e + S.mM := by have := S.mM_le; omega
    rw [he, pow_add]; push_cast; ring
  have hM' : 2 ≤ 2 * S.L ^ e := by have := Nat.one_le_pow e S.L S.Lpos; omega
  have hsv : ∀ ν, ν ≠ μ → S.shj j μ ν = 0 := fun ν hν => by simp [shj, Pi.single_eq_of_ne hν]
  have hsv' : ∀ ν, ν ≠ μ → (-S.shj j μ) ν = 0 := fun ν hν => by simp [hsv ν hν]
  -- the coordinate `μ`
  have e1 : (y - S.shj j μ - c1) μ = y μ - ((sp S.L S.k j : ℝ) : AddCircle (ellT S.L S.mT)) - c1 μ := by
    simp [shj]
  have e2 : (y + S.shj j μ - c2) μ = y μ + ((sp S.L S.k j : ℝ) : AddCircle (ellT S.L S.mT)) - c2 μ := by
    simp [shj]
  have hm1 : ‖y μ - ((sp S.L S.k j : ℝ) : AddCircle (ellT S.L S.mT)) - c1 μ‖ ≤ side / 2 := by
    rw [← e1]; exact (norm_le_pi_norm _ μ).trans hy1
  have hm2 : ‖y μ + ((sp S.L S.k j : ℝ) : AddCircle (ellT S.L S.mT)) - c2 μ‖ ≤ side / 2 := by
    rw [← e2]; exact (norm_le_pi_norm _ μ).trans hy2
  have hside0 : 0 < side := by rw [hside]; exact mul_pos (by positivity) (sp_pos S.Lpos _)
  rcases two_cells_1d hside0 hsp has hM' hper (hC hc1 μ) (hC hc2 μ) hm1 hm2 with h | h
  · apply hy
    refine mem_iUnion₂.2 ⟨c1, hc1, ?_⟩
    rw [mem_cell]
    refine S.coord_cell_of_shift (v := -S.shj j μ) hsv' ?_ h
    rw [← sub_eq_add_neg]; exact hy1
  · apply hy
    refine mem_iUnion₂.2 ⟨c2, hc2, ?_⟩
    rw [mem_cell]
    exact S.coord_cell_of_shift hsv hy2 h

/-- **A bond of the layer at each block**: for `y ∈ Γ_j` one of `(y, μ)` and `(y - a_je_μ, μ)` is a bond of `Γ_j`. -/
theorem exists_layer_bond {j : ℕ} (hjk : j ≤ S.k) {y : Tor (ellT S.L S.mT)} (hyT : y ∈ S.TL j) (hyΩ : y ∈ S.Ω j)
    (hy : y ∉ S.Ω (j + 1)) (μ : Fin 4) :
    S.IsLayerBond j y μ ∨ S.IsLayerBond j (y - S.shj j μ) μ := by
  have hbend : ∀ z, S.bend j z μ = z + S.shj j μ := fun z => rfl
  have hT' : y - S.shj j μ ∈ S.TL j := by
    intro ν
    obtain ⟨r, hr⟩ := hyT ν
    by_cases hν : ν = μ
    · subst hν
      refine ⟨r - 1, ?_⟩
      simp only [shj, Pi.sub_apply, Pi.single_eq_same, hr, ← AddCircle.coe_sub]
      congr 1; push_cast; ring
    · refine ⟨r, ?_⟩
      simp only [shj, Pi.sub_apply, Pi.single_eq_of_ne hν, sub_zero, hr]
  rcases Nat.lt_or_ge j S.k with hlt | hge
  · by_cases h1 : y + S.shj j μ ∈ S.Ω (j + 1)
    · right
      have h2 : y - S.shj j μ ∉ S.Ω (j + 1) := fun h2 => S.not_both_near (by omega) hy μ ⟨h1, h2⟩
      refine ⟨hT', Or.inr ?_, h2, ?_⟩
      · rw [hbend, sub_add_cancel]; exact hyΩ
      · rw [hbend, sub_add_cancel]; exact hy
    · left
      exact ⟨hyT, Or.inl hyΩ, hy, by rw [hbend]; exact h1⟩
  · left
    have hE := S.Ω_top (j + 1) (by omega)
    refine ⟨hyT, Or.inl hyΩ, hy, ?_⟩
    rw [hE]; simp

end SeqDom

end Lattices
end CoreLean

end
