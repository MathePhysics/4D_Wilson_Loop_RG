/-
`lem:cube-distance` of BALABAN_CORE.tex (`a021c13be348`), the statements after the first, on the continuum model
`ContSeq` with the weighted distance `d` of `Distance.lean`. A closed cube with the centre `c` and the side `s` is
`cell s c`; for `□` of the side `2Ma_j`, `□̃^n` is the cube of the side `(2 + 2n)Ma_j` with the same centre.
(i) If `j(y') ≤ j + 1`, `y' ∈ □̃^r` and `z ∉ □̃^{r+1}`, then `d(z, y') ≥ M/L³` (`cube_distance_i_cube`), and
`d(y'', y') ≥ M/L³ - 2` for a point `y''` of a layer whose block has a point outside `□̃^{r+1}`
(`cube_distance_i_block`). (ii) For `M ≥ 6L + 12`, a point `p` with `j(p) ≤ j + 1` whose block meets the cube `□_h` of the
side `(4/3)Ma_j + 2a₀` has `|p - c|_∞ < Ma_j`, so lies in `□`, and `d(z, p) ≥ M/(4L³)` for `z ∉ □`
(`cube_distance_ii`). The scale bound `j ≤ j(□) + 1` of the points near the cube (the remark after `def:walk-cubes`)
is a hypothesis. The proofs are the core's: an `ℓ^∞`-distance of at least `sMa_j` and part (i) with `s = 1`, `1/4`.
-/
import CoreLean.CubeDistance

open Set

noncomputable section

namespace CoreLean
namespace Summation
namespace ContSeq

variable {p : ℝ} (C : ContSeq p)

lemma a_mono {i j : ℕ} (h : i ≤ j) : C.a i ≤ C.a j := by
  unfold a aa
  have hL : (1 : ℝ) ≤ C.L := by have := C.three_le_L; exact_mod_cast (by omega : 1 ≤ C.L)
  have hLk : (0 : ℝ) < (C.L : ℝ) ^ C.k := by have := C.L_pos; positivity
  exact div_le_div_of_nonneg_right (pow_le_pow_right₀ hL h) hLk.le

lemma a_le_L {i j : ℕ} (h : i ≤ j + 1) : C.a i ≤ C.L * C.a j := by
  rw [C.L_mul_a]; exact C.a_mono h

lemma dist1_ge (z z' : Tor p) (ν : Fin 4) : ‖z ν - z' ν‖ ≤ dist1 z z' :=
  Finset.single_le_sum (f := fun ν => ‖z ν - z' ν‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ ν)

/-- An `ℓ^∞`-separation `|z_ν - y'_ν| ≥ t` in one direction gives `dist1 y' z ≥ t`. -/
lemma far_coord {y' z c : Tor p} {h₁ h₂ : ℝ} (hy : y' ∈ cell (2 * h₁) c) (hz : z ∉ cell (2 * h₂) c) :
    h₂ - h₁ ≤ dist1 y' z := by
  simp only [cell, mem_setOf_eq, not_forall, not_le] at hy hz
  obtain ⟨ν, hν⟩ := hz
  have h1 := hy ν
  have h2 : ‖z ν - c ν‖ ≤ ‖y' ν - z ν‖ + ‖y' ν - c ν‖ := by
    calc ‖z ν - c ν‖ = ‖-(y' ν - z ν) + (y' ν - c ν)‖ := by congr 1; abel
      _ ≤ ‖-(y' ν - z ν)‖ + ‖y' ν - c ν‖ := norm_add_le _ _
      _ = ‖y' ν - z ν‖ + ‖y' ν - c ν‖ := by rw [norm_neg]
  have h3 := dist1_ge y' z ν
  linarith

/-- **`lem:cube-distance`(i)**, the second statement: `y' ∈ □̃^r`, `j(y') ≤ j + 1`, `z ∉ □̃^{r+1}` give
`d(z, y') ≥ M/L³`. -/
theorem cube_distance_i_cube {M : ℝ} (hM0 : 0 < M) (hMR : M ≤ C.RM) {j : ℕ} {r : ℕ} {c y' z : Tor p}
    (hscale : C.D.scale y' ≤ j + 1) (hy : y' ∈ cell ((2 + 2 * r) * M * C.a j) c)
    (hz : z ∉ cell ((2 + 2 * (r + 1)) * M * C.a j) c) :
    ENNReal.ofReal (M / (C.L : ℝ) ^ 3) ≤ wdist C.D y' z := by
  have h := far_coord (h₁ := (1 + r) * M * C.a j) (h₂ := (2 + r) * M * C.a j)
    (by convert hy using 2; ring) (by convert hz using 2; ring)
  have := C.cube_distance_i (s := 1) hM0 hMR one_pos le_rfl hscale (by linarith)
  simpa using this

/-- **`lem:cube-distance`(i)**, the third statement: for a point `y''` of a layer `Γ_i` whose block has a point
outside `□̃^{r+1}`, `d(y'', y') ≥ M/L³ - 2`. -/
theorem cube_distance_i_block {M : ℝ} (hM0 : 0 < M) (hMR : M ≤ C.RM) {j : ℕ} {r : ℕ} {c y' : Tor p}
    (hscale : C.D.scale y' ≤ j + 1) (hy : y' ∈ cell ((2 + 2 * r) * M * C.a j) c) {i : ℕ} (hi : i ≤ C.k)
    {y'' : Tor p} (hy''l : InLat (C.a i) y'') (hy''1 : y'' ∈ C.Ω i) (hy''2 : y'' ∉ C.Ω (i + 1))
    {z : Tor p} (hzb : z ∈ cell (C.a i) y'') (hz : z ∉ cell ((2 + 2 * (r + 1)) * M * C.a j) c) :
    ENNReal.ofReal (M / (C.L : ℝ) ^ 3 - 2) ≤ wdist C.D y'' y' := by
  have h1 := C.cube_distance_i_cube hM0 hMR hscale hy hz
  have h2 := C.wdist_cell_le hi hy''l hy''1 hy''2 hzb
  have h3 : wdist C.D y' z ≤ wdist C.D y'' y' + wdist C.D y'' z := by
    rw [wdist_comm C.D y'' y']
    exact wdist_triangle C.D y' y'' z
  rw [ENNReal.ofReal_sub _ (by norm_num : (0 : ℝ) ≤ 2), tsub_le_iff_right]
  exact h1.trans (h3.trans (add_le_add_right h2 _))

/-- **`lem:cube-distance`(ii)**: for `M ≥ 6L + 12` and `□` of the side `2Ma_j` with the centre `c`, a point `p` with
`j(p) ≤ j + 1` whose block (of the side `a_i`, `i ≤ j + 1`) meets the cube `□_h` of the side `(4/3)Ma_j + 2a₀` satisfies
`|p - c|_∞ < Ma_j`, hence lies in `□`, and `d(z, p) ≥ M/(4L³)` for every `z ∉ □`. -/
theorem cube_distance_ii {M : ℝ} (hML : 6 * (C.L : ℝ) + 12 ≤ M) (hMR : M ≤ C.RM) {j i : ℕ} (hij : i ≤ j + 1)
    {c pt x : Tor p} (hscale : C.D.scale pt ≤ j + 1) (hxb : x ∈ cell (C.a i) pt)
    (hxh : x ∈ cell (4 / 3 * M * C.a j + 2 * C.a 0) c) :
    (∀ ν, ‖pt ν - c ν‖ < M * C.a j) ∧ pt ∈ cell (2 * M * C.a j) c ∧
      ∀ z, z ∉ cell (2 * M * C.a j) c → ENNReal.ofReal (M / (4 * (C.L : ℝ) ^ 3)) ≤ wdist C.D pt z := by
  have haj := C.a_pos j
  have ha0 : C.a 0 ≤ C.a j := C.a_mono (Nat.zero_le j)
  have hai : C.a i ≤ C.L * C.a j := C.a_le_L hij
  have hL := C.L_pos
  -- `|p - c|_∞ ≤ (2/3)Ma_j + a₀ + (1/2)La_j`
  have hpc : ∀ ν, ‖pt ν - c ν‖ ≤ 2 / 3 * M * C.a j + C.a 0 + C.L * C.a j / 2 := by
    intro ν
    have h1 := hxb ν
    have h2 := hxh ν
    have h3 : ‖pt ν - c ν‖ ≤ ‖x ν - pt ν‖ + ‖x ν - c ν‖ := by
      calc ‖pt ν - c ν‖ = ‖-(x ν - pt ν) + (x ν - c ν)‖ := by congr 1; abel
        _ ≤ ‖-(x ν - pt ν)‖ + ‖x ν - c ν‖ := norm_add_le _ _
        _ = ‖x ν - pt ν‖ + ‖x ν - c ν‖ := by rw [norm_neg]
    linarith
  have hlt : ∀ ν, ‖pt ν - c ν‖ < M * C.a j := by
    intro ν
    have := hpc ν
    nlinarith
  refine ⟨hlt, fun ν => by have := hlt ν; linarith, fun z hz => ?_⟩
  -- `|z - p|_∞ ≥ (1/3)Ma_j - a₀ - (1/2)La_j ≥ (1/4)Ma_j`
  have hfar : 1 / 4 * M * C.a j ≤ dist1 pt z := by
    simp only [cell, mem_setOf_eq, not_forall, not_le] at hz
    obtain ⟨ν, hν⟩ := hz
    have h1 := hpc ν
    have h2 : ‖z ν - c ν‖ ≤ ‖pt ν - z ν‖ + ‖pt ν - c ν‖ := by
      calc ‖z ν - c ν‖ = ‖-(pt ν - z ν) + (pt ν - c ν)‖ := by congr 1; abel
        _ ≤ ‖-(pt ν - z ν)‖ + ‖pt ν - c ν‖ := norm_add_le _ _
        _ = ‖pt ν - z ν‖ + ‖pt ν - c ν‖ := by rw [norm_neg]
    have h3 := dist1_ge pt z ν
    nlinarith
  have hM0 : 0 < M := by linarith
  have := C.cube_distance_i (s := 1 / 4) hM0 hMR (by norm_num) (by norm_num) hscale hfar
  convert this using 2
  ring

/-- **The layers near a cube** (the remark after `def:walk-cubes`): for `RM ≥ 12LM`, a point `z` within the
`ℓ^∞`-distance `10Ma_j` of a point `y ∈ Ω_j` and of a point `w ∉ Ω_{j+1}` (the points of `□̃^9` and of a cube `b` of
the grid in `□`) lies in `Ω_{j-1}` and not in `Ω_{j+2}`, so that its scale is `j - 1`, `j`, or `j + 1`. -/
theorem layers_near {M : ℝ} (hM0 : 0 < M) (hRM : 12 * (C.L : ℝ) * M ≤ C.RM) {j : ℕ} (hj : j ≤ C.k)
    {y w z : Tor p} (hy : y ∈ C.Ω j) (hw : w ∉ C.Ω (j + 1)) (hzy : dist z y ≤ 10 * M * C.a j)
    (hzw : dist z w ≤ 10 * M * C.a j) :
    z ∈ C.Ω (j - 1) ∧ z ∉ C.Ω (j + 2) ∧ C.D.scale z ≤ j + 1 ∧ j - 1 ≤ C.D.scale z := by
  have hL := C.L_pos
  have hL1 : (1 : ℝ) ≤ C.L := by have := C.three_le_L; exact_mod_cast (by omega : 1 ≤ C.L)
  have h1 : z ∈ C.Ω (j - 1) := by
    rcases Nat.lt_or_ge j 2 with hj2 | hj2
    · rw [show j - 1 = 0 by omega, C.Ω_zero]; trivial
    by_contra hz
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at hz
    have hsep := C.sep i (by omega) (by omega) z hz y hy
    have hai := C.a_pos i
    have e := C.L_mul_a i
    have : 12 * (C.L : ℝ) * M * C.a i ≤ C.RM * C.a i := mul_le_mul_of_nonneg_right hRM hai.le
    change C.RM * 1 * C.a i ≤ dist z y at hsep
    have e2 : 12 * M * C.a (i + 1) = 12 * (C.L : ℝ) * M * C.a i := by rw [← e]; ring
    have hMa : 0 < M * C.a (i + 1) := mul_pos hM0 (C.a_pos _)
    linarith
  have h2 : z ∉ C.Ω (j + 2) := by
    intro hz
    rcases Nat.lt_or_ge C.k (j + 2) with hk | hk
    · have : C.Ω (j + 2) = ∅ := by
        simp only [Ω, Om]; rw [if_neg (by omega), if_neg (by omega)]
      rw [this] at hz; exact hz
    have hsep := C.sep (j + 1) (by omega) (by omega) w hw z hz
    have haj := C.a_pos j
    have e := C.L_mul_a j
    rw [dist_comm] at hsep
    have h3 : 12 * (C.L : ℝ) * M * C.a (j + 1) ≤ C.RM * C.a (j + 1) :=
      mul_le_mul_of_nonneg_right hRM (C.a_pos _).le
    have hMa : 0 < M * C.a j := mul_pos hM0 haj
    have hLL : (1 : ℝ) ≤ C.L * C.L := by nlinarith
    have h4 : 10 * M * C.a j < 12 * (C.L : ℝ) * M * C.a (j + 1) := by
      rw [← e]
      calc 10 * M * C.a j < 12 * (M * C.a j) := by linarith
        _ ≤ 12 * ((C.L * C.L) * (M * C.a j)) := by nlinarith
        _ = 12 * (C.L : ℝ) * M * (C.L * C.a j) := by ring
    change C.RM * 1 * C.a (j + 1) ≤ dist z w at hsep
    linarith
  obtain ⟨hs1, hs2⟩ := C.D.mem_scale z
  refine ⟨h1, h2, ?_, ?_⟩
  · by_contra h
    exact h2 (C.D.Ω_anti (show j + 2 ≤ C.D.scale z by omega) hs1)
  · by_contra h
    exact hs2 (C.D.Ω_anti (show C.D.scale z + 1 ≤ j - 1 by omega) h1)

end ContSeq
end Summation
end CoreLean

end
