/-
`lem:layer-bonds`(i) of BALABAN_CORE.tex (`a021c13be348`), for the sequences of domains of `SequencesTorus.lean`: if
`RM ≥ 2L`, every point within the `ℓ^∞`-distance `(3/2)a_j` of `Ω_j` lies in `Ω_{j-1}` (`Ω_{-1} = Ω_0`), and within
`3a_j` if `RM ≥ 4L`. The proof is the core's: by `eq:separation` the distance of `Ω_j` from the complement of `Ω_{j-1}`
exceeds `RMa_{j-1} ≥ 2La_{j-1} = 2a_j`, and `4a_j` if `RM ≥ 4L`.
-/
import CoreLean.SequencesTorus

open Set

noncomputable section

namespace CoreLean
namespace Lattices
namespace SeqDom

variable (S : SeqDom)

lemma sp_succ (L k j : ℕ) : sp L k (j + 1) = L * sp L k j := by
  unfold sp; ring

lemma sp_pos {L k : ℕ} (hL : 0 < L) (j : ℕ) : 0 < sp L k j := by
  unfold sp
  have : 0 < eta L k := by unfold eta; positivity
  positivity

/-- **`lem:layer-bonds`(i)**: for `RM ≥ cL` with `c > 0`, every point within the distance `< ca_j` of `Ω_j`
lies in `Ω_{j-1}`; with `c = 2` this contains the distance `(3/2)a_j`, with `c = 4` the distance `3a_j`. -/
theorem layer_bonds_i {c : ℝ} (hRM : c * S.L ≤ ((S.R * S.L ^ S.mM : ℕ) : ℝ)) {j : ℕ} (hj : j ≤ S.k)
    {y z : Tor (ellT S.L S.mT)} (hy : y ∈ S.Ω j) (hz : dist z y < c * sp S.L S.k j) :
    z ∈ S.Ω (j - 1) := by
  rcases Nat.lt_or_ge j 2 with hj2 | hj2
  · have : j - 1 = 0 := by omega
    rw [this, S.Ω_zero]; exact mem_univ _
  by_contra hzn
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hzn
  have hsep := S.sep i (by omega) (by omega) ⟨z, hzn⟩ ⟨y, hy⟩
  have hd : setDist (S.Ω i)ᶜ (S.Ω (i + 1)) ≤ dist z y := setDist_le hzn hy
  have hL : (0 : ℝ) < S.L := by exact_mod_cast S.Lpos
  have hsp := sp_pos (k := S.k) S.Lpos i
  rw [sp_succ] at hz
  have : c * S.L * sp S.L S.k i ≤ ((S.R * S.L ^ S.mM : ℕ) : ℝ) * sp S.L S.k i :=
    mul_le_mul_of_nonneg_right hRM hsp.le
  nlinarith

/-- The form of the core: within `(3/2)a_j` for `RM ≥ 2L`. -/
theorem layer_bonds_i_two (hRM : 2 * S.L ≤ S.R * S.L ^ S.mM) {j : ℕ} (hj : j ≤ S.k)
    {y z : Tor (ellT S.L S.mT)} (hy : y ∈ S.Ω j) (hz : dist z y ≤ 3 / 2 * sp S.L S.k j) : z ∈ S.Ω (j - 1) := by
  refine S.layer_bonds_i (c := 2) (by exact_mod_cast hRM) hj hy (lt_of_le_of_lt hz ?_)
  have := sp_pos (k := S.k) S.Lpos j
  linarith

/-- The form of the core: within `3a_j` for `RM ≥ 4L`. -/
theorem layer_bonds_i_four (hRM : 4 * S.L ≤ S.R * S.L ^ S.mM) {j : ℕ} (hj : j ≤ S.k)
    {y z : Tor (ellT S.L S.mT)} (hy : y ∈ S.Ω j) (hz : dist z y ≤ 3 * sp S.L S.k j) : z ∈ S.Ω (j - 1) := by
  refine S.layer_bonds_i (c := 4) (by exact_mod_cast hRM) hj hy (lt_of_le_of_lt hz ?_)
  have := sp_pos (k := S.k) S.Lpos j
  linarith

end SeqDom
end Lattices
end CoreLean

end
