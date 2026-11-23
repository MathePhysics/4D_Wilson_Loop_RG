/-
`lem:wide-class`(i) of BALABAN_CORE.tex: the cubes of the wide class.

Model (with `BlockPartition.lean`). The block size is `M = L^m`; the cubes of the grid of side `Ma_j` are
the cells of scale `j + m` (centred at the points of `T^{(j+m)}`, like the cells `Δ_j`; with this
placement the grids of the sides `Ma_j` nest, as the cells do), so that a set is a union of cubes of
that grid iff membership depends only on the cell of scale `j + m` (`UnionCells`). A cube of side `s` is
`{x | 0 ≤ x_ν - c_ν < s}` (`Cube`). The separation `R ≥ 21L` with `M` enters as `RM ≥ 21LM`; the grids
are defined for `j + m ≤ m_𝕋 + k` (`M ≤ L^{m_𝕋}` in `def:sequence`).
-/
import CoreLean.Transports

open Finset

noncomputable section

namespace CoreLean

namespace Blocks

variable {N : ℕ} [NeZero N]

namespace DomSeq

variable (S : DomSeq N)

/-- `Q` is a union of cells of scale `g`. -/
def UnionCells (g : ℕ) (Q : Set (Pt N)) : Prop := ∀ x, x ∈ Q ↔ cen S.L g x ∈ Q

/-- The cube `{x | 0 ≤ x_ν - c_ν < s}`. -/
def Cube (c : Pt N) (s : ℕ) : Set (Pt N) := {x | ∀ ν, (x ν - c ν).val < s}

/-- A cube of the class (`hi = 20Ma_j`) or of the wide class (`hi = 20LMa_j`) of the index `j`, of the
block size `M = L^m` (`def:regular-pairs`(i)). -/
def ClassCube (m j hi : ℕ) (Q : Set (Pt N)) : Prop :=
  S.UnionCells (j + m) Q ∧ (∃ c s, Q = Cube c s ∧ 10 * S.L ^ m * S.L ^ j ≤ s ∧ s ≤ hi) ∧
    Q ⊆ S.Ω j \ S.Ω (j + 2) ∧ ∃ x ∈ Q, x ∈ S.Ω j ∧ x ∉ S.Ω (j + 1)

/-- Two points of a cube of side `s` are at the `ℓ^∞`-distance of less than `s`. -/
lemma dinf_lt_of_cube {c : Pt N} {s : ℕ} {x x' : Pt N} (hx : x ∈ Cube c s) (hx' : x' ∈ Cube c s)
    (hs : 0 < s) : dinf x x' < s := by
  rw [dinf_lt_iff hs]
  intro ν
  have e : x ν - x' ν = ((((x ν - c ν).val : ℤ) - ((x' ν - c ν).val : ℤ) : ℤ) : ZMod N) := by
    push_cast
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    ring
  rw [e]
  refine lt_of_le_of_lt (cd_intCast_le _) ?_
  have h1 := hx ν
  have h2 := hx' ν
  omega

/-- The grids nest: a union of cells of scale `g + 1` is a union of cells of scale `g`. -/
lemma unionCells_pred {g : ℕ} (hg : S.L ^ (g + 1) ∣ N) {Q : Set (Pt N)}
    (hQ : S.UnionCells (g + 1) Q) : S.UnionCells g Q := by
  intro x
  rw [hQ x, hQ (cen S.L g x)]
  have : cen S.L (g + 1) (cen S.L g x) = cen S.L (g + 1) x := by
    funext ν; exact cen1_cen1 S.L_odd hg (x ν)
  rw [this]

/-- `lem:wide-class`(i): a cube which is a union of cubes of the grid of side `Ma_j`, has a side
`10Ma_j ≤ s ≤ 20Ma_j`, and meets `Ω_j \ Ω_{j+1}` is a cube of the class of the index `j` if it lies in
`Ω_j`; otherwise `j ≥ 1` and it is a cube of the wide class of the index `j - 1`. -/
theorem wide_class {m : ℕ} (hRM : 21 * (S.L : ℝ) * (S.L : ℝ) ^ m ≤ S.RM) {j : ℕ}
    (hjm : j + m ≤ S.mT + S.k) {Q : Set (Pt N)} (hQ : S.UnionCells (j + m) Q) {c : Pt N} {s : ℕ}
    (hQc : Q = Cube c s) (hs1 : 10 * S.L ^ m * S.L ^ j ≤ s) (hs2 : s ≤ 20 * S.L ^ m * S.L ^ j)
    (hmeet : ∃ x ∈ Q, x ∈ S.Ω j ∧ x ∉ S.Ω (j + 1)) :
    (Q ⊆ S.Ω j → S.ClassCube m j (20 * S.L ^ m * S.L ^ j) Q) ∧
    (¬ Q ⊆ S.Ω j → 1 ≤ j ∧
      S.ClassCube m (j - 1) (20 * S.L * S.L ^ m * S.L ^ (j - 1)) Q) := by
  have hL := S.L_pos
  have hL3 : (3 : ℝ) ≤ S.L := by exact_mod_cast S.three_le_L
  have hLm : (0 : ℝ) < (S.L : ℝ) ^ m := pow_pos hL _
  have hspos : 0 < s := lt_of_lt_of_le (by have := S.three_le_L; positivity) hs1
  obtain ⟨x₀, hx₀Q, hx₀j, hx₀j1⟩ := hmeet
  -- the diameter of the cube
  have hdiam : ∀ x ∈ Q, ∀ x' ∈ Q, (dinf x x' : ℝ) < 20 * (S.L : ℝ) ^ m * (S.L : ℝ) ^ j := by
    intro x hx x' hx'
    rw [hQc] at hx hx'
    have h := dinf_lt_of_cube hx hx' hspos
    have : dinf x x' < 20 * S.L ^ m * S.L ^ j := lt_of_lt_of_le h hs2
    exact_mod_cast this
  have hLj : (0 : ℝ) < (S.L : ℝ) ^ j := pow_pos hL _
  constructor
  · intro hsub
    refine ⟨hQ, ⟨c, s, hQc, hs1, hs2⟩, fun x hx => ⟨hsub hx, fun hx2 => ?_⟩, x₀, hx₀Q, hx₀j, hx₀j1⟩
    -- a point of `Ω_{j+2}` would be farther than `RMa_{j+1}` from `x₀`
    have hsep := S.sep' (j + 1) x₀ hx₀j1 x hx2
    have hd := hdiam x₀ hx₀Q x hx
    have : 20 * (S.L : ℝ) ^ m * (S.L : ℝ) ^ j ≤ S.RM * (S.L : ℝ) ^ (j + 1) := by
      rw [pow_succ]
      have : 20 * (S.L : ℝ) ^ m * (S.L : ℝ) ^ j ≤ 21 * S.L * (S.L : ℝ) ^ m * ((S.L : ℝ) ^ j * S.L) := by
        have : (1 : ℝ) ≤ S.L * S.L := by nlinarith
        nlinarith [mul_pos hLm hLj]
      nlinarith [mul_le_mul_of_nonneg_right hRM (by positivity : (0 : ℝ) ≤ (S.L : ℝ) ^ j * S.L)]
    linarith
  · intro hsub
    obtain ⟨x₁, hx₁Q, hx₁j⟩ : ∃ x ∈ Q, x ∉ S.Ω j := by
      by_contra h; push_neg at h; exact hsub h
    have hj1 : 1 ≤ j := by
      by_contra h
      have : j = 0 := by omega
      subst this
      exact hx₁j (by rw [S.Ω_zero]; trivial)
    refine ⟨hj1, ?_, ⟨c, s, hQc, ?_, ?_⟩, fun x hx => ⟨?_, ?_⟩, x₁, hx₁Q, ?_, ?_⟩
    · -- the grid of side `Ma_{j-1}`
      refine S.unionCells_pred ?_ (by rwa [show j - 1 + m + 1 = j + m by omega])
      rw [show j - 1 + m + 1 = j + m by omega]
      exact (Dvd.dvd.mul_left (pow_dvd_pow _ hjm) 2).trans (dvd_of_eq S.N_eq.symm)
    · calc 10 * S.L ^ m * S.L ^ (j - 1) ≤ 10 * S.L ^ m * S.L ^ j := by
            gcongr
            · have := S.three_le_L; omega
            · omega
        _ ≤ s := hs1
    · calc s ≤ 20 * S.L ^ m * S.L ^ j := hs2
        _ = 20 * S.L * S.L ^ m * S.L ^ (j - 1) := by
            rw [show j = j - 1 + 1 by omega, pow_succ]; simp only [Nat.add_sub_cancel]; ring
    · -- the cube lies in `Ω_{j-1}`
      by_contra hx'
      have hsep := S.sep' (j - 1) x hx' x₀ (by rwa [Nat.sub_add_cancel hj1])
      have hd := hdiam x hx x₀ hx₀Q
      have e : (S.L : ℝ) ^ j = S.L * (S.L : ℝ) ^ (j - 1) := by
        rw [← pow_succ']; congr 1; omega
      have hLj1 : (0 : ℝ) < (S.L : ℝ) ^ (j - 1) := pow_pos hL _
      rw [e] at hd
      nlinarith [mul_le_mul_of_nonneg_right hRM hLj1.le, mul_pos hLm hLj1]
    · -- and does not meet `Ω_{j+1}`
      intro hx2
      rw [show j - 1 + 2 = j + 1 by omega] at hx2
      have hsep := S.sep' j x₁ hx₁j x hx2
      have hd := hdiam x₁ hx₁Q x hx
      have : 20 * (S.L : ℝ) ^ m * (S.L : ℝ) ^ j ≤ S.RM * (S.L : ℝ) ^ j := by
        nlinarith [mul_le_mul_of_nonneg_right hRM hLj.le, mul_pos hLm hLj]
      linarith
    · -- `x₁ ∈ Ω_{j-1}`
      by_contra hx'
      have hsep := S.sep' (j - 1) x₁ hx' x₀ (by rwa [Nat.sub_add_cancel hj1])
      have hd := hdiam x₁ hx₁Q x₀ hx₀Q
      have e : (S.L : ℝ) ^ j = S.L * (S.L : ℝ) ^ (j - 1) := by
        rw [← pow_succ']; congr 1; omega
      have hLj1 : (0 : ℝ) < (S.L : ℝ) ^ (j - 1) := pow_pos hL _
      rw [e] at hd
      nlinarith [mul_le_mul_of_nonneg_right hRM hLj1.le, mul_pos hLm hLj1]
    · rwa [Nat.sub_add_cancel hj1]

end DomSeq

end Blocks

end CoreLean
