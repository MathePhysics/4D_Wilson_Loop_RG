/-
`prop:sf-vector-lower` of BALABAN_CORE.tex (`c1d6d533fce5`), the step "The comparison sequence": the sequence with the
layers `i` and `i + 1` only (`Ω_n = 𝕋` for `n ≤ i`, `Ω_{i+1} = Λ`, `Ω_n = ∅` for `n ≥ i + 2`) on the lattice of a given
sequence, for a union `Λ` of cubes of the grid of side `Ma_{i+1}`; no separation condition applies to it. The cases (a)
and (b) of the core are `twoLayer S j Λ` and `twoLayer S (j - 1) Λ`, the case (c) is `oneLayer S 0`.

* `twoLayer`, `twoLayer_low`, `twoLayer_mid`, `twoLayer_high`: the sequence and its domains.
* `twoLayer_N0`: the same fine lattice (definitionally).
-/
import CoreLean.SFVectorForms

open Finset Matrix

noncomputable section

namespace CoreLean
namespace SFBounds

open Lattices SeqDom Blocks SmallFieldBlocks SFLocal SmallFieldDecay SmallFieldCoercivity
  SequenceOperators CompressedInverse ConcretePairing SFBox SFBox.SeqDomBox

variable (S : SeqDom) {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "NF" => SequenceAverages.N0 S

/-- `Λ` is a union of cubes of the grid of side `Ma_n`. -/
def IsCubes (n : ℕ) (Λ : Set (Tor (ellT S.L S.mT))) : Prop :=
  ∃ C : Set (Tor (ellT S.L S.mT)), C ⊆ Lat (ellT S.L S.mT) ((S.L ^ S.mM : ℕ) * sp S.L S.k n) ∧
    Λ = ⋃ c ∈ C, cell ((S.L ^ S.mM : ℕ) * sp S.L S.k n) c

open Classical in
/-- **The sequence with the layers `i` and `i + 1` only** on the lattice of `S`. -/
def twoLayer (i : ℕ) (hi : i + 1 ≤ S.k) (Λ : Set (Tor (ellT S.L S.mT))) (hΛ : IsCubes S (i + 1) Λ) : SeqDom where
  L := S.L
  L_odd := S.L_odd
  three_le_L := S.three_le_L
  k := S.k
  mT := S.mT
  one_le_mT := S.one_le_mT
  mM := S.mM
  mM_le := S.mM_le
  R := S.R
  one_le_R := S.one_le_R
  Ω := fun n => if n ≤ i then Set.univ else if n = i + 1 then Λ else ∅
  Ω_zero := by simp
  Ω_succ := fun n => by
    by_cases h : n + 1 ≤ i
    · rw [if_pos h, if_pos (by omega)]
    · rw [if_neg h]
      by_cases h' : n + 1 = i + 1
      · rw [if_pos h', if_pos (by omega)]; exact Set.subset_univ _
      · rw [if_neg h']; exact Set.empty_subset _
  Ω_top := fun n hn => by rw [if_neg (by omega), if_neg (by omega)]
  cubes := fun n _ _ => by
    by_cases h : n ≤ i
    · refine ⟨Lat (ellT S.L S.mT) ((S.L ^ S.mM : ℕ) * sp S.L S.k n), subset_rfl, ?_⟩
      rw [if_pos h]
      ext z
      simp only [Set.mem_univ, true_iff, Set.mem_iUnion]
      have hL := S.Lpos
      obtain ⟨c, hc, hz⟩ := cells_cover (mul_pos (Nat.cast_pos.2 (pow_pos S.Lpos _)) (Lattices.sp_pos S.Lpos n)) z
      exact ⟨c, hc, hz⟩
    · by_cases h' : n = i + 1
      · subst h'; rw [if_neg h, if_pos rfl]; exact hΛ
      · exact ⟨∅, Set.empty_subset _, by rw [if_neg h, if_neg h']; simp⟩
  sep := fun n _ _ hc hn => by
    exfalso
    by_cases h : n ≤ i
    · rw [if_pos h] at hc; simp at hc
    · by_cases h' : n = i
      · omega
      · rw [if_neg (by omega : ¬ (n + 1 ≤ i)), if_neg (by omega : ¬ (n + 1 = i + 1))] at hn; simp at hn

variable {S}

lemma twoLayer_low {i : ℕ} {hi : i + 1 ≤ S.k} {Λ : Set (Tor (ellT S.L S.mT))} {hΛ : IsCubes S (i + 1) Λ} {n : ℕ}
    (hn : n ≤ i) : (twoLayer S i hi Λ hΛ).Ω n = Set.univ := by
  show (if n ≤ i then Set.univ else if n = i + 1 then Λ else ∅) = _
  rw [if_pos hn]; rfl

lemma twoLayer_mid {i : ℕ} {hi : i + 1 ≤ S.k} {Λ : Set (Tor (ellT S.L S.mT))} {hΛ : IsCubes S (i + 1) Λ} :
    (twoLayer S i hi Λ hΛ).Ω (i + 1) = Λ := by
  show (if i + 1 ≤ i then Set.univ else if i + 1 = i + 1 then Λ else ∅) = _
  rw [if_neg (by omega), if_pos rfl]

lemma twoLayer_high {i : ℕ} {hi : i + 1 ≤ S.k} {Λ : Set (Tor (ellT S.L S.mT))} {hΛ : IsCubes S (i + 1) Λ} {n : ℕ}
    (hn : i + 2 ≤ n) : (twoLayer S i hi Λ hΛ).Ω n = ∅ := by
  show (if n ≤ i then Set.univ else if n = i + 1 then Λ else ∅) = _
  rw [if_neg (by omega), if_neg (by omega)]; rfl

lemma twoLayer_N0 {i : ℕ} {hi : i + 1 ≤ S.k} {Λ : Set (Tor (ellT S.L S.mT))} {hΛ : IsCubes S (i + 1) Λ} :
    SequenceAverages.N0 (twoLayer S i hi Λ hΛ) = NF := rfl

/-! ### The minimiser of the variational problem -/

variable (S)

/-- **The minimiser** `λ = G'Rf`, `R = I - P` (the torus as the Dirichlet domain, trivial configuration). -/
def minim [NeZero N] (f : Site NF → Mat) : Site NF → Mat :=
  Gp' S.toDomSeq (cfgX (X0 S)) (W1 S) Set.univ (f - Pop S (X0 S) (W1 S) Set.univ f)

/-- **`λ = G'Rf ∈ N(Q')`.** -/
theorem minim_null [NeZero N] (f : Site NF → Mat) :
    ∀ y ∈ detB S.toDomSeq, avgW S.toDomSeq (W1 S) y (minim S f) = 0 := by
  have hb := hb_triv (N := N) (S := S) Set.univ
  have h0 : Pop S (X0 S) (W1 S) Set.univ (f - Pop S (X0 S) (W1 S) Set.univ f) = 0 := by
    rw [map_sub, Pop_idem S _ _ _ hb, sub_self]
  exact (blk_zero_iff S (W1 S) _).1 ((Pop_eq_zero_iff S _ _ _ hb _).1 h0)

/-- **`Δλ = Rf`** for the minimiser. -/
theorem minim_lap [NeZero N] (f : Site NF → Mat) :
    Ds1L a1 (cfgX (X0 S)) (D0L a1 (cfgX (X0 S)) (minim S f)) = f - Pop S (X0 S) (W1 S) Set.univ f := by
  funext x
  have h := eqn_Gp' S.toDomSeq (cfgX (X0 S)) (W1 S) Set.univ (hK_triv S Set.univ)
    (f - Pop S (X0 S) (W1 S) Set.univ f) (Set.mem_univ x)
  have hN : Ncon S.toDomSeq (W1 S) (minim S f) = 0 := by
    funext x'
    unfold Ncon
    rw [minim_null S f _ (bc_mem_detB S x')]
    simp only [Ad, Matrix.mul_zero, Matrix.zero_mul, smul_zero, Pi.zero_apply]
  change Lap 1 (cfgX (X0 S)) (minim S f) x = _
  rw [show minim S f = Gp' S.toDomSeq (cfgX (X0 S)) (W1 S) Set.univ (f - Pop S (X0 S) (W1 S) Set.univ f) from rfl] at hN ⊢
  rw [h, hN, Pi.zero_apply, sub_zero]

/-- **`‖f - Δλ‖² = ‖Pf‖²`** for the minimiser (eq:sf-variational, the equality). -/
theorem minim_dist [NeZero N] (f : Site NF → Mat) :
    ∑ x, hs2 ((f - Ds1L a1 (cfgX (X0 S)) (D0L a1 (cfgX (X0 S)) (minim S f))) x) =
      ∑ x, hs2 (Pop S (X0 S) (W1 S) Set.univ f x) := by
  rw [minim_lap, sub_sub_cancel]

/-! ### The Laplacian of a product (eq:local-leibniz, eq:local-commutator at the trivial configuration) -/

/-- The Laplacian of the trivial configuration: `Δλ(x) = Σ_ν(2λ(x) - λ(x + e_ν) - λ(x - e_ν))`. -/
lemma lap0_triv (lam : Site NF → Mat) (x : Site NF) :
    Ds1L a1 (cfgX (X0 S)) (D0L a1 (cfgX (X0 S)) lam) x =
      ∑ ν, ((2 : ℂ) • lam x - lam (x + unit NF ν) - lam (x - unit NF ν)) := by
  rw [Ds1L_triv]
  refine sum_congr rfl fun ν _ => ?_
  simp only [D0L_triv, sub_add_cancel]
  rw [two_smul]; abel

/-- The scalar Laplacian of the fine lattice. -/
def lapR (g : Site NF → ℝ) (x : Site NF) : ℝ := ∑ ν, (2 * g x - g (x + unit NF ν) - g (x - unit NF ν))

/-- **The Leibniz rule**: `Δ(gλ) = gΔλ + (Δg)λ - Σ_ν(d⁺g d⁺λ + d⁻g d⁻λ)`. -/
lemma lap_mul (g : Site NF → ℝ) (lam : Site NF → Mat) (x : Site NF) :
    Ds1L a1 (cfgX (X0 S)) (D0L a1 (cfgX (X0 S)) (fun x => (g x : ℂ) • lam x)) x =
      (g x : ℂ) • Ds1L a1 (cfgX (X0 S)) (D0L a1 (cfgX (X0 S)) lam) x + (lapR S g x : ℂ) • lam x -
        ∑ ν, (((g (x + unit NF ν) - g x : ℝ) : ℂ) • (lam (x + unit NF ν) - lam x) +
          ((g (x - unit NF ν) - g x : ℝ) : ℂ) • (lam (x - unit NF ν) - lam x)) := by
  rw [lap0_triv, lap0_triv, smul_sum]
  simp only [lapR]
  push_cast
  rw [sum_smul, ← sum_add_distrib, ← sum_sub_distrib]
  refine sum_congr rfl fun ν _ => ?_
  module

end SFBounds
end CoreLean

end
