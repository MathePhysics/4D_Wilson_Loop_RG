/-
`lem:partition-of-unity` of BALABAN_CORE.tex (`46925ba99aac`) for a sequence of domains on the torus.

The setting (`Scales`, `Domains`), represented on `ℝ⁴` with the torus distance `dT`:
* the sides `s_i = Ma_i` of the grids, `s_{i+1} = Ls_i`, the side `ℓ = P_is_i` of the torus with `P_i ≥ 2` for
  `i ≤ k` (`Ma_k ≤ ℓ/2`), the fine spacing `η` with `12η ≤ s_0` (`M ≥ 12`), and the separation `R ≥ 12L`
  (`def:walk-cubes`);
* domains `Ω_0 = 𝕋 ⊃ Ω_1 ⊃ … ⊃ Ω_k`, `Ω_{k+1} = ∅`, each `Ω_i`, `1 ≤ i ≤ k`, a union of cubes of the grid
  of side `s_i` (`hgrid`), with `dist(Ω_i^c, Ω_{i+1}) > Rs_i` for `1 ≤ i < k` (`hsep`, `eq:separation`), and a
  Dirichlet domain which is the torus or a union of cubes of the grid of side `s_0 = Mη` (`hD`).

The family `𝒟_i` (`InD`): the cubes of side `2s_i` centred at a corner `s_i(n + ½)` of the grid, one of whose
`2⁴` cubes of the grid lies in `Ω_i`, is not contained in `Ω_{i+1}`, and lies in `Ω_D` if `i = 0`. The functions
`φ_□` (`Scales.φ`), `N² = Σ_{□ ∈ 𝒟}φ_□²` (`N2`), `h_□ = φ_□/max{N, 1}` (`hpu`), as in the proof of the lemma.

* `scale`: if `x ∈ □ ∈ 𝒟_j` and `φ_{□'}(x) ≠ 0` for `□' ∈ 𝒟_i`, then `|i - j| ≤ 1` (by `eq:separation`).
* `card_T_le`: at most `48` cubes of `𝒟` have `φ_{□'}(x) ≠ 0` at a point of a cube of `𝒟`.
* `covering`: `N ≥ 1` at the points within `2η` of the Dirichlet domain.
* `pu_sum`, `pu_mem`, `pu_support`: (i).
-/
import CoreLean.PartitionTorus

open Real Finset
open scoped Classical

noncomputable section

namespace CoreLean
namespace PartitionUnity

local notation "E" => Fin 4 → ℝ

/-- The scales of a sequence of domains with the block size `M` and the separation `R`. -/
structure Scales where
  L : ℕ
  k : ℕ
  ℓ : ℝ
  s : ℕ → ℝ
  P : ℕ → ℕ
  η : ℝ
  R : ℝ
  hL : 2 ≤ L
  hℓ : 0 < ℓ
  hs0 : 0 < s 0
  hsL : ∀ i, s (i + 1) = L * s i
  hP : ∀ i ≤ k, 2 ≤ P i ∧ ℓ = P i * s i
  hη : 0 < η
  hηs : 12 * η ≤ s 0
  hR : 12 * L ≤ R

namespace Scales

variable (S : Scales)

lemma L_ge : (2 : ℝ) ≤ S.L := by exact_mod_cast S.hL

lemma s_pos (i : ℕ) : 0 < S.s i := by
  induction i with
  | zero => exact S.hs0
  | succ i ih => rw [S.hsL]; have := S.L_ge; positivity

lemma s_mono {i j : ℕ} (h : i ≤ j) : S.s i ≤ S.s j := by
  induction h with
  | refl => exact le_rfl
  | @step m _ ih => rw [S.hsL]; nlinarith [S.s_pos m, S.L_ge]

lemma s_succ_le {i j : ℕ} (h : i + 1 ≤ j) : S.L * S.s i ≤ S.s j := by
  rw [← S.hsL]; exact S.s_mono h

lemma s_le_half {i : ℕ} (hi : i ≤ S.k) : S.s i ≤ S.ℓ / 2 := by
  obtain ⟨h2, he⟩ := S.hP i hi
  have : (2 : ℝ) ≤ S.P i := by exact_mod_cast h2
  rw [he]; nlinarith [S.s_pos i]

lemma η_le (i : ℕ) : 12 * S.η ≤ S.s i := S.hηs.trans (S.s_mono (Nat.zero_le i))

instance instNeZero (i : Fin (S.k + 1)) : NeZero (S.P i) :=
  ⟨by have := (S.hP i (Nat.lt_succ_iff.1 i.2)).1; omega⟩

/-- The cubes: a scale `i ≤ k` and a corner `s_i(n + ½)`, `n ∈ (ℤ/P_iℤ)⁴`, of the grid of side `s_i`. -/
abbrev Idx := Σ i : Fin (S.k + 1), Fin 4 → ZMod (S.P i)

lemma hP' (i : Fin (S.k + 1)) : S.ℓ = S.P i * S.s i := (S.hP i (Nat.lt_succ_iff.1 i.2)).2

lemma hP2 (i : Fin (S.k + 1)) : 2 ≤ S.P i := (S.hP i (Nat.lt_succ_iff.1 i.2)).1

lemma s_le_half' (i : Fin (S.k + 1)) : S.s i ≤ S.ℓ / 2 := S.s_le_half (Nat.lt_succ_iff.1 i.2)

/-- The function `φ_□(x) = Π_μ h(rep(x_μ - c_μ)/s_i)` of the cube `□ = (i, n)` with the centre `c`. -/
def φ (q : S.Idx) (x : E) : ℝ := phiT S.hℓ (S.s q.1) (cen (S.s q.1) q.2) x

lemma φ_nonneg (q : S.Idx) (x : E) : 0 ≤ S.φ q x := phiT_nonneg _ _ _ _

lemma φ_le_one (q : S.Idx) (x : E) : S.φ q x ≤ 1 := phiT_le_one _ _ _ _

lemma dT_lt_of_φ_ne {q : S.Idx} {x : E} (h : S.φ q x ≠ 0) :
    dT S.hℓ x (cen (S.s q.1) q.2) < 2 / 3 * S.s q.1 := by
  rw [dT_lt_iff]
  intro μ
  have : gT S.hℓ (S.s q.1) (cen (S.s q.1) q.2 μ) (x μ) ≠ 0 := by
    intro h0; exact h (by unfold Scales.φ phiT; exact Finset.prod_eq_zero (Finset.mem_univ μ) h0)
  exact abs_rep_lt_of_gT_ne S.hℓ (S.s_pos _) this

lemma φ_eq_zero {q : S.Idx} {x : E} (h : 2 / 3 * S.s q.1 ≤ dT S.hℓ x (cen (S.s q.1) q.2)) : S.φ q x = 0 := by
  by_contra hne
  exact absurd (S.dT_lt_of_φ_ne hne) (not_lt.2 h)

end Scales

/-- The cube of the grid of side `s_i` centred at `g`. -/
def gcube (S : Scales) (i : ℕ) (g : E) : Set E := {x | dT S.hℓ x g ≤ S.s i / 2}

/-- `g` is a centre of a cube of the grid of side `s_i`. -/
def IsGridCentre (S : Scales) (i : ℕ) (g : E) : Prop := ∀ μ, ∃ m : ℤ, g μ = S.s i * m

/-- The centre of one of the `2⁴` cubes of the grid of side `s_i` which have the corner `s_i(n + ½)`. -/
def gc (S : Scales) (i : Fin (S.k + 1)) (n : Fin 4 → ZMod (S.P i)) (ε : Fin 4 → Bool) : E :=
  fun μ => cen (S.s i) n μ + (if ε μ then S.s i / 2 else -(S.s i / 2))

lemma dT_self (S : Scales) (x : E) : dT S.hℓ x x = 0 := by
  refine le_antisymm ((dT_le_iff S.hℓ).2 fun μ => ?_) (dT_nonneg _ _ _)
  rw [sub_self, rep_of_mem S.hℓ (by linarith [S.hℓ]) (by linarith [S.hℓ]), abs_zero]

lemma mem_gcube_self (S : Scales) (i : ℕ) (g : E) : g ∈ gcube S i g := by
  show dT S.hℓ g g ≤ S.s i / 2
  rw [dT_self]; linarith [S.s_pos i]

lemma dT_gc (S : Scales) (i : Fin (S.k + 1)) (n : Fin 4 → ZMod (S.P i)) (ε : Fin 4 → Bool) :
    dT S.hℓ (cen (S.s i) n) (gc S i n ε) ≤ S.s i / 2 := by
  rw [dT_le_iff]
  intro μ
  refine (abs_rep_le_abs S.hℓ _).trans ?_
  have hs := S.s_pos i
  simp only [gc]
  split_ifs
  · rw [show cen (S.s i) n μ - (cen (S.s i) n μ + S.s i / 2) = -(S.s i / 2) by ring, abs_neg,
      abs_of_pos (by linarith)]
  · rw [show cen (S.s i) n μ - (cen (S.s i) n μ + -(S.s i / 2)) = S.s i / 2 by ring,
      abs_of_pos (by linarith)]

lemma dT_cen_of_mem (S : Scales) {i : Fin (S.k + 1)} {n : Fin 4 → ZMod (S.P i)} {ε : Fin 4 → Bool} {y : E}
    (hy : y ∈ gcube S i (gc S i n ε)) : dT S.hℓ y (cen (S.s i) n) ≤ S.s i := by
  have h1 : dT S.hℓ y (gc S i n ε) ≤ S.s i / 2 := hy
  have h2 := dT_gc S i n ε
  rw [dT_comm] at h2
  linarith [dT_triangle S.hℓ y (gc S i n ε) (cen (S.s i) n)]

/-- A sequence of domains on the torus, with a Dirichlet domain. -/
structure Domains (S : Scales) where
  Ω : ℕ → Set E
  ΩD : Set E
  hΩ0 : Ω 0 = Set.univ
  hanti : ∀ i, Ω (i + 1) ⊆ Ω i
  hΩk : Ω (S.k + 1) = ∅
  hgrid : ∀ i, 1 ≤ i → i ≤ S.k → ∀ x ∈ Ω i, ∃ g, IsGridCentre S i g ∧ x ∈ gcube S i g ∧ gcube S i g ⊆ Ω i
  hsep : ∀ i, 1 ≤ i → i < S.k → ∀ y ∉ Ω i, ∀ y' ∈ Ω (i + 1), S.R * S.s i < dT S.hℓ y y'
  hD : ΩD = Set.univ ∨
    ∀ x ∈ ΩD, ∃ g, IsGridCentre S 0 g ∧ x ∈ gcube S 0 g ∧ gcube S 0 g ⊆ ΩD

namespace Domains

variable {S : Scales} (D : Domains S)

lemma anti_le {i j : ℕ} (h : i ≤ j) : D.Ω j ⊆ D.Ω i := by
  induction h with
  | refl => exact subset_rfl
  | step _ ih => exact (D.hanti _).trans ih

/-- `□ ∈ 𝒟`: one of the `2⁴` cubes of the grid at the corner lies in `Ω_i`, is not contained in `Ω_{i+1}`,
and lies in `Ω_D` if `i = 0`. -/
def InD (q : S.Idx) : Prop :=
  ∃ ε : Fin 4 → Bool, gcube S q.1 (gc S q.1 q.2 ε) ⊆ D.Ω q.1 ∧
    ¬ gcube S q.1 (gc S q.1 q.2 ε) ⊆ D.Ω ((q.1 : ℕ) + 1) ∧
    ((q.1 : ℕ) = 0 → gcube S q.1 (gc S q.1 q.2 ε) ⊆ D.ΩD)

/-- `N² = Σ_{□ ∈ 𝒟}φ_□²`. -/
def N2 (x : E) : ℝ := ∑ q, if D.InD q then S.φ q x ^ 2 else 0

/-- `h_□ = φ_□/max{N, 1}` for `□ ∈ 𝒟`. -/
def hpu (q : S.Idx) (x : E) : ℝ := if D.InD q then S.φ q x / max (√(D.N2 x)) 1 else 0

lemma N2_nonneg (x : E) : 0 ≤ D.N2 x :=
  Finset.sum_nonneg fun q _ => by split_ifs <;> positivity

/-- **The scales.** If `x ∈ □ ∈ 𝒟_j` and `φ_{□'}(x) ≠ 0` for `□' ∈ 𝒟_i`, then `j ≤ i + 1` and `i ≤ j + 1`. -/
theorem scale {q q' : S.Idx} (hq : D.InD q) (hq' : D.InD q') {x : E}
    (hx : dT S.hℓ x (cen (S.s q.1) q.2) ≤ S.s q.1) (hφ : S.φ q' x ≠ 0) :
    (q.1 : ℕ) ≤ q'.1 + 1 ∧ (q'.1 : ℕ) ≤ q.1 + 1 := by
  obtain ⟨ε, hb, hnb, -⟩ := hq
  obtain ⟨ε', hb', hnb', -⟩ := hq'
  set j : ℕ := (q.1 : ℕ) with hj
  set i : ℕ := (q'.1 : ℕ) with hi
  have hjk : j ≤ S.k := Nat.lt_succ_iff.1 q.1.2
  have hik : i ≤ S.k := Nat.lt_succ_iff.1 q'.1.2
  have hφd := S.dT_lt_of_φ_ne hφ
  have hR := S.hR
  have hL := S.L_ge
  -- the centre `g` of the cube of the grid of `□` lies in `Ω_j`, within `s_j/2` of the centre of `□`
  have hgj : gc S q.1 q.2 ε ∈ D.Ω j := hb (mem_gcube_self S _ _)
  have hcg : dT S.hℓ (cen (S.s q.1) q.2) (gc S q.1 q.2 ε) ≤ S.s j / 2 := dT_gc S _ _ _
  have hg'i : gc S q'.1 q'.2 ε' ∈ D.Ω i := hb' (mem_gcube_self S _ _)
  have hcg' : dT S.hℓ (cen (S.s q'.1) q'.2) (gc S q'.1 q'.2 ε') ≤ S.s i / 2 := dT_gc S _ _ _
  constructor
  · by_contra h
    push_neg at h
    obtain ⟨y, hy, hyn⟩ := Set.not_subset.1 hnb'
    have hy' : y ∉ D.Ω (j - 1) := fun h' => hyn (D.anti_le (by omega) h')
    have hg : gc S q.1 q.2 ε ∈ D.Ω (j - 1 + 1) := by rw [show j - 1 + 1 = j by omega]; exact hgj
    have hsep := D.hsep (j - 1) (by omega) (by omega) y hy' _ hg
    have hyc := dT_cen_of_mem S hy
    have hsi : S.s i ≤ S.s (j - 1) := S.s_mono (by omega)
    have hsj : S.s j = S.L * S.s (j - 1) := by rw [show j = j - 1 + 1 by omega, S.hsL]; simp
    have hpos := S.s_pos (j - 1)
    have htri : dT S.hℓ y (gc S q.1 q.2 ε) ≤ S.s i + 2 / 3 * S.s i + S.s j + S.s j / 2 := by
      have t1 := dT_triangle S.hℓ y (cen (S.s q'.1) q'.2) x
      have t2 := dT_triangle S.hℓ y x (cen (S.s q.1) q.2)
      have t3 := dT_triangle S.hℓ y (cen (S.s q.1) q.2) (gc S q.1 q.2 ε)
      rw [dT_comm S.hℓ (cen (S.s q'.1) q'.2) x] at t1
      linarith
    nlinarith
  · by_contra h
    push_neg at h
    obtain ⟨y, hy, hyn⟩ := Set.not_subset.1 hnb
    have hy' : y ∉ D.Ω (i - 1) := fun h' => hyn (D.anti_le (by omega) h')
    have hg : gc S q'.1 q'.2 ε' ∈ D.Ω (i - 1 + 1) := by rw [show i - 1 + 1 = i by omega]; exact hg'i
    have hsep := D.hsep (i - 1) (by omega) (by omega) y hy' _ hg
    have hyc := dT_cen_of_mem S hy
    have hsj : S.s j ≤ S.s (i - 1) := S.s_mono (by omega)
    have hsi : S.s i = S.L * S.s (i - 1) := by rw [show i = i - 1 + 1 by omega, S.hsL]; simp
    have hpos := S.s_pos (i - 1)
    have htri : dT S.hℓ y (gc S q'.1 q'.2 ε') ≤ S.s j + S.s j + 2 / 3 * S.s i + S.s i / 2 := by
      have t1 := dT_triangle S.hℓ y (cen (S.s q.1) q.2) x
      have t2 := dT_triangle S.hℓ y x (cen (S.s q'.1) q'.2)
      have t3 := dT_triangle S.hℓ y (cen (S.s q'.1) q'.2) (gc S q'.1 q'.2 ε')
      rw [dT_comm S.hℓ (cen (S.s q.1) q.2) x] at t1
      linarith
    nlinarith

/-- The cubes of `𝒟` whose functions do not vanish at `x`. -/
def T (x : E) : Finset S.Idx := Finset.univ.filter fun q => D.InD q ∧ S.φ q x ≠ 0

/-- **The count.** At a point of a cube of `𝒟` at most `48` functions `φ_{□'}`, `□' ∈ 𝒟`, do not vanish. -/
theorem card_T_le {q : S.Idx} (hq : D.InD q) {x : E} (hx : dT S.hℓ x (cen (S.s q.1) q.2) ≤ S.s q.1) :
    (D.T x).card ≤ 48 := by
  set sc : Finset (Fin (S.k + 1)) :=
    Finset.univ.filter fun i => (q.1 : ℕ) ≤ i + 1 ∧ (i : ℕ) ≤ q.1 + 1 with hsc
  have hsub : D.T x ⊆ sc.sigma fun i =>
      Finset.univ.filter fun n : Fin 4 → ZMod (S.P i) => phiT S.hℓ (S.s i) (cen (S.s i) n) x ≠ 0 := by
    intro q' hq'
    simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at hq'
    rw [Finset.mem_sigma]
    refine ⟨?_, ?_⟩
    · simp only [hsc, Finset.mem_filter, Finset.mem_univ, true_and]
      exact D.scale hq hq'.1 hx hq'.2
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hq'.2
  refine (Finset.card_le_card hsub).trans ?_
  rw [Finset.card_sigma]
  have hfib : ∀ i ∈ sc, (Finset.univ.filter fun n : Fin 4 → ZMod (S.P i) =>
      phiT S.hℓ (S.s i) (cen (S.s i) n) x ≠ 0).card ≤ 16 :=
    fun i _ => card_nonzero_le S.hℓ (S.hP' i) (S.hP2 i) (S.s_pos i) x
  have hsc3 : sc.card ≤ 3 := by
    have : sc.card ≤ (Finset.Icc ((q.1 : ℕ) - 1) ((q.1 : ℕ) + 1)).card := by
      refine Finset.card_le_card_of_injOn (fun i => (i : ℕ)) (fun i hi => ?_) (fun a _ b _ h => Fin.ext h)
      simp only [hsc, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hi
      simp only [Finset.coe_Icc, Set.mem_Icc]
      omega
    rw [Nat.card_Icc] at this
    omega
  calc ∑ i ∈ sc, _ ≤ ∑ _i ∈ sc, 16 := Finset.sum_le_sum hfib
    _ = sc.card * 16 := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ 48 := by omega

/-- Every point lies in a layer. -/
lemma layer (x : E) : ∃ i ≤ S.k, x ∈ D.Ω i ∧ x ∉ D.Ω (i + 1) := by
  have hex : ∃ i, x ∉ D.Ω (i + 1) := ⟨S.k, by rw [D.hΩk]; simp⟩
  refine ⟨Nat.find hex, Nat.find_min' hex (by rw [D.hΩk]; simp), ?_, Nat.find_spec hex⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
  · rw [h0, D.hΩ0]; trivial
  · have := Nat.find_min hex (Nat.sub_lt hpos one_pos)
    push_neg at this
    rwa [show Nat.find hex - 1 + 1 = Nat.find hex by omega] at this

lemma exists_grid_centre (i : ℕ) (x : E) : ∃ g, IsGridCentre S i g ∧ x ∈ gcube S i g := by
  refine ⟨fun μ => S.s i * round (x μ / S.s i), fun μ => ⟨_, rfl⟩, ?_⟩
  show dT S.hℓ x _ ≤ S.s i / 2
  rw [dT_le_iff]
  intro μ
  have hs := S.s_pos i
  refine (abs_rep_le_abs S.hℓ _).trans ?_
  have := abs_sub_round (x μ / S.s i)
  rw [show x μ - S.s i * round (x μ / S.s i) = S.s i * (x μ / S.s i - round (x μ / S.s i)) by
    field_simp, abs_mul, abs_of_pos hs]
  nlinarith

/-- **The covering.** At the points within `2η` of the Dirichlet domain, `N ≥ 1`. -/
theorem covering {x : E} (hx : x ∈ D.ΩD) {p : E} (hp : dT S.hℓ p x ≤ 2 * S.η) : 1 ≤ D.N2 p := by
  obtain ⟨i, hik, hxi, hxn⟩ := D.layer x
  -- the cube `b` of the grid of side `s_i` which contains `x`
  obtain ⟨g, hgc, hxb, hbi, hbD⟩ : ∃ g, IsGridCentre S i g ∧ x ∈ gcube S i g ∧ gcube S i g ⊆ D.Ω i ∧
      (i = 0 → gcube S i g ⊆ D.ΩD) := by
    rcases Nat.eq_zero_or_pos i with h0 | hpos
    · subst h0
      rcases D.hD with hu | hg
      · obtain ⟨g, hgc, hxb⟩ := Domains.exists_grid_centre (S := S) 0 x
        exact ⟨g, hgc, hxb, by rw [D.hΩ0]; exact Set.subset_univ _, fun _ => by rw [hu]; exact Set.subset_univ _⟩
      · obtain ⟨g, hgc, hxb, hbD⟩ := hg x hx
        exact ⟨g, hgc, hxb, by rw [D.hΩ0]; exact Set.subset_univ _, fun _ => hbD⟩
    · obtain ⟨g, hgc, hxb, hbi⟩ := D.hgrid i hpos hik x hxi
      exact ⟨g, hgc, hxb, hbi, fun h => absurd h (by omega)⟩
  obtain ⟨i', rfl⟩ : ∃ i' : Fin (S.k + 1), (i' : ℕ) = i := ⟨⟨i, Nat.lt_succ_iff.2 hik⟩, rfl⟩
  have hs := S.s_pos i'
  have hη := S.η_le i'
  -- every cube at the scale `i` whose function does not vanish at `p` has `b` as one of its cubes of the grid
  have hInD : ∀ n : Fin 4 → ZMod (S.P i'), S.φ ⟨i', n⟩ p ≠ 0 → D.InD ⟨i', n⟩ := by
    intro n hn
    have hpc := S.dT_lt_of_φ_ne hn
    set ε : Fin 4 → Bool := fun μ => decide (rep S.hℓ (cen (S.s i') n μ - g μ) < 0) with hε
    have hcong : ∀ μ, ∃ w : ℤ, gc S i' n ε μ = g μ + w * S.ℓ := by
      intro μ
      obtain ⟨m, hm⟩ := hgc μ
      obtain ⟨w, hw⟩ := rep_eq_sub S.hℓ (cen (S.s i') n μ - g μ)
      set r := rep S.hℓ (cen (S.s i') n μ - g μ) with hr
      have hrb : |r| < 4 / 3 * S.s i' := by
        have t1 := abs_rep_add_le S.hℓ (cen (S.s i') n μ - p μ) (p μ - x μ)
        have t2 := abs_rep_add_le S.hℓ (cen (S.s i') n μ - p μ + (p μ - x μ)) (x μ - g μ)
        rw [show cen (S.s i') n μ - p μ + (p μ - x μ) + (x μ - g μ) = cen (S.s i') n μ - g μ by ring] at t2
        have e1 : |rep S.hℓ (cen (S.s i') n μ - p μ)| < 2 / 3 * S.s i' := by
          rw [show cen (S.s i') n μ - p μ = -(p μ - cen (S.s i') n μ) by ring, abs_rep_neg]
          exact (le_dT S.hℓ _ _ μ).trans_lt hpc
        have e2 : |rep S.hℓ (p μ - x μ)| ≤ 2 * S.η := (le_dT S.hℓ _ _ μ).trans hp
        have e3 : |rep S.hℓ (x μ - g μ)| ≤ S.s i' / 2 := (le_dT S.hℓ _ _ μ).trans hxb
        rw [← hr] at t2
        linarith
      -- `r = s(z + ½)` with an integer `z`, so `r = ±s/2`
      set z : ℤ := (n μ).val - m - w * S.P i' with hz
      have hrz : r = S.s i' * (z + 1 / 2) := by
        rw [hw, hz, cen, corner, hm, S.hP' i']; push_cast; ring
      have hz' : z = 0 ∨ z = -1 := by
        rw [hrz, abs_mul, abs_of_pos hs] at hrb
        have : |(z : ℝ) + 1 / 2| < 4 / 3 := by nlinarith
        rw [abs_lt] at this
        have h1 : (-2 : ℝ) < z := by linarith
        have h2 : (z : ℝ) < 1 := by linarith
        have h1' : -2 < z := by exact_mod_cast h1
        have h2' : z < 1 := by exact_mod_cast h2
        omega
      refine ⟨w, ?_⟩
      have hcg : cen (S.s i') n μ = g μ + r + w * S.ℓ := by rw [hw]; ring
      simp only [gc]
      rcases hz' with h0 | h1
      · have hr' : r = S.s i' / 2 := by rw [hrz, h0]; push_cast; ring
        have : ε μ = false := by simp only [hε, ← hr, hr', decide_eq_false_iff_not, not_lt]; positivity
        rw [this, if_neg (by simp), hcg, hr']; ring
      · have hr' : r = -(S.s i' / 2) := by rw [hrz, h1]; push_cast; ring
        have : ε μ = true := by simp only [hε, ← hr, hr', decide_eq_true_eq]; linarith
        rw [this, if_pos rfl, hcg, hr']; ring
    have heq : gcube S i' (gc S i' n ε) = gcube S i' g := by
      ext y
      simp only [gcube, Set.mem_setOf_eq]
      have : dT S.hℓ y (gc S i' n ε) = dT S.hℓ y g := by
        unfold dT
        congr 1
        funext μ
        obtain ⟨w, hw⟩ := hcong μ
        rw [hw, show y μ - (g μ + w * S.ℓ) = (y μ - g μ) + ((-w : ℤ) : ℝ) * S.ℓ by push_cast; ring,
          rep_add_int_mul]
      rw [this]
    exact ⟨ε, by rw [heq]; exact hbi, by rw [heq]; exact fun h => hxn (h hxb),
      fun h0 => by rw [heq]; exact hbD h0⟩
  -- the cubes at the scale `i` alone give `N(p)² ≥ 1`
  have hsum : ∑ n : Fin 4 → ZMod (S.P i'), (if D.InD ⟨i', n⟩ then S.φ ⟨i', n⟩ p ^ 2 else 0) = 1 := by
    rw [← torus_grid_sum S.hℓ (S.hP' i') (S.hP2 i') (S.s_pos i') p]
    refine Finset.sum_congr rfl fun n _ => ?_
    by_cases hn : S.φ ⟨i', n⟩ p = 0
    · rw [hn]; simp [Scales.φ] at hn ⊢; simp [hn]
    · rw [if_pos (hInD n hn)]; rfl
  unfold N2
  rw [Fintype.sum_sigma, ← hsum]
  exact Finset.single_le_sum (f := fun i'' : Fin (S.k + 1) => ∑ n : Fin 4 → ZMod (S.P i''),
    (if D.InD ⟨i'', n⟩ then S.φ ⟨i'', n⟩ p ^ 2 else 0))
    (fun i'' _ => Finset.sum_nonneg fun n _ => by split_ifs <;> positivity) (Finset.mem_univ i')

/-- **(i)**, the values: `h_□` has its values in `[0, 1]`. -/
theorem pu_mem (q : S.Idx) (x : E) : 0 ≤ D.hpu q x ∧ D.hpu q x ≤ 1 := by
  unfold hpu
  split_ifs
  · have h1 : 1 ≤ max (√(D.N2 x)) 1 := le_max_right _ _
    refine ⟨div_nonneg (S.φ_nonneg q x) (by linarith), ?_⟩
    rw [div_le_one (by linarith)]
    linarith [S.φ_le_one q x]
  · exact ⟨le_rfl, zero_le_one⟩

/-- **(i)**, the support: `h_□` vanishes outside the cube with the centre of `□` and the side `4s_i/3`. -/
theorem pu_support (q : S.Idx) {x : E} (h : 2 / 3 * S.s q.1 ≤ dT S.hℓ x (cen (S.s q.1) q.2)) :
    D.hpu q x = 0 := by
  unfold hpu
  split_ifs
  · rw [S.φ_eq_zero h, zero_div]
  · rfl

/-- **(i)**: `Σ_{□ ∈ 𝒟}h_□² = 1` on the Dirichlet domain. -/
theorem pu_sum {x : E} (hx : x ∈ D.ΩD) : ∑ q, D.hpu q x ^ 2 = 1 := by
  have hN := D.covering hx (p := x) (by rw [dT_self]; linarith [S.hη])
  have h1 : 1 ≤ √(D.N2 x) := by rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt hN
  have hmax : max (√(D.N2 x)) 1 = √(D.N2 x) := max_eq_left h1
  have hterm : ∀ q, D.hpu q x ^ 2 = (if D.InD q then S.φ q x ^ 2 else 0) / D.N2 x := fun q => by
    unfold hpu
    rw [hmax]
    split_ifs
    · rw [div_pow, Real.sq_sqrt (D.N2_nonneg x)]
    · simp
  simp only [hterm]
  rw [← Finset.sum_div]
  exact div_self (by have h' : 1 ≤ D.N2 x := hN; unfold N2 at h'; linarith)

end Domains

end PartitionUnity
end CoreLean

end
