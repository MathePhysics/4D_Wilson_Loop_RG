/-
`def:sequence` of BALABAN_CORE.tex (`ea68ea6e3640`) on the torus of `LatticesTorus.lean`, the statements of the
paragraph after it, and the passage to the model `ContSeq` of `lem:summation` (`SummationGeometry.lean`).

A sequence of domains (`SeqDom`) has the block size `M = L^{m_M} ≤ L^{m_𝕋}` and the separation `R`: `Ω_0 = 𝕋`, the
domains decrease, `Ω_j` is a union of cubes of the grid of side `Ma_j` for `1 ≤ j ≤ k`, `Ω_j = ∅` for `j > k`, and
`dist(Ω_j^c, Ω_{j+1}) > RMa_j` (`eq:separation`) when both sets are nonempty. Its layers are
`Γ_j = Ω_j^{(j)} \ Ω_{j+1}` (`eq:layers`), its determining set the pairs `(j, y)` with `y ∈ Γ_j`, and
`Δ(y) = B^j(y)`, `Δ̃(y) = {x ∈ T^{(0)} | |x - y|_∞ < a_j}` (`eq:cells`).

Proved: `Ω_j` is the union of the cells `Δ_j(y)`, `y ∈ T^{(j)} ∩ Ω_j` (`Ω_eq_cells`); the sets `Ω_j \ Ω_{j+1}`
are pairwise disjoint and cover the torus (`layers_cover`); the fine points of `Ω_j \ Ω_{j+1}` are those of the
blocks `B^j(y)`, `y ∈ Γ_j` (`layer_fine`); the blocks `Δ(y)`, `y ∈ 𝐁`, form a partition of the fine lattice
(`blocks_partition_fine`). Every sequence of domains is a `ContSeq` with the same domains (`toContSeq`,
`Om_eq`), so that `lem:summation` (`summation_core`) and `lem:distance` hold for it, with the weighted distance
of the core's paths on `[0, 1]`.
-/
import CoreLean.LatticesTorus
import CoreLean.SummationBound
import CoreLean.DistancePaths

open Set

noncomputable section

namespace CoreLean
namespace Lattices

variable {p : ℝ}

/-- The distance `dist(A, B)` of two sets: the infimum of `|x - y|_∞` over `x ∈ A`, `y ∈ B`. -/
def setDist (A B : Set (Tor p)) : ℝ := sInf {d | ∃ x ∈ A, ∃ y ∈ B, d = dist x y}

lemma setDist_le {A B : Set (Tor p)} {x y : Tor p} (hx : x ∈ A) (hy : y ∈ B) : setDist A B ≤ dist x y :=
  csInf_le ⟨0, by rintro _ ⟨_, _, _, _, rfl⟩; exact dist_nonneg⟩ ⟨x, hx, y, hy, rfl⟩

/-- The lattice of spacing `a` with `p = Ma`, `M ≥ 1`, is finite. -/
lemma lat_finite {a : ℝ} {M : ℕ} (hM : 0 < M) (hp : p = M * a) : (Lat p a).Finite := by
  have hC : (LatC p a).Finite := by
    refine ((Set.finite_Iio M).image fun r : ℕ => (((r : ℝ) * a : ℝ) : AddCircle p)).subset ?_
    rintro t ⟨r, rfl⟩
    have hM' : (0 : ℤ) < M := by exact_mod_cast hM
    have h0 : 0 ≤ r % (M : ℤ) := Int.emod_nonneg r hM'.ne'
    have hlt : r % (M : ℤ) < M := Int.emod_lt_of_pos r hM'
    refine ⟨(r % (M : ℤ)).toNat, by simp only [mem_Iio]; omega, ?_⟩
    have hr : (r : ℝ) * a = (((r % (M : ℤ)).toNat : ℕ) : ℝ) * a + ((r / (M : ℤ) : ℤ) : ℝ) * p := by
      have e : (((r % (M : ℤ)).toNat : ℕ) : ℝ) = ((r % (M : ℤ) : ℤ) : ℝ) := by
        rw [← Int.cast_natCast, Int.toNat_of_nonneg h0]
      rw [e, hp]
      have := Int.emod_add_mul_ediv r (M : ℤ)
      have h' : (r : ℝ) = ((r % (M : ℤ) : ℤ) : ℝ) + (M : ℝ) * ((r / (M : ℤ) : ℤ) : ℝ) := by
        exact_mod_cast this.symm
      rw [h']; ring
    rw [hr, AddCircle.coe_add, coe_int_mul_period, add_zero]
  have e : Lat p a = Set.pi univ fun _ : Fin 4 => LatC p a := by ext z; simp [Lat]
  rw [e]
  exact Set.Finite.pi fun _ => hC

/-- **`def:sequence`**: a sequence of domains with the block size `M = L^{m_M}` and the separation `R`. -/
structure SeqDom where
  L : ℕ
  L_odd : Odd L
  three_le_L : 3 ≤ L
  k : ℕ
  mT : ℕ
  one_le_mT : 1 ≤ mT
  mM : ℕ
  mM_le : mM ≤ mT
  R : ℕ
  one_le_R : 1 ≤ R
  Ω : ℕ → Set (Tor (ellT L mT))
  Ω_zero : Ω 0 = univ
  Ω_succ : ∀ j, Ω (j + 1) ⊆ Ω j
  Ω_top : ∀ j, k < j → Ω j = ∅
  cubes : ∀ j, 1 ≤ j → j ≤ k → ∃ C : Set (Tor (ellT L mT)),
    C ⊆ Lat (ellT L mT) ((L ^ mM : ℕ) * sp L k j) ∧ Ω j = ⋃ c ∈ C, cell ((L ^ mM : ℕ) * sp L k j) c
  sep : ∀ j, 1 ≤ j → j < k → (Ω j)ᶜ.Nonempty → (Ω (j + 1)).Nonempty →
    ((R * L ^ mM : ℕ) : ℝ) * sp L k j < setDist (Ω j)ᶜ (Ω (j + 1))

namespace SeqDom

variable (S : SeqDom)

/-- The lattice `T^{(j)}`. -/
abbrev TL (j : ℕ) : Set (Tor (ellT S.L S.mT)) := T S.L S.k S.mT j

/-- The layer `Γ_j = Ω_j^{(j)} \ Ω_{j+1}` (`eq:layers`). -/
def Γ (j : ℕ) : Set (Tor (ellT S.L S.mT)) := (S.Ω j ∩ S.TL j) \ S.Ω (j + 1)

/-- The determining set `𝐁 = ⨆_{j ≤ k} Γ_j`, as the pairs `(j, y)`, `y ∈ Γ_j`; `j` is the scale of `y`. -/
def detSet : Set (ℕ × Tor (ellT S.L S.mT)) := {q | q.1 ≤ S.k ∧ q.2 ∈ S.Γ q.1}

/-- `Δ(y) = B^j(y)` (`eq:cells`). -/
def Δy (q : ℕ × Tor (ellT S.L S.mT)) : Set (Tor (ellT S.L S.mT)) := Bn S.L S.k S.mT q.1 q.1 q.2

/-- `Δ̃(y) = {x ∈ T^{(0)} | |x - y|_∞ < a_j}` (`eq:cells`). -/
def Δt (q : ℕ × Tor (ellT S.L S.mT)) : Set (Tor (ellT S.L S.mT)) :=
  {x ∈ S.TL 0 | ‖x - q.2‖ < sp S.L S.k q.1}

lemma mem_Δy {q : ℕ × Tor (ellT S.L S.mT)} {x : Tor (ellT S.L S.mT)} :
    x ∈ S.Δy q ↔ x ∈ Δ S.L S.k S.mT q.1 q.2 ∧ x ∈ S.TL 0 := by
  simp only [Δy, Bn, mem_inter_iff, Nat.sub_self]

lemma Lpos : 0 < S.L := by have := S.three_le_L; omega

lemma Ω_anti {i j : ℕ} (h : i ≤ j) : S.Ω j ⊆ S.Ω i := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact (S.Ω_succ _).trans ih

/-- A cube of side `Ma_j` is the union of the cells of the points of `T^{(j)}` in it. -/
lemma cube_eq_cells {j : ℕ} (hj : j ≤ S.k) {c : Tor (ellT S.L S.mT)}
    (hc : c ∈ Lat (ellT S.L S.mT) ((S.L ^ S.mM : ℕ) * sp S.L S.k j)) :
    cell ((S.L ^ S.mM : ℕ) * sp S.L S.k j) c =
      ⋃ x ∈ S.TL j ∩ cell ((S.L ^ S.mM : ℕ) * sp S.L S.k j) c, Δ S.L S.k S.mT j x := by
  exact cell_eq_biUnion (H := Blocks.half S.L S.mM) (sp_pos S.Lpos j) (M_pos S.Lpos j) (ellT_eq S.Lpos hj)
    (by rw [Blocks.two_half_add_one S.L_odd]) hc

/-- **`Ω_j` is the union of the cells `Δ_j(y)`, `y ∈ T^{(j)} ∩ Ω_j`.** -/
theorem Ω_eq_cells {j : ℕ} (hj : j ≤ S.k) : S.Ω j = ⋃ y ∈ S.TL j ∩ S.Ω j, Δ S.L S.k S.mT j y := by
  apply Subset.antisymm
  · intro z hz
    rcases Nat.eq_zero_or_pos j with rfl | hj1
    · obtain ⟨y, hy, hzy⟩ := Δ_cover (k := S.k) (m := S.mT) S.Lpos 0 z
      exact mem_iUnion₂.2 ⟨y, ⟨hy, by rw [S.Ω_zero]; trivial⟩, hzy⟩
    · obtain ⟨C, hC, hΩ⟩ := S.cubes j hj1 hj
      have hz' := hz
      rw [hΩ] at hz'
      obtain ⟨c, hc, hzc⟩ := mem_iUnion₂.1 hz'
      rw [S.cube_eq_cells hj (hC hc)] at hzc
      obtain ⟨x, ⟨hxT, hxc⟩, hzx⟩ := mem_iUnion₂.1 hzc
      exact mem_iUnion₂.2 ⟨x, ⟨hxT, by rw [hΩ]; exact mem_iUnion₂.2 ⟨c, hc, hxc⟩⟩, hzx⟩
  · refine iUnion₂_subset fun y hy => ?_
    obtain ⟨hyT, hyΩ⟩ := hy
    rcases Nat.eq_zero_or_pos j with rfl | hj1
    · rw [S.Ω_zero]; exact subset_univ _
    · obtain ⟨C, hC, hΩ⟩ := S.cubes j hj1 hj
      have hyΩ' := hyΩ
      rw [hΩ] at hyΩ'
      obtain ⟨c, hc, hyc⟩ := mem_iUnion₂.1 hyΩ'
      calc Δ S.L S.k S.mT j y
          ⊆ ⋃ x ∈ S.TL j ∩ cell ((S.L ^ S.mM : ℕ) * sp S.L S.k j) c, Δ S.L S.k S.mT j x :=
            subset_biUnion_of_mem (u := fun x => Δ S.L S.k S.mT j x) ⟨hyT, hyc⟩
        _ = cell _ c := (S.cube_eq_cells hj (hC hc)).symm
        _ ⊆ S.Ω j := by rw [hΩ]; exact subset_biUnion_of_mem (u := fun c => cell _ c) hc

/-- The cell of a point of `T^{(j)}` in a cell of scale `j + 1` lies in that cell. -/
lemma Δ_subset_succ {j : ℕ} (hj : j + 1 ≤ S.k) {y w : Tor (ellT S.L S.mT)} (hy : y ∈ S.TL j)
    (hw : w ∈ S.TL (j + 1)) (hyw : y ∈ Δ S.L S.k S.mT (j + 1) w) :
    Δ S.L S.k S.mT j y ⊆ Δ S.L S.k S.mT (j + 1) w := by
  have e := Δ_eq_iUnion S.L_odd (Nat.le_add_left 1 j) hj hw
  simp only [Nat.add_sub_cancel] at e
  rw [e]
  exact subset_biUnion_of_mem (u := fun x => Δ S.L S.k S.mT j x)
    (show y ∈ Bn S.L S.k S.mT (j + 1) 1 w from ⟨hyw, by rw [Nat.add_sub_cancel]; exact hy⟩)

/-- Every point of `T^{(0)}` lies in the cell of exactly one point of `T^{(j)}`. -/
lemma unique_cell {j : ℕ} (hj : j ≤ S.k) {x : Tor (ellT S.L S.mT)} (hx : x ∈ S.TL 0) :
    ∃! y, y ∈ S.TL j ∧ x ∈ Δ S.L S.k S.mT j y := by
  obtain ⟨y, ⟨hy, hxy⟩, hu⟩ := Bn_partition S.L_odd (le_refl j) hj (by rw [Nat.sub_self]; exact hx)
  exact ⟨y, ⟨hy, hxy.1⟩, fun y' ⟨hy', hxy'⟩ => hu y' ⟨hy', hxy', by rw [Nat.sub_self]; exact hx⟩⟩

/-- **The sets `Ω_j \ Ω_{j+1}`, `j ≤ k`, are pairwise disjoint and cover the torus.** -/
theorem layers_cover (z : Tor (ellT S.L S.mT)) : ∃! j, j ≤ S.k ∧ z ∈ S.Ω j ∧ z ∉ S.Ω (j + 1) := by
  classical
  set j := Nat.findGreatest (fun j => z ∈ S.Ω j) S.k
  have h0 : z ∈ S.Ω 0 := by rw [S.Ω_zero]; trivial
  have hj : z ∈ S.Ω j := Nat.findGreatest_spec (P := fun j => z ∈ S.Ω j) (Nat.zero_le _) h0
  have hjk : j ≤ S.k := Nat.findGreatest_le _
  have hj1 : z ∉ S.Ω (j + 1) := by
    intro h
    rcases lt_or_ge j S.k with hlt | hge
    · exact Nat.findGreatest_is_greatest (P := fun j => z ∈ S.Ω j) (Nat.lt_succ_self j) hlt h
    · rw [S.Ω_top (j + 1) (by omega)] at h; exact h
  refine ⟨j, ⟨hjk, hj, hj1⟩, fun j' ⟨hj'k, hj', hj'1⟩ => ?_⟩
  rcases lt_trichotomy j' j with h | h | h
  · exact absurd (S.Ω_anti (by omega : j' + 1 ≤ j) hj) hj'1
  · exact h
  · exact absurd (S.Ω_anti (by omega : j + 1 ≤ j') hj') hj1

/-- **The fine points of `Ω_j \ Ω_{j+1}` are those of the blocks `B^j(y)`, `y ∈ Γ_j`.** -/
theorem layer_fine {j : ℕ} (hj : j ≤ S.k) :
    (S.Ω j \ S.Ω (j + 1)) ∩ S.TL 0 = ⋃ y ∈ S.Γ j, S.Δy (j, y) := by
  ext x
  simp only [mem_inter_iff, mem_sdiff, mem_iUnion, exists_prop, mem_Δy]
  constructor
  · rintro ⟨⟨hxΩ, hxΩ'⟩, hx0⟩
    have hxΩ2 := hxΩ
    rw [S.Ω_eq_cells hj] at hxΩ2
    obtain ⟨y, ⟨hyT, hyΩ⟩, hxy⟩ := mem_iUnion₂.1 hxΩ2
    refine ⟨y, ⟨⟨hyΩ, hyT⟩, fun hy' => hxΩ' ?_⟩, hxy, hx0⟩
    rcases lt_or_ge j S.k with hjk | hjk
    · have hy'' := hy'
      rw [S.Ω_eq_cells (j := j + 1) hjk] at hy'' ⊢
      obtain ⟨w, ⟨hwT, hwΩ⟩, hyw⟩ := mem_iUnion₂.1 hy''
      exact mem_iUnion₂.2 ⟨w, ⟨hwT, hwΩ⟩, S.Δ_subset_succ hjk hyT hwT hyw hxy⟩
    · rw [S.Ω_top (j + 1) (by omega)] at hy'; exact hy'.elim
  · rintro ⟨y, ⟨⟨hyΩ, hyT⟩, hyΩ'⟩, hxy, hx0⟩
    refine ⟨⟨?_, fun hx' => ?_⟩, hx0⟩
    · rw [S.Ω_eq_cells hj]; exact mem_iUnion₂.2 ⟨y, ⟨hyT, hyΩ⟩, hxy⟩
    · rcases lt_or_ge j S.k with hjk | hjk
      · rw [S.Ω_eq_cells (j := j + 1) hjk] at hx'
        obtain ⟨w, ⟨hwT, hwΩ⟩, hxw⟩ := mem_iUnion₂.1 hx'
        have e := Δ_eq_iUnion S.L_odd (Nat.le_add_left 1 j) hjk hwT
        simp only [Nat.add_sub_cancel] at e
        rw [e] at hxw
        obtain ⟨y', hy', hxy'⟩ := mem_iUnion₂.1 hxw
        obtain ⟨hy'w, hy'T⟩ := hy'
        rw [Nat.add_sub_cancel] at hy'T
        obtain ⟨y0, -, huniq⟩ := S.unique_cell hj hx0
        have hyy : y' = y := (huniq y' ⟨hy'T, hxy'⟩).trans (huniq y ⟨hyT, hxy⟩).symm
        apply hyΩ'
        rw [S.Ω_eq_cells (j := j + 1) hjk]
        exact mem_iUnion₂.2 ⟨w, ⟨hwT, hwΩ⟩, hyy ▸ hy'w⟩
      · rw [S.Ω_top (j + 1) (by omega)] at hx'; exact hx'.elim

/-- **The blocks `Δ(y)`, `y ∈ 𝐁`, form a partition of the fine lattice.** -/
theorem blocks_partition_fine {x : Tor (ellT S.L S.mT)} (hx : x ∈ S.TL 0) :
    ∃! q, q ∈ S.detSet ∧ x ∈ S.Δy q := by
  obtain ⟨j, ⟨hjk, hj, hj1⟩, hju⟩ := S.layers_cover x
  have hmem : x ∈ (S.Ω j \ S.Ω (j + 1)) ∩ S.TL 0 := ⟨⟨hj, hj1⟩, hx⟩
  rw [S.layer_fine hjk] at hmem
  obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.1 hmem
  refine ⟨(j, y), ⟨⟨hjk, hy⟩, hxy⟩, ?_⟩
  rintro ⟨j', y'⟩ ⟨⟨hj'k, hy'⟩, hxy'⟩
  have hfine : x ∈ (S.Ω j' \ S.Ω (j' + 1)) ∩ S.TL 0 := by
    rw [S.layer_fine hj'k]; exact mem_iUnion₂.2 ⟨y', hy', hxy'⟩
  have hjj : j' = j := hju j' ⟨hj'k, hfine.1.1, hfine.1.2⟩
  subst hjj
  obtain ⟨y0, -, huniq⟩ := S.unique_cell hjk hx
  have h1 := huniq y' ⟨hy'.1.2, (S.mem_Δy.1 hxy').1⟩
  have h2 := huniq y ⟨hy.1.2, (S.mem_Δy.1 hxy).1⟩
  rw [h1.trans h2.symm]

/-- **The ends of the bonds of a layer are points of `𝐁` once `RM ≥ L`**: for `1 ≤ j ≤ k` and two points of
`T^{(j)}` at the distance at most `a_j`, one of them in `Ω_j` and neither in `Ω_{j+1}`, each of them lies in `Γ_j`
or in `Γ_{j-1}`. -/
theorem layer_bond_ends (hRM : S.L ≤ S.R * S.L ^ S.mM) {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ S.k)
    {y y' : Tor (ellT S.L S.mT)} (hy : y ∈ S.TL j) (hy' : y' ∈ S.TL j) (hd : ‖y - y'‖ ≤ sp S.L S.k j)
    (hin : y ∈ S.Ω j ∨ y' ∈ S.Ω j) (hout : y ∉ S.Ω (j + 1)) (hout' : y' ∉ S.Ω (j + 1)) :
    ∀ w ∈ ({y, y'} : Set (Tor (ellT S.L S.mT))), w ∈ S.Γ j ∨ w ∈ S.Γ (j - 1) := by
  -- an end outside `Ω_j` next to a point of `Ω_j` lies in `Ω_{j-1}`
  have key : ∀ w v : Tor (ellT S.L S.mT), w ∈ S.TL j → w ∉ S.Ω j → v ∈ S.Ω j → dist w v ≤ sp S.L S.k j →
      w ∈ S.Γ (j - 1) := by
    intro w v hw hwΩ hv hwv
    have hj' : j - 1 + 1 = j := by omega
    have hwT : w ∈ S.TL (j - 1) := by
      have := T_subset (L := S.L) (k := S.k) (m := S.mT) (j - 1); rw [hj'] at this; exact this hw
    refine ⟨⟨?_, hwT⟩, by rw [hj']; exact hwΩ⟩
    rcases Nat.eq_zero_or_pos (j - 1) with h0 | h0
    · rw [h0, S.Ω_zero]; trivial
    by_contra hc
    have hsep := S.sep (j - 1) h0 (by omega) ⟨w, hc⟩ ⟨v, by rw [hj']; exact hv⟩
    have h1 := setDist_le (show w ∈ (S.Ω (j - 1))ᶜ from hc) (show v ∈ S.Ω (j - 1 + 1) by rw [hj']; exact hv)
    have h2 : sp S.L S.k j = (S.L : ℝ) * sp S.L S.k (j - 1) := by
      rw [sp_sub j 1 hj1]; push_cast; ring
    have h3 : (S.L : ℝ) ≤ ((S.R * S.L ^ S.mM : ℕ) : ℝ) := by exact_mod_cast hRM
    have h4 : (S.L : ℝ) * sp S.L S.k (j - 1) ≤ ((S.R * S.L ^ S.mM : ℕ) : ℝ) * sp S.L S.k (j - 1) :=
      mul_le_mul_of_nonneg_right h3 (sp_pos S.Lpos _).le
    linarith
  intro w hw
  rcases hw with rfl | hw
  · by_cases hwΩ : w ∈ S.Ω j
    · exact Or.inl ⟨⟨hwΩ, hy⟩, hout⟩
    · exact Or.inr (key w y' hy hwΩ (hin.resolve_left hwΩ) (by rw [dist_eq_norm]; exact hd))
  · rw [mem_singleton_iff] at hw
    subst hw
    by_cases hwΩ : w ∈ S.Ω j
    · exact Or.inl ⟨⟨hwΩ, hy'⟩, hout'⟩
    · exact Or.inr (key w y hy' hwΩ (hin.resolve_right hwΩ) (by rw [dist_eq_norm, norm_sub_rev]; exact hd))

/-! ### The sequence as a `ContSeq` -/

lemma finite_TL {j : ℕ} (hj : j ≤ S.k) : (S.TL j).Finite := lat_finite (M_pos S.Lpos j) (ellT_eq S.Lpos hj)

open Classical in
/-- The points of `T^{(j)} ∩ Ω_j`, as a finite set. -/
def Sset (j : ℕ) : Finset (Tor (ellT S.L S.mT)) :=
  if h : j ≤ S.k then ((S.finite_TL h).inter_of_left (S.Ω j)).toFinset else ∅

lemma sp_eq_aa (j : ℕ) : sp S.L S.k j = Summation.aa S.L S.k j := by
  simp only [sp, eta, Summation.aa, div_eq_mul_inv]

lemma cell_eq_summation (a : ℝ) (y : Tor (ellT S.L S.mT)) : Summation.cell a y = cell a y := by
  ext z
  show (∀ ν, ‖z ν - y ν‖ ≤ a / 2) ↔ z ∈ cell a y
  rw [mem_cell]
  constructor
  · intro h
    have ha : 0 ≤ a / 2 := (norm_nonneg _).trans (h 0)
    exact (pi_norm_le_iff_of_nonneg ha).2 h
  · intro h ν; exact (coord_le (z - y) ν).trans h

lemma Om_eq (j : ℕ) : Summation.Om S.L S.k S.Sset j = S.Ω j := by
  unfold Summation.Om
  split_ifs with h0 hk
  · rw [h0, S.Ω_zero]
  · rw [S.Ω_eq_cells hk]
    ext z
    simp only [mem_iUnion, exists_prop, Sset, dite_eq_left hk, Set.Finite.mem_toFinset, mem_inter_iff,
      cell_eq_summation, ← sp_eq_aa]
    constructor
    · rintro ⟨y, hy, hz⟩; exact ⟨y, hy, hz⟩
    · rintro ⟨y, hy, hz⟩; exact ⟨y, hy, hz⟩
  · rw [S.Ω_top j (by omega)]

/-- **A sequence of domains is a `ContSeq` with the same domains**, with `RM` the product of the separation and
the block size. -/
def toContSeq : Summation.ContSeq (ellT S.L S.mT) where
  L := S.L
  L_odd := S.L_odd
  three_le_L := S.three_le_L
  k := S.k
  mT := S.mT
  one_le_mT := S.one_le_mT
  p_eq := rfl
  S := S.Sset
  S_lat := fun j y hy ν => by
    unfold Sset at hy
    split_ifs at hy with hk
    · obtain ⟨hyT, -⟩ := (Set.Finite.mem_toFinset _).1 hy
      obtain ⟨r, hr⟩ := hyT ν
      exact ⟨r, by rw [hr, sp_eq_aa]⟩
    · simp at hy
  Ω_succ := fun j => by rw [S.Om_eq, S.Om_eq]; exact S.Ω_succ j
  RM := ((S.R * S.L ^ S.mM : ℕ) : ℝ)
  sep := fun i hi hik x hx y hy => by
    rw [S.Om_eq] at hx hy
    have := S.sep i hi hik ⟨x, hx⟩ ⟨y, hy⟩
    rw [mul_one, ← sp_eq_aa]
    exact this.le.trans (setDist_le hx hy)

lemma toContSeq_Ω (j : ℕ) : (S.toContSeq).Ω j = S.Ω j := S.Om_eq j

/-- The layers of the `ContSeq` are the layers `Γ_j`. -/
lemma toContSeq_Gam (j : ℕ) : (S.toContSeq).Gam j = S.Γ j := by
  ext y
  simp only [Summation.ContSeq.Gam, S.toContSeq_Ω, Γ, mem_sdiff, mem_inter_iff, mem_ofPred_eq]
  have hlat : Summation.InLat ((S.toContSeq).a j) y ↔ y ∈ S.TL j := by
    simp only [Summation.InLat, Summation.ContSeq.a, toContSeq, ← sp_eq_aa]
    rfl
  rw [hlat]
  tauto

instance : Fact (0 < ellT S.L S.mT) := ⟨by unfold ellT; have := S.Lpos; positivity⟩

/-- **`lem:summation` for a sequence of domains**, with the weighted distance `d` of the core's Lipschitz paths
on `[0, 1]`: `Σ_{y' ∈ 𝐁} e^{-αδ d(y, y')} ≤ c₁(α, δ)` for `y ∈ 𝐁` and `RM ≥ r₁(α, δ)`. -/
theorem summation_core {α δ : ℝ} (hα : 0 < α) (hδ : 0 < δ)
    (hRM : (S.toContSeq).r1 α δ ≤ ((S.R * S.L ^ S.mM : ℕ) : ℝ)) {y : Tor (ellT S.L S.mT)}
    (hy : y ∈ (S.toContSeq).BF) :
    ∑ y' ∈ (S.toContSeq).BF, Real.exp (-(α * δ * (udist (S.toContSeq).D y y').toReal)) ≤
      (S.toContSeq).c1 α δ := by
  have h := (S.toContSeq).summation hα hδ hRM hy
  simp only [Summation.ContSeq.dd] at h
  have hp : (0 : ℝ) < ellT S.L S.mT := Fact.out
  simpa only [udist_eq_wdist hp] using h

/-- The determining set of the `ContSeq` consists of the points of the layers `Γ_j`, `j ≤ k`. -/
lemma mem_BF {y : Tor (ellT S.L S.mT)} : y ∈ (S.toContSeq).BF ↔ ∃ j ≤ S.k, y ∈ S.Γ j := by
  simp only [Summation.ContSeq.BF, Finset.mem_biUnion, Finset.mem_range, Summation.ContSeq.mem_GamF,
    toContSeq_Gam]
  constructor
  · rintro ⟨j, hj, hy⟩; exact ⟨j, by change j < S.k + 1 at hj; omega, hy⟩
  · rintro ⟨j, hj, hy⟩; exact ⟨j, by change j < S.k + 1; omega, hy⟩

end SeqDom

end Lattices
end CoreLean

end
