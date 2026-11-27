import CoreLean.WilsonLoop.Geometry

/-!
# Sanity check: the geometry of the unit square

This file evaluates the definitions of `CoreLean.WilsonLoop.Geometry` on one concrete loop: the unit
square in the `0`-`1` plane on the lattice with `6` sites per side, whose bonds are the boundary
`CoreLean.plaqPath 0 1 0` of a plaquette.  [WL] states that `Λ(C) = 2` and `P(C)/r(C) = 8` for a
square.

## Main results

* `CoreLean.WilsonLoop.unitSquare_perimeter`, `CoreLean.WilsonLoop.unitSquare_corners_length`:
  `P(C) = 4`, and the square has four corners.
* `CoreLean.WilsonLoop.unitSquare_shortestSegment`: `s(C) = 1`.
* `CoreLean.WilsonLoop.unitSquare_separation`: `δ(C) = 1`.
* `CoreLean.WilsonLoop.unitSquare_cornerIsolation`,
  `CoreLean.WilsonLoop.unitSquare_isolationRatio`: `r(C) = 1/2` and `P(C)/r(C) = 8`.
* `CoreLean.WilsonLoop.unitSquare_smallDiameter`: the square has small diameter.
* `CoreLean.WilsonLoop.unitSquare_chordArcLE`,
  `CoreLean.WilsonLoop.unitSquare_two_le_of_arcDist_le`: `Λ(C) ≤ 2`, and the supremum in the
  definition of `Λ(C)` is not smaller than `2`.

## Implementation notes

* The lemmas of the first two sections hold for every loop; they are stated with the
  orientations `CoreLean.WilsonLoop.Loop.orientAt` of the bonds and their displacements
  `CoreLean.WilsonLoop.orientVec`.
* The segments of the unfolding of the square are described by
  `CoreLean.WilsonLoop.squareSideSet`: the four sides of the square, translated by the period
  vectors (`CoreLean.WilsonLoop.unitSquare_unfoldingSegments`).
-/

noncomputable section

namespace CoreLean

namespace WilsonLoop

variable {n : ℕ}

/-! ### The lift of a general loop -/

/-- The orientations of the bonds are periodic in the index, the period being the perimeter. -/
theorem Loop.orientAt_add_perimeter (C : Loop n) (i : ℕ) :
    C.orientAt (i + C.perimeter) = C.orientAt i := by
  simp [Loop.orientAt]

/-- The orientation of the `i`-th bond depends only on `i` modulo the perimeter. -/
theorem Loop.orientAt_mod_perimeter (C : Loop n) (i : ℕ) :
    C.orientAt (i % C.perimeter) = C.orientAt i := by
  simp [Loop.orientAt]

/-- The lifted site `x̃_{i+1}` is the lifted site `x̃_i` displaced by the orientation `v_i`. -/
theorem Loop.liftSite_succ (C : Loop n) (i : ℕ) :
    C.liftSite (i + 1) = C.liftSite i + orientVec (C.orientAt i) := by
  simp [Loop.liftSite, Finset.sum_range_succ, add_assoc]

/-- If the lift of a loop is closed, then its sites are periodic in the index. -/
theorem Loop.liftSite_add_perimeter (C : Loop n)
    (h : C.liftSite C.perimeter = C.liftSite 0) (i : ℕ) :
    C.liftSite (i + C.perimeter) = C.liftSite i := by
  induction i with
  | zero => rw [Nat.zero_add, h]
  | succ i ih =>
    rw [Nat.add_right_comm, C.liftSite_succ, ih, C.orientAt_add_perimeter, C.liftSite_succ]

/-- If the lift of a loop is closed, then its sites do not change when the index is increased by
a multiple of the perimeter. -/
theorem Loop.liftSite_add_mul_perimeter (C : Loop n)
    (h : C.liftSite C.perimeter = C.liftSite 0) (i m : ℕ) :
    C.liftSite (i + m * C.perimeter) = C.liftSite i := by
  induction m with
  | zero => simp
  | succ m ih => rw [Nat.succ_mul, ← Nat.add_assoc, C.liftSite_add_perimeter h, ih]

/-- If the lift of a loop is closed, then its sites depend only on the index modulo the
perimeter. -/
theorem Loop.liftSite_mod_perimeter (C : Loop n)
    (h : C.liftSite C.perimeter = C.liftSite 0) (i : ℕ) :
    C.liftSite (i % C.perimeter) = C.liftSite i := by
  have h' := C.liftSite_add_mul_perimeter h (i % C.perimeter) (i / C.perimeter)
  rw [Nat.mul_comm, Nat.mod_add_div] at h'
  exact h'.symm

/-- At an integer arc length the lifted loop is at a lifted site. -/
theorem Loop.point_natCast (C : Loop n) (i : ℕ) (μ : Fin 4) :
    C.point (i : ℝ) μ = (C.liftSite i μ : ℝ) := by
  simp [Loop.point]

/-- On the `i`-th bond, both endpoints included, the lifted loop is the affine path from the
lifted site `x̃_i` in the direction `v_i`. -/
theorem Loop.point_of_mem_Icc (C : Loop n) (i : ℕ) {t : ℝ} (h₁ : (i : ℝ) ≤ t) (h₂ : t ≤ i + 1)
    (μ : Fin 4) :
    C.point t μ = (C.liftSite i μ : ℝ) + (t - i) * (orientVec (C.orientAt i) μ : ℝ) := by
  rcases h₂.eq_or_lt with rfl | h₂
  · have h := C.point_natCast (i + 1) μ
    rw [C.liftSite_succ] at h
    simp only [Pi.add_apply, Int.cast_add, Nat.cast_add, Nat.cast_one] at h
    rw [h]
    ring
  · have hfloor : ⌊t⌋₊ = i := (Nat.floor_eq_iff (i.cast_nonneg.trans h₁)).2 ⟨h₁, h₂⟩
    have hfract : Int.fract t = t - i :=
      Int.fract_eq_iff.2 ⟨by linarith, by linarith, i, by simp⟩
    simp only [Loop.point, hfloor, hfract]

/-! ### The periodic distance and the chord–arc bound -/

/-- The periodic distance is nonnegative. -/
theorem torusDist_nonneg (N : ℕ) (x y : Fin 4 → ℝ) : 0 ≤ torusDist N x y := by
  unfold torusDist
  exact Finset.le_sup'_of_le _ (Finset.mem_univ 0) (abs_nonneg _)

/-- A real number of absolute value less than half a period has `0` as its nearest multiple of
the period. -/
theorem round_div_eq_zero {N : ℕ} {d : ℝ} (h : 2 * |d| < N) : round (d / N) = 0 := by
  have hN : (0 : ℝ) < N := lt_of_le_of_lt (by positivity) h
  obtain ⟨h₁, h₂⟩ := abs_lt.1 (show |d| < N / 2 by linarith)
  rw [round_eq_zero_iff, Set.mem_Ico]
  constructor
  · rw [le_div_iff₀ hN]
    linarith
  · rw [div_lt_iff₀ hN]
    linarith

/-- The periodic distance is at least the distance in a coordinate in which the points are
closer than half a period. -/
theorem abs_sub_le_torusDist {N : ℕ} {x y : Fin 4 → ℝ} (μ : Fin 4)
    (h : 2 * |x μ - y μ| < N) : |x μ - y μ| ≤ torusDist N x y := by
  unfold torusDist
  refine Finset.le_sup'_of_le _ (Finset.mem_univ μ) ?_
  simp [round_div_eq_zero h]

/-- The periodic distance of two points which are closer than half a period in every coordinate
is at most their `ℓ^∞`-distance. -/
theorem torusDist_le {N : ℕ} {x y : Fin 4 → ℝ} {c : ℝ} (h : ∀ μ, 2 * |x μ - y μ| < N)
    (hc : ∀ μ, |x μ - y μ| ≤ c) : torusDist N x y ≤ c := by
  unfold torusDist
  refine Finset.sup'_le _ _ fun μ _ ↦ ?_
  simpa [round_div_eq_zero (h μ)] using hc μ

/-- A bound on the chord–arc constant can be weakened. -/
theorem Loop.ChordArcLE.mono {C : Loop n} {Λ Λ' : ℝ} (h : C.ChordArcLE Λ) (hΛ : Λ ≤ Λ') :
    C.ChordArcLE Λ' :=
  ⟨h.1.trans hΛ, fun t t' h₁ h₂ h₃ h₄ ↦ (h.2 t t' h₁ h₂ h₃ h₄).trans
    (mul_le_mul_of_nonneg_right hΛ (torusDist_nonneg _ _ _))⟩

/-! ### The unit square: bonds, lifted sites, corners -/

/-- The unit square in the `0`-`1` plane on the lattice with `6` sites per side: the boundary of
the plaquette at the origin. -/
def unitSquare : Loop 6 := ⟨plaqPath 0 1 0, by decide, by decide, by decide⟩

/-- The perimeter of the unit square: `P(C) = 4`. -/
theorem unitSquare_perimeter : unitSquare.perimeter = 4 := rfl

/-- The unit square has four corners. -/
theorem unitSquare_corners_length : unitSquare.corners.length = 4 := by decide

/-- The orientations of the bonds of the unit square are `e₀, e₁, -e₀, -e₁`. -/
theorem unitSquare_orients :
    unitSquare.orients = [(0, true), (1, true), (0, false), (1, false)] := rfl

/-- The orientation of the `i`-th bond of the unit square. -/
theorem unitSquare_orientAt (i : ℕ) :
    unitSquare.orientAt i =
      [(0, true), (1, true), (0, false), (1, false)].getD (i % 4) (0, true) := rfl

/-- The lift of the unit square starts at the origin. -/
theorem unitSquare_liftSite_zero : unitSquare.liftSite 0 = ![0, 0, 0, 0] := by decide

/-- The second lifted site of the unit square. -/
theorem unitSquare_liftSite_one : unitSquare.liftSite 1 = ![1, 0, 0, 0] := by decide

/-- The third lifted site of the unit square. -/
theorem unitSquare_liftSite_two : unitSquare.liftSite 2 = ![1, 1, 0, 0] := by decide

/-- The fourth lifted site of the unit square. -/
theorem unitSquare_liftSite_three : unitSquare.liftSite 3 = ![0, 1, 0, 0] := by decide

/-- The lift of the unit square is closed. -/
theorem unitSquare_liftSite_closed :
    unitSquare.liftSite unitSquare.perimeter = unitSquare.liftSite 0 := by decide

/-- The displacement of the first bond of the unit square. -/
theorem unitSquare_orientVec_orientAt_zero :
    orientVec (unitSquare.orientAt 0) = ![1, 0, 0, 0] := by
  decide

/-- The displacement of the second bond of the unit square. -/
theorem unitSquare_orientVec_orientAt_one :
    orientVec (unitSquare.orientAt 1) = ![0, 1, 0, 0] := by
  decide

/-- The displacement of the third bond of the unit square. -/
theorem unitSquare_orientVec_orientAt_two :
    orientVec (unitSquare.orientAt 2) = ![-1, 0, 0, 0] := by
  decide

/-- The displacement of the fourth bond of the unit square. -/
theorem unitSquare_orientVec_orientAt_three :
    orientVec (unitSquare.orientAt 3) = ![0, -1, 0, 0] := by
  decide

/-- Every lifted site `x̃_i`, `i ≥ 1`, of the unit square lies over a corner. -/
theorem unitSquare_isCornerAt (i : ℕ) : unitSquare.IsCornerAt i ↔ 1 ≤ i := by
  refine ⟨fun h ↦ h.1, fun h ↦ ⟨h, ?_⟩⟩
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  rw [Nat.add_sub_cancel, unitSquare_orientAt, unitSquare_orientAt, Nat.add_mod]
  have h4 : j % 4 < 4 := Nat.mod_lt _ (by norm_num)
  generalize j % 4 = r at h4 ⊢
  interval_cases r <;> decide

/-- The segments of the unit square are its bonds. -/
theorem unitSquare_isSegment (i j : ℕ) : unitSquare.IsSegment i j ↔ 1 ≤ i ∧ j = i + 1 := by
  simp only [Loop.IsSegment, unitSquare_isCornerAt]
  constructor
  · rintro ⟨hij, hi, -, h⟩
    refine ⟨hi, ?_⟩
    by_contra hne
    exact h (i + 1) (by omega) (by omega) (by omega)
  · rintro ⟨hi, rfl⟩
    exact ⟨by omega, hi, by omega, fun m h₁ h₂ ↦ by omega⟩

/-- Every segment of the unit square has one bond. -/
theorem unitSquare_segmentLengths : unitSquare.segmentLengths = {1} := by
  ext l
  simp only [Loop.segmentLengths, Set.mem_ofPred_eq, Set.mem_singleton_iff, unitSquare_isSegment,
    unitSquare_isCornerAt]
  constructor
  · rintro (⟨i, j, ⟨-, rfl⟩, rfl⟩ | ⟨h, -⟩)
    · omega
    · exact absurd ⟨1, le_rfl⟩ h
  · rintro rfl
    exact Or.inl ⟨1, 2, ⟨le_rfl, rfl⟩, rfl⟩

/-- The shortest segment of the unit square: `s(C) = 1`. -/
theorem unitSquare_shortestSegment : unitSquare.shortestSegment = 1 := by
  rw [Loop.shortestSegment, unitSquare_segmentLengths, csInf_singleton]

/-! ### The unit square: the points of the lift -/

/-- The point at distance `s` from the initial corner of the side `a`, `a < 4`, of the unit
square in the `0`-`1` plane of `ℝ⁴`, the sides being numbered along the loop `unitSquare`. -/
def squareSide (a : ℕ) (s : ℝ) : Fin 4 → ℝ :=
  match a with
  | 0 => ![s, 0, 0, 0]
  | 1 => ![1, s, 0, 0]
  | 2 => ![1 - s, 1, 0, 0]
  | _ => ![0, 1 - s, 0, 0]

/-- The lift of the unit square on its `i`-th bond, both endpoints included. -/
theorem unitSquare_point {i : ℕ} {t : ℝ} (h₁ : (i : ℝ) ≤ t) (h₂ : t ≤ i + 1) :
    unitSquare.point t = squareSide (i % 4) (t - i) := by
  funext μ
  rw [unitSquare.point_of_mem_Icc i h₁ h₂ μ,
    ← unitSquare.liftSite_mod_perimeter unitSquare_liftSite_closed i,
    ← unitSquare.orientAt_mod_perimeter i, unitSquare_perimeter]
  have h4 : i % 4 < 4 := Nat.mod_lt _ (by norm_num)
  generalize i % 4 = r at h4 ⊢
  generalize t - (i : ℝ) = s
  interval_cases r <;> fin_cases μ <;>
    simp [squareSide, unitSquare_liftSite_zero, unitSquare_liftSite_one,
      unitSquare_liftSite_two, unitSquare_liftSite_three, unitSquare_orientVec_orientAt_zero,
      unitSquare_orientVec_orientAt_one, unitSquare_orientVec_orientAt_two,
      unitSquare_orientVec_orientAt_three] <;>
    ring

/-- The points of the sides of the unit square have their coordinates in `[0, 1]`. -/
theorem squareSide_mem_Icc {a : ℕ} (ha : a < 4) {s : ℝ} (h₀ : 0 ≤ s) (h₁ : s ≤ 1) (μ : Fin 4) :
    0 ≤ squareSide a s μ ∧ squareSide a s μ ≤ 1 := by
  interval_cases a <;> fin_cases μ <;> simp [squareSide, h₀, h₁]

/-- The final corner of a side of the unit square is the initial corner of the next side. -/
theorem squareSide_one {a : ℕ} (ha : a < 4) : squareSide a 1 = squareSide ((a + 1) % 4) 0 := by
  interval_cases a <;> simp [squareSide]

/-- Opposite sides of the unit square are at distance at least `1`. -/
theorem one_le_dist_squareSide {a : ℕ} (ha : a < 4) (s s' : ℝ) :
    1 ≤ dist (squareSide a s) (squareSide ((a + 2) % 4) s') := by
  interval_cases a
  · exact le_trans (by simp [squareSide, Real.dist_eq]) (dist_le_pi_dist _ _ 1)
  · exact le_trans (by simp [squareSide]) (dist_le_pi_dist _ _ 0)
  · exact le_trans (by simp [squareSide]) (dist_le_pi_dist _ _ 1)
  · exact le_trans (by simp [squareSide, Real.dist_eq]) (dist_le_pi_dist _ _ 0)

/-- The points of the lift of the unit square have their coordinates in `[0, 1]`. -/
theorem unitSquare_point_mem_Icc {t : ℝ} (ht : 0 ≤ t) (μ : Fin 4) :
    0 ≤ unitSquare.point t μ ∧ unitSquare.point t μ ≤ 1 := by
  have h₁ : ((⌊t⌋₊ : ℕ) : ℝ) ≤ t := Nat.floor_le ht
  have h₂ : t ≤ ⌊t⌋₊ + 1 := (Nat.lt_floor_add_one t).le
  rw [unitSquare_point h₁ h₂]
  exact squareSide_mem_Icc (Nat.mod_lt _ (by norm_num)) (by linarith) (by linarith) μ

/-- The coordinates in the `0`-`1` plane of the points of the unit square, side by side. -/
theorem unitSquare_point_cases {t : ℝ} (h₀ : 0 ≤ t) (h₄ : t < 4) :
    (t ≤ 1 ∧ unitSquare.point t 0 = t ∧ unitSquare.point t 1 = 0) ∨
    (1 ≤ t ∧ t ≤ 2 ∧ unitSquare.point t 0 = 1 ∧ unitSquare.point t 1 = t - 1) ∨
    (2 ≤ t ∧ t ≤ 3 ∧ unitSquare.point t 0 = 3 - t ∧ unitSquare.point t 1 = 1) ∨
    (3 ≤ t ∧ unitSquare.point t 0 = 0 ∧ unitSquare.point t 1 = 4 - t) := by
  have h₁ : ((⌊t⌋₊ : ℕ) : ℝ) ≤ t := Nat.floor_le h₀
  have h₂ : t ≤ ⌊t⌋₊ + 1 := (Nat.lt_floor_add_one t).le
  have hi : ⌊t⌋₊ < 4 := (Nat.floor_lt h₀).2 (by exact_mod_cast h₄)
  have hp := unitSquare_point h₁ h₂
  generalize ⌊t⌋₊ = i at h₁ h₂ hi hp
  interval_cases i
  · norm_num at h₁ h₂
    refine Or.inl ⟨h₂, ?_, ?_⟩ <;> simp [hp, squareSide]
  · norm_num at h₁ h₂
    refine Or.inr (Or.inl ⟨h₁, h₂, ?_, ?_⟩) <;> simp [hp, squareSide]
  · norm_num at h₁ h₂
    refine Or.inr (Or.inr (Or.inl ⟨h₁, h₂, ?_, ?_⟩)) <;> simp [hp, squareSide]
    ring
  · norm_num at h₁ h₂
    refine Or.inr (Or.inr (Or.inr ⟨h₁, ?_, ?_⟩)) <;> simp [hp, squareSide]
    ring

/-! ### The unit square: the segments of the unfolding and the separation -/

/-- The side `a` of the unit square, translated by the period vector `6 k`. -/
def squareSideSet (a : ℕ) (k : Fin 4 → ℤ) : Set (Fin 4 → ℝ) :=
  {x | ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ x = squareSide a s + periodShift 6 k}

/-- The points of a translated side of the unit square. -/
theorem mem_squareSideSet {a : ℕ} {k : Fin 4 → ℤ} {x : Fin 4 → ℝ} :
    x ∈ squareSideSet a k ↔ ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ x = squareSide a s + periodShift 6 k :=
  Iff.rfl

/-- The lift of the `i`-th bond of the unit square, translated by a period vector, is a
translated side of the square. -/
theorem unitSquare_segment (i : ℕ) (k : Fin 4 → ℤ) :
    {x | ∃ t : ℝ, (i : ℝ) ≤ t ∧ t ≤ ((i + 1 : ℕ) : ℝ) ∧
      x = unitSquare.point t + periodShift 6 k} = squareSideSet (i % 4) k := by
  ext x
  rw [mem_squareSideSet, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨t, h₁, h₂, rfl⟩
    push_cast at h₂
    exact ⟨t - i, by linarith, by linarith, by rw [unitSquare_point h₁ h₂]⟩
  · rintro ⟨s, h₀, h₁, rfl⟩
    refine ⟨i + s, by linarith, by push_cast; linarith, ?_⟩
    rw [unitSquare_point (by linarith) (by linarith), add_sub_cancel_left]

/-- The segments of the unfolding of the unit square are the four sides of the square,
translated by the period vectors. -/
theorem unitSquare_unfoldingSegments :
    unitSquare.unfoldingSegments =
      {S | ∃ (a : ℕ) (k : Fin 4 → ℤ), a < 4 ∧ S = squareSideSet a k} := by
  ext S
  simp only [Loop.unfoldingSegments, Set.mem_ofPred_eq, unitSquare_isSegment,
    unitSquare_isCornerAt]
  constructor
  · rintro (⟨i, j, k, ⟨-, rfl⟩, rfl⟩ | ⟨h, -⟩)
    · exact ⟨i % 4, k, Nat.mod_lt _ (by norm_num), unitSquare_segment i k⟩
    · exact absurd ⟨1, le_rfl⟩ h
  · rintro ⟨a, k, ha, rfl⟩
    refine Or.inl ⟨a + 4, a + 4 + 1, k, ⟨by omega, rfl⟩, ?_⟩
    rw [unitSquare_segment, Nat.add_mod_right, Nat.mod_eq_of_lt ha]

/-- The final corner of each translated side of the unit square is a preimage of a corner. -/
theorem squareSide_one_mem_cornerLifts {a : ℕ} (ha : a < 4) (k : Fin 4 → ℤ) :
    squareSide a 1 + periodShift 6 k ∈ unitSquare.cornerLifts := by
  have h₁ : ((a : ℕ) : ℝ) ≤ ((a + 1 : ℕ) : ℝ) := by push_cast; linarith
  have h₂ : ((a + 1 : ℕ) : ℝ) ≤ (a : ℝ) + 1 := by push_cast; linarith
  have h₃ : ((a + 1 : ℕ) : ℝ) - a = 1 := by push_cast; ring
  rw [Loop.cornerLifts, Set.mem_ofPred_eq]
  refine ⟨a + 1, k, (unitSquare_isCornerAt _).2 (by omega), ?_⟩
  rw [unitSquare_point h₁ h₂, Nat.mod_eq_of_lt ha, h₃]

/-- Translates by different period vectors of points of the unit cube are at distance at least
`5`. -/
theorem five_le_dist_add_periodShift {p q : Fin 4 → ℝ} (hp : ∀ μ, 0 ≤ p μ ∧ p μ ≤ 1)
    (hq : ∀ μ, 0 ≤ q μ ∧ q μ ≤ 1) {k k' : Fin 4 → ℤ} (hk : k ≠ k') :
    5 ≤ dist (p + periodShift 6 k) (q + periodShift 6 k') := by
  obtain ⟨μ, hμ⟩ := Function.ne_iff.1 hk
  refine le_trans ?_ (dist_le_pi_dist _ _ μ)
  simp only [Pi.add_apply, periodShift, Real.dist_eq, Nat.cast_ofNat]
  have h : (k μ : ℝ) + 1 ≤ k' μ ∨ (k' μ : ℝ) + 1 ≤ k μ := by
    rcases lt_or_gt_of_ne hμ with h | h
    · exact Or.inl (by exact_mod_cast Int.add_one_le_iff.2 h)
    · exact Or.inr (by exact_mod_cast Int.add_one_le_iff.2 h)
  rw [le_abs]
  rcases h with h | h
  · exact Or.inr (by linarith [hp μ, hq μ])
  · exact Or.inl (by linarith [hp μ, hq μ])

/-- Two distinct non-adjacent segments of the unfolding of the unit square are at distance at
least `1`. -/
theorem unitSquare_one_le_dist {S S' : Set (Fin 4 → ℝ)} (hS : S ∈ unitSquare.unfoldingSegments)
    (hS' : S' ∈ unitSquare.unfoldingSegments) (hne : S ≠ S')
    (hadj : ¬ ∃ x ∈ unitSquare.cornerLifts, x ∈ S ∧ x ∈ S') {x y : Fin 4 → ℝ} (hx : x ∈ S)
    (hy : y ∈ S') : 1 ≤ dist x y := by
  rw [unitSquare_unfoldingSegments] at hS hS'
  obtain ⟨a, k, ha, rfl⟩ := hS
  obtain ⟨b, k', hb, rfl⟩ := hS'
  obtain ⟨s, hs₀, hs₁, rfl⟩ := mem_squareSideSet.1 hx
  obtain ⟨s', hs'₀, hs'₁, rfl⟩ := mem_squareSideSet.1 hy
  by_cases hk : k = k'
  · subst hk
    rw [dist_add_right]
    have hab : a ≠ b := fun h ↦ hne (by rw [h])
    have h : b = (a + 1) % 4 ∨ a = (b + 1) % 4 ∨ b = (a + 2) % 4 := by omega
    rcases h with rfl | rfl | rfl
    · exact absurd ⟨_, squareSide_one_mem_cornerLifts ha k,
        mem_squareSideSet.2 ⟨1, zero_le_one, le_rfl, rfl⟩,
        mem_squareSideSet.2 ⟨0, le_rfl, zero_le_one, by rw [squareSide_one ha]⟩⟩ hadj
    · exact absurd ⟨_, squareSide_one_mem_cornerLifts hb k,
        mem_squareSideSet.2 ⟨0, le_rfl, zero_le_one, by rw [squareSide_one hb]⟩,
        mem_squareSideSet.2 ⟨1, zero_le_one, le_rfl, rfl⟩⟩ hadj
    · exact one_le_dist_squareSide ha s s'
  · exact le_trans (by norm_num) (five_le_dist_add_periodShift
      (squareSide_mem_Icc ha hs₀ hs₁) (squareSide_mem_Icc hb hs'₀ hs'₁) hk)

/-- The separation of the unit square: `δ(C) = 1`.  Opposite sides of one copy of the square are
at distance `1`, and sides of different copies are at distance at least `5`. -/
theorem unitSquare_separation : unitSquare.separation = 1 := by
  unfold Loop.separation
  refine IsLeast.csInf_eq ⟨?_, ?_⟩
  · have hdisj : ∀ z, z ∈ squareSideSet 0 0 → z ∉ squareSideSet 2 0 := by
      intro z hz hz'
      obtain ⟨s, -, -, rfl⟩ := mem_squareSideSet.1 hz
      obtain ⟨s', -, -, h⟩ := mem_squareSideSet.1 hz'
      have h1 : (1 : ℝ) ≤ dist (squareSide 0 s) (squareSide 2 s') :=
        one_le_dist_squareSide (a := 0) (by norm_num) s s'
      have h2 : dist (squareSide 0 s) (squareSide 2 s') = 0 := by
        rw [← dist_add_right _ _ (periodShift 6 0), h, dist_self]
      linarith
    have hx : squareSide 0 0 + periodShift 6 0 ∈ squareSideSet 0 0 :=
      mem_squareSideSet.2 ⟨0, le_rfl, zero_le_one, rfl⟩
    have hy : squareSide 2 1 + periodShift 6 0 ∈ squareSideSet 2 0 :=
      mem_squareSideSet.2 ⟨1, zero_le_one, le_rfl, rfl⟩
    refine ⟨squareSideSet 0 0, ?_, squareSideSet 2 0, ?_, ?_, ?_, _, hx, _, hy, ?_⟩
    · rw [unitSquare_unfoldingSegments]
      exact ⟨0, 0, by norm_num, rfl⟩
    · rw [unitSquare_unfoldingSegments]
      exact ⟨2, 0, by norm_num, rfl⟩
    · exact fun h ↦ hdisj _ hx (h ▸ hx)
    · rintro ⟨z, -, hz, hz'⟩
      exact hdisj z hz hz'
    · rw [dist_add_right]
      refine le_antisymm (one_le_dist_squareSide (a := 0) (by norm_num) 0 1) ?_
      rw [dist_pi_le_iff zero_le_one]
      intro μ
      fin_cases μ <;> simp [squareSide, Real.dist_eq]
  · rintro d ⟨S, hS, S', hS', hne, hadj, x, hx, y, hy, rfl⟩
    exact unitSquare_one_le_dist hS hS' hne hadj hx hy

/-! ### The unit square: corner isolation, small diameter, chord–arc constant -/

/-- The corner isolation of the unit square: `r(C) = min(1/2, 1, 4/8) = 1/2`. -/
theorem unitSquare_cornerIsolation : unitSquare.cornerIsolation = 1 / 2 := by
  rw [Loop.cornerIsolation, unitSquare_shortestSegment, unitSquare_separation,
    unitSquare_perimeter, Nat.cast_one, Nat.cast_ofNat,
    min_eq_right (by norm_num : (4 : ℝ) / 8 ≤ 1), min_eq_left (by norm_num : (1 : ℝ) / 2 ≤ 4 / 8)]

/-- The ratio of the perimeter to the corner isolation of the unit square: `P(C)/r(C) = 8`. -/
theorem unitSquare_isolationRatio : unitSquare.isolationRatio = 8 := by
  rw [Loop.isolationRatio, unitSquare_cornerIsolation, unitSquare_perimeter]
  norm_num

/-- The unit square on the lattice with `6` sites per side has small diameter. -/
theorem unitSquare_smallDiameter : unitSquare.SmallDiameter := by
  refine ⟨unitSquare_liftSite_closed, ?_⟩
  have hd : Metric.diam (unitSquare.point '' Set.Icc (0 : ℝ) (unitSquare.perimeter : ℝ)) ≤ 1 := by
    apply Metric.diam_le_of_forall_dist_le zero_le_one
    rintro _ ⟨t, ht, rfl⟩ _ ⟨t', ht', rfl⟩
    rw [dist_pi_le_iff zero_le_one]
    intro μ
    have h := unitSquare_point_mem_Icc ht.1 μ
    have h' := unitSquare_point_mem_Icc ht'.1 μ
    rw [Real.dist_eq, abs_le]
    constructor <;> linarith
  rw [Nat.cast_ofNat]
  linarith

/-- The chord–arc constant of the unit square: `Λ(C) ≤ 2`. -/
theorem unitSquare_chordArcLE : unitSquare.ChordArcLE 2 := by
  refine ⟨le_rfl, fun t t' ht₀ ht₄ ht'₀ ht'₄ ↦ ?_⟩
  rw [unitSquare_perimeter, Nat.cast_ofNat] at ht₄ ht'₄
  have hT : ∀ μ, |unitSquare.point t μ - unitSquare.point t' μ| ≤
      torusDist 6 (unitSquare.point t) (unitSquare.point t') := by
    intro μ
    apply abs_sub_le_torusDist
    have h := unitSquare_point_mem_Icc ht₀ μ
    have h' := unitSquare_point_mem_Icc ht'₀ μ
    have : |unitSquare.point t μ - unitSquare.point t' μ| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith
    push_cast
    linarith
  obtain ⟨a₀, b₀⟩ := abs_le.1 (hT 0)
  obtain ⟨a₁, b₁⟩ := abs_le.1 (hT 1)
  have hm₁ := min_le_left |t - t'| (4 - |t - t'|)
  have hm₂ := min_le_right |t - t'| (4 - |t - t'|)
  rw [Loop.arcDist, unitSquare_perimeter, Nat.cast_ofNat]
  generalize torusDist 6 (unitSquare.point t) (unitSquare.point t') = T at a₀ b₀ a₁ b₁ ⊢
  generalize min |t - t'| (4 - |t - t'|) = m at hm₁ hm₂ ⊢
  rcases unitSquare_point_cases ht₀ ht₄ with
    ⟨h, p₀, p₁⟩ | ⟨h, h', p₀, p₁⟩ | ⟨h, h', p₀, p₁⟩ | ⟨h, p₀, p₁⟩ <;>
  rcases unitSquare_point_cases ht'₀ ht'₄ with
    ⟨g, q₀, q₁⟩ | ⟨g, g', q₀, q₁⟩ | ⟨g, g', q₀, q₁⟩ | ⟨g, q₀, q₁⟩ <;>
  rw [p₀, q₀] at a₀ b₀ <;> rw [p₁, q₁] at a₁ b₁ <;>
  rcases abs_cases (t - t') with ⟨ha, -⟩ | ⟨ha, -⟩ <;> rw [ha] at hm₁ hm₂ <;> linarith

/-- The supremum in the definition of the chord–arc constant of the unit square is not smaller
than `2`: the opposite corners are at arc distance `2` and at distance `1`. -/
theorem unitSquare_two_le_of_arcDist_le {Λ : ℝ}
    (h : ∀ t t' : ℝ, 0 ≤ t → t < unitSquare.perimeter → 0 ≤ t' → t' < unitSquare.perimeter →
      unitSquare.arcDist t t' ≤ Λ * torusDist 6 (unitSquare.point t) (unitSquare.point t')) :
    2 ≤ Λ := by
  have h02 := h 0 2 le_rfl (by norm_num [unitSquare_perimeter]) (by norm_num)
    (by norm_num [unitSquare_perimeter])
  have hT : torusDist 6 (unitSquare.point 0) (unitSquare.point 2) ≤ 1 := by
    have hd : ∀ μ, |unitSquare.point 0 μ - unitSquare.point 2 μ| ≤ 1 := fun μ ↦ by
      have hb := unitSquare_point_mem_Icc (t := 0) le_rfl μ
      have hb' := unitSquare_point_mem_Icc (t := 2) (by norm_num) μ
      rw [abs_le]
      constructor <;> linarith
    exact torusDist_le (fun μ ↦ by push_cast; linarith [hd μ]) hd
  have hT₀ := torusDist_nonneg 6 (unitSquare.point 0) (unitSquare.point 2)
  have ha : unitSquare.arcDist 0 2 = 2 := by norm_num [Loop.arcDist, unitSquare_perimeter]
  rw [ha] at h02
  generalize torusDist 6 (unitSquare.point 0) (unitSquare.point 2) = T at h02 hT hT₀
  by_contra hΛ
  have h₁ : Λ * T ≤ 2 * T := mul_le_mul_of_nonneg_right (not_le.1 hΛ).le hT₀
  have h₂ : T = 1 := by linarith
  rw [h₂] at h02
  linarith [not_le.1 hΛ]

end WilsonLoop

end CoreLean
