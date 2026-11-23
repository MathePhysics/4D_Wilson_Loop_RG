/-
The grids of a torus and the linear size relative to a set, `def:localisation`(iii) of BALABAN_CORE.tex
(`63991d7efeeb`), for `lem:contracted-geometry`.

All grids live on one torus `𝕋 = (ℝ/sNℤ)⁴` (`Torus s N` of `CubeCountTorus.lean`, with the distance `|·|_∞`).
A grid (`Grid`) has the side `a` and `n` cubes in each direction, `an = sN`; its cubes are the closed
`|·|_∞`-balls of radius `a/2` about the points `π(a·c)`, `c ∈ (ℤ/nℤ)⁴`. For `a = s`, `n = N` they are the cubes
of `CubeCountTorus.lean` (`Grid.cube` is `cube s N` by definition). The grid of side `Ma_k` and the coarser grid
of side `LMa_k` of `lem:contracted-geometry` are two grids of this kind on the same torus.

The linear size relative to `D` (`eq:contracted-size`) is modelled as in `CubeCountTorus.lean`: `G` is the union of
a finite family of segments, and `|G \ D|` is replaced by the sum over the segments of the Euclidean length of the
part outside `D` (`lenOut`): the length times the Lebesgue measure of the parameters `θ ∈ [0, 1]` at which the
segment is outside `D`. A finite union of segments is the union of a family of segments which meet at most at their
end points, so that the two infima agree.

* `Grid.exists_lift`, `Grid.cube_eq_image`: the points of a cube lift to the box of side `a` about `a·c`.
* `Grid.Touch`: two cubes touch (their indices differ by at most one in each coordinate); `touch_inter`,
  `touch_of_dist_lt`, `far_of_not_touch` (cubes which do not touch have the distance `≥ a`).
* `Grid.card_near_le`: at most `81` cubes have their centre within `R < 3a/2` of a point.
* `Grid.exists_seg_adj`: two points of two equal cubes, or of two cubes which share a wall, are joined by a segment
  in their union of a length of at most `3a` (the core's `√7a < 3a`).
* `Grid.Adm`, `Grid.cost`, `Grid.d`: the admissible families, their cost, and `d(X; D)`.
* `Grid.join_pieces`: connected pieces which cover a connected union of cubes are joined by `#pieces - 1`
  segments of a length of at most `3a`.
-/
import CoreLean.CubeCountTorus
import Mathlib.MeasureTheory.Measure.Hausdorff

open Set Real MeasureTheory

noncomputable section

namespace CoreLean
namespace Contracted

/-- A segment `θ ↦ π(σ.1 + θσ.2)`, `θ ∈ [0, 1]`. -/
abbrev Seg := (Fin 4 → ℝ) × (Fin 4 → ℝ)

/-! ### Generalities -/

lemma norm_le_of_coord {v : Fin 4 → ℝ} {r : ℝ} (hr : 0 ≤ r) (h : ∀ ν, |v ν| ≤ r) : ‖v‖ ≤ r :=
  (pi_norm_le_iff_of_nonneg hr).2 fun ν => by rw [Real.norm_eq_abs]; exact h ν

lemma eu_le_of_sq {v : Fin 4 → ℝ} {c : ℝ} (hc : 0 ≤ c) (h : ∑ ν, v ν ^ 2 ≤ c ^ 2) : eu v ≤ c := by
  unfold eu
  calc Real.sqrt (∑ ν, v ν ^ 2) ≤ Real.sqrt (c ^ 2) := Real.sqrt_le_sqrt h
    _ = c := Real.sqrt_sq hc

lemma sq_le_of_abs {x b : ℝ} (h : |x| ≤ b) : x ^ 2 ≤ b ^ 2 := by
  rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg x) h 2

/-- The segment reduced to the point `π(z)`. -/
def pt (z : Fin 4 → ℝ) : Seg := (z, 0)

lemma segSet_pt {s : ℝ} {N : ℕ} (z : Fin 4 → ℝ) : segSet s N (pt z) = {proj s N z} := by
  ext x
  simp only [segSet, pt, smul_zero, add_zero, mem_image, mem_singleton_iff]
  constructor
  · rintro ⟨-, -, rfl⟩; rfl
  · rintro rfl; exact ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩

lemma eu_zero : eu (0 : Fin 4 → ℝ) = 0 := by simp [eu]

lemma start_mem_segSet {s : ℝ} {N : ℕ} (σ : Seg) : proj s N σ.1 ∈ segSet s N σ :=
  ⟨0, ⟨le_rfl, zero_le_one⟩, by simp⟩

lemma end_mem_segSet {s : ℝ} {N : ℕ} (x y : Fin 4 → ℝ) : proj s N y ∈ segSet s N (x, y - x) :=
  ⟨1, ⟨zero_le_one, le_rfl⟩, by simp⟩

/-- A preconnected set with finitely many preconnected sets which meet it has a preconnected union. -/
lemma isPreconnected_hub {α ι : Type*} [TopologicalSpace α] {H : Set α} (hH : IsPreconnected H)
    (I : Finset ι) (A : ι → Set α) (hA : ∀ i ∈ I, IsPreconnected (A i))
    (hm : ∀ i ∈ I, (A i ∩ H).Nonempty) : IsPreconnected (H ∪ ⋃ i ∈ I, A i) := by
  classical
  induction I using Finset.induction_on with
  | empty => simpa using hH
  | insert i I hi ih =>
    have ih' := ih (fun j hj => hA j (Finset.mem_insert_of_mem hj))
      (fun j hj => hm j (Finset.mem_insert_of_mem hj))
    have e : H ∪ ⋃ j ∈ insert i I, A j = (H ∪ ⋃ j ∈ I, A j) ∪ A i := by
      rw [Finset.set_biUnion_insert]; ext; simp only [mem_union]; tauto
    rw [e]
    obtain ⟨x, hx1, hx2⟩ := hm i (Finset.mem_insert_self i I)
    exact ih'.union x (Or.inl hx2) hx1 (hA i (Finset.mem_insert_self i I))

/-! ### The part of a segment outside a set -/

/-- The Euclidean length of the part of the segment `σ` outside `F`. -/
def lenOut (s : ℝ) (N : ℕ) (F : Set (Torus s N)) (σ : Seg) : ℝ :=
  eu σ.2 * (volume {θ ∈ Icc (0 : ℝ) 1 | proj s N (σ.1 + θ • σ.2) ∉ F}).toReal

section LenOut

variable {s : ℝ} {N : ℕ}

lemma volume_out_le (F : Set (Torus s N)) (σ : Seg) :
    volume {θ ∈ Icc (0 : ℝ) 1 | proj s N (σ.1 + θ • σ.2) ∉ F} ≤ 1 := by
  calc volume {θ ∈ Icc (0 : ℝ) 1 | proj s N (σ.1 + θ • σ.2) ∉ F} ≤ volume (Icc (0 : ℝ) 1) :=
        measure_mono fun θ hθ => hθ.1
    _ = 1 := by simp

lemma volume_out_ne_top (F : Set (Torus s N)) (σ : Seg) :
    volume {θ ∈ Icc (0 : ℝ) 1 | proj s N (σ.1 + θ • σ.2) ∉ F} ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (volume_out_le F σ)

lemma lenOut_nonneg (F : Set (Torus s N)) (σ : Seg) : 0 ≤ lenOut s N F σ :=
  mul_nonneg (eu_nonneg _) ENNReal.toReal_nonneg

lemma lenOut_le_eu (F : Set (Torus s N)) (σ : Seg) : lenOut s N F σ ≤ eu σ.2 := by
  unfold lenOut
  refine mul_le_of_le_one_right (eu_nonneg _) ?_
  have := ENNReal.toReal_mono ENNReal.one_ne_top (volume_out_le F σ)
  simpa using this

lemma lenOut_anti {F F' : Set (Torus s N)} (h : F ⊆ F') (σ : Seg) : lenOut s N F' σ ≤ lenOut s N F σ := by
  unfold lenOut
  refine mul_le_mul_of_nonneg_left ?_ (eu_nonneg _)
  exact ENNReal.toReal_mono (volume_out_ne_top F σ) (measure_mono fun θ hθ => ⟨hθ.1, fun h' => hθ.2 (h h')⟩)

lemma lenOut_pt (F : Set (Torus s N)) (z : Fin 4 → ℝ) : lenOut s N F (pt z) = 0 := by
  simp [lenOut, pt, eu_zero]

end LenOut

/-! ### Grids -/

/-- A grid of the torus `Torus s N`: side `a`, `n` cubes in each direction, `an = sN`. -/
structure Grid where
  s : ℝ
  N : ℕ
  a : ℝ
  n : ℕ
  ha : 0 < a
  hP : a * n = s * N
  hn : NeZero n

namespace Grid

variable (g : Grid)

instance : NeZero g.n := g.hn

/-- The indices of the cubes. -/
abbrev Idx := Fin 4 → ZMod g.n

/-- The torus. -/
abbrev T := Torus g.s g.N

/-- The representative `a · c` of the centre of the cube `c`. -/
def lift (c : g.Idx) : Fin 4 → ℝ := fun ν => g.a * ((c ν).val : ℝ)

/-- The centre of the cube `c`. -/
def centre (c : g.Idx) : g.T := proj g.s g.N (g.lift c)

/-- The cube `{z | |z - π(a·c)|_∞ ≤ a/2}`. -/
def cube (c : g.Idx) : Set g.T := Metric.closedBall (g.centre c) (g.a / 2)

/-- The union of the cubes of `X`. -/
def cubes (X : Finset g.Idx) : Set g.T := ⋃ c ∈ X, g.cube c

variable {g}

lemma centre_mem_cube (c : g.Idx) : g.centre c ∈ g.cube c :=
  Metric.mem_closedBall_self (by linarith [g.ha])

lemma cube_subset_cubes {X : Finset g.Idx} {c : g.Idx} (hc : c ∈ X) : g.cube c ⊆ g.cubes X :=
  fun _ hx => mem_biUnion hc hx

lemma cubes_mono {X Y : Finset g.Idx} (h : X ⊆ Y) : g.cubes X ⊆ g.cubes Y :=
  biUnion_subset_biUnion_left fun _ hc => h hc

/-- Integer multiples of `a` project to the centres of the cubes of their classes. -/
lemma proj_int (k : Fin 4 → ℤ) :
    proj g.s g.N (fun ν => g.a * (k ν : ℝ)) = g.centre (fun ν => (k ν : ZMod g.n)) := by
  funext ν
  simp only [centre, lift, proj]
  rw [← sub_eq_zero, ← AddCircle.coe_sub, AddCircle.coe_eq_zero_iff]
  refine ⟨k ν / g.n, ?_⟩
  have h := ZMod.val_intCast (n := g.n) (k ν)
  have h2 : (((k ν : ZMod g.n).val : ℕ) : ℝ) = ((k ν % g.n : ℤ) : ℝ) := by rw [← h]; norm_cast
  have h3 : ((k ν : ℤ) : ℝ) = ((k ν % g.n : ℤ) : ℝ) + g.n * ((k ν / g.n : ℤ) : ℝ) := by
    exact_mod_cast (Int.emod_add_mul_ediv (k ν) g.n).symm
  rw [zsmul_eq_mul, h2, h3, ← g.hP]
  ring

/-- `π(a·c + a·δ)` is the centre of `c + δ`. -/
lemma centre_add_int (c : g.Idx) (δ : Fin 4 → ℤ) :
    g.centre (c + fun ν => (δ ν : ZMod g.n)) = proj g.s g.N (g.lift c + fun ν => g.a * (δ ν : ℝ)) := by
  have := proj_int (g := g) (fun ν => ((c ν).val : ℤ) + δ ν)
  have e1 : (fun ν => g.a * ((((c ν).val : ℤ) + δ ν : ℤ) : ℝ)) = g.lift c + fun ν => g.a * (δ ν : ℝ) := by
    funext ν; simp only [lift, Pi.add_apply]; push_cast; ring
  have e2 : (fun ν => ((((c ν).val : ℤ) + δ ν : ℤ) : ZMod g.n)) = c + fun ν => (δ ν : ZMod g.n) := by
    funext ν; simp only [Pi.add_apply]; push_cast; rw [ZMod.natCast_zmod_val]
  rw [e1, e2] at this
  exact this.symm

/-- Every point of the torus lifts to a point at the distance `dist (x ν) (π y ν)` from `y` in each coordinate. -/
lemma exists_lift (x : g.T) (y : Fin 4 → ℝ) :
    ∃ z : Fin 4 → ℝ, proj g.s g.N z = x ∧
      ∀ ν, |z ν - y ν| = dist (x ν) ((y ν : ℝ) : AddCircle (g.s * g.N)) := by
  choose x0 hx0 using fun ν => QuotientAddGroup.mk_surjective (x ν)
  set P := g.s * (g.N : ℝ)
  refine ⟨fun ν => x0 ν - round (P⁻¹ * (x0 ν - y ν)) * P, ?_, fun ν => ?_⟩
  · funext ν
    simp only [proj]
    rw [AddCircle.coe_sub]
    have : ((round (P⁻¹ * (x0 ν - y ν)) * P : ℝ) : AddCircle P) = 0 := by
      rw [AddCircle.coe_eq_zero_iff]; exact ⟨round (P⁻¹ * (x0 ν - y ν)), by rw [zsmul_eq_mul]⟩
    rw [this, sub_zero]; exact hx0 ν
  · rw [dist_eq_norm, ← hx0 ν]
    change |x0 ν - round (P⁻¹ * (x0 ν - y ν)) * P - y ν| = ‖((x0 ν : ℝ) : AddCircle P) - ((y ν : ℝ) : AddCircle P)‖
    rw [← AddCircle.coe_sub, AddCircle.norm_eq]
    congr 1; ring

lemma exists_lift_near {x : g.T} {y : Fin 4 → ℝ} {r : ℝ} (h : dist x (proj g.s g.N y) ≤ r) :
    ∃ z : Fin 4 → ℝ, proj g.s g.N z = x ∧ ‖z - y‖ ≤ r := by
  obtain ⟨z, hz, hd⟩ := exists_lift (g := g) x y
  refine ⟨z, hz, norm_le_of_coord (dist_nonneg.trans h) fun ν => ?_⟩
  rw [Pi.sub_apply, hd]
  exact (dist_le_pi_dist _ _ ν).trans h

lemma lift_of_mem_cube {x : g.T} {c : g.Idx} (hx : x ∈ g.cube c) :
    ∃ z : Fin 4 → ℝ, proj g.s g.N z = x ∧ ‖z - g.lift c‖ ≤ g.a / 2 :=
  exists_lift_near (Metric.mem_closedBall.1 hx)

lemma proj_mem_cube {z : Fin 4 → ℝ} {c : g.Idx} (h : ‖z - g.lift c‖ ≤ g.a / 2) :
    proj g.s g.N z ∈ g.cube c :=
  Metric.mem_closedBall.2 ((dist_proj_le _ _).trans (by rw [dist_eq_norm]; exact h))

lemma proj_mem_closedBall {z y : Fin 4 → ℝ} {r : ℝ} (h : ‖z - y‖ ≤ r) :
    proj g.s g.N z ∈ Metric.closedBall (proj g.s g.N y) r :=
  Metric.mem_closedBall.2 ((dist_proj_le _ _).trans (by rw [dist_eq_norm]; exact h))

lemma cube_eq_image (c : g.Idx) :
    g.cube c = proj g.s g.N '' Metric.closedBall (g.lift c) (g.a / 2) := by
  ext x
  constructor
  · intro hx
    obtain ⟨z, rfl, hz⟩ := lift_of_mem_cube hx
    exact ⟨z, by rw [Metric.mem_closedBall, dist_eq_norm]; exact hz, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact proj_mem_cube (by rw [Metric.mem_closedBall, dist_eq_norm] at hz; exact hz)

lemma isPreconnected_cube (c : g.Idx) : IsPreconnected (g.cube c) := by
  rw [cube_eq_image]
  exact (convex_closedBall _ _).isPreconnected.image _ lipschitzWith_proj.continuous.continuousOn

/-! ### Touching cubes -/

/-- Two cubes touch: their indices differ by at most one in each coordinate. -/
def Touch (c c' : g.Idx) : Prop := ∀ ν, c' ν - c ν = -1 ∨ c' ν - c ν = 0 ∨ c' ν - c ν = 1

lemma touch_refl (c : g.Idx) : Touch c c := fun ν => Or.inr (Or.inl (sub_self _))

lemma touch_symm {c c' : g.Idx} (h : Touch c c') : Touch c' c := fun ν => by
  rcases h ν with h | h | h
  · right; right; rw [← neg_sub, h, neg_neg]
  · right; left; rw [← neg_sub, h, neg_zero]
  · left; rw [← neg_sub, h]

lemma touch_iff_int {c c' : g.Idx} :
    Touch c c' ↔ ∃ δ : Fin 4 → ℤ, (∀ ν, |δ ν| ≤ 1) ∧ c' = c + fun ν => (δ ν : ZMod g.n) := by
  constructor
  · intro h
    have : ∀ ν, ∃ t : ℤ, |t| ≤ 1 ∧ c' ν = c ν + (t : ZMod g.n) := fun ν => by
      rcases h ν with h | h | h
      · exact ⟨-1, by norm_num, eq_add_of_sub_eq' (by push_cast; exact h)⟩
      · exact ⟨0, by norm_num, by rw [sub_eq_zero.1 h]; simp⟩
      · exact ⟨1, by norm_num, eq_add_of_sub_eq' (by push_cast; exact h)⟩
    choose δ hδ1 hδ2 using this
    exact ⟨δ, hδ1, funext hδ2⟩
  · rintro ⟨δ, hδ, rfl⟩ ν
    simp only [Pi.add_apply, add_sub_cancel_left]
    have := hδ ν
    rcases (by rw [abs_le] at this; omega : δ ν = -1 ∨ δ ν = 0 ∨ δ ν = 1) with h | h | h <;>
      simp [h]

/-- Touching cubes have a point in common. -/
lemma touch_inter {c c' : g.Idx} (h : Touch c c') : (g.cube c ∩ g.cube c').Nonempty := by
  obtain ⟨δ, hδ, rfl⟩ := touch_iff_int.1 h
  have ha := g.ha
  refine ⟨proj g.s g.N (g.lift c + fun ν => g.a / 2 * (δ ν : ℝ)), ?_, ?_⟩
  · refine proj_mem_cube (norm_le_of_coord (by linarith) fun ν => ?_)
    simp only [Pi.sub_apply, Pi.add_apply, add_sub_cancel_left, abs_mul, abs_of_pos (by linarith : 0 < g.a / 2)]
    have : |(δ ν : ℝ)| ≤ 1 := by exact_mod_cast hδ ν
    nlinarith
  · rw [cube, centre_add_int]
    refine proj_mem_closedBall (norm_le_of_coord (by linarith) fun ν => ?_)
    simp only [Pi.sub_apply, Pi.add_apply]
    have : |(δ ν : ℝ)| ≤ 1 := by exact_mod_cast hδ ν
    rw [show g.lift c ν + g.a / 2 * (δ ν : ℝ) - (g.lift c ν + g.a * (δ ν : ℝ)) = -(g.a / 2) * δ ν by ring,
      abs_mul, abs_neg, abs_of_pos (by linarith : 0 < g.a / 2)]
    nlinarith

lemma dist_centre_le_of_touch {c c' : g.Idx} (h : Touch c c') : dist (g.centre c) (g.centre c') ≤ g.a := by
  obtain ⟨δ, hδ, rfl⟩ := touch_iff_int.1 h
  rw [centre_add_int, centre, dist_comm]
  refine (dist_proj_le _ _).trans ?_
  rw [dist_eq_norm, add_sub_cancel_left]
  refine norm_le_of_coord g.ha.le fun ν => ?_
  rw [abs_mul, abs_of_pos g.ha]
  have : |(δ ν : ℝ)| ≤ 1 := by exact_mod_cast hδ ν
  nlinarith [g.ha]

/-- Two values of the circle at the distance `< 2a` of the centres `a·u`, `a·w` give indices which differ by at most
one. -/
lemma coord_touch {u w : ZMod g.n}
    (h : dist (((g.a * (w.val : ℝ) : ℝ)) : AddCircle (g.s * g.N)) ((g.a * (u.val : ℝ) : ℝ)) < 2 * g.a) :
    u - w = -1 ∨ u - w = 0 ∨ u - w = 1 := by
  have ha := g.ha
  rw [dist_eq_norm, ← AddCircle.coe_sub, AddCircle.norm_eq] at h
  set r := round ((g.s * g.N)⁻¹ * (g.a * (w.val : ℝ) - g.a * (u.val : ℝ)))
  set t : ℤ := (u.val : ℤ) - w.val + r * g.n
  have ht : g.a * (w.val : ℝ) - g.a * (u.val : ℝ) - r * (g.s * g.N) = -(g.a * t) := by
    simp only [t]; rw [← g.hP]; push_cast; ring
  rw [ht, abs_neg, abs_mul, abs_of_pos ha] at h
  have h2 : |(t : ℝ)| < 2 := by nlinarith
  have h3 : |t| < 2 := by exact_mod_cast h2
  have hut : u - w = (t : ZMod g.n) := by
    simp only [t]; push_cast; rw [ZMod.natCast_self, mul_zero, add_zero, ZMod.natCast_zmod_val,
      ZMod.natCast_zmod_val]
  rw [hut]
  rcases (by rw [abs_lt] at h3; omega : t = -1 ∨ t = 0 ∨ t = 1) with h | h | h <;> simp [h]

/-- Cubes whose centres are at a distance `< 2a` touch. -/
lemma touch_of_dist_lt {c c' : g.Idx} (h : dist (g.centre c) (g.centre c') < 2 * g.a) : Touch c c' :=
  fun ν => coord_touch ((dist_le_pi_dist _ _ ν).trans_lt h)

/-- Cubes which do not touch are at a distance `≥ a`. -/
lemma far_of_not_touch {c c' : g.Idx} (h : ¬ Touch c c') {x z : g.T} (hx : x ∈ g.cube c)
    (hz : z ∈ g.cube c') : g.a ≤ dist x z := by
  by_contra hlt
  push_neg at hlt
  refine h (touch_of_dist_lt ?_)
  have h1 := Metric.mem_closedBall.1 hx
  have h2 := Metric.mem_closedBall.1 hz
  calc dist (g.centre c) (g.centre c') ≤ dist (g.centre c) x + dist x z + dist z (g.centre c') :=
        dist_triangle4 _ _ _ _
    _ < g.a / 2 + g.a + g.a / 2 := by rw [dist_comm] at h1; linarith
    _ = 2 * g.a := by ring

/-! ### Counting the cubes near a point -/

/-- At most three cubes of a circle have their centre within `R < 3a/2` of a point. -/
lemma card_near_coord (q : AddCircle (g.s * g.N)) {R : ℝ} (hR : R < 3 * g.a / 2) :
    (Finset.univ.filter fun k : ZMod g.n =>
      dist ((g.a * (k.val : ℝ) : ℝ) : AddCircle (g.s * g.N)) q ≤ R).card ≤ 3 := by
  have ha := g.ha
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
  set lo := ⌈x / g.a - R / g.a⌉
  set hi := ⌊x / g.a + R / g.a⌋
  have hsub : (Finset.univ.filter fun k : ZMod g.n =>
      dist ((g.a * (k.val : ℝ) : ℝ) : AddCircle (g.s * g.N)) (x : AddCircle (g.s * g.N)) ≤ R) ⊆
      (Finset.Icc lo hi).image (Int.cast : ℤ → ZMod g.n) := by
    intro k hk
    rw [Finset.mem_filter] at hk
    have hd := hk.2
    rw [dist_eq_norm, ← AddCircle.coe_sub, AddCircle.norm_eq] at hd
    set m := round ((g.s * g.N)⁻¹ * (g.a * (k.val : ℝ) - x))
    set j : ℤ := (k.val : ℤ) - m * g.n
    have hj : |g.a * (j : ℝ) - x| ≤ R := by
      have : g.a * (j : ℝ) - x = g.a * (k.val : ℝ) - x - m * (g.s * g.N) := by
        simp only [j]; rw [← g.hP]; push_cast; ring
      rw [this]; exact hd
    rw [abs_le] at hj
    refine Finset.mem_image.2 ⟨j, Finset.mem_Icc.2 ⟨?_, ?_⟩, ?_⟩
    · rw [Int.ceil_le, ← sub_div, div_le_iff₀ ha]; nlinarith
    · rw [Int.le_floor, ← add_div, le_div_iff₀ ha]; nlinarith
    · simp only [j]; push_cast; simp
  refine (Finset.card_le_card hsub).trans (Finset.card_image_le.trans ?_)
  rw [Int.card_Icc]
  have hlo : x / g.a - R / g.a ≤ lo := Int.le_ceil _
  have hhi : (hi : ℝ) ≤ x / g.a + R / g.a := Int.floor_le _
  have hR' : 2 * (R / g.a) < 3 := by rw [mul_div_assoc', div_lt_iff₀ ha]; linarith
  have hab : ((hi - lo : ℤ) : ℝ) < 3 := by push_cast; linarith
  have : hi - lo < 3 := by exact_mod_cast hab
  omega

/-- At most `81` cubes have their centre within `R < 3a/2` of a point. -/
lemma card_near_le (q : g.T) {R : ℝ} (hR : R < 3 * g.a / 2) :
    (Finset.univ.filter fun c : g.Idx => dist (g.centre c) q ≤ R).card ≤ 81 := by
  have hsub : (Finset.univ.filter fun c : g.Idx => dist (g.centre c) q ≤ R) ⊆
      Fintype.piFinset fun ν => Finset.univ.filter fun k : ZMod g.n =>
        dist ((g.a * (k.val : ℝ) : ℝ) : AddCircle (g.s * g.N)) (q ν) ≤ R := by
    intro c hc
    rw [Fintype.mem_piFinset]
    intro ν
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
    exact (dist_le_pi_dist _ _ ν).trans hc
  refine (Finset.card_le_card hsub).trans ?_
  rw [Fintype.card_piFinset]
  calc ∏ ν, _ ≤ 3 ^ (Finset.univ : Finset (Fin 4)).card :=
        Finset.prod_le_pow_card _ _ _ fun ν _ => card_near_coord (q ν) hR
    _ = 81 := by simp

/-! ### Segments in one cube and in two cubes which share a wall -/

/-- Two points of a cube are joined by a segment in the cube of a length of at most `2a`. -/
lemma exists_seg_cube {c : g.Idx} {x y : g.T} (hx : x ∈ g.cube c) (hy : y ∈ g.cube c) :
    ∃ σ : Seg, segSet g.s g.N σ ⊆ g.cube c ∧ x ∈ segSet g.s g.N σ ∧ y ∈ segSet g.s g.N σ ∧
      eu σ.2 ≤ 2 * g.a := by
  have ha := g.ha
  obtain ⟨x', rfl, hx'⟩ := lift_of_mem_cube hx
  obtain ⟨y', rfl, hy'⟩ := lift_of_mem_cube hy
  refine ⟨(x', y' - x'), ?_, start_mem_segSet _, end_mem_segSet _ _, ?_⟩
  · rintro _ ⟨θ, ⟨h0, h1⟩, rfl⟩
    refine proj_mem_cube ?_
    have hc := (convex_closedBall (g.lift c) (g.a / 2))
      (by rw [Metric.mem_closedBall, dist_eq_norm]; exact hx')
      (by rw [Metric.mem_closedBall, dist_eq_norm]; exact hy') (by linarith : 0 ≤ 1 - θ) h0
      (by ring : 1 - θ + θ = 1)
    rw [Metric.mem_closedBall, dist_eq_norm] at hc
    convert hc using 2
    module
  · refine eu_le_of_sq (by linarith) ?_
    have hb : ∀ ν, |(y' - x') ν| ≤ g.a := fun ν => by
      have h1 := (norm_le_pi_norm (y' - g.lift c) ν).trans hy'
      have h2 := (norm_le_pi_norm (x' - g.lift c) ν).trans hx'
      simp only [Real.norm_eq_abs, Pi.sub_apply] at h1 h2 ⊢
      calc |y' ν - x' ν| = |(y' ν - g.lift c ν) - (x' ν - g.lift c ν)| := by ring_nf
        _ ≤ |y' ν - g.lift c ν| + |x' ν - g.lift c ν| := abs_sub _ _
        _ ≤ g.a := by linarith
    rw [Fin.sum_univ_four]
    nlinarith [sq_le_of_abs (hb 0), sq_le_of_abs (hb 1), sq_le_of_abs (hb 2), sq_le_of_abs (hb 3)]

/-- One coordinate of a segment from a point near `l` to a point near `l + ea`. -/
lemma one_dim {l u v e θ a : ℝ} (ha : 0 < a) (he : e = 1 ∨ e = -1) (hu : |u - l| ≤ a / 2)
    (hv : |v - (l + e * a)| ≤ a / 2) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    |(1 - θ) * u + θ * v - l| ≤ a / 2 ∨ |(1 - θ) * u + θ * v - (l + e * a)| ≤ a / 2 := by
  rw [abs_le] at hu hv
  have h1θ : 0 ≤ 1 - θ := by linarith
  have p1 := mul_nonneg h1θ (by linarith : 0 ≤ u - l + a / 2)
  have p2 := mul_nonneg h1θ (by linarith : 0 ≤ a / 2 - (u - l))
  rcases he with rfl | rfl
  · have p3 := mul_nonneg h0 (by linarith : 0 ≤ v - (l + 1 * a) + a / 2)
    have p4 := mul_nonneg h0 (by linarith : 0 ≤ a / 2 - (v - (l + 1 * a)))
    by_cases hc : (1 - θ) * u + θ * v - l ≤ a / 2
    · left; rw [abs_le]; constructor <;> nlinarith
    · right; rw [abs_le]; constructor <;> nlinarith
  · have p3 := mul_nonneg h0 (by linarith : 0 ≤ v - (l + -1 * a) + a / 2)
    have p4 := mul_nonneg h0 (by linarith : 0 ≤ a / 2 - (v - (l + -1 * a)))
    by_cases hc : -(a / 2) ≤ (1 - θ) * u + θ * v - l
    · left; rw [abs_le]; constructor <;> nlinarith
    · right; rw [abs_le]; constructor <;> nlinarith

/-- The convex combination of two numbers within `r` of `l` is within `r` of `l`. -/
lemma convex_coord {l u v θ r : ℝ} (hu : |u - l| ≤ r) (hv : |v - l| ≤ r) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    |(1 - θ) * u + θ * v - l| ≤ r := by
  rw [show (1 - θ) * u + θ * v - l = (1 - θ) * (u - l) + θ * (v - l) by ring]
  calc |(1 - θ) * (u - l) + θ * (v - l)| ≤ |(1 - θ) * (u - l)| + |θ * (v - l)| := abs_add_le _ _
    _ = (1 - θ) * |u - l| + θ * |v - l| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (by linarith : 0 ≤ 1 - θ), abs_of_nonneg h0]
    _ ≤ (1 - θ) * r + θ * r := by gcongr <;> linarith
    _ = r := by ring

/-- The centre of a neighbour across a wall. -/
lemma centre_wallNbr (c : g.Idx) (p : Fin 4 × Bool) :
    g.centre (wallNbr (ZMod g.n) c p) =
      proj g.s g.N (g.lift c + fun ν => g.a * ((if p.2 then (1 : ℝ) else -1) * (Pi.single p.1 (1 : ℝ) : Fin 4 → ℝ) ν)) := by
  set δ : Fin 4 → ℤ := fun ν => (if p.2 then (1 : ℤ) else -1) * (Pi.single p.1 (1 : ℤ) : Fin 4 → ℤ) ν
  have h1 : wallNbr (ZMod g.n) c p = c + fun ν => (δ ν : ZMod g.n) := by
    funext ν
    simp only [wallNbr, δ, Pi.add_apply]
    by_cases hν : ν = p.1
    · subst hν; cases p.2 <;> simp [sub_eq_add_neg]
    · cases p.2 <;> simp [Pi.single_apply, hν]
  have h2 : (fun ν => g.a * ((if p.2 then (1 : ℝ) else -1) * (Pi.single p.1 (1 : ℝ) : Fin 4 → ℝ) ν)) =
      fun ν => g.a * (δ ν : ℝ) := by
    funext ν
    simp only [δ]
    by_cases hν : ν = p.1
    · subst hν; cases p.2 <;> simp
    · cases p.2 <;> simp [Pi.single_apply, hν]
  rw [h1, centre_add_int, h2]

/-- Two points of two cubes which share a wall are joined by a segment in their union of a length of at most
`3a`. -/
lemma exists_seg_wall {c : g.Idx} {p : Fin 4 × Bool} {x y : g.T} (hx : x ∈ g.cube c)
    (hy : y ∈ g.cube (wallNbr (ZMod g.n) c p)) :
    ∃ σ : Seg, segSet g.s g.N σ ⊆ g.cube c ∪ g.cube (wallNbr (ZMod g.n) c p) ∧ x ∈ segSet g.s g.N σ ∧
      y ∈ segSet g.s g.N σ ∧ eu σ.2 ≤ 3 * g.a := by
  have ha := g.ha
  set e : ℝ := if p.2 then 1 else -1 with he_def
  have he : e = 1 ∨ e = -1 := by by_cases hb : p.2 = true <;> simp [he_def, hb]
  set w : Fin 4 → ℝ := g.lift c + fun ν => g.a * (e * (Pi.single p.1 (1 : ℝ) : Fin 4 → ℝ) ν) with hw
  have hcw : g.cube (wallNbr (ZMod g.n) c p) = Metric.closedBall (proj g.s g.N w) (g.a / 2) := by
    rw [cube, centre_wallNbr]
  obtain ⟨x', rfl, hx'⟩ := lift_of_mem_cube hx
  rw [hcw] at hy
  obtain ⟨y', rfl, hy'⟩ := exists_lift_near (g := g) (Metric.mem_closedBall.1 hy)
  have hxc : ∀ ν, |x' ν - g.lift c ν| ≤ g.a / 2 := fun ν => by
    have := (norm_le_pi_norm (x' - g.lift c) ν).trans hx'
    simpa [Real.norm_eq_abs] using this
  have hyw : ∀ ν, |y' ν - w ν| ≤ g.a / 2 := fun ν => by
    have := (norm_le_pi_norm (y' - w) ν).trans hy'
    simpa [Real.norm_eq_abs] using this
  have hwν : ∀ ν, ν ≠ p.1 → w ν = g.lift c ν := fun ν hν => by
    simp [hw, Pi.single_apply, hν]
  have hwμ : w p.1 = g.lift c p.1 + e * g.a := by simp [hw]; ring
  refine ⟨(x', y' - x'), ?_, start_mem_segSet _, end_mem_segSet _ _, ?_⟩
  · rintro _ ⟨θ, ⟨h0, h1⟩, rfl⟩
    have hz : ∀ ν, (x' + θ • (y' - x')) ν = (1 - θ) * x' ν + θ * y' ν := fun ν => by
      simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; ring
    have hother : ∀ ν, ν ≠ p.1 → |(x' + θ • (y' - x')) ν - g.lift c ν| ≤ g.a / 2 := fun ν hν => by
      rw [hz]
      exact convex_coord (hxc ν) (by rw [← hwν ν hν]; exact hyw ν) h0 h1
    have hμ := one_dim ha he (hxc p.1) (by rw [← hwμ]; exact hyw p.1) h0 h1
    rw [← hz] at hμ
    rcases hμ with hμ | hμ
    · left
      refine proj_mem_cube (norm_le_of_coord (by linarith) fun ν => ?_)
      rw [Pi.sub_apply]
      by_cases hν : ν = p.1
      · subst hν; exact hμ
      · exact hother ν hν
    · right
      rw [hcw]
      refine proj_mem_closedBall (norm_le_of_coord (by linarith) fun ν => ?_)
      rw [Pi.sub_apply]
      by_cases hν : ν = p.1
      · subst hν; rw [hwμ]; exact hμ
      · rw [hwν ν hν]; exact hother ν hν
  · refine eu_le_of_sq (by linarith) ?_
    have hb : ∀ ν, |(y' - x') ν| ≤ (if ν = p.1 then 2 * g.a else g.a) := fun ν => by
      simp only [Pi.sub_apply]
      have hxy : |y' ν - x' ν| ≤ |y' ν - w ν| + |w ν - g.lift c ν| + |x' ν - g.lift c ν| := by
        calc |y' ν - x' ν| = |(y' ν - w ν) + (w ν - g.lift c ν) - (x' ν - g.lift c ν)| := by ring_nf
          _ ≤ |(y' ν - w ν) + (w ν - g.lift c ν)| + |x' ν - g.lift c ν| := abs_sub _ _
          _ ≤ _ := by gcongr; exact abs_add_le _ _
      by_cases hν : ν = p.1
      · subst hν
        have hwl : |w p.1 - g.lift c p.1| = g.a := by
          rw [hwμ, show g.lift c p.1 + e * g.a - g.lift c p.1 = e * g.a by ring, abs_mul, abs_of_pos ha]
          rcases he with h | h <;> simp [h]
        rw [if_pos rfl]
        linarith [hyw p.1, hxc p.1]
      · rw [if_neg hν]
        have hwl : |w ν - g.lift c ν| = 0 := by rw [hwν ν hν, sub_self, abs_zero]
        linarith [hyw ν, hxc ν]
    have hsq : ∀ ν, (y' - x') ν ^ 2 ≤ (if ν = p.1 then 2 * g.a else g.a) ^ 2 := fun ν =>
      sq_le_of_abs (hb ν)
    have htot : ∑ ν, (if ν = p.1 then 2 * g.a else g.a) ^ 2 = 7 * g.a ^ 2 := by
      have hf : ∀ ν : Fin 4, (if ν = p.1 then 2 * g.a else g.a) ^ 2 =
          g.a ^ 2 + (if ν = p.1 then 3 * g.a ^ 2 else 0) := fun ν => by split_ifs <;> ring
      rw [Finset.sum_congr rfl fun ν _ => hf ν, Finset.sum_add_distrib]
      simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      push_cast; ring
    calc ∑ ν, (y' - x') ν ^ 2 ≤ ∑ ν, (if ν = p.1 then 2 * g.a else g.a) ^ 2 :=
          Finset.sum_le_sum fun ν _ => hsq ν
      _ = 7 * g.a ^ 2 := htot
      _ ≤ (3 * g.a) ^ 2 := by nlinarith

/-- Two points of two cubes which are equal or share a wall are joined by a segment in their union of a length of at
most `3a`. -/
lemma exists_seg_adj {c c' : g.Idx} (h : c = c' ∨ (wallGraph (ZMod g.n)).Adj c c') {x y : g.T}
    (hx : x ∈ g.cube c) (hy : y ∈ g.cube c') :
    ∃ σ : Seg, segSet g.s g.N σ ⊆ g.cube c ∪ g.cube c' ∧ x ∈ segSet g.s g.N σ ∧ y ∈ segSet g.s g.N σ ∧
      eu σ.2 ≤ 3 * g.a := by
  rcases h with rfl | ⟨-, p, rfl⟩
  · obtain ⟨σ, h1, h2, h3, h4⟩ := exists_seg_cube hx hy
    exact ⟨σ, h1.trans subset_union_left, h2, h3, by linarith [g.ha]⟩
  · exact exists_seg_wall hx hy

/-! ### Admissible families and the linear size relative to a set -/

variable (g)

/-- The families of segments admissible in `eq:contracted-size` for `X` and `D`: they lie in `X`, meet every cube
of `X`, and their union is connected together with `D`. -/
def Adm (X D : Finset g.Idx) (S : Finset Seg) : Prop :=
  (∀ σ ∈ S, segSet g.s g.N σ ⊆ g.cubes X) ∧
  (∀ c ∈ X, ∃ σ ∈ S, (segSet g.s g.N σ ∩ g.cube c).Nonempty) ∧
  IsPreconnected ((⋃ σ ∈ S, segSet g.s g.N σ) ∪ g.cubes D)

/-- The length of a family outside `D`. -/
def cost (D : Finset g.Idx) (S : Finset Seg) : ℝ := ∑ σ ∈ S, lenOut g.s g.N (g.cubes D) σ

/-- The linear size `d(X; D)` of `eq:contracted-size`. -/
def d (X D : Finset g.Idx) : ℝ := g.a⁻¹ * sInf (g.cost D '' {S | g.Adm X D S})

variable {g}

lemma cost_nonneg (D : Finset g.Idx) (S : Finset Seg) : 0 ≤ g.cost D S :=
  Finset.sum_nonneg fun σ _ => lenOut_nonneg _ σ

lemma d_nonneg (X D : Finset g.Idx) : 0 ≤ g.d X D := by
  refine mul_nonneg (inv_nonneg.2 g.ha.le) (Real.sInf_nonneg ?_)
  rintro _ ⟨S, -, rfl⟩
  exact cost_nonneg D S

lemma bddBelow_cost (X D : Finset g.Idx) : BddBelow (g.cost D '' {S | g.Adm X D S}) :=
  ⟨0, by rintro _ ⟨S, -, rfl⟩; exact cost_nonneg D S⟩

/-- An admissible family bounds `a · d(X; D)` from above. -/
lemma a_mul_d_le {X D : Finset g.Idx} {S : Finset Seg} (h : g.Adm X D S) : g.a * g.d X D ≤ g.cost D S := by
  unfold d
  rw [← mul_assoc, mul_inv_cancel₀ g.ha.ne', one_mul]
  exact csInf_le (bddBelow_cost X D) ⟨S, h, rfl⟩

/-- A lower bound for all admissible families bounds `a · d(X; D)` from below. -/
lemma le_a_mul_d {X D : Finset g.Idx} (hne : ∃ S, g.Adm X D S) {B : ℝ}
    (h : ∀ S, g.Adm X D S → B ≤ g.cost D S) : B ≤ g.a * g.d X D := by
  unfold d
  rw [← mul_assoc, mul_inv_cancel₀ g.ha.ne', one_mul]
  obtain ⟨S0, h0⟩ := hne
  exact le_csInf ⟨_, S0, h0, rfl⟩ (by rintro _ ⟨S, hS, rfl⟩; exact h S hS)

/-- For every `ε > 0` there is an admissible family of a cost of at most `a(d(X; D) + ε)`. -/
lemma exists_adm_le {X D : Finset g.Idx} (hne : ∃ S, g.Adm X D S) {ε : ℝ} (hε : 0 < ε) :
    ∃ S, g.Adm X D S ∧ g.cost D S ≤ g.a * (g.d X D + ε) := by
  have ha := g.ha
  obtain ⟨S0, h0⟩ := hne
  have hlt : sInf (g.cost D '' {S | g.Adm X D S}) < sInf (g.cost D '' {S | g.Adm X D S}) + g.a * ε :=
    lt_add_of_pos_right _ (mul_pos ha hε)
  obtain ⟨_, ⟨S, hS, rfl⟩, hlt'⟩ := exists_lt_of_csInf_lt (s := g.cost D '' {S | g.Adm X D S})
    ⟨_, S0, h0, rfl⟩ hlt
  refine ⟨S, hS, hlt'.le.trans (le_of_eq ?_)⟩
  unfold d
  field_simp

/-! ### Joining connected pieces -/

/-- A segment is preconnected. -/
lemma isPreconnected_segSet' (σ : Seg) : IsPreconnected (segSet g.s g.N σ) :=
  isPreconnected_Icc.image _ (lipschitzWith_proj.continuous.comp
    (continuous_const.add (continuous_id.smul continuous_const))).continuousOn

/-- In a connected union `Z` covered by the cube sets `C p` of pieces `p ∈ P`, a proper nonempty subfamily `B` has
a piece outside it with a cube equal to, or sharing a wall with, a cube of a piece of `B`. -/
lemma exists_adjacent_piece {ι : Type*} [DecidableEq ι] {P B : Finset ι} (C : ι → Finset g.Idx) {Z : Finset g.Idx}
    (hZ : ((wallGraph (ZMod g.n)).induce (Z : Set g.Idx)).Connected) (hBP : B ⊆ P) (hB : B.Nonempty)
    (hPB : (P \ B).Nonempty) (hCZ : ∀ p ∈ P, C p ⊆ Z) (hcov : ∀ c ∈ Z, ∃ p ∈ P, c ∈ C p)
    (hCne : ∀ p ∈ P, (C p).Nonempty) :
    ∃ p ∈ P \ B, ∃ q ∈ B, ∃ c ∈ C p, ∃ c' ∈ C q, c' = c ∨ (wallGraph (ZMod g.n)).Adj c' c := by
  obtain ⟨q0, hq0⟩ := hB
  obtain ⟨c0, hc0⟩ := hCne q0 (hBP hq0)
  obtain ⟨p1, hp1⟩ := hPB
  have hp1P := (Finset.mem_sdiff.1 hp1).1
  obtain ⟨c1, hc1⟩ := hCne p1 hp1P
  have hc0Z : c0 ∈ Z := hCZ q0 (hBP hq0) hc0
  have hc1Z : c1 ∈ Z := hCZ p1 hp1P hc1
  set Found := ∃ p ∈ P \ B, ∃ q ∈ B, ∃ c ∈ C p, ∃ c' ∈ C q, c' = c ∨ (wallGraph (ZMod g.n)).Adj c' c
  have hr := (SimpleGraph.reachable_iff_reflTransGen _ _).1
    (hZ.preconnected ⟨c0, hc0Z⟩ ⟨c1, hc1Z⟩)
  have key : ∀ v : (Z : Set g.Idx), Relation.ReflTransGen
      ((wallGraph (ZMod g.n)).induce (Z : Set g.Idx)).Adj ⟨c0, hc0Z⟩ v →
      (∃ q ∈ B, v.1 ∈ C q) ∨ Found := by
    intro v hv
    induction hv with
    | refl => exact Or.inl ⟨q0, hq0, hc0⟩
    | @tail v w _ hvw ih =>
      rcases ih with ⟨q, hq, hvq⟩ | hf
      · obtain ⟨p, hp, hwp⟩ := hcov w.1 w.2
        by_cases hpB : p ∈ B
        · exact Or.inl ⟨p, hpB, hwp⟩
        · exact Or.inr ⟨p, Finset.mem_sdiff.2 ⟨hp, hpB⟩, q, hq, w.1, hwp, v.1, hvq, Or.inr hvw⟩
      · exact Or.inr hf
  rcases key _ hr with ⟨q, hq, hc1q⟩ | hf
  · exact ⟨p1, hp1, q, hq, c1, hc1, c1, hc1q, Or.inl rfl⟩
  · exact hf

/-- **Joining pieces.** Preconnected pieces `A p`, `p ∈ P`, which meet every cube of their cube sets `C p`, the cube
sets covering a connected union `Z`, are joined by segments in `Z` of a total length of at most `3a(#P - 1)`. -/
theorem join_pieces {ι : Type*} [DecidableEq ι] (P : Finset ι) (hP : P.Nonempty) (A : ι → Set g.T) (C : ι → Finset g.Idx)
    {Z : Finset g.Idx} (hZ : ((wallGraph (ZMod g.n)).induce (Z : Set g.Idx)).Connected)
    (hA : ∀ p ∈ P, IsPreconnected (A p)) (hAC : ∀ p ∈ P, ∀ c ∈ C p, (A p ∩ g.cube c).Nonempty)
    (hCZ : ∀ p ∈ P, C p ⊆ Z) (hcov : ∀ c ∈ Z, ∃ p ∈ P, c ∈ C p) (hCne : ∀ p ∈ P, (C p).Nonempty) :
    ∃ J : Finset Seg, (∀ σ ∈ J, segSet g.s g.N σ ⊆ g.cubes Z) ∧
      ∑ σ ∈ J, eu σ.2 ≤ 3 * g.a * ((P.card : ℝ) - 1) ∧
      IsPreconnected ((⋃ p ∈ P, A p) ∪ ⋃ σ ∈ J, segSet g.s g.N σ) := by
  classical
  have ha := g.ha
  have key : ∀ k : ℕ, ∀ B ⊆ P, B.Nonempty → (P \ B).card = k →
      (∃ J : Finset Seg, (∀ σ ∈ J, segSet g.s g.N σ ⊆ g.cubes Z) ∧
        ∑ σ ∈ J, eu σ.2 ≤ 3 * g.a * ((B.card : ℝ) - 1) ∧
        IsPreconnected ((⋃ p ∈ B, A p) ∪ ⋃ σ ∈ J, segSet g.s g.N σ)) →
      ∃ J : Finset Seg, (∀ σ ∈ J, segSet g.s g.N σ ⊆ g.cubes Z) ∧
        ∑ σ ∈ J, eu σ.2 ≤ 3 * g.a * ((P.card : ℝ) - 1) ∧
        IsPreconnected ((⋃ p ∈ P, A p) ∪ ⋃ σ ∈ J, segSet g.s g.N σ) := by
    intro k
    induction k with
    | zero =>
      intro B hBP _ hk hJ
      have : B = P := Finset.Subset.antisymm hBP (Finset.sdiff_eq_empty_iff_subset.1
        (Finset.card_eq_zero.1 hk))
      subst this; exact hJ
    | succ k ih =>
      intro B hBP hB hk ⟨J, hJZ, hJl, hJc⟩
      have hPB : (P \ B).Nonempty := Finset.card_pos.1 (by omega)
      obtain ⟨p, hp, q, hq, c, hc, c', hc', hadj⟩ :=
        exists_adjacent_piece C hZ hBP hB hPB hCZ hcov hCne
      have hpP := (Finset.mem_sdiff.1 hp).1
      have hpB := (Finset.mem_sdiff.1 hp).2
      obtain ⟨y, hyA, hyc⟩ := hAC q (hBP hq) c' hc'
      obtain ⟨x, hxA, hxc⟩ := hAC p hpP c hc
      obtain ⟨σ, hσ, hyσ, hxσ, hσl⟩ := exists_seg_adj hadj hyc hxc
      refine ih (insert p B) (Finset.insert_subset hpP hBP) (Finset.insert_nonempty _ _) ?_
        ⟨insert σ J, ?_, ?_, ?_⟩
      · rw [Finset.sdiff_insert, Finset.card_erase_of_mem hp]; omega
      · intro τ hτ
        rcases Finset.mem_insert.1 hτ with rfl | hτ
        · exact hσ.trans (union_subset (cube_subset_cubes (hCZ q (hBP hq) hc'))
            (cube_subset_cubes (hCZ p hpP hc)))
        · exact hJZ τ hτ
      · by_cases hσJ : σ ∈ J
        · rw [Finset.insert_eq_of_mem hσJ, Finset.card_insert_of_notMem hpB]
          push_cast; nlinarith
        · rw [Finset.sum_insert hσJ, Finset.card_insert_of_notMem hpB]
          push_cast; linarith
      · have e : (⋃ r ∈ insert p B, A r) ∪ ⋃ τ ∈ insert σ J, segSet g.s g.N τ =
            (((⋃ r ∈ B, A r) ∪ ⋃ τ ∈ J, segSet g.s g.N τ) ∪ segSet g.s g.N σ) ∪ A p := by
          rw [Finset.set_biUnion_insert, Finset.set_biUnion_insert]
          ext; simp only [mem_union]; tauto
        rw [e]
        refine IsPreconnected.union x (Or.inr hxσ) hxA ?_ (hA p hpP)
        refine IsPreconnected.union y (Or.inl (mem_iUnion₂.2 ⟨q, hq, hyA⟩)) hyσ hJc ?_
        exact isPreconnected_segSet' σ
  obtain ⟨p0, hp0⟩ := hP
  refine key _ {p0} (Finset.singleton_subset_iff.2 hp0) (Finset.singleton_nonempty _) rfl
    ⟨∅, by simp, by simp, ?_⟩
  simpa using hA p0 hp0


/-- Admissible families exist for a connected `X` and `D ⊆ X`. -/
lemma exists_adm {X D : Finset g.Idx} (hX : ((wallGraph (ZMod g.n)).induce (X : Set g.Idx)).Connected)
    (hD : D ⊆ X) : ∃ S, g.Adm X D S := by
  classical
  have hXne : X.Nonempty := by
    obtain ⟨⟨c, hc⟩⟩ := hX.nonempty
    exact ⟨c, hc⟩
  obtain ⟨J, hJZ, -, hJc⟩ := join_pieces (g := g) X hXne (fun c : g.Idx => ({g.centre c} : Set g.T))
    (fun c : g.Idx => ({c} : Finset g.Idx)) hX
    (fun c _ => isPreconnected_singleton) (fun c _ c' hc' => by
      rw [Finset.mem_singleton.1 hc']; exact ⟨g.centre c, mem_singleton _, centre_mem_cube c⟩)
    (fun c hc => Finset.singleton_subset_iff.2 hc) (fun c hc => ⟨c, hc, Finset.mem_singleton_self c⟩)
    (fun c _ => Finset.singleton_nonempty c)
  set S := J ∪ X.image (fun c => pt (g.lift c)) with hS
  have hU : (⋃ σ ∈ S, segSet g.s g.N σ) = (⋃ c ∈ X, ({g.centre c} : Set g.T)) ∪ ⋃ σ ∈ J, segSet g.s g.N σ := by
    rw [hS, Finset.set_biUnion_union, Finset.set_biUnion_finset_image]
    simp only [segSet_pt]
    rw [union_comm]; rfl
  refine ⟨S, ?_, ?_, ?_⟩
  · intro σ hσ
    rcases Finset.mem_union.1 hσ with h | h
    · exact hJZ σ h
    · obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 h
      rw [segSet_pt, singleton_subset_iff]
      exact cube_subset_cubes hc (centre_mem_cube c)
  · intro c hc
    refine ⟨pt (g.lift c), Finset.mem_union_right _ (Finset.mem_image_of_mem _ hc), g.centre c, ?_,
      centre_mem_cube c⟩
    rw [segSet_pt]; rfl
  · rw [hU]
    have e : g.cubes D = ⋃ d ∈ D, g.cube d := rfl
    rw [e]
    refine isPreconnected_hub hJc D (fun d => g.cube d) (fun d _ => isPreconnected_cube d) fun d hd => ?_
    exact ⟨g.centre d, centre_mem_cube d, Or.inl (mem_biUnion (hD hd) rfl)⟩

end Grid

end Contracted
end CoreLean

end
