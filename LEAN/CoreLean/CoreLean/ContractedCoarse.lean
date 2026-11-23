/-
`lem:contracted-geometry`(iii) of BALABAN_CORE.tex (`63991d7efeeb`): the fine grid and the coarser grid.

The fine grid `g` has the side `a` and `n = Ln'` cubes per direction, `L = 2h + 1` odd; the coarser grid `coarse g`
has the side `La` and `n'` cubes per direction, on the same torus. The cube of the coarser grid which contains the
fine cube `c` has the index `K(c)`, the nearest multiple of `L` to `c`, divided by `L` (`Kz v = ⌊(v + h)/L⌋`), and
the fine cube lies in it (`cube_subset_coarse`). For a union `X` of fine cubes, `X^∼` (`tilde`) is the union of the
cubes which touch a cube of `X`, and `X'` (`prime`) the union of the coarser cubes `K(c)`, `c ∈ X^∼`: the core's
description of the smallest union of coarser cubes which contains `X^∼` (every fine cube lies in exactly one coarser
cube).

* `conn_tilde`, `conn_prime`: `Z^∼` and `Z'` are connected for a connected `Z`.
* `prime_meets`: every cube of `D'` meets `D`.
* `far_of_not_touch_prime`: a cube `Q` of `Z'` which touches no cube of `D'` is touched by a fine cube `□` of `Z` at
  the distance `≥ La` from `D`, all of whose points are within `La/2 + a` of the centre of `Q`.
* `contracted_iii`: `L d'(Z'; D') ≤ (1 + 486/L) d(Z; D)`, through `(1 + 324/L)`; the strands of the core are replaced
  by `count_mass`, as in (v).
-/
import CoreLean.ContractedGeometry

open Set Real MeasureTheory
open scoped ENNReal NNReal

noncomputable section

namespace CoreLean
namespace Contracted
namespace Grid

/-! ### Connectedness through relations on the whole index set -/

lemma conn_iff {g : Grid} {X : Finset g.Idx} :
    g.Conn X ↔ X.Nonempty ∧ ∀ a ∈ X, ∀ b ∈ X,
      Relation.ReflTransGen (fun u v => (wallGraph (ZMod g.n)).Adj u v ∧ u ∈ X ∧ v ∈ X) a b := by
  constructor
  · intro hX
    refine ⟨Conn.nonempty hX, fun a ha b hb => ?_⟩
    have hr := (SimpleGraph.reachable_iff_reflTransGen _ _).1
      (SimpleGraph.Connected.preconnected hX ⟨a, ha⟩ ⟨b, hb⟩)
    exact Relation.ReflTransGen.lift
      (p := fun u v => (wallGraph (ZMod g.n)).Adj u v ∧ u ∈ X ∧ v ∈ X)
      (fun v : (X : Set g.Idx) => v.1) (fun v w hvw => ⟨hvw, v.2, w.2⟩) _ _ hr
  · rintro ⟨⟨c, hc⟩, h⟩
    unfold Conn
    rw [SimpleGraph.connected_iff]
    refine ⟨fun u v => ?_, ⟨⟨c, hc⟩⟩⟩
    rw [SimpleGraph.reachable_iff_reflTransGen]
    have key : ∀ b, Relation.ReflTransGen (fun u v => (wallGraph (ZMod g.n)).Adj u v ∧ u ∈ X ∧ v ∈ X) u.1 b →
        ∀ hb : b ∈ X, Relation.ReflTransGen ((wallGraph (ZMod g.n)).induce (X : Set g.Idx)).Adj u ⟨b, hb⟩ := by
      intro b hub
      induction hub with
      | refl => intro _; exact Relation.ReflTransGen.refl
      | @tail b' b'' _ hstep ih =>
        intro hb''
        exact (ih hstep.2.1).tail hstep.1
    exact key v.1 (h u.1 u.2 v.1 v.2) v.2

/-! ### The coarser grid -/

variable {g : Grid} {h n' : ℕ}

/-- The coarser grid of side `La`, `L = 2h + 1`, with `n'` cubes per direction, `n = Ln'`. -/
abbrev coarse (g : Grid) (h n' : ℕ) (hn : g.n = (2 * h + 1) * n') : Grid where
  s := g.s
  N := g.N
  a := ((2 * h + 1 : ℕ) : ℝ) * g.a
  n := n'
  ha := by have := g.ha; positivity
  hP := by rw [← g.hP, hn]; push_cast; ring
  hn := ⟨fun h0 => NeZero.ne g.n (by rw [hn, h0, mul_zero])⟩

/-- `⌊(v + h)/L⌋`, the index of the multiple of `L` nearest to `v`. -/
def Kz (h : ℕ) (v : ℤ) : ℤ := (v + h) / (2 * h + 1 : ℕ)

lemma Kz_spec (v : ℤ) : |v - ((2 * h + 1 : ℕ) : ℤ) * Kz h v| ≤ h := by
  unfold Kz
  have hL : (0 : ℤ) < ((2 * h + 1 : ℕ) : ℤ) := by positivity
  have h1 := Int.emod_add_mul_ediv (v + h) ((2 * h + 1 : ℕ) : ℤ)
  have h2 := Int.emod_nonneg (v + h) hL.ne'
  have h3 := Int.emod_lt_of_pos (v + h) hL
  push_cast at h1 h2 h3 ⊢
  rw [abs_le]; constructor <;> linarith

lemma Kz_add_mul (v t : ℤ) : Kz h (v + ((2 * h + 1 : ℕ) : ℤ) * t) = Kz h v + t := by
  unfold Kz
  rw [show v + ((2 * h + 1 : ℕ) : ℤ) * t + h = v + h + t * ((2 * h + 1 : ℕ) : ℤ) by ring,
    Int.add_mul_ediv_right _ _ (by positivity)]

lemma Kz_close (v i : ℤ) (hi : |i| ≤ ((2 * h + 1 : ℕ) : ℤ)) : |Kz h (v + i) - Kz h v| ≤ 1 := by
  unfold Kz
  set L : ℤ := ((2 * h + 1 : ℕ) : ℤ) with hLdef
  have hL : 0 < L := by positivity
  have a1 := Int.emod_add_mul_ediv (v + h) L
  have a2 := Int.emod_nonneg (v + h) hL.ne'
  have a3 := Int.emod_lt_of_pos (v + h) hL
  have b1 := Int.emod_add_mul_ediv (v + i + h) L
  have b2 := Int.emod_nonneg (v + i + h) hL.ne'
  have b3 := Int.emod_lt_of_pos (v + i + h) hL
  rw [abs_le] at hi ⊢
  set q0 := (v + h) / L
  set q1 := (v + i + h) / L
  constructor
  · by_contra hc
    have : q1 - q0 ≤ -2 := by omega
    nlinarith
  · by_contra hc
    have : 2 ≤ q1 - q0 := by omega
    nlinarith

variable {hn : g.n = (2 * h + 1) * n'}

/-- The index of the coarser cube which contains the fine cube `c`. -/
def K (hn : g.n = (2 * h + 1) * n') (c : g.Idx) : (coarse g h n' hn).Idx :=
  fun ν => ((Kz h ((c ν).val : ℤ) : ℤ) : ZMod n')

/-- `K` computed from any integer representative. -/
lemma K_int {c : g.Idx} {ν : Fin 4} {v : ℤ} (hv : (v : ZMod g.n) = c ν) :
    K hn c ν = ((Kz h v : ℤ) : ZMod n') := by
  have hval : (((c ν).val : ℤ) : ZMod g.n) = c ν := by
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  have hdvd : (g.n : ℤ) ∣ ((c ν).val : ℤ) - v :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub v ((c ν).val : ℤ) g.n).1 (hv.trans hval.symm)
  obtain ⟨t, ht⟩ := hdvd
  have ht' : ((c ν).val : ℤ) - v = (((2 * h + 1) * n' : ℕ) : ℤ) * t := by rw [← hn]; exact ht
  have e : ((c ν).val : ℤ) = v + ((2 * h + 1 : ℕ) : ℤ) * (n' * t) := by
    push_cast at ht' ⊢; linarith
  simp only [K]
  rw [e, Kz_add_mul]
  push_cast
  simp

/-- The centre of `K(c)` is within `ha` of the centre of `c`. -/
lemma coarse_centre (c : g.Idx) :
    (coarse g h n' hn).centre (K hn c) =
      proj g.s g.N (fun ν => ((2 * h + 1 : ℕ) : ℝ) * g.a * (Kz h ((c ν).val : ℤ) : ℝ)) := by
  have := (coarse g h n' hn).proj_int (fun ν => Kz h ((c ν).val : ℤ))
  exact this.symm

lemma centre_close (c : g.Idx) : dist (g.centre c) ((coarse g h n' hn).centre (K hn c)) ≤ h * g.a := by
  have ha := g.ha
  rw [coarse_centre, centre]
  refine (dist_proj_le _ _).trans ?_
  rw [dist_eq_norm]
  refine norm_le_of_coord (by positivity) fun ν => ?_
  simp only [lift, Pi.sub_apply]
  have := Kz_spec (h := h) ((c ν).val : ℤ)
  have h2 : |(((c ν).val : ℤ) : ℝ) - ((2 * h + 1 : ℕ) : ℝ) * (Kz h ((c ν).val : ℤ) : ℝ)| ≤ h := by
    exact_mod_cast this
  rw [show g.a * ((c ν).val : ℝ) - ((2 * h + 1 : ℕ) : ℝ) * g.a * (Kz h ((c ν).val : ℤ) : ℝ) =
      g.a * ((((c ν).val : ℤ) : ℝ) - ((2 * h + 1 : ℕ) : ℝ) * (Kz h ((c ν).val : ℤ) : ℝ)) by push_cast; ring,
    abs_mul, abs_of_pos ha]
  nlinarith

/-- Every fine cube lies in the coarser cube `K(c)`. -/
lemma cube_subset_coarse (c : g.Idx) : g.cube c ⊆ (coarse g h n' hn).cube (K hn c) := by
  intro x hx
  have h1 := Metric.mem_closedBall.1 hx
  have h2 := centre_close (hn := hn) c
  rw [cube, Metric.mem_closedBall]
  calc dist x ((coarse g h n' hn).centre (K hn c)) ≤ dist x (g.centre c) +
        dist (g.centre c) ((coarse g h n' hn).centre (K hn c)) := dist_triangle _ _ _
    _ ≤ g.a / 2 + h * g.a := add_le_add h1 h2
    _ = ((2 * h + 1 : ℕ) : ℝ) * g.a / 2 := by push_cast; ring

/-! ### `X^∼` and `X'` -/

/-- `X^∼`: the cubes which touch a cube of `X`. -/
def tilde (X : Finset g.Idx) : Finset g.Idx := Finset.univ.filter fun c' => ∃ c ∈ X, Touch c c'

lemma subset_tilde (X : Finset g.Idx) : X ⊆ tilde X := fun c hc =>
  Finset.mem_filter.2 ⟨Finset.mem_univ _, c, hc, touch_refl c⟩

lemma tilde_mono {X Y : Finset g.Idx} (h : X ⊆ Y) : tilde X ⊆ tilde Y := fun c hc => by
  obtain ⟨-, d, hd, hdc⟩ := Finset.mem_filter.1 hc
  exact Finset.mem_filter.2 ⟨Finset.mem_univ _, d, h hd, hdc⟩

/-- `X'`: the coarser cubes `K(c)`, `c ∈ X^∼`. -/
def prime (hn : g.n = (2 * h + 1) * n') (X : Finset g.Idx) : Finset (coarse g h n' hn).Idx :=
  (tilde X).image (K hn)

lemma prime_mono {X Y : Finset g.Idx} (hXY : X ⊆ Y) : prime hn X ⊆ prime hn Y :=
  Finset.image_subset_image (tilde_mono hXY)

lemma K_mem_prime {X : Finset g.Idx} {c : g.Idx} (hc : c ∈ X) : K hn c ∈ prime hn X :=
  Finset.mem_image_of_mem _ (subset_tilde X hc)

lemma cubes_subset_prime (X : Finset g.Idx) : g.cubes X ⊆ (coarse g h n' hn).cubes (prime hn X) := by
  intro x hx
  obtain ⟨c, hc, hxc⟩ := mem_iUnion₂.1 hx
  exact mem_iUnion₂.2 ⟨K hn c, K_mem_prime hc, cube_subset_coarse c hxc⟩

/-- The steps of a touching pair, one coordinate at a time. -/
lemma reach_of_touch {X : Finset g.Idx} {c c' : g.Idx} (hc : c ∈ X) (hcc' : Touch c c') :
    Relation.ReflTransGen (fun u v => (wallGraph (ZMod g.n)).Adj u v ∧ u ∈ tilde X ∧ v ∈ tilde X) c c' := by
  classical
  obtain ⟨δ, hδ, rfl⟩ := touch_iff_int.1 hcc'
  set part : ℕ → g.Idx := fun k => c + fun ν => (((if ν.val < k then δ ν else 0) : ℤ) : ZMod g.n) with hpart
  have hpart_mem : ∀ k, part k ∈ tilde X := fun k => by
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, c, hc, touch_iff_int.2 ⟨_, fun ν => ?_, rfl⟩⟩
    split_ifs
    · exact hδ ν
    · simp
  have hstep : ∀ k, Relation.ReflTransGen
      (fun u v => (wallGraph (ZMod g.n)).Adj u v ∧ u ∈ tilde X ∧ v ∈ tilde X) (part k) (part (k + 1)) := by
    intro k
    by_cases hk : k < 4
    · set μ : Fin 4 := ⟨k, hk⟩
      have hd := hδ μ
      rw [abs_le] at hd
      by_cases heq : part k = part (k + 1)
      · rw [heq]
      · have hne0 : δ μ ≠ 0 := by
          intro h0; apply heq; funext ν; simp only [hpart, Pi.add_apply]; congr 2
          by_cases hν : ν.val = k
          · have : ν = μ := Fin.ext hν
            subst this; simp [h0]
          · have : ν.val < k + 1 ↔ ν.val < k := by omega
            simp only [this]
        have h1 : δ μ = 1 ∨ δ μ = -1 := by omega
        refine Relation.ReflTransGen.single ⟨⟨heq, (if δ μ = 1 then (μ, true) else (μ, false)), ?_⟩,
          hpart_mem k, hpart_mem (k + 1)⟩
        funext ν
        by_cases hν : ν = μ
        · subst hν
          rcases h1 with h1 | h1
          · simp [hpart, wallNbr, μ, h1]
          · simp [hpart, wallNbr, μ, h1, sub_eq_add_neg]
        · have hν' : ν.val ≠ k := fun h' => hν (Fin.ext h')
          have : ν.val < k + 1 ↔ ν.val < k := by omega
          rcases h1 with h1 | h1
          · simp [hpart, wallNbr, h1, Pi.single_apply, hν, this]
          · simp [hpart, wallNbr, h1, Pi.single_apply, hν, this, sub_eq_add_neg]
    · have : part (k + 1) = part k := by
        funext ν
        simp only [hpart, Pi.add_apply]
        have h1 : ν.val < k + 1 := by omega
        have h2 : ν.val < k := by omega
        simp [h1, h2]
      rw [this]
  have hall : ∀ k, Relation.ReflTransGen
      (fun u v => (wallGraph (ZMod g.n)).Adj u v ∧ u ∈ tilde X ∧ v ∈ tilde X) (part 0) (part k) := by
    intro k
    induction k with
    | zero => exact Relation.ReflTransGen.refl
    | succ k ih => exact ih.trans (hstep k)
  have h0 : part 0 = c := by funext ν; simp [hpart]
  have h4 : part 4 = c + fun ν => (δ ν : ZMod g.n) := by
    funext ν; simp only [hpart, Pi.add_apply]; simp [ν.isLt]
  have := hall 4
  rwa [h0, h4] at this

/-- `Z^∼` is connected for a connected `Z`. -/
lemma conn_tilde {Z : Finset g.Idx} (hZ : g.Conn Z) : g.Conn (tilde Z) := by
  obtain ⟨hne, hR⟩ := conn_iff.1 hZ
  refine conn_iff.2 ⟨hne.mono (subset_tilde Z), fun a ha b hb => ?_⟩
  obtain ⟨-, c, hc, hca⟩ := Finset.mem_filter.1 ha
  obtain ⟨-, d, hd, hdb⟩ := Finset.mem_filter.1 hb
  have h1 : Relation.ReflTransGen (fun u v => (wallGraph (ZMod g.n)).Adj u v ∧ u ∈ tilde Z ∧ v ∈ tilde Z)
      a c := by
    have := reach_of_touch hc hca
    exact Relation.ReflTransGen.mono
      (p := fun u v => (wallGraph (ZMod g.n)).Adj u v ∧ u ∈ tilde Z ∧ v ∈ tilde Z)
      (fun u v huv => ⟨huv.1.symm, huv.2.2, huv.2.1⟩) _ _ (Relation.ReflTransGen.swap _ _ this)
  have h2 : Relation.ReflTransGen (fun u v => (wallGraph (ZMod g.n)).Adj u v ∧ u ∈ tilde Z ∧ v ∈ tilde Z)
      c d :=
    Relation.ReflTransGen.mono (fun u v huv => ⟨huv.1, subset_tilde Z huv.2.1, subset_tilde Z huv.2.2⟩) _ _
      (hR c hc d hd)
  exact (h1.trans h2).trans (reach_of_touch hd hdb)

/-- Two fine cubes which share a wall lie in equal coarser cubes or in two which share a wall. -/
lemma K_adj {c c' : g.Idx} (hadj : (wallGraph (ZMod g.n)).Adj c c') :
    K hn c = K hn c' ∨ (wallGraph (ZMod n')).Adj (K hn c) (K hn c') := by
  classical
  obtain ⟨-, ⟨μ, b⟩, rfl⟩ := hadj
  set e : ℤ := if b then 1 else -1 with he
  have he1 : |e| ≤ ((2 * h + 1 : ℕ) : ℤ) := by
    have : |e| = 1 := by cases b <;> simp [he]
    rw [this]; push_cast; omega
  set v : ℤ := ((c μ).val : ℤ)
  have hcv : (v : ZMod g.n) = c μ := by simp only [v, Int.cast_natCast, ZMod.natCast_zmod_val]
  have hK' : ∀ ν, K hn (wallNbr (ZMod g.n) c (μ, b)) ν =
      if ν = μ then ((Kz h (v + e) : ℤ) : ZMod n') else K hn c ν := fun ν => by
    by_cases hν : ν = μ
    · subst hν
      rw [if_pos rfl]
      refine K_int ?_
      simp only [wallNbr]
      cases b <;> simp [he, hcv, sub_eq_add_neg]
    · rw [if_neg hν]
      simp only [K, wallNbr]
      cases b <;> simp [Pi.single_apply, hν]
  have hclose := Kz_close (h := h) v e he1
  have hKc : K hn c μ = ((Kz h v : ℤ) : ZMod n') := rfl
  rw [abs_le] at hclose
  rcases (by omega : Kz h (v + e) = Kz h v ∨ Kz h (v + e) = Kz h v + 1 ∨ Kz h (v + e) = Kz h v - 1)
    with h0 | h0 | h0
  · left
    funext ν
    rw [hK' ν]
    split_ifs with hν
    · subst hν; rw [h0, hKc]
    · rfl
  · by_cases heq : K hn c = K hn (wallNbr (ZMod g.n) c (μ, b))
    · exact Or.inl heq
    · refine Or.inr ⟨heq, (μ, true), ?_⟩
      funext ν
      rw [hK' ν]
      simp only [wallNbr, if_true, Pi.add_apply]
      split_ifs with hν
      · subst hν; rw [h0, hKc]; simp
      · simp [Pi.single_apply, hν]
  · by_cases heq : K hn c = K hn (wallNbr (ZMod g.n) c (μ, b))
    · exact Or.inl heq
    · refine Or.inr ⟨heq, (μ, false), ?_⟩
      funext ν
      rw [hK' ν]
      simp only [wallNbr, Bool.false_eq_true, if_false, Pi.sub_apply]
      split_ifs with hν
      · subst hν; rw [h0, hKc]; simp
      · simp [Pi.single_apply, hν]

/-- `Z'` is connected for a connected `Z`. -/
lemma conn_prime {Z : Finset g.Idx} (hZ : g.Conn Z) : (coarse g h n' hn).Conn (prime hn Z) := by
  obtain ⟨hne, hR⟩ := conn_iff.1 (conn_tilde hZ)
  refine conn_iff.2 ⟨hne.image _, fun A hA B hB => ?_⟩
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hA
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hB
  refine Relation.ReflTransGen.lift' (K hn) (fun u v huv => ?_) _ _ (hR a ha b hb)
  show Relation.ReflTransGen _ (K hn u) (K hn v)
  rcases K_adj (hn := hn) huv.1 with heq | hadj
  · rw [heq]
  · exact Relation.ReflTransGen.single ⟨hadj, Finset.mem_image_of_mem _ huv.2.1,
      Finset.mem_image_of_mem _ huv.2.2⟩

/-- Every cube of `D'` meets `D`. -/
lemma prime_meets {D : Finset g.Idx} {C : (coarse g h n' hn).Idx} (hC : C ∈ prime hn D) :
    ((coarse g h n' hn).cube C ∩ g.cubes D).Nonempty := by
  obtain ⟨c', hc', rfl⟩ := Finset.mem_image.1 hC
  obtain ⟨-, d, hd, hdc'⟩ := Finset.mem_filter.1 hc'
  obtain ⟨z, hz1, hz2⟩ := touch_inter hdc'
  exact ⟨z, cube_subset_coarse c' hz2, mem_iUnion₂.2 ⟨d, hd, hz1⟩⟩

/-- Two values of the circle at a distance `< Ra` of the centres `a·w`, `a·u` give indices which differ by an
integer of absolute value `< R`. -/
lemma coord_close {u w : ZMod g.n} {R : ℝ}
    (hd : dist (((g.a * (w.val : ℝ) : ℝ)) : AddCircle (g.s * g.N)) ((g.a * (u.val : ℝ) : ℝ)) < R * g.a) :
    ∃ j : ℤ, (|j| : ℝ) < R ∧ u - w = (j : ZMod g.n) := by
  have ha := g.ha
  rw [dist_eq_norm, ← AddCircle.coe_sub, AddCircle.norm_eq] at hd
  set r := round ((g.s * g.N)⁻¹ * (g.a * (w.val : ℝ) - g.a * (u.val : ℝ)))
  set t : ℤ := (u.val : ℤ) - w.val + r * g.n
  have ht : g.a * (w.val : ℝ) - g.a * (u.val : ℝ) - r * (g.s * g.N) = -(g.a * t) := by
    simp only [t]; rw [← g.hP]; push_cast; ring
  rw [ht, abs_neg, abs_mul, abs_of_pos ha] at hd
  refine ⟨t, ?_, ?_⟩
  · have : |(t : ℝ)| * g.a < R * g.a := by linarith
    have h2 := lt_of_mul_lt_mul_right this ha.le
    exact_mod_cast h2
  · simp only [t]; push_cast
    rw [ZMod.natCast_self, mul_zero, add_zero, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]

/-- **The far cubes of `Z'`.** A cube `Q = K(c'')` of `Z'`, `c''` touching the fine cube `□` of `Z`, which touches no
cube of `D'`: the points of `□` are at the distance `≥ La` from `D`. -/
lemma far_of_not_touch_prime {D : Finset g.Idx} {sq c'' : g.Idx} (hsq : Touch sq c'')
    (hQ : ∀ C ∈ prime hn D, ¬ Touch C (K hn c'')) {x z : g.T} (hx : x ∈ g.cube sq) (hz : z ∈ g.cubes D) :
    ((2 * h + 1 : ℕ) : ℝ) * g.a ≤ dist x z := by
  classical
  have ha := g.ha
  set L : ℕ := 2 * h + 1 with hL
  by_contra hlt
  push_neg at hlt
  obtain ⟨d, hd, hzd⟩ := mem_iUnion₂.1 hz
  -- the centres of `d` and `c''` are at a distance `< (L + 2)a`
  have hcen : dist (g.centre d) (g.centre c'') < ((L : ℝ) + 2) * g.a := by
    have h1 := Metric.mem_closedBall.1 hzd
    have h2 := Metric.mem_closedBall.1 hx
    have h3 := dist_centre_le_of_touch hsq
    calc dist (g.centre d) (g.centre c'') ≤ dist (g.centre d) z + dist z x + dist x (g.centre sq) +
          dist (g.centre sq) (g.centre c'') := by
          linarith [dist_triangle (g.centre d) z x, dist_triangle (g.centre d) x (g.centre sq),
            dist_triangle (g.centre d) (g.centre sq) (g.centre c'')]
      _ < g.a / 2 + L * g.a + g.a / 2 + g.a := by
          rw [dist_comm (g.centre d) z, dist_comm z x]; linarith
      _ = ((L : ℝ) + 2) * g.a := by ring
  have hj : ∀ ν, ∃ j : ℤ, (|j| : ℝ) < (L : ℝ) + 2 ∧ c'' ν - d ν = (j : ZMod g.n) := fun ν =>
    coord_close ((dist_le_pi_dist _ _ ν).trans_lt hcen)
  choose j hj1 hj2 using hj
  have hjL : ∀ ν, |j ν| ≤ (L : ℤ) + 1 := fun ν => by
    have h1 := hj1 ν
    have h2 : (|j ν| : ℝ) < ((L + 2 : ℤ) : ℝ) := by push_cast; exact h1
    have h3 : |j ν| < L + 2 := by exact_mod_cast h2
    omega
  -- the cube `d'` of `D^∼` one step from `d` towards `c''`
  set δ : Fin 4 → ℤ := fun ν => Int.sign (j ν) with hδ
  set d' : g.Idx := d + fun ν => (δ ν : ZMod g.n) with hd'
  have hdd' : Touch d d' := touch_iff_int.2 ⟨δ, fun ν => by
    simp only [hδ]
    rcases lt_trichotomy (j ν) 0 with h | h | h
    · rw [Int.sign_eq_neg_one_of_neg h]; norm_num
    · rw [h]; simp
    · rw [Int.sign_eq_one_of_pos h]; norm_num, rfl⟩
  have hd'D : K hn d' ∈ prime hn D :=
    Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, d, hd, hdd'⟩)
  refine hQ _ hd'D (fun ν => ?_)
  -- in each coordinate, `K(d')` and `K(c'')` differ by at most one
  set v : ℤ := ((c'' ν).val : ℤ)
  set i : ℤ := -j ν + δ ν
  have hi : |i| ≤ (L : ℤ) := by
    have := hjL ν
    simp only [i, hδ]
    rw [abs_le] at this ⊢
    rcases lt_trichotomy (j ν) 0 with h | h | h
    · rw [Int.sign_eq_neg_one_of_neg h]; constructor <;> omega
    · rw [h]; simp
    · rw [Int.sign_eq_one_of_pos h]; constructor <;> omega
  have hv : (v : ZMod g.n) = c'' ν := by simp only [v, Int.cast_natCast, ZMod.natCast_zmod_val]
  have hd'v : ((v + i : ℤ) : ZMod g.n) = d' ν := by
    simp only [hd', Pi.add_apply, i]
    push_cast
    rw [hv]
    have := hj2 ν
    rw [sub_eq_iff_eq_add] at this
    rw [this]; ring
  have hK1 : K hn d' ν = ((Kz h (v + i) : ℤ) : ZMod n') := K_int hd'v
  have hK2 : K hn c'' ν = ((Kz h v : ℤ) : ZMod n') := K_int hv
  have hclose := Kz_close (h := h) v i (by simpa [hL] using hi)
  rw [hK1, hK2]
  rw [abs_le] at hclose
  rcases (by omega : Kz h v - Kz h (v + i) = -1 ∨ Kz h v - Kz h (v + i) = 0 ∨ Kz h v - Kz h (v + i) = 1)
    with e | e | e
  · left; rw [← Int.cast_sub, e]; simp
  · right; left; rw [← Int.cast_sub, e]; simp
  · right; right; rw [← Int.cast_sub, e]; simp

/-- The points of a fine cube `□` touching `c''` are within `La/2 + a` of the centre of `K(c'')`. -/
lemma dist_coarse_centre_le {sq c'' : g.Idx} (hsq : Touch sq c'') {x : g.T} (hx : x ∈ g.cube sq) :
    dist x ((coarse g h n' hn).centre (K hn c'')) ≤ ((2 * h + 1 : ℕ) : ℝ) * g.a / 2 + g.a := by
  have h1 := Metric.mem_closedBall.1 hx
  have h2 := dist_centre_le_of_touch hsq
  have h3 := centre_close (hn := hn) c''
  calc dist x ((coarse g h n' hn).centre (K hn c'')) ≤ dist x (g.centre sq) + dist (g.centre sq) (g.centre c'') +
        dist (g.centre c'') ((coarse g h n' hn).centre (K hn c'')) := dist_triangle4 _ _ _ _
    _ ≤ g.a / 2 + g.a + h * g.a := by linarith
    _ = ((2 * h + 1 : ℕ) : ℝ) * g.a / 2 + g.a := by push_cast; ring

/-! ### `X'` is the smallest union of coarser cubes containing `X^∼` -/

/-- A coarser cube which contains the centre of a fine cube `c` is `K(c)`. -/
lemma coarse_eq_of_mem {c : g.Idx} {C : (coarse g h n' hn).Idx}
    (hC : g.centre c ∈ (coarse g h n' hn).cube C) : C = K hn c := by
  have : NeZero n' := (coarse g h n' hn).hn
  have ha := g.ha
  funext ν
  have hd := (dist_le_pi_dist _ _ ν).trans (Metric.mem_closedBall.1 hC)
  simp only [centre, lift, proj] at hd
  rw [dist_eq_norm, ← AddCircle.coe_sub, AddCircle.norm_eq] at hd
  set L : ℤ := ((2 * h + 1 : ℕ) : ℤ) with hLdef
  set v : ℤ := ((c ν).val : ℤ)
  set w : ℤ := ((C ν).val : ℤ)
  set r := round ((g.s * g.N)⁻¹ * (g.a * ((c ν).val : ℝ) -
    ((2 * h + 1 : ℕ) : ℝ) * g.a * ((C ν).val : ℝ)))
  set m : ℤ := w + r * n'
  have hP : g.s * (g.N : ℝ) = g.a * ((2 * h + 1 : ℕ) : ℝ) * n' := by rw [← g.hP, hn]; push_cast; ring
  have e : g.a * ((c ν).val : ℝ) - ((2 * h + 1 : ℕ) : ℝ) * g.a * ((C ν).val : ℝ) - r * (g.s * g.N) =
      g.a * ((v - L * m : ℤ) : ℝ) := by
    rw [hP]; simp only [v, w, m, hLdef]; push_cast; ring
  rw [e, abs_mul, abs_of_pos ha] at hd
  have h1 : |((v - L * m : ℤ) : ℝ)| * 2 ≤ ((2 * h + 1 : ℕ) : ℝ) := by
    have : |((v - L * m : ℤ) : ℝ)| * g.a ≤ ((2 * h + 1 : ℕ) : ℝ) * g.a / 2 := by linarith
    nlinarith
  have h2 : |v - L * m| * 2 ≤ 2 * h + 1 := by
    have := h1
    rw [← Int.cast_abs] at this
    exact_mod_cast this
  have h3 : |v - L * m| ≤ h := by omega
  have hKz : Kz h v = m := by
    have : v = (v - L * m) + L * m := by ring
    rw [this, Kz_add_mul]
    have h4 : Kz h (v - L * m) = 0 := by
      unfold Kz
      rw [abs_le] at h3
      exact Int.ediv_eq_zero_of_lt (by omega) (by push_cast; omega)
    rw [h4, zero_add]
  have hK : K hn c ν = ((m : ℤ) : ZMod n') := by simp only [K]; rw [hKz]
  rw [hK]
  simp only [m, w]
  push_cast
  simp only [ZMod.natCast_self, mul_zero, add_zero]
  exact (ZMod.natCast_zmod_val _).symm

/-- `X'` is the smallest union of coarser cubes which contains `X^∼`. -/
theorem prime_isLeast (X : Finset g.Idx) :
    g.cubes (tilde X) ⊆ (coarse g h n' hn).cubes (prime hn X) ∧
      ∀ W : Finset (coarse g h n' hn).Idx, g.cubes (tilde X) ⊆ (coarse g h n' hn).cubes W → prime hn X ⊆ W := by
  refine ⟨fun x hx => ?_, fun W hW C hC => ?_⟩
  · obtain ⟨c, hc, hxc⟩ := mem_iUnion₂.1 hx
    exact mem_iUnion₂.2 ⟨K hn c, Finset.mem_image_of_mem _ hc, cube_subset_coarse c hxc⟩
  · obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hC
    obtain ⟨C', hC', hcC'⟩ := mem_iUnion₂.1 (hW (mem_iUnion₂.2 ⟨c, hc, centre_mem_cube c⟩))
    rw [← coarse_eq_of_mem hcC']
    exact hC'

/-! ### (iii) -/

/-- A point of the torus as a segment. -/
def ptOf (g : Grid) (x : g.T) : Seg := pt (Classical.choose (exists_lift (g := g) x 0))

lemma segSet_ptOf (x : g.T) : segSet g.s g.N (g.ptOf x) = {x} := by
  rw [ptOf, segSet_pt, (Classical.choose_spec (exists_lift (g := g) x 0)).1]

lemma lenOut_ptOf (F : Set g.T) (x : g.T) : lenOut g.s g.N F (g.ptOf x) = 0 := lenOut_pt _ _

/-- **`lem:contracted-geometry`(iii)**: for a connected union `Z` of cubes of the fine grid and a nonempty union
`D ⊆ Z` of cubes, `L d'(Z'; D') ≤ (1 + 486/L) d(Z; D)`, `d'` the linear size for the coarser grid. -/
theorem contracted_iii (hh : 1 ≤ h) {Z D : Finset g.Idx} (hZ : g.Conn Z) (hDZ : D ⊆ Z) (hD : D.Nonempty) :
    ((2 * h + 1 : ℕ) : ℝ) * (coarse g h n' hn).d (prime hn Z) (prime hn D) ≤
      (1 + 486 / ((2 * h + 1 : ℕ) : ℝ)) * g.d Z D := by
  classical
  have ha := g.ha
  set L : ℝ := ((2 * h + 1 : ℕ) : ℝ) with hLdef
  have hh' : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hL3 : 3 ≤ L := by simp only [hLdef]; push_cast; linarith
  have hL0 : 0 < L := by linarith
  have : NeZero n' := (coarse g h n' hn).hn
  set gc := coarse g h n' hn with hgc
  have hgca : gc.a = L * g.a := rfl
  set Z' := prime hn Z with hZ'
  set D' := prime hn D with hD'
  -- the cubes of `Z'` with a fine cube `□` of `Z` and a fine cube `c''` touching it
  have hQdata : ∀ Q : gc.Idx, ∃ sq c'' : g.Idx, Q ∈ Z' → sq ∈ Z ∧ Touch sq c'' ∧ K hn c'' = Q := fun Q => by
    by_cases hQ : Q ∈ Z'
    · obtain ⟨c'', hc'', hK⟩ := Finset.mem_image.1 hQ
      obtain ⟨-, sq, hsq, hsqc⟩ := Finset.mem_filter.1 hc''
      exact ⟨sq, c'', fun _ => ⟨hsq, hsqc, hK⟩⟩
    · exact ⟨0, 0, fun h' => absurd h' hQ⟩
  choose sqF cF hQd using hQdata
  -- the inequality for one admissible family
  have hkey : ∀ S, g.Adm Z D S → gc.a * gc.d Z' D' ≤ (1 + 324 / L) * g.cost D S := by
    intro S hS
    set G := ⋃ σ ∈ S, segSet g.s g.N σ with hG
    set near : gc.Idx → Prop := fun Q => ∃ C ∈ D', Touch C Q with hnear
    set Zn := Z'.filter near with hZn
    set Zf := Z'.filter fun Q => ¬ near Q with hZf
    -- the points of the cubes near `D'`
    have hpn : ∀ Q : gc.Idx, ∃ p : g.T, near Q → p ∈ gc.cube Q ∧ p ∈ gc.cubes D' := fun Q => by
      by_cases hQ : near Q
      · obtain ⟨C, hC, hCQ⟩ := hQ
        obtain ⟨p, hp1, hp2⟩ := touch_inter hCQ
        exact ⟨p, fun _ => ⟨hp2, mem_iUnion₂.2 ⟨C, hC, hp1⟩⟩⟩
      · exact ⟨gc.centre Q, fun h' => absurd h' hQ⟩
    choose pF hpF using hpn
    -- the points `x_Q ∈ G` and `y_Q ∈ Q` in the fine cubes `□_Q`
    have hxy : ∀ Q : gc.Idx, ∃ x y : g.T, Q ∈ Z' →
        x ∈ G ∧ x ∈ g.cube (sqF Q) ∧ y ∈ g.cube (sqF Q) ∧ y ∈ gc.cube Q := fun Q => by
      by_cases hQ : Q ∈ Z'
      · obtain ⟨hsq, hsqc, hK⟩ := hQd Q hQ
        obtain ⟨σ, hσ, x, hx1, hx2⟩ := hS.2.1 _ hsq
        obtain ⟨y, hy1, hy2⟩ := touch_inter hsqc
        refine ⟨x, y, fun _ => ⟨mem_iUnion₂.2 ⟨σ, hσ, hx1⟩, hx2, hy1, ?_⟩⟩
        rw [← hK]; exact cube_subset_coarse _ hy2
      · exact ⟨g.centre 0, g.centre 0, fun h' => absurd h' hQ⟩
    choose xF yF hxyF using hxy
    have hseg : ∀ Q : gc.Idx, ∃ σ : Seg, Q ∈ Z' → segSet g.s g.N σ ⊆ g.cube (sqF Q) ∧
        xF Q ∈ segSet g.s g.N σ ∧ yF Q ∈ segSet g.s g.N σ ∧ eu σ.2 ≤ 2 * g.a := fun Q => by
      by_cases hQ : Q ∈ Z'
      · obtain ⟨-, hx2, hy1, -⟩ := hxyF Q hQ
        obtain ⟨σ, h1, h2, h3, h4⟩ := exists_seg_cube hx2 hy1
        exact ⟨σ, fun _ => ⟨h1, h2, h3, h4⟩⟩
      · exact ⟨pt 0, fun h' => absurd h' hQ⟩
    choose segQ hsegQ using hseg
    have hZnZ : ∀ Q ∈ Zn, Q ∈ Z' := fun Q hQ => (Finset.mem_filter.1 hQ).1
    have hZfZ : ∀ Q ∈ Zf, Q ∈ Z' := fun Q hQ => (Finset.mem_filter.1 hQ).1
    set S' := S ∪ Zn.image (fun Q => g.ptOf (pF Q)) ∪ Zf.image segQ with hS'
    -- the connected set
    set H := G ∪ g.cubes D with hH
    have hH1 : IsPreconnected (H ∪ ⋃ C ∈ D', gc.cube C) := by
      refine isPreconnected_hub hS.2.2 D' (fun C => gc.cube C) (fun C _ => gc.isPreconnected_cube C)
        fun C hC => ?_
      obtain ⟨z, hz1, hz2⟩ := prime_meets (hn := hn) hC
      exact ⟨z, hz1, Or.inr hz2⟩
    have hH2 : IsPreconnected ((H ∪ ⋃ C ∈ D', gc.cube C) ∪ ⋃ Q ∈ Zf, segSet g.s g.N (segQ Q)) := by
      refine isPreconnected_hub hH1 Zf (fun Q => segSet g.s g.N (segQ Q)) (fun Q _ => isPreconnected_segSet' _)
        fun Q hQ => ⟨xF Q, (hsegQ Q (hZfZ Q hQ)).2.1, Or.inl (Or.inl (hxyF Q (hZfZ Q hQ)).1)⟩
    have hSeq : (⋃ σ ∈ S', segSet g.s g.N σ) ∪ gc.cubes D' =
        (H ∪ ⋃ C ∈ D', gc.cube C) ∪ ⋃ Q ∈ Zf, segSet g.s g.N (segQ Q) := by
      apply Subset.antisymm
      · rintro z (hz | hz)
        · obtain ⟨σ, hσ, hzσ⟩ := mem_iUnion₂.1 hz
          rcases Finset.mem_union.1 hσ with hσ | hσ
          · rcases Finset.mem_union.1 hσ with hσ | hσ
            · exact Or.inl (Or.inl (Or.inl (mem_iUnion₂.2 ⟨σ, hσ, hzσ⟩)))
            · obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.1 hσ
              rw [segSet_ptOf, mem_singleton_iff] at hzσ
              rw [hzσ]
              exact Or.inl (Or.inr ((hpF Q (Finset.mem_filter.1 hQ).2).2))
          · obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.1 hσ
            exact Or.inr (mem_iUnion₂.2 ⟨Q, hQ, hzσ⟩)
        · exact Or.inl (Or.inr hz)
      · rintro z ((hz | hz) | hz)
        · rcases hz with hz | hz
          · obtain ⟨σ, hσ, hzσ⟩ := mem_iUnion₂.1 hz
            exact Or.inl (mem_iUnion₂.2 ⟨σ, Finset.mem_union_left _ (Finset.mem_union_left _ hσ), hzσ⟩)
          · exact Or.inr (cubes_subset_prime (hn := hn) D hz)
        · exact Or.inr hz
        · obtain ⟨Q, hQ, hzQ⟩ := mem_iUnion₂.1 hz
          exact Or.inl (mem_iUnion₂.2 ⟨segQ Q, Finset.mem_union_right _ (Finset.mem_image_of_mem _ hQ), hzQ⟩)
    have hAdm : gc.Adm Z' D' S' := by
      refine ⟨fun σ hσ => ?_, fun Q hQ => ?_, by rw [hSeq]; exact hH2⟩
      · rcases Finset.mem_union.1 hσ with hσ | hσ
        · rcases Finset.mem_union.1 hσ with hσ | hσ
          · exact (hS.1 σ hσ).trans (cubes_subset_prime (hn := hn) Z)
          · obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.1 hσ
            have e : segSet gc.s gc.N (g.ptOf (pF Q)) = {pF Q} := segSet_ptOf (pF Q)
            rw [e, singleton_subset_iff]
            exact mem_iUnion₂.2 ⟨Q, hZnZ Q hQ, (hpF Q (Finset.mem_filter.1 hQ).2).1⟩
        · obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.1 hσ
          refine (hsegQ Q (hZfZ Q hQ)).1.trans ((cube_subset_coarse (hn := hn) _).trans ?_)
          exact fun z hz => mem_iUnion₂.2 ⟨_, K_mem_prime (hQd Q (hZfZ Q hQ)).1, hz⟩
      · by_cases hn' : near Q
        · refine ⟨g.ptOf (pF Q), Finset.mem_union_left _ (Finset.mem_union_right _
            (Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨hQ, hn'⟩))), pF Q, ?_, (hpF Q hn').1⟩
          have e : segSet gc.s gc.N (g.ptOf (pF Q)) = {pF Q} := segSet_ptOf (pF Q)
          rw [e]; rfl
        · exact ⟨segQ Q, Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨hQ, hn'⟩)),
            yF Q, (hsegQ Q hQ).2.2.1, (hxyF Q hQ).2.2.2⟩
    -- the number of the far cubes
    have hcount : (Zf.card : ℝ) * (L * g.a / 2) ≤ (81 : ℕ) * g.cost D S := by
      refine count_mass (isClosed_cubes D)
        ⟨g.centre hD.choose, mem_iUnion₂.2 ⟨_, hD.choose_spec, centre_mem_cube _⟩⟩ hS.2.2 Zf xF
        (fun Q hQ => (hxyF Q (hZfZ Q hQ)).1) (by positivity) ?_ ?_
      · intro Q hQ z hz
        obtain ⟨hsq, hsqc, hK⟩ := hQd Q (hZfZ Q hQ)
        have hfar : ∀ C ∈ prime hn D, ¬ Touch C (K hn (cF Q)) := fun C hC hCt =>
          (Finset.mem_filter.1 hQ).2 ⟨C, hC, hK ▸ hCt⟩
        have := far_of_not_touch_prime hsqc hfar (hxyF Q (hZfZ Q hQ)).2.1 hz
        rw [← hLdef] at this
        rw [dist_comm]
        have : L * g.a / 2 < L * g.a := by nlinarith
        linarith
      · intro p
        refine (Finset.card_le_card ?_).trans (gc.card_near_le p (R := L * g.a + g.a) (by rw [hgca]; nlinarith))
        intro Q hQ
        rw [Finset.mem_filter] at hQ ⊢
        refine ⟨Finset.mem_univ _, ?_⟩
        obtain ⟨hsq, hsqc, hK⟩ := hQd Q (hZfZ Q hQ.1)
        have h1 := dist_coarse_centre_le (hn := hn) hsqc (hxyF Q (hZfZ Q hQ.1)).2.1
        rw [hK, ← hLdef] at h1
        calc dist (gc.centre Q) p ≤ dist (gc.centre Q) (xF Q) + dist (xF Q) p := dist_triangle _ _ _
          _ ≤ (L * g.a / 2 + g.a) + L * g.a / 2 := by
              rw [dist_comm (gc.centre Q) (xF Q), dist_comm (xF Q) p]; exact add_le_add h1 hQ.2
          _ = L * g.a + g.a := by ring
    -- the cost
    have hl0 : ∀ σ, 0 ≤ lenOut g.s g.N (gc.cubes D') σ := fun σ => lenOut_nonneg _ σ
    have hc1 : ∑ σ ∈ S, lenOut g.s g.N (gc.cubes D') σ ≤ g.cost D S :=
      Finset.sum_le_sum fun σ _ => lenOut_anti (cubes_subset_prime (hn := hn) D) σ
    have hc2 : ∑ σ ∈ Zn.image (fun Q => g.ptOf (pF Q)), lenOut g.s g.N (gc.cubes D') σ = 0 :=
      Finset.sum_eq_zero fun σ hσ => by
        obtain ⟨Q, -, rfl⟩ := Finset.mem_image.1 hσ; exact lenOut_ptOf _ _
    have hc3 : ∑ σ ∈ Zf.image segQ, lenOut g.s g.N (gc.cubes D') σ ≤ 2 * g.a * Zf.card := by
      refine (sum_image_le' _ _ hl0).trans ?_
      have hle : ∀ Q ∈ Zf, lenOut g.s g.N (gc.cubes D') (segQ Q) ≤ 2 * g.a := fun Q hQ =>
        (lenOut_le_eu _ _).trans (hsegQ Q (hZfZ Q hQ)).2.2.2
      refine (Finset.sum_le_sum hle).trans ?_
      rw [Finset.sum_const, nsmul_eq_mul]; linarith
    have hfarc : 2 * g.a * Zf.card ≤ 324 / L * g.cost D S := by
      have h81 : ((81 : ℕ) : ℝ) = 81 := by norm_num
      rw [h81] at hcount
      rw [div_mul_eq_mul_div, le_div_iff₀ hL0]
      nlinarith
    have hcost : gc.cost D' S' ≤ (1 + 324 / L) * g.cost D S := by
      show ∑ σ ∈ S', lenOut g.s g.N (gc.cubes D') σ ≤ (1 + 324 / L) * g.cost D S
      refine (sum_union_le' _ _ hl0).trans ?_
      refine (add_le_add (sum_union_le' _ _ hl0) le_rfl).trans ?_
      rw [hc2, add_zero]
      linarith only [hc1, hc3, hfarc]
    exact (a_mul_d_le hAdm).trans hcost
  -- the infimum
  have hne := exists_adm (g := g) hZ hDZ
  have hd0 := d_nonneg (g := g) Z D
  have h324 : L * gc.d Z' D' ≤ (1 + 324 / L) * g.d Z D := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have hc : 0 < 1 + 324 / L := by positivity
    obtain ⟨S, hS, hcS⟩ := exists_adm_le hne (by positivity : 0 < ε / (1 + 324 / L))
    have h1 := hkey S hS
    rw [hgca] at h1
    have h2 : L * g.a * gc.d Z' D' ≤ (1 + 324 / L) * (g.a * (g.d Z D + ε / (1 + 324 / L))) :=
      h1.trans (mul_le_mul_of_nonneg_left hcS hc.le)
    have h3 : (1 + 324 / L) * (g.a * (g.d Z D + ε / (1 + 324 / L))) =
        g.a * ((1 + 324 / L) * g.d Z D + ε) := by field_simp
    rw [h3, mul_comm L, mul_assoc] at h2
    exact le_of_mul_le_mul_left h2 ha
  have h486 : (1 + 324 / L) * g.d Z D ≤ (1 + 486 / L) * g.d Z D := by
    refine mul_le_mul_of_nonneg_right ?_ hd0
    have : 324 / L ≤ 486 / L := div_le_div_of_nonneg_right (by norm_num) hL0.le
    linarith
  exact h324.trans h486

end Grid
end Contracted
end CoreLean

end
