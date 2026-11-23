/-
`def:block-paths` and the transports of the rule `m` in BALABAN_CORE.tex (`7374c382ba1b`): the mean over all orderings
of the four coordinates is the mean over the family `𝐆(y, x)`.

The path which traverses the coordinates in a full ordering `π` depends only on the order in which `π` meets the
coordinates with `n_μ ≠ 0` (`stair_filter`); over the `24` full orderings each ordering of these coordinates occurs
`24/s!` times, `s` their number (`fiber_count`, a finite check). So the sums of `eq:group-mean` over the two families
differ by the factor `24/s!`, and a mean of the one family is a mean of the other (`isMeanOf_full_iff_G`). This identifies
the transports of the index family of the lattice theorems (all full orderings, `axial_regular_G`, `transport_lattice`)
with those of `𝐆(y, x)`: `axial_gauge_full_iff_G`.
-/
import CoreLean.RelativeAverageDefs

open Matrix NormedSpace
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace CoreLean
namespace RelativeAverage

open LatticePaths LatticeKappa RegularAverages BlockPaths AverageHolo MeanTransports

variable {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "GLN" => (Matrix (Fin N) (Fin N) ℂ)ˣ

/-- The `24` orderings of the four coordinates. -/
def P4 : List (List (Fin 4)) := [[0, 1, 2, 3], [0, 1, 3, 2], [0, 2, 1, 3], [0, 2, 3, 1], [0, 3, 1, 2], [0, 3, 2, 1], [1, 0, 2, 3], [1, 0, 3, 2], [1, 2, 0, 3], [1, 2, 3, 0], [1, 3, 0, 2], [1, 3, 2, 0], [2, 0, 1, 3], [2, 0, 3, 1], [2, 1, 0, 3], [2, 1, 3, 0], [2, 3, 0, 1], [2, 3, 1, 0], [3, 0, 1, 2], [3, 0, 2, 1], [3, 1, 0, 2], [3, 1, 2, 0], [3, 2, 0, 1], [3, 2, 1, 0]]

/-- A function on the coordinates from its four values. -/
def bf (b0 b1 b2 b3 : Bool) (i : Fin 4) : Bool := [b0, b1, b2, b3].getD i.val false

set_option maxRecDepth 100000 in
/-- Over the `24` orderings, every ordering of the coordinates with `b = true` occurs `24/s!` times. -/
theorem fiber_count : ∀ b0 b1 b2 b3 : Bool, ∀ π₁ ∈ P4,
    (P4.filter fun π => π.filter (bf b0 b1 b2 b3) = π₁.filter (bf b0 b1 b2 b3)).length *
      (([0, 1, 2, 3] : List (Fin 4)).filter (bf b0 b1 b2 b3)).length.factorial = 24 := by
  decide

set_option maxRecDepth 100000 in
theorem P4_perm : ∀ π ∈ P4, π.Perm [0, 1, 2, 3] := by decide

set_option maxRecDepth 100000 in
theorem perm_P4 : ∀ a b c d : Fin 4, [a, b, c, d].Perm [0, 1, 2, 3] → [a, b, c, d] ∈ P4 := by decide

set_option maxRecDepth 100000 in
theorem P4_nodup : P4.Nodup := by decide

theorem P4_length : P4.length = 24 := rfl

/-- The coordinates with `v_σ = 0` contribute nothing to a staircase path. -/
lemma stair_filter {n : ℕ} [NeZero n] (w : Site n) (v : Fin 4 → ℤ) :
    ∀ (π : List (Fin 4)) (o : Fin 4 → ℤ), stair w v π o = stair w v (π.filter fun σ => decide (v σ ≠ 0)) o
  | [], _ => rfl
  | σ :: π, o => by
    by_cases hσ : v σ = 0
    · have hf : (σ :: π).filter (fun σ => decide (v σ ≠ 0)) = π.filter (fun σ => decide (v σ ≠ 0)) := by
        simp [List.filter_cons, hσ]
      rw [hf, stair, hσ, segZ_zero, List.nil_append, Pi.single_zero, add_zero]
      exact stair_filter w v π o
    · have hf : (σ :: π).filter (fun σ => decide (v σ ≠ 0)) = σ :: π.filter (fun σ => decide (v σ ≠ 0)) := by
        simp [List.filter_cons, hσ]
      rw [hf, stair, stair, stair_filter w v π]

lemma bf_eq (v : Fin 4 → ℤ) : (fun σ => decide (v σ ≠ 0)) =
    bf (decide (v 0 ≠ 0)) (decide (v 1 ≠ 0)) (decide (v 2 ≠ 0)) (decide (v 3 ≠ 0)) := by
  funext σ; fin_cases σ <;> rfl

/-- **The sums over the two families**: for a function `F` of the orderings of the coordinates with `v_σ ≠ 0`,
`Σ_π F(π|_{v ≠ 0}) = (24/s!) Σ_{Γ ∈ Ords v} F(Γ)` over the `24` full orderings `π`. -/
theorem sum_full_eq {M : Type*} [AddCommGroup M] (v : Fin 4 → ℤ) (F : List (Fin 4) → M) :
    (P4.map fun π => F (π.filter fun σ => decide (v σ ≠ 0))).sum =
      (24 / (supp v).length.factorial) • ∑ Γ : Ords v, F Γ.1 := by
  classical
  set b := fun σ : Fin 4 => decide (v σ ≠ 0) with hb
  have hsupp : supp v = ([0, 1, 2, 3] : List (Fin 4)).filter b := rfl
  rw [← List.sum_toFinset _ P4_nodup, Finset.sum_comp]
  -- the image is the set of the orderings of `supp v`
  have himg : P4.toFinset.image (fun π => π.filter b) = (supp v).permutations.toFinset := by
    ext σ
    simp only [Finset.mem_image, List.mem_toFinset, List.mem_permutations]
    constructor
    · rintro ⟨π, hπ, rfl⟩
      rw [hsupp]; exact (P4_perm π hπ).filter b
    · intro hσ
      refine ⟨σ ++ zer v, ?_, ?_⟩
      · have hp : (σ ++ zer v).Perm [0, 1, 2, 3] := (hσ.append_right _).trans (List.filter_append_perm _ _)
        have hl : (σ ++ zer v).length = 4 := by simpa using hp.length_eq
        match hm : σ ++ zer v, hl with
        | [a, b', c, d], _ => exact perm_P4 a b' c d (hm ▸ hp)
      · rw [List.filter_append]
        have h1 : σ.filter b = σ := List.filter_eq_self.2 fun a ha => by
          have := hσ.subset ha
          rw [hsupp, List.mem_filter] at this
          exact this.2
        have h2 : (zer v).filter b = [] := List.filter_eq_nil_iff.2 fun a ha => by
          simp only [zer, List.mem_filter] at ha
          simpa [hb] using ha.2
        rw [h1, h2, List.append_nil]
  rw [himg]
  -- the fibers have `24/s!` elements
  have hfib : ∀ σ ∈ (supp v).permutations.toFinset,
      (P4.toFinset.filter fun π => π.filter b = σ).card = 24 / (supp v).length.factorial := by
    intro σ hσ
    obtain ⟨π₁, hπ₁, hπσ⟩ : ∃ π₁ ∈ P4, π₁.filter b = σ := by
      have : σ ∈ P4.toFinset.image (fun π => π.filter b) := by rw [himg]; exact hσ
      obtain ⟨π₁, h1, h2⟩ := Finset.mem_image.1 this
      exact ⟨π₁, List.mem_toFinset.1 h1, h2⟩
    have hc := fiber_count (decide (v 0 ≠ 0)) (decide (v 1 ≠ 0)) (decide (v 2 ≠ 0)) (decide (v 3 ≠ 0)) π₁ hπ₁
    rw [← bf_eq v, ← hb, hπσ, ← hsupp] at hc
    have hcard : (P4.toFinset.filter fun π => π.filter b = σ).card = (P4.filter fun π => π.filter b = σ).length := by
      rw [show (P4.toFinset.filter fun π => π.filter b = σ) = (P4.filter fun π => π.filter b = σ).toFinset by
        ext π; simp, List.toFinset_card_of_nodup (P4_nodup.filter _)]
    rw [hcard]
    have hf : 0 < (supp v).length.factorial := Nat.factorial_pos _
    rw [← hc, Nat.mul_div_cancel _ hf]
  rw [Finset.sum_congr rfl fun σ hσ => by rw [hfib σ hσ], ← Finset.smul_sum]
  congr 1
  exact (Finset.sum_coe_sort _ F).symm

/-- The orderings of the coordinates as a family indexed by `Fin 24`. -/
def fullOrd (i : Fin P4.length) : List (Fin 4) := P4[i.1]

/-- The index of the increasing ordering. -/
def i0 : Fin P4.length := ⟨0, by rw [P4_length]; norm_num⟩

lemma fullOrd_zero : fullOrd i0 = [0, 1, 2, 3] := rfl

lemma fullOrd_perm (i : Fin P4.length) : (fullOrd i).Perm [0, 1, 2, 3] := P4_perm _ (List.getElem_mem _)

/-- The ordering of the coordinates with `n_μ ≠ 0` in increasing order, as an element of `𝐆(y, x)`. -/
def suppOrd (h : ℕ) (x : Pts h) : Ords (offP h x) :=
  ⟨supp (offP h x), List.mem_toFinset.2 (List.mem_permutations.2 (List.Perm.refl _))⟩

set_option maxHeartbeats 4000000 in
/-- **The two means agree**: `T` is a mean of the values of a configuration on the paths of all full orderings of the
coordinates, with base the increasing ordering, if and only if it is a mean of its values on the paths of `𝐆(y, x)`,
with base the increasing ordering of the coordinates with `n_μ ≠ 0`. -/
theorem isMeanOf_full_iff_G {n : ℕ} [NeZero n] (V : Config N n) (w : Site n) (h : ℕ) (x : Pts h) (T : GLN) :
    IsMeanOf (fun i : Fin P4.length => V.hol (stair w (offP h x) (fullOrd i) 0)) i0 T ↔
      IsMeanOf (fun i : Fin (nG h x) => holG V w h x (enumG h x i)) ((enumG h x).symm (suppOrd h x)) T := by
  set v := offP h x
  set F : List (Fin 4) → Mat := fun σ => LogM (((V.hol (stair w v σ 0) * T⁻¹ : GLN)) : Mat) with hF
  -- the values of the two families
  have hval : ∀ i : Fin P4.length, V.hol (stair w v (fullOrd i) 0) =
      V.hol (stair w v ((fullOrd i).filter fun σ => decide (v σ ≠ 0)) 0) := fun i => by rw [← stair_filter]
  have hG : ∀ Γ : Ords v, holG V w h x Γ = V.hol (stair w v Γ.1 0) := fun Γ => by
    rw [holG, stair_ordG]
  have hbase : V.hol (stair w v (fullOrd i0) 0) = holG V w h x (enumG h x ((enumG h x).symm (suppOrd h x))) := by
    rw [Equiv.apply_symm_apply, hG, fullOrd_zero, stair_filter]
    rfl
  -- the sums
  have hsum : ∑ i : Fin P4.length, LogM (((V.hol (stair w v (fullOrd i) 0) * T⁻¹ : GLN)) : Mat) =
      (24 / (supp v).length.factorial) • ∑ i : Fin (nG h x), LogM (((holG V w h x (enumG h x i) * T⁻¹ : GLN)) : Mat) := by
    have h1 : ∑ i : Fin P4.length, LogM (((V.hol (stair w v (fullOrd i) 0) * T⁻¹ : GLN)) : Mat) =
        (P4.map fun π => F (π.filter fun σ => decide (v σ ≠ 0))).sum := by
      rw [← Fin.sum_univ_fun_getElem]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [hF]
      rw [← stair_filter]
      rfl
    have h2 : ∑ i : Fin (nG h x), LogM (((holG V w h x (enumG h x i) * T⁻¹ : GLN)) : Mat) = ∑ Γ : Ords v, F Γ.1 := by
      rw [← Equiv.sum_comp (enumG h x).symm]
      refine Finset.sum_congr rfl fun Γ _ => ?_
      rw [Equiv.apply_symm_apply, hG]
    rw [h1, h2, sum_full_eq v F]
  have hc0 : (24 / (supp v).length.factorial) ≠ 0 := by
    have hl : (supp v).length ≤ 4 := by
      have : (supp v).length ≤ ([0, 1, 2, 3] : List (Fin 4)).length := List.length_filter_le _ _
      simpa using this
    have hf : (supp v).length.factorial ≤ 24 := by
      calc (supp v).length.factorial ≤ (4 : ℕ).factorial := Nat.factorial_le hl
        _ = 24 := rfl
    exact (Nat.div_pos hf (Nat.factorial_pos _)).ne'
  unfold IsMeanOf
  beta_reduce
  rw [hbase, hsum]
  constructor
  · rintro ⟨Z, hZ, hT, hs⟩
    refine ⟨Z, hZ, hT, ?_⟩
    rw [← Nat.cast_smul_eq_nsmul ℂ] at hs
    rcases smul_eq_zero.1 hs with h0 | h0
    · exact absurd (by exact_mod_cast h0) hc0
    · exact h0
  · rintro ⟨Z, hZ, hT, hs⟩
    exact ⟨Z, hZ, hT, by rw [hs, smul_zero]⟩

/-- **The axial gauge for the two families**: the condition of `axial_regular_G` on the transports (the identity is a mean
of the values on the paths of all full orderings, for every offset `m` of the block) is the condition that the identity
is a mean of the values on the paths of `𝐆(y, x)`, for every point `x` of the block: the transports of the rule `m` of
the core are trivial. -/
theorem axial_gauge_full_iff_G {n : ℕ} [NeZero n] (V : Config N n) (w : Site n) (h : ℕ) :
    (∀ m, AxialReference.InM h m →
      IsMeanOf (fun i : Fin P4.length => V.hol (stair w m (fullOrd i) 0)) i0 1) ↔
      ∀ x : Pts h, IsMeanOf (fun i : Fin (nG h x) => holG V w h x (enumG h x i)) ((enumG h x).symm (suppOrd h x)) 1 := by
  constructor
  · intro hm x
    exact (isMeanOf_full_iff_G V w h x 1).1 (hm _ (offP_inM h x))
  · intro hx m hm
    obtain ⟨x, rfl⟩ := offP_surj h hm
    exact (isMeanOf_full_iff_G V w h x 1).2 (hx x)

section AxialStraight

open BoxGeometry AxialStraightLattice AxialReference AxialRegular

/-- **`cor:axial-straight` with the transports of `𝐆(y, x)`**: `axial_regular_G` with its hypothesis on the transports
stated for the family `𝐆(y, x)` of the core (the identity is a mean of the values on the paths of `𝐆(y, x)` at every point
of every block, i.e. the transports of the rule `m` are trivial), through `axial_gauge_full_iff_G`. -/
theorem axial_regular_GG (G : GaugeGroup N) (hG : IsClosed G.mats) (hN : 1 ≤ N) (h : ℕ) (hh : 1 ≤ h) :
    ∃ c : ℝ, 0 < c ∧ ∀ (j : ℕ), 1 ≤ j → ∀ (μ : Fin 4) (nn : ℕ → ℕ) [∀ i, NeZero (nn i)],
      (∀ i, i < j → 3 * Lz h ^ (j - i) ≤ (nn i : ℤ)) →
      ∀ (base : ∀ i, Site (nn i)) (V : ∀ i, Config N (nn i)), (∀ i, i < j → IsGField G (V i)) →
      ∀ α : ℝ, 0 ≤ α → α ≤ c →
      (∀ μ' ν' z, PlaqIn (Reg h j μ 0 (base 0)) μ' ν' z →
        hs (((plaq (V 0) μ' ν' z : GLN) : Mat) - 1) ≤ α * ((((2 * h + 1 : ℕ) : ℝ) ^ 2)⁻¹) ^ j) →
      (∀ i, i < j → ∀ z, Lat (Lz h) (i + 1) z → InB (Lz h) j μ z → ∀ x : Pts h,
        IsMeanOf (fun ι => holG (V i) (img h (base i) i z) h x (enumG h x ι)) ((enumG h x).symm (suppOrd h x)) 1) →
      (∀ i, i < j → ∀ ct : Bd (Lz h) j μ (i + 1),
        (V (i + 1)).val ⟨img h (base (i + 1)) (i + 1) ct.1.1, ct.1.2, true⟩ =
          avgB G (V i) (img h (base i) i ct.1.1) ct.1.2 (2 * h + 1) (offP h) (ordG h)) →
      ∀ i, i ≤ j → ∀ b : Bd (Lz h) j μ i,
        ‖(((V i).val ⟨img h (base i) i b.1.1, b.1.2, true⟩ : GLN) : Mat) -
          sval (Lz h) j μ (1 : Mat) (((V j).val ⟨img h (base j) j 0, μ, true⟩ : GLN) : Mat) i b‖ ≤
          4 * (59 * Real.sqrt N) * α := by
  obtain ⟨c, hc, H⟩ := axial_regular_G G hG hN h hh
  refine ⟨c, hc, fun j hj μ nn _ hn base V hV α hα hαc hU haxial hrel => ?_⟩
  exact H j hj μ nn hn base V hV α hα hαc hU (k := P4.length) (by rw [P4_length]; norm_num) fullOrd fullOrd_perm i0
    fullOrd_zero (fun i hi z hz hB => (axial_gauge_full_iff_G (V i) (img h (base i) i z) h).2 (haxial i hi z hz hB))
    hrel

end AxialStraight

set_option maxHeartbeats 4000000 in
/-- **`lem:moved-transports`(iii) for the family `𝐆(y, x)`**: for a `G`-valued field whose plaquettes in a box containing
the block are at most `β`, and the transport `T = U(y, x)` of `𝐆(y, x)` (a mean of the values on its paths), every path
`Γ ∈ 𝐆(y, x)` has `U(Γ) = e^{iX_Γ}T` with `‖X_Γ‖ ≤ 4(π/2)·6h²β`: `moved_iii_lattice` for the full orderings, whose mean is
`T` by `isMeanOf_full_iff_G`, and every path of `𝐆(y, x)` is the path of a full ordering (`stair_filter`). -/
theorem moved_iii_G (G : GaugeGroup N) (hG : IsClosed G.mats) :
    ∃ r : ℝ, 0 < r ∧ ∀ {n : ℕ} [NeZero n] (U : Config N n), IsGField G U → ∀ (y : Site n) (lo hi : Fin 4 → ℤ) (β : ℝ),
      0 ≤ β → PlaqBound U (boxR y lo hi) β → ∀ (h : ℕ) (x : Pts h), LatticePaths.InBox lo hi 0 → LatticePaths.InBox lo hi (offP h x) →
      6 * (h : ℝ) ^ 2 * β ≤ r → 512 * (Real.pi / 2 * (6 * (h : ℝ) ^ 2 * β)) ≤ 1 →
      ∀ T : GLN, IsMeanOf (fun i : Fin (nG h x) => holG U y h x (enumG h x i)) ((enumG h x).symm (suppOrd h x)) T →
      ∃ X : Ords (offP h x) → Mat, ∀ Γ, holG U y h x Γ = expU (Complex.I • X Γ) * T ∧
        ‖X Γ‖ ≤ 4 * (Real.pi / 2 * (6 * (h : ℝ) ^ 2 * β)) := by
  obtain ⟨r, hr, H⟩ := moved_iii_lattice G hG
  refine ⟨r, hr, fun U hU y lo hi β hβ hP h x h0 hm hbr hb T hT => ?_⟩
  have hTf := (isMeanOf_full_iff_G U y h x T).2 hT
  have hmh : ∀ σ, (((offP h x) σ).natAbs : ℝ) ≤ (h : ℝ) := fun σ => by
    have := offP_inM h x σ
    exact_mod_cast (by omega : ((offP h x) σ).natAbs ≤ h)
  obtain ⟨X, hX⟩ := H U hU y lo hi β hβ hP (offP h x) h0 hm (h : ℝ) hmh hbr hb (k := P4.length)
    (by rw [P4_length]; norm_num) fullOrd fullOrd_perm i0 fullOrd_zero T hTf
  -- every path of `𝐆(y, x)` is the path of a full ordering
  have hidx : ∀ Γ : Ords (offP h x), ∃ i : Fin P4.length,
      (fullOrd i).filter (fun σ => decide (offP h x σ ≠ 0)) = Γ.1 := fun Γ => by
    have hp : (Γ.1 ++ zer (offP h x)).Perm [0, 1, 2, 3] :=
      ((ords_perm Γ).append_right _).trans (List.filter_append_perm _ _)
    have hl : (Γ.1 ++ zer (offP h x)).length = 4 := by simpa using hp.length_eq
    have hmem : Γ.1 ++ zer (offP h x) ∈ P4 := by
      match hm : Γ.1 ++ zer (offP h x), hl with
      | [a, b', c, d], _ => exact perm_P4 a b' c d (hm ▸ hp)
    obtain ⟨i, hi, hget⟩ := List.getElem_of_mem hmem
    refine ⟨⟨i, hi⟩, ?_⟩
    simp only [fullOrd, hget, List.filter_append]
    have h1 : Γ.1.filter (fun σ => decide (offP h x σ ≠ 0)) = Γ.1 := List.filter_eq_self.2 fun a ha => by
      have := (ords_perm Γ).subset ha
      simp only [supp, List.mem_filter] at this
      exact this.2
    have h2 : (zer (offP h x)).filter (fun σ => decide (offP h x σ ≠ 0)) = [] :=
      List.filter_eq_nil_iff.2 fun a ha => by
        simp only [zer, List.mem_filter] at ha
        simpa using ha.2
    rw [h1, h2, List.append_nil]
  choose idx hidx' using hidx
  refine ⟨fun Γ => X (idx Γ), fun Γ => ?_⟩
  have e : holG U y h x Γ = U.hol (stair y (offP h x) (fullOrd (idx Γ)) 0) := by
    rw [holG, stair_ordG, stair_filter y (offP h x) (fullOrd (idx Γ)), hidx' Γ]
  rw [e]
  exact hX (idx Γ)

end RelativeAverage
end CoreLean

end
