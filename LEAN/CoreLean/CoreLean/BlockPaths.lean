/-
`def:block-paths` of BALABAN_CORE.tex (`293a3f02bbc3`): the family `𝐆(y, x)` of the paths from the centre
of a block to its points, and the results on the averages for this family.
* `Pts h`, `offP`: the points `x = y + Σ n_μ e_μ`, `|n_μ| ≤ h`, of a block, by `n_μ + h ∈ Fin L`; `offP` is a
  bijection onto `[-h, h]⁴` (`offP_inM`, `offP_inj`, `offP_surj`) and there are `L⁴` points (`card_pts`).
* `Ords v`: the orderings of the coordinates `μ` with `n_μ ≠ 0`; `ordG` completes an ordering by the
  coordinates with `n_μ = 0`, which contribute no bonds (`stair_ordG`). So the path `stair y n (ordG x Γ) 0`
  traverses the coordinates with `n_μ ≠ 0` in the order `Γ`, `|n_μ|` bonds in the direction of the sign of
  `n_μ` for each: the family `𝐆(y, x)`, one path for every ordering.
* `regular_averages_i_G`, `regular_averages_ii_G`, `axial_regular_G`: `prop:regular-averages`(i), (ii) and
  `cor:axial-straight` for this family, with the mean `L⁻⁴Σ_{x ∈ B(y₀)}`.
-/
import CoreLean.AxialRegular

open Matrix NormedSpace
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace CoreLean

namespace BlockPaths

open LatticePaths LatticeKappa BoxGeometry AxialStraightLattice AxialReference RegularAverages AxialRegular

set_option linter.unusedSectionVars false

variable {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "GLN" => (Matrix (Fin N) (Fin N) ℂ)ˣ

/-! ### The points of a block -/

/-- The points of a block, by `n_μ + h`. -/
abbrev Pts (h : ℕ) := Fin 4 → Fin (2 * h + 1)

/-- The offset `n = x - y` of the point. -/
def offP (h : ℕ) (x : Pts h) : Fin 4 → ℤ := fun σ => ((x σ : ℕ) : ℤ) - h

lemma offP_inM (h : ℕ) (x : Pts h) : InM h (offP h x) := fun σ => by
  have := (x σ).isLt
  simp only [offP]
  omega

lemma offP_inj (h : ℕ) {x x' : Pts h} (e : offP h x = offP h x') : x = x' := by
  funext σ
  have := congrFun e σ
  simp only [offP] at this
  exact Fin.ext (by omega)

lemma offP_surj (h : ℕ) {v : Fin 4 → ℤ} (hv : InM h v) : ∃ x : Pts h, offP h x = v := by
  refine ⟨fun σ => ⟨(v σ + h).toNat, by have := hv σ; omega⟩, funext fun σ => ?_⟩
  have := hv σ
  simp only [offP]
  omega

lemma card_pts (h : ℕ) : Fintype.card (Pts h) = (2 * h + 1) ^ 4 := by simp

/-! ### The orderings -/

/-- The coordinates `μ` with `n_μ ≠ 0`, in increasing order. -/
def supp (v : Fin 4 → ℤ) : List (Fin 4) := ([0, 1, 2, 3] : List (Fin 4)).filter fun σ => decide (v σ ≠ 0)

/-- The coordinates `μ` with `n_μ = 0`. -/
def zer (v : Fin 4 → ℤ) : List (Fin 4) := ([0, 1, 2, 3] : List (Fin 4)).filter fun σ => !decide (v σ ≠ 0)

/-- The orderings of the coordinates with `n_μ ≠ 0`. -/
abbrev Ords (v : Fin 4 → ℤ) := ↥((supp v).permutations.toFinset)

lemma ords_perm {v : Fin 4 → ℤ} (Γ : Ords v) : Γ.1.Perm (supp v) :=
  List.mem_permutations.1 (List.mem_toFinset.1 Γ.2)

lemma card_ords_pos (v : Fin 4 → ℤ) : 0 < Fintype.card (Ords v) := by
  rw [Fintype.card_coe]
  exact Finset.card_pos.2 ⟨supp v, List.mem_toFinset.2 (List.mem_permutations.2 (List.Perm.refl _))⟩

/-- The number of orderings is `|{μ | n_μ ≠ 0}|!`. -/
lemma card_ords (v : Fin 4 → ℤ) : Fintype.card (Ords v) = (supp v).length.factorial := by
  have hnd : (supp v).Nodup := List.Nodup.filter _ (by decide)
  rw [Fintype.card_coe, List.toFinset_card_of_nodup (List.nodup_permutations _ hnd),
    List.length_permutations]

/-- The ordering `Γ` of the coordinates with `n_μ ≠ 0`, followed by the others. -/
def ordG (h : ℕ) (x : Pts h) (Γ : Ords (offP h x)) : List (Fin 4) := Γ.1 ++ zer (offP h x)

lemma ordG_perm (h : ℕ) (x : Pts h) (Γ : Ords (offP h x)) : (ordG h x Γ).Perm [0, 1, 2, 3] :=
  ((ords_perm Γ).append_right _).trans (List.filter_append_perm _ _)

variable {n : ℕ} [NeZero n]

lemma stair_zero_coords (y : Site n) (v : Fin 4 → ℤ) :
    ∀ (l : List (Fin 4)) (o : Fin 4 → ℤ), (∀ σ ∈ l, v σ = 0) → stair y v l o = []
  | [], _, _ => rfl
  | σ :: l, o, hl => by
    simp only [stair, hl σ (by simp), segZ_zero, List.nil_append]
    exact stair_zero_coords y v l _ fun τ hτ => hl τ (by simp [hτ])

/-- The coordinates with `n_μ = 0` contribute no bonds: the path of `ordG x Γ` is the path which traverses
the coordinates with `n_μ ≠ 0` in the order `Γ`. -/
lemma stair_ordG (h : ℕ) (y : Site n) (x : Pts h) (Γ : Ords (offP h x)) (o : Fin 4 → ℤ) :
    stair y (offP h x) (ordG h x Γ) o = stair y (offP h x) Γ.1 o := by
  rw [ordG, stair_append, stair_zero_coords y _ (zer (offP h x)) _ fun σ hσ => ?_, List.append_nil]
  simpa [zer] using (List.mem_filter.1 hσ).2

/-! ### The averages for the family `𝐆` -/

/-- **`prop:regular-averages`(i)** for the family `𝐆(y, x)` of `def:block-paths`: with `L = 2h + 1`,
`|M(U)(∂p') - id| ≤ L⁻⁴Σ_{x ∈ B(y₀)}Σ_{p ⊂ p'_x}|U(∂p) - id| + 2²⁷NL⁴α² ≤ L²α + 2²⁷NL⁴α²`. -/
theorem regular_averages_i_G (G : GaugeGroup N) (hG : IsClosed G.mats) (hN : 1 ≤ N) :
    ∃ c : ℝ, 0 < c ∧ ∀ {n : ℕ} [NeZero n] (U : Config N n), IsGField G U →
      ∀ (h : ℕ), 4 * h + 4 ≤ n → ∀ (y₀ : Site n) (μ ν : Fin 4), μ ≠ ν →
      ∀ α : ℝ, 0 ≤ α → α * ((2 * h + 1 : ℕ) : ℝ) ^ 2 ≤ c →
      (∀ μ' ν' z, PlaqIn (boxR y₀ (loD h) (hiD h μ ν)) μ' ν' z →
        hs (((plaq U μ' ν' z : GLN) : Mat) - 1) ≤ α) →
      hs (((plaqAvg G U y₀ μ ν (2 * h + 1) (offP h) (ordG h) : GLN) : Mat) - 1) ≤
          (((2 * h + 1 : ℕ) : ℝ) ^ 4)⁻¹ * ∑ x : Pts h, ∑ i ∈ Finset.range (2 * h + 1),
            ∑ j ∈ Finset.range (2 * h + 1),
              hs (((plaq U μ ν (ofs y₀ (offP h x) + i • unit n μ + j • unit n ν) : GLN) : Mat) - 1) +
            2 ^ 27 * N * ((2 * h + 1 : ℕ) : ℝ) ^ 4 * α ^ 2 ∧
        (((2 * h + 1 : ℕ) : ℝ) ^ 4)⁻¹ * ∑ x : Pts h, ∑ i ∈ Finset.range (2 * h + 1),
            ∑ j ∈ Finset.range (2 * h + 1),
              hs (((plaq U μ ν (ofs y₀ (offP h x) + i • unit n μ + j • unit n ν) : GLN) : Mat) - 1) ≤
          ((2 * h + 1 : ℕ) : ℝ) ^ 2 * α := by
  obtain ⟨c, hc, HI⟩ := regular_averages_i G hG hN
  refine ⟨c, hc, fun {n} _ U hU h hn y₀ μ ν hμν α hα hαc hplq => ?_⟩
  have H := HI U hU h hn y₀ μ ν hμν (ι := Pts h) (P := fun x => Ords (offP h x)) (offP h) (ordG h)
    (by rw [card_pts]; positivity) (fun x => card_ords_pos _) (offP_inM h) (ordG_perm h) α hα hαc hplq
  have hcard : (Fintype.card (Pts h) : ℝ) = ((2 * h + 1 : ℕ) : ℝ) ^ 4 := by
    rw [card_pts]; push_cast; ring
  simpa only [meanP, hcard] using H

/-- **`prop:regular-averages`(ii)** for the family `𝐆(y, x)`. -/
theorem regular_averages_ii_G (G : GaugeGroup N) (hG : IsClosed G.mats) (hN : 1 ≤ N) :
    ∃ c₂ : ℝ, 0 < c₂ ∧ ∀ (h : ℕ), 1 ≤ h → ∀ (nl : ℕ) (μ ν : Fin 4), μ ≠ ν →
      ∀ (nn : ℕ → ℕ) [∀ l, NeZero (nn l)], (∀ l, l < nl → 4 * h + 4 ≤ nn l) →
      ∀ (base : ∀ l, Site (nn l)) (V : ∀ l, Config N (nn l)), (∀ l, l ≤ nl → IsGField G (V l)) →
      (∀ l, l < nl → ∀ (ρ : Fin 4) (x : Fin 4 → ℤ), Lat (Lz h) (l + 1) x → InR h nl μ ν (l + 1) x →
        InR h nl μ ν (l + 1) (x + Lz h ^ (l + 1) • Pi.single ρ 1) →
        V (l + 1) ρ (img h (base (l + 1)) (l + 1) x) =
          avgB G (V l) (img h (base l) l x) ρ (2 * h + 1) (offP h) (ordG h)) →
      ∀ α : ℝ, 0 ≤ α → α ≤ c₂ →
      (∀ μ' ν' x, PlaqR h nl μ ν 0 μ' ν' x →
        hs (((plaq (V 0) μ' ν' (img h (base 0) 0 x) : GLN) : Mat) - 1) ≤
          α * ((((2 * h + 1 : ℕ) : ℝ) ^ 2)⁻¹) ^ nl) →
      hs (((plaq (V nl) μ ν (base nl) : GLN) : Mat) - 1) ≤ α + 2 * (2 ^ 27 * N) * α ^ 2 ∧
        α + 2 * (2 ^ 27 * N) * α ^ 2 ≤ 2 * α := by
  obtain ⟨c₂, hc₂, HII⟩ := regular_averages_ii G hG hN
  refine ⟨c₂, hc₂, fun h hh nl μ ν hμν nn _ hn base V hV hrel α hα hαc hbase => ?_⟩
  exact HII h hh nl μ ν hμν nn hn base V hV (ι := Pts h) (P := fun x => Ords (offP h x)) (offP h)
    (ordG h) (by rw [card_pts]; positivity) (fun x => card_ords_pos _) (offP_inM h) (ordG_perm h) hrel
    α hα hαc hbase

/-- **`cor:axial-straight`** for the family `𝐆(y, x)`, with the plaquette hypothesis at the finest scale:
the constant `c` depends on `G`, `N`, and `L` only. -/
theorem axial_regular_G (G : GaugeGroup N) (hG : IsClosed G.mats) (hN : 1 ≤ N) (h : ℕ) (hh : 1 ≤ h) :
    ∃ c : ℝ, 0 < c ∧ ∀ (j : ℕ), 1 ≤ j → ∀ (μ : Fin 4) (nn : ℕ → ℕ) [∀ i, NeZero (nn i)],
      (∀ i, i < j → 3 * Lz h ^ (j - i) ≤ (nn i : ℤ)) →
      ∀ (base : ∀ i, Site (nn i)) (V : ∀ i, Config N (nn i)), (∀ i, i < j → IsGField G (V i)) →
      ∀ α : ℝ, 0 ≤ α → α ≤ c →
      (∀ μ' ν' z, PlaqIn (Reg h j μ 0 (base 0)) μ' ν' z →
        hs (((plaq (V 0) μ' ν' z : GLN) : Mat) - 1) ≤ α * ((((2 * h + 1 : ℕ) : ℝ) ^ 2)⁻¹) ^ j) →
      ∀ {k : ℕ} (_hk : 0 < k) (l : Fin k → List (Fin 4)), (∀ Γ, (l Γ).Perm [0, 1, 2, 3]) →
      ∀ x₀, l x₀ = [0, 1, 2, 3] →
      (∀ i, i < j → ∀ z, Lat (Lz h) (i + 1) z → InB (Lz h) j μ z → ∀ m, InM h m →
        IsMeanOf (fun Γ => (V i).hol (stair (img h (base i) i z) m (l Γ) 0)) x₀ 1) →
      (∀ i, i < j → ∀ ct : Bd (Lz h) j μ (i + 1),
        (V (i + 1)).val ⟨img h (base (i + 1)) (i + 1) ct.1.1, ct.1.2, true⟩ =
          avgB G (V i) (img h (base i) i ct.1.1) ct.1.2 (2 * h + 1) (offP h) (ordG h)) →
      ∀ i, i ≤ j → ∀ b : Bd (Lz h) j μ i,
        ‖(((V i).val ⟨img h (base i) i b.1.1, b.1.2, true⟩ : GLN) : Mat) -
          sval (Lz h) j μ (1 : Mat) (((V j).val ⟨img h (base j) j 0, μ, true⟩ : GLN) : Mat) i b‖ ≤
          4 * (59 * Real.sqrt N) * α := by
  obtain ⟨c, hc, H⟩ := axial_regular G hG hN h hh (ι := Pts h) (P := fun x => Ords (offP h x))
  refine ⟨c, hc, fun j hj μ nn _ hn base V hV α hα hαc hU k hk l hl x₀ hx₀ haxial hrel => ?_⟩
  exact H j hj μ nn hn base V hV α hα hαc hU (offP h) (ordG h) (by rw [card_pts]; positivity)
    (fun x => card_ords_pos _) (ordG_perm h) (offP_inM h) hk l hl x₀ hx₀ haxial hrel

end BlockPaths

end CoreLean

end
