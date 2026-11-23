/-
The reference field `V₀` of the proof of `cor:axial-straight` of BALABAN_CORE.tex (`46b63b49e8d2`), on the
lattice `T^{(i)}` in its own units (`Site n`, `n ≥ 2L` points per side), and the check of the hypotheses
(i)–(iii) of `lem:axial-smallness` for it.

The bond `c̃` runs from `y = c̃₋` to `y + Le_μ = c̃₊`, `L = 2h + 1`. The offset of a site `x` from `y` is
represented in `[-h, n - 1 - h]` (`rep`), uniquely; `B(c̃₋)` and `B(c̃₊)` are the sites whose offsets lie
in the boxes `|v_σ| ≤ h` and `|v_σ - Lδ_{σμ}| ≤ h` (`Bm`, `Bp`). `V₀` is `W` on the bonds `(x, x + e_μ)`
from `B(c̃₋)` to `B(c̃₊)` and `id` on all other positive bonds.

Proved: (i) every plaquette of `V₀` with corners in `B(c̃₋) ∪ B(c̃₊)` equals `id`; (ii) `V₀` is `id` along
every staircase path of `𝐆(c̃_±, x)`, so that its mean transports are `id`; (iii) `V₀([c̃]) = W`, every
loop of `c̃` has the holonomy `id`, and `M(V₀)(c̃) = W` (`def:average`).
-/
import CoreLean.LatticeKappa

open Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace CoreLean

namespace AxialReference

open LatticePaths LatticeKappa MeanTransports Classical

set_option linter.unusedSectionVars false

variable {N n : ℕ} [NeZero n]

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "GLN" => (Matrix (Fin N) (Fin N) ℂ)ˣ

/-! ### Offsets -/

variable (y : Site n) (h : ℕ)

/-- The representative in `[-h, n - 1 - h]` of the offset `x_σ - y_σ`. -/
def rep (x : Site n) (σ : Fin 4) : ℤ := ((x σ - y σ + (h : ZMod n)).val : ℤ) - h

lemma rep_cast (x : Site n) (σ : Fin 4) : ((rep y h x σ : ℤ) : ZMod n) = x σ - y σ := by
  unfold rep
  push_cast
  rw [ZMod.natCast_zmod_val]
  ring

lemma rep_range (x : Site n) (σ : Fin 4) : -(h : ℤ) ≤ rep y h x σ ∧ rep y h x σ ≤ n - 1 - h := by
  have := ZMod.val_lt (x σ - y σ + (h : ZMod n))
  unfold rep
  omega

lemma rep_unique {x : Site n} {σ : Fin 4} {a : ℤ} (ha1 : -(h : ℤ) ≤ a) (ha2 : a ≤ n - 1 - h)
    (hc : ((a : ℤ) : ZMod n) = x σ - y σ) : a = rep y h x σ := by
  have e : ((a : ℤ) : ZMod n) = ((rep y h x σ : ℤ) : ZMod n) := hc.trans (rep_cast y h x σ).symm
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at e
  obtain ⟨t, ht⟩ := e
  obtain ⟨r1, r2⟩ := rep_range y h x σ
  have hn : (0 : ℤ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have a1 : (n : ℤ) * t < n * 1 := by rw [← ht]; linarith
  have a2 : (n : ℤ) * (-1) < n * t := by rw [← ht]; linarith
  have b1 := lt_of_mul_lt_mul_left a1 hn.le
  have b2 := lt_of_mul_lt_mul_left a2 hn.le
  have : t = 0 := by omega
  rw [this, mul_zero] at ht
  linarith

lemma rep_ofs {v : Fin 4 → ℤ} (hv : ∀ σ, -(h : ℤ) ≤ v σ ∧ v σ ≤ n - 1 - h) : rep y h (ofs y v) = v := by
  funext σ
  refine (rep_unique y h (hv σ).1 (hv σ).2 ?_).symm
  simp [ofs]

lemma rep_add_unit_ne {x : Site n} {κ σ : Fin 4} (h' : σ ≠ κ) :
    rep y h (x + unit n κ) σ = rep y h x σ := by
  simp [rep, unit, Pi.single_eq_of_ne h']

/-! ### The two blocks -/

/-- The offsets of `B(c̃₋)`. -/
def InM (v : Fin 4 → ℤ) : Prop := ∀ σ, -(h : ℤ) ≤ v σ ∧ v σ ≤ h

/-- The offsets of `B(c̃₊)`, `c̃₊ = y + (2h + 1)e_μ`. -/
def InP (μ : Fin 4) (v : Fin 4 → ℤ) : Prop :=
  ∀ σ, (σ ≠ μ → -(h : ℤ) ≤ v σ ∧ v σ ≤ h) ∧ (σ = μ → (h : ℤ) + 1 ≤ v σ ∧ v σ ≤ 3 * h + 1)

/-- `x ∈ B(c̃₋)`. -/
def Bm (x : Site n) : Prop := InM h (rep y h x)

/-- `x ∈ B(c̃₊)`. -/
def Bp (μ : Fin 4) (x : Site n) : Prop := InP h μ (rep y h x)

variable {y h}

lemma disj {μ : Fin 4} {x : Site n} (hm : Bm y h x) (hp : Bp y h μ x) : False := by
  have a := (hm μ).2
  have b := ((hp μ).2 rfl).1
  linarith

/-- Inside `B(c̃₋) ∪ B(c̃₊)` the block is determined by the coordinate `μ` of the offset. -/
lemma blk_det {μ : Fin 4} {x x' : Site n} (hx : Bm y h x ∨ Bp y h μ x) (hx' : Bm y h x' ∨ Bp y h μ x')
    (he : rep y h x μ = rep y h x' μ) : (Bm y h x ↔ Bm y h x') ∧ (Bp y h μ x ↔ Bp y h μ x') := by
  have k1 : ∀ z, Bm y h z → rep y h z μ ≤ h := fun z hz => (hz μ).2
  have k2 : ∀ z, Bp y h μ z → (h : ℤ) + 1 ≤ rep y h z μ := fun z hz => ((hz μ).2 rfl).1
  rcases hx with a | a <;> rcases hx' with b | b
  · exact ⟨iff_of_true a b, iff_of_false (fun c => disj a c) (fun c => disj b c)⟩
  · exfalso; have := k1 x a; have := k2 x' b; linarith
  · exfalso; have := k2 x a; have := k1 x' b; linarith
  · exact ⟨iff_of_false (fun c => disj c a) (fun c => disj c b), iff_of_true a b⟩

variable (hn : 4 * h + 2 ≤ n)
include hn

lemma bm_ofs {v : Fin 4 → ℤ} (hv : InM h v) : Bm y h (ofs y v) := by
  unfold Bm
  rw [rep_ofs y h (fun σ => ⟨(hv σ).1, by have := (hv σ).2; omega⟩)]
  exact hv

lemma bp_ofs {μ : Fin 4} {v : Fin 4 → ℤ} (hv : InP h μ v) : Bp y h μ (ofs y v) := by
  unfold Bp
  have hr : ∀ σ, -(h : ℤ) ≤ v σ ∧ v σ ≤ n - 1 - h := fun σ => by
    by_cases hσ : σ = μ
    · have := (hv σ).2 hσ; constructor <;> omega
    · have := (hv σ).1 hσ; constructor <;> omega
  rw [rep_ofs y h hr]
  exact hv

omit hn

/-! ### The field `V₀` -/

variable (y h)

/-- `V₀`: `W` on the bonds `(x, x + e_μ)` from `B(c̃₋)` to `B(c̃₊)`, `id` on the other positive bonds. -/
def V0 (μ : Fin 4) (W : GLN) : Config N n :=
  fun ρ x => if ρ = μ ∧ Bm y h x ∧ Bp y h μ (x + unit n μ) then W else 1

variable {y h}

lemma V0_mem {G : GaugeGroup N} {μ : Fin 4} {W : GLN} (hW : W ∈ G.carrier) :
    IsGField G (V0 y h μ W) := fun ρ x => by
  unfold V0
  split_ifs
  · exact hW
  · exact G.carrier.one_mem

/-- `V₀ = id` on a bond with both ends in one of the two blocks. -/
lemma val_inside {μ : Fin 4} {W : GLN} (t : Bond n)
    (ht : (Bm y h t.site ∧ Bm y h t.plus) ∨ (Bp y h μ t.site ∧ Bp y h μ t.plus)) :
    (V0 y h μ W).val t = 1 := by
  obtain ⟨x, ρ, s⟩ := t
  cases s with
  | true =>
    simp only [Bond.plus, ↓reduceIte] at ht
    simp only [Config.val, ↓reduceIte, V0]
    rw [ite_eq_right_iff]
    rintro ⟨rfl, hm, hp⟩
    rcases ht with ⟨_, h2⟩ | ⟨h1, _⟩
    · exact (disj h2 hp).elim
    · exact (disj hm h1).elim
  | false =>
    simp only [Bond.plus, Bool.false_eq_true, ↓reduceIte] at ht
    simp only [Config.val, Bool.false_eq_true, ↓reduceIte, V0]
    rw [inv_eq_one, ite_eq_right_iff]
    rintro ⟨rfl, hm, hp⟩
    rw [sub_add_cancel] at hp
    rcases ht with ⟨h1, _⟩ | ⟨_, h2⟩
    · exact (disj h1 hp).elim
    · exact (disj hm h2).elim

lemma hol_one {U : Config N n} : ∀ γ : List (Bond n), (∀ t ∈ γ, U.val t = 1) → U.hol γ = 1
  | [], _ => by simp
  | b :: γ, hγ => by
    rw [hol_cons, hγ b (by simp), hol_one γ (fun t ht => hγ t (by simp [ht])), one_mul]

/-! ### (ii): the transports of `V₀` -/

include hn in
/-- `V₀ = id` along the staircase paths from `c̃₋` to the points of `B(c̃₋)`. -/
lemma hol_stair_minus {μ : Fin 4} {W : GLN} {m : Fin 4 → ℤ} (hm : InM h m) {l : List (Fin 4)}
    (hl : l.Nodup) : (V0 y h μ W).hol (stair y m l 0) = 1 := by
  refine hol_one _ fun t ht => val_inside t (Or.inl ?_)
  obtain ⟨v, v', hv, hv', hs, hp⟩ := mem_stair y m l 0 hl t ht
  have key : ∀ w, Partial 0 m l w → InM h w := fun w hw σ => by
    obtain ⟨h1, h2⟩ := hw σ
    obtain ⟨a1, a2⟩ := hm σ
    by_cases hσ : σ ∈ l
    · have := h2 hσ; simp only [Pi.zero_apply, sub_zero] at this; unfold LatticePaths.Btw at this; omega
    · have := h1 hσ; simp only [Pi.zero_apply] at this; omega
  rw [hs, hp]
  exact ⟨bm_ofs hn (key v hv), bm_ofs hn (key v' hv')⟩

include hn in
/-- `V₀ = id` along the staircase paths from `c̃₊` to the points of `B(c̃₊)`. -/
lemma hol_stair_plus {μ : Fin 4} {W : GLN} {m : Fin 4 → ℤ} (hm : InM h m) {l : List (Fin 4)}
    (hl : l.Nodup) :
    (V0 y h μ W).hol (stair (ofs y ((Pi.single μ ((2 * h + 1 : ℕ) : ℤ) : Fin 4 → ℤ))) m l 0) = 1 := by
  rw [stair_base, add_zero]
  refine hol_one _ fun t ht => val_inside t (Or.inr ?_)
  obtain ⟨v, v', hv, hv', hs, hp⟩ := mem_stair y m l _ hl t ht
  have key : ∀ w, Partial ((Pi.single μ ((2 * h + 1 : ℕ) : ℤ) : Fin 4 → ℤ)) m l w → InP h μ w := fun w hw σ => by
    obtain ⟨h1, h2⟩ := hw σ
    obtain ⟨a1, a2⟩ := hm σ
    refine ⟨fun hσμ => ?_, fun hσμ => ?_⟩
    · have hs0 : (Pi.single μ ((2 * h + 1 : ℕ) : ℤ) : Fin 4 → ℤ) σ = 0 := Pi.single_eq_of_ne hσμ _
      by_cases hσ : σ ∈ l
      · have := h2 hσ; rw [hs0, sub_zero] at this; unfold LatticePaths.Btw at this; omega
      · have := h1 hσ; rw [hs0] at this; omega
    · rw [hσμ] at h1 h2 a1 a2 ⊢
      have hs0 : (Pi.single μ ((2 * h + 1 : ℕ) : ℤ) : Fin 4 → ℤ) μ = 2 * h + 1 := by simp
      by_cases hσ : μ ∈ l
      · have := h2 hσ; rw [hs0] at this; unfold LatticePaths.Btw at this; omega
      · have := h1 hσ; rw [hs0] at this; omega
  rw [hs, hp]
  exact ⟨bp_ofs hn (key v hv), bp_ofs hn (key v' hv')⟩

lemma LogM_one : LogM (1 : Mat) = 0 := by
  have h := LogM_exp (Z := (0 : Mat)) (by rw [norm_zero]; exact Real.log_pos one_lt_two)
  rwa [NormedSpace.exp_zero] at h

/-- The mean of copies of `id` is `id`. -/
lemma isMeanOf_one {k : ℕ} (x : Fin k) : IsMeanOf (fun _ : Fin k => (1 : GLN)) x 1 :=
  ⟨0, by simp, by simp, by simp [LogM_one]⟩

include hn in
/-- (ii) for `V₀`: its mean transports from `c̃₋` and from `c̃₊` to the points of their blocks are
`id`. -/
theorem transports_V0 {μ : Fin 4} {W : GLN} {m : Fin 4 → ℤ} (hm : InM h m) {k : ℕ}
    (l : Fin k → List (Fin 4)) (hl : ∀ Γ, (l Γ).Nodup) (x : Fin k) :
    IsMeanOf (fun Γ => (V0 y h μ W).hol (stair y m (l Γ) 0)) x 1 ∧
      IsMeanOf (fun Γ => (V0 y h μ W).hol
        (stair (ofs y ((Pi.single μ ((2 * h + 1 : ℕ) : ℤ) : Fin 4 → ℤ))) m (l Γ) 0)) x 1 := by
  constructor
  · have e : (fun Γ => (V0 y h μ W).hol (stair y m (l Γ) 0)) = fun _ => 1 :=
      funext fun Γ => hol_stair_minus hn hm (hl Γ)
    rw [e]; exact isMeanOf_one x
  · have e : (fun Γ => (V0 y h μ W).hol
        (stair (ofs y ((Pi.single μ ((2 * h + 1 : ℕ) : ℤ) : Fin 4 → ℤ))) m (l Γ) 0)) = fun _ => 1 :=
      funext fun Γ => hol_stair_plus hn hm (hl Γ)
    rw [e]; exact isMeanOf_one x

/-! ### (i): the plaquettes of `V₀` -/

lemma V0_ne {μ ρ : Fin 4} {W : GLN} (hρ : ρ ≠ μ) (x : Site n) : V0 y h μ W ρ x = 1 := by
  simp [V0, hρ]

lemma V0_congr {μ : Fin 4} {W : GLN} {x x' : Site n} (h1 : Bm y h x ↔ Bm y h x')
    (h2 : Bp y h μ (x + unit n μ) ↔ Bp y h μ (x' + unit n μ)) : V0 y h μ W μ x = V0 y h μ W μ x' := by
  simp only [V0, h1, h2]

/-- (i) for `V₀`: every plaquette with corners in `B(c̃₋) ∪ B(c̃₊)` equals `id`. -/
theorem plaq_V0 {μ : Fin 4} {W : GLN} (ν κ : Fin 4) (hνκ : ν ≠ κ) (x : Site n)
    (hP : PlaqIn {z | Bm y h z ∨ Bp y h μ z} ν κ x) : plaq (V0 y h μ W) ν κ x = 1 := by
  obtain ⟨c1, c2, c3, c4⟩ := hP
  rw [plaq_eq]
  by_cases hν : ν = μ
  · subst hν
    have hκ : κ ≠ ν := Ne.symm hνκ
    rw [V0_ne hκ, V0_ne hκ, V0_congr (x' := x + unit n κ)
      (blk_det c1 c3 (rep_add_unit_ne y h hνκ).symm).1
      (by
        rw [show x + unit n κ + unit n ν = x + unit n ν + unit n κ by abel]
        exact (blk_det c2 c4 (rep_add_unit_ne y h hνκ).symm).2)]
    group
  · by_cases hκ : κ = μ
    · subst hκ
      rw [V0_ne hν, V0_ne hν, V0_congr (x := x + unit n ν) (x' := x)
        (blk_det c2 c1 (rep_add_unit_ne y h (Ne.symm hνκ))).1
        (by
          exact (blk_det c4 c3 (by
            rw [add_right_comm x (unit n ν) (unit n κ)]
            exact rep_add_unit_ne y h (x := x + unit n κ) (Ne.symm hνκ))).2)]
      group
    · rw [V0_ne hν, V0_ne hκ, V0_ne hν, V0_ne hκ]
      group

/-- (i) in the form of `lem:axial-smallness`: in the box of offsets of `B(c̃₋) ∪ B(c̃₊)` the plaquettes of
`V₀` are at most every `β ≥ 0`. -/
theorem plaqBound_V0 (hn : 4 * h + 2 ≤ n) {μ : Fin 4} {W : GLN} {β : ℝ} (hβ : 0 ≤ β) :
    PlaqBound (V0 y h μ W) (boxR y (fun _ => -(h : ℤ))
      (fun σ => if σ = μ then 3 * (h : ℤ) + 1 else h)) β := by
  have hmem : ∀ z ∈ boxR y (fun _ => -(h : ℤ)) (fun σ => if σ = μ then 3 * (h : ℤ) + 1 else h),
      Bm y h z ∨ Bp y h μ z := by
    rintro z ⟨v, hv, rfl⟩
    by_cases hc : v μ ≤ h
    · left
      refine bm_ofs hn fun σ => ⟨(hv σ).1, ?_⟩
      by_cases hσ : σ = μ
      · rw [hσ]; exact hc
      · have := (hv σ).2; simp only [hσ, ↓reduceIte] at this; exact this
    · right
      refine bp_ofs hn fun σ => ⟨fun hσ => ⟨(hv σ).1, ?_⟩, fun hσ => ?_⟩
      · have := (hv σ).2; simp only [hσ, ↓reduceIte] at this; exact this
      · rw [hσ]
        have := (hv μ).2; simp only [↓reduceIte] at this
        constructor <;> omega
  intro ν κ x hνκ ⟨c1, c2, c3, c4⟩
  rw [plaq_V0 ν κ hνκ x ⟨hmem _ c1, hmem _ c2, hmem _ c3, hmem _ c4⟩, Units.val_one, sub_self,
    norm_zero]
  exact hβ

/-! ### (iii): the average of `V₀` on `c̃` -/

lemma seg_add (ρ : Fin 4) (s : Bool) : ∀ (a b : ℕ) (z : Site n),
    seg ρ s z (a + b) = seg ρ s z a ++ seg ρ s (z + a • dvec ρ s) b
  | 0, b, z => by simp [seg]
  | a + 1, b, z => by
    rw [show a + 1 + b = (a + b) + 1 by omega]
    show (⟨z, ρ, s⟩ : Bond n) :: seg ρ s (z + dvec ρ s) (a + b) =
      ((⟨z, ρ, s⟩ : Bond n) :: seg ρ s (z + dvec ρ s) a) ++ _
    rw [seg_add ρ s a b (z + dvec ρ s), List.cons_append,
      show z + dvec ρ s + a • dvec ρ s = z + (a + 1) • dvec ρ s by rw [succ_nsmul]; abel]

lemma seg_pt (v : Fin 4 → ℤ) (μ : Fin 4) (i : ℕ) :
    ofs y v + i • dvec μ true = ofs y (v + Pi.single μ (i : ℤ)) := by
  rw [ofs_add_single, natCast_zsmul]
  simp [dvec]

include hn in
/-- The straight path of `L = 2h + 1` bonds from a point of `B(c̃₋)` to its translate in `B(c̃₊)` has
exactly one bond between the blocks, so that `V₀` along it is `W`. -/
theorem hol_cross {μ : Fin 4} {W : GLN} {v : Fin 4 → ℤ} (hv : InM h v) :
    (V0 y h μ W).hol (seg μ true (ofs y v) (2 * h + 1)) = W := by
  obtain ⟨k₀, hk₀⟩ : ∃ k₀ : ℕ, (k₀ : ℤ) = h - v μ := ⟨(h - v μ).toNat, by
    have := (hv μ).2; omega⟩
  have hk₀2 : k₀ ≤ 2 * h := by have := (hv μ).1; omega
  have hsplit : 2 * h + 1 = k₀ + (1 + (2 * h - k₀)) := by omega
  have hoff : ∀ (i : ℤ) σ, σ ≠ μ → (v + (Pi.single μ i : Fin 4 → ℤ)) σ = v σ := fun i σ hσ => by
    simp [Pi.single_eq_of_ne hσ]
  have hon : ∀ (i : ℤ), (v + (Pi.single μ i : Fin 4 → ℤ)) μ = v μ + i := fun i => by simp
  have mkM : ∀ i : ℤ, -(h : ℤ) ≤ v μ + i → v μ + i ≤ h → InM h (v + Pi.single μ i) := fun i a b σ => by
    by_cases hσ : σ = μ
    · rw [hσ, hon]; exact ⟨a, b⟩
    · rw [hoff i σ hσ]; exact hv σ
  have mkP : ∀ i : ℤ, (h : ℤ) + 1 ≤ v μ + i → v μ + i ≤ 3 * h + 1 → InP h μ (v + Pi.single μ i) :=
    fun i a b σ => ⟨fun hσ => by rw [hoff i σ hσ]; exact hv σ, fun hσ => by rw [hσ, hon]; exact ⟨a, b⟩⟩
  rw [hsplit, seg_add, seg_add, hol_append, hol_append]
  have p1 : (V0 y h μ W).hol (seg μ true (ofs y v) k₀) = 1 := by
    refine hol_one _ fun t ht => val_inside t (Or.inl ?_)
    obtain ⟨i, hi, hs, hp⟩ := mem_seg_iff ht
    rw [hs, hp, seg_pt, seg_pt]
    have := (hv μ).1
    exact ⟨bm_ofs hn (mkM i (by omega) (by omega)), bm_ofs hn (mkM (i + 1 : ℕ) (by push_cast; omega)
      (by push_cast; omega))⟩
  have p2 : (V0 y h μ W).hol (seg μ true (ofs y v + k₀ • dvec μ true) 1) = W := by
    rw [seg_pt]
    have hz1 : ofs y (v + (Pi.single μ (k₀ : ℤ) : Fin 4 → ℤ)) + unit n μ =
        ofs y (v + (Pi.single μ ((k₀ : ℤ) + 1) : Fin 4 → ℤ)) := by
      rw [Pi.single_add, ← add_assoc, ofs_add_single y _ μ 1, one_smul]
    have hbm := bm_ofs (y := y) hn (mkM k₀ (by have := (hv μ).1; omega) (by omega))
    have hbp : Bp y h μ (ofs y (v + (Pi.single μ (k₀ : ℤ) : Fin 4 → ℤ)) + unit n μ) := by
      rw [hz1]; exact bp_ofs hn (mkP ((k₀ : ℤ) + 1) (by omega) (by have := (hv μ).2; omega))
    show (V0 y h μ W).hol [⟨ofs y (v + (Pi.single μ (k₀ : ℤ) : Fin 4 → ℤ)), μ, true⟩] = W
    rw [hol_cons, hol_nil, mul_one]
    show V0 y h μ W μ (ofs y (v + (Pi.single μ (k₀ : ℤ) : Fin 4 → ℤ))) = W
    have hc : μ = μ ∧ Bm y h (ofs y (v + (Pi.single μ (k₀ : ℤ) : Fin 4 → ℤ))) ∧
        Bp y h μ (ofs y (v + (Pi.single μ (k₀ : ℤ) : Fin 4 → ℤ)) + unit n μ) := ⟨rfl, hbm, hbp⟩
    simp only [V0, hc, and_self, ↓reduceIte]
  have p3 : (V0 y h μ W).hol (seg μ true (ofs y v + k₀ • dvec μ true + 1 • dvec μ true)
      (2 * h - k₀)) = 1 := by
    refine hol_one _ fun t ht => val_inside t (Or.inr ?_)
    obtain ⟨i, hi, hs, hp⟩ := mem_seg_iff ht
    have e3 : ∀ a b c : ℕ, ofs y v + a • dvec μ true + b • dvec μ true + c • dvec μ true =
        ofs y v + (a + b + c) • dvec μ true := fun a b c => by simp only [add_nsmul]; abel
    rw [hs, hp, e3, e3, seg_pt, seg_pt]
    have := (hv μ).2
    exact ⟨bp_ofs hn (mkP ((k₀ + 1 + i : ℕ) : ℤ) (by push_cast; omega) (by push_cast; omega)),
      bp_ofs hn (mkP ((k₀ + 1 + (i + 1) : ℕ) : ℤ) (by push_cast; omega) (by push_cast; omega))⟩
  rw [p1, p2, p3, one_mul, mul_one]

include hn in
/-- `V₀([c̃]) = W`. -/
theorem hol_ctilde {μ : Fin 4} {W : GLN} :
    (V0 y h μ W).hol (segZ μ y ((2 * h + 1 : ℕ) : ℤ)) = W := by
  have e : segZ μ y ((2 * h + 1 : ℕ) : ℤ) = seg μ true (ofs y 0) (2 * h + 1) := by
    rw [segZ_eq, ofs_zero, Int.natAbs_natCast,
      show sgn ((2 * h + 1 : ℕ) : ℤ) = true from decide_eq_true (Int.natCast_nonneg _)]
  rw [e]
  exact hol_cross hn (fun σ => by simp)

include hn in
/-- (iii) for `V₀`: every loop `ℓ_c̃(x, Γ, Γ')` (`x ∈ B(c̃₋)` with offsets `off(x)`, `Γ`, `Γ'` staircase
paths for orderings of the coordinates) has the holonomy `id`, and the average is
`M(V₀)(c̃) = W = V₀([c̃])` (`def:average`). -/
theorem avg_V0 (G : GaugeGroup N) {μ : Fin 4} {W : GLN} {ι : Type*} [Fintype ι] {P P' : ι → Type*}
    [∀ x, Fintype (P x)] [∀ x, Fintype (P' x)] (off : ι → Fin 4 → ℤ) (hoff : ∀ x, InM h (off x))
    (ord : ∀ x, P x → List (Fin 4)) (ord' : ∀ x, P' x → List (Fin 4))
    (hord : ∀ x Γ, (ord x Γ).Nodup) (hord' : ∀ x Γ', (ord' x Γ').Nodup) :
    (∀ x Γ Γ', Average.loop (fun x Γ => (V0 y h μ W).hol (stair y (off x) (ord x Γ) 0))
        (fun x => (V0 y h μ W).hol (segZ μ (ofs y (off x)) ((2 * h + 1 : ℕ) : ℤ)))
        (fun x Γ' => (V0 y h μ W).hol
          (stair (ofs y ((Pi.single μ ((2 * h + 1 : ℕ) : ℤ) : Fin 4 → ℤ))) (off x) (ord' x Γ') 0))
        ((V0 y h μ W).hol (segZ μ y ((2 * h + 1 : ℕ) : ℤ))) x Γ Γ' = 1) ∧
    Average.avg G.inChart G.chartLog (fun x Γ => (V0 y h μ W).hol (stair y (off x) (ord x Γ) 0))
        (fun x => (V0 y h μ W).hol (segZ μ (ofs y (off x)) ((2 * h + 1 : ℕ) : ℤ)))
        (fun x Γ' => (V0 y h μ W).hol
          (stair (ofs y ((Pi.single μ ((2 * h + 1 : ℕ) : ℤ) : Fin 4 → ℤ))) (off x) (ord' x Γ') 0))
        ((V0 y h μ W).hol (segZ μ y ((2 * h + 1 : ℕ) : ℤ))) = W := by
  have hseg : ∀ z : Site n, segZ μ z ((2 * h + 1 : ℕ) : ℤ) = seg μ true z (2 * h + 1) := fun z => by
    rw [segZ_eq, Int.natAbs_natCast,
      show sgn ((2 * h + 1 : ℕ) : ℤ) = true from decide_eq_true (Int.natCast_nonneg _)]
  have hl : ∀ x Γ Γ', Average.loop (fun x Γ => (V0 y h μ W).hol (stair y (off x) (ord x Γ) 0))
      (fun x => (V0 y h μ W).hol (segZ μ (ofs y (off x)) ((2 * h + 1 : ℕ) : ℤ)))
      (fun x Γ' => (V0 y h μ W).hol
        (stair (ofs y ((Pi.single μ ((2 * h + 1 : ℕ) : ℤ) : Fin 4 → ℤ))) (off x) (ord' x Γ') 0))
      ((V0 y h μ W).hol (segZ μ y ((2 * h + 1 : ℕ) : ℤ))) x Γ Γ' = 1 := by
    intro x Γ Γ'
    unfold Average.loop
    dsimp only
    rw [hol_stair_minus hn (hoff x) (hord x Γ), hol_stair_plus hn (hoff x) (hord' x Γ'),
      hseg (ofs y (off x)), hol_cross hn (hoff x), hol_ctilde hn]
    group
  refine ⟨hl, ?_⟩
  obtain ⟨hin, hlog⟩ := GaugeGroup.chartLog_eq (G := G) (W := 1) G.zero_mem_lie
    (by rw [norm_zero]; exact Real.pi_pos) (by simp)
  unfold Average.avg Average.beta
  simp only [hl, hin, implies_true, ↓reduceIte, hlog, smul_zero, Finset.sum_const_zero, expU_zero,
    one_mul]
  exact hol_ctilde hn

/-! ### `lem:axial-smallness` for the reference fields of `cor:axial-straight` -/

/-- The lower corner of the box `B(c̃₋) ∪ B(c̃₊)`, in offsets from `c̃₋`. -/
def loB (h : ℕ) : Fin 4 → ℤ := fun _ => -(h : ℤ)

/-- The upper corner of the box `B(c̃₋) ∪ B(c̃₊)`, in offsets from `c̃₋`. -/
def hiB (h : ℕ) (μ : Fin 4) : Fin 4 → ℤ := fun σ => if σ = μ then 3 * (h : ℤ) + 1 else h

lemma inBox_M {h : ℕ} {μ : Fin 4} {v : Fin 4 → ℤ} (hv : InM h v) : InBox (loB h) (hiB h μ) v :=
  fun σ => by
    have := hv σ
    unfold loB hiB
    split_ifs <;> constructor <;> omega

lemma inBox_P {h : ℕ} {μ : Fin 4} {v : Fin 4 → ℤ} (hv : InP h μ v) : InBox (loB h) (hiB h μ) v :=
  fun σ => by
    unfold loB hiB
    split_ifs with hσ
    · have := (hv σ).2 hσ; constructor <;> omega
    · have := (hv σ).1 hσ; constructor <;> omega

lemma inM_zero (h : ℕ) : InM h 0 := fun σ => by simp

lemma inP_shift {h : ℕ} {μ : Fin 4} {v : Fin 4 → ℤ} (hv : InM h v) :
    InP h μ ((Pi.single μ ((2 * h + 1 : ℕ) : ℤ) : Fin 4 → ℤ) + v) := fun σ => by
  refine ⟨fun hσ => ?_, fun hσ => ?_⟩
  · simp only [Pi.add_apply, Pi.single_eq_of_ne hσ, zero_add]; exact hv σ
  · rw [hσ]
    have := hv μ
    simp only [Pi.add_apply, Pi.single_eq_same]
    push_cast
    constructor <;> omega

lemma inP_update {h : ℕ} {μ : Fin 4} {v : Fin 4 → ℤ} (hv : InM h v) :
    InP h μ (Function.update v μ ((2 * h + 1 : ℕ) : ℤ)) := fun σ => by
  refine ⟨fun hσ => ?_, fun hσ => ?_⟩
  · simp only [Function.update_apply, hσ, ↓reduceIte]; exact hv σ
  · simp only [Function.update_apply, hσ, ↓reduceIte]
    push_cast
    constructor <;> omega

lemma natAbs_le {h : ℕ} {v : Fin 4 → ℤ} (hv : InM h v) (σ : Fin 4) : ((v σ).natAbs : ℝ) ≤ h := by
  have := hv σ
  exact_mod_cast (show (v σ).natAbs ≤ h by omega)

lemma one_val (b : Bond n) : (1 : Config N n).val b = 1 := by
  unfold Config.val
  split_ifs <;> simp

lemma plaqBound_one {R : Set (Site n)} {β : ℝ} (hβ : 0 ≤ β) : PlaqBound (1 : Config N n) R β := by
  intro μ ν x _ _
  rw [plaq_eq]
  simpa using hβ

/-- `lem:axial-smallness` for a bond in one block, with the reference field `V₀ = id` of
`cor:axial-straight`: if the transports of `V` from the centre `y` of the block to the two ends of the
bond are `id` (the axial gauge), then `‖V(b) - 1‖` obeys the bound of the lemma; the hypotheses (i)–(iii)
on `V₀` are discharged. -/
theorem axial_one_block_id (G : GaugeGroup N) (hG : IsClosed G.mats) :
    ∃ r : ℝ, 0 < r ∧ ∀ {n : ℕ} [NeZero n] (V : Config N n), IsGField G V →
      ∀ (y : Site n) (lo hi : Fin 4 → ℤ) (β : ℝ), 0 ≤ β → PlaqBound V (boxR y lo hi) β →
      ∀ (m : Fin 4 → ℤ) (P S : List (Fin 4)) (ρ : Fin 4),
      P ++ ρ :: S = [0, 1, 2, 3] → InBox lo hi 0 → InBox lo hi m → InBox lo hi (m + Pi.single ρ 1) →
      ∀ (h : ℝ), (∀ σ, ((m σ).natAbs : ℝ) ≤ h) →
      (∀ σ, (((m + Pi.single ρ 1 : Fin 4 → ℤ) σ).natAbs : ℝ) ≤ h) → 6 * h ^ 2 * β ≤ r →
      512 * (Real.pi / 2 * (6 * h ^ 2 * β)) ≤ 1 →
      ∀ {k : ℕ} (_hk : 0 < k) (l : Fin k → List (Fin 4)), (∀ Γ, (l Γ).Perm [0, 1, 2, 3]) →
      ∀ x, l x = [0, 1, 2, 3] →
      IsMeanOf (fun Γ => V.hol (stair y m (l Γ) 0)) x 1 →
      IsMeanOf (fun Γ => V.hol (stair y (m + Pi.single ρ 1) (l Γ) 0)) x 1 →
      ‖((V.val ⟨ofs y m, ρ, true⟩ : GLN) : Mat) - 1‖ ≤
        8 * Real.pi * (6 * h ^ 2 * β) + 2 * ((S.map fun σ => (m σ).natAbs).sum * β) := by
  obtain ⟨r, hr0, H⟩ := axial_one_block_lattice G hG
  refine ⟨r, hr0, fun {n} [NeZero n] V hV y lo hi β hβ hPV m P S ρ hPS h0 hm hm' h hh hh' hbr hb512 k hk l hl x hx
    hT hT' => ?_⟩
  have t1 : ∀ m' : Fin 4 → ℤ,
      IsMeanOf (fun Γ => (1 : Config N n).hol (stair y m' (l Γ) 0)) x 1 := fun m' => by
    have e : (fun Γ => (1 : Config N n).hol (stair y m' (l Γ) 0)) = fun _ => 1 :=
      funext fun Γ => hol_one _ fun t _ => one_val t
    rw [e]
    exact isMeanOf_one x
  have := H V 1 hV (fun _ _ => G.carrier.one_mem) y lo hi β hβ hPV (plaqBound_one hβ) m P S ρ hPS h0
    hm hm' h hh hh' hbr hb512 hk l hl x hx 1 1 hT (t1 m) hT' (t1 _)
  rwa [one_val, inv_one, mul_one] at this

/-- `lem:axial-smallness` for the bond between the blocks, with the reference field `V₀` of
`cor:axial-straight` (`id` inside the blocks `B(c̃₋)`, `B(c̃₊)` of side `L = 2h + 1`, and
`W = M(V)(c̃)` on the bonds between them): if the transports of `V` from `c̃₋` to `b₋` and from `c̃₊` to
`b₊` are `id` (the axial gauge), then `‖V(b) - M(V)(c̃)‖` obeys the bound of the lemma with `α₁ = 0`.
The hypotheses (i)–(iii) on `V₀`, the box containments, and the bounds on the offsets are discharged
from `b₋ ∈ B(c̃₋)`, `b₊ ∈ B(c̃₊)`, and the points `x ∈ B(c̃₋)` of the average. -/
theorem axial_between_V0 (G : GaugeGroup N) (hG : IsClosed G.mats) {ι : Type*} [Fintype ι]
    {P P' : ι → Type*} [∀ x, Fintype (P x)] [∀ x, Fintype (P' x)] :
    ∃ r : ℝ, 0 < r ∧ ∃ rG : ℝ, 0 < rG ∧ ∀ {n : ℕ} [NeZero n] (V : Config N n), IsGField G V →
      ∀ (y : Site n) (μ : Fin 4) (h : ℕ), 4 * h + 2 ≤ n → ∀ α : ℝ, 0 ≤ α →
      PlaqBound V (boxR y (loB h) (hiB h μ)) (Real.sqrt N * α) →
      α ≤ rG / (8 * Real.sqrt N * ((2 * h + 1 : ℕ) : ℝ) ^ 2) →
      7 * Real.sqrt N * ((2 * h + 1 : ℕ) : ℝ) ^ 2 * α ≤ Real.pi →
      6 * (h : ℝ) ^ 2 * (Real.sqrt N * α) ≤ r →
      512 * (Real.pi / 2 * (6 * (h : ℝ) ^ 2 * (Real.sqrt N * α))) ≤ 1 →
      ∀ (off : ι → Fin 4 → ℤ) (ord : ∀ x, P x → List (Fin 4)) (ord' : ∀ x, P' x → List (Fin 4)),
      (∀ x Γ, (ord x Γ).Perm [0, 1, 2, 3]) → (∀ x Γ', (ord' x Γ').Perm [0, 1, 2, 3]) →
      (∀ x, InM h (off x)) →
      ∀ (m n' : Fin 4 → ℤ) (Pre Post : List (Fin 4)), Pre ++ μ :: Post = [0, 1, 2, 3] →
      n' + Pi.single μ ((2 * h + 1 : ℕ) : ℤ) = m + Pi.single μ 1 → InM h m → InM h n' →
      ∀ {k : ℕ} (_hk : 0 < k) (l : Fin k → List (Fin 4)), (∀ Γ, (l Γ).Perm [0, 1, 2, 3]) →
      ∀ x, l x = [0, 1, 2, 3] →
      IsMeanOf (fun Γ => V.hol (stair y m (l Γ) 0)) x 1 →
      IsMeanOf (fun Γ => V.hol
        (stair (ofs y (Pi.single μ ((2 * h + 1 : ℕ) : ℤ) : Fin 4 → ℤ)) n' (l Γ) 0)) x 1 →
      ‖((V.val ⟨ofs y m, μ, true⟩ : GLN) : Mat) - ((Average.avg G.inChart G.chartLog
          (fun x Γ => V.hol (stair y (off x) (ord x Γ) 0))
          (fun x => V.hol (segZ μ (ofs y (off x)) ((2 * h + 1 : ℕ) : ℤ)))
          (fun x Γ' => V.hol
            (stair (ofs y (Pi.single μ ((2 * h + 1 : ℕ) : ℤ) : Fin 4 → ℤ)) (off x) (ord' x Γ') 0))
          (V.hol (segZ μ y ((2 * h + 1 : ℕ) : ℤ))) : GLN) : Mat)‖ ≤
        8 * Real.pi * (6 * (h : ℝ) ^ 2 * (Real.sqrt N * α)) +
        2 * ((2 * h + 1 : ℕ) * (Pre.map fun σ => (n' σ).natAbs).sum * (Real.sqrt N * α)) +
        14 * Real.sqrt N * ((2 * h + 1 : ℕ) : ℝ) ^ 2 * α +
        2 * ((Post.map fun σ => (m σ).natAbs).sum * (Real.sqrt N * α)) := by
  obtain ⟨r, hr0, rG, hrG0, H⟩ := axial_between_lattice (P := P) (P' := P') G hG
  refine ⟨r, hr0, rG, hrG0, fun {n} [NeZero n] V hV y μ h hn α hα hPV hαr hπ hbr hb512 off ord ord' hord hord' hoff
    m n' Pre Post hPS hz hm hn' k hk l hl x hx hT hT' => ?_⟩
  set W := Average.avg G.inChart G.chartLog (fun x Γ => V.hol (stair y (off x) (ord x Γ) 0))
    (fun x => V.hol (segZ μ (ofs y (off x)) ((2 * h + 1 : ℕ) : ℤ)))
    (fun x Γ' => V.hol
      (stair (ofs y (Pi.single μ ((2 * h + 1 : ℕ) : ℤ) : Fin 4 → ℤ)) (off x) (ord' x Γ') 0))
    (V.hol (segZ μ y ((2 * h + 1 : ℕ) : ℤ))) with hW
  have hWG : W ∈ G.carrier := GaugeGroup.avg_mem hG _ _ _ _ (hV.hol_mem _)
  have hV0 : IsGField G (V0 y h μ W) := V0_mem hWG
  have hnd : ∀ Γ, (l Γ).Nodup := fun Γ => (hl Γ).nodup_iff.2 (by decide)
  have hm1 : InP h μ (m + Pi.single μ 1) := by rw [← hz, add_comm]; exact inP_shift hn'
  have tm := (transports_V0 (y := y) (μ := μ) (W := W) hn hm l hnd x).1
  have tp' := (transports_V0 (y := y) (μ := μ) (W := W) hn hn' l hnd x).2
  have hav := (avg_V0 (y := y) (μ := μ) (W := W) hn G off hoff ord ord'
    (fun x Γ => (hord x Γ).nodup_iff.2 (by decide))
    (fun x Γ' => (hord' x Γ').nodup_iff.2 (by decide))).2
  have hsingle : InP h μ (Pi.single μ ((2 * h + 1 : ℕ) : ℤ) : Fin 4 → ℤ) := by
    have := inP_shift (μ := μ) (inM_zero h)
    rwa [add_zero] at this
  have hLh : 4 * ((2 * h + 1 : ℕ) : ℝ) * (h : ℝ) + 6 * (h : ℝ) ^ 2 ≤
      4 * ((2 * h + 1 : ℕ) : ℝ) ^ 2 := by
    have : (0 : ℝ) ≤ h := Nat.cast_nonneg h
    push_cast
    nlinarith
  have := H V (V0 y h μ W) hV hV0 y (loB h) (hiB h μ) μ (2 * h + 1) α h hα hPV
    (plaqBound_V0 hn (mul_nonneg (Real.sqrt_nonneg _) hα)) hαr hπ hLh hbr hb512
    off ord ord' hord hord' (fun x σ => natAbs_le (hoff x) σ) (inBox_M (inM_zero h))
    (fun x => inBox_M (hoff x)) (inBox_P hsingle) (fun x => inBox_P (inP_shift (hoff x)))
    m n' Pre Post hPS hz (inBox_M hm) (inBox_P hm1) (inBox_P (inP_update hn'))
    (inBox_P (inP_shift hn')) (natAbs_le hm) (natAbs_le hn') hk l hl x hx 1 1
    hT tm hT' tp' W W hW hav.symm 0 (by simp)
  have hplus : ofs y m + unit n μ = ofs y (m + Pi.single μ 1) := by
    rw [ofs_add_single, one_smul]
  have hc : μ = μ ∧ Bm y h (ofs y m) ∧ Bp y h μ (ofs y m + unit n μ) :=
    ⟨rfl, bm_ofs hn hm, by rw [hplus]; exact bp_ofs hn hm1⟩
  have hb : (V0 y h μ W).val ⟨ofs y m, μ, true⟩ = W := by
    show V0 y h μ W μ (ofs y m) = W
    simp only [V0, hc, and_self, ↓reduceIte]
  have e : (((V.val ⟨ofs y m, μ, true⟩ * W⁻¹ : GLN) : Mat) - 1) =
      (((V.val ⟨ofs y m, μ, true⟩ : GLN) : Mat) - (W : Mat)) * ((W⁻¹ : GLN) : Mat) := by
    rw [Units.val_mul, sub_mul, Units.mul_inv]
  rw [hb, add_zero, e, CStarRing.norm_mul_mem_unitary _ (G.unitary _ (G.carrier.inv_mem hWG))] at this
  exact this

end AxialReference

end CoreLean

end
