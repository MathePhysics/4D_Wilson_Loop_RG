/-
`lem:average-kernels` of BALABAN_CORE.tex (`0d76a9bf9596`): the kernels of the averages, the first bound.

The `ℓ¹`-sums of the proof over the bonds of the region of a level, `‖A‖_{1,l} = Σ_{b'} a_{i+l}⁴‖A(b')‖`, in the units of
the forms of the levels (`D_l = a_{i+l}A`, so that `‖A‖_{1,l} = a_{i+l}³Σ‖D_l(b')‖`). The points of a level are the
points `x ∈ Lˡℤ⁴` of the box `[-H_l, Lⁿ + H_l]⁴` with the bonds `(x, ν)` of the region (`RB`).

* `boxPts`, `mem_boxPts`, `RB`, `ell1`: the finite sums.
* `Pbox`, `box_site'`, `card_Pbox_le`: a bond of the level `l` lies in the boxes of at most `8` bonds of the level
  `l + 1` (two for each direction).
-/
import CoreLean.RelativeAverageLevels
import CoreLean.BlockAverageTransports

open Matrix NormedSpace Filter Topology Metric
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace CoreLean
namespace RelativeAverage

open LatticePaths LatticeKappa RegularAverages BlockPaths AverageHolo MeanTransports AxialReference
  AxialStraightLattice BoxGeometry StraightExtension

variable {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "GLN" => (Matrix (Fin N) (Fin N) ℂ)ˣ

open Classical in
/-- The points of the box `[-H_l, Lⁿ + H_l]⁴`, which contains the region of the level `l`. -/
def boxPts (h nl l : ℕ) : Finset (Fin 4 → ℤ) :=
  Fintype.piFinset fun _ => Finset.Icc (-Hw h nl l) (Lz h ^ nl + Hw h nl l)

lemma mem_boxPts {h nl l : ℕ} {μ : Fin 4} {x : Fin 4 → ℤ} (hR : Rg h nl μ l x) : x ∈ boxPts h nl l := by
  simp only [boxPts, Fintype.mem_piFinset, Finset.mem_Icc]
  intro σ
  have a := hR σ
  have hp : (0 : ℤ) ≤ Lz h ^ nl := (pow_pos (Lz_pos h) _).le
  refine ⟨a.1, a.2.trans ?_⟩
  split_ifs <;> linarith

/-- The bonds `(x, ν)` of the region of the level `l`. -/
def RB (h nl : ℕ) (μ : Fin 4) (l : ℕ) (x : Fin 4 → ℤ) (ν : Fin 4) : Prop :=
  Lat (Lz h) l x ∧ Rg h nl μ l x ∧ Rg h nl μ l (x + Lz h ^ l • Pi.single ν 1)

open Classical in
/-- The `ℓ¹`-sum over the bonds of the region of the level `l`. -/
def ell1 (h nl : ℕ) (μ : Fin 4) (l : ℕ) (f : (Fin 4 → ℤ) → Fin 4 → ℝ) : ℝ :=
  ∑ x ∈ boxPts h nl l, ∑ ν : Fin 4, if RB h nl μ l x ν then f x ν else 0

open Classical in
lemma le_ell1 {h nl l : ℕ} {μ : Fin 4} {f : (Fin 4 → ℤ) → Fin 4 → ℝ} (hf : ∀ x ν, 0 ≤ f x ν) {x : Fin 4 → ℤ}
    {ν : Fin 4} (hb : RB h nl μ l x ν) : f x ν ≤ ell1 h nl μ l f := by
  have hx : x ∈ boxPts h nl l := mem_boxPts hb.2.1
  have hnn : ∀ y ∈ boxPts h nl l, 0 ≤ ∑ ν : Fin 4, if RB h nl μ l y ν then f y ν else 0 := fun y _ =>
    Finset.sum_nonneg fun ν _ => by split_ifs; exacts [hf y ν, le_rfl]
  calc f x ν = if RB h nl μ l x ν then f x ν else 0 := by rw [if_pos hb]
    _ ≤ ∑ ν : Fin 4, if RB h nl μ l x ν then f x ν else 0 :=
        Finset.single_le_sum (f := fun ν => if RB h nl μ l x ν then f x ν else 0)
          (fun ν _ => by split_ifs; exacts [hf x ν, le_rfl]) (Finset.mem_univ ν)
    _ ≤ ell1 h nl μ l f := Finset.single_le_sum (f := fun y => ∑ ν : Fin 4, if RB h nl μ l y ν then f y ν else 0)
          hnn hx

/-- The bond `(x', ν)` of the level `l` lies in the box of the bond `(x, ρ)` of the level `l + 1`. -/
def Pbox (h l : ℕ) (x : Fin 4 → ℤ) (ρ : Fin 4) (x' : Fin 4 → ℤ) (ν : Fin 4) : Prop :=
  ∃ m, LatticePaths.InBox (loD h) (hiD h ρ ρ) m ∧ LatticePaths.InBox (loD h) (hiD h ρ ρ) (m + Pi.single ν 1) ∧
    x' = x + Lz h ^ l • m

/-- `box_site` with the offset of the bond in the box. -/
lemma box_site' {n : ℕ} [NeZero n] {h nl l : ℕ} (hn : 4 * h + 4 ≤ n) {μ ρ : Fin 4} (y : Site n)
    {x : Fin 4 → ℤ} (hx : Lat (Lz h) (l + 1) x) (h0 : Rg h nl μ (l + 1) x)
    (h1 : Rg h nl μ (l + 1) (x + Lz h ^ (l + 1) • Pi.single ρ 1)) {ν : Fin 4} {z : Site n}
    (hb : BoxBond (img h y l x) h ρ ν z) :
    ∃ x', RB h nl μ l x' ν ∧ Pbox h l x ρ x' ν ∧ z = img h y l x' := by
  obtain ⟨hm, hm'⟩ := box_bond hn hb
  set m := rep (img h y l x) h z
  have hxl := lat_succ_le hx
  refine ⟨x + Lz h ^ l • m, ⟨lat_add_smul hxl m, rg_of_bond h0 h1 hm, ?_⟩, ⟨m, hm, hm', rfl⟩, ?_⟩
  · have e : x + Lz h ^ l • m + Lz h ^ l • Pi.single ν 1 = x + Lz h ^ l • (m + Pi.single ν 1) := by
      rw [smul_add, add_assoc]
    rw [e]; exact rg_of_bond h0 h1 hm'
  · rw [← img_add y hxl, StraightExtension.ofs_rep]

/-- Two offsets of a box which differ by a multiple of `L` in every coordinate, and lie in the same half in the
direction of the bond, are equal. -/
lemma offset_eq {h : ℕ} {ρ : Fin 4} {m m' : Fin 4 → ℤ} (hm : LatticePaths.InBox (loD h) (hiD h ρ ρ) m)
    (hm' : LatticePaths.InBox (loD h) (hiD h ρ ρ) m') (hd : ∀ σ, Lz h ∣ m σ - m' σ)
    (hs : (m ρ ≤ h ↔ m' ρ ≤ h)) : m = m' := by
  funext σ
  have a := hm σ
  have b := hm' σ
  simp only [loD, hiD, or_self] at a b
  obtain ⟨k, hk⟩ := hd σ
  have hL : Lz h = 2 * h + 1 := rfl
  by_cases hσ : σ = ρ
  · subst hσ
    simp only [↓reduceIte] at a b
    by_cases h1 : m σ ≤ h
    · have h2 := hs.1 h1
      have : k = 0 := by
        rcases lt_trichotomy k 0 with hk0 | hk0 | hk0
        · have : (2 * h + 1 : ℤ) * k ≤ -(2 * h + 1) := by nlinarith
          rw [← hL] at this; omega
        · exact hk0
        · have : (2 * h + 1 : ℤ) ≤ (2 * h + 1) * k := by nlinarith
          rw [← hL] at this; omega
      rw [this, mul_zero] at hk; omega
    · have h2 : ¬ m' σ ≤ h := fun h' => h1 (hs.2 h')
      have : k = 0 := by
        rcases lt_trichotomy k 0 with hk0 | hk0 | hk0
        · have : (2 * h + 1 : ℤ) * k ≤ -(2 * h + 1) := by nlinarith
          rw [← hL] at this; omega
        · exact hk0
        · have : (2 * h + 1 : ℤ) ≤ (2 * h + 1) * k := by nlinarith
          rw [← hL] at this; omega
      rw [this, mul_zero] at hk; omega
  · simp only [hσ, ↓reduceIte] at a b
    have : k = 0 := by
      rcases lt_trichotomy k 0 with hk0 | hk0 | hk0
      · have : (2 * h + 1 : ℤ) * k ≤ -(2 * h + 1) := by nlinarith
        rw [← hL] at this; omega
      · exact hk0
      · have : (2 * h + 1 : ℤ) ≤ (2 * h + 1) * k := by nlinarith
        rw [← hL] at this; omega
    rw [this, mul_zero] at hk; omega

open Classical in
/-- **A bond of the level `l` lies in the boxes of at most two bonds of the level `l + 1` in each direction.** -/
lemma card_Pbox_le (h nl l : ℕ) (μ ρ : Fin 4) (x' : Fin 4 → ℤ) (ν : Fin 4) :
    ((boxPts h nl (l + 1)).filter fun x => Lat (Lz h) (l + 1) x ∧ Pbox h l x ρ x' ν).card ≤ 2 := by
  set S := (boxPts h nl (l + 1)).filter fun x => Lat (Lz h) (l + 1) x ∧ Pbox h l x ρ x' ν
  -- the half of the box in which the bond lies
  let F : (Fin 4 → ℤ) → Bool := fun x => decide ((x' - x) ρ ≤ (h : ℤ) * Lz h ^ l)
  have hinj : Set.InjOn F S := by
    intro x hx y hy hxy
    simp only [S, Finset.coe_filter, Set.mem_setOf_eq] at hx hy
    obtain ⟨-, hxl, m, hm, -, hxm⟩ := hx
    obtain ⟨-, hyl, m', hm', -, hym⟩ := hy
    have hQ : 0 < Lz h ^ l := pow_pos (Lz_pos h) l
    have hmx : ∀ σ, (x' - x) σ = Lz h ^ l * m σ := fun σ => by
      rw [hxm]; simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have hmy : ∀ σ, (x' - y) σ = Lz h ^ l * m' σ := fun σ => by
      rw [hym]; simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have hd : ∀ σ, Lz h ∣ m σ - m' σ := fun σ => by
      have e : Lz h ^ l * (m σ - m' σ) = y σ - x σ := by
        have := hmx σ; have := hmy σ; simp only [Pi.sub_apply] at *; linarith
      have hdiv : Lz h ^ (l + 1) ∣ y σ - x σ := dvd_sub (hyl σ) (hxl σ)
      rw [← e, pow_succ] at hdiv
      exact (mul_dvd_mul_iff_left hQ.ne').1 hdiv
    have hs : (m ρ ≤ h ↔ m' ρ ≤ h) := by
      have e1 : F x = decide (m ρ ≤ h) := by
        simp only [F, hmx]
        congr 1
        exact propext ⟨fun h' => by nlinarith, fun h' => by nlinarith⟩
      have e2 : F y = decide (m' ρ ≤ h) := by
        simp only [F, hmy]
        congr 1
        exact propext ⟨fun h' => by nlinarith, fun h' => by nlinarith⟩
      rw [e1, e2] at hxy
      exact decide_eq_decide.1 hxy
    have hmm := offset_eq hm hm' hd hs
    funext σ
    have := hmx σ; have := hmy σ
    simp only [Pi.sub_apply, hmm] at *
    linarith
  calc S.card ≤ (Finset.univ : Finset Bool).card := Finset.card_le_card_of_injOn F
        (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _)) hinj
    _ = 2 := rfl


open Classical in
/-- **The sum over the boxes**: `Σ_{c'} Σ_{b' ∈ box(c')} f(b') ≤ 8Σ_{b'} f(b')`, every bond of the level `l` lying in the
boxes of at most eight bonds of the level `l + 1`. -/
lemma sum_box_le (h nl l : ℕ) (μ : Fin 4) {f : (Fin 4 → ℤ) → Fin 4 → ℝ} (hf : ∀ x ν, 0 ≤ f x ν) :
    ∑ x ∈ boxPts h nl (l + 1), ∑ ρ : Fin 4, ∑ x' ∈ boxPts h nl l, ∑ ν : Fin 4,
      (if RB h nl μ (l + 1) x ρ ∧ RB h nl μ l x' ν ∧ Pbox h l x ρ x' ν then f x' ν else 0) ≤
      8 * ell1 h nl μ l f := by
  rw [Finset.sum_comm]
  have e1 : ∀ ρ : Fin 4, ∑ x ∈ boxPts h nl (l + 1), ∑ x' ∈ boxPts h nl l, ∑ ν : Fin 4,
      (if RB h nl μ (l + 1) x ρ ∧ RB h nl μ l x' ν ∧ Pbox h l x ρ x' ν then f x' ν else 0) =
      ∑ x' ∈ boxPts h nl l, ∑ ν : Fin 4, ∑ x ∈ boxPts h nl (l + 1),
      (if RB h nl μ (l + 1) x ρ ∧ RB h nl μ l x' ν ∧ Pbox h l x ρ x' ν then f x' ν else 0) := fun ρ => by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x' _ => ?_
    rw [Finset.sum_comm]
  simp only [e1]
  rw [Finset.sum_comm]
  simp only [ell1, Finset.mul_sum]
  refine Finset.sum_le_sum fun x' _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun ν _ => ?_
  by_cases hb : RB h nl μ l x' ν
  · rw [if_pos hb]
    have hρ : ∀ ρ : Fin 4, ∑ x ∈ boxPts h nl (l + 1),
        (if RB h nl μ (l + 1) x ρ ∧ RB h nl μ l x' ν ∧ Pbox h l x ρ x' ν then f x' ν else 0) ≤ 2 * f x' ν := by
      intro ρ
      calc ∑ x ∈ boxPts h nl (l + 1),
            (if RB h nl μ (l + 1) x ρ ∧ RB h nl μ l x' ν ∧ Pbox h l x ρ x' ν then f x' ν else 0)
          ≤ ∑ x ∈ boxPts h nl (l + 1), (if Lat (Lz h) (l + 1) x ∧ Pbox h l x ρ x' ν then f x' ν else 0) :=
            Finset.sum_le_sum fun x _ => by
              split_ifs with h1 h2
              · exact le_rfl
              · exact absurd ⟨h1.1.1, h1.2.2⟩ h2
              · exact hf x' ν
              · exact le_rfl
        _ = ((boxPts h nl (l + 1)).filter fun x => Lat (Lz h) (l + 1) x ∧ Pbox h l x ρ x' ν).card * f x' ν := by
            rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
        _ ≤ 2 * f x' ν := mul_le_mul_of_nonneg_right (by exact_mod_cast card_Pbox_le h nl l μ ρ x' ν) (hf x' ν)
    calc ∑ ρ : Fin 4, ∑ x ∈ boxPts h nl (l + 1),
          (if RB h nl μ (l + 1) x ρ ∧ RB h nl μ l x' ν ∧ Pbox h l x ρ x' ν then f x' ν else 0)
        ≤ ∑ _ρ : Fin 4, 2 * f x' ν := Finset.sum_le_sum fun ρ _ => hρ ρ
      _ = 8 * f x' ν := by simp; ring
  · rw [if_neg hb, mul_zero]
    refine le_of_eq (Finset.sum_eq_zero fun ρ _ => Finset.sum_eq_zero fun x _ => ?_)
    rw [if_neg fun h' => hb h'.2.1]


/-- The offsets of the bonds of the lines `[x, x + c']` lie in the box of `c'`. -/
lemma line_inBox {h : ℕ} {ρ : Fin 4} (xp : Pts h) {j : ℕ} (hj : j < 2 * h + 1) :
    LatticePaths.InBox (loD h) (hiD h ρ ρ) (offP h xp + (j : ℤ) • Pi.single ρ 1) ∧
      LatticePaths.InBox (loD h) (hiD h ρ ρ) (offP h xp + (j : ℤ) • Pi.single ρ 1 + Pi.single ρ 1) := by
  have ho := offP_inM h xp
  constructor <;> intro σ <;> have := ho σ <;>
    simp only [loD, hiD, or_self, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply] <;>
    split_ifs <;> constructor <;> push_cast <;> omega

lemma line_RB {h nl l : ℕ} {μ ρ : Fin 4} {x : Fin 4 → ℤ} (hb : RB h nl μ (l + 1) x ρ) (xp : Pts h) {j : ℕ}
    (hj : j < 2 * h + 1) : RB h nl μ l (x + Lz h ^ l • (offP h xp + (j : ℤ) • Pi.single ρ 1)) ρ := by
  obtain ⟨hx, h0, h1⟩ := hb
  obtain ⟨i0, i1⟩ := line_inBox (ρ := ρ) xp hj
  refine ⟨lat_add_smul (lat_succ_le hx) _, rg_of_bond h0 h1 i0, ?_⟩
  have e : x + Lz h ^ l • (offP h xp + (j : ℤ) • Pi.single ρ 1) + Lz h ^ l • Pi.single ρ 1 =
      x + Lz h ^ l • (offP h xp + (j : ℤ) • Pi.single ρ 1 + Pi.single ρ 1) := by
    rw [smul_add (Lz h ^ l) _ (Pi.single ρ 1), add_assoc]
  rw [e]; exact rg_of_bond h0 h1 i1

open Classical in
/-- **The sum over the lines**: `Σ_{c'} Σ_{x ∈ B(c'₋)} Σ_{b ∈ [x, x + c']} f(b) ≤ LΣ_{b'} f(b')`, every bond of the
level `l` lying on the lines of at most `L` pairs of a bond `c'` and a point `x ∈ B(c'₋)`. -/
lemma sum_lines_le (h nl l : ℕ) (μ : Fin 4) {f : (Fin 4 → ℤ) → Fin 4 → ℝ} (hf : ∀ x ν, 0 ≤ f x ν) :
    ∑ x ∈ boxPts h nl (l + 1), ∑ ρ : Fin 4, ∑ xp : Pts h, ∑ j ∈ Finset.range (2 * h + 1),
      (if RB h nl μ (l + 1) x ρ then f (x + Lz h ^ l • (offP h xp + (j : ℤ) • Pi.single ρ 1)) ρ else 0) ≤
      ((2 * h + 1 : ℕ) : ℝ) * ell1 h nl μ l f := by
  -- for one direction and one position on the lines, the map to the bonds of the level `l` is injective
  have key : ∀ (ρ : Fin 4) (j : ℕ), j < 2 * h + 1 →
      ∑ x ∈ boxPts h nl (l + 1), ∑ xp : Pts h,
        (if RB h nl μ (l + 1) x ρ then f (x + Lz h ^ l • (offP h xp + (j : ℤ) • Pi.single ρ 1)) ρ else 0) ≤
      ∑ x' ∈ boxPts h nl l, if RB h nl μ l x' ρ then f x' ρ else 0 := by
    intro ρ j hj
    set S := (boxPts h nl (l + 1) ×ˢ (Finset.univ : Finset (Pts h))).filter fun p => RB h nl μ (l + 1) p.1 ρ
    set φ : (Fin 4 → ℤ) × Pts h → (Fin 4 → ℤ) :=
      fun p => p.1 + Lz h ^ l • (offP h p.2 + (j : ℤ) • Pi.single ρ 1)
    have hQ : 0 < Lz h ^ l := pow_pos (Lz_pos h) l
    have hinj : Set.InjOn φ S := by
      rintro ⟨x, xp⟩ hx ⟨y, yp⟩ hy hxy
      simp only [S, Finset.coe_filter, Finset.mem_product, Finset.mem_univ, and_true, Set.mem_setOf_eq] at hx hy
      have hxl := hx.2.1
      have hyl := hy.2.1
      simp only [φ] at hxy
      have hd : ∀ σ, offP h xp σ = offP h yp σ := fun σ => by
        have e := congrFun hxy σ
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e
        have e' : Lz h ^ l * (offP h xp σ - offP h yp σ) = y σ - x σ := by linarith
        have hdiv : Lz h ^ (l + 1) ∣ y σ - x σ := dvd_sub (hyl σ) (hxl σ)
        rw [← e', pow_succ] at hdiv
        obtain ⟨k, hk⟩ := (mul_dvd_mul_iff_left hQ.ne').1 hdiv
        have a := offP_inM h xp σ
        have b := offP_inM h yp σ
        have hL : Lz h = 2 * h + 1 := rfl
        have : k = 0 := by
          rcases lt_trichotomy k 0 with hk0 | hk0 | hk0
          · have : (2 * h + 1 : ℤ) * k ≤ -(2 * h + 1) := by nlinarith
            rw [← hL] at this; omega
          · exact hk0
          · have : (2 * h + 1 : ℤ) ≤ (2 * h + 1) * k := by nlinarith
            rw [← hL] at this; omega
        rw [this, mul_zero] at hk; linarith
      have hp : xp = yp := by
        funext σ
        have := hd σ
        simp only [offP] at this
        exact Fin.ext (by omega)
      subst hp
      have hxy' : x = y := by
        funext σ
        have e := congrFun hxy σ
        simp only [Pi.add_apply] at e
        linarith
      rw [hxy']
    have e1 : ∑ x ∈ boxPts h nl (l + 1), ∑ xp : Pts h,
        (if RB h nl μ (l + 1) x ρ then f (x + Lz h ^ l • (offP h xp + (j : ℤ) • Pi.single ρ 1)) ρ else 0) =
        ∑ p ∈ S, f (φ p) ρ := by
      rw [Finset.sum_filter, Finset.sum_product]
    rw [e1, ← Finset.sum_image (f := fun y => f y ρ) hinj]
    rw [← Finset.sum_filter]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun y _ _ => hf y ρ
    intro y hy
    obtain ⟨⟨x, xp⟩, hp, rfl⟩ := Finset.mem_image.1 hy
    simp only [S, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true] at hp
    have hr := line_RB hp.2 xp hj
    exact Finset.mem_filter.2 ⟨mem_boxPts hr.2.1, hr⟩
  -- sum over the positions and the directions
  have e2 : ∑ x ∈ boxPts h nl (l + 1), ∑ ρ : Fin 4, ∑ xp : Pts h, ∑ j ∈ Finset.range (2 * h + 1),
      (if RB h nl μ (l + 1) x ρ then f (x + Lz h ^ l • (offP h xp + (j : ℤ) • Pi.single ρ 1)) ρ else 0) =
      ∑ ρ : Fin 4, ∑ j ∈ Finset.range (2 * h + 1), ∑ x ∈ boxPts h nl (l + 1), ∑ xp : Pts h,
      (if RB h nl μ (l + 1) x ρ then f (x + Lz h ^ l • (offP h xp + (j : ℤ) • Pi.single ρ 1)) ρ else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    calc _ = ∑ x ∈ boxPts h nl (l + 1), ∑ j ∈ Finset.range (2 * h + 1), ∑ xp : Pts h,
          (if RB h nl μ (l + 1) x ρ then f (x + Lz h ^ l • (offP h xp + (j : ℤ) • Pi.single ρ 1)) ρ else 0) :=
          Finset.sum_congr rfl fun x _ => Finset.sum_comm
      _ = _ := Finset.sum_comm
  rw [e2]
  calc ∑ ρ : Fin 4, ∑ j ∈ Finset.range (2 * h + 1), ∑ x ∈ boxPts h nl (l + 1), ∑ xp : Pts h,
        (if RB h nl μ (l + 1) x ρ then f (x + Lz h ^ l • (offP h xp + (j : ℤ) • Pi.single ρ 1)) ρ else 0)
      ≤ ∑ ρ : Fin 4, ∑ _j ∈ Finset.range (2 * h + 1),
          ∑ x' ∈ boxPts h nl l, (if RB h nl μ l x' ρ then f x' ρ else 0) :=
        Finset.sum_le_sum fun ρ _ => Finset.sum_le_sum fun j hj => key ρ j (Finset.mem_range.1 hj)
    _ = ((2 * h + 1 : ℕ) : ℝ) * ell1 h nl μ l f := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ell1]
        rw [← Finset.mul_sum, Finset.sum_comm]


/-- **`Q₀` of a gauge field as a mean over the lines**: `‖L(Q₀(U)B)(c)‖ ≤ L⁻⁴Σ_{x ∈ B(c₋)}Σ_{b ∈ [x, x + c]}‖B(b)‖`, the
transports along the paths `Γ_b` being isometries. -/
theorem norm_Q0L_lines {n : ℕ} [NeZero n] {h : ℕ} {U : Config N n} (hU : U.IsGaugeField) (y : Site n) (μ : Fin 4)
    (B : Fin 4 → Site n → Mat) :
    ‖Q0L U y μ h B‖ ≤ (((2 * h + 1 : ℕ) : ℝ) ^ 4)⁻¹ *
      ∑ xp : Pts h, ∑ j ∈ Finset.range (2 * h + 1), ‖B μ (ofs y (offP h xp) + j • unit n μ)‖ := by
  simp only [Q0L, ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_sum', Finset.sum_apply,
    ContinuousLinearMap.comp_apply, AdL_apply, evalL_apply]
  rw [norm_smul, norm_inv, norm_pow, Complex.norm_natCast]
  refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => ?_)) (by positivity)
  have hn0 : (0 : ℝ) < (nG h x : ℝ) := by exact_mod_cast card_ords_pos (offP h x)
  rw [norm_smul, norm_inv, Complex.norm_natCast]
  have hs : ‖∑ Γ : Ords (offP h x), ∑ j ∈ Finset.range (2 * h + 1),
      Ad (U.hol (pathGb y μ h x Γ j)) (B μ (ofs y (offP h x) + j • unit n μ))‖ ≤
      (nG h x : ℝ) * ∑ j ∈ Finset.range (2 * h + 1), ‖B μ (ofs y (offP h x) + j • unit n μ)‖ := by
    refine (norm_sum_le _ _).trans ?_
    have : ∀ Γ : Ords (offP h x), ‖∑ j ∈ Finset.range (2 * h + 1),
        Ad (U.hol (pathGb y μ h x Γ j)) (B μ (ofs y (offP h x) + j • unit n μ))‖ ≤
        ∑ j ∈ Finset.range (2 * h + 1), ‖B μ (ofs y (offP h x) + j • unit n μ)‖ := fun Γ => by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
      rw [SupportCont.opNorm_Ad_unitary (hol_unitary' U hU _)]
    refine (Finset.sum_le_sum fun Γ _ => this Γ).trans ?_
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  calc (nG h x : ℝ)⁻¹ * _ ≤ (nG h x : ℝ)⁻¹ * ((nG h x : ℝ) *
        ∑ j ∈ Finset.range (2 * h + 1), ‖B μ (ofs y (offP h x) + j • unit n μ)‖) :=
        mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by field_simp

/-- The sites of the lines of the bond `img x` of the level `l + 1` are the images of the points of the level `l`. -/
lemma line_site {n : ℕ} [NeZero n] {h l : ℕ} (y : Site n) {x : Fin 4 → ℤ} (hx : Lat (Lz h) l x) (ρ : Fin 4)
    (xp : Pts h) (j : ℕ) :
    ofs (img h y l x) (offP h xp) + j • unit n ρ = img h y l (x + Lz h ^ l • (offP h xp + (j : ℤ) • Pi.single ρ 1)) := by
  rw [← img_add y hx]
  induction j with
  | zero => simp
  | succ j ih =>
    rw [succ_nsmul, ← add_assoc, ih]
    have := ofs1 (img h y l x) (offP h xp + (j : ℤ) • Pi.single ρ 1) ρ
    rw [← this]
    congr 1
    push_cast
    rw [add_smul, one_smul, add_assoc]

open Classical in
/-- The supremum of a form over the box of a bond of the level `l + 1` is at most its `ℓ¹`-sum over the box. -/
lemma restrict_le_sum_box {n : ℕ} [NeZero n] {h nl l : ℕ} (hn : 4 * h + 4 ≤ n) {μ ρ : Fin 4} (y : Site n)
    {x : Fin 4 → ℤ} (hx : Lat (Lz h) (l + 1) x) (h0 : Rg h nl μ (l + 1) x)
    (h1 : Rg h nl μ (l + 1) (x + Lz h ^ (l + 1) • Pi.single ρ 1)) [DecidablePred (InBoxB (img h y l x) h ρ)]
    (B : Fin 4 → Site n → Mat) :
    ‖restrictF B (InBoxB (img h y l x) h ρ)‖ ≤
      ∑ x' ∈ boxPts h nl l, ∑ ν : Fin 4,
        (if RB h nl μ l x' ν ∧ Pbox h l x ρ x' ν then ‖B ν (img h y l x')‖ else 0) := by
  have hnn : ∀ x' ν, 0 ≤ (if RB h nl μ l x' ν ∧ Pbox h l x ρ x' ν then ‖B ν (img h y l x')‖ else 0) :=
    fun x' ν => by split_ifs; exacts [norm_nonneg _, le_rfl]
  refine norm_restrictF_box_le (Finset.sum_nonneg fun x' _ => Finset.sum_nonneg fun ν _ => hnn x' ν)
    fun ν z hb => ?_
  obtain ⟨x', hr, hp, rfl⟩ := box_site' hn y hx h0 h1 hb
  have hx' : x' ∈ boxPts h nl l := mem_boxPts hr.2.1
  calc ‖B ν (img h y l x')‖ = if RB h nl μ l x' ν ∧ Pbox h l x ρ x' ν then ‖B ν (img h y l x')‖ else 0 := by
        rw [if_pos ⟨hr, hp⟩]
    _ ≤ ∑ ν' : Fin 4, (if RB h nl μ l x' ν' ∧ Pbox h l x ρ x' ν' then ‖B ν' (img h y l x')‖ else 0) :=
        Finset.single_le_sum (f := fun ν' => if RB h nl μ l x' ν' ∧ Pbox h l x ρ x' ν' then
          ‖B ν' (img h y l x')‖ else 0) (fun ν' _ => hnn x' ν') (Finset.mem_univ ν)
    _ ≤ _ := Finset.single_le_sum (f := fun x'' => ∑ ν' : Fin 4, (if RB h nl μ l x'' ν' ∧ Pbox h l x ρ x'' ν' then
          ‖B ν' (img h y l x'')‖ else 0)) (fun x'' _ => Finset.sum_nonneg fun ν' _ => hnn x'' ν') hx'


/-- **`Q = Q₀ + E`**: `‖LQ(e^{iaA'}U)B - LQ₀(U)B‖ ≤ C(α₀ + α₁)‖B‖_{∞,box}`, from (vii) and (v) of
`prop:relative-average`. -/
theorem pert_bound (h : ℕ) (μ : Fin 4) :
    ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧
      ∀ {n : ℕ} [NeZero n] (U : Config N n), U.IsGaugeField → 4 * h + 4 ≤ n → ∀ (y : Site n)
        [DecidablePred (InBoxB y h μ)] (α₀ α₁ : ℝ), 0 ≤ α₀ → 0 ≤ α₁ → α₀ ≤ c → α₁ ≤ c →
        (∀ μ' ν' z, PlaqIn (boxR y (loD h) (hiD h μ μ)) μ' ν' z →
          hs (((plaq U μ' ν' z : GLN) : Mat) - 1) ≤ α₀) →
        ∀ A' : Fin 4 → Site n → Mat, (∀ ρ z, BoxBond y h μ ρ z → ‖A' ρ z‖ ≤ α₁) →
        ∀ B : Fin 4 → Site n → Mat,
          ‖((2 * h + 1 : ℕ) : ℂ) • Qlin (moveC U A') y μ h B - Q0L U y μ h B‖ ≤
            C * (α₀ + α₁) * ‖restrictF B (InBoxB y h μ)‖ := by
  obtain ⟨cb, C₀, C₁, C₂, C₃, hcb, hC₀, hC₁, hC₂, hC₃, hbox⟩ := relative_average_box (N := N) h μ
  obtain ⟨c7, C₇, hc7, hC₇, h7⟩ := relative_average_vii_box (N := N) h μ
  refine ⟨min cb c7, C₀ + C₇, lt_min hcb hc7, by positivity, ?_⟩
  intro n _ U hU hn y _ α₀ α₁ hα₀ hα₁ hα₀c hα₁c hplq A' hA' B
  have hcb' : min cb c7 ≤ cb := min_le_left _ _
  have hc7' : min cb c7 ≤ c7 := min_le_right _ _
  set R := restrictF B (InBoxB y h μ)
  have hA0 : ∀ ρ z, BoxBond y h μ ρ z → ‖(0 : Fin 4 → Site n → Mat) ρ z‖ ≤ α₁ := fun ρ z _ => by
    simp only [Pi.zero_apply, norm_zero]; exact hα₁
  have hA0' : ∀ ρ z, BoxBond y h μ ρ z → ‖(0 : Fin 4 → Site n → Mat) ρ z‖ ≤ (0 : ℝ) := fun ρ z _ => by simp
  have h1 := h7 U hU hn y α₀ α₁ hα₀ hα₁ (hα₀c.trans hc7') (hα₁c.trans hc7') hplq A' 0 hA' hA0 B
  rw [moveC_zero, sub_zero] at h1
  have hRA : ‖restrictF A' (InBoxB y h μ)‖ ≤ α₁ := norm_restrictF_box_le hα₁ hA'
  obtain ⟨h2, -, -⟩ := hbox U hU hn y α₀ 0 hα₀ le_rfl (hα₀c.trans hcb') hcb.le hplq 0 hA0' B
  rw [moveC_zero, add_zero] at h2
  have e : ((2 * h + 1 : ℕ) : ℂ) • Qlin (moveC U A') y μ h B - Q0L U y μ h B =
      (((2 * h + 1 : ℕ) : ℂ) • Qlin (moveC U A') y μ h B - ((2 * h + 1 : ℕ) : ℂ) • Qlin U y μ h B) +
      (((2 * h + 1 : ℕ) : ℂ) • Qlin U y μ h B - Q0L U y μ h B) := by abel
  rw [e]
  have hR0 : 0 ≤ ‖R‖ := norm_nonneg _
  have h1' : C₇ * ‖restrictF A' (InBoxB y h μ)‖ * ‖R‖ ≤ C₇ * α₁ * ‖R‖ :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hRA hC₇) hR0
  refine (norm_add_le _ _).trans ?_
  nlinarith [mul_nonneg (mul_nonneg hC₀ hα₁) hR0, mul_nonneg (mul_nonneg hC₇ hα₀) hR0]

open Classical in
/-- **One step of the kernel bound** (the proof of `lem:average-kernels`, "One step"): under the per-level
hypotheses, the linear parts `D_{l+1} = LQ(V_l)D_l` satisfy `Σ_{c'}‖D_{l+1}(c')‖ ≤ (L⁻³ + 8C(α₀⁽ˡ⁾ + α₁⁽ˡ⁾))Σ_{b'}‖D_l(b')‖`,
the sums over the bonds of the regions: `‖Q⁽ˡ⁾A‖_{1,l+1} ≤ (1 + 8L³C(α₀⁽ˡ⁾ + α₁⁽ˡ⁾))‖A‖_{1,l}`. -/
theorem kernel_step (h : ℕ) :
    ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧ ∀ (nl : ℕ) (μ : Fin 4) (nn : ℕ → ℕ) [∀ l, NeZero (nn l)],
      (∀ l, 4 * h + 4 ≤ nn l) → ∀ (base : ∀ l, Site (nn l)) (U V : ∀ l, Config N (nn l))
      (A' D : ∀ l, Fin 4 → Site (nn l) → Mat) (a₀ a₁ : ℕ → ℝ),
      (∀ l, U l |>.IsGaugeField) →
      (∀ l, l < nl → ∀ ν x, Lat (Lz h) l x → Rg h nl μ l x → Rg h nl μ l (x + Lz h ^ l • Pi.single ν 1) →
        V l ν (img h (base l) l x) = moveC (U l) (A' l) ν (img h (base l) l x)) →
      (∀ l, l < nl → ∀ ρ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x →
        Rg h nl μ (l + 1) (x + Lz h ^ (l + 1) • Pi.single ρ 1) →
        (∀ μ' ν' z, PlaqIn (boxR (img h (base l) l x) (loD h) (hiD h ρ ρ)) μ' ν' z →
          hs (((plaq (U l) μ' ν' z : GLN) : Mat) - 1) ≤ a₀ l) ∧
        (∀ ν z, BoxBond (img h (base l) l x) h ρ ν z → ‖A' l ν z‖ ≤ a₁ l)) →
      (∀ l, l < nl → 0 ≤ a₀ l ∧ 0 ≤ a₁ l ∧ a₀ l ≤ c ∧ a₁ l ≤ c) →
      (∀ l, l < nl → ∀ ρ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x →
        Rg h nl μ (l + 1) (x + Lz h ^ (l + 1) • Pi.single ρ 1) →
        D (l + 1) ρ (img h (base (l + 1)) (l + 1) x) =
          ((2 * h + 1 : ℕ) : ℂ) • Qlin (V l) (img h (base l) l x) ρ h (D l)) →
      ∀ l, l < nl →
        ell1 h nl μ (l + 1) (fun x ν => ‖D (l + 1) ν (img h (base (l + 1)) (l + 1) x)‖) ≤
          ((((2 * h + 1 : ℕ) : ℝ) ^ 3)⁻¹ + 8 * C * (a₀ l + a₁ l)) *
            ell1 h nl μ l (fun x ν => ‖D l ν (img h (base l) l x)‖) := by
  choose cp Cp hcp hCp hpert using fun ρ : Fin 4 => pert_bound (N := N) h ρ
  set c := Finset.univ.inf' Finset.univ_nonempty cp
  set C := Finset.univ.sup' Finset.univ_nonempty Cp
  have hc0 : 0 < c := (Finset.lt_inf'_iff _).2 fun ρ _ => hcp ρ
  have hcle : ∀ ρ, c ≤ cp ρ := fun ρ => Finset.inf'_le _ (Finset.mem_univ ρ)
  have hCle : ∀ ρ, Cp ρ ≤ C := fun ρ => Finset.le_sup' _ (Finset.mem_univ ρ)
  have hC0 : 0 ≤ C := (hCp 0).trans (hCle 0)
  refine ⟨c, C, hc0, hC0, ?_⟩
  intro nl μ nn _ hn base U V A' D a₀ a₁ hU hVU hdat ha hD l hl
  have hn2 : 4 * h + 2 ≤ nn l := by have := hn l; omega
  obtain ⟨ha0, ha1, ha0c, ha1c⟩ := ha l hl
  set f : (Fin 4 → ℤ) → Fin 4 → ℝ := fun x ν => ‖D l ν (img h (base l) l x)‖ with hf
  have hf0 : ∀ x ν, 0 ≤ f x ν := fun x ν => norm_nonneg _
  set Lr : ℝ := ((2 * h + 1 : ℕ) : ℝ) with hLr
  have hL0 : 0 < Lr := by positivity
  set α := a₀ l + a₁ l
  -- the bound at one bond of the level `l + 1`
  have hbond : ∀ x ρ, (if RB h nl μ (l + 1) x ρ then ‖D (l + 1) ρ (img h (base (l + 1)) (l + 1) x)‖ else 0) ≤
      (Lr ^ 4)⁻¹ * ∑ xp : Pts h, ∑ j ∈ Finset.range (2 * h + 1),
        (if RB h nl μ (l + 1) x ρ then f (x + Lz h ^ l • (offP h xp + (j : ℤ) • Pi.single ρ 1)) ρ else 0) +
      C * α * ∑ x' ∈ boxPts h nl l, ∑ ν : Fin 4,
        (if RB h nl μ (l + 1) x ρ ∧ RB h nl μ l x' ν ∧ Pbox h l x ρ x' ν then f x' ν else 0) := by
    intro x ρ
    by_cases hb : RB h nl μ (l + 1) x ρ
    · obtain ⟨hx, q0, q1⟩ := hb
      have hb' : RB h nl μ (l + 1) x ρ := ⟨hx, q0, q1⟩
      simp only [hb', if_true, true_and]
      set y := img h (base l) l x
      have hbox : ∀ ν z, (Bm y h z ∨ Bp y h ρ z) → (Bm y h (z + unit (nn l) ν) ∨ Bp y h ρ (z + unit (nn l) ν)) →
          V l ν z = moveC (U l) (A' l) ν z := fun ν z h1 h2 => by
        obtain ⟨x', hx', r0, r1, rfl⟩ := box_site (hn l) (base l) hx q0 q1 ⟨h1, h2⟩
        exact hVU l hl ν x' hx' r0 r1
      have hQ : Qlin (V l) y ρ h = Qlin (moveC (U l) (A' l)) y ρ h := by
        simp only [Qlin, relLog_fun_local (y := y) (μ := ρ) (h := h) hn2 hbox]
      obtain ⟨hpl, hA⟩ := hdat l hl ρ x hx q0 q1
      have hp := hpert ρ (U l) (hU l) (hn l) y (a₀ l) (a₁ l) ha0 ha1 (ha0c.trans (hcle ρ)) (ha1c.trans (hcle ρ))
        hpl (A' l) hA (D l)
      have hq := norm_Q0L_lines (h := h) (hU l) y ρ (D l)
      have hR := restrict_le_sum_box (nl := nl) (μ := μ) (hn l) (base l) hx q0 q1 (D l)
      have hxl := lat_succ_le hx
      have hlines : ∑ xp : Pts h, ∑ j ∈ Finset.range (2 * h + 1),
          ‖D l ρ (ofs y (offP h xp) + j • unit (nn l) ρ)‖ =
          ∑ xp : Pts h, ∑ j ∈ Finset.range (2 * h + 1), f (x + Lz h ^ l • (offP h xp + (j : ℤ) • Pi.single ρ 1)) ρ := by
        refine Finset.sum_congr rfl fun xp _ => Finset.sum_congr rfl fun j _ => ?_
        simp only [hf, y, line_site (base l) hxl ρ xp j]
      rw [hD l hl ρ x hx q0 q1, hQ]
      have e : ((2 * h + 1 : ℕ) : ℂ) • Qlin (moveC (U l) (A' l)) y ρ h (D l) =
          Q0L (U l) y ρ h (D l) + (((2 * h + 1 : ℕ) : ℂ) • Qlin (moveC (U l) (A' l)) y ρ h (D l) -
            Q0L (U l) y ρ h (D l)) := by abel
      rw [e]
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [← hlines]; exact hq
      · refine hp.trans ?_
        have hCα : Cp ρ * α ≤ C * α := mul_le_mul_of_nonneg_right (hCle ρ) (by positivity)
        calc Cp ρ * α * ‖restrictF (D l) (InBoxB y h ρ)‖ ≤ C * α * ‖restrictF (D l) (InBoxB y h ρ)‖ :=
              mul_le_mul_of_nonneg_right hCα (norm_nonneg _)
          _ ≤ C * α * _ := mul_le_mul_of_nonneg_left hR (by positivity)
    · rw [if_neg hb]
      have h1 : 0 ≤ (Lr ^ 4)⁻¹ * ∑ xp : Pts h, ∑ j ∈ Finset.range (2 * h + 1),
          (if RB h nl μ (l + 1) x ρ then f (x + Lz h ^ l • (offP h xp + (j : ℤ) • Pi.single ρ 1)) ρ else 0) :=
        mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by
          split_ifs <;> first | exact hf0 _ _ | exact le_rfl)
      have h2 : 0 ≤ C * α * ∑ x' ∈ boxPts h nl l, ∑ ν : Fin 4,
          (if RB h nl μ (l + 1) x ρ ∧ RB h nl μ l x' ν ∧ Pbox h l x ρ x' ν then f x' ν else 0) :=
        mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by
          split_ifs <;> first | exact hf0 _ _ | exact le_rfl)
      linarith
  -- sum over the bonds of the level `l + 1`
  have hlin := sum_lines_le h nl l μ hf0
  have hbx := sum_box_le h nl l μ hf0
  have hsum : ell1 h nl μ (l + 1) (fun x ν => ‖D (l + 1) ν (img h (base (l + 1)) (l + 1) x)‖) ≤
      (Lr ^ 4)⁻¹ * ∑ x ∈ boxPts h nl (l + 1), ∑ ρ : Fin 4, ∑ xp : Pts h, ∑ j ∈ Finset.range (2 * h + 1),
        (if RB h nl μ (l + 1) x ρ then f (x + Lz h ^ l • (offP h xp + (j : ℤ) • Pi.single ρ 1)) ρ else 0) +
      C * α * ∑ x ∈ boxPts h nl (l + 1), ∑ ρ : Fin 4, ∑ x' ∈ boxPts h nl l, ∑ ν : Fin 4,
        (if RB h nl μ (l + 1) x ρ ∧ RB h nl μ l x' ν ∧ Pbox h l x ρ x' ν then f x' ν else 0) := by
    simp only [ell1, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun ρ _ => by
      simpa only [Finset.mul_sum] using hbond x ρ
  refine hsum.trans ?_
  have hCα0 : 0 ≤ C * α := by positivity
  calc (Lr ^ 4)⁻¹ * _ + C * α * _ ≤ (Lr ^ 4)⁻¹ * (Lr * ell1 h nl μ l f) + C * α * (8 * ell1 h nl μ l f) :=
        add_le_add (mul_le_mul_of_nonneg_left hlin (by positivity)) (mul_le_mul_of_nonneg_left hbx hCα0)
    _ = ((Lr ^ 3)⁻¹ + 8 * C * α) * ell1 h nl μ l f := by
        field_simp


open Classical in
/-- **`lem:average-kernels`, the first bound**: under the per-level hypotheses with the data of the level `l` at most
`eL^{-(n-l)}`, `e ≤ c`, `8L³Ce ≤ 1`, the linear parts `D_{l+1} = LQ(V_l)D_l` satisfy
`Σ_{c'}‖D_n(c')‖ ≤ 2L^{-3n}Σ_{b'}‖D_0(b')‖`; for `D_0` supported on one bond `b`, `‖D_n(c)‖ ≤ 2L^{-3n}‖D_0(b)‖`, that is
`‖(Q_n(𝐔)A₁)(c)‖ ≤ 2(a_i/a_j)⁴‖A₁(b)‖` (`C_Q = 2`). -/
theorem average_kernels_i (h : ℕ) (hh : 1 ≤ h) :
    ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧ ∀ (nl : ℕ) (μ : Fin 4) (nn : ℕ → ℕ) [∀ l, NeZero (nn l)],
      (∀ l, 4 * h + 4 ≤ nn l) → ∀ (base : ∀ l, Site (nn l)) (U V : ∀ l, Config N (nn l))
      (A' D : ∀ l, Fin 4 → Site (nn l) → Mat) (a₀ a₁ : ℕ → ℝ) (e : ℝ),
      (∀ l, U l |>.IsGaugeField) →
      (∀ l, l < nl → ∀ ν x, Lat (Lz h) l x → Rg h nl μ l x → Rg h nl μ l (x + Lz h ^ l • Pi.single ν 1) →
        V l ν (img h (base l) l x) = moveC (U l) (A' l) ν (img h (base l) l x)) →
      (∀ l, l < nl → ∀ ρ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x →
        Rg h nl μ (l + 1) (x + Lz h ^ (l + 1) • Pi.single ρ 1) →
        (∀ μ' ν' z, PlaqIn (boxR (img h (base l) l x) (loD h) (hiD h ρ ρ)) μ' ν' z →
          hs (((plaq (U l) μ' ν' z : GLN) : Mat) - 1) ≤ a₀ l) ∧
        (∀ ν z, BoxBond (img h (base l) l x) h ρ ν z → ‖A' l ν z‖ ≤ a₁ l)) →
      (∀ l, l < nl → 0 ≤ a₀ l ∧ 0 ≤ a₁ l ∧ a₀ l + a₁ l ≤ e * ((((2 * h + 1 : ℕ) : ℝ)) ^ (nl - l))⁻¹) →
      0 ≤ e → e ≤ c → 8 * (((2 * h + 1 : ℕ) : ℝ)) ^ 3 * C * e ≤ 1 →
      (∀ l, l < nl → ∀ ρ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x →
        Rg h nl μ (l + 1) (x + Lz h ^ (l + 1) • Pi.single ρ 1) →
        D (l + 1) ρ (img h (base (l + 1)) (l + 1) x) =
          ((2 * h + 1 : ℕ) : ℂ) • Qlin (V l) (img h (base l) l x) ρ h (D l)) →
      ell1 h nl μ nl (fun x ν => ‖D nl ν (img h (base nl) nl x)‖) ≤
        2 * ((((2 * h + 1 : ℕ) : ℝ) ^ 3)⁻¹) ^ nl * ell1 h nl μ 0 (fun x ν => ‖D 0 ν (img h (base 0) 0 x)‖) := by
  obtain ⟨c, C, hc, hC, hks⟩ := kernel_step (N := N) h
  refine ⟨c, C, hc, hC, ?_⟩
  intro nl μ nn _ hn base U V A' D a₀ a₁ e hU hVU hdat ha he hec hCe hD
  set Lr : ℝ := ((2 * h + 1 : ℕ) : ℝ) with hLr
  have hL3 : 3 ≤ Lr := by rw [hLr]; push_cast; have : (1 : ℝ) ≤ h := by exact_mod_cast hh
                          linarith
  have hL0 : 0 < Lr := by linarith
  set q : ℝ := (Lr ^ 3)⁻¹ with hq
  have hq0 : 0 < q := by positivity
  have hp1 : ∀ m, (Lr ^ m)⁻¹ ≤ 1 := fun m => inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith))
  set x : ℕ → ℝ := fun l => if l < nl then a₀ l + a₁ l else 0 with hx
  have hx0 : ∀ l, 0 ≤ x l := fun l => by
    simp only [hx]; split_ifs with hl
    · obtain ⟨h1, h2, -⟩ := ha l hl; linarith
    · exact le_rfl
  have hstep := hks nl μ nn hn base U V A' D a₀ a₁ hU hVU hdat
    (fun l hl => by
      obtain ⟨h1, h2, h3⟩ := ha l hl
      have : e * (Lr ^ (nl - l))⁻¹ ≤ e := by have := hp1 (nl - l); nlinarith
      exact ⟨h1, h2, by linarith, by linarith⟩) hD
  set E : ℕ → ℝ := fun l => ell1 h nl μ l (fun x ν => ‖D l ν (img h (base l) l x)‖) with hE
  have hE0 : ∀ l, 0 ≤ E l := fun l => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by
    split_ifs; exacts [norm_nonneg _, le_rfl]
  -- the iteration
  have hit : ∀ l, l ≤ nl → E l ≤ (∏ m ∈ Finset.range l, (q + 8 * C * x m)) * E 0 := by
    intro l
    induction l with
    | zero => intro _; simp
    | succ l ih =>
      intro hl
      have hll : l < nl := by omega
      have h1 := hstep l hll
      have hxl : x l = a₀ l + a₁ l := by simp only [hx, if_pos hll]
      rw [Finset.prod_range_succ, hxl]
      calc E (l + 1) ≤ (q + 8 * C * (a₀ l + a₁ l)) * E l := h1
        _ ≤ (q + 8 * C * (a₀ l + a₁ l)) * ((∏ m ∈ Finset.range l, (q + 8 * C * x m)) * E 0) :=
            mul_le_mul_of_nonneg_left (ih hll.le) (by have := hx0 l; rw [hxl] at this; positivity)
        _ = _ := by ring
  -- the product
  have hprod := prod_le_exp hq0 (by positivity : (0 : ℝ) ≤ 8 * C) x hx0 nl
  have hsum : ∑ l ∈ Finset.range nl, x l ≤ e / 2 := by
    have hg := geom_partial hL3 nl nl le_rfl
    simp only [Nat.sub_self, pow_zero, _root_.inv_one, mul_one] at hg
    calc ∑ l ∈ Finset.range nl, x l ≤ ∑ l ∈ Finset.range nl, e * (Lr ^ (nl - l))⁻¹ :=
          Finset.sum_le_sum fun l hl => by
            simp only [hx, if_pos (Finset.mem_range.1 hl)]; exact (ha l (Finset.mem_range.1 hl)).2.2
      _ = e * ∑ l ∈ Finset.range nl, (Lr ^ (nl - l))⁻¹ := by rw [Finset.mul_sum]
      _ ≤ e * (1 / 2) := mul_le_mul_of_nonneg_left hg he
      _ = e / 2 := by ring
  have hexp : Real.exp (8 * C * (∑ l ∈ Finset.range nl, x l) / q) ≤ 2 := by
    have hy0 : 0 ≤ 8 * C * (∑ l ∈ Finset.range nl, x l) / q :=
      div_nonneg (mul_nonneg (by positivity) (Finset.sum_nonneg fun l _ => hx0 l)) hq0.le
    have hy1 : 8 * C * (∑ l ∈ Finset.range nl, x l) / q ≤ 1 / 2 := by
      rw [hq, div_inv_eq_mul]
      have h8 : 0 ≤ 8 * C := by positivity
      have := mul_le_mul_of_nonneg_left hsum h8
      have hL3' : 0 ≤ Lr ^ 3 := by positivity
      calc 8 * C * (∑ l ∈ Finset.range nl, x l) * Lr ^ 3 ≤ 8 * C * (e / 2) * Lr ^ 3 :=
            mul_le_mul_of_nonneg_right this hL3'
        _ = (8 * Lr ^ 3 * C * e) / 2 := by ring
        _ ≤ 1 / 2 := by linarith
    have := GroupMean.exp_small_le hy0 (hy1.trans (by norm_num))
    linarith
  calc E nl ≤ (∏ m ∈ Finset.range nl, (q + 8 * C * x m)) * E 0 := hit nl le_rfl
    _ ≤ (q ^ nl * 2) * E 0 :=
        mul_le_mul_of_nonneg_right (hprod.trans (mul_le_mul_of_nonneg_left hexp (by positivity))) (hE0 0)
    _ = 2 * q ^ nl * E 0 := by ring

open Classical in
/-- The `ℓ¹`-sum of a form supported on one bond of the region is its value there. -/
lemma ell1_single {h nl l : ℕ} {μ : Fin 4} {f : (Fin 4 → ℤ) → Fin 4 → ℝ} {x₀ : Fin 4 → ℤ} {ν₀ : Fin 4}
    (hb : RB h nl μ l x₀ ν₀) (hf : ∀ x ν, RB h nl μ l x ν → (x, ν) ≠ (x₀, ν₀) → f x ν = 0) :
    ell1 h nl μ l f = f x₀ ν₀ := by
  simp only [ell1]
  rw [Finset.sum_eq_single x₀]
  · rw [Finset.sum_eq_single ν₀]
    · rw [if_pos hb]
    · intro ν _ hν
      split_ifs with h'
      · exact hf x₀ ν h' (by simp [hν])
      · rfl
    · intro h'; exact absurd (Finset.mem_univ ν₀) h'
  · intro x _ hx
    refine Finset.sum_eq_zero fun ν _ => ?_
    split_ifs with h'
    · exact hf x ν h' (by simp [hx])
    · rfl
  · intro h'; exact absurd (mem_boxPts hb.2.1) h'

/-- **`lem:average-kernels`, the first bound at a single bond**: if `D_0 = A₁` vanishes on the bonds of the region
other than `b`, then `‖D_n(c)‖ ≤ 2L^{-3n}‖A₁(b)‖` at every bond `c` of the region of the last level. -/
theorem average_kernels_i_single (h : ℕ) (hh : 1 ≤ h) :
    ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧ ∀ (nl : ℕ) (μ : Fin 4) (nn : ℕ → ℕ) [∀ l, NeZero (nn l)],
      (∀ l, 4 * h + 4 ≤ nn l) → ∀ (base : ∀ l, Site (nn l)) (U V : ∀ l, Config N (nn l))
      (A' D : ∀ l, Fin 4 → Site (nn l) → Mat) (a₀ a₁ : ℕ → ℝ) (e : ℝ) (x₀ : Fin 4 → ℤ) (ν₀ : Fin 4),
      (∀ l, U l |>.IsGaugeField) →
      (∀ l, l < nl → ∀ ν x, Lat (Lz h) l x → Rg h nl μ l x → Rg h nl μ l (x + Lz h ^ l • Pi.single ν 1) →
        V l ν (img h (base l) l x) = moveC (U l) (A' l) ν (img h (base l) l x)) →
      (∀ l, l < nl → ∀ ρ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x →
        Rg h nl μ (l + 1) (x + Lz h ^ (l + 1) • Pi.single ρ 1) →
        (∀ μ' ν' z, PlaqIn (boxR (img h (base l) l x) (loD h) (hiD h ρ ρ)) μ' ν' z →
          hs (((plaq (U l) μ' ν' z : GLN) : Mat) - 1) ≤ a₀ l) ∧
        (∀ ν z, BoxBond (img h (base l) l x) h ρ ν z → ‖A' l ν z‖ ≤ a₁ l)) →
      (∀ l, l < nl → 0 ≤ a₀ l ∧ 0 ≤ a₁ l ∧ a₀ l + a₁ l ≤ e * ((((2 * h + 1 : ℕ) : ℝ)) ^ (nl - l))⁻¹) →
      0 ≤ e → e ≤ c → 8 * (((2 * h + 1 : ℕ) : ℝ)) ^ 3 * C * e ≤ 1 →
      (∀ l, l < nl → ∀ ρ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x →
        Rg h nl μ (l + 1) (x + Lz h ^ (l + 1) • Pi.single ρ 1) →
        D (l + 1) ρ (img h (base (l + 1)) (l + 1) x) =
          ((2 * h + 1 : ℕ) : ℂ) • Qlin (V l) (img h (base l) l x) ρ h (D l)) →
      RB h nl μ 0 x₀ ν₀ →
      (∀ x ν, RB h nl μ 0 x ν → (x, ν) ≠ (x₀, ν₀) → D 0 ν (img h (base 0) 0 x) = 0) →
      ∀ x ρ, RB h nl μ nl x ρ →
        ‖D nl ρ (img h (base nl) nl x)‖ ≤
          2 * ((((2 * h + 1 : ℕ) : ℝ) ^ 3)⁻¹) ^ nl * ‖D 0 ν₀ (img h (base 0) 0 x₀)‖ := by
  obtain ⟨c, C, hc, hC, hk⟩ := average_kernels_i (N := N) h hh
  refine ⟨c, C, hc, hC, ?_⟩
  intro nl μ nn _ hn base U V A' D a₀ a₁ e x₀ ν₀ hU hVU hdat ha he hec hCe hD hb0 hsupp x ρ hb
  have hkb := hk nl μ nn hn base U V A' D a₀ a₁ e hU hVU hdat ha he hec hCe hD
  have he1 : ell1 h nl μ 0 (fun x ν => ‖D 0 ν (img h (base 0) 0 x)‖) = ‖D 0 ν₀ (img h (base 0) 0 x₀)‖ :=
    ell1_single (f := fun x ν => ‖D 0 ν (img h (base 0) 0 x)‖) hb0 fun x ν hb hne => by
      show ‖D 0 ν (img h (base 0) 0 x)‖ = 0
      rw [hsupp x ν hb hne, norm_zero]
  have hle : ‖D nl ρ (img h (base nl) nl x)‖ ≤ ell1 h nl μ nl (fun x ν => ‖D nl ν (img h (base nl) nl x)‖) :=
    le_ell1 (f := fun x ν => ‖D nl ν (img h (base nl) nl x)‖) (fun x ν => norm_nonneg _) hb
  rw [he1] at hkb
  exact hle.trans hkb


/-! ### `lem:remainder-kernel` -/

open Classical in
lemma ell1_mono {h nl l : ℕ} {μ : Fin 4} {f g : (Fin 4 → ℤ) → Fin 4 → ℝ}
    (hfg : ∀ x ν, RB h nl μ l x ν → f x ν ≤ g x ν) : ell1 h nl μ l f ≤ ell1 h nl μ l g :=
  Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun ν _ => by
    split_ifs with hb
    · exact hfg x ν hb
    · exact le_rfl

open Classical in
lemma ell1_add {h nl l : ℕ} {μ : Fin 4} (f g : (Fin 4 → ℤ) → Fin 4 → ℝ) :
    ell1 h nl μ l (fun x ν => f x ν + g x ν) = ell1 h nl μ l f + ell1 h nl μ l g := by
  simp only [ell1, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun ν _ => ?_
  split_ifs <;> simp

open Classical in
lemma ell1_smul {h nl l : ℕ} {μ : Fin 4} (c : ℝ) (f : (Fin 4 → ℤ) → Fin 4 → ℝ) :
    ell1 h nl μ l (fun x ν => c * f x ν) = c * ell1 h nl μ l f := by
  simp only [ell1, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun ν _ => ?_
  split_ifs <;> simp

open Classical in
lemma ell1_nonneg {h nl l : ℕ} {μ : Fin 4} {f : (Fin 4 → ℤ) → Fin 4 → ℝ} (hf : ∀ x ν, 0 ≤ f x ν) :
    0 ≤ ell1 h nl μ l f :=
  Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun ν _ => by split_ifs; exacts [hf x ν, le_rfl]

open Classical in
/-- `Σ_{c'}‖X‖_{∞,box(c')} ≤ 8Σ_{b'}‖X(b')‖`. -/
lemma ell1_restrict_le {n : ℕ} [NeZero n] {h nl l : ℕ} (hn : 4 * h + 4 ≤ n) {μ : Fin 4} (y : Site n)
    (X : Fin 4 → Site n → Mat) :
    ell1 h nl μ (l + 1) (fun x ρ => ‖restrictF X (InBoxB (img h y l x) h ρ)‖) ≤
      8 * ell1 h nl μ l (fun x ν => ‖X ν (img h y l x)‖) := by
  refine le_trans ?_ (sum_box_le h nl l μ (f := fun x ν => ‖X ν (img h y l x)‖) fun _ _ => norm_nonneg _)
  simp only [ell1]
  refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun ρ _ => ?_
  by_cases hb : RB h nl μ (l + 1) x ρ
  · rw [if_pos hb]
    obtain ⟨hx, q0, q1⟩ := hb
    refine (restrict_le_sum_box hn y hx q0 q1 X).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun x' _ => Finset.sum_congr rfl fun ν _ => ?_
    simp only [show RB h nl μ (l + 1) x ρ from ⟨hx, q0, q1⟩, true_and]
  · rw [if_neg hb]
    exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by
      split_ifs; exacts [norm_nonneg _, le_rfl]

open Classical in
/-- **One step of the kernel bound for one form**: `Σ_{c'}‖LQ(V_l)X(c')‖ ≤ (L⁻³ + 8C(α₀⁽ˡ⁾ + α₁⁽ˡ⁾))Σ_{b'}‖X(b')‖`. -/
theorem kernel_step1 (h : ℕ) :
    ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧ ∀ (nl : ℕ) (μ : Fin 4) (nn : ℕ → ℕ) [∀ l, NeZero (nn l)],
      (∀ l, 4 * h + 4 ≤ nn l) → ∀ (base : ∀ l, Site (nn l)) (U V : ∀ l, Config N (nn l))
      (A' : ∀ l, Fin 4 → Site (nn l) → Mat) (a₀ a₁ : ℕ → ℝ),
      (∀ l, U l |>.IsGaugeField) →
      (∀ l, l < nl → ∀ ν x, Lat (Lz h) l x → Rg h nl μ l x → Rg h nl μ l (x + Lz h ^ l • Pi.single ν 1) →
        V l ν (img h (base l) l x) = moveC (U l) (A' l) ν (img h (base l) l x)) →
      (∀ l, l < nl → ∀ ρ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x →
        Rg h nl μ (l + 1) (x + Lz h ^ (l + 1) • Pi.single ρ 1) →
        (∀ μ' ν' z, PlaqIn (boxR (img h (base l) l x) (loD h) (hiD h ρ ρ)) μ' ν' z →
          hs (((plaq (U l) μ' ν' z : GLN) : Mat) - 1) ≤ a₀ l) ∧
        (∀ ν z, BoxBond (img h (base l) l x) h ρ ν z → ‖A' l ν z‖ ≤ a₁ l)) →
      (∀ l, l < nl → 0 ≤ a₀ l ∧ 0 ≤ a₁ l ∧ a₀ l ≤ c ∧ a₁ l ≤ c) →
      ∀ l, l < nl → ∀ X : Fin 4 → Site (nn l) → Mat,
        ell1 h nl μ (l + 1) (fun x ν => ‖((2 * h + 1 : ℕ) : ℂ) • Qlin (V l) (img h (base l) l x) ν h X‖) ≤
          ((((2 * h + 1 : ℕ) : ℝ) ^ 3)⁻¹ + 8 * C * (a₀ l + a₁ l)) *
            ell1 h nl μ l (fun x ν => ‖X ν (img h (base l) l x)‖) := by
  choose cp Cp hcp hCp hpert using fun ρ : Fin 4 => pert_bound (N := N) h ρ
  set c := Finset.univ.inf' Finset.univ_nonempty cp
  set C := Finset.univ.sup' Finset.univ_nonempty Cp
  have hc0 : 0 < c := (Finset.lt_inf'_iff _).2 fun ρ _ => hcp ρ
  have hcle : ∀ ρ, c ≤ cp ρ := fun ρ => Finset.inf'_le _ (Finset.mem_univ ρ)
  have hCle : ∀ ρ, Cp ρ ≤ C := fun ρ => Finset.le_sup' _ (Finset.mem_univ ρ)
  have hC0 : 0 ≤ C := (hCp 0).trans (hCle 0)
  refine ⟨c, C, hc0, hC0, ?_⟩
  intro nl μ nn _ hn base U V A' a₀ a₁ hU hVU hdat ha l hl X
  have hn2 : 4 * h + 2 ≤ nn l := by have := hn l; omega
  obtain ⟨ha0, ha1, ha0c, ha1c⟩ := ha l hl
  set f : (Fin 4 → ℤ) → Fin 4 → ℝ := fun x ν => ‖X ν (img h (base l) l x)‖ with hf
  have hf0 : ∀ x ν, 0 ≤ f x ν := fun x ν => norm_nonneg _
  set Lr : ℝ := ((2 * h + 1 : ℕ) : ℝ) with hLr
  have hL0 : 0 < Lr := by positivity
  set α := a₀ l + a₁ l
  -- the bound at one bond of the level `l + 1`
  have hbond : ∀ x ρ, (if RB h nl μ (l + 1) x ρ then ‖((2 * h + 1 : ℕ) : ℂ) • Qlin (V l) (img h (base l) l x) ρ h X‖ else 0) ≤
      (Lr ^ 4)⁻¹ * ∑ xp : Pts h, ∑ j ∈ Finset.range (2 * h + 1),
        (if RB h nl μ (l + 1) x ρ then f (x + Lz h ^ l • (offP h xp + (j : ℤ) • Pi.single ρ 1)) ρ else 0) +
      C * α * ∑ x' ∈ boxPts h nl l, ∑ ν : Fin 4,
        (if RB h nl μ (l + 1) x ρ ∧ RB h nl μ l x' ν ∧ Pbox h l x ρ x' ν then f x' ν else 0) := by
    intro x ρ
    by_cases hb : RB h nl μ (l + 1) x ρ
    · obtain ⟨hx, q0, q1⟩ := hb
      have hb' : RB h nl μ (l + 1) x ρ := ⟨hx, q0, q1⟩
      simp only [hb', if_true, true_and]
      set y := img h (base l) l x
      have hbox : ∀ ν z, (Bm y h z ∨ Bp y h ρ z) → (Bm y h (z + unit (nn l) ν) ∨ Bp y h ρ (z + unit (nn l) ν)) →
          V l ν z = moveC (U l) (A' l) ν z := fun ν z h1 h2 => by
        obtain ⟨x', hx', r0, r1, rfl⟩ := box_site (hn l) (base l) hx q0 q1 ⟨h1, h2⟩
        exact hVU l hl ν x' hx' r0 r1
      have hQ : Qlin (V l) y ρ h = Qlin (moveC (U l) (A' l)) y ρ h := by
        simp only [Qlin, relLog_fun_local (y := y) (μ := ρ) (h := h) hn2 hbox]
      obtain ⟨hpl, hA⟩ := hdat l hl ρ x hx q0 q1
      have hp := hpert ρ (U l) (hU l) (hn l) y (a₀ l) (a₁ l) ha0 ha1 (ha0c.trans (hcle ρ)) (ha1c.trans (hcle ρ))
        hpl (A' l) hA X
      have hq := norm_Q0L_lines (h := h) (hU l) y ρ X
      have hR := restrict_le_sum_box (nl := nl) (μ := μ) (hn l) (base l) hx q0 q1 X
      have hxl := lat_succ_le hx
      have hlines : ∑ xp : Pts h, ∑ j ∈ Finset.range (2 * h + 1),
          ‖X ρ (ofs y (offP h xp) + j • unit (nn l) ρ)‖ =
          ∑ xp : Pts h, ∑ j ∈ Finset.range (2 * h + 1), f (x + Lz h ^ l • (offP h xp + (j : ℤ) • Pi.single ρ 1)) ρ := by
        refine Finset.sum_congr rfl fun xp _ => Finset.sum_congr rfl fun j _ => ?_
        simp only [hf, y, line_site (base l) hxl ρ xp j]
      rw [hQ]
      have e : ((2 * h + 1 : ℕ) : ℂ) • Qlin (moveC (U l) (A' l)) y ρ h X =
          Q0L (U l) y ρ h X + (((2 * h + 1 : ℕ) : ℂ) • Qlin (moveC (U l) (A' l)) y ρ h X -
            Q0L (U l) y ρ h X) := by abel
      rw [e]
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [← hlines]; exact hq
      · refine hp.trans ?_
        have hCα : Cp ρ * α ≤ C * α := mul_le_mul_of_nonneg_right (hCle ρ) (by positivity)
        calc Cp ρ * α * ‖restrictF X (InBoxB y h ρ)‖ ≤ C * α * ‖restrictF X (InBoxB y h ρ)‖ :=
              mul_le_mul_of_nonneg_right hCα (norm_nonneg _)
          _ ≤ C * α * _ := mul_le_mul_of_nonneg_left hR (by positivity)
    · rw [if_neg hb]
      have h1 : 0 ≤ (Lr ^ 4)⁻¹ * ∑ xp : Pts h, ∑ j ∈ Finset.range (2 * h + 1),
          (if RB h nl μ (l + 1) x ρ then f (x + Lz h ^ l • (offP h xp + (j : ℤ) • Pi.single ρ 1)) ρ else 0) :=
        mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by
          split_ifs <;> first | exact hf0 _ _ | exact le_rfl)
      have h2 : 0 ≤ C * α * ∑ x' ∈ boxPts h nl l, ∑ ν : Fin 4,
          (if RB h nl μ (l + 1) x ρ ∧ RB h nl μ l x' ν ∧ Pbox h l x ρ x' ν then f x' ν else 0) :=
        mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by
          split_ifs <;> first | exact hf0 _ _ | exact le_rfl)
      linarith
  -- sum over the bonds of the level `l + 1`
  have hlin := sum_lines_le h nl l μ hf0
  have hbx := sum_box_le h nl l μ hf0
  have hsum : ell1 h nl μ (l + 1) (fun x ν => ‖((2 * h + 1 : ℕ) : ℂ) • Qlin (V l) (img h (base l) l x) ν h X‖) ≤
      (Lr ^ 4)⁻¹ * ∑ x ∈ boxPts h nl (l + 1), ∑ ρ : Fin 4, ∑ xp : Pts h, ∑ j ∈ Finset.range (2 * h + 1),
        (if RB h nl μ (l + 1) x ρ then f (x + Lz h ^ l • (offP h xp + (j : ℤ) • Pi.single ρ 1)) ρ else 0) +
      C * α * ∑ x ∈ boxPts h nl (l + 1), ∑ ρ : Fin 4, ∑ x' ∈ boxPts h nl l, ∑ ν : Fin 4,
        (if RB h nl μ (l + 1) x ρ ∧ RB h nl μ l x' ν ∧ Pbox h l x ρ x' ν then f x' ν else 0) := by
    simp only [ell1, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun ρ _ => by
      simpa only [Finset.mul_sum] using hbond x ρ
  refine hsum.trans ?_
  have hCα0 : 0 ≤ C * α := by positivity
  calc (Lr ^ 4)⁻¹ * _ + C * α * _ ≤ (Lr ^ 4)⁻¹ * (Lr * ell1 h nl μ l f) + C * α * (8 * ell1 h nl μ l f) :=
        add_le_add (mul_le_mul_of_nonneg_left hlin (by positivity)) (mul_le_mul_of_nonneg_left hbx hCα0)
    _ = ((Lr ^ 3)⁻¹ + 8 * C * α) * ell1 h nl μ l f := by
        field_simp


set_option maxHeartbeats 4000000 in
open Classical in
/-- **`lem:remainder-kernel`**: under the per-level hypotheses with data at most `eL^{-(n-l)}`, the forms
`B_{l+1} = (1/i) log 𝓜_{V_l}(B_l)` with `‖B_0‖ ≤ tL^{-n}`, the derivatives `δ_{l+1} = LQ(V_l)δ_l + C'(V_l; B_l)δ_l` of the
forms in the direction `δ_0 = A₁` (the core's `δ^{(l+1)} = Q^{(l)}δ^{(l)} + Y_l`), and the linear parts
`D_{l+1} = LQ(V_l)D_l`, `D_0 = A₁`, satisfy `Σ_{c'}‖δ_n(c') - D_n(c')‖ ≤ 32L³C₃tL^{-3n}Σ_{b'}‖A₁(b')‖`. For `A₁` supported
on one bond `b` this is `‖(𝖢'_n(A)A₁)(c)‖ ≤ 32C₃L³a_j(a_i/a_j)⁴‖A₁(b)‖‖A‖_∞` (`eq:remainder-kernel`). -/
theorem remainder_kernel (h : ℕ) (hh : 1 ≤ h) :
    ∃ c C C₃ : ℝ, 0 < c ∧ 0 ≤ C ∧ 0 ≤ C₃ ∧ ∀ (nl : ℕ) (μ : Fin 4) (nn : ℕ → ℕ) [∀ l, NeZero (nn l)],
      (∀ l, 4 * h + 4 ≤ nn l) → ∀ (base : ∀ l, Site (nn l)) (U V : ∀ l, Config N (nn l))
      (A' B δ D : ∀ l, Fin 4 → Site (nn l) → Mat) (a₀ a₁ : ℕ → ℝ) (t e : ℝ),
      (∀ l, U l |>.IsGaugeField) →
      (∀ l, l < nl → ∀ ν x, Lat (Lz h) l x → Rg h nl μ l x → Rg h nl μ l (x + Lz h ^ l • Pi.single ν 1) →
        V l ν (img h (base l) l x) = moveC (U l) (A' l) ν (img h (base l) l x)) →
      (∀ l, l < nl → ∀ ρ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x →
        Rg h nl μ (l + 1) (x + Lz h ^ (l + 1) • Pi.single ρ 1) →
        (∀ μ' ν' z, PlaqIn (boxR (img h (base l) l x) (loD h) (hiD h ρ ρ)) μ' ν' z →
          hs (((plaq (U l) μ' ν' z : GLN) : Mat) - 1) ≤ a₀ l) ∧
        (∀ ν z, BoxBond (img h (base l) l x) h ρ ν z → ‖A' l ν z‖ ≤ a₁ l)) →
      (∀ l, l < nl → 0 ≤ a₀ l ∧ 0 ≤ a₁ l ∧ a₀ l + a₁ l ≤ e * ((((2 * h + 1 : ℕ) : ℝ)) ^ (nl - l))⁻¹) →
      (∀ l, l < nl → ∀ ρ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x →
        Rg h nl μ (l + 1) (x + Lz h ^ (l + 1) • Pi.single ρ 1) →
        B (l + 1) ρ (img h (base (l + 1)) (l + 1) x) = relLog (V l) (B l) (img h (base l) l x) ρ h ∧
        δ (l + 1) ρ (img h (base (l + 1)) (l + 1) x) =
          ((2 * h + 1 : ℕ) : ℂ) • Qlin (V l) (img h (base l) l x) ρ h (δ l) +
            fderiv ℂ (fun B' => Crem (V l) B' (img h (base l) l x) ρ h) (B l) (δ l) ∧
        D (l + 1) ρ (img h (base (l + 1)) (l + 1) x) =
          ((2 * h + 1 : ℕ) : ℂ) • Qlin (V l) (img h (base l) l x) ρ h (D l)) →
      0 ≤ t → 0 ≤ e → e ≤ c → 2 * t < c → C * (e + 2 * t) ≤ 1 →
      (((2 * h + 1 : ℕ) : ℝ)) ^ 3 * (8 * C * e + 16 * C₃ * t) ≤ 1 →
      (∀ ν x, Lat (Lz h) 0 x → Rg h nl μ 0 x → Rg h nl μ 0 (x + Lz h ^ 0 • Pi.single ν 1) →
        ‖B 0 ν (img h (base 0) 0 x)‖ ≤ t * ((((2 * h + 1 : ℕ) : ℝ)) ^ nl)⁻¹ ∧
        δ 0 ν (img h (base 0) 0 x) = D 0 ν (img h (base 0) 0 x)) →
      ell1 h nl μ nl (fun x ν => ‖δ nl ν (img h (base nl) nl x) - D nl ν (img h (base nl) nl x)‖) ≤
        32 * (((2 * h + 1 : ℕ) : ℝ)) ^ 3 * C₃ * t * ((((2 * h + 1 : ℕ) : ℝ) ^ 3)⁻¹) ^ nl *
          ell1 h nl μ 0 (fun x ν => ‖D 0 ν (img h (base 0) 0 x)‖) := by
  obtain ⟨cf, Cf, hcf, hCf, hof⟩ := order_forms (N := N) h hh
  obtain ⟨ck, Ck, hck, hCk, hks⟩ := kernel_step1 (N := N) h
  choose cb C0 C1 C2 C3 hcb hC0 hC1 hC2 hC3 hbox using fun ρ : Fin 4 => relative_average_box (N := N) h ρ
  set cbm := Finset.univ.inf' Finset.univ_nonempty cb
  set C3m := Finset.univ.sup' Finset.univ_nonempty C3
  have hcbm : ∀ ρ, cbm ≤ cb ρ := fun ρ => Finset.inf'_le _ (Finset.mem_univ ρ)
  have hC3m : ∀ ρ, C3 ρ ≤ C3m := fun ρ => Finset.le_sup' _ (Finset.mem_univ ρ)
  have hcbm0 : 0 < cbm := (Finset.lt_inf'_iff _).2 fun ρ _ => hcb ρ
  have hC3m0 : 0 ≤ C3m := (hC3 0).trans (hC3m 0)
  refine ⟨min cf (min ck cbm), max Cf Ck, C3m, lt_min hcf (lt_min hck hcbm0), hCf.trans (le_max_left _ _),
    hC3m0, ?_⟩
  intro nl μ nn _ hn base U V A' B δ D a₀ a₁ t e hU hVU hdat ha hrel ht he hec htc hCE hsm h0
  have hcf' : min cf (min ck cbm) ≤ cf := min_le_left _ _
  have hck' : min cf (min ck cbm) ≤ ck := (min_le_right _ _).trans (min_le_left _ _)
  have hcb' : min cf (min ck cbm) ≤ cbm := (min_le_right _ _).trans (min_le_right _ _)
  set Lr : ℝ := ((2 * h + 1 : ℕ) : ℝ) with hLr
  have hL3 : 3 ≤ Lr := by rw [hLr]; push_cast; have : (1 : ℝ) ≤ h := by exact_mod_cast hh
                          linarith
  have hL0 : 0 < Lr := by linarith
  set q : ℝ := (Lr ^ 3)⁻¹ with hq
  have hq0 : 0 < q := by positivity
  have hp1 : ∀ m, (Lr ^ m)⁻¹ ≤ 1 := fun m => inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith))
  have hCEf : Cf * (e + 2 * t) ≤ 1 :=
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)).trans hCE
  -- the forms
  have hforms := hof nl μ nn hn base U V A' B a₀ a₁ t e hU hVU hdat (fun l hl ρ x hx q0 q1 =>
    (hrel l hl ρ x hx q0 q1).1) ha ht he (hec.trans hcf') (htc.trans_le hcf') hCEf (fun ν x hx q0 q1 =>
    (h0 ν x hx q0 q1).1)
  have hdat' : ∀ l, l < nl → 0 ≤ a₀ l ∧ 0 ≤ a₁ l ∧ a₀ l ≤ ck ∧ a₁ l ≤ ck := fun l hl => by
    obtain ⟨h1, h2, h3⟩ := ha l hl
    have : e * (Lr ^ (nl - l))⁻¹ ≤ e := by have := hp1 (nl - l); nlinarith
    exact ⟨h1, h2, by linarith [hec.trans hck'], by linarith [hec.trans hck']⟩
  have hks' := hks nl μ nn hn base U V A' a₀ a₁ hU hVU hdat hdat'
  set Eδ : ℕ → ℝ := fun l => ell1 h nl μ l (fun x ν => ‖δ l ν (img h (base l) l x)‖) with hEδ
  set ER : ℕ → ℝ := fun l => ell1 h nl μ l (fun x ν => ‖δ l ν (img h (base l) l x) - D l ν (img h (base l) l x)‖)
    with hER
  have hEδ0 : ∀ l, 0 ≤ Eδ l := fun l => ell1_nonneg fun _ _ => norm_nonneg _
  have hER0 : ∀ l, 0 ≤ ER l := fun l => ell1_nonneg fun _ _ => norm_nonneg _
  set α : ℕ → ℝ := fun l => if l < nl then a₀ l + a₁ l else 0 with hα
  have hα0 : ∀ l, 0 ≤ α l := fun l => by
    simp only [hα]; split_ifs with hl
    · obtain ⟨h1, h2, -⟩ := ha l hl; linarith
    · exact le_rfl
  -- the bound of one step, for `δ` and for `δ - D`
  have hstep : ∀ l, l < nl →
      Eδ (l + 1) ≤ (q + (8 * Max.max Cf Ck * α l + 16 * C3m * t * (Lr ^ (nl - l))⁻¹)) * Eδ l ∧
      ER (l + 1) ≤ (q + 8 * Max.max Cf Ck * α l) * ER l + 16 * C3m * t * (Lr ^ (nl - l))⁻¹ * Eδ l := by
    intro l hl
    have hn2 : 4 * h + 2 ≤ nn l := by have := hn l; omega
    have hαl : α l = a₀ l + a₁ l := by simp only [hα, if_pos hl]
    obtain ⟨ha0, ha1, -⟩ := ha l hl
    set ql := (Lr ^ (nl - l))⁻¹
    have hql : ql ≤ 1 := hp1 _
    -- the derivative of the remainder at one bond
    have hY : ∀ x ρ, RB h nl μ (l + 1) x ρ →
        ‖fderiv ℂ (fun B' => Crem (V l) B' (img h (base l) l x) ρ h) (B l) (δ l)‖ ≤
          2 * C3m * t * ql * ‖restrictF (δ l) (InBoxB (img h (base l) l x) h ρ)‖ := by
      intro x ρ ⟨hx, q0, q1⟩
      set y := img h (base l) l x
      have hbx : ∀ ν z, (Bm y h z ∨ Bp y h ρ z) → (Bm y h (z + unit (nn l) ν) ∨ Bp y h ρ (z + unit (nn l) ν)) →
          V l ν z = moveC (U l) (A' l) ν z := fun ν z h1 h2 => by
        obtain ⟨x', hx', r0, r1, rfl⟩ := box_site (hn l) (base l) hx q0 q1 ⟨h1, h2⟩
        exact hVU l hl ν x' hx' r0 r1
      have hf := relLog_fun_local (y := y) (μ := ρ) (h := h) hn2 hbx
      have hQ : Qlin (V l) y ρ h = Qlin (moveC (U l) (A' l)) y ρ h := by simp only [Qlin, hf]
      have hCf : (fun B' => Crem (V l) B' y ρ h) = (fun B' => Crem (moveC (U l) (A' l)) B' y ρ h) := by
        funext B'
        simp only [Crem, hQ]
        rw [congrFun hf B']
      obtain ⟨hpl, hA⟩ := hdat l hl ρ x hx q0 q1
      have hRB : ‖restrictF (B l) (InBoxB y h ρ)‖ ≤ 2 * t * ql := by
        refine norm_restrictF_box_le (by positivity) fun ν z hb => ?_
        obtain ⟨x', hx', r0, r1, rfl⟩ := box_site (hn l) (base l) hx q0 q1 hb
        exact hforms l hl.le ν x' hx' r0 r1
      have hae : a₀ l + a₁ l ≤ e := by have := (ha l hl).2.2; nlinarith
      obtain ⟨-, -, hrem⟩ := hbox ρ (U l) (hU l) (hn l) y (a₀ l) (a₁ l) ha0 ha1
        ((by linarith : a₀ l ≤ e).trans ((hec.trans hcb').trans (hcbm ρ)))
        ((by linarith : a₁ l ≤ e).trans ((hec.trans hcb').trans (hcbm ρ))) hpl (A' l) hA (B l)
      have hlt : ‖restrictF (B l) (InBoxB y h ρ)‖ < cb ρ := by
        have : 2 * t * ql ≤ 2 * t := by nlinarith
        linarith [htc.trans_le (hcb'.trans (hcbm ρ))]
      rw [hCf]
      refine ((hrem hlt).2 (δ l)).trans ?_
      have h1 : C3 ρ * ‖restrictF (B l) (InBoxB y h ρ)‖ ≤ C3m * (2 * t * ql) :=
        mul_le_mul (hC3m ρ) hRB (norm_nonneg _) hC3m0
      calc C3 ρ * ‖restrictF (B l) (InBoxB y h ρ)‖ * ‖restrictF (δ l) (InBoxB y h ρ)‖
          ≤ C3m * (2 * t * ql) * ‖restrictF (δ l) (InBoxB y h ρ)‖ :=
            mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
        _ = 2 * C3m * t * ql * ‖restrictF (δ l) (InBoxB y h ρ)‖ := by ring
    have hrestr := ell1_restrict_le (nl := nl) (μ := μ) (l := l) (hn l) (base l) (δ l)
    have hk1 := hks' l hl (δ l)
    have hk2 := hks' l hl (δ l - D l)
    have hc0 : 0 ≤ 2 * C3m * t * ql := by positivity
    rw [← hαl] at hk1 hk2
    constructor
    · -- `δ`
      have hpt : ∀ x ρ, RB h nl μ (l + 1) x ρ → ‖δ (l + 1) ρ (img h (base (l + 1)) (l + 1) x)‖ ≤
          ‖((2 * h + 1 : ℕ) : ℂ) • Qlin (V l) (img h (base l) l x) ρ h (δ l)‖ +
            2 * C3m * t * ql * ‖restrictF (δ l) (InBoxB (img h (base l) l x) h ρ)‖ := fun x ρ hb => by
        obtain ⟨hx, q0, q1⟩ := hb
        rw [(hrel l hl ρ x hx q0 q1).2.1]
        exact (norm_add_le _ _).trans (add_le_add le_rfl (hY x ρ ⟨hx, q0, q1⟩))
      calc Eδ (l + 1) ≤ ell1 h nl μ (l + 1) (fun x ρ =>
              ‖((2 * h + 1 : ℕ) : ℂ) • Qlin (V l) (img h (base l) l x) ρ h (δ l)‖ +
                2 * C3m * t * ql * ‖restrictF (δ l) (InBoxB (img h (base l) l x) h ρ)‖) := ell1_mono hpt
        _ = _ + 2 * C3m * t * ql * _ := by rw [ell1_add, ell1_smul]
        _ ≤ (q + 8 * Ck * α l) * Eδ l + 2 * C3m * t * ql * (8 * Eδ l) :=
            add_le_add hk1 (mul_le_mul_of_nonneg_left hrestr hc0)
        _ ≤ (q + (8 * Max.max Cf Ck * α l + 16 * C3m * t * ql)) * Eδ l := by
            have : 8 * Ck * α l ≤ 8 * Max.max Cf Ck * α l :=
              mul_le_mul_of_nonneg_right (by linarith [le_max_right Cf Ck]) (hα0 l)
            nlinarith [hEδ0 l]
    · -- `δ - D`
      have hpt : ∀ x ρ, RB h nl μ (l + 1) x ρ →
          ‖δ (l + 1) ρ (img h (base (l + 1)) (l + 1) x) - D (l + 1) ρ (img h (base (l + 1)) (l + 1) x)‖ ≤
          ‖((2 * h + 1 : ℕ) : ℂ) • Qlin (V l) (img h (base l) l x) ρ h (δ l - D l)‖ +
            2 * C3m * t * ql * ‖restrictF (δ l) (InBoxB (img h (base l) l x) h ρ)‖ := fun x ρ hb => by
        obtain ⟨hx, q0, q1⟩ := hb
        rw [(hrel l hl ρ x hx q0 q1).2.1, (hrel l hl ρ x hx q0 q1).2.2, map_sub, smul_sub]
        have e : ((2 * h + 1 : ℕ) : ℂ) • Qlin (V l) (img h (base l) l x) ρ h (δ l) +
            fderiv ℂ (fun B' => Crem (V l) B' (img h (base l) l x) ρ h) (B l) (δ l) -
            ((2 * h + 1 : ℕ) : ℂ) • Qlin (V l) (img h (base l) l x) ρ h (D l) =
            (((2 * h + 1 : ℕ) : ℂ) • Qlin (V l) (img h (base l) l x) ρ h (δ l) -
              ((2 * h + 1 : ℕ) : ℂ) • Qlin (V l) (img h (base l) l x) ρ h (D l)) +
            fderiv ℂ (fun B' => Crem (V l) B' (img h (base l) l x) ρ h) (B l) (δ l) := by abel
        rw [e]
        exact (norm_add_le _ _).trans (add_le_add le_rfl (hY x ρ ⟨hx, q0, q1⟩))
      have hRl : ell1 h nl μ l (fun x ν => ‖(δ l - D l) ν (img h (base l) l x)‖) = ER l := rfl
      calc ER (l + 1) ≤ ell1 h nl μ (l + 1) (fun x ρ =>
              ‖((2 * h + 1 : ℕ) : ℂ) • Qlin (V l) (img h (base l) l x) ρ h (δ l - D l)‖ +
                2 * C3m * t * ql * ‖restrictF (δ l) (InBoxB (img h (base l) l x) h ρ)‖) := ell1_mono hpt
        _ = _ + 2 * C3m * t * ql * _ := by rw [ell1_add, ell1_smul]
        _ ≤ (q + 8 * Ck * α l) * ER l + 2 * C3m * t * ql * (8 * Eδ l) :=
            add_le_add (hRl ▸ hk2) (mul_le_mul_of_nonneg_left hrestr hc0)
        _ ≤ (q + 8 * Max.max Cf Ck * α l) * ER l + 16 * C3m * t * ql * Eδ l := by
            have : 8 * Ck * α l ≤ 8 * Max.max Cf Ck * α l :=
              mul_le_mul_of_nonneg_right (by linarith [le_max_right Cf Ck]) (hα0 l)
            nlinarith [hER0 l, hEδ0 l]
  -- the growth of `δ`: `Eδ(l) ≤ 2qˡEδ(0)`
  set Cm := Max.max Cf Ck
  set x : ℕ → ℝ := fun l => 8 * Cm * α l + 16 * C3m * t * (if l < nl then (Lr ^ (nl - l))⁻¹ else 0) with hx
  have hx0 : ∀ l, 0 ≤ x l := fun l => by
    have := hα0 l
    have : 0 ≤ (if l < nl then (Lr ^ (nl - l))⁻¹ else 0) := by split_ifs <;> positivity
    have hCm : 0 ≤ Cm := hCf.trans (le_max_left _ _)
    simp only [hx]; positivity
  have hxsum : ∑ l ∈ Finset.range nl, x l ≤ (8 * Cm * e + 16 * C3m * t) / 2 := by
    have hg := geom_partial hL3 nl nl le_rfl
    simp only [Nat.sub_self, pow_zero, _root_.inv_one, mul_one] at hg
    have hCm : 0 ≤ Cm := hCf.trans (le_max_left _ _)
    calc ∑ l ∈ Finset.range nl, x l ≤ ∑ l ∈ Finset.range nl, (8 * Cm * e + 16 * C3m * t) * (Lr ^ (nl - l))⁻¹ :=
          Finset.sum_le_sum fun l hl => by
            have hl' := Finset.mem_range.1 hl
            simp only [hx, hα, if_pos hl']
            have := (ha l hl').2.2
            nlinarith [mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ 8 * Cm)]
      _ = (8 * Cm * e + 16 * C3m * t) * ∑ l ∈ Finset.range nl, (Lr ^ (nl - l))⁻¹ := by rw [Finset.mul_sum]
      _ ≤ (8 * Cm * e + 16 * C3m * t) * (1 / 2) := mul_le_mul_of_nonneg_left hg (by positivity)
      _ = _ := by ring
  have hexp : ∀ l, l ≤ nl → Real.exp ((∑ m ∈ Finset.range l, x m) / q) ≤ 2 := fun l hl => by
    have hs : ∑ m ∈ Finset.range l, x m ≤ ∑ m ∈ Finset.range nl, x m :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hl) fun m _ _ => hx0 m
    have hy0 : 0 ≤ (∑ m ∈ Finset.range l, x m) / q := div_nonneg (Finset.sum_nonneg fun m _ => hx0 m) hq0.le
    have hy1 : (∑ m ∈ Finset.range l, x m) / q ≤ 1 / 2 := by
      rw [hq, div_inv_eq_mul]
      have hL3' : 0 ≤ Lr ^ 3 := by positivity
      calc (∑ m ∈ Finset.range l, x m) * Lr ^ 3 ≤ (8 * Cm * e + 16 * C3m * t) / 2 * Lr ^ 3 :=
            mul_le_mul_of_nonneg_right (hs.trans hxsum) hL3'
        _ = Lr ^ 3 * (8 * Cm * e + 16 * C3m * t) / 2 := by ring
        _ ≤ 1 / 2 := by linarith
    have := GroupMean.exp_small_le hy0 (hy1.trans (by norm_num))
    linarith
  have hδit : ∀ l, l ≤ nl → Eδ l ≤ (∏ m ∈ Finset.range l, (q + 1 * x m)) * Eδ 0 := by
    intro l
    induction l with
    | zero => intro _; simp
    | succ l ih =>
      intro hl
      have hll : l < nl := by omega
      rw [Finset.prod_range_succ]
      have hxl : x l = 8 * Cm * α l + 16 * C3m * t * (Lr ^ (nl - l))⁻¹ := by simp only [hx, if_pos hll]
      calc Eδ (l + 1) ≤ (q + (8 * Cm * α l + 16 * C3m * t * (Lr ^ (nl - l))⁻¹)) * Eδ l := (hstep l hll).1
        _ ≤ (q + 1 * x l) * ((∏ m ∈ Finset.range l, (q + 1 * x m)) * Eδ 0) := by
            rw [one_mul, hxl]
            exact mul_le_mul_of_nonneg_left (ih hll.le) (by have := hx0 l; rw [hxl] at this; positivity)
        _ = _ := by ring
  have hδ2 : ∀ l, l ≤ nl → Eδ l ≤ 2 * q ^ l * Eδ 0 := fun l hl => by
    have hprod := prod_le_exp hq0 zero_le_one x hx0 l
    simp only [one_mul] at hprod
    calc Eδ l ≤ (∏ m ∈ Finset.range l, (q + 1 * x m)) * Eδ 0 := hδit l hl
      _ ≤ (q ^ l * 2) * Eδ 0 := by
          simp only [one_mul]
          exact mul_le_mul_of_nonneg_right (hprod.trans (mul_le_mul_of_nonneg_left (hexp l hl) (by positivity)))
            (hEδ0 0)
      _ = 2 * q ^ l * Eδ 0 := by ring
  -- the remainder: `ER(l) ≤ 64L³C₃tqˡσ_lEδ(0)`
  have hER0' : ER 0 = 0 := by
    refine le_antisymm ?_ (hER0 0)
    calc ER 0 ≤ ell1 h nl μ 0 (fun _ _ => (0 : ℝ)) := ell1_mono fun x ν hb => by
          obtain ⟨hx, q0, q1⟩ := hb
          rw [(h0 ν x hx q0 q1).2, sub_self, norm_zero]
      _ = 0 := by simp [ell1]
  set M := 64 * Lr ^ 3 * C3m * t with hM
  have hMq : M * q = 64 * C3m * t := by rw [hM, hq]; field_simp
  have hRit : ∀ l, l ≤ nl → ER l ≤ M * q ^ l * (∑ m ∈ Finset.range l, (Lr ^ (nl - m))⁻¹) * Eδ 0 := by
    intro l
    induction l with
    | zero => intro _; simp [hER0']
    | succ l ih =>
      intro hl
      have hll : l < nl := by omega
      have hαl : α l = a₀ l + a₁ l := by simp only [hα, if_pos hll]
      set ql := (Lr ^ (nl - l))⁻¹
      set σ := ∑ m ∈ Finset.range l, (Lr ^ (nl - m))⁻¹
      have hσ0 : 0 ≤ σ := Finset.sum_nonneg fun m _ => by positivity
      have hσ12 : σ ≤ 1 / 2 := (geom_partial hL3 nl l hll.le).trans (by have := hp1 (nl - l); nlinarith)
      have hql0 : 0 ≤ ql := by positivity
      have hαe : α l ≤ e * ql := by rw [hαl]; exact (ha l hll).2.2
      have hCm : 0 ≤ Cm := hCf.trans (le_max_left _ _)
      have hM0 : 0 ≤ M := by positivity
      have hEq : 0 ≤ Eδ 0 := hEδ0 0
      rw [Finset.sum_range_succ, pow_succ]
      have h1 := (hstep l hll).2
      have h2 := hδ2 l hll.le
      have h3 := ih hll.le
      -- `(q + 8Cα)Mqˡσ + 16C₃tq_l·2qˡ ≤ Mq^{l+1}(σ + q_l)`
      have hkey : 8 * Cm * α l * (M * σ) ≤ 32 * C3m * t * ql := by
        have hCe' : 8 * Lr ^ 3 * Cm * e ≤ 1 := by
          have := hsm
          have : 0 ≤ Lr ^ 3 * (16 * C3m * t) := by positivity
          nlinarith
        calc 8 * Cm * α l * (M * σ) ≤ 8 * Cm * (e * ql) * (M * (1 / 2)) :=
              mul_le_mul (mul_le_mul_of_nonneg_left hαe (by positivity)) (mul_le_mul_of_nonneg_left hσ12 hM0)
                (mul_nonneg hM0 hσ0) (by positivity)
          _ = (8 * Lr ^ 3 * Cm * e) * (32 * C3m * t * ql) := by rw [hM]; ring
          _ ≤ 1 * (32 * C3m * t * ql) := by
              exact mul_le_mul_of_nonneg_right hCe' (by positivity)
          _ = 32 * C3m * t * ql := one_mul _
      have hqpow : 0 ≤ q ^ l := by positivity
      calc ER (l + 1) ≤ (q + 8 * Cm * α l) * ER l + 16 * C3m * t * ql * Eδ l := h1
        _ ≤ (q + 8 * Cm * α l) * (M * q ^ l * σ * Eδ 0) + 16 * C3m * t * ql * (2 * q ^ l * Eδ 0) := by
            have hq8 : 0 ≤ q + 8 * Cm * α l := by have := hα0 l; positivity
            exact add_le_add (mul_le_mul_of_nonneg_left h3 hq8) (mul_le_mul_of_nonneg_left h2 (by positivity))
        _ = q ^ l * Eδ 0 * (M * q * σ + 8 * Cm * α l * (M * σ) + 32 * C3m * t * ql) := by ring
        _ ≤ q ^ l * Eδ 0 * (M * q * σ + 64 * C3m * t * ql) := by
            have : 0 ≤ q ^ l * Eδ 0 := by positivity
            nlinarith
        _ = M * (q ^ l * q) * (σ + ql) * Eδ 0 := by rw [← hMq]; ring
  have hfin := hRit nl le_rfl
  have hg := geom_partial hL3 nl nl le_rfl
  simp only [Nat.sub_self, pow_zero, _root_.inv_one, mul_one] at hg
  have hEδD : Eδ 0 = ell1 h nl μ 0 (fun x ν => ‖D 0 ν (img h (base 0) 0 x)‖) := by
    refine le_antisymm (ell1_mono fun x ν hb => ?_) (ell1_mono fun x ν hb => ?_)
    · obtain ⟨hx, q0, q1⟩ := hb; rw [(h0 ν x hx q0 q1).2]
    · obtain ⟨hx, q0, q1⟩ := hb; rw [(h0 ν x hx q0 q1).2]
  have hM0 : 0 ≤ M := by positivity
  calc ER nl ≤ M * q ^ nl * (∑ m ∈ Finset.range nl, (Lr ^ (nl - m))⁻¹) * Eδ 0 := hfin
    _ ≤ M * q ^ nl * (1 / 2) * Eδ 0 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hg (by positivity)) (hEδ0 0)
    _ = 32 * Lr ^ 3 * C3m * t * q ^ nl * ell1 h nl μ 0 (fun x ν => ‖D 0 ν (img h (base 0) 0 x)‖) := by
        rw [hM, hEδD]; ring


/-- **`eq:remainder-kernel` at a single bond**: with the hypotheses of `remainder_kernel` and `A₁ = D_0` vanishing on the
bonds of the region other than `b = (x₀, ν₀)`, `‖δ_n(c) - D_n(c)‖ ≤ 32L³C₃tL^{-3n}‖A₁(b)‖` at every bond `c` of the
last level: `‖(𝖢'_n(A)A₁)(c)‖ ≤ 32C₃L³a_j(a_i/a_j)⁴‖A₁(b)‖‖A‖_∞`. -/
theorem remainder_kernel_single {h : ℕ} {nl : ℕ} {μ : Fin 4} {nn : ℕ → ℕ} [∀ l, NeZero (nn l)]
    {base : ∀ l, Site (nn l)} {δ D : ∀ l, Fin 4 → Site (nn l) → Mat} {x₀ : Fin 4 → ℤ} {ν₀ : Fin 4} {K : ℝ}
    (hK : ell1 h nl μ nl (fun x ν => ‖δ nl ν (img h (base nl) nl x) - D nl ν (img h (base nl) nl x)‖) ≤
      K * ell1 h nl μ 0 (fun x ν => ‖D 0 ν (img h (base 0) 0 x)‖))
    (hb0 : RB h nl μ 0 x₀ ν₀) (hsupp : ∀ x ν, RB h nl μ 0 x ν → (x, ν) ≠ (x₀, ν₀) → D 0 ν (img h (base 0) 0 x) = 0)
    {x : Fin 4 → ℤ} {ρ : Fin 4} (hb : RB h nl μ nl x ρ) :
    ‖δ nl ρ (img h (base nl) nl x) - D nl ρ (img h (base nl) nl x)‖ ≤ K * ‖D 0 ν₀ (img h (base 0) 0 x₀)‖ := by
  have he1 : ell1 h nl μ 0 (fun x ν => ‖D 0 ν (img h (base 0) 0 x)‖) = ‖D 0 ν₀ (img h (base 0) 0 x₀)‖ :=
    ell1_single (f := fun x ν => ‖D 0 ν (img h (base 0) 0 x)‖) hb0 fun x ν hb hne => by
      show ‖D 0 ν (img h (base 0) 0 x)‖ = 0
      rw [hsupp x ν hb hne, norm_zero]
  have hle : ‖δ nl ρ (img h (base nl) nl x) - D nl ρ (img h (base nl) nl x)‖ ≤
      ell1 h nl μ nl (fun x ν => ‖δ nl ν (img h (base nl) nl x) - D nl ν (img h (base nl) nl x)‖) :=
    le_ell1 (f := fun x ν => ‖δ nl ν (img h (base nl) nl x) - D nl ν (img h (base nl) nl x)‖)
      (fun x ν => norm_nonneg _) hb
  rw [he1] at hK
  exact hle.trans hK


set_option maxHeartbeats 4000000 in
/-- **`prop:relative-average-order`(iii), the derivative of the remainder**: under the hypotheses of `order_forms`, the
derivatives `δ_{l+1} = LQ(V_l)δ_l + C'(V_l; B_l)δ_l` of the forms in a direction `δ_0` with `‖δ_0‖ ≤ s₀`, and the linear
parts `D_{l+1} = LQ(V_l)D_l`, `D_0 = δ_0`, satisfy `‖δ_n - D_n‖ ≤ 4C₃tL^{n-1}s₀` at the last level: the derivative of
`C_n(𝐔; a_jA)` in the direction `δA` is at most `(4C₃/L)‖a_jA‖_∞‖a_j δA‖_∞`. -/
theorem order_iii_deriv (h : ℕ) (hh : 1 ≤ h) :
    ∃ c C C₃ : ℝ, 0 < c ∧ 0 ≤ C ∧ 0 ≤ C₃ ∧ ∀ (nl : ℕ) (μ : Fin 4) (nn : ℕ → ℕ) [∀ l, NeZero (nn l)],
      (∀ l, 4 * h + 4 ≤ nn l) → ∀ (base : ∀ l, Site (nn l)) (U V : ∀ l, Config N (nn l))
      (A' B δ D : ∀ l, Fin 4 → Site (nn l) → Mat) (a₀ a₁ : ℕ → ℝ) (t e s₀ : ℝ),
      (∀ l, U l |>.IsGaugeField) →
      (∀ l, l < nl → ∀ ν x, Lat (Lz h) l x → Rg h nl μ l x → Rg h nl μ l (x + Lz h ^ l • Pi.single ν 1) →
        V l ν (img h (base l) l x) = moveC (U l) (A' l) ν (img h (base l) l x)) →
      (∀ l, l < nl → ∀ ρ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x →
        Rg h nl μ (l + 1) (x + Lz h ^ (l + 1) • Pi.single ρ 1) →
        (∀ μ' ν' z, PlaqIn (boxR (img h (base l) l x) (loD h) (hiD h ρ ρ)) μ' ν' z →
          hs (((plaq (U l) μ' ν' z : GLN) : Mat) - 1) ≤ a₀ l) ∧
        (∀ ν z, BoxBond (img h (base l) l x) h ρ ν z → ‖A' l ν z‖ ≤ a₁ l)) →
      (∀ l, l < nl → 0 ≤ a₀ l ∧ 0 ≤ a₁ l ∧ a₀ l + a₁ l ≤ e * ((((2 * h + 1 : ℕ) : ℝ)) ^ (nl - l))⁻¹) →
      (∀ l, l < nl → ∀ ρ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x →
        Rg h nl μ (l + 1) (x + Lz h ^ (l + 1) • Pi.single ρ 1) →
        B (l + 1) ρ (img h (base (l + 1)) (l + 1) x) = relLog (V l) (B l) (img h (base l) l x) ρ h ∧
        δ (l + 1) ρ (img h (base (l + 1)) (l + 1) x) =
          ((2 * h + 1 : ℕ) : ℂ) • Qlin (V l) (img h (base l) l x) ρ h (δ l) +
            fderiv ℂ (fun B' => Crem (V l) B' (img h (base l) l x) ρ h) (B l) (δ l) ∧
        D (l + 1) ρ (img h (base (l + 1)) (l + 1) x) =
          ((2 * h + 1 : ℕ) : ℂ) • Qlin (V l) (img h (base l) l x) ρ h (D l)) →
      0 ≤ t → 0 ≤ e → 0 ≤ s₀ → e ≤ c → 2 * t < c → C * (e + 2 * t) ≤ 1 → C * e + 2 * C₃ * t ≤ 1 →
      (∀ ν x, Lat (Lz h) 0 x → Rg h nl μ 0 x → Rg h nl μ 0 (x + Lz h ^ 0 • Pi.single ν 1) →
        ‖B 0 ν (img h (base 0) 0 x)‖ ≤ t * ((((2 * h + 1 : ℕ) : ℝ)) ^ nl)⁻¹ ∧
        δ 0 ν (img h (base 0) 0 x) = D 0 ν (img h (base 0) 0 x) ∧ ‖δ 0 ν (img h (base 0) 0 x)‖ ≤ s₀) →
      ∀ ν x, Lat (Lz h) nl x → Rg h nl μ nl x → Rg h nl μ nl (x + Lz h ^ nl • Pi.single ν 1) →
        ‖δ nl ν (img h (base nl) nl x) - D nl ν (img h (base nl) nl x)‖ ≤
          4 * C₃ * t * ((((2 * h + 1 : ℕ) : ℝ)) ^ nl / ((2 * h + 1 : ℕ) : ℝ)) * s₀ := by
  classical
  obtain ⟨cf, Cf, hcf, hCf, hof⟩ := order_forms (N := N) h hh
  choose cl Cl hcl hCl hlin using fun ρ : Fin 4 => linear_bound (N := N) h ρ
  choose cb C0 C1 C2 C3 hcb hC0 hC1 hC2 hC3 hbox using fun ρ : Fin 4 => relative_average_box (N := N) h ρ
  set clm := Finset.univ.inf' Finset.univ_nonempty cl
  set cbm := Finset.univ.inf' Finset.univ_nonempty cb
  set Clm := Finset.univ.sup' Finset.univ_nonempty Cl
  set C3m := Finset.univ.sup' Finset.univ_nonempty C3
  have hclm : ∀ ρ, clm ≤ cl ρ := fun ρ => Finset.inf'_le _ (Finset.mem_univ ρ)
  have hcbm : ∀ ρ, cbm ≤ cb ρ := fun ρ => Finset.inf'_le _ (Finset.mem_univ ρ)
  have hClm : ∀ ρ, Cl ρ ≤ Clm := fun ρ => Finset.le_sup' _ (Finset.mem_univ ρ)
  have hC3m : ∀ ρ, C3 ρ ≤ C3m := fun ρ => Finset.le_sup' _ (Finset.mem_univ ρ)
  have hclm0 : 0 < clm := (Finset.lt_inf'_iff _).2 fun ρ _ => hcl ρ
  have hcbm0 : 0 < cbm := (Finset.lt_inf'_iff _).2 fun ρ _ => hcb ρ
  have hClm0 : 0 ≤ Clm := (hCl 0).trans (hClm 0)
  have hC3m0 : 0 ≤ C3m := (hC3 0).trans (hC3m 0)
  refine ⟨min cf (min clm cbm), max Cf Clm, C3m, lt_min hcf (lt_min hclm0 hcbm0), hCf.trans (le_max_left _ _),
    hC3m0, ?_⟩
  intro nl μ nn _ hn base U V A' B δ D a₀ a₁ t e s₀ hU hVU hdat ha hrel ht he hs₀ hec htc hCE hCE2 h0
  have hcf' : min cf (min clm cbm) ≤ cf := min_le_left _ _
  have hcl' : min cf (min clm cbm) ≤ clm := (min_le_right _ _).trans (min_le_left _ _)
  have hcb' : min cf (min clm cbm) ≤ cbm := (min_le_right _ _).trans (min_le_right _ _)
  set Lr : ℝ := ((2 * h + 1 : ℕ) : ℝ) with hLr
  have hL3 : 3 ≤ Lr := by rw [hLr]; push_cast; have : (1 : ℝ) ≤ h := by exact_mod_cast hh
                          linarith
  have hL0 : 0 < Lr := by linarith
  have hp1 : ∀ m, (Lr ^ m)⁻¹ ≤ 1 := fun m => inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith))
  set Cm := max Cf Clm
  have hCm0 : 0 ≤ Cm := hCf.trans (le_max_left _ _)
  have hCEf : Cf * (e + 2 * t) ≤ 1 :=
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)).trans hCE
  have hforms := hof nl μ nn hn base U V A' B a₀ a₁ t e hU hVU hdat (fun l hl ρ x hx q0 q1 =>
    (hrel l hl ρ x hx q0 q1).1) ha ht he (hec.trans hcf') (htc.trans_le hcf') hCEf (fun ν x hx q0 q1 =>
    (h0 ν x hx q0 q1).1)
  -- the bounds of one step at a bond of the level `l + 1`, in the box norms
  have hone : ∀ l, l < nl → ∀ ρ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x →
      Rg h nl μ (l + 1) (x + Lz h ^ (l + 1) • Pi.single ρ 1) → ∀ X : Fin 4 → Site (nn l) → Mat,
      ‖((2 * h + 1 : ℕ) : ℂ) • Qlin (V l) (img h (base l) l x) ρ h X‖ ≤
        (Lr + Cm * (a₀ l + a₁ l)) * ‖restrictF X (InBoxB (img h (base l) l x) h ρ)‖ ∧
      ‖fderiv ℂ (fun B' => Crem (V l) B' (img h (base l) l x) ρ h) (B l) X‖ ≤
        2 * C3m * t * (Lr ^ (nl - l))⁻¹ * ‖restrictF X (InBoxB (img h (base l) l x) h ρ)‖ := by
    intro l hl ρ x hx q0 q1 X
    have hn2 : 4 * h + 2 ≤ nn l := by have := hn l; omega
    obtain ⟨ha0, ha1, ha2⟩ := ha l hl
    have hae : a₀ l + a₁ l ≤ e := by have := hp1 (nl - l); nlinarith
    set y := img h (base l) l x
    have hbx : ∀ ν z, (Bm y h z ∨ Bp y h ρ z) → (Bm y h (z + unit (nn l) ν) ∨ Bp y h ρ (z + unit (nn l) ν)) →
        V l ν z = moveC (U l) (A' l) ν z := fun ν z h1 h2 => by
      obtain ⟨x', hx', r0, r1, rfl⟩ := box_site (hn l) (base l) hx q0 q1 ⟨h1, h2⟩
      exact hVU l hl ν x' hx' r0 r1
    have hf := relLog_fun_local (y := y) (μ := ρ) (h := h) hn2 hbx
    have hQ : Qlin (V l) y ρ h = Qlin (moveC (U l) (A' l)) y ρ h := by simp only [Qlin, hf]
    have hCf : (fun B' => Crem (V l) B' y ρ h) = (fun B' => Crem (moveC (U l) (A' l)) B' y ρ h) := by
      funext B'
      simp only [Crem, hQ]
      rw [congrFun hf B']
    obtain ⟨hpl, hA⟩ := hdat l hl ρ x hx q0 q1
    constructor
    · rw [hQ]
      refine (hlin ρ (U l) (hU l) (hn l) y (a₀ l) (a₁ l) ha0 ha1
        ((by linarith : a₀ l ≤ e).trans ((hec.trans hcl').trans (hclm ρ)))
        ((by linarith : a₁ l ≤ e).trans ((hec.trans hcl').trans (hclm ρ))) hpl (A' l) hA X).trans ?_
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      have : Cl ρ * (a₀ l + a₁ l) ≤ Cm * (a₀ l + a₁ l) :=
        mul_le_mul_of_nonneg_right ((hClm ρ).trans (le_max_right _ _)) (by positivity)
      linarith
    · have hRB : ‖restrictF (B l) (InBoxB y h ρ)‖ ≤ 2 * t * (Lr ^ (nl - l))⁻¹ := by
        refine norm_restrictF_box_le (by have := hp1 (nl - l); positivity) fun ν z hb => ?_
        obtain ⟨x', hx', r0, r1, rfl⟩ := box_site (hn l) (base l) hx q0 q1 hb
        exact hforms l hl.le ν x' hx' r0 r1
      obtain ⟨-, -, hrem⟩ := hbox ρ (U l) (hU l) (hn l) y (a₀ l) (a₁ l) ha0 ha1
        ((by linarith : a₀ l ≤ e).trans ((hec.trans hcb').trans (hcbm ρ)))
        ((by linarith : a₁ l ≤ e).trans ((hec.trans hcb').trans (hcbm ρ))) hpl (A' l) hA (B l)
      have hlt : ‖restrictF (B l) (InBoxB y h ρ)‖ < cb ρ := by
        have : 2 * t * (Lr ^ (nl - l))⁻¹ ≤ 2 * t := by have := hp1 (nl - l); nlinarith
        linarith [htc.trans_le (hcb'.trans (hcbm ρ))]
      rw [hCf]
      refine ((hrem hlt).2 X).trans ?_
      have h1 : C3 ρ * ‖restrictF (B l) (InBoxB y h ρ)‖ ≤ C3m * (2 * t * (Lr ^ (nl - l))⁻¹) :=
        mul_le_mul (hC3m ρ) hRB (norm_nonneg _) hC3m0
      calc C3 ρ * ‖restrictF (B l) (InBoxB y h ρ)‖ * ‖restrictF X (InBoxB y h ρ)‖
          ≤ C3m * (2 * t * (Lr ^ (nl - l))⁻¹) * ‖restrictF X (InBoxB y h ρ)‖ :=
            mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
        _ = _ := by ring
  -- the growth of the derivatives: `‖δ_l‖ ≤ S_l`
  set yv : ℕ → ℝ := fun l => if l < nl then Cm * (a₀ l + a₁ l) + 2 * C3m * t * (Lr ^ (nl - l))⁻¹ else 0 with hyv
  have hyv0 : ∀ l, 0 ≤ yv l := fun l => by
    simp only [hyv]; split_ifs with hl
    · obtain ⟨h1, h2, -⟩ := ha l hl; positivity
    · exact le_rfl
  set S : ℕ → ℝ := fun l => s₀ * ∏ m ∈ Finset.range l, (Lr + yv m) with hS
  have hS0 : ∀ l, 0 ≤ S l := fun l => mul_nonneg hs₀ (Finset.prod_nonneg fun m _ => by have := hyv0 m; positivity)
  have hδS : ∀ l, l ≤ nl → ∀ ν x, Lat (Lz h) l x → Rg h nl μ l x → Rg h nl μ l (x + Lz h ^ l • Pi.single ν 1) →
      ‖δ l ν (img h (base l) l x)‖ ≤ S l := by
    intro l
    induction l with
    | zero => intro _ ν x hx q0 q1; simpa [hS] using (h0 ν x hx q0 q1).2.2
    | succ l ih =>
      intro hl ρ x hx q0 q1
      have hll : l < nl := by omega
      have hR : ‖restrictF (δ l) (InBoxB (img h (base l) l x) h ρ)‖ ≤ S l := by
        refine norm_restrictF_box_le (hS0 l) fun ν z hb => ?_
        obtain ⟨x', hx', r0, r1, rfl⟩ := box_site (hn l) (base l) hx q0 q1 hb
        exact ih hll.le ν x' hx' r0 r1
      obtain ⟨h1, h2⟩ := hone l hll ρ x hx q0 q1 (δ l)
      rw [(hrel l hll ρ x hx q0 q1).2.1]
      have hyl : yv l = Cm * (a₀ l + a₁ l) + 2 * C3m * t * (Lr ^ (nl - l))⁻¹ := by simp only [hyv, if_pos hll]
      have hSl : S (l + 1) = (Lr + yv l) * S l := by simp only [hS, Finset.prod_range_succ]; ring
      rw [hSl, hyl]
      obtain ⟨ha0, ha1, -⟩ := ha l hll
      have hc2 : 0 ≤ 2 * C3m * t * (Lr ^ (nl - l))⁻¹ := by positivity
      calc ‖((2 * h + 1 : ℕ) : ℂ) • Qlin (V l) (img h (base l) l x) ρ h (δ l) +
            fderiv ℂ (fun B' => Crem (V l) B' (img h (base l) l x) ρ h) (B l) (δ l)‖
          ≤ (Lr + Cm * (a₀ l + a₁ l)) * S l + 2 * C3m * t * (Lr ^ (nl - l))⁻¹ * S l :=
            (norm_add_le _ _).trans (add_le_add (h1.trans (mul_le_mul_of_nonneg_left hR (by positivity)))
              (h2.trans (mul_le_mul_of_nonneg_left hR hc2)))
        _ = _ := by ring
  have hsum : ∑ l ∈ Finset.range nl, yv l ≤ (Cm * e + 2 * C3m * t) / 2 := by
    have hg := geom_partial hL3 nl nl le_rfl
    simp only [Nat.sub_self, pow_zero, _root_.inv_one, mul_one] at hg
    calc ∑ l ∈ Finset.range nl, yv l ≤ ∑ l ∈ Finset.range nl, (Cm * e + 2 * C3m * t) * (Lr ^ (nl - l))⁻¹ :=
          Finset.sum_le_sum fun l hl => by
            have hl' := Finset.mem_range.1 hl
            simp only [hyv, if_pos hl']
            have := (ha l hl').2.2
            nlinarith [mul_le_mul_of_nonneg_left this hCm0]
      _ = (Cm * e + 2 * C3m * t) * ∑ l ∈ Finset.range nl, (Lr ^ (nl - l))⁻¹ := by rw [Finset.mul_sum]
      _ ≤ (Cm * e + 2 * C3m * t) * (1 / 2) := mul_le_mul_of_nonneg_left hg (by positivity)
      _ = _ := by ring
  have hCE2' : Cm * e + 2 * C3m * t ≤ 1 := hCE2
  have hS2 : ∀ l, l ≤ nl → S l ≤ 2 * Lr ^ l * s₀ := fun l hl => by
    have hprod := prod_le_exp hL0 zero_le_one yv hyv0 l
    simp only [one_mul] at hprod
    have hs : ∑ m ∈ Finset.range l, yv m ≤ ∑ m ∈ Finset.range nl, yv m :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hl) fun m _ _ => hyv0 m
    have hy0 : 0 ≤ (∑ m ∈ Finset.range l, yv m) / Lr := div_nonneg (Finset.sum_nonneg fun m _ => hyv0 m) hL0.le
    have hy1 : (∑ m ∈ Finset.range l, yv m) / Lr ≤ 1 / 2 := by
      rw [div_le_iff₀ hL0]; nlinarith
    have hexp := GroupMean.exp_small_le hy0 (hy1.trans (by norm_num))
    calc S l = s₀ * ∏ m ∈ Finset.range l, (Lr + yv m) := rfl
      _ ≤ s₀ * (Lr ^ l * 2) := mul_le_mul_of_nonneg_left
          (hprod.trans (mul_le_mul_of_nonneg_left (by linarith) (by positivity))) hs₀
      _ = 2 * Lr ^ l * s₀ := by ring
  -- the remainder: `‖δ_l - D_l‖ ≤ (8C₃t/L)Lˡσ_ls₀`
  set M := 8 * C3m * t / Lr with hM
  have hM0 : 0 ≤ M := by positivity
  have hMr : ∀ l, l ≤ nl → ∀ ν x, Lat (Lz h) l x → Rg h nl μ l x → Rg h nl μ l (x + Lz h ^ l • Pi.single ν 1) →
      ‖δ l ν (img h (base l) l x) - D l ν (img h (base l) l x)‖ ≤
        M * Lr ^ l * (∑ m ∈ Finset.range l, (Lr ^ (nl - m))⁻¹) * s₀ := by
    intro l
    induction l with
    | zero => intro _ ν x hx q0 q1; rw [(h0 ν x hx q0 q1).2.1, sub_self, norm_zero]; simp
    | succ l ih =>
      intro hl ρ x hx q0 q1
      have hll : l < nl := by omega
      set ql := (Lr ^ (nl - l))⁻¹
      set σ := ∑ m ∈ Finset.range l, (Lr ^ (nl - m))⁻¹
      have hσ0 : 0 ≤ σ := Finset.sum_nonneg fun m _ => by positivity
      have hσ12 : σ ≤ 1 / 2 := (geom_partial hL3 nl l hll.le).trans (by have := hp1 (nl - l); nlinarith)
      have hql0 : 0 ≤ ql := by positivity
      obtain ⟨ha0, ha1, ha2⟩ := ha l hll
      have hRr : ‖restrictF (δ l - D l) (InBoxB (img h (base l) l x) h ρ)‖ ≤ M * Lr ^ l * σ * s₀ := by
        refine norm_restrictF_box_le (by positivity) fun ν z hb => ?_
        obtain ⟨x', hx', r0, r1, rfl⟩ := box_site (hn l) (base l) hx q0 q1 hb
        simpa only [Pi.sub_apply] using ih hll.le ν x' hx' r0 r1
      have hRδ : ‖restrictF (δ l) (InBoxB (img h (base l) l x) h ρ)‖ ≤ 2 * Lr ^ l * s₀ := by
        refine norm_restrictF_box_le (by positivity) fun ν z hb => ?_
        obtain ⟨x', hx', r0, r1, rfl⟩ := box_site (hn l) (base l) hx q0 q1 hb
        exact (hδS l hll.le ν x' hx' r0 r1).trans (hS2 l hll.le)
      obtain ⟨h1, -⟩ := hone l hll ρ x hx q0 q1 (δ l - D l)
      obtain ⟨-, h2⟩ := hone l hll ρ x hx q0 q1 (δ l)
      rw [(hrel l hll ρ x hx q0 q1).2.1, (hrel l hll ρ x hx q0 q1).2.2]
      have heqn : ((2 * h + 1 : ℕ) : ℂ) • Qlin (V l) (img h (base l) l x) ρ h (δ l) +
          fderiv ℂ (fun B' => Crem (V l) B' (img h (base l) l x) ρ h) (B l) (δ l) -
          ((2 * h + 1 : ℕ) : ℂ) • Qlin (V l) (img h (base l) l x) ρ h (D l) =
          ((2 * h + 1 : ℕ) : ℂ) • Qlin (V l) (img h (base l) l x) ρ h (δ l - D l) +
          fderiv ℂ (fun B' => Crem (V l) B' (img h (base l) l x) ρ h) (B l) (δ l) := by
        rw [map_sub, smul_sub]; abel
      rw [heqn, Finset.sum_range_succ, pow_succ]
      have hae : a₀ l + a₁ l ≤ e * ql := ha2
      have hkey : Cm * (a₀ l + a₁ l) * (M * σ) ≤ 4 * C3m * t * ql := by
        have hCe : Cm * e ≤ 1 := by nlinarith [mul_nonneg hC3m0 ht]
        calc Cm * (a₀ l + a₁ l) * (M * σ) ≤ Cm * (e * ql) * (M * (1 / 2)) :=
              mul_le_mul (mul_le_mul_of_nonneg_left hae hCm0) (mul_le_mul_of_nonneg_left hσ12 hM0)
                (mul_nonneg hM0 hσ0) (by positivity)
          _ = (Cm * e) * (4 * C3m * t * ql) / Lr := by rw [hM]; field_simp; ring
          _ ≤ 1 * (4 * C3m * t * ql) / Lr :=
              div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hCe (by positivity)) hL0.le
          _ ≤ 4 * C3m * t * ql := by
              rw [one_mul, div_le_iff₀ hL0]
              nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hC3m0 ht) hql0) (show (0 : ℝ) ≤ 4 by norm_num)]
      have hMLr : M * Lr = 8 * C3m * t := by rw [hM]; field_simp
      have hLl : 0 ≤ Lr ^ l := by positivity
      calc ‖((2 * h + 1 : ℕ) : ℂ) • Qlin (V l) (img h (base l) l x) ρ h (δ l - D l) +
            fderiv ℂ (fun B' => Crem (V l) B' (img h (base l) l x) ρ h) (B l) (δ l)‖
          ≤ (Lr + Cm * (a₀ l + a₁ l)) * (M * Lr ^ l * σ * s₀) + 2 * C3m * t * ql * (2 * Lr ^ l * s₀) :=
            (norm_add_le _ _).trans (add_le_add (h1.trans (mul_le_mul_of_nonneg_left hRr (by positivity)))
              (h2.trans (mul_le_mul_of_nonneg_left hRδ (by positivity))))
        _ = Lr ^ l * s₀ * (M * Lr * σ + Cm * (a₀ l + a₁ l) * (M * σ) + 4 * C3m * t * ql) := by ring
        _ ≤ Lr ^ l * s₀ * (M * Lr * σ + 8 * C3m * t * ql) := by
            have : 0 ≤ Lr ^ l * s₀ := by positivity
            nlinarith
        _ = M * (Lr ^ l * Lr) * (σ + ql) * s₀ := by rw [← hMLr]; ring
  intro ν x hx q0 q1
  refine (hMr nl le_rfl ν x hx q0 q1).trans ?_
  have hg := geom_partial hL3 nl nl le_rfl
  simp only [Nat.sub_self, pow_zero, _root_.inv_one, mul_one] at hg
  calc M * Lr ^ nl * (∑ m ∈ Finset.range nl, (Lr ^ (nl - m))⁻¹) * s₀ ≤ M * Lr ^ nl * (1 / 2) * s₀ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hg (by positivity)) hs₀
    _ = 4 * C3m * t * (Lr ^ nl / Lr) * s₀ := by rw [hM]; field_simp; ring


/-! ### The derivatives of the forms of the levels -/

/-- **`B ↦ (1/i) log 𝓜_𝐔(B)(c)` is holomorphic near small `B`** for the core's `𝐔`: near `B₀` with
`‖B₀‖_{∞,box} < c` it equals `B ↦ (1/i) log 𝓜_{𝐔_X}(Ad_u B|_{box})(c)` in the axial gauge. -/
theorem relLog_core_differentiableAt (h : ℕ) (μ : Fin 4) :
    ∃ c : ℝ, 0 < c ∧
      ∀ {n : ℕ} [NeZero n] (U : Config N n), U.IsGaugeField → 4 * h + 4 ≤ n → ∀ (y : Site n)
        [DecidablePred (InBoxB y h μ)] (α₀ α₁ : ℝ), 0 ≤ α₀ → 0 ≤ α₁ → α₀ ≤ c → α₁ ≤ c →
        (∀ μ' ν' z, PlaqIn (boxR y (loD h) (hiD h μ μ)) μ' ν' z →
          hs (((plaq U μ' ν' z : GLN) : Mat) - 1) ≤ α₀) →
        ∀ A' : Fin 4 → Site n → Mat, (∀ ρ z, BoxBond y h μ ρ z → ‖A' ρ z‖ ≤ α₁) →
        ∀ B₀ : Fin 4 → Site n → Mat, ‖restrictF B₀ (InBoxB y h μ)‖ < c →
          DifferentiableAt ℂ (fun B => relLog (moveC U A') B y μ h) B₀ := by
  obtain ⟨ci, hci, hpol⟩ := uniform_polydisc (N := N) h μ
  set K := redK N h
  have hK4 : 4 ≤ K := four_le_redK N h
  have hKpos : 0 < K := by linarith
  set c := min (min (ci / (2 * K)) (1 / (8 * K))) ci with hc_def
  have hc1 : c ≤ ci / (2 * K) := (min_le_left _ _).trans (min_le_left _ _)
  have hc2 : c ≤ 1 / (8 * K) := (min_le_left _ _).trans (min_le_right _ _)
  have hc3 : c ≤ ci := min_le_right _ _
  refine ⟨c, lt_min (lt_min (by positivity) (by positivity)) hci, ?_⟩
  intro n _ U hU hn y _ α₀ α₁ hα₀ hα₁ hα₀c hα₁c hplq A' hA B₀ hB₀
  have hn2 : 4 * h + 2 ≤ n := by omega
  obtain ⟨X, hXc, -, hag, -, -⟩ := reduce_box_supp hU hn y μ hα₀ hα₁ hα₀c hα₁c hc2 hplq A' hA
  have hKc : K * c ≤ ci / 2 := by
    calc K * c ≤ K * (ci / (2 * K)) := mul_le_mul_of_nonneg_left hc1 hKpos.le
      _ = ci / 2 := by field_simp
  have hXci : ‖X‖ < ci := by linarith
  set u := uG U y h
  have hu : ∀ z, ((u z : GLN) : Mat) ∈ unitaryGroup (Fin N) ℂ := fun z => hol_unitary' U hU _
  set P := restrictBoxL (N := N) y h μ
  set g : (Fin 4 → Site n → Mat) → Mat := fun B => relLog (UX (N := N) X) (AdFL u (P B)) y μ h with hg
  have hPB : ∀ B, P B = restrictF B (InBoxB y h μ) := fun B => rfl
  have hAdF : ∀ B, AdFL u B = AdF u B := fun B => rfl
  -- `g` is differentiable at `B₀`
  have hcond0 : Cond (N := N) y μ h (X, AdFL u (P B₀)) :=
    hpol y X _ hXci (by rw [hAdF, hPB, norm_AdF_unitary hu]; linarith)
  have hgd : DifferentiableAt ℂ g B₀ := by
    have hd := relLog_pair_differentiableAt hcond0
    have hlin : DifferentiableAt ℂ (fun B : Fin 4 → Site n → Mat => ((X, AdFL u (P B)) : PairSp N n)) B₀ :=
      (differentiableAt_const X).prodMk ((AdFL u).comp P).differentiableAt
    exact DifferentiableAt.comp (f := fun B : Fin 4 → Site n → Mat => ((X, AdFL u (P B)) : PairSp N n)) B₀ hd hlin
  -- `relLog 𝐔 = g` near `B₀`
  have hopen : IsOpen {B : Fin 4 → Site n → Mat | ‖P B‖ < ci} :=
    isOpen_lt (continuous_norm.comp P.continuous) continuous_const
  have hev : (fun B => relLog (moveC U A') B y μ h) =ᶠ[𝓝 B₀] g := by
    filter_upwards [hopen.mem_nhds (show ‖P B₀‖ < ci by rw [hPB]; linarith)] with B hB
    rw [relLog_box hn2 (moveC U A') y μ B]
    have hc := hpol y X (AdF u (restrictF B (InBoxB y h μ))) hXci (by rw [norm_AdF_unitary hu, ← hPB]; exact hB)
    rw [relLog_reduce hU hn hag _ hc]
    rfl
  exact (hev.differentiableAt_iff).2 hgd


/-- **The derivatives of the forms of the levels** (the chain rule behind `δ^{(l+1)} = Q^{(l)}δ^{(l)} + Y_l` in the
proof of `lem:remainder-kernel`): for a family `s ↦ B(s)` of forms with `B(s)_{l+1} = (1/i) log 𝓜_{V_l}(B(s)_l)` on the
regions, whose values at level `0` have the derivatives `δ_0` at `s = 0`, the forms `δ_{l+1} = LQ(V_l)δ_l +
C'(V_l; B(0)_l)δ_l` are the derivatives `d/ds B(s)_l` at `s = 0` on the region of every level, as long as the forms
`B(0)_l` are smaller than `c` on the regions. -/
theorem forms_hasDerivAt (h : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ (nl : ℕ) (μ : Fin 4) (nn : ℕ → ℕ) [∀ l, NeZero (nn l)],
      (∀ l, 4 * h + 4 ≤ nn l) → ∀ (base : ∀ l, Site (nn l)) (U V : ∀ l, Config N (nn l))
      (A' δ : ∀ l, Fin 4 → Site (nn l) → Mat) (Bf : ℂ → ∀ l, Fin 4 → Site (nn l) → Mat) (a₀ a₁ s₀ : ℕ → ℝ),
      (∀ l, U l |>.IsGaugeField) →
      (∀ l, l < nl → ∀ ν x, Lat (Lz h) l x → Rg h nl μ l x → Rg h nl μ l (x + Lz h ^ l • Pi.single ν 1) →
        V l ν (img h (base l) l x) = moveC (U l) (A' l) ν (img h (base l) l x) ∧
        ‖Bf 0 l ν (img h (base l) l x)‖ ≤ s₀ l) →
      (∀ l, l < nl → ∀ ρ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x →
        Rg h nl μ (l + 1) (x + Lz h ^ (l + 1) • Pi.single ρ 1) →
        (∀ μ' ν' z, PlaqIn (boxR (img h (base l) l x) (loD h) (hiD h ρ ρ)) μ' ν' z →
          hs (((plaq (U l) μ' ν' z : GLN) : Mat) - 1) ≤ a₀ l) ∧
        (∀ ν z, BoxBond (img h (base l) l x) h ρ ν z → ‖A' l ν z‖ ≤ a₁ l)) →
      (∀ l, l < nl → 0 ≤ a₀ l ∧ 0 ≤ a₁ l ∧ a₀ l ≤ c ∧ a₁ l ≤ c ∧ 0 ≤ s₀ l ∧ s₀ l < c) →
      (∀ l, l < nl → ∀ ρ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x →
        Rg h nl μ (l + 1) (x + Lz h ^ (l + 1) • Pi.single ρ 1) →
        (∀ s, Bf s (l + 1) ρ (img h (base (l + 1)) (l + 1) x) = relLog (V l) (Bf s l) (img h (base l) l x) ρ h) ∧
        δ (l + 1) ρ (img h (base (l + 1)) (l + 1) x) =
          ((2 * h + 1 : ℕ) : ℂ) • Qlin (V l) (img h (base l) l x) ρ h (δ l) +
            fderiv ℂ (fun B' => Crem (V l) B' (img h (base l) l x) ρ h) (Bf 0 l) (δ l)) →
      (∀ ν x, Lat (Lz h) 0 x → Rg h nl μ 0 x → Rg h nl μ 0 (x + Lz h ^ 0 • Pi.single ν 1) →
        HasDerivAt (fun s => Bf s 0 ν (img h (base 0) 0 x)) (δ 0 ν (img h (base 0) 0 x)) 0) →
      ∀ l, l ≤ nl → ∀ ν x, Lat (Lz h) l x → Rg h nl μ l x → Rg h nl μ l (x + Lz h ^ l • Pi.single ν 1) →
        HasDerivAt (fun s => Bf s l ν (img h (base l) l x)) (δ l ν (img h (base l) l x)) 0 := by
  classical
  choose cd hcd hdiff using fun ρ : Fin 4 => relLog_core_differentiableAt (N := N) h ρ
  choose ci hci hpol using fun ρ : Fin 4 => uniform_polydisc (N := N) h ρ
  set c := min (Finset.univ.inf' Finset.univ_nonempty cd)
    (min (Finset.univ.inf' Finset.univ_nonempty fun ρ => ci ρ / (2 * redK N h))
      (1 / (8 * redK N h))) with hc_def
  have hKpos : 0 < redK N h := by linarith [four_le_redK N h]
  have hc0 : 0 < c := lt_min ((Finset.lt_inf'_iff _).2 fun ρ _ => hcd ρ)
    (lt_min ((Finset.lt_inf'_iff _).2 fun ρ _ => by have := hci ρ; positivity) (by positivity))
  have hcd' : ∀ ρ, c ≤ cd ρ := fun ρ => (min_le_left _ _).trans (Finset.inf'_le _ (Finset.mem_univ ρ))
  have hci' : ∀ ρ, c ≤ ci ρ / (2 * redK N h) := fun ρ =>
    ((min_le_right _ _).trans (min_le_left _ _)).trans (Finset.inf'_le (fun ρ => ci ρ / (2 * redK N h))
      (Finset.mem_univ ρ))
  have hc8 : c ≤ 1 / (8 * redK N h) := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨c, hc0, ?_⟩
  intro nl μ nn _ hn base U V A' δ Bf a₀ a₁ s₀ hU hVB hdat ha hrel h0 l
  induction l with
  | zero => intro _; exact h0
  | succ l ih =>
    intro hl ρ x hx q0 q1
    have hll : l < nl := by omega
    have hn2 : 4 * h + 2 ≤ nn l := by have := hn l; omega
    obtain ⟨ha0, ha1, ha0c, ha1c, hs0, hsc⟩ := ha l hll
    obtain ⟨hpl, hA⟩ := hdat l hll ρ x hx q0 q1
    obtain ⟨hBs, hδ⟩ := hrel l hll ρ x hx q0 q1
    set y := img h (base l) l x
    set W := moveC (U l) (A' l)
    have hbx : ∀ ν z, (Bm y h z ∨ Bp y h ρ z) → (Bm y h (z + unit (nn l) ν) ∨ Bp y h ρ (z + unit (nn l) ν)) →
        V l ν z = W ν z := fun ν z h1 h2 => by
      obtain ⟨x', hx', r0, r1, rfl⟩ := box_site (hn l) (base l) hx q0 q1 ⟨h1, h2⟩
      exact (hVB l hll ν x' hx' r0 r1).1
    have hf := relLog_fun_local (y := y) (μ := ρ) (h := h) hn2 hbx
    have hQ : Qlin (V l) y ρ h = Qlin W y ρ h := by simp only [Qlin, hf]
    have hCf : (fun B' => Crem (V l) B' y ρ h) = (fun B' => Crem W B' y ρ h) := by
      funext B'
      simp only [Crem, hQ]
      rw [congrFun hf B']
    set P := restrictBoxL (N := N) y h ρ
    have hPB : ∀ B, P B = restrictF B (InBoxB y h ρ) := fun B => rfl
    -- the restricted family has the restricted derivative
    have hR : HasDerivAt (fun s => P (Bf s l)) (P (δ l)) 0 := by
      refine hasDerivAt_pi.2 fun ν => hasDerivAt_pi.2 fun z => ?_
      simp only [hPB, restrictF]
      split_ifs with hb
      · obtain ⟨x', hx', r0, r1, rfl⟩ := box_site (hn l) (base l) hx q0 q1 hb
        exact ih hll.le ν x' hx' r0 r1
      · exact hasDerivAt_const _ _
    -- the size of `B(0)_l` on the box
    have hRB : ‖P (Bf 0 l)‖ ≤ s₀ l := by
      rw [hPB]
      refine norm_restrictF_box_le hs0 fun ν z hb => ?_
      obtain ⟨x', hx', r0, r1, rfl⟩ := box_site (hn l) (base l) hx q0 q1 hb
      exact (hVB l hll ν x' hx' r0 r1).2
    have hPP : P (P (Bf 0 l)) = P (Bf 0 l) := by simp only [hPB, restrictF_restrictF]
    have hd : DifferentiableAt ℂ (fun B => relLog W B y ρ h) (P (Bf 0 l)) :=
      hdiff ρ (U l) (hU l) (hn l) y (a₀ l) (a₁ l) ha0 ha1 (ha0c.trans (hcd' ρ)) (ha1c.trans (hcd' ρ)) hpl (A' l) hA
        (P (Bf 0 l)) (by rw [← hPB, hPP]; exact hRB.trans_lt (hsc.trans_le (hcd' ρ)))
    -- the chain rule
    have hcomp := hd.hasFDerivAt.comp_hasDerivAt (0 : ℂ) hR
    have hfun : (fun s => Bf s (l + 1) ρ (img h (base (l + 1)) (l + 1) x)) =
        (fun B => relLog W B y ρ h) ∘ (fun s => P (Bf s l)) := by
      funext s
      simp only [Function.comp, hBs s]
      rw [congrFun hf (Bf s l), relLog_box hn2 W y ρ (Bf s l), ← hPB (Bf s l)]
    rw [hfun]
    refine hcomp.congr_deriv ?_
    -- the derivative: `fderiv relLog (P B)(P δ) = LQ(V_l)δ + C'(V_l; B)δ`
    obtain ⟨X, hXc, -, hag, -, -⟩ := reduce_box_supp (hU l) (hn l) y ρ ha0 ha1 ha0c ha1c hc8 hpl (A' l) hA
    have hXci : ‖X‖ < ci ρ := by
      have h1 := hci' ρ
      have h2 : redK N h * c ≤ ci ρ / 2 := by
        calc redK N h * c ≤ redK N h * (ci ρ / (2 * redK N h)) := mul_le_mul_of_nonneg_left h1 hKpos.le
          _ = ci ρ / 2 := by field_simp
      have := hci ρ
      linarith
    have hQr : ∀ B, Qlin W y ρ h B = Qlin W y ρ h (P B) := fun B =>
      Qlin_restrict (hU l) (hn l) hag (hci ρ) (hpol ρ y) hXci B
    have hCrem_eq : (fun B => Crem W B y ρ h) = (fun B => Crem W B y ρ h) ∘ P := by
      funext B
      simp only [Function.comp, Crem]
      rw [relLog_box hn2 W y ρ B, hQr B, ← hPB B]
    have hCd : DifferentiableAt ℂ (fun B => Crem W B y ρ h) (P (Bf 0 l)) := by
      have e : (fun B => Crem W B y ρ h) = fun B => relLog W B y ρ h - (((2 * h + 1 : ℕ) : ℂ) • Qlin W y ρ h) B := by
        funext B; rfl
      rw [e]; exact hd.sub (ContinuousLinearMap.differentiableAt _)
    have hsplit : fderiv ℂ (fun B => relLog W B y ρ h) (P (Bf 0 l)) =
        (((2 * h + 1 : ℕ) : ℂ) • Qlin W y ρ h) + fderiv ℂ (fun B => Crem W B y ρ h) (P (Bf 0 l)) := by
      have e : (fun B => relLog W B y ρ h) = fun B => (((2 * h + 1 : ℕ) : ℂ) • Qlin W y ρ h) B + Crem W B y ρ h := by
        funext B; rw [linear_part]; rfl
      rw [e]
      exact ((((2 * h + 1 : ℕ) : ℂ) • Qlin W y ρ h).hasFDerivAt.add hCd.hasFDerivAt).fderiv
    have hCcomp : fderiv ℂ (fun B => Crem W B y ρ h) (Bf 0 l) =
        (fderiv ℂ (fun B => Crem W B y ρ h) (P (Bf 0 l))).comp P := by
      conv_lhs => rw [hCrem_eq]
      rw [fderiv_comp (Bf 0 l) hCd P.differentiableAt, ContinuousLinearMap.fderiv]
    rw [hδ, hQ, hCf, hsplit, ContinuousLinearMap.add_apply, hCcomp, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.smul_apply, ← hQr (δ l)]


/-- **`prop:relative-average-order`(i), the holomorphy of the forms in `A`**: for a family `a ↦ B(a)` of the forms of
the levels, over any complex normed space of parameters, with `B(a)_{l+1} = (1/i) log 𝓜_{V_l}(B(a)_l)` on the regions
and the values at level `0` complex differentiable at `a₀`, the values of every level are complex differentiable at
`a₀`, as long as the forms `B(a₀)_l` are smaller than `c` on the regions. -/
theorem forms_differentiableAt (h : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ (nl : ℕ) (μ : Fin 4) (nn : ℕ → ℕ) [∀ l, NeZero (nn l)],
      (∀ l, 4 * h + 4 ≤ nn l) → ∀ (base : ∀ l, Site (nn l)) (U V : ∀ l, Config N (nn l))
      (A' : ∀ l, Fin 4 → Site (nn l) → Mat) {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
      (Bf : E → ∀ l, Fin 4 → Site (nn l) → Mat) (a₀ : E) (a₀' a₁' s₀ : ℕ → ℝ),
      (∀ l, U l |>.IsGaugeField) →
      (∀ l, l < nl → ∀ ν x, Lat (Lz h) l x → Rg h nl μ l x → Rg h nl μ l (x + Lz h ^ l • Pi.single ν 1) →
        V l ν (img h (base l) l x) = moveC (U l) (A' l) ν (img h (base l) l x) ∧
        ‖Bf a₀ l ν (img h (base l) l x)‖ ≤ s₀ l) →
      (∀ l, l < nl → ∀ ρ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x →
        Rg h nl μ (l + 1) (x + Lz h ^ (l + 1) • Pi.single ρ 1) →
        (∀ μ' ν' z, PlaqIn (boxR (img h (base l) l x) (loD h) (hiD h ρ ρ)) μ' ν' z →
          hs (((plaq (U l) μ' ν' z : GLN) : Mat) - 1) ≤ a₀' l) ∧
        (∀ ν z, BoxBond (img h (base l) l x) h ρ ν z → ‖A' l ν z‖ ≤ a₁' l)) →
      (∀ l, l < nl → 0 ≤ a₀' l ∧ 0 ≤ a₁' l ∧ a₀' l ≤ c ∧ a₁' l ≤ c ∧ 0 ≤ s₀ l ∧ s₀ l < c) →
      (∀ l, l < nl → ∀ ρ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x →
        Rg h nl μ (l + 1) (x + Lz h ^ (l + 1) • Pi.single ρ 1) →
        ∀ a, Bf a (l + 1) ρ (img h (base (l + 1)) (l + 1) x) = relLog (V l) (Bf a l) (img h (base l) l x) ρ h) →
      (∀ ν x, Lat (Lz h) 0 x → Rg h nl μ 0 x → Rg h nl μ 0 (x + Lz h ^ 0 • Pi.single ν 1) →
        DifferentiableAt ℂ (fun a => Bf a 0 ν (img h (base 0) 0 x)) a₀) →
      ∀ l, l ≤ nl → ∀ ν x, Lat (Lz h) l x → Rg h nl μ l x → Rg h nl μ l (x + Lz h ^ l • Pi.single ν 1) →
        DifferentiableAt ℂ (fun a => Bf a l ν (img h (base l) l x)) a₀ := by
  classical
  choose cd hcd hdiff using fun ρ : Fin 4 => relLog_core_differentiableAt (N := N) h ρ
  set c := Finset.univ.inf' Finset.univ_nonempty cd
  have hc0 : 0 < c := (Finset.lt_inf'_iff _).2 fun ρ _ => hcd ρ
  have hcd' : ∀ ρ, c ≤ cd ρ := fun ρ => Finset.inf'_le _ (Finset.mem_univ ρ)
  refine ⟨c, hc0, ?_⟩
  intro nl μ nn _ hn base U V A' E _ _ Bf a₀ a₀' a₁' s₀ hU hVB hdat ha hrel h0 l
  induction l with
  | zero => intro _; exact h0
  | succ l ih =>
    intro hl ρ x hx q0 q1
    have hll : l < nl := by omega
    have hn2 : 4 * h + 2 ≤ nn l := by have := hn l; omega
    obtain ⟨ha0, ha1, ha0c, ha1c, hs0, hsc⟩ := ha l hll
    obtain ⟨hpl, hA⟩ := hdat l hll ρ x hx q0 q1
    set y := img h (base l) l x
    set W := moveC (U l) (A' l)
    have hbx : ∀ ν z, (Bm y h z ∨ Bp y h ρ z) → (Bm y h (z + unit (nn l) ν) ∨ Bp y h ρ (z + unit (nn l) ν)) →
        V l ν z = W ν z := fun ν z h1 h2 => by
      obtain ⟨x', hx', r0, r1, rfl⟩ := box_site (hn l) (base l) hx q0 q1 ⟨h1, h2⟩
      exact (hVB l hll ν x' hx' r0 r1).1
    have hf := relLog_fun_local (y := y) (μ := ρ) (h := h) hn2 hbx
    set P := restrictBoxL (N := N) y h ρ
    have hPB : ∀ B, P B = restrictF B (InBoxB y h ρ) := fun B => rfl
    have hR : DifferentiableAt ℂ (fun a => P (Bf a l)) a₀ := by
      refine differentiableAt_pi.2 fun ν => differentiableAt_pi.2 fun z => ?_
      simp only [hPB, restrictF]
      split_ifs with hb
      · obtain ⟨x', hx', r0, r1, rfl⟩ := box_site (hn l) (base l) hx q0 q1 hb
        exact ih hll.le ν x' hx' r0 r1
      · exact differentiableAt_const _
    have hRB : ‖P (Bf a₀ l)‖ ≤ s₀ l := by
      rw [hPB]
      refine norm_restrictF_box_le hs0 fun ν z hb => ?_
      obtain ⟨x', hx', r0, r1, rfl⟩ := box_site (hn l) (base l) hx q0 q1 hb
      exact (hVB l hll ν x' hx' r0 r1).2
    have hPP : P (P (Bf a₀ l)) = P (Bf a₀ l) := by simp only [hPB, restrictF_restrictF]
    have hd : DifferentiableAt ℂ (fun B => relLog W B y ρ h) (P (Bf a₀ l)) :=
      hdiff ρ (U l) (hU l) (hn l) y (a₀' l) (a₁' l) ha0 ha1 (ha0c.trans (hcd' ρ)) (ha1c.trans (hcd' ρ)) hpl
        (A' l) hA (P (Bf a₀ l)) (by rw [← hPB, hPP]; exact hRB.trans_lt (hsc.trans_le (hcd' ρ)))
    have hfun : (fun a => Bf a (l + 1) ρ (img h (base (l + 1)) (l + 1) x)) =
        (fun B => relLog W B y ρ h) ∘ (fun a => P (Bf a l)) := by
      funext a
      simp only [Function.comp, hrel l hll ρ x hx q0 q1 a]
      rw [congrFun hf (Bf a l), relLog_box hn2 W y ρ (Bf a l), ← hPB (Bf a l)]
    rw [hfun]
    exact hd.comp a₀ hR


open Classical in
/-- The exponents of the core's `𝐔 = e^{iaA'}U` in the axial gauge, `X(A') = (1/i) Log 𝐔^u` on the bonds of the box of
the bond and `0` elsewhere. -/
def Xax {n : ℕ} [NeZero n] (U : Config N n) (y : Site n) (h : ℕ) (μ : Fin 4) (A' : Fin 4 → Site n → Mat) :
    Fin 4 → Site n → Mat :=
  fun ρ z => if BoxBond y h μ ρ z then (1 / Complex.I) • LogM ((((moveC U A').gauge (uG U y h)) ρ z : GLN) : Mat)
    else 0

open Classical in
/-- **`prop:relative-average`(i), the holomorphy in `(A', A)` for the general `U`**: the map
`(A', B) ↦ (1/i) log 𝓜_{e^{iaA'}U}(B)(c)` is holomorphic near `(A'₀, B₀)` with `‖aA'₀‖_{∞,box}, ‖B₀‖_{∞,box} < c`, `U` a
gauge field with `|U(∂p) - id| ≤ α₀ ≤ c` on the box: in the axial gauge it is
`(1/i) log 𝓜_{𝐔_{X(A')}}(Ad_uB|_{box})(c)`, and `A' ↦ X(A') = (1/i) Log (e^{iaA'}U)^u` is holomorphic. -/
theorem relLog_core_pair_differentiableAt (h : ℕ) (μ : Fin 4) :
    ∃ c : ℝ, 0 < c ∧
      ∀ {n : ℕ} [NeZero n] (U : Config N n), U.IsGaugeField → 4 * h + 4 ≤ n → ∀ (y : Site n) (α₀ : ℝ),
        0 ≤ α₀ → α₀ ≤ c →
        (∀ μ' ν' z, PlaqIn (boxR y (loD h) (hiD h μ μ)) μ' ν' z →
          hs (((plaq U μ' ν' z : GLN) : Mat) - 1) ≤ α₀) →
        ∀ A'₀ B₀ : Fin 4 → Site n → Mat, ‖restrictF A'₀ (InBoxB y h μ)‖ < c →
          ‖restrictF B₀ (InBoxB y h μ)‖ < c →
          DifferentiableAt ℂ (fun p : (Fin 4 → Site n → Mat) × (Fin 4 → Site n → Mat) =>
            relLog (moveC U p.1) p.2 y μ h) (A'₀, B₀) := by
  obtain ⟨ci, hci, hpol⟩ := uniform_polydisc (N := N) h μ
  set K := redK N h
  have hK4 : 4 ≤ K := four_le_redK N h
  have hKpos : 0 < K := by linarith
  set c := min (min (ci / (2 * K)) (1 / (8 * K))) ci with hc_def
  have hc1 : c ≤ ci / (2 * K) := (min_le_left _ _).trans (min_le_left _ _)
  have hc2 : c ≤ 1 / (8 * K) := (min_le_left _ _).trans (min_le_right _ _)
  have hc3 : c ≤ ci := min_le_right _ _
  refine ⟨c, lt_min (lt_min (by positivity) (by positivity)) hci, ?_⟩
  intro n _ U hU hn y α₀ hα₀ hα₀c hplq A'₀ B₀ hA₀ hB₀
  have hn2 : 4 * h + 2 ≤ n := by omega
  have hKc : K * c ≤ ci / 2 := by
    calc K * c ≤ K * (ci / (2 * K)) := mul_le_mul_of_nonneg_left hc1 hKpos.le
      _ = ci / 2 := by field_simp
  have hK8 : K * c ≤ 1 / 8 := by
    calc K * c ≤ K * (1 / (8 * K)) := mul_le_mul_of_nonneg_left hc2 hKpos.le
      _ = 1 / 8 := by field_simp
  set u := uG U y h
  have hu : ∀ z, ((u z : GLN) : Mat) ∈ unitaryGroup (Fin N) ℂ := fun z => hol_unitary' U hU _
  -- the reduction at every `A'` small on the box gives `X(A')`
  have hred : ∀ A' : Fin 4 → Site n → Mat, ‖restrictF A' (InBoxB y h μ)‖ < c →
      ‖Xax U y h μ A'‖ ≤ K * c ∧ ∀ ρ z, BoxBond y h μ ρ z → ((moveC U A').gauge u) ρ z = UX (Xax U y h μ A') ρ z := by
    intro A' hA'
    have hA : ∀ ρ z, BoxBond y h μ ρ z → ‖A' ρ z‖ ≤ ‖restrictF A' (InBoxB y h μ)‖ := fun ρ z hb => by
      have := (norm_le_pi_norm (restrictF A' (InBoxB y h μ) ρ) z).trans
        (norm_le_pi_norm (restrictF A' (InBoxB y h μ)) ρ)
      rwa [restrictF_box_apply _ hb] at this
    obtain ⟨X, hXc, -, hag, hl, hz⟩ := reduce_box_supp hU hn y μ hα₀ (norm_nonneg _) hα₀c hA'.le hc2 hplq A' hA
    have hX : X = Xax U y h μ A' := by
      funext ρ z
      simp only [Xax]
      split_ifs with hb
      · exact hl ρ z hb
      · exact hz ρ z hb
    subst hX
    exact ⟨hXc, hag⟩
  obtain ⟨hX0c, hag0⟩ := hred A'₀ hA₀
  -- `A' ↦ X(A')` is holomorphic at `A'₀`
  have hXd : DifferentiableAt ℂ (Xax U y h μ) A'₀ := by
    refine differentiableAt_pi.2 fun ρ => differentiableAt_pi.2 fun z => ?_
    by_cases hb : BoxBond y h μ ρ z
    · have e : (fun A' => Xax U y h μ A' ρ z) =
          fun A' => (1 / Complex.I) • LogM ((((moveC U A').gauge u) ρ z : GLN) : Mat) := by
        funext A'; simp [Xax, hb]; rfl
      rw [e]
      have hm : DifferentiableAt ℂ (fun A' : Fin 4 → Site n → Mat =>
          ((((moveC U A').gauge u) ρ z : GLN) : Mat)) A'₀ := by
        simp only [Config.gauge, Units.val_mul]
        exact ((differentiableAt_const _).mul (moveC_differentiableAt U A'₀ ρ z)).mul (differentiableAt_const _)
      have hW : ‖((((moveC U A'₀).gauge u) ρ z : GLN) : Mat) - 1‖ < 1 := by
        rw [hag0 ρ z hb]
        show ‖((expU (Complex.I • Xax U y h μ A'₀ ρ z) * oneC (N := N) ρ z : GLN) : Mat) - 1‖ < 1
        simp only [oneC, mul_one, expU_val]
        have hXz : ‖Complex.I • Xax U y h μ A'₀ ρ z‖ ≤ 1 / 8 := by
          rw [norm_I_smul']
          exact ((norm_le_pi_norm (Xax U y h μ A'₀ ρ) z).trans (norm_le_pi_norm _ ρ)).trans (hX0c.trans hK8)
        have h1 := (BakerCampbellHausdorff.norm_exp_sub_one_le ℂ (Complex.I • Xax U y h μ A'₀ ρ z)).trans
          (exp_sub_one_le_two_mul (norm_nonneg _) hXz (by norm_num))
        linarith
      have hcomp : DifferentiableAt ℂ ((LogM (N := N)) ∘ fun A' : Fin 4 → Site n → Mat =>
          ((((moveC U A').gauge u) ρ z : GLN) : Mat)) A'₀ :=
        DifferentiableAt.comp (g := LogM (N := N)) A'₀ (analyticOnNhd_LogM (N := N) _ hW).differentiableAt hm
      exact (differentiableAt_const (1 / Complex.I)).smul hcomp
    · have e : (fun A' => Xax U y h μ A' ρ z) = fun _ => 0 := by
        funext A'; simp [Xax, hb]
      rw [e]; exact differentiableAt_const _
  -- the composite in the axial gauge
  set P := restrictBoxL (N := N) y h μ
  have hPB : ∀ B, P B = restrictF B (InBoxB y h μ) := fun B => rfl
  have hAdF : ∀ B, AdFL u B = AdF u B := fun B => rfl
  set g : (Fin 4 → Site n → Mat) × (Fin 4 → Site n → Mat) → Mat :=
    fun p => relLog (UX (N := N) (Xax U y h μ p.1)) (AdFL u (P p.2)) y μ h with hg
  have hcond0 : Cond (N := N) y μ h (Xax U y h μ A'₀, AdFL u (P B₀)) :=
    hpol y _ _ (by linarith) (by rw [hAdF, hPB, norm_AdF_unitary hu]; linarith)
  have hgd : DifferentiableAt ℂ g (A'₀, B₀) := by
    have hd := relLog_pair_differentiableAt hcond0
    have hX1 : DifferentiableAt ℂ (fun p : (Fin 4 → Site n → Mat) × (Fin 4 → Site n → Mat) =>
        Xax U y h μ p.1) (A'₀, B₀) :=
      DifferentiableAt.comp (g := Xax U y h μ) (f := Prod.fst) (A'₀, B₀) hXd differentiableAt_fst
    have hX2 : DifferentiableAt ℂ (fun p : (Fin 4 → Site n → Mat) × (Fin 4 → Site n → Mat) =>
        AdFL u (P p.2)) (A'₀, B₀) :=
      (AdFL u).differentiableAt.comp (A'₀, B₀) (P.differentiableAt.comp (A'₀, B₀) differentiableAt_snd)
    have hlin : DifferentiableAt ℂ (fun p : (Fin 4 → Site n → Mat) × (Fin 4 → Site n → Mat) =>
        ((Xax U y h μ p.1, AdFL u (P p.2)) : PairSp N n)) (A'₀, B₀) := hX1.prodMk hX2
    exact DifferentiableAt.comp (f := fun p : (Fin 4 → Site n → Mat) × (Fin 4 → Site n → Mat) =>
      ((Xax U y h μ p.1, AdFL u (P p.2)) : PairSp N n)) (A'₀, B₀) hd hlin
  have hopen : IsOpen {p : (Fin 4 → Site n → Mat) × (Fin 4 → Site n → Mat) | ‖P p.1‖ < c ∧ ‖P p.2‖ < ci} :=
    (isOpen_lt (continuous_norm.comp (P.continuous.comp continuous_fst)) continuous_const).inter
      (isOpen_lt (continuous_norm.comp (P.continuous.comp continuous_snd)) continuous_const)
  have hev : (fun p : (Fin 4 → Site n → Mat) × (Fin 4 → Site n → Mat) => relLog (moveC U p.1) p.2 y μ h)
      =ᶠ[𝓝 (A'₀, B₀)] g := by
    filter_upwards [hopen.mem_nhds (show (A'₀, B₀) ∈ {p : (Fin 4 → Site n → Mat) × (Fin 4 → Site n → Mat) |
      ‖P p.1‖ < c ∧ ‖P p.2‖ < ci} from ⟨by rw [hPB]; exact hA₀, by rw [hPB]; linarith⟩)] with p hp
    obtain ⟨hp1, hp2⟩ := hp
    obtain ⟨hXc, hag⟩ := hred p.1 (by rw [← hPB]; exact hp1)
    rw [relLog_box hn2 (moveC U p.1) y μ p.2]
    have hc := hpol y (Xax U y h μ p.1) (AdF u (restrictF p.2 (InBoxB y h μ))) (by linarith)
      (by rw [norm_AdF_unitary hu, ← hPB]; exact hp2)
    rw [relLog_reduce hU hn hag _ hc]
    rfl
  exact (hev.differentiableAt_iff).2 hgd


/-! ### The holomorphy of the site factors and of the gauge transformations of the levels -/

/-- `sExp(𝐔_X, B, c₊)` is holomorphic in the pair where the conditions hold. -/
lemma sExp_pair_differentiableAt_end {n : ℕ} [NeZero n] {y : Site n} {μ : Fin 4} {h : ℕ} {p₀ : PairSp N n}
    (hcp : Cond (N := N) y μ h p₀) :
    DifferentiableAt ℂ (fun p : PairSp N n => sExp (UX (N := N) p.1) p.2 (cPlus y μ h) h) p₀ := by
  have htA : ∀ x : Pts h, DifferentiableAt ℂ (fun p : PairSp N n =>
      ((trans (moveC (UX (N := N) p.1) p.2) (cPlus y μ h) h x : GLN) : Mat)) p₀ := fun x =>
    trans_differentiableAt (fun p : PairSp N n => moveC (UX (N := N) p.1) p.2)
      (UXB_hV p₀) (cPlus y μ h) h x (hcp.gA1.1 x) ((hcp.gA1.2 x).trans (by norm_num))
  have ht : ∀ x : Pts h, DifferentiableAt ℂ (fun p : PairSp N n =>
      ((trans (UX (N := N) p.1) (cPlus y μ h) h x : GLN) : Mat)) p₀ := fun x =>
    trans_differentiableAt (fun p : PairSp N n => UX (N := N) p.1)
      (UX_hV p₀) (cPlus y μ h) h x (hcp.g1.1 x) ((hcp.g1.2 x).trans (by norm_num))
  unfold sExp
  have hs : DifferentiableAt ℂ (fun p : PairSp N n => ∑ x : Pts h,
      LogM ((trans (moveC (UX (N := N) p.1) p.2) (cPlus y μ h) h x *
        (trans (UX (N := N) p.1) (cPlus y μ h) h x)⁻¹ : GLN) : Mat)) p₀ := by
    refine DifferentiableAt.fun_sum fun x _ => ?_
    have hL := (analyticOnNhd_LogM (N := N) _ (hcp.q1 x)).differentiableAt
    have hm : DifferentiableAt ℂ (fun p : PairSp N n =>
        ((trans (moveC (UX (N := N) p.1) p.2) (cPlus y μ h) h x *
          (trans (UX (N := N) p.1) (cPlus y μ h) h x)⁻¹ : GLN) : Mat)) p₀ := by
      simp only [Units.val_mul]
      exact (htA x).mul (inv_differentiableAt (ht x))
    exact DifferentiableAt.comp (g := LogM (N := N)) p₀ hL hm
  exact hs.fun_const_smul _

/-- **The exponents of the site factors are holomorphic near small `B`** for the core's `𝐔`, at both ends of the bond. -/
theorem sExp_core_differentiableAt (h : ℕ) (μ : Fin 4) :
    ∃ c : ℝ, 0 < c ∧
      ∀ {n : ℕ} [NeZero n] (U : Config N n), U.IsGaugeField → 4 * h + 4 ≤ n → ∀ (y : Site n)
        [DecidablePred (InBoxB y h μ)] (α₀ α₁ : ℝ), 0 ≤ α₀ → 0 ≤ α₁ → α₀ ≤ c → α₁ ≤ c →
        (∀ μ' ν' z, PlaqIn (boxR y (loD h) (hiD h μ μ)) μ' ν' z →
          hs (((plaq U μ' ν' z : GLN) : Mat) - 1) ≤ α₀) →
        ∀ A' : Fin 4 → Site n → Mat, (∀ ρ z, BoxBond y h μ ρ z → ‖A' ρ z‖ ≤ α₁) →
        ∀ (b : Bool) (B₀ : Fin 4 → Site n → Mat), ‖restrictF B₀ (InBoxB y h μ)‖ < c →
          DifferentiableAt ℂ (fun B => sExp (moveC U A') B (ofs y (endW h μ b)) h) B₀ := by
  obtain ⟨ci, hci, hpol⟩ := uniform_polydisc (N := N) h μ
  set K := redK N h
  have hK4 : 4 ≤ K := four_le_redK N h
  have hKpos : 0 < K := by linarith
  set c := min (min (ci / (2 * K)) (1 / (8 * K))) ci with hc_def
  have hc1 : c ≤ ci / (2 * K) := (min_le_left _ _).trans (min_le_left _ _)
  have hc2 : c ≤ 1 / (8 * K) := (min_le_left _ _).trans (min_le_right _ _)
  have hc3 : c ≤ ci := min_le_right _ _
  refine ⟨c, lt_min (lt_min (by positivity) (by positivity)) hci, ?_⟩
  intro n _ U hU hn y _ α₀ α₁ hα₀ hα₁ hα₀c hα₁c hplq A' hA b B₀ hB₀
  classical
  have hn2 : 4 * h + 2 ≤ n := by omega
  obtain ⟨X, hXc, -, hag, -, -⟩ := reduce_box_supp hU hn y μ hα₀ hα₁ hα₀c hα₁c hc2 hplq A' hA
  have hKc : K * c ≤ ci / 2 := by
    calc K * c ≤ K * (ci / (2 * K)) := mul_le_mul_of_nonneg_left hc1 hKpos.le
      _ = ci / 2 := by field_simp
  have hXci : ‖X‖ < ci := by linarith
  set u := uG U y h
  have hu : ∀ z, ((u z : GLN) : Mat) ∈ unitaryGroup (Fin N) ℂ := fun z => hol_unitary' U hU _
  set W := moveC U A'
  set z₀ := ofs y (endW h μ b)
  set P := restrictBoxL (N := N) y h μ
  have hPB : ∀ B, P B = restrictF B (InBoxB y h μ) := fun B => rfl
  have hAdF : ∀ B, AdFL u B = AdF u B := fun B => rfl
  -- the bonds of the block of `z₀` lie in the box
  have hbb : ∀ ν z, Bm z₀ h z → Bm z₀ h (z + unit n ν) → BoxBond y h μ ν z := fun ν z h1 h2 =>
    boxBond_of_end hn2 b h1 h2
  -- `sExp` of `𝐔` at `z₀` reads `B` on the box only
  have hloc : ∀ B, sExp W B z₀ h = sExp W (P B) z₀ h := fun B => by
    rw [sExp_local hn2 W B, sExp_local hn2 W (P B)]
    congr 1
    funext ν z
    simp only [restrictF, hPB]
    split_ifs with h1 h2 <;> first | rfl | (exfalso; exact h2 (hbb ν z h1.1 h1.2)) | skip
  -- the axial gauge on a neighbourhood
  set g : (Fin 4 → Site n → Mat) → Mat :=
    fun B => Ad (u z₀)⁻¹ (sExp (UX (N := N) X) (AdFL u (P B)) z₀ h) with hg
  have hgd : DifferentiableAt ℂ g B₀ := by
    have hcond0 : Cond (N := N) y μ h (X, AdFL u (P B₀)) :=
      hpol y X _ hXci (by rw [hAdF, hPB, norm_AdF_unitary hu]; linarith)
    have hs : DifferentiableAt ℂ (fun B => sExp (UX (N := N) X) (AdFL u (P B)) z₀ h) B₀ := by
      have hlin : DifferentiableAt ℂ (fun B : Fin 4 → Site n → Mat => ((X, AdFL u (P B)) : PairSp N n)) B₀ :=
        (differentiableAt_const X).prodMk ((AdFL u).comp P).differentiableAt
      cases b
      · have hd := sExp_pair_differentiableAt hcond0
        have e : z₀ = y := by simp only [z₀, endW, Bool.false_eq_true, ↓reduceIte, ofs_zero]
        rw [e]
        exact DifferentiableAt.comp (f := fun B : Fin 4 → Site n → Mat => ((X, AdFL u (P B)) : PairSp N n)) B₀ hd hlin
      · have hd := sExp_pair_differentiableAt_end hcond0
        exact DifferentiableAt.comp (f := fun B : Fin 4 → Site n → Mat => ((X, AdFL u (P B)) : PairSp N n)) B₀ hd hlin
    simp only [hg, Ad]
    exact ((differentiableAt_const _).mul hs).mul (differentiableAt_const _)
  have hopen : IsOpen {B : Fin 4 → Site n → Mat | ‖P B‖ < c} :=
    isOpen_lt (continuous_norm.comp P.continuous) continuous_const
  have hev : (fun B => sExp W B z₀ h) =ᶠ[𝓝 B₀] g := by
    filter_upwards [hopen.mem_nhds (show ‖P B₀‖ < c by rw [hPB]; exact hB₀)] with B hB
    have hB' : ‖P B‖ < c := hB
    have hcond := hpol y X (AdF u (P B)) hXci (by rw [norm_AdF_unitary hu]; linarith)
    -- `GoodAt` at `z₀` for `𝐔` and for `e^{iPB}𝐔`
    have hboxR : ∀ ν z, (Bm y h z ∨ Bp y h μ z) → (Bm y h (z + unit n ν) ∨ Bp y h μ (z + unit n ν)) →
        ((moveC W (P B)).gauge u) ν z = moveC (UX (N := N) X) (AdF u (P B)) ν z := fun ν z h1 h2 => by
      rw [← moveC_gauge]
      simp only [moveC]
      rw [hag ν z ⟨h1, h2⟩]
    have hgW : GoodAt W z₀ h := by
      refine (goodAt_gauge hu).1 ((goodAt_local hn2 fun ν z h1 h2 => hag ν z (hbb ν z h1 h2)).2 ?_)
      cases b
      · simpa only [z₀, endW, Bool.false_eq_true, ↓reduceIte, ofs_zero] using hcond.g0
      · exact hcond.g1
    have hgB : GoodAt (moveC W (P B)) z₀ h := by
      refine (goodAt_gauge hu).1 ((goodAt_local hn2 fun ν z h1 h2 => hboxR ν z (hbb ν z h1 h2).1
        (hbb ν z h1 h2).2).2 ?_)
      cases b
      · simpa only [z₀, endW, Bool.false_eq_true, ↓reduceIte, ofs_zero] using hcond.gA0
      · exact hcond.gA1
    have hcov := sExp_gauge W u (P B) z₀ h
      (fun Z => by rw [SupportCont.opNorm_Ad_unitary (hu _)]; linarith [norm_nonneg Z])
      hgW.expsG_le hgB.expsG_le
    have hloc2 : sExp (W.gauge u) (AdF u (P B)) z₀ h = sExp (UX (N := N) X) (AdF u (P B)) z₀ h :=
      sExp_local_V hn2 _ fun ν z h1 h2 => hag ν z (hbb ν z h1 h2)
    simp only [hg, hAdF]
    rw [hloc B, ← hloc2, hcov, ← Ad_mul', inv_mul_cancel]
    simp [Ad]
  exact (hev.differentiableAt_iff).2 hgd


open Classical in
/-- The exponent of the site factor at an end of the bond reads the form on the box of the bond only. -/
lemma sExp_end_local {n : ℕ} [NeZero n] {h : ℕ} (hn : 4 * h + 2 ≤ n) {y : Site n} {μ : Fin 4} (V : Config N n)
    (B : Fin 4 → Site n → Mat) (b : Bool) :
    sExp V B (ofs y (endW h μ b)) h = sExp V (restrictF B (InBoxB y h μ)) (ofs y (endW h μ b)) h := by
  rw [sExp_local hn V B, sExp_local hn V (restrictF B (InBoxB y h μ))]
  congr 1
  funext ν z
  simp only [restrictF]
  split_ifs with h1 h2
  · rfl
  · exact absurd (boxBond_of_end hn b h1.1 h1.2) h2
  · rfl

open Classical in
/-- **`prop:relative-average-order`(i), the holomorphy of the gauge transformations `𝐠_l`** (and so of `v_n`): for families
`a ↦ B(a)`, `a ↦ 𝐠(a)` with `𝐠(a)_{l+1} = 𝐠(a)_l v_{V_l}(B(a)_l)` on the regions, the forms holomorphic at `a₀` on the
regions (`forms_differentiableAt`) and small there, and `𝐠(a)_0` holomorphic, the values of `𝐠(a)_l` are holomorphic at
`a₀` on the region of every level. -/
theorem gauge_differentiableAt (h : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ (nl : ℕ) (μ : Fin 4) (nn : ℕ → ℕ) [∀ l, NeZero (nn l)],
      (∀ l, 4 * h + 4 ≤ nn l) → ∀ (base : ∀ l, Site (nn l)) (U V : ∀ l, Config N (nn l))
      (A' : ∀ l, Fin 4 → Site (nn l) → Mat) {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
      (Bf : E → ∀ l, Fin 4 → Site (nn l) → Mat) (gf : E → ∀ l, Site (nn l) → GLN) (a₀ : E)
      (a₀' a₁' s₀ : ℕ → ℝ),
      (∀ l, U l |>.IsGaugeField) →
      (∀ l, l < nl → ∀ ν x, Lat (Lz h) l x → Rg h nl μ l x → Rg h nl μ l (x + Lz h ^ l • Pi.single ν 1) →
        V l ν (img h (base l) l x) = moveC (U l) (A' l) ν (img h (base l) l x) ∧
        ‖Bf a₀ l ν (img h (base l) l x)‖ ≤ s₀ l ∧
        DifferentiableAt ℂ (fun a => Bf a l ν (img h (base l) l x)) a₀) →
      (∀ l, l < nl → ∀ ρ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x →
        Rg h nl μ (l + 1) (x + Lz h ^ (l + 1) • Pi.single ρ 1) →
        (∀ μ' ν' z, PlaqIn (boxR (img h (base l) l x) (loD h) (hiD h ρ ρ)) μ' ν' z →
          hs (((plaq (U l) μ' ν' z : GLN) : Mat) - 1) ≤ a₀' l) ∧
        (∀ ν z, BoxBond (img h (base l) l x) h ρ ν z → ‖A' l ν z‖ ≤ a₁' l)) →
      (∀ l, l < nl → 0 ≤ a₀' l ∧ 0 ≤ a₁' l ∧ a₀' l ≤ c ∧ a₁' l ≤ c ∧ 0 ≤ s₀ l ∧ s₀ l < c) →
      (∀ l, l < nl → ∀ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x → ∀ a,
        gf a (l + 1) (img h (base (l + 1)) (l + 1) x) =
          gf a l (img h (base l) l x) * siteFactor (V l) (Bf a l) (img h (base l) l x) h) →
      (∀ x, Lat (Lz h) 0 x → Rg h nl μ 0 x → DifferentiableAt ℂ (fun a => ((gf a 0 (img h (base 0) 0 x) : GLN) : Mat)) a₀) →
      ∀ l, l ≤ nl → ∀ x, Lat (Lz h) l x → Rg h nl μ l x →
        DifferentiableAt ℂ (fun a => ((gf a l (img h (base l) l x) : GLN) : Mat)) a₀ := by
  choose cs hcs hsd using fun ρ : Fin 4 => sExp_core_differentiableAt (N := N) h ρ
  set c := Finset.univ.inf' Finset.univ_nonempty cs
  have hc0 : 0 < c := (Finset.lt_inf'_iff _).2 fun ρ _ => hcs ρ
  have hcs' : ∀ ρ, c ≤ cs ρ := fun ρ => Finset.inf'_le _ (Finset.mem_univ ρ)
  refine ⟨c, hc0, ?_⟩
  intro nl μ nn _ hn base U V A' E _ _ Bf gf a₀ a₀' a₁' s₀ hU hVB hdat ha hg h0 l
  induction l with
  | zero => intro _; exact h0
  | succ l ih =>
    intro hl x hx hR
    have hll : l < nl := by omega
    have hn2 : 4 * h + 2 ≤ nn l := by have := hn l; omega
    obtain ⟨ha0, ha1, ha0c, ha1c, hs0, hsc⟩ := ha l hll
    obtain ⟨x', b, hx', r0, r1, hb⟩ := rg_end_img (base l) hl hx hR
    obtain ⟨hpl, hA⟩ := hdat l hll μ x' hx' r0 r1
    set y := img h (base l) l x'
    set W := moveC (U l) (A' l)
    set P := restrictBoxL (N := N) y h μ
    have hPB : ∀ B, P B = restrictF B (InBoxB y h μ) := fun B => rfl
    -- the site factor at `img x = ofs y (endW b)`
    have hVW : ∀ a, sExp (V l) (Bf a l) (ofs y (endW h μ b)) h = sExp W (P (Bf a l)) (ofs y (endW h μ b)) h :=
      fun a => by
        rw [sExp_local_V hn2 (Bf a l) fun ν z h1 h2 => by
          obtain ⟨x'', hx'', s0, s1, rfl⟩ := box_site (hn l) (base l) hx' r0 r1 (boxBond_of_end hn2 b h1 h2)
          exact (hVB l hll ν x'' hx'' s0 s1).1]
        rw [sExp_end_local hn2 W (Bf a l) b, ← hPB (Bf a l)]
    have hR' : DifferentiableAt ℂ (fun a => P (Bf a l)) a₀ := by
      refine differentiableAt_pi.2 fun ν => differentiableAt_pi.2 fun z => ?_
      simp only [hPB, restrictF]
      split_ifs with hbb
      · obtain ⟨x'', hx'', s0, s1, rfl⟩ := box_site (hn l) (base l) hx' r0 r1 hbb
        exact (hVB l hll ν x'' hx'' s0 s1).2.2
      · exact differentiableAt_const _
    have hRB : ‖P (Bf a₀ l)‖ ≤ s₀ l := by
      rw [hPB]
      refine norm_restrictF_box_le hs0 fun ν z hbb => ?_
      obtain ⟨x'', hx'', s0, s1, rfl⟩ := box_site (hn l) (base l) hx' r0 r1 hbb
      exact (hVB l hll ν x'' hx'' s0 s1).2.1
    have hPP : restrictF (P (Bf a₀ l)) (InBoxB y h μ) = P (Bf a₀ l) := by simp only [hPB, restrictF_restrictF]
    have hsdiff : DifferentiableAt ℂ (fun B => sExp W B (ofs y (endW h μ b)) h) (P (Bf a₀ l)) :=
      hsd μ (U l) (hU l) (hn l) y (a₀' l) (a₁' l) ha0 ha1 (ha0c.trans (hcs' μ)) (ha1c.trans (hcs' μ)) hpl (A' l)
        hA b (P (Bf a₀ l)) (by rw [hPP]; exact hRB.trans_lt (hsc.trans_le (hcs' μ)))
    have hS : DifferentiableAt ℂ (fun a => sExp (V l) (Bf a l) (img h (base l) l x) h) a₀ := by
      have e : (fun a => sExp (V l) (Bf a l) (img h (base l) l x) h) =
          (fun B => sExp W B (ofs y (endW h μ b)) h) ∘ (fun a => P (Bf a l)) := by
        funext a; simp only [Function.comp, hb, hVW a]
      rw [e]; exact hsdiff.comp a₀ hR'
    have hval : (fun a => ((gf a (l + 1) (img h (base (l + 1)) (l + 1) x) : GLN) : Mat)) =
        fun a => ((gf a l (img h (base l) l x) : GLN) : Mat) * exp (sExp (V l) (Bf a l) (img h (base l) l x) h) := by
      funext a
      rw [hg l hll x hx hR a, Units.val_mul, siteFactor_eq_sExp, expU_val]
    rw [hval]
    exact (ih hll.le x (lat_succ_le hx) (rg_mono hR)).mul ((exp_analytic _).differentiableAt.comp a₀ hS)


/-- **`prop:relative-average-order`(i), the holomorphy of the averages**: if `M^l(e^{ia_iA(a)}𝐔) = (e^{iB(a)_l}V_l)^{𝐠(a)_l}`
at a bond of the region (`order_H`) for every `a`, and the form at the bond and the gauge transformations at its ends
are holomorphic at `a₀` (`forms_differentiableAt`, `gauge_differentiableAt`), then so is the average. -/
theorem average_differentiableAt {n : ℕ} [NeZero n] {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (Wf : E → Config N n) (V : Config N n) (Bf : E → Fin 4 → Site n → Mat) (gf : E → Site n → GLN) (a₀ : E)
    {ρ : Fin 4} {z : Site n}
    (hW : ∀ a, Wf a ρ z = ((moveC V (Bf a)).gauge (gf a)) ρ z)
    (hB : DifferentiableAt ℂ (fun a => Bf a ρ z) a₀)
    (hg0 : DifferentiableAt ℂ (fun a => ((gf a z : GLN) : Mat)) a₀)
    (hg1 : DifferentiableAt ℂ (fun a => ((gf a (z + unit n ρ) : GLN) : Mat)) a₀) :
    DifferentiableAt ℂ (fun a => ((Wf a ρ z : GLN) : Mat)) a₀ := by
  have e : (fun a => ((Wf a ρ z : GLN) : Mat)) = fun a => ((gf a z : GLN) : Mat) *
      (exp (Complex.I • Bf a ρ z) * ((V ρ z : GLN) : Mat)) * (((gf a (z + unit n ρ))⁻¹ : GLN) : Mat) := by
    funext a
    rw [hW a, Config.gauge, moveC, Units.val_mul, Units.val_mul, Units.val_mul, expU_val]
  rw [e]
  exact (hg0.mul (((exp_analytic _).differentiableAt.comp a₀ (hB.const_smul Complex.I)).mul
    (differentiableAt_const _))).mul (inv_differentiableAt hg1)


/-- **`prop:relative-average-order`(i), the holomorphy of the forms in `(A', A)`**: for families over any complex normed
space of parameters, with backgrounds `V(a)_l = e^{iA'(a)_l}U_l` on the regions, `A'(a)_l` holomorphic and small at `a₀`
on the regions, `B(a)_{l+1} = (1/i) log 𝓜_{V(a)_l}(B(a)_l)`, and the values at level `0` holomorphic at `a₀`, the
values of the forms of every level are holomorphic at `a₀`, as long as the forms `B(a₀)_l` are smaller than `c`. -/
theorem forms_differentiableAt_pair (h : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ (nl : ℕ) (μ : Fin 4) (nn : ℕ → ℕ) [∀ l, NeZero (nn l)],
      (∀ l, 4 * h + 4 ≤ nn l) → ∀ (base : ∀ l, Site (nn l)) (U : ∀ l, Config N (nn l))
      {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
      (Vf : E → ∀ l, Config N (nn l)) (A'f Bf : E → ∀ l, Fin 4 → Site (nn l) → Mat) (a₀ : E) (a₀' s₀ : ℕ → ℝ),
      (∀ l, U l |>.IsGaugeField) →
      (∀ l, l < nl → ∀ ν x, Lat (Lz h) l x → Rg h nl μ l x → Rg h nl μ l (x + Lz h ^ l • Pi.single ν 1) →
        (∀ a, Vf a l ν (img h (base l) l x) = moveC (U l) (A'f a l) ν (img h (base l) l x)) ∧
        ‖A'f a₀ l ν (img h (base l) l x)‖ ≤ s₀ l ∧ ‖Bf a₀ l ν (img h (base l) l x)‖ ≤ s₀ l ∧
        DifferentiableAt ℂ (fun a => A'f a l ν (img h (base l) l x)) a₀) →
      (∀ l, l < nl → ∀ ρ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x →
        Rg h nl μ (l + 1) (x + Lz h ^ (l + 1) • Pi.single ρ 1) →
        ∀ μ' ν' z, PlaqIn (boxR (img h (base l) l x) (loD h) (hiD h ρ ρ)) μ' ν' z →
          hs (((plaq (U l) μ' ν' z : GLN) : Mat) - 1) ≤ a₀' l) →
      (∀ l, l < nl → 0 ≤ a₀' l ∧ a₀' l ≤ c ∧ 0 ≤ s₀ l ∧ s₀ l < c) →
      (∀ l, l < nl → ∀ ρ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x →
        Rg h nl μ (l + 1) (x + Lz h ^ (l + 1) • Pi.single ρ 1) →
        ∀ a, Bf a (l + 1) ρ (img h (base (l + 1)) (l + 1) x) = relLog (Vf a l) (Bf a l) (img h (base l) l x) ρ h) →
      (∀ ν x, Lat (Lz h) 0 x → Rg h nl μ 0 x → Rg h nl μ 0 (x + Lz h ^ 0 • Pi.single ν 1) →
        DifferentiableAt ℂ (fun a => Bf a 0 ν (img h (base 0) 0 x)) a₀) →
      ∀ l, l ≤ nl → ∀ ν x, Lat (Lz h) l x → Rg h nl μ l x → Rg h nl μ l (x + Lz h ^ l • Pi.single ν 1) →
        DifferentiableAt ℂ (fun a => Bf a l ν (img h (base l) l x)) a₀ := by
  classical
  choose cd hcd hdiff using fun ρ : Fin 4 => relLog_core_pair_differentiableAt (N := N) h ρ
  set c := Finset.univ.inf' Finset.univ_nonempty cd
  have hc0 : 0 < c := (Finset.lt_inf'_iff _).2 fun ρ _ => hcd ρ
  have hcd' : ∀ ρ, c ≤ cd ρ := fun ρ => Finset.inf'_le _ (Finset.mem_univ ρ)
  refine ⟨c, hc0, ?_⟩
  intro nl μ nn _ hn base U E _ _ Vf A'f Bf a₀ a₀' s₀ hU hVB hdat ha hrel h0 l
  induction l with
  | zero => intro _; exact h0
  | succ l ih =>
    intro hl ρ x hx q0 q1
    have hll : l < nl := by omega
    have hn2 : 4 * h + 2 ≤ nn l := by have := hn l; omega
    obtain ⟨ha0, ha0c, hs0, hsc⟩ := ha l hll
    have hpl := hdat l hll ρ x hx q0 q1
    set y := img h (base l) l x
    set P := restrictBoxL (N := N) y h ρ
    have hPB : ∀ B, P B = restrictF B (InBoxB y h ρ) := fun B => rfl
    -- the background reads `A'(a)` on the box only
    have hloc : ∀ a, relLog (Vf a l) (Bf a l) y ρ h = relLog (moveC (U l) (P (A'f a l))) (P (Bf a l)) y ρ h :=
      fun a => by
        have hbx : ∀ ν z, (Bm y h z ∨ Bp y h ρ z) → (Bm y h (z + unit (nn l) ν) ∨ Bp y h ρ (z + unit (nn l) ν)) →
            Vf a l ν z = moveC (U l) (P (A'f a l)) ν z := fun ν z h1 h2 => by
          obtain ⟨x', hx', r0, r1, rfl⟩ := box_site (hn l) (base l) hx q0 q1 ⟨h1, h2⟩
          rw [(hVB l hll ν x' hx' r0 r1).1 a]
          simp only [moveC, hPB, restrictF_box_apply _ ⟨h1, h2⟩]
        rw [congrFun (relLog_fun_local (y := y) (μ := ρ) (h := h) hn2 hbx) (Bf a l),
          relLog_box hn2 _ y ρ (Bf a l), ← hPB (Bf a l)]
    have hRA : DifferentiableAt ℂ (fun a => P (A'f a l)) a₀ := by
      refine differentiableAt_pi.2 fun ν => differentiableAt_pi.2 fun z => ?_
      simp only [hPB, restrictF]
      split_ifs with hb
      · obtain ⟨x', hx', r0, r1, rfl⟩ := box_site (hn l) (base l) hx q0 q1 hb
        exact (hVB l hll ν x' hx' r0 r1).2.2.2
      · exact differentiableAt_const _
    have hRB : DifferentiableAt ℂ (fun a => P (Bf a l)) a₀ := by
      refine differentiableAt_pi.2 fun ν => differentiableAt_pi.2 fun z => ?_
      simp only [hPB, restrictF]
      split_ifs with hb
      · obtain ⟨x', hx', r0, r1, rfl⟩ := box_site (hn l) (base l) hx q0 q1 hb
        exact ih hll.le ν x' hx' r0 r1
      · exact differentiableAt_const _
    have hsA : ‖restrictF (P (A'f a₀ l)) (InBoxB y h ρ)‖ < cd ρ := by
      rw [← hPB, show P (P (A'f a₀ l)) = P (A'f a₀ l) by simp only [hPB, restrictF_restrictF], hPB]
      refine lt_of_le_of_lt (norm_restrictF_box_le hs0 fun ν z hb => ?_) (hsc.trans_le (hcd' ρ))
      obtain ⟨x', hx', r0, r1, rfl⟩ := box_site (hn l) (base l) hx q0 q1 hb
      exact (hVB l hll ν x' hx' r0 r1).2.1
    have hsB : ‖restrictF (P (Bf a₀ l)) (InBoxB y h ρ)‖ < cd ρ := by
      rw [← hPB, show P (P (Bf a₀ l)) = P (Bf a₀ l) by simp only [hPB, restrictF_restrictF], hPB]
      refine lt_of_le_of_lt (norm_restrictF_box_le hs0 fun ν z hb => ?_) (hsc.trans_le (hcd' ρ))
      obtain ⟨x', hx', r0, r1, rfl⟩ := box_site (hn l) (base l) hx q0 q1 hb
      exact (hVB l hll ν x' hx' r0 r1).2.2.1
    have hd := hdiff ρ (U l) (hU l) (hn l) y (a₀' l) ha0 (ha0c.trans (hcd' ρ)) hpl (P (A'f a₀ l)) (P (Bf a₀ l))
      hsA hsB
    have hfun : (fun a => Bf a (l + 1) ρ (img h (base (l + 1)) (l + 1) x)) =
        (fun p : (Fin 4 → Site (nn l) → Mat) × (Fin 4 → Site (nn l) → Mat) => relLog (moveC (U l) p.1) p.2 y ρ h) ∘
          (fun a => (P (A'f a l), P (Bf a l))) := by
      funext a
      simp only [Function.comp, hrel l hll ρ x hx q0 q1 a]
      exact hloc a
    rw [hfun]
    exact hd.comp a₀ (hRA.prodMk hRB)


/-- The fluctuations `A'_l = (1/i) Log(V_lU_l⁻¹)` of the backgrounds are holomorphic wherever the backgrounds are and
`V_lU_l⁻¹` lies within `1` of `id` (the input of `forms_differentiableAt_pair`, with `average_differentiableAt` for the
backgrounds `V_l = M^l(e^{ia_iA'}U)`). -/
lemma logRatio_differentiableAt {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (Vf : E → GLN) (W : GLN)
    {a₀ : E} (hV : DifferentiableAt ℂ (fun a => ((Vf a : GLN) : Mat)) a₀)
    (h1 : ‖((Vf a₀ * W⁻¹ : GLN) : Mat) - 1‖ < 1) :
    DifferentiableAt ℂ (fun a => (1 / Complex.I) • LogM (((Vf a * W⁻¹ : GLN) : Mat))) a₀ := by
  have hm : DifferentiableAt ℂ (fun a => ((Vf a * W⁻¹ : GLN) : Mat)) a₀ := by
    simp only [Units.val_mul]
    exact hV.mul (differentiableAt_const _)
  have hcomp : DifferentiableAt ℂ ((LogM (N := N)) ∘ fun a => ((Vf a * W⁻¹ : GLN) : Mat)) a₀ :=
    DifferentiableAt.comp (g := LogM (N := N)) a₀ (analyticOnNhd_LogM (N := N) _ h1).differentiableAt hm
  exact (differentiableAt_const (1 / Complex.I)).smul hcomp


set_option maxHeartbeats 4000000 in
/-- **`prop:relative-average-order`(v), the Lipschitz continuity of `Q_n` in `a_jA'`**: for two backgrounds
`V^i_l = e^{iA'^i_l}U_l` of the levels with data at most `eL^{-(n-l)}` and `‖A'^1_l - A'^2_l‖_{∞,box} ≤ kL^{-(n-l)}`, the
linear parts `D^i_{l+1} = LQ(V^i_l)D^i_l` with a common `D_0`, `‖D_0‖ ≤ s₀`, satisfy `‖D^1_n - D^2_n‖ ≤ 2C₇kL^{n-1}s₀`:
`‖(Q_n(𝐔¹) - Q_n(𝐔²))A‖ ≤ (2C₇/L)k‖A‖_∞`, `k` the size of `a_j(A'^1_l - A'^2_l)` in the units of the last scale. -/
theorem order_v_lip (h : ℕ) (hh : 1 ≤ h) :
    ∃ c C C₇ : ℝ, 0 < c ∧ 0 ≤ C ∧ 0 ≤ C₇ ∧ ∀ (nl : ℕ) (μ : Fin 4) (nn : ℕ → ℕ) [∀ l, NeZero (nn l)],
      (∀ l, 4 * h + 4 ≤ nn l) → ∀ (base : ∀ l, Site (nn l)) (U V₁ V₂ : ∀ l, Config N (nn l))
      (A₁ A₂ D₁ D₂ : ∀ l, Fin 4 → Site (nn l) → Mat) (a₀ a₁ : ℕ → ℝ) (e k s₀ : ℝ),
      (∀ l, U l |>.IsGaugeField) →
      (∀ l, l < nl → ∀ ν x, Lat (Lz h) l x → Rg h nl μ l x → Rg h nl μ l (x + Lz h ^ l • Pi.single ν 1) →
        V₁ l ν (img h (base l) l x) = moveC (U l) (A₁ l) ν (img h (base l) l x) ∧
        V₂ l ν (img h (base l) l x) = moveC (U l) (A₂ l) ν (img h (base l) l x)) →
      (∀ l, l < nl → ∀ ρ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x →
        Rg h nl μ (l + 1) (x + Lz h ^ (l + 1) • Pi.single ρ 1) →
        (∀ μ' ν' z, PlaqIn (boxR (img h (base l) l x) (loD h) (hiD h ρ ρ)) μ' ν' z →
          hs (((plaq (U l) μ' ν' z : GLN) : Mat) - 1) ≤ a₀ l) ∧
        (∀ ν z, BoxBond (img h (base l) l x) h ρ ν z → ‖A₁ l ν z‖ ≤ a₁ l ∧ ‖A₂ l ν z‖ ≤ a₁ l ∧
          ‖A₁ l ν z - A₂ l ν z‖ ≤ k * ((((2 * h + 1 : ℕ) : ℝ)) ^ (nl - l))⁻¹)) →
      (∀ l, l < nl → 0 ≤ a₀ l ∧ 0 ≤ a₁ l ∧ a₀ l + a₁ l ≤ e * ((((2 * h + 1 : ℕ) : ℝ)) ^ (nl - l))⁻¹) →
      (∀ l, l < nl → ∀ ρ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x →
        Rg h nl μ (l + 1) (x + Lz h ^ (l + 1) • Pi.single ρ 1) →
        D₁ (l + 1) ρ (img h (base (l + 1)) (l + 1) x) =
          ((2 * h + 1 : ℕ) : ℂ) • Qlin (V₁ l) (img h (base l) l x) ρ h (D₁ l) ∧
        D₂ (l + 1) ρ (img h (base (l + 1)) (l + 1) x) =
          ((2 * h + 1 : ℕ) : ℂ) • Qlin (V₂ l) (img h (base l) l x) ρ h (D₂ l)) →
      0 ≤ e → 0 ≤ k → 0 ≤ s₀ → e ≤ c → C * e ≤ 1 →
      (∀ ν x, Lat (Lz h) 0 x → Rg h nl μ 0 x → Rg h nl μ 0 (x + Lz h ^ 0 • Pi.single ν 1) →
        D₁ 0 ν (img h (base 0) 0 x) = D₂ 0 ν (img h (base 0) 0 x) ∧ ‖D₂ 0 ν (img h (base 0) 0 x)‖ ≤ s₀) →
      ∀ ν x, Lat (Lz h) nl x → Rg h nl μ nl x → Rg h nl μ nl (x + Lz h ^ nl • Pi.single ν 1) →
        ‖D₁ nl ν (img h (base nl) nl x) - D₂ nl ν (img h (base nl) nl x)‖ ≤
          2 * C₇ * k * ((((2 * h + 1 : ℕ) : ℝ)) ^ nl / ((2 * h + 1 : ℕ) : ℝ)) * s₀ := by
  classical
  choose cl Cl hcl hCl hlin using fun ρ : Fin 4 => linear_bound (N := N) h ρ
  choose c7 C7 hc7 hC7 h7 using fun ρ : Fin 4 => relative_average_vii_box (N := N) h ρ
  set clm := Finset.univ.inf' Finset.univ_nonempty cl
  set c7m := Finset.univ.inf' Finset.univ_nonempty c7
  set Clm := Finset.univ.sup' Finset.univ_nonempty Cl
  set C7m := Finset.univ.sup' Finset.univ_nonempty C7
  have hclm : ∀ ρ, clm ≤ cl ρ := fun ρ => Finset.inf'_le _ (Finset.mem_univ ρ)
  have hc7m : ∀ ρ, c7m ≤ c7 ρ := fun ρ => Finset.inf'_le _ (Finset.mem_univ ρ)
  have hClm : ∀ ρ, Cl ρ ≤ Clm := fun ρ => Finset.le_sup' _ (Finset.mem_univ ρ)
  have hC7m : ∀ ρ, C7 ρ ≤ C7m := fun ρ => Finset.le_sup' _ (Finset.mem_univ ρ)
  have hclm0 : 0 < clm := (Finset.lt_inf'_iff _).2 fun ρ _ => hcl ρ
  have hc7m0 : 0 < c7m := (Finset.lt_inf'_iff _).2 fun ρ _ => hc7 ρ
  have hClm0 : 0 ≤ Clm := (hCl 0).trans (hClm 0)
  have hC7m0 : 0 ≤ C7m := (hC7 0).trans (hC7m 0)
  refine ⟨min clm c7m, Clm, C7m, lt_min hclm0 hc7m0, hClm0, hC7m0, ?_⟩
  intro nl μ nn _ hn base U V₁ V₂ A₁ A₂ D₁ D₂ a₀ a₁ e k s₀ hU hVV hdat ha hDD he hk hs₀ hec hCe h0
  have hcl' : min clm c7m ≤ clm := min_le_left _ _
  have hc7' : min clm c7m ≤ c7m := min_le_right _ _
  set Lr : ℝ := ((2 * h + 1 : ℕ) : ℝ) with hLr
  have hL3 : 3 ≤ Lr := by rw [hLr]; push_cast; have : (1 : ℝ) ≤ h := by exact_mod_cast hh
                          linarith
  have hL0 : 0 < Lr := by linarith
  have hp1 : ∀ m, (Lr ^ m)⁻¹ ≤ 1 := fun m => inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith))
  -- the bounds of one step at a bond of the level `l + 1`
  have hone : ∀ l, l < nl → ∀ ρ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x →
      Rg h nl μ (l + 1) (x + Lz h ^ (l + 1) • Pi.single ρ 1) → ∀ X : Fin 4 → Site (nn l) → Mat,
      ‖((2 * h + 1 : ℕ) : ℂ) • Qlin (V₁ l) (img h (base l) l x) ρ h X‖ ≤
        (Lr + Clm * (a₀ l + a₁ l)) * ‖restrictF X (InBoxB (img h (base l) l x) h ρ)‖ ∧
      ‖((2 * h + 1 : ℕ) : ℂ) • Qlin (V₂ l) (img h (base l) l x) ρ h X‖ ≤
        (Lr + Clm * (a₀ l + a₁ l)) * ‖restrictF X (InBoxB (img h (base l) l x) h ρ)‖ ∧
      ‖((2 * h + 1 : ℕ) : ℂ) • Qlin (V₁ l) (img h (base l) l x) ρ h X -
        ((2 * h + 1 : ℕ) : ℂ) • Qlin (V₂ l) (img h (base l) l x) ρ h X‖ ≤
        C7m * (k * (Lr ^ (nl - l))⁻¹) * ‖restrictF X (InBoxB (img h (base l) l x) h ρ)‖ := by
    intro l hl ρ x hx q0 q1 X
    have hn2 : 4 * h + 2 ≤ nn l := by have := hn l; omega
    obtain ⟨ha0, ha1, ha2⟩ := ha l hl
    have hae : a₀ l + a₁ l ≤ e := by have := hp1 (nl - l); nlinarith
    set y := img h (base l) l x
    have hbx : ∀ i : Fin 2, ∀ ν z, (Bm y h z ∨ Bp y h ρ z) →
        (Bm y h (z + unit (nn l) ν) ∨ Bp y h ρ (z + unit (nn l) ν)) →
        (if i = 0 then V₁ l else V₂ l) ν z = moveC (U l) (if i = 0 then A₁ l else A₂ l) ν z := fun i ν z h1 h2 => by
      obtain ⟨x', hx', r0, r1, rfl⟩ := box_site (hn l) (base l) hx q0 q1 ⟨h1, h2⟩
      obtain ⟨e1, e2⟩ := hVV l hl ν x' hx' r0 r1
      fin_cases i
      · simpa using e1
      · simpa using e2
    have hQ1 : Qlin (V₁ l) y ρ h = Qlin (moveC (U l) (A₁ l)) y ρ h := by
      simp only [Qlin, relLog_fun_local (y := y) (μ := ρ) (h := h) hn2 (fun ν z h1 h2 => by
        simpa using hbx 0 ν z h1 h2)]
    have hQ2 : Qlin (V₂ l) y ρ h = Qlin (moveC (U l) (A₂ l)) y ρ h := by
      simp only [Qlin, relLog_fun_local (y := y) (μ := ρ) (h := h) hn2 (fun ν z h1 h2 => by
        simpa using hbx 1 ν z h1 h2)]
    obtain ⟨hpl, hA⟩ := hdat l hl ρ x hx q0 q1
    have ha0c : a₀ l ≤ e := by linarith
    have ha1c : a₁ l ≤ e := by linarith
    have hClC : Cl ρ * (a₀ l + a₁ l) ≤ Clm * (a₀ l + a₁ l) :=
      mul_le_mul_of_nonneg_right (hClm ρ) (by positivity)
    refine ⟨?_, ?_, ?_⟩
    · rw [hQ1]
      refine (hlin ρ (U l) (hU l) (hn l) y (a₀ l) (a₁ l) ha0 ha1 (ha0c.trans ((hec.trans hcl').trans (hclm ρ)))
        (ha1c.trans ((hec.trans hcl').trans (hclm ρ))) hpl (A₁ l) (fun ν z hb => (hA ν z hb).1) X).trans ?_
      exact mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
    · rw [hQ2]
      refine (hlin ρ (U l) (hU l) (hn l) y (a₀ l) (a₁ l) ha0 ha1 (ha0c.trans ((hec.trans hcl').trans (hclm ρ)))
        (ha1c.trans ((hec.trans hcl').trans (hclm ρ))) hpl (A₂ l) (fun ν z hb => (hA ν z hb).2.1) X).trans ?_
      exact mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
    · rw [hQ1, hQ2]
      refine (h7 ρ (U l) (hU l) (hn l) y (a₀ l) (a₁ l) ha0 ha1 (ha0c.trans ((hec.trans hc7').trans (hc7m ρ)))
        (ha1c.trans ((hec.trans hc7').trans (hc7m ρ))) hpl (A₁ l) (A₂ l) (fun ν z hb => (hA ν z hb).1)
        (fun ν z hb => (hA ν z hb).2.1) X).trans ?_
      have hd : ‖restrictF (A₁ l - A₂ l) (InBoxB y h ρ)‖ ≤ k * (Lr ^ (nl - l))⁻¹ :=
        norm_restrictF_box_le (by have := hp1 (nl - l); positivity) fun ν z hb => by
          simpa only [Pi.sub_apply] using (hA ν z hb).2.2
      exact mul_le_mul_of_nonneg_right (mul_le_mul (hC7m ρ) hd (norm_nonneg _) hC7m0) (norm_nonneg _)
  -- the growth of `D₂`: `‖D₂_l‖ ≤ 2Lˡs₀`
  set yv : ℕ → ℝ := fun l => if l < nl then Clm * (a₀ l + a₁ l) else 0 with hyv
  have hyv0 : ∀ l, 0 ≤ yv l := fun l => by
    simp only [hyv]; split_ifs with hl
    · obtain ⟨h1, h2, -⟩ := ha l hl; positivity
    · exact le_rfl
  set S : ℕ → ℝ := fun l => s₀ * ∏ m ∈ Finset.range l, (Lr + yv m) with hS
  have hS0 : ∀ l, 0 ≤ S l := fun l => mul_nonneg hs₀ (Finset.prod_nonneg fun m _ => by have := hyv0 m; positivity)
  have hDS : ∀ l, l ≤ nl → ∀ ν x, Lat (Lz h) l x → Rg h nl μ l x → Rg h nl μ l (x + Lz h ^ l • Pi.single ν 1) →
      ‖D₂ l ν (img h (base l) l x)‖ ≤ S l := by
    intro l
    induction l with
    | zero => intro _ ν x hx q0 q1; simpa [hS] using (h0 ν x hx q0 q1).2
    | succ l ih =>
      intro hl ρ x hx q0 q1
      have hll : l < nl := by omega
      have hR : ‖restrictF (D₂ l) (InBoxB (img h (base l) l x) h ρ)‖ ≤ S l := by
        refine norm_restrictF_box_le (hS0 l) fun ν z hb => ?_
        obtain ⟨x', hx', r0, r1, rfl⟩ := box_site (hn l) (base l) hx q0 q1 hb
        exact ih hll.le ν x' hx' r0 r1
      obtain ⟨-, h2, -⟩ := hone l hll ρ x hx q0 q1 (D₂ l)
      rw [(hDD l hll ρ x hx q0 q1).2]
      have hyl : yv l = Clm * (a₀ l + a₁ l) := by simp only [hyv, if_pos hll]
      have hSl : S (l + 1) = (Lr + yv l) * S l := by simp only [hS, Finset.prod_range_succ]; ring
      rw [hSl, hyl]
      obtain ⟨ha0, ha1, -⟩ := ha l hll
      exact h2.trans (mul_le_mul_of_nonneg_left hR (by positivity))
  have hsum : ∑ l ∈ Finset.range nl, yv l ≤ Clm * e / 2 := by
    have hg := geom_partial hL3 nl nl le_rfl
    simp only [Nat.sub_self, pow_zero, _root_.inv_one, mul_one] at hg
    calc ∑ l ∈ Finset.range nl, yv l ≤ ∑ l ∈ Finset.range nl, Clm * e * (Lr ^ (nl - l))⁻¹ :=
          Finset.sum_le_sum fun l hl => by
            have hl' := Finset.mem_range.1 hl
            simp only [hyv, if_pos hl']
            have := (ha l hl').2.2
            nlinarith [mul_le_mul_of_nonneg_left this hClm0]
      _ = Clm * e * ∑ l ∈ Finset.range nl, (Lr ^ (nl - l))⁻¹ := by rw [Finset.mul_sum]
      _ ≤ Clm * e * (1 / 2) := mul_le_mul_of_nonneg_left hg (by positivity)
      _ = _ := by ring
  have hS2 : ∀ l, l ≤ nl → S l ≤ 2 * Lr ^ l * s₀ := fun l hl => by
    have hprod := prod_le_exp hL0 zero_le_one yv hyv0 l
    simp only [one_mul] at hprod
    have hs : ∑ m ∈ Finset.range l, yv m ≤ ∑ m ∈ Finset.range nl, yv m :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hl) fun m _ _ => hyv0 m
    have hy0 : 0 ≤ (∑ m ∈ Finset.range l, yv m) / Lr := div_nonneg (Finset.sum_nonneg fun m _ => hyv0 m) hL0.le
    have hy1 : (∑ m ∈ Finset.range l, yv m) / Lr ≤ 1 / 2 := by
      rw [div_le_iff₀ hL0]; nlinarith
    have hexp := GroupMean.exp_small_le hy0 (hy1.trans (by norm_num))
    calc S l = s₀ * ∏ m ∈ Finset.range l, (Lr + yv m) := rfl
      _ ≤ s₀ * (Lr ^ l * 2) := mul_le_mul_of_nonneg_left
          (hprod.trans (mul_le_mul_of_nonneg_left (by linarith) (by positivity))) hs₀
      _ = 2 * Lr ^ l * s₀ := by ring
  -- the difference: `‖D₁_l - D₂_l‖ ≤ (4C₇k/L)Lˡσ_ls₀`
  set M := 4 * C7m * k / Lr with hM
  have hM0 : 0 ≤ M := by positivity
  have hMr : ∀ l, l ≤ nl → ∀ ν x, Lat (Lz h) l x → Rg h nl μ l x → Rg h nl μ l (x + Lz h ^ l • Pi.single ν 1) →
      ‖D₁ l ν (img h (base l) l x) - D₂ l ν (img h (base l) l x)‖ ≤
        M * Lr ^ l * (∑ m ∈ Finset.range l, (Lr ^ (nl - m))⁻¹) * s₀ := by
    intro l
    induction l with
    | zero => intro _ ν x hx q0 q1; rw [(h0 ν x hx q0 q1).1, sub_self, norm_zero]; simp
    | succ l ih =>
      intro hl ρ x hx q0 q1
      have hll : l < nl := by omega
      set ql := (Lr ^ (nl - l))⁻¹
      set σ := ∑ m ∈ Finset.range l, (Lr ^ (nl - m))⁻¹
      have hσ0 : 0 ≤ σ := Finset.sum_nonneg fun m _ => by positivity
      have hσ12 : σ ≤ 1 / 2 := (geom_partial hL3 nl l hll.le).trans (by have := hp1 (nl - l); nlinarith)
      have hql0 : 0 ≤ ql := by positivity
      obtain ⟨ha0, ha1, ha2⟩ := ha l hll
      have hRr : ‖restrictF (D₁ l - D₂ l) (InBoxB (img h (base l) l x) h ρ)‖ ≤ M * Lr ^ l * σ * s₀ := by
        refine norm_restrictF_box_le (by positivity) fun ν z hb => ?_
        obtain ⟨x', hx', r0, r1, rfl⟩ := box_site (hn l) (base l) hx q0 q1 hb
        simpa only [Pi.sub_apply] using ih hll.le ν x' hx' r0 r1
      have hR2 : ‖restrictF (D₂ l) (InBoxB (img h (base l) l x) h ρ)‖ ≤ 2 * Lr ^ l * s₀ := by
        refine norm_restrictF_box_le (by positivity) fun ν z hb => ?_
        obtain ⟨x', hx', r0, r1, rfl⟩ := box_site (hn l) (base l) hx q0 q1 hb
        exact (hDS l hll.le ν x' hx' r0 r1).trans (hS2 l hll.le)
      obtain ⟨h1, -, -⟩ := hone l hll ρ x hx q0 q1 (D₁ l - D₂ l)
      obtain ⟨-, -, h3⟩ := hone l hll ρ x hx q0 q1 (D₂ l)
      rw [(hDD l hll ρ x hx q0 q1).1, (hDD l hll ρ x hx q0 q1).2]
      have heqn : ((2 * h + 1 : ℕ) : ℂ) • Qlin (V₁ l) (img h (base l) l x) ρ h (D₁ l) -
          ((2 * h + 1 : ℕ) : ℂ) • Qlin (V₂ l) (img h (base l) l x) ρ h (D₂ l) =
          ((2 * h + 1 : ℕ) : ℂ) • Qlin (V₁ l) (img h (base l) l x) ρ h (D₁ l - D₂ l) +
          (((2 * h + 1 : ℕ) : ℂ) • Qlin (V₁ l) (img h (base l) l x) ρ h (D₂ l) -
            ((2 * h + 1 : ℕ) : ℂ) • Qlin (V₂ l) (img h (base l) l x) ρ h (D₂ l)) := by
        rw [map_sub, smul_sub]; abel
      rw [heqn, Finset.sum_range_succ, pow_succ]
      have hae : a₀ l + a₁ l ≤ e * ql := ha2
      have hkey : Clm * (a₀ l + a₁ l) * (M * σ) ≤ 2 * C7m * k * ql := by
        calc Clm * (a₀ l + a₁ l) * (M * σ) ≤ Clm * (e * ql) * (M * (1 / 2)) :=
              mul_le_mul (mul_le_mul_of_nonneg_left hae hClm0) (mul_le_mul_of_nonneg_left hσ12 hM0)
                (mul_nonneg hM0 hσ0) (by positivity)
          _ = (Clm * e) * (2 * C7m * k * ql) / Lr := by rw [hM]; field_simp; ring
          _ ≤ 1 * (2 * C7m * k * ql) / Lr :=
              div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hCe (by positivity)) hL0.le
          _ ≤ 2 * C7m * k * ql := by
              rw [one_mul, div_le_iff₀ hL0]
              nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hC7m0 hk) hql0) (show (0 : ℝ) ≤ 2 by norm_num)]
      have hMLr : M * Lr = 4 * C7m * k := by rw [hM]; field_simp
      have hLl : 0 ≤ Lr ^ l := by positivity
      calc ‖((2 * h + 1 : ℕ) : ℂ) • Qlin (V₁ l) (img h (base l) l x) ρ h (D₁ l - D₂ l) +
            (((2 * h + 1 : ℕ) : ℂ) • Qlin (V₁ l) (img h (base l) l x) ρ h (D₂ l) -
              ((2 * h + 1 : ℕ) : ℂ) • Qlin (V₂ l) (img h (base l) l x) ρ h (D₂ l))‖
          ≤ (Lr + Clm * (a₀ l + a₁ l)) * (M * Lr ^ l * σ * s₀) + C7m * (k * ql) * (2 * Lr ^ l * s₀) :=
            (norm_add_le _ _).trans (add_le_add (h1.trans (mul_le_mul_of_nonneg_left hRr (by positivity)))
              (h3.trans (mul_le_mul_of_nonneg_left hR2 (by positivity))))
        _ = Lr ^ l * s₀ * (M * Lr * σ + Clm * (a₀ l + a₁ l) * (M * σ) + 2 * C7m * k * ql) := by ring
        _ ≤ Lr ^ l * s₀ * (M * Lr * σ + 4 * C7m * k * ql) := by
            have : 0 ≤ Lr ^ l * s₀ := by positivity
            nlinarith
        _ = M * (Lr ^ l * Lr) * (σ + ql) * s₀ := by rw [← hMLr]; ring
  intro ν x hx q0 q1
  refine (hMr nl le_rfl ν x hx q0 q1).trans ?_
  have hg := geom_partial hL3 nl nl le_rfl
  simp only [Nat.sub_self, pow_zero, _root_.inv_one, mul_one] at hg
  calc M * Lr ^ nl * (∑ m ∈ Finset.range nl, (Lr ^ (nl - m))⁻¹) * s₀ ≤ M * Lr ^ nl * (1 / 2) * s₀ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hg (by positivity)) hs₀
    _ = 2 * C7m * k * (Lr ^ nl / Lr) * s₀ := by rw [hM]; field_simp; ring


/-- **(vii) for `Q'` at both ends of the bond, with the norm of `λ` over the block**:
`‖(Q'(e^{iaA'₁}U) - Q'(e^{iaA'₂}U))λ(c_±)‖ ≤ C‖a(A'₁ - A'₂)‖_{∞,box}‖λ‖_{∞,B(c_±)}`. -/
theorem blockAvg_step_lip (h : ℕ) (μ : Fin 4) :
    ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧
      ∀ {n : ℕ} [NeZero n] (U : Config N n), U.IsGaugeField → 4 * h + 4 ≤ n → ∀ (y : Site n)
        [DecidablePred (InBoxB y h μ)] (α₀ α₁ : ℝ), 0 ≤ α₀ → 0 ≤ α₁ → α₀ ≤ c → α₁ ≤ c →
        (∀ μ' ν' z, PlaqIn (boxR y (loD h) (hiD h μ μ)) μ' ν' z →
          hs (((plaq U μ' ν' z : GLN) : Mat) - 1) ≤ α₀) →
        ∀ A'₁ A'₂ : Fin 4 → Site n → Mat, (∀ ρ z, BoxBond y h μ ρ z → ‖A'₁ ρ z‖ ≤ α₁) →
        (∀ ρ z, BoxBond y h μ ρ z → ‖A'₂ ρ z‖ ≤ α₁) →
        ∀ (b : Bool) (lam : Site n → Mat) (s : ℝ), 0 ≤ s → (∀ z, Bm (ofs y (endW h μ b)) h z → ‖lam z‖ ≤ s) →
          ‖blockAvg (moveC U A'₁) lam (ofs y (endW h μ b)) h - blockAvg (moveC U A'₂) lam (ofs y (endW h μ b)) h‖ ≤
            C * ‖restrictF (A'₁ - A'₂) (InBoxB y h μ)‖ * s := by
  obtain ⟨ci, hci, hpol⟩ := uniform_polydisc (N := N) h μ
  obtain ⟨r, C, hr, hC, hlip⟩ := uniform_blockAvg_lip (N := N) h μ
  set K := redK N h
  have hK4 : 4 ≤ K := four_le_redK N h
  have hKpos : 0 < K := by linarith
  set m := min ci r with hm
  have hm0 : 0 < m := lt_min hci hr
  set c := min (m / (2 * K)) (1 / (8 * K)) with hc_def
  have hc1 : c ≤ m / (2 * K) := min_le_left _ _
  have hc2 : c ≤ 1 / (8 * K) := min_le_right _ _
  refine ⟨c, 24 * C, by positivity, by positivity, ?_⟩
  intro n _ U hU hn y _ α₀ α₁ hα₀ hα₁ hα₀c hα₁c hplq A'₁ A'₂ hA₁ hA₂ b lam s hs0 hls
  classical
  obtain ⟨X₁, hX1c, -, hag₁, hl₁, hz₁⟩ := reduce_box_supp hU hn y μ hα₀ hα₁ hα₀c hα₁c hc2 hplq A'₁ hA₁
  obtain ⟨X₂, hX2c, -, hag₂, hl₂, hz₂⟩ := reduce_box_supp hU hn y μ hα₀ hα₁ hα₀c hα₁c hc2 hplq A'₂ hA₂
  have hKc : K * c ≤ m / 2 := by
    calc K * c ≤ K * (m / (2 * K)) := mul_le_mul_of_nonneg_left hc1 hKpos.le
      _ = m / 2 := by field_simp
  have hK8 : K * c ≤ 1 / 8 := by
    calc K * c ≤ K * (1 / (8 * K)) := mul_le_mul_of_nonneg_left hc2 hKpos.le
      _ = 1 / 8 := by field_simp
  have hmci : m ≤ ci := min_le_left _ _
  have hmr : m ≤ r := min_le_right _ _
  have hn2 : 4 * h + 2 ≤ n := by omega
  have hc8 : c ≤ 1 / 8 := hc2.trans (by rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith)
  have hgood : ∀ X : Fin 4 → Site n → Mat, ‖X‖ ≤ K * c → GoodAt (UX (N := N) X) (ofs y (endW h μ b)) h :=
    fun X hX => by
      have hcond := hpol y X 0 (by linarith) (by rw [norm_zero]; exact hci)
      cases b
      · simpa only [endW, Bool.false_eq_true, ↓reduceIte, ofs_zero] using hcond.g0
      · exact hcond.g1
  have hu : ∀ z, ((uG U y h z : GLN) : Mat) ∈ unitaryGroup (Fin N) ℂ := fun z => hol_unitary' U hU _
  rw [blockAvg_reduce_end hn b hag₁ hU (hgood X₁ hX1c), blockAvg_reduce_end hn b hag₂ hU (hgood X₂ hX2c),
    ← Ad_sub, SupportCont.opNorm_Ad_unitary (SupportCont.unitary_inv (hu _))]
  set z₀ := ofs y (endW h μ b)
  set lamR : Site n → Mat := fun z => if Bm z₀ h z then Ad (uG U y h z) (lam z) else 0 with hlamR
  have hR : ∀ V : Config N n, blockAvg V (fun z => Ad (uG U y h z) (lam z)) z₀ h = blockAvg V lamR z₀ h :=
    fun V => by
      simp only [blockAvg, hlamR]
      congr 1
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [if_pos (bm_ofs hn2 (offP_inM h x))]
  have hlamRn : ‖lamR‖ ≤ s := (pi_norm_le_iff_of_nonneg hs0).2 fun z => by
    simp only [hlamR]
    split_ifs with hz
    · rw [SupportCont.opNorm_Ad_unitary (hu z)]; exact hls z hz
    · rw [norm_zero]; exact hs0
  rw [hR, hR]
  have hl := hlip z₀ lamR X₁ X₂ (by linarith) (by linarith)
  have hXl := X_lip hU y μ (fun ρ z hb => (hA₁ ρ z hb).trans (hα₁c.trans hc8))
    (fun ρ z hb => (hA₂ ρ z hb).trans (hα₁c.trans hc8)) (by linarith) (by linarith) hag₁ hag₂ hl₁ hl₂ hz₁ hz₂
  calc ‖blockAvg (UX (N := N) X₁) lamR z₀ h - blockAvg (UX (N := N) X₂) lamR z₀ h‖ ≤ C * ‖X₁ - X₂‖ * ‖lamR‖ := hl
    _ ≤ C * (24 * ‖restrictF (A'₁ - A'₂) (InBoxB y h μ)‖) * s :=
        mul_le_mul (mul_le_mul_of_nonneg_left hXl hC) hlamRn (norm_nonneg _) (by positivity)
    _ = 24 * C * ‖restrictF (A'₁ - A'₂) (InBoxB y h μ)‖ * s := by ring


set_option maxHeartbeats 4000000 in
/-- **`prop:relative-average-order`(v), the Lipschitz continuity of `Q'_n` in `a_jA'`**: for two backgrounds as in
`order_v_lip`, the block averages `λ^i_{l+1} = Q'(V^i_l)λ^i_l` with a common `λ_0`, `‖λ_0‖ ≤ s₀`, satisfy
`‖λ^1_n - λ^2_n‖ ≤ 2C'ks₀` at the sites of the last level: `‖(Q'_n(𝐔¹) - Q'_n(𝐔²))λ‖ ≤ 2C'k‖λ‖_∞`. -/
theorem order_v_lip_Q' (h : ℕ) (hh : 1 ≤ h) :
    ∃ c C C' : ℝ, 0 < c ∧ 0 ≤ C ∧ 0 ≤ C' ∧ ∀ (nl : ℕ) (μ : Fin 4) (nn : ℕ → ℕ) [∀ l, NeZero (nn l)],
      (∀ l, 4 * h + 4 ≤ nn l) → ∀ (base : ∀ l, Site (nn l)) (U V₁ V₂ : ∀ l, Config N (nn l))
      (A₁ A₂ : ∀ l, Fin 4 → Site (nn l) → Mat) (lam₁ lam₂ : ∀ l, Site (nn l) → Mat) (a₀ a₁ : ℕ → ℝ) (e k s₀ : ℝ),
      (∀ l, U l |>.IsGaugeField) →
      (∀ l, l < nl → ∀ ν x, Lat (Lz h) l x → Rg h nl μ l x → Rg h nl μ l (x + Lz h ^ l • Pi.single ν 1) →
        V₁ l ν (img h (base l) l x) = moveC (U l) (A₁ l) ν (img h (base l) l x) ∧
        V₂ l ν (img h (base l) l x) = moveC (U l) (A₂ l) ν (img h (base l) l x)) →
      (∀ l, l < nl → ∀ ρ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x →
        Rg h nl μ (l + 1) (x + Lz h ^ (l + 1) • Pi.single ρ 1) →
        (∀ μ' ν' z, PlaqIn (boxR (img h (base l) l x) (loD h) (hiD h ρ ρ)) μ' ν' z →
          hs (((plaq (U l) μ' ν' z : GLN) : Mat) - 1) ≤ a₀ l) ∧
        (∀ ν z, BoxBond (img h (base l) l x) h ρ ν z → ‖A₁ l ν z‖ ≤ a₁ l ∧ ‖A₂ l ν z‖ ≤ a₁ l ∧
          ‖A₁ l ν z - A₂ l ν z‖ ≤ k * ((((2 * h + 1 : ℕ) : ℝ)) ^ (nl - l))⁻¹)) →
      (∀ l, l < nl → 0 ≤ a₀ l ∧ 0 ≤ a₁ l ∧ a₀ l + a₁ l ≤ e * ((((2 * h + 1 : ℕ) : ℝ)) ^ (nl - l))⁻¹) →
      (∀ l, l < nl → ∀ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x →
        lam₁ (l + 1) (img h (base (l + 1)) (l + 1) x) = blockAvg (V₁ l) (lam₁ l) (img h (base l) l x) h ∧
        lam₂ (l + 1) (img h (base (l + 1)) (l + 1) x) = blockAvg (V₂ l) (lam₂ l) (img h (base l) l x) h) →
      0 ≤ e → 0 ≤ k → 0 ≤ s₀ → e ≤ c → C * e ≤ 1 →
      (∀ x, Lat (Lz h) 0 x → Rg h nl μ 0 x →
        lam₁ 0 (img h (base 0) 0 x) = lam₂ 0 (img h (base 0) 0 x) ∧ ‖lam₂ 0 (img h (base 0) 0 x)‖ ≤ s₀) →
      ∀ x, Lat (Lz h) nl x → Rg h nl μ nl x →
        ‖lam₁ nl (img h (base nl) nl x) - lam₂ nl (img h (base nl) nl x)‖ ≤ 2 * C' * k * s₀ := by
  classical
  choose cs Cs hcs hCs hstep using fun ρ : Fin 4 => blockAvg_step (N := N) h ρ
  choose cq Cq hcq hCq hlip using fun ρ : Fin 4 => blockAvg_step_lip (N := N) h ρ
  set csm := Finset.univ.inf' Finset.univ_nonempty cs
  set cqm := Finset.univ.inf' Finset.univ_nonempty cq
  set Csm := Finset.univ.sup' Finset.univ_nonempty Cs
  set Cqm := Finset.univ.sup' Finset.univ_nonempty Cq
  have hcsm : ∀ ρ, csm ≤ cs ρ := fun ρ => Finset.inf'_le _ (Finset.mem_univ ρ)
  have hcqm : ∀ ρ, cqm ≤ cq ρ := fun ρ => Finset.inf'_le _ (Finset.mem_univ ρ)
  have hCsm : ∀ ρ, Cs ρ ≤ Csm := fun ρ => Finset.le_sup' _ (Finset.mem_univ ρ)
  have hCqm : ∀ ρ, Cq ρ ≤ Cqm := fun ρ => Finset.le_sup' _ (Finset.mem_univ ρ)
  have hcsm0 : 0 < csm := (Finset.lt_inf'_iff _).2 fun ρ _ => hcs ρ
  have hcqm0 : 0 < cqm := (Finset.lt_inf'_iff _).2 fun ρ _ => hcq ρ
  have hCsm0 : 0 ≤ Csm := (hCs 0).trans (hCsm 0)
  have hCqm0 : 0 ≤ Cqm := (hCq 0).trans (hCqm 0)
  refine ⟨min csm cqm, Csm, Cqm, lt_min hcsm0 hcqm0, hCsm0, hCqm0, ?_⟩
  intro nl μ nn _ hn base U V₁ V₂ A₁ A₂ lam₁ lam₂ a₀ a₁ e k s₀ hU hVV hdat ha hrel he hk hs₀ hec hCe h0
  have hcs' : min csm cqm ≤ csm := min_le_left _ _
  have hcq' : min csm cqm ≤ cqm := min_le_right _ _
  set Lr : ℝ := ((2 * h + 1 : ℕ) : ℝ) with hLr
  have hL3 : 3 ≤ Lr := by rw [hLr]; push_cast; have : (1 : ℝ) ≤ h := by exact_mod_cast hh
                          linarith
  have hp1 : ∀ m, (Lr ^ m)⁻¹ ≤ 1 := fun m => inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith))
  -- the reduction of a site of the level `l + 1` to an end of a bond, with the data of the two backgrounds
  have hsite : ∀ l, l < nl → ∀ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x →
      ∃ x' b, Lat (Lz h) (l + 1) x' ∧ Rg h nl μ (l + 1) x' ∧
        Rg h nl μ (l + 1) (x' + Lz h ^ (l + 1) • Pi.single μ 1) ∧
        img h (base l) l x = ofs (img h (base l) l x') (endW h μ b) := fun l hl x hx hR =>
    rg_end_img (base l) hl hx hR
  have hloc : ∀ l, l < nl → ∀ (x' : Fin 4 → ℤ) (b : Bool), Lat (Lz h) (l + 1) x' → Rg h nl μ (l + 1) x' →
      Rg h nl μ (l + 1) (x' + Lz h ^ (l + 1) • Pi.single μ 1) → ∀ lam : Site (nn l) → Mat,
      blockAvg (V₁ l) lam (ofs (img h (base l) l x') (endW h μ b)) h =
        blockAvg (moveC (U l) (A₁ l)) lam (ofs (img h (base l) l x') (endW h μ b)) h ∧
      blockAvg (V₂ l) lam (ofs (img h (base l) l x') (endW h μ b)) h =
        blockAvg (moveC (U l) (A₂ l)) lam (ofs (img h (base l) l x') (endW h μ b)) h := by
    intro l hl x' b hx' r0 r1 lam
    have hn2 : 4 * h + 2 ≤ nn l := by have := hn l; omega
    have hbb : ∀ ν z, Bm (ofs (img h (base l) l x') (endW h μ b)) h z →
        Bm (ofs (img h (base l) l x') (endW h μ b)) h (z + unit (nn l) ν) →
        V₁ l ν z = moveC (U l) (A₁ l) ν z ∧ V₂ l ν z = moveC (U l) (A₂ l) ν z := fun ν z h1 h2 => by
      obtain ⟨x'', hx'', s0, s1, rfl⟩ := box_site (hn l) (base l) hx' r0 r1 (boxBond_of_end hn2 b h1 h2)
      exact hVV l hl ν x'' hx'' s0 s1
    constructor
    · have ht := trans_local (V := V₁ l) (V' := moveC (U l) (A₁ l)) hn2
        (y := ofs (img h (base l) l x') (endW h μ b)) (h := h) fun ν z h1 h2 => (hbb ν z h1 h2).1
      simp only [blockAvg, ht]
    · have ht := trans_local (V := V₂ l) (V' := moveC (U l) (A₂ l)) hn2
        (y := ofs (img h (base l) l x') (endW h μ b)) (h := h) fun ν z h1 h2 => (hbb ν z h1 h2).2
      simp only [blockAvg, ht]
  -- the growth of `λ₂`: `‖λ₂_l‖ ≤ 2s₀`
  set yv : ℕ → ℝ := fun l => if l < nl then Csm * (a₀ l + a₁ l) else 0 with hyv
  have hyv0 : ∀ l, 0 ≤ yv l := fun l => by
    simp only [hyv]; split_ifs with hl
    · obtain ⟨h1, h2, -⟩ := ha l hl; positivity
    · exact le_rfl
  set S : ℕ → ℝ := fun l => s₀ * ∏ m ∈ Finset.range l, (1 + yv m) with hS
  have hS0 : ∀ l, 0 ≤ S l := fun l => mul_nonneg hs₀ (Finset.prod_nonneg fun m _ => by have := hyv0 m; positivity)
  have hlamS : ∀ l, l ≤ nl → ∀ x, Lat (Lz h) l x → Rg h nl μ l x → ‖lam₂ l (img h (base l) l x)‖ ≤ S l := by
    intro l
    induction l with
    | zero => intro _ x hx hR; simpa [hS] using (h0 x hx hR).2
    | succ l ih =>
      intro hl x hx hR
      have hll : l < nl := by omega
      have hn2 : 4 * h + 2 ≤ nn l := by have := hn l; omega
      obtain ⟨x', b, hx', r0, r1, hb⟩ := hsite l hll x hx hR
      obtain ⟨hpl, hA⟩ := hdat l hll μ x' hx' r0 r1
      obtain ⟨ha0, ha1, ha2⟩ := ha l hll
      have hae : a₀ l + a₁ l ≤ e := by have := hp1 (nl - l); nlinarith
      have hlb : ∀ z, Bm (ofs (img h (base l) l x') (endW h μ b)) h z → ‖lam₂ l z‖ ≤ S l := fun z hz => by
        obtain ⟨x'', hx'', s0, rfl⟩ := box_pt (base l) hx' r0 r1 (bmp_of_end hn2 b hz)
        exact ih hll.le x'' hx'' s0
      rw [(hrel l hll x hx hR).2, hb, (hloc l hll x' b hx' r0 r1 _).2]
      have hyl : yv l = Csm * (a₀ l + a₁ l) := by simp only [hyv, if_pos hll]
      have hSl : S (l + 1) = (1 + yv l) * S l := by simp only [hS, Finset.prod_range_succ]; ring
      rw [hSl, hyl]
      refine (hstep μ (U l) (hU l) (hn l) _ (a₀ l) (a₁ l) ha0 ha1
        ((by linarith : a₀ l ≤ e).trans ((hec.trans hcs').trans (hcsm μ)))
        ((by linarith : a₁ l ≤ e).trans ((hec.trans hcs').trans (hcsm μ))) hpl (A₂ l)
        (fun ν z hb => (hA ν z hb).2.1) b (lam₂ l) (S l) (hS0 l) hlb).trans ?_
      have : Cs μ * (a₀ l + a₁ l) ≤ Csm * (a₀ l + a₁ l) := mul_le_mul_of_nonneg_right (hCsm μ) (by positivity)
      exact mul_le_mul_of_nonneg_right (by linarith) (hS0 l)
  have hsum : ∑ l ∈ Finset.range nl, yv l ≤ Csm * e / 2 := by
    have hg := geom_partial hL3 nl nl le_rfl
    simp only [Nat.sub_self, pow_zero, _root_.inv_one, mul_one] at hg
    calc ∑ l ∈ Finset.range nl, yv l ≤ ∑ l ∈ Finset.range nl, Csm * e * (Lr ^ (nl - l))⁻¹ :=
          Finset.sum_le_sum fun l hl => by
            have hl' := Finset.mem_range.1 hl
            simp only [hyv, if_pos hl']
            have := (ha l hl').2.2
            nlinarith [mul_le_mul_of_nonneg_left this hCsm0]
      _ = Csm * e * ∑ l ∈ Finset.range nl, (Lr ^ (nl - l))⁻¹ := by rw [Finset.mul_sum]
      _ ≤ Csm * e * (1 / 2) := mul_le_mul_of_nonneg_left hg (by positivity)
      _ = _ := by ring
  have hS2 : ∀ l, l ≤ nl → S l ≤ 2 * s₀ := fun l hl => by
    have hprod := prod_le_exp one_pos zero_le_one yv hyv0 l
    simp only [one_mul, one_pow, div_one] at hprod
    have hs : ∑ m ∈ Finset.range l, yv m ≤ ∑ m ∈ Finset.range nl, yv m :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hl) fun m _ _ => hyv0 m
    have hy0 : 0 ≤ ∑ m ∈ Finset.range l, yv m := Finset.sum_nonneg fun m _ => hyv0 m
    have hy1 : ∑ m ∈ Finset.range l, yv m ≤ 1 / 2 := by nlinarith
    have hexp := GroupMean.exp_small_le hy0 (hy1.trans (by norm_num))
    calc S l = s₀ * ∏ m ∈ Finset.range l, (1 + yv m) := rfl
      _ ≤ s₀ * 2 := mul_le_mul_of_nonneg_left (hprod.trans (by linarith)) hs₀
      _ = 2 * s₀ := by ring
  -- the difference: `‖λ₁_l - λ₂_l‖ ≤ 4C'kσ_ls₀`
  set M := 4 * Cqm * k with hM
  have hM0 : 0 ≤ M := by positivity
  have hMr : ∀ l, l ≤ nl → ∀ x, Lat (Lz h) l x → Rg h nl μ l x →
      ‖lam₁ l (img h (base l) l x) - lam₂ l (img h (base l) l x)‖ ≤
        M * (∑ m ∈ Finset.range l, (Lr ^ (nl - m))⁻¹) * s₀ := by
    intro l
    induction l with
    | zero => intro _ x hx hR; rw [(h0 x hx hR).1, sub_self, norm_zero]; simp
    | succ l ih =>
      intro hl x hx hR
      have hll : l < nl := by omega
      have hn2 : 4 * h + 2 ≤ nn l := by have := hn l; omega
      set ql := (Lr ^ (nl - l))⁻¹
      set σ := ∑ m ∈ Finset.range l, (Lr ^ (nl - m))⁻¹
      have hσ0 : 0 ≤ σ := Finset.sum_nonneg fun m _ => by positivity
      have hσ12 : σ ≤ 1 / 2 := (geom_partial hL3 nl l hll.le).trans (by have := hp1 (nl - l); nlinarith)
      have hql0 : 0 ≤ ql := by positivity
      obtain ⟨x', b, hx', r0, r1, hb⟩ := hsite l hll x hx hR
      obtain ⟨hpl, hA⟩ := hdat l hll μ x' hx' r0 r1
      obtain ⟨ha0, ha1, ha2⟩ := ha l hll
      have hae : a₀ l + a₁ l ≤ e := by have := hp1 (nl - l); nlinarith
      set z₀ := ofs (img h (base l) l x') (endW h μ b)
      have hlb1 : ∀ z, Bm z₀ h z → ‖(lam₁ l - lam₂ l) z‖ ≤ M * σ * s₀ := fun z hz => by
        obtain ⟨x'', hx'', s0, rfl⟩ := box_pt (base l) hx' r0 r1 (bmp_of_end hn2 b hz)
        simpa only [Pi.sub_apply] using ih hll.le x'' hx'' s0
      have hlb2 : ∀ z, Bm z₀ h z → ‖lam₂ l z‖ ≤ 2 * s₀ := fun z hz => by
        obtain ⟨x'', hx'', s0, rfl⟩ := box_pt (base l) hx' r0 r1 (bmp_of_end hn2 b hz)
        exact (hlamS l hll.le x'' hx'' s0).trans (hS2 l hll.le)
      obtain ⟨e1, e2⟩ := hloc l hll x' b hx' r0 r1 (lam₁ l)
      obtain ⟨-, e3⟩ := hloc l hll x' b hx' r0 r1 (lam₂ l)
      obtain ⟨e4, -⟩ := hloc l hll x' b hx' r0 r1 (lam₂ l)
      rw [(hrel l hll x hx hR).1, (hrel l hll x hx hR).2, hb, e1, e3]
      -- `Q'(𝐔¹)λ₁ - Q'(𝐔²)λ₂ = Q'(𝐔¹)(λ₁ - λ₂) + (Q'(𝐔¹) - Q'(𝐔²))λ₂`
      have hlinb : blockAvg (moveC (U l) (A₁ l)) (lam₁ l) z₀ h - blockAvg (moveC (U l) (A₂ l)) (lam₂ l) z₀ h =
          blockAvg (moveC (U l) (A₁ l)) (lam₁ l - lam₂ l) z₀ h +
            (blockAvg (moveC (U l) (A₁ l)) (lam₂ l) z₀ h - blockAvg (moveC (U l) (A₂ l)) (lam₂ l) z₀ h) := by
        simp only [blockAvg, Pi.sub_apply, Ad_sub, Finset.sum_sub_distrib, smul_sub]
        abel
      rw [hlinb]
      have hs1 := hstep μ (U l) (hU l) (hn l) _ (a₀ l) (a₁ l) ha0 ha1
        ((by linarith : a₀ l ≤ e).trans ((hec.trans hcs').trans (hcsm μ)))
        ((by linarith : a₁ l ≤ e).trans ((hec.trans hcs').trans (hcsm μ))) hpl (A₁ l)
        (fun ν z hb => (hA ν z hb).1) b (lam₁ l - lam₂ l) (M * σ * s₀) (by positivity) hlb1
      have hs2 := hlip μ (U l) (hU l) (hn l) _ (a₀ l) (a₁ l) ha0 ha1
        ((by linarith : a₀ l ≤ e).trans ((hec.trans hcq').trans (hcqm μ)))
        ((by linarith : a₁ l ≤ e).trans ((hec.trans hcq').trans (hcqm μ))) hpl (A₁ l) (A₂ l)
        (fun ν z hb => (hA ν z hb).1) (fun ν z hb => (hA ν z hb).2.1) b (lam₂ l) (2 * s₀) (by positivity) hlb2
      have hd : ‖restrictF (A₁ l - A₂ l) (InBoxB (img h (base l) l x') h μ)‖ ≤ k * ql :=
        norm_restrictF_box_le (by positivity) fun ν z hb => by
          simpa only [Pi.sub_apply] using (hA ν z hb).2.2
      rw [Finset.sum_range_succ]
      have hkey : Csm * (a₀ l + a₁ l) * (M * σ) ≤ 2 * Cqm * k * ql := by
        calc Csm * (a₀ l + a₁ l) * (M * σ) ≤ Csm * (e * ql) * (M * (1 / 2)) :=
              mul_le_mul (mul_le_mul_of_nonneg_left ha2 hCsm0) (mul_le_mul_of_nonneg_left hσ12 hM0)
                (mul_nonneg hM0 hσ0) (by positivity)
          _ = (Csm * e) * (2 * Cqm * k * ql) := by rw [hM]; ring
          _ ≤ 1 * (2 * Cqm * k * ql) := mul_le_mul_of_nonneg_right hCe (by positivity)
          _ = 2 * Cqm * k * ql := one_mul _
      have hCsC : Cs μ * (a₀ l + a₁ l) ≤ Csm * (a₀ l + a₁ l) := mul_le_mul_of_nonneg_right (hCsm μ) (by positivity)
      have hCqC : Cq μ * ‖restrictF (A₁ l - A₂ l) (InBoxB (img h (base l) l x') h μ)‖ ≤ Cqm * (k * ql) :=
        mul_le_mul (hCqm μ) hd (norm_nonneg _) hCqm0
      calc ‖blockAvg (moveC (U l) (A₁ l)) (lam₁ l - lam₂ l) z₀ h +
            (blockAvg (moveC (U l) (A₁ l)) (lam₂ l) z₀ h - blockAvg (moveC (U l) (A₂ l)) (lam₂ l) z₀ h)‖
          ≤ (1 + Csm * (a₀ l + a₁ l)) * (M * σ * s₀) + Cqm * (k * ql) * (2 * s₀) :=
            (norm_add_le _ _).trans (add_le_add (hs1.trans (mul_le_mul_of_nonneg_right (by linarith)
              (by positivity))) (hs2.trans (mul_le_mul_of_nonneg_right hCqC (by positivity))))
        _ = s₀ * (M * σ + Csm * (a₀ l + a₁ l) * (M * σ) + 2 * Cqm * k * ql) := by ring
        _ ≤ s₀ * (M * σ + M * ql) := by
            have : 2 * Cqm * k * ql + 2 * Cqm * k * ql = M * ql := by rw [hM]; ring
            nlinarith
        _ = M * (σ + ql) * s₀ := by ring
  intro x hx hR
  refine (hMr nl le_rfl x hx hR).trans ?_
  have hg := geom_partial hL3 nl nl le_rfl
  simp only [Nat.sub_self, pow_zero, _root_.inv_one, mul_one] at hg
  calc M * (∑ m ∈ Finset.range nl, (Lr ^ (nl - m))⁻¹) * s₀ ≤ M * (1 / 2) * s₀ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hg hM0) hs₀
    _ = 2 * Cqm * k * s₀ := by rw [hM]; ring


/-- **Cauchy's estimate as a Lipschitz bound**: a map holomorphic on the ball of radius `R` and bounded by `K` there is
Lipschitz continuous with the constant `2K/R` on the ball of radius `R/2` (the step from the holomorphy and the bounds of
the backgrounds `A'_l` in `A'` to the hypothesis `‖A'^1_l - A'^2_l‖ ≤ kL^{-(n-l)}` of `order_v_lip`). -/
theorem lip_half_ball {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F]
    [NormedSpace ℂ F] {f : E → F} {R K : ℝ} (hR : 0 < R) (hf : DifferentiableOn ℂ f (ball 0 R))
    (hK : ∀ y ∈ ball (0 : E) R, ‖f y‖ ≤ K) {x y : E} (hx : ‖x‖ ≤ R / 2) (hy : ‖y‖ ≤ R / 2) :
    ‖f x - f y‖ ≤ 2 * K / R * ‖x - y‖ := by
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0 (mem_ball_self hR))
  have hsub : closedBall (0 : E) (R / 2) ⊆ ball 0 R := closedBall_subset_ball (by linarith)
  have hder : ∀ z ∈ closedBall (0 : E) (R / 2), ‖fderiv ℂ f z‖ ≤ 2 * K / R := fun z hz => by
    have hzb := hsub hz
    rw [mem_closedBall, dist_zero_right] at hz
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
    have := SchwarzCauchy.cauchy_fderiv hf hK hzb v
    rw [sub_zero] at this
    calc _ ≤ K * ‖v‖ / (R - ‖z‖) := this
      _ ≤ 2 * K / R * ‖v‖ := by
          rw [div_le_iff₀ (by linarith)]
          have e : 2 * K / R * ‖v‖ * (R - ‖z‖) = K * ‖v‖ * (2 * (R - ‖z‖) / R) := by field_simp
          rw [e]
          have : 1 ≤ 2 * (R - ‖z‖) / R := by rw [le_div_iff₀ hR]; linarith
          nlinarith [mul_nonneg hK0 (norm_nonneg v)]
  exact (convex_closedBall (0 : E) (R / 2)).norm_image_sub_le_of_norm_fderiv_le
    (fun z hz => hf.differentiableAt (isOpen_ball.mem_nhds (hsub hz))) hder
    (by rw [mem_closedBall, dist_zero_right]; exact hy) (by rw [mem_closedBall, dist_zero_right]; exact hx)


/-! ### Constants uniform in the direction of the bond -/

/-- **(v) and (vi) of `prop:relative-average` with constants uniform in `μ`** (a minimum and maxima over the four
directions of the constants of `relative_average_box`). -/
theorem relative_average_box_uniform (h : ℕ) :
    ∃ c C₀ C₁ C₂ C₃ : ℝ, 0 < c ∧ 0 ≤ C₀ ∧ 0 ≤ C₁ ∧ 0 ≤ C₂ ∧ 0 ≤ C₃ ∧
      ∀ (μ : Fin 4) {n : ℕ} [NeZero n] (U : Config N n), U.IsGaugeField → 4 * h + 4 ≤ n → ∀ (y : Site n)
        [DecidablePred (InBoxB y h μ)] (α₀ α₁ : ℝ), 0 ≤ α₀ → 0 ≤ α₁ → α₀ ≤ c → α₁ ≤ c →
        (∀ μ' ν' z, PlaqIn (boxR y (loD h) (hiD h μ μ)) μ' ν' z →
          hs (((plaq U μ' ν' z : GLN) : Mat) - 1) ≤ α₀) →
        ∀ A' : Fin 4 → Site n → Mat, (∀ ρ z, BoxBond y h μ ρ z → ‖A' ρ z‖ ≤ α₁) →
        ∀ B : Fin 4 → Site n → Mat,
          ‖((2 * h + 1 : ℕ) : ℂ) • Qlin (moveC U A') y μ h B - Q0L (moveC U A') y μ h B‖ ≤
            C₀ * (α₀ + α₁) * ‖restrictF B (InBoxB y h μ)‖ ∧
          ‖((2 * h + 1 : ℕ) : ℂ) • Qlin (moveC U A') y μ h B‖ ≤ C₁ * ‖restrictF B (InBoxB y h μ)‖ ∧
          (‖restrictF B (InBoxB y h μ)‖ < c →
            ‖Crem (moveC U A') B y μ h‖ ≤ C₂ * ‖restrictF B (InBoxB y h μ)‖ ^ 2 ∧
            ∀ δ, ‖fderiv ℂ (fun B' => Crem (moveC U A') B' y μ h) B δ‖ ≤
              C₃ * ‖restrictF B (InBoxB y h μ)‖ * ‖restrictF δ (InBoxB y h μ)‖) := by
  choose cb C0 C1 C2 C3 hcb hC0 hC1 hC2 hC3 hbox using fun μ : Fin 4 => relative_average_box (N := N) h μ
  set c := Finset.univ.inf' Finset.univ_nonempty cb
  set C₀ := Finset.univ.sup' Finset.univ_nonempty C0
  set C₁ := Finset.univ.sup' Finset.univ_nonempty C1
  set C₂ := Finset.univ.sup' Finset.univ_nonempty C2
  set C₃ := Finset.univ.sup' Finset.univ_nonempty C3
  have hc : ∀ μ, c ≤ cb μ := fun μ => Finset.inf'_le _ (Finset.mem_univ μ)
  have h0 : ∀ μ, C0 μ ≤ C₀ := fun μ => Finset.le_sup' _ (Finset.mem_univ μ)
  have h1 : ∀ μ, C1 μ ≤ C₁ := fun μ => Finset.le_sup' _ (Finset.mem_univ μ)
  have h2 : ∀ μ, C2 μ ≤ C₂ := fun μ => Finset.le_sup' _ (Finset.mem_univ μ)
  have h3 : ∀ μ, C3 μ ≤ C₃ := fun μ => Finset.le_sup' _ (Finset.mem_univ μ)
  refine ⟨c, C₀, C₁, C₂, C₃, (Finset.lt_inf'_iff _).2 fun μ _ => hcb μ, (hC0 0).trans (h0 0),
    (hC1 0).trans (h1 0), (hC2 0).trans (h2 0), (hC3 0).trans (h3 0), ?_⟩
  intro μ n _ U hU hn y _ α₀ α₁ hα₀ hα₁ hα₀c hα₁c hplq A' hA B
  obtain ⟨e1, e2, e3⟩ := hbox μ U hU hn y α₀ α₁ hα₀ hα₁ (hα₀c.trans (hc μ)) (hα₁c.trans (hc μ)) hplq A' hA B
  have hR := norm_nonneg (restrictF B (InBoxB y h μ))
  refine ⟨e1.trans ?_, e2.trans (mul_le_mul_of_nonneg_right (h1 μ) hR), fun hB => ?_⟩
  · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (h0 μ) (by positivity)) hR
  · obtain ⟨f1, f2⟩ := e3 (hB.trans_le (hc μ))
    refine ⟨f1.trans (mul_le_mul_of_nonneg_right (h2 μ) (by positivity)), fun δ => (f2 δ).trans ?_⟩
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (h3 μ) hR) (norm_nonneg _)

/-- **(vii) of `prop:relative-average` for `Q` with constants uniform in `μ`**. -/
theorem relative_average_vii_box_uniform (h : ℕ) :
    ∃ c C₁ : ℝ, 0 < c ∧ 0 ≤ C₁ ∧
      ∀ (μ : Fin 4) {n : ℕ} [NeZero n] (U : Config N n), U.IsGaugeField → 4 * h + 4 ≤ n → ∀ (y : Site n)
        [DecidablePred (InBoxB y h μ)] (α₀ α₁ : ℝ), 0 ≤ α₀ → 0 ≤ α₁ → α₀ ≤ c → α₁ ≤ c →
        (∀ μ' ν' z, PlaqIn (boxR y (loD h) (hiD h μ μ)) μ' ν' z →
          hs (((plaq U μ' ν' z : GLN) : Mat) - 1) ≤ α₀) →
        ∀ A'₁ A'₂ : Fin 4 → Site n → Mat, (∀ ρ z, BoxBond y h μ ρ z → ‖A'₁ ρ z‖ ≤ α₁) →
        (∀ ρ z, BoxBond y h μ ρ z → ‖A'₂ ρ z‖ ≤ α₁) → ∀ B : Fin 4 → Site n → Mat,
          ‖((2 * h + 1 : ℕ) : ℂ) • Qlin (moveC U A'₁) y μ h B - ((2 * h + 1 : ℕ) : ℂ) • Qlin (moveC U A'₂) y μ h B‖
            ≤ C₁ * ‖restrictF (A'₁ - A'₂) (InBoxB y h μ)‖ * ‖restrictF B (InBoxB y h μ)‖ := by
  choose c7 C7 hc7 hC7 h7 using fun μ : Fin 4 => relative_average_vii_box (N := N) h μ
  set c := Finset.univ.inf' Finset.univ_nonempty c7
  set C₁ := Finset.univ.sup' Finset.univ_nonempty C7
  have hc : ∀ μ, c ≤ c7 μ := fun μ => Finset.inf'_le _ (Finset.mem_univ μ)
  have hC : ∀ μ, C7 μ ≤ C₁ := fun μ => Finset.le_sup' _ (Finset.mem_univ μ)
  refine ⟨c, C₁, (Finset.lt_inf'_iff _).2 fun μ _ => hc7 μ, (hC7 0).trans (hC 0), ?_⟩
  intro μ n _ U hU hn y _ α₀ α₁ hα₀ hα₁ hα₀c hα₁c hplq A'₁ A'₂ hA₁ hA₂ B
  refine (h7 μ U hU hn y α₀ α₁ hα₀ hα₁ (hα₀c.trans (hc μ)) (hα₁c.trans (hc μ)) hplq A'₁ A'₂ hA₁ hA₂ B).trans ?_
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hC μ) (norm_nonneg _)) (norm_nonneg _)

/-- **(vi) of `prop:relative-average` for the site factors with constants uniform in `μ` and in the end**. -/
theorem relative_average_site_uniform (h : ℕ) :
    ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧
      ∀ (μ : Fin 4) (b : Bool) {n : ℕ} [NeZero n] (U : Config N n), U.IsGaugeField → 4 * h + 4 ≤ n →
        ∀ (y : Site n) (α₀ α₁ : ℝ), 0 ≤ α₀ → 0 ≤ α₁ → α₀ ≤ c → α₁ ≤ c →
        (∀ μ' ν' z, PlaqIn (boxR y (loD h) (hiD h μ μ)) μ' ν' z →
          hs (((plaq U μ' ν' z : GLN) : Mat) - 1) ≤ α₀) →
        ∀ A' : Fin 4 → Site n → Mat, (∀ ρ z, BoxBond y h μ ρ z → ‖A' ρ z‖ ≤ α₁) →
        ∀ (B : Fin 4 → Site n → Mat) [DecidablePred (Bm (ofs y (endW h μ b)) h)],
          ‖restrictF B (Bm (ofs y (endW h μ b)) h)‖ < c →
          ‖sExp (moveC U A') B (ofs y (endW h μ b)) h‖ ≤ C * ‖restrictF B (Bm (ofs y (endW h μ b)) h)‖ := by
  choose cs Cs hcs hCs hsite using fun p : Fin 4 × Bool =>
    relative_average_site (N := N) h p.1 (w := endW h p.1 p.2)
      (by simp only [endW]; split_ifs; exacts [Or.inr rfl, Or.inl rfl])
  set c := Finset.univ.inf' Finset.univ_nonempty cs
  set C := Finset.univ.sup' Finset.univ_nonempty Cs
  have hc : ∀ p, c ≤ cs p := fun p => Finset.inf'_le _ (Finset.mem_univ p)
  have hC : ∀ p, Cs p ≤ C := fun p => Finset.le_sup' _ (Finset.mem_univ p)
  refine ⟨c, C, (Finset.lt_inf'_iff _).2 fun p _ => hcs p, (hCs (0, false)).trans (hC _), ?_⟩
  intro μ b n _ U hU hn y α₀ α₁ hα₀ hα₁ hα₀c hα₁c hplq A' hA B _ hB
  refine (hsite (μ, b) U hU hn y α₀ α₁ hα₀ hα₁ (hα₀c.trans (hc _)) (hα₁c.trans (hc _)) hplq A' hA B
    (hB.trans_le (hc _))).trans ?_
  exact mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _)


/-- **(vii) of `prop:relative-average` for `Q'` with constants uniform in `μ`**. -/
theorem relative_average_vii_Q'_uniform (h : ℕ) :
    ∃ c C₁ : ℝ, 0 < c ∧ 0 ≤ C₁ ∧
      ∀ (μ : Fin 4) {n : ℕ} [NeZero n] (U : Config N n), U.IsGaugeField → 4 * h + 4 ≤ n → ∀ (y : Site n)
        [DecidablePred (InBoxB y h μ)] (α₀ α₁ : ℝ), 0 ≤ α₀ → 0 ≤ α₁ → α₀ ≤ c → α₁ ≤ c →
        (∀ μ' ν' z, PlaqIn (boxR y (loD h) (hiD h μ μ)) μ' ν' z →
          hs (((plaq U μ' ν' z : GLN) : Mat) - 1) ≤ α₀) →
        ∀ A'₁ A'₂ : Fin 4 → Site n → Mat, (∀ ρ z, BoxBond y h μ ρ z → ‖A'₁ ρ z‖ ≤ α₁) →
        (∀ ρ z, BoxBond y h μ ρ z → ‖A'₂ ρ z‖ ≤ α₁) → ∀ lam : Site n → Mat,
          ‖blockAvg (moveC U A'₁) lam y h - blockAvg (moveC U A'₂) lam y h‖ ≤
            C₁ * ‖restrictF (A'₁ - A'₂) (InBoxB y h μ)‖ * ‖lam‖ := by
  choose cq Cq hcq hCq hq using fun μ : Fin 4 => relative_average_vii_Q' (N := N) h μ
  set c := Finset.univ.inf' Finset.univ_nonempty cq
  set C₁ := Finset.univ.sup' Finset.univ_nonempty Cq
  have hc : ∀ μ, c ≤ cq μ := fun μ => Finset.inf'_le _ (Finset.mem_univ μ)
  have hC : ∀ μ, Cq μ ≤ C₁ := fun μ => Finset.le_sup' _ (Finset.mem_univ μ)
  refine ⟨c, C₁, (Finset.lt_inf'_iff _).2 fun μ _ => hcq μ, (hCq 0).trans (hC 0), ?_⟩
  intro μ n _ U hU hn y _ α₀ α₁ hα₀ hα₁ hα₀c hα₁c hplq A'₁ A'₂ hA₁ hA₂ lam
  refine (hq μ U hU hn y α₀ α₁ hα₀ hα₁ (hα₀c.trans (hc μ)) (hα₁c.trans (hc μ)) hplq A'₁ A'₂ hA₁ hA₂ lam).trans ?_
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hC μ) (norm_nonneg _)) (norm_nonneg _)

/-- **`𝓜_𝐔(B)(c)` within `1` of `id`, with a constant uniform in `μ`**. -/
theorem relAvg_near_uniform (h : ℕ) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (μ : Fin 4) {n : ℕ} [NeZero n] (U : Config N n), U.IsGaugeField → 4 * h + 4 ≤ n → ∀ (y : Site n)
        [DecidablePred (InBoxB y h μ)] (α₀ α₁ : ℝ), 0 ≤ α₀ → 0 ≤ α₁ → α₀ ≤ c → α₁ ≤ c →
        (∀ μ' ν' z, PlaqIn (boxR y (loD h) (hiD h μ μ)) μ' ν' z →
          hs (((plaq U μ' ν' z : GLN) : Mat) - 1) ≤ α₀) →
        ∀ A' : Fin 4 → Site n → Mat, (∀ ρ z, BoxBond y h μ ρ z → ‖A' ρ z‖ ≤ α₁) →
        ∀ B : Fin 4 → Site n → Mat, ‖restrictF B (InBoxB y h μ)‖ < c →
          ‖((relAvg (moveC U A') B y μ h : GLN) : Mat) - 1‖ < 1 := by
  choose cr hcr hnear using fun μ : Fin 4 => relAvg_near (N := N) h μ
  set c := Finset.univ.inf' Finset.univ_nonempty cr
  have hc : ∀ μ, c ≤ cr μ := fun μ => Finset.inf'_le _ (Finset.mem_univ μ)
  refine ⟨c, (Finset.lt_inf'_iff _).2 fun μ _ => hcr μ, ?_⟩
  intro μ n _ U hU hn y _ α₀ α₁ hα₀ hα₁ hα₀c hα₁c hplq A' hA B hB
  exact hnear μ U hU hn y α₀ α₁ hα₀ hα₁ (hα₀c.trans (hc μ)) (hα₁c.trans (hc μ)) hplq A' hA B (hB.trans_le (hc μ))


/-! ### `lem:block-average-transports` on the levels -/

/-- The points `x ∈ Bˡ(y)` of the level `0`, indexed by their offsets at the levels `l - 1, …, 0` (`p 0` the offset at the
level `l - 1`). -/
def ptB (h : ℕ) : (l : ℕ) → (Fin 4 → ℤ) → (Fin l → Pts h) → (Fin 4 → ℤ)
  | 0, y, _ => y
  | l + 1, y, p => ptB h l (y + Lz h ^ l • offP h (p 0)) (Fin.tail p)

/-- The composite transports `W(y, x) = 𝐔^{(l-1)}(y_l, y_{l-1})⋯𝐔^{(0)}(y_1, y_0)` of `Q'_l`. -/
def WB (h : ℕ) (nn : ℕ → ℕ) [∀ l, NeZero (nn l)] (base : ∀ l, Site (nn l)) (V : ∀ l, Config N (nn l)) :
    (l : ℕ) → (Fin 4 → ℤ) → (Fin l → Pts h) → GLN
  | 0, _, _ => 1
  | l + 1, y, p => trans (V l) (img h (base l) l y) h (p 0) * WB h nn base V l (y + Lz h ^ l • offP h (p 0)) (Fin.tail p)

/-- The block of a point of the region of the level `l + 1` lies in the region of the level `l`. -/
lemma rg_site {h nl l : ℕ} {μ : Fin 4} {y : Fin 4 → ℤ} (hR : Rg h nl μ (l + 1) y) (xp : Pts h) :
    Rg h nl μ l (y + Lz h ^ l • offP h xp) := by
  have hstep : Hw h nl l = Hw h nl (l + 1) + Lz h ^ l * h := Hw_step
  have hQ : 0 < Lz h ^ l := pow_pos (Lz_pos h) l
  intro σ
  have a := hR σ
  have b := offP_inM h xp σ
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [hstep]
  have h1 : Lz h ^ l * (-(h : ℤ)) ≤ Lz h ^ l * offP h xp σ := mul_le_mul_of_nonneg_left b.1 hQ.le
  have h2 : Lz h ^ l * offP h xp σ ≤ Lz h ^ l * h := mul_le_mul_of_nonneg_left b.2 hQ.le
  constructor <;> nlinarith [a.1, a.2]

/-- **`lem:block-average-transports`, the identity**: if `λ_{l+1} = Q'(V_l)λ_l` on the regions, then
`λ_l(y) = L^{-4l} Σ_{x ∈ Bˡ(y)} Ad_{W(y,x)} λ_0(x)` on the region of every level, the sum over the offsets of the levels. -/
theorem block_composite (h nl : ℕ) (μ : Fin 4) (nn : ℕ → ℕ) [∀ l, NeZero (nn l)] (base : ∀ l, Site (nn l))
    (V : ∀ l, Config N (nn l)) (lam : ∀ l, Site (nn l) → Mat)
    (hlam : ∀ l, l < nl → ∀ y, Lat (Lz h) (l + 1) y → Rg h nl μ (l + 1) y →
      lam (l + 1) (img h (base (l + 1)) (l + 1) y) = blockAvg (V l) (lam l) (img h (base l) l y) h) :
    ∀ l, l ≤ nl → ∀ y, Lat (Lz h) l y → Rg h nl μ l y →
      lam l (img h (base l) l y) = ((((2 * h + 1 : ℕ) : ℂ) ^ 4)⁻¹) ^ l •
        ∑ p : Fin l → Pts h, Ad (WB h nn base V l y p) (lam 0 (img h (base 0) 0 (ptB h l y p))) := by
  intro l
  induction l with
  | zero => intro _ y _ _; simp [WB, ptB, Ad]
  | succ l ih =>
    intro hl y hy hR
    have hll : l < nl := by omega
    have hyl := lat_succ_le hy
    rw [hlam l hll y hy hR, blockAvg]
    have hpt : ∀ xp : Pts h, ofs (img h (base l) l y) (offP h xp) = img h (base l) l (y + Lz h ^ l • offP h xp) :=
      fun xp => img_add (base l) hyl _
    simp only [hpt]
    have hih : ∀ xp : Pts h, lam l (img h (base l) l (y + Lz h ^ l • offP h xp)) =
        ((((2 * h + 1 : ℕ) : ℂ) ^ 4)⁻¹) ^ l • ∑ q : Fin l → Pts h,
          Ad (WB h nn base V l (y + Lz h ^ l • offP h xp) q)
            (lam 0 (img h (base 0) 0 (ptB h l (y + Lz h ^ l • offP h xp) q))) := fun xp =>
      ih hll.le _ (lat_add_smul hyl _) (rg_site hR xp)
    simp only [hih, Ad_smul, Ad_sum, ← Ad_mul, Finset.smul_sum, smul_smul]
    rw [← (Fin.consEquiv fun _ : Fin (l + 1) => Pts h).sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun xp _ => Finset.sum_congr rfl fun q _ => ?_
    simp only [Fin.consEquiv_apply, WB, ptB, Fin.cons_zero, Fin.tail_cons, pow_succ]
    ring_nf


/-- The block average of the `0`-form which is `Z` at one point of the block and `0` elsewhere is `L⁻⁴` times the
transported `Z`. -/
lemma blockAvg_single_pt {n : ℕ} [NeZero n] {h : ℕ} (hn : 4 * h + 4 ≤ n) (V : Config N n) (z₀ : Site n) (xp : Pts h)
    (Z : Mat) :
    blockAvg V (fun z => if z = ofs z₀ (offP h xp) then Z else 0) z₀ h =
      (((2 * h + 1 : ℕ) : ℂ) ^ 4)⁻¹ • Ad (trans V z₀ h xp) Z := by
  simp only [blockAvg]
  congr 1
  rw [Finset.sum_eq_single xp]
  · rw [if_pos rfl]
  · intro x _ hx
    rw [if_neg]
    · simp [Ad]
    intro e
    apply hx
    have hb : ∀ v : Pts h, ∀ σ, -(h : ℤ) - 1 ≤ offP h v σ ∧ offP h v σ ≤ 3 * h + 2 := fun v σ => by
      have := offP_inM h v σ; constructor <;> omega
    have := RegularAverages.ofs_inj hn z₀ (hb x) (hb xp) e
    funext σ
    have hσ := congrFun this σ
    simp only [offP] at hσ
    exact Fin.ext (by omega)
  · intro h'; exact absurd (Finset.mem_univ xp) h'

/-- **The transports of the core's `𝐔` are near isometries** at both ends of the bond: with the transports of the
gauge field `U` (isometries, `trans_mem_G`), `‖Ad_{𝐔(c_±,x)}Z - Ad_{U(c_±,x)}Z‖ ≤ L⁴C‖aA'‖_{∞,box}‖Z‖`. -/
theorem trans_near_iso (h : ℕ) (μ : Fin 4) :
    ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧
      ∀ {n : ℕ} [NeZero n] (U : Config N n), U.IsGaugeField → 4 * h + 4 ≤ n → ∀ (y : Site n)
        [DecidablePred (InBoxB y h μ)] (α₀ α₁ : ℝ), 0 ≤ α₀ → 0 ≤ α₁ → α₀ ≤ c → α₁ ≤ c →
        (∀ μ' ν' z, PlaqIn (boxR y (loD h) (hiD h μ μ)) μ' ν' z →
          hs (((plaq U μ' ν' z : GLN) : Mat) - 1) ≤ α₀) →
        ∀ A' : Fin 4 → Site n → Mat, (∀ ρ z, BoxBond y h μ ρ z → ‖A' ρ z‖ ≤ α₁) →
        ∀ (b : Bool) (xp : Pts h) (Z : Mat),
          ‖Ad (trans (moveC U A') (ofs y (endW h μ b)) h xp) Z - Ad (trans U (ofs y (endW h μ b)) h xp) Z‖ ≤
            C * α₁ * ‖Z‖ := by
  obtain ⟨c, Cq, hc, hCq, hlip⟩ := blockAvg_step_lip (N := N) h μ
  refine ⟨c, ((2 * h + 1 : ℕ) : ℝ) ^ 4 * Cq, hc, by positivity, ?_⟩
  intro n _ U hU hn y _ α₀ α₁ hα₀ hα₁ hα₀c hα₁c hplq A' hA b xp Z
  set z₀ := ofs y (endW h μ b)
  set lam : Site n → Mat := fun z => if z = ofs z₀ (offP h xp) then Z else 0
  have hA0 : ∀ ρ z, BoxBond y h μ ρ z → ‖(0 : Fin 4 → Site n → Mat) ρ z‖ ≤ α₁ := fun ρ z _ => by
    simp only [Pi.zero_apply, norm_zero]; exact hα₁
  have hl := hlip U hU hn y α₀ α₁ hα₀ hα₁ hα₀c hα₁c hplq A' 0 hA hA0 b lam ‖Z‖ (norm_nonneg _)
    (fun z _ => by simp only [lam]; split_ifs; exacts [le_rfl, by rw [norm_zero]; exact norm_nonneg _])
  rw [moveC_zero, blockAvg_single_pt hn, blockAvg_single_pt hn, ← smul_sub, norm_smul, sub_zero] at hl
  have hL : (0 : ℝ) < ((2 * h + 1 : ℕ) : ℝ) ^ 4 := by positivity
  rw [norm_inv, norm_pow, Complex.norm_natCast] at hl
  have hRA : ‖restrictF A' (InBoxB y h μ)‖ ≤ α₁ := norm_restrictF_box_le hα₁ hA
  calc ‖Ad (trans (moveC U A') z₀ h xp) Z - Ad (trans U z₀ h xp) Z‖
      = ((2 * h + 1 : ℕ) : ℝ) ^ 4 * ((((2 * h + 1 : ℕ) : ℝ) ^ 4)⁻¹ *
          ‖Ad (trans (moveC U A') z₀ h xp) Z - Ad (trans U z₀ h xp) Z‖) := by field_simp
    _ ≤ ((2 * h + 1 : ℕ) : ℝ) ^ 4 * (Cq * ‖restrictF A' (InBoxB y h μ)‖ * ‖Z‖) :=
        mul_le_mul_of_nonneg_left hl hL.le
    _ ≤ ((2 * h + 1 : ℕ) : ℝ) ^ 4 * (Cq * α₁ * ‖Z‖) := by gcongr
    _ = ((2 * h + 1 : ℕ) : ℝ) ^ 4 * Cq * α₁ * ‖Z‖ := by ring


/-- **`lem:block-average-transports`, the bounds**: for gauge fields `U_l` with values in `G`, backgrounds
`V_l = e^{iA'_l}U_l` with data at most `c` and `‖A'_l‖ ≤ eL^{-(n-l)}` on the boxes, and `2CL⁴e ≤ log 2`, the composite
transports satisfy `‖Ad_{W(y,x)}^{±1}Z‖ ≤ 2‖Z‖` at every point `y` of the region of every level. With `block_composite`
this is the lemma: `(Q'_nλ)(y) = L^{-4n}Σ_{x ∈ Bⁿ(y)}Ad_{W(y,x)}λ(x)` with near-isometric `Ad_{W(y,x)}^{±1}`. -/
theorem block_transports_bound (G : GaugeGroup N) (hG : IsClosed G.mats) (h : ℕ) (hh : 1 ≤ h) :
    ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧ ∀ (nl : ℕ) (μ : Fin 4) (nn : ℕ → ℕ) [∀ l, NeZero (nn l)],
      (∀ l, 4 * h + 4 ≤ nn l) → ∀ (base : ∀ l, Site (nn l)) (U V : ∀ l, Config N (nn l))
      (A' : ∀ l, Fin 4 → Site (nn l) → Mat) (a₀ a₁ : ℕ → ℝ) (e : ℝ),
      (∀ l, IsGField G (U l)) →
      (∀ l, l < nl → ∀ ν x, Lat (Lz h) l x → Rg h nl μ l x → Rg h nl μ l (x + Lz h ^ l • Pi.single ν 1) →
        V l ν (img h (base l) l x) = moveC (U l) (A' l) ν (img h (base l) l x)) →
      (∀ l, l < nl → ∀ ρ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x →
        Rg h nl μ (l + 1) (x + Lz h ^ (l + 1) • Pi.single ρ 1) →
        (∀ μ' ν' z, PlaqIn (boxR (img h (base l) l x) (loD h) (hiD h ρ ρ)) μ' ν' z →
          hs (((plaq (U l) μ' ν' z : GLN) : Mat) - 1) ≤ a₀ l) ∧
        (∀ ν z, BoxBond (img h (base l) l x) h ρ ν z → ‖A' l ν z‖ ≤ a₁ l)) →
      (∀ l, l < nl → 0 ≤ a₀ l ∧ 0 ≤ a₁ l ∧ a₀ l ≤ c ∧ a₁ l ≤ e * ((((2 * h + 1 : ℕ) : ℝ)) ^ (nl - l))⁻¹) →
      0 ≤ e → e ≤ c → 2 * C * e ≤ Real.log 2 →
      ∀ l, l ≤ nl → ∀ y, Lat (Lz h) l y → Rg h nl μ l y → ∀ (p : Fin l → Pts h) (Z : Mat),
        ‖Ad (WB h nn base V l y p) Z‖ ≤ 2 * ‖Z‖ ∧ ‖Ad (WB h nn base V l y p)⁻¹ Z‖ ≤ 2 * ‖Z‖ := by
  classical
  choose cn Cn hcn hCn hni using fun ρ : Fin 4 => trans_near_iso (N := N) h ρ
  choose cg hcg hmem using fun ρ : Fin 4 => trans_mem_G (N := N) G hG h ρ
  set c := min (Finset.univ.inf' Finset.univ_nonempty cn) (Finset.univ.inf' Finset.univ_nonempty cg)
  set C := Finset.univ.sup' Finset.univ_nonempty Cn
  have hcn' : ∀ ρ, c ≤ cn ρ := fun ρ => (min_le_left _ _).trans (Finset.inf'_le _ (Finset.mem_univ ρ))
  have hcg' : ∀ ρ, c ≤ cg ρ := fun ρ => (min_le_right _ _).trans (Finset.inf'_le _ (Finset.mem_univ ρ))
  have hCn' : ∀ ρ, Cn ρ ≤ C := fun ρ => Finset.le_sup' _ (Finset.mem_univ ρ)
  have hc0 : 0 < c := lt_min ((Finset.lt_inf'_iff _).2 fun ρ _ => hcn ρ) ((Finset.lt_inf'_iff _).2 fun ρ _ => hcg ρ)
  have hC0 : 0 ≤ C := (hCn 0).trans (hCn' 0)
  refine ⟨c, C, hc0, hC0, ?_⟩
  intro nl μ nn _ hn base U V A' a₀ a₁ e hUG hVU hdat ha he hec hCe
  have hU : ∀ l, (U l).IsGaugeField := fun l => (hUG l).gauge
  set Lr : ℝ := ((2 * h + 1 : ℕ) : ℝ) with hLr
  have hL3 : 3 ≤ Lr := by rw [hLr]; push_cast; have : (1 : ℝ) ≤ h := by exact_mod_cast hh
                          linarith
  have hp1 : ∀ m, (Lr ^ m)⁻¹ ≤ 1 := fun m => inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith))
  set ε : ℕ → ℝ := fun l => if l < nl then C * a₁ l else 0 with hε
  have hε0 : ∀ l, 0 ≤ ε l := fun l => by
    simp only [hε]; split_ifs with hl
    · exact mul_nonneg hC0 (ha l hl).2.1
    · exact le_rfl
  have hεsum : ∑ m ∈ Finset.range nl, ε m ≤ C * e / 2 := by
    have hg := geom_partial hL3 nl nl le_rfl
    simp only [Nat.sub_self, pow_zero, _root_.inv_one, mul_one] at hg
    calc ∑ m ∈ Finset.range nl, ε m ≤ ∑ m ∈ Finset.range nl, C * e * (Lr ^ (nl - m))⁻¹ :=
          Finset.sum_le_sum fun m hm => by
            have hm' := Finset.mem_range.1 hm
            simp only [hε, if_pos hm']
            have := (ha m hm').2.2.2
            nlinarith [mul_le_mul_of_nonneg_left this hC0]
      _ = C * e * ∑ m ∈ Finset.range nl, (Lr ^ (nl - m))⁻¹ := by rw [Finset.mul_sum]
      _ ≤ C * e * (1 / 2) := mul_le_mul_of_nonneg_left hg (by positivity)
      _ = _ := by ring
  -- the invariant: `‖Ad_{W}^{±1}Z‖ ≤ exp(2Σ_{m<l}ε_m)‖Z‖`
  have hinv : ∀ l, l ≤ nl → ∀ y, Lat (Lz h) l y → Rg h nl μ l y → ∀ (p : Fin l → Pts h) (Z : Mat),
      ‖Ad (WB h nn base V l y p) Z‖ ≤ Real.exp (2 * ∑ m ∈ Finset.range l, ε m) * ‖Z‖ ∧
      ‖Ad (WB h nn base V l y p)⁻¹ Z‖ ≤ Real.exp (2 * ∑ m ∈ Finset.range l, ε m) * ‖Z‖ := by
    intro l
    induction l with
    | zero => intro _ y _ _ p Z; simp [WB, Ad]
    | succ l ih =>
      intro hl y hy hR p Z
      have hll : l < nl := by omega
      have hn2 : 4 * h + 2 ≤ nn l := by have := hn l; omega
      obtain ⟨ha0, ha1, ha0c, ha1e⟩ := ha l hll
      have ha1c : a₁ l ≤ e := by have := hp1 (nl - l); nlinarith
      obtain ⟨x', b, hx', r0, r1, hb⟩ := rg_end_img (base l) hl hy hR
      obtain ⟨hpl, hA⟩ := hdat l hll μ x' hx' r0 r1
      set z₀ := ofs (img h (base l) l x') (endW h μ b)
      -- the transport of the step
      have ht : ∀ xx, trans (V l) z₀ h xx = trans (moveC (U l) (A' l)) z₀ h xx :=
        trans_local hn2 fun ν z h1 h2 => by
          obtain ⟨x'', hx'', s0, s1, rfl⟩ := box_site (hn l) (base l) hx' r0 r1 (boxBond_of_end hn2 b h1 h2)
          exact hVU l hll ν x'' hx'' s0 s1
      have hiso : ∀ W : Mat, ‖Ad (trans (U l) z₀ h (p 0)) W‖ = ‖W‖ := fun W =>
        SupportCont.opNorm_Ad_unitary (G.unitary _ (hmem μ (U l) (hUG l) (hn l) (img h (base l) l x') (a₀ l) ha0
          (ha0c.trans (hcg' μ)) hpl b (p 0))) W
      have hεl : ε l = C * a₁ l := by simp only [hε, if_pos hll]
      have hεle : ε l ≤ 1 / 2 := by
        rw [hεl]
        have : C * a₁ l ≤ C * e := mul_le_mul_of_nonneg_left ha1c hC0
        have := Real.log_two_lt_d9
        linarith
      have hclose : ∀ W : Mat, ‖Ad (trans (moveC (U l) (A' l)) z₀ h (p 0)) W - Ad (trans (U l) z₀ h (p 0)) W‖ ≤
          ε l * ‖W‖ := fun W => by
        refine (hni μ (U l) (hU l) (hn l) (img h (base l) l x') (a₀ l) (a₁ l) ha0 ha1 (ha0c.trans (hcn' μ))
          ((ha1c.trans hec).trans (hcn' μ)) hpl (A' l) hA b (p 0) W).trans ?_
        rw [hεl]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hCn' μ) ha1) (norm_nonneg _)
      have hT := BlockAverageTransports.near_iso (hε0 l) hεle hiso hclose
      have hih := ih hll.le (y + Lz h ^ l • offP h (p 0)) (lat_add_smul (lat_succ_le hy) _) (rg_site hR (p 0))
        (Fin.tail p)
      have hWdef : WB h nn base V (l + 1) y p =
          trans (moveC (U l) (A' l)) z₀ h (p 0) * WB h nn base V l (y + Lz h ^ l • offP h (p 0)) (Fin.tail p) := by
        simp only [WB, hb, ht]
      rw [hWdef, Finset.sum_range_succ, mul_add, Real.exp_add]
      constructor
      · rw [Ad_mul]
        calc ‖Ad (trans (moveC (U l) (A' l)) z₀ h (p 0)) (Ad (WB h nn base V l (y + Lz h ^ l • offP h (p 0))
              (Fin.tail p)) Z)‖
            ≤ Real.exp (2 * ε l) * ‖Ad (WB h nn base V l (y + Lz h ^ l • offP h (p 0)) (Fin.tail p)) Z‖ :=
              (hT _).1
          _ ≤ Real.exp (2 * ε l) * (Real.exp (2 * ∑ m ∈ Finset.range l, ε m) * ‖Z‖) :=
              mul_le_mul_of_nonneg_left (hih Z).1 (Real.exp_pos _).le
          _ = _ := by ring
      · rw [_root_.mul_inv_rev, Ad_mul]
        calc ‖Ad (WB h nn base V l (y + Lz h ^ l • offP h (p 0)) (Fin.tail p))⁻¹
              (Ad (trans (moveC (U l) (A' l)) z₀ h (p 0))⁻¹ Z)‖
            ≤ Real.exp (2 * ∑ m ∈ Finset.range l, ε m) * ‖Ad (trans (moveC (U l) (A' l)) z₀ h (p 0))⁻¹ Z‖ :=
              (hih _).2
          _ ≤ Real.exp (2 * ∑ m ∈ Finset.range l, ε m) * (Real.exp (2 * ε l) * ‖Z‖) :=
              mul_le_mul_of_nonneg_left (hT Z).2 (Real.exp_pos _).le
          _ = _ := by ring
  intro l hl y hy hR p Z
  obtain ⟨h1, h2⟩ := hinv l hl y hy hR p Z
  have hs : ∑ m ∈ Finset.range l, ε m ≤ ∑ m ∈ Finset.range nl, ε m :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hl) fun m _ _ => hε0 m
  have hexp : Real.exp (2 * ∑ m ∈ Finset.range l, ε m) ≤ 2 := by
    calc Real.exp (2 * ∑ m ∈ Finset.range l, ε m) ≤ Real.exp (Real.log 2) := by
          apply Real.exp_le_exp.2
          have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
          linarith [hs, hεsum]
      _ = 2 := Real.exp_log (by norm_num)
  exact ⟨h1.trans (mul_le_mul_of_nonneg_right hexp (norm_nonneg _)),
    h2.trans (mul_le_mul_of_nonneg_right hexp (norm_nonneg _))⟩


/-- The bound of `lem:block-average-transports` in the Hilbert–Schmidt norm: `‖Ad_WZ‖ ≤ 2‖Z‖` for all `Z` gives
`|Ad_WZ| ≤ 2√N|Z|` (`lem:norms`(i)). -/
lemma hs_Ad_of_op (hN : 0 < N) {W : GLN} (hW : ∀ Z : Mat, ‖Ad W Z‖ ≤ 2 * ‖Z‖) (Z : Mat) :
    hs (Ad W Z) ≤ 2 * Real.sqrt N * hs Z :=
  calc hs (Ad W Z) ≤ ‖Ad W Z‖ := hs_le_opNorm hN _
    _ ≤ 2 * ‖Z‖ := hW Z
    _ ≤ 2 * (Real.sqrt N * hs Z) := mul_le_mul_of_nonneg_left (opNorm_le_sqrt_mul_hs Z) (by norm_num)
    _ = 2 * Real.sqrt N * hs Z := by ring

/-- **`prop:relative-average-order`(iv) and (vi) from the data on `T^{(i)}`**: under the hypotheses of `order_levels`,
`‖(1/i) log v_n(A)(y)‖ ≤ C₁‖a_jA‖` at the sites of the last level and
`‖M^n(e^{ia_iA}𝐔)(c)M^n(𝐔)(c)⁻¹ - id‖ ≤ 8(2C₁ + 2)‖a_jA‖` at its bonds. -/
theorem relative_average_order_iv_vi (G : GaugeGroup N) (hG : IsClosed G.mats) (hN : 1 ≤ N) (h : ℕ) (hh : 1 ≤ h) :
    ∃ c C₁ : ℝ, 0 < c ∧ 0 ≤ C₁ ∧ ∀ (nl : ℕ) (μ : Fin 4) (nn : ℕ → ℕ) [∀ l, NeZero (nn l)],
      (∀ l, 4 * h + 4 ≤ nn l) → ∀ (base : ∀ l, Site (nn l)) (U V W : ∀ l, Config N (nn l))
      (B' B : ∀ l, Fin 4 → Site (nn l) → Mat) (g' g : ∀ l, Site (nn l) → GLN) (α₀ t' t : ℝ),
      (∀ l, IsGField G (U l)) →
      (∀ l, l < nl → ∀ ρ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x →
        Rg h nl μ (l + 1) (x + Lz h ^ (l + 1) • Pi.single ρ 1) →
        U (l + 1) ρ (img h (base (l + 1)) (l + 1) x) = avgM (U l) (img h (base l) l x) ρ h ∧
        V (l + 1) ρ (img h (base (l + 1)) (l + 1) x) = avgM (V l) (img h (base l) l x) ρ h ∧
        W (l + 1) ρ (img h (base (l + 1)) (l + 1) x) = avgM (W l) (img h (base l) l x) ρ h ∧
        B' (l + 1) ρ (img h (base (l + 1)) (l + 1) x) = relLog (U l) (B' l) (img h (base l) l x) ρ h ∧
        B (l + 1) ρ (img h (base (l + 1)) (l + 1) x) = relLog (V l) (B l) (img h (base l) l x) ρ h) →
      (∀ l, l < nl → ∀ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x →
        g' (l + 1) (img h (base (l + 1)) (l + 1) x) =
          g' l (img h (base l) l x) * siteFactor (U l) (B' l) (img h (base l) l x) h ∧
        g (l + 1) (img h (base (l + 1)) (l + 1) x) =
          g l (img h (base l) l x) * siteFactor (V l) (B l) (img h (base l) l x) h) →
      (∀ z, g' 0 z = 1) → (∀ z, g 0 z = 1) →
      (∀ ρ x, Lat (Lz h) 0 x → Rg h nl μ 0 x → Rg h nl μ 0 (x + Lz h ^ 0 • Pi.single ρ 1) →
        V 0 ρ (img h (base 0) 0 x) = moveC (U 0) (B' 0) ρ (img h (base 0) 0 x) ∧
        W 0 ρ (img h (base 0) 0 x) = moveC (V 0) (B 0) ρ (img h (base 0) 0 x) ∧
        ‖B' 0 ρ (img h (base 0) 0 x)‖ ≤ t' * ((((2 * h + 1 : ℕ) : ℝ)) ^ nl)⁻¹ ∧
        ‖B 0 ρ (img h (base 0) 0 x)‖ ≤ t * ((((2 * h + 1 : ℕ) : ℝ)) ^ nl)⁻¹) →
      (∀ μ' ν' x, Lat (Lz h) 0 x → Rg h nl μ 0 x → Rg h nl μ 0 (x + Pi.single μ' 1) →
        Rg h nl μ 0 (x + Pi.single ν' 1) → Rg h nl μ 0 (x + Pi.single μ' 1 + Pi.single ν' 1) →
        hs (((plaq (U 0) μ' ν' (img h (base 0) 0 x) : GLN) : Mat) - 1) ≤
          α₀ * ((((2 * h + 1 : ℕ) : ℝ) ^ 2)⁻¹) ^ nl) →
      0 ≤ α₀ → 0 ≤ t' → 0 ≤ t → α₀ ≤ c → t' ≤ c → t ≤ c →
      (∀ x, Lat (Lz h) nl x → Rg h nl μ nl x →
        ‖(1 / Complex.I) • LogM ((g nl (img h (base nl) nl x) : GLN) : Mat)‖ ≤ C₁ * t) ∧
      (∀ ρ x, Lat (Lz h) nl x → Rg h nl μ nl x → Rg h nl μ nl (x + Lz h ^ nl • Pi.single ρ 1) →
        ‖((W nl ρ (img h (base nl) nl x) * (V nl ρ (img h (base nl) nl x))⁻¹ : GLN) : Mat) - 1‖ ≤
          8 * (2 * C₁ + 2) * t) := by
  obtain ⟨c, C₁, Ko, hc, hC₁, hKo, hlev⟩ := order_levels G hG hN h hh
  refine ⟨min (min c (1 / (64 * (C₁ + 1)))) (1 / (4 * (Ko + 1))), C₁,
    lt_min (lt_min hc (by positivity)) (by positivity), hC₁, ?_⟩
  intro nl μ nn _ hn base U V W B' B g' g α₀ t' t hUG hrel hgrel hg'0 hg0 h0 hbase hα₀ ht' ht hα₀c ht'c htc
  have k1 : min (min c (1 / (64 * (C₁ + 1)))) (1 / (4 * (Ko + 1))) ≤ c := (min_le_left _ _).trans (min_le_left _ _)
  have k2 : min (min c (1 / (64 * (C₁ + 1)))) (1 / (4 * (Ko + 1))) ≤ 1 / (64 * (C₁ + 1)) :=
    (min_le_left _ _).trans (min_le_right _ _)
  have k3 : min (min c (1 / (64 * (C₁ + 1)))) (1 / (4 * (Ko + 1))) ≤ 1 / (4 * (Ko + 1)) := min_le_right _ _
  have hlv := hlev nl μ nn hn base U V W B' B g' g α₀ t' t hUG hrel hgrel hg'0 hg0 h0 hbase hα₀ ht' ht
    (hα₀c.trans k1) (ht'c.trans k1) (htc.trans k1) nl le_rfl
  obtain ⟨hform, hgau⟩ := hlv
  simp only [Nat.sub_self, pow_zero, _root_.inv_one, mul_one] at hform hgau
  have hC1t : C₁ * t ≤ 1 / 64 := by
    calc C₁ * t ≤ (C₁ + 1) * (1 / (64 * (C₁ + 1))) := mul_le_mul (by linarith) (htc.trans k2) ht (by positivity)
      _ = 1 / 64 := by field_simp
  have ht64 : t ≤ 1 / 64 := by
    calc t ≤ 1 / (64 * (C₁ + 1)) := htc.trans k2
      _ ≤ 1 / 64 := by
          rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hKt : Ko * t' ≤ 1 / 4 := by
    calc Ko * t' ≤ (Ko + 1) * (1 / (4 * (Ko + 1))) := mul_le_mul (by linarith) (ht'c.trans k3) ht' (by positivity)
      _ = 1 / 4 := by field_simp
  refine ⟨fun x hx hR => ?_, fun ρ x hx q0 q1 => ?_⟩
  · obtain ⟨G', hG', hGn⟩ := hgau x hx hR
    have hlt : ‖G'‖ < Real.log 2 := by have := Real.log_two_gt_d9; linarith
    rw [order_iv hG' hlt]; exact hGn
  · obtain ⟨⟨A'l, hVA, hA'n⟩, hWf, hBn⟩ := hform ρ x hx q0 q1
    obtain ⟨Gm, hGm, hGmn⟩ := hgau x hx q0
    obtain ⟨Gp, hGp, hGpn⟩ := hgau _ (lat_add_smul hx _) q1
    rw [← img_unit (base nl) hx] at hGp
    have hU := (hUG nl).gauge ρ (img h (base nl) nl x)
    have hA8 : ‖Complex.I • A'l‖ ≤ 1 / 4 := by rw [norm_I_smul']; linarith
    have hE : ‖exp (Complex.I • A'l)‖ ≤ 2 := by
      have := norm_exp_le' (Complex.I • A'l)
      have h2 : Real.exp ‖Complex.I • A'l‖ ≤ 2 := by
        calc Real.exp ‖Complex.I • A'l‖ ≤ Real.exp (1 / 4) := Real.exp_le_exp.2 hA8
          _ ≤ 2 := by have := exp_half_le_two; have := Real.exp_le_exp.2 (show (1 / 4 : ℝ) ≤ 1 / 2 by norm_num)
                      linarith
      linarith
    have hE' : ‖exp (-(Complex.I • A'l))‖ ≤ 2 := by
      have := norm_exp_le' (-(Complex.I • A'l))
      have h2 : Real.exp ‖-(Complex.I • A'l)‖ ≤ 2 := by
        rw [norm_neg]
        calc Real.exp ‖Complex.I • A'l‖ ≤ Real.exp (1 / 4) := Real.exp_le_exp.2 hA8
          _ ≤ 2 := by have := exp_half_le_two; have := Real.exp_le_exp.2 (show (1 / 4 : ℝ) ≤ 1 / 2 by norm_num)
                      linarith
      linarith
    have hU1 : ‖((U nl ρ (img h (base nl) nl x) : GLN) : Mat)‖ ≤ 1 := by
      have := opNorm_unitary_mul ((U nl ρ (img h (base nl) nl x) : GLN) : Mat) 1 1 hU (Submonoid.one_mem _)
      simp only [mul_one] at this
      rw [this]; exact norm_one_mat_le
    have hUi1 : ‖(((U nl ρ (img h (base nl) nl x))⁻¹ : GLN) : Mat)‖ ≤ 1 := by
      have := opNorm_unitary_mul (((U nl ρ (img h (base nl) nl x))⁻¹ : GLN) : Mat) 1 1
        (SupportCont.unitary_inv hU) (Submonoid.one_mem _)
      simp only [mul_one] at this
      rw [this]; exact norm_one_mat_le
    have hVv : ((V nl ρ (img h (base nl) nl x) : GLN) : Mat) =
        exp (Complex.I • A'l) * ((U nl ρ (img h (base nl) nl x) : GLN) : Mat) := by
      rw [hVA, Units.val_mul, expU_val]
    have hViv : (((V nl ρ (img h (base nl) nl x))⁻¹ : GLN) : Mat) =
        (((U nl ρ (img h (base nl) nl x))⁻¹ : GLN) : Mat) * exp (-(Complex.I • A'l)) := by
      rw [hVA, _root_.mul_inv_rev, Units.val_mul, expU_inv_val]
    have hV : ‖((V nl ρ (img h (base nl) nl x) : GLN) : Mat)‖ ≤ 2 := by
      rw [hVv]
      calc ‖exp (Complex.I • A'l) * ((U nl ρ (img h (base nl) nl x) : GLN) : Mat)‖
          ≤ ‖exp (Complex.I • A'l)‖ * ‖((U nl ρ (img h (base nl) nl x) : GLN) : Mat)‖ := norm_mul_le _ _
        _ ≤ 2 * 1 := mul_le_mul hE hU1 (norm_nonneg _) (by norm_num)
        _ = 2 := by norm_num
    have hVi : ‖(((V nl ρ (img h (base nl) nl x))⁻¹ : GLN) : Mat)‖ ≤ 2 := by
      rw [hViv]
      calc ‖(((U nl ρ (img h (base nl) nl x))⁻¹ : GLN) : Mat) * exp (-(Complex.I • A'l))‖
          ≤ ‖(((U nl ρ (img h (base nl) nl x))⁻¹ : GLN) : Mat)‖ * ‖exp (-(Complex.I • A'l))‖ := norm_mul_le _ _
        _ ≤ 1 * 2 := mul_le_mul hUi1 hE' (norm_nonneg _) (by norm_num)
        _ = 2 := by norm_num
    exact order_vi (W nl) (V nl) (B nl) (g nl) hWf hGm hGp hGmn hGpn hBn (by linarith) (by linarith) hV hVi


/-- **The remark after `lem:block-average-transports`**: if `λ_l(y) = L^{-4l}Σ_{x ∈ Bˡ(y)}Ad_{W(y,x)}λ_0(x)` with
`‖Ad_{W(y,x)}Z‖ ≤ 2‖Z‖` and `‖λ_0‖ ≤ s` on the block, then `‖λ_l(y)‖ ≤ 2s`: `‖(Q'_lλ)(y)‖ ≤ 2‖λ‖_{∞,Bˡ(y)}`. -/
lemma block_average_bound {h l : ℕ} (W : (Fin l → Pts h) → GLN) (f : (Fin l → Pts h) → Mat) {s : ℝ}
    (hW : ∀ p Z, ‖Ad (W p) Z‖ ≤ 2 * ‖Z‖) (hf : ∀ p, ‖f p‖ ≤ s) :
    ‖((((2 * h + 1 : ℕ) : ℂ) ^ 4)⁻¹) ^ l • ∑ p : Fin l → Pts h, Ad (W p) (f p)‖ ≤ 2 * s := by
  have hcard : (Finset.univ : Finset (Fin l → Pts h)).card = ((2 * h + 1) ^ 4) ^ l := by
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin]
    simp [Pts, Fintype.card_fun, Fintype.card_fin]
  have hs : 0 ≤ s := (norm_nonneg _).trans (hf (fun _ => 0))
  have hL : (0 : ℝ) < ((2 * h + 1 : ℕ) : ℝ) ^ 4 := by positivity
  rw [norm_smul, norm_pow, norm_inv, norm_pow, Complex.norm_natCast]
  have hsum : ‖∑ p : Fin l → Pts h, Ad (W p) (f p)‖ ≤ (((2 * h + 1 : ℕ) : ℝ) ^ 4) ^ l * (2 * s) := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ p : Fin l → Pts h, ‖Ad (W p) (f p)‖ ≤ ∑ _p : Fin l → Pts h, 2 * s :=
          Finset.sum_le_sum fun p _ => (hW p (f p)).trans (by linarith [hf p])
      _ = (((2 * h + 1 : ℕ) : ℝ) ^ 4) ^ l * (2 * s) := by
          rw [Finset.sum_const, hcard, nsmul_eq_mul]; push_cast; ring
  calc ((((2 * h + 1 : ℕ) : ℝ) ^ 4)⁻¹) ^ l * ‖∑ p : Fin l → Pts h, Ad (W p) (f p)‖
      ≤ ((((2 * h + 1 : ℕ) : ℝ) ^ 4)⁻¹) ^ l * ((((2 * h + 1 : ℕ) : ℝ) ^ 4) ^ l * (2 * s)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 2 * s := by rw [← mul_assoc, ← mul_pow, inv_mul_cancel₀ hL.ne', one_pow, one_mul]


/-! ### `prop:relative-average-order`(i), the locality -/

lemma Hw_succ_self (h l : ℕ) : Hw h (l + 1) l = Lz h ^ l * h := by
  have e := two_Hw h (l + 1) l
  have : 2 * Hw h (l + 1) l = 2 * (Lz h ^ l * h) := by rw [e, pow_succ]; unfold Lz; ring
  omega

/-- The blocks of order `l` of the ends of a bond of the box of a bond `c'` of the level `l + 1` lie in the blocks of
order `l + 1` of the ends of `c'`. -/
lemma subR_mono {h l m : ℕ} {ρ ν : Fin 4} {x x' w : Fin 4 → ℤ}
    (hw : LatticePaths.InBox (loD h) (hiD h ρ ρ) w) (hw' : LatticePaths.InBox (loD h) (hiD h ρ ρ) (w + Pi.single ν 1))
    (hx : RegularAverages.InR h l ν ν m (x' - (x + Lz h ^ l • w))) :
    RegularAverages.InR h (l + 1) ρ ρ m (x' - x) := by
  have hadd := Hw_add h (l + 1) l m
  have hs := Hw_succ_self h l
  have hQ : 0 < Lz h ^ l := pow_pos (Lz_pos h) l
  have hpow : Lz h ^ (l + 1) = Lz h ^ l * (2 * h + 1) := by rw [pow_succ]; rfl
  intro σ
  have a := hx σ
  have b := hw σ
  have b' := hw' σ
  simp only [loD, hiD, or_self, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply] at a b b' ⊢
  rw [hadd, hs]
  by_cases hσρ : σ = ρ
  · subst hσρ
    simp only [↓reduceIte] at b b' ⊢
    rw [hpow]
    by_cases hσν : σ = ν
    · subst hσν
      simp only [↓reduceIte, mul_one] at a b'
      have h1 : Lz h ^ l * (-(h : ℤ)) ≤ Lz h ^ l * w σ := mul_le_mul_of_nonneg_left b.1 hQ.le
      have h2 : Lz h ^ l * (w σ + 1) ≤ Lz h ^ l * (3 * h + 1) := mul_le_mul_of_nonneg_left b'.2 hQ.le
      constructor <;> nlinarith
    · simp only [hσν, ↓reduceIte, add_zero, zero_add] at a b'
      have h1 : Lz h ^ l * (-(h : ℤ)) ≤ Lz h ^ l * w σ := mul_le_mul_of_nonneg_left b.1 hQ.le
      have h2 : Lz h ^ l * w σ ≤ Lz h ^ l * (3 * h + 1) := mul_le_mul_of_nonneg_left b.2 hQ.le
      constructor <;> nlinarith
  · simp only [hσρ, ↓reduceIte] at b b' ⊢
    by_cases hσν : σ = ν
    · subst hσν
      simp only [↓reduceIte, mul_one] at a b'
      have h1 : Lz h ^ l * (-(h : ℤ)) ≤ Lz h ^ l * w σ := mul_le_mul_of_nonneg_left b.1 hQ.le
      have h2 : Lz h ^ l * (w σ + 1) ≤ Lz h ^ l * h := mul_le_mul_of_nonneg_left b'.2 hQ.le
      constructor <;> nlinarith
    · simp only [hσν, ↓reduceIte, add_zero, zero_add] at a b'
      have h1 : Lz h ^ l * (-(h : ℤ)) ≤ Lz h ^ l * w σ := mul_le_mul_of_nonneg_left b.1 hQ.le
      have h2 : Lz h ^ l * w σ ≤ Lz h ^ l * h := mul_le_mul_of_nonneg_left b.2 hQ.le
      constructor <;> nlinarith

/-- **The locality of the forms of the levels**: for two families of forms with the same backgrounds and the
relations `B_{l+1} = (1/i) log 𝓜_{V_l}(B_l)` on the regions, if the forms of the level `0` agree on the bonds with both
ends in `Bˡ(c'₋) ∪ Bˡ(c'₊)`, then the forms of the level `l` agree at `c'`: `A^{(l)}(c')` is formed from `A` on these
bonds (`prop:relative-average-order`(i)). -/
theorem forms_local (h nl : ℕ) (μ : Fin 4) (nn : ℕ → ℕ) [∀ l, NeZero (nn l)] (hn : ∀ l, 4 * h + 4 ≤ nn l)
    (base : ∀ l, Site (nn l)) (V : ∀ l, Config N (nn l)) (B B' : ∀ l, Fin 4 → Site (nn l) → Mat)
    (hrel : ∀ l, l < nl → ∀ ρ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x →
      Rg h nl μ (l + 1) (x + Lz h ^ (l + 1) • Pi.single ρ 1) →
      B (l + 1) ρ (img h (base (l + 1)) (l + 1) x) = relLog (V l) (B l) (img h (base l) l x) ρ h ∧
      B' (l + 1) ρ (img h (base (l + 1)) (l + 1) x) = relLog (V l) (B' l) (img h (base l) l x) ρ h) :
    ∀ l, l ≤ nl → ∀ ρ x, Lat (Lz h) l x → Rg h nl μ l x → Rg h nl μ l (x + Lz h ^ l • Pi.single ρ 1) →
      (∀ ν x', Lat (Lz h) 0 x' → RegularAverages.InR h l ρ ρ 0 (x' - x) →
        RegularAverages.InR h l ρ ρ 0 (x' + Pi.single ν 1 - x) →
        B 0 ν (img h (base 0) 0 x') = B' 0 ν (img h (base 0) 0 x')) →
      B l ρ (img h (base l) l x) = B' l ρ (img h (base l) l x) := by
  classical
  intro l
  induction l with
  | zero =>
    intro _ ρ x hx _ _ hag
    refine hag ρ x hx (fun σ => ?_) (fun σ => ?_)
    · simp only [Hw, Pi.sub_apply, sub_self, pow_zero, Int.zero_ediv, neg_zero, add_zero, or_self, le_refl,
        true_and]
      split_ifs <;> simp
    · simp only [Hw, Pi.add_apply, Pi.sub_apply, Pi.single_apply, pow_zero, sub_self, Int.zero_ediv]
      split_ifs <;> simp_all
  | succ l ih =>
    intro hl ρ x hx q0 q1 hag
    have hll : l < nl := by omega
    have hn2 : 4 * h + 2 ≤ nn l := by have := hn l; omega
    obtain ⟨hB, hB'⟩ := hrel l hll ρ x hx q0 q1
    rw [hB, hB', relLog_box hn2 (V l) _ ρ (B l), relLog_box hn2 (V l) _ ρ (B' l)]
    congr 1
    funext ν z
    by_cases hb : BoxBond (img h (base l) l x) h ρ ν z
    · rw [restrictF_box_apply _ hb, restrictF_box_apply _ hb]
      obtain ⟨hm, hm'⟩ := box_bond (hn l) hb
      obtain ⟨x'', hx'', r0, r1, rfl⟩ := box_site (hn l) (base l) hx q0 q1 hb
      -- the bond `(x'', ν)` of the box is `x + Lˡm` with `m = rep(img x, z)`; its blocks lie in those of `c'`
      have hxl := lat_succ_le hx
      set m := rep (img h (base l) l x) h (img h (base l) l x'')
      have hx''eq : img h (base l) l x'' = img h (base l) l (x + Lz h ^ l • m) := by
        rw [← img_add (base l) hxl, StraightExtension.ofs_rep]
      have hxx : x + Lz h ^ l • m = x'' ∨ True := Or.inr trivial
      rw [hx''eq]
      refine ih hll.le ν (x + Lz h ^ l • m) (lat_add_smul hxl m) (rg_of_bond q0 q1 hm) ?_ ?_
      · have e : x + Lz h ^ l • m + Lz h ^ l • Pi.single ν 1 = x + Lz h ^ l • (m + Pi.single ν 1) := by
          rw [smul_add, add_assoc]
        rw [e]; exact rg_of_bond q0 q1 hm'
      · intro ν' x' hx' s0 s1
        exact hag ν' x' hx' (subR_mono hm hm' s0) (subR_mono hm hm' s1)
    · rw [restrictF_box_apply' _ hb, restrictF_box_apply' _ hb]


/-- `average_differentiableAt` with the gauge form near `a₀` only. -/
theorem average_differentiableAt' {n : ℕ} [NeZero n] {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (Wf : E → Config N n) (V : Config N n) (Bf : E → Fin 4 → Site n → Mat) (gf : E → Site n → GLN) (a₀ : E)
    {ρ : Fin 4} {z : Site n}
    (hW : ∀ᶠ a in 𝓝 a₀, Wf a ρ z = ((moveC V (Bf a)).gauge (gf a)) ρ z)
    (hB : DifferentiableAt ℂ (fun a => Bf a ρ z) a₀)
    (hg0 : DifferentiableAt ℂ (fun a => ((gf a z : GLN) : Mat)) a₀)
    (hg1 : DifferentiableAt ℂ (fun a => ((gf a (z + unit n ρ) : GLN) : Mat)) a₀) :
    DifferentiableAt ℂ (fun a => ((Wf a ρ z : GLN) : Mat)) a₀ := by
  have hev : (fun a => ((Wf a ρ z : GLN) : Mat)) =ᶠ[𝓝 a₀] fun a => ((gf a z : GLN) : Mat) *
      (exp (Complex.I • Bf a ρ z) * ((V ρ z : GLN) : Mat)) * (((gf a (z + unit n ρ))⁻¹ : GLN) : Mat) := by
    filter_upwards [hW] with a ha
    rw [ha, Config.gauge, moveC, Units.val_mul, Units.val_mul, Units.val_mul, expU_val]
  refine (hev.differentiableAt_iff).2 ?_
  exact (hg0.mul (((exp_analytic _).differentiableAt.comp a₀ (hB.const_smul Complex.I)).mul
    (differentiableAt_const _))).mul (inv_differentiableAt hg1)

set_option maxHeartbeats 4000000 in
/-- **The backgrounds of the levels are Lipschitz continuous in `A'`** (the per-level hypothesis of `order_v_lip` from the
data on `T^{(i)}`): for families `a ↦ B(a), 𝐠(a), W(a)` of the forms, gauge transformations, and averages
`W(a)_l = M^l(e^{ia}U)` of the pairs `(0, a)`, `a` in the ball of radius `R = tL^{-n}` of the forms of the level `0`, with
`t ≤ c`, the fluctuations `A'(a)_l = (1/i) Log(W(a)_lU_l⁻¹)` satisfy
`‖A'(a₁)_l - A'(a₂)_l‖ ≤ 2(4C₁ + 4)L^{-(n-l)}·Lⁿ‖a₁ - a₂‖` for `‖a₁‖, ‖a₂‖ ≤ R/2`: by `lip_half_ball` from their
holomorphy (`forms_differentiableAt`, `gauge_differentiableAt`, `average_differentiableAt`, `logRatio_differentiableAt`)
and their bound (`background_levels`). -/
theorem background_lip (h : ℕ) (hh : 1 ≤ h) :
    ∃ c C C₁ : ℝ, 0 < c ∧ 0 ≤ C ∧ 0 ≤ C₁ ∧ ∀ (nl : ℕ) (μ : Fin 4) (nn : ℕ → ℕ) [∀ l, NeZero (nn l)],
      (∀ l, 4 * h + 4 ≤ nn l) → ∀ (base : ∀ l, Site (nn l)) (U : ∀ l, Config N (nn l))
      (Bf : (Fin 4 → Site (nn 0) → Mat) → ∀ l, Fin 4 → Site (nn l) → Mat)
      (gf : (Fin 4 → Site (nn 0) → Mat) → ∀ l, Site (nn l) → GLN)
      (Wf : (Fin 4 → Site (nn 0) → Mat) → ∀ l, Config N (nn l)) (a₀ : ℕ → ℝ) (t e₀ : ℝ),
      (∀ l, U l |>.IsGaugeField) →
      (∀ l, l < nl → ∀ ρ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x →
        Rg h nl μ (l + 1) (x + Lz h ^ (l + 1) • Pi.single ρ 1) →
        (∀ μ' ν' z, PlaqIn (boxR (img h (base l) l x) (loD h) (hiD h ρ ρ)) μ' ν' z →
          hs (((plaq (U l) μ' ν' z : GLN) : Mat) - 1) ≤ a₀ l) ∧
        U (l + 1) ρ (img h (base (l + 1)) (l + 1) x) = avgM (U l) (img h (base l) l x) ρ h ∧
        ∀ a, Wf a (l + 1) ρ (img h (base (l + 1)) (l + 1) x) = avgM (Wf a l) (img h (base l) l x) ρ h ∧
          Bf a (l + 1) ρ (img h (base (l + 1)) (l + 1) x) = relLog (U l) (Bf a l) (img h (base l) l x) ρ h) →
      (∀ l, l < nl → ∀ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x → ∀ a,
        gf a (l + 1) (img h (base (l + 1)) (l + 1) x) =
          gf a l (img h (base l) l x) * siteFactor (U l) (Bf a l) (img h (base l) l x) h) →
      (∀ a z, gf a 0 z = 1) →
      (∀ a ρ x, Lat (Lz h) 0 x → Rg h nl μ 0 x → Rg h nl μ 0 (x + Lz h ^ 0 • Pi.single ρ 1) →
        Wf a 0 ρ (img h (base 0) 0 x) = moveC (U 0) (Bf a 0) ρ (img h (base 0) 0 x) ∧
        Bf a 0 ρ (img h (base 0) 0 x) = a ρ (img h (base 0) 0 x)) →
      (∀ l, l < nl → 0 ≤ a₀ l ∧ a₀ l ≤ e₀ * ((((2 * h + 1 : ℕ) : ℝ)) ^ (nl - l))⁻¹) →
      0 < t → 0 ≤ e₀ → e₀ ≤ c → t ≤ c → C * (e₀ + 2 * t) ≤ 1 →
      ∀ l, l ≤ nl → ∀ ρ x, Lat (Lz h) l x → Rg h nl μ l x → Rg h nl μ l (x + Lz h ^ l • Pi.single ρ 1) →
      ∀ a₁ a₂ : Fin 4 → Site (nn 0) → Mat,
        ‖a₁‖ ≤ t * ((((2 * h + 1 : ℕ) : ℝ)) ^ nl)⁻¹ / 2 → ‖a₂‖ ≤ t * ((((2 * h + 1 : ℕ) : ℝ)) ^ nl)⁻¹ / 2 →
        ‖(1 / Complex.I) • LogM (((Wf a₁ l ρ (img h (base l) l x) * (U l ρ (img h (base l) l x))⁻¹ : GLN) : Mat)) -
          (1 / Complex.I) • LogM (((Wf a₂ l ρ (img h (base l) l x) * (U l ρ (img h (base l) l x))⁻¹ : GLN) : Mat))‖ ≤
          2 * (4 * C₁ + 4) * ((((2 * h + 1 : ℕ) : ℝ)) ^ (nl - l))⁻¹ * ((((2 * h + 1 : ℕ) : ℝ)) ^ nl * ‖a₁ - a₂‖) := by
  obtain ⟨cF, hcF, hFD⟩ := forms_differentiableAt (N := N) h
  obtain ⟨cG, hcG, hGD⟩ := gauge_differentiableAt (N := N) h
  obtain ⟨cH, CH, C₁H, hcH, hCH, hC₁H, hH⟩ := order_H (N := N) h hh
  obtain ⟨cb, Cb, C₁b, hcb, hCb, hC₁b, hBL⟩ := background_levels (N := N) h hh
  set c := min (min (min (cF / 4) (cG / 4)) (min (cH / 4) (cb / 4)))
    (min (1 / (256 * (C₁H + 1))) (1 / (1024 * (2 * C₁b + 2)))) with hc_def
  have k1 : c ≤ cF / 4 := (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have k2 : c ≤ cG / 4 := (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have k3 : c ≤ cH / 4 := (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have k4 : c ≤ cb / 4 := (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have k5 : c ≤ 1 / (256 * (C₁H + 1)) := (min_le_right _ _).trans (min_le_left _ _)
  have k6 : c ≤ 1 / (1024 * (2 * C₁b + 2)) := (min_le_right _ _).trans (min_le_right _ _)
  have hc0 : 0 < c := lt_min (lt_min (lt_min (by positivity) (by positivity)) (lt_min (by positivity) (by positivity)))
    (lt_min (by positivity) (by positivity))
  refine ⟨c, max CH Cb, C₁b, hc0, hCH.trans (le_max_left _ _), hC₁b, ?_⟩
  intro nl μ nn _ hn base U Bf gf Wf a₀ t e₀ hU hdat hgr hg0 h0 ha ht he hec htc hCE l hl ρ x hx q0 q1 a₁ a₂ ha₁ ha₂
  set Lr : ℝ := ((2 * h + 1 : ℕ) : ℝ) with hLr
  have hL0 : 0 < Lr := by positivity
  have hp1 : ∀ m, (Lr ^ m)⁻¹ ≤ 1 := fun m => inv_le_one_of_one_le₀ (one_le_pow₀ (by rw [hLr]; push_cast; linarith))
  set R := t * (Lr ^ nl)⁻¹ with hR
  have hR0 : 0 < R := by positivity
  -- the conditions at every `a` of the ball
  have hCEH : CH * (e₀ + 2 * t) ≤ 1 :=
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)).trans hCE
  have hCEb : Cb * (e₀ + 2 * t) ≤ 1 :=
    (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)).trans hCE
  have hC₁Ht : C₁H * t ≤ 1 / 256 := by
    calc C₁H * t ≤ (C₁H + 1) * (1 / (256 * (C₁H + 1))) := mul_le_mul (by linarith) (htc.trans k5) ht.le (by positivity)
      _ = 1 / 256 := by field_simp
  have hC₁bt : (2 * C₁b + 2) * t ≤ 1 / 1024 := by
    calc (2 * C₁b + 2) * t ≤ (2 * C₁b + 2) * (1 / (1024 * (2 * C₁b + 2))) := by gcongr; linarith
      _ = 1 / 1024 := by field_simp
  have hB0 : ∀ a : Fin 4 → Site (nn 0) → Mat, ‖a‖ < R → ∀ ν x, Lat (Lz h) 0 x → Rg h nl μ 0 x →
      Rg h nl μ 0 (x + Lz h ^ 0 • Pi.single ν 1) → ‖Bf a 0 ν (img h (base 0) 0 x)‖ ≤ t * (Lr ^ nl)⁻¹ :=
    fun a haR ν x hx q0 q1 => by
      rw [(h0 a ν x hx q0 q1).2]
      exact ((norm_le_pi_norm (a ν) _).trans (norm_le_pi_norm a ν)).trans haR.le
  -- the gauge form, the forms bound, and the gauge transformations at every `a` of the ball
  have hHa : ∀ a : Fin 4 → Site (nn 0) → Mat, ‖a‖ < R → ∀ l, l ≤ nl →
      (∀ ρ x, Lat (Lz h) l x → Rg h nl μ l x → Rg h nl μ l (x + Lz h ^ l • Pi.single ρ 1) →
        Wf a l ρ (img h (base l) l x) = ((moveC (U l) (Bf a l)).gauge (gf a l)) ρ (img h (base l) l x) ∧
        ‖Bf a l ρ (img h (base l) l x)‖ ≤ 2 * t * (Lr ^ (nl - l))⁻¹) ∧
      (∀ x, Lat (Lz h) l x → Rg h nl μ l x →
        ∃ G : Mat, gf a l (img h (base l) l x) = expU (Complex.I • G) ∧ ‖G‖ ≤ C₁H * t * (Lr ^ (nl - l))⁻¹) :=
    fun a haR => by
      have hH' := hH nl μ nn hn base U U (Wf a) (fun _ => 0) (Bf a) (gf a) a₀ (fun _ => 0) t e₀ hU
        (fun l _ ν x _ _ _ => by rw [moveC_zero])
        (fun l hl ρ x hx q0 q1 => ⟨(hdat l hl ρ x hx q0 q1).1, fun ν z _ => by simp⟩)
        (fun l hl ρ x hx q0 q1 => (hdat l hl ρ x hx q0 q1).2.1)
        (fun l hl ρ x hx q0 q1 => ((hdat l hl ρ x hx q0 q1).2.2 a).1)
        (fun ρ x hx q0 q1 => (h0 a ρ x hx q0 q1).1)
        (fun l hl ρ x hx q0 q1 => ((hdat l hl ρ x hx q0 q1).2.2 a).2)
        (fun l hl x hx q0 => hgr l hl x hx q0 a) (hg0 a)
        (fun l hl => ⟨(ha l hl).1, le_rfl, by simpa using (ha l hl).2⟩) ht.le he (hec.trans (k3.trans (by linarith)))
        (by linarith) hCEH hC₁Ht (hB0 a haR)
      exact hH'
  -- the fluctuations and their bound on the ball
  set F : (Fin 4 → Site (nn 0) → Mat) → Mat := fun a =>
    (1 / Complex.I) • LogM (((Wf a l ρ (img h (base l) l x) * (U l ρ (img h (base l) l x))⁻¹ : GLN) : Mat)) with hF
  have hFbound : ∀ a ∈ ball (0 : Fin 4 → Site (nn 0) → Mat) R, ‖F a‖ ≤ (4 * C₁b + 4) * t * (Lr ^ (nl - l))⁻¹ := by
    intro a haR
    rw [mem_ball, dist_zero_right] at haR
    obtain ⟨Bt, hBt, hBtn⟩ := hBL nl μ nn hn base U (Wf a) (Bf a) (gf a) a₀ t e₀ hU
      (fun l hl ρ x hx q0 q1 => (hdat l hl ρ x hx q0 q1).1) (fun l hl ρ x hx q0 q1 => (hdat l hl ρ x hx q0 q1).2.1)
      (fun l hl ρ x hx q0 q1 => ((hdat l hl ρ x hx q0 q1).2.2 a).1) (fun ρ x hx q0 q1 => (h0 a ρ x hx q0 q1).1)
      (fun l hl ρ x hx q0 q1 => ((hdat l hl ρ x hx q0 q1).2.2 a).2) (fun l hl x hx q0 => hgr l hl x hx q0 a)
      (hg0 a) ha ht.le he (hec.trans (k4.trans (by linarith))) (by linarith) hCEb hC₁bt (hB0 a haR) l hl ρ x hx q0 q1
    have hBts : ‖Bt‖ < Real.log 2 := by
      have := Real.log_two_gt_d9
      have h1 : (4 * C₁b + 4) * t * (Lr ^ (nl - l))⁻¹ ≤ (4 * C₁b + 4) * t :=
        mul_le_of_le_one_right (by positivity) (hp1 (nl - l))
      nlinarith
    have hval : F a = Bt := by
      simp only [hF]
      rw [hBt, mul_inv_cancel_right]
      exact order_iv rfl hBts
    rw [hval]; exact hBtn
  -- the holomorphy on the ball
  have hFd : DifferentiableOn ℂ F (ball 0 R) := by
    intro a₃ ha₃
    rw [mem_ball, dist_zero_right] at ha₃
    have hH3 := hHa a₃ ha₃
    have hforms := hFD nl μ nn hn base U U (fun _ => 0) Bf a₃ a₀ (fun _ => 0) (fun l => 2 * t * (Lr ^ (nl - l))⁻¹) hU
      (fun l hl ν x hx q0 q1 => ⟨by rw [moveC_zero], ((hH3 l hl.le).1 ν x hx q0 q1).2⟩)
      (fun l hl ρ x hx q0 q1 => ⟨(hdat l hl ρ x hx q0 q1).1, fun ν z _ => by simp⟩)
      (fun l hl => by
        obtain ⟨h1, h2⟩ := ha l hl
        have : e₀ * (Lr ^ (nl - l))⁻¹ ≤ e₀ := by have := hp1 (nl - l); nlinarith
        have : 2 * t * (Lr ^ (nl - l))⁻¹ ≤ 2 * t := by have := hp1 (nl - l); nlinarith
        refine ⟨h1, le_rfl, by linarith [hec.trans k1], hcF.le, by positivity, by linarith [htc.trans k1]⟩)
      (fun l hl ρ x hx q0 q1 a => ((hdat l hl ρ x hx q0 q1).2.2 a).2)
      (fun ν x hx q0 q1 => by
        have e : (fun a : Fin 4 → Site (nn 0) → Mat => Bf a 0 ν (img h (base 0) 0 x)) =
            fun a => a ν (img h (base 0) 0 x) := funext fun a => (h0 a ν x hx q0 q1).2
        rw [e]
        exact ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Site (nn 0) => Mat) (img h (base 0) 0 x)).comp
          (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 4 => Site (nn 0) → Mat) ν)).differentiableAt)
    have hgauge := hGD nl μ nn hn base U U (fun _ => 0) Bf gf a₃ a₀ (fun _ => 0)
      (fun l => 2 * t * (Lr ^ (nl - l))⁻¹) hU
      (fun l hl ν x hx q0 q1 => ⟨by rw [moveC_zero], ((hH3 l hl.le).1 ν x hx q0 q1).2, hforms l hl.le ν x hx q0 q1⟩)
      (fun l hl ρ x hx q0 q1 => ⟨(hdat l hl ρ x hx q0 q1).1, fun ν z _ => by simp⟩)
      (fun l hl => by
        obtain ⟨h1, h2⟩ := ha l hl
        have : e₀ * (Lr ^ (nl - l))⁻¹ ≤ e₀ := by have := hp1 (nl - l); nlinarith
        have : 2 * t * (Lr ^ (nl - l))⁻¹ ≤ 2 * t := by have := hp1 (nl - l); nlinarith
        refine ⟨h1, le_rfl, by linarith [hec.trans k2], hcG.le, by positivity, by linarith [htc.trans k2]⟩)
      (fun l hl x hx q0 a => hgr l hl x hx q0 a)
      (fun x hx q0 => by simp only [hg0]; exact differentiableAt_const _)
    have hWd := average_differentiableAt' (fun a => Wf a l) (U l) (fun a => Bf a l) (fun a => gf a l) a₃
      (ρ := ρ) (z := img h (base l) l x)
      (by
        filter_upwards [isOpen_ball.mem_nhds (show a₃ ∈ ball (0 : Fin 4 → Site (nn 0) → Mat) R by
          rw [mem_ball, dist_zero_right]; exact ha₃)] with a haR
        rw [mem_ball, dist_zero_right] at haR
        exact ((hHa a haR l hl).1 ρ x hx q0 q1).1)
      (hforms l hl ρ x hx q0 q1) (hgauge l hl x hx q0)
      (by rw [img_unit (base l) hx]; exact hgauge l hl _ (lat_add_smul hx _) q1)
    -- `W(a₃)U⁻¹` is within `1` of `id`
    obtain ⟨Bt, hBt, hBtn⟩ := hBL nl μ nn hn base U (Wf a₃) (Bf a₃) (gf a₃) a₀ t e₀ hU
      (fun l hl ρ x hx q0 q1 => (hdat l hl ρ x hx q0 q1).1) (fun l hl ρ x hx q0 q1 => (hdat l hl ρ x hx q0 q1).2.1)
      (fun l hl ρ x hx q0 q1 => ((hdat l hl ρ x hx q0 q1).2.2 a₃).1) (fun ρ x hx q0 q1 => (h0 a₃ ρ x hx q0 q1).1)
      (fun l hl ρ x hx q0 q1 => ((hdat l hl ρ x hx q0 q1).2.2 a₃).2) (fun l hl x hx q0 => hgr l hl x hx q0 a₃)
      (hg0 a₃) ha ht.le he (hec.trans (k4.trans (by linarith))) (by linarith) hCEb hC₁bt (hB0 a₃ ha₃) l hl ρ x hx q0 q1
    have hBt8 : ‖Complex.I • Bt‖ ≤ 1 / 4 := by
      rw [norm_I_smul']
      have h1 : (4 * C₁b + 4) * t * (Lr ^ (nl - l))⁻¹ ≤ (4 * C₁b + 4) * t :=
        mul_le_of_le_one_right (by positivity) (hp1 (nl - l))
      nlinarith
    have h1 : ‖((Wf a₃ l ρ (img h (base l) l x) * (U l ρ (img h (base l) l x))⁻¹ : GLN) : Mat) - 1‖ < 1 := by
      rw [hBt, mul_inv_cancel_right, expU_val]
      have h2 := (BakerCampbellHausdorff.norm_exp_sub_one_le ℂ (Complex.I • Bt)).trans
        (exp_sub_one_le_two_mul (norm_nonneg _) hBt8 (by norm_num))
      linarith
    exact (logRatio_differentiableAt (fun a => Wf a l ρ (img h (base l) l x)) (U l ρ (img h (base l) l x))
      hWd h1).differentiableWithinAt
  -- Cauchy's estimate
  have hlip := lip_half_ball hR0 hFd hFbound ha₁ ha₂
  calc ‖F a₁ - F a₂‖ ≤ 2 * ((4 * C₁b + 4) * t * (Lr ^ (nl - l))⁻¹) / R * ‖a₁ - a₂‖ := hlip
    _ = 2 * (4 * C₁b + 4) * (Lr ^ (nl - l))⁻¹ * (Lr ^ nl * ‖a₁ - a₂‖) := by
        rw [hR]; field_simp


set_option maxHeartbeats 4000000 in
/-- **The fluctuations of the levels are holomorphic in `A'`** (the proof of `lem:average-kernels`: "`𝐖 = 𝐔^{(l)}(c')U_l(c')⁻¹`
is a holomorphic function of `A'`"): under the hypotheses of `background_lip`, `A'(a)_l = (1/i) Log(W(a)_lU_l⁻¹)` is
holomorphic on the ball of radius `R = tL^{-n}` of the forms of the level `0` and at most `(4C₁ + 4)tL^{-(n-l)}` there. -/
theorem fluct_holo (h : ℕ) (hh : 1 ≤ h) :
    ∃ c C C₁ : ℝ, 0 < c ∧ 0 ≤ C ∧ 0 ≤ C₁ ∧ ∀ (nl : ℕ) (μ : Fin 4) (nn : ℕ → ℕ) [∀ l, NeZero (nn l)],
      (∀ l, 4 * h + 4 ≤ nn l) → ∀ (base : ∀ l, Site (nn l)) (U : ∀ l, Config N (nn l))
      (Bf : (Fin 4 → Site (nn 0) → Mat) → ∀ l, Fin 4 → Site (nn l) → Mat)
      (gf : (Fin 4 → Site (nn 0) → Mat) → ∀ l, Site (nn l) → GLN)
      (Wf : (Fin 4 → Site (nn 0) → Mat) → ∀ l, Config N (nn l)) (a₀ : ℕ → ℝ) (t e₀ : ℝ),
      (∀ l, U l |>.IsGaugeField) →
      (∀ l, l < nl → ∀ ρ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x →
        Rg h nl μ (l + 1) (x + Lz h ^ (l + 1) • Pi.single ρ 1) →
        (∀ μ' ν' z, PlaqIn (boxR (img h (base l) l x) (loD h) (hiD h ρ ρ)) μ' ν' z →
          hs (((plaq (U l) μ' ν' z : GLN) : Mat) - 1) ≤ a₀ l) ∧
        U (l + 1) ρ (img h (base (l + 1)) (l + 1) x) = avgM (U l) (img h (base l) l x) ρ h ∧
        ∀ a, Wf a (l + 1) ρ (img h (base (l + 1)) (l + 1) x) = avgM (Wf a l) (img h (base l) l x) ρ h ∧
          Bf a (l + 1) ρ (img h (base (l + 1)) (l + 1) x) = relLog (U l) (Bf a l) (img h (base l) l x) ρ h) →
      (∀ l, l < nl → ∀ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x → ∀ a,
        gf a (l + 1) (img h (base (l + 1)) (l + 1) x) =
          gf a l (img h (base l) l x) * siteFactor (U l) (Bf a l) (img h (base l) l x) h) →
      (∀ a z, gf a 0 z = 1) →
      (∀ a ρ x, Lat (Lz h) 0 x → Rg h nl μ 0 x → Rg h nl μ 0 (x + Lz h ^ 0 • Pi.single ρ 1) →
        Wf a 0 ρ (img h (base 0) 0 x) = moveC (U 0) (Bf a 0) ρ (img h (base 0) 0 x) ∧
        Bf a 0 ρ (img h (base 0) 0 x) = a ρ (img h (base 0) 0 x)) →
      (∀ l, l < nl → 0 ≤ a₀ l ∧ a₀ l ≤ e₀ * ((((2 * h + 1 : ℕ) : ℝ)) ^ (nl - l))⁻¹) →
      0 < t → 0 ≤ e₀ → e₀ ≤ c → t ≤ c → C * (e₀ + 2 * t) ≤ 1 →
      ∀ l, l ≤ nl → ∀ ρ x, Lat (Lz h) l x → Rg h nl μ l x → Rg h nl μ l (x + Lz h ^ l • Pi.single ρ 1) →
        DifferentiableOn ℂ (fun a : Fin 4 → Site (nn 0) → Mat =>
          (1 / Complex.I) • LogM (((Wf a l ρ (img h (base l) l x) * (U l ρ (img h (base l) l x))⁻¹ : GLN) : Mat)))
          (ball 0 (t * ((((2 * h + 1 : ℕ) : ℝ)) ^ nl)⁻¹)) ∧
        ∀ a ∈ ball (0 : Fin 4 → Site (nn 0) → Mat) (t * ((((2 * h + 1 : ℕ) : ℝ)) ^ nl)⁻¹),
          ‖(1 / Complex.I) • LogM (((Wf a l ρ (img h (base l) l x) * (U l ρ (img h (base l) l x))⁻¹ : GLN) : Mat))‖ ≤
            (4 * C₁ + 4) * t * ((((2 * h + 1 : ℕ) : ℝ)) ^ (nl - l))⁻¹ := by
  obtain ⟨cF, hcF, hFD⟩ := forms_differentiableAt (N := N) h
  obtain ⟨cG, hcG, hGD⟩ := gauge_differentiableAt (N := N) h
  obtain ⟨cH, CH, C₁H, hcH, hCH, hC₁H, hH⟩ := order_H (N := N) h hh
  obtain ⟨cb, Cb, C₁b, hcb, hCb, hC₁b, hBL⟩ := background_levels (N := N) h hh
  set c := min (min (min (cF / 4) (cG / 4)) (min (cH / 4) (cb / 4)))
    (min (1 / (256 * (C₁H + 1))) (1 / (1024 * (2 * C₁b + 2)))) with hc_def
  have k1 : c ≤ cF / 4 := (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have k2 : c ≤ cG / 4 := (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have k3 : c ≤ cH / 4 := (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have k4 : c ≤ cb / 4 := (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have k5 : c ≤ 1 / (256 * (C₁H + 1)) := (min_le_right _ _).trans (min_le_left _ _)
  have k6 : c ≤ 1 / (1024 * (2 * C₁b + 2)) := (min_le_right _ _).trans (min_le_right _ _)
  have hc0 : 0 < c := lt_min (lt_min (lt_min (by positivity) (by positivity)) (lt_min (by positivity) (by positivity)))
    (lt_min (by positivity) (by positivity))
  refine ⟨c, max CH Cb, C₁b, hc0, hCH.trans (le_max_left _ _), hC₁b, ?_⟩
  intro nl μ nn _ hn base U Bf gf Wf a₀ t e₀ hU hdat hgr hg0 h0 ha ht he hec htc hCE l hl ρ x hx q0 q1
  set Lr : ℝ := ((2 * h + 1 : ℕ) : ℝ) with hLr
  have hL0 : 0 < Lr := by positivity
  have hp1 : ∀ m, (Lr ^ m)⁻¹ ≤ 1 := fun m => inv_le_one_of_one_le₀ (one_le_pow₀ (by rw [hLr]; push_cast; linarith))
  set R := t * (Lr ^ nl)⁻¹ with hR
  have hR0 : 0 < R := by positivity
  -- the conditions at every `a` of the ball
  have hCEH : CH * (e₀ + 2 * t) ≤ 1 :=
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)).trans hCE
  have hCEb : Cb * (e₀ + 2 * t) ≤ 1 :=
    (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)).trans hCE
  have hC₁Ht : C₁H * t ≤ 1 / 256 := by
    calc C₁H * t ≤ (C₁H + 1) * (1 / (256 * (C₁H + 1))) := mul_le_mul (by linarith) (htc.trans k5) ht.le (by positivity)
      _ = 1 / 256 := by field_simp
  have hC₁bt : (2 * C₁b + 2) * t ≤ 1 / 1024 := by
    calc (2 * C₁b + 2) * t ≤ (2 * C₁b + 2) * (1 / (1024 * (2 * C₁b + 2))) := by gcongr; linarith
      _ = 1 / 1024 := by field_simp
  have hB0 : ∀ a : Fin 4 → Site (nn 0) → Mat, ‖a‖ < R → ∀ ν x, Lat (Lz h) 0 x → Rg h nl μ 0 x →
      Rg h nl μ 0 (x + Lz h ^ 0 • Pi.single ν 1) → ‖Bf a 0 ν (img h (base 0) 0 x)‖ ≤ t * (Lr ^ nl)⁻¹ :=
    fun a haR ν x hx q0 q1 => by
      rw [(h0 a ν x hx q0 q1).2]
      exact ((norm_le_pi_norm (a ν) _).trans (norm_le_pi_norm a ν)).trans haR.le
  -- the gauge form, the forms bound, and the gauge transformations at every `a` of the ball
  have hHa : ∀ a : Fin 4 → Site (nn 0) → Mat, ‖a‖ < R → ∀ l, l ≤ nl →
      (∀ ρ x, Lat (Lz h) l x → Rg h nl μ l x → Rg h nl μ l (x + Lz h ^ l • Pi.single ρ 1) →
        Wf a l ρ (img h (base l) l x) = ((moveC (U l) (Bf a l)).gauge (gf a l)) ρ (img h (base l) l x) ∧
        ‖Bf a l ρ (img h (base l) l x)‖ ≤ 2 * t * (Lr ^ (nl - l))⁻¹) ∧
      (∀ x, Lat (Lz h) l x → Rg h nl μ l x →
        ∃ G : Mat, gf a l (img h (base l) l x) = expU (Complex.I • G) ∧ ‖G‖ ≤ C₁H * t * (Lr ^ (nl - l))⁻¹) :=
    fun a haR => by
      have hH' := hH nl μ nn hn base U U (Wf a) (fun _ => 0) (Bf a) (gf a) a₀ (fun _ => 0) t e₀ hU
        (fun l _ ν x _ _ _ => by rw [moveC_zero])
        (fun l hl ρ x hx q0 q1 => ⟨(hdat l hl ρ x hx q0 q1).1, fun ν z _ => by simp⟩)
        (fun l hl ρ x hx q0 q1 => (hdat l hl ρ x hx q0 q1).2.1)
        (fun l hl ρ x hx q0 q1 => ((hdat l hl ρ x hx q0 q1).2.2 a).1)
        (fun ρ x hx q0 q1 => (h0 a ρ x hx q0 q1).1)
        (fun l hl ρ x hx q0 q1 => ((hdat l hl ρ x hx q0 q1).2.2 a).2)
        (fun l hl x hx q0 => hgr l hl x hx q0 a) (hg0 a)
        (fun l hl => ⟨(ha l hl).1, le_rfl, by simpa using (ha l hl).2⟩) ht.le he (hec.trans (k3.trans (by linarith)))
        (by linarith) hCEH hC₁Ht (hB0 a haR)
      exact hH'
  -- the fluctuations and their bound on the ball
  set F : (Fin 4 → Site (nn 0) → Mat) → Mat := fun a =>
    (1 / Complex.I) • LogM (((Wf a l ρ (img h (base l) l x) * (U l ρ (img h (base l) l x))⁻¹ : GLN) : Mat)) with hF
  have hFbound : ∀ a ∈ ball (0 : Fin 4 → Site (nn 0) → Mat) R, ‖F a‖ ≤ (4 * C₁b + 4) * t * (Lr ^ (nl - l))⁻¹ := by
    intro a haR
    rw [mem_ball, dist_zero_right] at haR
    obtain ⟨Bt, hBt, hBtn⟩ := hBL nl μ nn hn base U (Wf a) (Bf a) (gf a) a₀ t e₀ hU
      (fun l hl ρ x hx q0 q1 => (hdat l hl ρ x hx q0 q1).1) (fun l hl ρ x hx q0 q1 => (hdat l hl ρ x hx q0 q1).2.1)
      (fun l hl ρ x hx q0 q1 => ((hdat l hl ρ x hx q0 q1).2.2 a).1) (fun ρ x hx q0 q1 => (h0 a ρ x hx q0 q1).1)
      (fun l hl ρ x hx q0 q1 => ((hdat l hl ρ x hx q0 q1).2.2 a).2) (fun l hl x hx q0 => hgr l hl x hx q0 a)
      (hg0 a) ha ht.le he (hec.trans (k4.trans (by linarith))) (by linarith) hCEb hC₁bt (hB0 a haR) l hl ρ x hx q0 q1
    have hBts : ‖Bt‖ < Real.log 2 := by
      have := Real.log_two_gt_d9
      have h1 : (4 * C₁b + 4) * t * (Lr ^ (nl - l))⁻¹ ≤ (4 * C₁b + 4) * t :=
        mul_le_of_le_one_right (by positivity) (hp1 (nl - l))
      nlinarith
    have hval : F a = Bt := by
      simp only [hF]
      rw [hBt, mul_inv_cancel_right]
      exact order_iv rfl hBts
    rw [hval]; exact hBtn
  -- the holomorphy on the ball
  have hFd : DifferentiableOn ℂ F (ball 0 R) := by
    intro a₃ ha₃
    rw [mem_ball, dist_zero_right] at ha₃
    have hH3 := hHa a₃ ha₃
    have hforms := hFD nl μ nn hn base U U (fun _ => 0) Bf a₃ a₀ (fun _ => 0) (fun l => 2 * t * (Lr ^ (nl - l))⁻¹) hU
      (fun l hl ν x hx q0 q1 => ⟨by rw [moveC_zero], ((hH3 l hl.le).1 ν x hx q0 q1).2⟩)
      (fun l hl ρ x hx q0 q1 => ⟨(hdat l hl ρ x hx q0 q1).1, fun ν z _ => by simp⟩)
      (fun l hl => by
        obtain ⟨h1, h2⟩ := ha l hl
        have : e₀ * (Lr ^ (nl - l))⁻¹ ≤ e₀ := by have := hp1 (nl - l); nlinarith
        have : 2 * t * (Lr ^ (nl - l))⁻¹ ≤ 2 * t := by have := hp1 (nl - l); nlinarith
        refine ⟨h1, le_rfl, by linarith [hec.trans k1], hcF.le, by positivity, by linarith [htc.trans k1]⟩)
      (fun l hl ρ x hx q0 q1 a => ((hdat l hl ρ x hx q0 q1).2.2 a).2)
      (fun ν x hx q0 q1 => by
        have e : (fun a : Fin 4 → Site (nn 0) → Mat => Bf a 0 ν (img h (base 0) 0 x)) =
            fun a => a ν (img h (base 0) 0 x) := funext fun a => (h0 a ν x hx q0 q1).2
        rw [e]
        exact ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Site (nn 0) => Mat) (img h (base 0) 0 x)).comp
          (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 4 => Site (nn 0) → Mat) ν)).differentiableAt)
    have hgauge := hGD nl μ nn hn base U U (fun _ => 0) Bf gf a₃ a₀ (fun _ => 0)
      (fun l => 2 * t * (Lr ^ (nl - l))⁻¹) hU
      (fun l hl ν x hx q0 q1 => ⟨by rw [moveC_zero], ((hH3 l hl.le).1 ν x hx q0 q1).2, hforms l hl.le ν x hx q0 q1⟩)
      (fun l hl ρ x hx q0 q1 => ⟨(hdat l hl ρ x hx q0 q1).1, fun ν z _ => by simp⟩)
      (fun l hl => by
        obtain ⟨h1, h2⟩ := ha l hl
        have : e₀ * (Lr ^ (nl - l))⁻¹ ≤ e₀ := by have := hp1 (nl - l); nlinarith
        have : 2 * t * (Lr ^ (nl - l))⁻¹ ≤ 2 * t := by have := hp1 (nl - l); nlinarith
        refine ⟨h1, le_rfl, by linarith [hec.trans k2], hcG.le, by positivity, by linarith [htc.trans k2]⟩)
      (fun l hl x hx q0 a => hgr l hl x hx q0 a)
      (fun x hx q0 => by simp only [hg0]; exact differentiableAt_const _)
    have hWd := average_differentiableAt' (fun a => Wf a l) (U l) (fun a => Bf a l) (fun a => gf a l) a₃
      (ρ := ρ) (z := img h (base l) l x)
      (by
        filter_upwards [isOpen_ball.mem_nhds (show a₃ ∈ ball (0 : Fin 4 → Site (nn 0) → Mat) R by
          rw [mem_ball, dist_zero_right]; exact ha₃)] with a haR
        rw [mem_ball, dist_zero_right] at haR
        exact ((hHa a haR l hl).1 ρ x hx q0 q1).1)
      (hforms l hl ρ x hx q0 q1) (hgauge l hl x hx q0)
      (by rw [img_unit (base l) hx]; exact hgauge l hl _ (lat_add_smul hx _) q1)
    -- `W(a₃)U⁻¹` is within `1` of `id`
    obtain ⟨Bt, hBt, hBtn⟩ := hBL nl μ nn hn base U (Wf a₃) (Bf a₃) (gf a₃) a₀ t e₀ hU
      (fun l hl ρ x hx q0 q1 => (hdat l hl ρ x hx q0 q1).1) (fun l hl ρ x hx q0 q1 => (hdat l hl ρ x hx q0 q1).2.1)
      (fun l hl ρ x hx q0 q1 => ((hdat l hl ρ x hx q0 q1).2.2 a₃).1) (fun ρ x hx q0 q1 => (h0 a₃ ρ x hx q0 q1).1)
      (fun l hl ρ x hx q0 q1 => ((hdat l hl ρ x hx q0 q1).2.2 a₃).2) (fun l hl x hx q0 => hgr l hl x hx q0 a₃)
      (hg0 a₃) ha ht.le he (hec.trans (k4.trans (by linarith))) (by linarith) hCEb hC₁bt (hB0 a₃ ha₃) l hl ρ x hx q0 q1
    have hBt8 : ‖Complex.I • Bt‖ ≤ 1 / 4 := by
      rw [norm_I_smul']
      have h1 : (4 * C₁b + 4) * t * (Lr ^ (nl - l))⁻¹ ≤ (4 * C₁b + 4) * t :=
        mul_le_of_le_one_right (by positivity) (hp1 (nl - l))
      nlinarith
    have h1 : ‖((Wf a₃ l ρ (img h (base l) l x) * (U l ρ (img h (base l) l x))⁻¹ : GLN) : Mat) - 1‖ < 1 := by
      rw [hBt, mul_inv_cancel_right, expU_val]
      have h2 := (BakerCampbellHausdorff.norm_exp_sub_one_le ℂ (Complex.I • Bt)).trans
        (exp_sub_one_le_two_mul (norm_nonneg _) hBt8 (by norm_num))
      linarith
    exact (logRatio_differentiableAt (fun a => Wf a l ρ (img h (base l) l x)) (U l ρ (img h (base l) l x))
      hWd h1).differentiableWithinAt
  exact ⟨hFd, hFbound⟩


/-! ### `lem:holomorphic-estimates` -/

/-- **`lem:holomorphic-estimates`**: for `f` holomorphic on `{‖x‖ < r₁} × {‖y‖ < r₂}` with `‖f‖ ≤ M`:
(i) if `f(x, 0) = 0` and `f(0, y) = 0`, then `‖f(x, y)‖ ≤ M‖x‖‖y‖/(r₁r₂)` (the core's `4M‖x‖‖y‖/(r₁r₂)` for
`‖x‖ ≤ r₁/2`, `‖y‖ ≤ r₂/2`); (ii) if `f(0, ·)` vanishes at `0` with its derivative, then `‖f(0, y)‖ ≤ M‖y‖²/r₂²`;
(iii) `‖f(x, y) - f(x, y')‖ ≤ 2M‖y - y'‖/r₂` for `‖y‖, ‖y'‖ ≤ r₂/2` (the core's `8M`). -/
theorem holomorphic_estimates {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [NormedAddCommGroup Y]
    [NormedSpace ℂ Y] [NormedAddCommGroup Z] [NormedSpace ℂ Z] {f : X × Y → Z} {r₁ r₂ M : ℝ} (hr₁ : 0 < r₁)
    (hr₂ : 0 < r₂) (hf : DifferentiableOn ℂ f (ball (0 : X) r₁ ×ˢ ball (0 : Y) r₂))
    (hM : ∀ x ∈ ball (0 : X) r₁, ∀ y ∈ ball (0 : Y) r₂, ‖f (x, y)‖ ≤ M) :
    ((∀ x, f (x, 0) = 0) → (∀ y, f (0, y) = 0) → ∀ x ∈ ball (0 : X) r₁, ∀ y ∈ ball (0 : Y) r₂,
        ‖f (x, y)‖ ≤ M * ‖x‖ * ‖y‖ / (r₁ * r₂)) ∧
      (HasFDerivAt (fun y => f (0, y)) (0 : Y →L[ℂ] Z) 0 → f (0, 0) = 0 → ∀ y ∈ ball (0 : Y) r₂,
        ‖f (0, y)‖ ≤ M * ‖y‖ ^ 2 / r₂ ^ 2) ∧
      (∀ x ∈ ball (0 : X) r₁, ∀ y y' : Y, ‖y‖ ≤ r₂ / 2 → ‖y'‖ ≤ r₂ / 2 →
        ‖f (x, y) - f (x, y')‖ ≤ 2 * M / r₂ * ‖y - y'‖) := by
  -- the slices are holomorphic
  have hsy : ∀ x ∈ ball (0 : X) r₁, DifferentiableOn ℂ (fun y => f (x, y)) (ball 0 r₂) := fun x hx y hy =>
    DifferentiableWithinAt.comp (s := ball (0 : Y) r₂) (t := ball (0 : X) r₁ ×ˢ ball (0 : Y) r₂) y
      (hf (x, y) (Set.mk_mem_prod hx hy))
      ((differentiableAt_const x).prodMk differentiableAt_id).differentiableWithinAt
      (fun y' hy' => Set.mk_mem_prod hx hy')
  have hsx : ∀ y ∈ ball (0 : Y) r₂, DifferentiableOn ℂ (fun x => f (x, y)) (ball 0 r₁) := fun y hy x hx =>
    DifferentiableWithinAt.comp (s := ball (0 : X) r₁) (t := ball (0 : X) r₁ ×ˢ ball (0 : Y) r₂) x
      (hf (x, y) (Set.mk_mem_prod hx hy))
      (differentiableAt_id.prodMk (differentiableAt_const y)).differentiableWithinAt
      (fun x' hx' => Set.mk_mem_prod hx' hy)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (mem_ball_self hr₁) 0 (mem_ball_self hr₂))
  refine ⟨fun hx0 hy0 x hx y hy => ?_, fun hd h00 y hy => ?_, fun x hx y y' hy hy' => ?_⟩
  · -- Schwarz in `y`, then in `x`
    have h1 : ∀ x' ∈ ball (0 : X) r₁, ‖f (x', y)‖ ≤ M / r₂ * ‖y‖ := fun x' hx' => by
      have := SchwarzCauchy.schwarz_one (hsy x' hx') (K := M) (fun y' hy' => by
        rw [hx0 x', sub_zero]; exact hM x' hx' y' hy') hy
      simpa [hx0 x'] using this
    have h2 := SchwarzCauchy.schwarz_one (hsx y hy) (K := M / r₂ * ‖y‖) (fun x' hx' => by
      rw [hy0 y, sub_zero]; exact h1 x' hx') hx
    simp only [hy0 y, sub_zero] at h2
    calc ‖f (x, y)‖ ≤ M / r₂ * ‖y‖ / r₁ * ‖x‖ := h2
      _ = M * ‖x‖ * ‖y‖ / (r₁ * r₂) := by field_simp
  · -- Schwarz of the second order in `y`
    have := SchwarzCauchy.schwarz_two (hsy 0 (mem_ball_self hr₁)) (K := M) (fun y' hy' => by
      rw [h00, sub_zero]; exact hM 0 (mem_ball_self hr₁) y' hy') hd hy
    simp only [h00, sub_zero] at this
    calc ‖f (0, y)‖ ≤ M * (‖y‖ / r₂) ^ 2 := this
      _ = M * ‖y‖ ^ 2 / r₂ ^ 2 := by field_simp
  · -- Cauchy's estimate in `y`
    exact lip_half_ball hr₂ (hsy x hx) (fun y'' hy'' => hM x hx y'' hy'') hy hy'

/-- **The Lipschitz continuity of a remainder in the parameter** (the estimate behind the Lipschitz continuity of
`C_n` in `a_jA'`, `prop:relative-average-order`(v)): for `f` holomorphic on `{‖x‖ < r₁} × {‖y‖ < r₂}`, bounded by `M`,
with `f(x, 0) = 0`, and `D_x` the derivative of `f(x, ·)` at `0`, the remainders `R_x(y) = f(x, y) - D_xy` satisfy
`‖R_{x₁}(y) - R_{x₂}(y)‖ ≤ 4M‖x₁ - x₂‖‖y‖²/(r₁r₂²)` for `‖x₁‖, ‖x₂‖ ≤ r₁/2`. The difference `h = f(x₁, ·) - f(x₂, ·)` is
at most `K = 2M‖x₁ - x₂‖/r₁` by Cauchy's estimate in `x`, its derivative at `0` at most `K/r₂` by Cauchy's estimate in
`y`, and the lemma of Schwarz of the second order applies to `h - h'(0)`, at most `2K`. -/
theorem remainder_lip {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [NormedAddCommGroup Y]
    [NormedSpace ℂ Y] [NormedAddCommGroup Z] [NormedSpace ℂ Z] {f : X × Y → Z} {r₁ r₂ M : ℝ} (hr₁ : 0 < r₁)
    (hr₂ : 0 < r₂) (hf : DifferentiableOn ℂ f (ball (0 : X) r₁ ×ˢ ball (0 : Y) r₂))
    (hM : ∀ x ∈ ball (0 : X) r₁, ∀ y ∈ ball (0 : Y) r₂, ‖f (x, y)‖ ≤ M) (h0 : ∀ x, f (x, 0) = 0)
    {x₁ x₂ : X} (hx₁ : ‖x₁‖ ≤ r₁ / 2) (hx₂ : ‖x₂‖ ≤ r₁ / 2) {y : Y} (hy : y ∈ ball (0 : Y) r₂) :
    ‖(f (x₁, y) - fderiv ℂ (fun y' => f (x₁, y')) 0 y) - (f (x₂, y) - fderiv ℂ (fun y' => f (x₂, y')) 0 y)‖ ≤
      4 * M * ‖x₁ - x₂‖ * ‖y‖ ^ 2 / (r₁ * r₂ ^ 2) := by
  have hsy : ∀ x ∈ ball (0 : X) r₁, DifferentiableOn ℂ (fun y => f (x, y)) (ball 0 r₂) := fun x hx y hy =>
    (hf (x, y) ⟨hx, hy⟩).comp y ((differentiableAt_const x).prodMk differentiableAt_id).differentiableWithinAt
      (fun y' hy' => Set.mk_mem_prod hx hy')
  have hsx : ∀ y ∈ ball (0 : Y) r₂, DifferentiableOn ℂ (fun x => f (x, y)) (ball 0 r₁) := fun y hy x hx =>
    (hf (x, y) ⟨hx, hy⟩).comp x (differentiableAt_id.prodMk (differentiableAt_const y)).differentiableWithinAt
      (fun x' hx' => Set.mk_mem_prod hx' hy)
  have hb₁ : x₁ ∈ ball (0 : X) r₁ := mem_ball_zero_iff.2 (by linarith)
  have hb₂ : x₂ ∈ ball (0 : X) r₁ := mem_ball_zero_iff.2 (by linarith)
  set K := 2 * M / r₁ * ‖x₁ - x₂‖ with hK
  -- the difference of the slices
  set hd : Y → Z := fun y => f (x₁, y) - f (x₂, y) with hhd
  have hdd : DifferentiableOn ℂ hd (ball 0 r₂) := (hsy x₁ hb₁).sub (hsy x₂ hb₂)
  have hdK : ∀ y ∈ ball (0 : Y) r₂, ‖hd y‖ ≤ K := fun y hy =>
    lip_half_ball hr₁ (hsx y hy) (fun x hx => hM x hx y hy) hx₁ hx₂
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hdK 0 (mem_ball_self hr₂))
  have hd0 : hd 0 = 0 := by simp [hhd, h0]
  have hn0 : ball (0 : Y) r₂ ∈ 𝓝 (0 : Y) := ball_mem_nhds 0 hr₂
  have hD₁ := ((hsy x₁ hb₁).differentiableAt hn0).hasFDerivAt
  have hD₂ := ((hsy x₂ hb₂).differentiableAt hn0).hasFDerivAt
  set L := fderiv ℂ (fun y' => f (x₁, y')) 0 - fderiv ℂ (fun y' => f (x₂, y')) 0 with hL
  have hdL : HasFDerivAt hd L 0 := hD₁.sub hD₂
  have hLeq : fderiv ℂ hd 0 = L := hdL.fderiv
  -- the derivative at `0` by Cauchy's estimate
  have hLv : ∀ v : Y, ‖L v‖ ≤ K * ‖v‖ / r₂ := fun v => by
    have := SchwarzCauchy.cauchy_fderiv hdd hdK (mem_ball_self hr₂) v
    rwa [hLeq, sub_self, norm_zero, sub_zero] at this
  -- the lemma of Schwarz of the second order for `h - L`
  set φ : Y → Z := fun y => hd y - L y with hφ
  have hφd : DifferentiableOn ℂ φ (ball 0 r₂) := hdd.sub L.differentiable.differentiableOn
  have hφ0 : φ 0 = 0 := by simp [hφ, hd0]
  have hφD : HasFDerivAt φ (0 : Y →L[ℂ] Z) 0 := by
    have := hdL.sub L.hasFDerivAt
    rwa [sub_self] at this
  have hφK : ∀ y ∈ ball (0 : Y) r₂, ‖φ y - φ 0‖ ≤ 2 * K := fun y hy => by
    rw [hφ0, sub_zero]
    have hyr : ‖y‖ < r₂ := mem_ball_zero_iff.1 hy
    have h1 := hdK y hy
    have h2 := hLv y
    have h3 : K * ‖y‖ / r₂ ≤ K := by
      rw [div_le_iff₀ hr₂]; exact mul_le_mul_of_nonneg_left hyr.le hK0
    calc ‖φ y‖ ≤ ‖hd y‖ + ‖L y‖ := norm_sub_le _ _
      _ ≤ 2 * K := by linarith
  have hs := SchwarzCauchy.schwarz_two hφd hφK hφD hy
  rw [hφ0, sub_zero, sub_zero] at hs
  have e : (f (x₁, y) - fderiv ℂ (fun y' => f (x₁, y')) 0 y) - (f (x₂, y) - fderiv ℂ (fun y' => f (x₂, y')) 0 y) =
      φ y := by
    simp only [hφ, hhd, hL, ContinuousLinearMap.sub_apply]; abel
  rw [e]
  calc ‖φ y‖ ≤ 2 * K * (‖y‖ / r₂) ^ 2 := hs
    _ = 4 * M * ‖x₁ - x₂‖ * ‖y‖ ^ 2 / (r₁ * r₂ ^ 2) := by rw [hK]; field_simp; ring

end RelativeAverage
end CoreLean

end
