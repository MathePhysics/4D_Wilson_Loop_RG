/-
The bumps `ζ_y` of the step "The lower bound at the trivial field" of `prop:sf-block` of BALABAN_CORE.tex
(`d4ef86a9a5fd`) on the fine lattice of a sequence of domains (`a₀ = 1`, `a_j = Lʲ = 2h + 1`):
`ζ_y(x) = Π_μ τ_h(x_μ - y_μ)/c²`, `c = (h + 1)²`, with the bump `τ_h` of `SFBump.lean` (the core's `cos²(πt)` replaced).

* `zeta_nonneg`, `zeta_le_one`: `0 ≤ ζ_y ≤ 1`.
* `zeta_supp`: `ζ_y` vanishes outside the block `Δ(y)`.
* `zeta_second`: `|ζ_y(x + e_μ) - 2ζ_y(x) + ζ_y(x - e_μ)| ≤ 18/c ≤ 72a_j⁻²`.
* `zeta_mass`: `Σ_{x ∈ Δ(y)}ζ_y(x) ≥ ((9/16)(h + 1))⁴ ≥ (9/32)⁴a_j⁴`.
-/
import CoreLean.SFBlockEntries
import CoreLean.SFBump

open Finset Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace CoreLean
namespace SFBounds

open Lattices SeqDom Blocks SmallFieldBlocks SFBump

variable (S : SeqDom)

local notation "NF" => SequenceAverages.N0 S
set_option quotPrecheck false in
local notation "jj" => (S.toDomSeq).sc

/-- `τ_h` of the representative of least absolute value. -/
def tval (h : ℕ) (u : ZMod NF) : ℝ := tau h u.valMinAbs

/-- The constant `c = (h + 1)²`. -/
abbrev cB (h : ℕ) : ℝ := ((h : ℝ) + 1) ^ 2

/-- The factor of the bump in the direction `ν`. -/
def zf (y x : Site NF) (ν : Fin 4) : ℝ := tval S (half S.L (jj y)) (x ν - y ν) / cB (half S.L (jj y)) ^ 2

/-- **The bump** `ζ_y(x) = Π_μ τ_h(x_μ - y_μ)/c²`. -/
def zeta (y x : Site NF) : ℝ := ∏ ν, zf S y x ν

lemma cB_pos (h : ℕ) : 0 < cB h := by unfold cB; positivity

lemma zf_nonneg (y x : Site NF) (ν : Fin 4) : 0 ≤ zf S y x ν :=
  div_nonneg (tau_nonneg _ _) (by positivity)

lemma zf_le_one (y x : Site NF) (ν : Fin 4) : zf S y x ν ≤ 1 := by
  unfold zf; exact div_le_one_of_le₀ (tau_le _ _) (by have := cB_pos (half S.L (jj y)); positivity)

lemma zeta_nonneg (y x : Site NF) : 0 ≤ zeta S y x := prod_nonneg fun ν _ => zf_nonneg S y x ν

lemma zeta_le_one (y x : Site NF) : zeta S y x ≤ 1 :=
  prod_le_one₀ (fun ν _ => zf_nonneg S y x ν) fun ν _ => zf_le_one S y x ν

lemma half_lt_NF (j : ℕ) (hj : j ≤ S.k) : 2 * (half S.L j + 3) ≤ NF := by
  have h1 := two_half_add_one S.L_odd j
  have hNF : NF = 2 * S.L ^ (S.mT + S.k) := SequenceAverages.N0_eq S
  have h2 : S.L ^ (j + 1) ≤ S.L ^ (S.mT + S.k) := Nat.pow_le_pow_right S.Lpos (by have := S.one_le_mT; omega)
  have h3 : S.L ^ (j + 1) = S.L ^ j * S.L := pow_succ _ _
  have hL := S.three_le_L
  have h4 : 1 ≤ S.L ^ j := Nat.one_le_pow _ _ S.Lpos
  nlinarith

/-- **The support**: `ζ_y` vanishes outside `Δ(y)`. -/
theorem zeta_supp {y x : Site NF} (hy : y ∈ detB S.toDomSeq) (hx : x ∉ Blk S.toDomSeq (jj y) y) :
    zeta S y x = 0 := by
  by_contra hne
  apply hx
  have hall : ∀ ν, zf S y x ν ≠ 0 := fun ν h => hne (prod_eq_zero (mem_univ ν) h)
  have hlat := (S.mem_detB_iff_inLat y).1 hy
  refine mem_filter.2 ⟨mem_univ _, funext fun ν => ?_⟩
  have hν := hall ν
  have hk : |(x ν - y ν).valMinAbs| ≤ half S.L (jj y) := by
    by_contra hk
    exact hν (by unfold zf tval; rw [tau_supp (by omega), zero_div])
  have hcd : cd (x ν - y ν) ≤ half S.L (jj y) := by
    unfold cd; rw [Int.abs_eq_natAbs] at hk; omega
  exact (eq_cen1 S.L_odd ((S.toDomSeq).dvd_N ((S.toDomSeq).sc_le y)) (hlat ν) hcd).symm

lemma valMinAbs_add_small {m : ℕ} [NeZero m] (u : ZMod m) (s : ℤ) (h : 2 * (|u.valMinAbs| + |s|) < m) :
    (u + (s : ZMod m)).valMinAbs = u.valMinAbs + s := by
  have e : u + (s : ZMod m) = ((u.valMinAbs + s : ℤ) : ZMod m) := by
    push_cast; simp
  rw [e]
  have h1 := abs_le.1 (le_refl |u.valMinAbs|)
  exact valMinAbs_intCast (by cases abs_cases u.valMinAbs <;> cases abs_cases s <;> omega)
    (by cases abs_cases u.valMinAbs <;> cases abs_cases s <;> omega)

/-- `|τ_h(u + 1) - 2τ_h(u) + τ_h(u - 1)| ≤ 18c` on `ℤ/N₀` when `2(h + 2) ≤ N₀`. -/
lemma tval_second {h : ℕ} (hN : 2 * (h + 3) ≤ NF) (u : ZMod NF) :
    |tval S h (u + 1) - 2 * tval S h u + tval S h (u - 1)| ≤ 18 * cB h := by
  have hN' : (2 * (h + 3) : ℤ) ≤ (NF : ℤ) := by exact_mod_cast hN
  rcases le_or_gt |u.valMinAbs| (h + 1) with hv | hv
  · have e1 : (u + 1).valMinAbs = u.valMinAbs + 1 := by
      have := valMinAbs_add_small u 1 (by rw [abs_one]; omega)
      simpa using this
    have e2 : (u - 1).valMinAbs = u.valMinAbs - 1 := by
      have := valMinAbs_add_small u (-1) (by rw [abs_neg, abs_one]; omega)
      simpa [sub_eq_add_neg] using this
    unfold tval; rw [e1, e2]; exact tau_second h u.valMinAbs
  · have hcd : h + 2 ≤ cd u := by unfold cd; rw [← Int.natCast_natAbs] at hv; omega
    have hone : cd (1 : ZMod NF) ≤ 1 := by
      have := cd_intCast_le (N := NF) 1; simpa using this
    have hp : h + 1 ≤ cd (u + 1) := by
      have := cd_sub_le u (u + 1) 0
      rw [sub_zero, sub_zero, show u - (u + 1) = -1 by ring, cd_neg] at this; omega
    have hm : h + 1 ≤ cd (u - 1) := by
      have := cd_sub_le u (u - 1) 0
      rw [sub_zero, sub_zero, show u - (u - 1) = 1 by ring] at this; omega
    have z0 : tval S h u = 0 := by
      unfold tval; exact tau_out (by unfold cd at hcd; rw [← Int.natCast_natAbs]; omega)
    have z1 : tval S h (u + 1) = 0 := by
      unfold tval; exact tau_supp (by unfold cd at hp; rw [← Int.natCast_natAbs]; omega)
    have z2 : tval S h (u - 1) = 0 := by
      unfold tval; exact tau_supp (by unfold cd at hm; rw [← Int.natCast_natAbs]; omega)
    rw [z0, z1, z2]; simp; unfold cB; positivity

lemma zf_shift_ne {y x : Site NF} {μ ν : Fin 4} (h : ν ≠ μ) (s : Site NF) (hs : s = unit _ μ ∨ s = -unit _ μ) :
    zf S y (x + s) ν = zf S y x ν := by
  unfold zf
  rcases hs with rfl | rfl <;> simp [unit, Pi.single_eq_of_ne h]

/-- **The second differences of the bump**: `|ζ_y(x + e_μ) - 2ζ_y(x) + ζ_y(x - e_μ)| ≤ 18/c`. -/
theorem zeta_second {y : Site NF} (hy : y ∈ detB S.toDomSeq) (x : Site NF) (μ : Fin 4) :
    |zeta S y (x + unit _ μ) - 2 * zeta S y x + zeta S y (x - unit _ μ)| ≤ 18 / cB (half S.L (jj y)) := by
  set h := half S.L (jj y)
  have hc := cB_pos h
  set P := ∏ ν ∈ univ.erase μ, zf S y x ν
  have hP0 : 0 ≤ P := prod_nonneg fun ν _ => zf_nonneg S y x ν
  have hP1 : P ≤ 1 := prod_le_one₀ (fun ν _ => zf_nonneg S y x ν) fun ν _ => zf_le_one S y x ν
  have hsplit : ∀ s : Site NF, (s = unit _ μ ∨ s = -unit _ μ ∨ s = 0) →
      zeta S y (x + s) = zf S y (x + s) μ * P := by
    intro s hs
    unfold zeta
    rw [← mul_prod_erase univ _ (mem_univ μ)]
    congr 1
    refine prod_congr rfl fun ν hν => ?_
    rcases hs with hs | hs | hs
    · exact zf_shift_ne S (ne_of_mem_erase hν) s (Or.inl hs)
    · exact zf_shift_ne S (ne_of_mem_erase hν) s (Or.inr hs)
    · rw [hs, add_zero]
  have e1 := hsplit (unit _ μ) (Or.inl rfl)
  have e2 := hsplit (-unit _ μ) (Or.inr (Or.inl rfl))
  have e0 := hsplit 0 (Or.inr (Or.inr rfl))
  rw [add_zero] at e0
  rw [sub_eq_add_neg x, e1, e2, e0]
  have hu : ∀ s : Site NF, (x + s) μ - y μ = (x μ - y μ) + s μ := fun s => by simp; ring
  have h1 : (unit NF μ) μ = 1 := by simp [unit]
  have ht := tval_second S (half_lt_NF S (jj y) ((S.toDomSeq).sc_le y)) (x μ - y μ)
  have hrw : zf S y (x + unit _ μ) μ * P - 2 * (zf S y x μ * P) + zf S y (x + -unit _ μ) μ * P =
      (tval S h (x μ - y μ + 1) - 2 * tval S h (x μ - y μ) + tval S h (x μ - y μ - 1)) / cB h ^ 2 * P := by
    unfold zf
    rw [hu, hu, h1, show (-unit NF μ) μ = -1 by simp [unit], ← sub_eq_add_neg]
    ring
  rw [hrw, abs_mul, abs_div, abs_of_pos (by positivity : (0 : ℝ) < cB h ^ 2), abs_of_nonneg hP0]
  calc |tval S h (x μ - y μ + 1) - 2 * tval S h (x μ - y μ) + tval S h (x μ - y μ - 1)| / cB h ^ 2 * P
      ≤ 18 * cB h / cB h ^ 2 * 1 := by gcongr
    _ = 18 / cB h := by field_simp

/-- **The mass of the bump**: `Σ_{x ∈ Δ(y)}ζ_y(x) ≥ ((9/16)(h + 1))⁴`. -/
theorem zeta_mass {y : Site NF} (hy : y ∈ detB S.toDomSeq) :
    ((9 / 16) * ((half S.L (jj y) : ℝ) + 1)) ^ 4 ≤ ∑ x ∈ Blk S.toDomSeq (jj y) y, zeta S y x := by
  set h := half S.L (jj y)
  set n := S.L ^ jj y
  have hn : n = 2 * h + 1 := (two_half_add_one S.L_odd _).symm
  have hlat := (S.mem_detB_iff_inLat y).1 hy
  rw [SmallFieldBlocks.sum_Blk (S := S.toDomSeq) (jj y) ((S.toDomSeq).sc_le y) hlat]
  have hN := half_lt_NF S (jj y) ((S.toDomSeq).sc_le y)
  -- the factor of an offset
  have hfac : ∀ (o : Fin 4 → ℕ) ν, o ν < n →
      zf S y (phi S.toDomSeq (jj y) y o) ν = tau h ((o ν : ℤ) - h) / cB h ^ 2 := by
    intro o ν ho
    unfold zf tval
    congr 2
    simp only [phi, toDomSeq_L, add_sub_cancel_left]
    exact valMinAbs_intCast (by omega) (by omega)
  have hsum : ∑ o ∈ DiscretePoincare.box 4 n, zeta S y (phi S.toDomSeq (jj y) y o) =
      ∑ o ∈ DiscretePoincare.box 4 n, ∏ ν, tau h ((o ν : ℤ) - h) / cB h ^ 2 := by
    refine sum_congr rfl fun o ho => prod_congr rfl fun ν _ => hfac o ν ?_
    simp only [DiscretePoincare.box, Fintype.mem_piFinset, mem_range] at ho
    exact ho ν
  simp only [toDomSeq_L]
  rw [hsum, DiscretePoincare.box, ← Finset.prod_univ_sum (t := fun _ => range n)
    (f := fun _ o => tau h ((o : ℤ) - h) / cB h ^ 2)]
  simp only [prod_const, card_univ, Fintype.card_fin]
  -- the sum in one variable
  have h1 : ∑ o ∈ range n, tau h ((o : ℤ) - h) / cB h ^ 2 = (∑ k ∈ Icc (-(h : ℤ)) h, tau h k) / cB h ^ 2 := by
    rw [← sum_div]
    congr 1
    refine sum_nbij' (fun o => (o : ℤ) - h) (fun k => (k + h).toNat) (fun o ho => ?_) (fun k hk => ?_)
      (fun o _ => ?_) (fun k hk => ?_) (fun _ _ => rfl)
    · simp only [mem_range] at ho; simp only [mem_Icc]; omega
    · simp only [mem_Icc] at hk; simp only [mem_range]; omega
    · simp
    · simp only [mem_Icc] at hk; omega
  rw [h1]
  have h2 := tau_sum h
  have hc := cB_pos h
  have h3 : (9 / 16) * ((h : ℝ) + 1) ≤ (∑ k ∈ Icc (-(h : ℤ)) h, tau h k) / cB h ^ 2 := by
    rw [le_div_iff₀ (by positivity)]; exact h2
  exact pow_le_pow_left₀ (by positivity) h3 4

end SFBounds
end CoreLean

end
