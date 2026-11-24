/-
`prop:sf-vector-lower` of BALABAN_CORE.tex (`95f07f48317e`), the steps "The comparison sequence" and "The cut-off
minimiser" for the cubes of the partition of unity of `SFPartition.lean`, on the fine lattice (`a₀ = 1`).

* `cq`: the fine site next to the centre `Ma_j(n + ½)` of a cube `□ = (j, n)`; `dT_cq`: it lies within `η/2` of it.
* `dinf_cq_of_hL`: the support of `h_□` lies within `(2/3)Ma_j + ½` of `c_□`.
* `not_mem_two`, `mem_pred`, `mem_of_meets` (the remark after `def:walk-cubes`): the sites within `6Ma_j` of the centre
  of a cube of `𝒟_j` are not in `Ω_{j+2}`, are in `Ω_{j-1}`, and are in `Ω_j` if one of them is in `Ω_{j+1}`.
-/
import CoreLean.SFIMSBounds

open Finset

noncomputable section

namespace CoreLean
namespace PartitionUnity

open Lattices SFBounds Blocks SmallFieldBlocks

variable (S : Lattices.SeqDom) (hM : 12 ≤ S.L ^ S.mM) (hR : 12 * S.L ≤ S.R)

local notation "NF" => SequenceAverages.N0 S

/-- The odd number `Ma_j(2v + 1)` (in the units `a₀ = 1`): twice the centre `Ma_j(v + ½)` of a cube. -/
def codd (j v : ℕ) : ℕ := S.L ^ S.mM * S.L ^ j * (2 * v + 1)

lemma codd_odd (j v : ℕ) : codd S j v % 2 = 1 := by
  unfold codd
  have hL : Odd S.L := S.L_odd
  exact Nat.odd_iff.1 (((hL.pow).mul hL.pow).mul (odd_two_mul_add_one v))

/-- **The fine site next to the centre of a cube**: `c_μ = (Ma_j(2n_μ + 1) - 1)/2`. -/
def cq (q : (toScales S hM hR).Idx) : Site NF := fun μ => (((codd S q.1 (q.2 μ).val) - 1) / 2 : ℕ)

lemma cq_lt (q : (toScales S hM hR).Idx) (μ : Fin 4) : ((codd S q.1 (q.2 μ).val) - 1) / 2 < NF := by
  have hv : (q.2 μ).val < 2 * S.L ^ (S.mT - S.mM + S.k - q.1) := ZMod.val_lt _
  have hjk : (q.1 : ℕ) ≤ S.k := Nat.lt_succ_iff.1 q.1.2
  have hmM := S.mM_le
  set a := S.L ^ S.mM * S.L ^ (q.1 : ℕ)
  set b := S.L ^ (S.mT - S.mM + S.k - q.1)
  have ha : 1 ≤ a := Nat.one_le_iff_ne_zero.2 (by have := S.Lpos; positivity)
  have hNF : NF = 2 * (a * b) := by
    rw [SequenceAverages.N0_eq S]
    have e : S.mT + S.k = S.mM + (q.1 : ℕ) + (S.mT - S.mM + S.k - q.1) := by omega
    simp only [a, b]
    rw [e, pow_add, pow_add]
  have hc : codd S q.1 (q.2 μ).val + a ≤ 4 * (a * b) := by
    have h1 : a * (2 * (q.2 μ).val + 2) ≤ a * (4 * b) := Nat.mul_le_mul_left a (by omega)
    have e1 : codd S q.1 (q.2 μ).val + a = a * (2 * (q.2 μ).val + 2) := by unfold codd; simp only [a]; ring
    have e2 : a * (4 * b) = 4 * (a * b) := by ring
    omega
  omega

lemma cq_val (q : (toScales S hM hR).Idx) (μ : Fin 4) :
    ((cq S hM hR q μ).val : ℝ) = ((codd S q.1 (q.2 μ).val : ℝ) - 1) / 2 := by
  unfold cq
  rw [ZMod.val_natCast_of_lt (cq_lt S hM hR q μ)]
  have h := codd_odd S q.1 (q.2 μ).val
  have h1 : 1 ≤ codd S q.1 (q.2 μ).val := by omega
  have e : 2 * ((codd S q.1 (q.2 μ).val - 1) / 2) = codd S q.1 (q.2 μ).val - 1 := by omega
  have e' : ((2 * ((codd S q.1 (q.2 μ).val - 1) / 2) : ℕ) : ℝ) = ((codd S q.1 (q.2 μ).val - 1 : ℕ) : ℝ) := by
    rw [e]
  push_cast [Nat.cast_sub h1] at e'
  linarith

/-- **`c_□` lies within `η/2` of the centre of `□`.** -/
lemma dT_cq (q : (toScales S hM hR).Idx) :
    dT (toScales S hM hR).hℓ (liftE S (cq S hM hR q)) (cen ((toScales S hM hR).s q.1) q.2) ≤ eta S.L S.k / 2 := by
  have he : 0 < eta S.L S.k := eta_pos S.Lpos
  have hηs : 12 * eta S.L S.k ≤ (toScales S hM hR).s 0 := (toScales S hM hR).η_le 0
  have hs := (toScales S hM hR).s_le_half' q.1
  have hsm : (toScales S hM hR).s 0 ≤ (toScales S hM hR).s q.1 := (toScales S hM hR).s_mono (Nat.zero_le _)
  rw [dT_le_iff]
  intro μ
  have e : liftE S (cq S hM hR q) μ - cen ((toScales S hM hR).s q.1) q.2 μ = -(eta S.L S.k / 2) := by
    simp only [liftE, cen, corner, cq_val]
    show ((codd S q.1 (q.2 μ).val : ℝ) - 1) / 2 * eta S.L S.k -
      ((S.L ^ S.mM : ℕ) : ℝ) * sp S.L S.k q.1 * (((q.2 μ).val : ℝ) + 1 / 2) = _
    simp only [codd, sp]
    push_cast
    ring
  rw [e]
  have h1 : -((toScales S hM hR).ℓ / 2) < -(eta S.L S.k / 2) := by linarith
  have h2 : -(eta S.L S.k / 2) ≤ (toScales S hM hR).ℓ / 2 := by linarith
  rw [rep_of_mem (toScales S hM hR).hℓ h1 h2, abs_neg, abs_of_pos (by linarith)]
lemma s_eq (j : ℕ) : (toScales S hM hR).s j = ((S.L ^ S.mM : ℕ) : ℝ) * (S.L : ℝ) ^ j * eta S.L S.k := by
  show ((S.L ^ S.mM : ℕ) : ℝ) * sp S.L S.k j = _
  unfold sp; ring

/-- The torus distance of a fine site from the centre of a cube. -/
lemma dT_cen_le (q : (toScales S hM hR).Idx) (x : Site NF) :
    dT (toScales S hM hR).hℓ (liftE S x) (cen ((toScales S hM hR).s q.1) q.2) ≤
      ((dinf x (cq S hM hR q) : ℝ) + 1 / 2) * eta S.L S.k := by
  have h1 := dT_triangle (toScales S hM hR).hℓ (liftE S x) (liftE S (cq S hM hR q)) (cen ((toScales S hM hR).s q.1) q.2)
  rw [dT_liftE] at h1
  have h2 := dT_cq S hM hR q
  linarith

/-- **The support of `h_□`** lies within `(2/3)Ma_j + ½` of `c_□`. -/
theorem dinf_cq_of_hL {q : (toScales S hM hR).Idx} {x : Site NF} (h : hL S hM hR q x ≠ 0) :
    (dinf x (cq S hM hR q) : ℝ) < 2 / 3 * ((S.L ^ S.mM : ℕ) : ℝ) * (S.L : ℝ) ^ (q.1 : ℕ) + 1 / 2 := by
  set D := toDomains S hM hR
  have hq' : D.hpu q (liftE S x) ≠ 0 := h
  have hI : D.InD q := by by_contra hI; exact hq' (by unfold Domains.hpu; rw [if_neg hI])
  have hφ : (toScales S hM hR).φ q (liftE S x) ≠ 0 := by
    intro h0; exact hq' (by unfold Domains.hpu; rw [if_pos hI, h0, zero_div])
  have hd := (toScales S hM hR).dT_lt_of_φ_ne hφ
  have h1 := dT_triangle (toScales S hM hR).hℓ (liftE S x) (cen ((toScales S hM hR).s q.1) q.2) (liftE S (cq S hM hR q))
  rw [dT_liftE, dT_comm (toScales S hM hR).hℓ (cen _ _)] at h1
  have h2 := dT_cq S hM hR q
  have hsj := s_eq S hM hR q.1
  have he : 0 < eta S.L S.k := eta_pos S.Lpos
  have h3 : (dinf x (cq S hM hR q) : ℝ) * eta S.L S.k <
      (2 / 3 * ((S.L ^ S.mM : ℕ) : ℝ) * (S.L : ℝ) ^ (q.1 : ℕ) + 1 / 2) * eta S.L S.k := by linarith
  exact lt_of_mul_lt_mul_right h3 he.le

/-! ### The scales near a cube of `𝒟_j` -/

/-- A cube with a non-vanishing `h_□` is a cube of `𝒟`. -/
lemma InD_of_hL {q : (toScales S hM hR).Idx} {x : Site NF} (h : hL S hM hR q x ≠ 0) : (toDomains S hM hR).InD q := by
  have hq' : (toDomains S hM hR).hpu q (liftE S x) ≠ 0 := h
  by_contra hI; exact hq' (by unfold Domains.hpu; rw [if_neg hI])

lemma liftE_mem {i : ℕ} {x : Site NF} : liftE S x ∈ (toDomains S hM hR).Ω i ↔ x ∈ (S.toDomSeq).Ω i := Iff.rfl

/-- **No site within `6Ma_j` of the centre of a cube of `𝒟_j` lies in `Ω_{j+2}`.** -/
theorem not_mem_two {q : (toScales S hM hR).Idx} (hI : (toDomains S hM hR).InD q) {x : Site NF}
    (hx : (dinf x (cq S hM hR q) : ℝ) ≤ 6 * ((S.L ^ S.mM : ℕ) : ℝ) * (S.L : ℝ) ^ (q.1 : ℕ)) :
    x ∉ (S.toDomSeq).Ω ((q.1 : ℕ) + 2) := by
  intro hx2
  obtain ⟨ε, -, hnot, -⟩ := hI
  obtain ⟨p, hp, hpn⟩ := Set.not_subset.1 hnot
  have hpc := dT_cen_of_mem (toScales S hM hR) hp
  have hxc := dT_cen_le S hM hR q x
  have he : 0 < eta S.L S.k := eta_pos S.Lpos
  have hs := (toScales S hM hR).s_pos q.1
  have hηs : 12 * eta S.L S.k ≤ (toScales S hM hR).s q.1 := (toScales S hM hR).η_le q.1
  have hsj := s_eq S hM hR q.1
  have h6 : ((dinf x (cq S hM hR q) : ℝ) + 1 / 2) * eta S.L S.k ≤ 6 * (toScales S hM hR).s q.1 + eta S.L S.k / 2 := by
    have := mul_le_mul_of_nonneg_right hx he.le
    rw [hsj]; nlinarith
  have hd : dT (toScales S hM hR).hℓ p (liftE S x) ≤ 8 * (toScales S hM hR).s q.1 := by
    have := dT_triangle (toScales S hM hR).hℓ p (cen ((toScales S hM hR).s q.1) q.2) (liftE S x)
    rw [dT_comm (toScales S hM hR).hℓ (cen _ _) (liftE S x)] at this
    linarith
  have hL : (2 : ℝ) ≤ (toScales S hM hR).L := (toScales S hM hR).L_ge
  have hR' : 12 * ((toScales S hM hR).L : ℝ) ≤ (toScales S hM hR).R := (toScales S hM hR).hR
  rcases Nat.lt_or_ge ((q.1 : ℕ) + 1) S.k with h0 | h0
  · have hx2' : liftE S x ∈ (toDomains S hM hR).Ω ((q.1 : ℕ) + 1 + 1) := hx2
    have hsep := (toDomains S hM hR).hsep ((q.1 : ℕ) + 1) (by omega) h0 p hpn (liftE S x) hx2'
    have h3 : (toScales S hM hR).s ((q.1 : ℕ) + 1) = (toScales S hM hR).L * (toScales S hM hR).s q.1 :=
      (toScales S hM hR).hsL _
    rw [h3] at hsep
    have h4 : 12 * (toScales S hM hR).L * ((toScales S hM hR).L * (toScales S hM hR).s q.1) ≤
        (toScales S hM hR).R * ((toScales S hM hR).L * (toScales S hM hR).s q.1) :=
      mul_le_mul_of_nonneg_right hR' (by positivity)
    have h6 : 2 * (toScales S hM hR).s q.1 ≤ (toScales S hM hR).L * (toScales S hM hR).s q.1 :=
      mul_le_mul_of_nonneg_right hL hs.le
    have h7 : 2 * ((toScales S hM hR).L * (toScales S hM hR).s q.1) ≤
        (toScales S hM hR).L * ((toScales S hM hR).L * (toScales S hM hR).s q.1) :=
      mul_le_mul_of_nonneg_right hL (by positivity)
    have h5 : 8 * (toScales S hM hR).s q.1 < 12 * (toScales S hM hR).L * ((toScales S hM hR).L * (toScales S hM hR).s q.1) := by
      linarith
    linarith
  · have h4 := (S.toDomSeq).Ω_anti (show (S.toDomSeq).k + 1 ≤ (q.1 : ℕ) + 2 by change S.k + 1 ≤ _; omega) hx2
    rw [(S.toDomSeq).Ω_top] at h4
    exact h4

/-- **The sites within `6Ma_j` of the centre of a cube of `𝒟_j`, `j ≥ 1`, lie in `Ω_{j-1}`.** -/
theorem mem_pred {q : (toScales S hM hR).Idx} (hI : (toDomains S hM hR).InD q) {x : Site NF}
    (hx : (dinf x (cq S hM hR q) : ℝ) ≤ 6 * ((S.L ^ S.mM : ℕ) : ℝ) * (S.L : ℝ) ^ (q.1 : ℕ)) :
    x ∈ (S.toDomSeq).Ω ((q.1 : ℕ) - 1) := by
  rcases Nat.lt_or_ge ((q.1 : ℕ) - 1) 1 with h0 | h0
  · have e : (q.1 : ℕ) - 1 = 0 := by omega
    rw [e, (S.toDomSeq).Ω_zero]; trivial
  by_contra hxn
  obtain ⟨ε, hsub, -, -⟩ := hI
  have hg : gc (toScales S hM hR) q.1 q.2 ε ∈ (toDomains S hM hR).Ω q.1 :=
    hsub (mem_gcube_self (toScales S hM hR) q.1 _)
  have hgc := dT_gc (toScales S hM hR) q.1 q.2 ε
  have hxc := dT_cen_le S hM hR q x
  have he : 0 < eta S.L S.k := eta_pos S.Lpos
  have hηs : 12 * eta S.L S.k ≤ (toScales S hM hR).s q.1 := (toScales S hM hR).η_le q.1
  have hsj := s_eq S hM hR q.1
  have h6 : ((dinf x (cq S hM hR q) : ℝ) + 1 / 2) * eta S.L S.k ≤ 6 * (toScales S hM hR).s q.1 + eta S.L S.k / 2 := by
    have := mul_le_mul_of_nonneg_right hx he.le
    rw [hsj]; nlinarith
  have hd : dT (toScales S hM hR).hℓ (liftE S x) (gc (toScales S hM hR) q.1 q.2 ε) ≤ 7 * (toScales S hM hR).s q.1 := by
    have := dT_triangle (toScales S hM hR).hℓ (liftE S x) (cen ((toScales S hM hR).s q.1) q.2) (gc (toScales S hM hR) q.1 q.2 ε)
    linarith
  have hxn' : liftE S x ∉ (toDomains S hM hR).Ω ((q.1 : ℕ) - 1) := hxn
  have hsep := (toDomains S hM hR).hsep ((q.1 : ℕ) - 1) h0 (by have := Nat.lt_succ_iff.1 q.1.2; omega) (liftE S x) hxn'
    (gc (toScales S hM hR) q.1 q.2 ε) (by rw [show (q.1 : ℕ) - 1 + 1 = q.1 by omega]; exact hg)
  have hsL : (toScales S hM hR).s q.1 = (toScales S hM hR).L * (toScales S hM hR).s ((q.1 : ℕ) - 1) := by
    rw [← (toScales S hM hR).hsL]; congr 1; omega
  have hs1 := (toScales S hM hR).s_pos ((q.1 : ℕ) - 1)
  have hL : (2 : ℝ) ≤ (toScales S hM hR).L := (toScales S hM hR).L_ge
  have hR' : 12 * ((toScales S hM hR).L : ℝ) ≤ (toScales S hM hR).R := (toScales S hM hR).hR
  rw [hsL] at hd
  have h4 : 12 * (toScales S hM hR).L * (toScales S hM hR).s ((q.1 : ℕ) - 1) ≤
      (toScales S hM hR).R * (toScales S hM hR).s ((q.1 : ℕ) - 1) := mul_le_mul_of_nonneg_right hR' hs1.le
  have h5 : 7 * ((toScales S hM hR).L * (toScales S hM hR).s ((q.1 : ℕ) - 1)) <
      12 * (toScales S hM hR).L * (toScales S hM hR).s ((q.1 : ℕ) - 1) := by
    have : 0 < (toScales S hM hR).L * (toScales S hM hR).s ((q.1 : ℕ) - 1) := by positivity
    linarith
  linarith
/-- **If a site within `6Ma_j` of the centre lies in `Ω_{j+1}`, all of them lie in `Ω_j`** (`j ≥ 1`). -/
theorem mem_of_meets {q : (toScales S hM hR).Idx} (hj : 1 ≤ (q.1 : ℕ)) {x x' : Site NF}
    (hx : (dinf x (cq S hM hR q) : ℝ) ≤ 6 * ((S.L ^ S.mM : ℕ) : ℝ) * (S.L : ℝ) ^ (q.1 : ℕ))
    (hx' : (dinf x' (cq S hM hR q) : ℝ) ≤ 6 * ((S.L ^ S.mM : ℕ) : ℝ) * (S.L : ℝ) ^ (q.1 : ℕ))
    (h1 : x' ∈ (S.toDomSeq).Ω ((q.1 : ℕ) + 1)) : x ∈ (S.toDomSeq).Ω q.1 := by
  by_contra hxn
  have hk : (q.1 : ℕ) + 1 ≤ S.k := by
    by_contra hc
    have h4 := (S.toDomSeq).Ω_anti (show (S.toDomSeq).k + 1 ≤ (q.1 : ℕ) + 1 by change S.k + 1 ≤ _; omega) h1
    rw [(S.toDomSeq).Ω_top] at h4; exact h4
  have hsep := (S.toDomSeq).sep q.1 hj (by change (q.1 : ℕ) < S.k; omega) x hxn x' h1
  have hRMd : (S.toDomSeq).RM = ((S.R * S.L ^ S.mM : ℕ) : ℝ) := rfl
  have hLd : (S.toDomSeq).L = S.L := rfl
  rw [hRMd, hLd] at hsep
  have htri := dinf_triangle x (cq S hM hR q) x'
  rw [dinf_comm (cq S hM hR q) x'] at htri
  have htri' : (dinf x x' : ℝ) ≤ dinf x (cq S hM hR q) + dinf x' (cq S hM hR q) := by exact_mod_cast htri
  have hR12 : (12 : ℝ) < S.R := by
    have : (12 : ℝ) * S.L ≤ S.R := by exact_mod_cast hR
    have : (3 : ℝ) ≤ S.L := by exact_mod_cast S.three_le_L
    nlinarith
  have hp : (0 : ℝ) < ((S.L ^ S.mM : ℕ) : ℝ) * (S.L : ℝ) ^ (q.1 : ℕ) := by have := S.Lpos; positivity
  have e : ((S.R * S.L ^ S.mM : ℕ) : ℝ) * (S.L : ℝ) ^ (q.1 : ℕ) = (S.R : ℝ) * (((S.L ^ S.mM : ℕ) : ℝ) * (S.L : ℝ) ^ (q.1 : ℕ)) := by
    push_cast; ring
  rw [e] at hsep
  nlinarith

/-! ### The comparison sequence of a cube -/

lemma L_le_M (hM' : 12 ≤ S.L ^ S.mM) : S.L ≤ S.L ^ S.mM := by
  rcases Nat.eq_zero_or_pos S.mM with h | h
  · rw [h, pow_zero] at hM'; omega
  · exact Nat.le_self_pow (by omega) _

lemma L_le_M_real (hM' : 12 ≤ S.L ^ S.mM) : (S.L : ℝ) ≤ ((S.L ^ S.mM : ℕ) : ℝ) := by
  exact_mod_cast L_le_M S hM'

section TwoLayer

variable {S} {i : ℕ} {hi : i + 1 ≤ S.k} {Λ : Set (Tor (ellT S.L S.mT))} {hΛ : IsCubes S (i + 1) Λ}

lemma mem_two_low {n : ℕ} (hn : n ≤ i) (x : Site NF) : x ∈ ((twoLayer S i hi Λ hΛ).toDomSeq).Ω n := by
  show (twoLayer S i hi Λ hΛ).ef x ∈ (twoLayer S i hi Λ hΛ).Ω n
  rw [twoLayer_low hn]; trivial

lemma mem_two_mid (x : Site NF) : x ∈ ((twoLayer S i hi Λ hΛ).toDomSeq).Ω (i + 1) ↔ S.ef x ∈ Λ := by
  show (twoLayer S i hi Λ hΛ).ef x ∈ (twoLayer S i hi Λ hΛ).Ω (i + 1) ↔ _
  rw [twoLayer_mid]; rfl

lemma not_mem_two_high {n : ℕ} (hn : i + 2 ≤ n) (x : Site NF) : x ∉ ((twoLayer S i hi Λ hΛ).toDomSeq).Ω n := by
  intro h
  have h' : (twoLayer S i hi Λ hΛ).ef x ∈ (twoLayer S i hi Λ hΛ).Ω n := h
  rw [twoLayer_high hn] at h'
  exact h'

/-- The comparison sequence has the scale of `S` at a site with the same membership. -/
lemma sc_two_eq (x : Site NF) (h : ∀ n, x ∈ ((twoLayer S i hi Λ hΛ).toDomSeq).Ω n ↔ x ∈ (S.toDomSeq).Ω n) :
    ((twoLayer S i hi Λ hΛ).toDomSeq).sc x = (S.toDomSeq).sc x := by
  refine le_antisymm ?_ ?_
  · exact ((S.toDomSeq).mem_iff x _).1 ((h _).1 (((twoLayer S i hi Λ hΛ).toDomSeq).mem_sc x))
  · exact (((twoLayer S i hi Λ hΛ).toDomSeq).mem_iff x _).1 ((h _).2 ((S.toDomSeq).mem_sc x))

/-- The scales of the comparison sequence are `i` and `i + 1`. -/
lemma sc_two_mem (x : Site NF) :
    i ≤ ((twoLayer S i hi Λ hΛ).toDomSeq).sc x ∧ ((twoLayer S i hi Λ hΛ).toDomSeq).sc x ≤ i + 1 := by
  constructor
  · exact (((twoLayer S i hi Λ hΛ).toDomSeq).mem_iff x _).1 (mem_two_low le_rfl x)
  · by_contra hc
    push_neg at hc
    exact not_mem_two_high (show i + 2 ≤ ((twoLayer S i hi Λ hΛ).toDomSeq).sc x by omega) x
      (((twoLayer S i hi Λ hΛ).toDomSeq).mem_sc x)

end TwoLayer

/-- **The comparison sequence of a cube** (the step "The comparison sequence"): the sequence `S'` with the layers
`i ∈ {j - 1, j}` and `i + 1` only, `Ω'_{i+1} = Ω_{i+1}`, has the membership of `S` at the sites within `6Ma_j` of the
centre. -/
theorem exists_comparison {q : (toScales S hM hR).Idx} (hI : (toDomains S hM hR).InD q) (hk1 : 1 ≤ S.k) :
    ∃ (i : ℕ) (hi : i + 1 ≤ S.k) (Λ : Set (Tor (ellT S.L S.mT))) (hΛ : IsCubes S (i + 1) Λ),
      i ≤ (q.1 : ℕ) ∧ (q.1 : ℕ) ≤ i + 1 ∧
      ∀ x : Site NF, (dinf x (cq S hM hR q) : ℝ) ≤ 6 * ((S.L ^ S.mM : ℕ) : ℝ) * (S.L : ℝ) ^ (q.1 : ℕ) →
        ∀ n, (x ∈ ((twoLayer S i hi Λ hΛ).toDomSeq).Ω n ↔ x ∈ (S.toDomSeq).Ω n) := by
  have hjk : (q.1 : ℕ) ≤ S.k := Nat.lt_succ_iff.1 q.1.2
  by_cases hA : (q.1 : ℕ) = 0 ∨ ∃ x' : Site NF,
      (dinf x' (cq S hM hR q) : ℝ) ≤ 6 * ((S.L ^ S.mM : ℕ) : ℝ) * (S.L : ℝ) ^ (q.1 : ℕ) ∧
        x' ∈ (S.toDomSeq).Ω ((q.1 : ℕ) + 1)
  · -- (a), (c): the layers `j`, `j + 1`
    have hi : (q.1 : ℕ) + 1 ≤ S.k := by
      rcases hA with h0 | ⟨x', -, h1⟩
      · omega
      · by_contra hc
        have h4 := (S.toDomSeq).Ω_anti (show (S.toDomSeq).k + 1 ≤ (q.1 : ℕ) + 1 by change S.k + 1 ≤ _; omega) h1
        rw [(S.toDomSeq).Ω_top] at h4; exact h4
    refine ⟨q.1, hi, S.Ω ((q.1 : ℕ) + 1), S.cubes ((q.1 : ℕ) + 1) (by omega) hi, le_rfl, by omega, ?_⟩
    intro x hx n
    have hxj : x ∈ (S.toDomSeq).Ω q.1 := by
      rcases hA with h0 | ⟨x', hx', h1⟩
      · rw [h0, (S.toDomSeq).Ω_zero]; trivial
      · by_cases hj0 : (q.1 : ℕ) = 0
        · rw [hj0, (S.toDomSeq).Ω_zero]; trivial
        · exact mem_of_meets S hM hR (by omega) hx hx' h1
    have hx2 := not_mem_two S hM hR hI hx
    rcases Nat.lt_or_ge (q.1 : ℕ) n with hn | hn
    · rcases Nat.lt_or_ge (q.1 + 1 : ℕ) n with hn' | hn'
      · exact ⟨fun h => absurd h (not_mem_two_high (by omega) x),
          fun h => absurd ((S.toDomSeq).Ω_anti (show (q.1 : ℕ) + 2 ≤ n by omega) h) hx2⟩
      · have e : n = (q.1 : ℕ) + 1 := by omega
        subst e
        exact (mem_two_mid x).trans Iff.rfl
    · exact ⟨fun _ => (S.toDomSeq).Ω_anti hn hxj, fun _ => mem_two_low hn x⟩
  · -- (b): the layers `j - 1`, `j`
    push_neg at hA
    obtain ⟨hj0, hB⟩ := hA
    have hi : (q.1 : ℕ) - 1 + 1 ≤ S.k := by omega
    have e1 : (q.1 : ℕ) - 1 + 1 = q.1 := by omega
    have hΛ : IsCubes S ((q.1 : ℕ) - 1 + 1) (S.Ω q.1) := by rw [e1]; exact S.cubes q.1 (by omega) hjk
    refine ⟨(q.1 : ℕ) - 1, hi, S.Ω q.1, hΛ, by omega, by omega, ?_⟩
    intro x hx n
    have hxp := mem_pred S hM hR hI hx
    have hxn := hB x hx
    rcases Nat.lt_or_ge ((q.1 : ℕ) - 1) n with hn | hn
    · rcases Nat.lt_or_ge (q.1 : ℕ) n with hn' | hn'
      · exact ⟨fun h => absurd h (not_mem_two_high (by omega) x),
          fun h => absurd ((S.toDomSeq).Ω_anti (show (q.1 : ℕ) + 1 ≤ n by omega) h) hxn⟩
      · have e : n = (q.1 : ℕ) - 1 + 1 := by omega
        subst e
        refine (mem_two_mid x).trans ?_
        show S.ef x ∈ S.Ω q.1 ↔ S.ef x ∈ S.Ω ((q.1 : ℕ) - 1 + 1)
        rw [e1]
    · exact ⟨fun _ => (S.toDomSeq).Ω_anti hn hxp, fun _ => mem_two_low hn x⟩

/-! ### The common blocks and the constraint form -/

/-- The union of the blocks whose centres lie within `5Ma_j` of `c_□`. -/
def Vq (q : (toScales S hM hR).Idx) : Set (Site NF) :=
  {x | (dinf (bc S.toDomSeq x) (cq S hM hR q) : ℝ) ≤ 5 * ((S.L ^ S.mM : ℕ) : ℝ) * (S.L : ℝ) ^ (q.1 : ℕ)}

/-- **The blocks common to `S` and the comparison sequence** (the hypothesis `hV` of `local_bound`). -/
theorem hV_cube {q : (toScales S hM hR).Idx} (hI : (toDomains S hM hR).InD q) {i : ℕ} {hi : i + 1 ≤ S.k}
    {Λ : Set (Tor (ellT S.L S.mT))} {hΛ : IsCubes S (i + 1) Λ}
    (hag : ∀ x : Site NF, (dinf x (cq S hM hR q) : ℝ) ≤ 6 * ((S.L ^ S.mM : ℕ) : ℝ) * (S.L : ℝ) ^ (q.1 : ℕ) →
      ∀ n, (x ∈ ((twoLayer S i hi Λ hΛ).toDomSeq).Ω n ↔ x ∈ (S.toDomSeq).Ω n)) :
    ∀ x ∈ Vq S hM hR q, (S.toDomSeq).sc x = ((twoLayer S i hi Λ hΛ).toDomSeq).sc x ∧
      ∀ x' ∈ Blk S.toDomSeq ((S.toDomSeq).sc x) (bc S.toDomSeq x), x' ∈ Vq S hM hR q := by
  intro x hx
  have hx5 : (dinf (bc S.toDomSeq x) (cq S hM hR q) : ℝ) ≤ 5 * ((S.L ^ S.mM : ℕ) : ℝ) * (S.L : ℝ) ^ (q.1 : ℕ) := hx
  have hp : (0 : ℝ) ≤ ((S.L ^ S.mM : ℕ) : ℝ) * (S.L : ℝ) ^ (q.1 : ℕ) := by positivity
  have hy6 : (dinf (bc S.toDomSeq x) (cq S hM hR q) : ℝ) ≤ 6 * ((S.L ^ S.mM : ℕ) : ℝ) * (S.L : ℝ) ^ (q.1 : ℕ) := by
    linarith
  have hsc : (S.toDomSeq).sc x ≤ (q.1 : ℕ) + 1 := by
    rw [← sc_bc S.toDomSeq x]
    by_contra hc
    exact not_mem_two S hM hR hI hy6 (((S.toDomSeq).mem_iff _ _).2 (by omega))
  have hxb := mem_blk_bc S x
  have hdb := dinf_lt_of_blk S hxb
  rw [sc_bc] at hdb
  have hL1 : (1 : ℝ) ≤ S.L := by exact_mod_cast S.Lpos
  have hpow : (S.L : ℝ) ^ (S.toDomSeq).sc x ≤ ((S.L ^ S.mM : ℕ) : ℝ) * (S.L : ℝ) ^ (q.1 : ℕ) := by
    calc (S.L : ℝ) ^ (S.toDomSeq).sc x ≤ (S.L : ℝ) ^ ((q.1 : ℕ) + 1) := pow_le_pow_right₀ hL1 hsc
      _ = (S.L : ℝ) * (S.L : ℝ) ^ (q.1 : ℕ) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (L_le_M_real S hM) (by positivity)
  have hx6 : (dinf x (cq S hM hR q) : ℝ) ≤ 6 * ((S.L ^ S.mM : ℕ) : ℝ) * (S.L : ℝ) ^ (q.1 : ℕ) := by
    have := dinf_triangle x (bc S.toDomSeq x) (cq S hM hR q)
    have h' : (dinf x (cq S hM hR q) : ℝ) ≤ dinf x (bc S.toDomSeq x) + dinf (bc S.toDomSeq x) (cq S hM hR q) := by
      exact_mod_cast this
    linarith
  refine ⟨(sc_two_eq x (hag x hx6)).symm, fun x' hx' => ?_⟩
  have hb : bc S.toDomSeq x' = bc S.toDomSeq x := by
    rw [fiber_eq]
    have : Blocks.cen S.L ((S.toDomSeq).sc x) x' = bc S.toDomSeq x := (Finset.mem_filter.1 hx').2
    rw [sc_bc]; exact this
  show (dinf (bc S.toDomSeq x') (cq S hM hR q) : ℝ) ≤ _
  rw [hb]; exact hx5

omit hM hR in
lemma mem_QB_iff {T : Lattices.SeqDom} (q' : ℕ × Site (SequenceAverages.N0 T) × Fin 4) :
    q' ∈ QB T ↔ q'.1 < T.k + 1 ∧ InLat T.L q'.1 q'.2.1 ∧ T.IsLayerBond q'.1 (T.ef q'.2.1) q'.2.2 := by
  unfold QB
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_univ, and_true]

lemma Qt_ne_zero {A : Fin 4 → Site NF → Matrix (Fin N) (Fin N) ℂ} {j : ℕ} {y : Site NF} {μ : Fin 4}
    (h : Qt S A j y μ ≠ 0) :
    ∃ x ∈ Blk S.toDomSeq j y, ∃ t ∈ range (S.L ^ j), A μ (x + ((t : ℕ) : ZMod NF) • CoreLean.unit NF μ) ≠ 0 := by
  unfold Qt at h
  have h1 : ∑ x ∈ Blk S.toDomSeq j y, ∑ t ∈ range (S.L ^ j), A μ (x + ((t : ℕ) : ZMod NF) • CoreLean.unit NF μ) ≠ 0 :=
    fun h0 => h (by rw [h0, smul_zero])
  obtain ⟨x, hx, hx0⟩ := Finset.exists_ne_zero_of_sum_ne_zero h1
  obtain ⟨t, ht, ht0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx0
  exact ⟨x, hx, t, ht, ht0⟩

/-- **The constraint form of the comparison sequence** (the hypothesis `hQ` of `local_bound`): for a `1`-form
supported within `Ma_j` of `c_□`, the bonds of the layers of `S'` whose boxes meet the support are bonds of the layers
of `S`, so that `⟨X^*, Q_{S'}^*Q_{S'}X⟩ ≤ ⟨X^*, Q^*QX⟩`. -/
theorem Qnorm_two_le {q : (toScales S hM hR).Idx} {i : ℕ} {hi : i + 1 ≤ S.k}
    {Λ : Set (Tor (ellT S.L S.mT))} {hΛ : IsCubes S (i + 1) Λ} (hij : i ≤ (q.1 : ℕ))
    (hag : ∀ x : Site NF, (dinf x (cq S hM hR q) : ℝ) ≤ 6 * ((S.L ^ S.mM : ℕ) : ℝ) * (S.L : ℝ) ^ (q.1 : ℕ) →
      ∀ n, (x ∈ ((twoLayer S i hi Λ hΛ).toDomSeq).Ω n ↔ x ∈ (S.toDomSeq).Ω n))
    (X : Fin 4 → Site NF → Matrix (Fin N) (Fin N) ℂ)
    (hX : ∀ μ x, X μ x ≠ 0 → (dinf x (cq S hM hR q) : ℝ) ≤ ((S.L ^ S.mM : ℕ) : ℝ) * (S.L : ℝ) ^ (q.1 : ℕ)) :
    Qnorm (twoLayer S i hi Λ hΛ) X ≤ Qnorm S X := by
  set F : ℕ × Site NF × Fin 4 → ℝ := fun q' =>
    ((S.L ^ q'.1 : ℕ) : ℝ) ^ 2 * ‖emb (N := N) (Qt S X q'.1 q'.2.1 q'.2.2)‖ ^ 2
  have hF0 : ∀ q', 0 ≤ F q' := fun q' => by positivity
  have e1 : Qnorm (twoLayer S i hi Λ hΛ) X = ∑ q' ∈ QB (twoLayer S i hi Λ hΛ), F q' := rfl
  have e2 : Qnorm S X = ∑ q' ∈ QB S, F q' := rfl
  rw [e1, e2, ← Finset.sum_filter_ne_zero]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun q' _ _ => hF0 q'
  intro q' hq'
  obtain ⟨j', y0, μ⟩ := q'
  obtain ⟨y, rfl⟩ : ∃ y : Site NF, y = y0 := ⟨y0, rfl⟩
  rw [Finset.mem_filter] at hq'
  obtain ⟨hqT, hF⟩ := hq'
  have hQt : Qt S X j' y μ ≠ 0 := fun h0 => hF (by
    show ((S.L ^ j' : ℕ) : ℝ) ^ 2 * ‖emb (N := N) (Qt S X j' y μ)‖ ^ 2 = 0
    rw [h0, norm_emb_sq]; simp [hs2, ntr])
  obtain ⟨x, hx, t, ht, hX0⟩ := Qt_ne_zero S hQt
  rw [Finset.mem_range] at ht
  have hp := hX μ _ hX0
  rw [mem_QB_iff] at hqT
  refine (mem_QB_iff (T := S) ((j', y, μ) : ℕ × Site NF × Fin 4)).2 ?_
  obtain ⟨hmem, hlat, hTL, hend, hy1, hb1⟩ := hqT
  refine ⟨hmem, hlat, hTL, ?_⟩
  -- the scale of the bond is at most `i + 1`
  have hj' : j' ≤ i + 1 := by
    by_contra hc
    rcases hend with he | he
    · have : (twoLayer S i hi Λ hΛ).Ω j' = ∅ := twoLayer_high (by omega)
      rw [this] at he; exact he
    · have : (twoLayer S i hi Λ hΛ).Ω j' = ∅ := twoLayer_high (by omega)
      rw [this] at he; exact he
  -- the ends lie within `3Ma_j` of the centre
  have hL1 : (1 : ℝ) ≤ S.L := by exact_mod_cast S.Lpos
  have hpow : 2 * (S.L : ℝ) ^ j' ≤ 2 * (((S.L ^ S.mM : ℕ) : ℝ) * (S.L : ℝ) ^ (q.1 : ℕ)) := by
    have h1 : (S.L : ℝ) ^ j' ≤ (S.L : ℝ) ^ ((q.1 : ℕ) + 1) := pow_le_pow_right₀ hL1 (by omega)
    have h2 : (S.L : ℝ) ^ ((q.1 : ℕ) + 1) ≤ ((S.L ^ S.mM : ℕ) : ℝ) * (S.L : ℝ) ^ (q.1 : ℕ) := by
      rw [pow_succ, mul_comm]
      exact mul_le_mul_of_nonneg_right (L_le_M_real S hM) (by positivity)
    linarith
  have hnear : ∀ s : ℕ, s ≤ S.L ^ j' → (dinf (y + ((s : ℕ) : ZMod NF) • CoreLean.unit NF μ) (cq S hM hR q) : ℝ) ≤
      6 * ((S.L ^ S.mM : ℕ) : ℝ) * (S.L : ℝ) ^ (q.1 : ℕ) := by
    intro s hs
    have hd := box_dinf S hx μ ht.le hs
    have htri := dinf_triangle (y + ((s : ℕ) : ZMod NF) • CoreLean.unit NF μ)
      (x + ((t : ℕ) : ZMod NF) • CoreLean.unit NF μ) (cq S hM hR q)
    rw [dinf_comm (y + ((s : ℕ) : ZMod NF) • CoreLean.unit NF μ) (x + ((t : ℕ) : ZMod NF) • CoreLean.unit NF μ)] at htri
    have h1 : (dinf (y + ((s : ℕ) : ZMod NF) • CoreLean.unit NF μ) (cq S hM hR q) : ℝ) ≤
        (dinf (x + ((t : ℕ) : ZMod NF) • CoreLean.unit NF μ) (y + ((s : ℕ) : ZMod NF) • CoreLean.unit NF μ) : ℝ) +
          dinf (x + ((t : ℕ) : ZMod NF) • CoreLean.unit NF μ) (cq S hM hR q) := by exact_mod_cast htri
    have h2 : (dinf (x + ((t : ℕ) : ZMod NF) • CoreLean.unit NF μ) (y + ((s : ℕ) : ZMod NF) • CoreLean.unit NF μ) : ℝ) ≤
        2 * (S.L : ℝ) ^ j' := by
      have := Nat.cast_le (α := ℝ) |>.2 hd; push_cast at this; exact this
    have hp0 : (0 : ℝ) ≤ ((S.L ^ S.mM : ℕ) : ℝ) * (S.L : ℝ) ^ (q.1 : ℕ) := by positivity
    linarith
  have hy := hag y (by simpa using hnear 0 (Nat.zero_le _))
  have hyn := hag (ynext S j' y μ) (hnear (S.L ^ j') le_rfl)
  have hnext : S.bend j' (S.ef y) μ = S.ef (ynext S j' y μ) := by rw [ef_ynext]; rfl
  have hnextT : (twoLayer S i hi Λ hΛ).bend j' ((twoLayer S i hi Λ hΛ).ef y) μ = S.ef (ynext S j' y μ) := hnext
  rw [hnextT] at hend hb1
  rw [hnext]
  refine ⟨?_, (hy (j' + 1)).not.1 hy1, (hyn (j' + 1)).not.1 hb1⟩
  rcases hend with he | he
  · exact Or.inl ((hy j').1 he)
  · exact Or.inr ((hyn j').1 he)

end PartitionUnity

namespace SFBounds

open Lattices SeqDom Blocks SmallFieldBlocks SFBox SFBox.SeqDomBox SmallFieldDecay SequenceOperators
open scoped Matrix.Norms.L2Operator

variable {S : Lattices.SeqDom} {N : ℕ}

/-- **The hypotheses of `prop:sf-block` for the comparison sequence** at the trivial configuration: the conditions
on `RM` and `δ` are those of `S`, since the two sequences have the same `L`, `R`, and `M`. -/
theorem scalarHyp_two [NeZero N] {δ : ℝ} (H : ScalarHyp (N := N) S (X0 S) 0 (W1 S) 0 Set.univ δ) {i : ℕ}
    {hi : i + 1 ≤ S.k} {Λ : Set (Tor (ellT S.L S.mT))} {hΛ : IsCubes S (i + 1) Λ} :
    ScalarHyp (N := N) (twoLayer S i hi Λ hΛ) (X0 (twoLayer S i hi Λ hΛ)) 0 (W1 (twoLayer S i hi Λ hΛ)) 0
      Set.univ δ where
  hX := ⟨fun i x μ _ _ => by simp, fun i x μ ν _ _ => by simp⟩
  hα0 := le_rfl
  hα := by norm_num
  hη := le_rfl
  hW1 := fun y _ x _ Z => by simp [Ad, hs, hs2, ntr]
  hW := wbound_triv _
  hsmall := by norm_num
  hRM8 := H.hRM8
  hRMs := H.hRMs
  hRM1 := H.hRM1
  hδ0 := H.hδ0
  hδ := H.hδ
  hD := fun _ _ => trivial

end SFBounds

namespace PartitionUnity

open Lattices SFBounds Blocks SmallFieldBlocks

/-- **The weight of the cut-off**: `φ(x) = κ min_{z ∈ B} d(x, z)`. -/
def phW (T : Lattices.SeqDom) (B : Finset (Site (SequenceAverages.N0 T))) (hB : B.Nonempty) (κ : ℝ)
    (x : Site (SequenceAverages.N0 T)) : ℝ :=
  κ * B.inf' hB fun z => T.dF x z

lemma phW_lip (T : Lattices.SeqDom) (B : Finset (Site (SequenceAverages.N0 T))) (hB : B.Nonempty) {κ : ℝ}
    (hκ : 0 ≤ κ) (x x' : Site (SequenceAverages.N0 T)) : |phW T B hB κ x - phW T B hB κ x'| ≤ κ * T.dF x x' := by
  have key : ∀ a b, B.inf' hB (fun z => T.dF a z) ≤ T.dF a b + B.inf' hB (fun z => T.dF b z) := by
    intro a b
    obtain ⟨z, hz, hzeq⟩ := Finset.exists_mem_eq_inf' hB (fun z => T.dF b z)
    rw [hzeq]
    exact (Finset.inf'_le _ hz).trans (T.dF_triangle a b z)
  unfold phW
  rw [abs_le]
  constructor
  · have := key x' x
    rw [T.dF_comm x' x] at this
    nlinarith
  · have := key x x'
    nlinarith

lemma phW_zero (T : Lattices.SeqDom) (B : Finset (Site (SequenceAverages.N0 T))) (hB : B.Nonempty) (κ : ℝ)
    {x : Site (SequenceAverages.N0 T)} (hx : x ∈ B) : phW T B hB κ x = 0 := by
  unfold phW
  have h1 : B.inf' hB (fun z => T.dF x z) ≤ 0 := by
    refine (Finset.inf'_le _ hx).trans (le_of_eq ?_)
    unfold Lattices.SeqDom.dF; rw [wdist_self]; rfl
  have h2 : 0 ≤ B.inf' hB (fun z => T.dF x z) := (Finset.le_inf'_iff hB _).2 fun z _ => T.dF_nonneg x z
  rw [le_antisymm h1 h2, mul_zero]

lemma phW_nonneg (T : Lattices.SeqDom) (B : Finset (Site (SequenceAverages.N0 T))) (hB : B.Nonempty) {κ : ℝ}
    (hκ : 0 ≤ κ) (x : Site (SequenceAverages.N0 T)) : 0 ≤ phW T B hB κ x :=
  mul_nonneg hκ ((Finset.le_inf'_iff hB _).2 fun z _ => T.dF_nonneg x z)

lemma phW_ge (T : Lattices.SeqDom) (B : Finset (Site (SequenceAverages.N0 T))) (hB : B.Nonempty) {κ r : ℝ}
    (hκ : 0 ≤ κ) {x : Site (SequenceAverages.N0 T)} (h : ∀ z ∈ B, r ≤ T.dF x z) : κ * r ≤ phW T B hB κ x :=
  mul_le_mul_of_nonneg_left ((Finset.le_inf'_iff hB _).2 h) hκ

end PartitionUnity

namespace PartitionUnity

/-- The bound of the constant of the cut-off, uniform in the scale of the cube. -/
def Kbar (L κ CI Cb : ℝ) : ℝ :=
  CI + 288 * (1 + CI) * ((512 / 3) ^ 2 * L ^ 4 + 512 * (32 / 9) ^ 2 * κ ^ 2 * L ^ 6 + 81 * Cb ^ 2 * L ^ 4 +
    128 * (32 / 9) ^ 2 * L ^ 2)

/-- **The constant of the cut-off is bounded uniformly in the scale**: with `t = a_i`, `H₁ = h + 1 ≥ t/2`, the
first differences `g₁ = 16/(9H₁)`, the Laplacian `g₂ = 128/(3H₁²)`, and `ε = κLt⁻¹`. -/
lemma bracket_le {L t H1 κ CI Cb : ℝ} (ht : 0 < t) (hH : t / 2 ≤ H1) (hCI : 0 ≤ CI) (hL : 0 ≤ L) :
    CI + ((128 / (3 * H1 ^ 2)) ^ 2 + 512 * (16 / (9 * H1)) ^ 2 * (κ * L * t⁻¹) ^ 2 + 81 * Cb ^ 2 * (t ^ 4)⁻¹) *
        (t ^ 2 * L ^ 2) * (288 * (t ^ 2 * L ^ 2) * (1 + CI)) +
      128 * (16 / (9 * H1)) ^ 2 * (288 * (t ^ 2 * L ^ 2) * (1 + CI)) ≤ Kbar L κ CI Cb := by
  have hH0 : 0 < H1 := by linarith
  set s := t / H1 with hs
  have hs0 : 0 ≤ s := by positivity
  have hs2 : s ≤ 2 := by rw [hs, div_le_iff₀ hH0]; linarith
  have e : CI + ((128 / (3 * H1 ^ 2)) ^ 2 + 512 * (16 / (9 * H1)) ^ 2 * (κ * L * t⁻¹) ^ 2 + 81 * Cb ^ 2 * (t ^ 4)⁻¹) *
        (t ^ 2 * L ^ 2) * (288 * (t ^ 2 * L ^ 2) * (1 + CI)) +
      128 * (16 / (9 * H1)) ^ 2 * (288 * (t ^ 2 * L ^ 2) * (1 + CI)) =
      CI + 288 * (1 + CI) * ((128 / 3) ^ 2 * s ^ 4 * L ^ 4 + 512 * (16 / 9) ^ 2 * κ ^ 2 * L ^ 6 * s ^ 2 +
        81 * Cb ^ 2 * L ^ 4 + 128 * (16 / 9) ^ 2 * L ^ 2 * s ^ 2) := by
    rw [hs]; field_simp; ring
  rw [e]
  unfold Kbar
  have h1 : s ^ 2 ≤ 4 := by nlinarith
  have h2 : s ^ 4 ≤ 16 := by nlinarith
  have hA : (128 / 3) ^ 2 * s ^ 4 * L ^ 4 ≤ (512 / 3) ^ 2 * L ^ 4 := by
    have : 0 ≤ L ^ 4 := by positivity
    nlinarith
  have hB : 512 * (16 / 9) ^ 2 * κ ^ 2 * L ^ 6 * s ^ 2 ≤ 512 * (32 / 9) ^ 2 * κ ^ 2 * L ^ 6 := by
    have : 0 ≤ κ ^ 2 * L ^ 6 := by positivity
    nlinarith
  have hC : 128 * (16 / 9) ^ 2 * L ^ 2 * s ^ 2 ≤ 128 * (32 / 9) ^ 2 * L ^ 2 := by
    have : 0 ≤ L ^ 2 := by positivity
    nlinarith
  have h288 : 0 ≤ 288 * (1 + CI) := by positivity
  have hsum : (128 / 3) ^ 2 * s ^ 4 * L ^ 4 + 512 * (16 / 9) ^ 2 * κ ^ 2 * L ^ 6 * s ^ 2 + 81 * Cb ^ 2 * L ^ 4 +
      128 * (16 / 9) ^ 2 * L ^ 2 * s ^ 2 ≤ (512 / 3) ^ 2 * L ^ 4 + 512 * (32 / 9) ^ 2 * κ ^ 2 * L ^ 6 +
        81 * Cb ^ 2 * L ^ 4 + 128 * (32 / 9) ^ 2 * L ^ 2 := by linarith
  have := mul_le_mul_of_nonneg_left hsum h288
  linarith

end PartitionUnity

namespace PartitionUnity

open Lattices SeqDom SFBounds SFLocal Blocks SmallFieldBlocks SmallFieldDecay SFBox SequenceOperators

variable (S : Lattices.SeqDom) (hM : 12 ≤ S.L ^ S.mM) (hR : 12 * S.L ≤ S.R) {N : ℕ}

local notation "NF" => SequenceAverages.N0 S
local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "RMS" => ((S.R * S.L ^ S.mM : ℕ) : ℝ)

/-- The side `Ma_j` of a cube of `𝒟_j`, in the units `a₀ = 1`. -/
def nq (q : (toScales S hM hR).Idx) : ℕ := S.L ^ S.mM * S.L ^ (q.1 : ℕ)

/-- **The cut-off of a cube**: `χ = 1` within `3Ma_j` of `c_□` and `χ = 0` beyond `4Ma_j`. -/
def chiq (q : (toScales S hM hR).Idx) (x : Site NF) : ℝ :=
  chiC ((nq S hM hR q - 1) / 2) (3 * nq S hM hR q - 1) (cq S hM hR q) x

/-- The rate of the weight of the cut-off. -/
def kap0 (S : Lattices.SeqDom) (N : ℕ) (δ : ℝ) : ℝ := min (1 / 2 * (7 / 32 * thetaB S N δ)) (1 / (128 * S.L))

lemma nq_odd (q : (toScales S hM hR).Idx) : nq S hM hR q % 2 = 1 := by
  unfold nq
  exact Nat.odd_iff.1 ((S.L_odd.pow).mul S.L_odd.pow)

lemma nq_ge (q : (toScales S hM hR).Idx) : 12 ≤ nq S hM hR q := by
  unfold nq
  exact hM.trans (Nat.le_mul_of_pos_right _ (pow_pos S.Lpos _))

lemma nq_real (q : (toScales S hM hR).Idx) :
    ((nq S hM hR q : ℕ) : ℝ) = ((S.L ^ S.mM : ℕ) : ℝ) * (S.L : ℝ) ^ (q.1 : ℕ) := by
  unfold nq; push_cast; ring

lemma chiq_one (q : (toScales S hM hR).Idx) {x : Site NF} (hx : dinf x (cq S hM hR q) ≤ 3 * nq S hM hR q) :
    chiq S hM hR q x = 1 := by
  have hn := nq_ge S hM hR q
  unfold chiq
  refine chiC_one _ _ _ _ fun ν => ?_
  have h1 := cd_le_dinf x (cq S hM hR q) ν
  unfold cd at h1
  rw [Int.abs_eq_natAbs]
  omega

lemma dinf_self' (x : Site NF) : dinf x x = 0 := by
  unfold dinf; simp [cd]

omit hM hR in
lemma dinf_sub_unit' (x : Site NF) (μ : Fin 4) : dinf (x - CoreLean.unit NF μ) x ≤ 1 := by
  unfold dinf
  refine Finset.sup_le fun ν _ => ?_
  by_cases h : ν = μ
  · subst h
    have e : (x - CoreLean.unit NF ν) ν - x ν = ((-1 : ℤ) : ZMod NF) := by
      simp [CoreLean.unit]
    rw [e]
    exact (cd_intCast_le (N := NF) (-1)).trans (by simp)
  · have e : (x - CoreLean.unit NF μ) ν - x ν = 0 := by
      simp [CoreLean.unit, Pi.single_eq_of_ne h]
    rw [e]; simp [cd]

omit hM hR in
lemma dinf_add_unit' (x : Site NF) (μ : Fin 4) : dinf (x + CoreLean.unit NF μ) x ≤ 1 := by
  unfold dinf
  refine Finset.sup_le fun ν _ => ?_
  by_cases h : ν = μ
  · subst h
    have e : (x + CoreLean.unit NF ν) ν - x ν = ((1 : ℤ) : ZMod NF) := by
      simp [CoreLean.unit]
    rw [e]
    exact (cd_intCast_le (N := NF) 1).trans (by simp)
  · have e : (x + CoreLean.unit NF μ) ν - x ν = 0 := by
      simp [CoreLean.unit, Pi.single_eq_of_ne h]
    rw [e]; simp [cd]

/-- The sites where `h_□A` or `∂^*(h_□A)` does not vanish lie within `(2/3)Ma_j + 3/2` of `c_□`. -/
lemma dinf_of_f (q : (toScales S hM hR).Idx) (A : Fin 4 → Site NF → Mat) {x : Site NF}
    (hx : Ds1L a1 (cfgX (X0 S)) (locA S (hL S hM hR q) A) x ≠ 0) :
    (dinf x (cq S hM hR q) : ℝ) < 2 / 3 * ((nq S hM hR q : ℕ) : ℝ) + 3 / 2 := by
  rw [Ds1L_triv] at hx
  obtain ⟨μ, -, hμ⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx
  rw [nq_real]
  by_cases h1 : hL S hM hR q (x - CoreLean.unit NF μ) = 0
  · have h2 : hL S hM hR q x ≠ 0 := by
      intro h2; apply hμ; simp only [locA, h1, h2, Complex.ofReal_zero, zero_smul, sub_self]
    have := dinf_cq_of_hL S hM hR h2
    linarith
  · have := dinf_cq_of_hL S hM hR h1
    have h3 := dinf_triangle x (x - CoreLean.unit NF μ) (cq S hM hR q)
    rw [dinf_comm x (x - CoreLean.unit NF μ)] at h3
    have h4 := dinf_sub_unit' S x μ
    have h5 : (dinf x (cq S hM hR q) : ℝ) ≤ dinf (x - CoreLean.unit NF μ) x + dinf (x - CoreLean.unit NF μ) (cq S hM hR q) := by
      exact_mod_cast h3
    have h6 : (dinf (x - CoreLean.unit NF μ) x : ℝ) ≤ 1 := by exact_mod_cast h4
    linarith

end PartitionUnity

namespace PartitionUnity

open Lattices SeqDom SFBounds SFLocal Blocks SmallFieldBlocks SmallFieldDecay SFBox SequenceOperators

variable (S : Lattices.SeqDom) (hM : 12 ≤ S.L ^ S.mM) (hR : 12 * S.L ≤ S.R) {N : ℕ}

local notation "NF" => SequenceAverages.N0 S
local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "RMS" => ((S.R * S.L ^ S.mM : ℕ) : ℝ)

/-- **The cut-off bound for a cube** (eq:sf-cut-off, the hypothesis `hcut` of `local_bound`) on a torus wider than
`8Ma_j + 4`: `‖Δ(λ^S - λ̃)‖² ≤ 8e^{-2κM/L}K̄‖∂^*X‖²` for `X = h_□A`. -/
theorem hcut_big [NeZero N] {δ : ℝ} (H : ScalarHyp (N := N) S (X0 S) 0 (W1 S) 0 Set.univ δ)
    (hRMb : (S.toContSeq).r1 (1 / 2) (1 / 32 * δ) ≤ RMS) (hRMs4 : 32 * Real.log S.L / (1 / 4 * δ) ≤ RMS)
    (hsmallT : CTd S N δ 0 0 * (S.toContSeq).c1 (1 / 2) (1 / 32 * δ) ≤ gammaB N / 4)
    (hRMθs : 32 * Real.log S.L / (thetaB S N δ / 2) ≤ RMS)
    (hRMθc : (S.toContSeq).r1 (1 / 2) (7 / 16 * thetaB S N δ) ≤ RMS)
    (hRMsum : (S.toContSeq).r1 (1 / 2) (7 / 32 * thetaB S N δ) ≤ RMS)
    (q : (toScales S hM hR).Idx) {i : ℕ} {hi : i + 1 ≤ S.k} {Λ : Set (Tor (ellT S.L S.mT))}
    {hΛ : IsCubes S (i + 1) Λ} (hij : i ≤ (q.1 : ℕ)) (A : Fin 4 → Site NF → Mat)
    (hbig : 2 * (4 * nq S hM hR q + 2) ≤ NF) :
    ∑ x, hs2 (Ds1L a1 (cfgX (X0 S)) (D0L a1 (cfgX (X0 S))
        (minim (twoLayer S i hi Λ hΛ) (Ds1L a1 (cfgX (X0 S)) (locA S (hL S hM hR q) A)) -
          corr (twoLayer S i hi Λ hΛ) (fun x => (chiq S hM hR q x : ℂ) •
            minim (twoLayer S i hi Λ hΛ) (Ds1L a1 (cfgX (X0 S)) (locA S (hL S hM hR q) A)) x))) x) ≤
      8 * Real.exp (-(2 * (kap0 S N δ * (((S.L ^ S.mM : ℕ) : ℝ) / S.L)))) *
        Kbar S.L (kap0 S N δ) (CIone S N δ (kap0 S N δ)) Cbump *
        ∑ x, hs2 (Ds1L a1 (cfgX (X0 S)) (locA S (hL S hM hR q) A) x) := by
  set T := twoLayer S i hi Λ hΛ
  set n := nq S hM hR q
  set c := cq S hM hR q
  set f := Ds1L a1 (cfgX (X0 S)) (locA S (hL S hM hR q) A)
  set χ := chiq S hM hR q
  set κ := kap0 S N δ
  have hn := nq_ge S hM hR q
  have hodd := nq_odd S hM hR q
  have hL1 : (1 : ℝ) ≤ S.L := by exact_mod_cast S.Lpos
  have hL0 : (0 : ℝ) < S.L := by linarith
  have hθ : 0 < thetaB S N δ := H.thetaB_pos (N := N)
  have hκ0 : 0 ≤ κ := le_min (by positivity) (by positivity)
  have hκL : κ ≤ 1 / (128 * S.L) := min_le_right _ _
  have hκθ : κ ≤ 1 / 2 * (7 / 32 * thetaB S N δ) := min_le_left _ _
  -- the parameters of the cut-off
  set h := (n - 1) / 2
  set D := 3 * n - 1
  have hh : 2 * h + 1 = n := by omega
  have hchn : 2 * (D + 2 * h + 4) ≤ NF := by omega
  -- the comparison sequence
  have HT := scalarHyp_two (hi := hi) (Λ := Λ) (hΛ := hΛ) H
  have hsc : ∀ x, i ≤ (T.toDomSeq).sc x ∧ (T.toDomSeq).sc x ≤ i + 1 := fun x => sc_two_mem (hi := hi) (Λ := Λ) (hΛ := hΛ) x
  have hRM1 : 1 ≤ S.R * S.L ^ S.mM := Nat.one_le_iff_ne_zero.2 (by
    have := S.one_le_R; have := S.Lpos; positivity)
  -- the weight
  set B : Finset (Site NF) := Finset.univ.filter fun z => dinf z c ≤ n
  have hB : B.Nonempty := ⟨c, Finset.mem_filter.2 ⟨Finset.mem_univ _, by rw [dinf_self']; omega⟩⟩
  set ph := phW T B hB κ
  set M : ℝ := ((S.L ^ S.mM : ℕ) : ℝ)
  set Φ := κ * (M / S.L)
  have hnM : ((n : ℕ) : ℝ) = M * (S.L : ℝ) ^ (q.1 : ℕ) := nq_real S hM hR q
  -- far from `c` the weight is at least `Φ`
  have hfar : ∀ x, 2 * n ≤ dinf x c → Φ ≤ ph x := by
    intro x hx
    refine phW_ge T B hB hκ0 fun z0 hz => ?_
    obtain ⟨z, rfl⟩ : ∃ z : Site NF, z = z0 := ⟨z0, rfl⟩
    have hz' : dinf z c ≤ n := (Finset.mem_filter.1 hz).2
    have htri : dinf x c ≤ dinf x z + dinf z c := dinf_triangle x z c
    have hxz : n ≤ dinf x z := by omega
    have hm : T.Ω (i + 1 + 1) = ∅ := twoLayer_high (by omega)
    have hdF := dF_ge_dinf T hm x z
    have hpow : (S.L : ℝ) ^ (i + 1) ≤ (S.L : ℝ) * (S.L : ℝ) ^ (q.1 : ℕ) := by
      rw [pow_succ, mul_comm]; exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL1 hij) hL0.le
    have hp : (0 : ℝ) < (S.L : ℝ) ^ (i + 1) := by positivity
    have hM0 : (0 : ℝ) ≤ M := by positivity
    have h1 : M / S.L ≤ (n : ℝ) / (S.L : ℝ) ^ (i + 1) := by
      rw [div_le_div_iff₀ hL0 hp, hnM]
      calc M * (S.L : ℝ) ^ (i + 1) ≤ M * ((S.L : ℝ) * (S.L : ℝ) ^ (q.1 : ℕ)) := mul_le_mul_of_nonneg_left hpow hM0
        _ = M * (S.L : ℝ) ^ (q.1 : ℕ) * S.L := by ring
    have h2 : (n : ℝ) / (S.L : ℝ) ^ (i + 1) ≤ (dinf x z : ℝ) / (S.L : ℝ) ^ (i + 1) :=
      div_le_div_of_nonneg_right (by exact_mod_cast hxz) hp.le
    exact h1.trans (h2.trans hdF)
  -- the cut-off is `1` near `c`
  have hone : ∀ x, dinf x c ≤ 3 * n → χ x = 1 := fun x hx => chiq_one S hM hR q hx
  have hnear : ∀ x, χ x ≠ 1 → 3 * n < dinf x c := fun x hx => by
    by_contra h'; exact hx (hone x (by omega))
  -- the support of `f`
  have hfsupp : ∀ x, f x ≠ 0 → x ∈ B := by
    intro x hx
    have h1 := dinf_of_f S hM hR q A hx
    have h2 : (dinf x c : ℝ) ≤ n := by
      have : (12 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, by exact_mod_cast h2⟩
  have hfχ : ∀ x, χ x ≠ 1 → f x = 0 := by
    intro x hx
    by_contra hfx
    have := (Finset.mem_filter.1 (hfsupp x hfx)).2
    have := hnear x hx
    omega
  -- the bounds of the cut-off
  have hg1 : ∀ x ν, |χ (x + CoreLean.unit NF ν) - χ x| ≤ 16 / (9 * ((h : ℝ) + 1)) ∧
      |χ (x - CoreLean.unit NF ν) - χ x| ≤ 16 / (9 * ((h : ℝ) + 1)) := fun x ν => chiC_unit h D hchn c x ν
  have hg2 : ∀ x, |lapR T χ x| ≤ 128 / (3 * ((h : ℝ) + 1) ^ 2) := fun x => chiC_lap h D hchn c x
  -- the weight at the bonds
  set ε := κ * S.L * ((S.L : ℝ) ^ i)⁻¹
  have hε : ε ≤ 1 := by
    have h1 : ((S.L : ℝ) ^ i)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hL1)
    have h2 : κ * S.L ≤ 1 / 128 := by
      have := mul_le_mul_of_nonneg_right hκL hL0.le
      have e : 1 / (128 * (S.L : ℝ)) * S.L = 1 / 128 := by field_simp
      linarith
    calc ε ≤ κ * S.L * 1 := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ 1 := by linarith
  have hunit : ∀ x : Site NF, ∀ ν, T.dF x (x + CoreLean.unit NF ν) ≤ S.L * ((S.L : ℝ) ^ i)⁻¹ ∧
      T.dF x (x + -CoreLean.unit NF ν) ≤ S.L * ((S.L : ℝ) ^ i)⁻¹ := by
    intro x ν
    have hsci : ∀ z, ((S.L : ℝ) ^ (T.toDomSeq).sc z)⁻¹ ≤ ((S.L : ℝ) ^ i)⁻¹ := fun z =>
      inv_anti₀ (by positivity) (pow_le_pow_right₀ hL1 (hsc z).1)
    have hw := T.wdist_unit_le_sc hRM1 x ν
    have hw2 : T.dF (x + -CoreLean.unit NF ν) x ≤ S.L * ((S.L : ℝ) ^ (T.toDomSeq).sc x)⁻¹ := by
      let x' : Site (SequenceAverages.N0 T) := x
      have h := (T.wdist_unit_le_sc hRM1 (x' + -CoreLean.unit (SequenceAverages.N0 T) ν) ν).2
      have e : x' + -CoreLean.unit (SequenceAverages.N0 T) ν + CoreLean.unit (SequenceAverages.N0 T) ν = x' := by
        abel
      rw [e] at h
      exact h
    constructor
    · exact hw.1.trans (mul_le_mul_of_nonneg_left (hsci x) hL0.le)
    · exact (le_of_eq (T.dF_comm _ _)).trans (hw2.trans (mul_le_mul_of_nonneg_left (hsci x) hL0.le))
  have hphb : ∀ (x : Site NF) ν, |ph x - ph (x + CoreLean.unit NF ν)| ≤ ε ∧ |ph x - ph (x + -CoreLean.unit NF ν)| ≤ ε := by
    intro x ν
    obtain ⟨h1, h2⟩ := hunit x ν
    constructor
    · refine (phW_lip T B hB hκ0 _ _).trans ?_
      calc κ * T.dF x (x + CoreLean.unit NF ν) ≤ κ * (S.L * ((S.L : ℝ) ^ i)⁻¹) := mul_le_mul_of_nonneg_left h1 hκ0
        _ = ε := by ring
    · refine (phW_lip T B hB hκ0 _ _).trans ?_
      calc κ * T.dF x (x + -CoreLean.unit NF ν) ≤ κ * (S.L * ((S.L : ℝ) ^ i)⁻¹) := mul_le_mul_of_nonneg_left h2 hκ0
        _ = ε := by ring
  -- the conditions on `Φ`
  have hΦ1 : ∀ x : Site NF, χ x ≠ 1 → Φ ≤ ph x := fun x hx => hfar x (by have := hnear x hx; omega)
  have hΦ2 : ∀ x : Site NF, lapR T χ x ≠ 0 → Φ ≤ ph x := by
    intro x hx
    refine hfar x ?_
    by_contra hc
    push_neg at hc
    apply hx
    unfold lapR
    refine Finset.sum_eq_zero fun ν _ => ?_
    have h1 : χ x = 1 := hone x (by omega)
    have h2 : χ (x + CoreLean.unit NF ν) = 1 := hone _ (by
      have := dinf_triangle (x + CoreLean.unit NF ν) x c; have := dinf_add_unit' S x ν; omega)
    have h3 : χ (x - CoreLean.unit NF ν) = 1 := hone _ (by
      have := dinf_triangle (x - CoreLean.unit NF ν) x c; have := dinf_sub_unit' S x ν; omega)
    show 2 * χ x - χ (x + CoreLean.unit NF ν) - χ (x - CoreLean.unit NF ν) = 0
    rw [h1, h2, h3]; ring
  have hΦ3 : ∀ (x : Site NF) ν, (χ (x + CoreLean.unit NF ν) - χ x ≠ 0 ∨ χ (x - CoreLean.unit NF ν) - χ x ≠ 0) → Φ ≤ ph x := by
    intro x ν hx
    refine hfar x ?_
    by_contra hc
    push_neg at hc
    have h1 : χ x = 1 := hone x (by omega)
    have h2 : χ (x + CoreLean.unit NF ν) = 1 := hone _ (by
      have := dinf_triangle (x + CoreLean.unit NF ν) x c; have := dinf_add_unit' S x ν; omega)
    have h3 : χ (x - CoreLean.unit NF ν) = 1 := hone _ (by
      have := dinf_triangle (x - CoreLean.unit NF ν) x c; have := dinf_sub_unit' S x ν; omega)
    rw [h1, h2, h3] at hx
    simp at hx
  -- the blocks where the average of `χλ` does not vanish
  set Z : Finset (Site NF) := Finset.univ.filter fun x => 2 * n ≤ dinf x c
  have hZ : ∀ y ∈ detB T.toDomSeq, avgW T.toDomSeq (W1 T) y (fun x => (χ x : ℂ) • minim T f x) ≠ 0 →
      ∀ x ∈ Blk T.toDomSeq ((T.toDomSeq).sc y) y, x ∈ Z := by
    intro y0 hy havg x0 hx
    obtain ⟨y, rfl⟩ : ∃ y : Site NF, y = y0 := ⟨y0, rfl⟩
    obtain ⟨x, rfl⟩ : ∃ x : Site NF, x = x0 := ⟨x0, rfl⟩
    by_contra hxZ
    have hxc : dinf x c < 2 * n := by
      by_contra h'; exact hxZ (Finset.mem_filter.2 ⟨Finset.mem_univ _, by omega⟩)
    apply havg
    have hblk : ∀ x' ∈ Blk T.toDomSeq ((T.toDomSeq).sc y) y, χ x' = 1 := by
      intro x0' hx'
      obtain ⟨x', rfl⟩ : ∃ x' : Site NF, x' = x0' := ⟨x0', rfl⟩
      have hh1 : ∀ ν, cd (x' ν - y ν) ≤ half S.L ((T.toDomSeq).sc y) := fun ν =>
        SmallFieldBlocks.cd_le_of_mem (S := T.toDomSeq) hx' ν
      have hh2 : ∀ ν, cd (x ν - y ν) ≤ half S.L ((T.toDomSeq).sc y) := fun ν =>
        SmallFieldBlocks.cd_le_of_mem (S := T.toDomSeq) hx ν
      have hhalf := two_half_add_one S.L_odd ((T.toDomSeq).sc y)
      have hpow : S.L ^ ((T.toDomSeq).sc y) ≤ n := by
        have h1 : S.L ^ ((T.toDomSeq).sc y) ≤ S.L ^ ((q.1 : ℕ) + 1) :=
          Nat.pow_le_pow_right S.Lpos (by have := (hsc y).2; omega)
        have h2 : S.L ^ ((q.1 : ℕ) + 1) ≤ n := by
          show S.L ^ ((q.1 : ℕ) + 1) ≤ S.L ^ S.mM * S.L ^ (q.1 : ℕ)
          rw [pow_succ, mul_comm]; exact Nat.mul_le_mul_right _ (L_le_M S hM)
        omega
      have hd : dinf x' x ≤ 2 * half S.L ((T.toDomSeq).sc y) := by
        unfold dinf
        refine Finset.sup_le fun ν _ => ?_
        have e : x' ν - x ν = (x' ν - y ν) + -(x ν - y ν) := by ring
        rw [e]
        refine (cd_add_le _ _).trans ?_
        have : cd (-(x ν - y ν)) = cd (x ν - y ν) := cd_neg _
        have := hh1 ν
        have := hh2 ν
        omega
      exact hone x' (by have := dinf_triangle x' x c; omega)
    have e : avgW T.toDomSeq (W1 T) y (fun x => (χ x : ℂ) • minim T f x) = avgW T.toDomSeq (W1 T) y (minim T f) := by
      rw [avgW_triv_eq T T.toDomSeq hy, avgW_triv_eq T T.toDomSeq hy]
      congr 1
      refine Finset.sum_congr rfl fun x' hx' => ?_
      rw [hblk x' hx', Complex.ofReal_one, one_smul]
    rw [e]; exact minim_null T f y hy
  -- the bound of `cutoff_bound_gen`
  have hcb := cutoff_bound_gen (T := T) HT hRMb hRMs4 hsmallT hRMθs hRMθc hRMsum hRM1 (i := i) hsc f χ ph
    (g1 := 16 / (9 * ((h : ℝ) + 1))) (g2 := 128 / (3 * ((h : ℝ) + 1) ^ 2)) (ε := ε) (κ := κ) (Φ := Φ)
    hκ0 hκθ hκL (phW_lip T B hB hκ0) hε hphb (fun x => chiC_mem _ _ _ x) hg1 hg2 hΦ1 hΦ2 hΦ3 Z hZ
    (fun x hx => hfar x (Finset.mem_filter.1 hx).2) hfχ
  -- the weight vanishes on the support of `f`
  have hsumφ : ∑ x, Real.exp (2 * ph x) * hs2 (f x) = ∑ x, hs2 (f x) := by
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hfx : f x = 0
    · rw [hfx]; simp [hs2, ntr]
    · rw [show ph x = 0 from phW_zero T B hB κ (hfsupp x hfx)]; simp
  -- the bracket
  have hCI : 0 ≤ CIone S N δ κ := by
    have h1 : 0 ≤ (S.toContSeq).c1 (1 / 2) (7 / 32 * thetaB S N δ) := by unfold Summation.ContSeq.c1; positivity
    unfold CIone; positivity
  have hH : (S.L : ℝ) ^ i / 2 ≤ (h : ℝ) + 1 := by
    have e1 : (2 * (h : ℝ) + 1) = n := by exact_mod_cast hh
    have h2 : (S.L : ℝ) ^ i ≤ n := by
      rw [hnM]
      have hM1 : (1 : ℝ) ≤ M := by
        show (1 : ℝ) ≤ ((S.L ^ S.mM : ℕ) : ℝ)
        have : (12 : ℝ) ≤ ((S.L ^ S.mM : ℕ) : ℝ) := by exact_mod_cast hM
        linarith
      calc (S.L : ℝ) ^ i ≤ (S.L : ℝ) ^ (q.1 : ℕ) := pow_le_pow_right₀ hL1 hij
        _ ≤ M * (S.L : ℝ) ^ (q.1 : ℕ) := le_mul_of_one_le_left (by positivity) hM1
    linarith
  have hbr := bracket_le (L := S.L) (t := (S.L : ℝ) ^ i) (H1 := (h : ℝ) + 1) (κ := κ) (CI := CIone S N δ κ)
    (Cb := Cbump) (by positivity) hH hCI hL0.le
  have e2 : (S.L : ℝ) ^ (2 * (i + 1)) = ((S.L : ℝ) ^ i) ^ 2 * (S.L : ℝ) ^ 2 := by ring
  have e4 : (S.L : ℝ) ^ (4 * i) = ((S.L : ℝ) ^ i) ^ 4 := by ring
  have hexp : 0 ≤ 8 * Real.exp (-(2 * Φ)) := by positivity
  have hsum0 : 0 ≤ ∑ x, hs2 (f x) := Finset.sum_nonneg fun x _ => hs2_nonneg _
  refine le_trans hcb ?_
  rw [hsumφ]
  show 8 * Real.exp (-(2 * Φ)) * (CIone S N δ κ + ((128 / (3 * ((h : ℝ) + 1) ^ 2)) ^ 2 +
      512 * (16 / (9 * ((h : ℝ) + 1))) ^ 2 * ε ^ 2 + 81 * Cbump ^ 2 * ((S.L : ℝ) ^ (4 * i))⁻¹) *
      (S.L : ℝ) ^ (2 * (i + 1)) * (288 * (S.L : ℝ) ^ (2 * (i + 1)) * (1 + CIone S N δ κ)) +
      128 * (16 / (9 * ((h : ℝ) + 1))) ^ 2 * (288 * (S.L : ℝ) ^ (2 * (i + 1)) * (1 + CIone S N δ κ))) *
      ∑ x, hs2 (f x) ≤ _
  rw [e2, e4]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbr hexp) hsum0

end PartitionUnity

namespace PartitionUnity

open Lattices SeqDom SFBounds SFLocal Blocks SmallFieldBlocks SmallFieldDecay SFBox SequenceOperators

variable (S : Lattices.SeqDom) (hM : 12 ≤ S.L ^ S.mM) (hR : 12 * S.L ≤ S.R) {N : ℕ}

local notation "NF" => SequenceAverages.N0 S
local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "RMS" => ((S.R * S.L ^ S.mM : ℕ) : ℝ)

/-- **On a torus narrower than `8Ma_j + 4`** the cut-off `χ = 1` gives `λ̃ = λ^S`. -/
theorem hcut_small [NeZero N] {i : ℕ} {hi : i + 1 ≤ S.k} {Λ : Set (Tor (ellT S.L S.mT))}
    {hΛ : IsCubes S (i + 1) Λ} (f : Site NF → Mat) :
    ∑ x, hs2 (Ds1L a1 (cfgX (X0 S)) (D0L a1 (cfgX (X0 S))
        (minim (twoLayer S i hi Λ hΛ) f - corr (twoLayer S i hi Λ hΛ) (fun x => ((1 : ℝ) : ℂ) •
          minim (twoLayer S i hi Λ hΛ) f x))) x) ≤ 0 * ∑ x, hs2 (f x) := by
  have e : corr (twoLayer S i hi Λ hΛ) (fun x => ((1 : ℝ) : ℂ) • minim (twoLayer S i hi Λ hΛ) f x) =
      minim (twoLayer S i hi Λ hΛ) f := by
    funext x
    unfold corr
    have h1 : (fun x => ((1 : ℝ) : ℂ) • minim (twoLayer S i hi Λ hΛ) f x) = minim (twoLayer S i hi Λ hΛ) f := by
      funext x; rw [Complex.ofReal_one, one_smul]
    rw [h1, Finset.sum_eq_zero fun y hy => by rw [minim_null (twoLayer S i hi Λ hΛ) f y hy, smul_zero], sub_zero]
  have key : minim (twoLayer S i hi Λ hΛ) f - corr (twoLayer S i hi Λ hΛ) (fun x => ((1 : ℝ) : ℂ) •
      minim (twoLayer S i hi Λ hΛ) f x) = (0 : CoreLean.Form0 N NF) := by
    rw [e]; exact sub_self _
  rw [key, map_zero, map_zero, zero_mul]
  simp [hs2, ntr]

/-- **The cut-off vanishes outside the common blocks** (the hypothesis `hχV` of `local_bound`). -/
theorem chiq_V {q : (toScales S hM hR).Idx} (hI : (toDomains S hM hR).InD q) (x : Site NF)
    (hx : x ∉ Vq S hM hR q) : chiq S hM hR q x = 0 := by
  by_contra h0
  apply hx
  have hn := nq_ge S hM hR q
  have hodd := nq_odd S hM hR q
  -- `χ(x) ≠ 0` puts `x` within `4Ma_j` of `c_□`
  have h4 : dinf x (cq S hM hR q) < 4 * nq S hM hR q := by
    by_contra hc
    push_neg at hc
    obtain ⟨ν, -, hν⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty
      (fun ν => cd (x ν - cq S hM hR q ν))
    have hd : dinf x (cq S hM hR q) = cd (x ν - cq S hM hR q ν) := hν
    apply h0
    unfold chiq
    refine chiC_zero _ _ _ _ ν ?_
    unfold cd at hd
    rw [Int.abs_eq_natAbs]
    omega
  have hx6 : (dinf x (cq S hM hR q) : ℝ) ≤ 6 * ((S.L ^ S.mM : ℕ) : ℝ) * (S.L : ℝ) ^ (q.1 : ℕ) := by
    have hnr := nq_real S hM hR q
    have : (dinf x (cq S hM hR q) : ℝ) ≤ 4 * (nq S hM hR q : ℝ) := by exact_mod_cast h4.le
    have : (0 : ℝ) ≤ nq S hM hR q := by positivity
    linarith
  have hsc : (S.toDomSeq).sc x ≤ (q.1 : ℕ) + 1 := by
    by_contra hc
    exact not_mem_two S hM hR hI hx6 (((S.toDomSeq).mem_iff _ _).2 (by omega))
  have hxb := mem_blk_bc S x
  have hdb := dinf_lt_of_blk S hxb
  rw [sc_bc] at hdb
  have hpow : S.L ^ (S.toDomSeq).sc x ≤ nq S hM hR q := by
    have h1 : S.L ^ (S.toDomSeq).sc x ≤ S.L ^ ((q.1 : ℕ) + 1) := Nat.pow_le_pow_right S.Lpos hsc
    have h2 : S.L ^ ((q.1 : ℕ) + 1) ≤ nq S hM hR q := by
      show S.L ^ ((q.1 : ℕ) + 1) ≤ S.L ^ S.mM * S.L ^ (q.1 : ℕ)
      rw [pow_succ, mul_comm]; exact Nat.mul_le_mul_right _ (L_le_M S hM)
    omega
  have hdb' : dinf x (bc S.toDomSeq x) < S.L ^ (S.toDomSeq).sc x := by exact_mod_cast hdb
  have htri := dinf_triangle (bc S.toDomSeq x) x (cq S hM hR q)
  rw [dinf_comm (bc S.toDomSeq x) x] at htri
  show (dinf (bc S.toDomSeq x) (cq S hM hR q) : ℝ) ≤ 5 * ((S.L ^ S.mM : ℕ) : ℝ) * (S.L : ℝ) ^ (q.1 : ℕ)
  have hnr := nq_real S hM hR q
  have : dinf (bc S.toDomSeq x) (cq S hM hR q) ≤ 5 * nq S hM hR q := by omega
  have := (Nat.cast_le (α := ℝ)).2 this
  push_cast at this
  linarith

/-- The constant of the local bound. -/
def Cloc (L : ℕ) : ℝ := 2 * (1 + 2 * (SFOneLayer.Col * (1 + 2 ^ 17 * (L : ℝ) ^ 10)))

lemma Cloc_nonneg (L : ℕ) : 0 ≤ Cloc L := by unfold Cloc SFOneLayer.Col; positivity

/-- **The local bound for a cube** (the step "The local bound" for `X = h_□A`). -/
theorem cube_local [NeZero N] {δ : ℝ} (H : ScalarHyp (N := N) S (X0 S) 0 (W1 S) 0 Set.univ δ)
    (hRMb : (S.toContSeq).r1 (1 / 2) (1 / 32 * δ) ≤ RMS) (hRMs4 : 32 * Real.log S.L / (1 / 4 * δ) ≤ RMS)
    (hsmallT : CTd S N δ 0 0 * (S.toContSeq).c1 (1 / 2) (1 / 32 * δ) ≤ gammaB N / 4)
    (hRMθs : 32 * Real.log S.L / (thetaB S N δ / 2) ≤ RMS)
    (hRMθc : (S.toContSeq).r1 (1 / 2) (7 / 16 * thetaB S N δ) ≤ RMS)
    (hRMsum : (S.toContSeq).r1 (1 / 2) (7 / 32 * thetaB S N δ) ≤ RMS) (hk1 : 1 ≤ S.k)
    (hcutS : 8 * Real.exp (-(2 * (kap0 S N δ * (((S.L ^ S.mM : ℕ) : ℝ) / S.L)))) *
      Kbar S.L (kap0 S N δ) (CIone S N δ (kap0 S N δ)) Cbump ≤ 1 / 16)
    (A : Fin 4 → Site NF → Mat) (q : (toScales S hM hR).Idx) :
    formF S (locA S (hL S hM hR q) A) ≤ Cloc S.L * formA S (locA S (hL S hM hR q) A) := by
  by_cases hq0 : ∃ x0, hL S hM hR q x0 ≠ 0
  · obtain ⟨x0, hx0⟩ := hq0
    have hI := InD_of_hL S hM hR hx0
    obtain ⟨i, hi, Λ, hΛ, hij, hji, hag⟩ := exists_comparison S hM hR hI hk1
    have hX : ∀ μ x, locA S (hL S hM hR q) A μ x ≠ 0 →
        (dinf x (cq S hM hR q) : ℝ) ≤ ((S.L ^ S.mM : ℕ) : ℝ) * (S.L : ℝ) ^ (q.1 : ℕ) := by
      intro μ x hx
      have hh : hL S hM hR q x ≠ 0 := by
        intro h0; apply hx; simp only [locA, h0, Complex.ofReal_zero, zero_smul]
      have := dinf_cq_of_hL S hM hR hh
      have hn : (12 : ℝ) ≤ ((S.L ^ S.mM : ℕ) : ℝ) * (S.L : ℝ) ^ (q.1 : ℕ) := by
        rw [← nq_real]; exact_mod_cast nq_ge S hM hR q
      linarith
    have hQ := Qnorm_two_le S hM hR (hi := hi) (hΛ := hΛ) hij hag _ hX
    by_cases hbig : 2 * (4 * nq S hM hR q + 2) ≤ NF
    · have hcut := hcut_big S hM hR H hRMb hRMs4 hsmallT hRMθs hRMθc hRMsum q (hi := hi) (hΛ := hΛ) hij A hbig
      have hη0 : 0 ≤ 8 * Real.exp (-(2 * (kap0 S N δ * (((S.L ^ S.mM : ℕ) : ℝ) / S.L)))) *
          Kbar S.L (kap0 S N δ) (CIone S N δ (kap0 S N δ)) Cbump := by
        have hc1 : 0 ≤ (S.toContSeq).c1 (1 / 2) (7 / 32 * thetaB S N δ) := by
          unfold Summation.ContSeq.c1; positivity
        have hCI : 0 ≤ CIone S N δ (kap0 S N δ) := by unfold CIone; positivity
        have : 0 ≤ Kbar S.L (kap0 S N δ) (CIone S N δ (kap0 S N δ)) Cbump := by unfold Kbar; positivity
        positivity
      exact local_bound hi Λ hΛ _ (chiq S hM hR q) (Vq S hM hR q) (hV_cube S hM hR hI hag)
        (chiq_V S hM hR hI) hη0 hcutS hcut hQ
    · -- the torus lies within `6Ma_j` of the centre
      have hall : ∀ x : Site NF, (dinf x (cq S hM hR q) : ℝ) ≤ 6 * ((S.L ^ S.mM : ℕ) : ℝ) * (S.L : ℝ) ^ (q.1 : ℕ) := by
        intro x
        have hd : dinf x (cq S hM hR q) ≤ NF / 2 := Finset.sup_le fun ν _ => cd_le_half _
        have hn := nq_ge S hM hR q
        have : dinf x (cq S hM hR q) ≤ 6 * nq S hM hR q := by omega
        have hnr := nq_real S hM hR q
        have := (Nat.cast_le (α := ℝ)).2 this
        push_cast at this
        linarith
      have hV : ∀ x ∈ (Set.univ : Set (Site NF)), (S.toDomSeq).sc x = ((twoLayer S i hi Λ hΛ).toDomSeq).sc x ∧
          ∀ x' ∈ Blk S.toDomSeq ((S.toDomSeq).sc x) (bc S.toDomSeq x), x' ∈ (Set.univ : Set (Site NF)) :=
        fun x _ => ⟨(sc_two_eq x (hag x (hall x))).symm, fun _ _ => trivial⟩
      exact local_bound hi Λ hΛ _ (fun _ => 1) Set.univ hV (fun x hx => absurd trivial hx) le_rfl
        (by norm_num) (hcut_small S (hi := hi) (hΛ := hΛ) (Ds1L a1 (cfgX (X0 S)) (locA S (hL S hM hR q) A))) hQ
  · push_neg at hq0
    have e : locA S (hL S hM hR q) A = fun _ _ => 0 := by
      funext μ x; simp only [locA, hq0 x, Complex.ofReal_zero, zero_smul]
    rw [e]
    have h1 : formF S (fun (_ : Fin 4) (_ : Site NF) => (0 : Mat)) = 0 := by
      simp [formF, gradNorm, gbond, Qnorm, Qt, norm_emb_sq, hs2, ntr]
    have h2 : formA S (fun (_ : Fin 4) (_ : Site NF) => (0 : Mat)) = 0 := by
      unfold formA
      rw [h1]
      have : Ds1L a1 (cfgX (X0 S)) (fun (_ : Fin 4) (_ : Site NF) => (0 : Mat)) = 0 := map_zero _
      rw [this, map_zero]
      simp [hs2, ntr]
    rw [h1, h2, mul_zero]

end PartitionUnity

namespace PartitionUnity

open Lattices SeqDom SFBounds SFLocal Blocks SmallFieldBlocks SmallFieldDecay SFBox SequenceOperators

variable (S : Lattices.SeqDom) (hM : 12 ≤ S.L ^ S.mM) (hR : 12 * S.L ≤ S.R) {N : ℕ}

local notation "NF" => SequenceAverages.N0 S
local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "RMS" => ((S.R * S.L ^ S.mM : ℕ) : ℝ)

include hM hR

/-- **`prop:sf-vector-lower`, the first inequality** (the torus as the Dirichlet domain, at the trivial
configuration, `𝖺 = 1`, `k ≥ 1`): `⟨A^*, Δ^F_𝖺A⟩ ≤ 2C_loc⟨A^*, Δ_𝖺(id)A⟩` for every `1`-form `A`, under the conditions
of `prop:sf-block` on `RM`, the condition `8e^{-2κM/L}K̄ ≤ 1/16` of the cut-off, and the condition `Θ ≤ ½` of the
localisation, for a parameter `0 < ε ≤ 1`. -/
theorem vector_lower [NeZero N] {δ : ℝ} (H : ScalarHyp (N := N) S (X0 S) 0 (W1 S) 0 Set.univ δ)
    (hRMb : (S.toContSeq).r1 (1 / 2) (1 / 32 * δ) ≤ RMS) (hRMs4 : 32 * Real.log S.L / (1 / 4 * δ) ≤ RMS)
    (hsmallT : CTd S N δ 0 0 * (S.toContSeq).c1 (1 / 2) (1 / 32 * δ) ≤ gammaB N / 4)
    (hRMθs : 32 * Real.log S.L / (thetaB S N δ / 2) ≤ RMS)
    (hRMθc : (S.toContSeq).r1 (1 / 2) (7 / 16 * thetaB S N δ) ≤ RMS)
    (hRMsum : (S.toContSeq).r1 (1 / 2) (7 / 32 * thetaB S N δ) ≤ RMS)
    (hRMsum2 : (S.toContSeq).r1 (1 / 2) (7 / 32 * thetaB S N δ / 2) ≤ RMS)
    (hRMss : 32 * Real.log S.L / (2 * (7 / 32 * thetaB S N δ)) ≤ RMS)
    (hR1 : 1 ≤ S.R) (hRM2 : 2 * (S.L : ℝ) ≤ RMS) (hRMn : 2 * S.L ≤ S.R * S.L ^ S.mM) (hk1 : 1 ≤ S.k)
    (hcutS : 8 * Real.exp (-(2 * (kap0 S N δ * (((S.L ^ S.mM : ℕ) : ℝ) / S.L)))) *
      Kbar S.L (kap0 S N δ) (CIone S N δ (kap0 S N δ)) Cbump ≤ 1 / 16)
    {ε : ℝ} (hε0 : 0 < ε) (hε : ε ≤ 1) (hΘ : ThetaIMS S N δ (Cloc S.L) ε ≤ 1 / 2)
    (A : Fin 4 → Site NF → Mat) :
    formF S A ≤ 2 * Cloc S.L * formA S A :=
  ims_conclusion (hM := hM) (hR := hR) H hRMb hRMs4 hsmallT hRMθs hRMθc hRMsum hRMsum2 hRMss hR1 hRM2 hRMn A
    (Cloc_nonneg S.L) hε0 hε
    (fun q => cube_local S hM hR H hRMb hRMs4 hsmallT hRMθs hRMθc hRMsum hk1 hcutS A q) hΘ

/-- **`prop:sf-vector-lower`, both inequalities**: `⟨A^*, Δ_𝖺(id)A⟩ ≥ (2C_loc)⁻¹⟨A^*, Δ^F_𝖺A⟩ ≥
2^{-12}(2C_loc)⁻¹(‖∇A‖² + ‖A‖_w²)`. -/
theorem vector_lower_full [NeZero N] {δ : ℝ} (H : ScalarHyp (N := N) S (X0 S) 0 (W1 S) 0 Set.univ δ)
    (hRMb : (S.toContSeq).r1 (1 / 2) (1 / 32 * δ) ≤ RMS) (hRMs4 : 32 * Real.log S.L / (1 / 4 * δ) ≤ RMS)
    (hsmallT : CTd S N δ 0 0 * (S.toContSeq).c1 (1 / 2) (1 / 32 * δ) ≤ gammaB N / 4)
    (hRMθs : 32 * Real.log S.L / (thetaB S N δ / 2) ≤ RMS)
    (hRMθc : (S.toContSeq).r1 (1 / 2) (7 / 16 * thetaB S N δ) ≤ RMS)
    (hRMsum : (S.toContSeq).r1 (1 / 2) (7 / 32 * thetaB S N δ) ≤ RMS)
    (hRMsum2 : (S.toContSeq).r1 (1 / 2) (7 / 32 * thetaB S N δ / 2) ≤ RMS)
    (hRMss : 32 * Real.log S.L / (2 * (7 / 32 * thetaB S N δ)) ≤ RMS)
    (hR1 : 1 ≤ S.R) (hRM2 : 2 * (S.L : ℝ) ≤ RMS) (hRMn : 2 * S.L ≤ S.R * S.L ^ S.mM) (hk1 : 1 ≤ S.k)
    (hcutS : 8 * Real.exp (-(2 * (kap0 S N δ * (((S.L ^ S.mM : ℕ) : ℝ) / S.L)))) *
      Kbar S.L (kap0 S N δ) (CIone S N δ (kap0 S N δ)) Cbump ≤ 1 / 16)
    {ε : ℝ} (hε0 : 0 < ε) (hε : ε ≤ 1) (hΘ : ThetaIMS S N δ (Cloc S.L) ε ≤ 1 / 2)
    (A : Fin 4 → Site NF → Mat) :
    (2 * Cloc S.L)⁻¹ * formF S A ≤ formA S A ∧
      (2 ^ 12 : ℝ)⁻¹ * (2 * Cloc S.L)⁻¹ * (gradNorm S A + SFBounds.wnorm S A) ≤ (2 * Cloc S.L)⁻¹ * formF S A := by
  have h := vector_lower S hM hR H hRMb hRMs4 hsmallT hRMθs hRMθc hRMsum hRMsum2 hRMss hR1 hRM2 hRMn hk1 hcutS
    hε0 hε hΘ A
  have hC : 0 < 2 * Cloc S.L := by
    have : 0 < Cloc S.L := by unfold Cloc SFOneLayer.Col; positivity
    linarith
  constructor
  · rw [inv_mul_le_iff₀ hC]; exact h
  · have hc := sf_components S hRMn A
    have hi : 0 ≤ (2 * Cloc S.L)⁻¹ := inv_nonneg.2 hC.le
    have : (2 ^ 12 : ℝ)⁻¹ * (gradNorm S A + SFBounds.wnorm S A) ≤ formF S A := by
      unfold formF; rw [inv_mul_le_iff₀ (by norm_num)]; exact hc
    calc (2 ^ 12 : ℝ)⁻¹ * (2 * Cloc S.L)⁻¹ * (gradNorm S A + SFBounds.wnorm S A)
        = (2 * Cloc S.L)⁻¹ * ((2 ^ 12 : ℝ)⁻¹ * (gradNorm S A + SFBounds.wnorm S A)) := by ring
      _ ≤ (2 * Cloc S.L)⁻¹ * formF S A := mul_le_mul_of_nonneg_left this hi

end PartitionUnity

namespace PartitionUnity

open Lattices SeqDom SFBounds SFLocal Blocks SmallFieldBlocks SmallFieldDecay SFBox SequenceOperators

variable (S : Lattices.SeqDom) {N : ℕ}

local notation "NF" => SequenceAverages.N0 S
local notation "Mat" => Matrix (Fin N) (Fin N) ℂ

/-- **A sequence with `k = 0`** has the single layer `0`: `N Σ_{y,μ}|(QA)(y, μ)|² ≤ ⟨A^*, Q^*QA⟩`. -/
lemma qsum_k0 (hk0 : S.k = 0) (A : Fin 4 → Site NF → Mat) :
    (N : ℝ) * (((S.L ^ 0 : ℕ) : ℝ) ^ 2 * ∑ y ∈ detB S.toDomSeq, ∑ μ, hs2 (Qt S A 0 y μ)) ≤ Qnorm S A := by
  set g : Site NF × Fin 4 → ℕ × Site NF × Fin 4 := fun p => (0, p.1, p.2)
  have hg : Set.InjOn g ↑(detB S.toDomSeq ×ˢ (Finset.univ : Finset (Fin 4))) := by
    intro p _ p' _ h
    simp only [g, Prod.mk.injEq, true_and] at h
    exact Prod.ext h.1 h.2
  have hsub : (detB S.toDomSeq ×ˢ (Finset.univ : Finset (Fin 4))).image g ⊆ QB S := by
    intro q hq
    obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 hq
    refine (mem_QB_iff (T := S) _).2 ⟨by simp [g], fun ν => ⟨((p.1 ν).val : ℤ), by simp [g]⟩, ?_⟩
    have h1 : S.Ω (0 + 1) = ∅ := by rw [show (0 + 1 : ℕ) = S.k + 1 by omega]; exact S.Ω_top _ (Nat.lt_succ_self _)
    refine ⟨S.ef_mem_TL0 p.1, Or.inl (by rw [S.Ω_zero]; trivial), ?_, ?_⟩
    · show S.ef p.1 ∉ S.Ω (0 + 1); rw [h1]; exact Set.notMem_empty _
    · show S.bend 0 (S.ef p.1) p.2 ∉ S.Ω (0 + 1); rw [h1]; exact Set.notMem_empty _
  have e1 : (N : ℝ) * (((S.L ^ 0 : ℕ) : ℝ) ^ 2 * ∑ y ∈ detB S.toDomSeq, ∑ μ, hs2 (Qt S A 0 y μ)) =
      ∑ p ∈ detB S.toDomSeq ×ˢ (Finset.univ : Finset (Fin 4)),
        ((S.L ^ (g p).1 : ℕ) : ℝ) ^ 2 * ‖emb (N := N) (Qt S A (g p).1 (g p).2.1 (g p).2.2)‖ ^ 2 := by
    rw [Finset.sum_product, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun μ _ => ?_
    simp only [g, norm_emb_sq]; ring
  rw [e1, ← Finset.sum_image (f := fun q : ℕ × Site NF × Fin 4 =>
    ((S.L ^ q.1 : ℕ) : ℝ) ^ 2 * ‖emb (N := N) (Qt S A q.1 q.2.1 q.2.2)‖ ^ 2) hg]
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun q _ _ => by positivity

/-- **`prop:sf-vector-lower` for `k = 0`**: the sequence is a single layer, and `lem:sf-one-layer` applies to it
directly: `⟨A^*, Δ^F_𝖺A⟩ ≤ 2(1 + 2C_ol)⟨A^*, Δ_𝖺(id)A⟩ ≤ C_loc⟨A^*, Δ_𝖺(id)A⟩`. -/
theorem vector_lower_k0 [NeZero N] (hk0 : S.k = 0) (A : Fin 4 → Site NF → Mat) :
    formF S A ≤ Cloc S.L * formA S A := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  set f := Ds1L a1 (cfgX (X0 S)) A
  have hsc : ∀ x, (S.toDomSeq).sc x = 0 := fun x => by have := (S.toDomSeq).sc_le x; change _ ≤ S.k at this; omega
  have hone := one_layer_mat (S := S) (j := 0) (by omega) hsc (hb_triv (S := S) Set.univ) A
  have hq := qsum_k0 S hk0 A
  have hC : 0 ≤ SFOneLayer.Col := by unfold SFOneLayer.Col; positivity
  have hcurl : 0 ≤ curlE S A := by
    unfold curlE; exact Finset.sum_nonneg fun x _ => by
      have : 0 ≤ ∑ μ, ∑ ν, hs2 ((A ν (x + CoreLean.unit NF μ) - A ν x) - (A μ (x + CoreLean.unit NF ν) - A μ x)) :=
        Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => hs2_nonneg _
      positivity
  have hQs : 0 ≤ Qnorm S A := by unfold Qnorm; exact Finset.sum_nonneg fun _ _ => by positivity
  have hqC : ∑ x, hs2 (Pop S (X0 S) (W1 S) Set.univ f x) ≤ SFOneLayer.Col * (curlE S A + (N : ℝ)⁻¹ * Qnorm S A) := by
    refine hone.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl ?_) hC)
    rw [le_inv_mul_iff₀ hN]; exact hq
  have hp0 : 0 ≤ ∑ x, hs2 (Pop S (X0 S) (W1 S) Set.univ f x) := Finset.sum_nonneg fun x _ => hs2_nonneg _
  have hloc := local_alg (N := (N : ℝ)) (p := ∑ x, hs2 (Pop S (X0 S) (W1 S) Set.univ f x))
    (q := ∑ x, hs2 (Pop S (X0 S) (W1 S) Set.univ f x)) (r := 0) (η := 0) hN (by simp) hp0 le_rfl
    (by simp) hqC (grad_identity S A) (ds_le_grad S A) (Pop_contr S Set.univ f)
    (Finset.sum_nonneg fun x _ => hs2_nonneg _) hC le_rfl (by norm_num) hcurl hQs
  -- `⟨A^*, Δ_𝖺(id)A⟩ ≥ 0` and `2(1 + 2C_ol) ≤ C_loc`
  have hA0 : 0 ≤ formA S A := by
    unfold formA formF
    have h1 := Pop_contr S Set.univ f
    have h2 := grad_identity S A
    have h3 : (N : ℝ) * ∑ x, hs2 (Pop S (X0 S) (W1 S) Set.univ f x) ≤ N * ∑ x, hs2 (f x) :=
      mul_le_mul_of_nonneg_left h1 hN.le
    have h4 : 0 ≤ (N : ℝ) * curlE S A := mul_nonneg hN.le hcurl
    linarith
  have hCC : 2 * (1 + 2 * SFOneLayer.Col) ≤ Cloc S.L := by
    unfold Cloc
    have : SFOneLayer.Col ≤ SFOneLayer.Col * (1 + 2 ^ 17 * (S.L : ℝ) ^ 10) :=
      le_mul_of_one_le_right hC (by have : (0 : ℝ) ≤ 2 ^ 17 * (S.L : ℝ) ^ 10 := by positivity
                                    linarith)
    linarith
  unfold formA formF
  calc gradNorm S A + Qnorm S A ≤ 2 * (1 + 2 * SFOneLayer.Col) *
        (gradNorm S A + Qnorm S A - N * ∑ x, hs2 (Pop S (X0 S) (W1 S) Set.univ f x)) := hloc
    _ ≤ Cloc S.L * (gradNorm S A + Qnorm S A - N * ∑ x, hs2 (Pop S (X0 S) (W1 S) Set.univ f x)) := by
        have : 0 ≤ gradNorm S A + Qnorm S A - N * ∑ x, hs2 (Pop S (X0 S) (W1 S) Set.univ f x) := by
          unfold formA formF at hA0; exact hA0
        exact mul_le_mul_of_nonneg_right hCC this

end PartitionUnity

namespace PartitionUnity

open Lattices SeqDom SFBounds SFLocal Blocks SmallFieldBlocks SmallFieldDecay SFBox SequenceOperators

variable (S : Lattices.SeqDom) (hM : 12 ≤ S.L ^ S.mM) (hR : 12 * S.L ≤ S.R) {N : ℕ}

local notation "NF" => SequenceAverages.N0 S
local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "RMS" => ((S.R * S.L ^ S.mM : ℕ) : ℝ)

omit hM hR in
/-- `⟨A^*, Δ_𝖺(id)A⟩ ≥ 0`. -/
lemma formA_nonneg [NeZero N] (A : Fin 4 → Site NF → Mat) : 0 ≤ formA S A := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hcurl : 0 ≤ curlE S A := by
    unfold curlE; exact Finset.sum_nonneg fun x _ => by
      have : 0 ≤ ∑ μ, ∑ ν, hs2 ((A ν (x + CoreLean.unit NF μ) - A ν x) - (A μ (x + CoreLean.unit NF ν) - A μ x)) :=
        Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => hs2_nonneg _
      positivity
  have hQs : 0 ≤ Qnorm S A := by unfold Qnorm; exact Finset.sum_nonneg fun _ _ => by positivity
  unfold formA formF
  have h1 := Pop_contr S Set.univ (Ds1L a1 (cfgX (X0 S)) A)
  have h2 := grad_identity S A
  have h3 := mul_le_mul_of_nonneg_left h1 hN.le
  have h4 : 0 ≤ (N : ℝ) * curlE S A := mul_nonneg hN.le hcurl
  linarith

include hM hR

/-- **`prop:sf-vector-lower` on the torus**, for every `k`: `⟨A^*, Δ^F_𝖺A⟩ ≤ 2C_loc⟨A^*, Δ_𝖺(id)A⟩`. -/
theorem vector_lower_torus [NeZero N] {δ : ℝ} (H : ScalarHyp (N := N) S (X0 S) 0 (W1 S) 0 Set.univ δ)
    (hRMb : (S.toContSeq).r1 (1 / 2) (1 / 32 * δ) ≤ RMS) (hRMs4 : 32 * Real.log S.L / (1 / 4 * δ) ≤ RMS)
    (hsmallT : CTd S N δ 0 0 * (S.toContSeq).c1 (1 / 2) (1 / 32 * δ) ≤ gammaB N / 4)
    (hRMθs : 32 * Real.log S.L / (thetaB S N δ / 2) ≤ RMS)
    (hRMθc : (S.toContSeq).r1 (1 / 2) (7 / 16 * thetaB S N δ) ≤ RMS)
    (hRMsum : (S.toContSeq).r1 (1 / 2) (7 / 32 * thetaB S N δ) ≤ RMS)
    (hRMsum2 : (S.toContSeq).r1 (1 / 2) (7 / 32 * thetaB S N δ / 2) ≤ RMS)
    (hRMss : 32 * Real.log S.L / (2 * (7 / 32 * thetaB S N δ)) ≤ RMS)
    (hR1 : 1 ≤ S.R) (hRM2 : 2 * (S.L : ℝ) ≤ RMS) (hRMn : 2 * S.L ≤ S.R * S.L ^ S.mM)
    (hcutS : 8 * Real.exp (-(2 * (kap0 S N δ * (((S.L ^ S.mM : ℕ) : ℝ) / S.L)))) *
      Kbar S.L (kap0 S N δ) (CIone S N δ (kap0 S N δ)) Cbump ≤ 1 / 16)
    {ε : ℝ} (hε0 : 0 < ε) (hε : ε ≤ 1) (hΘ : ThetaIMS S N δ (Cloc S.L) ε ≤ 1 / 2)
    (A : Fin 4 → Site NF → Mat) :
    formF S A ≤ 2 * Cloc S.L * formA S A := by
  rcases Nat.eq_zero_or_pos S.k with hk | hk
  · have h := vector_lower_k0 S hk A
    have hC := Cloc_nonneg S.L
    have hA := formA_nonneg S A
    have : Cloc S.L * formA S A ≤ 2 * Cloc S.L * formA S A := by nlinarith [mul_nonneg hC hA]
    linarith
  · exact vector_lower S hM hR H hRMb hRMs4 hsmallT hRMθs hRMθc hRMsum hRMsum2 hRMss hR1 hRM2 hRMn hk hcutS
      hε0 hε hΘ A

end PartitionUnity

end CoreLean

end
