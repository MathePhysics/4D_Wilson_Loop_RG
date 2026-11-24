/-
`prop:sf-scalar` of BALABAN_CORE.tex (`4252790331fd`), the hypotheses of `(H2)` on `𝒩 = -Q'^*𝖺Q'`
(`eq:sf-constraint-term`), on the fine lattice of a sequence of domains (`a₀ = 1`), with the transports of the averages
subject to `|Ad_{W(y, x)}^{±1}Z| ≤ 2√N|Z|` (`lem:block-average-transports`).

* `Ncon_bound`: `|(Q'^*𝖺Q'u)(z)| ≤ 4Na_i⁻⁴‖u‖_{2,Δ(y)}`, `z ∈ Δ(y)`, `i = j(y)`.
* `Ncon_max`: `|(Q'^*𝖺Q'u)(z)| ≤ 4Na_i⁻²|u(z')|` for a site `z'` of the block of `z`, within `2La_i` of `z` (the pointwise
  hypothesis of `(H2)`).
* `blk_sum_le_box`: the sum of `|u|²` over the block of a site under `Q_8` about `x` (`j(x) ≥ 1`, `RM ≥ 8L²`) is at most
  the sum over `Q_{8+2L}` of the covering lattice.
* `Ncon_box`: `|a²(Q'^*𝖺Q'u)(n)| ≤ 4NL⁴a⁻²‖u‖_{2,Q_{8+2L}}` at the points of `Q_8` (the hypothesis on `𝒩` of
  `lem:sf-local` with `C_𝒩 = 4NL⁴`).
-/
import CoreLean.SFScalarOp
import CoreLean.SFLaplace

open Finset Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace CoreLean
namespace SFBounds

open Lattices SeqDom Blocks SmallFieldBlocks SFBox SFBox.SeqDomBox SFLocal LocalLaplacian InteriorSchauder
  SmallFieldDecay SmallFieldCoercivity SequenceOperators

variable (S : SeqDom) {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "GLN" => (Matrix (Fin N) (Fin N) ℂ)ˣ
local notation "NF" => SequenceAverages.N0 S
local notation "RMS" => ((S.R * S.L ^ S.mM : ℕ) : ℝ)
set_option quotPrecheck false in
local notation "jj" => (S.toDomSeq).sc

/-- The bounds of the transports of the averages. -/
def WBound (W : Site NF → Site NF → GLN) : Prop :=
  ∀ y ∈ detB S.toDomSeq, ∀ x ∈ Blk S.toDomSeq (jj y) y, ∀ Z : Mat,
    hs (Ad (W y x) Z) ≤ 2 * Real.sqrt N * hs Z ∧ hs (Ad (W y x)⁻¹ Z) ≤ 2 * Real.sqrt N * hs Z

lemma sum_hs_le_blk (u : Site NF → Mat) {y : Site NF} (hy : y ∈ detB S.toDomSeq) :
    ∑ x ∈ Blk S.toDomSeq (jj y) y, hs (u x) ≤
      (S.L : ℝ) ^ (2 * jj y) * Real.sqrt (∑ x ∈ Blk S.toDomSeq (jj y) y, hs2 (u x)) := by
  have h := block_L1_le S (fun (_ : Fin 1) x => u x) hy
  simpa [nsq, hs] using h

/-- **The constraint term**: `|(Q'^*𝖺Q'u)(z)| ≤ 4Na_i⁻⁴‖u‖_{2,Δ(y)}`. -/
theorem Ncon_bound [NeZero N] {W : Site NF → Site NF → GLN} (hW : WBound S W) (u : Site NF → Mat)
    (z : Site NF) :
    hs (Ncon S.toDomSeq W u z) ≤ 4 * N * ((S.L : ℝ) ^ (4 * jj z))⁻¹ *
      Real.sqrt (∑ x ∈ Blk S.toDomSeq (jj (bc S.toDomSeq z)) (bc S.toDomSeq z), hs2 (u x)) := by
  set y := bc S.toDomSeq z
  have hy : y ∈ detB S.toDomSeq := bc_mem_detB S z
  have hsc : jj y = jj z := sc_bc _ z
  have hzb : z ∈ Blk S.toDomSeq (jj y) y := mem_blk_bc S z
  have hL : (0 : ℝ) < S.L := by exact_mod_cast S.Lpos
  have hL1 : 1 ≤ S.L := by have := S.three_le_L; omega
  obtain ⟨ha1, ha2⟩ := aseq_mem S.L hL1 (jj z)
  have hN : 0 ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
  set B := Real.sqrt (∑ x ∈ Blk S.toDomSeq (jj y) y, hs2 (u x))
  have hB : 0 ≤ B := Real.sqrt_nonneg _
  -- the average
  have havg : hs (avgW S.toDomSeq W y u) ≤ 2 * Real.sqrt N * ((S.L : ℝ) ^ (2 * jj y))⁻¹ * B := by
    rw [avgW_blk S.toDomSeq W hy u, RegularAverages.hs_smul]
    simp only [toDomSeq_L]
    have h1 : hs (∑ x ∈ Blk S.toDomSeq (jj y) y, Ad (W y x) (u x)) ≤
        2 * Real.sqrt N * ∑ x ∈ Blk S.toDomSeq (jj y) y, hs (u x) := by
      refine (RegularAverages.hs_sum_le _ _).trans ?_
      rw [mul_sum]
      exact sum_le_sum fun x hx => ((hW y hy x hx) (u x)).1
    have h2 := sum_hs_le_blk S u hy
    have e : ‖((((S.L : ℝ) ^ (4 * jj y) : ℝ) : ℂ))⁻¹‖ = ((S.L : ℝ) ^ (4 * jj y))⁻¹ := by
      rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    rw [e]
    have e4 : ((S.L : ℝ) ^ (4 * jj y))⁻¹ * (S.L : ℝ) ^ (2 * jj y) = ((S.L : ℝ) ^ (2 * jj y))⁻¹ := by
      rw [show 4 * jj y = 2 * jj y + 2 * jj y by ring, pow_add]; field_simp
    calc ((S.L : ℝ) ^ (4 * jj y))⁻¹ * hs (∑ x ∈ Blk S.toDomSeq (jj y) y, Ad (W y x) (u x))
        ≤ ((S.L : ℝ) ^ (4 * jj y))⁻¹ * (2 * Real.sqrt N * ((S.L : ℝ) ^ (2 * jj y) * B)) := by
          gcongr
          exact h1.trans (mul_le_mul_of_nonneg_left h2 (by positivity))
      _ = 2 * Real.sqrt N * (((S.L : ℝ) ^ (4 * jj y))⁻¹ * (S.L : ℝ) ^ (2 * jj y)) * B := by ring
      _ = _ := by rw [e4]
  simp only [Ncon]
  rw [RegularAverages.hs_smul, Complex.norm_real, Real.norm_eq_abs]
  have hc : |aseq 1 S.L (jj z) * ((S.L : ℝ) ^ (2 * jj z))⁻¹| ≤ ((S.L : ℝ) ^ (2 * jj z))⁻¹ := by
    have hpos : 0 < aseq 1 S.L (jj z) := aseq_pos one_pos _ _
    rw [abs_of_pos (by positivity)]
    calc aseq 1 S.L (jj z) * ((S.L : ℝ) ^ (2 * jj z))⁻¹ ≤ 1 * ((S.L : ℝ) ^ (2 * jj z))⁻¹ := by gcongr
      _ = _ := one_mul _
  have hAd := ((hW y hy z hzb) (avgW S.toDomSeq W y u)).2
  rw [hsc] at havg
  have e : ((S.L : ℝ) ^ (2 * jj z))⁻¹ * ((S.L : ℝ) ^ (2 * jj z))⁻¹ = ((S.L : ℝ) ^ (4 * jj z))⁻¹ := by
    rw [← mul_inv, ← pow_add]; ring_nf
  have hsq : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt (Nat.cast_nonneg _)
  calc |aseq 1 S.L (jj z) * ((S.L : ℝ) ^ (2 * jj z))⁻¹| * hs (Ad (W y z)⁻¹ (avgW S.toDomSeq W y u))
      ≤ ((S.L : ℝ) ^ (2 * jj z))⁻¹ * (2 * Real.sqrt N * (2 * Real.sqrt N * ((S.L : ℝ) ^ (2 * jj z))⁻¹ * B)) := by
        exact mul_le_mul hc (hAd.trans (mul_le_mul_of_nonneg_left havg (by positivity))) (hs_nonneg _)
          (by positivity)
    _ = 4 * (Real.sqrt N * Real.sqrt N) * (((S.L : ℝ) ^ (2 * jj z))⁻¹ * ((S.L : ℝ) ^ (2 * jj z))⁻¹) * B := by ring
    _ = _ := by rw [hsq, e]

/-- **The pointwise form**: `|(Q'^*𝖺Q'u)(z)| ≤ 4Na_i⁻²|u(z')|` for a site `z'` of the block of `z`. -/
theorem Ncon_max [NeZero N] {W : Site NF → Site NF → GLN} (hW : WBound S W) (u : Site NF → Mat) (z : Site NF) :
    ∃ z' ∈ Blk S.toDomSeq (jj (bc S.toDomSeq z)) (bc S.toDomSeq z),
      hs (Ncon S.toDomSeq W u z) ≤ 4 * N * ((S.L : ℝ) ^ (2 * jj z))⁻¹ * hs (u z') := by
  set y := bc S.toDomSeq z
  have hy : y ∈ detB S.toDomSeq := bc_mem_detB S z
  have hsc : jj y = jj z := sc_bc _ z
  have hne : (Blk S.toDomSeq (jj y) y).Nonempty := ⟨z, mem_blk_bc S z⟩
  obtain ⟨z', hz', hmax⟩ := Finset.exists_max_image _ (fun x => hs (u x)) hne
  refine ⟨z', hz', (Ncon_bound S hW u z).trans ?_⟩
  have hL : (0 : ℝ) < S.L := by exact_mod_cast S.Lpos
  have hcard := card_Blk S hy
  have hsum : ∑ x ∈ Blk S.toDomSeq (jj y) y, hs2 (u x) ≤ (S.L : ℝ) ^ (4 * jj y) * hs (u z') ^ 2 := by
    calc ∑ x ∈ Blk S.toDomSeq (jj y) y, hs2 (u x) ≤ ∑ _x ∈ Blk S.toDomSeq (jj y) y, hs (u z') ^ 2 :=
          sum_le_sum fun x hx => by rw [← hs_sq]; exact pow_le_pow_left₀ (hs_nonneg _) (hmax x hx) 2
      _ = _ := by rw [sum_const, nsmul_eq_mul, hcard]
  have hsqrt : Real.sqrt (∑ x ∈ Blk S.toDomSeq (jj y) y, hs2 (u x)) ≤ (S.L : ℝ) ^ (2 * jj y) * hs (u z') := by
    rw [Real.sqrt_le_left (mul_nonneg (by positivity) (hs_nonneg _))]
    calc _ ≤ (S.L : ℝ) ^ (4 * jj y) * hs (u z') ^ 2 := hsum
      _ = _ := by rw [mul_pow, ← pow_mul]; ring_nf
  have hsqrt' : Real.sqrt (∑ x ∈ Blk S.toDomSeq (jj y) y, hs2 (u x)) ≤ (S.L : ℝ) ^ (2 * jj z) * hs (u z') := by
    rw [← hsc]; exact hsqrt
  have e : ((S.L : ℝ) ^ (4 * jj z))⁻¹ * (S.L : ℝ) ^ (2 * jj z) = ((S.L : ℝ) ^ (2 * jj z))⁻¹ := by
    rw [show 4 * jj z = 2 * jj z + 2 * jj z by ring, pow_add]; field_simp
  calc 4 * N * ((S.L : ℝ) ^ (4 * jj z))⁻¹ * Real.sqrt (∑ x ∈ Blk S.toDomSeq (jj y) y, hs2 (u x))
      ≤ 4 * N * ((S.L : ℝ) ^ (4 * jj z))⁻¹ * ((S.L : ℝ) ^ (2 * jj z) * hs (u z')) := by
        exact mul_le_mul_of_nonneg_left hsqrt' (by positivity)
    _ = 4 * N * (((S.L : ℝ) ^ (4 * jj z))⁻¹ * (S.L : ℝ) ^ (2 * jj z)) * hs (u z') := by ring
    _ = _ := by rw [e]

/-- A site of a block lies within `2La_i` of each site of the block. -/
lemma dinf_blk_le {y z z' : Site NF} (hz : z ∈ Blk S.toDomSeq (jj y) y) (hz' : z' ∈ Blk S.toDomSeq (jj y) y)
    (hy : y ∈ detB S.toDomSeq) : (dinf z' z : ℝ) ≤ 2 * (S.L : ℝ) ^ (jj z + 1) := by
  have h1 : ∀ ν, cd (z' ν - y ν) ≤ half S.L (jj y) := cd_le_of_mem (S := S.toDomSeq) hz'
  have h2 : ∀ ν, cd (z ν - y ν) ≤ half S.L (jj y) := cd_le_of_mem (S := S.toDomSeq) hz
  have hsc := sc_of_mem_blk S hy hz
  have hd : dinf z' z ≤ 2 * half S.L (jj y) := by
    refine Finset.sup_le fun ν _ => ?_
    have := cd_sub_le (z' ν) (y ν) (z ν)
    rw [cd_sub_comm (y ν) (z ν)] at this
    have := h1 ν; have := h2 ν
    omega
  have hh : (2 * half S.L (jj y) + 1 : ℝ) = (S.L : ℝ) ^ jj y := by exact_mod_cast two_half_add_one S.L_odd _
  have hL : (1 : ℝ) ≤ S.L := by exact_mod_cast (show 1 ≤ S.L by have := S.three_le_L; omega)
  have hp : (S.L : ℝ) ^ jj z ≤ (S.L : ℝ) ^ (jj z + 1) := pow_le_pow_right₀ hL (by omega)
  have : (dinf z' z : ℝ) ≤ 2 * half S.L (jj y) := by exact_mod_cast hd
  rw [← hsc] at hh this
  have h0 : (0 : ℝ) ≤ (S.L : ℝ) ^ (jj z + 1) := by positivity
  nlinarith

/-- **The block of a site under `Q_8` lifts into `Q_{8+2L}`**: the sum of `|u|²` over it is at most the sum over
`Q_{8+2L}` of the covering lattice. -/
theorem blk_sum_le_box (hRM : 8 * (S.L : ℝ) ^ 2 ≤ RMS) (u : Site NF → Mat) {x : Site NF}
    {n : Fin 4 → ℤ} (hn : InQr ((S.L : ℝ) ^ jj x)⁻¹ (xbar x) 8 n) :
    ∑ x' ∈ Blk S.toDomSeq (jj (bc S.toDomSeq (castS n))) (bc S.toDomSeq (castS n)), hs2 (u x') ≤
      ∑ w ∈ QF ((S.L : ℝ) ^ jj x)⁻¹ (xbar x) (8 + 2 * S.L), hs2 (u (castS w)) := by
  classical
  set y := bc S.toDomSeq (castS (n := NF) n)
  set T := Blk S.toDomSeq (jj y) y
  have hL3 : (3 : ℝ) ≤ S.L := by exact_mod_cast S.three_le_L
  set c : ℝ := (S.L : ℝ) ^ jj x
  have hc : 0 < c := by positivity
  have hsc : jj y = jj (castS n) := sc_bc _ _
  have hsc1 : jj (castS (n := NF) n) ≤ jj x + 1 := box_sc_le S hRM x (by linarith) hn
  have hnT : castS (n := NF) n ∈ T := mem_blk_bc S _
  set φ : Site NF → (Fin 4 → ℤ) := fun x' => n + fun ν => (x' ν - castS (n := NF) n ν).valMinAbs
  have hcast : ∀ x', castS (n := NF) (φ x') = x' := fun x' => by
    funext ν
    simp only [φ, castS, Pi.add_apply, Int.cast_add, ZMod.coe_valMinAbs]
    ring
  have hφ : ∀ x' ∈ T, φ x' ∈ QF c⁻¹ (xbar x) (8 + 2 * S.L) := by
    intro x' hx'
    rw [mem_QF (inv_pos.2 hc)]
    intro ν
    have h1 := cd_le_of_mem (S := S.toDomSeq) hx' ν
    have h2 := cd_le_of_mem (S := S.toDomSeq) hnT ν
    simp only [toDomSeq_L] at h1 h2
    have hcd : cd (x' ν - castS (n := NF) n ν) ≤ 2 * half S.L (jj y) := by
      have := cd_sub_le (x' ν) (y ν) (castS (n := NF) n ν)
      rw [cd_sub_comm (y ν)] at this
      omega
    have hh : (2 * half S.L (jj y) + 1 : ℝ) = (S.L : ℝ) ^ jj y := by exact_mod_cast two_half_add_one S.L_odd _
    have hpow : (S.L : ℝ) ^ jj y ≤ S.L * c := by
      rw [hsc]; simp only [c]; rw [← pow_succ']; exact pow_le_pow_right₀ (by linarith) hsc1
    have hdl : |((x' ν - castS (n := NF) n ν).valMinAbs : ℝ)| ≤ S.L * c := by
      have : |((x' ν - castS (n := NF) n ν).valMinAbs : ℝ)| ≤ 2 * half S.L (jj y) := by
        rw [← Int.cast_abs, ← Int.natCast_natAbs]; exact_mod_cast hcd
      linarith
    have hnν := hn ν
    unfold tc at hnν ⊢
    rw [abs_mul, abs_of_pos (inv_pos.2 hc)] at hnν ⊢
    have e : (((φ x' ν - xbar x ν : ℤ)) : ℝ) = ((n ν - xbar x ν : ℤ) : ℝ) +
        ((x' ν - castS (n := NF) n ν).valMinAbs : ℝ) := by
      simp only [φ, Pi.add_apply]; push_cast; ring
    rw [e]
    calc c⁻¹ * |((n ν - xbar x ν : ℤ) : ℝ) + ((x' ν - castS (n := NF) n ν).valMinAbs : ℝ)|
        ≤ c⁻¹ * |((n ν - xbar x ν : ℤ) : ℝ)| + c⁻¹ * (S.L * c) := by
          rw [← mul_add]; exact mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans (by linarith)) (by positivity)
      _ ≤ 8 + S.L := by
          have : c⁻¹ * (S.L * c) = S.L := by field_simp
          linarith
      _ ≤ 8 + 2 * S.L := by linarith
  have hinj : Set.InjOn φ T := fun a _ b _ h => by rw [← hcast a, ← hcast b, h]
  calc ∑ x' ∈ T, hs2 (u x') = ∑ x' ∈ T, hs2 (u (castS (φ x'))) := sum_congr rfl fun x' _ => by rw [hcast]
    _ = ∑ w ∈ T.image φ, hs2 (u (castS w)) := (sum_image (f := fun w => hs2 (u (castS w))) hinj).symm
    _ ≤ ∑ w ∈ QF c⁻¹ (xbar x) (8 + 2 * S.L), hs2 (u (castS w)) :=
        sum_le_sum_of_subset_of_nonneg (fun w hw => by
          obtain ⟨x', hx', rfl⟩ := mem_image.1 hw; exact hφ x' hx') fun _ _ _ => hs2_nonneg _

/-- **The hypothesis on `𝒩` of `lem:sf-local`** for `𝒩 = -Q'^*𝖺Q'`, with `C_𝒩 = 4NL⁴`. -/
theorem Ncon_box [NeZero N] (hRM : 8 * (S.L : ℝ) ^ 2 ≤ RMS) {W : Site NF → Site NF → GLN} (hW : WBound S W)
    (u : Site NF → Mat) {x : Site NF} (hj : 1 ≤ jj x) {n : Fin 4 → ℤ}
    (hn : InQr ((S.L : ℝ) ^ jj x)⁻¹ (xbar x) 8 n) :
    ‖SFBox.liftM (N := N) (fun (_ : Fin 1) z => ((((S.L : ℝ) ^ jj x) ^ 2 : ℝ)) • (-Ncon S.toDomSeq W u z)) n‖ ≤
      4 * N * (S.L : ℝ) ^ 4 * pn ((S.L : ℝ) ^ jj x)⁻¹ (QF ((S.L : ℝ) ^ jj x)⁻¹ (xbar x) (8 + 2 * S.L)) 2
        (fun z => ‖SFBox.liftM (N := N) (fun (_ : Fin 1) z => u z) z‖) := by
  have hL3 : (3 : ℝ) ≤ S.L := by exact_mod_cast S.three_le_L
  set c : ℝ := (S.L : ℝ) ^ jj x
  have hc : 0 < c := by positivity
  rw [pn_liftM, norm_liftM]
  have hnsq1 : (nsq fun (_ : Fin 1) => (c ^ 2 : ℝ) • -Ncon S.toDomSeq W u (castS n)) =
      hs2 ((c ^ 2 : ℝ) • Ncon S.toDomSeq W u (castS n)) := by
    simp [nsq, hs2]
  have hnsq2 : ∀ w, (nsq fun (_ : Fin 1) => u (castS (n := NF) w)) = hs2 (u (castS w)) := fun w => by simp [nsq]
  rw [hnsq1]
  simp only [hnsq2]
  have hs_r : Real.sqrt (hs2 ((c ^ 2 : ℝ) • Ncon S.toDomSeq W u (castS n))) =
      c ^ 2 * hs (Ncon S.toDomSeq W u (castS n)) := by
    rw [show Real.sqrt (hs2 ((c ^ 2 : ℝ) • Ncon S.toDomSeq W u (castS n))) =
      hs ((c ^ 2 : ℝ) • Ncon S.toDomSeq W u (castS n)) from rfl,
      show ((c ^ 2 : ℝ) • Ncon S.toDomSeq W u (castS n)) = (((c ^ 2 : ℝ)) : ℂ) • Ncon S.toDomSeq W u (castS n) from
        (Complex.coe_smul _ _).symm,
      RegularAverages.hs_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [hs_r]
  have hb := Ncon_bound S hW u (castS n)
  have hbox := blk_sum_le_box S hRM u hn
  have hsc1 : jj x ≤ jj (castS (n := NF) n) + 1 := by
    have h := box_mem_Ω S hRM x (by linarith) hn
    have := ((S.toDomSeq).mem_iff (castS n) _).1 (S.mem_toDomSeq_Ω.2 h)
    omega
  have hpow : ((S.L : ℝ) ^ (4 * jj (castS (n := NF) n)))⁻¹ ≤ (S.L : ℝ) ^ 4 * (c ^ 4)⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), inv_mul_le_iff₀ (by positivity)]
    simp only [c]
    rw [← pow_mul, ← pow_add]
    exact pow_le_pow_right₀ (by linarith) (by omega)
  have hsq : Real.sqrt (∑ x' ∈ Blk S.toDomSeq (jj (bc S.toDomSeq (castS n))) (bc S.toDomSeq (castS n)),
      hs2 (u x')) ≤ Real.sqrt (∑ w ∈ QF c⁻¹ (xbar x) (8 + 2 * S.L), hs2 (u (castS w))) := Real.sqrt_le_sqrt hbox
  have hN : 0 ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
  set Q := Real.sqrt (∑ w ∈ QF c⁻¹ (xbar x) (8 + 2 * S.L), hs2 (u (castS w)))
  have hQ : 0 ≤ Q := Real.sqrt_nonneg _
  calc Real.sqrt N * (c ^ 2 * hs (Ncon S.toDomSeq W u (castS n)))
      ≤ Real.sqrt N * (c ^ 2 * (4 * N * ((S.L : ℝ) ^ 4 * (c ^ 4)⁻¹) * Q)) := by
        gcongr
        exact hb.trans (mul_le_mul (mul_le_mul_of_nonneg_left hpow (by positivity)) hsq (Real.sqrt_nonneg _)
          (by positivity))
    _ = 4 * N * (S.L : ℝ) ^ 4 * (Real.sqrt N * c⁻¹ ^ 2 * Q) := by field_simp

end SFBounds
end CoreLean

end
