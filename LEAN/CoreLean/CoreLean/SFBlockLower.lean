/-
`prop:sf-block` of BALABAN_CORE.tex (`d4ef86a9a5fd`), the step "The lower bound at the trivial field", on the fine lattice
of a sequence of domains (`a₀ = 1`), at the trivial configuration (`𝐔 = id`, `W = id`):
for a function `μ` on the points of `𝐁` whose blocks lie in `Ω_D`,
`‖G'Q'^*μ‖₂ ≥ c_lo S`, `S² = Σ_y a_y⁸|μ(y)|²`, `c_lo = (9/32)⁴/(864 + 4N)`.

The test form is `φ = Σ_y a_y⁴ζ_yμ(y)^*` with the bumps of `SFBlockBump.lean` (the core takes `μ(y)` for `𝔤`-valued `μ`;
the adjoint makes the pairing `⟨φ, Q'^*μ⟩ = Σ_y a_y⁴|μ(y)|²Σ_{Δ(y)}ζ_y` real for complex values). The Laplacian of `φ` is
bounded through the shifted sums `Σ_x F(x ± e_μ)G(x)` (in place of the core's count of nine blocks).

* `P0_abs_le`: `|⟨f, g⟩| ≤ Σ_x|f(x)||g(x)|`; `cs_sum`: Cauchy–Schwarz for real sums.
* `lap_triv`: `Δφ = -Σ_μ(φ(· + e_μ) - 2φ + φ(· - e_μ))` at the trivial configuration.
* `pair_phi`: `Re⟨φ, Q'^*μ⟩ ≥ (9/32)⁴S²`; `lap_phi_pair`: `|⟨Δφ, w⟩| ≤ 864S‖w‖₂`; `ncon_phi_pair`:
  `|⟨Q'^*𝖺Q'φ, w⟩| ≤ 4NS‖w‖₂`.
* `lower_triv`: the lower bound.
-/
import CoreLean.SFBlockBump

open Finset Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace CoreLean
namespace SFBounds

open Lattices SeqDom Blocks SmallFieldBlocks SFBox SFBox.SeqDomBox SmallFieldDecay SmallFieldCoercivity
  SequenceOperators CompressedInverse SFBump

variable (S : SeqDom) {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "GLN" => (Matrix (Fin N) (Fin N) ℂ)ˣ
local notation "NF" => SequenceAverages.N0 S
local notation "RMS" => ((S.R * S.L ^ S.mM : ℕ) : ℝ)
set_option quotPrecheck false in
local notation "jj" => (S.toDomSeq).sc

/-- **Cauchy–Schwarz** for real sums. -/
lemma cs_sum {ι : Type*} (s : Finset ι) (a b : ι → ℝ) :
    ∑ i ∈ s, a i * b i ≤ Real.sqrt (∑ i ∈ s, a i ^ 2) * Real.sqrt (∑ i ∈ s, b i ^ 2) := by
  rw [← Real.sqrt_mul (sum_nonneg fun _ _ => sq_nonneg _)]
  exact Real.le_sqrt_of_sq_le (sum_mul_sq_le_sq_mul_sq s a b)

/-- `|⟨f, g⟩| ≤ Σ_x|f(x)||g(x)|` for the pairing `P0`. -/
lemma P0_abs_le (f g : Site NF → Mat) : ‖P0 f g‖ ≤ ∑ x, hs (f x) * hs (g x) := by
  simp only [P0, pairForm0, ConcretePairing.wpair_apply, a1, Complex.ofReal_one, one_pow, one_mul]
  exact (norm_sum_le _ _).trans (sum_le_sum fun x _ => norm_ntr_mul_le _ _)

lemma sum_sq_shift (F : Site NF → ℝ) (s : Site NF) : ∑ x, F (x + s) ^ 2 = ∑ x, F x ^ 2 :=
  Fintype.sum_equiv (Equiv.addRight s) _ _ fun _ => rfl

/-- `Σ_x F(x + s)G(x) ≤ ‖F‖₂‖G‖₂`. -/
lemma shift_cs (F G : Site NF → ℝ) (s : Site NF) :
    ∑ x, F (x + s) * G x ≤ Real.sqrt (∑ x, F x ^ 2) * Real.sqrt (∑ x, G x ^ 2) := by
  have := cs_sum univ (fun x => F (x + s)) G
  rwa [sum_sq_shift S F s] at this

/-- The trivial transports. -/
abbrev W1 : Site NF → Site NF → GLN := fun _ _ => 1

/-- The trivial field. -/
abbrev X0 : Fin 4 → Site NF → Mat := fun _ _ => 0

lemma QpStar_triv (μ : Site NF → Mat) (x : Site NF) : QpStar S (W1 S) μ x = μ (bc S.toDomSeq x) := by
  simp [QpStar, Ad]

/-- **The Laplacian at the trivial configuration.** -/
lemma lap_triv (v : Site NF → Mat) (x : Site NF) :
    Lap 1 (cfgX (X0 S)) v x = -∑ μ, (v (x + unit _ μ) - 2 • v x + v (x - unit _ μ)) := by
  simp only [Lap, Dbw, Dfw, cfgX, X0, smul_zero, expU_zero, Config.val, Bool.false_eq_true, if_false, inv_one,
    one_smul]
  rw [← sum_neg_distrib]
  refine sum_congr rfl fun μ _ => ?_
  simp only [Ad, Units.val_one, one_mul, mul_one, inv_one, sub_add_cancel]
  abel

/-- The test form `φ = Σ_y a_y⁴ζ_yμ(y)^*`, written at a site through the point of its block. -/
def phiT (μ : Site NF → Mat) : Site NF → Mat :=
  fun x => ∑ y ∈ detB S.toDomSeq, (((S.L : ℝ) ^ (4 * jj y) * zeta S y x : ℝ) : ℂ) • (μ y)ᴴ

lemma phiT_eq (μ : Site NF → Mat) (x : Site NF) :
    phiT S μ x = (((S.L : ℝ) ^ (4 * jj (bc S.toDomSeq x)) * zeta S (bc S.toDomSeq x) x : ℝ) : ℂ) •
      (μ (bc S.toDomSeq x))ᴴ := by
  unfold phiT
  rw [sum_eq_single (bc S.toDomSeq x)]
  · intro y hy hne
    rw [zeta_supp S hy (fun hx => hne ((sc_mem_blk S.toDomSeq hy hx).2.symm)), mul_zero, Complex.ofReal_zero,
      zero_smul]
  · intro h; exact absurd (bc_mem_detB S x) h

/-- `S² = Σ_y a_y⁸|μ(y)|²`. -/
def Ssq (μ : Site NF → Mat) : ℝ := ∑ y ∈ detB S.toDomSeq, (S.L : ℝ) ^ (8 * jj y) * hs2 (μ y)

/-- The function `F(z) = a_{j(z)}²|μ(y(z))|`, with `‖F‖₂ = S`. -/
def FT (μ : Site NF → Mat) : Site NF → ℝ := fun z => (S.L : ℝ) ^ (2 * jj z) * hs (μ (bc S.toDomSeq z))

lemma FT_sq (μ : Site NF → Mat) : ∑ z, FT S μ z ^ 2 = Ssq S μ := by
  rw [sum_blocks S.toDomSeq]
  unfold Ssq
  refine sum_congr rfl fun y hy => ?_
  have hterm : ∀ z ∈ Blk S.toDomSeq (jj y) y, FT S μ z ^ 2 = (S.L : ℝ) ^ (4 * jj y) * hs2 (μ y) := by
    intro z hz
    obtain ⟨hsc, hbc⟩ := sc_mem_blk S.toDomSeq hy hz
    simp only [FT, hsc, hbc, mul_pow, ← hs_sq, ← pow_mul]; ring_nf
  rw [sum_congr rfl hterm, sum_const, nsmul_eq_mul, card_Blk S hy, ← mul_assoc, ← pow_add]
  ring_nf

/-- **`Re⟨φ, Q'^*μ⟩ ≥ (9/32)⁴S²`.** -/
theorem pair_phi (μ : Site NF → Mat) :
    (9 / 32) ^ 4 * Ssq S μ ≤ (P0 (phiT S μ) (QpStar S (W1 S) μ)).re := by
  have hL : (0 : ℝ) < S.L := by exact_mod_cast S.Lpos
  simp only [P0, pairForm0, ConcretePairing.wpair_apply, a1, Complex.ofReal_one, one_pow, one_mul, QpStar_triv,
    phiT_eq, Complex.re_sum]
  rw [sum_blocks S.toDomSeq]
  unfold Ssq
  rw [mul_sum]
  refine sum_le_sum fun y hy => ?_
  have hterm : ∀ z ∈ Blk S.toDomSeq (jj y) y,
      (ntr ((((S.L : ℝ) ^ (4 * jj (bc S.toDomSeq z)) * zeta S (bc S.toDomSeq z) z : ℝ) : ℂ) •
        (μ (bc S.toDomSeq z))ᴴ * μ (bc S.toDomSeq z))).re =
      (S.L : ℝ) ^ (4 * jj y) * hs2 (μ y) * zeta S y z := by
    intro z hz
    obtain ⟨hsc, hbc⟩ := sc_mem_blk S.toDomSeq hy hz
    rw [hbc, smul_mul_assoc, ntr_smul, Complex.re_ofReal_mul]
    simp only [hs2]; ring
  rw [sum_congr rfl hterm, ← mul_sum]
  have hm := zeta_mass S hy
  have hh : (2 * (half S.L (jj y) : ℝ) + 1) = (S.L : ℝ) ^ jj y := by exact_mod_cast two_half_add_one S.L_odd _
  have h1 : (9 / 32) ^ 4 * (S.L : ℝ) ^ (4 * jj y) ≤ ((9 / 16) * ((half S.L (jj y) : ℝ) + 1)) ^ 4 := by
    rw [show (9 / 32 : ℝ) ^ 4 * (S.L : ℝ) ^ (4 * jj y) = ((9 / 16) * ((S.L : ℝ) ^ jj y / 2)) ^ 4 by
      rw [mul_comm 4 (jj y), pow_mul]; ring]
    gcongr; linarith
  have h2 := hs2_nonneg (μ y)
  calc (9 / 32) ^ 4 * ((S.L : ℝ) ^ (8 * jj y) * hs2 (μ y))
      = (S.L : ℝ) ^ (4 * jj y) * hs2 (μ y) * ((9 / 32) ^ 4 * (S.L : ℝ) ^ (4 * jj y)) := by
        rw [show 8 * jj y = 4 * jj y + 4 * jj y by ring, pow_add]; ring
    _ ≤ _ := by gcongr; exact h1.trans hm

/-- `18/c ≤ 72a_j⁻²` for `c = (h + 1)²`, `2h + 1 = a_j`. -/
lemma inv_cB_le (y : Site NF) : 18 / cB (half S.L (jj y)) ≤ 72 * ((S.L : ℝ) ^ (2 * jj y))⁻¹ := by
  have hh : (2 * (half S.L (jj y) : ℝ) + 1) = (S.L : ℝ) ^ jj y := by exact_mod_cast two_half_add_one S.L_odd _
  have hp : (0 : ℝ) < (S.L : ℝ) ^ jj y := by have := S.Lpos; positivity
  have hc : (S.L : ℝ) ^ (2 * jj y) ≤ 4 * cB (half S.L (jj y)) := by
    unfold cB; rw [mul_comm 2, pow_mul]; nlinarith [(Nat.cast_nonneg (half S.L (jj y)) : (0 : ℝ) ≤ _)]
  have hc0 := cB_pos (half S.L (jj y))
  have hP : (0 : ℝ) < (S.L : ℝ) ^ (2 * jj y) := pow_pos (by exact_mod_cast S.Lpos) _
  rw [div_le_iff₀ hc0]
  have hq : 1 / 4 ≤ cB (half S.L (jj y)) * ((S.L : ℝ) ^ (2 * jj y))⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ hP]; linarith
  nlinarith

/-- The second difference of `φ` in the direction `μ` is at most `72(F(x + e_μ) + F(x) + F(x - e_μ))`. -/
lemma phi_second (μ : Site NF → Mat) (x : Site NF) (ν : Fin 4) :
    hs (phiT S μ (x + unit _ ν) - 2 • phiT S μ x + phiT S μ (x - unit _ ν)) ≤
      72 * (FT S μ (x + unit _ ν) + FT S μ x + FT S μ (x - unit _ ν)) := by
  have hL : (0 : ℝ) < S.L := by exact_mod_cast S.Lpos
  have e : phiT S μ (x + unit _ ν) - 2 • phiT S μ x + phiT S μ (x - unit _ ν) =
      ∑ y ∈ detB S.toDomSeq, (((S.L : ℝ) ^ (4 * jj y) * (zeta S y (x + unit _ ν) - 2 * zeta S y x +
        zeta S y (x - unit _ ν)) : ℝ) : ℂ) • (μ y)ᴴ := by
    simp only [phiT, two_smul, ← sum_add_distrib, ← sum_sub_distrib, ← add_smul, ← sub_smul]
    refine sum_congr rfl fun y _ => ?_
    congr 1; push_cast; ring
  rw [e]
  refine (RegularAverages.hs_sum_le _ _).trans ?_
  set T : Site NF → ℝ := fun y => 72 * (S.L : ℝ) ^ (2 * jj y) * hs (μ y)
  have hterm : ∀ y ∈ detB S.toDomSeq, hs ((((S.L : ℝ) ^ (4 * jj y) * (zeta S y (x + unit _ ν) - 2 * zeta S y x +
      zeta S y (x - unit _ ν)) : ℝ) : ℂ) • (μ y)ᴴ) ≤
      (if y = bc S.toDomSeq (x + unit _ ν) then T y else 0) + (if y = bc S.toDomSeq x then T y else 0) +
        (if y = bc S.toDomSeq (x - unit _ ν) then T y else 0) := by
    intro y hy
    rw [RegularAverages.hs_smul, Complex.norm_real, Real.norm_eq_abs, hs_conjTranspose]
    have hT : 0 ≤ T y := by simp only [T]; exact mul_nonneg (by positivity) (hs_nonneg _)
    by_cases hin : y = bc S.toDomSeq (x + unit _ ν) ∨ y = bc S.toDomSeq x ∨ y = bc S.toDomSeq (x - unit _ ν)
    · have hb : |(S.L : ℝ) ^ (4 * jj y) * (zeta S y (x + unit _ ν) - 2 * zeta S y x + zeta S y (x - unit _ ν))| *
          hs (μ y) ≤ T y := by
        rw [abs_mul, abs_of_pos (pow_pos hL _)]
        have h1 := (zeta_second S hy x ν).trans (inv_cB_le S y)
        have e4 : (S.L : ℝ) ^ (4 * jj y) * (72 * ((S.L : ℝ) ^ (2 * jj y))⁻¹) = 72 * (S.L : ℝ) ^ (2 * jj y) := by
          rw [show 4 * jj y = 2 * jj y + 2 * jj y by ring, pow_add]; field_simp
        calc (S.L : ℝ) ^ (4 * jj y) * |zeta S y (x + unit _ ν) - 2 * zeta S y x + zeta S y (x - unit _ ν)| * hs (μ y)
            ≤ (S.L : ℝ) ^ (4 * jj y) * (72 * ((S.L : ℝ) ^ (2 * jj y))⁻¹) * hs (μ y) :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 (pow_nonneg hL.le _)) (hs_nonneg _)
          _ = T y := by rw [e4]
      rcases hin with h | h | h
      · rw [if_pos h]
        have : 0 ≤ (if y = bc S.toDomSeq x then T y else 0) + (if y = bc S.toDomSeq (x - unit _ ν) then T y else 0) :=
          add_nonneg (by split_ifs <;> linarith) (by split_ifs <;> linarith)
        linarith
      · rw [if_pos h]
        have h1 : 0 ≤ (if y = bc S.toDomSeq (x + unit _ ν) then T y else 0) := by split_ifs <;> linarith
        have h2 : 0 ≤ (if y = bc S.toDomSeq (x - unit _ ν) then T y else 0) := by split_ifs <;> linarith
        linarith
      · rw [if_pos h]
        have : 0 ≤ (if y = bc S.toDomSeq (x + unit _ ν) then T y else 0) + (if y = bc S.toDomSeq x then T y else 0) :=
          add_nonneg (by split_ifs <;> linarith) (by split_ifs <;> linarith)
        linarith
    · push_neg at hin
      obtain ⟨h1, h2, h3⟩ := hin
      have z : ∀ z, y ≠ bc S.toDomSeq z → zeta S y z = 0 := fun z hz =>
        zeta_supp S hy fun hm => hz (sc_mem_blk S.toDomSeq hy hm).2.symm
      rw [z _ h1, z _ h2, z _ h3, if_neg h1, if_neg h2, if_neg h3]
      simp
  refine (sum_le_sum hterm).trans (le_of_eq ?_)
  rw [sum_add_distrib, sum_add_distrib, sum_ite_eq', sum_ite_eq', sum_ite_eq', if_pos (bc_mem_detB S _),
    if_pos (bc_mem_detB S _), if_pos (bc_mem_detB S _)]
  simp only [T, FT, sc_bc]
  ring

/-- **`|⟨Δφ, w⟩| ≤ 864S‖w‖₂`** at the trivial configuration. -/
theorem lap_phi_pair (μ w : Site NF → Mat) :
    ‖P0 (fun x => Lap 1 (cfgX (X0 S)) (phiT S μ) x) w‖ ≤
      864 * Real.sqrt (Ssq S μ) * Real.sqrt (∑ x, hs (w x) ^ 2) := by
  refine (P0_abs_le S _ w).trans ?_
  have hpt : ∀ x, hs (Lap 1 (cfgX (X0 S)) (phiT S μ) x) ≤
      ∑ ν : Fin 4, 72 * (FT S μ (x + unit _ ν) + FT S μ x + FT S μ (x - unit _ ν)) := by
    intro x
    rw [lap_triv, SupportCont.hs_neg]
    exact (RegularAverages.hs_sum_le _ _).trans (sum_le_sum fun ν _ => phi_second S μ x ν)
  have hW : ∀ x, 0 ≤ hs (w x) := fun x => hs_nonneg _
  calc ∑ x, hs (Lap 1 (cfgX (X0 S)) (phiT S μ) x) * hs (w x)
      ≤ ∑ x, (∑ ν : Fin 4, 72 * (FT S μ (x + unit _ ν) + FT S μ x + FT S μ (x - unit _ ν))) * hs (w x) :=
        sum_le_sum fun x _ => mul_le_mul_of_nonneg_right (hpt x) (hW x)
    _ = 72 * ∑ ν : Fin 4, (∑ x, FT S μ (x + unit _ ν) * hs (w x) + ∑ x, FT S μ (x + 0) * hs (w x) +
          ∑ x, FT S μ (x + -unit _ ν) * hs (w x)) := by
        simp only [sum_mul, mul_sum, add_zero, ← sub_eq_add_neg]
        rw [sum_comm]
        refine sum_congr rfl fun ν _ => ?_
        rw [← sum_add_distrib, ← sum_add_distrib, mul_sum]
        refine sum_congr rfl fun x _ => by ring
    _ ≤ 72 * ∑ _ν : Fin 4, (3 * (Real.sqrt (∑ x, FT S μ x ^ 2) * Real.sqrt (∑ x, hs (w x) ^ 2))) := by
        gcongr with ν
        have h1 := shift_cs S (FT S μ) (fun x => hs (w x)) (unit _ ν)
        have h2 := shift_cs S (FT S μ) (fun x => hs (w x)) 0
        have h3 := shift_cs S (FT S μ) (fun x => hs (w x)) (-unit _ ν)
        linarith
    _ = 864 * Real.sqrt (Ssq S μ) * Real.sqrt (∑ x, hs (w x) ^ 2) := by
        rw [FT_sq]; simp; ring

/-- The trivial transports satisfy the bounds of `lem:block-average-transports`. -/
lemma wbound_triv [NeZero N] : WBound (N := N) S (W1 S) := by
  intro y _ x _ Z
  have hN : (1 : ℝ) ≤ Real.sqrt N := by
    rw [Real.one_le_sqrt]; exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hZ := hs_nonneg Z
  have e1 : Ad (W1 S y x) Z = Z := by simp [Ad]
  have e2 : Ad (W1 S y x)⁻¹ Z = Z := by simp [Ad]
  rw [e1, e2]; constructor <;> nlinarith

/-- **`|⟨Q'^*𝖺Q'φ, w⟩| ≤ 4NS‖w‖₂`** at the trivial transports. -/
theorem ncon_phi_pair [NeZero N] (μ w : Site NF → Mat) :
    ‖P0 (Ncon S.toDomSeq (W1 S) (phiT S μ)) w‖ ≤
      4 * N * Real.sqrt (Ssq S μ) * Real.sqrt (∑ x, hs (w x) ^ 2) := by
  refine (P0_abs_le S _ w).trans ?_
  have hL : (0 : ℝ) < S.L := by exact_mod_cast S.Lpos
  have hpt : ∀ x, hs (Ncon S.toDomSeq (W1 S) (phiT S μ) x) ≤ 4 * N * FT S μ x := by
    intro x
    refine (Ncon_bound S (wbound_triv S) _ x).trans ?_
    set y := bc S.toDomSeq x
    have hy : y ∈ detB S.toDomSeq := bc_mem_detB S x
    have hsc : jj y = jj x := sc_bc _ x
    have hblk : ∑ x' ∈ Blk S.toDomSeq (jj y) y, hs2 (phiT S μ x') ≤
        (S.L : ℝ) ^ (4 * jj y) * ((S.L : ℝ) ^ (4 * jj y) * hs (μ y)) ^ 2 := by
      have hterm : ∀ x' ∈ Blk S.toDomSeq (jj y) y, hs2 (phiT S μ x') ≤ ((S.L : ℝ) ^ (4 * jj y) * hs (μ y)) ^ 2 := by
        intro x' hx'
        obtain ⟨hsc', hbc'⟩ := sc_mem_blk S.toDomSeq hy hx'
        rw [← hs_sq, phiT_eq, hbc', RegularAverages.hs_smul, Complex.norm_real, Real.norm_eq_abs, hs_conjTranspose,
          abs_of_nonneg (mul_nonneg (by positivity) (zeta_nonneg S _ _))]
        have h1 := zeta_le_one S y x'
        have h0 := zeta_nonneg S y x'
        have : (S.L : ℝ) ^ (4 * jj y) * zeta S y x' * hs (μ y) ≤ (S.L : ℝ) ^ (4 * jj y) * hs (μ y) :=
          mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (pow_nonneg hL.le _) h1) (hs_nonneg _)
        exact pow_le_pow_left₀ (mul_nonneg (mul_nonneg (pow_nonneg hL.le _) h0) (hs_nonneg _)) this 2
      calc _ ≤ ∑ _x' ∈ Blk S.toDomSeq (jj y) y, ((S.L : ℝ) ^ (4 * jj y) * hs (μ y)) ^ 2 := sum_le_sum hterm
        _ = _ := by rw [sum_const, nsmul_eq_mul, card_Blk S hy]
    have hsq : Real.sqrt (∑ x' ∈ Blk S.toDomSeq (jj y) y, hs2 (phiT S μ x')) ≤
        (S.L : ℝ) ^ (2 * jj y) * ((S.L : ℝ) ^ (4 * jj y) * hs (μ y)) := by
      rw [Real.sqrt_le_left (by have := hs_nonneg (μ y); positivity)]
      calc _ ≤ _ := hblk
        _ = _ := by rw [mul_pow (S.L ^ (2 * jj y) : ℝ), ← pow_mul]; ring_nf
    calc 4 * N * ((S.L : ℝ) ^ (4 * jj x))⁻¹ * Real.sqrt (∑ x' ∈ Blk S.toDomSeq (jj y) y, hs2 (phiT S μ x'))
        ≤ 4 * N * ((S.L : ℝ) ^ (4 * jj x))⁻¹ * ((S.L : ℝ) ^ (2 * jj y) * ((S.L : ℝ) ^ (4 * jj y) * hs (μ y))) := by
          gcongr
      _ = 4 * N * FT S μ x := by
          simp only [FT]; rw [hsc]
          rw [show 4 * jj x = 2 * jj x + 2 * jj x by ring, pow_add]; field_simp; rfl
  have hW : ∀ x, 0 ≤ hs (w x) := fun x => hs_nonneg _
  calc ∑ x, hs (Ncon S.toDomSeq (W1 S) (phiT S μ) x) * hs (w x) ≤ ∑ x, 4 * N * FT S μ x * hs (w x) :=
        sum_le_sum fun x _ => mul_le_mul_of_nonneg_right (hpt x) (hW x)
    _ = 4 * N * ∑ x, FT S μ (x + 0) * hs (w x) := by rw [mul_sum]; simp [mul_assoc]
    _ ≤ 4 * N * (Real.sqrt (∑ x, FT S μ x ^ 2) * Real.sqrt (∑ x, hs (w x) ^ 2)) := by
        gcongr; exact shift_cs S _ _ 0
    _ = _ := by rw [FT_sq]; ring

lemma Ssq_nonneg (μ : Site NF → Mat) : 0 ≤ Ssq S μ :=
  sum_nonneg fun y _ => mul_nonneg (by have := S.Lpos; positivity) (hs2_nonneg _)

/-- The invertibility of `Π_DΔ'Π_D` at the trivial configuration. -/
lemma hK_triv [NeZero N] (ΩD : Set (Site NF)) :
    IsUnit (ckern (piD ΩD) (DeltaS S.toDomSeq (cfgX (N := N) (X0 S)) (W1 S))) :=
  deltaS_isUnit S.toDomSeq (cfgX (X0 S)) (W1 S) ΩD 0 0 le_rfl le_rfl
    (fun x μ Z => by simp [cfgX, X0, Ad, hs, hs2, ntr])
    (fun y _ x _ Z => by simp [Ad, hs, hs2, ntr])
    (fun y hy x hx Z => (wbound_triv S y hy x hx Z).1) (by norm_num)

/-- **The lower bound at the trivial field**: `‖G'Q'^*μ‖₂ ≥ (9/32)⁴(864 + 4N)⁻¹S` for `μ` on the points of `𝐁`
whose blocks lie in `Ω_D`. -/
theorem lower_triv [NeZero N] (ΩD : Set (Site NF)) (μ : Site NF → Mat)
    (hμ : ∀ y ∈ detB S.toDomSeq, μ y ≠ 0 → ∀ x ∈ Blk S.toDomSeq (jj y) y, x ∈ ΩD) :
    (9 / 32) ^ 4 / (864 + 4 * N) * Real.sqrt (Ssq S μ) ≤
      Real.sqrt (∑ x, hs (Gp' S.toDomSeq (cfgX (X0 S)) (W1 S) ΩD (QpStar S (W1 S) μ) x) ^ 2) := by
  set G := Gp' S.toDomSeq (cfgX (N := N) (X0 S)) (W1 S) ΩD
  set v := QpStar S (W1 S) μ
  set φ := phiT S μ
  set M := Real.sqrt (∑ x, hs (G v x) ^ 2)
  have hM : 0 ≤ M := Real.sqrt_nonneg _
  have hK := hK_triv (N := N) S ΩD
  have hP := piD_idem (N := N) ΩD
  -- `φ` vanishes outside `Ω_D`
  have hφ : piD ΩD φ = φ := by
    funext x
    rw [piD_apply]
    split_ifs with hx
    · rfl
    · simp only [φ, phiT_eq]
      by_cases h0 : μ (bc S.toDomSeq x) = 0
      · rw [h0]; simp
      · exact absurd (hμ _ (bc_mem_detB S x) h0 x (mem_blk_bc S x)) hx
  have hGφ : G (DeltaS S.toDomSeq (cfgX (X0 S)) (W1 S) φ) = φ := by
    have := cinv_T_P hP hK φ
    rw [hφ] at this; exact this
  have hpair : P0 φ v = P0 (DeltaS S.toDomSeq (cfgX (X0 S)) (W1 S) φ) (G v) := by
    rw [← Gp'_symm S.toDomSeq _ _ _ hK, hGφ]
  have hsplit : DeltaS S.toDomSeq (cfgX (X0 S)) (W1 S) φ =
      (fun x => Lap 1 (cfgX (X0 S)) φ x) + Ncon S.toDomSeq (W1 S) φ := by
    rw [DeltaS_eq]; congr 1
  have hbound : ‖P0 φ v‖ ≤ (864 + 4 * N) * Real.sqrt (Ssq S μ) * M := by
    rw [hpair, hsplit, map_add, LinearMap.add_apply]
    refine (norm_add_le _ _).trans ?_
    have h1 := lap_phi_pair S μ (G v)
    have h2 := ncon_phi_pair S μ (G v)
    linarith
  have hre := (pair_phi S μ).trans (Complex.re_le_norm _)
  have hS := Ssq_nonneg S μ
  have hsq := Real.sq_sqrt hS
  have hpos : (0 : ℝ) < 864 + 4 * N := by positivity
  rcases eq_or_lt_of_le (Real.sqrt_nonneg (Ssq S μ)) with h0 | h0
  · rw [← h0]; simp; exact hM
  · rw [div_mul_eq_mul_div, div_le_iff₀ hpos]
    have : (9 / 32) ^ 4 * Real.sqrt (Ssq S μ) * Real.sqrt (Ssq S μ) ≤
        (864 + 4 * N) * M * Real.sqrt (Ssq S μ) := by
      rw [mul_assoc, ← sq, hsq]; linarith
    have := le_of_mul_le_mul_right this h0
    linarith

end SFBounds
end CoreLean

end
