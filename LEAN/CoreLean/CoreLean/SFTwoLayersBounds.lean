/-
`lem:sf-two-layers` of BALABAN_CORE.tex (`c1d6d533fce5`), the steps "The circulations" and "Conclusion", on the fine
lattice: the right-hand side of `two_layers_coarse_rhs` by the curl energy and the constraint form.

* `tele2`: the circulation around a square of the side `n` is the sum of the circulations of its `n²` plaquettes.
* `circT_Bc`, `Pall_le`: `Σ_{p'}|(∂B)(p')|² ≤ 2N‖∂A‖²` (the core's `Σ_{p'}|(∂B)(p')|² ≤ ‖∂A‖²`, in the norm of `V`).
-/
import CoreLean.SFTwoLayersFine

open Finset Matrix

noncomputable section

namespace CoreLean
namespace SFBounds

open Lattices SeqDom Blocks SmallFieldBlocks SFLocal SmallFieldDecay SmallFieldCoercivity
  SequenceOperators CompressedInverse ConcretePairing SFBox SFBox.SeqDomBox

variable (S : SeqDom) {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "NF" => SequenceAverages.N0 S

/-- The curl `∂_μA_ν - ∂_νA_μ` at `p`. -/
def curlM (A : Fin 4 → Site NF → Mat) (μ ν : Fin 4) (p : Site NF) : Mat :=
  (A ν (p + unit NF μ) - A ν p) - (A μ (p + unit NF ν) - A μ p)

/-- **The circulation around a square of the side `n`** is the sum of the circulations of its plaquettes. -/
lemma tele2 {G : Type*} [AddCommGroup G] (f g : Site NF → G) (x u v : Site NF) (n : ℕ) :
    ∑ s ∈ range n, ∑ t ∈ range n,
      ((g (x + ((s : ℕ) : ZMod NF) • u + ((t : ℕ) : ZMod NF) • v + u) - g (x + ((s : ℕ) : ZMod NF) • u + ((t : ℕ) : ZMod NF) • v)) -
        (f (x + ((s : ℕ) : ZMod NF) • u + ((t : ℕ) : ZMod NF) • v + v) - f (x + ((s : ℕ) : ZMod NF) • u + ((t : ℕ) : ZMod NF) • v))) =
      ∑ t ∈ range n, f (x + ((t : ℕ) : ZMod NF) • u) + ∑ t ∈ range n, g (x + ((n : ℕ) : ZMod NF) • u + ((t : ℕ) : ZMod NF) • v) -
        ∑ t ∈ range n, f (x + ((n : ℕ) : ZMod NF) • v + ((t : ℕ) : ZMod NF) • u) - ∑ t ∈ range n, g (x + ((t : ℕ) : ZMod NF) • v) := by
  set P : ℕ → ℕ → Site NF := fun s t => x + ((s : ℕ) : ZMod NF) • u + ((t : ℕ) : ZMod NF) • v
  have hu : ∀ s t, P s t + u = P (s + 1) t := fun s t => by simp only [P]; push_cast; rw [add_smul, one_smul]; abel
  have hv : ∀ s t, P s t + v = P s (t + 1) := fun s t => by simp only [P]; push_cast; rw [add_smul, one_smul]; abel
  change ∑ s ∈ range n, ∑ t ∈ range n, ((g (P s t + u) - g (P s t)) - (f (P s t + v) - f (P s t))) = _
  simp only [hu, hv, sum_sub_distrib]
  have eg : ∑ s ∈ range n, ∑ t ∈ range n, g (P (s + 1) t) - ∑ s ∈ range n, ∑ t ∈ range n, g (P s t) =
      ∑ t ∈ range n, g (P n t) - ∑ t ∈ range n, g (P 0 t) := by
    rw [← sum_sub_distrib, ← sum_sub_distrib]
    simp only [← sum_sub_distrib]
    rw [sum_comm]
    exact sum_congr rfl fun t _ => sum_range_sub (fun s => g (P s t)) n
  have ef : ∑ s ∈ range n, ∑ t ∈ range n, f (P s (t + 1)) - ∑ s ∈ range n, ∑ t ∈ range n, f (P s t) =
      ∑ s ∈ range n, f (P s n) - ∑ s ∈ range n, f (P s 0) := by
    rw [← sum_sub_distrib, ← sum_sub_distrib]
    refine sum_congr rfl fun s _ => ?_
    rw [← sum_sub_distrib]
    exact sum_range_sub (fun t => f (P s t)) n
  have e1 : ∀ t, P n t = x + ((n : ℕ) : ZMod NF) • u + ((t : ℕ) : ZMod NF) • v := fun t => rfl
  have e2 : ∀ t, P 0 t = x + ((t : ℕ) : ZMod NF) • v := fun t => by simp [P]
  have e3 : ∀ s, P s n = x + ((n : ℕ) : ZMod NF) • v + ((s : ℕ) : ZMod NF) • u := fun s => by
    simp only [P]; abel
  have e4 : ∀ s, P s 0 = x + ((s : ℕ) : ZMod NF) • u := fun s => by simp [P]
  have hfin : ∑ s ∈ range n, ∑ t ∈ range n, g (P (s + 1) t) - ∑ s ∈ range n, ∑ t ∈ range n, g (P s t) -
      (∑ s ∈ range n, ∑ t ∈ range n, f (P s (t + 1)) - ∑ s ∈ range n, ∑ t ∈ range n, f (P s t)) =
      ∑ t ∈ range n, g (P n t) - ∑ t ∈ range n, g (P 0 t) - (∑ s ∈ range n, f (P s n) - ∑ s ∈ range n, f (P s 0)) := by
    rw [eg, ef]
  simp only [e1, e2, e3, e4] at hfin
  rw [← sub_eq_zero] at hfin ⊢
  rw [← hfin]
  abel

lemma card_Blk_j {j : ℕ} (hj : j ≤ S.k) {y : Site NF} (hy : InLat S.L j y) :
    (Blk S.toDomSeq j y).card = (S.L ^ j) ^ 4 := by
  rw [card_eq_sum_ones, sum_Blk_const S hj hy, smul_eq_mul, mul_one]

/-- **The coarse circulation** is the mean over the block of the circulations around the squares of the side `a_j`. -/
lemma circT_Bc {j : ℕ} (hj1 : j + 1 ≤ S.k) (A : Fin 4 → Site NF → Mat) (ν₁ ν₂ : Fin 4) (z : Coarse.T S.L (Mj S j)) :
    Coarse.circT (Bc S A j) ν₁ ν₂ z = emb (((((S.L ^ j : ℕ) : ℂ)) ^ 4)⁻¹ •
      ∑ x ∈ Blk S.toDomSeq j (fineOf S j z), ∑ s ∈ range (S.L ^ j), ∑ t ∈ range (S.L ^ j),
        curlM S A ν₁ ν₂ (x + ((s : ℕ) : ZMod NF) • unit NF ν₁ + ((t : ℕ) : ZMod NF) • unit NF ν₂)) := by
  have hj0 : j ≤ S.k := by omega
  set n := S.L ^ j
  set y := fineOf S j z
  have hy := inLat_fineOf S j z
  have hS2 := sum_Blk_add S hj0 hy (inLat_unit S j ν₁) (fun x => ∑ t ∈ range n, A ν₂ (x + ((t : ℕ) : ZMod NF) • unit NF ν₂))
  have hS3 := sum_Blk_add S hj0 hy (inLat_unit S j ν₂) (fun x => ∑ t ∈ range n, A ν₁ (x + ((t : ℕ) : ZMod NF) • unit NF ν₁))
  have key : ∑ x ∈ Blk S.toDomSeq j y, ∑ t ∈ range n, A ν₁ (x + ((t : ℕ) : ZMod NF) • unit NF ν₁) +
      ∑ x ∈ Blk S.toDomSeq j y, ∑ t ∈ range n, A ν₂ (x + ((n : ℕ) : ZMod NF) • unit NF ν₁ + ((t : ℕ) : ZMod NF) • unit NF ν₂) -
      ∑ x ∈ Blk S.toDomSeq j y, ∑ t ∈ range n, A ν₁ (x + ((n : ℕ) : ZMod NF) • unit NF ν₂ + ((t : ℕ) : ZMod NF) • unit NF ν₁) -
      ∑ x ∈ Blk S.toDomSeq j y, ∑ t ∈ range n, A ν₂ (x + ((t : ℕ) : ZMod NF) • unit NF ν₂) =
      ∑ x ∈ Blk S.toDomSeq j y, ∑ s ∈ range n, ∑ t ∈ range n,
        curlM S A ν₁ ν₂ (x + ((s : ℕ) : ZMod NF) • unit NF ν₁ + ((t : ℕ) : ZMod NF) • unit NF ν₂) := by
    rw [← sum_add_distrib, ← sum_sub_distrib, ← sum_sub_distrib]
    exact sum_congr rfl fun x _ => (tele2 S (A ν₁) (A ν₂) x (unit NF ν₁) (unit NF ν₂) n).symm
  have hn : ((n : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (pow_pos S.Lpos j).ne'
  have h1 : Coarse.circT (Bc S A j) ν₁ ν₂ z = emb (((n : ℕ) : ℂ) • Qt S A j y ν₁) +
      emb (((n : ℕ) : ℂ) • Qt S A j (ynext S j y ν₁) ν₂) - emb (((n : ℕ) : ℂ) • Qt S A j (ynext S j y ν₂) ν₁) -
      emb (((n : ℕ) : ℂ) • Qt S A j y ν₂) := by
    simp only [Coarse.circT, Bc]
    rw [fineOf_add S hj1, fineOf_add S hj1]
  have h2 : ∀ a b c d : Mat, emb a + emb b - emb c - emb d = embL (a + b - c - d) := fun a b c d => by
    rw [map_sub, map_sub, map_add]; rfl
  rw [h1, h2, ← smul_add, ← smul_sub, ← smul_sub]
  have hM : ((n : ℕ) : ℂ) • (Qt S A j y ν₁ + Qt S A j (ynext S j y ν₁) ν₂ - Qt S A j (ynext S j y ν₂) ν₁ -
      Qt S A j y ν₂) = ((((n : ℕ) : ℂ)) ^ 4)⁻¹ • ∑ x ∈ Blk S.toDomSeq j y, ∑ s ∈ range n, ∑ t ∈ range n,
        curlM S A ν₁ ν₂ (x + ((s : ℕ) : ZMod NF) • unit NF ν₁ + ((t : ℕ) : ZMod NF) • unit NF ν₂) := by
    simp only [Qt, ynext]
    rw [hS2, hS3, ← smul_add, ← smul_sub, ← smul_sub, smul_smul, key]
    rw [show ((n : ℕ) : ℂ) * ((((n : ℕ) : ℂ)) ^ 5)⁻¹ = ((((n : ℕ) : ℂ)) ^ 4)⁻¹ by field_simp]
  exact congrArg (embL (N := N)) hM

lemma norm_circT_le {j : ℕ} (hj1 : j + 1 ≤ S.k) (A : Fin 4 → Site NF → Mat) (ν₁ ν₂ : Fin 4)
    (z : Coarse.T S.L (Mj S j)) :
    ‖Coarse.circT (Bc S A j) ν₁ ν₂ z‖ ^ 2 ≤ ((((S.L ^ j : ℕ) : ℝ)) ^ 2)⁻¹ *
      ∑ x ∈ Blk S.toDomSeq j (fineOf S j z), ∑ s ∈ range (S.L ^ j), ∑ t ∈ range (S.L ^ j),
        ‖emb (N := N) (curlM S A ν₁ ν₂ (x + ((s : ℕ) : ZMod NF) • unit NF ν₁ + ((t : ℕ) : ZMod NF) • unit NF ν₂))‖ ^ 2 := by
  have hj0 : j ≤ S.k := by omega
  set n := S.L ^ j
  have hn : (0 : ℝ) < (n : ℝ) := by exact_mod_cast pow_pos S.Lpos j
  rw [circT_Bc S hj1]
  set F : Site NF × ℕ × ℕ → VS N 1 := fun p =>
    emb (curlM S A ν₁ ν₂ (p.1 + ((p.2.1 : ℕ) : ZMod NF) • unit NF ν₁ + ((p.2.2 : ℕ) : ZMod NF) • unit NF ν₂))
  set I := Blk S.toDomSeq j (fineOf S j z) ×ˢ range n ×ˢ range n
  have e1 : emb (((((n : ℕ) : ℂ)) ^ 4)⁻¹ • ∑ x ∈ Blk S.toDomSeq j (fineOf S j z), ∑ s ∈ range n, ∑ t ∈ range n,
      curlM S A ν₁ ν₂ (x + ((s : ℕ) : ZMod NF) • unit NF ν₁ + ((t : ℕ) : ZMod NF) • unit NF ν₂)) =
      ((((n : ℕ) : ℂ)) ^ 4)⁻¹ • ∑ p ∈ I, F p := by
    show embL _ = _
    rw [map_smul]
    simp only [map_sum, I, sum_product]
    rfl
  have e2 : ∑ p ∈ I, ‖F p‖ ^ 2 = ∑ x ∈ Blk S.toDomSeq j (fineOf S j z), ∑ s ∈ range n, ∑ t ∈ range n,
      ‖emb (N := N) (curlM S A ν₁ ν₂ (x + ((s : ℕ) : ZMod NF) • unit NF ν₁ + ((t : ℕ) : ZMod NF) • unit NF ν₂))‖ ^ 2 := by
    simp only [I, sum_product]; rfl
  have hc : (I.card : ℝ) = (n : ℝ) ^ 6 := by
    simp only [I, card_product, card_range, card_Blk_j S hj0 (inLat_fineOf S j z)]; simp only [n]; push_cast; ring
  rw [e1, norm_smul, mul_pow, ← e2]
  have h3 := Cochain.norm_sum_sq_le_card I F
  rw [hc] at h3
  have hnorm : ‖((((n : ℕ) : ℂ)) ^ 4)⁻¹‖ = ((n : ℝ) ^ 4)⁻¹ := by
    rw [norm_inv, norm_pow, Complex.norm_natCast]
  rw [hnorm]
  have hS : 0 ≤ ∑ p ∈ I, ‖F p‖ ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  calc (((n : ℝ) ^ 4)⁻¹) ^ 2 * ‖∑ p ∈ I, F p‖ ^ 2 ≤ (((n : ℝ) ^ 4)⁻¹) ^ 2 * ((n : ℝ) ^ 6 * ∑ p ∈ I, ‖F p‖ ^ 2) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = ((n : ℝ) ^ 2)⁻¹ * ∑ p ∈ I, ‖F p‖ ^ 2 := by field_simp

/-- **The circulations** (the core's step "The circulations"): `Σ_{p'}|(∂B)(p')|² ≤ 2N‖∂A‖²` in the norm of `V`. -/
theorem Pall_le {j : ℕ} (hj1 : j + 1 ≤ S.k) (A : Fin 4 → Site NF → Mat) :
    Coarse.Pall (Bc S A j) ≤ 2 * N * curlE S A := by
  set n := S.L ^ j
  have hn : (0 : ℝ) < (n : ℝ) := by exact_mod_cast pow_pos S.Lpos j
  set H : Fin 4 → Fin 4 → Site NF → ℝ := fun ν₁ ν₂ x => ‖emb (N := N) (curlM S A ν₁ ν₂ x)‖ ^ 2
  have htr : ∀ ν₁ ν₂ (c : Site NF), ∑ x, H ν₁ ν₂ (x + c) = ∑ x, H ν₁ ν₂ x := fun _ _ c =>
    Fintype.sum_equiv (Equiv.addRight c) _ _ (fun _ => rfl)
  have hsum : ∀ ν₁ ν₂, ∑ z : Coarse.T S.L (Mj S j), ∑ x ∈ Blk S.toDomSeq j (fineOf S j z), ∑ s ∈ range n,
      ∑ t ∈ range n, H ν₁ ν₂ (x + ((s : ℕ) : ZMod NF) • unit NF ν₁ + ((t : ℕ) : ZMod NF) • unit NF ν₂) =
      (n : ℝ) ^ 2 * ∑ x, H ν₁ ν₂ x := by
    intro ν₁ ν₂
    calc _ = ∑ x, ∑ s ∈ range n, ∑ t ∈ range n,
          H ν₁ ν₂ (x + ((s : ℕ) : ZMod NF) • unit NF ν₁ + ((t : ℕ) : ZMod NF) • unit NF ν₂) :=
          (sum_coarse S hj1 _).symm
      _ = ∑ s ∈ range n, ∑ t ∈ range n,
          ∑ x, H ν₁ ν₂ (x + (((s : ℕ) : ZMod NF) • unit NF ν₁ + ((t : ℕ) : ZMod NF) • unit NF ν₂)) := by
          rw [sum_comm]
          refine sum_congr rfl fun s _ => ?_
          rw [sum_comm]
          simp only [add_assoc]
      _ = ∑ s ∈ range n, ∑ t ∈ range n, ∑ x, H ν₁ ν₂ x := by simp only [htr]
      _ = (n : ℝ) ^ 2 * ∑ x, H ν₁ ν₂ x := by simp only [sum_const, card_range, nsmul_eq_mul]; ring
  unfold Coarse.Pall
  have reord : ∀ G : Coarse.T S.L (Mj S j) → Fin 4 → Fin 4 → ℝ,
      ∑ z, ∑ ν₁, ∑ ν₂, G z ν₁ ν₂ = ∑ ν₁, ∑ ν₂, ∑ z, G z ν₁ ν₂ := fun G => by
    rw [sum_comm]; exact sum_congr rfl fun _ _ => sum_comm
  calc ∑ z, ∑ ν₁, ∑ ν₂, ‖Coarse.circT (Bc S A j) ν₁ ν₂ z‖ ^ 2
      ≤ ∑ z, ∑ ν₁, ∑ ν₂, ((n : ℝ) ^ 2)⁻¹ * ∑ x ∈ Blk S.toDomSeq j (fineOf S j z), ∑ s ∈ range n, ∑ t ∈ range n,
          H ν₁ ν₂ (x + ((s : ℕ) : ZMod NF) • unit NF ν₁ + ((t : ℕ) : ZMod NF) • unit NF ν₂) :=
        sum_le_sum fun z _ => sum_le_sum fun ν₁ _ => sum_le_sum fun ν₂ _ => norm_circT_le S hj1 A ν₁ ν₂ z
    _ = ∑ ν₁, ∑ ν₂, ∑ x, H ν₁ ν₂ x := by
        rw [reord]
        refine sum_congr rfl fun ν₁ _ => sum_congr rfl fun ν₂ _ => ?_
        rw [← mul_sum, hsum, ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]
    _ = 2 * N * curlE S A := by
        have r2 : ∀ G : Fin 4 → Fin 4 → Site NF → ℝ, ∑ ν₁, ∑ ν₂, ∑ x, G ν₁ ν₂ x = ∑ x, ∑ ν₁, ∑ ν₂, G ν₁ ν₂ x :=
          fun G => by
            calc _ = ∑ ν₁, ∑ x, ∑ ν₂, G ν₁ ν₂ x := sum_congr rfl fun _ _ => sum_comm
              _ = _ := sum_comm
        rw [r2]
        unfold curlE
        rw [mul_sum]
        refine sum_congr rfl fun x _ => ?_
        simp only [H, norm_emb_sq, curlM, ← mul_sum]
        ring

/-! ### The nesting of the blocks and `𝔮 = a_{j+1}Q_{j+1}` -/

lemma Yc_injective {j : ℕ} (hj1 : j + 1 ≤ S.k) : Function.Injective (Yc S j) := by
  intro w w' h
  funext ν
  have h1 := congrFun h ν
  simp only [Yc] at h1
  have hn : 0 < S.L ^ j * S.L := Nat.mul_pos (pow_pos S.Lpos _) S.Lpos
  have hlt : ∀ a : ZMod (Mj S j), S.L ^ j * (S.L * a.val) < NF := fun a => by
    rw [← nLM S hj1, ← mul_assoc, ← mul_assoc]; exact Nat.mul_lt_mul_of_pos_left a.val_lt hn
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (hlt _), Nat.mod_eq_of_lt (hlt _), ← mul_assoc,
    ← mul_assoc] at h1
  exact ZMod.val_injective _ (Nat.eq_of_mul_eq_mul_left hn h1)

lemma Yc_add {j : ℕ} (hj1 : j + 1 ≤ S.k) (w : Coarse.W (Mj S j)) (μ : Fin 4) :
    Yc S j (w + Coarse.eW μ) = ynext S (j + 1) (Yc S j w) μ := by
  funext ν
  simp only [Yc, ynext, Pi.add_apply, Pi.smul_apply, smul_eq_mul, unit]
  by_cases h : ν = μ
  · subst h
    simp only [Pi.single_eq_same, mul_one]
    rw [show ((S.L ^ j * (S.L * (w ν).val) : ℕ) : ZMod NF) + ((S.L ^ (j + 1) : ℕ) : ZMod NF) =
      ((S.L ^ j * (S.L * ((w ν).val + 1)) : ℕ) : ZMod NF) by push_cast; ring]
    rw [ZMod.natCast_eq_natCast_iff', ZMod.val_add, ZMod.val_one_eq_one_mod, ← nLM S hj1]
    have e : ∀ x : ℕ, S.L ^ j * (S.L * x) = (S.L ^ j * S.L) * x := fun x => by ring
    simp only [e]
    rw [Nat.mul_mod_mul_left, Nat.mul_mod_mul_left, Nat.mod_mod, Nat.add_mod_mod]
  · simp only [Pi.single_eq_of_ne h, add_zero, mul_zero]

/-- **A block of `T^{(j+1)}` is the union of the blocks of `T^{(j)}` in it.** -/
lemma sum_Blk_succ {β : Type*} [AddCommMonoid β] {j : ℕ} (hj1 : j + 1 ≤ S.k) (w : Coarse.W (Mj S j))
    (G : Site NF → β) :
    ∑ x ∈ Blk S.toDomSeq (j + 1) (Yc S j w), G x =
      ∑ o ∈ Coarse.bx4 (L := S.L), ∑ x ∈ Blk S.toDomSeq j (fineOf S j (Coarse.pt (c0h S j) w o)), G x := by
  classical
  have e1 : ∑ x ∈ Blk S.toDomSeq (j + 1) (Yc S j w), G x = ∑ x, if cen S.L (j + 1) x = Yc S j w then G x else 0 := by
    rw [← sum_filter]; rfl
  rw [e1, sum_coarse S hj1]
  have e2 : ∀ z : Coarse.T S.L (Mj S j), ∑ x ∈ Blk S.toDomSeq j (fineOf S j z),
      (if cen S.L (j + 1) x = Yc S j w then G x else 0) =
      if cen S.L (j + 1) (fineOf S j z) = Yc S j w then ∑ x ∈ Blk S.toDomSeq j (fineOf S j z), G x else 0 := by
    intro z
    have hc : ∀ x ∈ Blk S.toDomSeq j (fineOf S j z), cen S.L (j + 1) x = cen S.L (j + 1) (fineOf S j z) := by
      intro x hx
      simp only [Blk, mem_filter, mem_univ, true_and] at hx
      rw [← cen_nest S hj1 x, show cen S.L j x = fineOf S j z from hx]
    rw [sum_congr rfl fun x hx => by rw [hc x hx]]
    split_ifs <;> simp
  rw [sum_congr rfl fun z _ => e2 z, Coarse.sum_pt (c0h S j)]
  have e3 : ∀ w' : Coarse.W (Mj S j), ∑ o ∈ Coarse.bx4 (L := S.L),
      (if cen S.L (j + 1) (fineOf S j (Coarse.pt (c0h S j) w' o)) = Yc S j w then
        ∑ x ∈ Blk S.toDomSeq j (fineOf S j (Coarse.pt (c0h S j) w' o)), G x else 0) =
      if w' = w then ∑ o ∈ Coarse.bx4 (L := S.L),
        ∑ x ∈ Blk S.toDomSeq j (fineOf S j (Coarse.pt (c0h S j) w' o)), G x else 0 := by
    intro w'
    rw [sum_congr rfl fun o ho => by rw [cen_fineOf_pt S hj1 w' ho]]
    by_cases h : w' = w
    · subst h; simp
    · have h' : Yc S j w' ≠ Yc S j w := fun e => h (Yc_injective S hj1 e)
      simp [h, h']
  rw [sum_congr rfl fun w' _ => e3 w', sum_ite_eq']
  simp

lemma sum_range_mul_split {β : Type*} [AddCommMonoid β] (n L : ℕ) (f : ℕ → β) :
    ∑ t ∈ range L, ∑ s ∈ range n, f (n * t + s) = ∑ s ∈ range (n * L), f s := by
  induction L with
  | zero => simp
  | succ L ih => rw [sum_range_succ, ih, mul_add, mul_one, sum_range_add]

lemma pt_add_t {L M : ℕ} [NeZero L] [NeZero M] (c0 : Coarse.T L M) (w : Coarse.W M) (o : Fin 4 → ℕ) (μ : Fin 4)
    (t : ℕ) : Coarse.pt c0 w (Function.update o μ (o μ + t)) = Coarse.pt c0 w o + Pi.single μ (t : ZMod (L * M)) := by
  funext ν'
  simp only [Coarse.pt, Pi.add_apply]
  by_cases h : ν' = μ
  · subst h; simp only [Function.update_self, Pi.single_eq_same]; push_cast; ring
  · simp only [Function.update_of_ne h, Pi.single_eq_of_ne h, add_zero]

open SFBounds in
/-- **`(𝔮B)(c) = a_{j+1}(Q_{j+1}A)(c)`** (the core's description of the averages of the trivial configuration). -/
theorem qB_Bc {j : ℕ} (hj1 : j + 1 ≤ S.k) (A : Fin 4 → Site NF → Mat) (w : Coarse.W (Mj S j)) (μ : Fin 4) :
    Coarse.qB (c0h S j) (Bc S A j) w μ = emb (((S.L ^ (j + 1) : ℕ) : ℂ) • Qt S A (j + 1) (Yc S j w) μ) := by
  have hj0 : j ≤ S.k := by omega
  set n := S.L ^ j
  set L := S.L
  have hn : ((n : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (pow_pos S.Lpos j).ne'
  have hL : ((L : ℕ) : ℂ) ≠ 0 := by exact_mod_cast S.Lpos.ne'
  -- the shifted blocks
  have hshift : ∀ a b c d t, Qt S A j (fineOf S j (Coarse.pt (c0h S j) w (bx μ (a + t) b c d))) μ =
      ((((n : ℕ) : ℂ)) ^ 5)⁻¹ • ∑ x ∈ Blk S.toDomSeq j (fineOf S j (Coarse.pt (c0h S j) w (bx μ a b c d))),
        ∑ s ∈ range n, A μ (x + ((n * t + s : ℕ) : ZMod NF) • unit NF μ) := by
    intro a b c d t
    have e1 : fineOf S j (Coarse.pt (c0h S j) w (bx μ (a + t) b c d)) =
        fineOf S j (Coarse.pt (c0h S j) w (bx μ a b c d)) + ((n * t : ℕ) : ZMod NF) • unit NF μ := by
      rw [Coarse.bx_update0, pt_add_t, fineOf_add_single S hj1]
    have hv : InLat S.L j (((n * t : ℕ) : ZMod NF) • unit NF μ) := by
      intro ν
      by_cases h : ν = μ
      · subst h; exact ⟨t, by simp [unit, n]⟩
      · exact ⟨0, by simp [unit, Pi.single_eq_of_ne h]⟩
    unfold Qt
    rw [e1, sum_Blk_add S hj0 (inLat_fineOf S j _) hv]
    congr 1
    refine sum_congr rfl fun x _ => sum_congr rfl fun s _ => ?_
    congr 1
    push_cast; rw [add_smul, add_assoc]
  -- the sum over the paths
  have hpath : ∀ a b c d, ∑ t ∈ range L, Qt S A j (fineOf S j (Coarse.pt (c0h S j) w (bx μ (a + t) b c d))) μ =
      ((((n : ℕ) : ℂ)) ^ 5)⁻¹ • ∑ x ∈ Blk S.toDomSeq j (fineOf S j (Coarse.pt (c0h S j) w (bx μ a b c d))),
        ∑ s ∈ range (n * L), A μ (x + ((s : ℕ) : ZMod NF) • unit NF μ) := by
    intro a b c d
    simp only [hshift, ← smul_sum]
    congr 1
    rw [sum_comm]
    refine sum_congr rfl fun x _ => ?_
    exact sum_range_mul_split n L (fun s => A μ (x + ((s : ℕ) : ZMod NF) • unit NF μ))
  -- the left side as a sum over the block of `T^{(j+1)}`
  have hsum : ∑ i ∈ SFComponents.Iq L, Qt S A j (fineOf S j (Coarse.pt (c0h S j) w
      (bx μ (i.1 + i.2.2.2.2) i.2.1 i.2.2.1 i.2.2.2.1))) μ =
      ((((n : ℕ) : ℂ)) ^ 5)⁻¹ • ∑ x ∈ Blk S.toDomSeq (j + 1) (Yc S j w),
        ∑ s ∈ range (n * L), A μ (x + ((s : ℕ) : ZMod NF) • unit NF μ) := by
    simp only [SFComponents.Iq, sum_product, hpath, ← smul_sum]
    congr 1
    rw [sum_Blk_succ S hj1 w, sum_box_insert μ L]
  -- assembly
  unfold Coarse.qB SFComponents.boxMean
  simp only [Bc]
  have e4 : ∑ i ∈ SFComponents.Iq L, emb (N := N) (((n : ℕ) : ℂ) • Qt S A j (fineOf S j (Coarse.pt (c0h S j) w
      (bx μ (i.1 + i.2.2.2.2) i.2.1 i.2.2.1 i.2.2.2.1))) μ) =
      emb (((n : ℕ) : ℂ) • ∑ i ∈ SFComponents.Iq L, Qt S A j (fineOf S j (Coarse.pt (c0h S j) w
        (bx μ (i.1 + i.2.2.2.2) i.2.1 i.2.2.1 i.2.2.2.1))) μ) := by
    show _ = embL _
    rw [smul_sum, map_sum]; rfl
  rw [e4, hsum, SFComponents.card_Iq, smul_smul, ← Complex.coe_smul]
  rw [show ∀ (c : ℂ) (X : Mat), c • emb (N := N) X = emb (c • X) from
    fun c X => (map_smul (embL (N := N)) c X).symm]
  refine congrArg emb ?_
  unfold Qt
  rw [smul_smul, smul_smul, smul_smul, show S.L ^ (j + 1) = n * L by rw [pow_succ]]
  congr 1
  simp only [L, n]
  push_cast
  field_simp

/-! ### The layers -/

lemma bend_ef (j : ℕ) (y : Site NF) (ν : Fin 4) : S.bend j (S.ef y) ν = S.ef (ynext S j y ν) := by
  rw [ef_ynext]; rfl

/-- A bond of `T^{(j)}` with no end in `Ω_{j+1}` is a bond of `Γ_j`. -/
lemma ilb_of {j : ℕ} (hj1 : j + 1 ≤ S.k) (hlow : ∀ i ≤ j, S.Ω i = Set.univ) (z : Coarse.T S.L (Mj S j)) (ν : Fin 4)
    (h1 : S.ef (fineOf S j z) ∉ S.Ω (j + 1)) (h2 : S.ef (fineOf S j (z + Coarse.e ν)) ∉ S.Ω (j + 1)) :
    S.IsLayerBond j (S.ef (fineOf S j z)) ν := by
  refine ⟨S.ef_mem_TL_of (inLat_fineOf S j z), Or.inl (by rw [hlow j le_rfl]; trivial), h1, ?_⟩
  rw [bend_ef, ← fineOf_add S hj1]; exact h2

open Classical in
/-- **The bonds of the layer `Γ_j`** on the coarse torus. -/
lemma Gj_le {j : ℕ} (hj1 : j + 1 ≤ S.k) (hlow : ∀ i ≤ j, S.Ω i = Set.univ) (A : Fin 4 → Site NF → Mat) :
    Coarse.Gj (Lam S j) (c0h S j) (Bc S A j) ≤
      ∑ z : Coarse.T S.L (Mj S j), ∑ ν, if S.IsLayerBond j (S.ef (fineOf S j z)) ν then ‖Bc S A j ν z‖ ^ 2 else 0 := by
  rw [Coarse.sum_pt (c0h S j)]
  unfold Coarse.Gj Coarse.Int Coarse.Cross
  rw [← sum_add_distrib]
  refine sum_le_sum fun w _ => ?_
  have e1 : (if Lam S j w then 0 else ∑ o ∈ Coarse.bx4 (L := S.L), ∑ ν,
      if o ν + 1 < S.L then ‖Bc S A j ν (Coarse.pt (c0h S j) w o)‖ ^ 2 else 0) =
      ∑ o ∈ Coarse.bx4 (L := S.L), ∑ ν, if Lam S j w then 0 else
        (if o ν + 1 < S.L then ‖Bc S A j ν (Coarse.pt (c0h S j) w o)‖ ^ 2 else 0) := by
    split_ifs <;> simp
  have e2 : ∑ μ, (if ¬ Lam S j w ∧ ¬ Lam S j (w + Coarse.eW μ) then ∑ o ∈ Coarse.bx4 (L := S.L),
      (if o μ = S.L - 1 then ‖Bc S A j μ (Coarse.pt (c0h S j) w o)‖ ^ 2 else 0) else 0) =
      ∑ o ∈ Coarse.bx4 (L := S.L), ∑ μ, if ¬ Lam S j w ∧ ¬ Lam S j (w + Coarse.eW μ) then
        (if o μ = S.L - 1 then ‖Bc S A j μ (Coarse.pt (c0h S j) w o)‖ ^ 2 else 0) else 0 := by
    rw [sum_comm]
    refine sum_congr rfl fun μ _ => ?_
    split_ifs <;> simp
  rw [e1, e2, ← sum_add_distrib]
  refine sum_le_sum fun o ho => ?_
  rw [← sum_add_distrib]
  refine sum_le_sum fun ν _ => ?_
  have ho' := Coarse.mem_bx4.1 ho
  set X := ‖Bc S A j ν (Coarse.pt (c0h S j) w o)‖ ^ 2
  have hX : 0 ≤ X := sq_nonneg _
  have hR : 0 ≤ if S.IsLayerBond j (S.ef (fineOf S j (Coarse.pt (c0h S j) w o))) ν then X else 0 := by
    split_ifs <;> simp [hX]
  have hin : S.ef (fineOf S j (Coarse.pt (c0h S j) w o)) ∈ S.Ω (j + 1) ↔ Lam S j w := lam_iff S hj1 w ho
  by_cases h1 : o ν + 1 < S.L
  · have hmem : Function.update o ν (o ν + 1) ∈ Coarse.bx4 (L := S.L) := by
      rw [Coarse.mem_bx4]; intro ν'
      by_cases h' : ν' = ν
      · subst h'; simp only [Function.update_self]; omega
      · rw [Function.update_of_ne h']; exact ho' ν'
    have hnext : S.ef (fineOf S j (Coarse.pt (c0h S j) w o + Coarse.e ν)) ∈ S.Ω (j + 1) ↔ Lam S j w := by
      rw [← Coarse.pt_update]; exact lam_iff S hj1 w hmem
    rw [if_neg (show ¬ (o ν = S.L - 1) by omega), if_pos h1]
    by_cases hw : Lam S j w
    · simp only [hw, if_true, not_true, false_and, if_false, add_zero]; exact hR
    · have hilb := ilb_of S hj1 hlow _ ν (fun h => hw (hin.1 h)) (fun h => hw (hnext.1 h))
      simp only [hw, if_false, not_false_eq_true, true_and, hilb, if_true]
      split_ifs <;> linarith
  · have h2 : o ν = S.L - 1 := by have := ho' ν; omega
    rw [if_neg h1, if_pos h2]
    simp only [ite_self, zero_add]
    by_cases hc : ¬ Lam S j w ∧ ¬ Lam S j (w + Coarse.eW ν)
    · rw [if_pos hc]
      have hmem : Function.update o ν 0 ∈ Coarse.bx4 (L := S.L) := by
        rw [Coarse.mem_bx4]; intro ν'
        by_cases h' : ν' = ν
        · subst h'; simp only [Function.update_self]; exact Nat.pos_of_ne_zero (NeZero.ne S.L)
        · rw [Function.update_of_ne h']; exact ho' ν'
      have hpt : Coarse.pt (c0h S j) w o + Coarse.e ν = Coarse.pt (c0h S j) (w + Coarse.eW ν) (Function.update o ν 0) := by
        rw [← Coarse.pt_update, Coarse.pt_next]
        congr 1
        funext ν'
        by_cases h' : ν' = ν
        · subst h'
          have hL0 : 0 < S.L := S.Lpos
          simp only [Function.update_self]
          omega
        · simp only [Function.update_of_ne h']
      have hnext : S.ef (fineOf S j (Coarse.pt (c0h S j) w o + Coarse.e ν)) ∈ S.Ω (j + 1) ↔
          Lam S j (w + Coarse.eW ν) := by
        rw [hpt]; exact lam_iff S hj1 _ hmem
      have hilb := ilb_of S hj1 hlow _ ν (fun h => hc.1 (hin.1 h)) (fun h => hc.2 (hnext.1 h))
      rw [if_pos hilb]
    · rw [if_neg hc]; exact hR

lemma norm_emb_smul (c : ℂ) (X : Mat) : ‖emb (N := N) (c • X)‖ = ‖c‖ * ‖emb (N := N) X‖ := by
  rw [show emb (N := N) (c • X) = c • emb X from map_smul (embL (N := N)) c X, norm_smul]

open Classical in
/-- **The layers are among the bonds of the constraint form**: `Σ_{Γ_j}|B|² + Σ_{Γ_{j+1}}|𝔮B|² ≤ Σ_ca_c²|(QA)(c)|²`. -/
theorem Gj_Gj1_le {j : ℕ} (hj1 : j + 1 ≤ S.k) (hlow : ∀ i ≤ j, S.Ω i = Set.univ)
    (hhigh : ∀ i, j + 2 ≤ i → S.Ω i = ∅) (A : Fin 4 → Site NF → Mat) :
    Coarse.Gj (Lam S j) (c0h S j) (Bc S A j) + Coarse.Gj1 (Lam S j) (c0h S j) (Bc S A j) ≤ Qnorm S A := by
  set G : ℕ × Site NF × Fin 4 → ℝ := fun q => ((S.L ^ q.1 : ℕ) : ℝ) ^ 2 * ‖emb (N := N) (Qt S A q.1 q.2.1 q.2.2)‖ ^ 2
  have hG : ∀ q, 0 ≤ G q := fun q => by positivity
  set s1 := (univ ×ˢ univ : Finset (Coarse.T S.L (Mj S j) × Fin 4)).filter
    fun p => S.IsLayerBond j (S.ef (fineOf S j p.1)) p.2
  set s2 := (univ ×ˢ univ : Finset (Coarse.W (Mj S j) × Fin 4)).filter
    fun p => Lam S j p.1 ∨ Lam S j (p.1 + Coarse.eW p.2)
  set g1 : Coarse.T S.L (Mj S j) × Fin 4 → ℕ × Site NF × Fin 4 := fun p => (j, fineOf S j p.1, p.2)
  set g2 : Coarse.W (Mj S j) × Fin 4 → ℕ × Site NF × Fin 4 := fun p => (j + 1, Yc S j p.1, p.2)
  -- the two sums
  have h1 : Coarse.Gj (Lam S j) (c0h S j) (Bc S A j) ≤ ∑ p ∈ s1, G (g1 p) := by
    refine (Gj_le S hj1 hlow A).trans (le_of_eq ?_)
    rw [sum_filter, sum_product]
    refine sum_congr rfl fun z _ => sum_congr rfl fun ν _ => ?_
    split_ifs
    · simp only [G, g1, Bc, norm_emb_smul, mul_pow, Complex.norm_natCast]
    · rfl
  have h2 : Coarse.Gj1 (Lam S j) (c0h S j) (Bc S A j) = ∑ p ∈ s2, G (g2 p) := by
    unfold Coarse.Gj1
    rw [sum_filter, sum_product]
    refine sum_congr rfl fun w _ => sum_congr rfl fun μ _ => ?_
    split_ifs
    · simp only [G, g2, qB_Bc S hj1, norm_emb_smul, mul_pow, Complex.norm_natCast]
    · rfl
  have hi1 : Set.InjOn g1 s1 := fun p _ q _ h => by
    simp only [g1, Prod.mk.injEq] at h
    exact Prod.ext (fineOf_injective S hj1 h.2.1) h.2.2
  have hi2 : Set.InjOn g2 s2 := fun p _ q _ h => by
    simp only [g2, Prod.mk.injEq] at h
    exact Prod.ext (Yc_injective S hj1 h.2.1) h.2.2
  have hsub1 : s1.image g1 ⊆ QB S := by
    intro q hq
    obtain ⟨p, hp, rfl⟩ := mem_image.1 hq
    simp only [s1, mem_filter, mem_product, mem_univ, true_and] at hp
    simp only [QB, g1, mem_filter, mem_product, mem_range, mem_univ, and_true]
    exact ⟨by omega, inLat_fineOf S j p.1, hp⟩
  have hsub2 : s2.image g2 ⊆ QB S := by
    intro q hq
    obtain ⟨p, hp, rfl⟩ := mem_image.1 hq
    simp only [s2, mem_filter, mem_product, mem_univ, true_and] at hp
    simp only [QB, g2, mem_filter, mem_product, mem_range, mem_univ, and_true]
    refine ⟨by omega, inLat_Yc S j p.1, S.ef_mem_TL_of (inLat_Yc S j p.1), ?_, ?_, ?_⟩
    · rcases hp with h | h
      · exact Or.inl h
      · refine Or.inr ?_
        rw [bend_ef, ← Yc_add S hj1]; exact h
    · rw [hhigh (j + 2) le_rfl]; exact Set.notMem_empty _
    · rw [hhigh (j + 2) le_rfl]; exact Set.notMem_empty _
  have hdisj : Disjoint (s1.image g1) (s2.image g2) := by
    rw [Finset.disjoint_left]
    intro q h1 h2
    obtain ⟨p, -, rfl⟩ := mem_image.1 h1
    obtain ⟨p', -, he⟩ := mem_image.1 h2
    simp only [g1, g2, Prod.mk.injEq] at he
    omega
  calc _ ≤ ∑ p ∈ s1, G (g1 p) + ∑ p ∈ s2, G (g2 p) := by rw [h2]; linarith
    _ = ∑ q ∈ s1.image g1 ∪ s2.image g2, G q := by rw [sum_union hdisj, sum_image hi1, sum_image hi2]
    _ ≤ ∑ q ∈ QB S, G q := sum_le_sum_of_subset_of_nonneg (union_subset hsub1 hsub2) fun q _ _ => hG q
    _ = Qnorm S A := rfl

open Classical in
/-- **`lem:sf-two-layers`** (fine lattice, trivial configuration, the torus as the Dirichlet domain): for a sequence
with the layers `j` and `j + 1` only (`Ω_i = 𝕋` for `i ≤ j`, `Ω_i = ∅` for `i ≥ j + 2`) and every `1`-form `A`,
`‖P∂^*A‖² ≤ C_tl(‖∂A‖² + ⟨A^*, Q^*𝖺QA⟩)` with `C_tl = C_ol(1 + 2^{17}L^{10})`; the constraint form is
`N⁻¹Σ_ca_c²‖(QA)(c)‖²_V = Σ_ca_c²|(QA)(c)|²`. -/
theorem sf_two_layers [NeZero N] {j : ℕ} (hj1 : j + 1 ≤ S.k) (hlow : ∀ i ≤ j, S.Ω i = Set.univ)
    (hhigh : ∀ i, j + 2 ≤ i → S.Ω i = ∅) (A : Fin 4 → Site NF → Mat) :
    ∑ x, hs2 (Pop S (X0 S) (W1 S) Set.univ (Ds1L a1 (cfgX (X0 S)) A) x) ≤
      SFOneLayer.Col * (1 + 2 ^ 17 * (S.L : ℝ) ^ 10) * (curlE S A + (N : ℝ)⁻¹ * Qnorm S A) := by
  have h := two_layers_coarse_rhs S hj1 hlow hhigh A
  have hP := Pall_le S hj1 A
  have hQ := Gj_Gj1_le S hj1 hlow hhigh A
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hC : 0 ≤ SFOneLayer.Col := by unfold SFOneLayer.Col; positivity
  have hcurl : 0 ≤ curlE S A := by
    unfold curlE; exact sum_nonneg fun x _ => by
      have : 0 ≤ ∑ μ, ∑ ν, hs2 ((A ν (x + unit NF μ) - A ν x) - (A μ (x + unit NF ν) - A μ x)) :=
        sum_nonneg fun _ _ => sum_nonneg fun _ _ => hs2_nonneg _
      positivity
  have hQn : 0 ≤ Qnorm S A := by unfold Qnorm; exact sum_nonneg fun _ _ => by positivity
  have hL : 0 ≤ (S.L : ℝ) ^ 10 := by positivity
  refine h.trans ?_
  rw [show SFOneLayer.Col * (1 + 2 ^ 17 * (S.L : ℝ) ^ 10) * (curlE S A + (N : ℝ)⁻¹ * Qnorm S A) =
    SFOneLayer.Col * ((1 + 2 ^ 17 * (S.L : ℝ) ^ 10) * (curlE S A + (N : ℝ)⁻¹ * Qnorm S A)) by ring]
  refine mul_le_mul_of_nonneg_left ?_ hC
  have k1 : (N : ℝ)⁻¹ * (2 ^ 16 * (S.L : ℝ) ^ 10 * (Coarse.Pall (Bc S A j) + Coarse.Gj (Lam S j) (c0h S j) (Bc S A j) +
      Coarse.Gj1 (Lam S j) (c0h S j) (Bc S A j))) ≤
      (N : ℝ)⁻¹ * (2 ^ 16 * (S.L : ℝ) ^ 10 * (2 * N * curlE S A + Qnorm S A)) := by
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (by positivity)) (by positivity)
    linarith
  have k2 : (N : ℝ)⁻¹ * (2 ^ 16 * (S.L : ℝ) ^ 10 * (2 * N * curlE S A + Qnorm S A)) =
      2 ^ 17 * (S.L : ℝ) ^ 10 * curlE S A + 2 ^ 16 * (S.L : ℝ) ^ 10 * ((N : ℝ)⁻¹ * Qnorm S A) := by
    field_simp
  have hQN : 0 ≤ (N : ℝ)⁻¹ * Qnorm S A := by positivity
  nlinarith [mul_nonneg hL hcurl, mul_nonneg hL hQN]

end SFBounds
end CoreLean

end
