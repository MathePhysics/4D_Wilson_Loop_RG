/-
`lem:sf-two-layers` of BALABAN_CORE.tex (`c1d6d533fce5`), the steps "The transformation", "Pairs of blocks", and
"Conclusion", on the coarse lattice `T^{(j)}`, here the torus `T = (ℤ/LMℤ)⁴` in the units `a_j`, with the blocks of
`T^{(j+1)}` the sets `{pt w o | o ∈ [0, L)⁴}`, `w ∈ (ℤ/Mℤ)⁴`, and explicit constants in place of the core's `C_b` and
`γ_t`.

* `pt`, `sum_pt`: the point `c₀ + Lw + o`; the sum over `T` as the sum over the blocks and the offsets.
* `sig`, `boxC`: the box `B(c₋) ∪ B(c₊)` of the bond `c = (w, μ)` of `T^{(j+1)}` in the coordinates with `μ` first, and
  the cochain on it; `circ_boxC`, `Bsum_boxC`, `cross_boxC`: its circulations, its bonds inside the blocks, and its
  crossing bonds as sums over `T`.
-/
import CoreLean.CochainPair
import CoreLean.SFComponentsFine

open Finset

noncomputable section

namespace CoreLean
namespace Coarse

open Cochain SFComponents

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (L M : ℕ) [NeZero L] [NeZero M]

instance : NeZero (L * M) := ⟨Nat.mul_ne_zero (NeZero.ne L) (NeZero.ne M)⟩

/-- The coarse lattice `T^{(j)}`. -/
abbrev T := Fin 4 → ZMod (L * M)

/-- The lattice `T^{(j+1)}` of the blocks. -/
abbrev W := Fin 4 → ZMod M

variable {L M}

/-- The point `c₀ + Lw + o` of the block `w` with the offset `o`. -/
def pt (c0 : T L M) (w : W M) (o : Fin 4 → ℕ) : T L M := fun ν => c0 ν + ((L * (w ν).val + o ν : ℕ) : ZMod (L * M))

/-- The unit vector of `T`. -/
abbrev e (ν : Fin 4) : T L M := Pi.single ν 1

/-- The unit vector of `W`. -/
abbrev eW (ν : Fin 4) : W M := Pi.single ν 1

lemma pt_update (c0 : T L M) (w : W M) (o : Fin 4 → ℕ) (ν : Fin 4) :
    pt c0 w (Function.update o ν (o ν + 1)) = pt c0 w o + e ν := by
  funext ν'
  simp only [pt, Pi.add_apply]
  by_cases h : ν' = ν
  · subst h; simp only [Function.update_self, Pi.single_eq_same]; push_cast; ring
  · simp only [Function.update_of_ne h, Pi.single_eq_of_ne h, add_zero]

lemma natCast_L_val_succ (a : ZMod M) :
    ((L * (a + 1).val : ℕ) : ZMod (L * M)) = ((L * (a.val + 1) : ℕ) : ZMod (L * M)) := by
  rw [ZMod.natCast_eq_natCast_iff']
  rw [ZMod.val_add, ZMod.val_one_eq_one_mod, Nat.mul_mod_mul_left, Nat.mul_mod_mul_left, Nat.mod_mod, Nat.add_mod_mod]

lemma pt_next (c0 : T L M) (w : W M) (o : Fin 4 → ℕ) (ν : Fin 4) :
    pt c0 (w + eW ν) o = pt c0 w (Function.update o ν (o ν + L)) := by
  funext ν'
  simp only [pt, Pi.add_apply]
  by_cases h : ν' = ν
  · subst h
    simp only [Function.update_self, Pi.single_eq_same]
    have := natCast_L_val_succ (L := L) (w ν')
    push_cast at this ⊢
    rw [this]; ring
  · simp only [Function.update_of_ne h, Pi.single_eq_of_ne h, add_zero]

/-- The offsets of a block. -/
abbrev bx4 : Finset (Fin 4 → ℕ) := DiscretePoincare.box 4 L

lemma mem_bx4 {o : Fin 4 → ℕ} : o ∈ (bx4 (L := L)) ↔ ∀ ν, o ν < L := by
  simp [DiscretePoincare.box, Fintype.mem_piFinset]

/-- **The sum over `T` as the sum over the blocks and the offsets.** -/
theorem sum_pt {β : Type*} [AddCommMonoid β] (c0 : T L M) (F : T L M → β) :
    ∑ z, F z = ∑ w : W M, ∑ o ∈ bx4 (L := L), F (pt c0 w o) := by
  rw [← sum_product']
  symm
  refine Finset.sum_nbij' (fun q => pt c0 q.1 q.2)
    (fun z => (fun ν => (((z ν - c0 ν).val / L : ℕ) : ZMod M), fun ν => (z ν - c0 ν).val % L))
    (fun _ _ => mem_univ _) (fun z _ => ?_) (fun q hq => ?_) (fun z _ => ?_) (fun _ _ => rfl)
  · simp only [mem_product, mem_univ, true_and, mem_bx4]
    intro ν; exact Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne L))
  · obtain ⟨w, o⟩ := q
    simp only [mem_product, mem_univ, true_and, mem_bx4] at hq
    have hv : ∀ ν, (pt c0 w o ν - c0 ν).val = L * (w ν).val + o ν := fun ν => by
      simp only [pt, add_sub_cancel_left]
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt]
      have h1 := (w ν).val_lt
      have h2 := hq ν
      calc L * (w ν).val + o ν < L * (w ν).val + L := by omega
        _ = L * ((w ν).val + 1) := by ring
        _ ≤ L * M := Nat.mul_le_mul_left _ h1
    have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
    simp only [Prod.mk.injEq]
    refine ⟨funext fun ν => ?_, funext fun ν => ?_⟩
    · rw [hv, Nat.mul_add_div hL, Nat.div_eq_of_lt (hq ν), add_zero, ZMod.natCast_zmod_val]
    · rw [hv, Nat.mul_add_mod, Nat.mod_eq_of_lt (hq ν)]
  · funext ν
    have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
    simp only [pt]
    have hlt : (z ν - c0 ν).val / L < M := Nat.div_lt_of_lt_mul (ZMod.val_lt _)
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hlt, Nat.div_add_mod, ZMod.natCast_zmod_val]
    ring

/-! ### The box of a bond of `T^{(j+1)}` in the coordinates with `μ` first -/

open SFBounds in
/-- The direction of `T` of the coordinate `i` of the box of the direction `μ`. -/
def sig (μ : Fin 4) : Fin 4 → Fin 4 := Fin.cases μ (fun i : Fin 3 => μ.succAbove i)

lemma sig_zero (μ : Fin 4) : sig μ 0 = μ := rfl

lemma sig_bijective (μ : Fin 4) : Function.Bijective (sig μ) :=
  (Finite.injective_iff_bijective).1 (by fin_cases μ <;> decide)

lemma sum_sig {β : Type*} [AddCommMonoid β] (μ : Fin 4) (g : Fin 4 → β) : ∑ i, g (sig μ i) = ∑ ν, g ν :=
  Fintype.sum_bijective (sig μ) (sig_bijective μ) _ _ fun _ => rfl

open SFBounds in
lemma bx_sig (μ : Fin 4) (a b c d : ℕ) (i : Fin 4) : bx μ a b c d (sig μ i) = ![a, b, c, d] i := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [sig, bx_same]
  · simp only [sig, Fin.cases_succ, bx_succAbove, Matrix.cons_val_succ]

open SFBounds in
lemma bx_update0 (μ : Fin 4) (a t b c d : ℕ) :
    bx μ (a + t) b c d = Function.update (bx μ a b c d) μ (bx μ a b c d μ + t) := by
  funext ν
  refine Fin.succAboveCases μ ?_ (fun i => ?_) ν
  · simp [bx_same]
  · simp [bx_succAbove, Function.update_of_ne (Fin.succAbove_ne μ i)]

open SFBounds in
lemma bx_mv (μ ν' : Fin 4) (a b c d : ℕ) :
    bx μ (mv ν' a b c d).1 (mv ν' a b c d).2.1 (mv ν' a b c d).2.2.1 (mv ν' a b c d).2.2.2 =
      Function.update (bx μ a b c d) (sig μ ν') (bx μ a b c d (sig μ ν') + 1) := by
  fin_cases ν'
  · have hm : mv 0 a b c d = (a + 1, b, c, d) := by simp [mv]
    change bx μ (mv 0 a b c d).1 (mv 0 a b c d).2.1 (mv 0 a b c d).2.2.1 (mv 0 a b c d).2.2.2 =
      Function.update (bx μ a b c d) (sig μ 0) (bx μ a b c d (sig μ 0) + 1)
    rw [hm]
    have := bx_update0 μ a 1 b c d
    rw [bx_same] at this
    rw [sig_zero, bx_same]
    exact this
  · have hm : mv 1 a b c d = (a, b + 1, c, d) := by simp [mv]
    change bx μ (mv 1 a b c d).1 (mv 1 a b c d).2.1 (mv 1 a b c d).2.2.1 (mv 1 a b c d).2.2.2 =
      Function.update (bx μ a b c d) (sig μ 1) (bx μ a b c d (sig μ 1) + 1)
    rw [hm]; exact bx_update1 μ a b c d
  · have hm : mv 2 a b c d = (a, b, c + 1, d) := by simp [mv]
    change bx μ (mv 2 a b c d).1 (mv 2 a b c d).2.1 (mv 2 a b c d).2.2.1 (mv 2 a b c d).2.2.2 =
      Function.update (bx μ a b c d) (sig μ 2) (bx μ a b c d (sig μ 2) + 1)
    rw [hm]; exact bx_update2 μ a b c d
  · have hm : mv 3 a b c d = (a, b, c, d + 1) := by simp [mv]
    change bx μ (mv 3 a b c d).1 (mv 3 a b c d).2.1 (mv 3 a b c d).2.2.1 (mv 3 a b c d).2.2.2 =
      Function.update (bx μ a b c d) (sig μ 3) (bx μ a b c d (sig μ 3) + 1)
    rw [hm]; exact bx_update3 μ a b c d

open SFBounds in
lemma pt_bx_mv (c0 : T L M) (w : W M) (μ ν' : Fin 4) (a b c d : ℕ) :
    pt c0 w (bx μ (mv ν' a b c d).1 (mv ν' a b c d).2.1 (mv ν' a b c d).2.2.1 (mv ν' a b c d).2.2.2) =
      pt c0 w (bx μ a b c d) + e (sig μ ν') := by
  rw [bx_mv, pt_update]

open SFBounds in
/-- **The cochain on the box of the bond `(w, μ)` of `T^{(j+1)}`**, in the coordinates with `μ` first. -/
def boxC (c0 : T L M) (B : Fin 4 → T L M → E) (w : W M) (μ : Fin 4) : Coch E :=
  fun ν' a b c d => B (sig μ ν') (pt c0 w (bx μ a b c d))

/-- The circulation of a plaquette of `T`. -/
def circT (B : Fin 4 → T L M → E) (ν₁ ν₂ : Fin 4) (z : T L M) : E :=
  B ν₁ z + B ν₂ (z + e ν₁) - B ν₁ (z + e ν₂) - B ν₂ z

lemma circ_boxC (c0 : T L M) (B : Fin 4 → T L M → E) (w : W M) (μ ν₁ ν₂ : Fin 4) (a b c d : ℕ) :
    circ (boxC c0 B w μ) ν₁ ν₂ a b c d = circT B (sig μ ν₁) (sig μ ν₂) (pt c0 w (SFBounds.bx μ a b c d)) := by
  simp only [circ, boxC, circT, pt_bx_mv]

/-- The circulations of the plaquettes with the first corner in the block `w`. -/
def Pblk (c0 : T L M) (B : Fin 4 → T L M → E) (w : W M) : ℝ :=
  ∑ o ∈ bx4 (L := L), ∑ ν₁, ∑ ν₂, ‖circT B ν₁ ν₂ (pt c0 w o)‖ ^ 2

lemma sum4_mono {f : ℕ → ℕ → ℕ → ℕ → ℝ} (hf : ∀ a b c d, 0 ≤ f a b c d) {m0 m1 m2 m3 n0 n1 n2 n3 : ℕ}
    (h0 : m0 ≤ n0) (h1 : m1 ≤ n1) (h2 : m2 ≤ n2) (h3 : m3 ≤ n3) :
    ∑ a ∈ range m0, ∑ b ∈ range m1, ∑ c ∈ range m2, ∑ d ∈ range m3, f a b c d ≤
      ∑ a ∈ range n0, ∑ b ∈ range n1, ∑ c ∈ range n2, ∑ d ∈ range n3, f a b c d := by
  refine (sum_le_sum_of_subset_of_nonneg (range_mono h0) fun _ _ _ =>
    sum_nonneg fun _ _ => sum_nonneg fun _ _ => sum_nonneg fun _ _ => hf _ _ _ _).trans ?_
  refine sum_le_sum fun a _ => ?_
  refine (sum_le_sum_of_subset_of_nonneg (range_mono h1) fun _ _ _ =>
    sum_nonneg fun _ _ => sum_nonneg fun _ _ => hf _ _ _ _).trans ?_
  refine sum_le_sum fun b _ => ?_
  refine (sum_le_sum_of_subset_of_nonneg (range_mono h2) fun _ _ _ => sum_nonneg fun _ _ => hf _ _ _ _).trans ?_
  refine sum_le_sum fun c _ => ?_
  exact sum_le_sum_of_subset_of_nonneg (range_mono h3) fun _ _ _ => hf _ _ _ _

open SFBounds in
lemma full_circ_le (c0 : T L M) (B : Fin 4 → T L M → E) (w : W M) (μ ν₁ ν₂ : Fin 4) :
    ∑ a ∈ range L, ∑ b ∈ range L, ∑ c ∈ range L, ∑ d ∈ range L, ‖circ (boxC c0 B w μ) ν₁ ν₂ a b c d‖ ^ 2 ≤
      Pblk c0 B w := by
  rw [Pblk, sum_box_insert μ L]
  refine sum_le_sum fun a _ => sum_le_sum fun b _ => sum_le_sum fun c _ => sum_le_sum fun d _ => ?_
  rw [circ_boxC]
  refine (single_le_sum (f := fun ν₂' => ‖circT B (sig μ ν₁) ν₂' (pt c0 w (bx μ a b c d))‖ ^ 2)
    (fun _ _ => by positivity) (mem_univ (sig μ ν₂))).trans ?_
  exact single_le_sum (f := fun ν₁' => ∑ ν₂', ‖circT B ν₁' ν₂' (pt c0 w (bx μ a b c d))‖ ^ 2)
    (fun _ _ => by positivity) (mem_univ (sig μ ν₁))

lemma plaq_boxC_le (c0 : T L M) (B : Fin 4 → T L M → E) (w : W M) (μ ν₁ ν₂ : Fin 4) :
    Cochain.plaq (boxC c0 B w μ) (cub L) ν₁ ν₂ ≤ Pblk c0 B w :=
  (sum4_mono (fun _ _ _ _ => by positivity) (Nat.sub_le _ _) (Nat.sub_le _ _) (Nat.sub_le _ _)
    (Nat.sub_le _ _)).trans (full_circ_le c0 B w μ ν₁ ν₂)

lemma Ptot_boxC_le (c0 : T L M) (B : Fin 4 → T L M → E) (w : W M) (μ : Fin 4) :
    Cochain.Ptot (boxC c0 B w μ) (cub L) ≤ 6 * Pblk c0 B w := by
  unfold Cochain.Ptot
  linarith [plaq_boxC_le c0 B w μ 0 1, plaq_boxC_le c0 B w μ 0 2, plaq_boxC_le c0 B w μ 0 3,
    plaq_boxC_le c0 B w μ 1 2, plaq_boxC_le c0 B w μ 1 3, plaq_boxC_le c0 B w μ 2 3]

lemma XP_boxC_le (c0 : T L M) (B : Fin 4 → T L M → E) (w : W M) (μ : Fin 4) :
    XP L (boxC c0 B w μ) ≤ 3 * Pblk c0 B w := by
  have hmem : L - 1 ∈ range L := mem_range.2 (by have := NeZero.ne L; omega)
  have k : ∀ ν : Fin 4, ∑ b ∈ range L, ∑ c ∈ range L, ∑ d ∈ range L,
      ‖circ (boxC c0 B w μ) 0 ν (L - 1) b c d‖ ^ 2 ≤ Pblk c0 B w := fun ν =>
    (single_le_sum (f := fun a => ∑ b ∈ range L, ∑ c ∈ range L, ∑ d ∈ range L,
      ‖circ (boxC c0 B w μ) 0 ν a b c d‖ ^ 2) (fun _ _ => by positivity) hmem).trans (full_circ_le c0 B w μ 0 ν)
  unfold XP
  simp only [sum_add_distrib]
  linarith [k 1, k 2, k 3]

/-! ### The bonds of the blocks -/

/-- The bonds with both ends in the block `w`: `Σ_{o}Σ_{ν, o_ν + 1 < L}‖B_ν(pt w o)‖²`. -/
def Int (c0 : T L M) (B : Fin 4 → T L M → E) (w : W M) : ℝ :=
  ∑ o ∈ bx4 (L := L), ∑ ν, if o ν + 1 < L then ‖B ν (pt c0 w o)‖ ^ 2 else 0

/-- The bonds of the direction `μ` from the block `w` to the block `w + e_μ`. -/
def Cross (c0 : T L M) (B : Fin 4 → T L M → E) (w : W M) (μ : Fin 4) : ℝ :=
  ∑ o ∈ bx4 (L := L), if o μ = L - 1 then ‖B μ (pt c0 w o)‖ ^ 2 else 0

omit [NormedSpace ℝ E] in
lemma sum_ite_lt (L : ℕ) (g : ℕ → ℝ) :
    ∑ t ∈ range L, (if t + 1 < L then g t else 0) = ∑ t ∈ range (L - 1), g t := by
  rw [← sum_filter]
  congr 1
  ext t; simp only [mem_filter, mem_range]; omega

lemma sum_ite_irr {ι : Type*} (p : Prop) [Decidable p] (s : Finset ι) (f : ι → ℝ) {inst : ι → Decidable p} :
    ∑ x ∈ s, @ite ℝ p (inst x) (f x) 0 = if p then ∑ x ∈ s, f x else 0 := by
  by_cases hp : p <;> simp [hp]

omit [NormedSpace ℝ E] in
lemma sum_pred_eq (L : ℕ) (F G : ℕ → ℝ) (h1 : ∀ t, t + 1 < L → G t = F t) (h2 : ∀ t, ¬ t + 1 < L → G t = 0) :
    ∑ t ∈ range (L - 1), F t = ∑ t ∈ range L, G t := by
  rw [← sum_ite_lt L F]
  refine sum_congr rfl fun t _ => ?_
  by_cases ht : t + 1 < L
  · rw [if_pos ht, h1 t ht]
  · rw [if_neg ht, h2 t ht]

open SFBounds in
/-- **The bonds inside a block** in the coordinates of the box: `Bsum = Int`. -/
lemma Bsum_boxC (c0 : T L M) (B : Fin 4 → T L M → E) (w : W M) (μ : Fin 4) :
    Bsum (boxC c0 B w μ) (cub L) = Int c0 B w := by
  unfold Int
  rw [sum_comm, ← sum_sig μ]
  simp only [sum_box_insert μ L, bx_sig, Fin.sum_univ_four]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons]
  unfold Bsum
  congr 1; congr 1; congr 1
  · refine sum_pred_eq _ _ _ (fun t ht => ?_) (fun t ht => ?_)
    · have ht' : t + 1 < L := ht
      simp only [ht', ↓reduceIte, boxC]
    · have ht' : ¬ t + 1 < L := ht
      simp only [ht', ↓reduceIte, sum_const_zero]
  · refine sum_congr rfl fun a _ => sum_pred_eq _ _ _ (fun t ht => ?_) (fun t ht => ?_)
    · have ht' : t + 1 < L := ht
      simp only [ht', ↓reduceIte, boxC]
    · have ht' : ¬ t + 1 < L := ht
      simp only [ht', ↓reduceIte, sum_const_zero]
  · refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => sum_pred_eq _ _ _ (fun t ht => ?_) (fun t ht => ?_)
    · have ht' : t + 1 < L := ht
      simp only [ht', ↓reduceIte, boxC]
    · have ht' : ¬ t + 1 < L := ht
      simp only [ht', ↓reduceIte, sum_const_zero]
  · refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => sum_congr rfl fun c _ =>
      sum_pred_eq _ _ _ (fun t ht => ?_) (fun t ht => ?_)
    · have ht' : t + 1 < L := ht
      simp only [ht', ↓reduceIte, boxC]
    · have ht' : ¬ t + 1 < L := ht
      simp only [ht', ↓reduceIte]

lemma shG_boxC (c0 : T L M) (B : Fin 4 → T L M → E) (w : W M) (μ : Fin 4) :
    shG L (boxC c0 B w μ) = boxC c0 B (w + eW μ) μ := by
  funext ν' a b c d
  simp only [shG, boxC, pt_next]
  rw [bx_update0, SFBounds.bx_same]

open SFBounds in
/-- **The crossing bonds** in the coordinates of the box. -/
lemma cross_boxC (c0 : T L M) (B : Fin 4 → T L M → E) (w : W M) (μ : Fin 4) :
    ∑ b ∈ range L, ∑ c ∈ range L, ∑ d ∈ range L, ‖boxC c0 B w μ 0 (L - 1) b c d‖ ^ 2 = Cross c0 B w μ := by
  unfold Cross
  rw [sum_box_insert μ L]
  simp only [bx_same, sum_ite_irr, sum_ite_eq', mem_range]
  rw [if_pos (by have := NeZero.ne L; omega)]
  rfl

/-- **The bonds of `T`**: each lies inside a block or crosses from a block to the next. -/
lemma total_split (c0 : T L M) (B : Fin 4 → T L M → E) :
    ∑ z, ∑ ν, ‖B ν z‖ ^ 2 = ∑ w : W M, (Int c0 B w + ∑ μ, Cross c0 B w μ) := by
  rw [sum_pt c0]
  refine sum_congr rfl fun w _ => ?_
  unfold Int Cross
  rw [sum_comm (s := univ) (t := bx4 (L := L)), ← sum_add_distrib]
  refine sum_congr rfl fun o ho => ?_
  rw [← sum_add_distrib]
  refine sum_congr rfl fun ν _ => ?_
  have h := (mem_bx4.1 ho) ν
  by_cases h1 : o ν + 1 < L
  · rw [if_pos h1, if_neg (by omega), add_zero]
  · rw [if_neg h1, if_pos (by omega), zero_add]

/-! ### The decomposition of a point -/

/-- The block and the offset of a point of `T`. -/
def dec (c0 : T L M) (z : T L M) : W M × (Fin 4 → ℕ) :=
  (fun ν => (((z ν - c0 ν).val / L : ℕ) : ZMod M), fun ν => (z ν - c0 ν).val % L)

lemma dec_pt (c0 : T L M) (w : W M) {o : Fin 4 → ℕ} (ho : o ∈ bx4 (L := L)) : dec c0 (pt c0 w o) = (w, o) := by
  rw [mem_bx4] at ho
  have hv : ∀ ν, (pt c0 w o ν - c0 ν).val = L * (w ν).val + o ν := fun ν => by
    simp only [pt, add_sub_cancel_left]
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt]
    have h1 := (w ν).val_lt
    have h2 := ho ν
    calc L * (w ν).val + o ν < L * (w ν).val + L := by omega
      _ = L * ((w ν).val + 1) := by ring
      _ ≤ L * M := Nat.mul_le_mul_left _ h1
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  simp only [dec, Prod.mk.injEq]
  refine ⟨funext fun ν => ?_, funext fun ν => ?_⟩
  · rw [hv, Nat.mul_add_div hL, Nat.div_eq_of_lt (ho ν), add_zero, ZMod.natCast_zmod_val]
  · rw [hv, Nat.mul_add_mod, Nat.mod_eq_of_lt (ho ν)]

/-! ### The function `ω` on the blocks of `Λ` -/

/-- The integral of `B` along the coordinate paths of the block `w` from its first corner. -/
def kapW (c0 : T L M) (B : Fin 4 → T L M → E) (w : W M) : ℕ → ℕ → ℕ → ℕ → E := kap (boxC c0 B w 0)

/-- Its mean over the block. -/
def meanW (c0 : T L M) (B : Fin 4 → T L M → E) (w : W M) : E :=
  ((L : ℝ) ^ 4)⁻¹ • ∑ a ∈ range L, ∑ b ∈ range L, ∑ c ∈ range L, ∑ d ∈ range L, kapW c0 B w a b c d

/-- **The function `ω`** (the core's transformation): on a block of `Λ` the path integral minus its mean, else `0`. -/
def omg (c0 : T L M) (Λ : W M → Prop) [DecidablePred Λ] (B : Fin 4 → T L M → E) (z : T L M) : E :=
  if Λ (dec c0 z).1 then
    kapW c0 B (dec c0 z).1 ((dec c0 z).2 0) ((dec c0 z).2 1) ((dec c0 z).2 2) ((dec c0 z).2 3) - meanW c0 B (dec c0 z).1
  else 0

variable (Λ : W M → Prop) [DecidablePred Λ]

lemma omg_pt (c0 : T L M) (B : Fin 4 → T L M → E) (w : W M) {o : Fin 4 → ℕ} (ho : o ∈ bx4 (L := L)) :
    omg c0 Λ B (pt c0 w o) = if Λ w then kapW c0 B w (o 0) (o 1) (o 2) (o 3) - meanW c0 B w else 0 := by
  simp only [omg, dec_pt c0 w ho]

open SFBounds in
lemma bx0_mem {a b c d : ℕ} (ha : a < L) (hb : b < L) (hc : c < L) (hd : d < L) : bx 0 a b c d ∈ bx4 (L := L) := by
  rw [mem_bx4]; intro ν; fin_cases ν <;> simp [bx] <;> assumption

open SFBounds in
lemma omg_bx0 (c0 : T L M) (B : Fin 4 → T L M → E) (w : W M) (hw : Λ w) {a b c d : ℕ} (ha : a < L) (hb : b < L)
    (hc : c < L) (hd : d < L) : omg c0 Λ B (pt c0 w (bx 0 a b c d)) = kapW c0 B w a b c d - meanW c0 B w := by
  rw [omg_pt Λ c0 B w (bx0_mem ha hb hc hd), if_pos hw]
  simp [bx]

lemma omg_zero (c0 : T L M) (B : Fin 4 → T L M → E) (w : W M) (hw : ¬ Λ w) {o : Fin 4 → ℕ}
    (ho : o ∈ bx4 (L := L)) : omg c0 Λ B (pt c0 w o) = 0 := by
  rw [omg_pt Λ c0 B w ho, if_neg hw]

open SFBounds in
/-- **The sums of `ω` over the blocks vanish.** -/
lemma omg_sum (c0 : T L M) (B : Fin 4 → T L M → E) (w : W M) : ∑ o ∈ bx4 (L := L), omg c0 Λ B (pt c0 w o) = 0 := by
  by_cases hw : Λ w
  · rw [sum_box_insert 0 L]
    have e : ∀ a ∈ range L, ∀ b ∈ range L, ∀ c ∈ range L, ∀ d ∈ range L,
        omg c0 Λ B (pt c0 w (bx 0 a b c d)) = kapW c0 B w a b c d - meanW c0 B w :=
      fun a ha b hb c hc d hd => omg_bx0 Λ c0 B w hw (mem_range.1 ha) (mem_range.1 hb) (mem_range.1 hc)
        (mem_range.1 hd)
    rw [sum_congr rfl fun a ha => sum_congr rfl fun b hb => sum_congr rfl fun c hc => sum_congr rfl fun d hd =>
      e a ha b hb c hc d hd]
    simp only [sum_sub_distrib, sum_const, card_range]
    have hL : (L : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne L
    rw [meanW, ← Nat.cast_smul_eq_nsmul ℝ, ← Nat.cast_smul_eq_nsmul ℝ, ← Nat.cast_smul_eq_nsmul ℝ,
      ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, smul_smul, smul_smul, smul_smul]
    rw [show (L : ℝ) * L * L * L * ((L : ℝ) ^ 4)⁻¹ = 1 by field_simp, one_smul, sub_self]
  · exact sum_eq_zero fun o ho => omg_zero Λ c0 B w hw ho

/-- `B̂ = B - dω`. -/
def Bh (c0 : T L M) (B : Fin 4 → T L M → E) : Fin 4 → T L M → E :=
  fun ν z => B ν z - (omg c0 Λ B (z + e ν) - omg c0 Λ B z)

omit [NeZero L] [NeZero M] [NormedSpace ℝ E] in
lemma circT_sub_d (B : Fin 4 → T L M → E) (ω : T L M → E) (ν₁ ν₂ : Fin 4) (z : T L M) :
    circT (fun ν z => B ν z - (ω (z + e ν) - ω z)) ν₁ ν₂ z = circT B ν₁ ν₂ z := by
  simp only [circT]
  rw [add_right_comm z (e ν₂) (e ν₁)]
  abel

lemma Pblk_Bh (c0 : T L M) (B : Fin 4 → T L M → E) (w : W M) : Pblk c0 (Bh Λ c0 B) w = Pblk c0 B w := by
  have h : ∀ ν₁ ν₂ z, circT (Bh Λ c0 B) ν₁ ν₂ z = circT B ν₁ ν₂ z := fun ν₁ ν₂ z =>
    circT_sub_d B (omg c0 Λ B) ν₁ ν₂ z
  simp only [Pblk, h]

/-! ### The bonds inside a block -/

omit [NormedSpace ℝ E] in
lemma Bsum_congr (G1 G2 : Coch E) (ℓ : Fin 4 → ℕ)
    (h0 : ∀ a b c d, a + 1 < ℓ 0 → b < ℓ 1 → c < ℓ 2 → d < ℓ 3 → G1 0 a b c d = G2 0 a b c d)
    (h1 : ∀ a b c d, a < ℓ 0 → b + 1 < ℓ 1 → c < ℓ 2 → d < ℓ 3 → G1 1 a b c d = G2 1 a b c d)
    (h2 : ∀ a b c d, a < ℓ 0 → b < ℓ 1 → c + 1 < ℓ 2 → d < ℓ 3 → G1 2 a b c d = G2 2 a b c d)
    (h3 : ∀ a b c d, a < ℓ 0 → b < ℓ 1 → c < ℓ 2 → d + 1 < ℓ 3 → G1 3 a b c d = G2 3 a b c d) :
    Bsum G1 ℓ = Bsum G2 ℓ := by
  unfold Bsum
  congr 1; congr 1; congr 1
  · refine sum_congr rfl fun a ha => sum_congr rfl fun b hb => sum_congr rfl fun c hc => sum_congr rfl fun d hd => ?_
    simp only [mem_range] at ha hb hc hd
    rw [h0 a b c d (by omega) hb hc hd]
  · refine sum_congr rfl fun a ha => sum_congr rfl fun b hb => sum_congr rfl fun c hc => sum_congr rfl fun d hd => ?_
    simp only [mem_range] at ha hb hc hd
    rw [h1 a b c d ha (by omega) hc hd]
  · refine sum_congr rfl fun a ha => sum_congr rfl fun b hb => sum_congr rfl fun c hc => sum_congr rfl fun d hd => ?_
    simp only [mem_range] at ha hb hc hd
    rw [h2 a b c d ha hb (by omega) hd]
  · refine sum_congr rfl fun a ha => sum_congr rfl fun b hb => sum_congr rfl fun c hc => sum_congr rfl fun d hd => ?_
    simp only [mem_range] at ha hb hc hd
    rw [h3 a b c d ha hb hc (by omega)]

open SFBounds in
/-- On a bond inside a block of `Λ`, `B̂ = F - dκ`. -/
lemma boxC_Bh_eq (c0 : T L M) (B : Fin 4 → T L M → E) (w : W M) (hw : Λ w) (ν : Fin 4) {a b c d : ℕ}
    (ha : a < L) (hb : b < L) (hc : c < L) (hd : d < L) (h0 : (mv ν a b c d).1 < L) (h1 : (mv ν a b c d).2.1 < L)
    (h2 : (mv ν a b c d).2.2.1 < L) (h3 : (mv ν a b c d).2.2.2 < L) :
    boxC c0 (Bh Λ c0 B) w 0 ν a b c d = Fh (boxC c0 B w 0) ν a b c d := by
  have hP := pt_bx_mv c0 w 0 ν a b c d
  simp only [boxC, Bh, Fh]
  rw [← hP, omg_bx0 Λ c0 B w hw h0 h1 h2 h3, omg_bx0 Λ c0 B w hw ha hb hc hd]
  simp only [kapW, mv]
  abel

/-- The bound of the bonds inside a block: `72L⁵Σ_{plaquettes}|∂B|²` on a block of `Λ`, `B` itself else. -/
def J (c0 : T L M) (B : Fin 4 → T L M → E) (w : W M) : ℝ :=
  if Λ w then 72 * (L : ℝ) ^ 5 * Pblk c0 B w else Int c0 B w

lemma J_nonneg (c0 : T L M) (B : Fin 4 → T L M → E) (w : W M) : 0 ≤ J Λ c0 B w := by
  unfold J Pblk Int
  split_ifs
  · positivity
  · refine sum_nonneg fun o _ => sum_nonneg fun ν _ => ?_
    split_ifs <;> positivity

/-- **The bonds inside a block** (the core's step "The transformation", with `C_b = 72L⁵`). -/
lemma Int_Bh_le (c0 : T L M) (B : Fin 4 → T L M → E) (w : W M) : Int c0 (Bh Λ c0 B) w ≤ J Λ c0 B w := by
  unfold J
  split_ifs with hw
  · rw [← Bsum_boxC c0 (Bh Λ c0 B) w 0]
    have e : Bsum (boxC c0 (Bh Λ c0 B) w 0) (cub L) = Bsum (Fh (boxC c0 B w 0)) (cub L) := by
      refine Bsum_congr _ _ _ (fun a b c d ha hb hc hd => ?_) (fun a b c d ha hb hc hd => ?_)
        (fun a b c d ha hb hc hd => ?_) (fun a b c d ha hb hc hd => ?_)
      all_goals
        simp only [cub] at ha hb hc hd
        exact boxC_Bh_eq Λ c0 B w hw _ (by omega) (by omega) (by omega) (by omega) (by simp [mv]; omega)
          (by simp [mv]; omega) (by simp [mv]; omega) (by simp [mv]; omega)
    rw [e]
    have hp := poincare_box (boxC c0 B w 0) (cub L) (m := L) (fun _ => le_rfl)
    have hq := Ptot_boxC_le c0 B w 0
    have hP : 0 ≤ Cochain.Ptot (boxC c0 B w 0) (cub L) := by
      have := plaq_nonneg (boxC c0 B w 0) (cub L)
      unfold Cochain.Ptot; linarith [this 0 1, this 0 2, this 0 3, this 1 2, this 1 3, this 2 3]
    calc _ ≤ 12 * (L : ℝ) * ((L : ℝ) * L * L * L) * Cochain.Ptot (boxC c0 B w 0) (cub L) := hp
      _ ≤ 12 * (L : ℝ) * ((L : ℝ) * L * L * L) * (6 * Pblk c0 B w) :=
          mul_le_mul_of_nonneg_left hq (by positivity)
      _ = _ := by ring
  · refine le_of_eq (sum_congr rfl fun o ho => sum_congr rfl fun ν _ => ?_)
    split_ifs with h
    · have ho' := mem_bx4.1 ho
      have hmem : Function.update o ν (o ν + 1) ∈ bx4 (L := L) := by
        rw [mem_bx4]; intro ν'
        by_cases h' : ν' = ν
        · subst h'; simp only [Function.update_self]; omega
        · rw [Function.update_of_ne h']; exact ho' ν'
      simp only [Bh]
      rw [← pt_update, omg_zero Λ c0 B w hw hmem, omg_zero Λ c0 B w hw ho, sub_zero, sub_zero]
    · rfl

/-! ### The crossing bonds -/

/-- **`(𝔮B)(c)`** for the bond `c = (w, μ)` of `T^{(j+1)}`: `L` times the mean over the block `w` of the means of
`B_μ` along the paths of `L` bonds. -/
def qB (c0 : T L M) (B : Fin 4 → T L M → E) (w : W M) (μ : Fin 4) : E :=
  (L : ℝ) • boxMean L (fun a b c d => B μ (pt c0 w (SFBounds.bx μ a b c d)))

open SFBounds in
lemma pt_bx_succ (c0 : T L M) (w : W M) (μ : Fin 4) (a b c d : ℕ) :
    pt c0 w (bx μ a b c d) + e μ = pt c0 w (bx μ (a + 1) b c d) := by
  rw [bx_update0, pt_update]

open SFBounds in
lemma pt_bx_L (c0 : T L M) (w : W M) (μ : Fin 4) (a b c d : ℕ) :
    pt c0 w (bx μ (a + L) b c d) = pt c0 (w + eW μ) (bx μ a b c d) := by
  rw [pt_next, bx_update0, bx_same]

open SFBounds in
/-- **`𝔮` does not see `dω`**: the sums of `dω` along the paths telescope and the sums of `ω` over the blocks vanish. -/
lemma qB_Bh (c0 : T L M) (B : Fin 4 → T L M → E) (w : W M) (μ : Fin 4) : qB c0 (Bh Λ c0 B) w μ = qB c0 B w μ := by
  unfold qB boxMean
  congr 2
  have hω : ∑ i ∈ Iq L, (omg c0 Λ B (pt c0 w (bx μ (i.1 + i.2.2.2.2) i.2.1 i.2.2.1 i.2.2.2.1) + e μ) -
      omg c0 Λ B (pt c0 w (bx μ (i.1 + i.2.2.2.2) i.2.1 i.2.2.1 i.2.2.2.1))) = 0 := by
    simp only [Iq, sum_product, pt_bx_succ]
    have e1 : ∀ a b c d, ∑ t ∈ range L, (omg c0 Λ B (pt c0 w (bx μ (a + t + 1) b c d)) -
        omg c0 Λ B (pt c0 w (bx μ (a + t) b c d))) =
        omg c0 Λ B (pt c0 (w + eW μ) (bx μ a b c d)) - omg c0 Λ B (pt c0 w (bx μ a b c d)) := fun a b c d => by
      have := sum_range_sub (fun t => omg c0 Λ B (pt c0 w (bx μ (a + t) b c d))) L
      simp only [add_zero, ← add_assoc] at this
      rw [this, pt_bx_L]
    simp only [e1, sum_sub_distrib]
    rw [← sum_box_insert μ L (fun o => omg c0 Λ B (pt c0 (w + eW μ) o)),
      ← sum_box_insert μ L (fun o => omg c0 Λ B (pt c0 w o)), omg_sum, omg_sum, sub_self]
  simp only [Bh, sum_sub_distrib, hω, sub_zero]

lemma Cross_Bh_out (c0 : T L M) (B : Fin 4 → T L M → E) (w : W M) (μ : Fin 4) (hw : ¬ Λ w)
    (hw' : ¬ Λ (w + eW μ)) : Cross c0 (Bh Λ c0 B) w μ = Cross c0 B w μ := by
  refine sum_congr rfl fun o ho => ?_
  split_ifs with h
  · have ho' := mem_bx4.1 ho
    have hmem : Function.update o μ 0 ∈ bx4 (L := L) := by
      rw [mem_bx4]; intro ν'
      by_cases h' : ν' = μ
      · subst h'; simp only [Function.update_self]; exact Nat.pos_of_ne_zero (NeZero.ne L)
      · rw [Function.update_of_ne h']; exact ho' ν'
    have hpt : pt c0 w o + e μ = pt c0 (w + eW μ) (Function.update o μ 0) := by
      rw [← pt_update, pt_next]
      congr 1
      funext ν'
      by_cases h' : ν' = μ
      · subst h'
        have hL0 : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
        simp only [Function.update_self]
        omega
      · simp only [Function.update_of_ne h']
    simp only [Bh]
    rw [hpt, omg_zero Λ c0 B _ hw' hmem, omg_zero Λ c0 B w hw ho, sub_zero, sub_zero]
  · rfl

/-- **The crossing bonds of a pair of blocks** (the core's step "Pairs of blocks", with `γ_t⁻¹ = 64L⁵`). -/
lemma Cross_Bh_le (c0 : T L M) (B : Fin 4 → T L M → E) (w : W M) (μ : Fin 4) :
    Cross c0 (Bh Λ c0 B) w μ ≤
      64 * (L : ℝ) ^ 5 * (3 * Pblk c0 B w + (J Λ c0 B w + J Λ c0 B (w + eW μ)) + ‖qB c0 B w μ‖ ^ 2) := by
  have hL : 1 ≤ L := Nat.pos_of_ne_zero (NeZero.ne L)
  have h := pair_cross L hL (boxC c0 (Bh Λ c0 B) w μ)
  rw [cross_boxC, shG_boxC, Bsum_boxC, Bsum_boxC] at h
  have hX := XP_boxC_le c0 (Bh Λ c0 B) w μ
  rw [Pblk_Bh] at hX
  have hq : (L : ℝ) ^ 2 * ‖boxMean L (fun a b c d => boxC c0 (Bh Λ c0 B) w μ 0 a b c d)‖ ^ 2 =
      ‖qB c0 B w μ‖ ^ 2 := by
    rw [← qB_Bh Λ c0 B w μ, qB, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    rfl
  rw [hq] at h
  have h1 := Int_Bh_le Λ c0 B w
  have h2 := Int_Bh_le Λ c0 B (w + eW μ)
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  linarith

/-! ### The conclusion -/

/-- All the plaquettes of `T`. -/
def Pall (B : Fin 4 → T L M → E) : ℝ := ∑ z, ∑ ν₁, ∑ ν₂, ‖circT B ν₁ ν₂ z‖ ^ 2

/-- The bonds of `T` with no end in a block of `Λ` (the layer `Γ_j`). -/
def Gj (c0 : T L M) (B : Fin 4 → T L M → E) : ℝ :=
  ∑ w : W M, (if Λ w then 0 else Int c0 B w) +
    ∑ w : W M, ∑ μ, (if ¬ Λ w ∧ ¬ Λ (w + eW μ) then Cross c0 B w μ else 0)

/-- The bonds `c` of `T^{(j+1)}` with an end in `Λ` (the layer `Γ_{j+1}`), `Σ_c|(𝔮B)(c)|²`. -/
def Gj1 (c0 : T L M) (B : Fin 4 → T L M → E) : ℝ :=
  ∑ w : W M, ∑ μ, (if Λ w ∨ Λ (w + eW μ) then ‖qB c0 B w μ‖ ^ 2 else 0)

lemma sum_shift_W {β : Type*} [AddCommMonoid β] (g : W M → β) (v : W M) : ∑ w, g (w + v) = ∑ w, g w :=
  Fintype.sum_equiv (Equiv.addRight v) _ _ fun _ => rfl

/-- **`lem:sf-two-layers` on the coarse lattice**: there is `ω`, zero on the blocks outside `Λ` and with the sum zero
over every block, such that `Σ_{bonds}|B - dω|² ≤ 2^{16}L^{10}(Σ_{plaquettes}|∂B|² + Σ_{Γ_j}|B|² + Σ_{Γ_{j+1}}|𝔮B|²)`. -/
theorem coarse_two_layers (c0 : T L M) (B : Fin 4 → T L M → E) :
    ∃ ω : T L M → E, (∀ w, ¬ Λ w → ∀ o ∈ bx4 (L := L), ω (pt c0 w o) = 0) ∧
      (∀ w, ∑ o ∈ bx4 (L := L), ω (pt c0 w o) = 0) ∧
      ∑ z, ∑ ν, ‖B ν z - (ω (z + e ν) - ω z)‖ ^ 2 ≤ 2 ^ 16 * (L : ℝ) ^ 10 * (Pall B + Gj Λ c0 B + Gj1 Λ c0 B) := by
  refine ⟨omg c0 Λ B, fun w hw o ho => omg_zero Λ c0 B w hw ho, fun w => omg_sum Λ c0 B w, ?_⟩
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  set Bh' := Bh Λ c0 B
  change ∑ z, ∑ ν, ‖Bh' ν z‖ ^ 2 ≤ _
  rw [total_split c0 Bh', sum_add_distrib]
  set P := ∑ w : W M, Pblk c0 B w with hPdef
  set SJ := ∑ w : W M, J Λ c0 B w
  have hPall : Pall B = P := by rw [hPdef, Pall, sum_pt c0]; rfl
  have hP0 : 0 ≤ P := sum_nonneg fun w _ => by unfold Pblk; positivity
  have hJ0 : ∀ w, 0 ≤ J Λ c0 B w := J_nonneg Λ c0 B
  have hq0 : ∀ w μ, 0 ≤ ‖qB c0 B w μ‖ ^ 2 := fun _ _ => sq_nonneg _
  -- the bonds inside the blocks
  have hI : ∑ w : W M, Int c0 Bh' w ≤ SJ := sum_le_sum fun w _ => Int_Bh_le Λ c0 B w
  -- `SJ ≤ 72L⁵P + Σ_{w ∉ Λ}Int`
  have hSJ : SJ ≤ 72 * (L : ℝ) ^ 5 * P + ∑ w : W M, (if Λ w then 0 else Int c0 B w) := by
    rw [hPdef, mul_sum, ← sum_add_distrib]
    refine sum_le_sum fun w _ => ?_
    unfold J
    have hPb : 0 ≤ Pblk c0 B w := by unfold Pblk; positivity
    have hIb : 0 ≤ Int c0 B w := by
      unfold Int; exact sum_nonneg fun o _ => sum_nonneg fun ν _ => by split_ifs <;> positivity
    have h72 := mul_nonneg (show (0 : ℝ) ≤ 72 * (L : ℝ) ^ 5 by positivity) hPb
    split_ifs <;> linarith
  -- the crossing bonds
  have hC : ∀ w μ, Cross c0 Bh' w μ ≤
      64 * (L : ℝ) ^ 5 * (3 * Pblk c0 B w + (J Λ c0 B w + J Λ c0 B (w + eW μ))) +
        64 * (L : ℝ) ^ 5 * (if Λ w ∨ Λ (w + eW μ) then ‖qB c0 B w μ‖ ^ 2 else 0) +
        (if ¬ Λ w ∧ ¬ Λ (w + eW μ) then Cross c0 B w μ else 0) := by
    intro w μ
    have hPb : 0 ≤ Pblk c0 B w := by unfold Pblk; positivity
    have hA : 0 ≤ 64 * (L : ℝ) ^ 5 * (3 * Pblk c0 B w + (J Λ c0 B w + J Λ c0 B (w + eW μ))) := by
      have := hJ0 w; have := hJ0 (w + eW μ); positivity
    by_cases h : Λ w ∨ Λ (w + eW μ)
    · have hn : ¬ (¬ Λ w ∧ ¬ Λ (w + eW μ)) := by tauto
      rw [if_pos h, if_neg hn, add_zero]
      have := Cross_Bh_le Λ c0 B w μ
      linarith
    · have hn : ¬ Λ w ∧ ¬ Λ (w + eW μ) := by tauto
      rw [if_neg h, if_pos hn, mul_zero, add_zero, Cross_Bh_out Λ c0 B w μ hn.1 hn.2]
      linarith
  have hCsum : ∑ w : W M, ∑ μ, Cross c0 Bh' w μ ≤
      64 * (L : ℝ) ^ 5 * (12 * P + 8 * SJ) + 64 * (L : ℝ) ^ 5 * Gj1 Λ c0 B +
        ∑ w : W M, ∑ μ, (if ¬ Λ w ∧ ¬ Λ (w + eW μ) then Cross c0 B w μ else 0) := by
    refine (sum_le_sum fun w _ => sum_le_sum fun μ _ => hC w μ).trans (le_of_eq ?_)
    have e1 : ∑ w : W M, ∑ μ : Fin 4, J Λ c0 B (w + eW μ) = 4 * SJ := by
      rw [sum_comm]
      simp only [sum_shift_W (fun w => J Λ c0 B w), sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
      norm_num
      rfl
    have a1 : ∑ w : W M, ∑ μ : Fin 4, 3 * Pblk c0 B w = 12 * P := by
      rw [hPdef, mul_sum]
      refine sum_congr rfl fun w _ => ?_
      simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    have a2 : ∑ w : W M, ∑ μ : Fin 4, J Λ c0 B w = 4 * SJ := by
      rw [mul_sum]
      refine sum_congr rfl fun w _ => ?_
      simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
      norm_num
    have s1 : ∑ w : W M, ∑ μ : Fin 4, (3 * Pblk c0 B w + (J Λ c0 B w + J Λ c0 B (w + eW μ))) = 12 * P + 8 * SJ := by
      simp only [sum_add_distrib]
      rw [a1, a2, e1]; ring
    have a1' : ∑ w : W M, ∑ μ : Fin 4, Pblk c0 B w = 4 * P := by
      rw [hPdef, mul_sum]
      refine sum_congr rfl fun w _ => ?_
      simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
      norm_num
    simp only [sum_add_distrib, ← mul_sum]
    rw [a1', a2, e1, Gj1]
    ring
  -- assembly
  unfold Gj
  set G0 := ∑ w : W M, (if Λ w then 0 else Int c0 B w)
  set G1 := ∑ w : W M, ∑ μ, (if ¬ Λ w ∧ ¬ Λ (w + eW μ) then Cross c0 B w μ else 0)
  have hG0 : 0 ≤ G0 := sum_nonneg fun w _ => by
    split_ifs
    · exact le_rfl
    · unfold Int; exact sum_nonneg fun o _ => sum_nonneg fun ν _ => by split_ifs <;> positivity
  have hG1 : 0 ≤ G1 := sum_nonneg fun w _ => sum_nonneg fun μ _ => by
    split_ifs
    · unfold Cross; exact sum_nonneg fun o _ => by split_ifs <;> positivity
    · exact le_rfl
  have hGj1 : 0 ≤ Gj1 Λ c0 B := sum_nonneg fun w _ => sum_nonneg fun μ _ => by split_ifs <;> positivity
  rw [hPall]
  have hL5 : (1 : ℝ) ≤ (L : ℝ) ^ 5 := one_le_pow₀ hL1
  have hL10 : (L : ℝ) ^ 10 = (L : ℝ) ^ 5 * (L : ℝ) ^ 5 := by ring
  rw [hL10]
  nlinarith [mul_le_mul_of_nonneg_left hSJ (show (0 : ℝ) ≤ 512 * (L : ℝ) ^ 5 by positivity),
    mul_nonneg (mul_nonneg (show (0 : ℝ) ≤ (L : ℝ) ^ 5 - 1 by linarith) (show (0 : ℝ) ≤ (L : ℝ) ^ 5 by positivity)) hP0,
    mul_nonneg (show (0 : ℝ) ≤ (L : ℝ) ^ 5 - 1 by linarith) hP0,
    mul_nonneg (mul_nonneg (show (0 : ℝ) ≤ (L : ℝ) ^ 5 - 1 by linarith) (show (0 : ℝ) ≤ (L : ℝ) ^ 5 by positivity)) hG0,
    mul_nonneg (show (0 : ℝ) ≤ (L : ℝ) ^ 5 - 1 by linarith) hG0,
    mul_nonneg (mul_nonneg (show (0 : ℝ) ≤ (L : ℝ) ^ 5 - 1 by linarith) (show (0 : ℝ) ≤ (L : ℝ) ^ 5 by positivity)) hG1,
    mul_nonneg (show (0 : ℝ) ≤ (L : ℝ) ^ 5 - 1 by linarith) hG1,
    mul_nonneg (mul_nonneg (show (0 : ℝ) ≤ (L : ℝ) ^ 5 - 1 by linarith) (show (0 : ℝ) ≤ (L : ℝ) ^ 5 by positivity)) hGj1,
    mul_nonneg (show (0 : ℝ) ≤ (L : ℝ) ^ 5 - 1 by linarith) hGj1,
    mul_nonneg (show (0 : ℝ) ≤ (L : ℝ) ^ 5 by positivity) hP0, mul_nonneg (show (0 : ℝ) ≤ (L : ℝ) ^ 5 by positivity) hG0,
    mul_nonneg (show (0 : ℝ) ≤ (L : ℝ) ^ 5 by positivity) hGj1]

end Coarse
end CoreLean

end
