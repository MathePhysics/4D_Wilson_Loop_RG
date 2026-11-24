/-
`lem:sf-two-layers` of BALABAN_CORE.tex (`c1d6d533fce5`), the step "Pairs of blocks", on the box
`[0, 2L) × [0, L)³` of the coarse lattice, with an explicit constant in place of the core's `γ_t`.

The two blocks are `a < L` and `a ≥ L`; the bonds crossing from one to the other are the bonds of the direction `0` at
`a = L - 1`. Their values `f(b, c, d) = G_0(L - 1, b, c, d)` form a function on the cube `[0, L)³`:

* its differences are circulations of the crossing plaquettes plus values on bonds inside the blocks (`circ01` …);
* its mean is `L` times the mean of `G_0` along the paths of `L` bonds from the points of the first block (the core's
  `(𝔮G)(c)`), up to the values on the bonds of the direction `0` inside the blocks.

With the Poincaré inequality on the cube (`cube3_poincare`, from `SFComponents.poincare4`), `pair_cross`:
`Σ_{crossing}‖G‖² ≤ 64L⁵(Σ_{crossing plaquettes}‖∂G‖² + Σ_{bonds inside the blocks}‖G‖² + L²‖QG‖²)`.
-/
import CoreLean.CochainPoincare
import CoreLean.SFComponents

open Finset

noncomputable section

namespace CoreLean
namespace Cochain

open SFComponents

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The cube of the side `L`. -/
abbrev cub (L : ℕ) : Fin 4 → ℕ := fun _ => L

/-- The translate by `L` in the direction `0` (the second block). -/
def shG (L : ℕ) (G : Coch E) : Coch E := fun ν a b c d => G ν (a + L) b c d

/-- The circulations of the plaquettes crossing the face `a = L - 1`. -/
def XP (L : ℕ) (G : Coch E) : ℝ :=
  ∑ b ∈ range L, ∑ c ∈ range L, ∑ d ∈ range L,
    (‖circ G 0 1 (L - 1) b c d‖ ^ 2 + ‖circ G 0 2 (L - 1) b c d‖ ^ 2 + ‖circ G 0 3 (L - 1) b c d‖ ^ 2)

/-- The differences of a function on the cube `[0, L)³`. -/
def D3 (L : ℕ) (f : ℕ → ℕ → ℕ → E) : ℝ :=
  ∑ t ∈ range (L - 1), ∑ c ∈ range L, ∑ d ∈ range L, ‖f (t + 1) c d - f t c d‖ ^ 2 +
  ∑ b ∈ range L, ∑ t ∈ range (L - 1), ∑ d ∈ range L, ‖f b (t + 1) d - f b t d‖ ^ 2 +
  ∑ b ∈ range L, ∑ c ∈ range L, ∑ t ∈ range (L - 1), ‖f b c (t + 1) - f b c t‖ ^ 2

/-- The mean over the cube `[0, L)³`. -/
def mean3 (L : ℕ) (f : ℕ → ℕ → ℕ → E) : E :=
  ((L : ℝ) ^ 3)⁻¹ • ∑ b ∈ range L, ∑ c ∈ range L, ∑ d ∈ range L, f b c d

lemma sum_comm_in {α : Type*} [AddCommMonoid α] (s t u : Finset ℕ) (g : ℕ → ℕ → ℕ → α) :
    ∑ x ∈ s, ∑ y ∈ t, ∑ z ∈ u, g x y z = ∑ x ∈ s, ∑ z ∈ u, ∑ y ∈ t, g x y z :=
  sum_congr rfl fun _ _ => sum_comm

lemma sum_comm_out {α : Type*} [AddCommMonoid α] (s t u : Finset ℕ) (g : ℕ → ℕ → ℕ → α) :
    ∑ x ∈ s, ∑ y ∈ t, ∑ z ∈ u, g x y z = ∑ z ∈ u, ∑ x ∈ s, ∑ y ∈ t, g x y z := by
  rw [sum_comm_in, sum_comm]

lemma sum_comm4 {α : Type*} [AddCommMonoid α] (s t u v : Finset ℕ) (g : ℕ → ℕ → ℕ → ℕ → α) :
    ∑ x ∈ s, ∑ y ∈ t, ∑ z ∈ u, ∑ w ∈ v, g x y z w = ∑ w ∈ v, ∑ x ∈ s, ∑ y ∈ t, ∑ z ∈ u, g x y z w := by
  calc _ = ∑ x ∈ s, ∑ w ∈ v, ∑ y ∈ t, ∑ z ∈ u, g x y z w :=
        sum_congr rfl fun x _ => sum_comm_out t u v (g x)
    _ = _ := sum_comm

/-- **The Poincaré inequality on the cube `[0, L)³`**: `Σ‖f - mean f‖² ≤ 4L²Σ_{bonds}‖∂f‖²`. -/
lemma cube3_poincare (L : ℕ) (hL : 1 ≤ L) (f : ℕ → ℕ → ℕ → E) :
    ∑ b ∈ range L, ∑ c ∈ range L, ∑ d ∈ range L, ‖f b c d - mean3 L f‖ ^ 2 ≤ 4 * (L : ℝ) ^ 2 * D3 L f := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
  set S3 := range L ×ˢ range L ×ˢ range L with hS3
  have hc : (S3.card : ℝ) = (L : ℝ) ^ 3 := by simp [hS3, card_product]; ring
  have hne : S3.Nonempty := by
    rw [← card_pos]; have : (0 : ℝ) < S3.card := by rw [hc]; positivity
    exact_mod_cast this
  have hpt : ∀ b c d, ‖f b c d - mean3 L f‖ ^ 2 ≤
      ((L : ℝ) ^ 3)⁻¹ * ∑ b' ∈ range L, ∑ c' ∈ range L, ∑ d' ∈ range L, ‖f b c d - f b' c' d'‖ ^ 2 := by
    intro b c d
    have h := sq_sub_mean_le S3 hne (f b c d) (fun i => f i.1 i.2.1 i.2.2)
    rw [hc] at h
    simpa only [hS3, sum_product, mean3] using h
  have h4 := poincare4 1 L L L (fun _ b c d => f b c d)
  simp only [range_one, sum_singleton, bondSum, Nat.cast_one, one_pow, one_mul, Nat.sub_self, range_zero,
    sum_empty, sum_const_zero, mul_zero, zero_add] at h4
  have e2 : ∑ c ∈ range L, ∑ d ∈ range L, ∑ t ∈ range (L - 1), ‖f (t + 1) c d - f t c d‖ ^ 2 =
      ∑ t ∈ range (L - 1), ∑ c ∈ range L, ∑ d ∈ range L, ‖f (t + 1) c d - f t c d‖ ^ 2 :=
    sum_comm_out _ _ _ (fun c d t => ‖f (t + 1) c d - f t c d‖ ^ 2)
  have e3 : ∑ b ∈ range L, ∑ d ∈ range L, ∑ t ∈ range (L - 1), ‖f b (t + 1) d - f b t d‖ ^ 2 =
      ∑ b ∈ range L, ∑ t ∈ range (L - 1), ∑ d ∈ range L, ‖f b (t + 1) d - f b t d‖ ^ 2 :=
    sum_comm_in _ _ _ (fun b d t => ‖f b (t + 1) d - f b t d‖ ^ 2)
  rw [e2, e3] at h4
  have hsum : ∑ b ∈ range L, ∑ c ∈ range L, ∑ d ∈ range L, ‖f b c d - mean3 L f‖ ^ 2 ≤
      ((L : ℝ) ^ 3)⁻¹ * ∑ b ∈ range L, ∑ c ∈ range L, ∑ d ∈ range L,
        ∑ b' ∈ range L, ∑ c' ∈ range L, ∑ d' ∈ range L, ‖f b c d - f b' c' d'‖ ^ 2 := by
    calc _ ≤ ∑ b ∈ range L, ∑ c ∈ range L, ∑ d ∈ range L, ((L : ℝ) ^ 3)⁻¹ *
          ∑ b' ∈ range L, ∑ c' ∈ range L, ∑ d' ∈ range L, ‖f b c d - f b' c' d'‖ ^ 2 :=
          sum_le_sum fun b _ => sum_le_sum fun c _ => sum_le_sum fun d _ => hpt b c d
      _ = _ := by simp only [mul_sum]
  refine hsum.trans ?_
  have hD : 0 ≤ D3 L f := by unfold D3; positivity
  calc ((L : ℝ) ^ 3)⁻¹ * _ ≤ ((L : ℝ) ^ 3)⁻¹ * (4 * (L * L * L) * ((L : ℝ) ^ 2 * D3 L f)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine h4.trans_eq ?_
        unfold D3; ring
    _ = 4 * (L : ℝ) ^ 2 * D3 L f := by field_simp

lemma norm_sub3_sq (x y z : E) : ‖x - y - z‖ ^ 2 ≤ 3 * (‖x‖ ^ 2 + ‖y‖ ^ 2 + ‖z‖ ^ 2) := by
  have h := norm_add3_sq x (-y) (-z)
  rwa [norm_neg, norm_neg, ← sub_eq_add_neg, ← sub_eq_add_neg] at h

lemma sq_add_le' (x y : E) : ‖x + y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
  have h := norm_add_le x y
  have h0 := norm_nonneg (x + y)
  nlinarith [sq_nonneg (‖x‖ - ‖y‖), norm_nonneg x, norm_nonneg y]

lemma sq_sub_le' (x y : E) : ‖x - y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
  have h := sq_add_le' x (-y)
  rwa [norm_neg, ← sub_eq_add_neg] at h

/-- A term of a nonnegative double-indexed sum is at most the sum. -/
lemma le_sum_at {f : ℕ → ℝ} (hf : ∀ a, 0 ≤ f a) {s : Finset ℕ} {a : ℕ} (ha : a ∈ s) : f a ≤ ∑ x ∈ s, f x :=
  single_le_sum (fun x _ => hf x) ha

/-- **The differences of the crossing values.** -/
lemma D3_cross_le (L : ℕ) (hL : 1 ≤ L) (G : Coch E) :
    D3 L (fun b c d => G 0 (L - 1) b c d) ≤ 3 * (XP L G + Bsum G (cub L) + Bsum (shG L G) (cub L)) := by
  have hL1 : L - 1 + 1 = L := Nat.sub_add_cancel hL
  have hP1 : ∀ b c d, G 0 (L - 1) (b + 1) c d - G 0 (L - 1) b c d =
      G 1 L b c d - G 1 (L - 1) b c d - circ G 0 1 (L - 1) b c d := fun b c d => by
    rw [circ01, hL1]; abel
  have hP2 : ∀ b c d, G 0 (L - 1) b (c + 1) d - G 0 (L - 1) b c d =
      G 2 L b c d - G 2 (L - 1) b c d - circ G 0 2 (L - 1) b c d := fun b c d => by
    rw [circ02, hL1]; abel
  have hP3 : ∀ b c d, G 0 (L - 1) b c (d + 1) - G 0 (L - 1) b c d =
      G 3 L b c d - G 3 (L - 1) b c d - circ G 0 3 (L - 1) b c d := fun b c d => by
    rw [circ03, hL1]; abel
  have hsub : range (L - 1) ⊆ range L := range_mono (Nat.sub_le _ _)
  have hmem : L - 1 ∈ range L := mem_range.2 (by omega)
  have hmem0 : 0 ∈ range L := mem_range.2 (by omega)
  -- the three parts of `XP`
  set X1 := ∑ b ∈ range L, ∑ c ∈ range L, ∑ d ∈ range L, ‖circ G 0 1 (L - 1) b c d‖ ^ 2
  set X2 := ∑ b ∈ range L, ∑ c ∈ range L, ∑ d ∈ range L, ‖circ G 0 2 (L - 1) b c d‖ ^ 2
  set X3 := ∑ b ∈ range L, ∑ c ∈ range L, ∑ d ∈ range L, ‖circ G 0 3 (L - 1) b c d‖ ^ 2
  have hXP : XP L G = X1 + X2 + X3 := by simp only [XP, X1, X2, X3, sum_add_distrib]
  -- the parts of the two `Bsum`s
  set B1 := ∑ a ∈ range L, ∑ b ∈ range (L - 1), ∑ c ∈ range L, ∑ d ∈ range L, ‖G 1 a b c d‖ ^ 2
  set B2 := ∑ a ∈ range L, ∑ b ∈ range L, ∑ c ∈ range (L - 1), ∑ d ∈ range L, ‖G 2 a b c d‖ ^ 2
  set B3 := ∑ a ∈ range L, ∑ b ∈ range L, ∑ c ∈ range L, ∑ d ∈ range (L - 1), ‖G 3 a b c d‖ ^ 2
  set C1 := ∑ a ∈ range L, ∑ b ∈ range (L - 1), ∑ c ∈ range L, ∑ d ∈ range L, ‖G 1 (a + L) b c d‖ ^ 2
  set C2 := ∑ a ∈ range L, ∑ b ∈ range L, ∑ c ∈ range (L - 1), ∑ d ∈ range L, ‖G 2 (a + L) b c d‖ ^ 2
  set C3 := ∑ a ∈ range L, ∑ b ∈ range L, ∑ c ∈ range L, ∑ d ∈ range (L - 1), ‖G 3 (a + L) b c d‖ ^ 2
  have hB0 : 0 ≤ ∑ a ∈ range (L - 1), ∑ b ∈ range L, ∑ c ∈ range L, ∑ d ∈ range L, ‖G 0 a b c d‖ ^ 2 := by
    positivity
  have hC0 : 0 ≤ ∑ a ∈ range (L - 1), ∑ b ∈ range L, ∑ c ∈ range L, ∑ d ∈ range L, ‖G 0 (a + L) b c d‖ ^ 2 := by
    positivity
  have hBs : Bsum G (cub L) = (∑ a ∈ range (L - 1), ∑ b ∈ range L, ∑ c ∈ range L, ∑ d ∈ range L,
      ‖G 0 a b c d‖ ^ 2) + B1 + B2 + B3 := rfl
  have hCs : Bsum (shG L G) (cub L) = (∑ a ∈ range (L - 1), ∑ b ∈ range L, ∑ c ∈ range L, ∑ d ∈ range L,
      ‖G 0 (a + L) b c d‖ ^ 2) + C1 + C2 + C3 := rfl
  -- the direction `1`
  have d1 : ∑ t ∈ range (L - 1), ∑ c ∈ range L, ∑ d ∈ range L,
      ‖G 0 (L - 1) (t + 1) c d - G 0 (L - 1) t c d‖ ^ 2 ≤ 3 * (C1 + B1 + X1) := by
    have hA : ∑ t ∈ range (L - 1), ∑ c ∈ range L, ∑ d ∈ range L, ‖G 1 L t c d‖ ^ 2 ≤ C1 := by
      have := le_sum_at (f := fun a => ∑ b ∈ range (L - 1), ∑ c ∈ range L, ∑ d ∈ range L, ‖G 1 (a + L) b c d‖ ^ 2)
        (fun _ => by positivity) hmem0
      simpa only [zero_add] using this
    have hB : ∑ t ∈ range (L - 1), ∑ c ∈ range L, ∑ d ∈ range L, ‖G 1 (L - 1) t c d‖ ^ 2 ≤ B1 :=
      le_sum_at (f := fun a => ∑ b ∈ range (L - 1), ∑ c ∈ range L, ∑ d ∈ range L, ‖G 1 a b c d‖ ^ 2)
        (fun _ => by positivity) hmem
    have hX : ∑ t ∈ range (L - 1), ∑ c ∈ range L, ∑ d ∈ range L, ‖circ G 0 1 (L - 1) t c d‖ ^ 2 ≤ X1 :=
      sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
    calc _ ≤ ∑ t ∈ range (L - 1), ∑ c ∈ range L, ∑ d ∈ range L,
          3 * (‖G 1 L t c d‖ ^ 2 + ‖G 1 (L - 1) t c d‖ ^ 2 + ‖circ G 0 1 (L - 1) t c d‖ ^ 2) :=
          sum_le_sum fun t _ => sum_le_sum fun c _ => sum_le_sum fun d _ => by rw [hP1]; exact norm_sub3_sq _ _ _
      _ = 3 * (∑ t ∈ range (L - 1), ∑ c ∈ range L, ∑ d ∈ range L, ‖G 1 L t c d‖ ^ 2 +
          ∑ t ∈ range (L - 1), ∑ c ∈ range L, ∑ d ∈ range L, ‖G 1 (L - 1) t c d‖ ^ 2 +
          ∑ t ∈ range (L - 1), ∑ c ∈ range L, ∑ d ∈ range L, ‖circ G 0 1 (L - 1) t c d‖ ^ 2) := by
          simp only [mul_add, sum_add_distrib, mul_sum]
      _ ≤ 3 * (C1 + B1 + X1) := by linarith
  -- the direction `2`
  have d2 : ∑ b ∈ range L, ∑ t ∈ range (L - 1), ∑ d ∈ range L,
      ‖G 0 (L - 1) b (t + 1) d - G 0 (L - 1) b t d‖ ^ 2 ≤ 3 * (C2 + B2 + X2) := by
    have hA : ∑ b ∈ range L, ∑ t ∈ range (L - 1), ∑ d ∈ range L, ‖G 2 L b t d‖ ^ 2 ≤ C2 := by
      have := le_sum_at (f := fun a => ∑ b ∈ range L, ∑ c ∈ range (L - 1), ∑ d ∈ range L, ‖G 2 (a + L) b c d‖ ^ 2)
        (fun _ => by positivity) hmem0
      simpa only [zero_add] using this
    have hB : ∑ b ∈ range L, ∑ t ∈ range (L - 1), ∑ d ∈ range L, ‖G 2 (L - 1) b t d‖ ^ 2 ≤ B2 :=
      le_sum_at (f := fun a => ∑ b ∈ range L, ∑ c ∈ range (L - 1), ∑ d ∈ range L, ‖G 2 a b c d‖ ^ 2)
        (fun _ => by positivity) hmem
    have hX : ∑ b ∈ range L, ∑ t ∈ range (L - 1), ∑ d ∈ range L, ‖circ G 0 2 (L - 1) b t d‖ ^ 2 ≤ X2 :=
      sum_le_sum fun b _ => sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
    calc _ ≤ ∑ b ∈ range L, ∑ t ∈ range (L - 1), ∑ d ∈ range L,
          3 * (‖G 2 L b t d‖ ^ 2 + ‖G 2 (L - 1) b t d‖ ^ 2 + ‖circ G 0 2 (L - 1) b t d‖ ^ 2) :=
          sum_le_sum fun b _ => sum_le_sum fun t _ => sum_le_sum fun d _ => by rw [hP2]; exact norm_sub3_sq _ _ _
      _ = 3 * (∑ b ∈ range L, ∑ t ∈ range (L - 1), ∑ d ∈ range L, ‖G 2 L b t d‖ ^ 2 +
          ∑ b ∈ range L, ∑ t ∈ range (L - 1), ∑ d ∈ range L, ‖G 2 (L - 1) b t d‖ ^ 2 +
          ∑ b ∈ range L, ∑ t ∈ range (L - 1), ∑ d ∈ range L, ‖circ G 0 2 (L - 1) b t d‖ ^ 2) := by
          simp only [mul_add, sum_add_distrib, mul_sum]
      _ ≤ 3 * (C2 + B2 + X2) := by linarith
  -- the direction `3`
  have d3 : ∑ b ∈ range L, ∑ c ∈ range L, ∑ t ∈ range (L - 1),
      ‖G 0 (L - 1) b c (t + 1) - G 0 (L - 1) b c t‖ ^ 2 ≤ 3 * (C3 + B3 + X3) := by
    have hA : ∑ b ∈ range L, ∑ c ∈ range L, ∑ t ∈ range (L - 1), ‖G 3 L b c t‖ ^ 2 ≤ C3 := by
      have := le_sum_at (f := fun a => ∑ b ∈ range L, ∑ c ∈ range L, ∑ d ∈ range (L - 1), ‖G 3 (a + L) b c d‖ ^ 2)
        (fun _ => by positivity) hmem0
      simpa only [zero_add] using this
    have hB : ∑ b ∈ range L, ∑ c ∈ range L, ∑ t ∈ range (L - 1), ‖G 3 (L - 1) b c t‖ ^ 2 ≤ B3 :=
      le_sum_at (f := fun a => ∑ b ∈ range L, ∑ c ∈ range L, ∑ d ∈ range (L - 1), ‖G 3 a b c d‖ ^ 2)
        (fun _ => by positivity) hmem
    have hX : ∑ b ∈ range L, ∑ c ∈ range L, ∑ t ∈ range (L - 1), ‖circ G 0 3 (L - 1) b c t‖ ^ 2 ≤ X3 :=
      sum_le_sum fun b _ => sum_le_sum fun c _ => sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
    calc _ ≤ ∑ b ∈ range L, ∑ c ∈ range L, ∑ t ∈ range (L - 1),
          3 * (‖G 3 L b c t‖ ^ 2 + ‖G 3 (L - 1) b c t‖ ^ 2 + ‖circ G 0 3 (L - 1) b c t‖ ^ 2) :=
          sum_le_sum fun b _ => sum_le_sum fun c _ => sum_le_sum fun t _ => by rw [hP3]; exact norm_sub3_sq _ _ _
      _ = 3 * (∑ b ∈ range L, ∑ c ∈ range L, ∑ t ∈ range (L - 1), ‖G 3 L b c t‖ ^ 2 +
          ∑ b ∈ range L, ∑ c ∈ range L, ∑ t ∈ range (L - 1), ‖G 3 (L - 1) b c t‖ ^ 2 +
          ∑ b ∈ range L, ∑ c ∈ range L, ∑ t ∈ range (L - 1), ‖circ G 0 3 (L - 1) b c t‖ ^ 2) := by
          simp only [mul_add, sum_add_distrib, mul_sum]
      _ ≤ 3 * (C3 + B3 + X3) := by linarith
  have e : D3 L (fun b c d => G 0 (L - 1) b c d) =
      ∑ t ∈ range (L - 1), ∑ c ∈ range L, ∑ d ∈ range L, ‖G 0 (L - 1) (t + 1) c d - G 0 (L - 1) t c d‖ ^ 2 +
      ∑ b ∈ range L, ∑ t ∈ range (L - 1), ∑ d ∈ range L, ‖G 0 (L - 1) b (t + 1) d - G 0 (L - 1) b t d‖ ^ 2 +
      ∑ b ∈ range L, ∑ c ∈ range L, ∑ t ∈ range (L - 1), ‖G 0 (L - 1) b c (t + 1) - G 0 (L - 1) b c t‖ ^ 2 := rfl
  rw [e, hXP, hBs, hCs]
  linarith

/-- The splitting of the paths: `Σ_{a,t<L}g(a + t) = Lg(L - 1) + Σ_{a,t<L}g'(a + t)`, `g' = g` off `L - 1`. -/
lemma sum_paths_split (L : ℕ) (g : ℕ → E) :
    ∑ a ∈ range L, ∑ t ∈ range L, g (a + t) =
      (L : ℝ) • g (L - 1) + ∑ a ∈ range L, ∑ t ∈ range L, (if a + t = L - 1 then 0 else g (a + t)) := by
  have h : ∀ a ∈ range L, ∑ t ∈ range L, g (a + t) =
      g (L - 1) + ∑ t ∈ range L, (if a + t = L - 1 then 0 else g (a + t)) := by
    intro a ha
    have ha' := mem_range.1 ha
    have hsplit : ∀ t, g (a + t) =
        (if a + t = L - 1 then g (L - 1) else 0) + (if a + t = L - 1 then 0 else g (a + t)) := by
      intro t; split_ifs with h
      · rw [h, add_zero]
      · rw [zero_add]
    rw [sum_congr rfl fun t _ => hsplit t, sum_add_distrib]
    congr 1
    have hc : ∀ t, (a + t = L - 1) ↔ (t = L - 1 - a) := fun t => by omega
    simp only [hc, sum_ite_eq', mem_range]
    rw [if_pos (by omega)]
  rw [sum_congr rfl h, sum_add_distrib, sum_const, card_range, ← Nat.cast_smul_eq_nsmul ℝ]

/-- `Σ_{s<2(L'+1)}` of `q` with the terms `s = L'` and `s ≥ 2L' + 1` removed. -/
lemma sum_h_eq (L' : ℕ) (q : ℕ → ℝ) :
    ∑ s ∈ range (2 * (L' + 1)), (if s = L' ∨ 2 * (L' + 1) - 1 ≤ s then 0 else q s) =
      ∑ s ∈ range L', q s + ∑ s ∈ range L', q (s + (L' + 1)) := by
  rw [two_mul, sum_range_add, sum_range_succ, sum_range_succ]
  rw [if_pos (Or.inl rfl), if_pos (Or.inr (by omega)), add_zero, add_zero]
  congr 1
  · exact sum_congr rfl fun s hs => by rw [if_neg (by have := mem_range.1 hs; omega)]
  · exact sum_congr rfl fun s hs => by rw [if_neg (by have := mem_range.1 hs; omega), add_comm]

lemma norm_sum_sq_le_card {ι : Type*} (s : Finset ι) (v : ι → E) :
    ‖∑ i ∈ s, v i‖ ^ 2 ≤ s.card * ∑ i ∈ s, ‖v i‖ ^ 2 :=
  (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2).trans (sq_sum_le_card_mul_sum_sq (s := s) (f := fun i => ‖v i‖))

/-- **The mean of the crossing values** is `L` times the mean along the paths (the core's `(𝔮G)(c)`), up to the
bonds of the direction `0` inside the blocks. -/
lemma mean_cross_le (L : ℕ) (hL : 1 ≤ L) (G : Coch E) :
    ‖mean3 L (fun b c d => G 0 (L - 1) b c d)‖ ^ 2 ≤
      2 * (L : ℝ) ^ 2 * ‖boxMean L (fun a b c d => G 0 a b c d)‖ ^ 2 +
        2 * ((L : ℝ) ^ 2)⁻¹ * (Bsum G (cub L) + Bsum (shG L G) (cub L)) := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
  set f : ℕ → ℕ → ℕ → E := fun b c d => G 0 (L - 1) b c d
  set g' : ℕ → ℕ → ℕ → ℕ → E := fun s b c d => if s = L - 1 then 0 else G 0 s b c d
  set R := ∑ b ∈ range L, ∑ c ∈ range L, ∑ d ∈ range L, ∑ a ∈ range L, ∑ t ∈ range L, g' (a + t) b c d with hRdef
  set bm := boxMean L (fun a b c d => G 0 a b c d)
  set XI := Bsum G (cub L) + Bsum (shG L G) (cub L)
  -- `L⁵QG = L⁴m + R`
  have hbm : ((L : ℝ) ^ 5) • bm = ((L : ℝ) ^ 4) • mean3 L f + R := by
    have e1 : ((L : ℝ) ^ 5) • bm =
        ∑ a ∈ range L, ∑ b ∈ range L, ∑ c ∈ range L, ∑ d ∈ range L, ∑ t ∈ range L, G 0 (a + t) b c d := by
      simp only [bm, boxMean, card_Iq, smul_smul]
      push_cast
      rw [mul_inv_cancel₀ (by positivity), one_smul]
      simp only [Iq, sum_product]
    have e2 : ∑ a ∈ range L, ∑ b ∈ range L, ∑ c ∈ range L, ∑ d ∈ range L, ∑ t ∈ range L, G 0 (a + t) b c d =
        ∑ b ∈ range L, ∑ c ∈ range L, ∑ d ∈ range L, ∑ a ∈ range L, ∑ t ∈ range L, G 0 (a + t) b c d :=
      (sum_comm4 (range L) (range L) (range L) (range L)
        (fun b c d a => ∑ t ∈ range L, G 0 (a + t) b c d)).symm
    have e3 : ∀ b c d, ∑ a ∈ range L, ∑ t ∈ range L, G 0 (a + t) b c d =
        (L : ℝ) • f b c d + ∑ a ∈ range L, ∑ t ∈ range L, g' (a + t) b c d := fun b c d =>
      sum_paths_split L (fun s => G 0 s b c d)
    rw [e1, e2]
    simp only [e3, sum_add_distrib, ← smul_sum]
    rw [mean3, smul_smul]
    congr 1
    congr 1
    field_simp
  have hm : mean3 L f = (L : ℝ) • bm - ((L : ℝ) ^ 4)⁻¹ • R := by
    have h4 : ((L : ℝ) ^ 4) ≠ 0 := by positivity
    have : mean3 L f = ((L : ℝ) ^ 4)⁻¹ • (((L : ℝ) ^ 5) • bm - R) := by
      rw [hbm, add_sub_cancel_right, smul_smul, inv_mul_cancel₀ h4, one_smul]
    rw [this, smul_sub, smul_smul]
    congr 2
    field_simp
  -- `‖R‖² ≤ L⁶XI`
  have hR : ‖R‖ ^ 2 ≤ (L : ℝ) ^ 6 * XI := by
    set I5 := range L ×ˢ range L ×ˢ range L ×ˢ range L ×ˢ range L
    have eR : R = ∑ i ∈ I5, g' (i.2.2.2.1 + i.2.2.2.2) i.1 i.2.1 i.2.2.1 := by
      simp only [hRdef, I5, sum_product]
    have hc : (I5.card : ℝ) = (L : ℝ) ^ 5 := by simp [I5, card_product]; ring
    have h1 := norm_sum_sq_le_card I5 (fun i => g' (i.2.2.2.1 + i.2.2.2.2) i.1 i.2.1 i.2.2.1)
    rw [← eR, hc] at h1
    have e5 : ∑ i ∈ I5, ‖g' (i.2.2.2.1 + i.2.2.2.2) i.1 i.2.1 i.2.2.1‖ ^ 2 =
        ∑ b ∈ range L, ∑ c ∈ range L, ∑ d ∈ range L, ∑ a ∈ range L, ∑ t ∈ range L, ‖g' (a + t) b c d‖ ^ 2 := by
      simp only [I5, sum_product]
    rw [e5] at h1
    obtain ⟨L', rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
    have hL' : L' + 1 - 1 = L' := by omega
    set q : ℕ → ℕ → ℕ → ℕ → ℝ := fun s b c d => ‖G 0 s b c d‖ ^ 2
    have hin : ∀ b c d, ∑ a ∈ range (L' + 1), ∑ t ∈ range (L' + 1), ‖g' (a + t) b c d‖ ^ 2 ≤
        ((L' + 1 : ℕ) : ℝ) * (∑ s ∈ range L', q s b c d + ∑ s ∈ range L', q (s + (L' + 1)) b c d) := by
      intro b c d
      set h : ℕ → ℝ := fun s => if s = L' ∨ 2 * (L' + 1) - 1 ≤ s then 0 else q s b c d
      have hh : ∀ s, 0 ≤ h s := fun s => by simp only [h]; split_ifs <;> positivity
      have e : ∀ a ∈ range (L' + 1), ∀ t ∈ range (L' + 1), ‖g' (a + t) b c d‖ ^ 2 = h (a + t) := by
        intro a ha t ht
        have ha' := mem_range.1 ha; have ht' := mem_range.1 ht
        simp only [g', h, q, hL']
        by_cases hs : a + t = L'
        · simp [hs]
        · rw [if_neg hs, if_neg (by omega)]
      calc _ = ∑ a ∈ range (L' + 1), ∑ t ∈ range (L' + 1), h (a + t) :=
            sum_congr rfl fun a ha => sum_congr rfl fun t ht => e a ha t ht
        _ ≤ ((L' + 1 : ℕ) : ℝ) * ∑ s ∈ range (2 * (L' + 1)), h s := sum_shift_le h hh (L' + 1)
        _ = _ := by rw [sum_h_eq]
    have hsum : ∑ b ∈ range (L' + 1), ∑ c ∈ range (L' + 1), ∑ d ∈ range (L' + 1),
        ∑ a ∈ range (L' + 1), ∑ t ∈ range (L' + 1), ‖g' (a + t) b c d‖ ^ 2 ≤ ((L' + 1 : ℕ) : ℝ) * XI := by
      calc _ ≤ ∑ b ∈ range (L' + 1), ∑ c ∈ range (L' + 1), ∑ d ∈ range (L' + 1),
            ((L' + 1 : ℕ) : ℝ) * (∑ s ∈ range L', q s b c d + ∑ s ∈ range L', q (s + (L' + 1)) b c d) :=
            sum_le_sum fun b _ => sum_le_sum fun c _ => sum_le_sum fun d _ => hin b c d
        _ = ((L' + 1 : ℕ) : ℝ) * (∑ s ∈ range L', ∑ b ∈ range (L' + 1), ∑ c ∈ range (L' + 1),
              ∑ d ∈ range (L' + 1), q s b c d +
            ∑ s ∈ range L', ∑ b ∈ range (L' + 1), ∑ c ∈ range (L' + 1), ∑ d ∈ range (L' + 1),
              q (s + (L' + 1)) b c d) := by
            rw [← sum_comm4 (range (L' + 1)) (range (L' + 1)) (range (L' + 1)) (range L') (fun b c d s => q s b c d),
              ← sum_comm4 (range (L' + 1)) (range (L' + 1)) (range (L' + 1)) (range L')
                (fun b c d s => q (s + (L' + 1)) b c d)]
            simp only [mul_add, sum_add_distrib, mul_sum]
        _ ≤ ((L' + 1 : ℕ) : ℝ) * XI := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            have hb1 : 0 ≤ ∑ a ∈ range (L' + 1), ∑ b ∈ range (L' + 1 - 1), ∑ c ∈ range (L' + 1),
                ∑ d ∈ range (L' + 1), ‖G 1 a b c d‖ ^ 2 := by positivity
            simp only [XI, Bsum, shG, cub, hL', q]
            have := hb1
            have : 0 ≤ ∑ a ∈ range (L' + 1), ∑ b ∈ range L', ∑ c ∈ range (L' + 1), ∑ d ∈ range (L' + 1),
                ‖G 1 a b c d‖ ^ 2 := by positivity
            have : 0 ≤ ∑ a ∈ range (L' + 1), ∑ b ∈ range (L' + 1), ∑ c ∈ range L', ∑ d ∈ range (L' + 1),
                ‖G 2 a b c d‖ ^ 2 := by positivity
            have : 0 ≤ ∑ a ∈ range (L' + 1), ∑ b ∈ range (L' + 1), ∑ c ∈ range (L' + 1), ∑ d ∈ range L',
                ‖G 3 a b c d‖ ^ 2 := by positivity
            have : 0 ≤ ∑ a ∈ range (L' + 1), ∑ b ∈ range L', ∑ c ∈ range (L' + 1), ∑ d ∈ range (L' + 1),
                ‖G 1 (a + (L' + 1)) b c d‖ ^ 2 := by positivity
            have : 0 ≤ ∑ a ∈ range (L' + 1), ∑ b ∈ range (L' + 1), ∑ c ∈ range L', ∑ d ∈ range (L' + 1),
                ‖G 2 (a + (L' + 1)) b c d‖ ^ 2 := by positivity
            have : 0 ≤ ∑ a ∈ range (L' + 1), ∑ b ∈ range (L' + 1), ∑ c ∈ range (L' + 1), ∑ d ∈ range L',
                ‖G 3 (a + (L' + 1)) b c d‖ ^ 2 := by positivity
            linarith
    calc ‖R‖ ^ 2 ≤ ((L' + 1 : ℕ) : ℝ) ^ 5 * (((L' + 1 : ℕ) : ℝ) * XI) :=
          h1.trans (mul_le_mul_of_nonneg_left hsum (by positivity))
      _ = _ := by ring
  -- the conclusion
  have hXI : 0 ≤ XI := by
    simp only [XI, Bsum]; positivity
  rw [hm]
  refine (sq_sub_le' _ _).trans ?_
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hL0, abs_of_pos (by positivity), mul_pow,
    mul_pow]
  have e : ((((L : ℝ) ^ 4)⁻¹) ^ 2) * ((L : ℝ) ^ 6 * XI) = ((L : ℝ) ^ 2)⁻¹ * XI := by field_simp
  have h2 : (((L : ℝ) ^ 4)⁻¹) ^ 2 * ‖R‖ ^ 2 ≤ ((L : ℝ) ^ 2)⁻¹ * XI := by
    rw [← e]; exact mul_le_mul_of_nonneg_left hR (by positivity)
  linarith

/-- **The crossing bonds of a pair of blocks** (`lem:sf-two-layers`, "Pairs of blocks", with `γ_t⁻¹` replaced by
`64L⁵`): on the box `[0, 2L) × [0, L)³`,
`Σ_{b,c,d<L}‖G_0(L - 1, b, c, d)‖² ≤ 64L⁵(XP + Σ_{bonds inside the blocks}‖G‖² + L²‖QG‖²)`. -/
theorem pair_cross (L : ℕ) (hL : 1 ≤ L) (G : Coch E) :
    ∑ b ∈ range L, ∑ c ∈ range L, ∑ d ∈ range L, ‖G 0 (L - 1) b c d‖ ^ 2 ≤
      64 * (L : ℝ) ^ 5 * (XP L G + (Bsum G (cub L) + Bsum (shG L G) (cub L)) +
        (L : ℝ) ^ 2 * ‖boxMean L (fun a b c d => G 0 a b c d)‖ ^ 2) := by
  have hL0 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  set f : ℕ → ℕ → ℕ → E := fun b c d => G 0 (L - 1) b c d
  set m := mean3 L f
  set XI := Bsum G (cub L) + Bsum (shG L G) (cub L) with hXIdef
  set bm := boxMean L (fun a b c d => G 0 a b c d)
  have hXI : 0 ≤ XI := by simp only [XI, Bsum]; positivity
  have hXP : 0 ≤ XP L G := by unfold XP; positivity
  have h1 : ∑ b ∈ range L, ∑ c ∈ range L, ∑ d ∈ range L, ‖f b c d‖ ^ 2 ≤
      2 * ∑ b ∈ range L, ∑ c ∈ range L, ∑ d ∈ range L, ‖f b c d - m‖ ^ 2 + 2 * (L : ℝ) ^ 3 * ‖m‖ ^ 2 := by
    calc _ ≤ ∑ b ∈ range L, ∑ c ∈ range L, ∑ d ∈ range L, (2 * ‖f b c d - m‖ ^ 2 + 2 * ‖m‖ ^ 2) :=
          sum_le_sum fun b _ => sum_le_sum fun c _ => sum_le_sum fun d _ => by
            have := sq_add_le' (f b c d - m) m
            rwa [sub_add_cancel] at this
      _ = _ := by simp only [sum_add_distrib, mul_sum, sum_const, card_range, nsmul_eq_mul]; ring
  have h2 := cube3_poincare L hL f
  have h3 : D3 L f ≤ 3 * (XP L G + XI) := by
    have := D3_cross_le L hL G; rw [hXIdef]; linarith
  have h4 : ‖m‖ ^ 2 ≤ 2 * (L : ℝ) ^ 2 * ‖bm‖ ^ 2 + 2 * ((L : ℝ) ^ 2)⁻¹ * XI := mean_cross_le L hL G
  have e : (L : ℝ) ^ 3 * ((L : ℝ) ^ 2)⁻¹ = L := by field_simp
  have p2 : (L : ℝ) ^ 2 ≤ (L : ℝ) ^ 5 := pow_le_pow_right₀ hL0 (by norm_num)
  have p1 : (L : ℝ) ≤ (L : ℝ) ^ 5 := by simpa using pow_le_pow_right₀ hL0 (show 1 ≤ 5 by norm_num)
  have hbm : 0 ≤ ‖bm‖ ^ 2 := sq_nonneg _
  have hD : 0 ≤ D3 L f := by unfold D3; positivity
  -- `Σ‖f‖² ≤ 24L²(XP + XI) + 4L⁵‖QG‖² + 4L·XI`
  have k1 : 2 * ∑ b ∈ range L, ∑ c ∈ range L, ∑ d ∈ range L, ‖f b c d - m‖ ^ 2 ≤ 24 * (L : ℝ) ^ 2 * (XP L G + XI) := by
    have := mul_le_mul_of_nonneg_left h3 (show (0 : ℝ) ≤ 4 * (L : ℝ) ^ 2 by positivity)
    nlinarith
  have k2 : 2 * (L : ℝ) ^ 3 * ‖m‖ ^ 2 ≤ 4 * (L : ℝ) ^ 5 * ‖bm‖ ^ 2 + 4 * (L : ℝ) * XI := by
    have := mul_le_mul_of_nonneg_left h4 (show (0 : ℝ) ≤ 2 * (L : ℝ) ^ 3 by positivity)
    calc _ ≤ 2 * (L : ℝ) ^ 3 * (2 * (L : ℝ) ^ 2 * ‖bm‖ ^ 2 + 2 * ((L : ℝ) ^ 2)⁻¹ * XI) := this
      _ = 4 * (L : ℝ) ^ 5 * ‖bm‖ ^ 2 + 4 * ((L : ℝ) ^ 3 * ((L : ℝ) ^ 2)⁻¹) * XI := by ring
      _ = _ := by rw [e]
  have q1 : 24 * (L : ℝ) ^ 2 * (XP L G + XI) ≤ 24 * (L : ℝ) ^ 5 * (XP L G + XI) :=
    mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have q2 : 4 * (L : ℝ) * XI ≤ 4 * (L : ℝ) ^ 5 * XI := mul_le_mul_of_nonneg_right (by linarith) hXI
  have q3 : 4 * (L : ℝ) ^ 5 * ‖bm‖ ^ 2 ≤ 4 * (L : ℝ) ^ 5 * ((L : ℝ) ^ 2 * ‖bm‖ ^ 2) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact le_mul_of_one_le_left hbm (one_le_pow₀ hL0)
  have hL5 : 0 ≤ (L : ℝ) ^ 5 := by positivity
  have hb2 : 0 ≤ (L : ℝ) ^ 2 * ‖bm‖ ^ 2 := by positivity
  nlinarith [mul_nonneg hL5 hXP, mul_nonneg hL5 hXI, mul_nonneg hL5 hb2]

end Cochain
end CoreLean

end
