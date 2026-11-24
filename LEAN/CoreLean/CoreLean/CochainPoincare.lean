/-
A discrete Poincaré inequality for `1`-cochains on a box of `ℤ⁴`, for `lem:sf-two-layers` of BALABAN_CORE.tex
(`a5545dd8c0af`), the steps "The transformation" and "Pairs of blocks" (explicit constants in place of the core's
`C_b` and `γ_t`).

A `1`-cochain is given by its four components `F μ : ℕ → ℕ → ℕ → ℕ → E` (the value on the bond from `(a, b, c, d)` in
the direction `μ`), its circulations by `circ`. With `κ` the sum of `F` along the path from the origin which changes
the coordinates in the order `0, 1, 2, 3` (`kap`), `F - dκ` is a sum of circulations (`kap_step0` … `kap_step3`).
-/
import Mathlib

open Finset

noncomputable section

namespace CoreLean
namespace Cochain

variable {E : Type*} [AddCommGroup E]

/-- A `1`-cochain on `ℕ⁴`: `F μ a b c d` on the bond from `(a, b, c, d)` in the direction `μ`. -/
abbrev Coch (E : Type*) := Fin 4 → ℕ → ℕ → ℕ → ℕ → E

/-- The point `(a, b, c, d)` moved by `e_μ`. -/
def mv (μ : Fin 4) (a b c d : ℕ) : ℕ × ℕ × ℕ × ℕ :=
  (a + if μ = 0 then 1 else 0, b + if μ = 1 then 1 else 0, c + if μ = 2 then 1 else 0, d + if μ = 3 then 1 else 0)

/-- The circulation `F_μ(z) + F_ν(z + e_μ) - F_μ(z + e_ν) - F_ν(z)` of the plaquette at `z` in the plane `(μ, ν)`. -/
def circ (F : Coch E) (μ ν : Fin 4) (a b c d : ℕ) : E :=
  F μ a b c d + F ν (mv μ a b c d).1 (mv μ a b c d).2.1 (mv μ a b c d).2.2.1 (mv μ a b c d).2.2.2 -
    F μ (mv ν a b c d).1 (mv ν a b c d).2.1 (mv ν a b c d).2.2.1 (mv ν a b c d).2.2.2 - F ν a b c d

/-- The integral of `F` along the coordinate path from the origin. -/
def kap (F : Coch E) (a b c d : ℕ) : E :=
  ∑ t ∈ range a, F 0 t 0 0 0 + ∑ t ∈ range b, F 1 a t 0 0 + ∑ t ∈ range c, F 2 a b t 0 + ∑ t ∈ range d, F 3 a b c t

lemma circ01 (F : Coch E) (a b c d : ℕ) :
    circ F 0 1 a b c d = F 0 a b c d + F 1 (a + 1) b c d - F 0 a (b + 1) c d - F 1 a b c d := by
  simp [circ, mv]

lemma circ02 (F : Coch E) (a b c d : ℕ) :
    circ F 0 2 a b c d = F 0 a b c d + F 2 (a + 1) b c d - F 0 a b (c + 1) d - F 2 a b c d := by
  simp [circ, mv]

lemma circ03 (F : Coch E) (a b c d : ℕ) :
    circ F 0 3 a b c d = F 0 a b c d + F 3 (a + 1) b c d - F 0 a b c (d + 1) - F 3 a b c d := by
  simp [circ, mv]

lemma circ12 (F : Coch E) (a b c d : ℕ) :
    circ F 1 2 a b c d = F 1 a b c d + F 2 a (b + 1) c d - F 1 a b (c + 1) d - F 2 a b c d := by
  simp [circ, mv]

lemma circ13 (F : Coch E) (a b c d : ℕ) :
    circ F 1 3 a b c d = F 1 a b c d + F 3 a (b + 1) c d - F 1 a b c (d + 1) - F 3 a b c d := by
  simp [circ, mv]

lemma circ23 (F : Coch E) (a b c d : ℕ) :
    circ F 2 3 a b c d = F 2 a b c d + F 3 a b (c + 1) d - F 2 a b c (d + 1) - F 3 a b c d := by
  simp [circ, mv]

/-- A telescoping sum of circulations. -/
lemma tele (f g : ℕ → E) (h : ℕ → E) (hfg : ∀ t, g t - f t = h (t + 1) - h t) (n : ℕ) :
    ∑ t ∈ range n, g t - ∑ t ∈ range n, f t = h n - h 0 := by
  rw [← sum_sub_distrib, sum_congr rfl fun t _ => hfg t, sum_range_sub]

/-- **The direction `3`**: `κ(z + e₃) - κ(z) = F₃(z)`. -/
lemma kap_step3 (F : Coch E) (a b c d : ℕ) : kap F a b c (d + 1) - kap F a b c d = F 3 a b c d := by
  simp only [kap, sum_range_succ]; abel

/-- **The direction `2`**: `κ(z + e₂) - κ(z) = F₂(z) + Σ_{t<d}circ₂₃(a, b, c, t)`. -/
lemma kap_step2 (F : Coch E) (a b c d : ℕ) :
    kap F a b (c + 1) d - kap F a b c d = F 2 a b c d + ∑ t ∈ range d, circ F 2 3 a b c t := by
  have e : ∀ t, F 3 a b (c + 1) t - F 3 a b c t = circ F 2 3 a b c t + (F 2 a b c (t + 1) - F 2 a b c t) :=
    fun t => by rw [circ23]; abel
  calc kap F a b (c + 1) d - kap F a b c d
      = F 2 a b c 0 + ∑ t ∈ range d, (F 3 a b (c + 1) t - F 3 a b c t) := by
        simp only [kap, sum_range_succ, sum_sub_distrib]; abel
    _ = F 2 a b c 0 + ∑ t ∈ range d, (circ F 2 3 a b c t + (F 2 a b c (t + 1) - F 2 a b c t)) := by
        rw [sum_congr rfl fun t _ => e t]
    _ = _ := by rw [sum_add_distrib, sum_range_sub (fun t => F 2 a b c t)]; abel

/-- **The direction `1`**. -/
lemma kap_step1 (F : Coch E) (a b c d : ℕ) :
    kap F a (b + 1) c d - kap F a b c d =
      F 1 a b c d + ∑ t ∈ range c, circ F 1 2 a b t 0 + ∑ t ∈ range d, circ F 1 3 a b c t := by
  have e2 : ∀ t, F 2 a (b + 1) t 0 - F 2 a b t 0 = circ F 1 2 a b t 0 + (F 1 a b (t + 1) 0 - F 1 a b t 0) :=
    fun t => by rw [circ12]; abel
  have e3 : ∀ t, F 3 a (b + 1) c t - F 3 a b c t = circ F 1 3 a b c t + (F 1 a b c (t + 1) - F 1 a b c t) :=
    fun t => by rw [circ13]; abel
  calc kap F a (b + 1) c d - kap F a b c d
      = F 1 a b 0 0 + ∑ t ∈ range c, (F 2 a (b + 1) t 0 - F 2 a b t 0) +
          ∑ t ∈ range d, (F 3 a (b + 1) c t - F 3 a b c t) := by
        simp only [kap, sum_range_succ, sum_sub_distrib]; abel
    _ = F 1 a b 0 0 + ∑ t ∈ range c, (circ F 1 2 a b t 0 + (F 1 a b (t + 1) 0 - F 1 a b t 0)) +
          ∑ t ∈ range d, (circ F 1 3 a b c t + (F 1 a b c (t + 1) - F 1 a b c t)) := by
        rw [sum_congr rfl fun t _ => e2 t, sum_congr rfl fun t _ => e3 t]
    _ = _ := by
        rw [sum_add_distrib, sum_add_distrib, sum_range_sub (fun t => F 1 a b t 0),
          sum_range_sub (fun t => F 1 a b c t)]
        abel

/-- **The direction `0`**. -/
lemma kap_step0 (F : Coch E) (a b c d : ℕ) :
    kap F (a + 1) b c d - kap F a b c d =
      F 0 a b c d + ∑ t ∈ range b, circ F 0 1 a t 0 0 + ∑ t ∈ range c, circ F 0 2 a b t 0 +
        ∑ t ∈ range d, circ F 0 3 a b c t := by
  have e1 : ∀ t, F 1 (a + 1) t 0 0 - F 1 a t 0 0 = circ F 0 1 a t 0 0 + (F 0 a (t + 1) 0 0 - F 0 a t 0 0) :=
    fun t => by rw [circ01]; abel
  have e2 : ∀ t, F 2 (a + 1) b t 0 - F 2 a b t 0 = circ F 0 2 a b t 0 + (F 0 a b (t + 1) 0 - F 0 a b t 0) :=
    fun t => by rw [circ02]; abel
  have e3 : ∀ t, F 3 (a + 1) b c t - F 3 a b c t = circ F 0 3 a b c t + (F 0 a b c (t + 1) - F 0 a b c t) :=
    fun t => by rw [circ03]; abel
  calc kap F (a + 1) b c d - kap F a b c d
      = F 0 a 0 0 0 + ∑ t ∈ range b, (F 1 (a + 1) t 0 0 - F 1 a t 0 0) +
          ∑ t ∈ range c, (F 2 (a + 1) b t 0 - F 2 a b t 0) + ∑ t ∈ range d, (F 3 (a + 1) b c t - F 3 a b c t) := by
        simp only [kap, sum_range_succ, sum_sub_distrib]; abel
    _ = F 0 a 0 0 0 + ∑ t ∈ range b, (circ F 0 1 a t 0 0 + (F 0 a (t + 1) 0 0 - F 0 a t 0 0)) +
          ∑ t ∈ range c, (circ F 0 2 a b t 0 + (F 0 a b (t + 1) 0 - F 0 a b t 0)) +
          ∑ t ∈ range d, (circ F 0 3 a b c t + (F 0 a b c (t + 1) - F 0 a b c t)) := by
        rw [sum_congr rfl fun t _ => e1 t, sum_congr rfl fun t _ => e2 t, sum_congr rfl fun t _ => e3 t]
    _ = _ := by
        rw [sum_add_distrib, sum_add_distrib, sum_add_distrib, sum_range_sub (fun t => F 0 a t 0 0),
          sum_range_sub (fun t => F 0 a b t 0), sum_range_sub (fun t => F 0 a b c t)]
        abel

section Norm

variable {E : Type*} [NormedAddCommGroup E]

/-- The circulations of the plaquettes in the plane `(μ, ν)` inside the box `ℓ₀ × ℓ₁ × ℓ₂ × ℓ₃`. -/
def plaq (F : Coch E) (ℓ : Fin 4 → ℕ) (μ ν : Fin 4) : ℝ :=
  ∑ a ∈ range (ℓ 0 - if μ = 0 ∨ ν = 0 then 1 else 0), ∑ b ∈ range (ℓ 1 - if μ = 1 ∨ ν = 1 then 1 else 0),
    ∑ c ∈ range (ℓ 2 - if μ = 2 ∨ ν = 2 then 1 else 0), ∑ d ∈ range (ℓ 3 - if μ = 3 ∨ ν = 3 then 1 else 0),
      ‖circ F μ ν a b c d‖ ^ 2

/-- The circulation energy of the box. -/
def Ptot (F : Coch E) (ℓ : Fin 4 → ℕ) : ℝ :=
  plaq F ℓ 0 1 + plaq F ℓ 0 2 + plaq F ℓ 0 3 + plaq F ℓ 1 2 + plaq F ℓ 1 3 + plaq F ℓ 2 3

lemma plaq_nonneg (F : Coch E) (ℓ : Fin 4 → ℕ) (μ ν : Fin 4) : 0 ≤ plaq F ℓ μ ν := by
  unfold plaq; positivity

/-- `‖x + y + z‖² ≤ 3(‖x‖² + ‖y‖² + ‖z‖²)`. -/
lemma norm_add3_sq (x y z : E) : ‖x + y + z‖ ^ 2 ≤ 3 * (‖x‖ ^ 2 + ‖y‖ ^ 2 + ‖z‖ ^ 2) := by
  have h : ‖x + y + z‖ ≤ ‖x‖ + ‖y‖ + ‖z‖ := by
    have h1 := norm_add_le (x + y) z; have h2 := norm_add_le x y; linarith
  have h0 := norm_nonneg (x + y + z)
  have := pow_le_pow_left₀ h0 h 2
  nlinarith [sq_nonneg (‖x‖ - ‖y‖), sq_nonneg (‖x‖ - ‖z‖), sq_nonneg (‖y‖ - ‖z‖)]

/-- `‖Σ_{t<n}x_t‖² ≤ nΣ_{t<n}‖x_t‖²`. -/
lemma norm_sum_sq_le (x : ℕ → E) (n : ℕ) : ‖∑ t ∈ range n, x t‖ ^ 2 ≤ n * ∑ t ∈ range n, ‖x t‖ ^ 2 := by
  have h := sq_sum_le_card_mul_sum_sq (s := range n) (f := fun t => ‖x t‖)
  rw [card_range] at h
  exact (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2).trans h

/-- A sub-sum along a line of the plaquettes of the plane `(0, 3)` (and the like) is at most `plaq`. -/
lemma line_le {f : ℕ → ℕ → ℕ → ℕ → ℝ} (hf : ∀ a b c d, 0 ≤ f a b c d) {m0 m1 m2 m3 a b c : ℕ}
    (ha : a < m0) (hb : b < m1) (hc : c < m2) {n : ℕ} (hn : n ≤ m3) :
    ∑ t ∈ range n, f a b c t ≤ ∑ a' ∈ range m0, ∑ b' ∈ range m1, ∑ c' ∈ range m2, ∑ d' ∈ range m3, f a' b' c' d' := by
  have h1 : ∑ t ∈ range n, f a b c t ≤ ∑ d' ∈ range m3, f a b c d' :=
    sum_le_sum_of_subset_of_nonneg (range_mono hn) fun _ _ _ => hf _ _ _ _
  refine h1.trans ?_
  refine (single_le_sum (f := fun c' => ∑ d' ∈ range m3, f a b c' d') (fun _ _ => sum_nonneg fun _ _ => hf _ _ _ _)
    (mem_range.2 hc)).trans ?_
  refine (single_le_sum (f := fun b' => ∑ c' ∈ range m2, ∑ d' ∈ range m3, f a b' c' d')
    (fun _ _ => sum_nonneg fun _ _ => sum_nonneg fun _ _ => hf _ _ _ _) (mem_range.2 hb)).trans ?_
  exact single_le_sum (f := fun a' => ∑ b' ∈ range m1, ∑ c' ∈ range m2, ∑ d' ∈ range m3, f a' b' c' d')
    (fun _ _ => sum_nonneg fun _ _ => sum_nonneg fun _ _ => sum_nonneg fun _ _ => hf _ _ _ _) (mem_range.2 ha)

end Norm

section Bound

variable {E : Type*} [NormedAddCommGroup E]

lemma line_le_b {f : ℕ → ℕ → ℕ → ℕ → ℝ} (hf : ∀ a b c d, 0 ≤ f a b c d) {m0 m1 m2 m3 a c d n : ℕ}
    (ha : a < m0) (hn : n ≤ m1) (hc : c < m2) (hd : d < m3) :
    ∑ t ∈ range n, f a t c d ≤ ∑ a' ∈ range m0, ∑ b' ∈ range m1, ∑ c' ∈ range m2, ∑ d' ∈ range m3, f a' b' c' d' := by
  have h1 : ∑ t ∈ range n, f a t c d ≤ ∑ b' ∈ range m1, ∑ c' ∈ range m2, ∑ d' ∈ range m3, f a b' c' d' := by
    refine (sum_le_sum_of_subset_of_nonneg (range_mono hn) fun _ _ _ => hf _ _ _ _).trans
      (sum_le_sum fun t _ => ?_)
    refine (single_le_sum (f := fun d' => f a t c d') (fun _ _ => hf _ _ _ _) (mem_range.2 hd)).trans ?_
    exact single_le_sum (f := fun c' => ∑ d' ∈ range m3, f a t c' d') (fun _ _ => sum_nonneg fun _ _ => hf _ _ _ _)
      (mem_range.2 hc)
  refine h1.trans ?_
  exact single_le_sum (f := fun a' => ∑ b' ∈ range m1, ∑ c' ∈ range m2, ∑ d' ∈ range m3, f a' b' c' d')
    (fun _ _ => sum_nonneg fun _ _ => sum_nonneg fun _ _ => sum_nonneg fun _ _ => hf _ _ _ _) (mem_range.2 ha)

lemma line_le_c {f : ℕ → ℕ → ℕ → ℕ → ℝ} (hf : ∀ a b c d, 0 ≤ f a b c d) {m0 m1 m2 m3 a b d n : ℕ}
    (ha : a < m0) (hb : b < m1) (hn : n ≤ m2) (hd : d < m3) :
    ∑ t ∈ range n, f a b t d ≤ ∑ a' ∈ range m0, ∑ b' ∈ range m1, ∑ c' ∈ range m2, ∑ d' ∈ range m3, f a' b' c' d' := by
  have h1 : ∑ t ∈ range n, f a b t d ≤ ∑ c' ∈ range m2, ∑ d' ∈ range m3, f a b c' d' := by
    refine (sum_le_sum_of_subset_of_nonneg (range_mono hn) fun _ _ _ => hf _ _ _ _).trans
      (sum_le_sum fun t _ => ?_)
    exact single_le_sum (f := fun d' => f a b t d') (fun _ _ => hf _ _ _ _) (mem_range.2 hd)
  refine h1.trans ?_
  refine (single_le_sum (f := fun b' => ∑ c' ∈ range m2, ∑ d' ∈ range m3, f a b' c' d')
    (fun _ _ => sum_nonneg fun _ _ => sum_nonneg fun _ _ => hf _ _ _ _) (mem_range.2 hb)).trans ?_
  exact single_le_sum (f := fun a' => ∑ b' ∈ range m1, ∑ c' ∈ range m2, ∑ d' ∈ range m3, f a' b' c' d')
    (fun _ _ => sum_nonneg fun _ _ => sum_nonneg fun _ _ => sum_nonneg fun _ _ => hf _ _ _ _) (mem_range.2 ha)

/-- **The bound of `F - dκ` on a bond of the direction `0`.** -/
lemma bound0 (F : Coch E) (ℓ : Fin 4 → ℕ) {m : ℕ} (hm : ∀ i, ℓ i ≤ m) {a b c d : ℕ}
    (ha : a + 1 < ℓ 0) (hb : b < ℓ 1) (hc : c < ℓ 2) (hd : d < ℓ 3) :
    ‖F 0 a b c d - (kap F (a + 1) b c d - kap F a b c d)‖ ^ 2 ≤ 3 * m * Ptot F ℓ := by
  rw [kap_step0]
  have hf : ∀ (μ ν : Fin 4) a b c d, 0 ≤ ‖circ F μ ν a b c d‖ ^ 2 := fun _ _ _ _ _ _ => sq_nonneg _
  have e : F 0 a b c d - (F 0 a b c d + ∑ t ∈ range b, circ F 0 1 a t 0 0 + ∑ t ∈ range c, circ F 0 2 a b t 0 +
      ∑ t ∈ range d, circ F 0 3 a b c t) = -(∑ t ∈ range b, circ F 0 1 a t 0 0 + ∑ t ∈ range c, circ F 0 2 a b t 0 +
      ∑ t ∈ range d, circ F 0 3 a b c t) := by abel
  rw [e, norm_neg]
  have h1 := line_le_b (hf 0 1) (m0 := ℓ 0 - 1) (m1 := ℓ 1 - 1) (m2 := ℓ 2) (m3 := ℓ 3) (a := a) (c := 0) (d := 0)
    (n := b) (by omega) (by omega) (by omega) (by omega)
  have h2 := line_le_c (hf 0 2) (m0 := ℓ 0 - 1) (m1 := ℓ 1) (m2 := ℓ 2 - 1) (m3 := ℓ 3) (a := a) (b := b) (d := 0)
    (n := c) (by omega) hb (by omega) (by omega)
  have h3 := line_le (hf 0 3) (m0 := ℓ 0 - 1) (m1 := ℓ 1) (m2 := ℓ 2) (m3 := ℓ 3 - 1) (a := a) (b := b) (c := c)
    (n := d) (by omega) hb hc (by omega)
  have p01 : plaq F ℓ 0 1 = ∑ a' ∈ range (ℓ 0 - 1), ∑ b' ∈ range (ℓ 1 - 1), ∑ c' ∈ range (ℓ 2), ∑ d' ∈ range (ℓ 3),
      ‖circ F 0 1 a' b' c' d'‖ ^ 2 := by simp [plaq]
  have p02 : plaq F ℓ 0 2 = ∑ a' ∈ range (ℓ 0 - 1), ∑ b' ∈ range (ℓ 1), ∑ c' ∈ range (ℓ 2 - 1), ∑ d' ∈ range (ℓ 3),
      ‖circ F 0 2 a' b' c' d'‖ ^ 2 := by simp [plaq]
  have p03 : plaq F ℓ 0 3 = ∑ a' ∈ range (ℓ 0 - 1), ∑ b' ∈ range (ℓ 1), ∑ c' ∈ range (ℓ 2), ∑ d' ∈ range (ℓ 3 - 1),
      ‖circ F 0 3 a' b' c' d'‖ ^ 2 := by simp [plaq]
  rw [← p01] at h1; rw [← p02] at h2; rw [← p03] at h3
  have q1 := norm_sum_sq_le (fun t => circ F 0 1 a t 0 0) b
  have q2 := norm_sum_sq_le (fun t => circ F 0 2 a b t 0) c
  have q3 := norm_sum_sq_le (fun t => circ F 0 3 a b c t) d
  have hbm : (b : ℝ) ≤ m := by exact_mod_cast (hb.le.trans (hm 1))
  have hcm : (c : ℝ) ≤ m := by exact_mod_cast (hc.le.trans (hm 2))
  have hdm : (d : ℝ) ≤ m := by exact_mod_cast (hd.le.trans (hm 3))
  have hP := plaq_nonneg F ℓ
  have hS1 : 0 ≤ ∑ t ∈ range b, ‖circ F 0 1 a t 0 0‖ ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  have hS2 : 0 ≤ ∑ t ∈ range c, ‖circ F 0 2 a b t 0‖ ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  have hS3 : 0 ≤ ∑ t ∈ range d, ‖circ F 0 3 a b c t‖ ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  refine (norm_add3_sq _ _ _).trans ?_
  unfold Ptot
  have := hP 1 2; have := hP 1 3; have := hP 2 3
  nlinarith [mul_le_mul hbm h1 hS1 (by positivity), mul_le_mul hcm h2 hS2 (by positivity),
    mul_le_mul hdm h3 hS3 (by positivity)]

lemma bound1 (F : Coch E) (ℓ : Fin 4 → ℕ) {m : ℕ} (hm : ∀ i, ℓ i ≤ m) {a b c d : ℕ}
    (ha : a < ℓ 0) (hb : b + 1 < ℓ 1) (hc : c < ℓ 2) (hd : d < ℓ 3) :
    ‖F 1 a b c d - (kap F a (b + 1) c d - kap F a b c d)‖ ^ 2 ≤ 3 * m * Ptot F ℓ := by
  rw [kap_step1]
  have hf : ∀ (μ ν : Fin 4) a b c d, 0 ≤ ‖circ F μ ν a b c d‖ ^ 2 := fun _ _ _ _ _ _ => sq_nonneg _
  have e : F 1 a b c d - (F 1 a b c d + ∑ t ∈ range c, circ F 1 2 a b t 0 + ∑ t ∈ range d, circ F 1 3 a b c t) =
      -(0 + ∑ t ∈ range c, circ F 1 2 a b t 0 + ∑ t ∈ range d, circ F 1 3 a b c t) := by abel
  rw [e, norm_neg]
  have h2 := line_le_c (hf 1 2) (m0 := ℓ 0) (m1 := ℓ 1 - 1) (m2 := ℓ 2 - 1) (m3 := ℓ 3) (a := a) (b := b) (d := 0)
    (n := c) ha (by omega) (by omega) (by omega)
  have h3 := line_le (hf 1 3) (m0 := ℓ 0) (m1 := ℓ 1 - 1) (m2 := ℓ 2) (m3 := ℓ 3 - 1) (a := a) (b := b) (c := c)
    (n := d) ha (by omega) hc (by omega)
  have p12 : plaq F ℓ 1 2 = ∑ a' ∈ range (ℓ 0), ∑ b' ∈ range (ℓ 1 - 1), ∑ c' ∈ range (ℓ 2 - 1), ∑ d' ∈ range (ℓ 3),
      ‖circ F 1 2 a' b' c' d'‖ ^ 2 := by simp [plaq]
  have p13 : plaq F ℓ 1 3 = ∑ a' ∈ range (ℓ 0), ∑ b' ∈ range (ℓ 1 - 1), ∑ c' ∈ range (ℓ 2), ∑ d' ∈ range (ℓ 3 - 1),
      ‖circ F 1 3 a' b' c' d'‖ ^ 2 := by simp [plaq]
  rw [← p12] at h2; rw [← p13] at h3
  have q2 := norm_sum_sq_le (fun t => circ F 1 2 a b t 0) c
  have q3 := norm_sum_sq_le (fun t => circ F 1 3 a b c t) d
  have hcm : (c : ℝ) ≤ m := by exact_mod_cast (hc.le.trans (hm 2))
  have hdm : (d : ℝ) ≤ m := by exact_mod_cast (hd.le.trans (hm 3))
  have hP := plaq_nonneg F ℓ
  have hS2 : 0 ≤ ∑ t ∈ range c, ‖circ F 1 2 a b t 0‖ ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  have hS3 : 0 ≤ ∑ t ∈ range d, ‖circ F 1 3 a b c t‖ ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  refine (norm_add3_sq _ _ _).trans ?_
  unfold Ptot
  have := hP 0 1; have := hP 0 2; have := hP 0 3; have := hP 2 3
  simp only [norm_zero]
  nlinarith [mul_le_mul hcm h2 hS2 (by positivity), mul_le_mul hdm h3 hS3 (by positivity)]

lemma bound2 (F : Coch E) (ℓ : Fin 4 → ℕ) {m : ℕ} (hm : ∀ i, ℓ i ≤ m) {a b c d : ℕ}
    (ha : a < ℓ 0) (hb : b < ℓ 1) (hc : c + 1 < ℓ 2) (hd : d < ℓ 3) :
    ‖F 2 a b c d - (kap F a b (c + 1) d - kap F a b c d)‖ ^ 2 ≤ 3 * m * Ptot F ℓ := by
  rw [kap_step2]
  have hf : ∀ (μ ν : Fin 4) a b c d, 0 ≤ ‖circ F μ ν a b c d‖ ^ 2 := fun _ _ _ _ _ _ => sq_nonneg _
  have e : F 2 a b c d - (F 2 a b c d + ∑ t ∈ range d, circ F 2 3 a b c t) = -(∑ t ∈ range d, circ F 2 3 a b c t) := by
    abel
  rw [e, norm_neg]
  have h3 := line_le (hf 2 3) (m0 := ℓ 0) (m1 := ℓ 1) (m2 := ℓ 2 - 1) (m3 := ℓ 3 - 1) (a := a) (b := b) (c := c)
    (n := d) ha hb (by omega) (by omega)
  have p23 : plaq F ℓ 2 3 = ∑ a' ∈ range (ℓ 0), ∑ b' ∈ range (ℓ 1), ∑ c' ∈ range (ℓ 2 - 1), ∑ d' ∈ range (ℓ 3 - 1),
      ‖circ F 2 3 a' b' c' d'‖ ^ 2 := by simp [plaq]
  rw [← p23] at h3
  have q3 := norm_sum_sq_le (fun t => circ F 2 3 a b c t) d
  have hdm : (d : ℝ) ≤ m := by exact_mod_cast (hd.le.trans (hm 3))
  have hP := plaq_nonneg F ℓ
  have hS3 : 0 ≤ ∑ t ∈ range d, ‖circ F 2 3 a b c t‖ ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  unfold Ptot
  have := hP 0 1; have := hP 0 2; have := hP 0 3; have := hP 1 2; have := hP 1 3
  have hm0 : (0 : ℝ) ≤ m := by positivity
  nlinarith [mul_le_mul hdm h3 hS3 (by positivity)]

lemma bound3 (F : Coch E) (a b c d : ℕ) : F 3 a b c d - (kap F a b c (d + 1) - kap F a b c d) = 0 := by
  rw [kap_step3, sub_self]

/-- `F - dκ`, in the directions. -/
def Fh (F : Coch E) : Coch E := fun μ a b c d =>
  F μ a b c d - (kap F (a + if μ = 0 then 1 else 0) (b + if μ = 1 then 1 else 0) (c + if μ = 2 then 1 else 0)
    (d + if μ = 3 then 1 else 0) - kap F a b c d)

/-- The sum of `‖G‖²` over the bonds of the box. -/
def Bsum (G : Coch E) (ℓ : Fin 4 → ℕ) : ℝ :=
  ∑ a ∈ range (ℓ 0 - 1), ∑ b ∈ range (ℓ 1), ∑ c ∈ range (ℓ 2), ∑ d ∈ range (ℓ 3), ‖G 0 a b c d‖ ^ 2 +
  ∑ a ∈ range (ℓ 0), ∑ b ∈ range (ℓ 1 - 1), ∑ c ∈ range (ℓ 2), ∑ d ∈ range (ℓ 3), ‖G 1 a b c d‖ ^ 2 +
  ∑ a ∈ range (ℓ 0), ∑ b ∈ range (ℓ 1), ∑ c ∈ range (ℓ 2 - 1), ∑ d ∈ range (ℓ 3), ‖G 2 a b c d‖ ^ 2 +
  ∑ a ∈ range (ℓ 0), ∑ b ∈ range (ℓ 1), ∑ c ∈ range (ℓ 2), ∑ d ∈ range (ℓ 3 - 1), ‖G 3 a b c d‖ ^ 2

lemma sum4_le_const {m0 m1 m2 m3 : ℕ} (f : ℕ → ℕ → ℕ → ℕ → ℝ) {B : ℝ}
    (hf : ∀ a < m0, ∀ b < m1, ∀ c < m2, ∀ d < m3, f a b c d ≤ B) :
    ∑ a ∈ range m0, ∑ b ∈ range m1, ∑ c ∈ range m2, ∑ d ∈ range m3, f a b c d ≤ m0 * m1 * m2 * m3 * B := by
  calc _ ≤ ∑ a ∈ range m0, ∑ b ∈ range m1, ∑ c ∈ range m2, ∑ d ∈ range m3, B :=
        sum_le_sum fun a ha => sum_le_sum fun b hb => sum_le_sum fun c hc => sum_le_sum fun d hd =>
          hf a (mem_range.1 ha) b (mem_range.1 hb) c (mem_range.1 hc) d (mem_range.1 hd)
    _ = _ := by simp [sum_const, card_range]; ring

/-- **The discrete Poincaré inequality for `1`-cochains**: `Σ_{bonds}‖F - dκ‖² ≤ 12mℓ₀ℓ₁ℓ₂ℓ₃Σ_{plaquettes}‖∂F‖²`,
`m ≥ ℓ_i`. -/
theorem poincare_box (F : Coch E) (ℓ : Fin 4 → ℕ) {m : ℕ} (hm : ∀ i, ℓ i ≤ m) :
    Bsum (Fh F) ℓ ≤ 12 * m * (ℓ 0 * ℓ 1 * ℓ 2 * ℓ 3) * Ptot F ℓ := by
  have hP : 0 ≤ Ptot F ℓ := by
    have := plaq_nonneg F ℓ
    unfold Ptot; linarith [this 0 1, this 0 2, this 0 3, this 1 2, this 1 3, this 2 3]
  have hB : 0 ≤ 3 * (m : ℝ) * Ptot F ℓ := by positivity
  unfold Bsum
  have t0 := sum4_le_const (m0 := ℓ 0 - 1) (m1 := ℓ 1) (m2 := ℓ 2) (m3 := ℓ 3) (fun a b c d => ‖Fh F 0 a b c d‖ ^ 2)
    (B := 3 * m * Ptot F ℓ) fun a ha b hb c hc d hd => by
      simp only [Fh]; simpa using bound0 F ℓ hm (by omega) hb hc hd
  have t1 := sum4_le_const (m0 := ℓ 0) (m1 := ℓ 1 - 1) (m2 := ℓ 2) (m3 := ℓ 3) (fun a b c d => ‖Fh F 1 a b c d‖ ^ 2)
    (B := 3 * m * Ptot F ℓ) fun a ha b hb c hc d hd => by
      simp only [Fh]; simpa using bound1 F ℓ hm ha (by omega) hc hd
  have t2 := sum4_le_const (m0 := ℓ 0) (m1 := ℓ 1) (m2 := ℓ 2 - 1) (m3 := ℓ 3) (fun a b c d => ‖Fh F 2 a b c d‖ ^ 2)
    (B := 3 * m * Ptot F ℓ) fun a ha b hb c hc d hd => by
      simp only [Fh]; simpa using bound2 F ℓ hm ha hb (by omega) hd
  have t3 := sum4_le_const (m0 := ℓ 0) (m1 := ℓ 1) (m2 := ℓ 2) (m3 := ℓ 3 - 1) (fun a b c d => ‖Fh F 3 a b c d‖ ^ 2)
    (B := 3 * m * Ptot F ℓ) fun a ha b hb c hc d hd => by
      simp only [Fh]; simp [bound3 F a b c d]; positivity
  have c0 : ((ℓ 0 - 1 : ℕ) : ℝ) ≤ ℓ 0 := by exact_mod_cast Nat.sub_le _ _
  have c1 : ((ℓ 1 - 1 : ℕ) : ℝ) ≤ ℓ 1 := by exact_mod_cast Nat.sub_le _ _
  have c2 : ((ℓ 2 - 1 : ℕ) : ℝ) ≤ ℓ 2 := by exact_mod_cast Nat.sub_le _ _
  have c3 : ((ℓ 3 - 1 : ℕ) : ℝ) ≤ ℓ 3 := by exact_mod_cast Nat.sub_le _ _
  have hl : ∀ i, (0 : ℝ) ≤ ℓ i := fun i => by positivity
  have k : ∀ x : ℝ, 0 ≤ x → x ≤ ℓ 0 → ∀ y : ℝ, 0 ≤ y → y ≤ ℓ 1 → ∀ z : ℝ, 0 ≤ z → z ≤ ℓ 2 → ∀ w : ℝ, 0 ≤ w →
      w ≤ ℓ 3 → x * y * z * w * (3 * m * Ptot F ℓ) ≤ ℓ 0 * ℓ 1 * ℓ 2 * ℓ 3 * (3 * m * Ptot F ℓ) := by
    intro x hx hx' y hy hy' z hz hz' w hw hw'
    apply mul_le_mul_of_nonneg_right _ hB
    exact mul_le_mul (mul_le_mul (mul_le_mul hx' hy' hy (hl 0)) hz' hz (by positivity)) hw' hw (by positivity)
  have u0 := k _ (by positivity) c0 _ (hl 1) le_rfl _ (hl 2) le_rfl _ (hl 3) le_rfl
  have u1 := k _ (hl 0) le_rfl _ (by positivity) c1 _ (hl 2) le_rfl _ (hl 3) le_rfl
  have u2 := k _ (hl 0) le_rfl _ (hl 1) le_rfl _ (by positivity) c2 _ (hl 3) le_rfl
  have u3 := k _ (hl 0) le_rfl _ (hl 1) le_rfl _ (hl 2) le_rfl _ (by positivity) c3
  linarith

end Bound

end Cochain
end CoreLean

end
