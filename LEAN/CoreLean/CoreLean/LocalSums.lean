/-
`lem:local-laplacian` of BALABAN_CORE.tex (`0580551bf179`): sums over the boxes `Q_ρ`, and the identity of the proof of
(iv), `Σ_{κ,ν}Σ_zε⁴‖∂_κ∂_νf(z)‖² = Σ_zε⁴‖Δf(z)‖²` for a function which vanishes outside a finite set.

A sum over `εℤ⁴` of a function which vanishes outside `Q_ρ` is the sum over the finite set `QF ρ'` for any `ρ' ≥ ρ`;
the shifts by `εe_μ` are handled by `sum_shift_QF`.

* `QF ε n₀ ρ`: the points of `Q_ρ` as a finite set (`mem_QF`).
* `SuppIn ρ f`: `f` vanishes outside `Q_ρ`; `SuppIn.dfw`, `SuppIn.dbw`: the differences vanish outside `Q_{ρ+ε}`.
* `sum_shift_QF`: `Σ_{z ∈ Q_{ρ'}}F(z + e) = Σ_{z ∈ Q_{ρ'}}F(z)` for `F` vanishing outside `Q_ρ`, `ρ + ε ≤ ρ'`, `e ∈ E`.
* `sbp`: the summation by parts `Σ_z(∂_κa(z), b(z)) = Σ_z(a(z), ∂^*_κb(z))`.
* `sum_dd_eq_lap`: the identity above.
-/
import CoreLean.LocalData

open Finset
open scoped RealInnerProductSpace Classical

noncomputable section

namespace CoreLean
namespace LocalLaplacian

variable {ε : ℝ} {n₀ : Fin 4 → ℤ}

/-- The points of `Q_ρ`. -/
def QF (ε : ℝ) (n₀ : Fin 4 → ℤ) (ρ : ℝ) : Finset (Fin 4 → ℤ) :=
  (Fintype.piFinset fun μ => Icc (n₀ μ - ⌈ρ / ε⌉₊) (n₀ μ + ⌈ρ / ε⌉₊)).filter (InQr ε n₀ ρ)

lemma mem_QF (hε : 0 < ε) {ρ : ℝ} {n : Fin 4 → ℤ} : n ∈ QF ε n₀ ρ ↔ InQr ε n₀ ρ n := by
  unfold QF
  rw [mem_filter, and_iff_right_iff_imp]
  intro h
  refine Fintype.mem_piFinset.2 fun μ => ?_
  have h1 := h μ
  unfold tc at h1
  rw [abs_mul, abs_of_pos hε] at h1
  have h2 : |((n μ - n₀ μ : ℤ) : ℝ)| ≤ (⌈ρ / ε⌉₊ : ℝ) :=
    (by rw [le_div_iff₀ hε]; linarith : |((n μ - n₀ μ : ℤ) : ℝ)| ≤ ρ / ε).trans (Nat.le_ceil _)
  have h3 : |n μ - n₀ μ| ≤ (⌈ρ / ε⌉₊ : ℤ) := by exact_mod_cast h2
  rw [mem_Icc]; constructor <;> linarith [abs_le.1 h3]

/-- `f` vanishes outside `Q_ρ`. -/
def SuppIn {M : Type*} [Zero M] (ε : ℝ) (n₀ : Fin 4 → ℤ) (ρ : ℝ) (f : (Fin 4 → ℤ) → M) : Prop :=
  ∀ z, f z ≠ 0 → InQr ε n₀ ρ z

lemma neg_mem_Eoff {e : Fin 4 → ℤ} (he : e ∈ Eoff) : -e ∈ Eoff := Fintype.mem_piFinset.2 fun μ => by
  have := Fintype.mem_piFinset.1 he μ
  rw [mem_Icc] at this ⊢; simp only [Pi.neg_apply]; constructor <;> linarith [this.1, this.2]

lemma e4_mem (μ : Fin 4) : e4 μ ∈ Eoff := Fintype.mem_piFinset.2 fun ν => by
  by_cases h : ν = μ
  · subst h; simp [e4]
  · simp [e4, Pi.single_eq_of_ne h]

lemma inQ_shift (hε : 0 < ε) {ρ : ℝ} {z e : Fin 4 → ℤ} (he : e ∈ Eoff) (h : InQr ε n₀ ρ (z + e)) :
    InQr ε n₀ (ρ + ε) z := fun ν => by
  have h1 := tc_add_off (n₀ := n₀) hε (neg_mem_Eoff he) (z + e) ν
  rw [add_neg_cancel_right] at h1
  have := h ν; linarith

lemma inQ_sub (hε : 0 < ε) {ρ : ℝ} {z e : Fin 4 → ℤ} (he : e ∈ Eoff) (h : InQr ε n₀ ρ z) :
    InQr ε n₀ (ρ + ε) (z - e) := fun ν => by
  have h1 := tc_add_off (n₀ := n₀) hε (neg_mem_Eoff he) z ν
  rw [← sub_eq_add_neg] at h1
  have := h ν; linarith

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma SuppIn.mono {ρ ρ' : ℝ} {f : (Fin 4 → ℤ) → V} (h : SuppIn ε n₀ ρ f) (hρ : ρ ≤ ρ') : SuppIn ε n₀ ρ' f :=
  fun z hz ν => (h z hz ν).trans hρ

lemma SuppIn.dfw (hε : 0 < ε) {ρ : ℝ} {f : (Fin 4 → ℤ) → V} (h : SuppIn ε n₀ ρ f) (μ : Fin 4) :
    SuppIn ε n₀ (ρ + ε) (dfw ε μ f) := fun z hz => by
  by_cases h0 : f z = 0
  · have h1 : f (z + e4 μ) ≠ 0 := by intro h1; apply hz; unfold CoreLean.dfw; rw [h0, h1]; simp
    exact inQ_shift hε (e4_mem μ) (h _ h1)
  · exact fun ν => (h z h0 ν).trans (by linarith)

lemma SuppIn.dbw (hε : 0 < ε) {ρ : ℝ} {f : (Fin 4 → ℤ) → V} (h : SuppIn ε n₀ ρ f) (μ : Fin 4) :
    SuppIn ε n₀ (ρ + ε) (dbw ε μ f) := fun z hz => by
  by_cases h0 : f z = 0
  · have h1 : f (z + -e4 μ) ≠ 0 := by
      intro h1; apply hz; unfold CoreLean.dbw; rw [h0, sub_eq_add_neg z, h1]; simp
    exact inQ_shift hε (neg_e4_mem μ) (h _ h1)
  · exact fun ν => (h z h0 ν).trans (by linarith)
where
  neg_e4_mem (μ : Fin 4) : -e4 μ ∈ Eoff := neg_mem_Eoff (e4_mem μ)

/-- Sums over two finite sets which contain the support agree. -/
lemma sum_eq_of_supp {M : Type*} [AddCommMonoid M] {F : (Fin 4 → ℤ) → M} {A B : Finset (Fin 4 → ℤ)}
    (hA : ∀ z, F z ≠ 0 → z ∈ A) (hB : ∀ z, F z ≠ 0 → z ∈ B) : ∑ z ∈ A, F z = ∑ z ∈ B, F z := by
  rw [← sum_subset (inter_subset_left (s₁ := A) (s₂ := B)) fun z hz hz' => by
      by_contra h; exact hz' (mem_inter.2 ⟨hz, hB z h⟩),
    ← sum_subset (inter_subset_right (s₁ := A) (s₂ := B)) fun z hz hz' => by
      by_contra h; exact hz' (mem_inter.2 ⟨hA z h, hz⟩)]

/-- **The shift**: `Σ_{z ∈ Q_{ρ'}}F(z + e) = Σ_{z ∈ Q_{ρ'}}F(z)`. -/
lemma sum_shift_QF {M : Type*} [AddCommMonoid M] (hε : 0 < ε) {ρ ρ' : ℝ} (hρ : ρ + ε ≤ ρ')
    {F : (Fin 4 → ℤ) → M} (hF : ∀ z, F z ≠ 0 → InQr ε n₀ ρ z) {e : Fin 4 → ℤ} (he : e ∈ Eoff) :
    ∑ z ∈ QF ε n₀ ρ', F (z + e) = ∑ z ∈ QF ε n₀ ρ', F z := by
  have e1 : ∑ z ∈ QF ε n₀ ρ', F (z + e) = ∑ w ∈ (QF ε n₀ ρ').map (addRightEmbedding e), F w := by
    rw [sum_map]; rfl
  rw [e1]
  refine sum_eq_of_supp (fun w hw => ?_) (fun w hw => ?_)
  · rw [mem_map]
    refine ⟨w - e, (mem_QF hε).2 fun ν => ((inQ_sub hε he (hF w hw)) ν).trans (by linarith), by simp⟩
  · exact (mem_QF hε).2 fun ν => ((hF w hw) ν).trans (by linarith)

/-! ### Summation by parts -/

section Inner

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]

/-- **Summation by parts**: `Σ_z⟨∂_κa(z), b(z)⟩ = Σ_z⟨a(z), ∂^*_κb(z)⟩` for `a` vanishing outside `Q_ρ`,
`ρ + ε ≤ ρ'`. -/
lemma sbp (hε : 0 < ε) {ρ ρ' : ℝ} (hρ : ρ + ε ≤ ρ') {a b : (Fin 4 → ℤ) → W} (ha : SuppIn ε n₀ ρ a)
    (hb : SuppIn ε n₀ ρ b) (κ : Fin 4) :
    ∑ z ∈ QF ε n₀ ρ', ⟪dfw ε κ a z, b z⟫ = ∑ z ∈ QF ε n₀ ρ', ⟪a z, dbw ε κ b z⟫ := by
  have hG : ∀ z, ⟪a z, b (z - e4 κ)⟫ ≠ 0 → InQr ε n₀ ρ z := fun z hz =>
    ha z fun h => hz (by rw [h, inner_zero_left])
  have hshift := sum_shift_QF hε hρ hG (e4_mem κ)
  simp only [add_sub_cancel_right] at hshift
  simp only [dfw, dbw, inner_smul_left, inner_smul_right, inner_sub_left, inner_sub_right, RCLike.conj_to_real,
    ← mul_sum, sum_sub_distrib, hshift]

/-- The mirrored summation by parts: `Σ_z⟨x(z), ∂_νy(z)⟩ = Σ_z⟨∂^*_νx(z), y(z)⟩`. -/
lemma sbp' (hε : 0 < ε) {ρ ρ' : ℝ} (hρ : ρ + ε ≤ ρ') {x y : (Fin 4 → ℤ) → W} (hx : SuppIn ε n₀ ρ x)
    (hy : SuppIn ε n₀ ρ y) (ν : Fin 4) :
    ∑ z ∈ QF ε n₀ ρ', ⟪x z, dfw ε ν y z⟫ = ∑ z ∈ QF ε n₀ ρ', ⟪dbw ε ν x z, y z⟫ := by
  calc ∑ z ∈ QF ε n₀ ρ', ⟪x z, dfw ε ν y z⟫ = ∑ z ∈ QF ε n₀ ρ', ⟪dfw ε ν y z, x z⟫ :=
        sum_congr rfl fun z _ => real_inner_comm _ _
    _ = ∑ z ∈ QF ε n₀ ρ', ⟪y z, dbw ε ν x z⟫ := sbp hε hρ hy hx ν
    _ = ∑ z ∈ QF ε n₀ ρ', ⟪dbw ε ν x z, y z⟫ := sum_congr rfl fun z _ => real_inner_comm _ _

lemma dfw_dbw_dfw (f : (Fin 4 → ℤ) → W) (κ ν : Fin 4) (z : Fin 4 → ℤ) :
    dbw ε κ (dfw ε κ (dfw ε ν f)) z = dfw ε ν (dbw ε κ (dfw ε κ f)) z := by
  simp only [dfw, dbw]
  rw [show z - e4 κ + e4 κ + e4 ν = z + e4 ν by abel, show z - e4 κ + e4 ν = z + e4 ν - e4 κ by abel,
    show z + e4 κ + e4 ν = z + e4 ν + e4 κ by abel, show z - e4 κ + e4 κ = z by abel,
    show z + e4 ν - e4 κ + e4 κ = z + e4 ν by abel]
  module

/-- **The identity of (iv)**: `Σ_{κ,ν}Σ_z‖∂_κ∂_νf(z)‖² = Σ_z‖Δf(z)‖²`. -/
theorem sum_dd_eq_lap (hε : 0 < ε) {ρ ρ' : ℝ} (hρ : ρ + 3 * ε ≤ ρ') {f : (Fin 4 → ℤ) → W}
    (hf : SuppIn ε n₀ ρ f) :
    ∑ κ, ∑ ν, ∑ z ∈ QF ε n₀ ρ', ‖dfw ε κ (dfw ε ν f) z‖ ^ 2 = ∑ z ∈ QF ε n₀ ρ', ‖lap ε f z‖ ^ 2 := by
  have h1 : ∀ ν, SuppIn ε n₀ (ρ + 2 * ε) (dfw ε ν f) := fun ν => (hf.dfw hε ν).mono (by linarith)
  have h2 : ∀ κ ν, SuppIn ε n₀ (ρ + 2 * ε) (dfw ε κ (dfw ε ν f)) := fun κ ν =>
    by have := (hf.dfw hε ν).dfw hε κ; exact this.mono (by linarith)
  have h3 : ∀ κ, SuppIn ε n₀ (ρ + 2 * ε) (dbw ε κ (dfw ε κ f)) := fun κ =>
    by have := (hf.dfw hε κ).dbw hε κ; exact this.mono (by linarith)
  have step : ∀ κ ν, ∑ z ∈ QF ε n₀ ρ', ‖dfw ε κ (dfw ε ν f) z‖ ^ 2 =
      ∑ z ∈ QF ε n₀ ρ', ⟪dbw ε ν (dfw ε ν f) z, dbw ε κ (dfw ε κ f) z⟫ := fun κ ν => by
    simp only [← real_inner_self_eq_norm_sq]
    rw [sbp hε (by linarith) (h1 ν) (h2 κ ν) κ]
    simp only [dfw_dbw_dfw]
    exact sbp' hε (by linarith) (h1 ν) (h3 κ) ν
  rw [sum_congr rfl fun κ _ => sum_congr rfl fun ν _ => step κ ν,
    sum_congr rfl fun z _ => (real_inner_self_eq_norm_sq (lap ε f z)).symm]
  simp only [lap, sum_inner, inner_sum]
  calc ∑ κ, ∑ ν, ∑ z ∈ QF ε n₀ ρ', ⟪dbw ε ν (dfw ε ν f) z, dbw ε κ (dfw ε κ f) z⟫
      = ∑ ν, ∑ κ, ∑ z ∈ QF ε n₀ ρ', ⟪dbw ε ν (dfw ε ν f) z, dbw ε κ (dfw ε κ f) z⟫ := sum_comm
    _ = ∑ ν, ∑ z ∈ QF ε n₀ ρ', ∑ κ, ⟪dbw ε ν (dfw ε ν f) z, dbw ε κ (dfw ε κ f) z⟫ :=
        sum_congr rfl fun ν _ => sum_comm
    _ = ∑ z ∈ QF ε n₀ ρ', ∑ ν, ∑ κ, ⟪dbw ε ν (dfw ε ν f) z, dbw ε κ (dfw ε κ f) z⟫ := sum_comm
    _ = ∑ z ∈ QF ε n₀ ρ', ∑ κ, ∑ ν, ⟪dbw ε ν (dfw ε ν f) z, dbw ε κ (dfw ε κ f) z⟫ :=
        sum_congr rfl fun z _ => sum_comm

end Inner

end LocalLaplacian
end CoreLean

end
