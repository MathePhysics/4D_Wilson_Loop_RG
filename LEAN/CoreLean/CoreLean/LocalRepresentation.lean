/-
`lem:local-laplacian` of BALABAN_CORE.tex (`0580551bf179`), the step "The localised equation": the identities
`eq:local-leibniz`, `eq:local-commutator`, `eq:local-localised`, and the representation `eq:local-representation`
`χu = G₁F₀ + Σ_μ∂^*_μG₁F_μ - Σ_μ∂_μG₁(ψ_μu)`.

The functions are defined on all of `εℤ⁴` (the core extends `u`, `h`, `g_μ` by zero outside `Q_R`; the identities
below use their values at the points of `Q_{r+1}` only, and hold for every extension). A local operator is given by its
coefficients `T n e`, `e ∈ E = {|e|_∞ ≤ 1}` (`locApp`); its norm condition enters only the bounds, not the identities.

* `lap_dfw`, `lap_dbw`, `lap_add`, `lap_sum`: `Δ` commutes with the differences and is additive.
* `commutator`: `eq:local-commutator`; `leibniz_dbw`: `χ∂^*_μv = ∂^*_μ(χ(· + εe_μ)v) + (∂_μχ)v`.
* `localised`: `eq:local-localised`, `(Δ + 1)(χu) = F₀ + Σ_μ∂^*_μF_μ - Σ_μ∂_μ(ψ_μu)` on all of `εℤ⁴`, from the equation
  `eq:local-equation` at the points of `Q_{R-2/3}`.
* `bounded_of_supp`: a function which vanishes outside a box is bounded; `representation`: `eq:local-representation`.
-/
import CoreLean.LocalCutoff
import CoreLean.ResolventEquation

open Finset

noncomputable section

namespace CoreLean
namespace LocalLaplacian

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/-- The offsets `E = {e | |e|_∞ ≤ 1}` (in the units of the lattice). -/
def Eoff : Finset (Fin 4 → ℤ) := Fintype.piFinset fun _ => Icc (-1) 1

/-- A local operator: `(Tf)(n) = Σ_{e ∈ E} T_e(n)f(n + e)`. -/
def locApp (T : (Fin 4 → ℤ) → (Fin 4 → ℤ) → (V →L[ℝ] V)) (f : (Fin 4 → ℤ) → V) (n : Fin 4 → ℤ) : V :=
  ∑ e ∈ Eoff, T n e (f (n + e))

variable {ε : ℝ}

/-! ### The Laplacian -/

lemma lap_dfw (f : (Fin 4 → ℤ) → V) (μ : Fin 4) (n : Fin 4 → ℤ) :
    lap ε (dfw ε μ f) n = dfw ε μ (lap ε f) n := by
  simp only [lap_eq, dfw, ← smul_sub, ← sum_sub_distrib, smul_sum]
  refine sum_congr rfl fun ν _ => ?_
  rw [show n + e4 ν + e4 μ = n + e4 μ + e4 ν by abel, show n - e4 ν + e4 μ = n + e4 μ - e4 ν by abel]
  module

lemma lap_dbw (f : (Fin 4 → ℤ) → V) (μ : Fin 4) (n : Fin 4 → ℤ) :
    lap ε (dbw ε μ f) n = dbw ε μ (lap ε f) n := by
  simp only [lap_eq, dbw, ← smul_sub, ← sum_sub_distrib, smul_sum]
  refine sum_congr rfl fun ν _ => ?_
  rw [show n + e4 ν - e4 μ = n - e4 μ + e4 ν by abel, show n - e4 ν - e4 μ = n - e4 μ - e4 ν by abel]
  module

lemma lap_add (f g : (Fin 4 → ℤ) → V) (n : Fin 4 → ℤ) :
    lap ε (fun m => f m + g m) n = lap ε f n + lap ε g n := by
  simp only [lap_eq, ← smul_add, ← sum_add_distrib]
  congr 1
  refine sum_congr rfl fun ν _ => ?_
  module

lemma lap_sum (f : Fin 4 → (Fin 4 → ℤ) → V) (n : Fin 4 → ℤ) :
    lap ε (fun m => ∑ μ, f μ m) n = ∑ μ, lap ε (f μ) n := by
  simp only [lap_eq, ← smul_sum]
  congr 1
  rw [sum_comm]
  refine sum_congr rfl fun ν _ => ?_
  simp only [smul_sum, ← sum_sub_distrib]

lemma dbw_add (f g : (Fin 4 → ℤ) → V) (μ : Fin 4) (n : Fin 4 → ℤ) :
    dbw ε μ (fun m => f m + g m) n = dbw ε μ f n + dbw ε μ g n := by
  simp only [dbw]; module

lemma dfw_add (f g : (Fin 4 → ℤ) → V) (μ : Fin 4) (n : Fin 4 → ℤ) :
    dfw ε μ (fun m => f m + g m) n = dfw ε μ f n + dfw ε μ g n := by
  simp only [dfw]; module

/-! ### The identities of Leibniz -/

variable {r : ℝ} {n₀ : Fin 4 → ℤ}

/-- `eq:local-commutator`, the term of one direction. -/
lemma commutator_term (χ : (Fin 4 → ℤ) → ℝ) (u : (Fin 4 → ℤ) → V) (μ : Fin 4) (n : Fin 4 → ℤ) :
    dbw ε μ (dfw ε μ fun m => χ m • u m) n = χ n • dbw ε μ (dfw ε μ u) n +
      (dbw ε μ (fun m => dfw ε μ χ m • u m) n - dfw ε μ (fun m => dfw ε μ χ (m - e4 μ) • u m) n -
        dbw ε μ (dfw ε μ χ) n • u n) := by
  simp only [dbw, dfw, smul_eq_mul, sub_add_cancel, add_sub_cancel_right]
  module

/-- **`eq:local-commutator`**: `Δ(χu) = χΔu + Σ_μ(∂^*_μ((∂_μχ)u) - ∂_μ(ψ_μu) - (∂^*_μ∂_μχ)u)`. -/
theorem commutator (χ : (Fin 4 → ℤ) → ℝ) (u : (Fin 4 → ℤ) → V) (n : Fin 4 → ℤ) :
    lap ε (fun m => χ m • u m) n = χ n • lap ε u n +
      ∑ μ, (dbw ε μ (fun m => dfw ε μ χ m • u m) n - dfw ε μ (fun m => dfw ε μ χ (m - e4 μ) • u m) n -
        dbw ε μ (dfw ε μ χ) n • u n) := by
  simp only [lap, commutator_term, sum_add_distrib, smul_sum]

/-- `χ∂^*_μv = ∂^*_μ(χ(· + εe_μ)v) + (∂_μχ)v` (`eq:local-leibniz`). -/
lemma leibniz_dbw (χ : (Fin 4 → ℤ) → ℝ) (v : (Fin 4 → ℤ) → V) (μ : Fin 4) (n : Fin 4 → ℤ) :
    χ n • dbw ε μ v n = dbw ε μ (fun m => χ (m + e4 μ) • v m) n + dfw ε μ χ n • v n := by
  simp only [dbw, dfw, smul_eq_mul, sub_add_cancel]
  module

/-! ### The localised equation -/

/-- The data of `lem:local-laplacian`: `u`, `h`, `g_μ`, and the coefficients of `c` and `G_μ`. -/
structure LData (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] where
  u : (Fin 4 → ℤ) → V
  h : (Fin 4 → ℤ) → V
  g : Fin 4 → (Fin 4 → ℤ) → V
  c : (Fin 4 → ℤ) → (Fin 4 → ℤ) → (V →L[ℝ] V)
  G : Fin 4 → (Fin 4 → ℤ) → (Fin 4 → ℤ) → (V →L[ℝ] V)

variable (D : LData V)

/-- `v_μ = g_μ + G_μu`. -/
def vf (μ : Fin 4) (n : Fin 4 → ℤ) : V := D.g μ n + locApp (D.G μ) D.u n

/-- **The equation** `eq:local-equation` at the points of `Q_{R-2/3}`. -/
def Eqn (ε : ℝ) (n₀ : Fin 4 → ℤ) (R : ℝ) : Prop :=
  ∀ n, InQr ε n₀ (R - 2 / 3) n → lap ε D.u n = D.h n + locApp D.c D.u n + ∑ μ, dbw ε μ (vf D μ) n

/-- `F₀ = χh + χcu + χu - Σ_μ(∂^*_μ∂_μχ)u + Σ_μ(∂_μχ)(g_μ + G_μu)`. -/
def F0 (ε r : ℝ) (n₀ : Fin 4 → ℤ) (n : Fin 4 → ℤ) : V :=
  chiL ε r n₀ n • D.h n + chiL ε r n₀ n • locApp D.c D.u n + chiL ε r n₀ n • D.u n -
    ∑ μ, dbw ε μ (dfw ε μ (chiL ε r n₀)) n • D.u n + ∑ μ, dfw ε μ (chiL ε r n₀) n • vf D μ n

/-- `F_μ = (∂_μχ)u + χ(· + εe_μ)(g_μ + G_μu)`. -/
def Fm (ε r : ℝ) (n₀ : Fin 4 → ℤ) (μ : Fin 4) (n : Fin 4 → ℤ) : V :=
  dfw ε μ (chiL ε r n₀) n • D.u n + chiL ε r n₀ (n + e4 μ) • vf D μ n

/-- `ψ_μu`, `ψ_μ(n) = ∂_μχ(n - e_μ)`. -/
def psiu (ε r : ℝ) (n₀ : Fin 4 → ℤ) (μ : Fin 4) (n : Fin 4 → ℤ) : V :=
  dfw ε μ (chiL ε r n₀) (n - e4 μ) • D.u n

lemma Fm_fun (ε r : ℝ) (n₀ : Fin 4 → ℤ) (μ : Fin 4) : Fm D ε r n₀ μ =
    fun n => dfw ε μ (chiL ε r n₀) n • D.u n + chiL ε r n₀ (n + e4 μ) • vf D μ n := rfl

lemma psiu_fun (ε r : ℝ) (n₀ : Fin 4 → ℤ) (μ : Fin 4) : psiu D ε r n₀ μ =
    fun n => dfw ε μ (chiL ε r n₀) (n - e4 μ) • D.u n := rfl

/-- `χu`. -/
def chiu (ε r : ℝ) (n₀ : Fin 4 → ℤ) (n : Fin 4 → ℤ) : V := chiL ε r n₀ n • D.u n

/-- **`eq:local-localised`**: `(Δ + 1)(χu) = F₀ + Σ_μ∂^*_μF_μ - Σ_μ∂_μ(ψ_μu)` on all of `εℤ⁴`. -/
theorem localised {R : ℝ} (hr : r + 1 / 3 ≤ R - 2 / 3) (hE : Eqn D ε n₀ R) (n : Fin 4 → ℤ) :
    lap ε (chiu D ε r n₀) n + chiu D ε r n₀ n =
      F0 D ε r n₀ n + ∑ μ, dbw ε μ (Fm D ε r n₀ μ) n - ∑ μ, dfw ε μ (psiu D ε r n₀ μ) n := by
  have hχ : chiL ε r n₀ n • lap ε D.u n =
      chiL ε r n₀ n • (D.h n + locApp D.c D.u n + ∑ μ, dbw ε μ (vf D μ) n) := by
    by_cases h0 : chiL ε r n₀ n = 0
    · rw [h0, zero_smul, zero_smul]
    · rw [hE n fun μ => by have := chiL_supp h0 μ; linarith]
  have hcomm := commutator (ε := ε) (chiL ε r n₀) D.u n
  unfold chiu
  rw [hcomm, hχ]
  simp only [Fm_fun, dbw_add, F0, psiu_fun, smul_add, smul_sum, leibniz_dbw (chiL ε r n₀) (vf D _), sum_add_distrib,
    sum_sub_distrib]
  abel

/-! ### Bounded functions -/

/-- A function which vanishes outside `{|t(n)|_∞ < ρ}` is bounded. -/
lemma bounded_of_supp (hε : 0 < ε) {ρ : ℝ} {f : (Fin 4 → ℤ) → V}
    (hf : ∀ n, (¬ ∀ μ, |tc ε n₀ n μ| < ρ) → f n = 0) : ∃ M, ∀ n, ‖f n‖ ≤ M := by
  obtain ⟨K, hK⟩ : ∃ K : ℕ, ρ / ε ≤ K := exists_nat_ge _
  set B : Finset (Fin 4 → ℤ) := Fintype.piFinset fun μ => Icc (n₀ μ - K) (n₀ μ + K)
  refine ⟨∑ m ∈ B, ‖f m‖, fun n => ?_⟩
  by_cases h : ∀ μ, |tc ε n₀ n μ| < ρ
  · have hn : n ∈ B := by
      refine Fintype.mem_piFinset.2 fun μ => ?_
      have h1 := h μ
      unfold tc at h1
      rw [abs_mul, abs_of_pos hε] at h1
      have h2 : |((n μ - n₀ μ : ℤ) : ℝ)| < K := by
        calc |((n μ - n₀ μ : ℤ) : ℝ)| < ρ / ε := by rw [lt_div_iff₀ hε]; linarith
          _ ≤ K := hK
      have h3 : |n μ - n₀ μ| < (K : ℤ) := by exact_mod_cast h2
      rw [mem_Icc]; constructor <;> linarith [abs_lt.1 h3]
    exact single_le_sum (f := fun m => ‖f m‖) (fun _ _ => norm_nonneg _) hn
  · rw [hf n h, norm_zero]; exact sum_nonneg fun _ _ => norm_nonneg _

lemma not_all_lt {n : Fin 4 → ℤ} {ρ ρ' : ℝ} (h : ¬ ∀ μ, |tc ε n₀ n μ| < ρ) (hρ : ρ' ≤ ρ) :
    ∃ μ, ρ' ≤ |tc ε n₀ n μ| := by
  push_neg at h; obtain ⟨μ, hμ⟩ := h; exact ⟨μ, hρ.trans hμ⟩

variable (hε : 0 < ε) (hε3 : ε ≤ 1 / 3)
include hε hε3

lemma chiL_zero_of {n : Fin 4 → ℤ} {μ : Fin 4} (h : r + 1 / 3 ≤ |tc ε n₀ n μ|) : chiL ε r n₀ n = 0 := by
  by_contra h0; have := chiL_supp h0 μ; linarith

lemma dfw_chiL_zero_of {n : Fin 4 → ℤ} {μ ν : Fin 4} (h : r + 2 / 3 ≤ |tc ε n₀ n ν|) :
    dfw ε μ (chiL ε r n₀) n = 0 := by
  by_contra h0; have := dfw_chiL_supp hε hε3 h0 ν; linarith

lemma dbw_dfw_chiL_zero_of {n : Fin 4 → ℤ} {μ ν : Fin 4} (h : r + 2 / 3 ≤ |tc ε n₀ n ν|) :
    dbw ε μ (dfw ε μ (chiL ε r n₀)) n = 0 := by
  by_contra h0; have := dbw_dfw_chiL_supp hε hε3 h0 ν; linarith

lemma chiL_add_zero_of {n : Fin 4 → ℤ} {μ ν : Fin 4} (h : r + 2 / 3 ≤ |tc ε n₀ n ν|) :
    chiL ε r n₀ (n + e4 μ) = 0 := by
  by_contra h0; have := chiL_add_supp hε hε3 h0 ν; linarith

lemma psi_zero_of {n : Fin 4 → ℤ} {μ ν : Fin 4} (h : r + 1 ≤ |tc ε n₀ n ν|) :
    dfw ε μ (chiL ε r n₀) (n - e4 μ) = 0 := by
  by_contra h0; have := psi_supp hε hε3 h0 ν; linarith

lemma F0_supp (n : Fin 4 → ℤ) (h : ¬ ∀ μ, |tc ε n₀ n μ| < r + 2 / 3) : F0 D ε r n₀ n = 0 := by
  obtain ⟨ν, hν⟩ := not_all_lt h le_rfl
  have h1 : chiL ε r n₀ n = 0 := chiL_zero_of hε hε3 (μ := ν) (by linarith)
  simp only [F0, h1, zero_smul, dbw_dfw_chiL_zero_of hε hε3 hν, dfw_chiL_zero_of hε hε3 hν, sum_const_zero]
  simp

lemma Fm_supp (μ : Fin 4) (n : Fin 4 → ℤ) (h : ¬ ∀ μ, |tc ε n₀ n μ| < r + 2 / 3) : Fm D ε r n₀ μ n = 0 := by
  obtain ⟨ν, hν⟩ := not_all_lt h le_rfl
  simp only [Fm, dfw_chiL_zero_of hε hε3 hν, chiL_add_zero_of hε hε3 hν, zero_smul, add_zero]

lemma psiu_supp (μ : Fin 4) (n : Fin 4 → ℤ) (h : ¬ ∀ μ, |tc ε n₀ n μ| < r + 1) : psiu D ε r n₀ μ n = 0 := by
  obtain ⟨ν, hν⟩ := not_all_lt h le_rfl
  simp only [psiu, psi_zero_of hε hε3 hν, zero_smul]

lemma chiu_supp (n : Fin 4 → ℤ) (h : ¬ ∀ μ, |tc ε n₀ n μ| < r + 1 / 3) : chiu D ε r n₀ n = 0 := by
  obtain ⟨ν, hν⟩ := not_all_lt h le_rfl
  simp only [chiu, chiL_zero_of hε hε3 hν, zero_smul]

omit hε hε3 in
lemma dif_false (f : (Fin 4 → ℤ) → V) (μ : Fin 4) : dif ε false μ f = dbw ε μ f := rfl

omit hε hε3 in
lemma dif_true (f : (Fin 4 → ℤ) → V) (μ : Fin 4) : dif ε true μ f = dfw ε μ f := rfl

/-- **`eq:local-representation`**: `χu = G₁F₀ + Σ_μ∂^*_μG₁F_μ - Σ_μ∂_μG₁(ψ_μu)`. -/
theorem representation {R : ℝ} (hr : r + 1 / 3 ≤ R - 2 / 3) (hE : Eqn D ε n₀ R) :
    chiu D ε r n₀ = fun n => resolvent ε (F0 D ε r n₀) n + ∑ μ, dbw ε μ (resolvent ε (Fm D ε r n₀ μ)) n -
      ∑ μ, dfw ε μ (resolvent ε (psiu D ε r n₀ μ)) n := by
  obtain ⟨M0, hM0⟩ := bounded_of_supp hε (F0_supp D hε hε3)
  have hMm : ∀ μ, ∃ M, ∀ n, ‖Fm D ε r n₀ μ n‖ ≤ M := fun μ => bounded_of_supp hε (Fm_supp D hε hε3 μ)
  have hMp : ∀ μ, ∃ M, ∀ n, ‖psiu D ε r n₀ μ n‖ ≤ M := fun μ => bounded_of_supp hε (psiu_supp D hε hε3 μ)
  choose Mm hMm using hMm
  choose Mp hMp using hMp
  obtain ⟨Mc, hMc⟩ := bounded_of_supp hε (chiu_supp D hε hε3)
  set W : (Fin 4 → ℤ) → V := fun n => resolvent ε (F0 D ε r n₀) n + ∑ μ, dbw ε μ (resolvent ε (Fm D ε r n₀ μ)) n -
      ∑ μ, dfw ε μ (resolvent ε (psiu D ε r n₀ μ)) n with hW
  -- `(Δ + 1)W = F₀ + Σ_μ∂^*_μF_μ - Σ_μ∂_μ(ψ_μu)`
  have hres : ∀ (F : (Fin 4 → ℤ) → V) (M : ℝ), (∀ n, ‖F n‖ ≤ M) →
      (fun n => lap ε (resolvent ε F) n + resolvent ε F n) = F := fun F M hF => by
    funext n; exact lap_resolvent_add hε hF n
  have hlapW : ∀ n, lap ε W n + W n =
      F0 D ε r n₀ n + ∑ μ, dbw ε μ (Fm D ε r n₀ μ) n - ∑ μ, dfw ε μ (psiu D ε r n₀ μ) n := fun n => by
    have e1 : lap ε W n = lap ε (resolvent ε (F0 D ε r n₀)) n +
        ∑ μ, dbw ε μ (lap ε (resolvent ε (Fm D ε r n₀ μ))) n -
        ∑ μ, dfw ε μ (lap ε (resolvent ε (psiu D ε r n₀ μ))) n := by
      rw [hW, lap_sub, lap_add, lap_sum, lap_sum]
      simp only [lap_dbw, lap_dfw]
    have e2 : ∀ μ, dbw ε μ (lap ε (resolvent ε (Fm D ε r n₀ μ))) n + dbw ε μ (resolvent ε (Fm D ε r n₀ μ)) n =
        dbw ε μ (Fm D ε r n₀ μ) n := fun μ => by
      rw [← dbw_add, hres _ _ (hMm μ)]
    have e3 : ∀ μ, dfw ε μ (lap ε (resolvent ε (psiu D ε r n₀ μ))) n + dfw ε μ (resolvent ε (psiu D ε r n₀ μ)) n =
        dfw ε μ (psiu D ε r n₀ μ) n := fun μ => by
      rw [← dfw_add, hres _ _ (hMp μ)]
    rw [e1, ← lap_resolvent_add hε hM0 n, ← sum_congr rfl fun μ _ => e2 μ, ← sum_congr rfl fun μ _ => e3 μ,
      sum_add_distrib, sum_add_distrib]
    simp only [hW]
    abel
  -- `χu - W` is bounded and solves `(Δ + 1)(χu - W) = 0`
  have hWb : ∀ n, ‖W n‖ ≤ M0 + ∑ μ, 2 * Mm μ + ∑ μ, 2 * Mp μ := fun n => by
    simp only [hW]
    refine (norm_sub_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add (norm_resolvent_le hM0 n)
      ((norm_sum_le _ _).trans (sum_le_sum fun μ _ => ?_)))) ((norm_sum_le _ _).trans (sum_le_sum fun μ _ => ?_)))
    · rw [← dif_false]; exact norm_dif_resolvent_le hε (hMm μ) false μ n
    · rw [← dif_true]; exact norm_dif_resolvent_le hε (hMp μ) true μ n
  funext n
  have hz := eq_zero_of_lap_add hε (u := fun m => chiu D ε r n₀ m - W m)
    (B := Mc + (M0 + ∑ μ, 2 * Mm μ + ∑ μ, 2 * Mp μ))
    (fun m => (norm_sub_le _ _).trans (add_le_add (hMc m) (hWb m)))
    (fun m => by
      rw [lap_sub, show ∀ a b c d : V, a - b + (c - d) = (a + c) - (b + d) from fun a b c d => by abel,
        localised D hr hE m, hlapW m, sub_self]) n
  exact sub_eq_zero.1 hz

end LocalLaplacian
end CoreLean

end
