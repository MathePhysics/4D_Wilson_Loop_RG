/-
**`lem:bumps`** of BALABAN_CORE.tex (`a021c13be348`) on the torus model of `MomentumTorus.lean`: `n = a_c/a₀ = 2r + 1`,
`h = r`, `T^{(0)} = (ℤ/nK)⁴` with `a₀ = 1/n`, `T^{(j)} = (ℤ/K)⁴` with `a_j = 1` embedded by `y ↦ ny` (`emb`), and
`Q_j(id) = Qop`. For the bond `c` of the direction `μ` and its end `y_c` (`side = false` for `y_c = c₋`, `true` for
`y_c = c₊`), the bonds of the direction `μ` with both ends in `Δ(y_c)` are those at `x = ny_c + me_μ + n_⊥`,
`-h ≤ m ≤ h - 1`, `|n_ν| ≤ h` (`pos`, `Iset`); `s(m) = m + h + 1` or `h - m` (`sOf`); `ψ(n_⊥) = ∏_{ν ≠ μ}β((n_ν + h + 1)/
(n + 1))`; `Ψ = (Σβ)³` (`Psi`); `K = n⁵/Ψ ≤ 2¹⁵n²` (`Kc`); `φ_c(b) = g(s(m))ψ(n_⊥)` (`phiR`). Proved: (i) the support
(`bump_support`), (ii) `‖φ_c‖_∞ ≤ 160 ≤ C_φ` and the differences `≤ C_φ/n = C_φa₀/a_c`, `C_φ = 1280` (`bump_le`,
`bump_diff`), (iii) `Q_j(id)φ_c` is the indicator function of `c` (`bump_average`), for `r ≥ 1` (`j ≥ 1`) and `K ≥ 2`.
The proof is the core's: a bond at `ny_c + me_μ + n_⊥` enters the average of `(y', μ)` with the weight `n⁻⁵(m + h + 1)` if
`y' = y_c`, `n⁻⁵(h - m)` if `y' + e_μ = y_c`, and `0` otherwise (`count_eq`).
-/
import CoreLean.BumpProfile
import CoreLean.MomentumTorus

open Finset

noncomputable section

namespace CoreLean
namespace BumpField

open Bumps

/-! ### The profiles -/

variable (r : ℕ)

/-- `n = a_c/a₀ = 2r + 1`. -/
abbrev nn : ℕ := 2 * r + 1

/-- The transverse profile `β((t + h + 1)/(n + 1))`. -/
def beta (t : ℤ) : ℝ := Bq (nn r + 1) (t + r + 1) / ((nn r + 1 : ℕ) : ℝ) ^ 4

/-- `s(m) = m + h + 1` (`y_c = c₋`) or `h - m` (`y_c = c₊`). -/
def sOf (side : Bool) (m : ℤ) : ℤ := if side then (r : ℤ) - m else m + r + 1

/-- `Σ_{|t| ≤ h}β((t + h + 1)/(n + 1))`. -/
def Sbeta : ℝ := SB (nn r + 1) / ((nn r + 1 : ℕ) : ℝ) ^ 4

/-- `Ψ`, the sum of `ψ`. -/
def Psi : ℝ := Sbeta r ^ 3

/-- `K = n⁵/Ψ`. -/
def Kc : ℝ := (nn r : ℝ) ^ 5 / Psi r

/-- The factors of `φ_c`: `g(s(m))` in the direction `μ`, `β` in the others. -/
def F (μ : Fin 4) (side : Bool) (ν : Fin 4) (t : ℤ) : ℝ :=
  if ν = μ then g (nn r) (Kc r) (sOf r side t) else beta r t

/-- `g(s(m))ψ(n_⊥)` at the offset `p = me_μ + n_⊥`. -/
def coef (μ : Fin 4) (side : Bool) (p : Fin 4 → ℤ) : ℝ := ∏ ν, F r μ side ν (p ν)

lemma Bq_out' {n : ℕ} {s : ℤ} (h : s ≤ 0 ∨ (n : ℤ) ≤ s) : Bq n s = 0 := by
  unfold Bq
  split_ifs with h1
  · rcases h with h | h
    · have : s = 0 := le_antisymm h h1.1
      subst this; simp
    · have : s = n := le_antisymm h1.2 h
      subst this; simp
  · rfl

lemma N_pos : (0 : ℝ) < ((nn r + 1 : ℕ) : ℝ) := by positivity

lemma beta_nonneg (t : ℤ) : 0 ≤ beta r t := by
  unfold beta; exact div_nonneg (Bq_nonneg _ _) (by positivity)

lemma beta_le (t : ℤ) : beta r t ≤ 1 / 16 := by
  unfold beta
  have h := N_pos r
  rw [div_le_iff₀ (by positivity)]
  have := Bq_le (nn r + 1) (t + r + 1)
  linarith

lemma abs_beta_le (t : ℤ) : |beta r t| ≤ 1 / 16 := by
  rw [abs_of_nonneg (beta_nonneg r t)]; exact beta_le r t

lemma beta_diff (t : ℤ) : |beta r (t + 1) - beta r t| ≤ 1 / (2 * (nn r : ℝ)) := by
  unfold beta
  have h := N_pos r
  have hn : (0 : ℝ) < (nn r : ℝ) := by positivity
  rw [← sub_div, abs_div, abs_of_pos (by positivity : (0 : ℝ) < ((nn r + 1 : ℕ) : ℝ) ^ 4),
    div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 := Bq_diff (nn r + 1) (t + r + 1)
  rw [show t + r + 1 + 1 = t + 1 + r + 1 by ring] at h1
  have hc : ((nn r + 1 : ℕ) : ℝ) = (nn r : ℝ) + 1 := by push_cast; ring
  rw [hc] at h1 ⊢
  calc |Bq (nn r + 1) (t + 1 + r + 1) - Bq (nn r + 1) (t + r + 1)| * (2 * (nn r : ℝ))
      ≤ ((nn r : ℝ) + 1) ^ 3 / 2 * (2 * (nn r : ℝ)) := mul_le_mul_of_nonneg_right h1 (by positivity)
    _ ≤ 1 * ((nn r : ℝ) + 1) ^ 4 := by nlinarith [pow_pos hn 3]

lemma beta_out {t : ℤ} (h : t < -(r : ℤ) ∨ (r : ℤ) < t) : beta r t = 0 := by
  unfold beta
  rw [Bq_out' (by push_cast; omega), zero_div]

/-- `Σ_{|t| ≤ h}β((t + h + 1)/(n + 1)) = Σ_{t=0}^{n+1}β(t/(n + 1))`. -/
lemma sum_beta : ∑ t ∈ Icc (-(r : ℤ)) r, beta r t = Sbeta r := by
  unfold beta Sbeta
  rw [← sum_div, ← sum_Bq]
  congr 1
  have h1 : ∑ s ∈ Icc (0 : ℤ) ((nn r + 1 : ℕ) : ℤ), Bq (nn r + 1) s =
      ∑ s ∈ Icc (1 : ℤ) ((2 * r + 1 : ℕ) : ℤ), Bq (nn r + 1) s := by
    symm
    refine sum_subset (fun s hs => ?_) (fun s hs hs' => ?_)
    · simp only [mem_Icc] at hs ⊢; push_cast at hs ⊢; omega
    · simp only [mem_Icc] at hs hs'; push_cast at hs hs'
      exact Bq_out' (by push_cast; omega)
  rw [h1]
  refine sum_nbij' (fun t => t + r + 1) (fun s => s - r - 1) ?_ ?_ ?_ ?_ ?_
  · intro t ht; simp only [mem_Icc] at ht ⊢; push_cast; omega
  · intro s hs; simp only [mem_Icc] at hs ⊢; push_cast at hs; omega
  · intro t _; ring
  · intro s _; ring
  · intro t _; rfl

lemma Sbeta_ge (hr : 1 ≤ r) : (nn r : ℝ) / 32 ≤ Sbeta r := by
  unfold Sbeta
  have h := SB_ge (n := nn r + 1) (by unfold nn; omega)
  have hN := N_pos r
  rw [le_div_iff₀ (by positivity)]
  have hc : ((nn r + 1 : ℕ) : ℝ) = (nn r : ℝ) + 1 := by push_cast; ring
  rw [hc] at h hN ⊢
  have hn : (0 : ℝ) ≤ (nn r : ℝ) := by positivity
  nlinarith [pow_pos hN 4]

lemma Psi_pos (hr : 1 ≤ r) : 0 < Psi r := by
  have := Sbeta_ge r hr
  have hn : (0 : ℝ) < (nn r : ℝ) := by positivity
  unfold Psi; have : 0 < Sbeta r := by linarith
  positivity

lemma Kc_nonneg (hr : 1 ≤ r) : 0 ≤ Kc r := by
  unfold Kc; exact div_nonneg (by positivity) (Psi_pos r hr).le

/-- `K = n⁵/Ψ ≤ 2¹⁵n²`. -/
lemma Kc_le (hr : 1 ≤ r) : Kc r ≤ 2 ^ 15 * (nn r : ℝ) ^ 2 := by
  have h := Sbeta_ge r hr
  have hn : (0 : ℝ) < (nn r : ℝ) := by positivity
  have hP := Psi_pos r hr
  unfold Kc
  rw [div_le_iff₀ hP]
  have h3 : ((nn r : ℝ) / 32) ^ 3 ≤ Psi r := by
    unfold Psi; exact pow_le_pow_left₀ (by positivity) h 3
  calc (nn r : ℝ) ^ 5 = 2 ^ 15 * (nn r : ℝ) ^ 2 * ((nn r : ℝ) / 32) ^ 3 := by ring
    _ ≤ 2 ^ 15 * (nn r : ℝ) ^ 2 * Psi r := mul_le_mul_of_nonneg_left h3 (by positivity)

lemma g_bound (hr : 1 ≤ r) (s : ℤ) : |g (nn r) (Kc r) s| ≤ 20 * 2 ^ 15 := by
  have hn : (0 : ℝ) < (nn r : ℝ) := by positivity
  refine (g_le (by unfold nn; omega) (Kc_nonneg r hr) s).trans ?_
  rw [div_le_iff₀ (by positivity)]
  have := Kc_le r hr
  linarith

lemma g_diff_bound (hr : 1 ≤ r) (s : ℤ) :
    |g (nn r) (Kc r) (s + 1) - g (nn r) (Kc r) s| ≤ 124 * 2 ^ 15 / (nn r : ℝ) := by
  have hn : (0 : ℝ) < (nn r : ℝ) := by positivity
  refine (g_diff (by unfold nn; omega) (Kc_nonneg r hr) s).trans ?_
  rw [div_le_div_iff₀ (by positivity) hn]
  have := Kc_le r hr
  have e : 124 * 2 ^ 15 * (nn r : ℝ) ^ 3 = 124 * (2 ^ 15 * (nn r : ℝ) ^ 2) * (nn r : ℝ) := by ring
  rw [e]
  exact mul_le_mul_of_nonneg_right (by linarith) hn.le

/-- The reindexing `m ↦ s(m)` of `[-h, h - 1]` onto `[1, n - 1]`. -/
lemma sum_sOf (side : Bool) (f : ℤ → ℝ) (h0 : f 0 = 0) (hn : f (nn r) = 0) :
    ∑ m ∈ Icc (-(r : ℤ)) (r - 1), f (sOf r side m) = ∑ s ∈ Icc (0 : ℤ) (nn r), f s := by
  have h1 : ∑ s ∈ Icc (0 : ℤ) (nn r), f s = ∑ s ∈ Icc (1 : ℤ) (2 * r), f s := by
    symm
    refine sum_subset (fun s hs => ?_) (fun s hs hs' => ?_)
    · simp only [mem_Icc] at hs ⊢; push_cast; omega
    · simp only [mem_Icc] at hs hs'; push_cast at hs
      rcases (show s = 0 ∨ s = ((nn r : ℕ) : ℤ) by push_cast; omega) with rfl | rfl
      · exact h0
      · exact hn
  rw [h1]
  cases side
  · refine sum_nbij' (fun m => m + r + 1) (fun s => s - r - 1) ?_ ?_ ?_ ?_ ?_
    · intro t ht; simp only [mem_Icc] at ht ⊢; omega
    · intro s hs; simp only [mem_Icc] at hs ⊢; omega
    · intro t _; ring
    · intro s _; ring
    · intro t _; simp [sOf]
  · refine sum_nbij' (fun m => (r : ℤ) - m) (fun s => (r : ℤ) - s) ?_ ?_ ?_ ?_ ?_
    · intro t ht; simp only [mem_Icc] at ht ⊢; omega
    · intro s hs; simp only [mem_Icc] at hs ⊢; omega
    · intro t _; ring
    · intro s _; ring
    · intro t _; simp [sOf]

/-! ### The bounds of `g(s(m))ψ(n_⊥)` -/

/-- The bounds of the factors: `20·2¹⁵` for `g`, `1/16` for `β`. -/
def Bd (μ ν : Fin 4) : ℝ := if ν = μ then 20 * 2 ^ 15 else 1 / 16

lemma Bd_pos (μ ν : Fin 4) : 0 < Bd μ ν := by unfold Bd; split_ifs <;> norm_num

lemma prod_Bd (μ : Fin 4) : ∏ ν, Bd μ ν = 160 := by
  rw [Fintype.prod_eq_mul_prod_compl μ]
  have : ∏ ν ∈ ({μ}ᶜ : Finset (Fin 4)), Bd μ ν = (1 / 16) ^ 3 := by
    rw [prod_congr rfl fun ν hν => (show Bd μ ν = 1 / 16 by
      unfold Bd; rw [if_neg (by simpa using hν)]), prod_const]
    simp [card_compl]
  rw [this]; unfold Bd; norm_num

lemma F_le (hr : 1 ≤ r) (μ : Fin 4) (side : Bool) (ν : Fin 4) (t : ℤ) : |F r μ side ν t| ≤ Bd μ ν := by
  unfold F Bd
  split_ifs
  · exact g_bound r hr _
  · exact abs_beta_le r t

lemma F_diff (hr : 1 ≤ r) (μ : Fin 4) (side : Bool) (ν : Fin 4) (t : ℤ) :
    |F r μ side ν (t + 1) - F r μ side ν t| ≤
      if ν = μ then 124 * 2 ^ 15 / (nn r : ℝ) else 1 / (2 * (nn r : ℝ)) := by
  unfold F
  split_ifs
  · cases side
    · have e : sOf r false (t + 1) = sOf r false t + 1 := by simp [sOf]; ring
      rw [e]; exact g_diff_bound r hr _
    · have e : sOf r true (t + 1) = sOf r true t - 1 := by simp [sOf]; ring
      rw [e, abs_sub_comm]
      have := g_diff_bound r hr (sOf r true t - 1)
      rwa [sub_add_cancel] at this
  · exact beta_diff r t

lemma coef_le (hr : 1 ≤ r) (μ : Fin 4) (side : Bool) (p : Fin 4 → ℤ) : |coef r μ side p| ≤ 160 := by
  unfold coef
  rw [abs_prod, ← prod_Bd μ]
  exact Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun ν _ => F_le r hr μ side ν (p ν)

/-- The first differences of `g(s(m))ψ(n_⊥)`: at most `992/n` in the direction `μ`, `1280/n` in the others. -/
lemma coef_diff (hr : 1 ≤ r) (μ : Fin 4) (side : Bool) (p : Fin 4 → ℤ) (κ : Fin 4) :
    |coef r μ side (p + Pi.single κ 1) - coef r μ side p| ≤ 1280 / (nn r : ℝ) := by
  have hn : (0 : ℝ) < (nn r : ℝ) := by positivity
  unfold coef
  rw [Fintype.prod_eq_mul_prod_compl κ, Fintype.prod_eq_mul_prod_compl κ (fun ν => F r μ side ν (p ν))]
  have hoff : ∏ ν ∈ ({κ}ᶜ : Finset (Fin 4)), F r μ side ν ((p + Pi.single κ 1 : Fin 4 → ℤ) ν) =
      ∏ ν ∈ ({κ}ᶜ : Finset (Fin 4)), F r μ side ν (p ν) := by
    refine prod_congr rfl fun ν hν => ?_
    have : ν ≠ κ := by simpa using hν
    simp [this]
  have hκ : (p + Pi.single κ 1 : Fin 4 → ℤ) κ = p κ + 1 := by simp
  rw [hoff, hκ, ← sub_mul, abs_mul]
  set X := ∏ ν ∈ ({κ}ᶜ : Finset (Fin 4)), F r μ side ν (p ν)
  have hX : |X| * Bd μ κ ≤ 160 := by
    have h1 : |X| ≤ ∏ ν ∈ ({κ}ᶜ : Finset (Fin 4)), Bd μ ν := by
      rw [abs_prod]
      exact Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun ν _ => F_le r hr μ side ν (p ν)
    have h2 := prod_Bd μ
    rw [Fintype.prod_eq_mul_prod_compl κ] at h2
    nlinarith [Bd_pos μ κ]
  have hD := F_diff r hr μ side κ (p κ)
  have hXn := abs_nonneg X
  by_cases hk : κ = μ
  · rw [if_pos hk] at hD
    have hB : Bd μ κ = 20 * 2 ^ 15 := by unfold Bd; rw [if_pos hk]
    rw [hB] at hX
    calc |F r μ side κ (p κ + 1) - F r μ side κ (p κ)| * |X| ≤ 124 * 2 ^ 15 / (nn r : ℝ) * |X| :=
          mul_le_mul_of_nonneg_right hD hXn
      _ ≤ 124 * 2 ^ 15 / (nn r : ℝ) * (160 / (20 * 2 ^ 15)) :=
          mul_le_mul_of_nonneg_left (by rw [le_div_iff₀ (by norm_num)]; exact hX) (by positivity)
      _ ≤ 1280 / (nn r : ℝ) := by rw [div_mul_eq_mul_div]; gcongr; norm_num
  · rw [if_neg hk] at hD
    have hB : Bd μ κ = 1 / 16 := by unfold Bd; rw [if_neg hk]
    rw [hB] at hX
    calc |F r μ side κ (p κ + 1) - F r μ side κ (p κ)| * |X| ≤ 1 / (2 * (nn r : ℝ)) * |X| :=
          mul_le_mul_of_nonneg_right hD hXn
      _ ≤ 1 / (2 * (nn r : ℝ)) * 2560 := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = 1280 / (nn r : ℝ) := by field_simp; norm_num

/-! ### The field on the torus -/

open MomentumTorus TorusFourier MomentumSymbols

variable (K : ℕ) [NeZero K]

/-- The offsets `me_μ + n_⊥`, `-h ≤ m ≤ h - 1`, `|n_ν| ≤ h`, of the bonds of the direction `μ` with both ends in
`Δ(y_c)`. -/
def Iset (μ : Fin 4) : Finset (Fin 4 → ℤ) :=
  Fintype.piFinset fun ν => if ν = μ then Icc (-(r : ℤ)) (r - 1) else Icc (-(r : ℤ)) r

/-- The point `y_c + a₀p` of `T^{(0)}`. -/
def pos (yc : Tor K) (p : Fin 4 → ℤ) : Tor (NN r K) := emb r K yc + castw r K p

/-- The block `Δ(y_c)` of the points `y_c + a₀w`, `|w_ν| ≤ h`. -/
def Delta (yc : Tor K) : Finset (Tor (NN r K)) := (box r).image (pos r K yc)

/-- `φ_c` on the positive bonds `(x, x + a₀e_ν)` of `T^{(0)}`: `g(s(m))ψ(n_⊥)` at `x = y_c + a₀(me_μ + n_⊥)`, `ν = μ`,
and `0` on the other bonds. -/
def phiR (μ : Fin 4) (side : Bool) (yc : Tor K) (ν : Fin 4) (x : Tor (NN r K)) : ℝ :=
  if ν = μ then ∑ p ∈ Iset r μ, (if x = pos r K yc p then coef r μ side p else 0) else 0

lemma castw_add (p q : Fin 4 → ℤ) : castw r K (p + q) = castw r K p + castw r K q := by
  funext i; simp [castw]

lemma castw_sub (p q : Fin 4 → ℤ) : castw r K (p - q) = castw r K p - castw r K q := by
  funext i; simp [castw]

lemma castw_single (κ : Fin 4) (a : ℤ) : castw r K (Pi.single κ a) = Pi.single κ (a : ZMod (NN r K)) := by
  funext i
  by_cases h : i = κ
  · subst h; simp [castw]
  · simp [castw, h]

lemma pos_add (yc : Tor K) (p q : Fin 4 → ℤ) : pos r K yc (p + q) = pos r K yc p + castw r K q := by
  unfold pos; rw [castw_add]; abel

lemma castw_inj (hr : 1 ≤ r) (hK : 2 ≤ K) {p q : Fin 4 → ℤ} (hp : ∀ i, |p i| ≤ r + 1)
    (hq : ∀ i, |q i| ≤ r + 1) (h : castw r K p = castw r K q) : p = q := by
  funext i
  have h1 := congrFun h i
  simp only [castw] at h1
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h1
  obtain ⟨hp1, hp2⟩ := abs_le.1 (hp i)
  obtain ⟨hq1, hq2⟩ := abs_le.1 (hq i)
  have hN : (4 * r + 2 : ℤ) ≤ ((NN r K : ℕ) : ℤ) := by
    have hK' : (2 : ℤ) ≤ K := by exact_mod_cast hK
    unfold NN; push_cast
    nlinarith
  have hr' : (1 : ℤ) ≤ r := by exact_mod_cast hr
  have h2 : |q i - p i| < ((NN r K : ℕ) : ℤ) := abs_lt.2 ⟨by linarith, by linarith⟩
  have := Int.eq_zero_of_abs_lt_dvd h1 h2
  linarith

lemma mem_Iset {μ : Fin 4} {p : Fin 4 → ℤ} :
    p ∈ Iset r μ ↔ (-(r : ℤ) ≤ p μ ∧ p μ ≤ r - 1) ∧ ∀ ν, ν ≠ μ → -(r : ℤ) ≤ p ν ∧ p ν ≤ r := by
  unfold Iset
  rw [Fintype.mem_piFinset]
  constructor
  · intro h
    refine ⟨by simpa using h μ, fun ν hν => ?_⟩
    have := h ν; rw [if_neg hν] at this; simpa using this
  · rintro ⟨h1, h2⟩ ν
    by_cases hν : ν = μ
    · subst hν; simpa using h1
    · rw [if_neg hν]; simpa using h2 ν hν

lemma mem_box {w : Fin 4 → ℤ} : w ∈ box r ↔ ∀ ν, -(r : ℤ) ≤ w ν ∧ w ν ≤ r := by
  unfold MomentumSymbols.box; rw [Fintype.mem_piFinset]; simp

lemma Iset_abs {μ : Fin 4} {p : Fin 4 → ℤ} (hp : p ∈ Iset r μ) (ν : Fin 4) : |p ν| ≤ r + 1 := by
  obtain ⟨h1, h2⟩ := (mem_Iset r).1 hp
  rw [abs_le]
  by_cases hν : ν = μ
  · subst hν; constructor <;> linarith [h1.1, h1.2]
  · have := h2 ν hν; constructor <;> linarith [this.1, this.2]

lemma coef_out {μ : Fin 4} (side : Bool) {p : Fin 4 → ℤ} (hp : p ∉ Iset r μ) : coef r μ side p = 0 := by
  unfold Iset at hp
  rw [Fintype.mem_piFinset] at hp
  push_neg at hp
  obtain ⟨ν, hν⟩ := hp
  unfold coef
  refine prod_eq_zero (mem_univ ν) ?_
  unfold F
  by_cases h : ν = μ
  · rw [if_pos h] at hν ⊢
    simp only [mem_Icc, not_and_or, not_le] at hν
    refine g_out _ (by unfold nn; omega) ?_
    cases side <;> simp only [sOf] <;> push_cast <;> omega
  · rw [if_neg h] at hν ⊢
    simp only [mem_Icc, not_and_or, not_le] at hν
    exact beta_out r (by omega)

lemma phiR_off {μ ν : Fin 4} (side : Bool) (yc : Tor K) (x : Tor (NN r K)) (h : ν ≠ μ) :
    phiR r K μ side yc ν x = 0 := by
  unfold phiR; rw [if_neg h]

lemma phiR_zero {μ : Fin 4} (side : Bool) (yc : Tor K) (ν : Fin 4) {x : Tor (NN r K)}
    (h : ∀ p ∈ Iset r μ, x ≠ pos r K yc p) : phiR r K μ side yc ν x = 0 := by
  unfold phiR
  split_ifs
  · exact sum_eq_zero fun p hp => if_neg (h p hp)
  · rfl

/-- `φ_c(y_c + a₀p) = g(s(p_μ))ψ(p_⊥)` for `|p_ν| ≤ h + 1`. -/
lemma phiR_pos (hr : 1 ≤ r) (hK : 2 ≤ K) {μ : Fin 4} (side : Bool) (yc : Tor K) {p : Fin 4 → ℤ}
    (hp : ∀ i, |p i| ≤ r + 1) : phiR r K μ side yc μ (pos r K yc p) = coef r μ side p := by
  unfold phiR
  rw [if_pos rfl]
  have hinj : ∀ q ∈ Iset r μ, pos r K yc p = pos r K yc q → q = p := fun q hq h =>
    (castw_inj r K hr hK hp (Iset_abs r hq) (add_left_cancel h)).symm
  by_cases hpI : p ∈ Iset r μ
  · rw [sum_eq_single p (fun q hq hqp => if_neg fun h => hqp (hinj q hq h)) (fun h => absurd hpI h), if_pos rfl]
  · rw [coef_out r side hpI]
    exact sum_eq_zero fun q hq => if_neg fun h => hpI (hinj q hq h ▸ hq)

/-- **`lem:bumps`(i)**: `φ_c` vanishes outside the bonds of the direction `μ` with both ends in `Δ(y_c)`. -/
theorem bump_support {μ ν : Fin 4} (side : Bool) (yc : Tor K) {x : Tor (NN r K)}
    (h : phiR r K μ side yc ν x ≠ 0) :
    ν = μ ∧ x ∈ Delta r K yc ∧ x + Pi.single μ 1 ∈ Delta r K yc := by
  have hν : ν = μ := by
    by_contra hν; exact h (phiR_off r K side yc x hν)
  subst hν
  have hx : ∃ p ∈ Iset r ν, x = pos r K yc p := by
    by_contra hx; push_neg at hx; exact h (phiR_zero r K side yc ν hx)
  obtain ⟨p, hp, rfl⟩ := hx
  obtain ⟨h1, h2⟩ := (mem_Iset r).1 hp
  refine ⟨rfl, mem_image.2 ⟨p, (mem_box r).2 fun i => ?_, rfl⟩, mem_image.2 ⟨p + Pi.single ν 1, (mem_box r).2 fun i => ?_, ?_⟩⟩
  · by_cases hi : i = ν
    · subst hi; constructor <;> linarith [h1.1, h1.2]
    · exact h2 i hi
  · by_cases hi : i = ν
    · subst hi; simp; constructor <;> linarith [h1.1, h1.2]
    · simp [hi]; exact h2 i hi
  · rw [pos_add, castw_single]; simp

/-- **`lem:bumps`(ii)**, the supremum: `‖φ_c‖_∞ ≤ 160 ≤ C_φ`. -/
theorem bump_le (hr : 1 ≤ r) (hK : 2 ≤ K) (μ : Fin 4) (side : Bool) (yc : Tor K) (ν : Fin 4) (x : Tor (NN r K)) :
    |phiR r K μ side yc ν x| ≤ 160 := by
  by_cases hν : ν = μ
  · subst hν
    by_cases hx : ∃ p ∈ Iset r ν, x = pos r K yc p
    · obtain ⟨p, hp, rfl⟩ := hx
      rw [phiR_pos r K hr hK side yc (Iset_abs r hp)]
      exact coef_le r hr ν side p
    · push_neg at hx
      rw [phiR_zero r K side yc ν hx, abs_zero]; norm_num
  · rw [phiR_off r K side yc x hν, abs_zero]; norm_num

/-- **`lem:bumps`(ii)**, the differences: `|φ_c(b + a₀e_κ) - φ_c(b)| ≤ C_φ/n = C_φa₀/a_c`, `C_φ = 1280`. -/
theorem bump_diff (hr : 1 ≤ r) (hK : 2 ≤ K) (μ : Fin 4) (side : Bool) (yc : Tor K) (ν : Fin 4)
    (x : Tor (NN r K)) (κ : Fin 4) :
    |phiR r K μ side yc ν (x + Pi.single κ 1) - phiR r K μ side yc ν x| ≤ 1280 / (nn r : ℝ) := by
  have hn : (0 : ℝ) < (nn r : ℝ) := by positivity
  by_cases hν : ν = μ
  · subst hν
    have hs : castw r K (Pi.single κ 1) = Pi.single κ 1 := by rw [castw_single]; simp
    by_cases hx : ∃ p ∈ Iset r ν, x = pos r K yc p
    · obtain ⟨p, hp, rfl⟩ := hx
      have hp1 : ∀ i, |(p + Pi.single κ 1 : Fin 4 → ℤ) i| ≤ r + 1 := by
        intro i
        obtain ⟨h1, h2⟩ := (mem_Iset r).1 hp
        rw [abs_le]
        by_cases hi : i = ν
        · subst hi
          by_cases hk : κ = i
          · subst hk; simp; constructor <;> linarith [h1.1, h1.2]
          · simp [Ne.symm hk]; constructor <;> linarith [h1.1, h1.2]
        · have := h2 i hi
          by_cases hk : κ = i
          · subst hk; simp; constructor <;> linarith [this.1, this.2]
          · simp [Ne.symm hk]; constructor <;> linarith [this.1, this.2]
      rw [← hs, ← pos_add, phiR_pos r K hr hK side yc hp1, phiR_pos r K hr hK side yc (Iset_abs r hp)]
      exact coef_diff r hr ν side p κ
    · by_cases hx' : ∃ p ∈ Iset r ν, x + Pi.single κ 1 = pos r K yc p
      · obtain ⟨p, hp, hxp⟩ := hx'
        have hx2 : x = pos r K yc (p - Pi.single κ 1) := by
          rw [sub_eq_add_neg, pos_add, ← hxp, show castw r K (-Pi.single κ 1) = -Pi.single κ 1 by
            funext i; by_cases hi : i = κ
            · subst hi; simp [castw]
            · simp [castw, hi]]
          abel
        have hp1 : ∀ i, |(p - Pi.single κ 1 : Fin 4 → ℤ) i| ≤ r + 1 := by
          intro i
          obtain ⟨h1, h2⟩ := (mem_Iset r).1 hp
          rw [abs_le]
          by_cases hi : i = ν
          · subst hi
            by_cases hk : κ = i
            · subst hk; simp; constructor <;> linarith [h1.1, h1.2]
            · simp [Ne.symm hk]; constructor <;> linarith [h1.1, h1.2]
          · have := h2 i hi
            by_cases hk : κ = i
            · subst hk; simp; constructor <;> linarith [this.1, this.2]
            · simp [Ne.symm hk]; constructor <;> linarith [this.1, this.2]
        rw [hxp, hx2, phiR_pos r K hr hK side yc hp1, phiR_pos r K hr hK side yc (Iset_abs r hp)]
        have := coef_diff r hr ν side (p - Pi.single κ 1) κ
        rwa [sub_add_cancel] at this
      · push_neg at hx hx'
        rw [phiR_zero r K side yc ν hx, phiR_zero r K side yc ν hx', sub_zero, abs_zero]
        positivity
  · rw [phiR_off r K side yc _ hν, phiR_off r K side yc _ hν, sub_zero, abs_zero]
    positivity

/-! ### The averages -/

lemma cast_zero_iff (a e : ℤ) :
    (((nn r : ℤ) * a + e : ℤ) : ZMod (NN r K)) = 0 ↔
      (nn r : ℤ) ∣ e ∧ ((a + e / (nn r : ℤ) : ℤ) : ZMod K) = 0 := by
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hNN : ((NN r K : ℕ) : ℤ) = (nn r : ℤ) * K := by unfold NN; push_cast; ring
  rw [hNN]
  have hn0 : (nn r : ℤ) ≠ 0 := by positivity
  constructor
  · intro h
    have he : (nn r : ℤ) ∣ e :=
      (dvd_add_right (dvd_mul_right _ _)).1 (dvd_trans (dvd_mul_right _ _) h)
    obtain ⟨e', rfl⟩ := he
    refine ⟨dvd_mul_right _ _, ?_⟩
    rw [mul_div_cancel_left₀ _ hn0]
    rw [← mul_add] at h
    exact (mul_dvd_mul_iff_left hn0).1 h
  · rintro ⟨⟨e', rfl⟩, h⟩
    rw [mul_div_cancel_left₀ _ hn0] at h
    rw [← mul_add]
    exact mul_dvd_mul_left _ h

/-- The equation of a point of the path from `y' + a₀w` to `y' + a₀w + a_je_μ` with `y_c + a₀p`, coordinatewise. -/
lemma coord_iff (y' yc : Tor K) (w p : Fin 4 → ℤ) (μ : Fin 4) (t : ℕ) (i : Fin 4) :
    (emb r K y' + castw r K w + Pi.single μ ((t : ℕ) : ZMod (NN r K)) : Tor (NN r K)) i = pos r K yc p i ↔
      (nn r : ℤ) ∣ (w i + (if i = μ then (t : ℤ) else 0) - p i) ∧
      y' i + (((w i + (if i = μ then (t : ℤ) else 0) - p i) / (nn r : ℤ) : ℤ) : ZMod K) = yc i := by
  set e := w i + (if i = μ then (t : ℤ) else 0) - p i with he
  have h1 : (emb r K y' + castw r K w + Pi.single μ ((t : ℕ) : ZMod (NN r K)) : Tor (NN r K)) i - pos r K yc p i =
      (((nn r : ℤ) * (((y' i).val : ℤ) - ((yc i).val : ℤ)) + e : ℤ) : ZMod (NN r K)) := by
    simp only [pos, Pi.add_apply, emb, castw, he, Pi.single_apply]
    split_ifs <;> push_cast <;> ring
  rw [← sub_eq_zero, h1, cast_zero_iff]
  refine and_congr_right fun _ => ?_
  have h2 : ((((y' i).val : ℤ) - ((yc i).val : ℤ) + e / (nn r : ℤ) : ℤ) : ZMod K) =
      y' i + ((e / (nn r : ℤ) : ℤ) : ZMod K) - yc i := by
    simp only [Int.cast_sub, Int.cast_add, Int.cast_natCast, ZMod.natCast_zmod_val]; ring
  rw [h2, sub_eq_zero]

/-- The bond `y_c + a₀p` lies on the path of `(y' + a₀w, t)` iff `y' = y_c`, `w = p - te_μ`, or `y' + e_μ = y_c`,
`w = p + (n - t)e_μ`. -/
lemma eq_iff {μ : Fin 4} {p w : Fin 4 → ℤ} (hp : p ∈ Iset r μ) (hw : w ∈ box r) {t : ℕ} (ht : t < nn r)
    (y' yc : Tor K) :
    emb r K y' + castw r K w + Pi.single μ ((t : ℕ) : ZMod (NN r K)) = pos r K yc p ↔
      (y' = yc ∧ w = p - Pi.single μ (t : ℤ)) ∨
        (y' + Pi.single μ 1 = yc ∧ w = p + Pi.single μ ((nn r : ℤ) - t)) := by
  rw [funext_iff]
  simp only [coord_iff]
  obtain ⟨hpμ, hpν⟩ := (mem_Iset r).1 hp
  have hwb := (mem_box r).1 hw
  have hn : (nn r : ℤ) = 2 * r + 1 := by push_cast; ring
  have hn0 : (nn r : ℤ) ≠ 0 := by positivity
  have ht' : (t : ℤ) < 2 * r + 1 := by have : t < 2 * r + 1 := ht; omega
  constructor
  · intro h
    have hoff : ∀ i, i ≠ μ → w i = p i ∧ y' i = yc i := by
      intro i hi
      obtain ⟨hd, hy⟩ := h i
      rw [if_neg hi] at hd hy
      have he : w i + 0 - p i = 0 := by
        refine Int.eq_zero_of_abs_lt_dvd hd ?_
        have := hwb i; have := hpν i hi
        rw [abs_lt]; constructor <;> omega
      rw [he, Int.zero_ediv] at hy
      simp only [Int.cast_zero, add_zero] at hy
      exact ⟨by omega, hy⟩
    obtain ⟨hd, hy⟩ := h μ
    rw [if_pos rfl] at hd hy
    obtain ⟨q, hq⟩ := hd
    have hwμ := hwb μ
    have hq1 : -1 < q := by
      by_contra hc; push_neg at hc
      have : (nn r : ℤ) * q ≤ -(nn r : ℤ) := by nlinarith
      omega
    have hq2 : q < 2 := by
      by_contra hc; push_neg at hc
      have : 2 * (nn r : ℤ) ≤ (nn r : ℤ) * q := by nlinarith
      omega
    rw [hq, mul_div_cancel_left₀ _ hn0] at hy
    rcases (show q = 0 ∨ q = 1 by omega) with rfl | rfl
    · left
      refine ⟨funext fun i => ?_, funext fun i => ?_⟩
      · by_cases hi : i = μ
        · subst hi; simpa using hy
        · exact (hoff i hi).2
      · by_cases hi : i = μ
        · subst hi; simp; omega
        · simp [hi]; exact (hoff i hi).1
    · right
      refine ⟨funext fun i => ?_, funext fun i => ?_⟩
      · by_cases hi : i = μ
        · subst hi; simpa using hy
        · simp [hi]; exact (hoff i hi).2
      · by_cases hi : i = μ
        · subst hi; simp; omega
        · simp [hi]; exact (hoff i hi).1
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) i
    · by_cases hi : i = μ
      · subst hi; simp
      · simp [hi]
    · by_cases hi : i = μ
      · subst hi
        have e : (p + Pi.single i ((nn r : ℤ) - t) : Fin 4 → ℤ) i + (if i = i then (t : ℤ) else 0) - p i = (nn r : ℤ) * 1 := by
          simp; ring
        rw [e, mul_div_cancel_left₀ _ hn0]
        simp
      · simp [hi]

lemma mem_box_sub {μ : Fin 4} {p : Fin 4 → ℤ} (hp : p ∈ Iset r μ) (t : ℕ) :
    p - Pi.single μ (t : ℤ) ∈ box r ↔ (t : ℤ) ≤ p μ + r := by
  obtain ⟨hpμ, hpν⟩ := (mem_Iset r).1 hp
  rw [mem_box]
  constructor
  · intro h; have := h μ; simp at this; omega
  · intro ht i
    by_cases hi : i = μ
    · subst hi; simp; omega
    · simp [hi]; exact hpν i hi

lemma mem_box_add {μ : Fin 4} {p : Fin 4 → ℤ} (hp : p ∈ Iset r μ) {t : ℕ} (ht : t < nn r) :
    p + Pi.single μ ((nn r : ℤ) - t) ∈ box r ↔ p μ + r + 1 ≤ (t : ℤ) := by
  obtain ⟨hpμ, hpν⟩ := (mem_Iset r).1 hp
  have ht' : (t : ℤ) < 2 * r + 1 := by have : t < 2 * r + 1 := ht; omega
  rw [mem_box]
  constructor
  · intro h; have := h μ; simp at this; push_cast at this; omega
  · intro ht i
    by_cases hi : i = μ
    · subst hi; simp; push_cast; omega
    · simp [hi]; exact hpν i hi

lemma count_le (k : ℤ) (hk0 : 0 ≤ k) (hk : k < 2 * r) :
    ∑ t ∈ range (nn r), (if (t : ℤ) ≤ k then (1 : ℝ) else 0) = k + 1 := by
  rw [sum_boole]
  have : (range (nn r)).filter (fun t : ℕ => (t : ℤ) ≤ k) = range (k.toNat + 1) := by
    ext t; simp only [mem_filter, mem_range]; unfold nn; omega
  rw [this, card_range]
  have h : ((k.toNat : ℕ) : ℤ) = k := Int.toNat_of_nonneg hk0
  push_cast
  exact_mod_cast congrArg (fun z : ℤ => (z : ℝ) + 1) h

lemma count_ge (k : ℤ) (hk0 : 0 ≤ k) (hk : k < 2 * r) :
    ∑ t ∈ range (nn r), (if k + 1 ≤ (t : ℤ) then (1 : ℝ) else 0) = 2 * r - k := by
  rw [sum_boole]
  have : (range (nn r)).filter (fun t : ℕ => k + 1 ≤ (t : ℤ)) = Ico (k.toNat + 1) (nn r) := by
    ext t; simp only [mem_filter, mem_range, mem_Ico]; unfold nn; omega
  rw [this, Nat.card_Ico]
  have h : ((k.toNat : ℕ) : ℤ) = k := Int.toNat_of_nonneg hk0
  have hle : k.toNat + 1 ≤ nn r := by unfold nn; omega
  rw [Nat.cast_sub hle]
  push_cast
  have h' : ((k.toNat : ℕ) : ℝ) = (k : ℝ) := by exact_mod_cast h
  rw [h']; ring

lemma ite_split {P A B C D : Prop} [Decidable P] [Decidable A] [Decidable B] [Decidable C] [Decidable D]
    (hP : P ↔ A ∧ B ∨ C ∧ D) (h : ¬(B ∧ D)) :
    (if P then (1 : ℝ) else 0) = (if A then (if B then 1 else 0) else 0) + (if C then (if D then 1 else 0) else 0) := by
  by_cases hA : A <;> by_cases hB : B <;> by_cases hC : C <;> by_cases hD : D <;> simp [hP, hA, hB, hC, hD] <;>
    exact h ⟨hB, hD⟩

/-- **The weights**: the bond `y_c + a₀p` enters the average of `(y', μ)` `m + h + 1` times if `y' = y_c` and `h - m`
times if `y' + e_μ = y_c`, `m = p_μ`, and in no other average of the direction `μ`. -/
lemma count_eq {μ : Fin 4} {p : Fin 4 → ℤ} (hp : p ∈ Iset r μ) (y' yc : Tor K) :
    ∑ w ∈ box r, ∑ t ∈ range (nn r),
      (if emb r K y' + castw r K w + Pi.single μ ((t : ℕ) : ZMod (NN r K)) = pos r K yc p then (1 : ℝ) else 0) =
      (if y' = yc then (p μ : ℝ) + r + 1 else 0) + (if y' + Pi.single μ 1 = yc then (r : ℝ) - p μ else 0) := by
  obtain ⟨hpμ, -⟩ := (mem_Iset r).1 hp
  have step : ∀ w ∈ box r, ∀ t ∈ range (nn r),
      (if emb r K y' + castw r K w + Pi.single μ ((t : ℕ) : ZMod (NN r K)) = pos r K yc p then (1 : ℝ) else 0) =
      (if y' = yc then (if w = p - Pi.single μ (t : ℤ) then 1 else 0) else 0) +
        (if y' + Pi.single μ 1 = yc then (if w = p + Pi.single μ ((nn r : ℤ) - t) then 1 else 0) else 0) := by
    intro w hw t ht
    rw [mem_range] at ht
    have hex : w = p - Pi.single μ (t : ℤ) → w ≠ p + Pi.single μ ((nn r : ℤ) - t) := by
      rintro rfl h
      have := congrFun h μ
      simp at this
      have : (0 : ℤ) < nn r := by positivity
      omega
    exact ite_split (eq_iff r K hp hw ht y' yc) (fun h => hex h.1 h.2)
  rw [sum_congr rfl fun w hw => sum_congr rfl fun t ht => step w hw t ht, sum_comm]
  have inner : ∀ t ∈ range (nn r), ∑ w ∈ box r,
      ((if y' = yc then (if w = p - Pi.single μ (t : ℤ) then (1 : ℝ) else 0) else 0) +
        (if y' + Pi.single μ 1 = yc then (if w = p + Pi.single μ ((nn r : ℤ) - t) then 1 else 0) else 0)) =
      (if y' = yc then (if (t : ℤ) ≤ p μ + r then 1 else 0) else 0) +
        (if y' + Pi.single μ 1 = yc then (if p μ + r + 1 ≤ (t : ℤ) then 1 else 0) else 0) := by
    intro t ht
    rw [mem_range] at ht
    rw [sum_add_distrib]
    congr 1
    · by_cases h1 : y' = yc
      · simp only [if_pos h1]; rw [sum_ite_eq']; exact if_congr (mem_box_sub r hp t) rfl rfl
      · simp only [if_neg h1, sum_const_zero]
    · by_cases h1 : y' + Pi.single μ 1 = yc
      · simp only [if_pos h1]; rw [sum_ite_eq']; exact if_congr (mem_box_add r hp ht) rfl rfl
      · simp only [if_neg h1, sum_const_zero]
  rw [sum_congr rfl inner, sum_add_distrib]
  have hk0 : 0 ≤ p μ + r := by omega
  have hk : p μ + r < 2 * r := by omega
  congr 1
  · split_ifs
    · rw [count_le r _ hk0 hk]; push_cast; ring
    · simp
  · split_ifs
    · have := count_ge r _ hk0 hk
      rw [show p μ + r + 1 = (p μ + r) + 1 by ring, this]; push_cast; ring
    · simp

/-- `Σ_pg(s(p_μ))ψ(p_⊥)W(p_μ) = (Σ_mg(s(m))W(m))Ψ`. -/
lemma sum_coef (μ : Fin 4) (side : Bool) (W : ℤ → ℝ) :
    ∑ p ∈ Iset r μ, coef r μ side p * W (p μ) =
      (∑ m ∈ Icc (-(r : ℤ)) (r - 1), g (nn r) (Kc r) (sOf r side m) * W m) * Sbeta r ^ 3 := by
  set G : Fin 4 → ℤ → ℝ := fun ν t => if ν = μ then g (nn r) (Kc r) (sOf r side t) * W t else beta r t with hG
  have h1 : ∀ p : Fin 4 → ℤ, coef r μ side p * W (p μ) = ∏ ν, G ν (p ν) := by
    intro p
    unfold coef
    rw [Fintype.prod_eq_mul_prod_compl μ, Fintype.prod_eq_mul_prod_compl μ (fun ν => G ν (p ν))]
    have : ∏ ν ∈ ({μ}ᶜ : Finset (Fin 4)), F r μ side ν (p ν) = ∏ ν ∈ ({μ}ᶜ : Finset (Fin 4)), G ν (p ν) := by
      refine prod_congr rfl fun ν hν => ?_
      have : ν ≠ μ := by simpa using hν
      simp [F, hG, this]
    rw [this]; simp only [F, hG, ↓reduceIte]; ring
  simp only [h1]
  unfold Iset
  rw [← prod_univ_sum, Fintype.prod_eq_mul_prod_compl μ]
  simp only [hG, if_pos rfl]
  congr 1
  rw [prod_congr rfl fun ν hν => (show (∑ t ∈ (if ν = μ then Icc (-(r : ℤ)) (r - 1) else Icc (-(r : ℤ)) r),
      (if ν = μ then g (nn r) (Kc r) (sOf r side t) * W t else beta r t)) = Sbeta r by
    have : ν ≠ μ := by simpa using hν
    simp only [if_neg this]; exact sum_beta r), prod_const]
  simp [card_compl]

lemma fA0 : (fun s : ℤ => (s : ℝ) * g (nn r) (Kc r) s) 0 = 0 := by simp

lemma fAn : (fun s : ℤ => (s : ℝ) * g (nn r) (Kc r) s) (nn r) = 0 := by
  beta_reduce; rw [g_out _ (by unfold nn; omega) (Or.inr le_rfl), mul_zero]

lemma fB0 : (fun s : ℤ => ((nn r : ℝ) - s) * g (nn r) (Kc r) s) 0 = 0 := by
  beta_reduce; rw [g_out _ (by unfold nn; omega) (Or.inl le_rfl), mul_zero]

lemma fBn : (fun s : ℤ => ((nn r : ℝ) - s) * g (nn r) (Kc r) s) (nn r) = 0 := by simp

lemma sumA (hr : 1 ≤ r) (side : Bool) :
    ∑ m ∈ Icc (-(r : ℤ)) (r - 1), g (nn r) (Kc r) (sOf r side m) * ((m : ℝ) + r + 1) =
      if side then 0 else Kc r := by
  have hn3 : 3 ≤ nn r := by unfold nn; omega
  cases side
  · rw [if_neg (by simp)]
    rw [sum_congr rfl (fun m _ => (show g (nn r) (Kc r) (sOf r false m) * ((m : ℝ) + r + 1) =
        (fun s : ℤ => (s : ℝ) * g (nn r) (Kc r) s) (sOf r false m) by simp only [sOf]; push_cast; ring))]
    exact (sum_sOf r false (fun s : ℤ => (s : ℝ) * g (nn r) (Kc r) s) (fA0 r) (fAn r)).trans (sum_s_g _ hn3)
  · rw [if_pos rfl]
    rw [sum_congr rfl (fun m _ => (show g (nn r) (Kc r) (sOf r true m) * ((m : ℝ) + r + 1) =
        (fun s : ℤ => ((nn r : ℝ) - s) * g (nn r) (Kc r) s) (sOf r true m) by simp only [sOf]; push_cast; ring))]
    exact (sum_sOf r true (fun s : ℤ => ((nn r : ℝ) - s) * g (nn r) (Kc r) s) (fB0 r) (fBn r)).trans (sum_ns_g _ hn3)

lemma sumB (hr : 1 ≤ r) (side : Bool) :
    ∑ m ∈ Icc (-(r : ℤ)) (r - 1), g (nn r) (Kc r) (sOf r side m) * ((r : ℝ) - m) =
      if side then Kc r else 0 := by
  have hn3 : 3 ≤ nn r := by unfold nn; omega
  cases side
  · rw [if_neg (by simp)]
    rw [sum_congr rfl (fun m _ => (show g (nn r) (Kc r) (sOf r false m) * ((r : ℝ) - m) =
        (fun s : ℤ => ((nn r : ℝ) - s) * g (nn r) (Kc r) s) (sOf r false m) by simp only [sOf]; push_cast; ring))]
    exact (sum_sOf r false (fun s : ℤ => ((nn r : ℝ) - s) * g (nn r) (Kc r) s) (fB0 r) (fBn r)).trans (sum_ns_g _ hn3)
  · rw [if_pos rfl]
    rw [sum_congr rfl (fun m _ => (show g (nn r) (Kc r) (sOf r true m) * ((r : ℝ) - m) =
        (fun s : ℤ => (s : ℝ) * g (nn r) (Kc r) s) (sOf r true m) by simp only [sOf]; push_cast; ring))]
    exact (sum_sOf r true (fun s : ℤ => (s : ℝ) * g (nn r) (Kc r) s) (fA0 r) (fAn r)).trans (sum_s_g _ hn3)

/-- `Q_j(id)` on real forms. -/
def Qr (A : Fin 4 → Tor (NN r K) → ℝ) (μ : Fin 4) (y : Tor K) : ℝ :=
  (((nn r : ℕ) : ℝ) ^ 4)⁻¹ * ∑ w ∈ box r, (((nn r : ℕ) : ℝ)⁻¹ *
    ∑ t ∈ range (nn r), A μ (emb r K y + castw r K w + Pi.single μ ((t : ℕ) : ZMod (NN r K))))

lemma Qop_real (A : Fin 4 → Tor (NN r K) → ℝ) (μ : Fin 4) (y : Tor K) :
    Qop r K (fun ν x => (A ν x : ℂ)) μ y = (Qr r K A μ y : ℂ) := by
  unfold Qop Qr; push_cast; rfl

/-- The lower end `c₋` of `c`: `y_c` or `y_c - e_μ`. -/
def cminus (μ : Fin 4) (side : Bool) (yc : Tor K) : Tor K := if side then yc - Pi.single μ 1 else yc

/-- **`lem:bumps`(iii)**: `Q_j(id)φ_c` is the indicator function of `c`. -/
theorem bump_average_real (hr : 1 ≤ r) (μ : Fin 4) (side : Bool) (yc : Tor K) (μ' : Fin 4) (y' : Tor K) :
    Qr r K (phiR r K μ side yc) μ' y' = if μ' = μ ∧ y' = cminus K μ side yc then 1 else 0 := by
  by_cases hμ : μ' = μ
  · subst hμ
    have hn : (0 : ℝ) < ((nn r : ℕ) : ℝ) := by positivity
    have h1 : ∀ x : Tor (NN r K), phiR r K μ' side yc μ' x =
        ∑ p ∈ Iset r μ', coef r μ' side p * (if x = pos r K yc p then 1 else 0) := by
      intro x; unfold phiR; rw [if_pos rfl]
      refine sum_congr rfl fun p _ => ?_
      split_ifs <;> simp
    have h2 : Qr r K (phiR r K μ' side yc) μ' y' = ((((nn r : ℕ) : ℝ) ^ 5)⁻¹) *
        ∑ p ∈ Iset r μ', coef r μ' side p * ∑ w ∈ box r, ∑ t ∈ range (nn r),
          (if emb r K y' + castw r K w + Pi.single μ' ((t : ℕ) : ZMod (NN r K)) = pos r K yc p then (1 : ℝ) else 0) := by
      unfold Qr
      simp only [h1]
      rw [← mul_sum, show ((((nn r : ℕ) : ℝ) ^ 5)⁻¹) = (((nn r : ℕ) : ℝ) ^ 4)⁻¹ * ((nn r : ℕ) : ℝ)⁻¹ by
        field_simp, mul_assoc]
      congr 2
      simp_rw [mul_sum]
      rw [sum_congr rfl fun w _ => sum_comm, sum_comm]
    rw [h2, sum_congr rfl fun p hp => by rw [count_eq r K hp y' yc]]
    have h3 : ∑ p ∈ Iset r μ', coef r μ' side p *
        ((if y' = yc then (p μ' : ℝ) + r + 1 else 0) + (if y' + Pi.single μ' 1 = yc then (r : ℝ) - p μ' else 0)) =
        (if y' = yc then (if side then 0 else Kc r) * Sbeta r ^ 3 else 0) +
          (if y' + Pi.single μ' 1 = yc then (if side then Kc r else 0) * Sbeta r ^ 3 else 0) := by
      rw [← sumA r hr side, ← sumB r hr side, ← sum_coef r μ' side (fun m => (m : ℝ) + r + 1),
        ← sum_coef r μ' side (fun m => (r : ℝ) - m)]
      split_ifs <;> simp [mul_add, sum_add_distrib]
    rw [h3]
    have hKS : Kc r * Sbeta r ^ 3 = ((nn r : ℕ) : ℝ) ^ 5 := by
      unfold Kc; rw [show Sbeta r ^ 3 = Psi r from rfl]
      field_simp [(Psi_pos r hr).ne']
    rcases side with _ | _
    · simp only [Bool.false_eq_true, if_false, zero_mul, ite_self, add_zero, cminus, true_and, hKS]
      split_ifs
      · exact inv_mul_cancel₀ (pow_ne_zero _ hn.ne')
      · simp
    · simp only [if_true, zero_mul, ite_self, zero_add, cminus, true_and, hKS, eq_sub_iff_add_eq]
      split_ifs
      · exact inv_mul_cancel₀ (pow_ne_zero _ hn.ne')
      · simp
  · rw [if_neg (fun h => hμ h.1)]
    unfold Qr
    simp [phiR_off r K side yc _ hμ]

/-- **`lem:bumps`(iii)**, with a coefficient: `(Q_j(id)(φ_cZ))(c') = Z` if `c' = c` and `0` otherwise (for
`Z ∈ 𝔤^c`, componentwise in a basis). -/
theorem bump_average (hr : 1 ≤ r) (μ : Fin 4) (side : Bool) (yc : Tor K) (Z : ℂ) (μ' : Fin 4) (y' : Tor K) :
    Qop r K (fun ν x => (phiR r K μ side yc ν x : ℂ) * Z) μ' y' =
      if μ' = μ ∧ y' = cminus K μ side yc then Z else 0 := by
  have h : Qop r K (fun ν x => (phiR r K μ side yc ν x : ℂ) * Z) μ' y' =
      Qop r K (fun ν x => (phiR r K μ side yc ν x : ℂ)) μ' y' * Z := by
    simp only [Qop, ← sum_mul, ← mul_assoc]
  rw [h, Qop_real, bump_average_real r K hr]
  split_ifs <;> simp

/-! ### The scale `j = 0` -/

lemma box_zero : box 0 = {0} := by
  ext w
  rw [mem_box, mem_singleton, funext_iff]
  simp only [Nat.cast_zero, neg_zero, Pi.zero_apply]
  exact forall_congr' fun i => ⟨fun h => le_antisymm h.2 h.1, fun h => ⟨h.ge, h.le⟩⟩

/-- For `j = 0` (`r = 0`) the average `Q_0` is the identity. -/
lemma Qop_zero (A : Fin 4 → Tor (NN 0 K) → ℂ) (μ : Fin 4) (y : Tor K) : Qop 0 K A μ y = A μ (emb 0 K y) := by
  have h0 : castw 0 K 0 = 0 := by funext i; simp [castw]
  unfold Qop
  rw [box_zero]
  simp [h0]

lemma emb_zero_inj {y y' : Tor K} (h : emb 0 K y = emb 0 K y') : y = y' := by
  funext i
  have h1 := congrFun h i
  simp only [emb, Nat.mul_zero, Nat.zero_add, Nat.cast_one, one_mul] at h1
  have h2 := congrArg ZMod.val h1
  have hK : NN 0 K = K := by unfold NN; ring
  rw [ZMod.val_natCast, ZMod.val_natCast, hK, Nat.mod_eq_of_lt (ZMod.val_lt _),
    Nat.mod_eq_of_lt (ZMod.val_lt _)] at h2
  exact ZMod.val_injective _ h2

/-- **`lem:bumps`**, `j = 0`: the indicator function of `c` has the property (iii). -/
theorem bump_zero (μ : Fin 4) (c : Tor K) (μ' : Fin 4) (y' : Tor K) :
    Qop 0 K (fun ν x => if ν = μ ∧ x = emb 0 K c then 1 else 0) μ' y' = if μ' = μ ∧ y' = c then 1 else 0 := by
  rw [Qop_zero]
  have : emb 0 K y' = emb 0 K c ↔ y' = c := ⟨emb_zero_inj K, fun h => h ▸ rfl⟩
  simp only [this]

end BumpField
end CoreLean

end
