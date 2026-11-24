/-
`lem:sf-local` of BALABAN_CORE.tex (`4252790331fd`), the step "The rescaled equation": the equation
`Δ_𝐔u = f + D^*_𝐔g + 𝒵u + 𝒩u` in the coordinates of the layer as an instance of `eq:local-equation`, and the norms of
its local operators.

* `lip_box`: in a box `Q_ρ`, a function whose differences along the bonds of the box are at most `B` changes by at most
  `B|n' - n|₁` (along a shortest path, which stays in the box).
* `SFData`: `u`, `f`, `g_μ`, the coefficients `Z_e(n)` of `𝒵`, and `𝒩u`; `toLData`: `h = f + Σ_μK'_μg_μ(· - e_μ) + 𝒩u`,
  `c = 𝒵 - 𝒞`, `𝒢'_μ = -𝒢_μ`; `eqn_of`: `eq:local-equation` at a point where the equation holds.
* `FieldHyp`: `‖Ã‖ ≤ α₁L`, `‖Ã(n + e_ν) - Ã(n)‖ ≤ εα₁L²` on `Q_{8+2L}`, `64L²α₁ ≤ 1`, `L ≥ 3`, `ε ≤ 1/3`;
  `norm_c_le`, `norm_G_le`, `lip_G`: the norms of the local operators at the points of `Q_8` (at most `1`) and the
  Lipschitz constant of `𝒢'_μ` on `Q_8` (at most `1`), when `Σ_e‖Z_e‖ ≤ 1/4`.
-/
import CoreLean.SFLocalOps
import CoreLean.InteriorRemainder

open Finset Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace CoreLean
namespace SFLocal

open LocalLaplacian InteriorSchauder

variable {N m : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ

variable {ε : ℝ} {n₀ : Fin 4 → ℤ}

lemma inQr_of_inBox (hε : 0 < ε) {ρ : ℝ} {x x' : Fin 4 → ℤ} (hx : InQr ε n₀ ρ x) (hx' : InQr ε n₀ ρ x')
    {s : Fin 4 → ℤ} {c : Fin 4 → ℕ} (hend : ∀ μ, x μ + s μ * c μ = x' μ) {p : Fin 4 → ℤ} (hp : InteriorSchauder.InBox x s c p) :
    InQr ε n₀ ρ p := fun μ => by
  obtain ⟨h1, h2⟩ := hp μ
  rw [hend μ] at h1 h2
  have a1 := abs_le.1 (hx μ)
  have a2 := abs_le.1 (hx' μ)
  unfold tc at a1 a2 ⊢
  have hlo : ((min (x μ) (x' μ) : ℤ) : ℝ) ≤ p μ := by exact_mod_cast h1
  have hhi : (p μ : ℝ) ≤ ((max (x μ) (x' μ) : ℤ) : ℝ) := by exact_mod_cast h2
  push_cast at a1 a2 hlo hhi ⊢
  rw [abs_le]
  constructor
  · rcases min_choice (x μ : ℝ) (x' μ) with h | h <;> rw [h] at hlo <;> nlinarith
  · rcases max_choice (x μ : ℝ) (x' μ) with h | h <;> rw [h] at hhi <;> nlinarith

/-- **The Lipschitz bound in a box.** -/
theorem lip_box {F : Type*} [SeminormedAddCommGroup F] (hε : 0 < ε) {ρ B : ℝ} {g : (Fin 4 → ℤ) → F}
    (hg : ∀ k ν, InQr ε n₀ ρ k → InQr ε n₀ ρ (k + e4 ν) → ‖g (k + e4 ν) - g k‖ ≤ B)
    {n n' : Fin 4 → ℤ} (hn : InQr ε n₀ ρ n) (hn' : InQr ε n₀ ρ n') : ‖g n' - g n‖ ≤ B * l1 (n' - n) := by
  obtain ⟨l, hl⟩ := exists_shortest n n'
  have h0 : ∀ μ, sgnv n n' μ = 0 → l.count μ = 0 := fun μ h => by
    rw [hl μ]; unfold sgnv at h; rw [Int.sign_eq_zero_iff_zero] at h; rw [h]; rfl
  have hbox := walkIn_box (sgnv n n') (sgnv_cases n n') l n h0
  have hend : ∀ μ, n μ + sgnv n n' μ * (l.count μ : ℤ) = n' μ := fun μ => by
    rw [hl μ, sgnv, Int.natCast_natAbs, Int.sign_mul_abs]; ring
  have hw : WalkIn (sgnv n n') (fun p μ => ‖g (p + sgnv n n' μ • e4 μ) - g p‖ ≤ B) n l := by
    refine WalkIn.mono (fun p μ ⟨h1, h2, h3⟩ => ?_) l n hbox
    have q1 := inQr_of_inBox hε hn hn' hend h1
    have q2 := inQr_of_inBox hε hn hn' hend h2
    rcases sgnv_cases n n' μ with hs | hs | hs
    · rw [hs, one_smul] at q2 ⊢; exact hg p μ q1 q2
    · rw [hs, neg_one_smul, ← sub_eq_add_neg] at q2 ⊢
      rw [norm_sub_rev]
      have := hg (p - e4 μ) μ q2 (by rwa [sub_add_cancel])
      rwa [sub_add_cancel] at this
    · exact absurd hs h3
  have := norm_sub_le_walk (sgnv n n') g l n hw
  rwa [walkEnd_shortest hl, length_eq_l1 hl] at this

/-! ### The data -/

/-- The data of `lem:sf-local` in the coordinates of the layer. -/
structure SFData (N m : ℕ) where
  u : (Fin 4 → ℤ) → VS N m
  f : (Fin 4 → ℤ) → VS N m
  g : Fin 4 → (Fin 4 → ℤ) → VS N m
  Z : (Fin 4 → ℤ) → (Fin 4 → ℤ) → (VS N m →L[ℝ] VS N m)
  Nu : (Fin 4 → ℤ) → VS N m

/-- The coefficients of `𝒢'_μ = -𝒢_μ`: `-K_μ(n)` at `e_μ` and `K''_μ(n) = K'_μ(n + e_μ)` at `0`. -/
def Gc (ε : ℝ) (A : Fin 4 → (Fin 4 → ℤ) → Mat) (μ : Fin 4) (n e : Fin 4 → ℤ) : VS N m →L[ℝ] VS N m :=
  if e = e4 μ then -Kf ε A μ n else if e = 0 then Kb ε A μ (n + e4 μ) else 0

/-- The data of `eq:local-equation`. -/
def toLData (ε : ℝ) (A : Fin 4 → (Fin 4 → ℤ) → Mat) (D : SFData N m) : LData (VS N m) where
  u := D.u
  h n := D.f n + ∑ μ, Kb ε A μ n (D.g μ (n - e4 μ)) + D.Nu n
  g := D.g
  c n e := D.Z n e - if e = 0 then Cop ε A n else 0
  G := Gc ε A

lemma e4_ne_zero (μ : Fin 4) : e4 μ ≠ 0 := fun h => by
  have := congrFun h μ; simp [e4] at this

lemma locApp_Gc (ε : ℝ) (A : Fin 4 → (Fin 4 → ℤ) → Mat) (μ : Fin 4) (u : (Fin 4 → ℤ) → VS N m) (n : Fin 4 → ℤ) :
    locApp (Gc ε A μ) u n = -Gop ε A μ u n := by
  unfold locApp
  rw [sum_eq_add (e4 μ) 0 (e4_ne_zero μ) (fun e _ he => by simp [Gc, he.1, he.2])
    (fun h => absurd (e4_mem μ) h) (fun h => absurd zero_mem_Eoff h)]
  simp [Gc, Gop, (e4_ne_zero μ).symm]
  abel

lemma locApp_c (ε : ℝ) (A : Fin 4 → (Fin 4 → ℤ) → Mat) (D : SFData N m) (u : (Fin 4 → ℤ) → VS N m) (n : Fin 4 → ℤ) :
    locApp (toLData ε A D).c u n = locApp D.Z u n - Cop ε A n (u n) := by
  have hc : ∀ e, (toLData ε A D).c n e = D.Z n e - (if e = 0 then Cop ε A n else 0) := fun e => rfl
  have h0 : ∑ e ∈ Eoff, (if e = 0 then Cop ε A n else 0) (u (n + e)) = Cop ε A n (u n) := by
    rw [sum_eq_single 0 (fun e _ he => by simp [he]) (fun h => absurd zero_mem_Eoff h)]
    simp
  simp only [locApp, hc, ContinuousLinearMap.sub_apply, sum_sub_distrib, h0]

lemma DbwV_eq (ε : ℝ) (A : Fin 4 → (Fin 4 → ℤ) → Mat) (μ : Fin 4) (v : (Fin 4 → ℤ) → VS N m) (n : Fin 4 → ℤ) :
    DbwV ε A μ v n = dbw ε μ v n + Kb ε A μ n (v (n - e4 μ)) := by
  simp only [DbwV, dbw, KV_apply]; module

/-- **The rescaled equation**: `Δ_𝐔u = f + D^*_𝐔g + 𝒵u + 𝒩u` at `n` gives `eq:local-equation` at `n`. -/
theorem eqn_of (ε : ℝ) (A : Fin 4 → (Fin 4 → ℤ) → Mat) (D : SFData N m) (hε : ε ≠ 0) {n : Fin 4 → ℤ}
    (h : covLapV ε A D.u n = D.f n + ∑ μ, DbwV ε A μ (D.g μ) n + locApp D.Z D.u n + D.Nu n) :
    lap ε D.u n = (toLData ε A D).h n + locApp (toLData ε A D).c D.u n +
      ∑ μ, dbw ε μ (vf (toLData ε A D) μ) n := by
  have hd := covLapV_eq ε A hε D.u n
  have hv : ∀ μ, vf (toLData ε A D) μ = fun k => D.g μ k - Gop ε A μ D.u k := fun μ => by
    funext k; simp only [vf, toLData, locApp_Gc, sub_eq_add_neg]
  simp only [hv, locApp_c, DbwV_eq] at h ⊢
  have hsub : ∀ μ, dbw ε μ (fun k => D.g μ k - Gop ε A μ D.u k) n = dbw ε μ (D.g μ) n - dbw ε μ (Gop ε A μ D.u) n :=
    fun μ => by simp only [dbw]; module
  simp only [hsub, sum_sub_distrib, sum_add_distrib] at h ⊢
  simp only [toLData]
  rw [hd] at h
  linear_combination (norm := module) h

end SFLocal
end CoreLean

end
