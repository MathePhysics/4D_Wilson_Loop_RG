/-
`prop:interior-schauder` of BALABAN_CORE.tex (`a71f8998da10`): an interior estimate for the covariant Laplacian.

The proof is the core's ("the proof of `prop:schauder` from its second step on"): the localised function
`w = χv` solves `(Δ + a⁻²)w = Σ_κ∂^*_κ(χλ_κ) + r` (`InteriorRemainder.lean`); in the units of `a`
(spacing `ε = η/a = 1/K`) the operator `Δ + a⁻²` is `a⁻²(Δ_ε + 1)`, whose inverse on the bounded functions is the
resolvent `G₁` of `prop:free-schauder` (`eq_resolvent`), so that
`w = Σ_κ a∂^*_κG₁(χλ_κ) + a²G₁r` (`w_eq`). On the set `S = {|x - y|_∞ ≤ 2a - η}`, where `χ = 1`,
`D_{𝐔,ν}v = Σ_κ∂_ν∂^*_κG₁(χλ_κ) + a∂_νG₁r + E_νv` with `E_νv = (D_{𝐔,ν} - ∂_ν)v` (`Dfw_eq_Phi`), and the three
terms have the moduli `6C_S(β)Λ_κ`, `C'_S(β)(5ΣΛ + 166V)` (`eq:free-second`, `eq:free-first`), and `V`
(`norm_E_walk_le`); the transport along a shortest path changes a value of `D_{𝐔,ν}v` by at most
`V(|z|₁/a)^β` (`path_dev`).

* `interior_schauder`: `‖Ad_{𝐔(γ)}(D_{𝐔,ν}v)(x') - (D_{𝐔,ν}v)(x)‖ ≤ C_I(β)(V + Σ_κΛ_κ)(|x - x'|₁/a)^β` for
  `x, x' ∈ S`, `|x - x'|₁ ≤ a`, every shortest path `γ` and every `ν`, with
  `C_I(β) = 6C_S(β) + 166C'_S(β) + 2`: the proposition with the sum `Σ_κD^*_{𝐔,κ}λ_κ` of its last statement
  (the case of one `μ` is `λ_κ = 0` for `κ ≠ μ`); the families of `0`-forms are treated member by member.
-/
import CoreLean.InteriorRemainder

open Matrix NormedSpace
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace CoreLean
namespace InteriorSchauder

variable {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "GLN" => (Matrix (Fin N) (Fin N) ℂ)ˣ

/-- `C_I(β) = 6C_S(β) + 166C'_S(β) + 2`. -/
def CI (β : ℝ) : ℝ := 6 * CS β + 166 * CS' β + 2

/-! ### Linearity of the differences, the Laplacian, and the resolvent -/

section Linear

variable {ε : ℝ}

lemma lap_add' (f g : (Fin 4 → ℤ) → Matrix (Fin N) (Fin N) ℂ) (n : Fin 4 → ℤ) :
    lap ε (fun m => f m + g m) n = lap ε f n + lap ε g n := by
  rw [lap_eq, lap_eq, lap_eq, ← smul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun μ _ => ?_
  module

lemma lap_smul' (c : ℝ) (f : (Fin 4 → ℤ) → Matrix (Fin N) (Fin N) ℂ) (n : Fin 4 → ℤ) :
    lap ε (fun m => c • f m) n = c • lap ε f n := by
  rw [lap_eq, lap_eq, Finset.smul_sum, Finset.smul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  module

lemma lap_sum' (s : Finset (Fin 4)) (g : Fin 4 → (Fin 4 → ℤ) → Matrix (Fin N) (Fin N) ℂ) (n : Fin 4 → ℤ) :
    lap ε (fun m => ∑ κ ∈ s, g κ m) n = ∑ κ ∈ s, lap ε (g κ) n := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    rw [lap_eq]; simp
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    rw [lap_add' (g a) (fun m => ∑ κ ∈ s, g κ m), ih]

lemma lap_dbw (κ : Fin 4) (f : (Fin 4 → ℤ) → Matrix (Fin N) (Fin N) ℂ) (n : Fin 4 → ℤ) :
    lap ε (dbw ε κ f) n = dbw ε κ (lap ε f) n := by
  unfold dbw
  rw [lap_eq, lap_eq, lap_eq, ← smul_sub, ← Finset.sum_sub_distrib, Finset.smul_sum, Finset.smul_sum,
    Finset.smul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [show n + e4 μ - e4 κ = n - e4 κ + e4 μ by abel, show n - e4 μ - e4 κ = n - e4 κ - e4 μ by abel]
  module

lemma dif_sum' (b : Bool) (μ : Fin 4) (g : Fin 4 → (Fin 4 → ℤ) → Matrix (Fin N) (Fin N) ℂ)
    (n : Fin 4 → ℤ) : dif ε b μ (fun m => ∑ κ, g κ m) n = ∑ κ, dif ε b μ (g κ) n := by
  cases b <;> simp [dif, dbw, dfw, Finset.smul_sum, ← Finset.sum_sub_distrib]

lemma dif_add' (b : Bool) (μ : Fin 4) (f g : (Fin 4 → ℤ) → Matrix (Fin N) (Fin N) ℂ) (n : Fin 4 → ℤ) :
    dif ε b μ (fun m => f m + g m) n = dif ε b μ f n + dif ε b μ g n := by
  cases b <;> · simp only [dif, dbw, dfw, Bool.false_eq_true, ↓reduceIte]; module

lemma dif_smul' (b : Bool) (μ : Fin 4) (c : ℝ) (f : (Fin 4 → ℤ) → Matrix (Fin N) (Fin N) ℂ)
    (n : Fin 4 → ℤ) : dif ε b μ (fun m => c • f m) n = c • dif ε b μ f n := by
  cases b <;> · simp only [dif, dbw, dfw, Bool.false_eq_true, ↓reduceIte]; module

lemma norm_dbw_le {f : (Fin 4 → ℤ) → Matrix (Fin N) (Fin N) ℂ} {M : ℝ} (hf : ∀ n, ‖f n‖ ≤ M) (hε : 0 < ε)
    (κ : Fin 4) (n : Fin 4 → ℤ) : ‖dbw ε κ f n‖ ≤ ε⁻¹ * (2 * M) := by
  unfold dbw
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hε.le)]
  refine mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (by linarith [hf (n - e4 κ), hf n]))
    (inv_nonneg.2 hε.le)

/-- `G₁(cf) = cG₁f`, by the uniqueness of the bounded solutions. -/
lemma resolvent_smul (hε : 0 < ε) (c : ℝ) {f : (Fin 4 → ℤ) → Matrix (Fin N) (Fin N) ℂ} {M : ℝ}
    (hf : ∀ n, ‖f n‖ ≤ M) : resolvent ε (fun m => c • f m) = fun n => c • resolvent ε f n := by
  symm
  refine eq_resolvent hε (M := |c| * M) (fun n => ?_) (B := |c| * M) (fun n => ?_) (fun n => ?_)
  · rw [norm_smul, Real.norm_eq_abs]; exact mul_le_mul_of_nonneg_left (hf n) (abs_nonneg c)
  · rw [norm_smul, Real.norm_eq_abs]; exact mul_le_mul_of_nonneg_left (norm_resolvent_le hf n) (abs_nonneg c)
  · rw [lap_smul', ← smul_add, lap_resolvent_add hε hf n]

end Linear

/-! ### The comparison -/

namespace Hyp

variable {η : ℝ} {K : ℕ} {y : Fin 4 → ℤ} {A : Fin 4 → (Fin 4 → ℤ) → Matrix (Fin N) (Fin N) ℂ}
  {v : (Fin 4 → ℤ) → Matrix (Fin N) (Fin N) ℂ} {lam : Fin 4 → (Fin 4 → ℤ) → Matrix (Fin N) (Fin N) ℂ}
  {rho : (Fin 4 → ℤ) → Matrix (Fin N) (Fin N) ℂ} {V : ℝ} {Λ : Fin 4 → ℝ} {β : ℝ}
  (H : Hyp η K y A v lam rho V Λ β)
include H

lemma ε_pos : (0 : ℝ) < (K : ℝ)⁻¹ := inv_pos.2 H.K_pos

/-- `Δ_η = a⁻²Δ_ε` with `ε = 1/K`. -/
lemma lap_scale (f : (Fin 4 → ℤ) → Matrix (Fin N) (Fin N) ℂ) (n : Fin 4 → ℤ) :
    lap (K : ℝ)⁻¹ f n = (K * η) ^ 2 • lap η f n := by
  rw [lap_eq, lap_eq, smul_smul]
  congr 1
  have := H.hη.ne'; have := H.K_pos.ne'; field_simp

/-- `∂^*_η = a⁻¹∂^*_ε`. -/
lemma dbw_scale (κ : Fin 4) (f : (Fin 4 → ℤ) → Matrix (Fin N) (Fin N) ℂ) (n : Fin 4 → ℤ) :
    (K * η) • dbw (K : ℝ)⁻¹ κ f n = (K * η) ^ 2 • dbw η κ f n := by
  unfold dbw; rw [smul_smul, smul_smul]; congr 1
  have := H.hη.ne'; have := H.K_pos.ne'; field_simp

lemma dfw_scale (ν : Fin 4) (f : (Fin 4 → ℤ) → Matrix (Fin N) (Fin N) ℂ) (n : Fin 4 → ℤ) :
    dfw η ν f n = (K * η)⁻¹ • dfw (K : ℝ)⁻¹ ν f n := by
  unfold dfw; rw [smul_smul]; congr 1
  have := H.hη.ne'; have := H.K_pos.ne'; field_simp

/-- The bound of the remainder, as a function. -/
lemma hrem : ∀ n, ‖rem η K y v lam n‖ ≤ (5 * ∑ κ, Λ κ + 166 * V) / (K * η) := fun n => H.norm_rem_le n

/-- **The comparison**: `w = Σ_κ a∂^*_κG₁(χλ_κ) + a²G₁r`, `G₁` the resolvent for the spacing `ε = 1/K`. -/
theorem w_eq : wloc K y v = fun n => ∑ κ, (K * η) • dbw (K : ℝ)⁻¹ κ (resolvent (K : ℝ)⁻¹ (chiLam K y lam κ)) n +
    (K * η) ^ 2 • resolvent (K : ℝ)⁻¹ (rem η K y v lam) n := by
  have hε := H.ε_pos
  set ε := (K : ℝ)⁻¹ with hεdef
  set a := (K : ℝ) * η with hadef
  set Mr := (5 * ∑ κ, Λ κ + 166 * V) / (K * η) with hMr
  set F : (Fin 4 → ℤ) → Matrix (Fin N) (Fin N) ℂ :=
    fun n => ∑ κ, a • dbw ε κ (chiLam K y lam κ) n + a ^ 2 • rem η K y v lam n with hF
  have hFb : ∀ n, ‖F n‖ ≤ ∑ κ, |a| * (ε⁻¹ * (2 * Λ κ)) + |a ^ 2| * Mr := fun n => by
    refine (norm_add_le _ _).trans (add_le_add ((norm_sum_le _ _).trans (Finset.sum_le_sum fun κ _ => ?_)) ?_)
    · rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (norm_dbw_le (H.norm_chiLam_le κ) hε κ n) (abs_nonneg _)
    · rw [norm_smul, Real.norm_eq_abs]; exact mul_le_mul_of_nonneg_left (H.hrem n) (abs_nonneg _)
  -- `w` solves `(Δ_ε + 1)w = F`
  have hw : wloc K y v = resolvent ε F := by
    refine eq_resolvent hε (fun n => hFb n) (B := V * a) (fun n => H.norm_wloc_le n) fun n => ?_
    rw [H.lap_scale, hF]
    simp only
    have hr : lap η (wloc K y v) n + ((K * η) ^ 2)⁻¹ • wloc K y v n =
        rem η K y v lam n + ∑ κ, dbw η κ (chiLam K y lam κ) n := by unfold rem; abel
    have ha2 : (K * η) ^ 2 ≠ 0 := by have := H.a_pos; positivity
    calc (K * η) ^ 2 • lap η (wloc K y v) n + wloc K y v n
        = (K * η) ^ 2 • (lap η (wloc K y v) n + ((K * η) ^ 2)⁻¹ • wloc K y v n) := by
          rw [smul_add, smul_smul, mul_inv_cancel₀ ha2, one_smul]
      _ = (K * η) ^ 2 • (rem η K y v lam n + ∑ κ, dbw η κ (chiLam K y lam κ) n) := by rw [hr]
      _ = ∑ κ, a • dbw ε κ (chiLam K y lam κ) n + a ^ 2 • rem η K y v lam n := by
          rw [smul_add, Finset.smul_sum, add_comm]
          congr 1
          exact Finset.sum_congr rfl fun κ _ => (H.dbw_scale κ _ n).symm
  -- the right side solves the same equation
  have hu : (fun n => ∑ κ, a • dbw ε κ (resolvent ε (chiLam K y lam κ)) n +
      a ^ 2 • resolvent ε (rem η K y v lam) n) = resolvent ε F := by
    refine eq_resolvent hε (fun n => hFb n)
      (B := ∑ κ, |a| * (ε⁻¹ * (2 * Λ κ)) + |a ^ 2| * Mr) (fun n => ?_) fun n => ?_
    · refine (norm_add_le _ _).trans (add_le_add ((norm_sum_le _ _).trans
        (Finset.sum_le_sum fun κ _ => ?_)) ?_)
      · rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left
          (norm_dbw_le (fun m => norm_resolvent_le (ε := ε) (H.norm_chiLam_le κ) m) hε κ n) (abs_nonneg _)
      · rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (norm_resolvent_le H.hrem n) (abs_nonneg _)
    · rw [lap_add' (fun m => ∑ κ, a • dbw ε κ (resolvent ε (chiLam K y lam κ)) m)
        (fun m => a ^ 2 • resolvent ε (rem η K y v lam) m), lap_sum', lap_smul']
      simp only [lap_smul', lap_dbw]
      have h1 : ∀ κ, lap ε (resolvent ε (chiLam K y lam κ)) = fun m =>
          chiLam K y lam κ m - resolvent ε (chiLam K y lam κ) m := fun κ => funext fun m => by
        rw [← lap_resolvent_add hε (H.norm_chiLam_le κ) m]; abel
      have h2 := lap_resolvent_add hε H.hrem n
      simp only [h1, hF]
      have h3 : ∀ κ, dbw ε κ (fun m => chiLam K y lam κ m - resolvent ε (chiLam K y lam κ) m) n =
          dbw ε κ (chiLam K y lam κ) n - dbw ε κ (resolvent ε (chiLam K y lam κ)) n := fun κ => by
        unfold dbw; module
      simp only [h3]
      rw [← h2]
      simp only [smul_sub, smul_add, Finset.sum_sub_distrib]
      abel
  rw [hw, ← hu]

omit H in
/-- `D_{𝐔,ν}v = ∂_νv + E_νv`, `E_νv(x) = η⁻¹(Ad_{𝐔(x, x + e_ν)}v(x + e_ν) - v(x + e_ν))`. -/
def Ev (η : ℝ) (A : Fin 4 → (Fin 4 → ℤ) → Matrix (Fin N) (Fin N) ℂ) (v : (Fin 4 → ℤ) → Matrix (Fin N) (Fin N) ℂ)
    (ν : Fin 4) (x : Fin 4 → ℤ) : Matrix (Fin N) (Fin N) ℂ :=
  η⁻¹ • (Ad (Uf η A ν x) (v (x + e4 ν)) - v (x + e4 ν))

omit H in
lemma Dfw_eq_dfw_add (ν : Fin 4) (x : Fin 4 → ℤ) : Dfw η A ν v x = dfw η ν v x + Ev η A v ν x := by
  unfold Dfw dfw Ev; module

omit H in
/-- The three terms of `D_{𝐔,ν}v` on `S`. -/
def Phi (η : ℝ) (K : ℕ) (y : Fin 4 → ℤ) (A : Fin 4 → (Fin 4 → ℤ) → Matrix (Fin N) (Fin N) ℂ)
    (v : (Fin 4 → ℤ) → Matrix (Fin N) (Fin N) ℂ) (lam : Fin 4 → (Fin 4 → ℤ) → Matrix (Fin N) (Fin N) ℂ)
    (ν : Fin 4) (x : Fin 4 → ℤ) : Matrix (Fin N) (Fin N) ℂ :=
  ∑ κ, dif (K : ℝ)⁻¹ true ν (dif (K : ℝ)⁻¹ false κ (resolvent (K : ℝ)⁻¹ (chiLam K y lam κ))) x +
    (K * η) • dif (K : ℝ)⁻¹ true ν (resolvent (K : ℝ)⁻¹ (rem η K y v lam)) x + Ev η A v ν x

/-- On `S` (`|x - y|_∞ ≤ 2a - η`), `D_{𝐔,ν}v = Φ`. -/
theorem Dfw_eq_Phi (ν : Fin 4) {x : Fin 4 → ℤ} (hx : InQ y (4 * K - 2) x) :
    Dfw η A ν v x = Phi η K y A v lam ν x := by
  have hε := H.ε_pos
  have hK := H.hK
  have c1 : chiK K y x = 1 := H.chi_eq_one_of (hx.mono (by omega))
  have c2 : chiK K y (x + e4 ν) = 1 := H.chi_eq_one_of ((hx.add_e ν).mono (by omega))
  have hdv : dfw η ν v x = dfw η ν (wloc K y v) x := by
    unfold dfw wloc; rw [c1, c2, one_smul, one_smul]
  rw [Dfw_eq_dfw_add, hdv, H.dfw_scale, H.w_eq]
  unfold Phi
  congr 1
  rw [show (fun n => ∑ κ, (K * η) • dbw (K : ℝ)⁻¹ κ (resolvent (K : ℝ)⁻¹ (chiLam K y lam κ)) n +
      (K * η) ^ 2 • resolvent (K : ℝ)⁻¹ (rem η K y v lam) n) =
      (fun n => (fun m => ∑ κ, (K * η) • dbw (K : ℝ)⁻¹ κ (resolvent (K : ℝ)⁻¹ (chiLam K y lam κ)) m) n +
        (fun m => (K * η) ^ 2 • resolvent (K : ℝ)⁻¹ (rem η K y v lam) m) n) from rfl]
  have e1 := dif_add' (ε := (K : ℝ)⁻¹) true ν
    (fun m => ∑ κ, (K * η) • dbw (K : ℝ)⁻¹ κ (resolvent (K : ℝ)⁻¹ (chiLam K y lam κ)) m)
    (fun m => (K * η) ^ 2 • resolvent (K : ℝ)⁻¹ (rem η K y v lam) m) x
  simp only [dif, ↓reduceIte] at e1
  rw [e1, smul_add]
  congr 1
  · have e2 := dif_sum' (ε := (K : ℝ)⁻¹) true ν
      (fun κ m => (K * η) • dbw (K : ℝ)⁻¹ κ (resolvent (K : ℝ)⁻¹ (chiLam K y lam κ)) m) x
    simp only [dif, ↓reduceIte] at e2
    rw [e2, Finset.smul_sum]
    refine Finset.sum_congr rfl fun κ _ => ?_
    have e3 := dif_smul' (ε := (K : ℝ)⁻¹) true ν (K * η)
      (fun m => dbw (K : ℝ)⁻¹ κ (resolvent (K : ℝ)⁻¹ (chiLam K y lam κ)) m) x
    simp only [dif, Bool.false_eq_true, ↓reduceIte] at e3 ⊢
    rw [e3, smul_smul, inv_mul_cancel₀ H.a_pos.ne', one_smul]
  · have e3 := dif_smul' (ε := (K : ℝ)⁻¹) true ν ((K * η) ^ 2)
      (fun m => resolvent (K : ℝ)⁻¹ (rem η K y v lam) m) x
    simp only [dif, ↓reduceIte] at e3 ⊢
    rw [e3, smul_smul]
    congr 1
    have := H.a_pos.ne'; field_simp

/-! ### The modulus of `E_νv` -/

/-- One step of `E_νv`: `‖E_νv(p + e_μ) - E_νv(p)‖ ≤ (9/16)V/K`. -/
lemma norm_E_step {μ ν : Fin 4} {p : Fin 4 → ℤ} (h1 : InQ y (8 * K) p) (h2 : InQ y (8 * K) (p + e4 μ))
    (h3 : InQ y (8 * K) (p + e4 ν)) (h4 : InQ y (8 * K) (p + e4 ν + e4 μ)) (h5 : InQ y (8 * K) (p + e4 μ + e4 ν)) :
    ‖Ev η A v ν (p + e4 μ) - Ev η A v ν p‖ ≤ 9 / 16 * (V / K) := by
  have hV := H.V_nonneg
  have ha := H.a_pos
  have hη := H.hη
  have hK := H.K_pos
  have e : Ev η A v ν (p + e4 μ) - Ev η A v ν p =
      η⁻¹ • ((Ad (Uf η A ν (p + e4 μ)) (v (p + e4 μ + e4 ν)) - Ad (Uf η A ν p) (v (p + e4 μ + e4 ν))) +
        (Ad (Uf η A ν p) (v (p + e4 μ + e4 ν) - v (p + e4 ν)) - (v (p + e4 μ + e4 ν) - v (p + e4 ν)))) := by
    unfold Ev; rw [Ad_sub]; module
  rw [e, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hη.le)]
  have hX1 : ‖η • A ν p‖ ≤ 1 / 32 := by
    rw [norm_smul, Real.norm_of_nonneg hη.le]
    have := H.hA ν p h1 h3
    nlinarith [norm_nonneg (A ν p), H.η_le_a]
  have hX2 : ‖η • A ν (p + e4 μ)‖ ≤ 1 / 32 := by
    rw [norm_smul, Real.norm_of_nonneg hη.le]
    have := H.hA ν (p + e4 μ) h2 h5
    nlinarith [norm_nonneg (A ν (p + e4 μ)), H.η_le_a]
  have hdA := H.hdA ν μ p h1 h2 h3 h5
  have hdA' : ‖dfw η μ (A ν) p‖ ≤ 1 / (32 * (K * η) ^ 2) := by
    rw [le_div_iff₀ (by positivity)]; linarith
  have hdiff : ‖η • A ν (p + e4 μ) - η • A ν p‖ = η * (η * ‖dfw η μ (A ν) p‖) := by
    rw [← smul_sub, norm_smul, Real.norm_of_nonneg hη.le]
    congr 1
    unfold dfw
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hη]
    field_simp
  have Ba : ‖Ad (Uf η A ν (p + e4 μ)) (v (p + e4 μ + e4 ν)) - Ad (Uf η A ν p) (v (p + e4 μ + e4 ν))‖ ≤
      η ^ 2 * V / (4 * (K * η)) := by
    have := norm_Ad_exp_sub_Ad_exp_le hX1 hX2 (v (p + e4 μ + e4 ν))
    unfold Uf
    refine this.trans ?_
    rw [hdiff]
    have hv := H.hv _ h5
    calc 8 * (η * (η * ‖dfw η μ (A ν) p‖)) * ‖v (p + e4 μ + e4 ν)‖ ≤
        8 * (η * (η * (1 / (32 * (K * η) ^ 2)))) * (V * (K * η)) := by gcongr
      _ = η ^ 2 * V / (4 * (K * η)) := by field_simp; ring
  -- the change of `v` along the bond `(p + e_ν, p + e_ν + e_μ)`
  have hdv : ‖v (p + e4 μ + e4 ν) - v (p + e4 ν)‖ ≤ η * (5 / 4 * V) := by
    have hcomm : p + e4 μ + e4 ν = p + e4 ν + e4 μ := by abel
    have e3 : v (p + e4 μ + e4 ν) - v (p + e4 ν) = η • (Dfw η A μ v (p + e4 ν) -
        η⁻¹ • (Ad (Uf η A μ (p + e4 ν)) (v (p + e4 ν + e4 μ)) - v (p + e4 ν + e4 μ))) := by
      unfold Dfw; rw [hcomm, smul_sub, smul_smul, smul_smul, mul_inv_cancel₀ hη.ne', one_smul, one_smul]; abel
    rw [e3, norm_smul, Real.norm_of_nonneg hη.le]
    refine mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans ?_) hη.le
    have b1 := H.hDv μ (p + e4 ν) h3 h4
    have b2 : ‖η⁻¹ • (Ad (Uf η A μ (p + e4 ν)) (v (p + e4 ν + e4 μ)) - v (p + e4 ν + e4 μ))‖ ≤ V / 4 := by
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hη.le)]
      calc η⁻¹ * ‖Ad (Uf η A μ (p + e4 ν)) (v (p + e4 ν + e4 μ)) - v (p + e4 ν + e4 μ)‖ ≤
          η⁻¹ * (η / (4 * (K * η)) * (V * (K * η))) :=
          mul_le_mul_of_nonneg_left ((H.bondF h3 h4 _).trans
            (mul_le_mul_of_nonneg_left (H.hv _ h4) (by positivity))) (inv_nonneg.2 hη.le)
        _ = V / 4 := by have := hη.ne'; have := hK.ne'; field_simp
    linarith
  have Bb : ‖Ad (Uf η A ν p) (v (p + e4 μ + e4 ν) - v (p + e4 ν)) - (v (p + e4 μ + e4 ν) - v (p + e4 ν))‖ ≤
      η / (4 * (K * η)) * (η * (5 / 4 * V)) :=
    (H.bondF h1 h3 _).trans (mul_le_mul_of_nonneg_left hdv (by positivity))
  calc η⁻¹ * ‖(Ad (Uf η A ν (p + e4 μ)) (v (p + e4 μ + e4 ν)) - Ad (Uf η A ν p) (v (p + e4 μ + e4 ν))) +
        (Ad (Uf η A ν p) (v (p + e4 μ + e4 ν) - v (p + e4 ν)) - (v (p + e4 μ + e4 ν) - v (p + e4 ν)))‖ ≤
      η⁻¹ * (η ^ 2 * V / (4 * (K * η)) + η / (4 * (K * η)) * (η * (5 / 4 * V))) :=
        mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add Ba Bb)) (inv_nonneg.2 hη.le)
    _ = 9 / 16 * (V / K) := by have := hη.ne'; have := hK.ne'; field_simp; ring

/-- The modulus of `E_νv` on `S`: `‖E_νv(x') - E_νv(x)‖ ≤ (9/16)(|x' - x|₁/K)V`. -/
lemma norm_E_walk_le (ν : Fin 4) {x x' : Fin 4 → ℤ} (hx : InQ y (4 * K - 2) x) (hx' : InQ y (4 * K - 2) x') :
    ‖Ev η A v ν x' - Ev η A v ν x‖ ≤ 9 / 16 * (V / K) * l1 (x' - x) := by
  have hK := H.hK
  obtain ⟨l, hl⟩ := exists_shortest x x'
  have hw := walk_inQ hl hx hx'
  have hstep : WalkIn (sgnv x x') (fun p μ => ‖Ev η A v ν (p + sgnv x x' μ • e4 μ) - Ev η A v ν p‖ ≤
      9 / 16 * (V / K)) x l :=
    WalkIn.mono (fun p μ ⟨q1, q2, q3⟩ => by
      have big : ∀ z, InQ y (4 * K - 2) z → ∀ a b : Fin 4, InQ y (8 * K) z ∧ InQ y (8 * K) (z + e4 a) ∧
          InQ y (8 * K) (z + e4 a + e4 b) := fun z hz a b =>
        ⟨hz.mono (by omega), (hz.add_e a).mono (by omega), ((hz.add_e a).add_e b).mono (by omega)⟩
      rcases sgnv_cases x x' μ with hs | hs | hs
      · rw [hs, one_smul]
        rw [hs, one_smul] at q2
        exact H.norm_E_step (big p q1 μ μ).1 (big p q1 μ μ).2.1 (big p q1 ν μ).2.1 (big p q1 ν μ).2.2
          (big p q1 μ ν).2.2
      · rw [hs, neg_one_smul, ← sub_eq_add_neg]
        rw [hs, neg_one_smul, ← sub_eq_add_neg] at q2
        rw [norm_sub_rev]
        have := H.norm_E_step (μ := μ) (ν := ν) (p := p - e4 μ) (big _ q2 μ μ).1
          (by rw [sub_add_cancel]; exact (big p q1 μ μ).1) (big _ q2 ν μ).2.1
          (by rw [add_right_comm, sub_add_cancel]; exact (big p q1 ν μ).2.1)
          (by rw [sub_add_cancel]; exact (big p q1 ν μ).2.1)
        rwa [sub_add_cancel] at this
      · exact absurd hs q3) l x hw
  have := norm_sub_le_walk (sgnv x x') (Ev η A v ν) l x hstep
  rwa [walkEnd_shortest hl, length_eq_l1 hl] at this

end Hyp

/-! ### The proposition -/

/-- **`prop:interior-schauder`**: for `x, x' ∈ S = {|x - y|_∞ ≤ 2a - η}` with `|x - x'|₁ ≤ a`, every shortest
path `γ` from `x` to `x'`, and every `ν`,
`‖Ad_{𝐔(γ)}(D_{𝐔,ν}v)(x') - (D_{𝐔,ν}v)(x)‖ ≤ C_I(β)(V + Σ_κΛ_κ)(|x - x'|₁/a)^β`. -/
theorem interior_schauder {η : ℝ} {K : ℕ} {y : Fin 4 → ℤ} {A : Fin 4 → (Fin 4 → ℤ) → Mat}
    {v : (Fin 4 → ℤ) → Mat} {lam : Fin 4 → (Fin 4 → ℤ) → Mat} {rho : (Fin 4 → ℤ) → Mat} {V : ℝ}
    {Λ : Fin 4 → ℝ} {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (H : Hyp η K y A v lam rho V Λ β)
    {x x' : Fin 4 → ℤ} (hx : InQ y (4 * K - 2) x) (hx' : InQ y (4 * K - 2) x') (hxx : l1 (x' - x) ≤ K)
    {l : List (Fin 4)} (hl : IsShortest x x' l) (ν : Fin 4) :
    ‖Ad (pathT η A (sgnv x x') x l) (Dfw η A ν v x') - Dfw η A ν v x‖ ≤
      CI β * (V + ∑ κ, Λ κ) * (η * l1 (x' - x) / (K * η)) ^ β := by
  have hK := H.hK
  have hKr := H.K_pos
  have hε := H.ε_pos
  have hV := H.V_nonneg
  have hΛ : 0 ≤ ∑ κ, Λ κ := Finset.sum_nonneg fun κ _ => H.Λ_nonneg κ
  rw [H.holder_rewrite]
  set m := x' - x with hm
  have hx'm : x' = x + m := by rw [hm]; abel
  set t := (l1 m / K) ^ β with ht
  have hx0 : 0 ≤ l1 m / K := div_nonneg (l1_nonneg _) hKr.le
  have hx1 : l1 m / K ≤ 1 := (div_le_one hKr).2 hxx
  have ht0 : 0 ≤ t := Real.rpow_nonneg hx0 β
  have hlt : l1 m / K ≤ t := le_rpow_self hx0 hx1 hβ0 hβ1.le
  have hεl : (K : ℝ)⁻¹ * l1 m = l1 m / K := by field_simp
  have hQx : InQ y (8 * K) x := hx.mono (by omega)
  have hQx' : InQ y (8 * K) x' := hx'.mono (by omega)
  -- the transport
  have hT : ‖Ad (pathT η A (sgnv x x') x l) (Dfw η A ν v x') - Dfw η A ν v x'‖ ≤ V * t := by
    refine (H.path_dev hl hQx hQx' hxx _).trans ?_
    have := H.hDv ν x' hQx' ((hx'.add_e ν).mono (by omega))
    calc l1 m / K * ‖Dfw η A ν v x'‖ ≤ t * V := mul_le_mul hlt this (norm_nonneg _) ht0
      _ = V * t := mul_comm _ _
  -- the three terms of `Φ`
  have hD1 : ∀ κ, ‖dif (K : ℝ)⁻¹ true ν (dif (K : ℝ)⁻¹ false κ (resolvent (K : ℝ)⁻¹ (chiLam K y lam κ))) x' -
      dif (K : ℝ)⁻¹ true ν (dif (K : ℝ)⁻¹ false κ (resolvent (K : ℝ)⁻¹ (chiLam K y lam κ))) x‖ ≤
      CS β * (6 * Λ κ) * t := fun κ => by
    have := norm_dif_dif_resolvent_sub_le hε hβ0 hβ1 (by linarith [H.Λ_nonneg κ] : 0 ≤ 6 * Λ κ)
      (H.norm_chiLam_le κ) (fun n m' => by rw [inv_mul_eq_div]; exact H.holder_chi_lam hβ0 hβ1.le κ n m') true false ν κ x m
    rwa [← hx'm, hεl] at this
  have hD2 : ‖(K * η) • dif (K : ℝ)⁻¹ true ν (resolvent (K : ℝ)⁻¹ (rem η K y v lam)) x' -
      (K * η) • dif (K : ℝ)⁻¹ true ν (resolvent (K : ℝ)⁻¹ (rem η K y v lam)) x‖ ≤
      CS' β * (5 * ∑ κ, Λ κ + 166 * V) * t := by
    have := norm_dif_resolvent_sub_le hε hβ0 hβ1 H.hrem true ν x m
    rw [← hx'm, hεl] at this
    rw [← smul_sub, norm_smul, Real.norm_of_nonneg H.a_pos.le]
    calc (K * η) * ‖_‖ ≤ (K * η) * (CS' β * ((5 * ∑ κ, Λ κ + 166 * V) / (K * η)) * t) :=
          mul_le_mul_of_nonneg_left this H.a_pos.le
      _ = CS' β * (5 * ∑ κ, Λ κ + 166 * V) * t := by
          have := H.a_pos.ne'; have := H.hη.ne'; have := hKr.ne'; field_simp
  have hD3 : ‖Hyp.Ev η A v ν x' - Hyp.Ev η A v ν x‖ ≤ V * t := by
    refine (H.norm_E_walk_le ν hx hx').trans ?_
    have : 9 / 16 * (V / K) * l1 m = 9 / 16 * V * (l1 m / K) := by ring
    rw [this]
    calc 9 / 16 * V * (l1 m / K) ≤ 1 * V * t := by gcongr; norm_num
      _ = V * t := by ring
  have hPhi : ‖Dfw η A ν v x' - Dfw η A ν v x‖ ≤
      (∑ κ, CS β * (6 * Λ κ) * t) + CS' β * (5 * ∑ κ, Λ κ + 166 * V) * t + V * t := by
    rw [H.Dfw_eq_Phi ν hx', H.Dfw_eq_Phi ν hx]
    unfold Hyp.Phi
    have e : (∑ κ, dif (K : ℝ)⁻¹ true ν (dif (K : ℝ)⁻¹ false κ (resolvent (K : ℝ)⁻¹ (chiLam K y lam κ))) x' +
        (K * η) • dif (K : ℝ)⁻¹ true ν (resolvent (K : ℝ)⁻¹ (rem η K y v lam)) x' + Hyp.Ev η A v ν x') -
        (∑ κ, dif (K : ℝ)⁻¹ true ν (dif (K : ℝ)⁻¹ false κ (resolvent (K : ℝ)⁻¹ (chiLam K y lam κ))) x +
        (K * η) • dif (K : ℝ)⁻¹ true ν (resolvent (K : ℝ)⁻¹ (rem η K y v lam)) x + Hyp.Ev η A v ν x) =
        ∑ κ, (dif (K : ℝ)⁻¹ true ν (dif (K : ℝ)⁻¹ false κ (resolvent (K : ℝ)⁻¹ (chiLam K y lam κ))) x' -
          dif (K : ℝ)⁻¹ true ν (dif (K : ℝ)⁻¹ false κ (resolvent (K : ℝ)⁻¹ (chiLam K y lam κ))) x) +
        ((K * η) • dif (K : ℝ)⁻¹ true ν (resolvent (K : ℝ)⁻¹ (rem η K y v lam)) x' -
          (K * η) • dif (K : ℝ)⁻¹ true ν (resolvent (K : ℝ)⁻¹ (rem η K y v lam)) x) +
        (Hyp.Ev η A v ν x' - Hyp.Ev η A v ν x) := by
      rw [Finset.sum_sub_distrib]; abel
    rw [e]
    refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add ?_ hD2)) hD3)
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun κ _ => hD1 κ)
  have hsum : ∑ κ, CS β * (6 * Λ κ) * t = 6 * CS β * (∑ κ, Λ κ) * t := by
    rw [Finset.mul_sum, Finset.sum_mul]; refine Finset.sum_congr rfl fun κ _ => ?_; ring
  rw [hsum] at hPhi
  have hCS : 0 ≤ CS β := by
    unfold CS
    have := c0_pos; have := one_le_m1
    have h1 : 0 < 8 / β := by positivity
    have h2 : 0 < 12 / (1 - β) := div_pos (by norm_num) (by linarith)
    positivity
  have hCS' : 0 ≤ CS' β := by unfold CS'; have : 0 < 4 / (1 - β) := div_pos (by norm_num) (by linarith); linarith
  calc ‖Ad (pathT η A (sgnv x x') x l) (Dfw η A ν v x') - Dfw η A ν v x‖ ≤
      ‖Ad (pathT η A (sgnv x x') x l) (Dfw η A ν v x') - Dfw η A ν v x'‖ + ‖Dfw η A ν v x' - Dfw η A ν v x‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ V * t + (6 * CS β * (∑ κ, Λ κ) * t + CS' β * (5 * ∑ κ, Λ κ + 166 * V) * t + V * t) :=
        add_le_add hT hPhi
    _ ≤ CI β * (V + ∑ κ, Λ κ) * t := by
        unfold CI
        have h1 : 0 ≤ CS' β * ∑ κ, Λ κ := mul_nonneg hCS' hΛ
        have h2 : 0 ≤ CS β * V := mul_nonneg hCS hV
        have h3 : 0 ≤ CS' β * V := mul_nonneg hCS' hV
        have h4 : 0 ≤ ∑ κ, Λ κ := hΛ
        nlinarith [mul_nonneg h1 ht0, mul_nonneg h2 ht0, mul_nonneg h3 ht0, mul_nonneg h4 ht0,
          mul_nonneg (mul_nonneg hCS hΛ) ht0, mul_nonneg hV ht0]

end InteriorSchauder
end CoreLean

end
