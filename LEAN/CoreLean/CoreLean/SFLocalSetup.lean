/-
`lem:sf-local` of BALABAN_CORE.tex (`4252790331fd`), the setting: functions with values in `M_N(ℂ)^m` and the covariant
differences acting on their members, in the coordinates of the layer (`εℤ⁴`, `ε = a₀/a`, indexed by `ℤ⁴`), and the
decomposition `eq:sf-laplacian` of the covariant Laplacian.

* `VS N m = EuclideanSpace ℂ (Fin m × Fin N × Fin N)`: `M_N(ℂ)^m` with the Euclidean norm, which is `√N` times the
  Hilbert–Schmidt norm `(Σ_k|X_k|²)^{1/2}` of the core (`normV_sq`); it is a complete real inner product space.
* `liftV φ`: a complex-linear map of `M_N(ℂ)` acting on the members; `norm_liftV_le`: `‖liftV φ‖ ≤ c` if
  `|φZ| ≤ c|Z|` in the Hilbert–Schmidt norm.
* `AdV W = liftV Ad_W`; `KV ε W = ε⁻¹(Ad_W - 1)` on the members.
* `DfwV`, `DbwV`, `covLapV`: `D_{𝐔,μ}`, `D^*_{𝐔,μ}`, `Δ_𝐔` in the coordinates of the layer, with the transports
  `𝐔(n, n ± e_μ)` of `InteriorSetup` (`Uf`, `Ub`) for the field `Ã` of the layer (`Ã = aA'`, so that
  `𝐔(n, n + e_μ) = e^{iεÃ_μ(n)} = e^{ia₀A'_μ(n)}`).
* `covLapV_eq`: `eq:sf-laplacian`, `Δ_𝐔u = Δu + Σ_μ∂^*_μ(𝒢_μu) + 𝒞u`.
-/
import CoreLean.LocalIntegrability
import CoreLean.InteriorSetup
import CoreLean.ProductExp

open Finset Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace CoreLean
namespace SFLocal

open LocalLaplacian InteriorSchauder

variable {N m : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "GLN" => (Matrix (Fin N) (Fin N) ℂ)ˣ

/-- `M_N(ℂ)^m` with the Euclidean norm. -/
abbrev VS (N m : ℕ) := EuclideanSpace ℂ (Fin m × Fin N × Fin N)

/-- The member `k` of `v`. -/
def matOf (v : VS N m) (k : Fin m) : Mat := Matrix.of fun i j => v (k, i, j)

/-- The element with the members `X k`. -/
def vecOf (X : Fin m → Mat) : VS N m := (WithLp.equiv 2 _).symm fun p => X p.1 p.2.1 p.2.2

@[simp] lemma matOf_vecOf (X : Fin m → Mat) (k : Fin m) : matOf (vecOf X) k = X k := by
  ext i j; rfl

@[simp] lemma vecOf_matOf (v : VS N m) : vecOf (fun k => matOf v k) = v := by
  ext p; rfl

lemma matOf_add (v w : VS N m) (k : Fin m) : matOf (v + w) k = matOf v k + matOf w k := by ext i j; rfl

lemma matOf_smul (c : ℂ) (v : VS N m) (k : Fin m) : matOf (c • v) k = c • matOf v k := by ext i j; rfl

lemma matOf_sub (v w : VS N m) (k : Fin m) : matOf (v - w) k = matOf v k - matOf w k := by ext i j; rfl

/-- `‖v‖² = NΣ_k|v_k|²`, with the Hilbert–Schmidt norm `|·|` of the core. -/
lemma normV_sq (v : VS N m) : ‖v‖ ^ 2 = N * ∑ k, hs2 (matOf v k) := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type, mul_sum]
  refine sum_congr rfl fun k _ => ?_
  rw [hs2_eq_sum, ← mul_assoc]
  by_cases hN : (N : ℝ) = 0
  · have : N = 0 := by exact_mod_cast hN
    subst this; simp
  · rw [mul_inv_cancel₀ hN, one_mul, Fintype.sum_prod_type, sum_comm]
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    rw [Complex.sq_norm]; rfl

/-- A complex-linear map of `M_N(ℂ)` acting on the members. -/
def liftL (φ : Mat →ₗ[ℂ] Mat) : VS N m →ₗ[ℂ] VS N m where
  toFun v := vecOf fun k => φ (matOf v k)
  map_add' v w := by ext p; simp [vecOf, matOf_add]
  map_smul' c v := by ext p; simp [vecOf, matOf_smul]

/-- The same as a continuous real-linear map. -/
def liftV (φ : Mat →ₗ[ℂ] Mat) : VS N m →L[ℝ] VS N m :=
  LinearMap.toContinuousLinearMap ((liftL (m := m) φ).restrictScalars ℝ)

lemma liftV_apply (φ : Mat →ₗ[ℂ] Mat) (v : VS N m) : liftV φ v = vecOf fun k => φ (matOf v k) := rfl

lemma matOf_liftV (φ : Mat →ₗ[ℂ] Mat) (v : VS N m) (k : Fin m) : matOf (liftV φ v) k = φ (matOf v k) := by
  rw [liftV_apply, matOf_vecOf]

/-- `‖liftV φ‖ ≤ c` if `|φZ| ≤ c|Z|`. -/
theorem norm_liftV_le (φ : Mat →ₗ[ℂ] Mat) {c : ℝ} (hc : 0 ≤ c) (h : ∀ Z, hs (φ Z) ≤ c * hs Z) :
    ‖(liftV φ : VS N m →L[ℝ] VS N m)‖ ≤ c := by
  refine ContinuousLinearMap.opNorm_le_bound _ hc fun v => ?_
  refine le_of_pow_le_pow_left₀ (n := 2) two_ne_zero (mul_nonneg hc (norm_nonneg _)) ?_
  rw [mul_pow, normV_sq, normV_sq, mul_sum, mul_sum, mul_sum]
  refine sum_le_sum fun k _ => ?_
  rw [matOf_liftV, ← hs_sq, ← hs_sq]
  have h1 := h (matOf v k)
  have h0 := hs_nonneg (φ (matOf v k))
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  nlinarith [mul_le_mul h1 h1 h0 (mul_nonneg hc (hs_nonneg (matOf v k)))]

/-- `Ad_W` as a complex-linear map. -/
def AdL (W : GLN) : Mat →ₗ[ℂ] Mat where
  toFun := Ad W
  map_add' := Ad_add W
  map_smul' c X := Ad_smul W c X

/-- `ε⁻¹(Ad_W - 1)` as a complex-linear map. -/
def KL (ε : ℝ) (W : GLN) : Mat →ₗ[ℂ] Mat := ((ε⁻¹ : ℝ) : ℂ) • (AdL W - LinearMap.id)

/-- `Ad_W` on the members. -/
abbrev AdV (W : GLN) : VS N m →L[ℝ] VS N m := liftV (AdL W)

/-- `ε⁻¹(Ad_W - 1)` on the members. -/
abbrev KV (ε : ℝ) (W : GLN) : VS N m →L[ℝ] VS N m := liftV (KL ε W)

lemma KV_apply (ε : ℝ) (W : GLN) (v : VS N m) : KV ε W v = ε⁻¹ • (AdV W v - v) := by
  ext p
  simp only [liftV_apply, KL, AdL, vecOf, matOf, LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.coe_mk,
    AddHom.coe_mk, LinearMap.id_apply]
  simp [Matrix.sub_apply, Matrix.smul_apply, PiLp.sub_apply, PiLp.smul_apply]

/-! ### The covariant differences in the coordinates of the layer -/

/-- `D_{𝐔,μ}` on `VS`-valued functions. -/
def DfwV (ε : ℝ) (A : Fin 4 → (Fin 4 → ℤ) → Mat) (μ : Fin 4) (u : (Fin 4 → ℤ) → VS N m) (n : Fin 4 → ℤ) : VS N m :=
  ε⁻¹ • (AdV (Uf ε A μ n) (u (n + e4 μ)) - u n)

/-- `D^*_{𝐔,μ}` on `VS`-valued functions. -/
def DbwV (ε : ℝ) (A : Fin 4 → (Fin 4 → ℤ) → Mat) (μ : Fin 4) (u : (Fin 4 → ℤ) → VS N m) (n : Fin 4 → ℤ) : VS N m :=
  ε⁻¹ • (AdV (Ub ε A μ n) (u (n - e4 μ)) - u n)

/-- `Δ_𝐔 = Σ_μD^*_{𝐔,μ}D_{𝐔,μ}`. -/
def covLapV (ε : ℝ) (A : Fin 4 → (Fin 4 → ℤ) → Mat) (u : (Fin 4 → ℤ) → VS N m) (n : Fin 4 → ℤ) : VS N m := ∑ μ, DbwV ε A μ (DfwV ε A μ u) n

/-- `K_μ(n) = ε⁻¹(Ad_{𝐔(n, n + e_μ)} - 1)`. -/
abbrev Kf (ε : ℝ) (A : Fin 4 → (Fin 4 → ℤ) → Mat) (μ : Fin 4) (n : Fin 4 → ℤ) : VS N m →L[ℝ] VS N m := KV ε (Uf ε A μ n)

/-- `K'_μ(n) = ε⁻¹(Ad_{𝐔(n, n - e_μ)} - 1)`. -/
abbrev Kb (ε : ℝ) (A : Fin 4 → (Fin 4 → ℤ) → Mat) (μ : Fin 4) (n : Fin 4 → ℤ) : VS N m →L[ℝ] VS N m := KV ε (Ub ε A μ n)

/-- `𝒢_μu = K_μu(· + e_μ) - K''_μu`, `K''_μ = K'_μ(· + e_μ)`. -/
def Gop (ε : ℝ) (A : Fin 4 → (Fin 4 → ℤ) → Mat) (μ : Fin 4) (u : (Fin 4 → ℤ) → VS N m) (n : Fin 4 → ℤ) : VS N m :=
  Kf ε A μ n (u (n + e4 μ)) - Kb ε A μ (n + e4 μ) (u n)

/-- `𝒞 = Σ_μ(∂^*_μK''_μ + K'_μK_μ(· - e_μ))`. -/
def Cop (ε : ℝ) (A : Fin 4 → (Fin 4 → ℤ) → Mat) (n : Fin 4 → ℤ) : VS N m →L[ℝ] VS N m :=
  ∑ μ, (ε⁻¹ • (Kb ε A μ n - Kb ε A μ (n + e4 μ)) + (Kb ε A μ n).comp (Kf ε A μ (n - e4 μ)))

/-- **`eq:sf-laplacian`**: `Δ_𝐔u = Δu + Σ_μ∂^*_μ(𝒢_μu) + 𝒞u`. -/
theorem covLapV_eq (ε : ℝ) (A : Fin 4 → (Fin 4 → ℤ) → Mat) (hε : ε ≠ 0) (u : (Fin 4 → ℤ) → VS N m) (n : Fin 4 → ℤ) :
    covLapV ε A u n = lap ε u n + ∑ μ, dbw ε μ (Gop ε A μ u) n + Cop ε A n (u n) := by
  simp only [covLapV, lap, Cop, ContinuousLinearMap.sum_apply, ← sum_add_distrib]
  refine sum_congr rfl fun μ _ => ?_
  simp only [DbwV, DfwV, dbw, dfw, Gop, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply, KV_apply, map_sub, map_smul, sub_add_cancel]
  module

end SFLocal
end CoreLean

end
