/-
Families of `0`-forms on the fine lattice (`M_N(ℂ)^m`-valued functions, `m ∈ {1, 4}` in BALABAN_CORE.tex
`4252790331fd`, `prop:sf-bounds`) and their periodic lifts to the coordinates of a layer (`lem:sf-local`), in the
units `a₀ = 1`; the case `m = 1` is `SFBox.lean`.

* `liftM u`: `n ↦ (u_k(n mod N₀))_k ∈ VS N m`; `norm_liftM_sq`: `‖ũ(n)‖² = NΣ_k|u_k|²`.
* `DfwV_liftM`, `DbwV_liftM`, `covLapV_liftM`, `sum_DbwV_liftM`: the differences of the layer are `Lʲ` times those of
  the fine lattice, acting on the members, and the covariant Laplacian is `L^{2j}` times that of the fine lattice.
-/
import CoreLean.SFBox

open Finset Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace CoreLean
namespace SFBox

open SFLocal LocalLaplacian InteriorSchauder

variable {N m : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ

variable {n : ℕ} [NeZero n]

/-- The periodic function of a family of `0`-forms, with values in `VS N m`. -/
def liftM (u : Fin m → Site n → Mat) : (Fin 4 → ℤ) → VS N m := fun z => vecOf fun k => u k (castS z)

lemma vecOf_subM (X Y : Fin m → Mat) : vecOf (fun k => X k - Y k) = vecOf X - vecOf Y := by ext p; rfl

lemma vecOf_csmulM (c : ℂ) (X : Fin m → Mat) : vecOf (fun k => c • X k) = c • vecOf X := by ext p; rfl

lemma vecOf_rsmulM (c : ℝ) (X : Fin m → Mat) : vecOf (fun k => ((c : ℝ) : ℂ) • X k) = c • vecOf X := by
  ext p; simp [vecOf, Complex.real_smul]

lemma vecOf_sumM {ι : Type*} (s : Finset ι) (X : ι → Fin m → Mat) :
    vecOf (fun k => ∑ i ∈ s, X i k) = ∑ i ∈ s, vecOf (X i) := by
  ext p; simp [vecOf]

lemma AdV_vecOfM (W : (Matrix (Fin N) (Fin N) ℂ)ˣ) (X : Fin m → Mat) :
    AdV W (vecOf X) = vecOf fun k => Ad W (X k) := by
  rw [liftV_apply]; simp only [matOf_vecOf]; rfl

variable {c : ℝ}

/-- **The forward differences of the layer**, on the members. -/
theorem DfwV_liftM (hc : c ≠ 0) (X : Fin 4 → Site n → Mat) (μ : Fin 4) (u : Fin m → Site n → Mat) :
    DfwV c⁻¹ (Atil c X) μ (liftM u) = liftM (fun k x => ((c : ℝ) : ℂ) • Dfw 1 (cfgX X) μ (u k) x) := by
  funext z
  simp only [DfwV, liftM, Uf_Atil hc, castS_add_e4, AdV_vecOfM, inv_inv, Dfw, inv_one, one_smul]
  rw [← vecOf_subM, ← vecOf_rsmulM]

/-- **The backward differences of the layer**, on the members. -/
theorem DbwV_liftM (hc : c ≠ 0) (X : Fin 4 → Site n → Mat) (μ : Fin 4) (u : Fin m → Site n → Mat) :
    DbwV c⁻¹ (Atil c X) μ (liftM u) = liftM (fun k x => ((c : ℝ) : ℂ) • Dbw 1 (cfgX X) μ (u k) x) := by
  funext z
  simp only [DbwV, liftM, Ub_Atil hc, castS_sub_e4, AdV_vecOfM, inv_inv, Dbw, inv_one, one_smul]
  rw [← vecOf_subM, ← vecOf_rsmulM]

/-- **The covariant Laplacian of the layer is `L^{2j}` times that of the fine lattice.** -/
theorem covLapV_liftM (hc : c ≠ 0) (X : Fin 4 → Site n → Mat) (u : Fin m → Site n → Mat) (z : Fin 4 → ℤ) :
    covLapV c⁻¹ (Atil c X) (liftM u) z =
      liftM (fun k x => ((c ^ 2 : ℝ) : ℂ) • Lap 1 (cfgX X) (u k) x) z := by
  simp only [covLapV, DfwV_liftM hc, DbwV_liftM hc, Dbw_smul]
  simp only [liftM, Lap, smul_smul, Finset.smul_sum]
  rw [vecOf_sumM]
  refine sum_congr rfl fun μ _ => ?_
  congr 1
  funext k
  congr 1
  push_cast; ring

/-- The `D^*` term of the layer: `Σ_μD^*_μ(Lʲg_μ)` of the layer is `L^{2j}D^*_𝐔g` of the fine lattice. -/
theorem sum_DbwV_liftM (hc : c ≠ 0) (X : Fin 4 → Site n → Mat) (g : Fin m → Fin 4 → Site n → Mat)
    (z : Fin 4 → ℤ) :
    ∑ μ, DbwV c⁻¹ (Atil c X) μ (liftM (fun k x => ((c : ℝ) : ℂ) • g k μ x)) z =
      liftM (fun k x => ((c ^ 2 : ℝ) : ℂ) • Ds1 1 (cfgX X) (g k) x) z := by
  simp only [DbwV_liftM hc, Dbw_smul]
  simp only [liftM, Ds1, smul_smul, Finset.smul_sum]
  rw [vecOf_sumM]
  refine sum_congr rfl fun μ _ => ?_
  congr 1
  funext k
  congr 1
  push_cast; ring

/-- `‖ũ(z)‖² = NΣ_k|u_k(z mod N₀)|²`. -/
lemma norm_liftM_sq (u : Fin m → Site n → Mat) (z : Fin 4 → ℤ) :
    ‖liftM (N := N) u z‖ ^ 2 = N * ∑ k, hs2 (u k (castS z)) := by
  rw [liftM, normV_sq]; simp

end SFBox
end CoreLean

end
