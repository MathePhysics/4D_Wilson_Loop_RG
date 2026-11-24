/-
The passage from the fine lattice of a sequence of domains to the coordinates of a layer of `lem:sf-local` of
BALABAN_CORE.tex (`4252790331fd`): the forms on the torus as periodic functions on the covering lattice `ℤ⁴`
(`a₀ = 1`), the rescaled field, and the covariant differences.

For a scale `j`, `ε = L^{-j}` and a field `X` on the fine lattice in the units `a₀ = 1` (the configuration
`𝐔 = e^{iX}`, `X = a₀A'`):
* `castS`: `ℤ⁴ → (ℤ/N₀)⁴`; `liftF u`: the periodic function `n ↦ u(n mod N₀)` with values in `VS N 1`;
* `Atil j X`: the field of the layer, `Ã(n) = LʲX(n mod N₀)` (`= aA'` in the core's notation), so that
  `e^{iεÃ} = 𝐔`;
* `DfwV_lift`, `DbwV_lift`, `covLapV_lift`: the differences of the layer are `Lʲ` times those of the fine lattice
  and the covariant Laplacian of the layer is `L^{2j}` times that of the fine lattice (the differences of the
  rescaled lattice are `a` times those of `a₀ℤ⁴`).
-/
import CoreLean.SFLocal
import CoreLean.SFDecaySeq

open Finset Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace CoreLean
namespace SFBox

open SFLocal LocalLaplacian InteriorSchauder

variable {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "GLN" => (Matrix (Fin N) (Fin N) ℂ)ˣ

variable {n : ℕ} [NeZero n]

/-- The site of `(ℤ/n)⁴` under a point of `ℤ⁴`. -/
def castS (z : Fin 4 → ℤ) : Site n := fun ν => (z ν : ZMod n)

lemma castS_add_e4 (z : Fin 4 → ℤ) (μ : Fin 4) : castS (n := n) (z + e4 μ) = castS z + unit n μ := by
  funext ν
  simp only [castS, Pi.add_apply, unit, e4]
  by_cases h : ν = μ
  · subst h; simp
  · simp [Pi.single_eq_of_ne h]

lemma castS_sub_e4 (z : Fin 4 → ℤ) (μ : Fin 4) : castS (n := n) (z - e4 μ) = castS z - unit n μ := by
  funext ν
  simp only [castS, Pi.sub_apply, unit, e4]
  by_cases h : ν = μ
  · subst h; simp
  · simp [Pi.single_eq_of_ne h]

/-- The periodic function of a `0`-form, with values in `VS N 1`. -/
def liftF (u : Site n → Mat) : (Fin 4 → ℤ) → VS N 1 := fun z => vecOf fun _ => u (castS z)

/-- The field of the layer, `Ã = LʲX`. -/
def Atil (c : ℝ) (X : Fin 4 → Site n → Mat) : Fin 4 → (Fin 4 → ℤ) → Mat := fun μ z => c • X μ (castS z)

/-- The configuration `𝐔 = e^{iX}`. -/
def cfgX (X : Fin 4 → Site n → Mat) : Config N n := fun μ x => expU (Complex.I • X μ x)

lemma vecOf_sub (X Y : Fin 1 → Mat) : vecOf (fun k => X k - Y k) = vecOf X - vecOf Y := by ext p; rfl

lemma vecOf_add (X Y : Fin 1 → Mat) : vecOf (fun k => X k + Y k) = vecOf X + vecOf Y := by ext p; rfl

lemma vecOf_csmul (c : ℂ) (X : Fin 1 → Mat) : vecOf (fun k => c • X k) = c • vecOf X := by ext p; rfl

lemma vecOf_rsmul (c : ℝ) (X : Fin 1 → Mat) : vecOf (fun k => ((c : ℝ) : ℂ) • X k) = c • vecOf X := by
  ext p; simp [vecOf, Complex.real_smul]

lemma vecOf_sum {ι : Type*} (s : Finset ι) (X : ι → Fin 1 → Mat) :
    vecOf (fun k => ∑ i ∈ s, X i k) = ∑ i ∈ s, vecOf (X i) := by
  ext p; simp [vecOf]

lemma AdV_vecOf (W : GLN) (X : Fin 1 → Mat) : AdV W (vecOf X) = vecOf fun k => Ad W (X k) := by
  rw [liftV_apply]; rfl

variable {c : ℝ}

lemma Uf_Atil (hc : c ≠ 0) (X : Fin 4 → Site n → Mat) (μ : Fin 4) (z : Fin 4 → ℤ) :
    Uf c⁻¹ (Atil c X) μ z = cfgX X μ (castS z) := by
  simp only [Uf, Atil, cfgX, smul_smul, inv_mul_cancel₀ hc, one_smul]

lemma Ub_Atil (hc : c ≠ 0) (X : Fin 4 → Site n → Mat) (μ : Fin 4) (z : Fin 4 → ℤ) :
    Ub c⁻¹ (Atil c X) μ z = (cfgX X).val ⟨castS z, μ, false⟩ := by
  simp only [Ub, Atil, cfgX, smul_smul, inv_mul_cancel₀ hc, one_smul, Config.val, castS_sub_e4]
  rw [expU_inv, smul_neg]
  rfl

/-- **The forward differences of the layer.** -/
theorem DfwV_lift (hc : c ≠ 0) (X : Fin 4 → Site n → Mat) (μ : Fin 4) (u : Site n → Mat) :
    DfwV c⁻¹ (Atil c X) μ (liftF u) = liftF (fun x => ((c : ℝ) : ℂ) • Dfw 1 (cfgX X) μ u x) := by
  funext z
  simp only [DfwV, liftF, Uf_Atil hc, castS_add_e4, AdV_vecOf, inv_inv, Dfw, inv_one, one_smul]
  rw [← vecOf_sub, ← vecOf_rsmul]

/-- **The backward differences of the layer.** -/
theorem DbwV_lift (hc : c ≠ 0) (X : Fin 4 → Site n → Mat) (μ : Fin 4) (u : Site n → Mat) :
    DbwV c⁻¹ (Atil c X) μ (liftF u) = liftF (fun x => ((c : ℝ) : ℂ) • Dbw 1 (cfgX X) μ u x) := by
  funext z
  simp only [DbwV, liftF, Ub_Atil hc, castS_sub_e4, AdV_vecOf, inv_inv, Dbw, inv_one, one_smul]
  rw [← vecOf_sub, ← vecOf_rsmul]

lemma liftF_smul (a : ℂ) (u : Site n → Mat) : liftF (fun x => a • u x) = fun z => a • liftF (N := N) u z := by
  funext z; simp only [liftF]; rw [vecOf_csmul]

lemma Dbw_smul (a : ℂ) (U : Config N n) (μ : Fin 4) (u : Site n → Mat) (x : Site n) :
    Dbw 1 U μ (fun y => a • u y) x = a • Dbw 1 U μ u x := by
  simp only [Dbw, Ad_smul, inv_one, one_smul, smul_sub]

/-- **The covariant Laplacian of the layer is `L^{2j}` times that of the fine lattice.** -/
theorem covLapV_lift (hc : c ≠ 0) (X : Fin 4 → Site n → Mat) (u : Site n → Mat) (z : Fin 4 → ℤ) :
    covLapV c⁻¹ (Atil c X) (liftF u) z = liftF (fun x => ((c ^ 2 : ℝ) : ℂ) • Lap 1 (cfgX X) u x) z := by
  simp only [covLapV, DfwV_lift hc, DbwV_lift hc, Dbw_smul]
  simp only [liftF, Lap, smul_smul, Finset.smul_sum]
  rw [vecOf_sum]
  refine sum_congr rfl fun μ _ => ?_
  congr 1
  funext k
  congr 1
  push_cast; ring

/-- The `D^*` term of the layer: `Σ_μD^*_μ(Lʲg_μ)` of the layer is `L^{2j}D^*_𝐔g` of the fine lattice. -/
theorem sum_DbwV_lift (hc : c ≠ 0) (X : Fin 4 → Site n → Mat) (g : Fin 4 → Site n → Mat) (z : Fin 4 → ℤ) :
    ∑ μ, DbwV c⁻¹ (Atil c X) μ (liftF (fun x => ((c : ℝ) : ℂ) • g μ x)) z =
      liftF (fun x => ((c ^ 2 : ℝ) : ℂ) • Ds1 1 (cfgX X) g x) z := by
  simp only [DbwV_lift hc, Dbw_smul]
  simp only [liftF, Ds1, smul_smul, Finset.smul_sum]
  rw [vecOf_sum]
  refine sum_congr rfl fun μ _ => ?_
  congr 1
  funext k
  congr 1
  push_cast; ring

/-- `‖ũ(z)‖² = N|u(z mod N₀)|²` with the Hilbert–Schmidt norm `|·|`. -/
lemma norm_liftF_sq (u : Site n → Mat) (z : Fin 4 → ℤ) : ‖liftF (N := N) u z‖ ^ 2 = N * hs2 (u (castS z)) := by
  rw [liftF, normV_sq]; simp

lemma norm_liftF (u : Site n → Mat) (z : Fin 4 → ℤ) : ‖liftF (N := N) u z‖ = Real.sqrt N * hs (u (castS z)) := by
  rw [← Real.sqrt_sq (norm_nonneg _), norm_liftF_sq, Real.sqrt_mul (Nat.cast_nonneg _), ← hs_sq,
    Real.sqrt_sq (hs_nonneg _)]

end SFBox
end CoreLean

end
