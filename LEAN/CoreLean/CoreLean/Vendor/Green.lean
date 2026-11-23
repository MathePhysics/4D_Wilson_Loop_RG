module

public import CoreLean.Vendor.HeatKernelBounds

/-!
# The lattice heat kernel on `ℤ^d` and the lattice Green's function

`p_t(x) = ∏_μ q_t(x_μ)` and `C(x) = ∫_0^∞ p_t(x) dt`.  This file collects the product structure
(`heatDiffProd`) and the time-integral bounds that give the pointwise decay of `C` and of its
finite differences.

Provenance: copied from `Balaban/Green/Lattice/Green.lean` of
https://github.com/scottnarmstrong/balaban-lean at commit `493e9eb`, Apache License 2.0
(`LICENSE-balaban-lean`); the only change is the import path.
-/

@[expose] public section

noncomputable section

namespace Balaban.LatticeGreen

open MeasureTheory Real Set Filter Topology

variable {d : ℕ}

/-- The product `∏_μ Δ^{m_μ} q_t (x_μ)` of one-dimensional differences. -/
def heatDiffProd (d : ℕ) (m : Fin d → ℕ) (t : ℝ) (x : Fin d → ℤ) : ℝ :=
  ∏ μ, heatDiff (m μ) t (x μ)

/-- The `d`-dimensional heat kernel `p_t(x) = ∏_μ q_t(x_μ)` of the nearest-neighbour walk. -/
def heatKernel (d : ℕ) (t : ℝ) (x : Fin d → ℤ) : ℝ := ∏ μ, heatKernel1 t (x μ)

theorem heatDiffProd_zero (d : ℕ) (t : ℝ) (x : Fin d → ℤ) :
    heatDiffProd d 0 t x = heatKernel d t x := by
  simp [heatDiffProd, heatKernel, heatDiff]

theorem continuous_heatDiff (m : ℕ) (n : ℤ) : Continuous fun t => heatDiff m t n := by
  induction m generalizing n with
  | zero => exact continuous_heatKernel1 n
  | succ m ih => exact (ih (n + 1)).sub (ih n)

theorem continuous_heatDiffProd (m : Fin d → ℕ) (x : Fin d → ℤ) :
    Continuous fun t => heatDiffProd d m t x :=
  continuous_finsetProd _ fun _ _ => continuous_heatDiff _ _

theorem heatDiffProd_shift (m : Fin d → ℕ) (μ : Fin d) (t : ℝ) (x : Fin d → ℤ) :
    heatDiffProd d m t (x + Pi.single μ 1) - heatDiffProd d m t x =
      heatDiffProd d (m + Pi.single μ 1) t x := by
  unfold heatDiffProd
  have e : ∀ f : Fin d → ℝ, ∏ ν, f ν = f μ * ∏ ν ∈ Finset.univ.erase μ, f ν :=
    fun f => (Finset.mul_prod_erase _ _ (Finset.mem_univ μ)).symm
  have e1 : ∏ ν, heatDiff (m ν) t ((x + (Pi.single μ 1 : Fin d → ℤ)) ν) =
      heatDiff (m μ) t ((x + (Pi.single μ 1 : Fin d → ℤ)) μ) *
        ∏ ν ∈ Finset.univ.erase μ, heatDiff (m ν) t ((x + (Pi.single μ 1 : Fin d → ℤ)) ν) := e _
  have e2 : ∏ ν, heatDiff (m ν) t (x ν) =
      heatDiff (m μ) t (x μ) * ∏ ν ∈ Finset.univ.erase μ, heatDiff (m ν) t (x ν) := e _
  have e3 : ∏ ν, heatDiff ((m + (Pi.single μ 1 : Fin d → ℕ)) ν) t (x ν) =
      heatDiff ((m + (Pi.single μ 1 : Fin d → ℕ)) μ) t (x μ) *
        ∏ ν ∈ Finset.univ.erase μ, heatDiff ((m + (Pi.single μ 1 : Fin d → ℕ)) ν) t (x ν) := e _
  rw [e1, e2, e3]
  have h1 : ∏ ν ∈ Finset.univ.erase μ, heatDiff (m ν) t ((x + (Pi.single μ 1 : Fin d → ℤ)) ν) =
      ∏ ν ∈ Finset.univ.erase μ, heatDiff (m ν) t (x ν) :=
    Finset.prod_congr rfl fun ν hν => by
      rw [Pi.add_apply, Pi.single_eq_of_ne (Finset.ne_of_mem_erase hν), add_zero]
  have h2 : ∏ ν ∈ Finset.univ.erase μ, heatDiff ((m + (Pi.single μ 1 : Fin d → ℕ)) ν) t (x ν) =
      ∏ ν ∈ Finset.univ.erase μ, heatDiff (m ν) t (x ν) :=
    Finset.prod_congr rfl fun ν hν => by
      rw [Pi.add_apply, Pi.single_eq_of_ne (Finset.ne_of_mem_erase hν), add_zero]
  rw [h1, h2]
  simp only [Pi.add_apply, Pi.single_eq_same, heatDiff]
  ring

end Balaban.LatticeGreen
