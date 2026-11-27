import CoreLean.WilsonLoop.GaugeGroup

/-!
# The differential of a representation is well defined

`CoreLean.WilsonLoop.Irrep.IsDifferential π A D` characterises `D = dπ(iA)` by
`π(e^{itA}) = e^{tD}` for all real `t` with `e^{itA} ∈ G`.  This file checks that the
characterisation determines `D`, and that it is not empty.

## Main statements

* `CoreLean.WilsonLoop.eq_of_exp_smul_eq`: a matrix is determined by its one-parameter group.
* `CoreLean.WilsonLoop.Irrep.IsDifferential.unique`: for `A ∈ 𝔤 = G.lie` there is at most one
  such `D`.
* `CoreLean.WilsonLoop.Irrep.isDifferential_zero`: `dπ(0) = 0`, so that the set whose supremum is
  `c_π` is not empty.
-/

namespace CoreLean

namespace WilsonLoop

open Complex

open scoped Matrix.Norms.L2Operator

variable {N : ℕ} {G : GaugeGroup N}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ

/-- A matrix is determined by its one-parameter group. -/
theorem eq_of_exp_smul_eq {d : ℕ} {D D' : Matrix (Fin d) (Fin d) ℂ}
    (h : ∀ t : ℝ, NormedSpace.exp (t • D) = NormedSpace.exp (t • D')) : D = D' := by
  have h1 := hasDerivAt_exp_smul_const (𝕂 := ℝ) D (0 : ℝ)
  have h2 := hasDerivAt_exp_smul_const (𝕂 := ℝ) D' (0 : ℝ)
  have h3 : (fun u : ℝ ↦ NormedSpace.exp (u • D)) = fun u : ℝ ↦ NormedSpace.exp (u • D') :=
    funext h
  rw [h3] at h1
  simpa using h1.unique h2

/-- The differential `dπ(iA)` at `A ∈ 𝔤` is unique. -/
theorem Irrep.IsDifferential.unique {π : Irrep G} {A : Mat} (hA : A ∈ G.lie)
    {D D' : Matrix (Fin π.dim) (Fin π.dim) ℂ} (h : π.IsDifferential A D)
    (h' : π.IsDifferential A D') : D = D' := by
  refine eq_of_exp_smul_eq fun t ↦ ?_
  rw [← h t (hA.2 t), ← h' t (hA.2 t)]

/-- `dπ(0) = 0`. -/
theorem Irrep.isDifferential_zero (π : Irrep G) : π.IsDifferential 0 0 := by
  intro t h
  have h1 : (⟨expU ((I * t) • (0 : Mat)), h⟩ : G.carrier) = 1 := Subtype.ext (by simp)
  rw [h1]
  simp

end WilsonLoop

end CoreLean
