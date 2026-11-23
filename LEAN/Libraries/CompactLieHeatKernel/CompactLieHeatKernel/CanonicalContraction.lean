import Mathlib.Analysis.InnerProductSpace.CanonicalTensor

/-!
# Basis-free contraction of a bilinear form

The key algebraic observation for the group Laplacian is that the expression

`∑ i, B (e i) (e i)`

is independent of the orthonormal basis `e`.  Rather than proving this by coordinate changes, we
contract `B` with mathlib's canonical covariant tensor.  The orthonormal-basis formula is then an
immediate theorem.
-/

noncomputable section

open TensorProduct
open scoped BigOperators

namespace CompactLieHeatKernel

variable
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Forget continuity in both slots of a continuous bilinear map. -/
def continuousBilinearToLinear (B : V →L[ℝ] V →L[ℝ] F) : V →ₗ[ℝ] V →ₗ[ℝ] F where
  toFun v := (B v).toLinearMap
  map_add' v w := by
    ext u
    simp
  map_smul' c v := by
    ext u
    simp

/-- Basis-free contraction of a continuous bilinear map against the inverse metric tensor. -/
def contractDiagonal (B : V →L[ℝ] V →L[ℝ] F) : F :=
  TensorProduct.lift (continuousBilinearToLinear B)
    (InnerProductSpace.canonicalCovariantTensor V)

/-- Computation of the contraction in an arbitrary orthonormal basis. -/
theorem contractDiagonal_eq_sum {ι : Type*} [Fintype ι]
    (B : V →L[ℝ] V →L[ℝ] F) (e : OrthonormalBasis ι ℝ V) :
    contractDiagonal B = ∑ i, B (e i) (e i) := by
  rw [contractDiagonal, InnerProductSpace.canonicalCovariantTensor_eq_sum V e]
  simp [continuousBilinearToLinear]

/-- The diagonal sum of a continuous bilinear map is independent of the orthonormal basis. -/
theorem sum_diagonal_orthonormalBasis_independent
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (B : V →L[ℝ] V →L[ℝ] F)
    (e : OrthonormalBasis ι ℝ V) (d : OrthonormalBasis κ ℝ V) :
    (∑ i, B (e i) (e i)) = ∑ j, B (d j) (d j) := by
  rw [← contractDiagonal_eq_sum B e, ← contractDiagonal_eq_sum B d]

end CompactLieHeatKernel
