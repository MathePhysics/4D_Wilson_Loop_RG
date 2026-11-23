/-
The analyticity and the locality in `lem:axial-representative` and the holomorphy in `lem:admissible-explicit`(iii) of
BALABAN_CORE.tex (`7374c382ba1b`), in the abstract form of `AxialGauge.lean`.

* `rep_differentiableAt`: the solution of `u(x) = a(x)⁻¹u(p x)b(x)` below the level `j` with the values `top` from the
  level `j` on depends holomorphically on a parameter on which the data `a`, `b`, `top` depend holomorphically
  (`u(x_n)` is a product of the data along the chain of `x_n` and their inverses).
* `rep_local`: it depends only on the data along the chain.
* `axial_representative_holo`: the representative in the axial gauge (`lem:axial-representative`) is holomorphic in the
  transports; `admissible_holo`: the admissible transformation `u_A` (`lem:admissible-explicit`(iii)) is holomorphic in
  the transports and the site factor `v_j`.
-/
import CoreLean.AxialGauge

open NormedSpace
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace CoreLean
namespace Axial

variable {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "GLN" => (Matrix (Fin N) (Fin N) ℂ)ˣ

variable {X : ℕ → Type*} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

lemma units_inv_differentiableAt {W : E → GLN} {e₀ : E} (hW : DifferentiableAt ℂ (fun e => ((W e : GLN) : Mat)) e₀) :
    DifferentiableAt ℂ (fun e => (((W e)⁻¹ : GLN) : Mat)) e₀ := by
  have h : (fun e => (((W e)⁻¹ : GLN) : Mat)) = fun e => Ring.inverse ((W e : GLN) : Mat) := by
    funext e; rw [Ring.inverse_unit]
  rw [h]
  exact hW.inverse (W e₀).isUnit

/-- **The analyticity of the solution of the downward recursion**: if `a`, `b`, and `top` depend holomorphically on a
parameter at `e₀`, so does `rep`. -/
theorem rep_differentiableAt (j : ℕ) (p : ∀ n, X n → X (n + 1)) (topf af bf : E → ∀ n, X n → GLN) (e₀ : E)
    (htop : ∀ n x, DifferentiableAt ℂ (fun e => ((topf e n x : GLN) : Mat)) e₀)
    (ha : ∀ n x, DifferentiableAt ℂ (fun e => ((af e n x : GLN) : Mat)) e₀)
    (hb : ∀ n x, DifferentiableAt ℂ (fun e => ((bf e n x : GLN) : Mat)) e₀) (n : ℕ) (x : X n) :
    DifferentiableAt ℂ (fun e => ((rep j p (topf e) (af e) (bf e) n x : GLN) : Mat)) e₀ := by
  by_cases h : n < j
  · have ih := rep_differentiableAt j p topf af bf e₀ htop ha hb (n + 1) (p n x)
    have e : (fun e => ((rep j p (topf e) (af e) (bf e) n x : GLN) : Mat)) =
        fun e => (((af e n x)⁻¹ : GLN) : Mat) * ((rep j p (topf e) (af e) (bf e) (n + 1) (p n x) : GLN) : Mat) *
          ((bf e n x : GLN) : Mat) := by
      funext e; rw [rep_of_lt h, Units.val_mul, Units.val_mul]
    rw [e]
    exact ((units_inv_differentiableAt (ha n x)).mul ih).mul (hb n x)
  · have e : (fun e => ((rep j p (topf e) (af e) (bf e) n x : GLN) : Mat)) = fun e => ((topf e n x : GLN) : Mat) := by
      funext e; rw [rep_of_ge (not_lt.mp h)]
    rw [e]
    exact htop n x
termination_by j - n

/-- **The locality of the solution**: `rep` at `x` depends only on the data at the points of the chain of `x` below the
level `j` and on `top` at the level `j`, through the hypothesis that two families of data agree along all chains. -/
theorem rep_local {Gp : Type*} [Group Gp] (j : ℕ) (p : ∀ n, X n → X (n + 1)) (top a b top' a' b' : ∀ n, X n → Gp)
    (S : ∀ n, Set (X n)) (hS : ∀ n, n < j → ∀ x ∈ S n, p n x ∈ S (n + 1))
    (hab : ∀ n, n < j → ∀ x ∈ S n, a n x = a' n x ∧ b n x = b' n x) (htop : ∀ n, j ≤ n → ∀ x ∈ S n, top n x = top' n x)
    (n : ℕ) (x : X n) (hx : x ∈ S n) :
    rep j p top a b n x = rep j p top' a' b' n x := by
  by_cases h : n < j
  · rw [rep_of_lt h, rep_of_lt h, (hab n h x hx).1, (hab n h x hx).2,
      rep_local j p top a b top' a' b' S hS hab htop (n + 1) (p n x) (hS n h x hx)]
  · rw [rep_of_ge (not_lt.mp h), rep_of_ge (not_lt.mp h), htop n (not_lt.mp h) x hx]
termination_by j - n

/-- **`lem:axial-representative`, the analyticity**: the representative in the axial gauge, `rep` with the values `id`
from the level `j` on, is holomorphic in a parameter on which the transports of `M^n(U₀)` and `M^n(U)` depend
holomorphically. -/
theorem axial_representative_holo (j : ℕ) (p : ∀ n, X n → X (n + 1)) (af bf : E → ∀ n, X n → GLN) (e₀ : E)
    (ha : ∀ n x, DifferentiableAt ℂ (fun e => ((af e n x : GLN) : Mat)) e₀)
    (hb : ∀ n x, DifferentiableAt ℂ (fun e => ((bf e n x : GLN) : Mat)) e₀) (n : ℕ) (x : X n) :
    DifferentiableAt ℂ (fun e => ((rep j p (fun _ _ => 1) (af e) (bf e) n x : GLN) : Mat)) e₀ :=
  rep_differentiableAt j p (fun _ _ _ => 1) af bf e₀ (fun _ _ => differentiableAt_const _) ha hb n x

/-- **`lem:admissible-explicit`(iii), the holomorphy**: the admissible transformation `u_A`, the solution of
`T₀(x)u(x) = u(p x)M_𝔱(x)` below the level `j` with `u(y) = v_j(y)⁻¹` at the level `j` and `id` above, is holomorphic in a
parameter on which the transports `T₀`, `M_𝔱` and the site factor `v_j` depend holomorphically. -/
theorem admissible_holo (j : ℕ) (p : ∀ n, X n → X (n + 1)) (T0f Mtf vf : E → ∀ n, X n → GLN)
    (e₀ : E) (hT : ∀ n x, DifferentiableAt ℂ (fun e => ((T0f e n x : GLN) : Mat)) e₀)
    (hM : ∀ n x, DifferentiableAt ℂ (fun e => ((Mtf e n x : GLN) : Mat)) e₀)
    (hv : ∀ x, DifferentiableAt ℂ (fun e => ((vf e j x : GLN) : Mat)) e₀) (n : ℕ) (x : X n) :
    DifferentiableAt ℂ (fun e => ((rep j p (fun m y => if m = j then (vf e m y)⁻¹ else 1)
      (T0f e) (Mtf e) n x : GLN) : Mat)) e₀ := by
  refine rep_differentiableAt j p (fun e m y => if m = j then (vf e m y)⁻¹ else 1) T0f Mtf e₀ ?_ hT hM n x
  intro m y
  by_cases hm : m = j
  · subst hm
    simp only [if_true]
    exact units_inv_differentiableAt (hv y)
  · simp only [if_neg hm]
    exact differentiableAt_const _

end Axial
end CoreLean

end
