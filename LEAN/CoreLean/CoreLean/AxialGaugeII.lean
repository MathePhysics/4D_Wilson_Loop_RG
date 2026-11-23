/-
`lem:admissible-explicit` of BALABAN_CORE.tex (`8913c33305b3`): the values in `G` in (iii), and (iv), in the
abstract form of `AxialGauge.lean`.

* `rep_mem`: the solution `rep` of `u(x) = a(x)⁻¹u(p x)b(x)` with the values `top` from the level `j` on has
  values in a subgroup `H` if `top`, `a`, `b` have.
* `admissible_mem` (`(iii)`, the values in `G`): the transformation `u_A` of `admissible_unique` has values in
  `H` if the transports of the two configurations and the site factors `v_j` have; for `𝐔₀` a gauge field
  and `A` with values in `𝔤` these lie in `G` (`lem:average`, `lem:group-mean`).
* `admissible_eq` (`(iv)`): a gauge transformation which satisfies the two conditions of (iii), as the
  admissible transformation of `thm:landau-gauge` does (`W^u` in the axial gauge of `U₀`, `N^j(u) = id`), is
  `u_A`.
-/
import CoreLean.AxialGauge

open NormedSpace

noncomputable section

namespace CoreLean

namespace Axial

section Recursion

variable {Gp : Type*} [Group Gp] {X : ℕ → Type*} {j : ℕ} {p : ∀ n, X n → X (n + 1)}

/-- The solution of the recursion has values in `H` if its data have. -/
theorem rep_mem (H : Subgroup Gp) {top a b : ∀ n, X n → Gp} (htop : ∀ n x, top n x ∈ H)
    (ha : ∀ n x, a n x ∈ H) (hb : ∀ n x, b n x ∈ H) : ∀ n x, rep j p top a b n x ∈ H := by
  have key : ∀ k n, j - n = k → ∀ x, rep j p top a b n x ∈ H := by
    intro k
    induction k with
    | zero =>
      intro n hk x
      rw [rep_of_ge (by omega)]
      exact htop n x
    | succ k ih =>
      intro n hk x
      rw [rep_of_lt (by omega)]
      exact H.mul_mem (H.mul_mem (H.inv_mem (ha n x)) (ih (n + 1) (by omega) _)) (hb n x)
  exact fun n x => key _ n rfl x

end Recursion

section Averaged

variable {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "GLN" => (Matrix (Fin N) (Fin N) ℂ)ˣ

variable {X : ℕ → Type*} [∀ n, Fintype (X n)] [∀ n, DecidableEq (X n)]

/-- `lem:admissible-explicit`(iii), the values in `G`: every transformation with the two conditions of (iii)
has values in `H` if the transports `T₀`, `M_𝔱` and the site factors `v_j` have. -/
theorem admissible_mem (H : Subgroup GLN) (p : ∀ n, X n → X (n + 1)) (ι : ∀ n, X (n + 1) → X n) (c : ℂ)
    (T0 : ∀ n, X n → GLN) (j : ℕ) (Mt Wt : ∀ n, X n → GLN)
    (hM : ∀ n, n < j → ∀ x, Mt n x = vfac p ι c T0 Wt n (ι n (p n x)) * Wt n x *
      (vfac p ι c T0 Wt n x)⁻¹)
    (hT0 : ∀ n x, T0 n x ∈ H) (hMt : ∀ n x, Mt n x ∈ H) (hv : ∀ y, vfac p ι c T0 Wt j y ∈ H)
    (u : ∀ n, X n → GLN) (hu1 : ∀ n, j < n → ∀ x, u n x = 1)
    (hurec : ∀ n, n < j → ∀ x, T0 n x * u n x = u (n + 1) (p n x) * Mt n x)
    (hucomp : ∀ n, n < j → ∀ y, u n (ι n y) = u (n + 1) y) (huN : ∀ y, Npow p ι c T0 u j y = 1) :
    ∀ n x, u n x ∈ H := by
  classical
  set top : ∀ n, X n → GLN := fun n x => if n = j then (vfac p ι c T0 Wt n x)⁻¹ else 1 with htopd
  have htopH : ∀ n x, top n x ∈ H := fun n x => by
    simp only [htopd]
    split_ifs with h
    · subst h; exact H.inv_mem (hv x)
    · exact H.one_mem
  have hrep : ∀ n x, u n x = rep j p top T0 Mt n x := by
    intro n x
    refine rep_unique u (fun n hn x => ?_) (fun n hn x => ?_) n x
    · rcases Nat.eq_or_lt_of_le hn with h | hlt
      · subst h
        have := huN x
        rw [N_eq p ι c T0 j u Mt Wt hurec hM hucomp j le_rfl x] at this
        simp only [htopd, ↓reduceIte]
        exact eq_inv_of_mul_eq_one_left this
      · rw [hu1 n hlt x]; simp [htopd, hlt.ne']
    · rw [← hurec n hn x]; group
  intro n x
  rw [hrep n x]
  exact rep_mem H htopH hT0 hMt n x

/-- `lem:admissible-explicit`(iv): two transformations with the two conditions of (iii) agree; so the
admissible transformation of `thm:landau-gauge`, which satisfies them, is `u_A`. -/
theorem admissible_eq (p : ∀ n, X n → X (n + 1)) (ι : ∀ n, X (n + 1) → X n) (c : ℂ)
    (T0 : ∀ n, X n → GLN) (j : ℕ) (Mt Wt : ∀ n, X n → GLN)
    (hM : ∀ n, n < j → ∀ x, Mt n x = vfac p ι c T0 Wt n (ι n (p n x)) * Wt n x *
      (vfac p ι c T0 Wt n x)⁻¹)
    (hp : ∀ n y, p n (ι n y) = y) (hT : ∀ n y, T0 n (ι n y) = 1) (hMt : ∀ n y, Mt n (ι n y) = 1)
    (u u' : ∀ n, X n → GLN)
    (hu : (∀ n, j < n → ∀ x, u n x = 1) ∧ (∀ n, n < j → ∀ x, T0 n x * u n x = u (n + 1) (p n x) * Mt n x) ∧
      (∀ n, n < j → ∀ y, u n (ι n y) = u (n + 1) y) ∧ (∀ y, Npow p ι c T0 u j y = 1))
    (hu' : (∀ n, j < n → ∀ x, u' n x = 1) ∧
      (∀ n, n < j → ∀ x, T0 n x * u' n x = u' (n + 1) (p n x) * Mt n x) ∧
      (∀ n, n < j → ∀ y, u' n (ι n y) = u' (n + 1) y) ∧ (∀ y, Npow p ι c T0 u' j y = 1)) :
    u = u' :=
  (admissible_unique p ι c T0 j Mt Wt hM hp hT hMt).unique hu hu'

end Averaged

end Axial

end CoreLean

end
