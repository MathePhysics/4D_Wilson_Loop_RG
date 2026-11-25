/-
The block points `ptB` of the levels as base-`L` numbers: the identification of the composite average at the trivial
configuration (`Q_trivial_levels`) with the mean over the block of the fine lattice.

* `Dg`: the digit value `Σ_i p_i L^{l-1-i}` of the offsets; `ptB_closed`: `ptB h l y p = y + Dg p - H_l`.
* `ptEquiv`, `Dg_ptEquiv`, `sum_ptB`: the digits are a bijection onto `[0, L^l)⁴` (`finFunctionFinEquiv`).
-/
import CoreLean.RelativeAverageQuadratic

open Finset

noncomputable section

namespace CoreLean
namespace RelativeAverage

open BlockPaths AxialStraightLattice RegularAverages

/-- The digit value of the offsets: `Dg(p)_σ = Σ_i p_i(σ)L^{l-1-i}`, `p 0` the most significant digit. -/
def Dg (h l : ℕ) (p : Fin l → Pts h) : Fin 4 → ℤ := fun σ => ∑ i : Fin l, ((p i σ : ℕ) : ℤ) * Lz h ^ (l - 1 - i)

lemma Dg_succ (h l : ℕ) (p : Fin (l + 1) → Pts h) :
    Dg h (l + 1) p = Lz h ^ l • (fun σ => ((p 0 σ : ℕ) : ℤ)) + Dg h l (Fin.tail p) := by
  funext σ
  simp only [Dg, Fin.sum_univ_succ, Fin.val_zero, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Fin.tail,
    Fin.val_succ]
  congr 1
  · rw [show l + 1 - 1 - 0 = l by omega]; ring
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [show l + 1 - 1 - (i + 1) = l - 1 - i by omega]

lemma Hw_succ (h l : ℕ) : Hw h (l + 1) 0 = Lz h ^ l * h + Hw h l 0 := by
  have h1 := two_Hw h (l + 1) 0
  have h2 := two_Hw h l 0
  have hL : Lz h = 2 * h + 1 := rfl
  rw [pow_succ, pow_zero] at h1
  rw [pow_zero] at h2
  have : 2 * Hw h (l + 1) 0 = 2 * (Lz h ^ l * h + Hw h l 0) := by rw [h1, mul_add, h2, hL]; ring
  omega

/-- **The block points in closed form**: `ptB h l y p = y + Dg(p) - H_l`, `H_l = (L^l - 1)/2`. -/
theorem ptB_closed (h : ℕ) : ∀ (l : ℕ) (y : Fin 4 → ℤ) (p : Fin l → Pts h),
    ptB h l y p = y + Dg h l p - fun _ => Hw h l 0
  | 0, y, p => by
    funext σ
    simp [ptB, Dg, Hw]
  | l + 1, y, p => by
    rw [ptB, ptB_closed h l, Dg_succ]
    funext σ
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, offP, Hw_succ]
    ring

/-- The digits as an equivalence onto `[0, L^l)⁴`. -/
def ptEquiv (h l : ℕ) : (Fin l → Pts h) ≃ (Fin 4 → Fin ((2 * h + 1) ^ l)) :=
  ((Equiv.piComm (fun (_ : Fin l) (_ : Fin 4) => Fin (2 * h + 1)) :
      (Fin l → Fin 4 → Fin (2 * h + 1)) ≃ (Fin 4 → Fin l → Fin (2 * h + 1)))).trans
    (Equiv.piCongrRight fun _ => (Equiv.arrowCongr Fin.revPerm (Equiv.refl _)).trans finFunctionFinEquiv)

lemma ptEquiv_val (h l : ℕ) (p : Fin l → Pts h) (σ : Fin 4) :
    (ptEquiv h l p σ : ℕ) = ∑ i : Fin l, ((p (Fin.rev i) σ : ℕ)) * (2 * h + 1) ^ (i : ℕ) := by
  simp only [ptEquiv, Equiv.trans_apply, Equiv.piCongrRight_apply, Pi.map_apply, Equiv.piComm_apply,
    Equiv.arrowCongr_apply, Equiv.refl_apply, Function.comp_apply, finFunctionFinEquiv_apply, Fin.revPerm_symm,
    Fin.revPerm_apply]

lemma Dg_ptEquiv (h l : ℕ) (p : Fin l → Pts h) (σ : Fin 4) :
    Dg h l p σ = ((ptEquiv h l p σ : ℕ) : ℤ) := by
  rw [ptEquiv_val]
  push_cast
  refine Fintype.sum_equiv Fin.revPerm _ _ fun i => ?_
  simp only [Fin.revPerm_apply, Fin.rev_rev, Fin.val_rev, Lz]
  push_cast
  congr 2
  omega

/-- **The sum over the block points**: `Σ_p F(ptB h l y p) = Σ_{o ∈ [0, L^l)⁴} F(y + o - H_l)`. -/
theorem sum_ptB {M : Type*} [AddCommMonoid M] (h l : ℕ) (y : Fin 4 → ℤ) (F : (Fin 4 → ℤ) → M) :
    ∑ p : Fin l → Pts h, F (ptB h l y p) =
      ∑ o : Fin 4 → Fin ((2 * h + 1) ^ l), F (y + (fun σ => ((o σ : ℕ) : ℤ)) - fun _ => Hw h l 0) := by
  refine Fintype.sum_equiv (ptEquiv h l) _ _ fun p => ?_
  rw [ptB_closed, show Dg h l p = fun σ => ((ptEquiv h l p σ : ℕ) : ℤ) from funext (Dg_ptEquiv h l p)]

end RelativeAverage
end CoreLean

end
