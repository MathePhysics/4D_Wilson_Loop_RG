/-
The concrete layer, step C5, abstract part (`CONCRETE_LAYER.md`): the inverses of `def:operators` of BALABAN_CORE.tex
(`615c66b253fe`), taken on the forms which vanish outside the Dirichlet domain (`def:dirichlet-domain`(i)) and have
their values in `𝔤^c`.

An operator `T` is replaced by its compression `ΠTΠ` with an idempotent `Π` (the indicator of the Dirichlet domain
times the projection onto `𝔤^c`, which the core does not write), and its inverse is the inverse of `ΠTΠ` in the corner
`Π End Π`:

* `cinv Π T = Π (ΠTΠ + 1 - Π)⁻¹`, with `Ring.inverse` (zero when `ΠTΠ + 1 - Π` is not invertible); it is `Π`-supported
  on both sides (`P_cinv`, `cinv_P`), and when `ΠTΠ + 1 - Π` is invertible it is a two-sided inverse of `ΠTΠ` there
  (`P_T_cinv`, `cinv_T_P`); for `Π = 1` it is the inverse `T⁻¹` (`cinv_one`).
* `Xop`, `Rop`: `P = G'Q'^*(Q'G'^2Q'^*)^{-1}Q'G'` and `R = I - P` of `def:operators`(iii), with the compressed inverses;
  `R` and `P` are idempotent (`Rop_idem`, `Xop_idem`) and `Q'G'R = 0` up to the compression (`Q_G_Rop`).
-/
import Mathlib

noncomputable section

namespace CoreLean
namespace CompressedInverse

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- `ΠTΠ + 1 - Π`. -/
def ckern (P T : Module.End ℂ V) : Module.End ℂ V := P * T * P + (1 - P)

/-- **The compressed inverse** `Π(ΠTΠ + 1 - Π)⁻¹`. -/
def cinv (P T : Module.End ℂ V) : Module.End ℂ V := P * Ring.inverse (ckern P T)

variable {P T : Module.End ℂ V}

lemma ckern_apply (x : V) : ckern P T x = P (T (P x)) + (x - P x) := rfl

lemma cinv_apply (x : V) : cinv P T x = P (Ring.inverse (ckern P T) x) := rfl

section Idem

variable (hP : ∀ x, P (P x) = P x)
include hP

lemma P_ckern (x : V) : P (ckern P T x) = P (T (P x)) := by
  rw [ckern_apply, map_add, map_sub, hP, hP, sub_self, add_zero]

lemma ckern_P (x : V) : ckern P T (P x) = P (T (P x)) := by
  rw [ckern_apply, hP, sub_self, add_zero]

/-- The inverse of `ΠTΠ + 1 - Π` commutes with `Π`. -/
lemma P_inv_comm (x : V) : P (Ring.inverse (ckern P T) x) = Ring.inverse (ckern P T) (P x) := by
  by_cases hK : IsUnit (ckern P T)
  · have h1 : ∀ y, ckern P T (Ring.inverse (ckern P T) y) = y := fun y =>
      LinearMap.congr_fun (Ring.mul_inverse_cancel _ hK) y
    have h2 : ∀ y, Ring.inverse (ckern P T) (ckern P T y) = y := fun y =>
      LinearMap.congr_fun (Ring.inverse_mul_cancel _ hK) y
    calc P (Ring.inverse (ckern P T) x)
        = Ring.inverse (ckern P T) (ckern P T (P (Ring.inverse (ckern P T) x))) := (h2 _).symm
      _ = Ring.inverse (ckern P T) (P (ckern P T (Ring.inverse (ckern P T) x))) := by
          rw [ckern_P hP, P_ckern hP]
      _ = Ring.inverse (ckern P T) (P x) := by rw [h1]
  · rw [Ring.inverse_non_unit _ hK]; simp

lemma P_cinv (x : V) : P (cinv P T x) = cinv P T x := by rw [cinv_apply, hP]

lemma cinv_P (x : V) : cinv P T (P x) = cinv P T x := by
  rw [cinv_apply, cinv_apply, ← P_inv_comm hP, hP]

section Unit

variable (hK : IsUnit (ckern P T))
include hK

/-- `Π T (cinv x) = Π x`: a right inverse of `ΠTΠ` on the range of `Π`. -/
lemma P_T_cinv (x : V) : P (T (cinv P T x)) = P x := by
  have h1 : ∀ y, ckern P T (Ring.inverse (ckern P T) y) = y := fun y =>
    LinearMap.congr_fun (Ring.mul_inverse_cancel _ hK) y
  rw [← P_cinv hP, cinv_apply, P_inv_comm hP, ← P_ckern hP, h1, hP]

/-- `cinv (T (Π x)) = Π x`: a left inverse of `ΠTΠ` on the range of `Π`. -/
lemma cinv_T_P (x : V) : cinv P T (T (P x)) = P x := by
  have h2 : ∀ y, Ring.inverse (ckern P T) (ckern P T y) = y := fun y =>
    LinearMap.congr_fun (Ring.inverse_mul_cancel _ hK) y
  rw [← cinv_P hP, cinv_apply, ← ckern_P (T := T) hP, h2, hP]

lemma cinv_T_cinv (x : V) : cinv P T (T (cinv P T x)) = cinv P T x := by
  conv_lhs => rw [← P_cinv hP x]
  rw [cinv_T_P hP hK, P_cinv hP]

end Unit

end Idem

/-- **The compressed inverse of a symmetric operator is symmetric**: if `Π` is idempotent and symmetric for a bilinear
form `B`, and `T` is symmetric on the range of `Π`, then `cinv Π T` is symmetric. -/
theorem cinv_symm (B : LinearMap.BilinForm ℂ V) (hP : ∀ x, P (P x) = P x) (hPs : ∀ x y, B (P x) y = B x (P y))
    (hT : ∀ a b, P a = a → P b = b → B (T a) b = B a (T b)) (hK : IsUnit (ckern P T)) (x y : V) :
    B (cinv P T x) y = B x (cinv P T y) := by
  have ha := P_cinv (T := T) hP x
  have hb := P_cinv (T := T) hP y
  calc B (cinv P T x) y = B (P (cinv P T x)) y := by rw [ha]
    _ = B (cinv P T x) (P y) := hPs _ _
    _ = B (cinv P T x) (P (T (cinv P T y))) := by rw [P_T_cinv hP hK y]
    _ = B (P (cinv P T x)) (T (cinv P T y)) := (hPs _ _).symm
    _ = B (cinv P T x) (T (cinv P T y)) := by rw [ha]
    _ = B (T (cinv P T x)) (cinv P T y) := (hT _ _ ha hb).symm
    _ = B (T (cinv P T x)) (P (cinv P T y)) := by rw [hb]
    _ = B (P (T (cinv P T x))) (cinv P T y) := (hPs _ _).symm
    _ = B (P x) (cinv P T y) := by rw [P_T_cinv hP hK x]
    _ = B x (P (cinv P T y)) := hPs _ _
    _ = B x (cinv P T y) := by rw [hb]

/-- For `Π = 1`, the compressed inverse is the inverse. -/
theorem cinv_one (T : Module.End ℂ V) : cinv 1 T = Ring.inverse T := by
  simp [cinv, ckern]

/-! ### The operators `P` and `R` -/

variable {W : Type*} [AddCommGroup W] [Module ℂ W]

/-- `Q'G'^2Q'^*`. -/
def Mop (Gp : Module.End ℂ V) (Q : V →ₗ[ℂ] W) (Qs : W →ₗ[ℂ] V) : Module.End ℂ W := Q ∘ₗ Gp ∘ₗ Gp ∘ₗ Qs

/-- `P = G'Q'^*(Q'G'^2Q'^*)^{-1}Q'G'`, the inverse compressed by `Π_B`. -/
def Xop (PB : Module.End ℂ W) (Gp : Module.End ℂ V) (Q : V →ₗ[ℂ] W) (Qs : W →ₗ[ℂ] V) : Module.End ℂ V :=
  Gp ∘ₗ Qs ∘ₗ cinv PB (Mop Gp Q Qs) ∘ₗ Q ∘ₗ Gp

/-- `R = I - P`, the identity compressed by `Π₀`. -/
def Rop (P0 : Module.End ℂ V) (PB : Module.End ℂ W) (Gp : Module.End ℂ V) (Q : V →ₗ[ℂ] W)
    (Qs : W →ₗ[ℂ] V) : Module.End ℂ V :=
  P0 - Xop PB Gp Q Qs

variable {PB : Module.End ℂ W} {P0 Gp : Module.End ℂ V} {Q : V →ₗ[ℂ] W} {Qs : W →ₗ[ℂ] V}

lemma Xop_apply (x : V) : Xop PB Gp Q Qs x = Gp (Qs (cinv PB (Mop Gp Q Qs) (Q (Gp x)))) := rfl

/-- `P² = P`. -/
theorem Xop_idem (hPB : ∀ y, PB (PB y) = PB y) (hK : IsUnit (ckern PB (Mop Gp Q Qs))) (x : V) :
    Xop PB Gp Q Qs (Xop PB Gp Q Qs x) = Xop PB Gp Q Qs x := by
  exact congrArg (fun z => Gp (Qs z)) (cinv_T_cinv hPB hK (Q (Gp x)))

/-- `R² = R`, for `G'` supported by the idempotent `Π₀` on both sides. -/
theorem Rop_idem (hP0 : ∀ x, P0 (P0 x) = P0 x) (hG1 : ∀ x, P0 (Gp x) = Gp x) (hG2 : ∀ x, Gp (P0 x) = Gp x)
    (hPB : ∀ y, PB (PB y) = PB y) (hK : IsUnit (ckern PB (Mop Gp Q Qs))) (x : V) :
    Rop P0 PB Gp Q Qs (Rop P0 PB Gp Q Qs x) = Rop P0 PB Gp Q Qs x := by
  have hPX : ∀ y, P0 (Xop PB Gp Q Qs y) = Xop PB Gp Q Qs y := fun y => by rw [Xop_apply, hG1]
  have hXP : ∀ y, Xop PB Gp Q Qs (P0 y) = Xop PB Gp Q Qs y := fun y => by rw [Xop_apply, Xop_apply, hG2]
  simp only [Rop, LinearMap.sub_apply, map_sub, hP0, hPX, hXP, Xop_idem hPB hK]
  abel

/-- `Π_B Q'G'R = 0`. -/
theorem Q_G_Rop (hG2 : ∀ x, Gp (P0 x) = Gp x) (hPB : ∀ y, PB (PB y) = PB y)
    (hK : IsUnit (ckern PB (Mop Gp Q Qs))) (x : V) : PB (Q (Gp (Rop P0 PB Gp Q Qs x))) = 0 := by
  have h := P_T_cinv hPB hK (Q (Gp x))
  change PB (Q (Gp (P0 x - Xop PB Gp Q Qs x))) = 0
  rw [map_sub, map_sub, map_sub, hG2, Xop_apply]
  change PB (Q (Gp x)) - PB (Mop Gp Q Qs (cinv PB (Mop Gp Q Qs) (Q (Gp x)))) = 0
  rw [h, sub_self]

/-! ### The operators `H = GQ^*(QGQ^*)^{-1}` and `G̃ = G - GQ^*(QGQ^*)^{-1}QG` -/

/-- `H = GQ^*(QGQ^*)^{-1}`, the inverse compressed by `Π_F`. -/
def Hop (PF : Module.End ℂ W) (G : Module.End ℂ V) (Q : V →ₗ[ℂ] W) (Qs : W →ₗ[ℂ] V) : W →ₗ[ℂ] V :=
  G ∘ₗ Qs ∘ₗ cinv PF (Q ∘ₗ G ∘ₗ Qs)

/-- `G̃ = G - GQ^*(QGQ^*)^{-1}QG`. -/
def Gtop (PF : Module.End ℂ W) (G : Module.End ℂ V) (Q : V →ₗ[ℂ] W) (Qs : W →ₗ[ℂ] V) : Module.End ℂ V :=
  G - Hop PF G Q Qs ∘ₗ Q ∘ₗ G

variable {PF : Module.End ℂ W} {G : Module.End ℂ V}

/-- **`QH = I`** on the compressed functions. -/
theorem Q_Hop (hPF : ∀ y, PF (PF y) = PF y) (hK : IsUnit (ckern PF (Q ∘ₗ G ∘ₗ Qs))) (μ : W) :
    PF (Q (Hop PF G Q Qs μ)) = PF μ :=
  P_T_cinv hPF hK μ

/-- **`QG̃ = 0`** on the compressed functions. -/
theorem Q_Gtop (hPF : ∀ y, PF (PF y) = PF y) (hK : IsUnit (ckern PF (Q ∘ₗ G ∘ₗ Qs))) (x : V) :
    PF (Q (Gtop PF G Q Qs x)) = 0 := by
  have h := P_T_cinv hPF hK (Q (G x))
  change PF (Q (G x - Hop PF G Q Qs (Q (G x)))) = 0
  rw [map_sub, map_sub]
  change PF (Q (G x)) - PF ((Q ∘ₗ G ∘ₗ Qs) (cinv PF (Q ∘ₗ G ∘ₗ Qs) (Q (G x)))) = 0
  rw [h, sub_self]

/-- **`G̃Q^* = 0`** on the compressed functions. -/
theorem Gtop_Qs (hPF : ∀ y, PF (PF y) = PF y) (hK : IsUnit (ckern PF (Q ∘ₗ G ∘ₗ Qs))) (μ : W) :
    Gtop PF G Q Qs (Qs (PF μ)) = 0 := by
  have h := cinv_T_P hPF hK μ
  change G (Qs (PF μ)) - G (Qs (cinv PF (Q ∘ₗ G ∘ₗ Qs) ((Q ∘ₗ G ∘ₗ Qs) (PF μ)))) = 0
  rw [h, sub_self]

end CompressedInverse
end CoreLean

end
