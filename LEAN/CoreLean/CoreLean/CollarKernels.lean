/-
`lem:collar-kernels`(i) of BALABAN_CORE.tex (`a021c13be348`), the identity `eq:response-identity` in abstract form.
With `H₁ = G₁Q^*(QG₁Q^*)⁻¹`, `𝓡 = H₁Q` (`eq:response-operator`) and `𝒞 = G₁ - H₁QG₁` (the propagator of the constrained
fluctuation, `def:fluctuation-propagator`):

* `𝒞Q^* = 0` (`C_Qs`) and `𝒞G₁⁻¹ = I - 𝓡` (`C_Ginv`);
* if `G₁⁻¹ = P + Q^*𝖺Q` (here `P = D^*D + Δ'(W) + DRD^* - Δ'_π - Δ^{(2)}_π`, `lem:hessian`(ii)), the term with `Q^*` is
  annihilated by `𝒞`, and `𝓡f = f - 𝒞Pf` (`response_identity`), which is `eq:response-identity`.
-/
import Mathlib

noncomputable section

namespace CoreLean
namespace CollarKernels

variable {E F : Type*} [AddCommGroup E] [AddCommGroup F]

variable (G Ginv P : E →+ E) (Q : E →+ F) (Qs : F →+ E) (Minv a : F →+ F)

/-- `H₁ = G₁Q^*(QG₁Q^*)⁻¹`. -/
def H1 (y : F) : E := G (Qs (Minv y))

/-- `𝒞 = G₁ - H₁QG₁`. -/
def Cop (f : E) : E := G f - H1 G Qs Minv (Q (G f))

/-- `𝒞Q^* = 0`. -/
theorem C_Qs (hM : ∀ y, Minv (Q (G (Qs y))) = y) (y : F) : Cop G Q Qs Minv (Qs y) = 0 := by
  simp only [Cop, H1, hM, sub_self]

/-- `𝒞G₁⁻¹ = I - 𝓡`. -/
theorem C_Ginv (hG : ∀ f, G (Ginv f) = f) (f : E) :
    Cop G Q Qs Minv (Ginv f) = f - H1 G Qs Minv (Q f) := by
  simp only [Cop, hG]

/-- **`eq:response-identity`**: `𝓡f = f - 𝒞Pf` when `G₁⁻¹ = P + Q^*𝖺Q`. -/
theorem response_identity (hG : ∀ f, G (Ginv f) = f) (hM : ∀ y, Minv (Q (G (Qs y))) = y)
    (hdec : ∀ f, Ginv f = P f + Qs (a (Q f))) (f : E) :
    H1 G Qs Minv (Q f) = f - Cop G Q Qs Minv (P f) := by
  have h1 := C_Ginv G Ginv Q Qs Minv hG f
  have hlin : Cop G Q Qs Minv (Ginv f) = Cop G Q Qs Minv (P f) + Cop G Q Qs Minv (Qs (a (Q f))) := by
    rw [hdec]; simp only [Cop, H1, map_add]; abel
  rw [hlin, C_Qs G Q Qs Minv hM, add_zero] at h1
  rw [h1]; abel

/-- `RG'Q'^* = 0` for `R = I - G'Q'^*(Q'G'^2Q'^*)⁻¹Q'G'` (the statement of (i) on `R` for the `0`-forms `Q'^*ν`). -/
theorem R_GQs {V W : Type*} [AddCommGroup V] [AddCommGroup W] (G' : V →+ V) (Q' : V →+ W) (Q's : W →+ V)
    (M' : W →+ W) (hM : ∀ y, M' (Q' (G' (G' (Q's y)))) = y) (y : W) :
    G' (Q's y) - G' (Q's (M' (Q' (G' (G' (Q's y)))))) = 0 := by
  rw [hM, sub_self]

end CollarKernels
end CoreLean

end
