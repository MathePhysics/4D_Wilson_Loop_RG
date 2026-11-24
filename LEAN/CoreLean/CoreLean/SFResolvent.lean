/-
`prop:sf-block` of BALABAN_CORE.tex (`d4ef86a9a5fd`): the comparison of `G'` at the complex field with `G'` at the
trivial configuration through the resolvent identity (used here in place of the holomorphy in the field and the lemma
of Schwarz of the core's proof), on the fine lattice (`a₀ = 1`).

* `cinv_sub`: `G_a - G_b = G_a(T_b - T_a)G_b` for compressed inverses.
* `lap_diff`: the covariant Laplacian minus the Laplacian in divergence form,
  `(Δ_𝐔 - Δ)f = -D^*_𝐔g + r`, `g_μ(z) = (1 - Ad_{𝐔(z, z + e_μ)})f(z + e_μ)`,
  `r(x) = Σ_μAd_{𝐔(x - e_μ, x)}⁻¹(1 - Ad_{𝐔(x - e_μ, x)})(f(x) - f(x - e_μ))` (cf. `eq:sf-laplacian`).
* `gdiv_bound`, `rdiv_bound`: `|g_μ(z)| ≤ 6‖X_μ(z)‖|f(z + e_μ)|`, `|r(x)| ≤ Σ_μ12‖X_μ(x - e_μ)‖|f(x) - f(x - e_μ)|`.
-/
import CoreLean.SFBlockForm

open Finset Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace CoreLean
namespace SFBounds

open Lattices SeqDom Blocks SmallFieldBlocks SFBox SFBox.SeqDomBox SmallFieldDecay SmallFieldCoercivity
  SequenceOperators CompressedInverse

/-- **The resolvent identity for compressed inverses.** -/
lemma cinv_sub {V : Type*} [AddCommGroup V] [Module ℂ V] {P Ta Tb : Module.End ℂ V}
    (hP : ∀ x, P (P x) = P x) (ha : IsUnit (ckern P Ta)) (hb : IsUnit (ckern P Tb)) (x : V) :
    cinv P Ta x - cinv P Tb x = cinv P Ta ((Tb - Ta) (cinv P Tb x)) := by
  rw [LinearMap.sub_apply, map_sub]
  have h1 : cinv P Ta (Ta (cinv P Tb x)) = cinv P Tb x := by
    conv_lhs => rw [← P_cinv hP (T := Tb) x]
    rw [cinv_T_P hP ha, P_cinv hP]
  have h2 : cinv P Ta (Tb (cinv P Tb x)) = cinv P Ta x := by
    rw [← cinv_P hP (T := Ta), P_T_cinv hP hb, cinv_P hP]
  rw [h1, h2]

variable (S : SeqDom) {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "GLN" => (Matrix (Fin N) (Fin N) ℂ)ˣ
local notation "NF" => SequenceAverages.N0 S

/-- The `1`-form `g_μ(z) = (1 - Ad_{𝐔(z, z + e_μ)})f(z + e_μ)`. -/
def gdiv (U : Config N NF) (f : Site NF → Mat) : Fin 4 → Site NF → Mat :=
  fun μ z => f (z + unit _ μ) - Ad (U μ z) (f (z + unit _ μ))

/-- The remainder `r(x) = Σ_μAd_{U_μ(x - e_μ)}⁻¹(1 - Ad_{U_μ(x - e_μ)})(f(x) - f(x - e_μ))`. -/
def rdiv (U : Config N NF) (f : Site NF → Mat) : Site NF → Mat := fun x =>
  ∑ μ, Ad (U μ (x - unit _ μ))⁻¹ ((f x - f (x - unit _ μ)) - Ad (U μ (x - unit _ μ)) (f x - f (x - unit _ μ)))

/-- **`(Δ_𝐔 - Δ)f = -D^*_𝐔g + r`.** -/
theorem lap_diff (X : Fin 4 → Site NF → Mat) (f : Site NF → Mat) (x : Site NF) :
    Lap 1 (cfgX X) f x - Lap 1 (cfgX (X0 S)) f x =
      -Ds1 1 (cfgX X) (gdiv S (cfgX X) f) x + rdiv S (cfgX X) f x := by
  rw [lap_triv, show Lap 1 (cfgX X) f x = ∑ μ, Dbw 1 (cfgX X) μ (Dfw 1 (cfgX X) μ f) x from rfl,
    show Ds1 1 (cfgX X) (gdiv S (cfgX X) f) x = ∑ μ, Dbw 1 (cfgX X) μ (gdiv S (cfgX X) f μ) x from rfl, rdiv,
    sub_neg_eq_add, ← sum_neg_distrib, ← sum_add_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun μ _ => ?_
  have hv : (cfgX X).val ⟨x, μ, false⟩ = (cfgX X μ (x - unit _ μ))⁻¹ := rfl
  simp only [Dbw, Dfw, gdiv, hv, inv_one, one_smul, sub_add_cancel, Ad_sub, Ad_inv_Ad]
  abel

lemma Ad_expU_inv (X : Mat) (Z : Mat) : Ad (expU (Complex.I • X))⁻¹ Z = Ad (expU (Complex.I • (-X))) Z := by
  rw [expU_inv, smul_neg]

/-- **`|g_μ(z)| ≤ 6‖X_μ(z)‖|f(z + e_μ)|`** for `‖X‖ ≤ 1/32`. -/
lemma gdiv_bound {X : Fin 4 → Site NF → Mat} (f : Site NF → Mat) (μ : Fin 4) (z : Site NF)
    (hX : ‖X μ z‖ ≤ 1 / 32) : hs (gdiv S (cfgX X) f μ z) ≤ 6 * ‖X μ z‖ * hs (f (z + unit _ μ)) := by
  simp only [gdiv]
  rw [← SupportCont.hs_neg, neg_sub]
  exact hs_Ad_exp_sub_le hX _

/-- `|Ad_{e^{iX}}⁻¹Z| ≤ 2|Z|` for `‖X‖ ≤ 1/32`. -/
lemma hs_Ad_inv_le {X : Mat} (hX : ‖X‖ ≤ 1 / 32) (Z : Mat) : hs (Ad (expU (Complex.I • X))⁻¹ Z) ≤ 2 * hs Z := by
  rw [Ad_expU_inv]
  have hX' : ‖-X‖ ≤ 1 / 32 := by rwa [norm_neg]
  have h := hs_Ad_exp_sub_le hX' Z
  have h2 := hs_add_le (Ad (expU (Complex.I • -X)) Z - Z) Z
  rw [sub_add_cancel] at h2
  have hZ := hs_nonneg Z
  rw [norm_neg] at h
  nlinarith [norm_nonneg X]

/-- **`|r(x)| ≤ Σ_μ12‖X_μ(x - e_μ)‖|f(x) - f(x - e_μ)|`** for `‖X‖ ≤ 1/32`. -/
lemma rdiv_bound {X : Fin 4 → Site NF → Mat} (f : Site NF → Mat) (x : Site NF)
    (hX : ∀ μ, ‖X μ (x - unit _ μ)‖ ≤ 1 / 32) :
    hs (rdiv S (cfgX X) f x) ≤ ∑ μ, 12 * ‖X μ (x - unit _ μ)‖ * hs (f x - f (x - unit _ μ)) := by
  simp only [rdiv]
  refine (RegularAverages.hs_sum_le _ _).trans (sum_le_sum fun μ _ => ?_)
  have h1 := hs_Ad_inv_le (hX μ) ((f x - f (x - unit _ μ)) - Ad (cfgX X μ (x - unit _ μ)) (f x - f (x - unit _ μ)))
  have h2 : hs ((f x - f (x - unit _ μ)) - Ad (cfgX X μ (x - unit _ μ)) (f x - f (x - unit _ μ))) ≤
      6 * ‖X μ (x - unit _ μ)‖ * hs (f x - f (x - unit _ μ)) := by
    rw [← SupportCont.hs_neg, neg_sub]; exact hs_Ad_exp_sub_le (hX μ) _
  simp only [cfgX] at h1 h2 ⊢
  linarith

end SFBounds
end CoreLean

end
