/-
`prop:sf-scalar` of BALABAN_CORE.tex (`4252790331fd`), the operator: in the model `Blocks.DomSeq` (`a₀ = 1`),
`Δ'_𝖺(𝐔) = D^*_𝐔D_𝐔 + Q'^*𝖺Q'` with the constraint operator of `eq:constraint-operator`,
`(Q'^*𝖺Q'f)(x) = 𝖺_ja_j⁻²Ad_{W(y, x)}⁻¹(Q'_jf)(y)` for `x ∈ Δ(y)`, `j = j(y)`.

* `Ncon`: the constraint operator; `P0_Ncon`: `⟨Q'^*𝖺Q'f, g⟩ = Σ_{y ∈ 𝐁}𝖺_ja_j²tr((Q'f)(y)(Q'g)(y))` (`eq:constraint-forms`,
  the transposes of the averages through `tr((Ad_W X)Y) = tr(X Ad_{W⁻¹}Y)`).
* `DeltaS_eq`: `Δ'_𝖺(𝐔)f = D^*_𝐔D_𝐔f + Q'^*𝖺Q'f`, by the nondegeneracy of the pairing.
* `eqn_Gp'`: at the sites of `Ω_D`, `u = G'h` satisfies `Δ_𝐔u = h - Q'^*𝖺Q'u`.
-/
import CoreLean.SmallFieldOperator

open Finset Matrix
open scoped Matrix.Norms.L2Operator
open LinearMap (BilinForm)

noncomputable section

namespace CoreLean
namespace SmallFieldDecay

open Blocks SmallFieldBlocks DiscretePoincare SmallFieldCoercivity SequenceOperators ConcretePairing
  CompressedInverse PairConcrete

variable {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "GLN" => (Matrix (Fin N) (Fin N) ℂ)ˣ

variable {n : ℕ} [NeZero n] (S : DomSeq n)

/-- **The constraint operator** `(Q'^*𝖺Q'f)(x) = 𝖺_ja_j⁻²Ad_{W(y, x)}⁻¹(Q'_jf)(y)`, `y = y(x)`, `j = j(x)`. -/
def Ncon (W : Site n → Site n → GLN) (f : Site n → Mat) : Site n → Mat := fun x =>
  ((aseq 1 S.L (S.sc x) * ((S.L : ℝ) ^ (2 * S.sc x))⁻¹ : ℝ) : ℂ) • Ad (W (bc S x) x)⁻¹ (avgW S W (bc S x) f)

/-- The average as a sum over the block: `(Q'_jf)(y) = a_j⁻⁴Σ_{x ∈ Δ(y)}Ad_{W(y, x)}f(x)`. -/
lemma avgW_blk (W : Site n → Site n → GLN) {y : Site n} (hy : y ∈ detB S) (f : Site n → Mat) :
    avgW S W y f = (((S.L : ℝ) ^ (4 * S.sc y) : ℝ) : ℂ)⁻¹ • ∑ x ∈ Blk S (S.sc y) y, Ad (W y x) (f x) := by
  obtain ⟨x0, -, rfl⟩ := mem_image.1 hy
  have hlat := inLat_bc (S := S) x0
  rw [avgW, ← sum_Blk (S := S) _ (S.sc_le _) hlat (fun x => Ad (W (bc S x0) x) (f x)), card_box]
  congr 2
  push_cast; rw [← pow_mul, mul_comm]

lemma sc_mem_blk {y x : Site n} (hy : y ∈ detB S) (hx : x ∈ Blk S (S.sc y) y) : S.sc x = S.sc y ∧ bc S x = y := by
  obtain ⟨x0, -, rfl⟩ := mem_image.1 hy
  have hcen : cen S.L (S.sc (bc S x0)) x = bc S x0 := (mem_filter.1 hx).2
  have h := (fiber_eq S x0 x).2 hcen
  exact ⟨by rw [← sc_bc S x, h], h⟩

/-- **`⟨Q'^*𝖺Q'f, g⟩` is the constraint form.** -/
theorem P0_Ncon (W : Site n → Site n → GLN) (f g : Site n → Mat) :
    P0 (Ncon S W f) g = wpair (cw S) (avgL S W f) (avgL S W g) := by
  have hL : (0 : ℝ) < S.L := by exact_mod_cast (show 0 < S.L by have := S.three_le_L; omega)
  simp only [P0, pairForm0, wpair_apply, a1, Complex.ofReal_one, one_pow, one_mul, Ncon]
  rw [sum_blocks S]
  rw [← Finset.sum_coe_sort (detB S)]
  refine sum_congr rfl fun y _ => ?_
  have hy := y.2
  -- the terms of the block of `y`
  have hterm : ∀ x ∈ Blk S (S.sc y.1) y.1,
      ntr (((aseq 1 S.L (S.sc x) * ((S.L : ℝ) ^ (2 * S.sc x))⁻¹ : ℝ) : ℂ) •
        Ad (W (bc S x) x)⁻¹ (avgW S W (bc S x) f) * g x) =
      ((aseq 1 S.L (S.sc y.1) * ((S.L : ℝ) ^ (2 * S.sc y.1))⁻¹ : ℝ) : ℂ) *
        ntr (avgW S W y.1 f * Ad (W y.1 x) (g x)) := by
    intro x hx
    obtain ⟨hsc, hbc⟩ := sc_mem_blk S hy hx
    rw [hsc, hbc, smul_mul_assoc, ntr_smul, ntr_Ad_mul, inv_inv]
  rw [sum_congr rfl hterm, ← mul_sum, ← ntr_sum, ← Finset.mul_sum]
  simp only [avgL, LinearMap.coe_mk, AddHom.coe_mk, cw]
  rw [avgW_blk S W hy g, mul_smul_comm, ntr_smul, ← mul_assoc]
  congr 1
  have h4 : ((S.L : ℂ) ^ (4 * S.sc y.1)) = ((S.L : ℂ) ^ (2 * S.sc y.1)) ^ 2 := by rw [← pow_mul]; ring_nf
  have hp : ((S.L : ℂ) ^ (2 * S.sc y.1)) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hL.ne')
  push_cast
  rw [h4]
  field_simp

/-- **`Δ'_𝖺(𝐔) = D^*_𝐔D_𝐔 + Q'^*𝖺Q'`.** -/
theorem DeltaS_eq (U : Config N n) (W : Site n → Site n → GLN) (f : Site n → Mat) :
    DeltaS S U W f = Ds1L a1 U (D0L a1 U f) + Ncon S W f := by
  have key : ∀ g, P0 (DeltaS S U W f - (Ds1L a1 U (D0L a1 U f) + Ncon S W f)) g = 0 := by
    intro g
    have h1 : P0 (DeltaS S U W f) g = PhiB S U W f g := by rw [DeltaS_spec, PhiB_apply]
    have h2 : P0 (Ds1L a1 U (D0L a1 U f)) g = pairForm1 a1 (D0L a1 U f) (D0L a1 U g) := by
      rw [show P0 (Ds1L a1 U (D0L a1 U f)) g = P0 g (Ds1L a1 U (D0L a1 U f)) from wpair_symm _ _ _,
        ← D0L_transpose, pairForm1_symm]
    rw [map_sub, map_add, LinearMap.sub_apply, LinearMap.add_apply, h1, h2, P0_Ncon]
    simp only [PhiB, LinearMap.add_apply, LinearMap.compl₁₂_apply]
    ring
  have := (P0_nondeg (N := N) (n := n)).1 _ key
  exact sub_eq_zero.1 this

/-- **The equation of `G'`** at the sites of `Ω_D`: `Δ_𝐔u = h - Q'^*𝖺Q'u` for `u = G'h`. -/
theorem eqn_Gp' (U : Config N n) (W : Site n → Site n → GLN) (ΩD : Set (Site n))
    (hK : IsUnit (ckern (piD ΩD) (DeltaS S U W))) (h : Site n → Mat) {x : Site n} (hx : x ∈ ΩD) :
    Lap 1 U (Gp' S U W ΩD h) x = h x - Ncon S W (Gp' S U W ΩD h) x := by
  have hP := piD_idem (N := N) ΩD
  have h1 := congrFun (P_T_cinv hP hK h) x
  rw [piD_apply, piD_apply, if_pos hx, if_pos hx] at h1
  rw [← Gp', DeltaS_eq] at h1
  rw [← h1]
  simp only [Pi.add_apply, add_sub_cancel_right, Lap_eq, a1, Complex.ofReal_one, LinearMap.comp_apply]

end SmallFieldDecay
end CoreLean

end
