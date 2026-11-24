/-
The blocks of a sequence of domains on the fine lattice (BALABAN_CORE.tex `542c68192a44`, `def:sequence`,
`eq:block`, `lem:block-partition`), in the model `Blocks.DomSeq` (fine lattice `(ℤ/n)⁴`, `η = 1`, `a_j = Lʲ`), in the
form in which `sec:small-field-operators` uses them.

* `bc S x = cen_{j(x)}(x)`: the point of `𝐁` whose block `Δ(y)` contains `x`; `detB S`: the determining set `𝐁` as
  the image of `bc`.
* `Blk j y`: the block `{x | cen_j(x) = y}`; `fiber_eq`: the fibre of `bc` over `y ∈ 𝐁` is the block of `y` of the
  scale `j(y)`, so that the blocks `Δ(y)`, `y ∈ 𝐁`, partition the fine lattice (`sum_blocks`).
* `phi y`, `psi y`: the offsets `o ∈ {0, …, Lʲ - 1}⁴` of the sites `y + o - h_j` of the block, a bijection
  (`sum_Blk`), which maps the bonds of the box to bonds of the block (`phi_update`).
-/
import CoreLean.BlockPartition
import CoreLean.DiscretePoincare
import CoreLean.Lattice

open Finset
open scoped Classical

noncomputable section

namespace CoreLean
namespace SmallFieldBlocks

open Blocks

variable {n : ℕ} [NeZero n] (S : DomSeq n)

/-- The point of `𝐁` whose block contains `x`. -/
def bc (x : Site n) : Site n := cen S.L (S.sc x) x

/-- The determining set `𝐁`. -/
def detB : Finset (Site n) := univ.image (bc S)

/-- The block `{x | cen_j(x) = y}`. -/
def Blk (j : ℕ) (y : Site n) : Finset (Site n) := univ.filter fun x => cen S.L j x = y

lemma sc_bc (x : Site n) : S.sc (bc S x) = S.sc x := S.sc_cen x

/-- **The fibre of `bc` over `y = bc x` is the block of `y` of the scale `j(y)`.** -/
lemma fiber_eq (x x' : Site n) : bc S x' = bc S x ↔ cen S.L (S.sc (bc S x)) x' = bc S x := by
  constructor
  · intro h
    have hs : S.sc x' = S.sc (bc S x) := by rw [← sc_bc S x', h]
    rw [← hs]; exact h
  · intro h
    set y := bc S x
    set j := S.sc y
    have hjk : j ≤ S.k := S.sc_le y
    have hin : x' ∈ S.Ω j := (S.cells j hjk x').mpr (by rw [h]; exact S.mem_sc y)
    have hout : x' ∉ S.Ω (j + 1) := by
      intro hx
      by_cases hk : j + 1 ≤ S.k
      · have := (S.cells_succ hk x').mp hx
        rw [h] at this
        exact S.not_mem_sc_succ y this
      · rw [S.Ω_empty (by omega)] at hx; exact absurd hx (Set.notMem_empty _)
    have hsc : S.sc x' = j := by
      have h1 := (S.mem_iff x' j).mp hin
      have h2 : ¬ j + 1 ≤ S.sc x' := fun hh => hout ((S.mem_iff x' _).mpr hh)
      omega
    show cen S.L (S.sc x') x' = y
    rw [hsc]; exact h

/-- **The blocks partition the fine lattice**: `Σ_x G(x) = Σ_{y ∈ 𝐁} Σ_{x ∈ Δ(y)} G(x)`. -/
lemma sum_blocks {M : Type*} [AddCommMonoid M] (G : Site n → M) :
    ∑ x, G x = ∑ y ∈ detB S, ∑ x ∈ Blk S (S.sc y) y, G x := by
  rw [← Finset.sum_fiberwise_of_maps_to (s := univ) (t := detB S) (g := bc S)
    (fun x _ => mem_image_of_mem _ (mem_univ x))]
  refine sum_congr rfl fun y hy => ?_
  obtain ⟨x, -, rfl⟩ := mem_image.1 hy
  congr 1
  ext x'
  simp only [mem_filter, mem_univ, true_and, Blk]
  exact fiber_eq S x x'

/-! ### The offsets of a block -/

/-- The site `y + o - h_j` of the offset `o`. -/
def phi (j : ℕ) (y : Site n) (o : Fin 4 → ℕ) : Site n :=
  fun ν => y ν + (((o ν : ℤ) - half S.L j : ℤ) : ZMod n)

/-- The offset `x - y + h_j` of a site of the block. -/
def psi (j : ℕ) (y : Site n) (x : Site n) : Fin 4 → ℕ :=
  fun ν => ((x ν - y ν).valMinAbs + half S.L j).toNat

variable {S}

lemma phi_update (j : ℕ) (y : Site n) (o : Fin 4 → ℕ) (μ : Fin 4) :
    phi S j y (Function.update o μ (o μ + 1)) = phi S j y o + unit n μ := by
  funext ν
  simp only [phi, Pi.add_apply, unit]
  by_cases h : ν = μ
  · subst h
    simp only [Function.update_self, Pi.single_eq_same]
    push_cast; ring
  · simp only [Function.update_of_ne h, Pi.single_eq_of_ne h, add_zero]

lemma half_le (j : ℕ) {hj : j ≤ S.k} : 2 * half S.L j + 1 ≤ n := by
  have h1 := two_half_add_one S.L_odd j
  have h2 := S.three_mul_le_N hj
  omega

/-- The offsets of the box give the sites of the block. -/
lemma phi_mem (j : ℕ) (hj : j ≤ S.k) {y : Site n} (hy : InLat S.L j y) {o : Fin 4 → ℕ}
    (ho : o ∈ DiscretePoincare.box 4 (S.L ^ j)) : phi S j y o ∈ Blk S j y := by
  have h1 := two_half_add_one S.L_odd j
  simp only [DiscretePoincare.box, Fintype.mem_piFinset, mem_range] at ho
  simp only [Blk, mem_filter, mem_univ, true_and]
  funext ν
  symm
  refine eq_cen1 S.L_odd (S.dvd_N hj) (hy ν) ?_
  simp only [phi, add_sub_cancel_left]
  refine (cd_intCast_le _).trans ?_
  have := ho ν
  omega

lemma cd_le_of_mem {j : ℕ} {y x : Site n} (hx : x ∈ Blk S j y) (ν : Fin 4) : cd (x ν - y ν) ≤ half S.L j := by
  simp only [Blk, mem_filter, mem_univ, true_and] at hx
  have := cd_sub_cen1_le S.L_odd j (x ν)
  rw [← hx]; exact this

lemma psi_mem {j : ℕ} {y x : Site n} (hx : x ∈ Blk S j y) : psi S j y x ∈ DiscretePoincare.box 4 (S.L ^ j) := by
  have h1 := two_half_add_one S.L_odd j
  simp only [DiscretePoincare.box, Fintype.mem_piFinset, mem_range, psi]
  intro ν
  have hc := cd_le_of_mem hx ν
  unfold cd at hc
  omega

lemma phi_psi {j : ℕ} {y x : Site n} (hx : x ∈ Blk S j y) : phi S j y (psi S j y x) = x := by
  funext ν
  have hc := cd_le_of_mem hx ν
  unfold cd at hc
  simp only [phi, psi]
  have e : (((((x ν - y ν).valMinAbs + half S.L j).toNat : ℕ) : ℤ) - half S.L j) = (x ν - y ν).valMinAbs := by
    omega
  rw [e, ZMod.coe_valMinAbs]; ring

lemma psi_phi (j : ℕ) (hj : j ≤ S.k) (y : Site n) {o : Fin 4 → ℕ}
    (ho : o ∈ DiscretePoincare.box 4 (S.L ^ j)) : psi S j y (phi S j y o) = o := by
  have h1 := two_half_add_one S.L_odd j
  have h2 := half_le (S := S) j (hj := hj)
  simp only [DiscretePoincare.box, Fintype.mem_piFinset, mem_range] at ho
  funext ν
  simp only [psi, phi, add_sub_cancel_left]
  have hv := ho ν
  rw [valMinAbs_intCast (by omega) (by omega)]
  omega

/-- **The sum over a block through its offsets.** -/
lemma sum_Blk {M : Type*} [AddCommMonoid M] (j : ℕ) (hj : j ≤ S.k) {y : Site n} (hy : InLat S.L j y)
    (F : Site n → M) : ∑ x ∈ Blk S j y, F x = ∑ o ∈ DiscretePoincare.box 4 (S.L ^ j), F (phi S j y o) := by
  refine Finset.sum_nbij' (psi S j y) (phi S j y) (fun x hx => psi_mem hx) (fun o ho => phi_mem j hj hy ho)
    (fun x hx => phi_psi hx) (fun o ho => psi_phi j hj y ho) (fun x hx => ?_)
  rw [phi_psi hx]

/-- The points of `𝐁` are points of `T^{(j(y))}`. -/
lemma inLat_bc (x : Site n) : InLat S.L (S.sc (bc S x)) (bc S x) := by
  rw [sc_bc]
  intro ν
  exact cen1_isMul _ _

end SmallFieldBlocks
end CoreLean

end
