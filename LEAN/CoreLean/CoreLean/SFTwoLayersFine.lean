/-
`lem:sf-two-layers` of BALABAN_CORE.tex (`c1d6d533fce5`) on the fine lattice (`a₀ = 1`) at the trivial configuration,
with the torus as the Dirichlet domain: the transport of `CoarseTwoLayers.coarse_two_layers` from the coarse torus
`T = (ℤ/LMℤ)⁴` to the points of `T^{(j)}` on the fine lattice.

* `Mj`, `nLM`: `M = 2L^{m_𝕋+k-j-1}`, `L^j·LM = N₀`.
* `fineOf`: the point `L^jz` of `T^{(j)}`; `fineOf_intCast`, `fineOf_add`: its arithmetic.
* `c0h`, `Yc`, `cen_fineOf_pt`: the blocks of `T^{(j+1)}` (`pt c0h w o`, `o ∈ [0, L)⁴`) have the centres `Yc w`.
* `sum_coarse`: the fine lattice is the union of the blocks `B^j(fineOf z)`.
-/
import CoreLean.CoarseTwoLayers
import CoreLean.SFTwoLayersGauge

open Finset Matrix

noncomputable section

namespace CoreLean
namespace SFBounds

open Lattices SeqDom Blocks SmallFieldBlocks SFLocal SmallFieldDecay SmallFieldCoercivity
  SequenceOperators CompressedInverse ConcretePairing SFBox SFBox.SeqDomBox

variable (S : SeqDom) {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "NF" => SequenceAverages.N0 S
set_option quotPrecheck false in
local notation "jj" => (S.toDomSeq).sc

/-- `M = 2L^{m_𝕋+k-j-1}`, the side of `T^{(j+1)}` in the units `a_{j+1}`. -/
def Mj (j : ℕ) : ℕ := 2 * S.L ^ (S.mT + S.k - j - 1)

instance instNeZeroL : NeZero S.L := ⟨by have := S.Lpos; omega⟩

instance instNeZeroMj (j : ℕ) : NeZero (Mj S j) := ⟨by unfold Mj; have := S.Lpos; positivity⟩

lemma nLM {j : ℕ} (hj : j + 1 ≤ S.k) : S.L ^ j * (S.L * Mj S j) = NF := by
  rw [SequenceAverages.N0_eq, Mj]
  obtain ⟨a, ha⟩ : ∃ a, S.mT + S.k = j + 1 + a := ⟨S.mT + S.k - j - 1, by omega⟩
  rw [show S.mT + S.k - j - 1 = a by omega, ha, pow_add, pow_succ]; ring

lemma Kj_eq {j : ℕ} (hj : j + 1 ≤ S.k) : Kj S j = S.L * Mj S j := by
  rw [Kj, Mj]
  obtain ⟨a, ha⟩ : ∃ a, S.mT + S.k - j = a + 1 := ⟨S.mT + S.k - j - 1, by omega⟩
  rw [show S.mT + S.k - j - 1 = a by omega, ha, pow_succ]; ring

/-- The point `L^jz` of `T^{(j)}` on the fine lattice. -/
def fineOf (j : ℕ) (z : Coarse.T S.L (Mj S j)) : Site NF := fun ν => ((S.L ^ j * (z ν).val : ℕ) : ZMod NF)

lemma fineOf_intCast {j : ℕ} (hj : j + 1 ≤ S.k) (t : ℤ) :
    ((S.L ^ j * ((t : ZMod (S.L * Mj S j))).val : ℕ) : ZMod NF) = ((((S.L ^ j : ℕ) : ℤ) * t : ℤ) : ZMod NF) := by
  have h := ZMod.val_intCast (n := S.L * Mj S j) t
  rw [show ((S.L ^ j * ((t : ZMod (S.L * Mj S j))).val : ℕ) : ZMod NF) =
    ((((S.L ^ j * ((t : ZMod (S.L * Mj S j))).val : ℕ) : ℤ)) : ZMod NF) by simp]
  rw [ZMod.intCast_eq_intCast_iff, Int.modEq_iff_dvd]
  push_cast
  rw [h, ← nLM S hj]
  push_cast
  exact ⟨t / ((S.L : ℤ) * (Mj S j : ℤ)), by rw [Int.emod_def]; ring⟩

lemma fineOf_add_single {j : ℕ} (hj : j + 1 ≤ S.k) (z : Coarse.T S.L (Mj S j)) (μ : Fin 4) (t : ℕ) :
    fineOf S j (z + Pi.single μ (t : ZMod (S.L * Mj S j))) =
      fineOf S j z + ((S.L ^ j * t : ℕ) : ZMod NF) • unit NF μ := by
  funext ν
  simp only [fineOf, Pi.add_apply, Pi.smul_apply, smul_eq_mul, unit]
  by_cases h : ν = μ
  · subst h
    simp only [Pi.single_eq_same, mul_one]
    have e : z ν + (t : ZMod (S.L * Mj S j)) = ((((z ν).val + t : ℕ) : ℤ) : ZMod (S.L * Mj S j)) := by
      push_cast; rw [ZMod.natCast_zmod_val]
    rw [e, fineOf_intCast S hj]
    push_cast; ring
  · simp only [Pi.single_eq_of_ne h, add_zero, mul_zero]

/-- **`fineOf(z + e_μ) = fineOf z + a_je_μ`.** -/
lemma fineOf_add {j : ℕ} (hj : j + 1 ≤ S.k) (z : Coarse.T S.L (Mj S j)) (μ : Fin 4) :
    fineOf S j (z + Coarse.e μ) = ynext S j (fineOf S j z) μ := by
  have := fineOf_add_single S hj z μ 1
  simp only [Nat.cast_one, mul_one] at this
  exact this

lemma inLat_fineOf (j : ℕ) (z : Coarse.T S.L (Mj S j)) : InLat S.L j (fineOf S j z) := by
  intro ν
  exact ⟨(z ν).val, by simp [fineOf]⟩

lemma cen_fineOf {j : ℕ} (hj : j + 1 ≤ S.k) (z : Coarse.T S.L (Mj S j)) :
    cen S.L j (fineOf S j z) = fineOf S j z := by
  funext ν
  symm
  refine eq_cen1 S.L_odd (S.toDomSeq.dvd_N (show j ≤ S.k by omega)) (inLat_fineOf S j z ν) ?_
  simp [sub_self, cd_zero]

lemma fineOf_injective {j : ℕ} (hj : j + 1 ≤ S.k) : Function.Injective (fineOf S j) := by
  intro z z' h
  funext ν
  have h1 := congrFun h ν
  simp only [fineOf] at h1
  have hn : 0 < S.L ^ j := pow_pos S.Lpos _
  have hlt : ∀ a : ZMod (S.L * Mj S j), S.L ^ j * a.val < NF := fun a => by
    rw [← nLM S hj]; exact Nat.mul_lt_mul_of_pos_left a.val_lt hn
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (hlt _), Nat.mod_eq_of_lt (hlt _)] at h1
  exact ZMod.val_injective _ (Nat.eq_of_mul_eq_mul_left hn h1)

/-! ### The blocks of `T^{(j+1)}` -/

/-- The first corner `-h`, `h = (L - 1)/2`, of the block of `0`. -/
def c0h (j : ℕ) : Coarse.T S.L (Mj S j) := fun _ => -((half S.L 1 : ℕ) : ZMod (S.L * Mj S j))

/-- The centre `a_{j+1}w` of the block `w`. -/
def Yc (j : ℕ) (w : Coarse.W (Mj S j)) : Site NF := fun ν => ((S.L ^ j * (S.L * (w ν).val) : ℕ) : ZMod NF)

lemma half_succ' (j : ℕ) : half S.L (j + 1) = S.L ^ j * half S.L 1 + half S.L j := by
  have h1 := two_half_add_one S.L_odd (j + 1)
  have h2 := two_half_add_one S.L_odd 1
  have h3 := two_half_add_one S.L_odd j
  have key : 2 * half S.L (j + 1) + 1 = (2 * half S.L j + 1) * (2 * half S.L 1 + 1) := by
    rw [h1, h2, h3, pow_succ, pow_one]
  rw [← h3]
  generalize half S.L (j + 1) = c at key ⊢
  generalize half S.L j = a at key ⊢
  generalize half S.L 1 = b at key ⊢
  ring_nf at key ⊢
  linarith

lemma inLat_Yc (j : ℕ) (w : Coarse.W (Mj S j)) : InLat S.L (j + 1) (Yc S j w) := by
  intro ν
  exact ⟨(w ν).val, by simp [Yc, pow_succ]; ring⟩

lemma fineOf_pt {j : ℕ} (hj : j + 1 ≤ S.k) (w : Coarse.W (Mj S j)) (o : Fin 4 → ℕ) (ν : Fin 4) :
    fineOf S j (Coarse.pt (c0h S j) w o) ν =
      ((((S.L ^ j : ℕ) : ℤ) * ((S.L * (w ν).val : ℕ) + (o ν : ℤ) - (half S.L 1 : ℕ)) : ℤ) : ZMod NF) := by
  have e : Coarse.pt (c0h S j) w o ν =
      ((((S.L * (w ν).val : ℕ) + (o ν : ℤ) - (half S.L 1 : ℕ)) : ℤ) : ZMod (S.L * Mj S j)) := by
    simp only [Coarse.pt, c0h]; push_cast; ring
  simp only [fineOf]
  rw [e, fineOf_intCast S hj]

/-- **The blocks of `T^{(j+1)}` have the centres `Yc w`**: `cen_{j+1}(fineOf(pt w o)) = Yc w` for `o ∈ [0, L)⁴`. -/
lemma cen_fineOf_pt {j : ℕ} (hj : j + 1 ≤ S.k) (w : Coarse.W (Mj S j)) {o : Fin 4 → ℕ}
    (ho : o ∈ Coarse.bx4 (L := S.L)) : cen S.L (j + 1) (fineOf S j (Coarse.pt (c0h S j) w o)) = Yc S j w := by
  rw [Coarse.mem_bx4] at ho
  funext ν
  symm
  refine eq_cen1 S.L_odd (S.toDomSeq.dvd_N hj) (inLat_Yc S j w ν) ?_
  have e : fineOf S j (Coarse.pt (c0h S j) w o) ν - Yc S j w ν =
      ((((S.L ^ j : ℕ) : ℤ) * ((o ν : ℤ) - (half S.L 1 : ℕ)) : ℤ) : ZMod NF) := by
    rw [fineOf_pt S hj]; simp only [Yc]; push_cast; ring
  rw [e]
  refine (cd_intCast_le _).trans ?_
  rw [Int.natAbs_mul, Int.natAbs_natCast, half_succ' S j]
  have h2 := two_half_add_one S.L_odd 1
  rw [pow_one] at h2
  have hv := ho ν
  have : ((o ν : ℤ) - (half S.L 1 : ℕ)).natAbs ≤ half S.L 1 := by omega
  calc S.L ^ j * ((o ν : ℤ) - (half S.L 1 : ℕ)).natAbs ≤ S.L ^ j * half S.L 1 := Nat.mul_le_mul_left _ this
    _ ≤ _ := Nat.le_add_right _ _

/-! ### The fine lattice as the union of the blocks of `T^{(j)}` -/

lemma sum_val_transport {β : Type*} [AddCommMonoid β] {K K' : ℕ} [NeZero K] [NeZero K'] (h : K = K')
    (H : (Fin 4 → ℕ) → β) :
    ∑ y : Fin 4 → ZMod K, H (fun ν => (y ν).val) = ∑ z : Fin 4 → ZMod K', H (fun ν => (z ν).val) := by
  subst h; rfl

/-- **The blocks `B^j(fineOf z)` partition the fine lattice.** -/
theorem sum_coarse {β : Type*} [AddCommMonoid β] {j : ℕ} (hj : j + 1 ≤ S.k) (f : Site NF → β) :
    ∑ x, f x = ∑ z : Coarse.T S.L (Mj S j), ∑ x ∈ Blk S.toDomSeq j (fineOf S j z), f x := by
  have hj0 : j ≤ S.k := by omega
  set S1 := oneLayer S j hj0
  have h1 := sum_blocks S1.toDomSeq f
  have hsc : ∀ x, (S1.toDomSeq).sc x = j := oneLayer_sc S hj0
  have h2 := sum_detB_tr (S := S1) hj0 hsc (fun y => ∑ x ∈ Blk S1.toDomSeq ((S1.toDomSeq).sc y) y, f x)
  refine (h1.trans h2).trans ?_
  simp only [hsc, tr_emb (S := S1) hj0]
  exact sum_val_transport (Kj_eq S hj) (fun v => ∑ x ∈ Blk S.toDomSeq j (fun ν => ((S.L ^ j * v ν : ℕ) : ZMod NF)), f x)

lemma card_box4 (n : ℕ) : (DiscretePoincare.box 4 n).card = n ^ 4 := by
  simp [DiscretePoincare.box, Fintype.card_piFinset]

/-- A constant summed over a block of `T^{(j)}`. -/
lemma sum_Blk_const {β : Type*} [AddCommMonoid β] {j : ℕ} (hj : j ≤ S.k) {y : Site NF} (hy : InLat S.L j y) (c : β) :
    ∑ _x ∈ Blk S.toDomSeq j y, c = (S.L ^ j) ^ 4 • c := by
  rw [sum_Blk (S := S.toDomSeq) j hj hy (fun _ => c), sum_const, card_box4]
  rfl

/-- The translate of a block by a point of `T^{(j)}`. -/
lemma sum_Blk_add {β : Type*} [AddCommMonoid β] {j : ℕ} (hj : j ≤ S.k) {y v : Site NF} (hy : InLat S.L j y)
    (hv : InLat S.L j v) (f : Site NF → β) :
    ∑ x ∈ Blk S.toDomSeq j (y + v), f x = ∑ x ∈ Blk S.toDomSeq j y, f (x + v) := by
  have hyv : InLat S.L j (y + v) := fun ν => by
    obtain ⟨r, hr⟩ := hy ν; obtain ⟨r', hr'⟩ := hv ν
    exact ⟨r + r', by simp only [Pi.add_apply, hr, hr']; push_cast; ring⟩
  rw [sum_Blk (S := S.toDomSeq) j hj hyv, sum_Blk (S := S.toDomSeq) j hj hy]
  refine sum_congr rfl fun o _ => ?_
  congr 1
  funext ν
  simp only [SmallFieldBlocks.phi, Pi.add_apply]; ring

lemma mem_Blk_add {j : ℕ} (hj : j ≤ S.k) {y v x : Site NF} (hy : InLat S.L j y) (hv : InLat S.L j v)
    (hx : x ∈ Blk S.toDomSeq j y) : x + v ∈ Blk S.toDomSeq j (y + v) := by
  have hyv : InLat S.L j (y + v) := fun ν => by
    obtain ⟨r, hr⟩ := hy ν; obtain ⟨r', hr'⟩ := hv ν
    exact ⟨r + r', by simp only [Pi.add_apply, hr, hr']; push_cast; ring⟩
  have e : x + v = SmallFieldBlocks.phi S.toDomSeq j (y + v) (SmallFieldBlocks.psi S.toDomSeq j y x) := by
    conv_lhs => rw [← SmallFieldBlocks.phi_psi hx]
    funext ν
    simp only [SmallFieldBlocks.phi, Pi.add_apply]; ring
  rw [e]
  exact SmallFieldBlocks.phi_mem j hj hyv (SmallFieldBlocks.psi_mem hx)

/-! ### The function `λ` of `ω` -/

lemma pt_dec' {L M : ℕ} [NeZero L] [NeZero M] (c0 : Coarse.T L M) (z : Coarse.T L M) :
    Coarse.pt c0 (Coarse.dec c0 z).1 (Coarse.dec c0 z).2 = z := by
  funext ν
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  simp only [Coarse.pt, Coarse.dec]
  have hlt : (z ν - c0 ν).val / L < M := Nat.div_lt_of_lt_mul (ZMod.val_lt _)
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt hlt, Nat.div_add_mod, ZMod.natCast_zmod_val]
  ring

lemma dec_mem' {L M : ℕ} [NeZero L] [NeZero M] (c0 : Coarse.T L M) (z : Coarse.T L M) :
    (Coarse.dec c0 z).2 ∈ Coarse.bx4 (L := L) := by
  rw [Coarse.mem_bx4]; intro ν
  exact Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne L))

/-- The point of the coarse torus of a point of `T^{(j)}`. -/
def fineInv (j : ℕ) (y : Site NF) : Coarse.T S.L (Mj S j) := fun ν => (((y ν).val / S.L ^ j : ℕ) : ZMod (S.L * Mj S j))

lemma fineInv_fineOf {j : ℕ} (hj : j + 1 ≤ S.k) (z : Coarse.T S.L (Mj S j)) : fineInv S j (fineOf S j z) = z := by
  funext ν
  have hn : 0 < S.L ^ j := pow_pos S.Lpos _
  have hlt : S.L ^ j * (z ν).val < NF := by rw [← nLM S hj]; exact Nat.mul_lt_mul_of_pos_left (z ν).val_lt hn
  simp only [fineInv, fineOf]
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt hlt, Nat.mul_div_cancel_left _ hn, ZMod.natCast_zmod_val]

lemma fineOf_fineInv {j : ℕ} (hj : j + 1 ≤ S.k) {y : Site NF} (hy : InLat S.L j y) : fineOf S j (fineInv S j y) = y := by
  funext ν
  have hn : 0 < S.L ^ j := pow_pos S.Lpos _
  have hd : S.L ^ j ∣ (y ν).val := dvd_val_of_isMul (S := S) (S.toDomSeq.dvd_N (show j ≤ S.k by omega)) (hy ν)
  have hlt : (y ν).val / S.L ^ j < S.L * Mj S j := by
    rw [Nat.div_lt_iff_lt_mul hn, mul_comm, nLM S hj]; exact ZMod.val_lt _
  simp only [fineOf, fineInv]
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt hlt, Nat.mul_div_cancel' hd, ZMod.natCast_zmod_val]

/-- `λ(x) = ω(z)` on the block `B^j(fineOf z)`. -/
def lamOf (j : ℕ) (ω : Coarse.T S.L (Mj S j) → Mat) : Site NF → Mat := fun x => ω (fineInv S j (cen S.L j x))

lemma lamOf_mem {j : ℕ} (hj : j + 1 ≤ S.k) (ω : Coarse.T S.L (Mj S j) → Mat) {z : Coarse.T S.L (Mj S j)} {x : Site NF}
    (hx : x ∈ Blk S.toDomSeq j (fineOf S j z)) : lamOf S j ω x = ω z := by
  simp only [Blk, mem_filter, mem_univ, true_and] at hx
  simp only [lamOf]
  rw [show cen S.L j x = fineOf S j z from hx, fineInv_fineOf S hj]

lemma inLat_unit (j : ℕ) (μ : Fin 4) : InLat S.L j (((S.L ^ j : ℕ) : ZMod NF) • unit NF μ) := by
  intro ν
  by_cases h : ν = μ
  · subst h; exact ⟨1, by simp [unit]⟩
  · exact ⟨0, by simp [unit, Pi.single_eq_of_ne h]⟩

/-- **`a_jQ_j∂λ = dω`** (the core's `a_jQ_j∂λ = dω`, Proposition `prop:relative-average-order`(v) at the trivial
configuration): `Q_j(∂λ)(fineOf z, μ) = L^{-j}(ω(z + e_μ) - ω(z))`. -/
lemma Qt_D0L {j : ℕ} (hj : j + 1 ≤ S.k) (ω : Coarse.T S.L (Mj S j) → Mat) (z : Coarse.T S.L (Mj S j)) (μ : Fin 4) :
    Qt S (D0L a1 (cfgX (X0 S)) (lamOf S j ω)) j (fineOf S j z) μ =
      ((S.L ^ j : ℕ) : ℂ)⁻¹ • (ω (z + Coarse.e μ) - ω z) := by
  have hj0 : j ≤ S.k := by omega
  unfold Qt
  simp only [D0L_triv]
  have htel : ∀ x ∈ Blk S.toDomSeq j (fineOf S j z), ∑ t ∈ range (S.L ^ j),
      (lamOf S j ω (x + ((t : ℕ) : ZMod NF) • unit NF μ + unit NF μ) - lamOf S j ω (x + ((t : ℕ) : ZMod NF) • unit NF μ)) =
      ω (z + Coarse.e μ) - ω z := by
    intro x hx
    have e1 : ∀ t : ℕ, x + ((t : ℕ) : ZMod NF) • unit NF μ + unit NF μ = x + ((t + 1 : ℕ) : ZMod NF) • unit NF μ := by
      intro t; push_cast; rw [add_smul, one_smul]; abel
    simp only [e1]
    rw [sum_range_sub (fun t => lamOf S j ω (x + ((t : ℕ) : ZMod NF) • unit NF μ))]
    simp only [Nat.cast_zero, zero_smul, add_zero]
    have hm : x + ((S.L ^ j : ℕ) : ZMod NF) • unit NF μ ∈ Blk S.toDomSeq j (fineOf S j (z + Coarse.e μ)) := by
      rw [fineOf_add S hj]
      exact mem_Blk_add S hj0 (inLat_fineOf S j z) (inLat_unit S j μ) hx
    rw [lamOf_mem S hj ω hm, lamOf_mem S hj ω hx]
  rw [sum_congr rfl htel, sum_Blk_const S hj0 (inLat_fineOf S j z), ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  congr 1
  have hn : ((S.L ^ j : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (pow_pos S.Lpos j).ne'
  push_cast
  field_simp

lemma Qt_sub (A A' : Fin 4 → Site NF → Mat) (j : ℕ) (y : Site NF) (μ : Fin 4) :
    Qt S (A - A') j y μ = Qt S A j y μ - Qt S A' j y μ := by
  simp only [Qt, Pi.sub_apply, sum_sub_distrib, smul_sub]

/-! ### `Q'λ = 0` -/

/-- The blocks of `Λ = Ω_{j+1}` on the coarse torus. -/
def Lam (j : ℕ) (w : Coarse.W (Mj S j)) : Prop := S.ef (Yc S j w) ∈ S.Ω (j + 1)

lemma lam_iff {j : ℕ} (hj : j + 1 ≤ S.k) (w : Coarse.W (Mj S j)) {o : Fin 4 → ℕ} (ho : o ∈ Coarse.bx4 (L := S.L)) :
    S.ef (fineOf S j (Coarse.pt (c0h S j) w o)) ∈ S.Ω (j + 1) ↔ Lam S j w := by
  have h : fineOf S j (Coarse.pt (c0h S j) w o) ∈ S.toDomSeq.Ω (j + 1) ↔
      cen S.L (j + 1) (fineOf S j (Coarse.pt (c0h S j) w o)) ∈ S.toDomSeq.Ω (j + 1) :=
    (S.toDomSeq).cells (j + 1) hj _
  rw [cen_fineOf_pt S hj w ho] at h
  exact h

open Classical in
/-- **`Q'λ = 0`** for `λ` of an `ω` which vanishes on the blocks outside `Λ` and has the sum zero over every block. -/
theorem avg_lamOf [NeZero N] {j : ℕ} (hj1 : j + 1 ≤ S.k) (hlow : ∀ i ≤ j, S.Ω i = Set.univ)
    (hhigh : ∀ i, j + 2 ≤ i → S.Ω i = ∅) (ω : Coarse.T S.L (Mj S j) → Mat)
    (h0 : ∀ w, ¬ Lam S j w → ∀ o ∈ Coarse.bx4 (L := S.L), ω (Coarse.pt (c0h S j) w o) = 0)
    (hs : ∀ w, ∑ o ∈ Coarse.bx4 (L := S.L), ω (Coarse.pt (c0h S j) w o) = 0) :
    ∀ y ∈ detB S.toDomSeq, avgW S.toDomSeq (W1 S) y (lamOf S j ω) = 0 := by
  have hj0 : j ≤ S.k := by omega
  have hsc : ∀ x, j ≤ jj x ∧ jj x ≤ j + 1 := fun x => by
    constructor
    · exact ((S.toDomSeq).mem_iff x j).1 (by rw [S.mem_toDomSeq_Ω, hlow j le_rfl]; trivial)
    · by_contra hc
      have := ((S.toDomSeq).mem_iff x (j + 2)).2 (by omega)
      rw [S.mem_toDomSeq_Ω, hhigh (j + 2) le_rfl] at this
      exact this
  intro y hy
  rw [avgW_triv_eq_zero_iff S S.toDomSeq hy]
  obtain ⟨x0, -, rfl⟩ := mem_image.1 hy
  rw [sc_bc]
  rcases (show jj x0 = j ∨ jj x0 = j + 1 by have := hsc x0; omega) with h1 | h1
  · -- the layer `j`: `ω = 0` on the block
    have hy' : bc S.toDomSeq x0 = cen S.L j x0 := by simp only [bc, h1]; rfl
    have hl : InLat S.L j (cen S.L j x0) := fun ν => cen1_isMul (L := S.L) j (x0 ν)
    set z := fineInv S j (cen S.L j x0)
    have hz : fineOf S j z = cen S.L j x0 := fineOf_fineInv S hj1 hl
    show ∑ x ∈ Blk S.toDomSeq (jj x0) (cen S.L (jj x0) x0), lamOf S j ω x = 0
    rw [h1, ← hz]
    rw [sum_congr rfl fun x hx => lamOf_mem S hj1 ω hx]
    have hω : ω z = 0 := by
      rw [← pt_dec' (c0h S j) z]
      refine h0 _ ?_ _ (dec_mem' (c0h S j) z)
      rw [← lam_iff S hj1 _ (dec_mem' (c0h S j) z), pt_dec' (c0h S j) z, hz]
      intro hin
      have hn := (S.toDomSeq).not_mem_sc_succ (bc S.toDomSeq x0)
      rw [sc_bc, h1, hy'] at hn
      exact hn (S.mem_toDomSeq_Ω.2 hin)
    simp [hω]
  · -- the layer `j + 1`: the sums of `ω` over the blocks vanish
    show ∑ x ∈ Blk S.toDomSeq (jj x0) (cen S.L (jj x0) x0), lamOf S j ω x = 0
    rw [h1]
    set Y := cen S.L (j + 1) x0
    have e1 : ∑ x ∈ Blk S.toDomSeq (j + 1) Y, lamOf S j ω x =
        ∑ x, if cen S.L (j + 1) x = Y then lamOf S j ω x else 0 := by
      rw [← sum_filter]; rfl
    rw [e1, sum_coarse S hj1]
    have e2 : ∀ z : Coarse.T S.L (Mj S j), ∑ x ∈ Blk S.toDomSeq j (fineOf S j z),
        (if cen S.L (j + 1) x = Y then lamOf S j ω x else 0) =
        if cen S.L (j + 1) (fineOf S j z) = Y then ((S.L ^ j) ^ 4) • ω z else 0 := by
      intro z
      have hc : ∀ x ∈ Blk S.toDomSeq j (fineOf S j z), cen S.L (j + 1) x = cen S.L (j + 1) (fineOf S j z) := by
        intro x hx
        simp only [Blk, mem_filter, mem_univ, true_and] at hx
        rw [← cen_nest S hj1 x, show cen S.L j x = fineOf S j z from hx]
      rw [sum_congr rfl fun x hx => by rw [hc x hx, lamOf_mem S hj1 ω hx]]
      split_ifs
      · exact sum_Blk_const S hj0 (inLat_fineOf S j z) _
      · exact sum_const_zero
    rw [sum_congr rfl fun z _ => e2 z, Coarse.sum_pt (c0h S j)]
    refine sum_eq_zero fun w _ => ?_
    have e3 : ∀ o ∈ Coarse.bx4 (L := S.L), (if cen S.L (j + 1) (fineOf S j (Coarse.pt (c0h S j) w o)) = Y then
        ((S.L ^ j) ^ 4) • ω (Coarse.pt (c0h S j) w o) else 0) =
        if Yc S j w = Y then ((S.L ^ j) ^ 4) • ω (Coarse.pt (c0h S j) w o) else 0 := fun o ho => by
      rw [cen_fineOf_pt S hj1 w ho]
    rw [sum_congr rfl e3]
    split_ifs
    · rw [← smul_sum, hs w, smul_zero]
    · exact sum_const_zero

/-! ### The transport of the coarse bound -/

/-- **The cochain `B = a_jQ_jA` on the coarse torus**, in `V`. -/
def Bc (A : Fin 4 → Site NF → Mat) (j : ℕ) : Fin 4 → Coarse.T S.L (Mj S j) → VS N 1 :=
  fun μ z => emb (((S.L ^ j : ℕ) : ℂ) • Qt S A j (fineOf S j z) μ)

/-- The points of `𝐁` of the sequence with the single layer `j` are the `fineOf z`. -/
theorem sum_detB_one {β : Type*} [AddCommMonoid β] {j : ℕ} (hj0 : j ≤ S.k) (hj1 : j + 1 ≤ S.k) (G : Site NF → β) :
    ∑ y ∈ detB (oneLayer S j hj0).toDomSeq, G y = ∑ z : Coarse.T S.L (Mj S j), G (fineOf S j z) := by
  set S1 := oneLayer S j hj0
  have hsc : ∀ x, (S1.toDomSeq).sc x = j := oneLayer_sc S hj0
  refine (sum_detB_tr (S := S1) hj0 hsc G).trans ?_
  simp only [tr_emb (S := S1) hj0]
  exact sum_val_transport (Kj_eq S hj1) (fun v => G (fun ν => ((S.L ^ j * v ν : ℕ) : ZMod NF)))

lemma norm_emb_sq (X : Mat) : ‖emb (N := N) X‖ ^ 2 = N * hs2 X := by
  rw [norm_emb, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _), hs, Real.sq_sqrt (hs2_nonneg X)]

/-- The curl energy `‖∂A‖² = Σ_x½Σ_{μ,ν}|∂_μA_ν - ∂_νA_μ|²`. -/
def curlE (A : Fin 4 → Site NF → Mat) : ℝ :=
  ∑ x, 1 / 2 * ∑ μ, ∑ ν, hs2 ((A ν (x + unit NF μ) - A ν x) - (A μ (x + unit NF ν) - A μ x))

open Classical in
/-- **`lem:sf-two-layers` with the coarse right-hand side**: `‖P∂^*A‖² ≤ C_ol(‖∂A‖² + N⁻¹2^{16}L^{10}(Σ_p|∂B|² +
Σ_{Γ_j}|B|² + Σ_{Γ_{j+1}}|𝔮B|²))`, `B = a_jQ_jA` on the coarse torus. -/
theorem two_layers_coarse_rhs [NeZero N] {j : ℕ} (hj1 : j + 1 ≤ S.k) (hlow : ∀ i ≤ j, S.Ω i = Set.univ)
    (hhigh : ∀ i, j + 2 ≤ i → S.Ω i = ∅) (A : Fin 4 → Site NF → Mat) :
    ∑ x, hs2 (Pop S (X0 S) (W1 S) Set.univ (Ds1L a1 (cfgX (X0 S)) A) x) ≤
      SFOneLayer.Col * (curlE S A + (N : ℝ)⁻¹ * (2 ^ 16 * (S.L : ℝ) ^ 10 *
        (Coarse.Pall (Bc S A j) + Coarse.Gj (Lam S j) (c0h S j) (Bc S A j) +
          Coarse.Gj1 (Lam S j) (c0h S j) (Bc S A j)))) := by
  have hj0 : j ≤ S.k := by omega
  obtain ⟨ω, h0, hs, hb⟩ := Coarse.coarse_two_layers (Lam S j) (c0h S j) (Bc S A j)
  set ω' : Coarse.T S.L (Mj S j) → Mat := fun z => proj (ω z)
  have h0' : ∀ w, ¬ Lam S j w → ∀ o ∈ Coarse.bx4 (L := S.L), ω' (Coarse.pt (c0h S j) w o) = 0 := by
    intro w hw o ho
    simp only [ω', h0 w hw o ho]
    ext a b; simp [proj, matOf]
  have hs' : ∀ w, ∑ o ∈ Coarse.bx4 (L := S.L), ω' (Coarse.pt (c0h S j) w o) = 0 := by
    intro w
    have := congrArg (projL (N := N)) (hs w)
    rw [map_sum, map_zero] at this
    exact this
  have havg := avg_lamOf S hj1 hlow hhigh ω' h0' hs'
  refine (two_layers_gauge S hj0 hj1 hlow hhigh A havg).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (by unfold SFOneLayer.Col; positivity)
  refine add_le_add le_rfl ?_
  -- the sum over the points of `T^{(j)}`
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hpt : ∀ z μ, ((S.L ^ j : ℕ) : ℝ) ^ 2 *
      hs2 (Qt S (A - D0L a1 (cfgX (X0 S)) (lamOf S j ω')) j (fineOf S j z) μ) =
      (N : ℝ)⁻¹ * ‖Bc S A j μ z - (ω (z + Coarse.e μ) - ω z)‖ ^ 2 := by
    intro z μ
    have hn : ((S.L ^ j : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (pow_pos S.Lpos j).ne'
    have e : Bc S A j μ z - (ω (z + Coarse.e μ) - ω z) =
        emb (((S.L ^ j : ℕ) : ℂ) • Qt S (A - D0L a1 (cfgX (X0 S)) (lamOf S j ω')) j (fineOf S j z) μ) := by
      rw [Qt_sub, Qt_D0L S hj1, smul_sub, smul_smul, mul_inv_cancel₀ hn, one_smul]
      show _ = embL _
      rw [map_sub, map_sub]
      simp only [Bc, ω']
      show _ = embL _ - (emb (proj (ω (z + Coarse.e μ))) - emb (proj (ω z)))
      rw [emb_proj, emb_proj]; rfl
    rw [e, norm_emb_sq, RegularAverages.hs2_smul, ← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hN.ne', one_mul]
    congr 1
    rw [Complex.norm_natCast]
  have e2 : ((S.L ^ j : ℕ) : ℝ) ^ 2 * ∑ y ∈ detB (oneLayer S j hj0).toDomSeq, ∑ μ,
      hs2 (Qt (oneLayer S j hj0) (A - D0L a1 (cfgX (X0 S)) (lamOf S j ω')) j y μ) =
      (N : ℝ)⁻¹ * ∑ z, ∑ ν, ‖Bc S A j ν z - (ω (z + Coarse.e ν) - ω z)‖ ^ 2 := by
    have h := sum_detB_one S hj0 hj1
      (fun y => ∑ μ, hs2 (Qt S (A - D0L a1 (cfgX (X0 S)) (lamOf S j ω')) j y μ))
    calc _ = ((S.L ^ j : ℕ) : ℝ) ^ 2 *
          ∑ z, ∑ μ, hs2 (Qt S (A - D0L a1 (cfgX (X0 S)) (lamOf S j ω')) j (fineOf S j z) μ) :=
          congrArg (fun t => ((S.L ^ j : ℕ) : ℝ) ^ 2 * t) h
      _ = _ := by
          rw [mul_sum, mul_sum]
          refine sum_congr rfl fun z _ => ?_
          rw [mul_sum, mul_sum]
          exact sum_congr rfl fun μ _ => hpt z μ
  rw [e2]
  exact mul_le_mul_of_nonneg_left hb (inv_nonneg.2 hN.le)

end SFBounds
end CoreLean

end
