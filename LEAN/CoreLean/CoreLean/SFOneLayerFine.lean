/-
`lem:sf-one-layer` of BALABAN_CORE.tex (`a5545dd8c0af`) for a sequence with a single layer of the order `j`, on its fine
lattice: the transport of the fine lattice `Site (N0 S)` (`a₀ = 1`) to the torus `(ℤ/nK)⁴` of `MomentumTorus.lean`
(`a₀ = 1/n`, `n = L^j = 2r + 1`, `K = 2L^{m_𝕋+k-j}`), where `SFOneLayerTorus.one_layer` holds.

* `rj`, `Kj`, `NN_eq`: the parameters and `nK = N₀`.
* `tr`: the coordinatewise bijection `Tor (NN r K) → Site (N0 S)`, additive (`tr_add`), `tr_single`, `sum_tr`.
* `tr_emb`, `sum_Blk_tr`, `sum_detB_tr`, `Qpop_tr`: the blocks, the points of `𝐁`, and `Q'` on the torus.
* `PT`, `PT_norm`, `PT_weak`: the scalar projection transported to the torus satisfies the hypotheses of `one_layer`.
* `one_layer_fine` (scalar), `one_layer_mat` (`M_N(ℂ)`-valued), `hb_triv` (`T̂` invertible at the trivial configuration),
  `sf_one_layer`: **`lem:sf-one-layer`** for `oneLayer S j`, `‖P∂^*A‖² ≤ C_ol(‖∂A‖² + a_j²Σ_{y,μ}|(QA)(y, μ)|²)`.
-/
import CoreLean.SFEntrywise
import CoreLean.SFOneLayerTorus

open Finset Matrix

noncomputable section

namespace CoreLean
namespace SFBounds

open Lattices SeqDom Blocks SmallFieldBlocks SFLocal TorusFourier SmallFieldDecay SmallFieldCoercivity
  SequenceOperators CompressedInverse ConcretePairing SFBox SFBox.SeqDomBox

variable (S : SeqDom) {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "NF" => SequenceAverages.N0 S

/-- `r` with `2r + 1 = L^j`. -/
def rj (j : ℕ) : ℕ := Blocks.half S.L j

/-- `K = 2L^{m_𝕋+k-j}`, the side of `T^{(j)}` in the units `a_j`. -/
def Kj (j : ℕ) : ℕ := 2 * S.L ^ (S.mT + S.k - j)

instance (j : ℕ) : NeZero (Kj S j) := ⟨by unfold Kj; have := S.Lpos; positivity⟩

lemma n_eq (j : ℕ) : 2 * rj S j + 1 = S.L ^ j := two_half_add_one S.L_odd j

lemma NN_eq {j : ℕ} (hj : j ≤ S.k) : MomentumTorus.NN (rj S j) (Kj S j) = NF := by
  have e : S.mT + S.k = j + (S.mT + S.k - j) := by omega
  rw [MomentumTorus.NN, n_eq, Kj, SequenceAverages.N0_eq]
  conv_rhs => rw [e]
  rw [pow_add]; ring

variable {S}

/-- **The transport** `Tor (NN r K) → Site (N0 S)`: the same residues. -/
def tr (j : ℕ) (z : TorusFourier.Tor (MomentumTorus.NN (rj S j) (Kj S j))) : Site NF := fun ν => ((z ν).val : ZMod NF)

lemma tr_add {j : ℕ} (hj : j ≤ S.k) (z w : TorusFourier.Tor (MomentumTorus.NN (rj S j) (Kj S j))) :
    tr j (z + w) = tr j z + tr j w := by
  funext ν
  simp only [tr, Pi.add_apply, ZMod.val_add, NN_eq S hj, ZMod.natCast_mod]
  push_cast; ring

lemma val_lt_NF {j : ℕ} (hj : j ≤ S.k) (a : ZMod (MomentumTorus.NN (rj S j) (Kj S j))) : a.val < NF := by
  rw [← NN_eq S hj]; exact ZMod.val_lt a

lemma tr_injective {j : ℕ} (hj : j ≤ S.k) : Function.Injective (tr (S := S) j) := by
  intro z w h
  funext ν
  have := congrFun h ν
  simp only [tr] at this
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (val_lt_NF hj _), Nat.mod_eq_of_lt (val_lt_NF hj _)] at this
  exact ZMod.val_injective _ this

lemma tr_bijective {j : ℕ} (hj : j ≤ S.k) : Function.Bijective (tr (S := S) j) := by
  refine ⟨tr_injective hj, fun x => ⟨fun ν => ((x ν).val : ZMod (MomentumTorus.NN (rj S j) (Kj S j))), ?_⟩⟩
  funext ν
  simp only [tr]
  rw [ZMod.val_natCast, NN_eq S hj, ZMod.natCast_mod, ZMod.natCast_zmod_val]

lemma sum_tr {M : Type*} [AddCommMonoid M] {j : ℕ} (hj : j ≤ S.k) (F : Site NF → M) :
    ∑ z, F (tr j z) = ∑ x, F x :=
  Function.Bijective.sum_comp (tr_bijective hj) F

lemma tr_single {j : ℕ} (hj : j ≤ S.k) (μ : Fin 4) (t : ℕ) :
    tr (S := S) j (Pi.single μ (t : ZMod (MomentumTorus.NN (rj S j) (Kj S j)))) = ((t : ℕ) : ZMod NF) • unit NF μ := by
  funext ν
  simp only [tr, unit, Pi.smul_apply, smul_eq_mul]
  by_cases h : ν = μ
  · subst h
    simp only [Pi.single_eq_same, mul_one]
    rw [ZMod.val_natCast, NN_eq S hj, ZMod.natCast_mod]
  · simp [Pi.single_eq_of_ne h]

lemma tr_intCast {j : ℕ} (hj : j ≤ S.k) (w : ℤ) :
    (((w : ZMod (MomentumTorus.NN (rj S j) (Kj S j))).val : ℕ) : ZMod NF) = (w : ZMod NF) := by
  have h := ZMod.val_intCast (n := MomentumTorus.NN (rj S j) (Kj S j)) w
  rw [← Int.cast_natCast, h, NN_eq S hj, ZMod.intCast_mod]

lemma tr_castw {j : ℕ} (hj : j ≤ S.k) (w : Fin 4 → ℤ) :
    tr (S := S) j (MomentumTorus.castw (rj S j) (Kj S j) w) = fun ν => (w ν : ZMod NF) := by
  funext ν; simp only [tr, MomentumTorus.castw]; exact tr_intCast hj _

lemma tr_emb {j : ℕ} (hj : j ≤ S.k) (y : TorusFourier.Tor (Kj S j)) :
    tr (S := S) j (MomentumTorus.emb (rj S j) (Kj S j) y) = fun ν => (((S.L ^ j * (y ν).val : ℕ)) : ZMod NF) := by
  funext ν
  simp only [tr, MomentumTorus.emb]
  rw [← Nat.cast_mul, ZMod.val_natCast, NN_eq S hj, ZMod.natCast_mod, n_eq]

lemma inLat_tr_emb {j : ℕ} (hj : j ≤ S.k) (y : TorusFourier.Tor (Kj S j)) :
    InLat S.L j (tr (S := S) j (MomentumTorus.emb (rj S j) (Kj S j) y)) := by
  rw [tr_emb hj]
  intro ν
  exact ⟨((y ν).val : ℤ), by push_cast; ring⟩

/-- The offsets of a block: `phi(y_f, o) = tr(emb y + (o - r))`. -/
lemma phi_tr {j : ℕ} (hj : j ≤ S.k) (y : TorusFourier.Tor (Kj S j)) (o : Fin 4 → ℕ) :
    phi S.toDomSeq j (tr (S := S) j (MomentumTorus.emb (rj S j) (Kj S j) y)) o =
      tr (S := S) j (MomentumTorus.emb (rj S j) (Kj S j) y +
        MomentumTorus.castw (rj S j) (Kj S j) (fun ν => (o ν : ℤ) - rj S j)) := by
  rw [tr_add hj, tr_castw hj]
  funext ν
  simp only [phi, Pi.add_apply]
  rfl

/-- The offsets `[0, n)⁴` and `[-r, r]⁴`. -/
lemma sum_box_shift {M : Type*} [AddCommMonoid M] (r : ℕ) (G : (Fin 4 → ℤ) → M) :
    ∑ o ∈ DiscretePoincare.box 4 (2 * r + 1), G (fun ν => (o ν : ℤ) - r) = ∑ w ∈ MomentumSymbols.box r, G w := by
  refine Finset.sum_nbij' (fun o ν => (o ν : ℤ) - r) (fun w ν => (w ν + r).toNat) (fun o ho => ?_) (fun w hw => ?_)
    (fun o ho => ?_) (fun w hw => ?_) (fun o _ => rfl)
  · simp only [DiscretePoincare.box, Fintype.mem_piFinset, mem_range] at ho
    simp only [MomentumSymbols.box, Fintype.mem_piFinset, mem_Icc]
    intro ν; have := ho ν; constructor <;> omega
  · simp only [MomentumSymbols.box, Fintype.mem_piFinset, mem_Icc] at hw
    simp only [DiscretePoincare.box, Fintype.mem_piFinset, mem_range]
    intro ν; have := hw ν; omega
  · funext ν; simp
  · funext ν
    simp only [MomentumSymbols.box, Fintype.mem_piFinset, mem_Icc] at hw
    have := hw ν
    simp only
    rw [Int.toNat_of_nonneg (by omega)]; ring

/-- **A block of `T^{(j)}` on the torus**: `Σ_{x ∈ B^j(y_f)}F(x) = Σ_{w ∈ [-r,r]⁴}F(tr(emb y + w))`. -/
lemma sum_Blk_tr {M : Type*} [AddCommMonoid M] {j : ℕ} (hj : j ≤ S.k) (y : TorusFourier.Tor (Kj S j))
    (F : Site NF → M) :
    ∑ x ∈ Blk S.toDomSeq j (tr (S := S) j (MomentumTorus.emb (rj S j) (Kj S j) y)), F x =
      ∑ w ∈ MomentumSymbols.box (rj S j),
        F (tr (S := S) j (MomentumTorus.emb (rj S j) (Kj S j) y + MomentumTorus.castw (rj S j) (Kj S j) w)) := by
  rw [sum_Blk (S := S.toDomSeq) j hj (inLat_tr_emb hj y) F]
  simp only [phi_tr hj]
  rw [show (S.toDomSeq).L ^ j = 2 * rj S j + 1 from (n_eq S j).symm]
  exact sum_box_shift (rj S j) (fun w => F (tr j (MomentumTorus.emb (rj S j) (Kj S j) y +
    MomentumTorus.castw (rj S j) (Kj S j) w)))

lemma dvd_val_of_isMul {m : ℕ} (hm : m ∣ NF) {u : ZMod NF} (hu : IsMul m u) : m ∣ u.val := by
  obtain ⟨r, rfl⟩ := hu
  have h := ZMod.val_intCast (n := NF) ((m : ℤ) * r)
  have h2 : (m : ℤ) ∣ ((m : ℤ) * r) % (NF : ℤ) := by
    rw [Int.emod_def]; exact Dvd.dvd.sub (dvd_mul_right _ _) (Dvd.dvd.mul_right (Int.natCast_dvd_natCast.2 hm) _)
  rw [← h] at h2
  exact Int.natCast_dvd_natCast.1 h2

lemma L_pow_mul_K {j : ℕ} (hj : j ≤ S.k) : S.L ^ j * Kj S j = NF := by
  rw [← NN_eq S hj, MomentumTorus.NN, n_eq]

/-- The point of `T^{(k)}` of a point of `T^{(j)}`. -/
def cr (j : ℕ) (x : Site NF) : TorusFourier.Tor (Kj S j) := fun ν => (((x ν).val / S.L ^ j : ℕ) : ZMod (Kj S j))

/-- **The points of `T^{(j)}` are the `tr(emb y)`**, `y` in the torus of the side `K`: for a sequence with the single
layer `j`, `Σ_{y ∈ 𝐁}G(y) = Σ_{y'}G(tr(emb y'))`. -/
theorem sum_detB_tr {M : Type*} [AddCommMonoid M] {j : ℕ} (hj : j ≤ S.k) (hsc : ∀ x, (S.toDomSeq).sc x = j)
    (G : Site NF → M) :
    ∑ y ∈ detB S.toDomSeq, G y = ∑ y' : TorusFourier.Tor (Kj S j), G (tr (S := S) j (MomentumTorus.emb (rj S j) (Kj S j) y')) := by
  have hLK := L_pow_mul_K (S := S) hj
  have hLpos : 0 < S.L ^ j := pow_pos S.Lpos _
  have hmem : ∀ y, y ∈ detB S.toDomSeq ↔ InLat S.L j y := fun y => by
    rw [mem_detB_iff_inLat S y, hsc y]
  symm
  refine Finset.sum_nbij' (fun y' => tr (S := S) j (MomentumTorus.emb (rj S j) (Kj S j) y')) (cr j)
    (fun y' _ => (hmem _).2 (inLat_tr_emb hj y')) (fun _ _ => mem_univ _) (fun y' _ => ?_) (fun x hx => ?_)
    (fun _ _ => rfl)
  · funext ν
    simp only [cr, tr_emb hj]
    have hlt : S.L ^ j * (y' ν).val < NF := by
      rw [← hLK]; exact Nat.mul_lt_mul_of_pos_left (ZMod.val_lt _) hLpos
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hlt, Nat.mul_div_cancel_left _ hLpos, ZMod.natCast_zmod_val]
  · have hx' := (hmem x).1 hx
    funext ν
    simp only [tr_emb hj, cr]
    have hd := dvd_val_of_isMul (S := S) (by rw [← hLK]; exact dvd_mul_right _ _) (hx' ν)
    obtain ⟨q, hq⟩ := hd
    have hqK : q < Kj S j := by
      have := ZMod.val_lt (x ν); rw [hq, ← hLK] at this
      exact lt_of_mul_lt_mul_left this (Nat.zero_le _)
    rw [hq, Nat.mul_div_cancel_left _ hLpos, ZMod.val_natCast, Nat.mod_eq_of_lt hqK, ← hq, ZMod.natCast_zmod_val]

/-- The inverse of `tr`. -/
def trinv (j : ℕ) (x : Site NF) : TorusFourier.Tor (MomentumTorus.NN (rj S j) (Kj S j)) :=
  fun ν => ((x ν).val : ZMod (MomentumTorus.NN (rj S j) (Kj S j)))

lemma tr_trinv {j : ℕ} (hj : j ≤ S.k) (x : Site NF) : tr (S := S) j (trinv j x) = x := by
  funext ν
  simp only [tr, trinv]
  rw [ZMod.val_natCast, NN_eq S hj, ZMod.natCast_mod, ZMod.natCast_zmod_val]

lemma trinv_tr {j : ℕ} (hj : j ≤ S.k) (z : TorusFourier.Tor (MomentumTorus.NN (rj S j) (Kj S j))) :
    trinv (S := S) j (tr j z) = z :=
  tr_injective hj (tr_trinv hj _)

lemma tr_step {j : ℕ} (hj : j ≤ S.k) (z : TorusFourier.Tor (MomentumTorus.NN (rj S j) (Kj S j))) (μ : Fin 4) :
    tr (S := S) j (z + Pi.single μ 1) = tr j z + unit NF μ := by
  rw [tr_add hj]
  have := tr_single (S := S) hj μ 1
  simp only [Nat.cast_one, one_smul] at this
  rw [this]

/-- **`Q'` on the torus**: `Q'_k(λ ∘ tr)(y) = Q'λ(tr(emb y))` for the sequence with the single layer `j`. -/
lemma Qpop_tr {j : ℕ} (hj : j ≤ S.k) (hsc : ∀ x, (S.toDomSeq).sc x = j) (lam : Site NF → ℂ)
    (y : TorusFourier.Tor (Kj S j)) :
    MomentumTorus.Qpop (rj S j) (Kj S j) (fun z => lam (tr (S := S) j z)) y =
      Qs S S.toDomSeq lam (tr (S := S) j (MomentumTorus.emb (rj S j) (Kj S j) y)) := by
  unfold Qs MomentumTorus.Qpop
  rw [hsc, DiscretePoincare.card_box]
  simp only [phi_tr hj]
  rw [show (S.toDomSeq).L ^ j = 2 * rj S j + 1 from (n_eq S j).symm,
    sum_box_shift (rj S j) (fun w => lam (tr j (MomentumTorus.emb (rj S j) (Kj S j) y +
      MomentumTorus.castw (rj S j) (Kj S j) w)))]
  push_cast; ring

/-- **The operator on the torus**: `p` transported by `tr`. -/
def PT (j : ℕ) [NeZero N] (φ : TorusFourier.Tor (MomentumTorus.NN (rj S j) (Kj S j)) → ℂ) :
    TorusFourier.Tor (MomentumTorus.NN (rj S j) (Kj S j)) → ℂ :=
  fun z => ps (N := N) S Set.univ (fun x => φ (trinv j x)) (tr j z)

lemma PT_norm [NeZero N] {j : ℕ} (hj : j ≤ S.k)
    (hb : Function.Bijective (kerLin (kerT (N := N) S (Subtype.val : BD S Set.univ → Site NF) (X0 S) (W1 S) Set.univ)))
    (φ : TorusFourier.Tor (MomentumTorus.NN (rj S j) (Kj S j)) → ℂ) :
    ∑ z, ‖PT (N := N) j φ z‖ ^ 2 = (∑ z, starRingEnd ℂ (PT (N := N) j φ z) * φ z).re := by
  have e : ∀ z, φ z = (fun x => φ (trinv (S := S) j x)) (tr j z) := fun z => by simp only [trinv_tr hj]
  simp only [PT]
  conv_rhs => arg 1; arg 2; ext z; rw [e z]
  rw [sum_tr hj (fun x => ‖ps (N := N) S Set.univ (fun x => φ (trinv j x)) x‖ ^ 2),
    sum_tr hj (fun x => starRingEnd ℂ (ps (N := N) S Set.univ (fun x => φ (trinv j x)) x) * φ (trinv j x))]
  exact ps_norm S Set.univ hb _

/-- **`PT` satisfies the weak equation of `G'(range Q'^*)`** on the torus, with `ν = n²m + (1 - 𝖺_j)Q'v`. -/
theorem PT_weak [NeZero N] {j : ℕ} (hj : j ≤ S.k) (hsc : ∀ x, (S.toDomSeq).sc x = j)
    (hb : Function.Bijective (kerLin (kerT (N := N) S (Subtype.val : BD S Set.univ → Site NF) (X0 S) (W1 S) Set.univ)))
    (φ : TorusFourier.Tor (MomentumTorus.NN (rj S j) (Kj S j)) → ℂ) :
    MomentumTorus.WeakRange (rj S j) (Kj S j) (PT (N := N) j φ) := by
  set φF : Site NF → ℂ := fun x => φ (trinv j x)
  set v := ps (N := N) S Set.univ φF
  obtain ⟨m, hm⟩ := ps_weak S hb φF
  set c : ℂ := ((SequenceOperators.aseq 1 S.L j : ℝ) : ℂ)
  set n : ℂ := ((2 * rj S j + 1 : ℕ) : ℂ)
  have hn : n = ((S.L ^ j : ℕ) : ℂ) := by simp only [n, n_eq]
  have hn0 : n ≠ 0 := by rw [hn]; exact_mod_cast (pow_pos S.Lpos j).ne'
  have hPT : ∀ z, PT (N := N) j φ z = v (tr j z) := fun z => rfl
  refine ⟨fun y => n ^ 2 * m (tr j (MomentumTorus.emb (rj S j) (Kj S j) y)) +
    (1 - c) * MomentumTorus.Qpop (rj S j) (Kj S j) (PT (N := N) j φ) y, fun lamT => ?_⟩
  set lam : Site NF → ℂ := fun x => lamT (trinv j x)
  have hlam : ∀ z, lamT z = lam (tr j z) := fun z => by simp only [lam, trinv_tr hj]
  have hl := hm lam
  -- the constants on `𝐁`
  have hc2 : ∀ y ∈ detB S.toDomSeq, ((SequenceOperators.aseq 1 S.L (S.toDomSeq.sc y) * (S.L : ℝ) ^ (2 * S.toDomSeq.sc y) : ℝ) : ℂ) =
      c * n ^ 2 := fun y _ => by rw [hsc, hn]; push_cast; ring
  have hc4 : ∀ y ∈ detB S.toDomSeq, (((S.L : ℝ) ^ (4 * S.toDomSeq.sc y) : ℝ) : ℂ) = n ^ 4 := fun y _ => by
    rw [hsc, hn]; push_cast; ring
  have e2 : ∑ y ∈ detB S.toDomSeq, ((SequenceOperators.aseq 1 S.L (S.toDomSeq.sc y) *
      (S.L : ℝ) ^ (2 * S.toDomSeq.sc y) : ℝ) : ℂ) *
        (starRingEnd ℂ (Qs S S.toDomSeq lam y) * Qs S S.toDomSeq v y) =
      c * n ^ 2 * ∑ y ∈ detB S.toDomSeq, starRingEnd ℂ (Qs S S.toDomSeq lam y) * Qs S S.toDomSeq v y := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun y hy => by rw [hc2 y hy]
  have e4 : ∑ y ∈ detB S.toDomSeq, (((S.L : ℝ) ^ (4 * S.toDomSeq.sc y) : ℝ) : ℂ) *
        (starRingEnd ℂ (Qs S S.toDomSeq lam y) * m y) =
      n ^ 4 * ∑ y ∈ detB S.toDomSeq, starRingEnd ℂ (Qs S S.toDomSeq lam y) * m y := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun y hy => by rw [hc4 y hy]
  rw [e2, e4, sum_detB_tr hj hsc, sum_detB_tr hj hsc] at hl
  -- the differences
  have hd : ∀ μ, (n ^ 4)⁻¹ * ∑ z, starRingEnd ℂ (MomentumTorus.d0 (rj S j) (Kj S j) μ lamT z) *
      MomentumTorus.d0 (rj S j) (Kj S j) μ (PT (N := N) j φ) z =
      (n ^ 2)⁻¹ * ∑ x, starRingEnd ℂ (lam (x + unit NF μ) - lam x) * (v (x + unit NF μ) - v x) := by
    intro μ
    have e : ∀ z, starRingEnd ℂ (MomentumTorus.d0 (rj S j) (Kj S j) μ lamT z) *
        MomentumTorus.d0 (rj S j) (Kj S j) μ (PT (N := N) j φ) z =
        n ^ 2 * (starRingEnd ℂ (lam (tr j z + unit NF μ) - lam (tr j z)) * (v (tr j z + unit NF μ) - v (tr j z))) := by
      intro z
      simp only [MomentumTorus.d0, hlam, hPT, tr_step hj, map_mul, map_natCast]
      ring
    rw [Finset.sum_congr rfl fun z _ => e z, ← Finset.mul_sum,
      sum_tr hj (fun x => starRingEnd ℂ (lam (x + unit NF μ) - lam x) * (v (x + unit NF μ) - v x))]
    field_simp
  -- the averages
  have hq : ∀ (g : Site NF → ℂ) (y : TorusFourier.Tor (Kj S j)),
      MomentumTorus.Qpop (rj S j) (Kj S j) (fun z => g (tr (S := S) j z)) y =
        Qs S S.toDomSeq g (tr j (MomentumTorus.emb (rj S j) (Kj S j) y)) := fun g y => Qpop_tr hj hsc g y
  have hql : MomentumTorus.Qpop (rj S j) (Kj S j) lamT = fun y => Qs S S.toDomSeq lam
      (tr j (MomentumTorus.emb (rj S j) (Kj S j) y)) := by
    funext y; rw [← hq]; congr 1; funext z; exact hlam z
  have hqv : MomentumTorus.Qpop (rj S j) (Kj S j) (PT (N := N) j φ) = fun y => Qs S S.toDomSeq v
      (tr j (MomentumTorus.emb (rj S j) (Kj S j) y)) := by
    funext y; rw [← hq]; rfl
  rw [Finset.sum_congr rfl fun μ _ => hd μ]
  simp only [hql, hqv]
  rw [Finset.sum_comm] at hl
  -- the algebra
  rw [← Finset.mul_sum]
  have hR : ∀ (A B C : TorusFourier.Tor (Kj S j) → ℂ), ∑ y, A y * (n ^ 2 * B y + (1 - c) * C y) =
      n ^ 2 * ∑ y, A y * B y + (1 - c) * ∑ y, A y * C y := fun A B C => by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun y _ => by ring
  rw [hR]
  field_simp
  linear_combination hl

/-! ### `lem:sf-one-layer` on the fine lattice -/

lemma ps_smul [NeZero N] (ΩD : Set (Site NF)) (c : ℂ) (φ : Site NF → ℂ) :
    ps (N := N) S ΩD (fun x => c * φ x) = fun x => c * ps (N := N) S ΩD φ x := by
  funext x
  have e : (fun y => (c * φ y) • (E00 : Mat)) = c • (fun y => φ y • (E00 : Mat)) := by
    funext y; simp [smul_smul]
  simp only [ps, e, map_smul]
  rfl

/-- `∂^*A = Σ_μ(A_μ(x - e_μ) - A_μ(x))` on the fine lattice (`a₀ = 1`). -/
def dsF (A : Fin 4 → Site NF → ℂ) (x : Site NF) : ℂ := ∑ μ, (A μ (x - unit NF μ) - A μ x)

/-- `‖∂A‖² = Σ_x½Σ_{μ,ν}|∂_μA_ν - ∂_νA_μ|²`. -/
def curlF (A : Fin 4 → Site NF → ℂ) : ℝ :=
  ∑ x, 1 / 2 * ∑ μ, ∑ ν, ‖(A ν (x + unit NF μ) - A ν x) - (A μ (x + unit NF ν) - A μ x)‖ ^ 2

/-- The scalar average `Q` of the trivial configuration on the bond `(y, μ)` of `T^{(j)}`. -/
def QtS (A : Fin 4 → Site NF → ℂ) (j : ℕ) (y : Site NF) (μ : Fin 4) : ℂ :=
  ((((S.L ^ j : ℕ) : ℂ)) ^ 5)⁻¹ * ∑ x ∈ Blk S.toDomSeq j y, ∑ t ∈ range (S.L ^ j),
    A μ (x + ((t : ℕ) : ZMod NF) • unit NF μ)

lemma tr_neg_step {j : ℕ} (hj : j ≤ S.k) (z : TorusFourier.Tor (MomentumTorus.NN (rj S j) (Kj S j))) (μ : Fin 4) :
    tr (S := S) j (z + -Pi.single μ 1) = tr j z - unit NF μ := by
  have h := tr_step (S := S) hj (z + -Pi.single μ 1) μ
  rw [neg_add_cancel_right] at h
  rw [h]; abel

/-- **`lem:sf-one-layer`** for a sequence with the single layer `j`, on its fine lattice (`a₀ = 1`, `a_j = n = L^j`), scalar
values: `Σ_x|p(∂^*A)(x)|² ≤ C_ol(‖∂A‖² + n²Σ_{y ∈ 𝐁}Σ_μ|(QA)(y, μ)|²)`. -/
theorem one_layer_fine [NeZero N] {j : ℕ} (hj : j ≤ S.k) (hsc : ∀ x, (S.toDomSeq).sc x = j)
    (hb : Function.Bijective (kerLin (kerT (N := N) S (Subtype.val : BD S Set.univ → Site NF) (X0 S) (W1 S) Set.univ)))
    (A : Fin 4 → Site NF → ℂ) :
    ∑ x, ‖ps (N := N) S Set.univ (dsF A) x‖ ^ 2 ≤
      SFOneLayer.Col * (curlF A + ((S.L ^ j : ℕ) : ℝ) ^ 2 *
        ∑ y ∈ detB S.toDomSeq, ∑ μ, ‖QtS A j y μ‖ ^ 2) := by
  have hn : 2 * rj S j + 1 = S.L ^ j := n_eq S j
  have hnR : (0 : ℝ) < ((2 * rj S j + 1 : ℕ) : ℝ) := by rw [hn]; exact_mod_cast pow_pos S.Lpos j
  set AT : Fin 4 → TorusFourier.Tor (MomentumTorus.NN (rj S j) (Kj S j)) → ℂ := fun μ z => A μ (tr j z)
  have h := MomentumTorus.one_layer (rj S j) (Kj S j) (PT (N := N) j) (fun f => PT_weak hj hsc hb f)
    (fun f => PT_norm hj hb f) AT
  -- the left side
  have hds : ∀ x, MomentumTorus.dstar (rj S j) (Kj S j) AT (trinv j x) = ((2 * rj S j + 1 : ℕ) : ℂ) * dsF A x := fun x => by
    simp only [MomentumTorus.dstar, AT, tr_neg_step hj, tr_trinv hj, dsF, Finset.mul_sum]
  have hL : ∑ z, ‖PT (N := N) j (MomentumTorus.dstar (rj S j) (Kj S j) AT) z‖ ^ 2 =
      ((2 * rj S j + 1 : ℕ) : ℝ) ^ 2 * ∑ x, ‖ps (N := N) S Set.univ (dsF A) x‖ ^ 2 := by
    simp only [PT, hds, ps_smul]
    rw [sum_tr hj (fun x => ‖((2 * rj S j + 1 : ℕ) : ℂ) * ps (N := N) S Set.univ (dsF A) x‖ ^ 2), Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [norm_mul, mul_pow, Complex.norm_natCast]
  -- the energy
  have hE : MomentumTorus.energy0 (rj S j) (Kj S j) AT = (((2 * rj S j + 1 : ℕ) : ℝ) ^ 2)⁻¹ * curlF A := by
    unfold MomentumTorus.energy0 curlF
    have e : ∀ z, 1 / 2 * ∑ μ, ∑ ν, ‖MomentumTorus.d0 (rj S j) (Kj S j) μ (AT ν) z -
        MomentumTorus.d0 (rj S j) (Kj S j) ν (AT μ) z‖ ^ 2 =
        ((2 * rj S j + 1 : ℕ) : ℝ) ^ 2 * (1 / 2 * ∑ μ, ∑ ν, ‖(A ν (tr j z + unit NF μ) - A ν (tr j z)) -
          (A μ (tr j z + unit NF ν) - A μ (tr j z))‖ ^ 2) := fun z => by
      simp only [MomentumTorus.d0, AT, tr_step hj, ← mul_sub, norm_mul, mul_pow, Complex.norm_natCast, Finset.mul_sum]
      ring
    rw [Finset.sum_congr rfl fun z _ => e z, ← Finset.mul_sum,
      sum_tr hj (fun x => 1 / 2 * ∑ μ, ∑ ν, ‖(A ν (x + unit NF μ) - A ν x) - (A μ (x + unit NF ν) - A μ x)‖ ^ 2)]
    have hn4 : (((2 * rj S j + 1 : ℕ) : ℝ) ^ 4)⁻¹ * ((2 * rj S j + 1 : ℕ) : ℝ) ^ 2 =
        (((2 * rj S j + 1 : ℕ) : ℝ) ^ 2)⁻¹ := by field_simp
    rw [← mul_assoc, hn4]
  -- the averages
  have hQ : ∀ μ (y : TorusFourier.Tor (Kj S j)), MomentumTorus.Qop (rj S j) (Kj S j) AT μ y =
      QtS A j (tr j (MomentumTorus.emb (rj S j) (Kj S j) y)) μ := fun μ y => by
    unfold MomentumTorus.Qop QtS
    rw [sum_Blk_tr hj y]
    simp only [AT, tr_add hj, tr_single hj, Finset.mul_sum]
    rw [← hn]
    refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun t _ => ?_
    ring
  have hQs : ∑ μ, ∑ y, ‖MomentumTorus.Qop (rj S j) (Kj S j) AT μ y‖ ^ 2 =
      ∑ y ∈ detB S.toDomSeq, ∑ μ, ‖QtS A j y μ‖ ^ 2 := by
    simp only [hQ]
    rw [Finset.sum_comm, sum_detB_tr hj hsc]
  rw [hL, hE, hQs] at h
  rw [← hn]
  have hCol : 0 ≤ SFOneLayer.Col := by unfold SFOneLayer.Col SFOneLayer.g0; positivity
  have key : ((((2 * rj S j + 1 : ℕ) : ℝ) ^ 4)⁻¹ * (((2 * rj S j + 1 : ℕ) : ℝ) ^ 2 * ∑ x, ‖ps (N := N) S Set.univ (dsF A) x‖ ^ 2)) * ((2 * rj S j + 1 : ℕ) : ℝ) ^ 2 ≤
      (SFOneLayer.Col * ((((2 * rj S j + 1 : ℕ) : ℝ) ^ 2)⁻¹ * curlF A + ∑ y ∈ detB S.toDomSeq, ∑ μ, ‖QtS A j y μ‖ ^ 2)) * ((2 * rj S j + 1 : ℕ) : ℝ) ^ 2 :=
    mul_le_mul_of_nonneg_right h (by positivity)
  have l1 : ((((2 * rj S j + 1 : ℕ) : ℝ) ^ 4)⁻¹ * (((2 * rj S j + 1 : ℕ) : ℝ) ^ 2 * ∑ x, ‖ps (N := N) S Set.univ (dsF A) x‖ ^ 2)) * ((2 * rj S j + 1 : ℕ) : ℝ) ^ 2 =
      ∑ x, ‖ps (N := N) S Set.univ (dsF A) x‖ ^ 2 := by field_simp
  have l2 : (SFOneLayer.Col * ((((2 * rj S j + 1 : ℕ) : ℝ) ^ 2)⁻¹ * curlF A + ∑ y ∈ detB S.toDomSeq, ∑ μ, ‖QtS A j y μ‖ ^ 2)) *
      ((2 * rj S j + 1 : ℕ) : ℝ) ^ 2 = SFOneLayer.Col * (curlF A + ((2 * rj S j + 1 : ℕ) : ℝ) ^ 2 * ∑ y ∈ detB S.toDomSeq, ∑ μ, ‖QtS A j y μ‖ ^ 2) := by
    field_simp
  rw [l1, l2] at key
  exact key

lemma swap5 {α β γ δ ε : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ] [Fintype ε]
    (F : α → β → γ → δ → ε → ℝ) :
    ∑ x, ∑ μ, ∑ ν, ∑ a, ∑ b, F x μ ν a b = ∑ a, ∑ b, ∑ x, ∑ μ, ∑ ν, F x μ ν a b := by
  conv_lhs => arg 2; ext x; arg 2; ext μ; rw [Finset.sum_comm]
  conv_lhs => arg 2; ext x; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => arg 2; ext a; arg 2; ext x; arg 2; ext μ; rw [Finset.sum_comm]
  conv_lhs => arg 2; ext a; arg 2; ext x; rw [Finset.sum_comm]
  conv_lhs => arg 2; ext a; rw [Finset.sum_comm]

lemma hs2_entries (X : Mat) : hs2 X = (N : ℝ)⁻¹ * ∑ a, ∑ b, ‖X a b‖ ^ 2 := by
  rw [hs2_eq_sum, Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [Complex.normSq_eq_norm_sq]

lemma Ds1L_entry (A : Fin 4 → Site NF → Mat) (x : Site NF) (a b : Fin N) :
    Ds1L a1 (cfgX (X0 S)) A x a b = dsF (fun μ y => A μ y a b) x := by
  simp only [Ds1L_apply, Ds1, Dbw, val_X0, Ad_one', dsF, a1, Complex.ofReal_one, inv_one, one_smul,
    Matrix.sum_apply, Matrix.sub_apply]

lemma Qt_entry (A : Fin 4 → Site NF → Mat) (j : ℕ) (y : Site NF) (μ : Fin 4) (a b : Fin N) :
    Qt S A j y μ a b = QtS (fun μ x => A μ x a b) j y μ := by
  simp only [Qt, QtS, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]

/-- **`lem:sf-one-layer`** for a sequence with the single layer `j`, on its fine lattice, `M_N(ℂ)`-valued `1`-forms
(`a₀ = 1`, `a_j = L^j`): `‖P∂^*A‖² ≤ C_ol(‖∂A‖² + a_j²Σ_{y,μ}|(QA)(y, μ)|²)`. -/
theorem one_layer_mat [NeZero N] {j : ℕ} (hj : j ≤ S.k) (hsc : ∀ x, (S.toDomSeq).sc x = j)
    (hb : Function.Bijective (kerLin (kerT (N := N) S (Subtype.val : BD S Set.univ → Site NF) (X0 S) (W1 S) Set.univ)))
    (A : Fin 4 → Site NF → Mat) :
    ∑ x, hs2 (Pop S (X0 S) (W1 S) Set.univ (Ds1L a1 (cfgX (X0 S)) A) x) ≤
      SFOneLayer.Col * (∑ x, 1 / 2 * ∑ μ, ∑ ν, hs2 ((A ν (x + unit NF μ) - A ν x) - (A μ (x + unit NF ν) - A μ x)) +
        ((S.L ^ j : ℕ) : ℝ) ^ 2 * ∑ y ∈ detB S.toDomSeq, ∑ μ, hs2 (Qt S A j y μ)) := by
  have hNinv : (0 : ℝ) ≤ (N : ℝ)⁻¹ := by positivity
  set Aab : Fin N → Fin N → Fin 4 → Site NF → ℂ := fun a b μ y => A μ y a b
  have hL : ∑ x, hs2 (Pop S (X0 S) (W1 S) Set.univ (Ds1L a1 (cfgX (X0 S)) A) x) =
      (N : ℝ)⁻¹ * ∑ a, ∑ b, ∑ x, ‖ps (N := N) S Set.univ (dsF (Aab a b)) x‖ ^ 2 := by
    simp only [hs2_entries, Pop_entry (N := N) S Set.univ hb, Ds1L_entry, ← Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
  have hC : ∑ x, 1 / 2 * ∑ μ, ∑ ν, hs2 ((A ν (x + unit NF μ) - A ν x) - (A μ (x + unit NF ν) - A μ x)) =
      (N : ℝ)⁻¹ * ∑ a, ∑ b, curlF (Aab a b) := by
    simp only [hs2_entries, curlF, Matrix.sub_apply, Finset.mul_sum]
    rw [swap5]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun x _ =>
      Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => ?_
    ring
  have hQ : ∑ y ∈ detB S.toDomSeq, ∑ μ, hs2 (Qt S A j y μ) =
      (N : ℝ)⁻¹ * ∑ a, ∑ b, ∑ y ∈ detB S.toDomSeq, ∑ μ, ‖QtS (Aab a b) j y μ‖ ^ 2 := by
    simp only [hs2_entries, Qt_entry, Finset.mul_sum]
    conv_lhs => arg 2; ext y; rw [Finset.sum_comm]
    conv_lhs => rw [Finset.sum_comm]
    conv_lhs => arg 2; ext a; arg 2; ext y; rw [Finset.sum_comm]
    conv_lhs => arg 2; ext a; rw [Finset.sum_comm]
  have hab : ∀ a b, ∑ x, ‖ps (N := N) S Set.univ (dsF (Aab a b)) x‖ ^ 2 ≤
      SFOneLayer.Col * (curlF (Aab a b) + ((S.L ^ j : ℕ) : ℝ) ^ 2 *
        ∑ y ∈ detB S.toDomSeq, ∑ μ, ‖QtS (Aab a b) j y μ‖ ^ 2) := fun a b => one_layer_fine hj hsc hb (Aab a b)
  rw [hL, hC, hQ]
  calc (N : ℝ)⁻¹ * ∑ a, ∑ b, ∑ x, ‖ps (N := N) S Set.univ (dsF (Aab a b)) x‖ ^ 2
      ≤ (N : ℝ)⁻¹ * ∑ a, ∑ b, SFOneLayer.Col * (curlF (Aab a b) + ((S.L ^ j : ℕ) : ℝ) ^ 2 *
          ∑ y ∈ detB S.toDomSeq, ∑ μ, ‖QtS (Aab a b) j y μ‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => hab a b) hNinv
    _ = _ := by
        simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum]
        ring

/-- **`T̂` is invertible at the trivial configuration**: it is coercive (`coercive_kerT`), hence injective, and the space
has finite dimension. -/
theorem hb_triv [NeZero N] (ΩD : Set (Site NF)) :
    Function.Bijective (kerLin (kerT (N := N) S (Subtype.val : BD S ΩD → Site NF) (X0 S) (W1 S) ΩD)) := by
  have hinj : Function.Injective (kerLin (kerT (N := N) S (Subtype.val : BD S ΩD → Site NF) (X0 S) (W1 S) ΩD)) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro μ hμ
    have hc := coercive_kerT S ΩD μ
    have h0 : kerApply (kerT S (Subtype.val : BD S ΩD → Site NF) (X0 S) (W1 S) ΩD) μ = 0 := hμ
    rw [h0, inner_zero_right, map_zero] at hc
    have hpos : (0 : ℝ) < ((9 / 32) ^ 4 / (864 + 4 * N)) ^ 2 := by positivity
    have : ‖μ‖ ^ 2 ≤ 0 := by nlinarith [sq_nonneg ‖μ‖]
    exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 (le_antisymm this (sq_nonneg _)))
  exact ⟨hinj, LinearMap.injective_iff_surjective.1 hinj⟩

/-- **`lem:sf-one-layer`** for the sequence with the single layer `j` on the lattice of `S` (fine lattice, `a₀ = 1`,
`a_j = L^j`, torus as the Dirichlet domain, trivial configuration, `M_N(ℂ)`-valued `1`-forms):
`‖P∂^*A‖² ≤ C_ol(‖∂A‖² + a_j²Σ_{y,μ}|(QA)(y, μ)|²)`. -/
theorem sf_one_layer [NeZero N] {j : ℕ} (hj : j ≤ S.k) (A : Fin 4 → Site NF → Mat) :
    ∑ x, hs2 (Pop (oneLayer S j hj) (X0 (oneLayer S j hj)) (W1 (oneLayer S j hj)) Set.univ
        (Ds1L a1 (cfgX (X0 (oneLayer S j hj))) A) x) ≤
      SFOneLayer.Col * (∑ x, 1 / 2 * ∑ μ, ∑ ν, hs2 ((A ν (x + unit NF μ) - A ν x) - (A μ (x + unit NF ν) - A μ x)) +
        ((S.L ^ j : ℕ) : ℝ) ^ 2 * ∑ y ∈ detB (oneLayer S j hj).toDomSeq, ∑ μ, hs2 (Qt (oneLayer S j hj) A j y μ)) :=
  one_layer_mat (S := oneLayer S j hj) hj (oneLayer_sc S hj) (hb_triv (S := oneLayer S j hj) Set.univ) A

end SFBounds
end CoreLean

end
