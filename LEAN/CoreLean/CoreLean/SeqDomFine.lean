/-
The bridge between the sequences of domains on the torus (`SeqDom`, `SequencesTorus.lean`) and the model
`Blocks.DomSeq` on the fine lattice, in which `lem:sf-coercivity` and `lem:sf-decay` of BALABAN_CORE.tex
(`4252790331fd`) are proved; with the two facts on the weighted distance of the proof of `lem:sf-decay`.

* `toDomSeq S`: the fine lattice `(ℤ/N₀)⁴`, `N₀ = 2L^{m_𝕋 + k}`, with the domains `Ω'_j = {x | xη ∈ Ω_j}` and
  `RM = RL^{m_M}`; `mem_iff_cen`: `Ω_j` is a union of cells of scale `j` on the fine points (from `Ω_eq_cells` and
  the uniqueness of the cell of a fine point); `sep`: `eq:separation` in the units `η = a₀`.
* `sc_eq`: the scale of a fine point in `toDomSeq S` is the scale `j(xη)` of `def:distance`.
* `wdist_block_le` (the second fact): for `y ∈ 𝐁` and `x ∈ Δ(y)`, `d(y, x) ≤ 2`.
* `wdist_unit_le` (the first fact): for neighbouring sites `x`, `x + e_μ`, `d(x, x + e_μ) ≤ a₀/a_{j_-} = L^{-j_-}`,
  `j_- = min{j(x), j(x + e_μ)}`: the straight segment lies in the cells of scale `j_-` of its ends, which lie in
  `Ω_{j_-}`, so that the weight is at most `a_{j_-}⁻¹` along it.
* `sc_sub_le`: the scales of neighbouring sites differ by at most one once `RM ≥ 1` (from `eq:separation`).
-/
import CoreLean.SequenceAverages
import CoreLean.SmallFieldBlocks
import CoreLean.LayerBonds

open Set MeasureTheory

noncomputable section

namespace CoreLean
namespace Lattices
namespace SeqDom

open Blocks SmallFieldBlocks

variable (S : SeqDom)

/-- The point `xη` of the torus of a fine point. -/
abbrev ef (x : Site (SequenceAverages.N0 S)) : Tor (ellT S.L S.mT) :=
  emb (N := SequenceAverages.N0 S) S.L S.k S.mT x

lemma ef_mem_TL0 (x : Site (SequenceAverages.N0 S)) : S.ef x ∈ S.TL 0 := by
  rw [TL, ← range_emb (N := SequenceAverages.N0 S) S.Lpos (SequenceAverages.N0_eq S)]
  exact ⟨x, rfl⟩

lemma ef_mem_TL_of {j : ℕ} {y : Site (SequenceAverages.N0 S)} (hy : Blocks.InLat S.L j y) : S.ef y ∈ S.TL j :=
  (inLat_iff S.Lpos (SequenceAverages.N0_eq S) y).1 hy

lemma ef_cen_mem_TL (j : ℕ) (x : Site (SequenceAverages.N0 S)) : S.ef (cen S.L j x) ∈ S.TL j :=
  S.ef_mem_TL_of fun ν => cen1_isMul (L := S.L) j (x ν)

lemma ef_mem_Δ_cen (j : ℕ) (x : Site (SequenceAverages.N0 S)) :
    S.ef x ∈ Δ S.L S.k S.mT j (S.ef (cen S.L j x)) :=
  emb_mem_Δ_cen S.L_odd (SequenceAverages.N0_eq S) j x

/-- **`Ω_j` is a union of cells of scale `j` on the fine points.** -/
theorem mem_iff_cen {j : ℕ} (hj : j ≤ S.k) (x : Site (SequenceAverages.N0 S)) :
    S.ef x ∈ S.Ω j ↔ S.ef (cen S.L j x) ∈ S.Ω j := by
  constructor
  · intro h
    rw [S.Ω_eq_cells hj] at h
    obtain ⟨y, ⟨hyT, hyΩ⟩, hxy⟩ := mem_iUnion₂.1 h
    obtain ⟨y0, -, hu⟩ := S.unique_cell hj (S.ef_mem_TL0 x)
    have e : S.ef (cen S.L j x) = y :=
      (hu _ ⟨S.ef_cen_mem_TL j x, S.ef_mem_Δ_cen j x⟩).trans (hu y ⟨hyT, hxy⟩).symm
    rwa [e]
  · intro h
    rw [S.Ω_eq_cells hj]
    exact mem_iUnion₂.2 ⟨_, ⟨S.ef_cen_mem_TL j x, h⟩, S.ef_mem_Δ_cen j x⟩

/-- The cell of a point of `T^{(j)} ∩ Ω_j` lies in `Ω_j`. -/
lemma Δ_subset_Ω {j : ℕ} (hj : j ≤ S.k) {y : Tor (ellT S.L S.mT)} (hyT : y ∈ S.TL j) (hyΩ : y ∈ S.Ω j) :
    Δ S.L S.k S.mT j y ⊆ S.Ω j := by
  rw [S.Ω_eq_cells hj]
  exact subset_biUnion_of_mem (u := fun y => Δ S.L S.k S.mT j y) ⟨hyT, hyΩ⟩

/-- **The sequence of domains on the fine lattice.** -/
def toDomSeq : DomSeq (SequenceAverages.N0 S) where
  L := S.L
  L_odd := S.L_odd
  three_le_L := S.three_le_L
  k := S.k
  mT := S.mT
  one_le_mT := S.one_le_mT
  N_eq := SequenceAverages.N0_eq S
  Ω j := {x | S.ef x ∈ S.Ω j}
  Ω_zero := by ext x; simp [S.Ω_zero]
  Ω_succ j _ hx := S.Ω_succ j hx
  Ω_top := by ext x; simp [S.Ω_top (S.k + 1) (Nat.lt_succ_self _)]
  cells j hj x := S.mem_iff_cen hj x
  RM := ((S.R * S.L ^ S.mM : ℕ) : ℝ)
  sep j hj1 hjk x hx x' hx' := by
    have h := S.sep j hj1 hjk ⟨_, hx⟩ ⟨_, hx'⟩
    have h2 := setDist_le (A := (S.Ω j)ᶜ) (B := S.Ω (j + 1)) hx hx'
    rw [dist_eq_norm, norm_emb_sub S.Lpos (SequenceAverages.N0_eq S)] at h2
    have he := eta_pos (k := S.k) S.Lpos
    have h3 : ((S.R * S.L ^ S.mM : ℕ) : ℝ) * (S.L : ℝ) ^ j * eta S.L S.k <
        (dinf x x' : ℝ) * eta S.L S.k := by
      have := h.trans_le h2
      simpa only [sp, mul_assoc] using this
    exact lt_of_mul_lt_mul_right h3 he.le

@[simp] lemma toDomSeq_L : (S.toDomSeq).L = S.L := rfl
@[simp] lemma toDomSeq_k : (S.toDomSeq).k = S.k := rfl
@[simp] lemma toDomSeq_RM : (S.toDomSeq).RM = ((S.R * S.L ^ S.mM : ℕ) : ℝ) := rfl

lemma mem_toDomSeq_Ω {j : ℕ} {x : Site (SequenceAverages.N0 S)} : x ∈ (S.toDomSeq).Ω j ↔ S.ef x ∈ S.Ω j :=
  Iff.rfl

lemma ef_mem_sc (x : Site (SequenceAverages.N0 S)) : S.ef x ∈ S.Ω ((S.toDomSeq).sc x) :=
  (S.toDomSeq).mem_sc x

/-- The spacings of the continuum model are the spacings `a_j`. -/
lemma D_a (j : ℕ) : (S.toContSeq).D.a j = sp S.L S.k j := (S.sp_eq_aa j).symm

lemma D_Ω (j : ℕ) : (S.toContSeq).D.Ω j = S.Ω j := S.toContSeq_Ω j

/-- **The scale of a fine point is the scale `j(xη)` of `def:distance`.** -/
theorem sc_eq (x : Site (SequenceAverages.N0 S)) : (S.toDomSeq).sc x = (S.toContSeq).D.scale (S.ef x) := by
  symm
  refine DomainData.scale_eq _ ((S.toDomSeq).sc_le x) ?_ ?_
  · rw [D_Ω]; exact (S.toDomSeq).mem_sc x
  · rw [D_Ω]; exact (S.toDomSeq).not_mem_sc_succ x

/-! ### The second fact: the blocks -/

/-- **The second fact on the distance**: for `y ∈ 𝐁` and `x ∈ Δ(y)`, `d(y, x) ≤ 2`. -/
theorem wdist_block_le {y x : Site (SequenceAverages.N0 S)} (hy : y ∈ detB S.toDomSeq)
    (hx : x ∈ Blk S.toDomSeq ((S.toDomSeq).sc y) y) :
    wdist (S.toContSeq).D (S.ef y) (S.ef x) ≤ ENNReal.ofReal 2 := by
  obtain ⟨x0, -, rfl⟩ := Finset.mem_image.1 hy
  set i := (S.toDomSeq).sc (bc S.toDomSeq x0)
  have hlat : S.ef (bc S.toDomSeq x0) ∈ S.TL i := S.ef_mem_TL_of (inLat_bc (S := S.toDomSeq) x0)
  have hcen : cen S.L i x = bc S.toDomSeq x0 := (Finset.mem_filter.1 hx).2
  refine (S.toContSeq).wdist_cell_le (i := i) ((S.toDomSeq).sc_le _) ?_ ?_ ?_ ?_
  · intro ν
    obtain ⟨r, hr⟩ := hlat ν
    exact ⟨r, by rw [hr]; congr 2⟩
  · rw [S.toContSeq_Ω]; exact S.ef_mem_sc _
  · rw [S.toContSeq_Ω]; exact (S.toDomSeq).not_mem_sc_succ _
  · have := S.ef_mem_Δ_cen i x
    rw [hcen] at this
    rw [show S.toContSeq.a i = sp S.L S.k i from (S.sp_eq_aa i).symm,
      cell_eq_summation]
    exact this

/-! ### The first fact: neighbouring sites -/

/-- The lift of a fine point, `(x_ν η)_ν`. -/
def lift (x : Site (SequenceAverages.N0 S)) : Fin 4 → ℝ := fun ν => ((x ν).val : ℝ) * eta S.L S.k

lemma projT_lift (x : Site (SequenceAverages.N0 S)) : projT (ellT S.L S.mT) (S.lift x) = S.ef x := rfl

/-- `π(x̃ + ηe_μ) = (x + e_μ)η`. -/
lemma projT_lift_add (x : Site (SequenceAverages.N0 S)) (μ : Fin 4) :
    projT (ellT S.L S.mT) (S.lift x + Pi.single μ (eta S.L S.k)) = S.ef (x + unit _ μ) := by
  funext ν
  simp only [projT, lift, Pi.add_apply, emb, unit]
  by_cases h : ν = μ
  · subst h
    simp only [Pi.single_eq_same]
    rw [← sub_eq_zero, ← AddCircle.coe_sub]
    have e : ((x ν).val : ℝ) * eta S.L S.k + eta S.L S.k - ((x ν + 1).val : ℝ) * eta S.L S.k =
        ((((x ν).val : ℤ) + 1 - (x ν + 1).val : ℤ) : ℝ) * eta S.L S.k := by push_cast; ring
    rw [e, coe_mul_eq_zero_iff (eta_pos S.Lpos) (ellT_eq_N S.Lpos (SequenceAverages.N0_eq S)),
      ← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    simp
  · simp [Pi.single_eq_of_ne h]

/-- A point within `η/2` of a fine point `x'` in each coordinate lies in `Ω_i` for `i ≤ j(x')`. -/
lemma near_mem_Ω {i : ℕ} {x' : Site (SequenceAverages.N0 S)} (hi : i ≤ (S.toDomSeq).sc x') (s : Fin 4 → ℝ)
    (hs : ∀ ν, |s ν| ≤ eta S.L S.k / 2) :
    (fun ν => S.ef x' ν + ((s ν : ℝ) : AddCircle (ellT S.L S.mT))) ∈ S.Ω i := by
  have hik : i ≤ S.k := hi.trans ((S.toDomSeq).sc_le x')
  have hx'Ω : S.ef x' ∈ S.Ω i := (S.toDomSeq).Ω_anti hi (S.ef_mem_sc x')
  have hcΩ := (S.mem_iff_cen hik x').1 hx'Ω
  refine S.Δ_subset_Ω hik (S.ef_cen_mem_TL i x') hcΩ ?_
  rw [Δ, mem_cell]
  have he := eta_pos (k := S.k) S.Lpos
  refine (pi_norm_le_iff_of_nonneg (by unfold sp; positivity)).2 fun ν => ?_
  have h1 : ‖S.ef x' ν - S.ef (cen S.L i x') ν‖ ≤ half S.L i * eta S.L S.k := by
    show ‖((((x' ν).val : ℝ) * eta S.L S.k : ℝ) : AddCircle (ellT S.L S.mT)) -
      (((((cen S.L i x') ν).val : ℝ) * eta S.L S.k : ℝ) : AddCircle (ellT S.L S.mT))‖ ≤ _
    rw [norm_emb_coord S.Lpos (SequenceAverages.N0_eq S)]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast cd_sub_cen1_le S.L_odd i (x' ν)) he.le
  have h2 : (2 * half S.L i + 1 : ℝ) = (S.L : ℝ) ^ i := by exact_mod_cast two_half_add_one S.L_odd i
  have e : (S.ef x' ν + ((s ν : ℝ) : AddCircle (ellT S.L S.mT))) - S.ef (cen S.L i x') ν =
      (S.ef x' ν - S.ef (cen S.L i x') ν) + ((s ν : ℝ) : AddCircle (ellT S.L S.mT)) := by abel
  show ‖(S.ef x' ν + ((s ν : ℝ) : AddCircle (ellT S.L S.mT))) - S.ef (cen S.L i x') ν‖ ≤ sp S.L S.k i / 2
  rw [e]
  refine (norm_add_le _ _).trans ?_
  have h3 := norm_coe_le (p := ellT S.L S.mT) (s ν)
  have h4 := hs ν
  unfold sp
  nlinarith

/-- **The first fact on the distance**: `d(x, x + e_μ) ≤ a₀/a_{j_-} = L^{-j_-}`. -/
theorem wdist_unit_le (x : Site (SequenceAverages.N0 S)) (μ : Fin 4) :
    wdist (S.toContSeq).D (S.ef x) (S.ef (x + unit _ μ)) ≤
      ENNReal.ofReal (((S.L : ℝ) ^ min ((S.toDomSeq).sc x) ((S.toDomSeq).sc (x + unit _ μ)))⁻¹) := by
  set i := min ((S.toDomSeq).sc x) ((S.toDomSeq).sc (x + unit _ μ))
  set e := eta S.L S.k
  have he : 0 < e := eta_pos S.Lpos
  set v : Fin 4 → ℝ := Pi.single μ e
  set xh := S.lift x
  set γ : ℝ → (Fin 4 → ℝ) := fun t => xh + t • v
  have hlip : LipschitzWith ‖v‖₊ γ :=
    LipschitzWith.of_dist_le_mul fun s t => by
      rw [dist_eq_norm, add_sub_add_left_eq_sub, ← sub_smul, norm_smul, Real.dist_eq,
        Real.norm_eq_abs, mul_comm]
      simp
  let P : TPath (ellT S.L S.mT) (S.ef x) (S.ef (x + unit _ μ)) :=
    ⟨1, zero_le_one, γ, _, hlip, by simp [γ, xh, projT_lift], by simpa [γ, xh, v] using S.projT_lift_add x μ⟩
  refine (iInf_le _ P).trans ?_
  have hderiv : ∀ (ν : Fin 4) (t : ℝ), deriv (fun s : ℝ => γ s ν) t = v ν := fun ν t => by
    have h := ((hasDerivAt_id t).mul_const (v ν)).const_add (xh ν)
    simp only [id, one_mul] at h
    simp only [γ, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact h.deriv
  have hsum : ∑ ν, |v ν| = e := by
    rw [Finset.sum_eq_single μ (fun b _ hb => by rw [show v b = 0 from Pi.single_eq_of_ne hb _, abs_zero])
      (by simp), show v μ = e from Pi.single_eq_same _ _, abs_of_pos he]
  -- the segment lies in `Ω_i`
  have hmem : ∀ t ∈ Icc (0 : ℝ) 1, projT (ellT S.L S.mT) (γ t) ∈ S.Ω i := by
    intro t ht
    rcases le_total t (1 / 2) with h | h
    · have := S.near_mem_Ω (x' := x) (i := i) (min_le_left _ _) (t • v) fun ν => by
        simp only [v, Pi.smul_apply, smul_eq_mul]
        by_cases hν : ν = μ
        · subst hν; rw [Pi.single_eq_same, abs_mul, abs_of_nonneg ht.1, abs_of_pos he]; nlinarith
        · rw [Pi.single_eq_of_ne hν]; simp; positivity
      convert this using 1
      funext ν
      simp only [projT, γ, Pi.add_apply]
      rw [AddCircle.coe_add]
      rfl
    · have := S.near_mem_Ω (x' := x + unit _ μ) (i := i) (min_le_right _ _) (-((1 - t) • v)) fun ν => by
        simp only [v, Pi.smul_apply, smul_eq_mul, Pi.neg_apply, abs_neg]
        by_cases hν : ν = μ
        · subst hν; rw [Pi.single_eq_same, abs_mul, abs_of_nonneg (by linarith [ht.2]), abs_of_pos he]
          nlinarith
        · rw [Pi.single_eq_of_ne hν]; simp; positivity
      convert this using 1
      funext ν
      rw [← S.projT_lift_add x μ]
      simp only [projT, γ, xh, Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, v]
      rw [← AddCircle.coe_add]
      congr 1
      ring
  have hbound : ∀ t ∈ Icc (0 : ℝ) 1, wIntegrand (S.toContSeq).D γ t ≤
      ENNReal.ofReal (((S.L : ℝ) ^ i)⁻¹) := by
    intro t ht
    have hsc : i ≤ (S.toContSeq).D.scale (projT (ellT S.L S.mT) (γ t)) := by
      classical
      have hik : i ≤ S.k := (min_le_left _ _).trans ((S.toDomSeq).sc_le x)
      unfold DomainData.scale
      exact Nat.le_findGreatest hik (by rw [D_Ω]; exact hmem t ht)
    have hw : (S.toContSeq).D.weight (projT (ellT S.L S.mT) (γ t)) ≤ (sp S.L S.k i)⁻¹ := by
      unfold DomainData.weight
      rw [← D_a]
      exact inv_anti₀ ((S.toContSeq).D.a_pos' i) ((S.toContSeq).D.a_mono _ _ hsc)
    unfold wIntegrand
    simp only [hderiv]
    rw [show (∑ ν, ‖v ν‖ₑ) = ENNReal.ofReal (∑ ν, |v ν|) by
      rw [ENNReal.ofReal_sum_of_nonneg (fun ν _ => abs_nonneg _)]
      refine Finset.sum_congr rfl fun ν _ => ?_
      rw [← Real.norm_eq_abs, ofReal_norm], hsum, ← ENNReal.ofReal_mul (by
        have := (S.toContSeq).D.one_le_weight (projT (ellT S.L S.mT) (γ t)); linarith)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hsp : (sp S.L S.k i)⁻¹ * e = ((S.L : ℝ) ^ i)⁻¹ := by
      simp only [sp, e]; rw [mul_inv, mul_assoc, inv_mul_cancel₀ he.ne', mul_one]
    rw [← hsp]
    exact mul_le_mul_of_nonneg_right hw he.le
  calc wlen (S.toContSeq).D P.γ 0 P.T
      ≤ ∫⁻ _t in Icc (0 : ℝ) 1, ENNReal.ofReal (((S.L : ℝ) ^ i)⁻¹) :=
        setLIntegral_mono measurable_const hbound
    _ = ENNReal.ofReal (((S.L : ℝ) ^ i)⁻¹) := by simp

/-- **The scales of neighbouring sites differ by at most one** once `RM ≥ 1`. -/
theorem sc_sub_le (hRM : 1 ≤ S.R * S.L ^ S.mM) (x : Site (SequenceAverages.N0 S)) (μ : Fin 4) :
    (S.toDomSeq).sc x ≤ (S.toDomSeq).sc (x + unit _ μ) + 1 ∧
      (S.toDomSeq).sc (x + unit _ μ) ≤ (S.toDomSeq).sc x + 1 := by
  have hd : dinf x (x + unit _ μ) ≤ 1 := by
    refine Finset.sup_le fun ν _ => ?_
    simp only [unit]
    by_cases h : ν = μ
    · subst h
      have h1 := cd_intCast_le (N := SequenceAverages.N0 S) 1
      simp only [Int.cast_one, Int.natAbs_one] at h1
      simpa only [Pi.add_apply, Pi.single_eq_same, sub_add_cancel_left, cd_neg] using h1
    · simp [Pi.single_eq_of_ne h, cd_zero]
  have hL1 : (1 : ℝ) ≤ S.L := by exact_mod_cast (show 1 ≤ S.L by have := S.three_le_L; omega)
  have key : ∀ y y' : Site (SequenceAverages.N0 S), dinf y y' ≤ 1 →
      ¬ (S.toDomSeq).sc y + 2 ≤ (S.toDomSeq).sc y' := fun y y' hyy h => by
    have := (S.toDomSeq).far h
    have h1 : (1 : ℝ) ≤ ((S.R * S.L ^ S.mM : ℕ) : ℝ) * (S.L : ℝ) ^ ((S.toDomSeq).sc y' - 1) :=
      one_le_mul_of_one_le_of_one_le (by exact_mod_cast hRM) (one_le_pow₀ hL1)
    have h2 : (dinf y y' : ℝ) ≤ 1 := by exact_mod_cast hyy
    simp only [toDomSeq_RM, toDomSeq_L] at this
    linarith
  constructor
  · have := key (x + unit _ μ) x (by rw [dinf_comm]; exact hd); omega
  · have := key x (x + unit _ μ) hd; omega

/-- The first fact in the form of `lem:sf-decay`: `d(x, x + e_μ) ≤ L · L^{-j(x)}` and `≤ L · L^{-j(x + e_μ)}`. -/
theorem wdist_unit_le_sc (hRM : 1 ≤ S.R * S.L ^ S.mM) (x : Site (SequenceAverages.N0 S)) (μ : Fin 4) :
    (wdist (S.toContSeq).D (S.ef x) (S.ef (x + unit _ μ))).toReal ≤
        S.L * ((S.L : ℝ) ^ (S.toDomSeq).sc x)⁻¹ ∧
      (wdist (S.toContSeq).D (S.ef x) (S.ef (x + unit _ μ))).toReal ≤
        S.L * ((S.L : ℝ) ^ (S.toDomSeq).sc (x + unit _ μ))⁻¹ := by
  have h := S.wdist_unit_le x μ
  have hL1 : (1 : ℝ) ≤ S.L := by exact_mod_cast (show 1 ≤ S.L by have := S.three_le_L; omega)
  have hL0 : (0 : ℝ) < S.L := by linarith
  have ht : (wdist (S.toContSeq).D (S.ef x) (S.ef (x + unit _ μ))).toReal ≤
      ((S.L : ℝ) ^ min ((S.toDomSeq).sc x) ((S.toDomSeq).sc (x + unit _ μ)))⁻¹ :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) h
  obtain ⟨h1, h2⟩ := S.sc_sub_le hRM x μ
  have step : ∀ a b : ℕ, a ≤ b + 1 → ((S.L : ℝ) ^ min a b)⁻¹ ≤ S.L * ((S.L : ℝ) ^ a)⁻¹ := by
    intro a b hab
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), inv_mul_le_iff₀ (by positivity)]
    calc (S.L : ℝ) ^ a ≤ (S.L : ℝ) ^ (min a b + 1) := pow_le_pow_right₀ hL1 (by omega)
      _ = (S.L : ℝ) ^ min a b * S.L := pow_succ _ _
  refine ⟨ht.trans (step _ _ h1), ht.trans ?_⟩
  rw [min_comm]
  exact step _ _ h2

end SeqDom
end Lattices
end CoreLean

end
