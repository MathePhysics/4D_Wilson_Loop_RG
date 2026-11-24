/-
The geometry of `sec:small-field-operators` of BALABAN_CORE.tex (`4252790331fd`) on the fine lattice of a sequence of
domains (`SeqDom`, through `toDomSeq` of `SeqDomFine.lean`), in the units `a₀ = 1`, `a_j = Lʲ`, with the weighted
distance `d` of `def:distance` of the embedded points (`dF`).

* `mem_detB_iff`, `image_detB`, `sum_detB_ef`: the determining set `𝐁` of the fine model is the determining set of the
  continuum model (`SequencesTorus.lean`), so that sums over it are sums over `𝐁` of the torus; `summation_fine`:
  `eq:summation` over the fine `𝐁` (`lem:summation`).
* `sc_sub_le_dF`: `|j(x) - j(x')| ≤ 1 + d(x, x')/(RM)` (`lem:distance`(ii)); `scale_shift`: `eq:sf-scale-shift`,
  `(a_{j'}/a_j)^σ ≤ L⁴e^{δd/8}` for `|σ| ≤ 4` and `RM ≥ 32δ⁻¹ log L`.
* `wdist_seg_le`: a straight segment in `Ω_i` has the weighted length at most `a_i⁻¹` times its `ℓ¹`-length;
  `dF_le_near`: a site `z` within the `ℓ^∞`-distance `ca_{j(x)}` of `x`, `cL ≤ RM`, has `d(x, z) ≤ |x - z|₁/a_{j(x)-1}`
  (the segment runs in `Ω_{j(x)-1}`, by `eq:separation`); `sc_le_succ_of_near`: then `j(z) ≤ j(x) + 1`.
* `tilde_scale`, `tilde_dist` (the fact (b) of `prop:sf-bounds`): for `y' ∈ Γ_{j'}` the sites of `Δ̃(y')` have the
  scales `j' - 1`, `j'`, `j' + 1` and lie at a weighted distance of at most `4L` from `y'`.
-/
import CoreLean.SFDecaySeq
import CoreLean.GlobalBounds

open Set MeasureTheory

noncomputable section

namespace CoreLean
namespace Lattices
namespace SeqDom

open Blocks SmallFieldBlocks

variable (S : SeqDom)

local notation "NF" => SequenceAverages.N0 S
local notation "RMS" => ((S.R * S.L ^ S.mM : ℕ) : ℝ)

lemma dF_eq (x x' : Site NF) : S.dF x x' = (S.toContSeq).dd (S.ef x) (S.ef x') := rfl

lemma dF_nonneg (x x' : Site NF) : 0 ≤ S.dF x x' := ENNReal.toReal_nonneg

lemma dF_triangle (x y z : Site NF) : S.dF x z ≤ S.dF x y + S.dF y z := (S.toContSeq).dd_triangle _ _ _

lemma dF_self (x : Site NF) : S.dF x x = 0 := by simp [dF, wdist_self]

lemma RMS_pos : 0 < RMS := by
  have := S.one_le_R; have := S.Lpos; positivity

/-! ### The determining set -/

/-- `y ∈ 𝐁` iff `y ∈ T^{(j(y))}`. -/
lemma mem_detB_iff_inLat (y : Site NF) :
    y ∈ detB S.toDomSeq ↔ Blocks.InLat S.L ((S.toDomSeq).sc y) y := by
  constructor
  · intro hy
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 hy
    have := inLat_bc (S := S.toDomSeq) x
    rwa [sc_bc] at this ⊢
  · intro hy
    refine Finset.mem_image.2 ⟨y, Finset.mem_univ _, ?_⟩
    funext ν
    show cen1 S.L ((S.toDomSeq).sc y) (y ν) = y ν
    exact (eq_cen1 S.L_odd ((S.toDomSeq).dvd_N ((S.toDomSeq).sc_le y)) (hy ν)
      (by rw [sub_self, cd_zero]; exact Nat.zero_le _)).symm

/-- **The fine determining set is the determining set of the torus.** -/
theorem mem_detB_iff (y : Site NF) : y ∈ detB S.toDomSeq ↔ S.ef y ∈ (S.toContSeq).BF := by
  rw [mem_detB_iff_inLat, mem_BF, inLat_iff S.Lpos (SequenceAverages.N0_eq S)]
  constructor
  · intro h
    exact ⟨_, (S.toDomSeq).sc_le y, ⟨⟨S.ef_mem_sc y, h⟩, (S.toDomSeq).not_mem_sc_succ y⟩⟩
  · rintro ⟨j, -, ⟨⟨hΩ, hT⟩, hΩ1⟩⟩
    have hsc : (S.toDomSeq).sc y = j := by
      have h1 := ((S.toDomSeq).mem_iff y j).1 (S.mem_toDomSeq_Ω.2 hΩ)
      have h2 : ¬ j + 1 ≤ (S.toDomSeq).sc y := fun h =>
        hΩ1 (S.mem_toDomSeq_Ω.1 (((S.toDomSeq).mem_iff y _).2 h))
      omega
    rw [hsc]; exact hT

theorem image_detB : (detB S.toDomSeq).image S.ef = (S.toContSeq).BF := by
  ext z
  constructor
  · intro hz
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hz
    exact (S.mem_detB_iff y).1 hy
  · intro hz
    obtain ⟨j, -, hzΓ⟩ := S.mem_BF.1 hz
    have hsub := lat_subset (p := ellT S.L S.mT) (sp_sub (L := S.L) (k := S.k) j j le_rfl)
    rw [Nat.sub_self] at hsub
    have hz0 : z ∈ S.TL 0 := hsub hzΓ.1.2
    rw [TL, ← range_emb (N := NF) S.Lpos (SequenceAverages.N0_eq S)] at hz0
    obtain ⟨y, rfl⟩ := hz0
    exact Finset.mem_image.2 ⟨y, (S.mem_detB_iff y).2 hz, rfl⟩

theorem sum_detB_ef {M : Type*} [AddCommMonoid M] (F : Tor (ellT S.L S.mT) → M) :
    ∑ y ∈ detB S.toDomSeq, F (S.ef y) = ∑ z ∈ (S.toContSeq).BF, F z := by
  rw [← S.image_detB, Finset.sum_image fun x _ y _ h =>
    emb_injective (N := NF) S.Lpos (SequenceAverages.N0_eq S) h]

/-- **`eq:summation` over the fine determining set.** -/
theorem summation_fine {α δ : ℝ} (hα : 0 < α) (hδ : 0 < δ) (hRM : (S.toContSeq).r1 α δ ≤ RMS)
    {y : Site NF} (hy : y ∈ detB S.toDomSeq) :
    ∑ y' ∈ detB S.toDomSeq, Real.exp (-(α * δ * S.dF y y')) ≤ (S.toContSeq).c1 α δ := by
  show ∑ y' ∈ detB S.toDomSeq, Real.exp (-(α * δ * (S.toContSeq).dd (S.ef y) (S.ef y'))) ≤ _
  rw [S.sum_detB_ef (fun z => Real.exp (-(α * δ * (S.toContSeq).dd (S.ef y) z)))]
  exact (S.toContSeq).summation hα hδ hRM ((S.mem_detB_iff y).1 hy)

/-! ### Scales and the distance -/

/-- **`|j(x) - j(x')| ≤ 1 + d(x, x')/(RM)`** (`lem:distance`(ii)). -/
theorem sc_sub_le_dF (x x' : Site NF) :
    |((S.toDomSeq).sc x : ℝ) - (S.toDomSeq).sc x'| ≤ 1 + S.dF x x' / RMS := by
  have h := wdist_ge_layers (S.toContSeq).D (R := RMS) (M := 1) (S.toContSeq).sep
    (z := S.ef x) (z' := S.ef x') (j := (S.toDomSeq).sc x) (j' := (S.toDomSeq).sc x')
    (by rw [D_Ω]; exact S.ef_mem_sc x) (by rw [D_Ω]; exact (S.toDomSeq).not_mem_sc_succ x)
    (by rw [D_Ω]; exact S.ef_mem_sc x') (by rw [D_Ω]; exact (S.toDomSeq).not_mem_sc_succ x')
  rw [ENNReal.ofReal_le_iff_le_toReal (wdist_ne_top _ _ _)] at h
  have hpos := S.RMS_pos
  have h2 : |((S.toDomSeq).sc x : ℝ) - (S.toDomSeq).sc x'| - 1 ≤ S.dF x x' / RMS := by
    rw [le_div_iff₀ hpos]
    have := le_max_left (|((S.toDomSeq).sc x : ℝ) - (S.toDomSeq).sc x'| - 1) 0
    unfold dF
    nlinarith
  linarith

/-- **`eq:sf-scale-shift`**: `(a_{j(x')}/a_{j(x)})^σ ≤ L⁴e^{δd(x, x')/8}` for `|σ| ≤ 4` and `RM ≥ 32δ⁻¹ log L`. -/
theorem scale_shift {δ σ : ℝ} (hδ : 0 < δ) (hRM : 32 * Real.log S.L / δ ≤ RMS) (hσ : |σ| ≤ 4)
    (x x' : Site NF) :
    ((S.L : ℝ) ^ (S.toDomSeq).sc x') ^ σ ≤
      (S.L : ℝ) ^ (4 : ℝ) * Real.exp (δ / 8 * S.dF x x') * ((S.L : ℝ) ^ (S.toDomSeq).sc x) ^ σ := by
  have hL : (1 : ℝ) ≤ S.L := by exact_mod_cast (show 1 ≤ S.L by have := S.three_le_L; omega)
  have h1 := GlobalBounds.rpow_scale_le hL one_pos hσ ((S.toDomSeq).sc x) ((S.toDomSeq).sc x')
  simp only [mul_one] at h1
  have hRM' : 4 * Real.log S.L ≤ δ / 8 * RMS := by
    rw [div_le_iff₀ hδ] at hRM; nlinarith
  have h2 := GlobalBounds.pow_scale_le hL S.RMS_pos hRM' (S.dF_nonneg x x') (S.sc_sub_le_dF x x')
  exact h1.trans (mul_le_mul_of_nonneg_right h2 (by positivity))

/-- **A straight segment in `Ω_i`** has the weighted length at most `a_i⁻¹` times its `ℓ¹`-length. -/
theorem wdist_seg_le {p : ℝ} (D : DomainData p) (xh v : Fin 4 → ℝ) (i : ℕ)
    (hmem : ∀ t ∈ Icc (0 : ℝ) 1, projT p (xh + t • v) ∈ D.Ω i) :
    wdist D (projT p xh) (projT p (xh + v)) ≤ ENNReal.ofReal ((D.a i)⁻¹ * ∑ ν, |v ν|) := by
  have hik : i ≤ D.k := by
    by_contra h
    have := D.Ω_anti (by omega : D.k + 1 ≤ i) (hmem 0 ⟨le_rfl, zero_le_one⟩)
    rw [D.Ω_top] at this; exact this
  set γ : ℝ → (Fin 4 → ℝ) := fun t => xh + t • v
  have hlip : LipschitzWith ‖v‖₊ γ :=
    LipschitzWith.of_dist_le_mul fun s t => by
      rw [dist_eq_norm, add_sub_add_left_eq_sub, ← sub_smul, norm_smul, Real.dist_eq,
        Real.norm_eq_abs, mul_comm]
      simp
  let P : TPath p (projT p xh) (projT p (xh + v)) :=
    ⟨1, zero_le_one, γ, _, hlip, by simp [γ], by simp [γ]⟩
  refine (iInf_le _ P).trans ?_
  have hderiv : ∀ (ν : Fin 4) (t : ℝ), deriv (fun s : ℝ => γ s ν) t = v ν := fun ν t => by
    have h := ((hasDerivAt_id t).mul_const (v ν)).const_add (xh ν)
    simp only [id, one_mul] at h
    simp only [γ, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact h.deriv
  have hbound : ∀ t ∈ Icc (0 : ℝ) 1, wIntegrand D γ t ≤ ENNReal.ofReal ((D.a i)⁻¹ * ∑ ν, |v ν|) := by
    intro t ht
    have hsc : i ≤ D.scale (projT p (γ t)) := by
      classical
      unfold DomainData.scale
      exact Nat.le_findGreatest hik (hmem t ht)
    have hw : D.weight (projT p (γ t)) ≤ (D.a i)⁻¹ :=
      inv_anti₀ (D.a_pos' i) (D.a_mono _ _ hsc)
    unfold wIntegrand
    simp only [hderiv]
    rw [show (∑ ν, ‖v ν‖ₑ) = ENNReal.ofReal (∑ ν, |v ν|) by
      rw [ENNReal.ofReal_sum_of_nonneg (fun ν _ => abs_nonneg _)]
      refine Finset.sum_congr rfl fun ν _ => ?_
      rw [← Real.norm_eq_abs, ofReal_norm], ← ENNReal.ofReal_mul (by
        have := D.one_le_weight (projT p (γ t)); linarith)]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hw (Finset.sum_nonneg fun _ _ => abs_nonneg _))
  calc wlen D P.γ 0 P.T
      ≤ ∫⁻ _t in Icc (0 : ℝ) 1, ENNReal.ofReal ((D.a i)⁻¹ * ∑ ν, |v ν|) :=
        setLIntegral_mono measurable_const hbound
    _ = ENNReal.ofReal ((D.a i)⁻¹ * ∑ ν, |v ν|) := by simp

/-- The lift of the difference `z - x` with the representatives of least absolute value. -/
def dlift (x z : Site NF) : Fin 4 → ℝ := fun ν => (((z ν - x ν).valMinAbs : ℤ) : ℝ) * eta S.L S.k

lemma projT_lift_dlift (x z : Site NF) : projT (ellT S.L S.mT) (S.lift x + S.dlift x z) = S.ef z := by
  funext ν
  simp only [projT, lift, dlift, Pi.add_apply]
  rw [AddCircle.coe_add, ← emb_coord_sub S.Lpos (SequenceAverages.N0_eq S) (z ν) (x ν)]
  show _ = ((((z ν).val : ℝ) * eta S.L S.k : ℝ) : AddCircle (ellT S.L S.mT))
  abel

lemma abs_dlift (x z : Site NF) (ν : Fin 4) : |S.dlift x z ν| = cd (x ν - z ν) * eta S.L S.k := by
  have he := eta_pos (k := S.k) S.Lpos
  simp only [dlift, abs_mul, abs_of_pos he]
  rw [cd_sub_comm, Blocks.cd, Nat.cast_natAbs, Int.cast_abs]

lemma sum_abs_dlift (x z : Site NF) : ∑ ν, |S.dlift x z ν| = d1 x z * eta S.L S.k := by
  simp only [abs_dlift, d1, Nat.cast_sum, Finset.sum_mul]

lemma d1_le_four_dinf (x z : Site NF) : d1 x z ≤ 4 * dinf x z := by
  calc d1 x z = ∑ ν, cd (x ν - z ν) := rfl
    _ ≤ ∑ _ν : Fin 4, dinf x z := Finset.sum_le_sum fun ν _ => cd_le_dinf x z ν
    _ = 4 * dinf x z := by simp

/-- The points of the segment from `x` to `z` lie within `|x - z|_∞` of `x`. -/
lemma dist_seg_le (x z : Site NF) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    dist (projT (ellT S.L S.mT) (S.lift x + t • S.dlift x z)) (S.ef x) ≤ dinf x z * eta S.L S.k := by
  have he := eta_pos (k := S.k) S.Lpos
  rw [dist_eq_norm]
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun ν => ?_
  simp only [Pi.sub_apply, projT, lift, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [AddCircle.coe_add]
  show ‖(_ + _) - ((((x ν).val : ℝ) * eta S.L S.k : ℝ) : AddCircle (ellT S.L S.mT))‖ ≤ _
  rw [add_sub_cancel_left]
  refine (norm_coe_le _).trans ?_
  rw [abs_mul, abs_of_nonneg ht.1, abs_dlift]
  calc t * (cd (x ν - z ν) * eta S.L S.k) ≤ 1 * (cd (x ν - z ν) * eta S.L S.k) :=
        mul_le_mul_of_nonneg_right ht.2 (by positivity)
    _ ≤ dinf x z * eta S.L S.k := by
        rw [one_mul]; exact mul_le_mul_of_nonneg_right (by exact_mod_cast cd_le_dinf x z ν) he.le

/-- **A site near `x` is at a weighted distance of at most `|x - z|₁/a_{j(x)-1}`.** -/
theorem dF_le_near {c : ℝ} (hRM : c * S.L ≤ RMS) (x z : Site NF)
    (hxz : (dinf x z : ℝ) < c * (S.L : ℝ) ^ (S.toDomSeq).sc x) :
    S.dF x z ≤ d1 x z / (S.L : ℝ) ^ ((S.toDomSeq).sc x - 1) := by
  set j := (S.toDomSeq).sc x
  have he := eta_pos (k := S.k) S.Lpos
  have hmem : ∀ t ∈ Icc (0 : ℝ) 1,
      projT (ellT S.L S.mT) (S.lift x + t • S.dlift x z) ∈ (S.toContSeq).D.Ω (j - 1) := by
    intro t ht
    rw [D_Ω]
    refine S.layer_bonds_i hRM ((S.toDomSeq).sc_le x) (S.ef_mem_sc x) ?_
    calc dist (projT (ellT S.L S.mT) (S.lift x + t • S.dlift x z)) (S.ef x) ≤ dinf x z * eta S.L S.k :=
          S.dist_seg_le x z ht
      _ < c * (S.L : ℝ) ^ j * eta S.L S.k := mul_lt_mul_of_pos_right hxz he
      _ = c * sp S.L S.k j := by unfold sp; ring
  have h := wdist_seg_le (S.toContSeq).D (S.lift x) (S.dlift x z) (j - 1) hmem
  rw [projT_lift, projT_lift_dlift, sum_abs_dlift, D_a] at h
  have e : (sp S.L S.k (j - 1))⁻¹ * (d1 x z * eta S.L S.k) = d1 x z / (S.L : ℝ) ^ (j - 1) := by
    unfold sp; field_simp
  rw [e] at h
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) h

/-- **The scale of a site near `x` is at most `j(x) + 1`.** -/
theorem sc_le_succ_of_near (hRM1 : 1 ≤ S.R * S.L ^ S.mM) {x z : Site NF}
    (h : (dinf x z : ℝ) ≤ RMS * (S.L : ℝ) ^ (S.toDomSeq).sc x) :
    (S.toDomSeq).sc z ≤ (S.toDomSeq).sc x + 1 := by
  by_contra hc
  have hfar := (S.toDomSeq).far (x := x) (x' := z) (by omega)
  simp only [toDomSeq_RM, toDomSeq_L] at hfar
  have hL1 : (1 : ℝ) ≤ S.L := by exact_mod_cast (show 1 ≤ S.L by have := S.three_le_L; omega)
  have hp : (S.L : ℝ) ^ (S.toDomSeq).sc x ≤ (S.L : ℝ) ^ ((S.toDomSeq).sc z - 1) :=
    pow_le_pow_right₀ hL1 (by omega)
  have := mul_le_mul_of_nonneg_left hp S.RMS_pos.le
  linarith

/-- **The fact (b), the scales**: the sites of `Δ̃(y')` have the scales `j' - 1`, `j'`, `j' + 1`. -/
theorem tilde_scale (hRM : (S.L : ℝ) ≤ RMS) {y' x : Site NF}
    (hx : (dinf x y' : ℝ) < (S.L : ℝ) ^ (S.toDomSeq).sc y') :
    (S.toDomSeq).sc y' ≤ (S.toDomSeq).sc x + 1 ∧ (S.toDomSeq).sc x ≤ (S.toDomSeq).sc y' + 1 := by
  have hRM1 : 1 ≤ S.R * S.L ^ S.mM := by have := Nat.one_le_pow S.mM S.L S.Lpos; nlinarith [S.one_le_R]
  constructor
  · have hxΩ : S.ef x ∈ S.Ω ((S.toDomSeq).sc y' - 1) := by
      refine S.layer_bonds_i (c := 1) (by linarith) ((S.toDomSeq).sc_le y') (S.ef_mem_sc y') ?_
      rw [dist_eq_norm, norm_emb_sub S.Lpos (SequenceAverages.N0_eq S)]
      have he := eta_pos (k := S.k) S.Lpos
      unfold sp
      nlinarith
    have := ((S.toDomSeq).mem_iff x _).1 (S.mem_toDomSeq_Ω.2 hxΩ)
    omega
  · refine S.sc_le_succ_of_near hRM1 ?_
    rw [dinf_comm]
    have hL0 : (0 : ℝ) ≤ (S.L : ℝ) ^ (S.toDomSeq).sc y' := by positivity
    have h1 : (1 : ℝ) ≤ RMS := by exact_mod_cast hRM1
    nlinarith

/-- **The fact (b), the distance**: the sites of `Δ̃(y')` lie at a weighted distance of at most `4L` from `y'`. -/
theorem tilde_dist (hRM : (S.L : ℝ) ≤ RMS) {y' x : Site NF}
    (hx : (dinf x y' : ℝ) < (S.L : ℝ) ^ (S.toDomSeq).sc y') : S.dF y' x ≤ 4 * S.L := by
  have hx' : (dinf y' x : ℝ) < 1 * (S.L : ℝ) ^ (S.toDomSeq).sc y' := by rw [dinf_comm, one_mul]; exact hx
  refine (S.dF_le_near (c := 1) (by linarith) y' x hx').trans ?_
  set j := (S.toDomSeq).sc y'
  have hL1 : (1 : ℝ) ≤ S.L := by exact_mod_cast (show 1 ≤ S.L by have := S.three_le_L; omega)
  have hd1 : (d1 y' x : ℝ) ≤ 4 * dinf y' x := by exact_mod_cast d1_le_four_dinf S y' x
  have hpow : (S.L : ℝ) ^ j ≤ S.L * (S.L : ℝ) ^ (j - 1) := by
    rcases Nat.eq_zero_or_pos j with h0 | h0
    · rw [h0]; simpa using hL1
    · rw [← pow_succ', Nat.sub_add_cancel h0]
  rw [div_le_iff₀ (by positivity)]
  rw [dinf_comm] at hx
  nlinarith

end SeqDom
end Lattices
end CoreLean

end
