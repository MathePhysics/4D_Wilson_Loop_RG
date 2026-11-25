/-
`prop:sf-vector-lower` of BALABAN_CORE.tex (`95f07f48317e`), the step "The double commutators": the bound of the
error of the localisation of the constraint form `⟨A^*, Q^*QA⟩` by the partition of unity of `SFPartition.lean`.

* `box_dinf`: a site `x + te_μ` of the box of a bond `(y, μ)` of `T^{(j)}` lies within `2a_j` of both ends.
* `box_scale`: the sites of the box of a bond of the layer `Γ_j` have the scales `j - 1`, `j`, `j + 1`.
-/
import CoreLean.SFPartition

open Finset

noncomputable section

namespace CoreLean
section LocalDistance

open MeasureTheory
open scoped ENNReal NNReal

variable {p : ℝ}

/-- The restriction of a path to `[0, t]`. -/
def TPath.restr {z z' : Tor p} (P : TPath p z z') (t : ℝ) (ht : 0 ≤ t) : TPath p z (projT p (P.γ t)) where
  T := t
  T_nonneg := ht
  γ := P.γ
  K := P.K
  lip := P.lip
  start := P.start
  stop := rfl

/-- **A short path stays at the scales up to `j(z) + 1`**: if `ℓ(γ) < RM`, then `j(γ(t)) ≤ j(z) + 1` on `[0, T]`
(`lem:distance`(ii)). -/
lemma scale_le_of_wlen (D : DomainData p) {R M : ℝ}
    (hsep : ∀ i, 1 ≤ i → i < D.k → ∀ x ∉ D.Ω i, ∀ y ∈ D.Ω (i + 1), R * M * D.a i ≤ dist x y)
    (hRM : 0 ≤ R * M) {z z' : Tor p} (P : TPath p z z') (hP : wlen D P.γ 0 P.T < ENNReal.ofReal (R * M))
    {t : ℝ} (ht : t ∈ Set.Icc 0 P.T) : D.scale (projT p (P.γ t)) ≤ D.scale z + 1 := by
  by_contra hc
  push_neg at hc
  set w := projT p (P.γ t)
  have hw : wdist D z w ≤ wlen D P.γ 0 P.T :=
    (iInf_le _ (P.restr t ht.1)).trans (lintegral_mono_set (Set.Icc_subset_Icc le_rfl ht.2))
  have hl := wdist_ge_layers D hsep (D.mem_scale z).1 (D.mem_scale z).2 (D.mem_scale w).1 (D.mem_scale w).2
  have h1 : (1 : ℝ) ≤ max (|(D.scale z : ℝ) - D.scale w| - 1) 0 := by
    refine le_max_of_le_left ?_
    have : (D.scale z : ℝ) + 2 ≤ D.scale w := by exact_mod_cast hc
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    linarith
  have h2 : ENNReal.ofReal (R * M) ≤ ENNReal.ofReal (R * M * max (|(D.scale z : ℝ) - D.scale w| - 1) 0) :=
    ENNReal.ofReal_le_ofReal (le_mul_of_one_le_right hRM h1)
  exact absurd (h2.trans (hl.trans hw)) (not_le.2 hP)

/-- **The local comparison of the distances**: if `d(z, z') < RM`, then `a_{j(z)+1}⁻¹|z - z'|₁ ≤ d(z, z')`. -/
theorem wdist_ge_local (D : DomainData p) {R M : ℝ}
    (hsep : ∀ i, 1 ≤ i → i < D.k → ∀ x ∉ D.Ω i, ∀ y ∈ D.Ω (i + 1), R * M * D.a i ≤ dist x y)
    (hRM : 0 ≤ R * M) {z z' : Tor p} (hd : wdist D z z' < ENNReal.ofReal (R * M)) :
    ENNReal.ofReal ((D.a (D.scale z + 1))⁻¹ * dist1 z z') ≤ wdist D z z' := by
  set m := D.scale z + 1
  have hc : 0 ≤ (D.a m)⁻¹ := inv_nonneg.2 (D.a_pos' m).le
  -- every path of the length less than `RM`
  have key : ∀ P : TPath p z z', wlen D P.γ 0 P.T < ENNReal.ofReal (R * M) →
      ENNReal.ofReal ((D.a m)⁻¹ * dist1 z z') ≤ wlen D P.γ 0 P.T := by
    intro P hP
    have h1 := ofReal_sum_abs_sub_le P.lip P.T_nonneg
    have h2 : dist1 z z' ≤ ∑ ν, |P.γ P.T ν - P.γ 0 ν| := by
      calc dist1 z z' = dist1 (projT p (P.γ 0)) (projT p (P.γ P.T)) := by rw [P.start, P.stop]
        _ ≤ ∑ ν, |P.γ 0 ν - P.γ P.T ν| := dist1_projT_le _ _
        _ = ∑ ν, |P.γ P.T ν - P.γ 0 ν| := Finset.sum_congr rfl fun ν _ => abs_sub_comm _ _
    rw [ENNReal.ofReal_mul hc]
    refine (mul_le_mul' le_rfl ((ENNReal.ofReal_le_ofReal h2).trans h1)).trans ?_
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_mono' measurableSet_Icc fun t ht => ?_
    unfold wIntegrand
    refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
    unfold DomainData.weight
    exact inv_anti₀ (D.a_pos' _) (D.a_mono _ _ (scale_le_of_wlen D hsep hRM P hP ht))
  by_contra hne
  push_neg at hne
  obtain ⟨P, hP⟩ := iInf_lt_iff.1 (lt_min hne hd)
  exact absurd (key P (hP.trans_le (min_le_right _ _))) (not_le.2 (hP.trans_le (min_le_left _ _)))

end LocalDistance

namespace Lattices
namespace SeqDom

variable (S : SeqDom)

local notation "NF" => SequenceAverages.N0 S
local notation "RMS" => ((S.R * S.L ^ S.mM : ℕ) : ℝ)

lemma scale_ef (x : Site NF) : (S.toContSeq).D.scale (S.ef x) = (S.toDomSeq).sc x :=
  (S.toContSeq).D.scale_eq (by have := (S.toDomSeq).sc_le x; exact this) (by rw [D_Ω]; exact S.ef_mem_sc x)
    (by rw [D_Ω]; exact (S.toDomSeq).not_mem_sc_succ x)

/-- **The local comparison on the fine lattice**: if `d(x, x') < RM`, then `|x - x'|_∞ ≤ L^{j(x)+1}d(x, x')`. -/
theorem dinf_le_dF (x x' : Site NF) (hd : S.dF x x' < RMS) :
    (Blocks.dinf x x' : ℝ) ≤ (S.L : ℝ) ^ ((S.toDomSeq).sc x + 1) * S.dF x x' := by
  have hL : 0 < S.L := S.Lpos
  have hpos := S.RMS_pos
  have hne := wdist_ne_top (S.toContSeq).D (S.ef x) (S.ef x')
  have hd' : wdist (S.toContSeq).D (S.ef x) (S.ef x') < ENNReal.ofReal (RMS * 1) := by
    rw [mul_one, ← ENNReal.ofReal_toReal hne]
    exact (ENNReal.ofReal_lt_ofReal_iff hpos).2 hd
  have h := wdist_ge_local (S.toContSeq).D (R := RMS) (M := 1) (S.toContSeq).sep (by rw [mul_one]; exact hpos.le) hd'
  rw [scale_ef] at h
  have hle : (sp S.L S.k ((S.toDomSeq).sc x + 1))⁻¹ * dist1 (S.ef x) (S.ef x') ≤ S.dF x x' := by
    unfold dF
    rw [← D_a, ← ENNReal.ofReal_le_iff_le_toReal hne]
    exact h
  have hdd : ‖S.ef x - S.ef x'‖ = Blocks.dinf x x' * eta S.L S.k :=
    norm_emb_sub hL (SequenceAverages.N0_eq S) x x'
  have h3 := norm_le_dist1 S (S.ef x) (S.ef x')
  rw [hdd] at h3
  have he : 0 < eta S.L S.k := eta_pos hL
  have hsp : sp S.L S.k ((S.toDomSeq).sc x + 1) = (S.L : ℝ) ^ ((S.toDomSeq).sc x + 1) * eta S.L S.k := rfl
  have hLp : (0 : ℝ) < (S.L : ℝ) ^ ((S.toDomSeq).sc x + 1) := by positivity
  have h4 : (Blocks.dinf x x' : ℝ) / (S.L : ℝ) ^ ((S.toDomSeq).sc x + 1) ≤ S.dF x x' :=
    calc (Blocks.dinf x x' : ℝ) / (S.L : ℝ) ^ ((S.toDomSeq).sc x + 1) =
          (sp S.L S.k ((S.toDomSeq).sc x + 1))⁻¹ * (Blocks.dinf x x' * eta S.L S.k) := by
          rw [hsp]; field_simp
      _ ≤ (sp S.L S.k ((S.toDomSeq).sc x + 1))⁻¹ * dist1 (S.ef x) (S.ef x') :=
          mul_le_mul_of_nonneg_left h3 (inv_nonneg.2 (by rw [hsp]; positivity))
      _ ≤ S.dF x x' := hle
  rwa [div_le_iff₀ hLp, mul_comm] at h4

end SeqDom
end Lattices

namespace PartitionUnity

open Lattices SFBounds SFLocal Blocks SmallFieldBlocks

variable (S : Lattices.SeqDom) {N : ℕ}

local notation "NF" => SequenceAverages.N0 S
local notation "Mat" => Matrix (Fin N) (Fin N) ℂ

lemma half_le_pow (j : ℕ) : half S.L j ≤ S.L ^ j := by unfold half; omega

/-- **A site of the box of a bond lies within `2a_j` of both ends.** -/
lemma box_dinf {j : ℕ} {y x : Site NF} (hx : x ∈ Blk S.toDomSeq j y) (μ : Fin 4) {t s : ℕ} (ht : t ≤ S.L ^ j)
    (hs : s ≤ S.L ^ j) :
    dinf (x + ((t : ℕ) : ZMod NF) • CoreLean.unit NF μ) (y + ((s : ℕ) : ZMod NF) • CoreLean.unit NF μ) ≤
      2 * S.L ^ j := by
  unfold dinf
  refine Finset.sup_le fun ν _ => ?_
  have hc := SmallFieldBlocks.cd_le_of_mem (S := S.toDomSeq) hx ν
  have hh := half_le_pow S j
  change cd (x ν - y ν) ≤ half S.L j at hc
  by_cases h : ν = μ
  · subst h
    have e : (x + ((t : ℕ) : ZMod NF) • CoreLean.unit NF ν) ν - (y + ((s : ℕ) : ZMod NF) • CoreLean.unit NF ν) ν =
        (x ν - y ν) + (((t : ℤ) - s : ℤ) : ZMod NF) := by
      simp only [CoreLean.unit, Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
      push_cast; ring
    rw [e]
    refine (cd_add_le _ _).trans ?_
    have h2 := cd_intCast_le (N := NF) ((t : ℤ) - s)
    have h3 : ((t : ℤ) - s).natAbs ≤ S.L ^ j := by omega
    omega
  · have e : (x + ((t : ℕ) : ZMod NF) • CoreLean.unit NF μ) ν - (y + ((s : ℕ) : ZMod NF) • CoreLean.unit NF μ) ν =
        x ν - y ν := by
      simp only [CoreLean.unit, Pi.add_apply, Pi.smul_apply, Pi.single_eq_of_ne h, smul_eq_mul, mul_zero, add_zero]
    rw [e]; omega

/-- **The scales of the sites of the box of a bond of a layer**: for `(j, y, μ) ∈ QB` and `x ∈ B^j(y)`, `t < a_j`,
the scale of `x + te_μ` is `j - 1`, `j`, or `j + 1` (by the separation, `RM ≥ 2L`). -/
theorem box_scale (hRM : 2 * (S.L : ℝ) ≤ ((S.R * S.L ^ S.mM : ℕ) : ℝ)) {j : ℕ} {y : Site NF} {μ : Fin 4}
    (hq : (j, y, μ) ∈ QB S) {x : Site NF} (hx : x ∈ Blk S.toDomSeq j y) {t : ℕ} (ht : t < S.L ^ j) :
    (S.toDomSeq).sc (x + ((t : ℕ) : ZMod NF) • CoreLean.unit NF μ) ≤ j + 1 ∧
      j ≤ (S.toDomSeq).sc (x + ((t : ℕ) : ZMod NF) • CoreLean.unit NF μ) + 1 := by
  set p := x + ((t : ℕ) : ZMod NF) • CoreLean.unit NF μ
  simp only [QB, mem_filter, mem_product, mem_range, mem_univ, true_and] at hq
  obtain ⟨hjk, -, -, hend, hy1, hb1⟩ := hq
  have hL1 : (1 : ℝ) ≤ S.L := by exact_mod_cast S.Lpos
  have hpow : (0 : ℝ) < (S.L : ℝ) ^ j := by positivity
  have hd0 := box_dinf S hx μ ht.le (Nat.zero_le _)
  have hd1 := box_dinf S hx μ ht.le le_rfl
  simp only [Nat.cast_zero, zero_smul, add_zero] at hd0
  have hnext : S.bend j (S.ef y) μ = S.ef (ynext S j y μ) := by rw [ef_ynext]; rfl
  have hRMd : (S.toDomSeq).RM = ((S.R * S.L ^ S.mM : ℕ) : ℝ) := rfl
  have hLd : (S.toDomSeq).L = S.L := rfl
  constructor
  · by_contra hc
    push_neg at hc
    have hp2 : p ∈ (S.toDomSeq).Ω (j + 1 + 1) := ((S.toDomSeq).mem_iff p _).2 (by omega)
    have hk : (S.toDomSeq).sc p ≤ S.k := (S.toDomSeq).sc_le p
    have hsep := (S.toDomSeq).sep (j + 1) (by omega) (by change j + 1 < S.k; omega) y hy1 p hp2
    rw [hRMd, hLd, dinf_comm] at hsep
    have : ((dinf p y : ℕ) : ℝ) ≤ 2 * (S.L : ℝ) ^ j := by
      have h := Nat.cast_le (α := ℝ) |>.2 hd0; push_cast at h; exact h
    have : ((S.R * S.L ^ S.mM : ℕ) : ℝ) * (S.L : ℝ) ^ (j + 1) ≥ 2 * (S.L : ℝ) ^ j := by
      have h1 : 2 * (S.L : ℝ) * (S.L : ℝ) ^ j ≤ ((S.R * S.L ^ S.mM : ℕ) : ℝ) * (S.L : ℝ) ^ j :=
        mul_le_mul_of_nonneg_right hRM hpow.le
      have h2 : 2 * (S.L : ℝ) ^ j ≤ 2 * (S.L : ℝ) * (S.L : ℝ) ^ j := by nlinarith
      have h3 : ((S.R * S.L ^ S.mM : ℕ) : ℝ) * (S.L : ℝ) ^ j ≤ ((S.R * S.L ^ S.mM : ℕ) : ℝ) * (S.L : ℝ) ^ (j + 1) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL1 (by omega)) (Nat.cast_nonneg _)
      linarith
    linarith
  · by_contra hc
    push_neg at hc
    have hpn : p ∉ (S.toDomSeq).Ω (j - 1) := fun h => by
      have := ((S.toDomSeq).mem_iff p _).1 h; omega
    have hsep : ∀ e ∈ (S.toDomSeq).Ω (j - 1 + 1), dinf p e ≤ 2 * S.L ^ j → False := by
      intro e he hde
      have hs := (S.toDomSeq).sep (j - 1) (by omega) (by change j - 1 < S.k; omega) p hpn e he
      rw [hRMd, hLd] at hs
      have : ((dinf p e : ℕ) : ℝ) ≤ 2 * (S.L : ℝ) ^ j := by
        have h := Nat.cast_le (α := ℝ) |>.2 hde; push_cast at h; exact h
      have hj : (S.L : ℝ) ^ j = S.L * (S.L : ℝ) ^ (j - 1) := by
        rw [← pow_succ']; congr 1; omega
      have h0 : (0 : ℝ) < (S.L : ℝ) ^ (j - 1) := by positivity
      have h1 : 2 * (S.L : ℝ) * (S.L : ℝ) ^ (j - 1) ≤ ((S.R * S.L ^ S.mM : ℕ) : ℝ) * (S.L : ℝ) ^ (j - 1) :=
        mul_le_mul_of_nonneg_right hRM h0.le
      rw [hj] at this
      linarith
    rw [show j - 1 + 1 = j by omega] at hsep
    rcases hend with he | he
    · exact hsep y he hd0
    · rw [hnext] at he
      exact hsep _ he hd1

/-- **The box of a bond of a layer lies in `Ω_{j-1}`**: for `(j, y, μ) ∈ QB`, `x ∈ B^j(y)` and `t ≤ a_j`, the scale
of `x + te_μ` is at least `j - 1` (the second half of `box_scale`, which uses only `box_dinf`). -/
theorem box_scale_low (hRM : 2 * (S.L : ℝ) ≤ ((S.R * S.L ^ S.mM : ℕ) : ℝ)) {j : ℕ} {y : Site NF} {μ : Fin 4}
    (hq : (j, y, μ) ∈ QB S) {x : Site NF} (hx : x ∈ Blk S.toDomSeq j y) {t : ℕ} (ht : t ≤ S.L ^ j) :
    j ≤ (S.toDomSeq).sc (x + ((t : ℕ) : ZMod NF) • CoreLean.unit NF μ) + 1 := by
  set p := x + ((t : ℕ) : ZMod NF) • CoreLean.unit NF μ
  simp only [QB, mem_filter, mem_product, mem_range, mem_univ, true_and] at hq
  obtain ⟨hjk, -, -, hend, hy1, hb1⟩ := hq
  have hL1 : (1 : ℝ) ≤ S.L := by exact_mod_cast S.Lpos
  have hd0 := box_dinf S hx μ ht (Nat.zero_le _)
  have hd1 := box_dinf S hx μ ht le_rfl
  simp only [Nat.cast_zero, zero_smul, add_zero] at hd0
  have hnext : S.bend j (S.ef y) μ = S.ef (ynext S j y μ) := by rw [ef_ynext]; rfl
  have hRMd : (S.toDomSeq).RM = ((S.R * S.L ^ S.mM : ℕ) : ℝ) := rfl
  have hLd : (S.toDomSeq).L = S.L := rfl
  by_contra hc
  push_neg at hc
  have hpn : p ∉ (S.toDomSeq).Ω (j - 1) := fun h => by
    have := ((S.toDomSeq).mem_iff p _).1 h; omega
  have hsep : ∀ e ∈ (S.toDomSeq).Ω (j - 1 + 1), dinf p e ≤ 2 * S.L ^ j → False := by
    intro e he hde
    have hs := (S.toDomSeq).sep (j - 1) (by omega) (by change j - 1 < S.k; omega) p hpn e he
    rw [hRMd, hLd] at hs
    have : ((dinf p e : ℕ) : ℝ) ≤ 2 * (S.L : ℝ) ^ j := by
      have h := Nat.cast_le (α := ℝ) |>.2 hde; push_cast at h; exact h
    have hj : (S.L : ℝ) ^ j = S.L * (S.L : ℝ) ^ (j - 1) := by
      rw [← pow_succ']; congr 1; omega
    have h0 : (0 : ℝ) < (S.L : ℝ) ^ (j - 1) := by positivity
    have h1 : 2 * (S.L : ℝ) * (S.L : ℝ) ^ (j - 1) ≤ ((S.R * S.L ^ S.mM : ℕ) : ℝ) * (S.L : ℝ) ^ (j - 1) :=
      mul_le_mul_of_nonneg_right hRM h0.le
    rw [hj] at this
    linarith
  rw [show j - 1 + 1 = j by omega] at hsep
  rcases hend with he | he
  · exact hsep y he hd0
  · rw [hnext] at he
    exact hsep _ he hd1

end PartitionUnity

namespace PartitionUnity

open Lattices SFBounds SFLocal Blocks SmallFieldBlocks

variable (S : Lattices.SeqDom) (hM : 12 ≤ S.L ^ S.mM) (hR : 12 * S.L ≤ S.R) {N : ℕ}

local notation "NF" => SequenceAverages.N0 S
local notation "Mat" => Matrix (Fin N) (Fin N) ℂ

open Classical in
/-- **The squared differences of the `h_□` at two sites of a box**: if `|x - x'|_∞ ≤ 4L^r` and both scales are at
least `r - 1`, then `Σ_□(h_□(x) - h_□(x'))² ≤ 1536C_pu²L⁴M^{-2}`. -/
theorem sum_hL_diff_box (x x' : Site NF) (r : ℕ) (hd : dinf x x' ≤ 4 * S.L ^ r)
    (hs : r ≤ (S.toDomSeq).sc x + 1) (hs' : r ≤ (S.toDomSeq).sc x' + 1) :
    ∑ q, (hL S hM hR q x - hL S hM hR q x') ^ 2 ≤ 1536 * Cpu S.L ^ 2 * (S.L : ℝ) ^ 4 / ((S.L : ℝ) ^ S.mM) ^ 2 := by
  set T1 := (Finset.univ : Finset (toScales S hM hR).Idx).filter fun q => hL S hM hR q x ≠ 0
  set T2 := (Finset.univ : Finset (toScales S hM hR).Idx).filter fun q => hL S hM hR q x' ≠ 0
  have hL1 : (1 : ℝ) ≤ S.L := by exact_mod_cast S.Lpos
  have hC := Cpu_nonneg S.L
  have hd' : (dinf x x' : ℝ) ≤ 4 * (S.L : ℝ) ^ r := by
    have h := Nat.cast_le (α := ℝ) |>.2 hd; push_cast at h; exact h
  have hterm : ∀ q ∈ T1 ∪ T2, (hL S hM hR q x - hL S hM hR q x') ^ 2 ≤
      16 * Cpu S.L ^ 2 * (S.L : ℝ) ^ 4 / ((S.L : ℝ) ^ S.mM) ^ 2 := by
    intro q hq
    have hlip := hL_lip S hM hR q x x'
    have hrq : r ≤ (q.1 : ℕ) + 2 := by
      rcases Finset.mem_union.1 hq with hq | hq
      · have := hL_scale S hM hR (Finset.mem_filter.1 hq).2; omega
      · have := hL_scale S hM hR (Finset.mem_filter.1 hq).2; omega
    have hMp : (0 : ℝ) < (S.L : ℝ) ^ S.mM := by positivity
    have hqp : (0 : ℝ) < (S.L : ℝ) ^ (q.1 : ℕ) := by positivity
    have hpow : (S.L : ℝ) ^ r ≤ (S.L : ℝ) ^ 2 * (S.L : ℝ) ^ (q.1 : ℕ) := by
      rw [← pow_add]; exact pow_le_pow_right₀ hL1 (by omega)
    have habs : |hL S hM hR q x - hL S hM hR q x'| ≤ 4 * Cpu S.L * (S.L : ℝ) ^ 2 / (S.L : ℝ) ^ S.mM := by
      refine hlip.trans ?_
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) hMp]
      have h1 : Cpu S.L * (dinf x x' : ℝ) ≤ Cpu S.L * (4 * ((S.L : ℝ) ^ 2 * (S.L : ℝ) ^ (q.1 : ℕ))) :=
        mul_le_mul_of_nonneg_left (hd'.trans (by linarith)) hC
      calc Cpu S.L * (dinf x x' : ℝ) * (S.L : ℝ) ^ S.mM
          ≤ Cpu S.L * (4 * ((S.L : ℝ) ^ 2 * (S.L : ℝ) ^ (q.1 : ℕ))) * (S.L : ℝ) ^ S.mM :=
            mul_le_mul_of_nonneg_right h1 hMp.le
        _ = _ := by ring
    have hsq := pow_le_pow_left₀ (abs_nonneg _) habs 2
    rw [sq_abs] at hsq
    refine hsq.trans (le_of_eq ?_)
    field_simp; ring
  have hzero : ∀ q, q ∉ T1 ∪ T2 → (hL S hM hR q x - hL S hM hR q x') ^ 2 = 0 := by
    intro q hq
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, not_or, not_not, T1, T2] at hq
    rw [hq.1, hq.2]; ring
  rw [← Finset.sum_subset (Finset.subset_univ (T1 ∪ T2)) (fun q _ hq => hzero q hq)]
  have hcard : ((T1 ∪ T2).card : ℝ) ≤ 96 := by
    have := Finset.card_union_le T1 T2
    have h1 : T1.card ≤ 48 := by convert card_hL S hM hR x
    have h2 : T2.card ≤ 48 := by convert card_hL S hM hR x'
    exact_mod_cast (this.trans (by omega))
  calc ∑ q ∈ T1 ∪ T2, (hL S hM hR q x - hL S hM hR q x') ^ 2
      ≤ ∑ _q ∈ T1 ∪ T2, 16 * Cpu S.L ^ 2 * (S.L : ℝ) ^ 4 / ((S.L : ℝ) ^ S.mM) ^ 2 := Finset.sum_le_sum hterm
    _ = (T1 ∪ T2).card * (16 * Cpu S.L ^ 2 * (S.L : ℝ) ^ 4 / ((S.L : ℝ) ^ S.mM) ^ 2) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 96 * (16 * Cpu S.L ^ 2 * (S.L : ℝ) ^ 4 / ((S.L : ℝ) ^ S.mM) ^ 2) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by ring

/-- `a_b^{-2} ≤ L²a_a^{-2}` for `a ≤ b + 1`. -/
lemma inv_sq_pow_le {a b : ℕ} (h : a ≤ b + 1) :
    (((S.L ^ b : ℕ) : ℝ) ^ 2)⁻¹ ≤ (S.L : ℝ) ^ 2 * (((S.L ^ a : ℕ) : ℝ) ^ 2)⁻¹ := by
  have hL1 : (1 : ℝ) ≤ S.L := by exact_mod_cast S.Lpos
  push_cast
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), inv_mul_eq_div, div_le_iff₀ (by positivity), ← pow_mul,
    ← pow_mul, ← pow_add]
  exact pow_le_pow_right₀ hL1 (by omega)

end PartitionUnity

namespace PartitionUnity

open Lattices SFBounds SFLocal Blocks SmallFieldBlocks

variable (S : Lattices.SeqDom) (hM : 12 ≤ S.L ^ S.mM) (hR : 12 * S.L ≤ S.R) {N : ℕ}

local notation "NF" => SequenceAverages.N0 S
local notation "Mat" => Matrix (Fin N) (Fin N) ℂ

/-- The constant of the bound of the squared differences at two sites of a box. -/
def KQ (L mM : ℕ) : ℝ := 1536 * Cpu L ^ 2 * (L : ℝ) ^ 4 / ((L : ℝ) ^ mM) ^ 2

lemma KQ_nonneg (L mM : ℕ) : 0 ≤ KQ L mM := by unfold KQ; have := Cpu_nonneg L; positivity

lemma norm_re_inner_le {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (u v : V) :
    |(inner ℂ u v).re| ≤ 1 / 2 * (‖u‖ ^ 2 + ‖v‖ ^ 2) := by
  refine (Complex.abs_re_le_norm _).trans ((norm_inner_le_norm _ _).trans ?_)
  nlinarith [sq_nonneg (‖u‖ - ‖v‖)]

lemma sum_sum_add {ι : Type*} (I : Finset ι) (f : ι → ℝ) :
    ∑ i ∈ I, ∑ i' ∈ I, (f i + f i') = 2 * I.card * ∑ i ∈ I, f i := by
  simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
  rw [← Finset.mul_sum]; ring

/-- **The term of a bond in `errQ`**: `|a_c²Σ_{i,i'}a_c^{-10}D(i, i')Re⟨A(i), A(i')⟩| ≤ K_Q a_c^{-3}Σ_i|A(i)|²`. -/
theorem bond_term_le (hRM : 2 * (S.L : ℝ) ≤ ((S.R * S.L ^ S.mM : ℕ) : ℝ)) {j : ℕ} {y : Site NF} {μ : Fin 4}
    (hq : (j, y, μ) ∈ QB S) (A : Fin 4 → Site NF → Mat) :
    |((S.L ^ j : ℕ) : ℝ) ^ 2 * ∑ i ∈ Blk S.toDomSeq j y ×ˢ range (S.L ^ j),
      ∑ i' ∈ Blk S.toDomSeq j y ×ˢ range (S.L ^ j),
        ((((S.L ^ j : ℕ) : ℝ) ^ 5)⁻¹) * ((((S.L ^ j : ℕ) : ℝ) ^ 5)⁻¹) *
          (∑ c, (hL S hM hR c (i.1 + ((i.2 : ℕ) : ZMod NF) • CoreLean.unit NF μ) -
            hL S hM hR c (i'.1 + ((i'.2 : ℕ) : ZMod NF) • CoreLean.unit NF μ)) ^ 2) *
          (inner ℂ (emb (N := N) (A μ (i.1 + ((i.2 : ℕ) : ZMod NF) • CoreLean.unit NF μ)))
            (emb (A μ (i'.1 + ((i'.2 : ℕ) : ZMod NF) • CoreLean.unit NF μ)))).re| ≤
      KQ S.L S.mM * ((((S.L ^ j : ℕ) : ℝ) ^ 3)⁻¹ * ∑ i ∈ Blk S.toDomSeq j y ×ˢ range (S.L ^ j),
        ‖emb (N := N) (A μ (i.1 + ((i.2 : ℕ) : ZMod NF) • CoreLean.unit NF μ))‖ ^ 2) := by
  set I := Blk S.toDomSeq j y ×ˢ range (S.L ^ j)
  set n : ℝ := ((S.L ^ j : ℕ) : ℝ)
  set pt : Site NF × ℕ → Site NF := fun i => i.1 + ((i.2 : ℕ) : ZMod NF) • CoreLean.unit NF μ
  set f : Site NF × ℕ → ℝ := fun i => ‖emb (N := N) (A μ (pt i))‖ ^ 2
  have hq' := hq
  simp only [QB, mem_filter, mem_product, mem_range, mem_univ, true_and] at hq'
  have hjk : j ≤ S.k := by omega
  have hn : 0 < n := by simp only [n]; have := S.Lpos; positivity
  have hI : (I.card : ℝ) = n ^ 5 := by
    simp only [I, n, Finset.card_product, card_Blk_j S hjk hq'.2.1, Finset.card_range]
    push_cast; ring
  have hK := KQ_nonneg S.L S.mM
  have hn5 : (0 : ℝ) ≤ (n ^ 5)⁻¹ * (n ^ 5)⁻¹ :=
    mul_nonneg (inv_nonneg.2 (pow_nonneg hn.le 5)) (inv_nonneg.2 (pow_nonneg hn.le 5))
  have hmem : ∀ i ∈ I, j ≤ (S.toDomSeq).sc (pt i) + 1 ∧ dinf (pt i) y ≤ 2 * S.L ^ j := by
    intro i hi
    rw [Finset.mem_product, Finset.mem_range] at hi
    refine ⟨(box_scale S hRM hq hi.1 hi.2).2, ?_⟩
    have h := box_dinf S hi.1 μ hi.2.le (Nat.zero_le (S.L ^ j))
    simpa only [Nat.cast_zero, zero_smul, add_zero] using h
  have hpair : ∀ i ∈ I, ∀ i' ∈ I,
      |(n ^ 5)⁻¹ * (n ^ 5)⁻¹ * (∑ c, (hL S hM hR c (pt i) - hL S hM hR c (pt i')) ^ 2) *
        (inner ℂ (emb (N := N) (A μ (pt i))) (emb (A μ (pt i')))).re| ≤
      (n ^ 5)⁻¹ * (n ^ 5)⁻¹ * KQ S.L S.mM * (1 / 2 * (f i + f i')) := by
    intro i hi i' hi'
    obtain ⟨h1, h2⟩ := hmem i hi
    obtain ⟨h1', h2'⟩ := hmem i' hi'
    have hd : dinf (pt i) (pt i') ≤ 4 * S.L ^ j := by
      have := dinf_triangle (pt i) y (pt i'); rw [dinf_comm y] at this; omega
    have hD := sum_hL_diff_box S hM hR (pt i) (pt i') j hd h1 h1'
    have hD0 : 0 ≤ ∑ c, (hL S hM hR c (pt i) - hL S hM hR c (pt i')) ^ 2 :=
      Finset.sum_nonneg fun c _ => sq_nonneg _
    have hre := norm_re_inner_le (emb (N := N) (A μ (pt i))) (emb (A μ (pt i')))
    have hD' : ∑ c, (hL S hM hR c (pt i) - hL S hM hR c (pt i')) ^ 2 ≤ KQ S.L S.mM := hD
    rw [abs_mul, abs_mul, abs_of_nonneg hn5, abs_of_nonneg hD0, mul_assoc]
    calc (n ^ 5)⁻¹ * (n ^ 5)⁻¹ * ((∑ c, (hL S hM hR c (pt i) - hL S hM hR c (pt i')) ^ 2) *
          |(inner ℂ (emb (N := N) (A μ (pt i))) (emb (A μ (pt i')))).re|)
        ≤ (n ^ 5)⁻¹ * (n ^ 5)⁻¹ * (KQ S.L S.mM * (1 / 2 * (f i + f i'))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hD' hre (abs_nonneg _) hK) hn5
      _ = _ := by ring
  rw [abs_mul, abs_of_pos (pow_pos hn 2)]
  calc n ^ 2 * |∑ i ∈ I, ∑ i' ∈ I, (n ^ 5)⁻¹ * (n ^ 5)⁻¹ *
        (∑ c, (hL S hM hR c (pt i) - hL S hM hR c (pt i')) ^ 2) *
        (inner ℂ (emb (N := N) (A μ (pt i))) (emb (A μ (pt i')))).re|
      ≤ n ^ 2 * ∑ i ∈ I, ∑ i' ∈ I, (n ^ 5)⁻¹ * (n ^ 5)⁻¹ * KQ S.L S.mM * (1 / 2 * (f i + f i')) := by
        refine mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi =>
          (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i' hi' => hpair i hi i' hi'))) (by positivity)
    _ = n ^ 2 * ((n ^ 5)⁻¹ * (n ^ 5)⁻¹ * KQ S.L S.mM * (1 / 2)) * ∑ i ∈ I, ∑ i' ∈ I, (f i + f i') := by
        simp only [Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    _ = KQ S.L S.mM * ((n ^ 3)⁻¹ * ∑ i ∈ I, f i) := by
        rw [sum_sum_add, hI]
        field_simp

end PartitionUnity

namespace PartitionUnity

open Lattices SFBounds SFLocal Blocks SmallFieldBlocks

variable (S : Lattices.SeqDom) (hM : 12 ≤ S.L ^ S.mM) (hR : 12 * S.L ≤ S.R) {N : ℕ}

local notation "NF" => SequenceAverages.N0 S
local notation "Mat" => Matrix (Fin N) (Fin N) ℂ

/-- The weighted density of a component on the sites of the scales `j - 1`, `j`, `j + 1`. -/
def gW (A : Fin 4 → Site NF → Mat) (j : ℕ) (μ : Fin 4) (p : Site NF) : ℝ :=
  (if (S.toDomSeq).sc p ≤ j + 1 ∧ j ≤ (S.toDomSeq).sc p + 1 then (1 : ℝ) else 0) *
    ((((S.L ^ (S.toDomSeq).sc p : ℕ) : ℝ) ^ 2)⁻¹ * ‖emb (N := N) (A μ p)‖ ^ 2)

lemma gW_nonneg (A : Fin 4 → Site NF → Mat) (j : ℕ) (μ : Fin 4) (p : Site NF) : 0 ≤ gW S A j μ p := by
  unfold gW; split_ifs <;> positivity

/-- At most three layers meet a site. -/
lemma sum_gW_le (A : Fin 4 → Site NF → Mat) (μ : Fin 4) (p : Site NF) :
    ∑ j ∈ range (S.k + 1), gW S A j μ p ≤
      3 * ((((S.L ^ (S.toDomSeq).sc p : ℕ) : ℝ) ^ 2)⁻¹ * ‖emb (N := N) (A μ p)‖ ^ 2) := by
  unfold gW
  rw [← Finset.sum_mul, Finset.sum_boole]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  have hsub : (range (S.k + 1)).filter (fun j => (S.toDomSeq).sc p ≤ j + 1 ∧ j ≤ (S.toDomSeq).sc p + 1) ⊆
      Finset.Icc ((S.toDomSeq).sc p - 1) ((S.toDomSeq).sc p + 1) := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_Icc] at hj ⊢
    omega
  have h := Finset.card_le_card hsub
  rw [Nat.card_Icc] at h
  have : ((range (S.k + 1)).filter (fun j => (S.toDomSeq).sc p ≤ j + 1 ∧ j ≤ (S.toDomSeq).sc p + 1)).card ≤ 3 := by
    omega
  exact_mod_cast this

/-- **The weight on a box**: `a_j^{-3}|A(x + te_μ)|² ≤ L²a_j^{-1}g_{j,μ}(x + te_μ)`. -/
lemma box_weight (hRM : 2 * (S.L : ℝ) ≤ ((S.R * S.L ^ S.mM : ℕ) : ℝ)) {j : ℕ} {y : Site NF} {μ : Fin 4}
    (hq : (j, y, μ) ∈ QB S) (A : Fin 4 → Site NF → Mat) {x : Site NF} (hx : x ∈ Blk S.toDomSeq j y) {t : ℕ}
    (ht : t < S.L ^ j) :
    (((S.L ^ j : ℕ) : ℝ) ^ 3)⁻¹ * ‖emb (N := N) (A μ (x + ((t : ℕ) : ZMod NF) • CoreLean.unit NF μ))‖ ^ 2 ≤
      (S.L : ℝ) ^ 2 * ((((S.L ^ j : ℕ) : ℝ))⁻¹ * gW S A j μ (x + ((t : ℕ) : ZMod NF) • CoreLean.unit NF μ)) := by
  set p := x + ((t : ℕ) : ZMod NF) • CoreLean.unit NF μ
  obtain ⟨h1, h2⟩ := box_scale S hRM hq hx ht
  have hw := inv_sq_pow_le S h1
  unfold gW
  rw [if_pos ⟨h1, h2⟩, one_mul]
  have hn : (0 : ℝ) < ((S.L ^ j : ℕ) : ℝ) := by have := S.Lpos; positivity
  have e : (((S.L ^ j : ℕ) : ℝ) ^ 3)⁻¹ = (((S.L ^ j : ℕ) : ℝ))⁻¹ * (((S.L ^ j : ℕ) : ℝ) ^ 2)⁻¹ := by
    rw [← mul_inv, ← pow_succ']
  rw [e]
  have hf : 0 ≤ ‖emb (N := N) (A μ p)‖ ^ 2 := sq_nonneg _
  calc (((S.L ^ j : ℕ) : ℝ))⁻¹ * (((S.L ^ j : ℕ) : ℝ) ^ 2)⁻¹ * ‖emb (N := N) (A μ p)‖ ^ 2
      ≤ (((S.L ^ j : ℕ) : ℝ))⁻¹ * ((S.L : ℝ) ^ 2 * (((S.L ^ (S.toDomSeq).sc p : ℕ) : ℝ) ^ 2)⁻¹) *
          ‖emb (N := N) (A μ p)‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hw (inv_nonneg.2 hn.le)) hf
    _ = _ := by ring

/-- **The sum over the bonds of the layers**: `Σ_c a_c^{-3}Σ_{X_c}|A_μ|² ≤ 3L²‖A‖_w²`. -/
theorem layer_sum_le (hRM : 2 * (S.L : ℝ) ≤ ((S.R * S.L ^ S.mM : ℕ) : ℝ)) (A : Fin 4 → Site NF → Mat) :
    ∑ q ∈ QB S, (((S.L ^ q.1 : ℕ) : ℝ) ^ 3)⁻¹ * ∑ i ∈ Blk S.toDomSeq q.1 q.2.1 ×ˢ range (S.L ^ q.1),
      ‖emb (N := N) (A q.2.2 (i.1 + ((i.2 : ℕ) : ZMod NF) • CoreLean.unit NF q.2.2))‖ ^ 2 ≤
      3 * (S.L : ℝ) ^ 2 * wnorm S A := by
  set F : ℕ × Site NF × Fin 4 → ℝ := fun q => (((S.L ^ q.1 : ℕ) : ℝ))⁻¹ *
    ∑ x ∈ Blk S.toDomSeq q.1 q.2.1, ∑ t ∈ range (S.L ^ q.1),
      gW S A q.1 q.2.2 (x + ((t : ℕ) : ZMod NF) • CoreLean.unit NF q.2.2)
  have hF0 : ∀ q, 0 ≤ F q := fun q => mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg _))
    (Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun t _ => gW_nonneg S A _ _ _)
  -- the box weight
  have h1 : ∑ q ∈ QB S, (((S.L ^ q.1 : ℕ) : ℝ) ^ 3)⁻¹ * ∑ i ∈ Blk S.toDomSeq q.1 q.2.1 ×ˢ range (S.L ^ q.1),
      ‖emb (N := N) (A q.2.2 (i.1 + ((i.2 : ℕ) : ZMod NF) • CoreLean.unit NF q.2.2))‖ ^ 2 ≤
      (S.L : ℝ) ^ 2 * ∑ q ∈ QB S, F q := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun q hq => ?_
    obtain ⟨j, y, μ⟩ := q
    simp only [F, Finset.sum_product, Finset.mul_sum]
    refine Finset.sum_le_sum fun x hx => Finset.sum_le_sum fun t ht => ?_
    exact box_weight S hRM hq A hx (Finset.mem_range.1 ht)
  -- each layer and direction
  have h2 : ∀ j μ, ∑ y, F (j, y, μ) = ∑ p, gW S A j μ p := by
    intro j μ
    simp only [F]
    rw [← Finset.mul_sum]
    have e : ∑ y, ∑ x ∈ Blk S.toDomSeq j y, ∑ t ∈ range (S.L ^ j),
        gW S A j μ (x + ((t : ℕ) : ZMod NF) • CoreLean.unit NF μ) =
        ∑ x, ∑ t ∈ range (S.L ^ j), gW S A j μ (x + ((t : ℕ) : ZMod NF) • CoreLean.unit NF μ) := by
      unfold Blk
      exact Finset.sum_fiberwise Finset.univ (fun x => Blocks.cen (S.toDomSeq).L j x) _
    rw [e, Finset.sum_comm]
    simp only [sum_shift_site S (fun p => gW S A j μ p), Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hn : (0 : ℝ) < ((S.L ^ j : ℕ) : ℝ) := by have := S.Lpos; positivity
    field_simp
  have h3 : ∑ q ∈ QB S, F q ≤ ∑ j ∈ range (S.k + 1), ∑ μ, ∑ p, gW S A j μ p := by
    have hsub : QB S ⊆ range (S.k + 1) ×ˢ (Finset.univ ×ˢ Finset.univ) := by
      classical
      intro q hq
      unfold QB at hq
      exact Finset.mem_of_mem_filter q hq
    refine (Finset.sum_le_sum_of_subset_of_nonneg hsub fun q _ _ => hF0 q).trans (le_of_eq ?_)
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_product, Finset.sum_comm]
    exact Finset.sum_congr rfl fun μ _ => h2 j μ
  have h4 : ∑ j ∈ range (S.k + 1), ∑ μ, ∑ p, gW S A j μ p ≤ 3 * wnorm S A := by
    have e : ∑ j ∈ range (S.k + 1), ∑ μ, ∑ p, gW S A j μ p = ∑ p, ∑ μ, ∑ j ∈ range (S.k + 1), gW S A j μ p := by
      rw [Finset.sum_comm]
      refine (Finset.sum_congr rfl fun μ _ => Finset.sum_comm).trans ?_
      exact Finset.sum_comm
    rw [e]
    unfold wnorm
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun p _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun μ _ => ?_
    refine (sum_gW_le S A μ p).trans (le_of_eq ?_)
    ring
  calc _ ≤ (S.L : ℝ) ^ 2 * ∑ q ∈ QB S, F q := h1
    _ ≤ (S.L : ℝ) ^ 2 * (3 * wnorm S A) := mul_le_mul_of_nonneg_left (h3.trans h4) (by positivity)
    _ = _ := by ring

/-- **The error of the localisation of the constraint form**: `|errQ| ≤ 3L²K_Q‖A‖_w² = 4608C_pu²L⁶M^{-2}‖A‖_w²`. -/
theorem errQ_le (hRM : 2 * (S.L : ℝ) ≤ ((S.R * S.L ^ S.mM : ℕ) : ℝ)) (A : Fin 4 → Site NF → Mat) :
    |errQ S Finset.univ (hL S hM hR) A| ≤ 3 * (S.L : ℝ) ^ 2 * KQ S.L S.mM * wnorm S A := by
  unfold errQ
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc _ ≤ ∑ q ∈ QB S, KQ S.L S.mM * ((((S.L ^ q.1 : ℕ) : ℝ) ^ 3)⁻¹ *
        ∑ i ∈ Blk S.toDomSeq q.1 q.2.1 ×ˢ range (S.L ^ q.1),
          ‖emb (N := N) (A q.2.2 (i.1 + ((i.2 : ℕ) : ZMod NF) • CoreLean.unit NF q.2.2))‖ ^ 2) := by
        refine Finset.sum_le_sum fun q hq => ?_
        obtain ⟨j, y, μ⟩ := q
        exact bond_term_le S hM hR hRM hq A
    _ = KQ S.L S.mM * ∑ q ∈ QB S, (((S.L ^ q.1 : ℕ) : ℝ) ^ 3)⁻¹ *
        ∑ i ∈ Blk S.toDomSeq q.1 q.2.1 ×ˢ range (S.L ^ q.1),
          ‖emb (N := N) (A q.2.2 (i.1 + ((i.2 : ℕ) : ZMod NF) • CoreLean.unit NF q.2.2))‖ ^ 2 := by
        rw [Finset.mul_sum]
    _ ≤ KQ S.L S.mM * (3 * (S.L : ℝ) ^ 2 * wnorm S A) :=
        mul_le_mul_of_nonneg_left (layer_sum_le S hRM A) (KQ_nonneg _ _)
    _ = _ := by ring

end PartitionUnity

namespace PartitionUnity

open Lattices SFBounds SFLocal Blocks SmallFieldBlocks

variable (S : Lattices.SeqDom) (hM : 12 ≤ S.L ^ S.mM) (hR : 12 * S.L ≤ S.R) {N : ℕ}

local notation "NF" => SequenceAverages.N0 S
local notation "Mat" => Matrix (Fin N) (Fin N) ℂ

/-- **The commutators of `∂^*` with the partition of unity**:
`Σ_□‖[∂^*, h_□]A‖² ≤ 384C_pu²L⁴M^{-2}‖A‖_w²` (in the norm of `V`). -/
theorem commA_le (hRM : (S.L : ℝ) < ((S.R * S.L ^ S.mM : ℕ) : ℝ)) (A : Fin 4 → Site NF → Mat) :
    (N : ℝ) * ∑ c, ∑ x, hs2 (commA S (hL S hM hR c) A x) ≤
      384 * Cpu S.L ^ 2 * (S.L : ℝ) ^ 4 / ((S.L : ℝ) ^ S.mM) ^ 2 * wnorm S A := by
  set K := 96 * Cpu S.L ^ 2 * (S.L : ℝ) ^ 4 / ((S.L : ℝ) ^ S.mM) ^ 2
  have hK : 0 ≤ K := by have := Cpu_nonneg S.L; positivity
  set w : Site NF → ℝ := fun x => ((S.L : ℝ) ^ (2 * (S.toDomSeq).sc x))⁻¹
  have hw0 : ∀ x, 0 ≤ w x := fun x => by positivity
  set d : (toScales S hM hR).Idx → Fin 4 → Site NF → ℝ := fun c μ x =>
    (hL S hM hR c (x + CoreLean.unit NF μ) - hL S hM hR c x) ^ 2
  -- the pointwise bound
  have h1 : ∀ c x, hs2 (commA S (hL S hM hR c) A x) ≤
      4 * ∑ μ, d c μ (x - CoreLean.unit NF μ) * hs2 (A μ (x - CoreLean.unit NF μ)) := by
    intro c x
    unfold commA
    refine (hs2_sum4_le _).trans (le_of_eq ?_)
    congr 1
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [RegularAverages.hs2_smul, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    simp only [d, sub_add_cancel]
    ring
  -- the shift and the bound of the differences
  have h2 : ∀ μ, ∑ x, (∑ c, d c μ (x - CoreLean.unit NF μ)) * hs2 (A μ (x - CoreLean.unit NF μ)) ≤
      K * ∑ x, w x * hs2 (A μ x) := by
    intro μ
    have e := sum_shift_site S (fun x => (∑ c, d c μ x) * hs2 (A μ x)) (-CoreLean.unit NF μ)
    simp only [← sub_eq_add_neg] at e
    rw [e, Finset.mul_sum]
    refine Finset.sum_le_sum fun x _ => ?_
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (sum_hL_diff_sq S hM hR hRM x μ) (hs2_nonneg _)
  have hwn : wnorm S A = ∑ x, w x * ∑ μ, (N : ℝ) * hs2 (A μ x) := by
    unfold wnorm
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [w, norm_emb_sq]
    push_cast; rw [← pow_mul, mul_comm 2]
  calc (N : ℝ) * ∑ c, ∑ x, hs2 (commA S (hL S hM hR c) A x)
      ≤ (N : ℝ) * ∑ c, ∑ x, 4 * ∑ μ, d c μ (x - CoreLean.unit NF μ) * hs2 (A μ (x - CoreLean.unit NF μ)) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun c _ => Finset.sum_le_sum fun x _ => h1 c x)
          (Nat.cast_nonneg _)
    _ = 4 * (N : ℝ) * ∑ c, ∑ x, ∑ μ, d c μ (x - CoreLean.unit NF μ) * hs2 (A μ (x - CoreLean.unit NF μ)) := by
        simp only [Finset.mul_sum]
        exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun x _ =>
          Finset.sum_congr rfl fun μ _ => by ring
    _ = 4 * (N : ℝ) * ∑ μ, ∑ x, (∑ c, d c μ (x - CoreLean.unit NF μ)) * hs2 (A μ (x - CoreLean.unit NF μ)) := by
        have h3 : ∑ c, ∑ x, ∑ μ, d c μ (x - CoreLean.unit NF μ) * hs2 (A μ (x - CoreLean.unit NF μ)) =
            ∑ μ, ∑ x, ∑ c, d c μ (x - CoreLean.unit NF μ) * hs2 (A μ (x - CoreLean.unit NF μ)) := by
          rw [Finset.sum_comm]
          exact (Finset.sum_congr rfl fun x _ => Finset.sum_comm).trans Finset.sum_comm
        rw [h3]
        simp only [Finset.sum_mul]
    _ ≤ 4 * (N : ℝ) * ∑ μ, K * ∑ x, w x * hs2 (A μ x) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun μ _ => h2 μ) (by positivity)
    _ = 4 * K * wnorm S A := by
        rw [hwn, ← Finset.mul_sum, Finset.sum_comm]
        simp only [Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun μ _ => by ring
    _ = _ := by simp only [K]; ring

end PartitionUnity

namespace PartitionUnity

open Lattices SFBounds SFLocal Blocks SmallFieldBlocks

variable (S : Lattices.SeqDom) (hM : 12 ≤ S.L ^ S.mM) (hR : 12 * S.L ≤ S.R) {N : ℕ}

local notation "NF" => SequenceAverages.N0 S
local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "RMS" => ((S.R * S.L ^ S.mM : ℕ) : ℝ)

open Classical in
/-- At most `96` of the differences `h_□(x) - h_□(x')` do not vanish. -/
lemma sum_hL_diff_of_term (x x' : Site NF) (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ q, (hL S hM hR q x ≠ 0 ∨ hL S hM hR q x' ≠ 0) → (hL S hM hR q x - hL S hM hR q x') ^ 2 ≤ B) :
    ∑ q, (hL S hM hR q x - hL S hM hR q x') ^ 2 ≤ 96 * B := by
  set T1 := (Finset.univ : Finset (toScales S hM hR).Idx).filter fun q => hL S hM hR q x ≠ 0
  set T2 := (Finset.univ : Finset (toScales S hM hR).Idx).filter fun q => hL S hM hR q x' ≠ 0
  have hzero : ∀ q, q ∉ T1 ∪ T2 → (hL S hM hR q x - hL S hM hR q x') ^ 2 = 0 := by
    intro q hq
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, not_or, not_not, T1, T2] at hq
    rw [hq.1, hq.2]; ring
  rw [← Finset.sum_subset (Finset.subset_univ (T1 ∪ T2)) (fun q _ hq => hzero q hq)]
  have hcard : ((T1 ∪ T2).card : ℝ) ≤ 96 := by
    have := Finset.card_union_le T1 T2
    have h1 : T1.card ≤ 48 := by convert card_hL S hM hR x
    have h2 : T2.card ≤ 48 := by convert card_hL S hM hR x'
    exact_mod_cast (this.trans (by omega))
  calc ∑ q ∈ T1 ∪ T2, (hL S hM hR q x - hL S hM hR q x') ^ 2
      ≤ ∑ _q ∈ T1 ∪ T2, B := Finset.sum_le_sum fun q hq => hB q (by
        rcases Finset.mem_union.1 hq with h | h
        · exact Or.inl (Finset.mem_filter.1 h).2
        · exact Or.inr (Finset.mem_filter.1 h).2)
    _ = (T1 ∪ T2).card * B := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 96 * B := mul_le_mul_of_nonneg_right hcard hB0

/-- The constant of the bound of the squared differences by the weighted distance. -/
def KP (L : ℕ) : ℝ := 96 * Cpu L ^ 2 * (L : ℝ) ^ 4 + 4

lemma KP_nonneg (L : ℕ) : 0 ≤ KP L := by unfold KP; have := Cpu_nonneg L; positivity

/-- **The squared differences of the partition of unity in the weighted distance**:
`Σ_□(h_□(x) - h_□(x'))² ≤ K_PM^{-2}d(x, x')²` for all sites (`R ≥ 1`). -/
theorem sum_hL_diff_dF (hR1 : 1 ≤ S.R) (x x' : Site NF) :
    ∑ q, (hL S hM hR q x - hL S hM hR q x') ^ 2 ≤ KP S.L / ((S.L : ℝ) ^ S.mM) ^ 2 * S.dF x x' ^ 2 := by
  have hL1 : (1 : ℝ) ≤ S.L := by exact_mod_cast S.Lpos
  have hMp : (0 : ℝ) < (S.L : ℝ) ^ S.mM := by positivity
  have hC := Cpu_nonneg S.L
  have hdF0 : 0 ≤ S.dF x x' := S.dF_nonneg x x'
  have hRMS : (S.L : ℝ) ^ S.mM ≤ RMS := by
    push_cast
    have : (1 : ℝ) ≤ S.R := by exact_mod_cast hR1
    nlinarith
  rcases lt_or_ge (S.dF x x') RMS with hd | hd
  · -- near: the local comparison of the distances
    set m := min ((S.toDomSeq).sc x) ((S.toDomSeq).sc x')
    have hdinf : (dinf x x' : ℝ) ≤ (S.L : ℝ) ^ (m + 1) * S.dF x x' := by
      rcases le_total ((S.toDomSeq).sc x) ((S.toDomSeq).sc x') with h | h
      · have e : m = (S.toDomSeq).sc x := min_eq_left h
        rw [e]; exact S.dinf_le_dF x x' hd
      · have e : m = (S.toDomSeq).sc x' := min_eq_right h
        rw [e, dinf_comm, S.dF_comm]
        exact S.dinf_le_dF x' x (by rw [S.dF_comm]; exact hd)
    have hB : ∀ q, (hL S hM hR q x ≠ 0 ∨ hL S hM hR q x' ≠ 0) → (hL S hM hR q x - hL S hM hR q x') ^ 2 ≤
        Cpu S.L ^ 2 * (S.L : ℝ) ^ 4 / ((S.L : ℝ) ^ S.mM) ^ 2 * S.dF x x' ^ 2 := by
      intro q hq
      have hmq : m + 1 ≤ (q.1 : ℕ) + 2 := by
        rcases hq with h | h
        · have := (hL_scale S hM hR h).2; have := min_le_left ((S.toDomSeq).sc x) ((S.toDomSeq).sc x'); omega
        · have := (hL_scale S hM hR h).2; have := min_le_right ((S.toDomSeq).sc x) ((S.toDomSeq).sc x'); omega
      have hqp : (0 : ℝ) < (S.L : ℝ) ^ (q.1 : ℕ) := by positivity
      have hpow : (S.L : ℝ) ^ (m + 1) ≤ (S.L : ℝ) ^ 2 * (S.L : ℝ) ^ (q.1 : ℕ) := by
        rw [← pow_add]; exact pow_le_pow_right₀ hL1 (by omega)
      have habs : |hL S hM hR q x - hL S hM hR q x'| ≤ Cpu S.L * (S.L : ℝ) ^ 2 / (S.L : ℝ) ^ S.mM * S.dF x x' := by
        refine (hL_lip S hM hR q x x').trans ?_
        have h1 : (dinf x x' : ℝ) ≤ (S.L : ℝ) ^ 2 * (S.L : ℝ) ^ (q.1 : ℕ) * S.dF x x' :=
          hdinf.trans (mul_le_mul_of_nonneg_right hpow hdF0)
        calc Cpu S.L / ((S.L : ℝ) ^ S.mM * (S.L : ℝ) ^ (q.1 : ℕ)) * (dinf x x' : ℝ)
            ≤ Cpu S.L / ((S.L : ℝ) ^ S.mM * (S.L : ℝ) ^ (q.1 : ℕ)) *
                ((S.L : ℝ) ^ 2 * (S.L : ℝ) ^ (q.1 : ℕ) * S.dF x x') :=
              mul_le_mul_of_nonneg_left h1 (by positivity)
          _ = _ := by field_simp
      have hsq := pow_le_pow_left₀ (abs_nonneg _) habs 2
      rw [sq_abs] at hsq
      refine hsq.trans (le_of_eq ?_)
      field_simp
    refine (sum_hL_diff_of_term S hM hR x x' _ (by positivity) hB).trans ?_
    have : 96 * (Cpu S.L ^ 2 * (S.L : ℝ) ^ 4 / ((S.L : ℝ) ^ S.mM) ^ 2 * S.dF x x' ^ 2) ≤
        KP S.L / ((S.L : ℝ) ^ S.mM) ^ 2 * S.dF x x' ^ 2 := by
      unfold KP
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, mul_div_assoc', div_le_div_iff_of_pos_right (by positivity)]
      nlinarith [sq_nonneg (S.dF x x')]
    exact this
  · -- far: `Σ_□(h_□(x) - h_□(x'))² ≤ 4`
    have h4 : ∑ q, (hL S hM hR q x - hL S hM hR q x') ^ 2 ≤ 4 := by
      have e : ∀ q, (hL S hM hR q x - hL S hM hR q x') ^ 2 ≤ 2 * hL S hM hR q x ^ 2 + 2 * hL S hM hR q x' ^ 2 :=
        fun q => by nlinarith [sq_nonneg (hL S hM hR q x + hL S hM hR q x')]
      refine (Finset.sum_le_sum fun q _ => e q).trans (le_of_eq ?_)
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hL_sum, hL_sum]; norm_num
    refine h4.trans ?_
    have h5 : (S.L : ℝ) ^ S.mM ≤ S.dF x x' := hRMS.trans hd
    have h6 : ((S.L : ℝ) ^ S.mM) ^ 2 ≤ S.dF x x' ^ 2 := pow_le_pow_left₀ hMp.le h5 2
    have h7 : 4 ≤ KP S.L := by
      unfold KP; have : 0 ≤ 96 * Cpu S.L ^ 2 * (S.L : ℝ) ^ 4 := by positivity
      linarith
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    nlinarith

end PartitionUnity

namespace PartitionUnity

open scoped Matrix
open Lattices SeqDom SFBounds SFLocal Blocks SmallFieldBlocks SmallFieldDecay SmallFieldCoercivity

variable (S : Lattices.SeqDom) (hM : 12 ≤ S.L ^ S.mM) (hR : 12 * S.L ≤ S.R) {N : ℕ}

local notation "NF" => SequenceAverages.N0 S
local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "RMS" => ((S.R * S.L ^ S.mM : ℕ) : ℝ)

lemma rpow_neg_four (j : ℕ) : ((S.L : ℝ) ^ j) ^ (-4 : ℝ) = ((S.L : ℝ) ^ (4 * j))⁻¹ := by
  have hL : (0 : ℝ) < S.L := by exact_mod_cast S.Lpos
  rw [Real.rpow_neg (by positivity), show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, ← pow_mul,
    mul_comm]

/-- `(d + 4)² ≤ (16θ^{-2} + 32)e^{θd/2}` for `d ≥ 0`. -/
lemma sq_add_four_le_exp {θ d : ℝ} (hθ : 0 < θ) (hd : 0 ≤ d) :
    (d + 4) ^ 2 ≤ (16 / θ ^ 2 + 32) * Real.exp (θ * d / 2) := by
  have he := Real.quadratic_le_exp_of_nonneg (show 0 ≤ θ * d / 2 by positivity)
  have h1 : d ^ 2 ≤ 8 / θ ^ 2 * Real.exp (θ * d / 2) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (θ * d)]
  have h2 : 1 ≤ Real.exp (θ * d / 2) := Real.one_le_exp (by positivity)
  have h3 : (d + 4) ^ 2 ≤ 2 * d ^ 2 + 32 := by nlinarith [sq_nonneg (d - 4)]
  have h4 : (16 / θ ^ 2 + 32) * Real.exp (θ * d / 2) = 2 * (8 / θ ^ 2 * Real.exp (θ * d / 2)) +
      32 * Real.exp (θ * d / 2) := by ring
  linarith

variable {S}

/-- **The kernel of `P` at the trivial configuration**: `|k_P(x, x')Z| ≤ C_Pa_{y(x')}^{-4}e^{-θd(y(x), y(x'))}|Z|`. -/
lemma kP_bound [NeZero N] {δ : ℝ} (H : ScalarHyp (N := N) S (X0 S) 0 (W1 S) 0 Set.univ δ)
    (hRMb : (S.toContSeq).r1 (1 / 2) (1 / 32 * δ) ≤ RMS) (hRMs4 : 32 * Real.log S.L / (1 / 4 * δ) ≤ RMS)
    (hsmallT : CTd S N δ 0 0 * (S.toContSeq).c1 (1 / 2) (1 / 32 * δ) ≤ gammaB N / 4)
    (hRMθs : 32 * Real.log S.L / (thetaB S N δ / 2) ≤ RMS)
    (hRMθc : (S.toContSeq).r1 (1 / 2) (7 / 16 * thetaB S N δ) ≤ RMS) (x x' : Site NF) (Z : Mat) :
    hs (kP S x x' Z) ≤ CPk S N δ * ((S.L : ℝ) ^ (4 * (S.toDomSeq).sc (bc S.toDomSeq x')))⁻¹ *
      Real.exp (-(7 / 32 * thetaB S N δ * S.dF (bc S.toDomSeq x) (bc S.toDomSeq x'))) * hs Z := by
  have hP := H.P_bound hRMb hRMs4 hsmallT hRMθs hRMθc (Pi.single x' Z) x
  have e : kP S x x' Z = Pop S (X0 S) (W1 S) Set.univ (Pi.single x' Z) x := rfl
  rw [e]
  refine hP.trans (le_of_eq ?_)
  rw [Finset.sum_eq_single x' (fun b _ hb => by rw [Pi.single_eq_of_ne hb, RegularAverages.hs_zero', mul_zero])
    (fun h => absurd (Finset.mem_univ x') h), Pi.single_eq_same]
  ring

/-- **The error of the localisation of `‖Pg‖²`**:
`|Re Σ_{x,x'}Σ_□(h_□(x) - h_□(x'))²tr((k_Pg(x'))^*g(x))| ≤ C_{err}M^{-2}‖g‖²`, with
`C_err = K_PC_P(16θ^{-2} + 32)(c₁(½, θ) + L⁴c₁(½, θ/2))/2`, `θ = (7/32)θ_B`. -/
theorem errP_le [NeZero N] {δ : ℝ} (H : ScalarHyp (N := N) S (X0 S) 0 (W1 S) 0 Set.univ δ)
    (hRMb : (S.toContSeq).r1 (1 / 2) (1 / 32 * δ) ≤ RMS) (hRMs4 : 32 * Real.log S.L / (1 / 4 * δ) ≤ RMS)
    (hsmallT : CTd S N δ 0 0 * (S.toContSeq).c1 (1 / 2) (1 / 32 * δ) ≤ gammaB N / 4)
    (hRMθs : 32 * Real.log S.L / (thetaB S N δ / 2) ≤ RMS)
    (hRMθc : (S.toContSeq).r1 (1 / 2) (7 / 16 * thetaB S N δ) ≤ RMS)
    (hRMsum : (S.toContSeq).r1 (1 / 2) (7 / 32 * thetaB S N δ) ≤ RMS)
    (hRMsum2 : (S.toContSeq).r1 (1 / 2) (7 / 32 * thetaB S N δ / 2) ≤ RMS)
    (hRMss : 32 * Real.log S.L / (2 * (7 / 32 * thetaB S N δ)) ≤ RMS)
    (hR1 : 1 ≤ S.R) (g : Site NF → Mat) :
    |(∑ x, ∑ x', ((∑ c, (hL S hM hR c x - hL S hM hR c x') ^ 2 : ℝ) : ℂ) *
        ntr ((kP S x x' (g x'))ᴴ * g x)).re| ≤
      KP S.L / ((S.L : ℝ) ^ S.mM) ^ 2 * (CPk S N δ * (16 / (7 / 32 * thetaB S N δ) ^ 2 + 32) *
        (((S.toContSeq).c1 (1 / 2) (7 / 32 * thetaB S N δ) +
          (S.L : ℝ) ^ 4 * (S.toContSeq).c1 (1 / 2) (7 / 32 * thetaB S N δ / 2)) / 2)) * ∑ x, hs2 (g x) := by
  set θ := 7 / 32 * thetaB S N δ
  have hθ : 0 < θ := by have := H.thetaB_pos (N := N); positivity
  have hL1 : (1 : ℝ) ≤ S.L := by exact_mod_cast S.Lpos
  have hCP : 0 ≤ CPk S N δ := by
    have h1 : 0 ≤ (S.toContSeq).c1 (1 / 2) (thetaB S N δ) := by unfold Summation.ContSeq.c1; positivity
    have h2 : 0 ≤ (S.toContSeq).c1 (1 / 2) (7 / 16 * thetaB S N δ) := by unfold Summation.ContSeq.c1; positivity
    unfold CPk gammaB; positivity
  set c1 := (S.toContSeq).c1 (1 / 2) θ
  set c2 := (S.toContSeq).c1 (1 / 2) (θ / 2)
  have hc1 : 0 ≤ c1 := by unfold c1 Summation.ContSeq.c1; positivity
  have hc2 : 0 ≤ c2 := by unfold c2 Summation.ContSeq.c1; positivity
  set Kc := KP S.L / ((S.L : ℝ) ^ S.mM) ^ 2 * (CPk S N δ * (16 / θ ^ 2 + 32))
  have hKc : 0 ≤ Kc := by have := KP_nonneg S.L; positivity
  set K : Site NF → Site NF → ℝ := fun x x' => ((S.L : ℝ) ^ (4 * (S.toDomSeq).sc (bc S.toDomSeq x')))⁻¹ *
    Real.exp (-(1 / 2 * θ * S.dF (bc S.toDomSeq x) (bc S.toDomSeq x')))
  have hK : ∀ x x', 0 ≤ K x x' := fun x x' => by positivity
  set u : Site NF → ℝ := fun x => hs (g x)
  have hu : ∀ x, 0 ≤ u x := fun x => hs_nonneg _
  -- the pointwise bound
  have hpt : ∀ x x', ‖((∑ c, (hL S hM hR c x - hL S hM hR c x') ^ 2 : ℝ) : ℂ) *
      ntr ((kP S x x' (g x'))ᴴ * g x)‖ ≤ Kc * (K x x' * u x' * u x) := by
    intro x x'
    set d := S.dF (bc S.toDomSeq x) (bc S.toDomSeq x')
    have hd0 : 0 ≤ d := S.dF_nonneg _ _
    have hD0 : 0 ≤ ∑ c, (hL S hM hR c x - hL S hM hR c x') ^ 2 := Finset.sum_nonneg fun c _ => sq_nonneg _
    have hdx : S.dF x x' ≤ d + 4 := by
      have h2 := S.dF_triangle x (bc S.toDomSeq x) x'
      have h3 := S.dF_triangle (bc S.toDomSeq x) (bc S.toDomSeq x') x'
      have h4 := dF_bc_le S x
      have h5 := dF_bc_le S x'
      rw [S.dF_comm] at h5
      linarith
    have hD : ∑ c, (hL S hM hR c x - hL S hM hR c x') ^ 2 ≤
        KP S.L / ((S.L : ℝ) ^ S.mM) ^ 2 * ((16 / θ ^ 2 + 32) * Real.exp (θ * d / 2)) := by
      refine (sum_hL_diff_dF S hM hR hR1 x x').trans ?_
      refine mul_le_mul_of_nonneg_left ?_ (by have := KP_nonneg S.L; positivity)
      exact (pow_le_pow_left₀ (S.dF_nonneg x x') hdx 2).trans (sq_add_four_le_exp hθ hd0)
    have hk := kP_bound H hRMb hRMs4 hsmallT hRMθs hRMθc x x' (g x')
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hD0]
    have htr : ‖ntr ((kP S x x' (g x'))ᴴ * g x)‖ ≤ hs (kP S x x' (g x')) * u x := by
      refine (norm_ntr_mul_le _ _).trans (le_of_eq ?_)
      rw [hs_conjTranspose]
    have hexp : Real.exp (θ * d / 2) * Real.exp (-(θ * d)) = Real.exp (-(1 / 2 * θ * d)) := by
      rw [← Real.exp_add]; congr 1; ring
    calc (∑ c, (hL S hM hR c x - hL S hM hR c x') ^ 2) * ‖ntr ((kP S x x' (g x'))ᴴ * g x)‖
        ≤ (KP S.L / ((S.L : ℝ) ^ S.mM) ^ 2 * ((16 / θ ^ 2 + 32) * Real.exp (θ * d / 2))) *
          ((CPk S N δ * ((S.L : ℝ) ^ (4 * (S.toDomSeq).sc (bc S.toDomSeq x')))⁻¹ * Real.exp (-(θ * d)) * u x') * u x) :=
          mul_le_mul hD (htr.trans (mul_le_mul_of_nonneg_right hk (hu x))) (norm_nonneg _)
            (by have := KP_nonneg S.L; positivity)
      _ = Kc * (((S.L : ℝ) ^ (4 * (S.toDomSeq).sc (bc S.toDomSeq x')))⁻¹ *
            (Real.exp (θ * d / 2) * Real.exp (-(θ * d))) * u x' * u x) := by simp only [Kc]; ring
      _ = Kc * (K x x' * u x' * u x) := by rw [hexp]
  -- the sums of the kernel
  have hrow : ∀ x, ∑ x', K x x' ≤ c1 := fun x => by
    have := sum_fine_bc S (fun y' => Real.exp (-(1 / 2 * θ * S.dF (bc S.toDomSeq x) y')))
    simp only [K]
    rw [this]
    exact summation_fine S (by norm_num) hθ hRMsum (bc_mem_detB S x)
  have hcol : ∀ x', ∑ x, K x x' ≤ (S.L : ℝ) ^ 4 * c2 := fun x' => by
    set y' := bc S.toDomSeq x'
    have hshift : ∀ x, K x x' ≤ (S.L : ℝ) ^ 4 * (((S.L : ℝ) ^ (4 * (S.toDomSeq).sc (bc S.toDomSeq x)))⁻¹ *
        Real.exp (-(1 / 2 * (θ / 2) * S.dF y' (bc S.toDomSeq x)))) := by
      intro x
      have hs := scale_shift S (δ := 2 * θ) (σ := -4) (by positivity) hRMss (by norm_num) (bc S.toDomSeq x) y'
      rw [rpow_neg_four, rpow_neg_four, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at hs
      simp only [K]
      rw [S.dF_comm (bc S.toDomSeq x) y']
      have he : Real.exp (2 * θ / 8 * S.dF y' (bc S.toDomSeq x)) *
          Real.exp (-(1 / 2 * θ * S.dF y' (bc S.toDomSeq x))) =
          Real.exp (-(1 / 2 * (θ / 2) * S.dF y' (bc S.toDomSeq x))) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [S.dF_comm (bc S.toDomSeq x) y'] at hs
      calc ((S.L : ℝ) ^ (4 * (S.toDomSeq).sc y'))⁻¹ * Real.exp (-(1 / 2 * θ * S.dF y' (bc S.toDomSeq x)))
          ≤ ((S.L : ℝ) ^ 4 * Real.exp (2 * θ / 8 * S.dF y' (bc S.toDomSeq x)) *
              ((S.L : ℝ) ^ (4 * (S.toDomSeq).sc (bc S.toDomSeq x)))⁻¹) *
            Real.exp (-(1 / 2 * θ * S.dF y' (bc S.toDomSeq x))) :=
            mul_le_mul_of_nonneg_right hs (Real.exp_pos _).le
        _ = (S.L : ℝ) ^ 4 * (((S.L : ℝ) ^ (4 * (S.toDomSeq).sc (bc S.toDomSeq x)))⁻¹ *
            (Real.exp (2 * θ / 8 * S.dF y' (bc S.toDomSeq x)) *
              Real.exp (-(1 / 2 * θ * S.dF y' (bc S.toDomSeq x))))) := by ring
        _ = _ := by rw [he]
    calc ∑ x, K x x' ≤ ∑ x, (S.L : ℝ) ^ 4 * (((S.L : ℝ) ^ (4 * (S.toDomSeq).sc (bc S.toDomSeq x)))⁻¹ *
          Real.exp (-(1 / 2 * (θ / 2) * S.dF y' (bc S.toDomSeq x)))) := Finset.sum_le_sum fun x _ => hshift x
      _ = (S.L : ℝ) ^ 4 * ∑ y ∈ detB S.toDomSeq, Real.exp (-(1 / 2 * (θ / 2) * S.dF y' y)) := by
          rw [← Finset.mul_sum, sum_fine_bc S (fun y => Real.exp (-(1 / 2 * (θ / 2) * S.dF y' y)))]
      _ ≤ (S.L : ℝ) ^ 4 * c2 :=
          mul_le_mul_of_nonneg_left (summation_fine S (by norm_num) (by positivity) hRMsum2 (bc_mem_detB S x'))
            (by positivity)
  -- Schur
  have hschur : ∑ x, ∑ x', K x x' * u x' * u x ≤ (c1 + (S.L : ℝ) ^ 4 * c2) / 2 * ∑ x, u x ^ 2 := by
    have hamgm : ∀ x x', K x x' * u x' * u x ≤ K x x' * (u x ^ 2 + u x' ^ 2) / 2 := fun x x' => by
      have := hK x x'
      nlinarith [sq_nonneg (u x - u x'), mul_nonneg this (sq_nonneg (u x - u x'))]
    calc ∑ x, ∑ x', K x x' * u x' * u x ≤ ∑ x, ∑ x', K x x' * (u x ^ 2 + u x' ^ 2) / 2 :=
          Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun x' _ => hamgm x x'
      _ = (∑ x, u x ^ 2 * ∑ x', K x x' + ∑ x', u x' ^ 2 * ∑ x, K x x') / 2 := by
          simp only [Finset.mul_sum, mul_add, add_div, Finset.sum_div, Finset.sum_add_distrib]
          congr 1
          · exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun x' _ => by ring
          · rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun x' _ => Finset.sum_congr rfl fun x _ => by ring
      _ ≤ (∑ x, u x ^ 2 * c1 + ∑ x', u x' ^ 2 * ((S.L : ℝ) ^ 4 * c2)) / 2 := by
          gcongr with x _ x' _
          · exact hrow x
          · exact hcol x'
      _ = (c1 + (S.L : ℝ) ^ 4 * c2) / 2 * ∑ x, u x ^ 2 := by
          rw [← Finset.sum_mul, ← Finset.sum_mul]; ring
  have hu2 : ∀ x, u x ^ 2 = hs2 (g x) := fun x => hs_sq _
  calc |(∑ x, ∑ x', ((∑ c, (hL S hM hR c x - hL S hM hR c x') ^ 2 : ℝ) : ℂ) *
        ntr ((kP S x x' (g x'))ᴴ * g x)).re|
      ≤ ‖∑ x, ∑ x', ((∑ c, (hL S hM hR c x - hL S hM hR c x') ^ 2 : ℝ) : ℂ) *
        ntr ((kP S x x' (g x'))ᴴ * g x)‖ := Complex.abs_re_le_norm _
    _ ≤ ∑ x, ∑ x', Kc * (K x x' * u x' * u x) :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => (norm_sum_le _ _).trans
          (Finset.sum_le_sum fun x' _ => hpt x x'))
    _ = Kc * ∑ x, ∑ x', K x x' * u x' * u x := by simp only [Finset.mul_sum]
    _ ≤ Kc * ((c1 + (S.L : ℝ) ^ 4 * c2) / 2 * ∑ x, u x ^ 2) := mul_le_mul_of_nonneg_left hschur hKc
    _ = _ := by simp only [hu2, Kc, c1, c2]; ring

end PartitionUnity

namespace PartitionUnity

open SequenceOperators SFBox
open Lattices SeqDom SFBounds SFLocal Blocks SmallFieldBlocks SmallFieldDecay SmallFieldCoercivity
open scoped Matrix

variable {S : Lattices.SeqDom} {hM : 12 ≤ S.L ^ S.mM} {hR : 12 * S.L ≤ S.R} {N : ℕ}

local notation "NF" => SequenceAverages.N0 S
local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "RMS" => ((S.R * S.L ^ S.mM : ℕ) : ℝ)

/-- The constant of the bound of the error of the localisation of `‖Pg‖²`. -/
def CerrP (S : Lattices.SeqDom) (N : ℕ) (δ : ℝ) : ℝ :=
  KP S.L / ((S.L : ℝ) ^ S.mM) ^ 2 * (CPk S N δ * (16 / (7 / 32 * thetaB S N δ) ^ 2 + 32) *
    (((S.toContSeq).c1 (1 / 2) (7 / 32 * thetaB S N δ) +
      (S.L : ℝ) ^ 4 * (S.toContSeq).c1 (1 / 2) (7 / 32 * thetaB S N δ / 2)) / 2))

/-- The total coefficient of the errors of the localisation, for the parameter `ε` of `ims_P1`. -/
def ThetaIMS (S : Lattices.SeqDom) (N : ℕ) (δ Cl ε : ℝ) : ℝ :=
  Cl * ε + (Cl + 1) * (384 * Cpu S.L ^ 2 * (S.L : ℝ) ^ 6 / ((S.L : ℝ) ^ S.mM) ^ 2 +
    1 / 2 * (3 * (S.L : ℝ) ^ 2 * KQ S.L S.mM)) * 2 ^ 12 + Cl / 2 * CerrP S N δ +
    Cl * ε⁻¹ * (384 * Cpu S.L ^ 2 * (S.L : ℝ) ^ 4 / ((S.L : ℝ) ^ S.mM) ^ 2) * 2 ^ 12

/-- The algebra of the conclusion of the localisation. -/
lemma ims_alg {F p g2 w Eg eQ eP cm SF SP N Cl ε Kg KQ CP Kc : ℝ} (hN : 0 < N) (hCl : 0 ≤ Cl) (hε0 : 0 < ε)
    (hε : ε ≤ 1) (hF : SF = F + Eg - 1 / 2 * eQ) (hsum : SF ≤ Cl * (SF - N * SP))
    (hpc : (1 - ε) * (p - 1 / 2 * eP) - ε⁻¹ * cm ≤ SP) (hEg : |Eg| ≤ Kg * w) (heQ : |eQ| ≤ KQ * w)
    (heP : |eP| ≤ CP * g2) (hcm : N * cm ≤ Kc * w) (hKg : 0 ≤ Kg) (hKQ : 0 ≤ KQ) (hCP : 0 ≤ CP) (hKc : 0 ≤ Kc)
    (hg2 : N * g2 ≤ F) (hw : w ≤ 2 ^ 12 * F) (hpg : p ≤ g2) (hF0 : 0 ≤ F)
    (hΘ : Cl * ε + (Cl + 1) * (Kg + 1 / 2 * KQ) * 2 ^ 12 + Cl / 2 * CP + Cl * ε⁻¹ * Kc * 2 ^ 12 ≤ 1 / 2) :
    F ≤ 2 * Cl * (F - N * p) := by
  have hεi : 0 ≤ ε⁻¹ := inv_nonneg.2 hε0.le
  have hpF : N * p ≤ F := (mul_le_mul_of_nonneg_left hpg hN.le).trans hg2
  have a2 : F ≤ SF + |Eg| + 1 / 2 * |eQ| := by
    rw [hF]; have := neg_abs_le Eg; have := le_abs_self eQ; linarith
  have a1 : SF ≤ F + |Eg| + 1 / 2 * |eQ| := by
    rw [hF]; have := le_abs_self Eg; have := neg_abs_le eQ; linarith
  have a3 : (1 - ε) * (1 / 2 * eP) ≤ 1 / 2 * |eP| := by
    have h1 : (1 - ε) * (1 / 2 * eP) ≤ (1 - ε) * (1 / 2 * |eP|) :=
      mul_le_mul_of_nonneg_left (by have := le_abs_self eP; linarith) (by linarith)
    have h2 : (1 - ε) * (1 / 2 * |eP|) ≤ 1 / 2 * |eP| := by
      have := abs_nonneg eP; nlinarith
    linarith
  have a4 : (1 - ε) * p - 1 / 2 * |eP| - ε⁻¹ * cm ≤ SP := by
    have : (1 - ε) * (p - 1 / 2 * eP) = (1 - ε) * p - (1 - ε) * (1 / 2 * eP) := by ring
    linarith
  have a5 : N * ((1 - ε) * p) - 1 / 2 * (N * |eP|) - ε⁻¹ * (N * cm) ≤ N * SP := by
    have := mul_le_mul_of_nonneg_left a4 hN.le
    have e : N * ((1 - ε) * p - 1 / 2 * |eP| - ε⁻¹ * cm) =
        N * ((1 - ε) * p) - 1 / 2 * (N * |eP|) - ε⁻¹ * (N * cm) := by ring
    linarith
  have b1 : N * |eP| ≤ CP * F := by
    calc N * |eP| ≤ N * (CP * g2) := mul_le_mul_of_nonneg_left heP hN.le
      _ = CP * (N * g2) := by ring
      _ ≤ CP * F := mul_le_mul_of_nonneg_left hg2 hCP
  have b2 : |Eg| ≤ Kg * 2 ^ 12 * F := hEg.trans (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hw hKg)
  have b3 : |eQ| ≤ KQ * 2 ^ 12 * F := heQ.trans (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hw hKQ)
  have b4 : N * cm ≤ Kc * 2 ^ 12 * F := hcm.trans (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hw hKc)
  have c2 : SF - N * SP ≤ F + |Eg| + 1 / 2 * |eQ| - (N * ((1 - ε) * p) - 1 / 2 * (N * |eP|) - ε⁻¹ * (N * cm)) := by
    linarith
  have c3 : Cl * (SF - N * SP) ≤ Cl * (F + |Eg| + 1 / 2 * |eQ| -
      (N * ((1 - ε) * p) - 1 / 2 * (N * |eP|) - ε⁻¹ * (N * cm))) := mul_le_mul_of_nonneg_left c2 hCl
  have e1 : Cl * (F + |Eg| + 1 / 2 * |eQ| - (N * ((1 - ε) * p) - 1 / 2 * (N * |eP|) - ε⁻¹ * (N * cm))) =
      Cl * (F - N * p) + Cl * ε * (N * p) + Cl / 2 * (N * |eP|) + Cl * ε⁻¹ * (N * cm) +
        Cl * (|Eg| + 1 / 2 * |eQ|) := by ring
  have d1 : Cl * ε * (N * p) ≤ Cl * ε * F := mul_le_mul_of_nonneg_left hpF (by positivity)
  have d2 : Cl / 2 * (N * |eP|) ≤ Cl / 2 * (CP * F) := mul_le_mul_of_nonneg_left b1 (by positivity)
  have d3 : Cl * ε⁻¹ * (N * cm) ≤ Cl * ε⁻¹ * (Kc * 2 ^ 12 * F) := mul_le_mul_of_nonneg_left b4 (by positivity)
  have d4 : (Cl + 1) * (|Eg| + 1 / 2 * |eQ|) ≤ (Cl + 1) * (Kg * 2 ^ 12 * F + 1 / 2 * (KQ * 2 ^ 12 * F)) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have hΘF := mul_le_mul_of_nonneg_right hΘ hF0
  have e2 : (Cl * ε + (Cl + 1) * (Kg + 1 / 2 * KQ) * 2 ^ 12 + Cl / 2 * CP + Cl * ε⁻¹ * Kc * 2 ^ 12) * F =
      Cl * ε * F + (Cl + 1) * (Kg * 2 ^ 12 * F + 1 / 2 * (KQ * 2 ^ 12 * F)) + Cl / 2 * (CP * F) +
        Cl * ε⁻¹ * (Kc * 2 ^ 12 * F) := by ring
  have e3 : (Cl + 1) * (|Eg| + 1 / 2 * |eQ|) = Cl * (|Eg| + 1 / 2 * |eQ|) + (|Eg| + 1 / 2 * |eQ|) := by ring
  have e4 : 2 * Cl * (F - N * p) = Cl * (F - N * p) + Cl * (F - N * p) := by ring
  -- `F ≤ Cl(F - Np) + ΘF ≤ Cl(F - Np) + ½F`
  have f1 : F ≤ Cl * (F - N * p) + 1 / 2 * F := by linarith
  have f2 : F ≤ 2 * Cl * (F - N * p) := by linarith
  exact f2

/-- **The conclusion of the localisation**: if `⟨X^*, Δ^F_𝖺X⟩ ≤ C_l⟨X^*, Δ_𝖺(id)X⟩` for every `X = h_□A` and the
coefficient `Θ` of the errors is at most `½`, then `⟨A^*, Δ^F_𝖺A⟩ ≤ 2C_l⟨A^*, Δ_𝖺(id)A⟩`. -/
theorem ims_conclusion [NeZero N] {δ : ℝ} (H : ScalarHyp (N := N) S (X0 S) 0 (W1 S) 0 Set.univ δ)
    (hRMb : (S.toContSeq).r1 (1 / 2) (1 / 32 * δ) ≤ RMS) (hRMs4 : 32 * Real.log S.L / (1 / 4 * δ) ≤ RMS)
    (hsmallT : CTd S N δ 0 0 * (S.toContSeq).c1 (1 / 2) (1 / 32 * δ) ≤ gammaB N / 4)
    (hRMθs : 32 * Real.log S.L / (thetaB S N δ / 2) ≤ RMS)
    (hRMθc : (S.toContSeq).r1 (1 / 2) (7 / 16 * thetaB S N δ) ≤ RMS)
    (hRMsum : (S.toContSeq).r1 (1 / 2) (7 / 32 * thetaB S N δ) ≤ RMS)
    (hRMsum2 : (S.toContSeq).r1 (1 / 2) (7 / 32 * thetaB S N δ / 2) ≤ RMS)
    (hRMss : 32 * Real.log S.L / (2 * (7 / 32 * thetaB S N δ)) ≤ RMS)
    (hR1 : 1 ≤ S.R) (hRM2 : 2 * (S.L : ℝ) ≤ RMS) (hRMn : 2 * S.L ≤ S.R * S.L ^ S.mM)
    (A : Fin 4 → Site NF → Mat) {Cl ε : ℝ} (hCl : 0 ≤ Cl) (hε0 : 0 < ε) (hε : ε ≤ 1)
    (hloc : ∀ q, formF S (locA S (hL S hM hR q) A) ≤ Cl * formA S (locA S (hL S hM hR q) A))
    (hΘ : ThetaIMS S N δ Cl ε ≤ 1 / 2) :
    formF S A ≤ 2 * Cl * formA S A := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hL0 : (0 : ℝ) < S.L := by exact_mod_cast S.Lpos
  have hRML : (S.L : ℝ) < RMS := by linarith
  have hF : ∑ c, formF S (locA S (hL S hM hR c) A) = formF S A +
      (∑ μ, ∑ x, ∑ ν, (∑ c, (hL S hM hR c (x + CoreLean.unit NF ν) - hL S hM hR c x) ^ 2) *
        (inner ℂ (emb (N := N) (A μ (x + CoreLean.unit NF ν))) (emb (A μ x))).re) -
      1 / 2 * errQ S Finset.univ (hL S hM hR) A := by
    simp only [formF, Finset.sum_add_distrib]
    rw [ims_grad S Finset.univ (hL S hM hR) (hL_sum S hM hR) A,
      ims_Q S Finset.univ (hL S hM hR) (hL_sum S hM hR) A]
    ring
  have hsum : ∑ c, formF S (locA S (hL S hM hR c) A) ≤ Cl * (∑ c, formF S (locA S (hL S hM hR c) A) -
      N * ∑ c, ∑ x, hs2 (Pop S (X0 S) (W1 S) Set.univ (Ds1L a1 (cfgX (X0 S)) (locA S (hL S hM hR c) A)) x)) := by
    refine (Finset.sum_le_sum fun c _ => hloc c).trans (le_of_eq ?_)
    unfold formA
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hPc := ims_P1 S Finset.univ (hL S hM hR) (hL_sum S hM hR) A hε0 hε
  have hEg := err_grad_le S hM hR hRML A
  have heQ := errQ_le S hM hR hRM2 A
  have heP := errP_le hM hR H hRMb hRMs4 hsmallT hRMθs hRMθc hRMsum hRMsum2 hRMss hR1 (Ds1L a1 (cfgX (X0 S)) A)
  have hcm := commA_le S hM hR hRML A
  have hcomp := sf_components S hRMn A
  have hcurl : 0 ≤ curlE S A := by
    unfold curlE; exact Finset.sum_nonneg fun x _ => by
      have : 0 ≤ ∑ μ, ∑ ν, hs2 ((A ν (x + CoreLean.unit NF μ) - A ν x) - (A μ (x + CoreLean.unit NF ν) - A μ x)) :=
        Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => hs2_nonneg _
      positivity
  have hgi := grad_identity S A
  have hQ0 : 0 ≤ Qnorm S A := by unfold Qnorm; exact Finset.sum_nonneg fun _ _ => by positivity
  have hg20 : 0 ≤ ∑ x, hs2 (Ds1L a1 (cfgX (X0 S)) A x) := Finset.sum_nonneg fun x _ => hs2_nonneg _
  have hNg : (N : ℝ) * ∑ x, hs2 (Ds1L a1 (cfgX (X0 S)) A x) ≤ gradNorm S A := by
    rw [hgi]; have := mul_nonneg hN.le hcurl; linarith
  have hg2 : (N : ℝ) * ∑ x, hs2 (Ds1L a1 (cfgX (X0 S)) A x) ≤ formF S A := by
    unfold formF; linarith
  have hw : SFBounds.wnorm S A ≤ 2 ^ 12 * formF S A := by
    have hG0 : 0 ≤ gradNorm S A := le_trans (mul_nonneg hN.le hg20) hNg
    unfold formF; linarith
  have hF0 : 0 ≤ formF S A := le_trans (mul_nonneg hN.le hg20) hg2
  have hCP : 0 ≤ CerrP S N δ := by
    have hθ : 0 < 7 / 32 * thetaB S N δ := by have := H.thetaB_pos (N := N); positivity
    have hc1 : 0 ≤ (S.toContSeq).c1 (1 / 2) (7 / 32 * thetaB S N δ) := by unfold Summation.ContSeq.c1; positivity
    have hc2 : 0 ≤ (S.toContSeq).c1 (1 / 2) (7 / 32 * thetaB S N δ / 2) := by
      unfold Summation.ContSeq.c1; positivity
    have hCPk : 0 ≤ CPk S N δ := by
      have h1 : 0 ≤ (S.toContSeq).c1 (1 / 2) (thetaB S N δ) := by unfold Summation.ContSeq.c1; positivity
      have h2 : 0 ≤ (S.toContSeq).c1 (1 / 2) (7 / 16 * thetaB S N δ) := by unfold Summation.ContSeq.c1; positivity
      unfold CPk gammaB; positivity
    have := KP_nonneg S.L
    unfold CerrP; positivity
  have hKg : 0 ≤ 384 * Cpu S.L ^ 2 * (S.L : ℝ) ^ 6 / ((S.L : ℝ) ^ S.mM) ^ 2 := by
    have := Cpu_nonneg S.L; positivity
  have hKQ : 0 ≤ 3 * (S.L : ℝ) ^ 2 * KQ S.L S.mM := by have := KQ_nonneg S.L S.mM; positivity
  have hKc : 0 ≤ 384 * Cpu S.L ^ 2 * (S.L : ℝ) ^ 4 / ((S.L : ℝ) ^ S.mM) ^ 2 := by
    have := Cpu_nonneg S.L; positivity
  unfold formA
  exact ims_alg hN hCl hε0 hε hF hsum hPc hEg heQ heP hcm hKg hKQ hCP hKc hg2 hw
    (Pop_contr S Set.univ _) hF0 hΘ

end PartitionUnity

end CoreLean

end
