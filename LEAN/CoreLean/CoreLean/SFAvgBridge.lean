/-
Bridge (B2) of `thm:small-field` (BALABAN_CORE.tex, `lem:block-average-transports`): the composite average of
`0`-forms `Q'_j(𝐔)` of the concrete layer (`SequenceOperators.Qpcomp`) at a site `y ∈ a_jℤ⁴` of the fine lattice is
the average `avgW` of the fine model with the composite transports `W_𝐔(y, x)` of the chain.

* `Wlev`: `W_𝐔(y, x) = WB(p)`, `p` the digits of the offset `psi(x)` of `x` in `B^j(y)` (`ptEquiv`);
* `qpcomp_avg`: `Q'_j(𝐔)λ(y/a_j) = avgW(W_𝐔)(y)λ` (`block_composite`, `ptB_closed`, `Dg_ptEquiv`, `psi_phi`).
-/
import CoreLean.SFConstraintBound
import CoreLean.BlockTransportsClose
import CoreLean.SequenceOperators

open Finset
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace CoreLean
namespace LevelsBridge

open MultiscaleAverages LatticePaths AxialStraightLattice RelativeAverage AverageHolo LatticeKappa BoxGeometry

/-- **The data of the levels at `e^{iX}`** (from `levels_expX`): fields `A'_l` with
`M^l(e^{iX}) = e^{iA'_l}` on the regions and `‖A'_l‖ ≤ K_ot'L^{-(n-l)}` on the boxes of the bonds of the next level. -/
theorem levels_data (h m k : ℕ) (G : GaugeGroup N) (hGc : IsClosed G.mats) (hN : 1 ≤ N) (hh : 1 ≤ h) :
    ∃ c Ko : ℝ, 0 < c ∧ 0 ≤ Ko ∧ ∀ (nl : ℕ) (μ : Fin 4), nl ≤ k → (∀ l, 4 * h + 4 ≤ nn h m k l) →
      ∀ (c0 : Fin 4 → ℤ) (X : Fin 4 → Site (nn h m k 0) → Matrix (Fin N) (Fin N) ℂ) (t' : ℝ),
      (∀ ρ x, Lat (Lz h) 0 x → Rg h nl μ 0 x → Rg h nl μ 0 (x + Lz h ^ 0 • Pi.single ρ 1) →
        ‖X ρ (img h (baseOf h m k c0 nl 0) 0 x)‖ ≤ t' * ((((2 * h + 1 : ℕ) : ℝ)) ^ nl)⁻¹) →
      0 ≤ t' → t' ≤ c →
      ∃ A' : ∀ l, Fin 4 → Site (nn h m k l) → Matrix (Fin N) (Fin N) ℂ,
        (∀ l, l < nl → ∀ ν x, Lat (Lz h) l x → Rg h nl μ l x → Rg h nl μ l (x + Lz h ^ l • Pi.single ν 1) →
          Mpow h m k (fun _ => True) (fun W => LogM (W : Matrix (Fin N) (Fin N) ℂ)) (moveC oneC X) l ν
            (img h (baseOf h m k c0 nl l) l x) = moveC oneC (A' l) ν (img h (baseOf h m k c0 nl l) l x)) ∧
        (∀ l, l < nl → ∀ ρ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x →
          Rg h nl μ (l + 1) (x + Lz h ^ (l + 1) • Pi.single ρ 1) →
          ∀ ν z, BoxBond (img h (baseOf h m k c0 nl l) l x) h ρ ν z →
            ‖A' l ν z‖ ≤ Ko * t' * ((((2 * h + 1 : ℕ) : ℝ)) ^ (nl - l))⁻¹) := by
  classical
  obtain ⟨c, Ko, hc, hKo, hlev⟩ := levels_expX h m k G hGc hN hh
  refine ⟨c, Ko, hc, hKo, ?_⟩
  intro nl μ hnl hn c0 X t' hX ht0 htc
  set Lr : ℝ := ((2 * h + 1 : ℕ) : ℝ)
  set a₁ : ℕ → ℝ := fun l => Ko * t' * (Lr ^ (nl - l))⁻¹
  set base := baseOf h m k c0 nl
  set V : ∀ l, Config N (nn h m k l) := fun l =>
    Mpow h m k (fun _ => True) (fun W => LogM (W : Matrix (Fin N) (Fin N) ℂ)) (moveC oneC X) l
  set A'f : ∀ l, Fin 4 → Site (nn h m k l) → Matrix (Fin N) (Fin N) ℂ := fun l ν z =>
    if hz : ∃ A : Matrix (Fin N) (Fin N) ℂ, V l ν z = expU (Complex.I • A) ∧ ‖A‖ ≤ a₁ l then hz.choose else 0
  have hreg : ∀ l, l ≤ nl → ∀ ν x, Lat (Lz h) l x → Rg h nl μ l x → Rg h nl μ l (x + Lz h ^ l • Pi.single ν 1) →
      V l ν (img h (base l) l x) = expU (Complex.I • A'f l ν (img h (base l) l x)) ∧
        ‖A'f l ν (img h (base l) l x)‖ ≤ a₁ l := by
    intro l hl ν x hx1 hx2 hx3
    have hex : ∃ A : Matrix (Fin N) (Fin N) ℂ, V l ν (img h (base l) l x) = expU (Complex.I • A) ∧ ‖A‖ ≤ a₁ l :=
      hlev nl μ hnl hn c0 X t' hX ht0 htc l hl ν x hx1 hx2 hx3
    simp only [A'f, dif_pos hex]
    exact hex.choose_spec
  refine ⟨A'f, fun l hl ν x hx1 hx2 hx3 => ?_, fun l hl ρ x hx q0 q1 ν z hb => ?_⟩
  · change V l ν (img h (base l) l x) = _
    rw [(hreg l hl.le ν x hx1 hx2 hx3).1]
    simp [moveC, oneC]
  · obtain ⟨x', hx', r0, r1, rfl⟩ := box_site (hn l) (base l) hx q0 q1 hb
    exact (hreg l hl.le ν x' hx' r0 r1).2

end LevelsBridge

namespace SFBounds

open Lattices SeqDom Blocks SmallFieldBlocks SFBox SFBox.SeqDomBox SmallFieldDecay SmallFieldCoercivity
  PartitionUnity RegularAverages AxialStraightLattice BoxGeometry

variable (S : SeqDom) {N : ℕ}

local notation "NF" => SequenceAverages.N0 S
local notation "RMS" => ((S.R * S.L ^ S.mM : ℕ) : ℝ)
set_option quotPrecheck false in
local notation "jj" => (S.toDomSeq).sc

/-- **The composite transports of `Q'_j(𝐔)` at a site of `a_jℤ⁴`**: `W_𝐔(y, x) = WB(p)`, `p` the digits of the offset
`psi(x) ∈ [0, a_j)⁴` of `x`. -/
def Wlev (U : Config N NF) (j : ℕ) (y : Site NF) (hlat : InLat S.L j y) (x : Site NF) :
    (Matrix (Fin N) (Fin N) ℂ)ˣ :=
  RelativeAverage.WB (SequenceAverages.hS S) (MultiscaleAverages.nn (SequenceAverages.hS S) S.mT S.k)
    (LevelsBridge.baseOf (SequenceAverages.hS S) S.mT S.k (c0Of S hlat) j)
    (fun l => MultiscaleAverages.Mpow (SequenceAverages.hS S) S.mT S.k (fun _ => True)
      (fun W => LogM (W : Matrix (Fin N) (Fin N) ℂ)) U l) j 0
    ((RelativeAverage.ptEquiv (SequenceAverages.hS S) j).symm
      (fun σ => ⟨SmallFieldBlocks.psi S.toDomSeq j y x σ % (2 * SequenceAverages.hS S + 1) ^ j, Nat.mod_lt _ (by positivity)⟩))

/-- **`Q'_j(𝐔)` as the average of the fine model** (bridge (B2)): at `y ∈ a_jℤ⁴`, `j ≤ k`,
`(Q'_j(𝐔)λ)(y/a_j) = a_j^{-4}Σ_{o ∈ [0, a_j)⁴}Ad_{W_𝐔(y, φ(o))}λ(φ(o))`, `φ(o) = y + o - h_j`. -/
theorem qpcomp_avg (U : Config N NF) (lam : Site NF → Matrix (Fin N) (Fin N) ℂ) {j : ℕ} (hj : j ≤ S.k)
    {y : Site NF} (hlat : InLat S.L j y) :
    SequenceOperators.Qpcomp (SequenceAverages.hS S) S.mT S.k (fun _ => True)
        (fun W => LogM (W : Matrix (Fin N) (Fin N) ℂ)) U j lam
        (LevelsBridge.baseOf (SequenceAverages.hS S) S.mT S.k (c0Of S hlat) j j) =
      (((DiscretePoincare.box 4 (S.L ^ j)).card : ℝ) : ℂ)⁻¹ •
        ∑ o ∈ DiscretePoincare.box 4 (S.L ^ j),
          Ad (Wlev S U j y hlat (SmallFieldBlocks.phi S.toDomSeq j y o)) (lam (SmallFieldBlocks.phi S.toDomSeq j y o)) := by
  set h := SequenceAverages.hS S
  set base := LevelsBridge.baseOf h S.mT S.k (c0Of S hlat) j
  set V : ∀ l, Config N (MultiscaleAverages.nn h S.mT S.k l) := fun l =>
    MultiscaleAverages.Mpow h S.mT S.k (fun _ => True) (fun W => LogM (W : Matrix (Fin N) (Fin N) ℂ)) U l
  set lm : ∀ l, Site (MultiscaleAverages.nn h S.mT S.k l) → Matrix (Fin N) (Fin N) ℂ := fun l =>
    SequenceOperators.Qpcomp h S.mT S.k (fun _ => True) (fun W => LogM (W : Matrix (Fin N) (Fin N) ℂ)) U l lam
  have hlam : ∀ l, l < j → ∀ z, Lat (Lz h) (l + 1) z → RelativeAverage.Rg h j 0 (l + 1) z →
      lm (l + 1) (img h (base (l + 1)) (l + 1) z) = RelativeAverage.blockAvg (V l) (lm l) (img h (base l) l z) h := by
    intro l hl z hz _
    have hup := LevelsBridge.up_img h S.mT S.k base l (by omega)
      (LevelsBridge.base_up h S.mT S.k (c0Of S hlat) j l hl (by omega)) z hz
    simp only [lm, SequenceOperators.Qpcomp_succ, LinearMap.comp_apply, SequenceOperators.QpStep_apply, hup]
    rfl
  have H := RelativeAverage.block_composite h j 0 (MultiscaleAverages.nn h S.mT S.k) base V lm hlam j le_rfl 0
    (fun σ => dvd_zero _) (RB_top S j 0).2.1
  rw [img_top] at H
  have hl0 : ∀ z : Fin 4 → ℤ, lm 0 (img h (base 0) 0 z) = lam (y + fun σ => ((z σ : ℤ) : ZMod NF)) := fun z => by
    simp only [lm, SequenceOperators.Qpcomp, LinearMap.id_apply]
    rw [show base 0 = y from baseOf_zero S hlat, img_zero]
  simp only [hl0] at H
  change lm j (base j) = _
  rw [H]
  have hpow : (2 * h + 1) ^ j = S.L ^ j := by rw [← SequenceAverages.L_eq S]
  have hn : 0 < S.L ^ j := pow_pos S.Lpos _
  congr 1
  · rw [DiscretePoincare.card_box]
    have hLc : ((2 * h + 1 : ℕ) : ℂ) = (S.L : ℂ) := by rw [← SequenceAverages.L_eq S]
    rw [hLc]; push_cast; ring
  · have e2 := sum_fin_congr hpow (fun o => Ad (Wlev S U j y hlat (SmallFieldBlocks.phi S.toDomSeq j y o))
      (lam (SmallFieldBlocks.phi S.toDomSeq j y o)))
    try simp only at e2
    rw [← sum_fin_box (S.L ^ j) hn, ← e2, ← Equiv.sum_comp (RelativeAverage.ptEquiv h j)]
    refine Finset.sum_congr rfl fun p _ => ?_
    have hbox : (fun σ => ((RelativeAverage.ptEquiv h j p σ : ℕ))) ∈ DiscretePoincare.box 4 (S.L ^ j) := by
      simp only [DiscretePoincare.box, Fintype.mem_piFinset, mem_range]
      intro σ; rw [← hpow]; exact (RelativeAverage.ptEquiv h j p σ).isLt
    have hphi : SmallFieldBlocks.phi S.toDomSeq j y (fun σ => ((RelativeAverage.ptEquiv h j p σ : ℕ))) =
        y + fun σ => ((RelativeAverage.ptB h j 0 p σ : ℤ) : ZMod NF) := by
      funext σ
      rw [RelativeAverage.ptB_closed]
      simp only [Pi.add_apply, Pi.sub_apply, zero_add]
      rw [RelativeAverage.Dg_ptEquiv]
      rw [show Hw h j 0 = (half S.L j : ℤ) from Hw_zero S j]
      simp only [SmallFieldBlocks.phi, Pi.add_apply]
      push_cast; rfl
    have hW : Wlev S U j y hlat (SmallFieldBlocks.phi S.toDomSeq j y (fun σ => ((RelativeAverage.ptEquiv h j p σ : ℕ)))) =
        RelativeAverage.WB h (MultiscaleAverages.nn h S.mT S.k) base V j 0 p := by
      have hfun : (fun σ => (⟨SmallFieldBlocks.psi S.toDomSeq j y (SmallFieldBlocks.phi S.toDomSeq j y
          (fun σ => ((RelativeAverage.ptEquiv h j p σ : ℕ)))) σ % (2 * h + 1) ^ j, Nat.mod_lt _ (by positivity)⟩ :
            Fin ((2 * h + 1) ^ j))) = RelativeAverage.ptEquiv h j p := by
        funext σ
        ext
        simp only [Fin.val_mk]
        rw [SmallFieldBlocks.psi_phi (S := S.toDomSeq) j hj y hbox]
        exact Nat.mod_eq_of_lt (RelativeAverage.ptEquiv h j p σ).isLt
      unfold Wlev
      rw [hfun, Equiv.symm_apply_apply]
    rw [hW, hphi]

/-- **The region of a point of `𝐁` lies in `Ω_{j-1}`**: for `y ∈ 𝐁`, `j = j(y)`, and `x` in the region of the level
`0` of `j` levels, the scale of `y + x` is at least `j - 1` (`sep'`, `|x|_∞ ≤ 2a_j`, `RM ≥ 2L`). -/
theorem detB_region_scale (hRM : 2 * (S.L : ℝ) ≤ RMS) {y : Site NF} (hy : y ∈ detB S.toDomSeq) {μ : Fin 4}
    (x : Fin 4 → ℤ) (hx : RelativeAverage.Rg (SequenceAverages.hS S) (jj y) μ 0 x) :
    jj y ≤ (S.toDomSeq).sc (y + fun σ => ((x σ : ℤ) : ZMod NF)) + 1 := by
  set j := jj y
  set p : Site NF := y + fun σ => ((x σ : ℤ) : ZMod NF)
  by_contra hc
  push_neg at hc
  have hpn : p ∉ (S.toDomSeq).Ω (j - 1) := fun h => by
    have := ((S.toDomSeq).mem_iff p _).1 h; omega
  have hye : y ∈ (S.toDomSeq).Ω (j - 1 + 1) := by
    rw [show j - 1 + 1 = j by omega]; exact (S.toDomSeq).mem_sc y
  have hs := (S.toDomSeq).sep' (j - 1) p hpn y hye
  have hRMd : (S.toDomSeq).RM = ((S.R * S.L ^ S.mM : ℕ) : ℝ) := rfl
  have hLd : (S.toDomSeq).L = S.L := rfl
  rw [hRMd, hLd] at hs
  have hh := half_le_pow S j
  have hd : dinf p y ≤ 2 * S.L ^ j := by
    unfold dinf
    refine Finset.sup_le fun ν _ => ?_
    have e : p ν - y ν = ((x ν : ℤ) : ZMod NF) := by simp only [p, Pi.add_apply]; ring
    rw [e]
    refine (cd_intCast_le (x ν)).trans ?_
    have h1 := hx ν
    rw [Hw_zero, Lz_hS] at h1
    simp only [or_self] at h1
    have hL : (0 : ℤ) ≤ (S.L : ℤ) ^ j := by positivity
    have hH : ((half S.L j : ℕ) : ℤ) ≤ ((S.L ^ j : ℕ) : ℤ) := by exact_mod_cast hh
    push_cast at hH
    have : (x ν).natAbs ≤ 2 * S.L ^ j := by
      have : |x ν| ≤ 2 * (S.L : ℤ) ^ j := by
        rw [abs_le]; split_ifs at h1 <;> constructor <;> linarith [h1.1, h1.2]
      have h2 : ((x ν).natAbs : ℤ) ≤ ((2 * S.L ^ j : ℕ) : ℤ) := by
        rw [Int.natCast_natAbs]; push_cast; exact this
      exact_mod_cast h2
    exact this
  have hd' : ((dinf p y : ℕ) : ℝ) ≤ 2 * (S.L : ℝ) ^ j := by
    have := Nat.cast_le (α := ℝ) |>.2 hd; push_cast at this; exact this
  have hj : (S.L : ℝ) ^ j = S.L * (S.L : ℝ) ^ (j - 1) := by rw [← pow_succ']; congr 1; omega
  have h0 : (0 : ℝ) < (S.L : ℝ) ^ (j - 1) := by have := S.Lpos; positivity
  have h1 : 2 * (S.L : ℝ) * (S.L : ℝ) ^ (j - 1) ≤ ((S.R * S.L ^ S.mM : ℕ) : ℝ) * (S.L : ℝ) ^ (j - 1) :=
    mul_le_mul_of_nonneg_right hRM h0.le
  rw [hj] at hd'
  linarith

/-- **The field on the region of a point of `𝐁`**: `‖X_ρ(y + x)‖ ≤ α₁La_j^{-1}` (as `region_field`). -/
theorem detB_region_field (hRM : 2 * (S.L : ℝ) ≤ RMS) {y : Site NF} (hy : y ∈ detB S.toDomSeq) {μ : Fin 4}
    {X : Fin 4 → Site NF → Matrix (Fin N) (Fin N) ℂ} {α₁ : ℝ} (hX : RegField S X α₁) (hα0 : 0 ≤ α₁) (ρ : Fin 4)
    (x : Fin 4 → ℤ) (hx : RelativeAverage.Rg (SequenceAverages.hS S) (jj y) μ 0 x)
    (hx' : RelativeAverage.Rg (SequenceAverages.hS S) (jj y) μ 0 (x + Lz (SequenceAverages.hS S) ^ 0 • Pi.single ρ 1)) :
    ‖X ρ (y + fun σ => ((x σ : ℤ) : ZMod NF))‖ ≤ α₁ * S.L * ((S.L : ℝ) ^ jj y)⁻¹ := by
  have hL1 : (1 : ℝ) ≤ S.L := by exact_mod_cast S.Lpos
  set j := jj y
  set z : Site NF := y + fun σ => ((x σ : ℤ) : ZMod NF)
  have hz' : (y + fun σ => ((((x + Lz (SequenceAverages.hS S) ^ 0 • Pi.single ρ 1 : Fin 4 → ℤ)) σ : ℤ) : ZMod NF)) =
      z + CoreLean.unit NF ρ := by
    funext σ
    simp only [z, pow_zero, one_smul, Pi.add_apply, CoreLean.unit]
    by_cases hσ : σ = ρ
    · subst hσ; simp; ring
    · simp [Pi.single_eq_of_ne hσ]
  have h1 : j ≤ (S.toDomSeq).sc z + 1 := detB_region_scale S hRM hy x hx
  have h2 := detB_region_scale S hRM hy _ hx'
  rw [hz'] at h2
  have hm1 : z ∈ (S.toDomSeq).Ω (j - 1) := S.toDomSeq.Ω_anti (by omega) (S.toDomSeq.mem_sc z)
  have hm2 : z + CoreLean.unit NF ρ ∈ (S.toDomSeq).Ω (j - 1) :=
    S.toDomSeq.Ω_anti (by omega) (S.toDomSeq.mem_sc _)
  have h := hX.hA (j - 1) z ρ hm1 hm2
  have hp : ((S.L : ℝ) ^ (j - 1))⁻¹ ≤ S.L * ((S.L : ℝ) ^ j)⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), ← div_eq_inv_mul, div_le_iff₀ (by positivity)]
    rw [show (S.L : ℝ) * (S.L : ℝ) ^ (j - 1) = (S.L : ℝ) ^ (j - 1 + 1) by ring]
    exact pow_le_pow_right₀ hL1 (by omega)
  calc ‖X ρ z‖ ≤ α₁ * ((S.L : ℝ) ^ (j - 1))⁻¹ := h
    _ ≤ α₁ * (S.L * ((S.L : ℝ) ^ j)⁻¹) := mul_le_mul_of_nonneg_left hp hα0
    _ = _ := by ring

open Classical in
/-- **The transports of the averages of the fine model at `𝐔`**: `W_𝐔(y, x) = Wlev` at the scale `j(y)`. -/
def Wf (U : Config N NF) (y x : Site NF) : (Matrix (Fin N) (Fin N) ℂ)ˣ :=
  if h : InLat S.L (jj y) y then Wlev S U (jj y) y h x else 1

/-- **`Q'_{j(y)}(𝐔)` at a point of `𝐁` is `avgW` with the transports `W_𝐔`** (bridge (B2)). -/
theorem qpcomp_avgW (U : Config N NF) (lam : Site NF → Matrix (Fin N) (Fin N) ℂ) {y : Site NF}
    (hy : y ∈ detB S.toDomSeq) :
    SequenceOperators.Qpcomp (SequenceAverages.hS S) S.mT S.k (fun _ => True)
        (fun W => LogM (W : Matrix (Fin N) (Fin N) ℂ)) U (jj y) lam (SequenceAverages.crd S (jj y) (S.ef y)) =
      avgW S.toDomSeq (Wf S U) y lam := by
  obtain ⟨hlat, hjk, -⟩ := detB_facts S hy
  rw [crd_ef S hjk hlat, qpcomp_avg S U lam hjk hlat]
  unfold avgW Wf
  simp only [dif_pos hlat]
  rfl

/-- **The bounds of the transports `W_𝐔` of the fine model** (bridge (B2), `lem:block-average-transports`): for a
regular field `X` with `α₁L, K_oα₁L ≤ c` and `2CK_oα₁L ≤ log 2`, the transports `W_𝐔` at `𝐔 = e^{iX}` satisfy
`WBound` (`|Ad_W^{±1}Z| ≤ 2√N|Z|`) and `|Ad_W Z - Z| ≤ √N(e^{C'K_oα₁L/2} - 1)|Z|` on the blocks of the points of `𝐁`
(`levels_data`, `block_transports_bound`, `block_transports_close`). -/
theorem Wf_bounds (G : GaugeGroup N) (hGc : IsClosed G.mats) (hN : 1 ≤ N) :
    ∃ c Ko C C' : ℝ, 0 < c ∧ 0 ≤ Ko ∧ 0 ≤ C ∧ 0 ≤ C' ∧
      ∀ (hRM : 2 * (S.L : ℝ) ≤ RMS)
        (hn : ∀ l, 4 * SequenceAverages.hS S + 4 ≤ MultiscaleAverages.nn (SequenceAverages.hS S) S.mT S.k l)
        {X : Fin 4 → Site NF → Matrix (Fin N) (Fin N) ℂ} {α₁ : ℝ} (hX : RegField S X α₁) (hα0 : 0 ≤ α₁)
        (hαc : α₁ * S.L ≤ c) (hKαc : Ko * (α₁ * S.L) ≤ c) (hlog : 2 * C * (Ko * (α₁ * S.L)) ≤ Real.log 2),
      WBound S (Wf S (cfgX X)) ∧
        ∀ y ∈ detB S.toDomSeq, ∀ x ∈ Blk S.toDomSeq (jj y) y, ∀ Z : Matrix (Fin N) (Fin N) ℂ,
          hs (Ad (Wf S (cfgX X) y x) Z - Z) ≤
            Real.sqrt N * (Real.exp (C' * (Ko * (α₁ * S.L)) / 2) - 1) * hs Z := by
  set h := SequenceAverages.hS S
  have hh := one_le_hS S S.three_le_L
  obtain ⟨c1, Ko, hc1, hKo, hlevd⟩ := LevelsBridge.levels_data h S.mT S.k G hGc hN hh
  obtain ⟨c2, C, hc2, hC, hbd⟩ := RelativeAverage.block_transports_bound (N := N) G hGc h hh
  obtain ⟨c3, C', hc3, hC', hcl⟩ := RelativeAverage.block_transports_close (N := N) h
  refine ⟨min c1 (min c2 c3), Ko, C, C', lt_min hc1 (lt_min hc2 hc3), hKo, hC, hC', ?_⟩
  intro hRM hn X α₁ hX hα0 hαc hKαc hlog
  have hN0 : 0 < N := by omega
  have hL3 : (3 : ℝ) ≤ (((2 * h + 1 : ℕ) : ℝ)) := by rw [Lr_hS]; exact_mod_cast S.three_le_L
  have hcfg : cfgX X = AverageHolo.moveC RelativeAverage.oneC X := by
    funext ρ z; simp [cfgX, AverageHolo.moveC, RelativeAverage.oneC]
  set t' : ℝ := α₁ * S.L
  have ht0 : 0 ≤ t' := by have : (0 : ℝ) ≤ S.L := Nat.cast_nonneg _; positivity
  have he0 : 0 ≤ Ko * t' := mul_nonneg hKo ht0
  -- the bounds at one point of `𝐁`, for every block point
  have key : ∀ y ∈ detB S.toDomSeq, ∀ x ∈ Blk S.toDomSeq (jj y) y, ∀ Z : Matrix (Fin N) (Fin N) ℂ,
      (‖Ad (Wf S (cfgX X) y x) Z‖ ≤ 2 * ‖Z‖ ∧ ‖Ad (Wf S (cfgX X) y x)⁻¹ Z‖ ≤ 2 * ‖Z‖) ∧
        ‖Ad (Wf S (cfgX X) y x) Z - Z‖ ≤ (Real.exp (C' * (Ko * t') / 2) - 1) * ‖Z‖ := by
    intro y hy x _ Z
    obtain ⟨hlat, hjk, -⟩ := detB_facts S hy
    set j := jj y
    set base := LevelsBridge.baseOf h S.mT S.k (c0Of S hlat) j
    obtain ⟨A', hVU, hdat⟩ := hlevd j 0 hjk hn (c0Of S hlat) X t'
      (fun ρ x' _ hx1 hx2 => by
        rw [baseOf_zero S hlat, img_zero, Lr_hS]
        exact detB_region_field S hRM hy hX hα0 ρ x' hx1 hx2)
      ht0 (hαc.trans (min_le_left _ _))
    set V : ∀ l, Config N (MultiscaleAverages.nn h S.mT S.k l) := fun l =>
      MultiscaleAverages.Mpow h S.mT S.k (fun _ => True) (fun W => LogM (W : Matrix (Fin N) (Fin N) ℂ)) (cfgX X) l
    have hVU' : ∀ l, l < j → ∀ ν x', Lat (Lz h) l x' → RelativeAverage.Rg h j 0 l x' →
        RelativeAverage.Rg h j 0 l (x' + Lz h ^ l • Pi.single ν 1) →
        V l ν (img h (base l) l x') = AverageHolo.moveC RelativeAverage.oneC (A' l) ν (img h (base l) l x') := by
      intro l hl ν x' h1 h2 h3
      simp only [V, hcfg]
      exact hVU l hl ν x' h1 h2 h3
    set p := (RelativeAverage.ptEquiv h j).symm
      (fun σ => ⟨SmallFieldBlocks.psi S.toDomSeq j y x σ % (2 * h + 1) ^ j, Nat.mod_lt _ (by positivity)⟩)
    have hW : Wf S (cfgX X) y x = RelativeAverage.WB h (MultiscaleAverages.nn h S.mT S.k) base V j 0 p := by
      unfold Wf; rw [dif_pos hlat]; rfl
    have hR0 := (RB_top S j 0).2.1
    have hb := hbd j 0 (MultiscaleAverages.nn h S.mT S.k) hn base (fun _ => RelativeAverage.oneC) V A'
      (fun _ => 0) (fun l => Ko * t' * ((((2 * h + 1 : ℕ) : ℝ)) ^ (j - l))⁻¹) (Ko * t')
      (fun _ _ _ => G.carrier.one_mem) hVU'
      (fun l hl ρ x' hx q0 q1 => ⟨fun μ' ν' z _ => by simp [LevelsBridge.plaq_oneC, RegularAverages.hs_zero'],
        hdat l hl ρ x' hx q0 q1⟩)
      (fun l _ => ⟨le_rfl, by positivity, hc2.le, le_rfl⟩) he0 (hKαc.trans ((min_le_right _ _).trans (min_le_left _ _)))
      (by linarith) j le_rfl 0 (fun σ => dvd_zero _) hR0 p Z
    have hc := hcl j 0 (MultiscaleAverages.nn h S.mT S.k) hn base V A'
      (fun l => Ko * t' * ((((2 * h + 1 : ℕ) : ℝ)) ^ (j - l))⁻¹) (Ko * t') hVU' hdat
      (fun l _ => ⟨by positivity, le_rfl⟩) he0 (hKαc.trans ((min_le_right _ _).trans (min_le_right _ _))) hL3
      j le_rfl 0 (fun σ => dvd_zero _) hR0 p Z
    rw [hW]
    exact ⟨hb, hc⟩
  refine ⟨fun y hy x hx Z => ?_, fun y hy x hx Z => ?_⟩
  · exact ⟨RelativeAverage.hs_Ad_of_op hN0 (fun Z => ((key y hy x hx Z).1).1) Z,
      RelativeAverage.hs_Ad_of_op hN0 (fun Z => ((key y hy x hx Z).1).2) Z⟩
  · have hd0 : 0 ≤ Real.exp (C' * (Ko * t') / 2) - 1 := by
      have : 0 ≤ C' * (Ko * t') / 2 := by positivity
      linarith [Real.add_one_le_exp (C' * (Ko * t') / 2)]
    calc hs (Ad (Wf S (cfgX X) y x) Z - Z) ≤ ‖Ad (Wf S (cfgX X) y x) Z - Z‖ := hs_le_opNorm hN0 _
      _ ≤ (Real.exp (C' * (Ko * t') / 2) - 1) * ‖Z‖ := (key y hy x hx Z).2
      _ ≤ (Real.exp (C' * (Ko * t') / 2) - 1) * (Real.sqrt N * hs Z) :=
          mul_le_mul_of_nonneg_left (opNorm_le_sqrt_mul_hs Z) hd0
      _ = _ := by ring

end SFBounds
end CoreLean

end
