/-
`lem:sf-vector-decay` of BALABAN_CORE.tex (`ed5cdfdcfc3e`), step (4) of "The complex field", in the fine model: the
region of the per-level framework for a bond of a layer and the field on it.

* `Lz_hS`, `Hw_zero`: `L = 2h + 1`, `H = (L^j - 1)/2` for the sequence.
* `region_scale`: a site `y + x` of the region of the level `0` of a bond `(j, y, μ)` of the layers has the scale
  at least `j - 1` (`box_scale_low` after writing `y + x = x' + te_μ`, `x' ∈ B^j(y)`, `0 ≤ t ≤ a_j`).
-/
import CoreLean.LevelsBridge
import CoreLean.SFVectorConj
import CoreLean.QTrivialBridge

open Finset
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace CoreLean
namespace SFBounds

open Lattices SeqDom Blocks SmallFieldBlocks SFBox SFBox.SeqDomBox SmallFieldDecay SmallFieldCoercivity
  SequenceOperators PartitionUnity RegularAverages AxialStraightLattice BoxGeometry

variable (S : SeqDom) {N : ℕ}

local notation "NF" => SequenceAverages.N0 S
local notation "RMS" => ((S.R * S.L ^ S.mM : ℕ) : ℝ)

lemma Lz_hS : Lz (SequenceAverages.hS S) = (S.L : ℤ) := by
  unfold Lz; rw [SequenceAverages.L_eq S]; push_cast; ring

lemma Hw_zero (j : ℕ) : Hw (SequenceAverages.hS S) j 0 = (half S.L j : ℤ) := by
  have h1 := two_Hw (SequenceAverages.hS S) j 0
  have h2 := two_half_add_one S.L_odd j
  rw [Lz_hS, pow_zero] at h1
  have h3 : (2 * half S.L j + 1 : ℤ) = (S.L : ℤ) ^ j := by exact_mod_cast h2
  omega

/-- **The region of a bond of a layer lies in `Ω_{j-1}`**: for `(j, y, μ) ∈ QB` and `x` in the region of the
level `0` of `j` levels, the scale of `y + x` is at least `j - 1`. -/
theorem region_scale (hRM : 2 * (S.L : ℝ) ≤ RMS) {j : ℕ} {y : Site NF} {μ : Fin 4} (hq : (j, y, μ) ∈ QB S)
    (x : Fin 4 → ℤ) (hx : RegularAverages.InR (SequenceAverages.hS S) j μ μ 0 x) :
    j ≤ (S.toDomSeq).sc (y + fun σ => ((x σ : ℤ) : ZMod NF)) + 1 := by
  have hq' := hq
  simp only [QB, mem_filter, mem_product, mem_range, mem_univ, true_and] at hq'
  obtain ⟨hjk, hlat, -⟩ := hq'
  set H : ℤ := ((half S.L j : ℕ) : ℤ)
  have hH := two_half_add_one S.L_odd j
  have hHz : (2 * H + 1 : ℤ) = (S.L : ℤ) ^ j := by simp only [H]; exact_mod_cast hH
  have hb : ∀ σ, -H ≤ x σ ∧ x σ ≤ (if σ = μ then (S.L : ℤ) ^ j else 0) + H := by
    intro σ
    have h := hx σ
    rw [Hw_zero, Lz_hS] at h
    simp only [or_self] at h
    exact h
  -- the shift along `μ`
  set t : ℕ := if x μ ≤ H then 0 else (x μ - H).toNat
  have ht : t ≤ S.L ^ j := by
    have h := hb μ
    simp only [if_true] at h
    simp only [t]
    split_ifs with hc
    · exact Nat.zero_le _
    · have : (x μ - H).toNat ≤ ((S.L : ℤ) ^ j).toNat := Int.toNat_le_toNat (by linarith)
      rwa [show ((S.L : ℤ) ^ j) = ((S.L ^ j : ℕ) : ℤ) by push_cast; rfl, Int.toNat_natCast] at this
  have hxt : ∀ σ, -H ≤ x σ - (if σ = μ then (t : ℤ) else 0) ∧ x σ - (if σ = μ then (t : ℤ) else 0) ≤ H := by
    intro σ
    have h := hb σ
    by_cases hσ : σ = μ
    · subst hσ
      simp only [if_true] at h ⊢
      simp only [t]
      split_ifs with hc
      · push_cast; constructor <;> linarith
      · rw [Int.toNat_of_nonneg (by linarith)]; constructor <;> linarith
    · simp only [hσ, if_false, sub_zero] at h ⊢
      constructor <;> linarith
  -- the point of the block
  set o : Fin 4 → ℕ := fun σ => (x σ - (if σ = μ then (t : ℤ) else 0) + H).toNat
  have ho : o ∈ DiscretePoincare.box 4 (S.L ^ j) := by
    simp only [DiscretePoincare.box, Fintype.mem_piFinset, mem_range, o]
    intro σ
    have h := hxt σ
    have hLp : (0 : ℤ) < (S.L : ℤ) ^ j := pow_pos (by exact_mod_cast S.Lpos) _
    have : (x σ - (if σ = μ then (t : ℤ) else 0) + H).toNat < ((S.L : ℤ) ^ j).toNat := by
      rw [Int.toNat_lt_toNat hLp]; linarith
    rwa [show ((S.L : ℤ) ^ j) = ((S.L ^ j : ℕ) : ℤ) by push_cast; rfl, Int.toNat_natCast] at this
  have hmem := phi_mem (S := S.toDomSeq) j (show j ≤ S.k by omega) hlat ho
  have hz : y + (fun σ => ((x σ : ℤ) : ZMod NF)) =
      SmallFieldBlocks.phi S.toDomSeq j y o + ((t : ℕ) : ZMod NF) • CoreLean.unit NF μ := by
    funext σ
    simp only [SmallFieldBlocks.phi, o, Pi.add_apply, Pi.smul_apply, CoreLean.unit, smul_eq_mul]
    have h := hxt σ
    rw [Int.toNat_of_nonneg (by linarith)]
    have hH' : ((H : ℤ) : ZMod NF) = ((half S.toDomSeq.L j : ℕ) : ZMod NF) := by
      simp only [H, Int.cast_natCast]; rfl
    by_cases hσ : σ = μ
    · subst hσ
      simp only [if_true, Pi.single_eq_same, mul_one]
      push_cast
      rw [hH']
      ring
    · simp only [hσ, if_false, Pi.single_eq_of_ne hσ, mul_zero, add_zero, sub_zero]
      push_cast
      rw [hH']
      ring
  rw [hz]
  exact box_scale_low S hRM hq hmem ht

/-- The coarse coordinates `y/a_j` of a site `y` of the lattice `a_jℤ⁴`, by choice. -/
def c0Of {j : ℕ} {y : Site NF} (hlat : InLat S.L j y) : Fin 4 → ℤ := fun σ => (hlat σ).choose

lemma baseOf_zero {j : ℕ} {y : Site NF} (hlat : InLat S.L j y) :
    LevelsBridge.baseOf (SequenceAverages.hS S) S.mT S.k (c0Of S hlat) j 0 = y := by
  funext σ
  simp only [LevelsBridge.baseOf, Nat.sub_zero, Lz_hS]
  rw [(hlat σ).choose_spec]
  simp only [c0Of]
  push_cast
  ring

lemma img_zero (y : Site NF) (x : Fin 4 → ℤ) :
    img (SequenceAverages.hS S) y 0 x = y + fun σ => ((x σ : ℤ) : ZMod NF) := by
  simp [img, LatticePaths.ofs, qt]

/-- **The field on the region of a bond of a layer**: for `(j, y, μ) ∈ QB` and a bond `(y + x, ρ)` of the region of
the level `0`, `|X_ρ(y + x)| ≤ α₁La_j^{-1}` (`RegField` on `Ω_{j-1}`, `region_scale`). -/
theorem region_field (hRM : 2 * (S.L : ℝ) ≤ RMS) {j : ℕ} {y : Site NF} {μ : Fin 4} (hq : (j, y, μ) ∈ QB S)
    {X : Fin 4 → Site NF → Matrix (Fin N) (Fin N) ℂ} {α₁ : ℝ} (hX : RegField S X α₁) (hα0 : 0 ≤ α₁) (ρ : Fin 4)
    (x : Fin 4 → ℤ) (hx : RegularAverages.InR (SequenceAverages.hS S) j μ μ 0 x)
    (hx' : RegularAverages.InR (SequenceAverages.hS S) j μ μ 0 (x + Lz (SequenceAverages.hS S) ^ 0 • Pi.single ρ 1)) :
    ‖X ρ (y + fun σ => ((x σ : ℤ) : ZMod NF))‖ ≤ α₁ * S.L * ((S.L : ℝ) ^ j)⁻¹ := by
  have hL1 : (1 : ℝ) ≤ S.L := by exact_mod_cast S.Lpos
  set z : Site NF := y + fun σ => ((x σ : ℤ) : ZMod NF)
  have hz' : (y + fun σ => ((((x + Lz (SequenceAverages.hS S) ^ 0 • Pi.single ρ 1 : Fin 4 → ℤ)) σ : ℤ) : ZMod NF)) =
      z + CoreLean.unit NF ρ := by
    funext σ
    simp only [z, pow_zero, one_smul, Pi.add_apply, CoreLean.unit]
    by_cases hσ : σ = ρ
    · subst hσ; simp; ring
    · simp [Pi.single_eq_of_ne hσ]
  have h1 : j ≤ (S.toDomSeq).sc z + 1 := region_scale S hRM hq x hx
  have h2 := region_scale S hRM hq _ hx'
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

lemma one_le_hS (hL3 : 3 ≤ S.L) : 1 ≤ SequenceAverages.hS S := by
  have := SequenceAverages.L_eq S; omega

lemma Lr_hS : (((2 * SequenceAverages.hS S + 1 : ℕ)) : ℝ) = S.L := by
  rw [← SequenceAverages.L_eq S]

open Classical in
/-- **`Q_j(e^{iX}) - Q_j(id)` at a bond of a layer** (the fine model): for `(j, y, μ) ∈ QB`, a regular field `X` with
`α₁L, K_oα₁L ≤ c`, and every `1`-form `A`, in the per-level norms of the region of `j` levels based at `y`,
`‖L^j(Q_j(e^{iX}) - Q_j(id))A‖_{1,j} ≤ (e^{Σ_l 8L³CK_oα₁L·L^{-(j-l)}} - 1)L^{-3j}‖A‖_{1,0}`. -/
theorem qseq_level_diff (G : GaugeGroup N) (hGc : IsClosed G.mats) (hN : 1 ≤ N) :
    ∃ c Ko C : ℝ, 0 < c ∧ 0 ≤ Ko ∧ 0 ≤ C ∧
      ∀ (hRM : 2 * (S.L : ℝ) ≤ RMS)
        (hn : ∀ l, 4 * SequenceAverages.hS S + 4 ≤ MultiscaleAverages.nn (SequenceAverages.hS S) S.mT S.k l)
        {j : ℕ} {y : Site NF} {μ : Fin 4} (hq : (j, y, μ) ∈ QB S)
        {X : Fin 4 → Site NF → Matrix (Fin N) (Fin N) ℂ} {α₁ : ℝ} (hX : RegField S X α₁) (hα0 : 0 ≤ α₁)
        (hαc : α₁ * S.L ≤ c) (hKαc : Ko * (α₁ * S.L) ≤ c) (A : Fin 4 → Site NF → Matrix (Fin N) (Fin N) ℂ),
      ∃ hlat : InLat S.L j y,
        RelativeAverage.ell1 (SequenceAverages.hS S) j μ j (fun x ν => ‖(((((2 * SequenceAverages.hS S + 1 : ℕ) : ℂ)) ^ j) •
            (MultiscaleAverages.Qcomp (SequenceAverages.hS S) S.mT S.k (fun _ => True)
                (fun W => LogM (W : Matrix (Fin N) (Fin N) ℂ)) (cfgX X) j A -
              MultiscaleAverages.Qcomp (SequenceAverages.hS S) S.mT S.k (fun _ => True)
                (fun W => LogM (W : Matrix (Fin N) (Fin N) ℂ)) RelativeAverage.oneC j A)) ν
              (img (SequenceAverages.hS S) (LevelsBridge.baseOf (SequenceAverages.hS S) S.mT S.k (c0Of S hlat) j j)
                j x)‖) ≤
          (Real.exp (∑ l ∈ Finset.range j, 8 * (((2 * SequenceAverages.hS S + 1 : ℕ) : ℝ)) ^ 3 * C *
              (Ko * (α₁ * S.L) * ((((2 * SequenceAverages.hS S + 1 : ℕ) : ℝ)) ^ (j - l))⁻¹)) - 1) *
            (((((2 * SequenceAverages.hS S + 1 : ℕ) : ℝ) ^ 3)⁻¹) ^ j *
              RelativeAverage.ell1 (SequenceAverages.hS S) j μ 0 (fun x ν => ‖A ν (y + fun σ => ((x σ : ℤ) : ZMod NF))‖)) := by
  have hh := one_le_hS S S.three_le_L
  obtain ⟨c, Ko, C, hc, hKo, hC, hd⟩ :=
    LevelsBridge.qcomp_diff (SequenceAverages.hS S) S.mT S.k G hGc hN hh
  refine ⟨c, Ko, C, hc, hKo, hC, ?_⟩
  intro hRM hn j y μ hq X α₁ hX hα0 hαc hKαc A
  have hq' := hq
  simp only [QB, mem_filter, mem_product, mem_range, mem_univ, true_and] at hq'
  obtain ⟨hjk, hlat, -⟩ := hq'
  refine ⟨hlat, ?_⟩
  have hcfg : cfgX X = AverageHolo.moveC RelativeAverage.oneC X := by
    funext ρ z; simp [cfgX, AverageHolo.moveC, RelativeAverage.oneC]
  have hb0 := baseOf_zero S hlat
  have h := hd j μ (by omega) hn (c0Of S hlat) X A (α₁ * S.L)
    (fun ρ x _ hx1 hx2 => by
      rw [hb0, img_zero, Lr_hS]
      exact region_field S hRM hq hX hα0 ρ x hx1 hx2)
    (by positivity) hαc hKαc
  rw [hcfg]
  simpa only [hb0, img_zero] using h

lemma img_top (j : ℕ) (b : Site (MultiscaleAverages.nn (SequenceAverages.hS S) S.mT S.k j)) :
    img (SequenceAverages.hS S) b j 0 = b := by
  funext σ; simp [img, LatticePaths.ofs, qt]

lemma RB_top (j : ℕ) (μ : Fin 4) : RelativeAverage.RB (SequenceAverages.hS S) j μ j 0 μ := by
  have hH : Hw (SequenceAverages.hS S) j j = 0 := by simp [Hw]
  have hp : (0 : ℤ) ≤ Lz (SequenceAverages.hS S) ^ j := pow_nonneg (by unfold Lz; omega) _
  refine ⟨fun σ => dvd_zero _, fun σ => ?_, fun σ => ?_⟩
  · simp only [Pi.zero_apply, hH, neg_zero, add_zero, or_self]
    split_ifs <;> constructor <;> linarith
  · simp only [zero_add, Pi.smul_apply, smul_eq_mul, hH, neg_zero, add_zero, or_self]
    by_cases hσ : σ = μ
    · subst hσ; simp only [Pi.single_eq_same, mul_one, if_true]; constructor <;> linarith
    · simp only [Pi.single_eq_of_ne hσ, mul_zero, if_neg hσ]; constructor <;> linarith

/-- The sum over `[0, n)⁴` as `Fin` tuples and as the box of `DiscretePoincare`. -/
lemma sum_fin_box {M : Type*} [AddCommMonoid M] (n : ℕ) (hn : 0 < n) (G : (Fin 4 → ℕ) → M) :
    ∑ o : Fin 4 → Fin n, G (fun σ => (o σ : ℕ)) = ∑ o ∈ DiscretePoincare.box 4 n, G o := by
  refine Finset.sum_nbij' (fun o σ => (o σ : ℕ)) (fun o σ => ⟨o σ % n, Nat.mod_lt _ hn⟩) (fun o _ => ?_)
    (fun _ _ => Finset.mem_univ _) (fun o _ => ?_) (fun o ho => ?_) (fun _ _ => rfl)
  · simp [DiscretePoincare.box, Fintype.mem_piFinset]
  · funext σ; ext; simp [Nat.mod_eq_of_lt (o σ).isLt]
  · simp only [DiscretePoincare.box, Fintype.mem_piFinset, Finset.mem_range] at ho
    funext σ; simp [Nat.mod_eq_of_lt (ho σ)]

lemma sum_fin_congr {M : Type*} [AddCommMonoid M] {a b : ℕ} (hab : a = b) (G : (Fin 4 → ℕ) → M) :
    ∑ o : Fin 4 → Fin a, G (fun σ => (o σ : ℕ)) = ∑ o : Fin 4 → Fin b, G (fun σ => (o σ : ℕ)) := by
  subst hab; rfl

open Classical in
/-- **`Q_j(id) = Qt`** at a bond of a layer: the composite average of the chain at the trivial configuration,
evaluated at the coarse point of the bond, is the mean `Qt` of the fine model over the lines of the box
(`Q_trivial_levels`, `sum_ptB`, `sum_Blk`). -/
theorem qcomp_one_Qt {j : ℕ} (hj : j ≤ S.k) {y : Site NF} (hlat : InLat S.L j y) (μ : Fin 4)
    (A : Fin 4 → Site NF → Matrix (Fin N) (Fin N) ℂ) :
    MultiscaleAverages.Qcomp (SequenceAverages.hS S) S.mT S.k (fun _ => True)
        (fun W => LogM (W : Matrix (Fin N) (Fin N) ℂ)) RelativeAverage.oneC j A μ
        (LevelsBridge.baseOf (SequenceAverages.hS S) S.mT S.k (c0Of S hlat) j j) = Qt S A j y μ := by
  set h := SequenceAverages.hS S
  set base := LevelsBridge.baseOf h S.mT S.k (c0Of S hlat) j
  set Lc : ℂ := ((2 * h + 1 : ℕ) : ℂ)
  have hLc : Lc = (S.L : ℂ) := by simp only [Lc, h]; rw [← SequenceAverages.L_eq S]
  have hLc0 : Lc ≠ 0 := by rw [hLc]; exact_mod_cast S.Lpos.ne'
  set B : ∀ l, Fin 4 → Site (MultiscaleAverages.nn h S.mT S.k l) → Matrix (Fin N) (Fin N) ℂ := fun l =>
    Lc ^ l • MultiscaleAverages.Qcomp h S.mT S.k (fun _ => True) (fun W => LogM (W : Matrix (Fin N) (Fin N) ℂ))
      RelativeAverage.oneC l A
  have hrec : ∀ l, l < j → ∀ ρ x, Lat (Lz h) (l + 1) x → RelativeAverage.Rg h j μ (l + 1) x →
      RelativeAverage.Rg h j μ (l + 1) (x + Lz h ^ (l + 1) • Pi.single ρ 1) →
      B (l + 1) ρ (img h (base (l + 1)) (l + 1) x) =
        Lc • RelativeAverage.Qlin (RelativeAverage.oneC (N := N)) (img h (base l) l x) ρ h (B l) := by
    intro l hl ρ x hx _ _
    have hup := LevelsBridge.up_img h S.mT S.k base l (by omega)
      (LevelsBridge.base_up h S.mT S.k (c0Of S hlat) j l hl (by omega)) x hx
    simp only [B, Pi.smul_apply, LevelsBridge.qcomp_succ_apply, LevelsBridge.mpow_oneC, hup, map_smul, smul_smul,
      pow_succ]
    ring_nf
  have hQT := RelativeAverage.Q_trivial_levels h j μ (MultiscaleAverages.nn h S.mT S.k) base B hrec j le_rfl μ 0
    (RB_top S j μ)
  rw [img_top] at hQT
  have hB0 : ∀ z, B 0 μ (img h (base 0) 0 z) = A μ (y + fun σ => ((z σ : ℤ) : ZMod NF)) := fun z => by
    simp only [B, pow_zero, one_smul, MultiscaleAverages.Qcomp_zero, LinearMap.id_apply]
    rw [show base 0 = y from baseOf_zero S hlat, img_zero]
  simp only [hB0] at hQT
  set F : (Fin 4 → ℤ) → Matrix (Fin N) (Fin N) ℂ := fun z => ∑ J ∈ Finset.range ((2 * h + 1) ^ j),
    A μ (y + fun σ => (((z + ((J : ℕ) : ℤ) • (Pi.single μ (1 : ℤ) : Fin 4 → ℤ)) σ : ℤ) : ZMod NF)) with hF
  have hQT' : B j μ (base j) = ((Lc ^ 4)⁻¹) ^ j • ∑ p : Fin j → BlockPaths.Pts h, F (RelativeAverage.ptB h j 0 p) := hQT
  rw [RelativeAverage.sum_ptB h j 0 F] at hQT'
  -- the right side is `L^j` times `Qt`
  have hpow : (2 * h + 1) ^ j = S.L ^ j := by rw [← SequenceAverages.L_eq S]
  have hQt : Qt S A j y μ = ((Lc ^ 5) ^ j)⁻¹ • ∑ o : Fin 4 → Fin ((2 * h + 1) ^ j),
      F ((0 : Fin 4 → ℤ) + (fun σ => ((o σ : ℕ) : ℤ)) - fun _ => Hw h j 0) := by
    unfold Qt
    rw [sum_Blk (S := S.toDomSeq) j hj hlat]
    rw [← sum_fin_box (S.toDomSeq.L ^ j) (pow_pos S.Lpos _) (fun o => ∑ t ∈ Finset.range (S.L ^ j),
      A μ (SmallFieldBlocks.phi S.toDomSeq j y o + ((t : ℕ) : ZMod NF) • CoreLean.unit NF μ))]
    rw [sum_fin_congr (show (2 * h + 1) ^ j = S.toDomSeq.L ^ j from hpow)
      (fun o' => F ((0 : Fin 4 → ℤ) + (fun σ => ((o' σ : ℕ) : ℤ)) - fun _ => Hw h j 0))]
    congr 1
    · rw [hLc]; push_cast; ring
    · refine Finset.sum_congr rfl fun o _ => ?_
      simp only [hF]
      rw [hpow]
      refine Finset.sum_congr rfl fun J _ => ?_
      congr 1
      funext σ
      simp only [SmallFieldBlocks.phi, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, CoreLean.unit,
        zero_add, Hw_zero]
      have hHw : Hw h j 0 = ((half S.L j : ℕ) : ℤ) := Hw_zero S j
      by_cases hσ : σ = μ
      · subst hσ; simp only [Pi.single_eq_same, mul_one, hHw]; push_cast
        rw [show ((half S.toDomSeq.L j : ℕ) : ZMod NF) = ((half S.L j : ℕ) : ZMod NF) from rfl]; ring
      · simp only [Pi.single_eq_of_ne hσ, mul_zero, add_zero, hHw]; push_cast
        rw [show ((half S.toDomSeq.L j : ℕ) : ZMod NF) = ((half S.L j : ℕ) : ZMod NF) from rfl]
  rw [hQt]
  have hsc : Lc ^ j • MultiscaleAverages.Qcomp h S.mT S.k (fun _ => True)
      (fun W => LogM (W : Matrix (Fin N) (Fin N) ℂ)) RelativeAverage.oneC j A μ (base j) =
      ((Lc ^ 4)⁻¹) ^ j • ∑ o : Fin 4 → Fin ((2 * h + 1) ^ j),
        F ((0 : Fin 4 → ℤ) + (fun σ => ((o σ : ℕ) : ℤ)) - fun _ => Hw h j 0) := hQT'
  have hLj : Lc ^ j ≠ 0 := pow_ne_zero _ hLc0
  calc MultiscaleAverages.Qcomp h S.mT S.k (fun _ => True) (fun W => LogM (W : Matrix (Fin N) (Fin N) ℂ))
        RelativeAverage.oneC j A μ (base j)
      = (Lc ^ j)⁻¹ • (Lc ^ j • MultiscaleAverages.Qcomp h S.mT S.k (fun _ => True)
          (fun W => LogM (W : Matrix (Fin N) (Fin N) ℂ)) RelativeAverage.oneC j A μ (base j)) := by
        rw [smul_smul, inv_mul_cancel₀ hLj, one_smul]
    _ = _ := by
        rw [hsc, smul_smul]
        congr 1
        rw [← inv_pow, ← inv_pow, ← mul_pow]
        congr 1
        rw [inv_pow, ← mul_inv, ← pow_succ', inv_pow]

end SFBounds
end CoreLean

end
