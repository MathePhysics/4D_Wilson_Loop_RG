/-
`def:localisation`(iii) of BALABAN_CORE.tex (`ea68ea6e3640`): the linear size `d(X; D)` with the one-dimensional
measure `|G \ D|` of the union `G`, with respect to the Euclidean length.

`ContractedGrid.lean` defines `d(X; D)` (`Grid.d`) with the sum over the segments of a family of the Euclidean length
of the part of each segment outside `D` (`lenOut`). Here the core's definition is formalised and the two infima
are shown to agree (`d_eq_dMeas`).

The torus with its Euclidean distance is the quotient `TorE P = ℝ⁴/(Pℤ)⁴` of the Euclidean space (`P = sN`), a
normed group, with the Hausdorff measure `μH[1]`; it is identified with `Torus s N = (ℝ/Pℤ)⁴` by the bijection
`toT`, and `H1E A = μH[1](toT⁻¹ A)` is the one-dimensional measure of a set `A` of the torus.

* `H1E_union_le`: `|G \ F| ≤ Σ_σ lenOut F σ` for the union `G` of a family (the segment parametrisations are
  Lipschitz with the constant `|σ₂|₂`).
* `exists_family_le`: conversely, every finite union `G` of segments is the union of a family with
  `Σ_σ lenOut F σ ≤ |G \ F|`, for `F` with a measurable preimage: the segments are cut into pieces of a length
  at most `P/8`, on which the parametrisation is an isometry up to the factor `|σ₂|₂`; the parameters at which a
  piece meets an earlier one form a closed interval (`param_ordConnected`), and the parts of each piece which are
  not covered by earlier ones are segments meeting the others at most at their end points.
-/
import CoreLean.ContractedGeometry
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

open Set Real MeasureTheory
open scoped ENNReal NNReal

noncomputable section

namespace CoreLean
namespace Contracted

local notation "E" => EuclideanSpace ℝ (Fin 4)

/-! ### The Euclidean torus -/

/-- The lattice `(Pℤ)⁴` of `ℝ⁴`. -/
def latE (P : ℝ) : AddSubgroup E where
  carrier := {v | ∀ ν, ((v.ofLp ν : ℝ) : AddCircle P) = 0}
  add_mem' := fun {a b} ha hb ν => by
    simp only [mem_ofPred_eq] at ha hb ⊢
    rw [WithLp.ofLp_add, Pi.add_apply, AddCircle.coe_add, ha ν, hb ν, add_zero]
  zero_mem' := fun ν => by simp
  neg_mem' := fun {a} ha ν => by
    simp only [mem_ofPred_eq] at ha ⊢
    rw [WithLp.ofLp_neg, Pi.neg_apply, AddCircle.coe_neg, ha ν, neg_zero]

instance isClosed_latE (P : ℝ) : IsClosed (latE P : Set E) := by
  have e : (latE P : Set E) = ⋂ ν, (fun v : E => ((v.ofLp ν : ℝ) : AddCircle P)) ⁻¹' {0} := by
    ext v; simp [latE]
  rw [e]
  exact isClosed_iInter fun ν => isClosed_singleton.preimage
    ((AddCircle.continuous_mk' P).comp ((continuous_apply ν).comp (PiLp.continuous_ofLp 2 _)))

/-- The torus `ℝ⁴/(Pℤ)⁴` with the Euclidean distance. -/
abbrev TorE (P : ℝ) := E ⧸ latE P

instance (P : ℝ) : MeasurableSpace (TorE P) := borel _

instance (P : ℝ) : BorelSpace (TorE P) := ⟨rfl⟩

/-- The projection `ℝ⁴ → TorE P`. -/
def mkE (P : ℝ) (x : Fin 4 → ℝ) : TorE P := QuotientAddGroup.mk (WithLp.toLp 2 x)

variable {s : ℝ} {N : ℕ}

/-- The projection of the Euclidean space to the torus `Torus s N`, as a homomorphism. -/
def projHom (s : ℝ) (N : ℕ) : E →+ Torus s N where
  toFun v := proj s N v.ofLp
  map_zero' := by funext ν; simp [proj]
  map_add' x y := by funext ν; simp [proj]

/-- The identification `TorE (sN) → Torus s N`. -/
def toT (s : ℝ) (N : ℕ) : TorE (s * N) →+ Torus s N :=
  QuotientAddGroup.lift (latE (s * N)) (projHom s N) fun v hv => funext fun ν => hv ν

lemma toT_mkE (x : Fin 4 → ℝ) : toT s N (mkE (s * N) x) = proj s N x := rfl

lemma toT_injective : Function.Injective (toT s N) := by
  rw [← AddMonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro z hz
  obtain ⟨v, rfl⟩ := QuotientAddGroup.mk_surjective z
  rw [AddMonoidHom.mem_ker] at hz
  rw [AddSubgroup.mem_bot, QuotientAddGroup.eq_zero_iff]
  exact fun ν => congrFun hz ν

lemma toT_surjective : Function.Surjective (toT s N) := by
  intro z
  choose x hx using fun ν => QuotientAddGroup.mk_surjective (z ν)
  exact ⟨mkE (s * N) x, funext fun ν => hx ν⟩

lemma continuous_toT : Continuous (toT s N) := by
  rw [(QuotientAddGroup.isQuotientMap_mk (latE (s * N))).continuous_iff]
  exact continuous_pi fun ν => (AddCircle.continuous_mk' _).comp ((continuous_apply ν).comp (PiLp.continuous_ofLp 2 _))

/-- The one-dimensional measure of a set of the torus, with respect to the Euclidean length. -/
def H1E (s : ℝ) (N : ℕ) (A : Set (Torus s N)) : ℝ≥0∞ := μH[1] (toT s N ⁻¹' A)

lemma H1E_mono {A B : Set (Torus s N)} (h : A ⊆ B) : H1E s N A ≤ H1E s N B :=
  measure_mono (preimage_mono h)

lemma norm_toLp (v : Fin 4 → ℝ) : ‖(WithLp.toLp 2 v : E)‖ = eu v := by
  rw [EuclideanSpace.norm_eq, eu]
  congr 1
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [Real.norm_eq_abs, sq_abs]

lemma eu_smul (c : ℝ) (v : Fin 4 → ℝ) : eu (c • v) = |c| * eu v := by
  rw [← norm_toLp, ← norm_toLp, WithLp.toLp_smul, norm_smul, Real.norm_eq_abs]

/-- The parametrisation `θ ↦ π(σ₁ + θσ₂)` of a segment in `TorE`. -/
def gam (P : ℝ) (σ : Seg) (θ : ℝ) : TorE P := mkE P (σ.1 + θ • σ.2)

lemma gam_sub (P : ℝ) (σ : Seg) (θ θ' : ℝ) :
    gam P σ θ - gam P σ θ' = QuotientAddGroup.mk (WithLp.toLp 2 ((θ - θ') • σ.2)) := by
  simp only [gam, mkE, ← QuotientAddGroup.mk_sub, ← WithLp.toLp_sub]
  congr 2
  rw [sub_smul]; abel

lemma dist_gam_le (P : ℝ) (σ : Seg) (θ θ' : ℝ) : dist (gam P σ θ) (gam P σ θ') ≤ eu σ.2 * dist θ θ' := by
  rw [dist_eq_norm, gam_sub, Real.dist_eq]
  refine QuotientAddGroup.norm_mk_le_norm.trans ?_
  rw [norm_toLp, eu_smul, mul_comm]

lemma lipschitz_gam (P : ℝ) (σ : Seg) : LipschitzWith ⟨eu σ.2, eu_nonneg _⟩ (gam P σ) :=
  LipschitzWith.of_dist_le_mul fun θ θ' => dist_gam_le P σ θ θ'

lemma preimage_image_proj (σ : Seg) (B : Set ℝ) :
    toT s N ⁻¹' ((fun θ => proj s N (σ.1 + θ • σ.2)) '' B) = gam (s * N) σ '' B := by
  ext z
  constructor
  · rintro ⟨θ, hθ, he⟩
    exact ⟨θ, hθ, toT_injective (by rw [← he]; rfl)⟩
  · rintro ⟨θ, hθ, rfl⟩
    exact ⟨θ, hθ, rfl⟩

/-- The part of a segment outside `F`, as the image of a set of parameters. -/
lemma segSet_diff (σ : Seg) (F : Set (Torus s N)) :
    segSet s N σ \ F = (fun θ => proj s N (σ.1 + θ • σ.2)) ''
      {θ ∈ Icc (0 : ℝ) 1 | proj s N (σ.1 + θ • σ.2) ∉ F} := by
  ext z
  simp only [segSet, mem_sdiff, mem_image, mem_ofPred_eq]
  constructor
  · rintro ⟨⟨θ, hθ, rfl⟩, hz⟩
    exact ⟨θ, ⟨hθ, hz⟩, rfl⟩
  · rintro ⟨θ, ⟨hθ, hz⟩, rfl⟩
    exact ⟨⟨θ, hθ, rfl⟩, hz⟩

/-- **`|σ \ F| ≤ lenOut F σ`.** -/
theorem H1E_seg_le (σ : Seg) (F : Set (Torus s N)) :
    H1E s N (segSet s N σ \ F) ≤ ENNReal.ofReal (lenOut s N F σ) := by
  rw [H1E, segSet_diff, preimage_image_proj]
  refine ((lipschitz_gam (s * N) σ).hausdorffMeasure_image_le zero_le_one _).trans ?_
  rw [ENNReal.rpow_one, hausdorffMeasure_real, lenOut,
    ENNReal.ofReal_mul (eu_nonneg _), ENNReal.ofReal_toReal (volume_out_ne_top F σ),
    ENNReal.ofReal_eq_coe_nnreal (eu_nonneg _)]
  exact le_rfl

/-- **`|G \ F| ≤ Σ_σ lenOut F σ`** for the union `G` of a finite family of segments. -/
theorem H1E_union_le (S : Finset Seg) (F : Set (Torus s N)) :
    H1E s N ((⋃ σ ∈ S, segSet s N σ) \ F) ≤ ENNReal.ofReal (∑ σ ∈ S, lenOut s N F σ) := by
  have e : (⋃ σ ∈ S, segSet s N σ) \ F = ⋃ σ ∈ S, (segSet s N σ \ F) := by
    ext z; simp only [mem_sdiff, mem_iUnion, exists_prop]; tauto
  rw [ENNReal.ofReal_sum_of_nonneg fun σ _ => lenOut_nonneg F σ, e]
  unfold H1E
  rw [preimage_iUnion₂]
  refine (measure_biUnion_finset_le S _).trans (Finset.sum_le_sum fun σ _ => H1E_seg_le σ F)

/-! ### Short segments -/

/-- A nonzero point of the lattice has the Euclidean length at least `P`. -/
lemma le_eu_of_mem {P : ℝ} (hP : 0 < P) {w : Fin 4 → ℝ} (hw : (WithLp.toLp 2 w : E) ∈ latE P) (h0 : w ≠ 0) :
    P ≤ eu w := by
  obtain ⟨ν, hν⟩ := Function.ne_iff.1 h0
  obtain ⟨k, hk⟩ := (AddCircle.coe_eq_zero_iff P).1 (hw ν)
  simp only [zsmul_eq_mul] at hk
  have hk0 : k ≠ 0 := by rintro rfl; simp at hk; exact hν (by rw [← hk]; rfl)
  have h1 : P ≤ |w ν| := by
    have : (w ν) = k * P := hk.symm
    rw [this, abs_mul, abs_of_pos hP]
    have : (1 : ℝ) ≤ |(k : ℝ)| := by
      have := Int.one_le_abs hk0
      exact_mod_cast this
    nlinarith
  refine h1.trans ?_
  rw [← norm_toLp]
  exact PiLp.norm_apply_le (WithLp.toLp 2 w) ν

/-- **Short vectors keep their length in the quotient.** -/
lemma norm_mk_short {P : ℝ} (hP : 0 < P) (v : Fin 4 → ℝ) (hv : eu v ≤ P / 2) :
    ‖(QuotientAddGroup.mk (WithLp.toLp 2 v) : TorE P)‖ = eu v := by
  apply le_antisymm (by rw [← norm_toLp]; exact QuotientAddGroup.norm_mk_le_norm)
  rw [QuotientAddGroup.norm_mk, Metric.le_infDist ⟨0, (latE P).zero_mem⟩]
  intro w hw
  obtain ⟨w', rfl⟩ := (WithLp.toLp_surjective 2 : Function.Surjective (WithLp.toLp 2 : (Fin 4 → ℝ) → E)) w
  rw [dist_eq_norm, ← WithLp.toLp_sub, norm_toLp]
  by_cases h0 : w' = 0
  · rw [h0, sub_zero]
  · have h1 := le_eu_of_mem hP hw h0
    have h2 : eu w' ≤ eu (v - w') + eu v := by
      rw [← norm_toLp, ← norm_toLp, ← norm_toLp]
      calc ‖(WithLp.toLp 2 w' : E)‖ = ‖(WithLp.toLp 2 v : E) - WithLp.toLp 2 (v - w')‖ := by
            rw [← WithLp.toLp_sub]; congr 2; abel
        _ ≤ ‖(WithLp.toLp 2 v : E)‖ + ‖(WithLp.toLp 2 (v - w') : E)‖ := norm_sub_le _ _
        _ = _ := add_comm _ _
    linarith

/-- A segment of the Euclidean length at most `P/8`. -/
def Short (P : ℝ) (σ : Seg) : Prop := eu σ.2 ≤ P / 8

/-- **On a short segment the parametrisation is an isometry up to the factor `|σ₂|₂`.** -/
lemma dist_gam_eq {P : ℝ} (hP : 0 < P) {σ : Seg} (hσ : Short P σ) {θ θ' : ℝ} (hθ : θ ∈ Icc (0 : ℝ) 1)
    (hθ' : θ' ∈ Icc (0 : ℝ) 1) : dist (gam P σ θ) (gam P σ θ') = eu σ.2 * dist θ θ' := by
  have hd : |θ - θ'| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hθ.1, hθ.2, hθ'.1, hθ'.2]
  rw [dist_eq_norm, gam_sub, norm_mk_short hP, eu_smul, Real.dist_eq, mul_comm]
  rw [eu_smul]
  have := eu_nonneg σ.2
  unfold Short at hσ
  nlinarith [abs_nonneg (θ - θ')]

lemma injOn_gam {P : ℝ} (hP : 0 < P) {σ : Seg} (hσ : Short P σ) (hpos : 0 < eu σ.2) :
    InjOn (gam P σ) (Icc 0 1) := fun θ hθ θ' hθ' he => by
  have := dist_gam_eq hP hσ hθ hθ'
  rw [he, dist_self] at this
  exact dist_eq_zero.1 ((mul_eq_zero.1 this.symm).resolve_left hpos.ne')

/-- **The lower bound**: `|σ₂|₂ · |B| ≤ |γ(B)|` for a short segment and `B ⊂ [0, 1]`. -/
lemma vol_le_H {P : ℝ} (hP : 0 < P) {σ : Seg} (hσ : Short P σ) {B : Set ℝ} (hB : B ⊆ Icc 0 1) :
    ENNReal.ofReal (eu σ.2) * volume B ≤ μH[1] (gam P σ '' B) := by
  rcases (eu_nonneg σ.2).eq_or_lt with h0 | hpos
  · rw [← h0, ENNReal.ofReal_zero, zero_mul]; exact bot_le
  have hinj := injOn_gam hP hσ hpos
  set g := Function.invFunOn (gam P σ) (Icc 0 1)
  have hg : ∀ θ ∈ Icc (0 : ℝ) 1, g (gam P σ θ) = θ := fun θ hθ =>
    hinj (Function.invFunOn_mem ⟨θ, hθ, rfl⟩) hθ (Function.invFunOn_eq ⟨θ, hθ, rfl⟩)
  set K : ℝ≥0 := (eu σ.2)⁻¹.toNNReal with hK
  have hKc : (K : ℝ) = (eu σ.2)⁻¹ := Real.coe_toNNReal _ (inv_nonneg.2 (eu_nonneg _))
  have hlip : LipschitzOnWith K g (gam P σ '' B) := by
    refine LipschitzOnWith.of_dist_le_mul ?_
    rintro _ ⟨θ, hθ, rfl⟩ _ ⟨θ', hθ', rfl⟩
    rw [hg θ (hB hθ), hg θ' (hB hθ'), dist_gam_eq hP hσ (hB hθ) (hB hθ'), hKc, ← mul_assoc,
      inv_mul_cancel₀ hpos.ne', one_mul]
  have himg : g '' (gam P σ '' B) = B := by
    ext θ
    constructor
    · rintro ⟨_, ⟨θ', hθ', rfl⟩, rfl⟩; rw [hg θ' (hB hθ')]; exact hθ'
    · intro hθ; exact ⟨gam P σ θ, ⟨θ, hθ, rfl⟩, hg θ (hB hθ)⟩
  have h1 := hlip.hausdorffMeasure_image_le zero_le_one
  rw [himg, hausdorffMeasure_real, ENNReal.rpow_one] at h1
  have hKe : (eu σ.2).toNNReal * K = 1 := by
    rw [hK, ← Real.toNNReal_mul (eu_nonneg _), mul_inv_cancel₀ hpos.ne', Real.toNNReal_one]
  calc ENNReal.ofReal (eu σ.2) * volume B
      ≤ ENNReal.ofReal (eu σ.2) * ((K : ℝ≥0∞) * μH[1] (gam P σ '' B)) := by gcongr
    _ = μH[1] (gam P σ '' B) := by
        rw [← mul_assoc, ENNReal.ofReal, ← ENNReal.coe_mul, hKe, ENNReal.coe_one, one_mul]

/-- `gam σ θ = gam τ t` iff `σ₁ + θσ₂ - τ₁ - tτ₂` lies in the lattice. -/
lemma gam_eq_iff (P : ℝ) (σ τ : Seg) (θ t : ℝ) :
    gam P σ θ = gam P τ t ↔ (WithLp.toLp 2 ((τ.1 + t • τ.2) - (σ.1 + θ • σ.2)) : E) ∈ latE P := by
  rw [gam, gam, mkE, mkE, QuotientAddGroup.eq, WithLp.toLp_sub, neg_add_eq_sub]

/-- **The parameters at which a short segment meets another form a convex set.** -/
lemma param_ordConnected {P : ℝ} (hP : 0 < P) {σ τ : Seg} (hσ : Short P σ) (hτ : Short P τ) :
    OrdConnected {θ ∈ Icc (0 : ℝ) 1 | gam P σ θ ∈ gam P τ '' Icc 0 1} := by
  refine ⟨fun θ1 h1 θ2 h2 θ hθ => ?_⟩
  obtain ⟨h1i, t1, ht1, he1⟩ := h1
  obtain ⟨h2i, t2, ht2, he2⟩ := h2
  rw [eq_comm, gam_eq_iff] at he1 he2
  set w1 := (τ.1 + t1 • τ.2) - (σ.1 + θ1 • σ.2)
  set w2 := (τ.1 + t2 • τ.2) - (σ.1 + θ2 • σ.2)
  -- the two lattice points agree
  have hw : w2 - w1 = 0 := by
    by_contra hne
    have hmem : (WithLp.toLp 2 (w2 - w1) : E) ∈ latE P := by
      rw [WithLp.toLp_sub]; exact (latE P).sub_mem he2 he1
    have hb := le_eu_of_mem hP hmem hne
    have e : w2 - w1 = (t2 - t1) • τ.2 - (θ2 - θ1) • σ.2 := by
      simp only [w1, w2, sub_smul]; abel
    have hle : eu (w2 - w1) ≤ P / 4 := by
      rw [e]
      have : eu ((t2 - t1) • τ.2 - (θ2 - θ1) • σ.2) ≤ eu ((t2 - t1) • τ.2) + eu ((θ2 - θ1) • σ.2) := by
        rw [← norm_toLp, ← norm_toLp, ← norm_toLp, WithLp.toLp_sub]; exact norm_sub_le _ _
      refine this.trans ?_
      rw [eu_smul, eu_smul]
      have a1 : |t2 - t1| ≤ 1 := by rw [abs_le]; constructor <;> linarith [ht1.1, ht1.2, ht2.1, ht2.2]
      have a2 : |θ2 - θ1| ≤ 1 := by rw [abs_le]; constructor <;> linarith [h1i.1, h1i.2, h2i.1, h2i.2]
      unfold Short at hσ hτ
      nlinarith [eu_nonneg σ.2, eu_nonneg τ.2, abs_nonneg (t2 - t1), abs_nonneg (θ2 - θ1)]
    linarith
  refine ⟨⟨h1i.1.trans hθ.1, hθ.2.trans h2i.2⟩, ?_⟩
  rcases eq_or_lt_of_le (hθ.1.trans hθ.2) with h12 | h12
  · have : θ = θ1 := le_antisymm (h12 ▸ hθ.2) hθ.1
    subst this
    exact ⟨t1, ht1, by rw [eq_comm, gam_eq_iff]; exact he1⟩
  · set lam := (θ - θ1) / (θ2 - θ1)
    have hlam0 : 0 ≤ lam := div_nonneg (by linarith [hθ.1]) (by linarith)
    have hlam1 : lam ≤ 1 := (div_le_one (by linarith)).2 (by linarith [hθ.2])
    have hθe : θ = θ1 + lam * (θ2 - θ1) := by simp only [lam]; field_simp; ring
    refine ⟨t1 + lam * (t2 - t1), ⟨by nlinarith [ht1.1, ht2.1, ht1.2, ht2.2],
      by nlinarith [ht1.1, ht2.1, ht1.2, ht2.2]⟩, ?_⟩
    rw [eq_comm, gam_eq_iff]
    have e : (τ.1 + (t1 + lam * (t2 - t1)) • τ.2) - (σ.1 + θ • σ.2) = w1 + lam • (w2 - w1) := by
      rw [hθe]; simp only [w1, w2, add_smul, smul_sub, smul_add, smul_smul]; abel_nf; module
    rw [e, hw, smul_zero, add_zero]
    exact he1

lemma continuous_gam (P : ℝ) (σ : Seg) : Continuous (gam P σ) := (lipschitz_gam P σ).continuous

lemma param_isClosed (P : ℝ) (σ τ : Seg) :
    IsClosed {θ ∈ Icc (0 : ℝ) 1 | gam P σ θ ∈ gam P τ '' Icc 0 1} :=
  isClosed_Icc.inter (((isCompact_Icc.image (continuous_gam P τ)).isClosed).preimage (continuous_gam P σ))

/-- A closed convex subset of `[0, 1]` is empty or an interval `[a, b]`. -/
lemma eq_Icc_of_ordConnected {I : Set ℝ} (hI : I ⊆ Icc 0 1) (hc : IsClosed I) (ho : OrdConnected I)
    (hne : I.Nonempty) : I = Icc (sInf I) (sSup I) := by
  have hbb : BddBelow I := ⟨0, fun x hx => (hI hx).1⟩
  have hba : BddAbove I := ⟨1, fun x hx => (hI hx).2⟩
  ext x
  constructor
  · intro hx; exact ⟨csInf_le hbb hx, le_csSup hba hx⟩
  · intro hx; exact ho.out (hc.csInf_mem hne hbb) (hc.csSup_mem hne hba) hx

/-! ### Pieces of a segment -/

/-- The piece `θ ∈ [t, t']` of a segment, as a segment. -/
def piece (σ : Seg) (t t' : ℝ) : Seg := (σ.1 + t • σ.2, (t' - t) • σ.2)

lemma segSet_piece (σ : Seg) {t t' : ℝ} (htt : t ≤ t') :
    segSet s N (piece σ t t') = (fun θ => proj s N (σ.1 + θ • σ.2)) '' Icc t t' := by
  ext z
  simp only [segSet, piece, mem_image]
  constructor
  · rintro ⟨θ', hθ', rfl⟩
    refine ⟨t + θ' * (t' - t), ⟨by nlinarith [hθ'.1], by nlinarith [hθ'.2]⟩, ?_⟩
    congr 1; rw [add_smul, mul_smul]; abel
  · rintro ⟨θ, hθ, rfl⟩
    rcases eq_or_lt_of_le htt with h | h
    · subst h
      have : θ = t := le_antisymm hθ.2 hθ.1
      subst this
      exact ⟨0, ⟨le_rfl, zero_le_one⟩, by simp⟩
    · refine ⟨(θ - t) / (t' - t), ⟨div_nonneg (by linarith [hθ.1]) (by linarith),
        (div_le_one (by linarith)).2 (by linarith [hθ.2])⟩, ?_⟩
      congr 1
      rw [smul_smul, div_mul_cancel₀ _ (by linarith : t' - t ≠ 0), sub_smul]; abel

/-- **`lenOut F (piece σ t t') = |σ₂|₂ |{θ ∈ [t, t'] | π(σ₁ + θσ₂) ∉ F}|`.** -/
lemma lenOut_piece (σ : Seg) (F : Set (Torus s N)) {t t' : ℝ} (htt : t < t') :
    lenOut s N F (piece σ t t') =
      eu σ.2 * (volume {θ ∈ Icc t t' | proj s N (σ.1 + θ • σ.2) ∉ F}).toReal := by
  set A := {θ ∈ Icc t t' | proj s N (σ.1 + θ • σ.2) ∉ F}
  have hc : t' - t ≠ 0 := by linarith
  have e : {θ' ∈ Icc (0 : ℝ) 1 | proj s N ((piece σ t t').1 + θ' • (piece σ t t').2) ∉ F} =
      ((t' - t) * ·) ⁻¹' ((fun h => t + h) ⁻¹' A) := by
    ext θ'
    simp only [piece, mem_ofPred_eq, mem_preimage, mem_Icc, A]
    have e2 : σ.1 + t • σ.2 + θ' • (t' - t) • σ.2 = σ.1 + (t + (t' - t) * θ') • σ.2 := by
      rw [add_smul, mul_smul]; rw [smul_comm θ' (t' - t)]; abel
    rw [e2]
    constructor
    · rintro ⟨⟨h0, h1⟩, h⟩; exact ⟨⟨by nlinarith, by nlinarith⟩, h⟩
    · rintro ⟨⟨h0, h1⟩, h⟩
      refine ⟨⟨?_, ?_⟩, h⟩
      · by_contra hc'; push Not at hc'; nlinarith
      · by_contra hc'; push Not at hc'; nlinarith
  rw [lenOut, e, Real.volume_preimage_mul_left hc, measure_preimage_add, piece, eu_smul,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _), abs_inv, abs_of_pos (by linarith : 0 < t' - t)]
  field_simp

/-! ### Consecutive points of a finite set of parameters -/

/-- `t < t'` are consecutive points of `Es`. -/
def Consec (Es : Finset ℝ) (t t' : ℝ) : Prop := t ∈ Es ∧ t' ∈ Es ∧ t < t' ∧ ∀ e ∈ Es, ¬ (t < e ∧ e < t')

lemma exists_consec (Es : Finset ℝ) (h0 : (0 : ℝ) ∈ Es) (h1 : (1 : ℝ) ∈ Es) {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) 1) :
    ∃ t t', Consec Es t t' ∧ θ ∈ Icc t t' := by
  classical
  rcases eq_or_lt_of_le hθ.2 with h | h
  · subst h
    have hA : (Es.filter (· < 1)).Nonempty := ⟨0, Finset.mem_filter.2 ⟨h0, zero_lt_one⟩⟩
    have ha := Finset.mem_filter.1 ((Es.filter (· < 1)).max'_mem hA)
    refine ⟨(Es.filter (· < 1)).max' hA, 1, ⟨ha.1, h1, ha.2, ?_⟩, ⟨ha.2.le, le_rfl⟩⟩
    rintro e he ⟨he1, he2⟩
    have := (Es.filter (· < 1)).le_max' e (Finset.mem_filter.2 ⟨he, he2⟩)
    linarith
  · have hA : (Es.filter (· ≤ θ)).Nonempty := ⟨0, Finset.mem_filter.2 ⟨h0, hθ.1⟩⟩
    have hB : (Es.filter (θ < ·)).Nonempty := ⟨1, Finset.mem_filter.2 ⟨h1, h⟩⟩
    have ha := Finset.mem_filter.1 ((Es.filter (· ≤ θ)).max'_mem hA)
    have hb := Finset.mem_filter.1 ((Es.filter (θ < ·)).min'_mem hB)
    refine ⟨(Es.filter (· ≤ θ)).max' hA, (Es.filter (θ < ·)).min' hB,
      ⟨ha.1, hb.1, lt_of_le_of_lt ha.2 hb.2, ?_⟩, ⟨ha.2, hb.2.le⟩⟩
    rintro e he ⟨he1, he2⟩
    rcases le_or_gt e θ with h' | h'
    · have := (Es.filter (· ≤ θ)).le_max' e (Finset.mem_filter.2 ⟨he, h'⟩); linarith
    · have := (Es.filter (θ < ·)).min'_le e (Finset.mem_filter.2 ⟨he, h'⟩); linarith

lemma consec_disjoint {Es : Finset ℝ} {t t' u u' : ℝ} (h : Consec Es t t') (h' : Consec Es u u')
    (hne : (t, t') ≠ (u, u')) : Disjoint (Ioo t t') (Ioo u u') := by
  rw [Set.disjoint_left]
  rintro θ ⟨h1, h2⟩ ⟨h3, h4⟩
  apply hne
  have htu : t = u := by
    rcases lt_trichotomy t u with htu | htu | htu
    · exact absurd ⟨htu, by linarith⟩ (h.2.2.2 u h'.1)
    · exact htu
    · exact absurd ⟨htu, by linarith⟩ (h'.2.2.2 t h.1)
  have htu' : t' = u' := by
    rcases lt_trichotomy t' u' with h5 | h5 | h5
    · exact absurd ⟨by rw [← htu]; exact h.2.2.1, h5⟩ (h'.2.2.2 t' h.2.1)
    · exact h5
    · exact absurd ⟨by rw [htu]; exact h'.2.2.1, h5⟩ (h.2.2.2 u' h'.2.1)
  rw [htu, htu']

/-- Between consecutive points of `Es`, a union of intervals with end points in `Es` either covers the closed
interval or misses the open one. -/
lemma consec_dichotomy {Es : Finset ℝ} (A : Finset ℕ) (I : ℕ → Set ℝ)
    (hI : ∀ j ∈ A, I j = ∅ ∨ (sInf (I j) ∈ Es ∧ sSup (I j) ∈ Es ∧ I j = Icc (sInf (I j)) (sSup (I j))))
    {t t' : ℝ} (h : Consec Es t t') : Icc t t' ⊆ ⋃ j ∈ A, I j ∨ Disjoint (Ioo t t') (⋃ j ∈ A, I j) := by
  by_cases hd : Disjoint (Ioo t t') (⋃ j ∈ A, I j)
  · exact Or.inr hd
  left
  obtain ⟨θ, ⟨h1, h2⟩, hθ⟩ := Set.not_disjoint_iff.1 hd
  obtain ⟨j, hj, hθj⟩ := mem_iUnion₂.1 hθ
  rcases hI j hj with he | ⟨ha, hb, heq⟩
  · rw [he] at hθj; simp at hθj
  rw [heq] at hθj
  have hat : sInf (I j) ≤ t := by
    by_contra hc; push Not at hc
    exact h.2.2.2 _ ha ⟨hc, by linarith [hθj.1]⟩
  have hbt : t' ≤ sSup (I j) := by
    by_contra hc; push Not at hc
    exact h.2.2.2 _ hb ⟨by linarith [hθj.2], hc⟩
  intro x hx
  exact mem_iUnion₂.2 ⟨j, hj, by rw [heq]; exact ⟨hat.trans hx.1, hx.2.trans hbt⟩⟩

lemma sum_image_le' {α β : Type*} [DecidableEq β] (S : Finset α) (g : α → β) (f : β → ℝ) (hf : ∀ x, 0 ≤ f x) :
    ∑ x ∈ S.image g, f x ≤ ∑ y ∈ S, f (g y) := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (g := g) (t := S.image g) (fun y hy => Finset.mem_image_of_mem g hy)]
  refine Finset.sum_le_sum fun x hx => ?_
  obtain ⟨y0, hy0, rfl⟩ := Finset.mem_image.1 hx
  exact Finset.single_le_sum (f := fun y => f (g y)) (fun y _ => hf _) (Finset.mem_filter.2 ⟨hy0, rfl⟩)

/-! ### The decomposition of a union of short segments -/

section Decomp

variable (P : ℝ) (σ : ℕ → Seg)

/-- The parameters at which the segment `i` meets the segment `j`. -/
def Iset (i j : ℕ) : Set ℝ := {θ ∈ Icc (0 : ℝ) 1 | gam P (σ i) θ ∈ gam P (σ j) '' Icc 0 1}

/-- The parameters at which the segment `i` meets an earlier one. -/
def Jset (i : ℕ) : Set ℝ := ⋃ j ∈ Finset.range i, Iset P σ i j

/-- The end points of the intervals `Iset i j`, `j < i`, with `0` and `1`. -/
def Ends (i : ℕ) : Finset ℝ :=
  insert 0 (insert 1 ((Finset.range i).biUnion fun j => {sInf (Iset P σ i j), sSup (Iset P σ i j)}))

open Classical in
/-- The pairs of consecutive end points between which the segment `i` meets no earlier one. -/
def Kept (i : ℕ) : Finset (ℝ × ℝ) :=
  (Ends P σ i ×ˢ Ends P σ i).filter fun p => Consec (Ends P σ i) p.1 p.2 ∧ Disjoint (Ioo p.1 p.2) (Jset P σ i)

/-- The pieces of the segments `i < m`. -/
def pieces (m : ℕ) : Finset Seg :=
  ((Finset.range m).sigma (Kept P σ)).image fun q => piece (σ q.1) q.2.1 q.2.2

variable {P σ}

lemma ends_mem_Icc (i : ℕ) {e : ℝ} (he : e ∈ Ends P σ i) : e ∈ Icc (0 : ℝ) 1 := by
  simp only [Ends, Finset.mem_insert, Finset.mem_biUnion, Finset.mem_range] at he
  have hsub : ∀ j, Iset P σ i j ⊆ Icc 0 1 := fun j θ hθ => hθ.1
  rcases he with rfl | rfl | ⟨j, -, hj⟩
  · exact ⟨le_rfl, zero_le_one⟩
  · exact ⟨zero_le_one, le_rfl⟩
  · simp only [Finset.mem_singleton] at hj
    rcases (Iset P σ i j).eq_empty_or_nonempty with he' | hne
    · rcases hj with rfl | rfl <;> simp [he']
    · have hbb : BddBelow (Iset P σ i j) := ⟨0, fun x hx => (hsub j hx).1⟩
      have hba : BddAbove (Iset P σ i j) := ⟨1, fun x hx => (hsub j hx).2⟩
      rcases hj with rfl | rfl
      · exact hsub j ((param_isClosed P (σ i) (σ j)).csInf_mem hne hbb)
      · exact hsub j ((param_isClosed P (σ i) (σ j)).csSup_mem hne hba)

lemma Iset_shape (hP : 0 < P) (hs : ∀ i, Short P (σ i)) (i j : ℕ) (hj : j ∈ Finset.range i) :
    Iset P σ i j = ∅ ∨ (sInf (Iset P σ i j) ∈ Ends P σ i ∧ sSup (Iset P σ i j) ∈ Ends P σ i ∧
      Iset P σ i j = Icc (sInf (Iset P σ i j)) (sSup (Iset P σ i j))) := by
  rcases (Iset P σ i j).eq_empty_or_nonempty with he | hne
  · exact Or.inl he
  right
  have hmem : ∀ x ∈ ({sInf (Iset P σ i j), sSup (Iset P σ i j)} : Finset ℝ), x ∈ Ends P σ i := fun x hx =>
    Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_biUnion.2 ⟨j, hj, hx⟩))
  exact ⟨hmem _ (by simp), hmem _ (by simp), eq_Icc_of_ordConnected (fun θ hθ => hθ.1)
    (param_isClosed P (σ i) (σ j)) (param_ordConnected hP (hs i) (hs j)) hne⟩

lemma kept_spec {i : ℕ} {p : ℝ × ℝ} (hp : p ∈ Kept P σ i) :
    Consec (Ends P σ i) p.1 p.2 ∧ Disjoint (Ioo p.1 p.2) (Jset P σ i) := by
  classical
  unfold Kept at hp
  exact (Finset.mem_filter.1 hp).2

lemma kept_Icc {i : ℕ} {p : ℝ × ℝ} (hp : p ∈ Kept P σ i) : Icc p.1 p.2 ⊆ Icc 0 1 := fun θ hθ =>
  ⟨(ends_mem_Icc i (kept_spec hp).1.1).1.trans hθ.1, hθ.2.trans (ends_mem_Icc i (kept_spec hp).1.2.1).2⟩

lemma param_eq_toT (σ' : Seg) (θ : ℝ) : proj s N (σ'.1 + θ • σ'.2) = toT s N (gam (s * N) σ' θ) := rfl

/-- **The pieces cover the segments.** -/
theorem segSet_subset_pieces (hP : 0 < s * N) (hs : ∀ i, Short (s * N) (σ i)) {m : ℕ} :
    ∀ i < m, segSet s N (σ i) ⊆ ⋃ τ ∈ pieces (s * N) σ m, segSet s N τ := by
  classical
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
  intro hi z hz
  obtain ⟨θ, hθ, rfl⟩ := hz
  show proj s N ((σ i).1 + θ • (σ i).2) ∈ _
  by_cases hJ : θ ∈ Jset (s * N) σ i
  · obtain ⟨j, hj, ⟨-, t, ht, he⟩⟩ := mem_iUnion₂.1 hJ
    have hji := Finset.mem_range.1 hj
    have : proj s N ((σ i).1 + θ • (σ i).2) = proj s N ((σ j).1 + t • (σ j).2) := by
      rw [param_eq_toT, param_eq_toT, he]
    rw [this]
    exact ih j hji (hji.trans hi) ⟨t, ht, rfl⟩
  · obtain ⟨t, t', hc, hθt⟩ := exists_consec (Ends (s * N) σ i) (by simp [Ends]) (by simp [Ends]) hθ
    rcases consec_dichotomy (Finset.range i) (Iset (s * N) σ i) (Iset_shape hP hs i) hc with hsub | hdis
    · exact absurd (hsub hθt) hJ
    · have hk : (t, t') ∈ Kept (s * N) σ i := by
        unfold Kept; exact Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨hc.1, hc.2.1⟩, hc, hdis⟩
      refine mem_iUnion₂.2 ⟨piece (σ i) t t', Finset.mem_image.2 ⟨⟨i, (t, t')⟩,
        Finset.mem_sigma.2 ⟨Finset.mem_range.2 hi, hk⟩, rfl⟩, ?_⟩
      rw [segSet_piece _ hc.2.2.1.le]
      exact ⟨θ, hθt, rfl⟩

/-- **The union of the pieces is the union of the segments.** -/
theorem union_pieces (hP : 0 < s * N) (hs : ∀ i, Short (s * N) (σ i)) (m : ℕ) :
    ⋃ τ ∈ pieces (s * N) σ m, segSet s N τ = ⋃ i ∈ Finset.range m, segSet s N (σ i) := by
  apply Subset.antisymm
  · refine iUnion₂_subset fun τ hτ => ?_
    obtain ⟨⟨i, p⟩, hq, rfl⟩ := Finset.mem_image.1 hτ
    obtain ⟨hi, hp⟩ := Finset.mem_sigma.1 hq
    refine Subset.trans ?_ (subset_biUnion_of_mem hi)
    rw [segSet_piece _ (kept_spec hp).1.2.2.1.le]
    exact image_mono (kept_Icc hp)
  · exact iUnion₂_subset fun i hi => segSet_subset_pieces hP hs i (Finset.mem_range.1 hi)

end Decomp

/-! ### The cost of the pieces -/

section Cost

variable {σ : ℕ → Seg}

/-- The parameters of the open piece `q` outside `F`. -/
def Bpart (s : ℝ) (N : ℕ) (σ : ℕ → Seg) (F : Set (Torus s N)) (q : (_ : ℕ) × (ℝ × ℝ)) : Set ℝ :=
  {θ ∈ Ioo q.2.1 q.2.2 | proj s N ((σ q.1).1 + θ • (σ q.1).2) ∉ F}

/-- The open piece `q` outside `F`, in `TorE`, if the segment is not a point. -/
def Apart (s : ℝ) (N : ℕ) (σ : ℕ → Seg) (F : Set (Torus s N)) (q : (_ : ℕ) × (ℝ × ℝ)) : Set (TorE (s * N)) :=
  if 0 < eu (σ q.1).2 then gam (s * N) (σ q.1) '' Bpart s N σ F q else ∅

lemma Bpart_subset {F : Set (Torus s N)} {q : (_ : ℕ) × (ℝ × ℝ)} (hq : q.2 ∈ Kept (s * N) σ q.1) :
    Bpart s N σ F q ⊆ Icc 0 1 := fun θ hθ => kept_Icc hq ⟨hθ.1.1.le, hθ.1.2.le⟩

lemma lenOut_le_Apart (hP : 0 < s * N) (hs : ∀ i, Short (s * N) (σ i)) (F : Set (Torus s N))
    {q : (_ : ℕ) × (ℝ × ℝ)} (hq : q.2 ∈ Kept (s * N) σ q.1) (hfin : μH[1] (Apart s N σ F q) ≠ ∞) :
    lenOut s N F (piece (σ q.1) q.2.1 q.2.2) ≤ (μH[1] (Apart s N σ F q)).toReal := by
  have hlt := (kept_spec hq).1.2.2.1
  rw [lenOut_piece _ _ hlt]
  rcases (eu_nonneg (σ q.1).2).eq_or_lt with h0 | hpos
  · rw [← h0, zero_mul]; exact ENNReal.toReal_nonneg
  have hvol : volume {θ ∈ Icc q.2.1 q.2.2 | proj s N ((σ q.1).1 + θ • (σ q.1).2) ∉ F} ≤
      volume (Bpart s N σ F q) := by
    calc volume {θ ∈ Icc q.2.1 q.2.2 | proj s N ((σ q.1).1 + θ • (σ q.1).2) ∉ F}
        ≤ volume (Bpart s N σ F q ∪ {q.2.1, q.2.2}) := by
          refine measure_mono fun θ hθ => ?_
          rcases eq_or_lt_of_le hθ.1.1 with h | h
          · exact Or.inr (by rw [← h]; simp)
          rcases eq_or_lt_of_le hθ.1.2 with h' | h'
          · exact Or.inr (by rw [h']; simp)
          exact Or.inl ⟨⟨h, h'⟩, hθ.2⟩
      _ ≤ volume (Bpart s N σ F q) + volume ({q.2.1, q.2.2} : Set ℝ) := measure_union_le _ _
      _ = volume (Bpart s N σ F q) := by
          rw [(Set.toFinite ({q.2.1, q.2.2} : Set ℝ)).measure_zero volume, add_zero]
  have hB : volume (Bpart s N σ F q) ≠ ∞ :=
    ne_top_of_le_ne_top (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
      (measure_mono fun θ hθ => hθ.1)
  have h1 := vol_le_H hP (hs q.1) (Bpart_subset (F := F) hq)
  rw [Apart, if_pos hpos] at hfin ⊢
  calc eu (σ q.1).2 * (volume {θ ∈ Icc q.2.1 q.2.2 | proj s N ((σ q.1).1 + θ • (σ q.1).2) ∉ F}).toReal
      ≤ eu (σ q.1).2 * (volume (Bpart s N σ F q)).toReal :=
        mul_le_mul_of_nonneg_left (ENNReal.toReal_mono hB hvol) hpos.le
    _ = (ENNReal.ofReal (eu (σ q.1).2) * volume (Bpart s N σ F q)).toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hpos.le]
    _ ≤ _ := ENNReal.toReal_mono hfin h1

lemma Apart_subset (F : Set (Torus s N)) {m : ℕ} {q : (_ : ℕ) × (ℝ × ℝ)}
    (hq : q ∈ (Finset.range m).sigma (Kept (s * N) σ)) :
    Apart s N σ F q ⊆ toT s N ⁻¹' ((⋃ i ∈ Finset.range m, segSet s N (σ i)) \ F) := by
  obtain ⟨hi, hk⟩ := Finset.mem_sigma.1 hq
  unfold Apart
  split_ifs
  · rintro _ ⟨θ, hθ, rfl⟩
    exact ⟨mem_iUnion₂.2 ⟨q.1, hi, θ, Bpart_subset hk hθ, rfl⟩, hθ.2⟩
  · exact empty_subset _

lemma Apart_disjoint (hP : 0 < s * N) (hs : ∀ i, Short (s * N) (σ i)) (F : Set (Torus s N)) (m : ℕ) :
    PairwiseDisjoint (↑((Finset.range m).sigma (Kept (s * N) σ))) (Apart s N σ F) := by
  rintro ⟨i, p⟩ hq ⟨j, p'⟩ hq' hne
  have hk := (Finset.mem_sigma.1 hq).2
  have hk' := (Finset.mem_sigma.1 hq').2
  simp only [Function.onFun, Apart]
  split_ifs with hi hj hj
  · rw [Set.disjoint_left]
    rintro _ ⟨θ, hθ, rfl⟩ ⟨θ', hθ', he⟩
    have hθI := Bpart_subset (F := F) hk hθ
    have hθI' := Bpart_subset (F := F) hk' hθ'
    rcases lt_trichotomy j i with hji | rfl | hij
    · have hJ : θ ∈ Jset (s * N) σ i :=
        mem_iUnion₂.2 ⟨j, Finset.mem_range.2 hji, hθI, θ', hθI', he⟩
      exact Set.disjoint_left.1 (kept_spec hk).2 hθ.1 hJ
    · have hθe : θ' = θ := injOn_gam hP (hs j) hi hθI' hθI he
      subst hθe
      have hpp : (p.1, p.2) ≠ (p'.1, p'.2) := fun h => hne (by
        have : p = p' := by ext <;> simp_all
        rw [this])
      exact Set.disjoint_left.1 (consec_disjoint (kept_spec hk).1 (kept_spec hk').1 hpp) hθ.1 hθ'.1
    · have hJ : θ' ∈ Jset (s * N) σ j :=
        mem_iUnion₂.2 ⟨i, Finset.mem_range.2 hij, hθI', θ, hθI, he.symm⟩
      exact Set.disjoint_left.1 (kept_spec hk').2 hθ'.1 hJ
  all_goals simp

lemma Apart_measurable (F : Set (Torus s N)) (hF : MeasurableSet (toT s N ⁻¹' F)) (hP : 0 < s * N)
    (hs : ∀ i, Short (s * N) (σ i)) {q : (_ : ℕ) × (ℝ × ℝ)} (hq : q.2 ∈ Kept (s * N) σ q.1) :
    MeasurableSet (Apart s N σ F q) := by
  unfold Apart
  split_ifs with hpos
  · have hBm : MeasurableSet (Bpart s N σ F q) := by
      have e : Bpart s N σ F q = Ioo q.2.1 q.2.2 ∩ gam (s * N) (σ q.1) ⁻¹' (toT s N ⁻¹' F)ᶜ := rfl
      rw [e]
      exact measurableSet_Ioo.inter (hF.compl.preimage (continuous_gam _ _).measurable)
    exact hBm.image_of_continuousOn_injOn (continuous_gam _ _).continuousOn
      ((injOn_gam hP (hs q.1) hpos).mono (Bpart_subset hq))
  · exact MeasurableSet.empty

/-- **The cost of the pieces is at most the measure of the union outside `F`.** -/
theorem cost_pieces_le (hP : 0 < s * N) (hs : ∀ i, Short (s * N) (σ i)) (F : Set (Torus s N))
    (hF : MeasurableSet (toT s N ⁻¹' F)) (m : ℕ) :
    ∑ τ ∈ pieces (s * N) σ m, lenOut s N F τ ≤
      (H1E s N ((⋃ i ∈ Finset.range m, segSet s N (σ i)) \ F)).toReal := by
  classical
  set T := (Finset.range m).sigma (Kept (s * N) σ)
  set G := ⋃ i ∈ Finset.range m, segSet s N (σ i)
  -- finiteness
  have hG : G = ⋃ τ ∈ (Finset.range m).image σ, segSet s N τ := by
    simp only [G, Finset.set_biUnion_finset_image]
  have hfinG : μH[1] (toT s N ⁻¹' (G \ F)) ≠ ∞ := by
    refine ne_top_of_le_ne_top ENNReal.ofReal_ne_top (le_trans ?_ (H1E_union_le (s := s) (N := N) ((Finset.range m).image σ) ∅))
    rw [← hG, diff_empty]
    exact measure_mono (preimage_mono diff_subset)
  have hfin : ∀ q ∈ T, μH[1] (Apart s N σ F q) ≠ ∞ := fun q hq =>
    ne_top_of_le_ne_top hfinG (measure_mono (Apart_subset F hq))
  calc ∑ τ ∈ pieces (s * N) σ m, lenOut s N F τ
      ≤ ∑ q ∈ T, lenOut s N F (piece (σ q.1) q.2.1 q.2.2) :=
        sum_image_le' T _ _ fun τ => lenOut_nonneg F τ
    _ ≤ ∑ q ∈ T, (μH[1] (Apart s N σ F q)).toReal :=
        Finset.sum_le_sum fun q hq => lenOut_le_Apart hP hs F (Finset.mem_sigma.1 hq).2 (hfin q hq)
    _ = (∑ q ∈ T, μH[1] (Apart s N σ F q)).toReal := (ENNReal.toReal_sum hfin).symm
    _ = (μH[1] (⋃ q ∈ T, Apart s N σ F q)).toReal := by
        rw [measure_biUnion_finset (Apart_disjoint hP hs F m)
          (fun q hq => Apart_measurable F hF hP hs (Finset.mem_sigma.1 hq).2)]
    _ ≤ (μH[1] (toT s N ⁻¹' (G \ F))).toReal :=
        ENNReal.toReal_mono hfinG (measure_mono (iUnion₂_subset fun q hq => Apart_subset F hq))
    _ = _ := rfl

end Cost

/-! ### Every finite union of segments is a union of pieces -/

lemma Icc_subdiv {m : ℕ} (hm : 0 < m) {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) 1) :
    ∃ k < m, θ ∈ Icc ((k : ℝ) / m) (((k : ℝ) + 1) / m) := by
  have hm' : (0 : ℝ) < m := Nat.cast_pos.2 hm
  by_cases hk : ⌊θ * m⌋₊ < m
  · refine ⟨⌊θ * m⌋₊, hk, ?_, ?_⟩
    · rw [div_le_iff₀ hm']; exact Nat.floor_le (by nlinarith [hθ.1])
    · rw [le_div_iff₀ hm']; exact (Nat.lt_floor_add_one _).le
  · push Not at hk
    have h1 : (m : ℝ) ≤ θ * m := (Nat.cast_le.2 hk).trans (Nat.floor_le (by nlinarith [hθ.1]))
    have hθ1 : θ = 1 := le_antisymm hθ.2 (by nlinarith)
    refine ⟨m - 1, by omega, ?_, ?_⟩
    · rw [hθ1, div_le_one hm', Nat.cast_le]; omega
    · rw [hθ1, Nat.cast_sub hm, Nat.cast_one, sub_add_cancel, div_self hm'.ne']

lemma segSet_subdiv (σ : Seg) {m : ℕ} (hm : 0 < m) :
    segSet s N σ = ⋃ k ∈ Finset.range m, segSet s N (piece σ ((k : ℝ) / m) (((k : ℝ) + 1) / m)) := by
  have hm' : (0 : ℝ) < m := Nat.cast_pos.2 hm
  have hle : ∀ k : ℕ, (k : ℝ) / m ≤ ((k : ℝ) + 1) / m := fun k => by gcongr; linarith
  ext z
  simp only [mem_iUnion, Finset.mem_range, exists_prop]
  constructor
  · rintro ⟨θ, hθ, rfl⟩
    obtain ⟨k, hk, hθk⟩ := Icc_subdiv hm hθ
    refine ⟨k, hk, ?_⟩
    rw [segSet_piece _ (hle k)]
    exact ⟨θ, hθk, rfl⟩
  · rintro ⟨k, hk, hz⟩
    rw [segSet_piece _ (hle k)] at hz
    obtain ⟨θ, hθ, rfl⟩ := hz
    refine ⟨θ, ⟨le_trans (by positivity) hθ.1, hθ.2.trans ?_⟩, rfl⟩
    rw [div_le_one hm']
    have : (k : ℝ) + 1 ≤ m := by exact_mod_cast hk
    exact this

/-- **Every finite union `G` of segments is the union of a family with `Σ_σ lenOut F σ ≤ |G \ F|`.** -/
theorem exists_family_le (hP : 0 < s * N) (S : Finset Seg) (F : Set (Torus s N))
    (hF : MeasurableSet (toT s N ⁻¹' F)) :
    ∃ S' : Finset Seg, (⋃ σ ∈ S', segSet s N σ) = (⋃ σ ∈ S, segSet s N σ) ∧
      ∑ σ ∈ S', lenOut s N F σ ≤ (H1E s N ((⋃ σ ∈ S, segSet s N σ) \ F)).toReal := by
  classical
  -- cut into short pieces
  set m := ⌈(∑ σ ∈ S, eu σ.2) * 8 / (s * N)⌉₊ + 1 with hm_def
  have hm : 0 < m := by omega
  have hm' : (0 : ℝ) < m := Nat.cast_pos.2 hm
  set S1 := S.biUnion fun σ => (Finset.range m).image fun k : ℕ => piece σ ((k : ℝ) / m) (((k : ℝ) + 1) / m)
  have hU1 : (⋃ τ ∈ S1, segSet s N τ) = ⋃ σ ∈ S, segSet s N σ := by
    simp only [S1, Finset.set_biUnion_biUnion, Finset.set_biUnion_finset_image]
    exact iUnion₂_congr fun σ _ => (segSet_subdiv σ hm).symm
  have hshort : ∀ τ ∈ S1, Short (s * N) τ := by
    intro τ hτ
    obtain ⟨σ, hσ, hτ'⟩ := Finset.mem_biUnion.1 hτ
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hτ'
    unfold Short piece
    simp only
    rw [eu_smul]
    have hk : ((k : ℝ) + 1) / m - (k : ℝ) / m = 1 / m := by field_simp; ring
    rw [hk, abs_of_pos (by positivity)]
    have h1 : eu σ.2 ≤ ∑ σ ∈ S, eu σ.2 := Finset.single_le_sum (fun σ _ => eu_nonneg σ.2) hσ
    have h2 : (∑ σ ∈ S, eu σ.2) * 8 / (s * N) ≤ m := by
      rw [hm_def]; push_cast
      linarith [Nat.le_ceil ((∑ σ ∈ S, eu σ.2) * 8 / (s * N))]
    rw [div_le_iff₀ hP] at h2
    rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ hm' (by norm_num : (0 : ℝ) < 8)]
    nlinarith
  -- enumerate
  set l := S1.toList
  set σf : ℕ → Seg := fun i => l.getD i (0, 0)
  have hget : ∀ i (hi : i < l.length), σf i = l[i] := fun i hi => by
    simp only [σf, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  have hdef : ∀ i, l.length ≤ i → σf i = (0, 0) := fun i hi => by
    simp only [σf, List.getD_eq_getElem?_getD, List.getElem?_eq_none hi, Option.getD_none]
  have hs : ∀ i, Short (s * N) (σf i) := by
    intro i
    by_cases hi : i < l.length
    · rw [hget i hi]
      exact hshort _ (Finset.mem_toList.1 (List.getElem_mem hi))
    · rw [hdef i (by omega)]
      unfold Short; simp only [eu]; simp only [Prod.snd_zero, Pi.zero_apply]
      norm_num; positivity
  have hUl : (⋃ i ∈ Finset.range l.length, segSet s N (σf i)) = ⋃ τ ∈ S1, segSet s N τ := by
    ext z
    simp only [mem_iUnion, Finset.mem_range, exists_prop]
    constructor
    · rintro ⟨i, hi, hz⟩
      refine ⟨l[i], Finset.mem_toList.1 (List.getElem_mem hi), ?_⟩
      rwa [← hget i hi]
    · rintro ⟨τ, hτ, hz⟩
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem (Finset.mem_toList.2 hτ)
      refine ⟨i, hi, ?_⟩
      rwa [hget i hi]
  refine ⟨pieces (s * N) σf l.length, ?_, ?_⟩
  · rw [union_pieces hP hs, hUl, hU1]
  · have := cost_pieces_le hP hs F hF l.length
    rwa [hUl, hU1] at this

/-! ### The two definitions of the linear size agree -/

namespace Grid

variable {g : Grid}

lemma period_pos (g : Grid) : 0 < g.s * g.N := by
  rw [← g.hP]
  have : (0 : ℝ) < g.n := Nat.cast_pos.2 (Nat.pos_of_ne_zero g.hn.out)
  exact mul_pos g.ha this

/-- The admissible unions `G` of `eq:contracted-size`: finite unions of segments in `X` which meet every
cube of `X` and whose union with `D` is connected. -/
def AdmSet (g : Grid) (X D : Finset g.Idx) : Set (Set g.T) :=
  {G | (∃ S : Finset Seg, G = ⋃ σ ∈ S, segSet g.s g.N σ) ∧ G ⊆ g.cubes X ∧
    (∀ c ∈ X, (G ∩ g.cube c).Nonempty) ∧ IsPreconnected (G ∪ g.cubes D)}

/-- **The linear size `d(X; D)` of `eq:contracted-size`**, with the one-dimensional measure of `G \ D`. -/
def dMeas (g : Grid) (X D : Finset g.Idx) : ℝ :=
  g.a⁻¹ * sInf ((fun G => (H1E g.s g.N (G \ g.cubes D)).toReal) '' AdmSet g X D)

lemma adm_iff {X D : Finset g.Idx} {S : Finset Seg} :
    g.Adm X D S ↔ (⋃ σ ∈ S, segSet g.s g.N σ) ∈ AdmSet g X D := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨⟨S, rfl⟩, iUnion₂_subset h1, fun c hc => ?_, h3⟩
    obtain ⟨σ, hσ, z, hz1, hz2⟩ := h2 c hc
    exact ⟨z, mem_iUnion₂.2 ⟨σ, hσ, hz1⟩, hz2⟩
  · rintro ⟨-, h1, h2, h3⟩
    refine ⟨fun σ hσ => (subset_biUnion_of_mem hσ).trans h1, fun c hc => ?_, h3⟩
    obtain ⟨z, hz1, hz2⟩ := h2 c hc
    obtain ⟨σ, hσ, hz⟩ := mem_iUnion₂.1 hz1
    exact ⟨σ, hσ, z, hz, hz2⟩

lemma measurable_cubes (D : Finset g.Idx) : MeasurableSet (toT g.s g.N ⁻¹' g.cubes D) := by
  refine (IsClosed.preimage continuous_toT ?_).measurableSet
  exact isClosed_biUnion_finset fun c _ => Metric.isClosed_closedBall

/-- **The two infima agree**: `d(X; D)` with the sum of the lengths outside `D` (`Grid.d`) is the linear size
with the one-dimensional measure of `G \ D` (`dMeas`). -/
theorem d_eq_dMeas (X D : Finset g.Idx) : g.d X D = dMeas g X D := by
  unfold d dMeas
  congr 1
  set C := g.cost D '' {S | g.Adm X D S}
  set M := (fun G => (H1E g.s g.N (G \ g.cubes D)).toReal) '' AdmSet g X D
  have hC0 : ∀ x ∈ C, 0 ≤ x := by rintro _ ⟨S, -, rfl⟩; exact cost_nonneg D S
  have hM0 : ∀ x ∈ M, 0 ≤ x := by rintro _ ⟨G, -, rfl⟩; exact ENNReal.toReal_nonneg
  by_cases hne : {S | g.Adm X D S}.Nonempty
  · obtain ⟨S0, hS0⟩ := hne
    have hCne : C.Nonempty := ⟨_, S0, hS0, rfl⟩
    have hMne : M.Nonempty := ⟨_, _, adm_iff.1 hS0, rfl⟩
    apply le_antisymm
    · refine le_csInf hMne ?_
      rintro _ ⟨G, ⟨⟨S, rfl⟩, hG⟩, rfl⟩
      obtain ⟨S', hU, hc⟩ := exists_family_le g.period_pos S (g.cubes D) (measurable_cubes D)
      have hS' : g.Adm X D S' := adm_iff.2 (by rw [hU]; exact ⟨⟨S, rfl⟩, hG⟩)
      exact (csInf_le ⟨0, hC0⟩ ⟨S', hS', rfl⟩).trans hc
    · refine le_csInf hCne ?_
      rintro _ ⟨S, hS, rfl⟩
      refine (csInf_le ⟨0, hM0⟩ ⟨_, adm_iff.1 hS, rfl⟩).trans ?_
      refine ENNReal.toReal_le_of_le_ofReal (cost_nonneg D S) ?_
      exact H1E_union_le S (g.cubes D)
  · have hC : C = ∅ := by
      rw [not_nonempty_iff_eq_empty] at hne; simp only [C, hne, image_empty]
    have hM : M = ∅ := by
      exact image_eq_empty.2 (eq_empty_of_forall_notMem fun G hG =>
        hne ⟨hG.1.choose, adm_iff.2 (hG.1.choose_spec ▸ hG)⟩)
    rw [hC, hM]

end Grid

/-- **The linear size of `lem:cube-count` is the core's `d(X)`**, with the one-dimensional measure of the union. -/
theorem size_eq_dMeas (s : ℝ) (N : ℕ) [NeZero N] (hs : 0 < s) (X : Finset (Fin 4 → ZMod N)) :
    size s N X = Grid.dMeas (Grid.unitGrid s N hs) X ∅ := by
  rw [← Grid.d_empty_eq_size s N hs X]
  exact Grid.d_eq_dMeas (g := Grid.unitGrid s N hs) X ∅

end Contracted
end CoreLean

end
