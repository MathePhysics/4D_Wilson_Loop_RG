import BlockPoincare.Estimate
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Analysis.Normed.Group.AddCircle

/-!
# The circle `ℝ / Tℤ` cut into `M` arcs

A concrete geometric instance of `BlockPartition`: the circle `AddCircle T` of circumference `T`,
with its quotient distance and its Haar measure of total mass `T`, partitioned into the `M` arcs
`(k T/M, (k+1) T/M]`.  Each arc has measure `T/M` and diameter at most `T/M`, so the block
estimate applies to it with `side = vol.toReal = T/M`.

## Main results

* `Torus.dist_coe_le` — the quotient map `ℝ → AddCircle T` does not increase distances.
* `Torus.arc` — the arcs, as preimages of intervals under the coordinate `coord`.
* `Torus.volume_arc`, `Torus.arc_disjoint`, `Torus.iUnion_arc`, `Torus.dist_le_of_mem_arc`.
* `Torus.arcs` — the `BlockPartition` itself.
* `Torus.hNegNorm_le_arcs` — the block estimate on the circle:
  `‖f‖_{H^{-s}} ≤ (T/M)^((1+2s)/2) ‖f‖_{L²}` for `f` with zero mean on every arc.

## Conventions

The arcs are half-open, `(k l, (k+1) l]` in the coordinate `coord x ∈ (0, T]` given by
`AddCircle.equivIoc T 0`; this makes disjointness and covering immediate from the corresponding
statements for intervals.  The distance is the quotient distance of `AddCircle`, so the diameter
of an arc of length `l` is at most `l`.

## Scope

Everything here is proved for the one-dimensional torus.  **Note on the exponent.**  The
Gagliardo seminorm of this library has the fixed exponent `2 + 2 s`, which is `d + 2 s` in
dimension `d = 2`; on the circle it is therefore not the usual one-dimensional `Hˢ` seminorm, and
`hNegNorm_le_arcs` should be read as the general theorem applied to that seminorm rather than as
a sharp statement about `Hˢ(S¹)`.  The circle is here as a factor of the two-dimensional torus,
where the exponent is the right one.  The two-dimensional torus of the
manuscript is the product of two copies of this; the product of two block partitions is
constructed in `BlockPoincare.Product`.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal Function

namespace BlockPoincare

namespace Torus

variable (T : ℝ) [hT : Fact (0 < T)]

lemma norm_coe_le (z : ℝ) : ‖(z : AddCircle T)‖ ≤ |z| := by
  have h0 : (0 : ℝ) < T := hT.out
  rw [AddCircle.norm_eq' (p := T) h0]
  have habs : T * |T⁻¹ * z| = |z| := by
    rw [abs_mul, abs_of_pos (inv_pos.2 h0), ← mul_assoc, mul_inv_cancel₀ h0.ne', one_mul]
  rcases le_or_gt (1 / 2 : ℝ) |T⁻¹ * z| with h | h  -- totalisation-audit: allow > 0
  · calc T * |T⁻¹ * z - round (T⁻¹ * z)| ≤ T * (1 / 2) := by  -- totalisation-audit: allow > 0
          have := abs_sub_round (T⁻¹ * z)
          nlinarith [h0]
      _ ≤ T * |T⁻¹ * z| := by nlinarith [h0]
      _ = |z| := habs
  · have hz : round (T⁻¹ * z) = 0 := by
      rw [round_eq_zero_iff]
      constructor
      · have := abs_lt.1 h
        linarith [this.1]
      · have := abs_lt.1 h
        linarith [this.2]
    rw [hz]
    simp only [Int.cast_zero, sub_zero]
    exact le_of_eq habs

/-- The quotient map `ℝ → AddCircle T` does not increase distances. -/
lemma dist_coe_le (x y : ℝ) : dist ((x : AddCircle T)) ((y : AddCircle T)) ≤ |x - y| := by
  have h : ((x : AddCircle T)) - ((y : AddCircle T)) = ((x - y : ℝ) : AddCircle T) :=
    (QuotientAddGroup.mk_sub _ x y).symm
  rw [dist_eq_norm, h]
  exact norm_coe_le T (x - y)

/-- The coordinate of a point of the circle in `(0, T]`. -/
def coord (x : AddCircle T) : ℝ := (AddCircle.equivIoc T 0 x : ℝ)

lemma coord_mem (x : AddCircle T) : coord T x ∈ Ioc 0 T := by
  obtain ⟨h1, h2⟩ := (AddCircle.equivIoc T 0 x).2
  refine ⟨h1, ?_⟩
  have h3 : coord T x ≤ 0 + T := h2
  linarith

lemma coe_coord (x : AddCircle T) : ((coord T x : ℝ) : AddCircle T) = x :=
  AddCircle.coe_equivIoc

lemma coord_coe {y : ℝ} (hy : y ∈ Ioc 0 T) : coord T ((y : ℝ) : AddCircle T) = y := by
  have hy' : y ∈ Ioc (0 : ℝ) (0 + T) := by rwa [zero_add]
  rw [coord, AddCircle.equivIoc_coe_eq hy']

lemma measurable_coord : Measurable (coord T) :=
  measurable_subtype_coe.comp (AddCircle.measurableEquivIoc T 0).measurable

variable (M : ℕ)

/-- The `k`-th arc: the points whose coordinate lies in `(k T/M, (k+1) T/M]`. -/
def arc (k : Fin M) : Set (AddCircle T) :=
  coord T ⁻¹' Ioc ((k : ℕ) * (T / M)) (((k : ℕ) + 1) * (T / M))  -- totalisation-audit: allow > 0

lemma measurableSet_arc (k : Fin M) : MeasurableSet (arc T M k) :=
  (measurable_coord T) measurableSet_Ioc

variable {T M}

lemma arc_disjoint (hM : 0 < M) : Pairwise (Disjoint on arc T M) := by
  have hl : 0 < T / M := div_pos hT.out (by exact_mod_cast hM)  -- totalisation-audit: allow > 0
  have key : ∀ k k' : Fin M, (k : ℕ) < (k' : ℕ) → ∀ x, x ∈ arc T M k → x ∈ arc T M k' → False := by
    intro k k' hlt x hx hx'
    simp only [arc, mem_preimage, mem_Ioc] at hx hx'
    have h1 : ((k : ℕ) : ℝ) + 1 ≤ ((k' : ℕ) : ℝ) := by exact_mod_cast hlt
    nlinarith [hx.2, hx'.1, hl]
  intro k k' hkk
  rw [Function.onFun, Set.disjoint_left]
  intro x hx hx'
  rcases lt_trichotomy (k : ℕ) (k' : ℕ) with h | h | h
  · exact key k k' h x hx hx'
  · exact hkk (Fin.ext h)
  · exact key k' k h x hx' hx

lemma iUnion_arc (hM : 0 < M) : ⋃ k, arc T M k = univ := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hl : 0 < T / M := div_pos hT.out hMR  -- totalisation-audit: allow > 0
  have hT0 : T ≠ 0 := hT.out.ne'
  have hM0 : (M : ℝ) ≠ 0 := hMR.ne'
  refine eq_univ_of_forall fun x => ?_
  obtain ⟨hc0, hcT⟩ := coord_mem T x
  set c := coord T x with hc
  set n := ⌈c / (T / M)⌉₊ with hn  -- totalisation-audit: allow > 0
  have hcl : 0 < c / (T / M) := div_pos hc0 hl  -- totalisation-audit: allow > 0
  have hn1 : 1 ≤ n := Nat.one_le_ceil_iff.2 hcl
  have hnM : n ≤ M := by
    refine Nat.ceil_le.2 ?_
    rw [div_le_iff₀ hl]
    calc c ≤ T := hcT
      _ = (M : ℝ) * (T / M) := by field_simp  -- totalisation-audit: allow > 0
  refine mem_iUnion.2 ⟨⟨n - 1, ?_⟩, ?_⟩
  · omega
  · simp only [arc, mem_preimage, mem_Ioc, ← hc]
    have hcast : (((n - 1 : ℕ) : ℝ)) = (n : ℝ) - 1 := by
      have : (1 : ℕ) ≤ n := hn1
      push_cast [Nat.cast_sub this]
      ring
    rw [hcast]
    constructor
    · have hlt : (n : ℝ) - 1 < c / (T / M) := by  -- totalisation-audit: allow > 0
        have := Nat.ceil_lt_add_one (le_of_lt hcl)
        rw [← hn] at this
        linarith
      calc ((n : ℝ) - 1) * (T / M) < (c / (T / M)) * (T / M) := by  -- totalisation-audit: allow > 0
            nlinarith [hl, hlt]
        _ = c := by field_simp
    · have hge : c / (T / M) ≤ (n : ℝ) := Nat.le_ceil _  -- totalisation-audit: allow > 0
      calc c = (c / (T / M)) * (T / M) := by field_simp  -- totalisation-audit: allow > 0
        _ ≤ (n : ℝ) * (T / M) := by nlinarith [hl, hge]  -- totalisation-audit: allow > 0
        _ = ((n : ℝ) - 1 + 1) * (T / M) := by ring  -- totalisation-audit: allow > 0

lemma dist_le_of_mem_arc {k : Fin M} {x y : AddCircle T} (hx : x ∈ arc T M k)
    (hy : y ∈ arc T M k) : dist x y ≤ T / M := by  -- totalisation-audit: allow > 0
  simp only [arc, mem_preimage, mem_Ioc] at hx hy
  have h := dist_coe_le T (coord T x) (coord T y)
  rw [coe_coord, coe_coord] at h
  refine h.trans ?_
  rw [abs_sub_le_iff]
  constructor <;> [nlinarith [hx.1, hx.2, hy.1, hy.2]; nlinarith [hx.1, hx.2, hy.1, hy.2]]

lemma arc_subset_Ioc (hM : 0 < M) (k : Fin M) :
    Ioc (((k : ℕ) : ℝ) * (T / M)) ((((k : ℕ) : ℝ) + 1) * (T / M))  -- totalisation-audit: allow > 0
        ⊆ Ioc (0 : ℝ) T := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hl : 0 < T / M := div_pos hT.out hMR  -- totalisation-audit: allow > 0
  have hk : ((k : ℕ) : ℝ) + 1 ≤ (M : ℝ) := by exact_mod_cast k.isLt
  have hT' : (M : ℝ) * (T / M) = T := by field_simp  -- totalisation-audit: allow > 0
  rintro y ⟨hy1, hy2⟩
  constructor
  · have : 0 ≤ ((k : ℕ) : ℝ) * (T / M) := by positivity  -- totalisation-audit: allow > 0
    linarith
  · nlinarith [hl, hk, hy2]

lemma volume_arc (hM : 0 < M) (k : Fin M) :
    volume (arc T M k) = ENNReal.ofReal (T / M) := by  -- totalisation-audit: allow > 0
  have hmp := AddCircle.measurePreserving_mk T 0
  have hms : MeasurableSet (arc T M k) := measurableSet_arc T M k
  have hpre : MeasurableSet (((↑) : ℝ → AddCircle T) ⁻¹' arc T M k) :=
    AddCircle.measurable_mk' hms
  have key : ((↑) : ℝ → AddCircle T) ⁻¹' arc T M k ∩ Ioc 0 (0 + T)
      = Ioc (((k : ℕ) : ℝ) * (T / M)) ((((k : ℕ) : ℝ) + 1) * (T /  -- totalisation-audit: allow > 0
          M)) := by
    ext y
    simp only [mem_inter_iff, mem_preimage, arc, mem_Ioc]
    constructor
    · rintro ⟨hy1, hy2⟩
      have hy' : y ∈ Ioc (0 : ℝ) T := by
        refine ⟨hy2.1, ?_⟩
        have := hy2.2
        linarith
      rwa [coord_coe T hy'] at hy1
    · intro hy
      have hy' : y ∈ Ioc (0 : ℝ) T := arc_subset_Ioc hM k hy
      refine ⟨?_, hy'.1, by have := hy'.2; linarith⟩
      rwa [coord_coe T hy']
  rw [← hmp.measure_preimage hms.nullMeasurableSet, Measure.restrict_apply hpre, key,
    Real.volume_Ioc]
  congr 1
  ring

/-- The circle `AddCircle T` cut into `M` arcs of length `T / M`. -/
def arcs (hM : 0 < M) : BlockPartition (AddCircle T) volume (Fin M) where
  block := arc T M
  side := T / M  -- totalisation-audit: allow > 0
  vol := ENNReal.ofReal (T / M)  -- totalisation-audit: allow > 0
  measurableSet_block := measurableSet_arc T M
  disjoint_block := arc_disjoint hM
  iUnion_block := iUnion_arc hM
  measure_block := volume_arc hM
  vol_ne_zero := by
    have hMR : (0 : ℝ) < M := by exact_mod_cast hM
    simp [ENNReal.ofReal_eq_zero, not_le, div_pos hT.out hMR]
  vol_ne_top := ENNReal.ofReal_ne_top
  dist_le := fun _ _ hx _ hy => dist_le_of_mem_arc hx hy
  side_nonneg := div_nonneg hT.out.le (Nat.cast_nonneg M)

@[simp] lemma arcs_side (hM : 0 < M) : (arcs (T := T) hM).side = T
    / M := rfl  -- totalisation-audit: allow > 0

@[simp] lemma arcs_vol_toReal (hM : 0 < M) : ((arcs (T :=
    T) hM).vol).toReal = T / M := by  -- totalisation-audit: allow finite, > 0
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  rw [show (arcs (T := T) hM).vol = ENNReal.ofReal (T / M) from  -- totalisation-audit: allow > 0
      rfl,
    ENNReal.toReal_ofReal (div_pos hT.out hMR).le]

lemma sqrt_arc_const {l s : ℝ} (hl : 0 < l) :
    Real.sqrt (l ^ (2 + 2 * s) / l) = l ^ ((1 + 2 * s) / 2) := by  -- totalisation-audit: allow > 0
  have h2 : l ^ (1 + 2 * s) * l ^ (1 : ℝ) = l ^ (2 + 2 * s) := by
    rw [← Real.rpow_add hl]
    congr 1
    ring
  rw [Real.rpow_one] at h2
  have h1 : l ^ (2 + 2 * s) / l = l ^ (1 + 2 * s) := by  -- totalisation-audit: allow > 0
    rw [div_eq_iff hl.ne', ← h2]
  rw [h1, Real.sqrt_eq_rpow, ← Real.rpow_mul hl.le]
  congr 1
  ring

/-- **The block estimate on the circle.**  If `f ∈ L²` has zero integral on every arc of a
subdivision of `AddCircle T` into `M` equal arcs, then
`‖f‖_{H^{-s}} ≤ (T/M)^((1+2s)/2) ‖f‖_{L²}`. -/
theorem hNegNorm_le_arcs {s : ℝ} {f : AddCircle T → ℝ} (hM : 0 < M) (hs : 0 < s)
    (hf : MemLp f 2 volume) (hzero : ∀ k, ∫ x in arc T M k, f x  -- totalisation-audit: allow L1 hyp
        = 0) :
    hNegNorm s volume f
      ≤ ENNReal.ofReal ((T / M) ^ ((1 + 2 * s) / 2) *  -- totalisation-audit: allow > 0
          Real.sqrt (∫ x, f x ^ 2 ∂(volume : Measure (AddCircle  -- totalisation-audit: allow L1 hyp
              T)))) := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have h := hNegNorm_le_of_blockIntegral_zero (arcs (T := T) hM) hs hf hzero
  rwa [arcs_side, arcs_vol_toReal, sqrt_arc_const (div_pos hT.out hMR)] at h

end Torus

end BlockPoincare
