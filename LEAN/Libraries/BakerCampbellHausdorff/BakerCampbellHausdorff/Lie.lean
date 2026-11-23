import BakerCampbellHausdorff.Dexp
import BakerCampbellHausdorff.GroupLaw
import BakerCampbellHausdorff.Product
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Calculus.MeanValue

/-!
# The Lie-algebraic Baker–Campbell–Hausdorff theorem

Let `𝔤` be a closed real Lie subalgebra of a real Banach algebra `𝔸`: a closed `ℝ`-submodule with
`x y - y x ∈ 𝔤` for `x, y ∈ 𝔤`.  Then `bch ℝ X Y = log (e^X e^Y) ∈ 𝔤` for small `X, Y ∈ 𝔤`, and
so is the logarithm of any short product of exponentials of elements of `𝔤`.  Consequently every
homogeneous term of the BCH series, evaluated at `X, Y ∈ 𝔤`, lies in `𝔤`: it is a limit of Lie
polynomials in `X` and `Y`.  (`mathlib`'s `LieRing.ofAssociativeRing` is only a local instance,
so `𝔤` is a `Submodule ℝ 𝔸` with an explicit bracket-closure hypothesis.)

## Main results

* `bch_mem`: `X, Y ∈ 𝔤`, `‖X‖ + ‖Y‖ < 1/10` ⟹ `bch ℝ X Y ∈ 𝔤`.
* `bchProd_mem`: `Xᵢ ∈ 𝔤`, `∑ ‖Xᵢ‖ < 1/10` ⟹ `log (e^X₀ ⋯ e^Xₘ₋₁) ∈ 𝔤`.
* `bchSeries_apply_diag_mem`: `bchSeries ℝ 𝔸 n (X, Y) ∈ 𝔤` for all `n`.
* `bch_mem_of_isScalarTower`, `bchProd_mem_of_isScalarTower`: the same for `bch 𝕂`, e.g. for a
  real Lie algebra such as `𝔰𝔲(n)` inside a complex Banach algebra (`log1p_eq_log1p_real`).
* `mem_of_forall_dual`, `coeff_mem_of_hasFPowerSeriesAt`: the two closedness arguments.

## Proof

Put `Z t = log (e^W e^(t Y))` for `W, Y ∈ 𝔤` and `t ∈ [0, 1]`.  Write `S` for the closed
subalgebra of operators `T : 𝔸 →L[ℝ] 𝔸` with `T 𝔤 ⊆ 𝔤` (`preserving`); it contains `ad X` for
`X ∈ 𝔤` and is closed under `exp`, `log1p` and convergent power series.

1. `e^(ad Z) = Ad (e^Z) = Ad (e^W) Ad (e^(t Y)) = e^(ad W) e^(ad (t Y)) ∈ S`, and `ad Z` is small,
   so `ad Z = log (e^(ad Z)) ∈ S` — using `log ∘ exp = id` in the Banach algebra `𝔸 →L[ℝ] 𝔸`.
   This does not presuppose `Z ∈ 𝔤` (`ad_log1p_mem_preserving`).
2. Differentiating `e^(Z t) = e^W e^(t Y)` with `D exp (Z) = e^Z · (1 - e^(-ad Z)) / ad Z`
   (`BakerCampbellHausdorff.Dexp`) gives `Φ Z' = Y` with `Φ = (1 - e^(-ad Z)) / ad Z ∈ S` close to
   `1`; its Neumann-series inverse lies in `S`, so `Z' ∈ 𝔤` (`deriv_mem_of_dexp`).
3. A continuous functional `f` vanishing on `𝔤` has `(f ∘ Z)' = f (Z') = 0`, so
   `f (Z 1) = f (Z 0) = f W = 0`; by Hahn–Banach, `Z 1 ∈ 𝔤` (`log1p_mem_of_dexp`).
-/

noncomputable section

open NormedSpace Filter Set
open scoped Topology

namespace BakerCampbellHausdorff

section Preserving

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]

/-- The operators preserving a submodule `𝔤`: a subalgebra of `𝔸 →L[ℝ] 𝔸`. -/
def preserving (𝔤 : Submodule ℝ 𝔸) : Subalgebra ℝ (𝔸 →L[ℝ] 𝔸) where
  carrier := {T | ∀ x ∈ 𝔤, T x ∈ 𝔤}
  mul_mem' hS hT x hx := hS _ (hT x hx)
  add_mem' hS hT x hx := 𝔤.add_mem (hS x hx) (hT x hx)
  algebraMap_mem' r x hx := by
    rw [Algebra.algebraMap_eq_smul_one]
    change r • x ∈ 𝔤
    exact 𝔤.smul_mem r hx

variable {𝔤 : Submodule ℝ 𝔸}

theorem mem_preserving {T : 𝔸 →L[ℝ] 𝔸} : T ∈ preserving 𝔤 ↔ ∀ x ∈ 𝔤, T x ∈ 𝔤 := Iff.rfl

theorem isClosed_preserving (h𝔤 : IsClosed (𝔤 : Set 𝔸)) :
    IsClosed (preserving 𝔤 : Set (𝔸 →L[ℝ] 𝔸)) := by
  have h : (preserving 𝔤 : Set (𝔸 →L[ℝ] 𝔸)) =
      ⋂ x ∈ 𝔤, (fun T : 𝔸 →L[ℝ] 𝔸 => T x) ⁻¹' (𝔤 : Set 𝔸) := by
    ext T
    simp only [SetLike.mem_coe, mem_iInter, mem_preimage]
    exact mem_preserving
  rw [h]
  exact isClosed_biInter fun x _ => h𝔤.preimage (continuous_eval_const x)

/-- `ad X` preserves a Lie subalgebra containing `X`. -/
theorem ad_mem_preserving (hlie : ∀ x ∈ 𝔤, ∀ y ∈ 𝔤, x * y - y * x ∈ 𝔤) {X : 𝔸} (hX : X ∈ 𝔤) :
    ad ℝ X ∈ preserving 𝔤 := fun x hx => hlie X hX x hx

/-- A convergent series of operators preserving a closed subspace preserves it. -/
theorem mem_preserving_of_hasSum (h𝔤 : IsClosed (𝔤 : Set 𝔸)) {f : ℕ → 𝔸 →L[ℝ] 𝔸}
    {T : 𝔸 →L[ℝ] 𝔸} (hf : HasSum f T) (hmem : ∀ n, f n ∈ preserving 𝔤) :
    T ∈ preserving 𝔤 :=
  (isClosed_preserving h𝔤).mem_of_tendsto hf.tendsto_sum_nat
    (Eventually.of_forall fun _ => Subalgebra.sum_mem _ fun n _ => hmem n)

variable [CompleteSpace 𝔸]

theorem exp_mem_preserving (h𝔤 : IsClosed (𝔤 : Set 𝔸)) {T : 𝔸 →L[ℝ] 𝔸}
    (hT : T ∈ preserving 𝔤) : exp T ∈ preserving 𝔤 :=
  mem_preserving_of_hasSum h𝔤 (exp_series_hasSum_exp' (𝕂 := ℝ) T) fun n =>
    Subalgebra.smul_mem _ (Subalgebra.pow_mem _ hT n) _

theorem log1p_mem_preserving (h𝔤 : IsClosed (𝔤 : Set 𝔸)) {T : 𝔸 →L[ℝ] 𝔸}
    (hT : T ∈ preserving 𝔤) (hT1 : ‖T‖ < 1) : log1p ℝ T ∈ preserving 𝔤 :=
  mem_preserving_of_hasSum h𝔤 (hasSum_log1p (𝕂 := ℝ) hT1) fun n =>
    Subalgebra.smul_mem _ (Subalgebra.pow_mem _ hT n) _

theorem expSubOneDiv_mem_preserving (h𝔤 : IsClosed (𝔤 : Set 𝔸)) {T : 𝔸 →L[ℝ] 𝔸}
    (hT : T ∈ preserving 𝔤) : expSubOneDiv ℝ T ∈ preserving 𝔤 :=
  mem_preserving_of_hasSum h𝔤 (hasSum_expSubOneDiv (𝕂 := ℝ) T) fun n =>
    Subalgebra.smul_mem _ (Subalgebra.pow_mem _ hT n) _

/-- **Neumann series**: an operator `B` preserving `𝔤` with `‖1 - B‖ < 1` has a left inverse
preserving `𝔤`. -/
theorem exists_leftInverse_mem_preserving (h𝔤 : IsClosed (𝔤 : Set 𝔸)) {B : 𝔸 →L[ℝ] 𝔸}
    (hB : B ∈ preserving 𝔤) (hB1 : ‖1 - B‖ < 1) :
    ∃ C ∈ preserving 𝔤, C * B = 1 := by
  have hS := (summable_geometric_of_norm_lt_one hB1).hasSum
  refine ⟨_, mem_preserving_of_hasSum h𝔤 hS fun n =>
    Subalgebra.pow_mem _ (Subalgebra.sub_mem _ (Subalgebra.one_mem _) hB) n, ?_⟩
  have h := geom_series_mul_neg (1 - B) hB1
  rwa [sub_sub_cancel] at h

end Preserving

section Curve

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] {𝔤 : Submodule ℝ 𝔸}

/-- A continuous linear functional bounded below on a subspace vanishes there. -/
theorem eq_zero_of_forall_lt {f : StrongDual ℝ 𝔸} {r : ℝ} (hf : ∀ b ∈ 𝔤, r < f b) {b : 𝔸}
    (hb : b ∈ 𝔤) : f b = 0 := by
  by_contra hne
  have h := hf (((r - 1) / f b) • b) (𝔤.smul_mem _ hb)  -- totalisation-audit: allow f b ≠ 0
  rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hne] at h
  linarith

/-- **Hahn–Banach**: a point killed by every continuous functional that vanishes on a closed
subspace `𝔤` lies in `𝔤`. -/
theorem mem_of_forall_dual (h𝔤 : IsClosed (𝔤 : Set 𝔸)) {z : 𝔸}
    (h : ∀ f : StrongDual ℝ 𝔸, (∀ b ∈ 𝔤, f b = 0) → f z = 0) : z ∈ 𝔤 := by
  by_contra hz
  obtain ⟨f, r, hfz, hf⟩ := geometric_hahn_banach_point_closed 𝔤.convex h𝔤 hz
  have h0 : r < 0 := by simpa using hf 0 𝔤.zero_mem
  have h1 := h f fun b hb => eq_zero_of_forall_lt hf hb
  linarith

variable [CompleteSpace 𝔸]

/-- Along `t ↦ log (e^W e^(t Y))`, `ad` of the logarithm preserves `𝔤`: it is the logarithm of
`Ad (e^W e^(t Y)) = e^(ad W) e^(ad (t Y))`. -/
theorem ad_log1p_mem_preserving (h𝔤 : IsClosed (𝔤 : Set 𝔸))
    (hlie : ∀ x ∈ 𝔤, ∀ y ∈ 𝔤, x * y - y * x ∈ 𝔤) {W V Z : 𝔸} (hW : W ∈ 𝔤) (hV : V ∈ 𝔤)
    (hZ : exp Z = exp W * exp V) (hZ8 : ‖Z‖ < 1 / 8) :  -- totalisation-audit: allow literal
    ad ℝ Z ∈ preserving 𝔤 := by
  have hnegZ : exp (-Z) = exp (-V) * exp (-W) := by
    refine left_inv_eq_right_inv (exp_neg_mul_exp ℝ Z) ?_
    rw [hZ, mul_assoc, ← mul_assoc (exp V), exp_mul_exp_neg ℝ, one_mul, exp_mul_exp_neg ℝ]
  have hexpad : ∀ x, exp (ad ℝ Z) x = exp (ad ℝ W) (exp (ad ℝ V) x) := fun x => by
    rw [exp_ad_apply, exp_ad_apply, exp_ad_apply, hZ, hnegZ]
    simp only [mul_assoc]
  have hmem : exp (ad ℝ Z) ∈ preserving 𝔤 := fun x hx => by
    rw [hexpad]
    exact exp_mem_preserving h𝔤 (ad_mem_preserving hlie hW) _
      (exp_mem_preserving h𝔤 (ad_mem_preserving hlie hV) x hx)
  have had : ‖ad ℝ Z‖ < 1 / 4 :=  -- totalisation-audit: allow literal
    (norm_ad_le Z).trans_lt (by linarith)
  rw [← log1p_exp_sub_one ℝ had]
  refine log1p_mem_preserving h𝔤 (Subalgebra.sub_mem _ hmem (Subalgebra.one_mem _)) ?_
  linarith [norm_exp_sub_one_lt ℝ had]

/-- The velocity of `t ↦ log (e^W e^(t Y))` lies in `𝔤`: if `exp ∘ Z` has derivative
`e^Z Y` and `ad Z` preserves `𝔤`, then `Z' = ((1 - e^(-ad Z)) / ad Z)⁻¹ Y ∈ 𝔤`. -/
theorem deriv_mem_of_dexp (h𝔤 : IsClosed (𝔤 : Set 𝔸)) {Z Z' Y : 𝔸} (hY : Y ∈ 𝔤)
    (had : ad ℝ Z ∈ preserving 𝔤) (hZ8 : ‖Z‖ < 1 / 8)  -- totalisation-audit: allow literal
    (hd : exp Z * expSubOneDiv ℝ (-ad ℝ Z) Z' = exp Z * Y) : Z' ∈ 𝔤 := by
  have hΦ : expSubOneDiv ℝ (-ad ℝ Z) ∈ preserving 𝔤 :=
    expSubOneDiv_mem_preserving h𝔤 (Subalgebra.neg_mem _ had)
  have hΦ1 : ‖1 - expSubOneDiv ℝ (-ad ℝ Z)‖ < 1 := by
    rw [norm_sub_rev]
    refine (norm_expSubOneDiv_sub_one_le _).trans_lt ?_
    have h1 : ‖-ad ℝ Z‖ ≤ 1 / 4 := by  -- totalisation-audit: allow literal
      rw [norm_neg]
      linarith [norm_ad_le (𝕂 := ℝ) Z]
    have h2 := Real.exp_bound_div_one_sub_of_interval'
      (x := 1 / 4) (by norm_num) (by norm_num)  -- totalisation-audit: allow literal
    have h3 : Real.exp ‖-ad ℝ Z‖ ≤ Real.exp (1 / 4) :=  -- totalisation-audit: allow literal
      Real.exp_le_exp.mpr h1
    norm_num at h2
    linarith
  obtain ⟨C, hC, hCΦ⟩ := exists_leftInverse_mem_preserving h𝔤 hΦ hΦ1
  have hΦZ' : expSubOneDiv ℝ (-ad ℝ Z) Z' = Y := by
    have h := congrArg (fun a => exp (-Z) * a) hd
    simpa only [← mul_assoc, exp_neg_mul_exp ℝ, one_mul] using h
  have h := congrArg (fun T : 𝔸 →L[ℝ] 𝔸 => T Z') hCΦ
  change C (expSubOneDiv ℝ (-ad ℝ Z) Z') = Z' at h
  rw [← h, hΦZ']
  exact hC Y hY

/-- **Core lemma.**  If `W, Y ∈ 𝔤`, `‖W‖ < 1/4` and `‖e^W e^(t Y) - 1‖ < 1/9` for `t ∈ [0, 1]`,
then `log (e^W e^Y) ∈ 𝔤`.  The derivative formula for `exp` enters as the hypothesis `hdexp`. -/
theorem log1p_mem_of_dexp (h𝔤 : IsClosed (𝔤 : Set 𝔸))
    (hlie : ∀ x ∈ 𝔤, ∀ y ∈ 𝔤, x * y - y * x ∈ 𝔤)
    (hdexp : ∀ Z : 𝔸,
      HasFDerivAt (exp : 𝔸 → 𝔸) (mulLeft ℝ (exp Z) * expSubOneDiv ℝ (-ad ℝ Z)) Z)
    {W Y : 𝔸} (hW : W ∈ 𝔤) (hY : Y ∈ 𝔤)
    (hW4 : ‖W‖ < 1 / 4)  -- totalisation-audit: allow literal
    (hsmall : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖exp W * exp (t • Y) - 1‖ < 1 / 9) :  -- totalisation-audit: allow literal
    log1p ℝ (exp W * exp Y - 1) ∈ 𝔤 := by
  set u : ℝ → 𝔸 := fun t => exp W * exp (t • Y) - 1 with hu_def
  set Z : ℝ → 𝔸 := fun t => log1p ℝ (u t) with hZ_def
  have hu' : ∀ t, HasDerivAt u (exp W * (exp (t • Y) * Y)) t := fun t =>
    ((hasDerivAt_exp_smul_const (𝕂 := ℝ) Y t).const_mul (exp W)).sub_const 1
  have key : ∀ t ∈ Icc (0 : ℝ) 1, ∃ z, HasDerivAt Z z t ∧ z ∈ 𝔤 := by
    intro t ht
    have hut := hsmall t ht
    have hu1 : ‖u t‖ < 1 := by linarith
    obtain ⟨D, hD⟩ := (analyticAt_log1p (𝕂 := ℝ) hu1).differentiableAt
    have hZd : HasDerivAt Z (D (exp W * (exp (t • Y) * Y))) t := hD.comp_hasDerivAt t (hu' t)
    refine ⟨_, hZd, ?_⟩
    have hexpZ : exp (Z t) = exp W * exp (t • Y) := by
      simp only [hZ_def, hu_def]
      rw [exp_log1p ℝ hu1, add_sub_cancel]
    have hZ8 : ‖Z t‖ < 1 / 8 := by  -- totalisation-audit: allow literal
      refine (norm_log1p_le_div hu1).trans_lt ?_
      have h0 := norm_nonneg (u t)
      rw [div_lt_iff₀ (by linarith)]
      linarith
    have had := ad_log1p_mem_preserving h𝔤 hlie hW (𝔤.smul_mem t hY) hexpZ hZ8
    refine deriv_mem_of_dexp h𝔤 hY had hZ8 ?_
    -- differentiate `exp (Z s) = 1 + u s` at `t`
    have hev : ∀ᶠ s in 𝓝 t, exp (Z s) = 1 + u s := by
      have hc : ContinuousAt (fun s => ‖u s‖) t :=
        continuous_norm.continuousAt.comp (hu' t).continuousAt
      filter_upwards [hc.eventually_lt continuousAt_const hu1] with s hs
      exact exp_log1p ℝ hs
    have h1 : HasDerivAt (fun s => exp (Z s))
        ((mulLeft ℝ (exp (Z t)) * expSubOneDiv ℝ (-ad ℝ (Z t)))
          (D (exp W * (exp (t • Y) * Y)))) t :=
      (hdexp (Z t)).comp_hasDerivAt t hZd
    have h2 : HasDerivAt (fun s => exp (Z s)) (exp W * (exp (t • Y) * Y)) t :=
      ((hu' t).const_add 1).congr_of_eventuallyEq hev
    have h3 := h1.unique h2
    change exp (Z t) * expSubOneDiv ℝ (-ad ℝ (Z t)) (D (exp W * (exp (t • Y) * Y))) = _ at h3
    rw [h3, hexpZ, mul_assoc]
  refine mem_of_forall_dual h𝔤 fun f hf => ?_
  have hderiv : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt (fun s => f (Z s)) 0 t := fun t ht => by
    obtain ⟨z, hz, hzg⟩ := key t ht
    have h := f.hasFDerivAt.comp_hasDerivAt t hz
    rwa [hf _ hzg] at h
  have hconst := constant_of_has_deriv_right_zero
    (fun t ht => (hderiv t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hderiv t (Ico_subset_Icc_self ht)).hasDerivWithinAt) 1
    (right_mem_Icc.mpr zero_le_one)
  have hZ0 : Z 0 = W := by
    simp only [hZ_def, hu_def, zero_smul, exp_zero, mul_one]
    exact log1p_exp_sub_one ℝ hW4
  have hZ1 : Z 1 = log1p ℝ (exp W * exp Y - 1) := by
    simp only [hZ_def, hu_def, one_smul]
  change f (Z 1) = f (Z 0) at hconst
  rw [← hZ1, hconst, hZ0]
  exact hf W hW

end Curve

section Coefficients

variable {𝔸 : Type*} [NormedAddCommGroup 𝔸] [NormedSpace ℝ 𝔸] {𝔤 : Submodule ℝ 𝔸}

/-- If `f s ∈ 𝔤` for all small `s > 0` and `f` has power series `q` at `0`, then every coefficient
of `q` lies in the closed subspace `𝔤`: `qₙ = lim_{s → 0⁺} s⁻ⁿ (f s - ∑_{k < n} sᵏ qₖ)`. -/
theorem coeff_mem_of_hasFPowerSeriesAt (h𝔤 : IsClosed (𝔤 : Set 𝔸)) {f : ℝ → 𝔸}
    {q : FormalMultilinearSeries ℝ ℝ 𝔸} (hf : HasFPowerSeriesAt f q 0)
    (hmem : ∀ᶠ s in 𝓝[>] (0 : ℝ), f s ∈ 𝔤) (n : ℕ) : q.coeff n ∈ 𝔤 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  have hpart : ∀ s : ℝ, q.partialSum n s ∈ 𝔤 := fun s => by
    refine Submodule.sum_mem _ fun k hk => ?_
    rw [q.apply_eq_pow_smul_coeff]
    exact 𝔤.smul_mem _ (ih k (Finset.mem_range.mp hk))
  obtain ⟨C, hC⟩ := (hf.isBigO_sub_partialSum_pow (n + 1)).bound
  set g : ℝ → 𝔸 := fun s => (s ^ n)⁻¹ • (f s - q.partialSum n s) with hg
  have hlim : Tendsto g (𝓝[>] 0) (𝓝 (q.coeff n)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun s => norm_nonneg _) ?_
      (g := fun s => C * s) ?_
    · filter_upwards [nhdsWithin_le_nhds hC, self_mem_nhdsWithin] with s hs hs0
      have hs0' : (0 : ℝ) < s := hs0
      have hpow : (0 : ℝ) < s ^ n := pow_pos hs0' n
      have hP : q.partialSum (n + 1) s = q.partialSum n s + s ^ n • q.coeff n := by
        rw [← q.apply_eq_pow_smul_coeff]
        exact Finset.sum_range_succ _ _
      have e : g s - q.coeff n = (s ^ n)⁻¹ • (f s - q.partialSum (n + 1) s) := by
        rw [hP, show f s - (q.partialSum n s + s ^ n • q.coeff n) =
          (f s - q.partialSum n s) - s ^ n • q.coeff n by abel, smul_sub, smul_smul,
          inv_mul_cancel₀ hpow.ne', one_smul]
      rw [zero_add, norm_pow, norm_norm, Real.norm_of_nonneg hs0'.le] at hs
      rw [e, norm_smul, norm_inv, norm_pow, Real.norm_of_nonneg hs0'.le]
      calc (s ^ n)⁻¹ * ‖f s - q.partialSum (n + 1) s‖ ≤ (s ^ n)⁻¹ * (C * s ^ (n + 1)) :=
            mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr hpow.le)
        _ = C * s := by
            rw [pow_succ]
            field_simp
    · have h : Tendsto (fun s : ℝ => C * s) (𝓝 0) (𝓝 (C * 0)) :=
        tendsto_const_nhds.mul tendsto_id
      rw [mul_zero] at h
      exact tendsto_nhdsWithin_of_tendsto_nhds h
  refine h𝔤.mem_of_tendsto hlim ?_
  filter_upwards [hmem] with s hs
  exact 𝔤.smul_mem _ (𝔤.sub_mem hs (hpart s))

end Coefficients

section Real

variable {𝕂 𝔸 : Type*} [RCLike 𝕂] [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] [NormedAlgebra ℝ 𝔸]
  [IsScalarTower ℝ 𝕂 𝔸]

theorem logCoeff_eq_ofReal (n : ℕ) : logCoeff 𝕂 n = (logCoeff ℝ n : 𝕂) := by
  rcases n with _ | n
  · simp
  · simp [logCoeff_succ]

/-- `log1p` does not depend on the scalar field: over `𝕂` and over `ℝ` it is the same series. -/
theorem log1p_eq_log1p_real (u : 𝔸) : log1p 𝕂 u = log1p ℝ u := by
  rw [log1p_eq_tsum, log1p_eq_tsum]
  congr 1
  funext n
  rw [logCoeff_eq_ofReal, RCLike.real_smul_eq_coe_smul (K := 𝕂)]

theorem bch_eq_bch_real (X Y : 𝔸) : bch 𝕂 X Y = bch ℝ X Y :=
  log1p_eq_log1p_real _

theorem bchProd_eq_bchProd_real {m : ℕ} (X : Fin m → 𝔸) : bchProd 𝕂 X = bchProd ℝ X :=
  log1p_eq_log1p_real _

end Real

theorem exp_one_tenth_lt :
    Real.exp (1 / 10) < 10 / 9 := by  -- totalisation-audit: allow literal
  have h := Real.exp_bound_div_one_sub_of_interval'
    (x := 1 / 10) (by norm_num) (by norm_num)  -- totalisation-audit: allow literal
  norm_num at h ⊢
  linarith

section Main

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] {𝔤 : Submodule ℝ 𝔸}

/-- **Lie-algebraic Baker–Campbell–Hausdorff theorem.**  If `𝔤` is a closed real Lie subalgebra
of `𝔸` and `X, Y ∈ 𝔤` with `‖X‖ + ‖Y‖ < 1/10`, then `bch ℝ X Y = log (e^X e^Y) ∈ 𝔤`. -/
theorem bch_mem (h𝔤 : IsClosed (𝔤 : Set 𝔸)) (hlie : ∀ x ∈ 𝔤, ∀ y ∈ 𝔤, x * y - y * x ∈ 𝔤)
    {X Y : 𝔸} (hX : X ∈ 𝔤) (hY : Y ∈ 𝔤)
    (h : ‖X‖ + ‖Y‖ < 1 / 10) :  -- totalisation-audit: allow literal
    bch ℝ X Y ∈ 𝔤 := by
  refine log1p_mem_of_dexp h𝔤 hlie
    (fun Z => BakerCampbellHausdorff.hasFDerivAt_exp (𝕂 := ℝ) Z) hX hY
    (by linarith [norm_nonneg Y]) fun t ht => ?_
  have h1 := norm_exp_mul_exp_sub_one_le ℝ X (t • Y)
  have ht' : ‖t • Y‖ ≤ ‖Y‖ := by
    rw [norm_smul, Real.norm_of_nonneg ht.1]
    exact mul_le_of_le_one_left (norm_nonneg Y) ht.2
  have h2 : Real.exp (‖X‖ + ‖t • Y‖) ≤ Real.exp (1 / 10) :=  -- totalisation-audit: allow literal
    Real.exp_le_exp.mpr (by linarith)
  linarith [exp_one_tenth_lt]

/-- **Lie-algebraic BCH for products**: if all `Xᵢ ∈ 𝔤` and `∑ ‖Xᵢ‖ < 1/10`, then
`log (e^X₀ ⋯ e^Xₘ₋₁) ∈ 𝔤`. -/
theorem bchProd_mem (h𝔤 : IsClosed (𝔤 : Set 𝔸)) (hlie : ∀ x ∈ 𝔤, ∀ y ∈ 𝔤, x * y - y * x ∈ 𝔤)
    {m : ℕ} {X : Fin m → 𝔸} (hX : ∀ i, X i ∈ 𝔤)
    (h : ∑ i, ‖X i‖ < 1 / 10) :  -- totalisation-audit: allow literal
    bchProd ℝ X ∈ 𝔤 := by
  induction m with
  | zero =>
    rw [bchProd, expProd_zero_length, sub_self, log1p_zero]
    exact 𝔤.zero_mem
  | succ m ih =>
    set X₀ : Fin m → 𝔸 := fun i => X i.castSucc with hX₀_def
    set Y := X (Fin.last m) with hY_def
    have hsum : ∑ i, ‖X i‖ = ∑ i, ‖X₀ i‖ + ‖Y‖ := Fin.sum_univ_castSucc _
    have hs₀ : ∑ i, ‖X₀ i‖ < 1 / 10 := by  -- totalisation-audit: allow literal
      linarith [norm_nonneg Y]
    have hW := ih (X := X₀) (fun i => hX _) hs₀
    have hlog2 : ∑ i, ‖X₀ i‖ < Real.log 2 := by  -- totalisation-audit: allow log of 2 > 0
      linarith [one_sixth_lt_log_two]
    have hexpW : exp (bchProd ℝ X₀) = expProd X₀ := exp_bchProd hlog2
    have hu := norm_expProd_sub_one_le ℝ X₀
    have he₀ : Real.exp (∑ i, ‖X₀ i‖) ≤ Real.exp (1 / 10) :=  -- totalisation-audit: allow literal
      Real.exp_le_exp.mpr hs₀.le
    have hu9 : ‖expProd X₀ - 1‖ < 1 / 9 := by  -- totalisation-audit: allow literal
      linarith [exp_one_tenth_lt]
    have hW4 : ‖bchProd ℝ X₀‖ < 1 / 4 := by  -- totalisation-audit: allow literal
      have h0 := norm_nonneg (expProd X₀ - 1)
      refine (norm_log1p_le_div (by linarith)).trans_lt ?_
      rw [div_lt_iff₀ (by linarith)]
      linarith
    have hmem := log1p_mem_of_dexp h𝔤 hlie
      (fun Z => BakerCampbellHausdorff.hasFDerivAt_exp (𝕂 := ℝ) Z) hW (hX (Fin.last m)) hW4
      fun t ht => by
        have h1 := norm_mul_sub_one_add_one_le (expProd X₀) (exp (t • Y))
        have h2 := norm_exp_sub_one_le ℝ (t • Y)
        have ht' : ‖t • Y‖ ≤ ‖Y‖ := by
          rw [norm_smul, Real.norm_of_nonneg ht.1]
          exact mul_le_of_le_one_left (norm_nonneg Y) ht.2
        have h3 : (‖expProd X₀ - 1‖ + 1) * (‖exp (t • Y) - 1‖ + 1) ≤
            Real.exp (∑ i, ‖X₀ i‖) * Real.exp ‖t • Y‖ :=
          mul_le_mul (by linarith) (by linarith) (by positivity) (Real.exp_pos _).le
        have h4 : Real.exp (∑ i, ‖X₀ i‖) * Real.exp ‖t • Y‖ ≤
            Real.exp (1 / 10) := by  -- totalisation-audit: allow literal
          rw [← Real.exp_add]
          exact Real.exp_le_exp.mpr (by linarith)
        rw [hexpW]
        linarith [exp_one_tenth_lt]
    rw [bchProd, expProd_castSucc, ← hexpW]
    exact hmem

/-- **The BCH series is Lie**: for `X, Y ∈ 𝔤`, the homogeneous term of degree `n` of the BCH
series, `bchSeries ℝ 𝔸 n (X, Y)`, lies in `𝔤`.  Applied to the closed Lie subalgebra generated by
`X` and `Y`, every homogeneous BCH term is a limit of Lie polynomials in `X` and `Y`. -/
theorem bchSeries_apply_diag_mem (h𝔤 : IsClosed (𝔤 : Set 𝔸))
    (hlie : ∀ x ∈ 𝔤, ∀ y ∈ 𝔤, x * y - y * x ∈ 𝔤) {X Y : 𝔸} (hX : X ∈ 𝔤) (hY : Y ∈ 𝔤)
    (n : ℕ) : bchSeries ℝ 𝔸 n (fun _ => (X, Y)) ∈ 𝔤 := by
  set L : ℝ →L[ℝ] 𝔸 × 𝔸 := ContinuousLinearMap.toSpanSingleton ℝ (X, Y) with hL
  have hq : HasFPowerSeriesAt ((fun v : 𝔸 × 𝔸 => bch ℝ v.1 v.2) ∘ L)
      ((bchSeries ℝ 𝔸).compContinuousLinearMap L) 0 := by
    apply HasFPowerSeriesAt.compContinuousLinearMap
    rw [map_zero]
    exact hasFPowerSeriesAt_bch
  have hcoeff : ((bchSeries ℝ 𝔸).compContinuousLinearMap L).coeff n =
      bchSeries ℝ 𝔸 n (fun _ => (X, Y)) := by
    rw [FormalMultilinearSeries.coeff, FormalMultilinearSeries.compContinuousLinearMap_apply]
    congr 1
    funext i
    simp [hL]
  rw [← hcoeff]
  refine coeff_mem_of_hasFPowerSeriesAt h𝔤 hq ?_ n
  have hc : ContinuousAt (fun s : ℝ => ‖s • X‖ + ‖s • Y‖) 0 := by fun_prop
  have hev := hc.eventually_lt continuousAt_const
    (show ‖(0 : ℝ) • X‖ + ‖(0 : ℝ) • Y‖ < 1 / 10 by simp)  -- totalisation-audit: allow literal
  filter_upwards [nhdsWithin_le_nhds hev] with s hs
  simp only [Function.comp_apply, hL, ContinuousLinearMap.toSpanSingleton_apply, Prod.smul_mk]
  exact bch_mem h𝔤 hlie (𝔤.smul_mem s hX) (𝔤.smul_mem s hY) hs

end Main

section MainScalar

variable {𝕂 𝔸 : Type*} [RCLike 𝕂] [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] [NormedAlgebra ℝ 𝔸]
  [IsScalarTower ℝ 𝕂 𝔸] [CompleteSpace 𝔸] {𝔤 : Submodule ℝ 𝔸}

/-- **Lie-algebraic BCH over `𝕂`**, e.g. a real Lie subalgebra such as `𝔰𝔲(n)` of a complex
Banach algebra: `bch 𝕂 X Y ∈ 𝔤`. -/
theorem bch_mem_of_isScalarTower (h𝔤 : IsClosed (𝔤 : Set 𝔸))
    (hlie : ∀ x ∈ 𝔤, ∀ y ∈ 𝔤, x * y - y * x ∈ 𝔤) {X Y : 𝔸} (hX : X ∈ 𝔤) (hY : Y ∈ 𝔤)
    (h : ‖X‖ + ‖Y‖ < 1 / 10) :  -- totalisation-audit: allow literal
    bch 𝕂 X Y ∈ 𝔤 := by
  rw [bch_eq_bch_real]
  exact bch_mem h𝔤 hlie hX hY h

/-- **Lie-algebraic BCH for products over `𝕂`**. -/
theorem bchProd_mem_of_isScalarTower (h𝔤 : IsClosed (𝔤 : Set 𝔸))
    (hlie : ∀ x ∈ 𝔤, ∀ y ∈ 𝔤, x * y - y * x ∈ 𝔤) {m : ℕ} {X : Fin m → 𝔸}
    (hX : ∀ i, X i ∈ 𝔤)
    (h : ∑ i, ‖X i‖ < 1 / 10) :  -- totalisation-audit: allow literal
    bchProd 𝕂 X ∈ 𝔤 := by
  rw [bchProd_eq_bchProd_real]
  exact bchProd_mem h𝔤 hlie hX h

end MainScalar

end BakerCampbellHausdorff
