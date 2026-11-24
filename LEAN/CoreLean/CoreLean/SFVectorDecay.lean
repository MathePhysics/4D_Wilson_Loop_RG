/-
`lem:sf-vector-decay` of BALABAN_CORE.tex (`51c39d070c46`), the step "The trivial configuration": the forms of
`Δ_𝖺(id)` conjugated by `e^{±φ}` for a weight `φ` with `|φ(x) - φ(x')| ≤ δd(x, x')`, on the fine lattice (`a₀ = 1`).

* `expA`: `(e^φA)_μ(x) = e^{φ(x)}A_μ(x)`; `gradB`: the sesquilinear form of `‖∇A‖²` (in the norm of `V`).
* `cosh_sub_le`: `e^s + e^{-s} - 2 ≤ 4s²` for `|s| ≤ 1`.
* `grad_conj`: `Re⟨∇(e^φA), ∇(e^{-φ}A)⟩ ≥ ‖∇A‖² - 16L²δ²‖A‖_w²` for `δL ≤ 1`.
-/
import CoreLean.SFCubeData

open Finset

noncomputable section

namespace CoreLean
namespace SFBounds

open Lattices SeqDom Blocks SmallFieldBlocks SFLocal SmallFieldDecay SmallFieldCoercivity

variable (S : SeqDom) {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "NF" => SequenceAverages.N0 S

/-- `e^φA`. -/
def expA (ph : Site NF → ℝ) (A : Fin 4 → Site NF → Mat) : Fin 4 → Site NF → Mat :=
  fun μ x => ((Real.exp (ph x) : ℝ) : ℂ) • A μ x

/-- The sesquilinear form of `‖∇A‖²`. -/
def gradB (A C : Fin 4 → Site NF → Mat) : ℂ :=
  ∑ μ, ∑ x, ∑ ν, inner ℂ (emb (N := N) (A μ (x + unit NF ν)) - emb (A μ x))
    (emb (N := N) (C μ (x + unit NF ν)) - emb (C μ x))

omit S in
lemma emb_smul' (c : ℂ) (X : Mat) : emb (N := N) (c • X) = c • emb X := embL.map_smul c X

/-- `e^s + e^{-s} - 2 ≤ 4s²` for `|s| ≤ 1`. -/
lemma cosh_sub_le {s : ℝ} (hs : |s| ≤ 1) : Real.exp s + Real.exp (-s) - 2 ≤ 4 * s ^ 2 := by
  have h1 := Real.abs_exp_sub_one_le hs
  have h2 := Real.abs_exp_sub_one_le (show |-s| ≤ 1 by rwa [abs_neg])
  rw [abs_neg] at h2
  have e : Real.exp s + Real.exp (-s) - 2 = -((Real.exp s - 1) * (Real.exp (-s) - 1)) := by
    have : Real.exp s * Real.exp (-s) = 1 := by rw [← Real.exp_add]; simp
    linear_combination this
  rw [e]
  have h3 : |(Real.exp s - 1) * (Real.exp (-s) - 1)| ≤ 2 * |s| * (2 * |s|) := by
    rw [abs_mul]; exact mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
  have h4 : 2 * |s| * (2 * |s|) = 4 * s ^ 2 := by rw [show 2 * |s| * (2 * |s|) = 4 * |s| ^ 2 by ring, sq_abs]
  have := neg_abs_le ((Real.exp s - 1) * (Real.exp (-s) - 1))
  linarith

lemma re_inner_smul_real {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (a b : ℝ) (x y : V) :
    (inner ℂ ((a : ℂ) • x) ((b : ℂ) • y)).re = a * b * (inner ℂ x y).re := by
  rw [inner_smul_left, inner_smul_right, Complex.conj_ofReal, ← mul_assoc, ← Complex.ofReal_mul, Complex.re_ofReal_mul]

/-- The real part of the conjugated term of a bond:
`Re⟨e^{φ'}β - e^φα, e^{-φ'}β - e^{-φ}α⟩ ≥ ‖β - α‖² - 2s²(‖α‖² + ‖β‖²)`, `s = φ' - φ`, `|s| ≤ 1`. -/
lemma bond_conj {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (α β : V) (p p' : ℝ)
    (hs : |p' - p| ≤ 1) :
    ‖β - α‖ ^ 2 - 2 * (p' - p) ^ 2 * (‖α‖ ^ 2 + ‖β‖ ^ 2) ≤
      (inner ℂ (((Real.exp p' : ℝ) : ℂ) • β - ((Real.exp p : ℝ) : ℂ) • α)
        (((Real.exp (-p') : ℝ) : ℂ) • β - ((Real.exp (-p) : ℝ) : ℂ) • α)).re := by
  set s := p' - p
  have hb : (inner ℂ β α).re = (inner ℂ α β).re := inner_re_symm (𝕜 := ℂ) β α
  have ea : Real.exp p' * Real.exp (-p') = 1 := by rw [← Real.exp_add]; simp
  have eb : Real.exp p * Real.exp (-p) = 1 := by rw [← Real.exp_add]; simp
  have ec : Real.exp p' * Real.exp (-p) = Real.exp s := by rw [← Real.exp_add]; congr 1; all_goals (simp only [s]; ring)
  have ed : Real.exp p * Real.exp (-p') = Real.exp (-s) := by rw [← Real.exp_add]; congr 1; all_goals (simp only [s]; ring)
  have hβ : (inner ℂ β β).re = ‖β‖ ^ 2 := by
    have := inner_self_eq_norm_sq (𝕜 := ℂ) β; simpa using this
  have hα : (inner ℂ α α).re = ‖α‖ ^ 2 := by
    have := inner_self_eq_norm_sq (𝕜 := ℂ) α; simpa using this
  have e1 : (inner ℂ (((Real.exp p' : ℝ) : ℂ) • β - ((Real.exp p : ℝ) : ℂ) • α)
      (((Real.exp (-p') : ℝ) : ℂ) • β - ((Real.exp (-p) : ℝ) : ℂ) • α)).re =
      ‖α‖ ^ 2 + ‖β‖ ^ 2 - (Real.exp s + Real.exp (-s)) * (inner ℂ α β).re := by
    rw [inner_sub_left, inner_sub_right, inner_sub_right, Complex.sub_re, Complex.sub_re, Complex.sub_re,
      re_inner_smul_real, re_inner_smul_real, re_inner_smul_real, re_inner_smul_real,
      hβ, hα, hb, ea, eb, ec, ed]
    ring
  have e2 : ‖β - α‖ ^ 2 = ‖α‖ ^ 2 + ‖β‖ ^ 2 - 2 * (inner ℂ α β).re := by
    rw [@norm_sub_sq ℂ]; simp only [RCLike.re_to_complex]; rw [hb]; ring
  rw [e1]
  have hc := cosh_sub_le hs
  have hin : |(inner ℂ α β).re| ≤ 1 / 2 * (‖α‖ ^ 2 + ‖β‖ ^ 2) := by
    refine (Complex.abs_re_le_norm _).trans ((norm_inner_le_norm _ _).trans ?_)
    nlinarith [sq_nonneg (‖α‖ - ‖β‖)]
  have hpos : 0 ≤ Real.exp s + Real.exp (-s) - 2 := by
    have := Real.add_one_le_exp s; have := Real.add_one_le_exp (-s); linarith
  have h3 : (Real.exp s + Real.exp (-s) - 2) * (inner ℂ α β).re ≤
      (Real.exp s + Real.exp (-s) - 2) * (1 / 2 * (‖α‖ ^ 2 + ‖β‖ ^ 2)) :=
    mul_le_mul_of_nonneg_left ((le_abs_self _).trans hin) hpos
  have h4 : (Real.exp s + Real.exp (-s) - 2) * (1 / 2 * (‖α‖ ^ 2 + ‖β‖ ^ 2)) ≤
      4 * s ^ 2 * (1 / 2 * (‖α‖ ^ 2 + ‖β‖ ^ 2)) :=
    mul_le_mul_of_nonneg_right hc (by positivity)
  nlinarith [e2]

/-- **The conjugated form of the Laplacian**: `Re⟨∇(e^φA), ∇(e^{-φ}A)⟩ ≥ ‖∇A‖² - 16L²δ²‖A‖_w²` for a weight `φ` with
`|φ(x) - φ(x')| ≤ δd(x, x')` and `δL ≤ 1`. -/
theorem grad_conj (hRM1 : 1 ≤ S.R * S.L ^ S.mM) {δ : ℝ} (hδ : 0 ≤ δ) (hδL : δ * S.L ≤ 1) (ph : Site NF → ℝ)
    (hph : ∀ x x', |ph x - ph x'| ≤ δ * S.dF x x') (A : Fin 4 → Site NF → Mat) :
    gradNorm S A - 16 * (S.L : ℝ) ^ 2 * δ ^ 2 * wnorm S A ≤
      (gradB S (expA S ph A) (expA S (fun x => -ph x) A)).re := by
  have hL1 : (1 : ℝ) ≤ S.L := by exact_mod_cast S.Lpos
  have hL0 : (0 : ℝ) < S.L := by linarith
  set w : Site NF → ℝ := fun x => ((S.L : ℝ) ^ (S.toDomSeq).sc x)⁻¹ ^ 2
  have hw0 : ∀ x, 0 ≤ w x := fun x => by positivity
  set a : Fin 4 → Site NF → VS N 1 := fun μ x => emb (A μ x)
  -- the bound of a bond
  have hterm : ∀ μ x ν, gbond S A μ x ν - 2 * (δ * S.L) ^ 2 *
      (w x * ‖a μ x‖ ^ 2 + w (x + unit NF ν) * ‖a μ (x + unit NF ν)‖ ^ 2) ≤
      (inner ℂ (emb (N := N) (expA S ph A μ (x + unit NF ν)) - emb (expA S ph A μ x))
        (emb (N := N) (expA S (fun x => -ph x) A μ (x + unit NF ν)) - emb (expA S (fun x => -ph x) A μ x))).re := by
    intro μ x ν
    have hw := S.wdist_unit_le_sc hRM1 x ν
    have hd1 : S.dF x (x + unit NF ν) ≤ S.L * ((S.L : ℝ) ^ (S.toDomSeq).sc x)⁻¹ := hw.1
    have hd2 : S.dF x (x + unit NF ν) ≤ S.L * ((S.L : ℝ) ^ (S.toDomSeq).sc (x + unit NF ν))⁻¹ := hw.2
    have hs := hph (x + unit NF ν) x
    rw [S.dF_comm] at hs
    have hinv : ∀ z, ((S.L : ℝ) ^ (S.toDomSeq).sc z)⁻¹ ≤ 1 := fun z => inv_le_one_of_one_le₀ (one_le_pow₀ hL1)
    have hs1 : |ph (x + unit NF ν) - ph x| ≤ 1 := by
      refine hs.trans ?_
      calc δ * S.dF x (x + unit NF ν) ≤ δ * (S.L * 1) :=
            mul_le_mul_of_nonneg_left (hd1.trans (mul_le_mul_of_nonneg_left (hinv x) hL0.le)) hδ
        _ ≤ 1 := by linarith
    have hsq : ∀ z, S.dF x (x + unit NF ν) ≤ S.L * ((S.L : ℝ) ^ (S.toDomSeq).sc z)⁻¹ →
        (ph (x + unit NF ν) - ph x) ^ 2 ≤ (δ * S.L) ^ 2 * w z := by
      intro z hz
      have h1 : |ph (x + unit NF ν) - ph x| ≤ δ * S.L * ((S.L : ℝ) ^ (S.toDomSeq).sc z)⁻¹ := by
        refine hs.trans ?_
        calc δ * S.dF x (x + unit NF ν) ≤ δ * (S.L * ((S.L : ℝ) ^ (S.toDomSeq).sc z)⁻¹) :=
              mul_le_mul_of_nonneg_left hz hδ
          _ = _ := by ring
      have h2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
      rw [sq_abs] at h2
      refine h2.trans (le_of_eq ?_)
      simp only [w]; ring
    have hb := bond_conj (a μ x) (a μ (x + unit NF ν)) (ph x) (ph (x + unit NF ν)) hs1
    have e1 : emb (N := N) (expA S ph A μ (x + unit NF ν)) - emb (expA S ph A μ x) =
        ((Real.exp (ph (x + unit NF ν)) : ℝ) : ℂ) • a μ (x + unit NF ν) - ((Real.exp (ph x) : ℝ) : ℂ) • a μ x := by
      simp only [expA, emb_smul', a]
    have e2 : emb (N := N) (expA S (fun x => -ph x) A μ (x + unit NF ν)) - emb (expA S (fun x => -ph x) A μ x) =
        ((Real.exp (-ph (x + unit NF ν)) : ℝ) : ℂ) • a μ (x + unit NF ν) - ((Real.exp (-ph x) : ℝ) : ℂ) • a μ x := by
      simp only [expA, emb_smul', a]
    rw [e1, e2]
    refine le_trans ?_ hb
    have hg : gbond S A μ x ν = ‖a μ (x + unit NF ν) - a μ x‖ ^ 2 := rfl
    rw [hg]
    have h3 := hsq x hd1
    have h4 := hsq (x + unit NF ν) hd2
    have h5 : (ph (x + unit NF ν) - ph x) ^ 2 * ‖a μ x‖ ^ 2 ≤ (δ * S.L) ^ 2 * w x * ‖a μ x‖ ^ 2 :=
      mul_le_mul_of_nonneg_right h3 (sq_nonneg _)
    have h6 : (ph (x + unit NF ν) - ph x) ^ 2 * ‖a μ (x + unit NF ν)‖ ^ 2 ≤
        (δ * S.L) ^ 2 * w (x + unit NF ν) * ‖a μ (x + unit NF ν)‖ ^ 2 :=
      mul_le_mul_of_nonneg_right h4 (sq_nonneg _)
    nlinarith
  -- the sum
  have hshift : ∀ μ ν, ∑ x, w (x + unit NF ν) * ‖a μ (x + unit NF ν)‖ ^ 2 = ∑ x, w x * ‖a μ x‖ ^ 2 :=
    fun μ ν => sum_shift_site S (fun x => w x * ‖a μ x‖ ^ 2) _
  have hwn : wnorm S A = ∑ μ, ∑ x, w x * ‖a μ x‖ ^ 2 := by
    unfold wnorm
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun x _ => ?_
    simp only [w, a]
    push_cast; rw [inv_pow]
  have hsum : ∑ μ, ∑ x, ∑ ν, (gbond S A μ x ν - 2 * (δ * S.L) ^ 2 *
      (w x * ‖a μ x‖ ^ 2 + w (x + unit NF ν) * ‖a μ (x + unit NF ν)‖ ^ 2)) =
      gradNorm S A - 16 * (S.L : ℝ) ^ 2 * δ ^ 2 * wnorm S A := by
    simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_add_distrib]
    unfold gradNorm
    congr 1
    have e1 : ∑ μ, ∑ x, w x * ∑ _ν : Fin 4, ‖a μ x‖ ^ 2 = 4 * ∑ μ, ∑ x, w x * ‖a μ x‖ ^ 2 := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    have e2 : ∑ μ, ∑ x, ∑ ν, w (x + unit NF ν) * ‖a μ (x + unit NF ν)‖ ^ 2 =
        4 * ∑ μ, ∑ x, w x * ‖a μ x‖ ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun μ _ => ?_
      rw [Finset.sum_comm]
      simp only [hshift, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      norm_num
    rw [hwn, e1, e2]
    ring
  rw [← hsum]
  unfold gradB
  rw [Complex.re_sum]
  refine Finset.sum_le_sum fun μ _ => ?_
  rw [Complex.re_sum]
  refine Finset.sum_le_sum fun x _ => ?_
  rw [Complex.re_sum]
  exact Finset.sum_le_sum fun ν _ => hterm μ x ν

/-- **The weighted distance near a point of `Ω_j`**: two sites within `ra_j` of a site of `Ω_j` are joined by a
segment in `Ω_{j-1}` (by the separation, `RM ≥ 9rL`), so that `d(p, p') ≤ 8rL`. -/
theorem dF_near_le {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ S.k) {e p p' : Site NF} (he : e ∈ (S.toDomSeq).Ω j) {r : ℝ}
    (hr : 0 ≤ r) (hp : (dinf p e : ℝ) ≤ r * (S.L : ℝ) ^ j) (hp' : (dinf p' e : ℝ) ≤ r * (S.L : ℝ) ^ j)
    (hRM : 9 * r * S.L ≤ ((S.R * S.L ^ S.mM : ℕ) : ℝ)) : S.dF p p' ≤ 8 * r * S.L := by
  have hL0 : (0 : ℝ) < S.L := by exact_mod_cast S.Lpos
  have hη : 0 < eta S.L S.k := eta_pos S.Lpos
  obtain ⟨x', hx', hcl⟩ := exists_close_lift (p := ellT S.L S.mT) (PartitionUnity.liftE S p) (S.ef p')
  set xh := PartitionUnity.liftE S p
  set v : Fin 4 → ℝ := x' - xh
  have hxh : projT (ellT S.L S.mT) xh = S.ef p := PartitionUnity.projT_liftE S p
  have hxv : xh + v = x' := by simp only [v]; abel
  -- the length of the segment
  have hpp' : (dinf p p' : ℝ) ≤ 2 * r * (S.L : ℝ) ^ j := by
    have h := dinf_triangle p e p'
    rw [dinf_comm e p'] at h
    have : (dinf p p' : ℝ) ≤ dinf p e + dinf p' e := by exact_mod_cast h
    linarith
  have hnorm : ‖S.ef p' - S.ef p‖ = (dinf p' p : ℝ) * eta S.L S.k :=
    norm_emb_sub S.Lpos (SequenceAverages.N0_eq S) p' p
  have hv : ∑ ν, |v ν| ≤ 4 * ((dinf p p' : ℝ) * eta S.L S.k) := by
    have hν : ∀ ν, |v ν| ≤ (dinf p p' : ℝ) * eta S.L S.k := by
      intro ν
      have h1 : |v ν| = ‖S.ef p' ν - (xh ν : AddCircle (ellT S.L S.mT))‖ := hcl ν
      have h2 : (xh ν : AddCircle (ellT S.L S.mT)) = S.ef p ν := by
        rw [← hxh]; rfl
      rw [h1, h2, dinf_comm p p', ← hnorm]
      exact norm_le_pi_norm (S.ef p' - S.ef p) ν
    calc ∑ ν, |v ν| ≤ ∑ _ν : Fin 4, (dinf p p' : ℝ) * eta S.L S.k := Finset.sum_le_sum fun ν _ => hν ν
      _ = 4 * ((dinf p p' : ℝ) * eta S.L S.k) := by simp
  -- the segment lies in `Ω_{j-1}`
  have hmem : ∀ t ∈ Set.Icc (0 : ℝ) 1, projT (ellT S.L S.mT) (xh + t • v) ∈ (S.toContSeq).D.Ω (j - 1) := by
    intro t ht
    rw [D_Ω]
    rcases Nat.lt_or_ge (j - 1) 1 with h0 | h0
    · rw [show j - 1 = 0 by omega, S.Ω_zero]; trivial
    by_contra hz
    have he' : S.ef e ∈ S.Ω (j - 1 + 1) := by rw [show j - 1 + 1 = j by omega]; exact he
    have hsep := S.sep (j - 1) h0 (by omega) ⟨_, hz⟩ ⟨_, he'⟩
    have h2 := setDist_le (A := (S.Ω (j - 1))ᶜ) (B := S.Ω (j - 1 + 1)) hz he'
    rw [dist_eq_norm] at h2
    -- `‖z - ef e‖ ≤ ‖z - ef p‖ + ‖ef p - ef e‖ ≤ 4|p - p'|η + |p - e|η`
    have h3 : ‖projT (ellT S.L S.mT) (xh + t • v) - S.ef p‖ ≤ ∑ ν, |v ν| := by
      rw [← hxh]
      refine (norm_le_dist1 S _ _).trans ((dist1_projT_le _ _).trans ?_)
      refine Finset.sum_le_sum fun ν _ => ?_
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_sub_cancel_left, abs_mul]
      rw [abs_of_nonneg ht.1]
      exact mul_le_of_le_one_left (abs_nonneg _) ht.2
    have h4 : ‖S.ef p - S.ef e‖ = (dinf p e : ℝ) * eta S.L S.k :=
      norm_emb_sub S.Lpos (SequenceAverages.N0_eq S) p e
    have h5 : ‖projT (ellT S.L S.mT) (xh + t • v) - S.ef e‖ ≤ 9 * r * (S.L : ℝ) ^ j * eta S.L S.k := by
      have := norm_sub_le_norm_sub_add_norm_sub (projT (ellT S.L S.mT) (xh + t • v)) (S.ef p) (S.ef e)
      have h6 : (dinf p p' : ℝ) * eta S.L S.k ≤ 2 * r * (S.L : ℝ) ^ j * eta S.L S.k :=
        mul_le_mul_of_nonneg_right hpp' hη.le
      have h7 : (dinf p e : ℝ) * eta S.L S.k ≤ r * (S.L : ℝ) ^ j * eta S.L S.k :=
        mul_le_mul_of_nonneg_right hp hη.le
      linarith
    have hsp : sp S.L S.k (j - 1) = (S.L : ℝ) ^ (j - 1) * eta S.L S.k := rfl
    have hLj : (S.L : ℝ) ^ j = S.L * (S.L : ℝ) ^ (j - 1) := by rw [← pow_succ']; congr 1; omega
    have h8 : 9 * r * (S.L : ℝ) ^ j * eta S.L S.k ≤
        ((S.R * S.L ^ S.mM : ℕ) : ℝ) * sp S.L S.k (j - 1) := by
      rw [hsp, hLj]
      have : (0 : ℝ) ≤ (S.L : ℝ) ^ (j - 1) * eta S.L S.k := by positivity
      calc 9 * r * (S.L * (S.L : ℝ) ^ (j - 1)) * eta S.L S.k = 9 * r * S.L * ((S.L : ℝ) ^ (j - 1) * eta S.L S.k) := by
            ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hRM this
    linarith
  -- the length of the segment in the weighted distance
  have hw := wdist_seg_le (S.toContSeq).D xh v (j - 1) hmem
  rw [hxv, hx', hxh, D_a] at hw
  have hne := wdist_ne_top (S.toContSeq).D (S.ef p) (S.ef p')
  have hsp : sp S.L S.k (j - 1) = (S.L : ℝ) ^ (j - 1) * eta S.L S.k := rfl
  have hspos : 0 < sp S.L S.k (j - 1) := by rw [hsp]; positivity
  have h1 : S.dF p p' ≤ (sp S.L S.k (j - 1))⁻¹ * ∑ ν, |v ν| := by
    unfold dF
    rw [← ENNReal.ofReal_le_ofReal_iff (by positivity), ENNReal.ofReal_toReal hne]
    exact hw
  refine h1.trans ?_
  have hLj : (S.L : ℝ) ^ j = S.L * (S.L : ℝ) ^ (j - 1) := by rw [← pow_succ']; congr 1; omega
  rw [hsp, inv_mul_le_iff₀ (by positivity)]
  calc ∑ ν, |v ν| ≤ 4 * ((dinf p p' : ℝ) * eta S.L S.k) := hv
    _ ≤ 4 * (2 * r * (S.L : ℝ) ^ j * eta S.L S.k) := by
        have := mul_le_mul_of_nonneg_right hpp' hη.le; linarith
    _ = (S.L : ℝ) ^ (j - 1) * eta S.L S.k * (8 * r * S.L) := by rw [hLj]; ring

/-- The sesquilinear form of `⟨A^*, Q^*QA⟩`. -/
def QB2 (A C : Fin 4 → Site NF → Mat) : ℂ :=
  ∑ q ∈ QB S, (((S.L ^ q.1 : ℕ) : ℝ) ^ 2 : ℂ) * inner ℂ (emb (N := N) (Qt S A q.1 q.2.1 q.2.2))
    (emb (N := N) (Qt S C q.1 q.2.1 q.2.2))

/-- `emb((QB)(c)) = a_c^{-5}Σ_i emb(B(p_i))` over the box of `c`. -/
lemma emb_Qt (B : Fin 4 → Site NF → Mat) (j : ℕ) (y : Site NF) (μ : Fin 4) :
    emb (N := N) (Qt S B j y μ) = (((((S.L ^ j : ℕ) : ℝ) ^ 5)⁻¹ : ℝ) : ℂ) •
      ∑ i ∈ Blk S.toDomSeq j y ×ˢ range (S.L ^ j), emb (N := N) (B μ (i.1 + ((i.2 : ℕ) : ZMod NF) • unit NF μ)) := by
  unfold Qt
  rw [emb_smul', Finset.sum_product]
  congr 1
  · push_cast; rfl
  · simp only [← embL_apply_eq, map_sum]
  where embL_apply_eq (X : Mat) : embL (N := N) X = emb X := rfl

/-- The real part of the form of two sums with real coefficients. -/
lemma re_inner_sum_real {ι V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (I : Finset ι) (c d : ι → ℝ)
    (u : ι → V) :
    (inner ℂ (∑ i ∈ I, ((c i : ℝ) : ℂ) • u i) (∑ i ∈ I, ((d i : ℝ) : ℂ) • u i)).re =
      ∑ i ∈ I, ∑ i' ∈ I, c i * d i' * (inner ℂ (u i) (u i')).re := by
  rw [sum_inner, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_sum, Complex.re_sum]
  exact Finset.sum_congr rfl fun i' _ => re_inner_smul_real _ _ _ _

/-- **The conjugated term of a bond of a layer**:
`|a_c²Re⟨Q(e^φA)(c), Q(e^{-φ}A)(c)⟩ - a_c²|(QA)(c)|²| ≤ 32Lδa_c^{-3}Σ_i|A(p_i)|²`. -/
theorem bond_Q_conj (hRM : 18 * (S.L : ℝ) ≤ ((S.R * S.L ^ S.mM : ℕ) : ℝ)) {δ : ℝ} (hδ : 0 ≤ δ)
    (hδL : 16 * S.L * δ ≤ 1) (ph : Site NF → ℝ) (hph : ∀ x x', |ph x - ph x'| ≤ δ * S.dF x x') {j : ℕ}
    {y : Site NF} {μ : Fin 4} (hq : (j, y, μ) ∈ QB S) (A : Fin 4 → Site NF → Mat) :
    |((((S.L ^ j : ℕ) : ℝ) ^ 2 : ℝ) : ℂ).re * (inner ℂ (emb (N := N) (Qt S (expA S ph A) j y μ))
        (emb (N := N) (Qt S (expA S (fun x => -ph x) A) j y μ))).re -
      ((S.L ^ j : ℕ) : ℝ) ^ 2 * ‖emb (N := N) (Qt S A j y μ)‖ ^ 2| ≤
      32 * S.L * δ * ((((S.L ^ j : ℕ) : ℝ) ^ 3)⁻¹ * ∑ i ∈ Blk S.toDomSeq j y ×ˢ range (S.L ^ j),
        ‖emb (N := N) (A μ (i.1 + ((i.2 : ℕ) : ZMod NF) • unit NF μ))‖ ^ 2) := by
  set I := Blk S.toDomSeq j y ×ˢ range (S.L ^ j)
  set n : ℝ := ((S.L ^ j : ℕ) : ℝ)
  set pt : Site NF × ℕ → Site NF := fun i => i.1 + ((i.2 : ℕ) : ZMod NF) • unit NF μ
  set u : Site NF × ℕ → VS N 1 := fun i => emb (N := N) (A μ (pt i))
  set f : Site NF × ℕ → ℝ := fun i => ‖u i‖ ^ 2
  have hq' := (PartitionUnity.mem_QB_iff (T := S) _).1 hq
  have hjk : j ≤ S.k := by have := hq'.1; omega
  have hn : 0 < n := by simp only [n]; have := S.Lpos; positivity
  have hL0 : (0 : ℝ) < S.L := by exact_mod_cast S.Lpos
  have hI : (I.card : ℝ) = n ^ 5 := by
    simp only [I, n, Finset.card_product, card_Blk_j S hjk hq'.2.1, Finset.card_range]
    push_cast; ring
  -- the weight varies by at most `16Lδ` on the box
  have hvar : ∀ i ∈ I, ∀ i' ∈ I, |Real.exp (ph (pt i)) * Real.exp (-ph (pt i')) - 1| ≤ 32 * S.L * δ := by
    intro i hi i' hi'
    rw [Finset.mem_product, Finset.mem_range] at hi hi'
    have hd : |ph (pt i) - ph (pt i')| ≤ 16 * S.L * δ := by
      refine (hph _ _).trans ?_
      rcases Nat.eq_zero_or_pos j with hj0 | hj1
      · -- the box of a bond of the layer `0` is the site `y`
        have hpt : ∀ k ∈ Blk S.toDomSeq j y, ∀ t < S.L ^ j, pt (k, t) = y := by
          intro k hk t ht
          subst hj0
          have ht0 : t = 0 := by simpa using ht
          have hky : k = y := by
            funext ν
            have h := SmallFieldBlocks.cd_le_of_mem (S := S.toDomSeq) hk ν
            have h0 : half S.toDomSeq.L 0 = 0 := by simp [half]
            rw [h0] at h
            have : (k ν - y ν).valMinAbs = 0 := by unfold cd at h; omega
            rw [ZMod.valMinAbs_eq_zero] at this
            exact sub_eq_zero.1 this
          simp [pt, ht0, hky]
        rw [hpt _ hi.1 _ hi.2, hpt _ hi'.1 _ hi'.2]
        unfold dF; rw [wdist_self]; simp only [ENNReal.toReal_zero, mul_zero]; positivity
      · -- an end of the bond lies in `Ω_j`
        obtain ⟨-, hend, -, -⟩ := hq'.2.2
        have hnext : S.bend j (S.ef y) μ = S.ef (ynext S j y μ) := by rw [ef_ynext]; rfl
        have hb : ∀ k ∈ Blk S.toDomSeq j y, ∀ t < S.L ^ j, ∀ s ≤ S.L ^ j,
            (dinf (pt (k, t)) (y + ((s : ℕ) : ZMod NF) • unit NF μ) : ℝ) ≤ 2 * (S.L : ℝ) ^ j := by
          intro k hk t ht s hs
          have := PartitionUnity.box_dinf S hk μ ht.le hs
          have h := Nat.cast_le (α := ℝ) |>.2 this; push_cast at h; exact h
        have hd2 : S.dF (pt i) (pt i') ≤ 8 * 2 * S.L := by
          rcases hend with he | he
          · have h0 := hb _ hi.1 _ hi.2 0 (Nat.zero_le _)
            have h0' := hb _ hi'.1 _ hi'.2 0 (Nat.zero_le _)
            simp only [Nat.cast_zero, zero_smul, add_zero] at h0 h0'
            exact dF_near_le S hj1 hjk (e := y) he (by norm_num) h0 h0' (by linarith)
          · rw [hnext] at he
            have h0 := hb _ hi.1 _ hi.2 (S.L ^ j) le_rfl
            have h0' := hb _ hi'.1 _ hi'.2 (S.L ^ j) le_rfl
            exact dF_near_le S hj1 hjk (e := ynext S j y μ) he (by norm_num) h0 h0' (by linarith)
        calc δ * S.dF (pt i) (pt i') ≤ δ * (8 * 2 * S.L) := mul_le_mul_of_nonneg_left hd2 hδ
          _ = 16 * S.L * δ := by ring
    have h1 : |ph (pt i) - ph (pt i')| ≤ 1 := hd.trans hδL
    have e : Real.exp (ph (pt i)) * Real.exp (-ph (pt i')) = Real.exp (ph (pt i) - ph (pt i')) := by
      rw [← Real.exp_add]; ring_nf
    rw [e]
    refine (Real.abs_exp_sub_one_le h1).trans ?_
    linarith
  -- the expansion of the two forms
  have e1 : (inner ℂ (emb (N := N) (Qt S (expA S ph A) j y μ)) (emb (N := N) (Qt S (expA S (fun x => -ph x) A) j y μ))).re =
      (n ^ 5)⁻¹ * (n ^ 5)⁻¹ * ∑ i ∈ I, ∑ i' ∈ I, Real.exp (ph (pt i)) * Real.exp (-ph (pt i')) * (inner ℂ (u i) (u i')).re := by
    rw [emb_Qt, emb_Qt, re_inner_smul_real]
    have h1 : ∑ i ∈ I, emb (N := N) (expA S ph A μ (pt i)) = ∑ i ∈ I, ((Real.exp (ph (pt i)) : ℝ) : ℂ) • u i := by
      refine Finset.sum_congr rfl fun i _ => ?_; simp only [expA, emb_smul', u]
    have h2 : ∑ i ∈ I, emb (N := N) (expA S (fun x => -ph x) A μ (pt i)) =
        ∑ i ∈ I, ((Real.exp (-ph (pt i)) : ℝ) : ℂ) • u i := by
      refine Finset.sum_congr rfl fun i _ => ?_; simp only [expA, emb_smul', u]
    simp only [pt] at h1 h2
    rw [h1, h2, re_inner_sum_real]
  have e2 : ‖emb (N := N) (Qt S A j y μ)‖ ^ 2 = (n ^ 5)⁻¹ * (n ^ 5)⁻¹ * ∑ i ∈ I, ∑ i' ∈ I, 1 * 1 * (inner ℂ (u i) (u i')).re := by
    have hh : (inner ℂ (emb (N := N) (Qt S A j y μ)) (emb (N := N) (Qt S A j y μ))).re = ‖emb (N := N) (Qt S A j y μ)‖ ^ 2 := by
      have := inner_self_eq_norm_sq (𝕜 := ℂ) (emb (N := N) (Qt S A j y μ)); simpa using this
    rw [← hh, emb_Qt, re_inner_smul_real]
    have h1 : ∑ i ∈ I, emb (N := N) (A μ (pt i)) = ∑ i ∈ I, (((1 : ℝ) : ℝ) : ℂ) • u i := by
      refine Finset.sum_congr rfl fun i _ => ?_; simp [u]
    simp only [pt] at h1
    rw [h1, re_inner_sum_real]
  rw [Complex.ofReal_re, e1, e2]
  have hdiff : n ^ 2 * ((n ^ 5)⁻¹ * (n ^ 5)⁻¹ * ∑ i ∈ I, ∑ i' ∈ I, Real.exp (ph (pt i)) * Real.exp (-ph (pt i')) *
        (inner ℂ (u i) (u i')).re) - n ^ 2 * ((n ^ 5)⁻¹ * (n ^ 5)⁻¹ * ∑ i ∈ I, ∑ i' ∈ I, 1 * 1 * (inner ℂ (u i) (u i')).re) =
      n ^ 2 * ((n ^ 5)⁻¹ * (n ^ 5)⁻¹) * ∑ i ∈ I, ∑ i' ∈ I,
        (Real.exp (ph (pt i)) * Real.exp (-ph (pt i')) - 1) * (inner ℂ (u i) (u i')).re := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ => by ring
  rw [hdiff]
  have hc0 : 0 ≤ n ^ 2 * ((n ^ 5)⁻¹ * (n ^ 5)⁻¹) := by positivity
  rw [abs_mul, abs_of_nonneg hc0]
  have hpair : ∀ i ∈ I, ∀ i' ∈ I, |(Real.exp (ph (pt i)) * Real.exp (-ph (pt i')) - 1) * (inner ℂ (u i) (u i')).re| ≤
      32 * S.L * δ * (1 / 2 * (f i + f i')) := by
    intro i hi i' hi'
    rw [abs_mul]
    exact mul_le_mul (hvar i hi i' hi') (PartitionUnity.norm_re_inner_le _ _) (abs_nonneg _) (by positivity)
  calc n ^ 2 * ((n ^ 5)⁻¹ * (n ^ 5)⁻¹) * |∑ i ∈ I, ∑ i' ∈ I,
        (Real.exp (ph (pt i)) * Real.exp (-ph (pt i')) - 1) * (inner ℂ (u i) (u i')).re|
      ≤ n ^ 2 * ((n ^ 5)⁻¹ * (n ^ 5)⁻¹) * ∑ i ∈ I, ∑ i' ∈ I, 32 * S.L * δ * (1 / 2 * (f i + f i')) :=
        mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi =>
          (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i' hi' => hpair i hi i' hi'))) hc0
    _ = n ^ 2 * ((n ^ 5)⁻¹ * (n ^ 5)⁻¹) * (32 * S.L * δ * (1 / 2)) * ∑ i ∈ I, ∑ i' ∈ I, (f i + f i') := by
        simp only [Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    _ = 32 * S.L * δ * ((n ^ 3)⁻¹ * ∑ i ∈ I, f i) := by
        rw [PartitionUnity.sum_sum_add, hI]
        field_simp

/-- **The conjugated constraint form**: `|Re⟨Q(e^φA), Q(e^{-φ}A)⟩ - ⟨A^*, Q^*QA⟩| ≤ 96L³δ‖A‖_w²`. -/
theorem Q_conj (hRM : 18 * (S.L : ℝ) ≤ ((S.R * S.L ^ S.mM : ℕ) : ℝ)) {δ : ℝ} (hδ : 0 ≤ δ)
    (hδL : 16 * S.L * δ ≤ 1) (ph : Site NF → ℝ) (hph : ∀ x x', |ph x - ph x'| ≤ δ * S.dF x x')
    (A : Fin 4 → Site NF → Mat) :
    |(QB2 S (expA S ph A) (expA S (fun x => -ph x) A)).re - Qnorm S A| ≤ 96 * (S.L : ℝ) ^ 3 * δ * wnorm S A := by
  have hL0 : (0 : ℝ) < S.L := by exact_mod_cast S.Lpos
  have hRM2 : 2 * (S.L : ℝ) ≤ ((S.R * S.L ^ S.mM : ℕ) : ℝ) := by linarith
  unfold QB2 Qnorm
  rw [Complex.re_sum, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ q ∈ QB S, |((((S.L ^ q.1 : ℕ) : ℝ) ^ 2 : ℂ) * inner ℂ (emb (N := N) (Qt S (expA S ph A) q.1 q.2.1 q.2.2))
          (emb (N := N) (Qt S (expA S (fun x => -ph x) A) q.1 q.2.1 q.2.2))).re -
        ((S.L ^ q.1 : ℕ) : ℝ) ^ 2 * ‖emb (N := N) (Qt S A q.1 q.2.1 q.2.2)‖ ^ 2|
      ≤ ∑ q ∈ QB S, 32 * S.L * δ * ((((S.L ^ q.1 : ℕ) : ℝ) ^ 3)⁻¹ *
          ∑ i ∈ Blk S.toDomSeq q.1 q.2.1 ×ˢ range (S.L ^ q.1),
            ‖emb (N := N) (A q.2.2 (i.1 + ((i.2 : ℕ) : ZMod NF) • unit NF q.2.2))‖ ^ 2) := by
        refine Finset.sum_le_sum fun q hq => ?_
        obtain ⟨j, y, μ⟩ := q
        have h := bond_Q_conj S hRM hδ hδL ph hph hq A
        rw [Complex.ofReal_re] at h
        rw [← Complex.ofReal_pow, Complex.re_ofReal_mul]
        exact h
    _ = 32 * S.L * δ * ∑ q ∈ QB S, (((S.L ^ q.1 : ℕ) : ℝ) ^ 3)⁻¹ *
          ∑ i ∈ Blk S.toDomSeq q.1 q.2.1 ×ˢ range (S.L ^ q.1),
            ‖emb (N := N) (A q.2.2 (i.1 + ((i.2 : ℕ) : ZMod NF) • unit NF q.2.2))‖ ^ 2 := by rw [Finset.mul_sum]
    _ ≤ 32 * S.L * δ * (3 * (S.L : ℝ) ^ 2 * wnorm S A) :=
        mul_le_mul_of_nonneg_left (PartitionUnity.layer_sum_le S hRM2 A) (by positivity)
    _ = 96 * (S.L : ℝ) ^ 3 * δ * wnorm S A := by ring

/-! ### The projection term -/

open scoped Matrix

open SFBox SequenceOperators ConcretePairing in
lemma herm_eq (f g : Site NF → Mat) : herm S f g = ∑ x, ntr ((f x)ᴴ * g x) := by
  simp only [herm, P0, pairForm0, ConcretePairing.wpair_apply, a1, Complex.ofReal_one, one_pow, one_mul, cstar]

open SFBox in
lemma Dfw_triv (ν : Fin 4) (l : Site NF → Mat) (x : Site NF) :
    Dfw 1 (cfgX (X0 S)) ν l x = l (x + unit NF ν) - l x := by
  simp [Dfw, cfgX, X0, Ad]

open SFBox SequenceOperators in
/-- **Summation by parts**: `⟨∂^*B, F⟩ = Σ_ν⟨B_ν, ∂_νF⟩` (trivial configuration, `a₀ = 1`). -/
lemma herm_Ds1L (B : Fin 4 → Site NF → Mat) (F : Site NF → Mat) :
    herm S (Ds1L a1 (cfgX (X0 S)) B) F = ∑ ν, ∑ x, ntr ((B ν x)ᴴ * Dfw 1 (cfgX (X0 S)) ν F x) := by
  rw [herm_eq]
  simp only [Ds1L_triv, Dfw_triv, Matrix.conjTranspose_sum, Matrix.sum_mul, ntr_sum, Matrix.conjTranspose_sub,
    Matrix.sub_mul, Matrix.mul_sub, ntr_sub]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  congr 1
  have := sum_shift_site S (fun x => ntr ((B ν (x - unit NF ν))ᴴ * F x)) (unit NF ν)
  simp only [add_sub_cancel_right] at this
  rw [← this]

open SFBox SequenceOperators in
/-- **The form of `P` through `∂P∂^*`**: `⟨P∂^*B, P∂^*C⟩ = Σ_ν⟨B_ν, ∂_νP∂^*C⟩` at the trivial configuration. -/
lemma herm_P_eq [NeZero N] (B C : Fin 4 → Site NF → Mat) :
    herm S (Pop S (X0 S) (W1 S) Set.univ (Ds1L a1 (cfgX (X0 S)) B)) (Pop S (X0 S) (W1 S) Set.univ (Ds1L a1 (cfgX (X0 S)) C)) =
      ∑ ν, ∑ x, ntr ((B ν x)ᴴ * Dfw 1 (cfgX (X0 S)) ν (Pop S (X0 S) (W1 S) Set.univ (Ds1L a1 (cfgX (X0 S)) C)) x) := by
  have hb := hb_triv (N := N) (S := S) Set.univ
  rw [Pop_herm_triv S Set.univ hb, Pop_idem S _ _ Set.univ hb, herm_Ds1L]

open SFBox SequenceOperators in
/-- The kernel of `∂_νP∂^*`: `k_G(x, x')Z = (∂_νP∂^*(δ_{x'}Z e_μ))(x)`. -/
def kG [NeZero N] (ν : Fin 4) (x : Site NF) (μ : Fin 4) (x' : Site NF) : Mat →ₗ[ℂ] Mat :=
  (LinearMap.proj x ∘ₗ DfwL S (cfgX (X0 S)) ν ∘ₗ Pop S (X0 S) (W1 S) Set.univ ∘ₗ Ds1L a1 (cfgX (X0 S))) ∘ₗ
    (LinearMap.single ℂ (fun _ : Fin 4 => Site NF → Mat) μ ∘ₗ LinearMap.single ℂ (fun _ : Site NF => Mat) x')

open SFBox SequenceOperators in
lemma kG_apply [NeZero N] (ν : Fin 4) (h : Fin 4 → Site NF → Mat) (x : Site NF) :
    Dfw 1 (cfgX (X0 S)) ν (Pop S (X0 S) (W1 S) Set.univ (Ds1L a1 (cfgX (X0 S)) h)) x =
      ∑ μ, ∑ x', kG S ν x μ x' (h μ x') := by
  have e : h = ∑ μ, ∑ x', Pi.single μ (Pi.single x' (h μ x')) := by
    funext μ0 x0
    simp only [Finset.sum_apply]
    rw [Finset.sum_eq_single μ0 (fun b _ hb => by simp [Pi.single_eq_of_ne' hb]) (by simp)]
    simp [Pi.single_apply]
  change (DfwL S (cfgX (X0 S)) ν (Pop S (X0 S) (W1 S) Set.univ (Ds1L a1 (cfgX (X0 S)) h))) x = _
  conv_lhs => rw [e]
  simp only [map_sum, Finset.sum_apply]
  rfl

open SFBox SequenceOperators in
/-- **The kernel of `∂_νP∂^*`** at the trivial configuration (`gradPDs_bound`):
`|k_G(x, x')Z| ≤ C_Pg a_{j(x)}^{-1}a_{j(x')}^{-5}e^{-θd(y(x), y(x'))}|Z|`. -/
lemma kG_bound [NeZero N] {δ0 : ℝ} (H : ScalarHyp (N := N) S (X0 S) 0 (W1 S) 0 Set.univ δ0)
    (hRMb : (S.toContSeq).r1 (1 / 2) (1 / 32 * δ0) ≤ ((S.R * S.L ^ S.mM : ℕ) : ℝ))
    (hRMs4 : 32 * Real.log S.L / (1 / 4 * δ0) ≤ ((S.R * S.L ^ S.mM : ℕ) : ℝ))
    (hsmallT : CTd S N δ0 0 0 * (S.toContSeq).c1 (1 / 2) (1 / 32 * δ0) ≤ gammaB N / 4)
    (hRMθs : 32 * Real.log S.L / (thetaB S N δ0 / 2) ≤ ((S.R * S.L ^ S.mM : ℕ) : ℝ))
    (hRMθc : (S.toContSeq).r1 (1 / 2) (7 / 16 * thetaB S N δ0) ≤ ((S.R * S.L ^ S.mM : ℕ) : ℝ))
    (ν : Fin 4) (x : Site NF) (μ : Fin 4) (x' : Site NF) (Z : Mat) :
    hs (kG S ν x μ x' Z) ≤ ScalarHyp.CPg S N δ0 0 * ((S.L : ℝ) ^ (S.toDomSeq).sc (bc S.toDomSeq x))⁻¹ *
      (((S.L : ℝ) ^ (S.toDomSeq).sc (bc S.toDomSeq x'))⁻¹ * ((S.L : ℝ) ^ (4 * (S.toDomSeq).sc (bc S.toDomSeq x')))⁻¹ *
        Real.exp (-(7 / 32 * thetaB S N δ0 * S.dF (bc S.toDomSeq x) (bc S.toDomSeq x')))) * hs Z := by
  have h := H.gradPDs_bound hRMb hRMs4 hsmallT hRMθs hRMθc ν
    (Pi.single μ (Pi.single x' Z) : Fin 4 → Site NF → Mat) x
  have e : kG S ν x μ x' Z =
      Dfw 1 (cfgX (X0 S)) ν (Pop S (X0 S) (W1 S) Set.univ (Ds1L a1 (cfgX (X0 S)) (Pi.single μ (Pi.single x' Z)))) x := rfl
  rw [e]
  refine h.trans (le_of_eq ?_)
  have hz : ∀ x'' μ', hs ((Pi.single μ (Pi.single x' Z) : Fin 4 → Site NF → Mat) μ' x'') =
      if μ' = μ ∧ x'' = x' then hs Z else 0 := by
    intro x'' μ'
    by_cases h1 : μ' = μ
    · subst h1
      by_cases h2 : x'' = x'
      · subst h2; simp
      · simp [h2, Pi.single_eq_of_ne h2, RegularAverages.hs_zero']
    · simp [h1, Pi.single_eq_of_ne h1, RegularAverages.hs_zero']
  simp only [hz]
  rw [Finset.sum_eq_single x' (fun b _ hb => by simp [hb]) (by simp)]
  simp only [and_true, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

/-- `|e^t - 1| ≤ |t|e^{|t|}`. -/
lemma abs_exp_sub_one_le' (t : ℝ) : |Real.exp t - 1| ≤ |t| * Real.exp |t| := by
  have h1 : |Real.exp t - 1| ≤ Real.exp |t| - 1 := by
    rcases le_total 0 t with ht | ht
    · rw [abs_of_nonneg ht, abs_of_nonneg (by linarith [Real.one_le_exp ht])]
    · rw [abs_of_nonpos ht, abs_of_nonpos (by linarith [Real.exp_le_one_iff.2 ht])]
      have h2 := Real.one_le_cosh t
      rw [Real.cosh_eq] at h2
      linarith
  have h2 : Real.exp |t| - 1 ≤ |t| * Real.exp |t| := by
    have := Real.add_one_le_exp (-|t|)
    have h3 : Real.exp |t| * Real.exp (-|t|) = 1 := by rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos |t|, abs_nonneg t]
  linarith

/-- **The test of Schur for the kernel `a_{y(x')}^{-4}e^{-θd/2}`** (rows from `summation_fine`, columns from
`scale_shift`). -/
lemma schur_kernel {θ : ℝ} (hθ : 0 < θ) (hRMsum : (S.toContSeq).r1 (1 / 2) θ ≤ ((S.R * S.L ^ S.mM : ℕ) : ℝ))
    (hRMsum2 : (S.toContSeq).r1 (1 / 2) (θ / 2) ≤ ((S.R * S.L ^ S.mM : ℕ) : ℝ))
    (hRMss : 32 * Real.log S.L / (2 * θ) ≤ ((S.R * S.L ^ S.mM : ℕ) : ℝ)) (u : Site NF → ℝ) (hu : ∀ x, 0 ≤ u x) :
    ∑ x, ∑ x', ((S.L : ℝ) ^ (4 * (S.toDomSeq).sc (bc S.toDomSeq x')))⁻¹ *
        Real.exp (-(1 / 2 * θ * S.dF (bc S.toDomSeq x) (bc S.toDomSeq x'))) * u x' * u x ≤
      ((S.toContSeq).c1 (1 / 2) θ + (S.L : ℝ) ^ 4 * (S.toContSeq).c1 (1 / 2) (θ / 2)) / 2 * ∑ x, u x ^ 2 := by
  have hL1 : (1 : ℝ) ≤ S.L := by exact_mod_cast S.Lpos
  set c1 := (S.toContSeq).c1 (1 / 2) θ
  set c2 := (S.toContSeq).c1 (1 / 2) (θ / 2)
  set K : Site NF → Site NF → ℝ := fun x x' => ((S.L : ℝ) ^ (4 * (S.toDomSeq).sc (bc S.toDomSeq x')))⁻¹ *
    Real.exp (-(1 / 2 * θ * S.dF (bc S.toDomSeq x) (bc S.toDomSeq x')))
  have hK : ∀ x x', 0 ≤ K x x' := fun x x' => by positivity
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
      rw [PartitionUnity.rpow_neg_four, PartitionUnity.rpow_neg_four, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num,
        Real.rpow_natCast] at hs
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

/-- The constant of the conjugated projection term. -/
def CPv (S : SeqDom) (N : ℕ) (δ0 : ℝ) : ℝ :=
  ScalarHyp.CPg S N δ0 0 * (Real.exp (7 / 32 * thetaB S N δ0) * (4 / (7 / 32 * thetaB S N δ0) + 4)) *
    (((S.toContSeq).c1 (1 / 2) (7 / 32 * thetaB S N δ0) +
      (S.L : ℝ) ^ 4 * (S.toContSeq).c1 (1 / 2) (7 / 32 * thetaB S N δ0 / 2)) / 2)

/-- `δ(d + 4)e^{δ(d+4)}e^{-θd} ≤ δe^θ(4/θ + 4)e^{-θd/2}` for `0 ≤ δ ≤ θ/4`, `d ≥ 0`. -/
lemma conj_weight_le {θ δ d : ℝ} (hθ : 0 < θ) (hδ : 0 ≤ δ) (hδθ : δ ≤ 1 / 4 * θ) (hd : 0 ≤ d) :
    δ * (d + 4) * Real.exp (δ * (d + 4)) * Real.exp (-(θ * d)) ≤
      δ * (Real.exp θ * (4 / θ + 4)) * Real.exp (-(1 / 2 * θ * d)) := by
  have h1 : Real.exp (δ * (d + 4)) ≤ Real.exp θ * Real.exp (θ * d / 4) := by
    rw [← Real.exp_add]; apply Real.exp_le_exp.2; nlinarith
  have h2 : d + 4 ≤ (4 / θ + 4) * Real.exp (θ * d / 4) := by
    have h3 := Real.add_one_le_exp (θ * d / 4)
    have h4 : d ≤ 4 / θ * Real.exp (θ * d / 4) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hθ]; nlinarith
    have h5 : 1 ≤ Real.exp (θ * d / 4) := Real.one_le_exp (by positivity)
    nlinarith
  have e : Real.exp (θ * d / 4) * Real.exp (θ * d / 4) * Real.exp (-(θ * d)) = Real.exp (-(1 / 2 * θ * d)) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hE := Real.exp_pos (-(θ * d))
  calc δ * (d + 4) * Real.exp (δ * (d + 4)) * Real.exp (-(θ * d))
      ≤ δ * ((4 / θ + 4) * Real.exp (θ * d / 4)) * (Real.exp θ * Real.exp (θ * d / 4)) * Real.exp (-(θ * d)) := by
        gcongr
    _ = δ * (Real.exp θ * (4 / θ + 4)) * (Real.exp (θ * d / 4) * Real.exp (θ * d / 4) * Real.exp (-(θ * d))) := by
        ring
    _ = _ := by rw [e]

open SFBox SequenceOperators in
/-- **The conjugated projection term**: `|Re⟨P∂^*(e^φA), P∂^*(e^{-φ}A)⟩ - ‖P∂^*A‖²| ≤ C_Pvδ Σ_x(a_{j(x)}^{-1}Σ_ν|A_ν(x)|)²`
for `0 ≤ δ ≤ θ/4`, `θ = (7/32)θ_B` (the kernel of `∂P∂^*` and the test of Schur). -/
theorem P_conj [NeZero N] {δ0 : ℝ} (H : ScalarHyp (N := N) S (X0 S) 0 (W1 S) 0 Set.univ δ0)
    (hRMb : (S.toContSeq).r1 (1 / 2) (1 / 32 * δ0) ≤ ((S.R * S.L ^ S.mM : ℕ) : ℝ))
    (hRMs4 : 32 * Real.log S.L / (1 / 4 * δ0) ≤ ((S.R * S.L ^ S.mM : ℕ) : ℝ))
    (hsmallT : CTd S N δ0 0 0 * (S.toContSeq).c1 (1 / 2) (1 / 32 * δ0) ≤ gammaB N / 4)
    (hRMθs : 32 * Real.log S.L / (thetaB S N δ0 / 2) ≤ ((S.R * S.L ^ S.mM : ℕ) : ℝ))
    (hRMθc : (S.toContSeq).r1 (1 / 2) (7 / 16 * thetaB S N δ0) ≤ ((S.R * S.L ^ S.mM : ℕ) : ℝ))
    (hRMsum : (S.toContSeq).r1 (1 / 2) (7 / 32 * thetaB S N δ0) ≤ ((S.R * S.L ^ S.mM : ℕ) : ℝ))
    (hRMsum2 : (S.toContSeq).r1 (1 / 2) (7 / 32 * thetaB S N δ0 / 2) ≤ ((S.R * S.L ^ S.mM : ℕ) : ℝ))
    (hRMss : 32 * Real.log S.L / (2 * (7 / 32 * thetaB S N δ0)) ≤ ((S.R * S.L ^ S.mM : ℕ) : ℝ))
    {δ : ℝ} (hδ : 0 ≤ δ) (hδθ : δ ≤ 1 / 4 * (7 / 32 * thetaB S N δ0)) (ph : Site NF → ℝ)
    (hph : ∀ x x', |ph x - ph x'| ≤ δ * S.dF x x') (A : Fin 4 → Site NF → Mat) :
    |(herm S (Pop S (X0 S) (W1 S) Set.univ (Ds1L a1 (cfgX (X0 S)) (expA S ph A)))
        (Pop S (X0 S) (W1 S) Set.univ (Ds1L a1 (cfgX (X0 S)) (expA S (fun x => -ph x) A)))).re -
      ∑ x, hs2 (Pop S (X0 S) (W1 S) Set.univ (Ds1L a1 (cfgX (X0 S)) A) x)| ≤
      CPv S N δ0 * δ * ∑ x, (((S.L : ℝ) ^ (S.toDomSeq).sc x)⁻¹ * ∑ ν, hs (A ν x)) ^ 2 := by
  set θ := 7 / 32 * thetaB S N δ0
  have hθ : 0 < θ := by have := H.thetaB_pos (N := N); positivity
  set k : Fin 4 → Site NF → Fin 4 → Site NF → ℂ := fun ν x μ x' => ntr ((A ν x)ᴴ * kG S ν x μ x' (A μ x'))
  -- the two forms through the kernel
  have e1 : herm S (Pop S (X0 S) (W1 S) Set.univ (Ds1L a1 (cfgX (X0 S)) (expA S ph A)))
      (Pop S (X0 S) (W1 S) Set.univ (Ds1L a1 (cfgX (X0 S)) (expA S (fun x => -ph x) A))) =
      ∑ ν, ∑ x, ∑ μ, ∑ x', ((Real.exp (ph x) * Real.exp (-ph x') : ℝ) : ℂ) * k ν x μ x' := by
    rw [herm_P_eq]
    refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun x _ => ?_
    rw [kG_apply, Matrix.mul_sum, ntr_sum]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [Matrix.mul_sum, ntr_sum]
    refine Finset.sum_congr rfl fun x' _ => ?_
    simp only [expA, k, map_smul, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, ntr_smul,
      Complex.star_def, Complex.conj_ofReal]
    push_cast; ring
  have e2 : ((∑ x, hs2 (Pop S (X0 S) (W1 S) Set.univ (Ds1L a1 (cfgX (X0 S)) A) x) : ℝ) : ℂ) =
      ∑ ν, ∑ x, ∑ μ, ∑ x', k ν x μ x' := by
    have h0 : ((∑ x, hs2 (Pop S (X0 S) (W1 S) Set.univ (Ds1L a1 (cfgX (X0 S)) A) x) : ℝ) : ℂ) =
        herm S (Pop S (X0 S) (W1 S) Set.univ (Ds1L a1 (cfgX (X0 S)) A))
          (Pop S (X0 S) (W1 S) Set.univ (Ds1L a1 (cfgX (X0 S)) A)) := by
      rw [herm_eq]; push_cast
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Schur.ntr_conj_self, hs_sq]
    rw [h0, herm_P_eq]
    refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun x _ => ?_
    rw [kG_apply, Matrix.mul_sum, ntr_sum]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [Matrix.mul_sum, ntr_sum]
  have e3 : (herm S (Pop S (X0 S) (W1 S) Set.univ (Ds1L a1 (cfgX (X0 S)) (expA S ph A)))
      (Pop S (X0 S) (W1 S) Set.univ (Ds1L a1 (cfgX (X0 S)) (expA S (fun x => -ph x) A)))).re -
      ∑ x, hs2 (Pop S (X0 S) (W1 S) Set.univ (Ds1L a1 (cfgX (X0 S)) A) x) =
      (∑ ν, ∑ x, ∑ μ, ∑ x', ((Real.exp (ph x) * Real.exp (-ph x') - 1 : ℝ) : ℂ) * k ν x μ x').re := by
    rw [e1, ← Complex.ofReal_re (∑ x, hs2 (Pop S (X0 S) (W1 S) Set.univ (Ds1L a1 (cfgX (X0 S)) A) x)), e2,
      ← Complex.sub_re]
    congr 1
    simp only [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun x _ =>
      Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun x' _ => ?_
    push_cast; ring
  rw [e3]
  -- the bound of a term
  set u : Site NF → ℝ := fun x => ((S.L : ℝ) ^ (S.toDomSeq).sc (bc S.toDomSeq x))⁻¹ * ∑ ν, hs (A ν x)
  have hu : ∀ x, 0 ≤ u x := fun x => mul_nonneg (by positivity) (Finset.sum_nonneg fun ν _ => hs_nonneg _)
  set K : Site NF → Site NF → ℝ := fun x x' => ((S.L : ℝ) ^ (4 * (S.toDomSeq).sc (bc S.toDomSeq x')))⁻¹ *
    Real.exp (-(1 / 2 * θ * S.dF (bc S.toDomSeq x) (bc S.toDomSeq x')))
  set C1 := Real.exp θ * (4 / θ + 4)
  have hCPg : 0 ≤ ScalarHyp.CPg S N δ0 0 := by
    have h1 : 0 ≤ (S.toContSeq).c1 (1 / 2) (thetaB S N δ0) := by unfold Summation.ContSeq.c1; positivity
    have h2 : 0 ≤ (S.toContSeq).c1 (1 / 2) (7 / 16 * thetaB S N δ0) := by unfold Summation.ContSeq.c1; positivity
    unfold ScalarHyp.CPg gammaB; positivity
  have hterm : ∀ x x', ∑ ν, ∑ μ, ‖((Real.exp (ph x) * Real.exp (-ph x') - 1 : ℝ) : ℂ) * k ν x μ x'‖ ≤
      ScalarHyp.CPg S N δ0 0 * δ * C1 * (K x x' * u x' * u x) := by
    intro x x'
    set d := S.dF (bc S.toDomSeq x) (bc S.toDomSeq x')
    have hd0 : 0 ≤ d := S.dF_nonneg _ _
    have hdx : S.dF x x' ≤ d + 4 := by
      have h2 := S.dF_triangle x (bc S.toDomSeq x) x'
      have h3 := S.dF_triangle (bc S.toDomSeq x) (bc S.toDomSeq x') x'
      have h4 := dF_bc_le S x
      have h5 := dF_bc_le S x'
      rw [S.dF_comm] at h5
      linarith
    have hexp : |Real.exp (ph x) * Real.exp (-ph x') - 1| ≤ δ * (d + 4) * Real.exp (δ * (d + 4)) := by
      have e : Real.exp (ph x) * Real.exp (-ph x') = Real.exp (ph x - ph x') := by rw [← Real.exp_add]; ring_nf
      rw [e]
      refine (abs_exp_sub_one_le' _).trans ?_
      have h1 : |ph x - ph x'| ≤ δ * (d + 4) := (hph x x').trans (mul_le_mul_of_nonneg_left hdx hδ)
      exact mul_le_mul h1 (Real.exp_le_exp.2 h1) (Real.exp_pos _).le (by positivity)
    have hw := conj_weight_le hθ hδ hδθ hd0
    set a := ((S.L : ℝ) ^ (S.toDomSeq).sc (bc S.toDomSeq x))⁻¹
    set b := ((S.L : ℝ) ^ (S.toDomSeq).sc (bc S.toDomSeq x'))⁻¹
    set c4 := ((S.L : ℝ) ^ (4 * (S.toDomSeq).sc (bc S.toDomSeq x')))⁻¹
    set E := Real.exp (-(θ * d))
    set cc := δ * (d + 4) * Real.exp (δ * (d + 4))
    set CP := ScalarHyp.CPg S N δ0 0
    have ha : 0 ≤ a := by positivity
    have hb : 0 ≤ b := by positivity
    have hk : ∀ ν μ, ‖k ν x μ x'‖ ≤ hs (A ν x) * (CP * a * (b * c4 * E) * hs (A μ x')) := by
      intro ν μ
      refine (norm_ntr_mul_le _ _).trans ?_
      rw [hs_conjTranspose]
      exact mul_le_mul_of_nonneg_left
        (kG_bound S H hRMb hRMs4 hsmallT hRMθs hRMθc ν x μ x' (A μ x')) (hs_nonneg _)
    have hux : u x = a * ∑ ν, hs (A ν x) := rfl
    have hux' : u x' = b * ∑ μ, hs (A μ x') := rfl
    calc ∑ ν, ∑ μ, ‖((Real.exp (ph x) * Real.exp (-ph x') - 1 : ℝ) : ℂ) * k ν x μ x'‖
        ≤ ∑ ν, ∑ μ, cc * (hs (A ν x) * (CP * a * (b * c4 * E) * hs (A μ x'))) := by
          refine Finset.sum_le_sum fun ν _ => Finset.sum_le_sum fun μ _ => ?_
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          exact mul_le_mul hexp (hk ν μ) (norm_nonneg _) (by positivity)
      _ = CP * (cc * E) * (c4 * u x' * u x) := by
          rw [hux, hux', show CP * (cc * E) * (c4 * (b * ∑ μ, hs (A μ x')) * (a * ∑ ν, hs (A ν x))) =
            CP * (cc * E) * c4 * b * a * ((∑ ν, hs (A ν x)) * ∑ μ, hs (A μ x')) by ring,
            Finset.sum_mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun ν _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun μ _ => by ring
      _ ≤ CP * (δ * C1 * Real.exp (-(1 / 2 * θ * d))) * (c4 * u x' * u x) := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hw hCPg) ?_
          have := hu x; have := hu x'; positivity
      _ = CP * δ * C1 * (K x x' * u x' * u x) := by simp only [K]; ring
  -- the sum and the test of Schur
  have hschur := schur_kernel S hθ hRMsum hRMsum2 hRMss u hu
  have hu2 : ∑ x, u x ^ 2 = ∑ x, (((S.L : ℝ) ^ (S.toDomSeq).sc x)⁻¹ * ∑ ν, hs (A ν x)) ^ 2 := by
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [u, sc_bc]
  have hC1 : 0 ≤ C1 := by positivity
  calc |(∑ ν, ∑ x, ∑ μ, ∑ x', ((Real.exp (ph x) * Real.exp (-ph x') - 1 : ℝ) : ℂ) * k ν x μ x').re|
      ≤ ‖∑ ν, ∑ x, ∑ μ, ∑ x', ((Real.exp (ph x) * Real.exp (-ph x') - 1 : ℝ) : ℂ) * k ν x μ x'‖ :=
        Complex.abs_re_le_norm _
    _ ≤ ∑ x, ∑ x', ∑ ν, ∑ μ, ‖((Real.exp (ph x) * Real.exp (-ph x') - 1 : ℝ) : ℂ) * k ν x μ x'‖ := by
        refine le_trans ((norm_sum_le _ _).trans (Finset.sum_le_sum fun ν _ => (norm_sum_le _ _).trans
          (Finset.sum_le_sum fun x _ => (norm_sum_le _ _).trans (Finset.sum_le_sum fun μ _ =>
            norm_sum_le _ _)))) (le_of_eq ?_)
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.sum_congr rfl fun ν _ => Finset.sum_comm, Finset.sum_comm]
    _ ≤ ∑ x, ∑ x', ScalarHyp.CPg S N δ0 0 * δ * C1 * (K x x' * u x' * u x) :=
        Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun x' _ => hterm x x'
    _ = ScalarHyp.CPg S N δ0 0 * δ * C1 * ∑ x, ∑ x', K x x' * u x' * u x := by simp only [Finset.mul_sum]
    _ ≤ ScalarHyp.CPg S N δ0 0 * δ * C1 * (((S.toContSeq).c1 (1 / 2) θ +
          (S.L : ℝ) ^ 4 * (S.toContSeq).c1 (1 / 2) (θ / 2)) / 2 * ∑ x, u x ^ 2) :=
        mul_le_mul_of_nonneg_left hschur (by positivity)
    _ = _ := by rw [hu2]; unfold CPv; ring

open SFBox SequenceOperators in
/-- The sesquilinear form of `Δ_𝖺(id)`: `⟨∇B, ∇C⟩ + ⟨QB, QC⟩ - N⟨P∂^*B, P∂^*C⟩` (in the norm of `V`). -/
def formA2 [NeZero N] (B C : Fin 4 → Site NF → Mat) : ℂ :=
  gradB S B C + QB2 S B C - (N : ℂ) * herm S (Pop S (X0 S) (W1 S) Set.univ (Ds1L a1 (cfgX (X0 S)) B))
    (Pop S (X0 S) (W1 S) Set.univ (Ds1L a1 (cfgX (X0 S)) C))

lemma sum_u_sq_le (A : Fin 4 → Site NF → Mat) :
    (N : ℝ) * ∑ x, (((S.L : ℝ) ^ (S.toDomSeq).sc x)⁻¹ * ∑ ν, hs (A ν x)) ^ 2 ≤ 4 * wnorm S A := by
  unfold wnorm
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun x _ => ?_
  have h1 : (∑ ν, hs (A ν x)) ^ 2 ≤ 4 * ∑ ν, hs (A ν x) ^ 2 := by
    rw [Fin.sum_univ_four, Fin.sum_univ_four]
    nlinarith [sq_nonneg (hs (A 0 x) - hs (A 1 x)), sq_nonneg (hs (A 0 x) - hs (A 2 x)),
      sq_nonneg (hs (A 0 x) - hs (A 3 x)), sq_nonneg (hs (A 1 x) - hs (A 2 x)),
      sq_nonneg (hs (A 1 x) - hs (A 3 x)), sq_nonneg (hs (A 2 x) - hs (A 3 x))]
  have h2 : ∑ ν, ‖emb (N := N) (A ν x)‖ ^ 2 = (N : ℝ) * ∑ ν, hs (A ν x) ^ 2 := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun ν _ => by rw [norm_emb_sq, hs_sq]
  rw [h2, mul_pow]
  push_cast
  have hw : 0 ≤ (((S.L : ℝ) ^ (S.toDomSeq).sc x)⁻¹) ^ 2 := by positivity
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  calc (N : ℝ) * ((((S.L : ℝ) ^ (S.toDomSeq).sc x)⁻¹) ^ 2 * (∑ ν, hs (A ν x)) ^ 2)
      ≤ (N : ℝ) * ((((S.L : ℝ) ^ (S.toDomSeq).sc x)⁻¹) ^ 2 * (4 * ∑ ν, hs (A ν x) ^ 2)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 hw) hN
    _ = 4 * (((((S.L : ℝ) ^ (S.toDomSeq).sc x) ^ 2)⁻¹) * ((N : ℝ) * ∑ ν, hs (A ν x) ^ 2)) := by
        rw [inv_pow]; ring

/-- The constant of the conjugation at the trivial configuration. -/
def Cconj (S : SeqDom) (N : ℕ) (δ0 : ℝ) : ℝ := 16 * (S.L : ℝ) ^ 2 + 96 * (S.L : ℝ) ^ 3 + 4 * CPv S N δ0

open SFBox SequenceOperators in
/-- **The conjugated form of `Δ_𝖺(id)`** (lem:sf-vector-decay, the trivial configuration):
`Re⟨(e^φA)^*, Δ_𝖺(id)(e^{-φ}A)⟩ ≥ ⟨A^*, Δ_𝖺(id)A⟩ - C_conjδ‖A‖_w²` for `0 ≤ δ ≤ min(θ/4, 1/(16L))`. -/
theorem conj_triv [NeZero N] {δ0 : ℝ} (H : ScalarHyp (N := N) S (X0 S) 0 (W1 S) 0 Set.univ δ0)
    (hRMb : (S.toContSeq).r1 (1 / 2) (1 / 32 * δ0) ≤ ((S.R * S.L ^ S.mM : ℕ) : ℝ))
    (hRMs4 : 32 * Real.log S.L / (1 / 4 * δ0) ≤ ((S.R * S.L ^ S.mM : ℕ) : ℝ))
    (hsmallT : CTd S N δ0 0 0 * (S.toContSeq).c1 (1 / 2) (1 / 32 * δ0) ≤ gammaB N / 4)
    (hRMθs : 32 * Real.log S.L / (thetaB S N δ0 / 2) ≤ ((S.R * S.L ^ S.mM : ℕ) : ℝ))
    (hRMθc : (S.toContSeq).r1 (1 / 2) (7 / 16 * thetaB S N δ0) ≤ ((S.R * S.L ^ S.mM : ℕ) : ℝ))
    (hRMsum : (S.toContSeq).r1 (1 / 2) (7 / 32 * thetaB S N δ0) ≤ ((S.R * S.L ^ S.mM : ℕ) : ℝ))
    (hRMsum2 : (S.toContSeq).r1 (1 / 2) (7 / 32 * thetaB S N δ0 / 2) ≤ ((S.R * S.L ^ S.mM : ℕ) : ℝ))
    (hRMss : 32 * Real.log S.L / (2 * (7 / 32 * thetaB S N δ0)) ≤ ((S.R * S.L ^ S.mM : ℕ) : ℝ))
    (hRM18 : 18 * (S.L : ℝ) ≤ ((S.R * S.L ^ S.mM : ℕ) : ℝ))
    {δ : ℝ} (hδ : 0 ≤ δ) (hδθ : δ ≤ 1 / 4 * (7 / 32 * thetaB S N δ0)) (hδL : 16 * S.L * δ ≤ 1)
    (ph : Site NF → ℝ) (hph : ∀ x x', |ph x - ph x'| ≤ δ * S.dF x x') (A : Fin 4 → Site NF → Mat) :
    formA S A - Cconj S N δ0 * δ * wnorm S A ≤ (formA2 S (expA S ph A) (expA S (fun x => -ph x) A)).re := by
  have hRM1 : 1 ≤ S.R * S.L ^ S.mM := Nat.one_le_iff_ne_zero.2 (by have := S.one_le_R; have := S.Lpos; positivity)
  have hL1 : (1 : ℝ) ≤ S.L := by exact_mod_cast S.Lpos
  have hδL' : δ * S.L ≤ 1 := by nlinarith
  have hδ1 : δ ≤ 1 := by nlinarith
  have hg := grad_conj S hRM1 hδ hδL' ph hph A
  have hq := Q_conj S hRM18 hδ hδL ph hph A
  have hp := P_conj S H hRMb hRMs4 hsmallT hRMθs hRMθc hRMsum hRMsum2 hRMss hδ hδθ ph hph A
  have hu := sum_u_sq_le S A
  have hw0 : 0 ≤ wnorm S A := by
    unfold wnorm; exact Finset.sum_nonneg fun x _ => mul_nonneg (by positivity)
      (Finset.sum_nonneg fun μ _ => sq_nonneg _)
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hCPv : 0 ≤ CPv S N δ0 := by
    have hθ : 0 < 7 / 32 * thetaB S N δ0 := by have := H.thetaB_pos (N := N); positivity
    have h1 : 0 ≤ (S.toContSeq).c1 (1 / 2) (thetaB S N δ0) := by unfold Summation.ContSeq.c1; positivity
    have h2 : 0 ≤ (S.toContSeq).c1 (1 / 2) (7 / 16 * thetaB S N δ0) := by unfold Summation.ContSeq.c1; positivity
    have h3 : 0 ≤ (S.toContSeq).c1 (1 / 2) (7 / 32 * thetaB S N δ0) := by unfold Summation.ContSeq.c1; positivity
    have h4 : 0 ≤ (S.toContSeq).c1 (1 / 2) (7 / 32 * thetaB S N δ0 / 2) := by unfold Summation.ContSeq.c1; positivity
    unfold CPv ScalarHyp.CPg gammaB; positivity
  -- the three parts
  have e : (formA2 S (expA S ph A) (expA S (fun x => -ph x) A)).re =
      (gradB S (expA S ph A) (expA S (fun x => -ph x) A)).re + (QB2 S (expA S ph A) (expA S (fun x => -ph x) A)).re -
        N * (herm S (Pop S (X0 S) (W1 S) Set.univ (Ds1L a1 (cfgX (X0 S)) (expA S ph A)))
          (Pop S (X0 S) (W1 S) Set.univ (Ds1L a1 (cfgX (X0 S)) (expA S (fun x => -ph x) A)))).re := by
    unfold formA2
    simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul,
      sub_zero]
  rw [e]
  unfold formA formF
  set Pf := (herm S (Pop S (X0 S) (W1 S) Set.univ (Ds1L a1 (cfgX (X0 S)) (expA S ph A)))
    (Pop S (X0 S) (W1 S) Set.univ (Ds1L a1 (cfgX (X0 S)) (expA S (fun x => -ph x) A)))).re
  set p := ∑ x, hs2 (Pop S (X0 S) (W1 S) Set.univ (Ds1L a1 (cfgX (X0 S)) A) x)
  set U2 := ∑ x, (((S.L : ℝ) ^ (S.toDomSeq).sc x)⁻¹ * ∑ ν, hs (A ν x)) ^ 2
  have hP : (N : ℝ) * Pf ≤ N * p + CPv S N δ0 * δ * (N * U2) := by
    have h1 : Pf ≤ p + CPv S N δ0 * δ * U2 := by have := (abs_le.1 hp).2; linarith
    have := mul_le_mul_of_nonneg_left h1 hN
    linarith
  have hU : CPv S N δ0 * δ * (N * U2) ≤ CPv S N δ0 * δ * (4 * wnorm S A) :=
    mul_le_mul_of_nonneg_left hu (by positivity)
  have hδ2 : 16 * (S.L : ℝ) ^ 2 * δ ^ 2 * wnorm S A ≤ 16 * (S.L : ℝ) ^ 2 * δ * wnorm S A := by
    have : δ ^ 2 ≤ δ := by nlinarith
    have := mul_le_mul_of_nonneg_left this (show (0 : ℝ) ≤ 16 * (S.L : ℝ) ^ 2 by positivity)
    nlinarith
  have hq' := (abs_le.1 hq).1
  unfold Cconj
  linarith

/-! ### The complex field: the covariant Laplacian -/

open SFBox SFBox.SeqDomBox
open scoped Matrix.Norms.L2Operator

open SFBox in
/-- The sesquilinear form of the covariant Laplacian `Δ_𝐔` of the components. -/
def gradBU (X : Fin 4 → Site NF → Mat) (B C : Fin 4 → Site NF → Mat) : ℂ :=
  ∑ μ, ∑ x, ∑ ν, inner ℂ (emb (N := N) (Dfw 1 (cfgX X) ν (B μ) x)) (emb (N := N) (Dfw 1 (cfgX X) ν (C μ) x))

omit S in
lemma inner_pert {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (u e1 v e2 : V) :
    |(inner ℂ (u + e1) (v + e2)).re - (inner ℂ u v).re| ≤ ‖u‖ * ‖e2‖ + ‖e1‖ * ‖v‖ + ‖e1‖ * ‖e2‖ := by
  have e : (inner ℂ (u + e1) (v + e2)).re - (inner ℂ u v).re =
      (inner ℂ u e2).re + (inner ℂ e1 v).re + (inner ℂ e1 e2).re := by
    simp only [inner_add_left, inner_add_right, Complex.add_re]; ring
  rw [e]
  have h1 := (Complex.abs_re_le_norm (inner ℂ u e2)).trans (norm_inner_le_norm u e2)
  have h2 := (Complex.abs_re_le_norm (inner ℂ e1 v)).trans (norm_inner_le_norm e1 v)
  have h3 := (Complex.abs_re_le_norm (inner ℂ e1 e2)).trans (norm_inner_le_norm e1 e2)
  calc |(inner ℂ u e2).re + (inner ℂ e1 v).re + (inner ℂ e1 e2).re|
      ≤ |(inner ℂ u e2).re| + |(inner ℂ e1 v).re| + |(inner ℂ e1 e2).re| := abs_add_three _ _ _
    _ ≤ _ := by linarith

omit S in
lemma emb_add' (Y Z : Mat) : emb (N := N) (Y + Z) = emb Y + emb Z := embL.map_add Y Z

omit S in
lemma emb_sub' (Y Z : Mat) : emb (N := N) (Y - Z) = emb Y - emb Z := embL.map_sub Y Z

open SFBox in
lemma Dfw_split (X : Fin 4 → Site NF → Mat) (ν : Fin 4) (f : Site NF → Mat) (x : Site NF) :
    Dfw 1 (cfgX X) ν f x = (f (x + unit NF ν) - f x) +
      (Ad (expU (Complex.I • X ν x)) (f (x + unit NF ν)) - f (x + unit NF ν)) := by
  simp only [Dfw, inv_one, one_smul, cfgX]; abel

omit S in
/-- The algebra of the bound of a bond of the covariant Laplacian. -/
lemma grad_pert_alg {n0 n' r m E α δ L : ℝ} (hn0 : 0 ≤ n0) (hn' : 0 ≤ n') (hr : 0 ≤ r) (hE0 : 0 ≤ E)
    (hα0 : 0 ≤ α) (hδ : 0 ≤ δ) (hL1 : 1 ≤ L) (hm : m ≤ n0 + 2 * (δ * L * r) * n') (hE : E ≤ 6 * α * L * r * n')
    (hδ1 : δ * L ≤ 1) (hα1 : α ≤ 1) :
    4 * m * E + E ^ 2 ≤ 12 * α * L * n0 ^ 2 + 96 * L ^ 2 * α * (r ^ 2 * n' ^ 2) := by
  have hL0 : 0 ≤ L := by linarith
  set X := r ^ 2 * n' ^ 2
  have hX : 0 ≤ X := by positivity
  have h1 : 4 * m * E ≤ 4 * (n0 + 2 * (δ * L * r) * n') * (6 * α * L * r * n') :=
    mul_le_mul (mul_le_mul_of_nonneg_left hm (by norm_num)) hE hE0 (by positivity)
  have h2 : E ^ 2 ≤ (6 * α * L * r * n') ^ 2 := pow_le_pow_left₀ hE0 hE 2
  have h3 : 4 * n0 * (6 * α * L * r * n') ≤ 12 * α * L * (n0 ^ 2 + X) := by
    have h := sq_nonneg (n0 - r * n')
    have e : (n0 - r * n') ^ 2 = n0 ^ 2 - 2 * n0 * (r * n') + X := by simp only [X]; ring
    have h' : 2 * n0 * (r * n') ≤ n0 ^ 2 + X := by linarith
    have e2 : 4 * n0 * (6 * α * L * r * n') = 12 * α * L * (2 * n0 * (r * n')) := by ring
    rw [e2]; exact mul_le_mul_of_nonneg_left h' (by positivity)
  have h4 : 4 * (2 * (δ * L * r) * n') * (6 * α * L * r * n') ≤ 48 * L ^ 2 * α * X := by
    have e : 4 * (2 * (δ * L * r) * n') * (6 * α * L * r * n') = (48 * L * α * X) * (δ * L) := by simp only [X]; ring
    rw [e]
    have : (48 * L * α * X) * (δ * L) ≤ (48 * L * α * X) * L :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith
  have h5 : (6 * α * L * r * n') ^ 2 ≤ 36 * L ^ 2 * α * X := by
    have e : (6 * α * L * r * n') ^ 2 = (36 * L ^ 2 * α * X) * α := by simp only [X]; ring
    rw [e]
    have : (36 * L ^ 2 * α * X) * α ≤ (36 * L ^ 2 * α * X) * 1 := mul_le_mul_of_nonneg_left hα1 (by positivity)
    linarith
  have h6 : 12 * α * L * X ≤ 12 * L ^ 2 * α * X := by
    have e : 12 * α * L * X = (12 * α * X) * L := by ring
    have e' : 12 * L ^ 2 * α * X = (12 * α * X) * L ^ 2 := by ring
    rw [e, e']
    exact mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
  have e1 : 4 * (n0 + 2 * (δ * L * r) * n') * (6 * α * L * r * n') =
      4 * n0 * (6 * α * L * r * n') + 4 * (2 * (δ * L * r) * n') * (6 * α * L * r * n') := by ring
  have e3 : 12 * α * L * (n0 ^ 2 + X) = 12 * α * L * n0 ^ 2 + 12 * α * L * X := by ring
  linarith

/-- **The covariant Laplacian at a small field**:
`|Re⟨D_𝐔(e^φA), D_𝐔(e^{-φ}A)⟩ - Re⟨∂(e^φA), ∂(e^{-φ}A)⟩| ≤ 12α₁L‖∇A‖² + 384L²α₁‖A‖_w²`. -/
theorem gradU_conj (hRML : (S.L : ℝ) < ((S.R * S.L ^ S.mM : ℕ) : ℝ)) {X : Fin 4 → Site NF → Mat} {α₁ : ℝ}
    (hX : RegField S X α₁) (hα0 : 0 ≤ α₁) (hα : α₁ ≤ 1 / 32) {δ : ℝ} (hδ : 0 ≤ δ) (hδL : 16 * S.L * δ ≤ 1)
    (ph : Site NF → ℝ) (hph : ∀ x x', |ph x - ph x'| ≤ δ * S.dF x x') (A : Fin 4 → Site NF → Mat) :
    |(gradBU S X (expA S ph A) (expA S (fun x => -ph x) A)).re -
      (gradB S (expA S ph A) (expA S (fun x => -ph x) A)).re| ≤
      12 * α₁ * S.L * gradNorm S A + 384 * (S.L : ℝ) ^ 2 * α₁ * wnorm S A := by
  have hL1 : (1 : ℝ) ≤ S.L := by exact_mod_cast S.Lpos
  have hL0 : (0 : ℝ) < S.L := by linarith
  have hRM1 : 1 ≤ S.R * S.L ^ S.mM := Nat.one_le_iff_ne_zero.2 (by have := S.one_le_R; have := S.Lpos; positivity)
  set w : Site NF → ℝ := fun x => ((S.L : ℝ) ^ (S.toDomSeq).sc x)⁻¹ ^ 2
  set a : Fin 4 → Site NF → VS N 1 := fun μ x => emb (A μ x)
  -- the bound of a bond
  have hterm : ∀ μ x ν, |(inner ℂ (emb (N := N) (Dfw 1 (cfgX X) ν (expA S ph A μ) x))
        (emb (N := N) (Dfw 1 (cfgX X) ν (expA S (fun x => -ph x) A μ) x))).re -
      (inner ℂ (emb (N := N) (expA S ph A μ (x + unit NF ν)) - emb (expA S ph A μ x))
        (emb (N := N) (expA S (fun x => -ph x) A μ (x + unit NF ν)) - emb (expA S (fun x => -ph x) A μ x))).re| ≤
      12 * α₁ * S.L * gbond S A μ x ν + 96 * (S.L : ℝ) ^ 2 * α₁ * (w (x + unit NF ν) * ‖a μ (x + unit NF ν)‖ ^ 2) := by
    intro μ x ν
    set x' := x + unit NF ν
    set s := ph x' - ph x
    set r : ℝ := ((S.L : ℝ) ^ (S.toDomSeq).sc x')⁻¹
    have hr0 : 0 ≤ r := by positivity
    have hr1 : r ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hL1)
    -- the field on the bond
    set i := min ((S.toDomSeq).sc x) ((S.toDomSeq).sc x')
    have hXb : ‖X ν x‖ ≤ α₁ * S.L * r := by
      have h1 := hX.hA i x ν (S.toDomSeq.Ω_anti (min_le_left _ _) (S.toDomSeq.mem_sc x))
        (S.toDomSeq.Ω_anti (min_le_right _ _) (S.toDomSeq.mem_sc x'))
      have hsc : (S.toDomSeq).sc x' ≤ (S.toDomSeq).sc x + 1 := (PartitionUnity.sc_unit S hRML x ν).1
      have h2 : ((S.L : ℝ) ^ i)⁻¹ ≤ S.L * r := by
        simp only [r]
        rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), ← div_eq_inv_mul, div_le_iff₀ (by positivity)]
        rw [show (S.L : ℝ) * (S.L : ℝ) ^ i = (S.L : ℝ) ^ (i + 1) by ring]
        exact pow_le_pow_right₀ hL1 (by simp only [i]; omega)
      calc ‖X ν x‖ ≤ α₁ * ((S.L : ℝ) ^ i)⁻¹ := h1
        _ ≤ α₁ * (S.L * r) := mul_le_mul_of_nonneg_left h2 hα0
        _ = α₁ * S.L * r := by ring
    have hXs : ‖X ν x‖ ≤ 1 / 32 := by
      have : α₁ * S.L * r ≤ α₁ * S.L * 1 := mul_le_mul_of_nonneg_left hr1 (by positivity)
      have hi : ((S.L : ℝ) ^ i)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hL1)
      have h1 := hX.hA i x ν (S.toDomSeq.Ω_anti (min_le_left _ _) (S.toDomSeq.mem_sc x))
        (S.toDomSeq.Ω_anti (min_le_right _ _) (S.toDomSeq.mem_sc x'))
      calc ‖X ν x‖ ≤ α₁ * ((S.L : ℝ) ^ i)⁻¹ := h1
        _ ≤ α₁ * 1 := mul_le_mul_of_nonneg_left hi hα0
        _ ≤ 1 / 32 := by linarith
    -- the weight on the bond
    have hs : |s| ≤ δ * S.L * r := by
      have h1 := hph x' x
      have h2 := (S.wdist_unit_le_sc hRM1 x ν).2
      rw [S.dF_comm] at h1
      calc |s| ≤ δ * S.dF x x' := h1
        _ ≤ δ * (S.L * r) := mul_le_mul_of_nonneg_left h2 hδ
        _ = δ * S.L * r := by ring
    have hs1 : |s| ≤ 1 / 16 := by
      have : δ * S.L * r ≤ δ * S.L * 1 := mul_le_mul_of_nonneg_left hr1 (by positivity)
      linarith
    -- the pieces
    obtain ⟨E, hEdef⟩ : ∃ E : VS N 1, E = emb (N := N) (Ad (expU (Complex.I • X ν x)) (A μ x') - A μ x') := ⟨_, rfl⟩
    have hE : ‖E‖ ≤ 6 * ‖X ν x‖ * ‖a μ x'‖ := by
      rw [hEdef]
      simp only [a, norm_emb]
      have := hs_Ad_exp_sub_le hXs (A μ x')
      have hN : 0 ≤ Real.sqrt N := Real.sqrt_nonneg _
      nlinarith
    have hAd : ∀ c : ℝ, Ad (expU (Complex.I • X ν x)) (((c : ℝ) : ℂ) • A μ x') =
        ((c : ℝ) : ℂ) • Ad (expU (Complex.I • X ν x)) (A μ x') := fun c => by
      simp only [Ad, Matrix.mul_smul, Matrix.smul_mul]
    have hsplit : ∀ q : Site NF → ℝ, emb (N := N) (Dfw 1 (cfgX X) ν (expA S q A μ) x) =
        (emb (N := N) (expA S q A μ x') - emb (expA S q A μ x)) + ((Real.exp (q x') : ℝ) : ℂ) • E := by
      intro q
      rw [hEdef, Dfw_split]
      simp only [expA, Ad_smul, emb_add', emb_sub', emb_smul', smul_sub]
      rfl
    rw [hsplit ph, hsplit (fun x => -ph x)]
    refine (inner_pert _ _ _ _).trans ?_
    -- the norms of the four vectors
    set α0 := a μ x' - a μ x
    have hu : ∀ p : ℝ, ∀ t : ℝ, |t| ≤ 1 / 16 → ‖((Real.exp (p + t) : ℝ) : ℂ) • a μ x' - ((Real.exp p : ℝ) : ℂ) • a μ x‖ ≤
        Real.exp p * (‖α0‖ + 2 * |t| * ‖a μ x'‖) := by
      intro p t ht
      have e : ((Real.exp (p + t) : ℝ) : ℂ) • a μ x' - ((Real.exp p : ℝ) : ℂ) • a μ x =
          ((Real.exp p : ℝ) : ℂ) • (α0 + ((Real.exp t - 1 : ℝ) : ℂ) • a μ x') := by
        simp only [α0, smul_add, smul_sub, smul_smul, Real.exp_add]; push_cast; module
      rw [e, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos p)]
      refine mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans ?_) (Real.exp_pos p).le
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
      have := Real.abs_exp_sub_one_le (show |t| ≤ 1 by linarith)
      nlinarith [norm_nonneg (a μ x')]
    have hup : ‖emb (N := N) (expA S ph A μ x') - emb (expA S ph A μ x)‖ ≤ Real.exp (ph x) * (‖α0‖ + 2 * |s| * ‖a μ x'‖) := by
      have := hu (ph x) s hs1
      simp only [expA, emb_smul', a] at this ⊢
      rwa [show ph x + s = ph x' by simp only [s]; ring] at this
    have hum : ‖emb (N := N) (expA S (fun x => -ph x) A μ x') - emb (expA S (fun x => -ph x) A μ x)‖ ≤
        Real.exp (-ph x) * (‖α0‖ + 2 * |-s| * ‖a μ x'‖) := by
      have := hu (-ph x) (-s) (by rwa [abs_neg])
      simp only [expA, emb_smul', a] at this ⊢
      rwa [show -ph x + -s = -ph x' by simp only [s]; ring] at this
    rw [abs_neg] at hum
    have hep : ‖((Real.exp (ph x') : ℝ) : ℂ) • E‖ = Real.exp (ph x') * ‖E‖ := by
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have hem : ‖((Real.exp (-ph x') : ℝ) : ℂ) • E‖ = Real.exp (-ph x') * ‖E‖ := by
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    rw [hep, hem]
    -- the exponentials
    have hx1 : Real.exp (ph x) * Real.exp (-ph x') ≤ 2 := by
      rw [← Real.exp_add]
      have h1 : |ph x + -ph x'| ≤ 1 / 16 := by rw [show ph x + -ph x' = -s by simp only [s]; ring, abs_neg]; exact hs1
      have := Real.abs_exp_sub_one_le (show |ph x + -ph x'| ≤ 1 by linarith)
      have := (abs_le.1 this).2
      linarith
    have hx2 : Real.exp (ph x') * Real.exp (-ph x) ≤ 2 := by
      rw [← Real.exp_add]
      have h1 : |ph x' + -ph x| ≤ 1 / 16 := by rw [show ph x' + -ph x = s by simp only [s]; ring]; exact hs1
      have := Real.abs_exp_sub_one_le (show |ph x' + -ph x| ≤ 1 by linarith)
      have := (abs_le.1 this).2
      linarith
    have hx3 : Real.exp (ph x') * Real.exp (-ph x') = 1 := by rw [← Real.exp_add]; simp
    -- assemble: `≤ 4(‖α0‖ + 2|s|‖a'‖)‖E‖ + ‖E‖²`
    set m := ‖α0‖ + 2 * |s| * ‖a μ x'‖
    have hm0 : 0 ≤ m := by positivity
    have hE0 : 0 ≤ ‖E‖ := norm_nonneg _
    have step1 : Real.exp (ph x) * m * (Real.exp (-ph x') * ‖E‖) + Real.exp (ph x') * ‖E‖ * (Real.exp (-ph x) * m) +
        Real.exp (ph x') * ‖E‖ * (Real.exp (-ph x') * ‖E‖) ≤ 4 * m * ‖E‖ + ‖E‖ ^ 2 := by
      have e1 : Real.exp (ph x) * m * (Real.exp (-ph x') * ‖E‖) = (Real.exp (ph x) * Real.exp (-ph x')) * (m * ‖E‖) := by ring
      have e2 : Real.exp (ph x') * ‖E‖ * (Real.exp (-ph x) * m) = (Real.exp (ph x') * Real.exp (-ph x)) * (m * ‖E‖) := by ring
      have e3 : Real.exp (ph x') * ‖E‖ * (Real.exp (-ph x') * ‖E‖) = (Real.exp (ph x') * Real.exp (-ph x')) * ‖E‖ ^ 2 := by ring
      rw [e1, e2, e3, hx3]
      have := mul_le_mul_of_nonneg_right hx1 (mul_nonneg hm0 hE0)
      have := mul_le_mul_of_nonneg_right hx2 (mul_nonneg hm0 hE0)
      linarith
    have hleft : ‖emb (N := N) (expA S ph A μ x') - emb (expA S ph A μ x)‖ * (Real.exp (-ph x') * ‖E‖) +
        Real.exp (ph x') * ‖E‖ * ‖emb (N := N) (expA S (fun x => -ph x) A μ x') - emb (expA S (fun x => -ph x) A μ x)‖ +
        Real.exp (ph x') * ‖E‖ * (Real.exp (-ph x') * ‖E‖) ≤ 4 * m * ‖E‖ + ‖E‖ ^ 2 := by
      refine le_trans ?_ step1
      have h1 := mul_le_mul_of_nonneg_right hup (show 0 ≤ Real.exp (-ph x') * ‖E‖ by positivity)
      have h2 := mul_le_mul_of_nonneg_left hum (show 0 ≤ Real.exp (ph x') * ‖E‖ by positivity)
      linarith
    refine hleft.trans ?_
    -- the bounds of `E` and of `s`
    have hE' : ‖E‖ ≤ 6 * α₁ * S.L * r * ‖a μ x'‖ := by
      have := mul_le_mul_of_nonneg_right hXb (norm_nonneg (a μ x'))
      nlinarith [norm_nonneg (a μ x')]
    have hg : gbond S A μ x ν = ‖α0‖ ^ 2 := rfl
    rw [hg]
    have hw' : w x' = r ^ 2 := rfl
    rw [hw']
    set n' := ‖a μ x'‖
    set n0 := ‖α0‖
    have hn' : 0 ≤ n' := norm_nonneg _
    have hn0 : 0 ≤ n0 := norm_nonneg _
    have hδ1 : δ * S.L ≤ 1 := by nlinarith
    have hα1 : α₁ ≤ 1 := by linarith
    have hm : m ≤ n0 + 2 * (δ * S.L * r) * n' := by
      simp only [m]
      have := mul_le_mul_of_nonneg_right hs (show 0 ≤ 2 * n' by positivity)
      nlinarith
    exact grad_pert_alg hn0 hn' hr0 hE0 hα0 hδ hL1 hm hE' hδ1 hα1
  -- the sum
  have hshift : ∀ μ ν, ∑ x, w (x + unit NF ν) * ‖a μ (x + unit NF ν)‖ ^ 2 = ∑ x, w x * ‖a μ x‖ ^ 2 :=
    fun μ ν => sum_shift_site S (fun x => w x * ‖a μ x‖ ^ 2) _
  have hwn : wnorm S A = ∑ μ, ∑ x, w x * ‖a μ x‖ ^ 2 := by
    unfold wnorm
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun x _ => ?_
    simp only [w, a]
    push_cast; rw [inv_pow]
  have hsum : ∑ μ, ∑ x, ∑ ν, (12 * α₁ * S.L * gbond S A μ x ν +
      96 * (S.L : ℝ) ^ 2 * α₁ * (w (x + unit NF ν) * ‖a μ (x + unit NF ν)‖ ^ 2)) =
      12 * α₁ * S.L * gradNorm S A + 384 * (S.L : ℝ) ^ 2 * α₁ * wnorm S A := by
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    unfold gradNorm
    congr 1
    have e2 : ∑ μ, ∑ x, ∑ ν, w (x + unit NF ν) * ‖a μ (x + unit NF ν)‖ ^ 2 =
        4 * ∑ μ, ∑ x, w x * ‖a μ x‖ ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun μ _ => ?_
      rw [Finset.sum_comm]
      simp only [hshift, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      norm_num
    rw [e2, hwn]; ring
  rw [← hsum]
  unfold gradBU gradB
  rw [Complex.re_sum, Complex.re_sum, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun μ _ => ?_)
  rw [Complex.re_sum, Complex.re_sum, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x _ => ?_)
  rw [Complex.re_sum, Complex.re_sum, ← Finset.sum_sub_distrib]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun ν _ => hterm μ x ν)

/-! ### The conclusion of `lem:sf-vector-decay` -/

/-- The sesquilinear pairing `⟨B^*, C⟩` of `1`-forms (in the norm of `V`). -/
def pair1V (B C : Fin 4 → Site NF → Mat) : ℂ := ∑ μ, ∑ x, inner ℂ (emb (N := N) (B μ x)) (emb (N := N) (C μ x))

lemma expA_zero (A : Fin 4 → Site NF → Mat) : expA S (fun _ => 0) A = A := by
  funext μ x; simp [expA]

lemma wnorm_nonneg' (A : Fin 4 → Site NF → Mat) : 0 ≤ wnorm S A := by
  unfold wnorm; exact Finset.sum_nonneg fun x _ => mul_nonneg (by positivity)
    (Finset.sum_nonneg fun μ _ => sq_nonneg _)

lemma gradNorm_nonneg' (A : Fin 4 → Site NF → Mat) : 0 ≤ gradNorm S A := by
  unfold gradNorm gbond; exact Finset.sum_nonneg fun μ _ => Finset.sum_nonneg fun x _ =>
    Finset.sum_nonneg fun ν _ => sq_nonneg _

/-- `‖A‖_w = 0` only for `A = 0`. -/
lemma eq_zero_of_wnorm (A : Fin 4 → Site NF → Mat) (h : wnorm S A = 0) : A = 0 := by
  unfold wnorm at h
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg fun x _ => mul_nonneg (by positivity)
    (Finset.sum_nonneg fun μ _ => sq_nonneg _)).1 h
  funext μ x
  have h1 := hterm x (Finset.mem_univ _)
  have hw : (0 : ℝ) < (((S.L ^ (S.toDomSeq).sc x : ℕ) : ℝ) ^ 2)⁻¹ := by
    have := S.Lpos; positivity
  have h2 : ∑ μ, ‖emb (N := N) (A μ x)‖ ^ 2 = 0 := by
    rcases mul_eq_zero.1 h1 with h | h
    · exact absurd h hw.ne'
    · exact h
  have h3 := (Finset.sum_eq_zero_iff_of_nonneg fun μ _ => sq_nonneg (‖emb (N := N) (A μ x)‖)).1 h2 μ
    (Finset.mem_univ _)
  have h4 : emb (N := N) (A μ x) = 0 := by
    rw [sq_eq_zero_iff, norm_eq_zero] at h3; exact h3
  have h5 := congrArg proj h4
  rw [proj_emb] at h5
  rw [h5]; simp [proj]
  rfl

/-- **Invertibility** (lem:sf-vector-decay, the conclusion): an operator `T` on the `1`-forms with
`Re⟨A^*, TA⟩ ≥ cN(A)²`, `c > 0`, is bijective (the space has finite dimension). -/
theorem bij_of_coercive (T : (Fin 4 → Site NF → Mat) →ₗ[ℂ] (Fin 4 → Site NF → Mat)) {c : ℝ} (hc : 0 < c)
    (h0 : ∀ A, c * (gradNorm S A + wnorm S A) ≤ (pair1V S A (T A)).re) : Function.Bijective T := by
  have hinj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro A hA
    have h := h0 A
    rw [hA] at h
    have h1 : (pair1V S A 0).re = 0 := by
      unfold pair1V; simp only [Pi.zero_apply]
      have : ∀ Z : Mat, emb (N := N) Z = embL Z := fun Z => rfl
      simp [this]
    rw [h1] at h
    have hg := gradNorm_nonneg' S A
    have hw := wnorm_nonneg' S A
    have hw0 : wnorm S A = 0 := by nlinarith
    exact eq_zero_of_wnorm S A hw0
  exact ⟨hinj, LinearMap.injective_iff_surjective.1 hinj⟩

end SFBounds
end CoreLean

end
