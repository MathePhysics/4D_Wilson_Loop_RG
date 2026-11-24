/-
`prop:sf-bounds` of BALABAN_CORE.tex (`4252790331fd`), the step "Values in the layers `j ≥ 2`", second part: the norm
`a⁻²‖u‖_{2,Q_{8+2L}}` of the number `Θ` of `lem:sf-local` by the weighted norm, on the fine lattice (`a₀ = 1`).

* `card_fiber_le`: the integers of an interval of the length `2R` in one class mod `n` are at most `2R/n + 1`;
  `sum_QF_le`: a sum over the box `Q_ρ` of the covering lattice of a function of the site underneath is at most
  `(2R/N₀ + 1)⁴` times the sum over the sites within `ρa` of `x` (`R = ⌈ρa⌉`): a site of the torus has at most that
  many points over it in the box (the core counts `(2(8 + 2L) + 1)⁴`).
* `theta_u_le`: for `j(x) = j ≥ 2`, `RM ≥ 8L²` and `φ` `δ₁`-Lipschitz in `d`, `δ₁ ≤ (128L)⁻¹`,
  `a⁻²(Σ_{n ∈ Q_{8+2L}}|u(n)|²)^{1/2} ≤ 25Le^L a⁻¹e^{-φ(x)}‖e^φu‖_w`.
-/
import CoreLean.SFValueHigh

open Finset Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace CoreLean
namespace SFBounds

open Lattices SeqDom Blocks SmallFieldBlocks SFBox SFBox.SeqDomBox LocalLaplacian

variable (S : SeqDom) {N m : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "NF" => SequenceAverages.N0 S
local notation "RMS" => ((S.R * S.L ^ S.mM : ℕ) : ℝ)
set_option quotPrecheck false in
local notation "jj" => (S.toDomSeq).sc

/-- **The integers of `[a - R, a + R]` in one class mod `n` are at most `2R/n + 1`.** -/
lemma card_fiber_le (n : ℕ) [NeZero n] (a : ℤ) (R : ℕ) (r : ZMod n) :
    ((Finset.Icc (a - R) (a + R)).filter fun t : ℤ => (t : ZMod n) = r).card ≤ 2 * R / n + 1 := by
  set f : ℤ → ℕ := fun t => (t - (a - R)).toNat / n
  have hmaps : Set.MapsTo f ((Finset.Icc (a - R) (a + R)).filter fun t : ℤ => (t : ZMod n) = r)
      (Finset.range (2 * R / n + 1)) := by
    intro t ht
    simp only [coe_filter, mem_Icc, Set.mem_ofPred_eq] at ht
    simp only [coe_range, Set.mem_Iio, f]
    have : (t - (a - R)).toNat ≤ 2 * R := by omega
    exact Nat.lt_succ_of_le (Nat.div_le_div_right this)
  have hinj : Set.InjOn f ((Finset.Icc (a - R) (a + R)).filter fun t : ℤ => (t : ZMod n) = r) := by
    intro t ht t' ht' hf
    simp only [coe_filter, mem_Icc, Set.mem_ofPred_eq] at ht ht'
    have hu : ((t - (a - R)).toNat : ℤ) = t - (a - R) := Int.toNat_of_nonneg (by omega)
    have hu' : ((t' - (a - R)).toNat : ℤ) = t' - (a - R) := Int.toNat_of_nonneg (by omega)
    have hdvd : (n : ℤ) ∣ ((t' - (a - R)).toNat : ℤ) - ((t - (a - R)).toNat : ℤ) := by
      rw [hu, hu', show t' - (a - R) - (t - (a - R)) = t' - t by ring]
      exact (ZMod.intCast_eq_intCast_iff_dvd_sub t t' n).1 (ht.2.trans ht'.2.symm)
    have hmod : (t - (a - R)).toNat % n = (t' - (a - R)).toNat % n := (Nat.modEq_iff_dvd.2 hdvd)
    have h1 := Nat.div_add_mod (t - (a - R)).toNat n
    have h2 := Nat.div_add_mod (t' - (a - R)).toNat n
    have hq : (t - (a - R)).toNat / n = (t' - (a - R)).toNat / n := hf
    have : (t - (a - R)).toNat = (t' - (a - R)).toNat := by rw [← h1, ← h2, hq, hmod]
    omega
  have := card_le_card_of_injOn f hmaps hinj
  rwa [card_range] at this

/-- **The multiplicity of the covering on a box.** -/
theorem sum_QF_le {n : ℕ} [NeZero n] {a ρ : ℝ} (ha : 0 < a) (x : Site n) (F : Site n → ℝ) (hF : ∀ y, 0 ≤ F y) :
    ∑ w ∈ QF a⁻¹ (xbar x) ρ, F (castS w) ≤
      ((2 * ⌈ρ / a⁻¹⌉₊ / n + 1) ^ 4 : ℕ) * ∑ y ∈ univ.filter (fun y : Site n => (dinf y x : ℝ) ≤ ρ * a), F y := by
  classical
  set R := ⌈ρ / a⁻¹⌉₊
  rw [← sum_fiberwise_of_maps_to (g := castS) (t := univ.filter fun y : Site n => (dinf y x : ℝ) ≤ ρ * a)
    (fun w hw => mem_filter.2 ⟨mem_univ _, dinf_castS_le ha x ((mem_QF (inv_pos.2 ha)).1 hw)⟩)]
  rw [mul_sum]
  refine sum_le_sum fun y _ => ?_
  rw [sum_congr rfl fun w hw => by rw [(mem_filter.1 hw).2], sum_const, nsmul_eq_mul]
  refine mul_le_mul_of_nonneg_right ?_ (hF y)
  have hsub : (QF a⁻¹ (xbar x) ρ).filter (fun w => castS w = y) ⊆
      Fintype.piFinset fun ν => (Finset.Icc (xbar x ν - R) (xbar x ν + R)).filter fun t : ℤ => (t : ZMod n) = y ν := by
    intro w hw
    obtain ⟨hwQ, hwy⟩ := mem_filter.1 hw
    unfold QF at hwQ
    obtain ⟨hwbox, -⟩ := mem_filter.1 hwQ
    rw [Fintype.mem_piFinset] at hwbox ⊢
    intro ν
    exact mem_filter.2 ⟨hwbox ν, by rw [← hwy]; rfl⟩
  have hc := card_le_card hsub
  rw [Fintype.card_piFinset] at hc
  have hprod : ∏ ν, ((Finset.Icc (xbar x ν - R) (xbar x ν + R)).filter fun t : ℤ => (t : ZMod n) = y ν).card ≤
      ∏ _ν : Fin 4, (2 * R / n + 1) := prod_le_prod' fun ν _ => card_fiber_le n _ R _
  rw [prod_const, card_univ, Fintype.card_fin] at hprod
  exact_mod_cast hc.trans hprod

/-- **`a⁻²‖u‖_{2,Q_{8+2L}}` by the weighted norm.** -/
theorem theta_u_le (hRM : 8 * (S.L : ℝ) ^ 2 ≤ RMS) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / (128 * S.L))
    {ph : Site NF → ℝ} (hph : ∀ x x', |ph x - ph x'| ≤ δ * S.dF x x') (u : Fin m → Site NF → Mat)
    {x : Site NF} (hj : 2 ≤ jj x) :
    ((S.L : ℝ) ^ jj x)⁻¹ ^ 2 * Real.sqrt (∑ w ∈ QF ((S.L : ℝ) ^ jj x)⁻¹ (xbar x) (8 + 2 * S.L),
        nsq fun k => u k (castS w)) ≤
      25 * S.L * Real.exp S.L * ((S.L : ℝ) ^ jj x)⁻¹ * Real.exp (-ph x) * Real.sqrt (wN S (eF S ph u)) := by
  set j := jj x
  set c : ℝ := (S.L : ℝ) ^ j
  have hL3 : (3 : ℝ) ≤ S.L := by exact_mod_cast S.three_le_L
  have hL0 : (0 : ℝ) < S.L := by linarith
  have hc : 0 < c := by positivity
  set M := wN S (eF S ph u)
  have hM : 0 ≤ M := wN_nonneg S _
  -- the multiplicity
  have hmult : 2 * ⌈(8 + 2 * (S.L : ℝ)) / c⁻¹⌉₊ / NF + 1 ≤ 5 := by
    have hNF : NF = 2 * S.L ^ (S.mT + S.k) := SequenceAverages.N0_eq S
    have hjk : j ≤ S.k := (S.toDomSeq).sc_le x
    have hceil : ⌈(8 + 2 * (S.L : ℝ)) / c⁻¹⌉₊ ≤ (8 + 2 * S.L) * S.L ^ j := by
      rw [div_inv_eq_mul, Nat.ceil_le]; push_cast; rfl
    have hpow : S.L ^ (j + 1) ≤ S.L ^ (S.mT + S.k) :=
      Nat.pow_le_pow_right S.Lpos (by have := S.one_le_mT; omega)
    have hL3n : 3 ≤ S.L := S.three_le_L
    have hlt : 2 * ⌈(8 + 2 * (S.L : ℝ)) / c⁻¹⌉₊ < 5 * NF := by
      rw [hNF]
      have h1 : 2 * ⌈(8 + 2 * (S.L : ℝ)) / c⁻¹⌉₊ ≤ 2 * ((8 + 2 * S.L) * S.L ^ j) := by omega
      have h2 : S.L ^ (j + 1) = S.L * S.L ^ j := by ring
      have h3 : 1 ≤ S.L ^ j := Nat.one_le_pow _ _ S.Lpos
      nlinarith
    have : 2 * ⌈(8 + 2 * (S.L : ℝ)) / c⁻¹⌉₊ / NF < 5 := (Nat.div_lt_iff_lt_mul (Nat.pos_of_ne_zero (NeZero.ne _))).2 hlt
    omega
  have hsum := sum_QF_le hc x (fun y => nsq fun k => u k y) (fun y => nsq_nonneg _) (ρ := 8 + 2 * S.L)
  -- the terms near `x`
  have hnear : ∀ y ∈ univ.filter (fun y : Site NF => (dinf y x : ℝ) ≤ (8 + 2 * S.L) * c),
      (nsq fun k => u k y) ≤ c ^ 2 * S.L ^ 2 * Real.exp (2 * S.L) * Real.exp (-2 * ph x) *
        (((S.L : ℝ) ^ (2 * jj y))⁻¹ * nsq fun k => eF S ph u k y) := by
    intro y hy
    have hy' := (mem_filter.1 hy).2
    have hsc : jj y ≤ j + 1 := by
      have hRM1 : 1 ≤ S.R * S.L ^ S.mM := by have := Nat.one_le_pow S.mM S.L S.Lpos; nlinarith [S.one_le_R]
      refine S.sc_le_succ_of_near hRM1 ?_
      rw [dinf_comm]
      have : (8 + 2 * (S.L : ℝ)) ≤ RMS := by nlinarith
      nlinarith
    have hd : S.dF x y ≤ 4 * (8 + 2 * S.L) * S.L := by
      have h1 := S.dF_le_near (c := 9 + 2 * S.L) (by nlinarith) x y (by rw [dinf_comm]; nlinarith)
      have hd1 : (d1 x y : ℝ) ≤ 4 * dinf x y := by exact_mod_cast d1_le_four_dinf S x y
      have hpow : c = S.L * (S.L : ℝ) ^ (j - 1) := by
        simp only [c]; rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ j)]
      have hp1 : (0 : ℝ) < (S.L : ℝ) ^ (j - 1) := by positivity
      refine h1.trans ?_
      rw [div_le_iff₀ hp1]
      have hy'' : (dinf x y : ℝ) ≤ (8 + 2 * S.L) * c := by rw [dinf_comm]; exact hy'
      calc (d1 x y : ℝ) ≤ 4 * dinf x y := hd1
        _ ≤ 4 * ((8 + 2 * S.L) * c) := by linarith
        _ = 4 * (8 + 2 * S.L) * S.L * (S.L : ℝ) ^ (j - 1) := by rw [hpow]; ring
    have hphd : -ph y ≤ δ * (4 * (8 + 2 * S.L) * S.L) - ph x := by
      have := (abs_le.1 (hph x y)).2
      nlinarith
    have hδL : δ * (4 * (8 + 2 * S.L) * S.L) ≤ S.L := by
      have : δ * (4 * (8 + 2 * S.L) * S.L) ≤ 1 / (128 * S.L) * (4 * (8 + 2 * S.L) * S.L) :=
        mul_le_mul_of_nonneg_right hδ (by positivity)
      have e : 1 / (128 * (S.L : ℝ)) * (4 * (8 + 2 * S.L) * S.L) = (8 + 2 * S.L) / 32 := by field_simp; ring
      linarith
    rw [nsq_eF]
    have hpow2 : ((S.L : ℝ) ^ (2 * jj y)) ≤ c ^ 2 * S.L ^ 2 := by
      calc ((S.L : ℝ) ^ (2 * jj y)) ≤ (S.L : ℝ) ^ (2 * (j + 1)) := pow_le_pow_right₀ (by linarith) (by omega)
        _ = c ^ 2 * S.L ^ 2 := by simp only [c]; ring
    have hexp : Real.exp (-2 * ph y) ≤ Real.exp (2 * S.L) * Real.exp (-2 * ph x) := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.2 (by linarith)
    have hq : (S.L : ℝ) ^ (2 * jj y) ≠ 0 := pow_ne_zero _ hL0.ne'
    have e : ((S.L : ℝ) ^ (2 * jj y))⁻¹ * (Real.exp (2 * ph y) * nsq fun k => u k y) *
        ((S.L : ℝ) ^ (2 * jj y) * Real.exp (-2 * ph y)) = nsq fun k => u k y := by
      rw [show -2 * ph y = -(2 * ph y) by ring, Real.exp_neg]
      field_simp
    have h0 := nsq_nonneg fun k => u k y
    calc (nsq fun k => u k y) = ((S.L : ℝ) ^ (2 * jj y))⁻¹ * (Real.exp (2 * ph y) * nsq fun k => u k y) *
          ((S.L : ℝ) ^ (2 * jj y) * Real.exp (-2 * ph y)) := e.symm
      _ ≤ ((S.L : ℝ) ^ (2 * jj y))⁻¹ * (Real.exp (2 * ph y) * nsq fun k => u k y) *
          (c ^ 2 * S.L ^ 2 * (Real.exp (2 * S.L) * Real.exp (-2 * ph x))) := by gcongr
      _ = _ := by ring
  have hsum2 : ∑ y ∈ univ.filter (fun y : Site NF => (dinf y x : ℝ) ≤ (8 + 2 * S.L) * c), (nsq fun k => u k y) ≤
      c ^ 2 * S.L ^ 2 * Real.exp (2 * S.L) * Real.exp (-2 * ph x) * M := by
    refine (sum_le_sum hnear).trans ?_
    rw [← mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun y _ _ => mul_nonneg (by positivity) (nsq_nonneg _)
  have htot : ∑ w ∈ QF c⁻¹ (xbar x) (8 + 2 * S.L), (nsq fun k => u k (castS w)) ≤
      625 * (c ^ 2 * S.L ^ 2 * Real.exp (2 * S.L) * Real.exp (-2 * ph x) * M) := by
    refine hsum.trans ?_
    have h5 : (((2 * ⌈(8 + 2 * (S.L : ℝ)) / c⁻¹⌉₊ / NF + 1) ^ 4 : ℕ) : ℝ) ≤ 625 := by
      have : (2 * ⌈(8 + 2 * (S.L : ℝ)) / c⁻¹⌉₊ / NF + 1) ^ 4 ≤ 5 ^ 4 := Nat.pow_le_pow_left hmult 4
      exact_mod_cast this
    have hS0 : 0 ≤ ∑ y ∈ univ.filter (fun y : Site NF => (dinf y x : ℝ) ≤ (8 + 2 * S.L) * c), (nsq fun k => u k y) :=
      sum_nonneg fun _ _ => nsq_nonneg _
    calc _ ≤ 625 * ∑ y ∈ univ.filter (fun y : Site NF => (dinf y x : ℝ) ≤ (8 + 2 * S.L) * c), (nsq fun k => u k y) :=
          mul_le_mul_of_nonneg_right h5 hS0
      _ ≤ _ := mul_le_mul_of_nonneg_left hsum2 (by norm_num)
  have hsq : Real.sqrt (625 * (c ^ 2 * S.L ^ 2 * Real.exp (2 * S.L) * Real.exp (-2 * ph x) * M)) =
      25 * c * S.L * Real.exp S.L * Real.exp (-ph x) * Real.sqrt M := by
    have e : 625 * (c ^ 2 * S.L ^ 2 * Real.exp (2 * S.L) * Real.exp (-2 * ph x) * M) =
        (25 * c * S.L * Real.exp S.L * Real.exp (-ph x)) ^ 2 * M := by
      rw [mul_pow, mul_pow, mul_pow, mul_pow, ← Real.exp_nat_mul, ← Real.exp_nat_mul]; push_cast; ring_nf
    rw [e, Real.sqrt_mul (pow_two_nonneg _), Real.sqrt_sq (by positivity)]
  calc c⁻¹ ^ 2 * Real.sqrt (∑ w ∈ QF c⁻¹ (xbar x) (8 + 2 * S.L), (nsq fun k => u k (castS w)))
      ≤ c⁻¹ ^ 2 * (25 * c * S.L * Real.exp S.L * Real.exp (-ph x) * Real.sqrt M) := by
        rw [← hsq]; gcongr
    _ = 25 * S.L * Real.exp S.L * c⁻¹ * Real.exp (-ph x) * Real.sqrt M := by
        field_simp

end SFBounds
end CoreLean

end
