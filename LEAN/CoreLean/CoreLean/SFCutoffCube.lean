/-
`prop:sf-vector-lower` of BALABAN_CORE.tex (`48a8b5af31cd`), the step "The cut-off minimiser": the cut-off of a cube
on the fine lattice, `χ(x) = Π_μχ₁(t_μ)` with the representative `t_μ` of `x_μ - c_μ` of least absolute value.

* `chi1Z_shift`: a step of `±1` moves the argument of `χ₁` by `±1` (both sides vanish near the antipode).
* `chiC`, `chiC_mem`, `chiC_one`, `chiC_zero`: the cut-off; `chiC_first`: `|χ(x ± e_μ) - χ(x)| ≤ 16/(9(h + 1))`;
  `chiC_lap`: `|Δχ| ≤ 128/(3(h + 1)²)`.
-/
import CoreLean.SFShellDecay
import CoreLean.SFCutoffProfile

open Finset

noncomputable section

namespace CoreLean
namespace SFBounds

open SFBump Blocks

variable {n : ℕ} [NeZero n]

/-- `χ₁` of the representative of `u ∈ ℤ/n` of least absolute value. -/
def chi1Z (h D : ℕ) (u : ZMod n) : ℝ := chi1 h D u.valMinAbs

lemma abs_valMinAbs_add_ge (u : ZMod n) (s : ℤ) (hs : |s| ≤ 1) :
    |u.valMinAbs| - 1 ≤ |(u + (s : ZMod n)).valMinAbs| := by
  have h1 := cd_add_le (u + (s : ZMod n)) (-(s : ZMod n))
  rw [add_neg_cancel_right] at h1
  have hs' := abs_le.1 hs
  have h2 : cd (-(s : ZMod n)) ≤ 1 := by
    rw [cd_neg]; exact (cd_intCast_le s).trans (by omega)
  have e1 : |u.valMinAbs| = (cd u : ℤ) := Int.abs_eq_natAbs _
  have e2 : |(u + (s : ZMod n)).valMinAbs| = (cd (u + (s : ZMod n)) : ℤ) := Int.abs_eq_natAbs _
  rw [e1, e2]
  omega

/-- **A step of `±1`** moves the argument of `χ₁` by `±1`, when `2(D + 2h + 4) ≤ n`. -/
lemma chi1Z_shift (h D : ℕ) (hn : 2 * (D + 2 * h + 4) ≤ n) (u : ZMod n) (s : ℤ) (hs : |s| ≤ 1) :
    chi1Z h D (u + (s : ZMod n)) = chi1 h D (u.valMinAbs + s) := by
  unfold chi1Z
  by_cases hu : |u.valMinAbs| ≤ D + 2 * h + 2
  · rw [valMinAbs_add_small u s (by omega)]
  · push_neg at hu
    have h1 := abs_valMinAbs_add_ge u s hs
    rw [chi1_zero h D (by omega), chi1_zero h D]
    have := abs_sub_abs_le_abs_sub u.valMinAbs (-s)
    rw [sub_neg_eq_add] at this
    have h2 : |-s| = |s| := abs_neg s
    omega

/-- **The cut-off of the cube with the centre `c`**. -/
def chiC (h D : ℕ) (c x : Fin 4 → ZMod n) : ℝ := ∏ ν, chi1Z h D (x ν - c ν)

lemma chi1Z_mem (h D : ℕ) (u : ZMod n) : 0 ≤ chi1Z h D u ∧ chi1Z h D u ≤ 1 := chi1_mem h D _

lemma chiC_mem (h D : ℕ) (c x : Fin 4 → ZMod n) : 0 ≤ chiC h D c x ∧ chiC h D c x ≤ 1 :=
  ⟨prod_nonneg fun ν _ => (chi1Z_mem h D _).1, Finset.prod_le_one₀ (fun ν _ => (chi1Z_mem h D _).1) fun ν _ => (chi1Z_mem h D _).2⟩

lemma chiC_one (h D : ℕ) (c x : Fin 4 → ZMod n) (hx : ∀ ν, |(x ν - c ν).valMinAbs| ≤ D + 1) : chiC h D c x = 1 :=
  prod_eq_one fun ν _ => chi1_one h D (hx ν)

lemma chiC_zero (h D : ℕ) (c x : Fin 4 → ZMod n) (ν : Fin 4) (hx : (D + 2 * h + 2 : ℤ) ≤ |(x ν - c ν).valMinAbs|) :
    chiC h D c x = 0 :=
  prod_eq_zero (mem_univ ν) (chi1_zero h D hx)

/-- The value of the cut-off after a step in the direction `μ`. -/
lemma chiC_step (h D : ℕ) (hn : 2 * (D + 2 * h + 4) ≤ n) (c x : Fin 4 → ZMod n) (μ : Fin 4) (s : ℤ) (hs : |s| ≤ 1) :
    chiC h D c (x + (s : ZMod n) • Pi.single μ 1) =
      chi1 h D ((x μ - c μ).valMinAbs + s) * ∏ ν ∈ univ.erase μ, chi1Z h D (x ν - c ν) := by
  unfold chiC
  rw [← mul_prod_erase univ _ (mem_univ μ)]
  congr 1
  · simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
    rw [show x μ + (s : ZMod n) - c μ = (x μ - c μ) + (s : ZMod n) by ring, chi1Z_shift h D hn _ s hs]
  · refine prod_congr rfl fun ν hν => ?_
    have hne : ν ≠ μ := ne_of_mem_erase hν
    simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_of_ne hne, smul_eq_mul, mul_zero, add_zero]

lemma prod_erase_mem (h D : ℕ) (c x : Fin 4 → ZMod n) (μ : Fin 4) :
    0 ≤ ∏ ν ∈ univ.erase μ, chi1Z h D (x ν - c ν) ∧ ∏ ν ∈ univ.erase μ, chi1Z h D (x ν - c ν) ≤ 1 :=
  ⟨prod_nonneg fun ν _ => (chi1Z_mem h D _).1, Finset.prod_le_one₀ (fun ν _ => (chi1Z_mem h D _).1) fun ν _ => (chi1Z_mem h D _).2⟩

lemma chiC_eq (h D : ℕ) (c x : Fin 4 → ZMod n) (μ : Fin 4) :
    chiC h D c x = chi1 h D ((x μ - c μ).valMinAbs) * ∏ ν ∈ univ.erase μ, chi1Z h D (x ν - c ν) := by
  unfold chiC; rw [← mul_prod_erase univ _ (mem_univ μ)]; rfl

/-- **The first differences of the cut-off.** -/
theorem chiC_first (h D : ℕ) (hn : 2 * (D + 2 * h + 4) ≤ n) (c x : Fin 4 → ZMod n) (μ : Fin 4) (s : ℤ) (hs : |s| ≤ 1) :
    |chiC h D c (x + (s : ZMod n) • Pi.single μ 1) - chiC h D c x| ≤ 16 / (9 * ((h : ℝ) + 1)) := by
  rw [chiC_step h D hn c x μ s hs, chiC_eq h D c x μ, ← sub_mul, abs_mul]
  obtain ⟨hp0, hp1⟩ := prod_erase_mem h D c x μ
  rw [abs_of_nonneg hp0]
  have hb : |chi1 h D ((x μ - c μ).valMinAbs + s) - chi1 h D ((x μ - c μ).valMinAbs)| ≤ 16 / (9 * ((h : ℝ) + 1)) := by
    rcases abs_le.1 hs with ⟨hs1, hs2⟩
    rcases (show s = -1 ∨ s = 0 ∨ s = 1 by omega) with rfl | rfl | rfl
    · have := chi1_first h D ((x μ - c μ).valMinAbs - 1)
      rw [sub_add_cancel, abs_sub_comm] at this
      simpa [sub_eq_add_neg] using this
    · simp; positivity
    · exact chi1_first h D _
  calc |chi1 h D ((x μ - c μ).valMinAbs + s) - chi1 h D ((x μ - c μ).valMinAbs)| * ∏ ν ∈ univ.erase μ, chi1Z h D (x ν - c ν)
      ≤ (16 / (9 * ((h : ℝ) + 1))) * 1 := mul_le_mul hb hp1 hp0 (by positivity)
    _ = _ := mul_one _

lemma unit_eq_smul (μ : Fin 4) : unit n μ = ((1 : ℤ) : ZMod n) • Pi.single μ 1 := by
  simp [unit]

lemma sub_unit_eq (x : Fin 4 → ZMod n) (μ : Fin 4) : x - unit n μ = x + ((-1 : ℤ) : ZMod n) • Pi.single μ 1 := by
  simp [unit, sub_eq_add_neg]

/-- **The first differences of the cut-off** at the bonds of the lattice. -/
lemma chiC_unit (h D : ℕ) (hn : 2 * (D + 2 * h + 4) ≤ n) (c x : Fin 4 → ZMod n) (μ : Fin 4) :
    |chiC h D c (x + unit n μ) - chiC h D c x| ≤ 16 / (9 * ((h : ℝ) + 1)) ∧
      |chiC h D c (x - unit n μ) - chiC h D c x| ≤ 16 / (9 * ((h : ℝ) + 1)) := by
  constructor
  · rw [unit_eq_smul]; exact chiC_first h D hn c x μ 1 (by norm_num)
  · rw [sub_unit_eq]; exact chiC_first h D hn c x μ (-1) (by norm_num)

/-- **The Laplacian of the cut-off**: `|Σ_ν(2χ(x) - χ(x + e_ν) - χ(x - e_ν))| ≤ 128/(3(h + 1)²)`. -/
theorem chiC_lap (h D : ℕ) (hn : 2 * (D + 2 * h + 4) ≤ n) (c x : Fin 4 → ZMod n) :
    |∑ ν, (2 * chiC h D c x - chiC h D c (x + unit n ν) - chiC h D c (x - unit n ν))| ≤
      128 / (3 * ((h : ℝ) + 1) ^ 2) := by
  have hpt : ∀ ν, |2 * chiC h D c x - chiC h D c (x + unit n ν) - chiC h D c (x - unit n ν)| ≤
      32 / (3 * ((h : ℝ) + 1) ^ 2) := by
    intro ν
    rw [sub_unit_eq, unit_eq_smul, chiC_step h D hn c x ν 1 (by norm_num), chiC_step h D hn c x ν (-1) (by norm_num),
      chiC_eq h D c x ν]
    set t := (x ν - c ν).valMinAbs
    obtain ⟨hp0, hp1⟩ := prod_erase_mem h D c x ν
    have e : 2 * (chi1 h D t * ∏ ν' ∈ univ.erase ν, chi1Z h D (x ν' - c ν')) -
        chi1 h D (t + 1) * ∏ ν' ∈ univ.erase ν, chi1Z h D (x ν' - c ν') -
        chi1 h D (t + -1) * ∏ ν' ∈ univ.erase ν, chi1Z h D (x ν' - c ν') =
        -(chi1 h D (t + 1) - 2 * chi1 h D t + chi1 h D (t - 1)) * ∏ ν' ∈ univ.erase ν, chi1Z h D (x ν' - c ν') := by
      rw [show t + -1 = t - 1 by ring]; ring
    rw [e, abs_mul, abs_neg, abs_of_nonneg hp0]
    calc |chi1 h D (t + 1) - 2 * chi1 h D t + chi1 h D (t - 1)| * ∏ ν' ∈ univ.erase ν, chi1Z h D (x ν' - c ν')
        ≤ (32 / (3 * ((h : ℝ) + 1) ^ 2)) * 1 := mul_le_mul (chi1_second h D t) hp1 hp0 (by positivity)
      _ = _ := mul_one _
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ ν, |2 * chiC h D c x - chiC h D c (x + unit n ν) - chiC h D c (x - unit n ν)| ≤
        ∑ _ν : Fin 4, 32 / (3 * ((h : ℝ) + 1) ^ 2) := sum_le_sum fun ν _ => hpt ν
    _ = 128 / (3 * ((h : ℝ) + 1) ^ 2) := by simp; ring

/-! ### The local bound at a cube -/

open Lattices SeqDom SmallFieldBlocks SFLocal SmallFieldDecay SmallFieldCoercivity
  SequenceOperators CompressedInverse ConcretePairing SFBox SFBox.SeqDomBox

/-- The arithmetic of the local bound. -/
lemma local_alg {N p q r w curl Qs G C η : ℝ} (hN : 0 < N) (hp : Real.sqrt p ≤ Real.sqrt q + Real.sqrt r)
    (hq0 : 0 ≤ q) (hr0 : 0 ≤ r) (hr : r ≤ η * w) (hq : q ≤ C * (curl + N⁻¹ * Qs)) (hG : G = N * curl + N * w)
    (hw : N * w ≤ 4 * G) (hpw : p ≤ w) (hp0 : 0 ≤ p) (hC : 0 ≤ C) (hη0 : 0 ≤ η) (hη : η ≤ 1 / 16) (hcurl : 0 ≤ curl)
    (hQs : 0 ≤ Qs) :
    G + Qs ≤ 2 * (1 + 2 * C) * (G + Qs - N * p) := by
  -- `p ≤ 2q + 2r`
  have h1 : p ≤ 2 * q + 2 * r := by
    have h := pow_le_pow_left₀ (Real.sqrt_nonneg _) hp 2
    rw [Real.sq_sqrt hp0] at h
    have : (Real.sqrt q + Real.sqrt r) ^ 2 ≤ 2 * q + 2 * r := by
      nlinarith [sq_nonneg (Real.sqrt q - Real.sqrt r), Real.sq_sqrt hq0, Real.sq_sqrt hr0]
    linarith
  -- `Np ≤ 2C(N curl + Qs) + 2ηNw`
  have h2 : N * p ≤ 2 * C * (N * curl + Qs) + 2 * η * (N * w) := by
    have e : N * (C * (curl + N⁻¹ * Qs)) = C * (N * curl + Qs) := by field_simp
    have := mul_le_mul_of_nonneg_left hq hN.le
    have := mul_le_mul_of_nonneg_left hr hN.le
    nlinarith
  -- `N curl + Qs ≤ G + Qs - Np`
  have h3 : N * curl + Qs ≤ G + Qs - N * p := by
    have := mul_le_mul_of_nonneg_left hpw hN.le
    rw [hG]; linarith
  have hw0 : 0 ≤ N * w := by have := mul_le_mul_of_nonneg_left hpw hN.le; nlinarith
  have h4 : 2 * η * (N * w) ≤ 8 * η * G := by nlinarith
  have hG0 : 0 ≤ G := by rw [hG]; nlinarith
  nlinarith [mul_le_mul_of_nonneg_left h3 (show (0 : ℝ) ≤ 2 * C by positivity)]

variable {S : Lattices.SeqDom} {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "NF" => SequenceAverages.N0 S
set_option quotPrecheck false in
local notation "jj" => (S.toDomSeq).sc

/-- **The local bound** (the core's step "The local bound"): for a `1`-form `X` on the torus with the comparison
sequence `S'` of the layers `i`, `i + 1`, a cut-off `χ` supported in a union `V` of blocks common to `S` and `S'`, the
bound `‖Δ(λ - λ̃)‖² ≤ η‖∂^*X‖²` on the shell with `η ≤ 1/16`, and `⟨X^*, Q_{S'}^*Q_{S'}X⟩ ≤ ⟨X^*, Q^*QX⟩`,
`⟨X^*, Δ^F_𝖺X⟩ ≤ 2(1 + 2C_tl)⟨X^*, Δ_𝖺(id)X⟩`. -/
theorem local_bound [NeZero N] {i : ℕ} (hi : i + 1 ≤ S.k) (Λ : Set (Tor (ellT S.L S.mT))) (hΛ : IsCubes S (i + 1) Λ)
    (X : Fin 4 → Site NF → Mat) (χ : Site NF → ℝ) (V : Set (Site NF))
    (hV : ∀ x ∈ V, jj x = ((twoLayer S i hi Λ hΛ).toDomSeq).sc x ∧
      ∀ x' ∈ Blk S.toDomSeq (jj x) (bc S.toDomSeq x), x' ∈ V)
    (hχV : ∀ x, x ∉ V → χ x = 0) {η : ℝ} (hη0 : 0 ≤ η) (hη : η ≤ 1 / 16)
    (hcut : ∑ x, hs2 (Ds1L a1 (cfgX (X0 S)) (D0L a1 (cfgX (X0 S))
        (minim (twoLayer S i hi Λ hΛ) (Ds1L a1 (cfgX (X0 S)) X) - corr (twoLayer S i hi Λ hΛ)
          (fun x => (χ x : ℂ) • minim (twoLayer S i hi Λ hΛ) (Ds1L a1 (cfgX (X0 S)) X) x))) x) ≤
      η * ∑ x, hs2 (Ds1L a1 (cfgX (X0 S)) X x))
    (hQ : Qnorm (twoLayer S i hi Λ hΛ) X ≤ Qnorm S X) :
    formF S X ≤ 2 * (1 + 2 * (SFOneLayer.Col * (1 + 2 ^ 17 * (S.L : ℝ) ^ 10))) * formA S X := by
  set f := Ds1L a1 (cfgX (X0 S)) X
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hstep := cutoff_step hi Λ hΛ f χ V hV hχV
  have htwo := sf_two_layers (twoLayer S i hi Λ hΛ) (j := i) hi (fun n hn => twoLayer_low hn)
    (fun n hn => twoLayer_high hn) X
  have hC : 0 ≤ SFOneLayer.Col * (1 + 2 ^ 17 * (S.L : ℝ) ^ 10) := by unfold SFOneLayer.Col; positivity
  have hq : ∑ x, hs2 (Pop (twoLayer S i hi Λ hΛ) (X0 (twoLayer S i hi Λ hΛ)) (W1 (twoLayer S i hi Λ hΛ))
      Set.univ f x) ≤ SFOneLayer.Col * (1 + 2 ^ 17 * (S.L : ℝ) ^ 10) * (curlE S X + (N : ℝ)⁻¹ * Qnorm S X) := by
    refine htwo.trans (mul_le_mul_of_nonneg_left ?_ hC)
    have := mul_le_mul_of_nonneg_left hQ (inv_nonneg.2 hN.le)
    exact add_le_add le_rfl this
  have hcurl : 0 ≤ curlE S X := by
    unfold curlE; exact sum_nonneg fun x _ => by
      have : 0 ≤ ∑ μ, ∑ ν, hs2 ((X ν (x + unit NF μ) - X ν x) - (X μ (x + unit NF ν) - X μ x)) :=
        sum_nonneg fun _ _ => sum_nonneg fun _ _ => hs2_nonneg _
      positivity
  have hQs : 0 ≤ Qnorm S X := by unfold Qnorm; exact sum_nonneg fun _ _ => by positivity
  unfold formA formF
  exact local_alg hN hstep (sum_nonneg fun x _ => hs2_nonneg _) (sum_nonneg fun x _ => hs2_nonneg _) hcut hq
    (grad_identity S X) (ds_le_grad S X) (Pop_contr S Set.univ f) (sum_nonneg fun x _ => hs2_nonneg _) hC hη0 hη
    hcurl hQs

end SFBounds
end CoreLean

end
