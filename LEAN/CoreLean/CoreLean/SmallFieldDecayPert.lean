/-
`lem:sf-decay` of BALABAN_CORE.tex (`542c68192a44`), the step "The complex field" and `eq:sf-conjugated`, in the model
`Blocks.DomSeq` (`η = 1`, `a_j = Lʲ`).

The differences of the forms of `𝐔` and of `id` at `(μ, ν) = (e^φλ^*, e^{-φ}λ)` (`SmallFieldDecay.Phi`):
* at a bond `b = (x, x')`, `(D_𝐔f)(b) = (∂f)(b) + E_bf(x')` with `E_b = Ad_{𝐔(b)} - 1`, `|E_bZ| ≤ ε a_{j(x')}^{-1}L|Z|`
  (the core's `|E_bZ| ≤ 8a₀‖A'(b)‖|Z|` with `‖A'(b)‖ ≤ α₁a_{j₋}^{-1}`, `a_{j₋}^{-1} ≤ La_{j(x')}^{-1}`), so that the
  term of `b` differs by at most `(4ε + ε²)ω_b(|∂λ(b)| + ω_b)`, `ω_b = La_{j(x')}^{-1}|λ(x')|` (`bond_pert_bound`), and
  the Laplacians by at most `(4ε + ε²)6L²N(λ)²` (`lap_pert`);
* at a block, `|Q'(𝐔)f - Q'(id)f| ≤ η f̄`, `|Q'(𝐔)f| ≤ 2√N f̄`, `|Q'(id)f| ≤ f̄` (the bounds of the transports of
  `lem:block-average-transports`), so that the constraint forms differ by at most `6√N η‖λ‖_w²` (`cons_pert`).
* `sf_conjugated`: `Re Φ_𝐔(e^φλ^*, e^{-φ}λ) ≥ ⅛N(λ)²` when `(4ε + ε²)6L² + 6√Nη ≤ ⅛`.

The constant `6L²` of the Laplacians replaces the core's `5L²`; under the core's choice `α₁ ≤ a_W` the condition holds
(`ε = 8α₁`, `η = 2√NL⁴C₁C'₃α₁`), which is recorded where the constants are fixed.
-/
import CoreLean.SmallFieldDecay
import CoreLean.RegularAverages
import CoreLean.Hessian

open Finset
open scoped Classical RealInnerProductSpace Matrix.Norms.L2Operator
open Matrix

noncomputable section

namespace CoreLean
namespace SmallFieldDecay

open Blocks SmallFieldBlocks DiscretePoincare SmallFieldCoercivity SequenceOperators

variable {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "GLN" => (Matrix (Fin N) (Fin N) ℂ)ˣ

lemma hs_rsmul (r : ℝ) (X : Mat) : hs (((r : ℝ) : ℂ) • X) = |r| * hs X := by
  rw [RegularAverages.hs_smul, Complex.norm_real, Real.norm_eq_abs]

/-- `‖tr((a + b)(c + d)) - tr(ac)‖ ≤ |a||d| + |b||c| + |b||d|`. -/
lemma bond_pert (a b c d : Mat) :
    ‖ntr ((a + b) * (c + d)) - ntr (a * c)‖ ≤ hs a * hs d + hs b * hs c + hs b * hs d := by
  have e : ntr ((a + b) * (c + d)) - ntr (a * c) = ntr (a * d) + ntr (b * c) + ntr (b * d) := by
    rw [add_mul, mul_add, mul_add, ntr_add', ntr_add', ntr_add']; ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  refine add_le_add ((norm_add_le _ _).trans (add_le_add (norm_ntr_mul_le _ _) (norm_ntr_mul_le _ _)))
    (norm_ntr_mul_le _ _)

/-- `e^{|s|} ≤ 2` and `|e^s - 1| ≤ 2|s|` for `|s| ≤ 1/128`. -/
lemma exp_small {s : ℝ} (hs : |s| ≤ 1 / 128) : Real.exp |s| ≤ 2 ∧ |Real.exp s - 1| ≤ 2 * |s| := by
  have hs1 : |s| ≤ 1 := by linarith
  have h := Real.abs_exp_sub_one_sub_id_le hs1
  have hsq : s ^ 2 ≤ |s| := by
    rw [← sq_abs]; nlinarith [abs_nonneg s]
  refine ⟨?_, ?_⟩
  · have h' := Real.abs_exp_sub_one_sub_id_le (x := |s|) (by rw [abs_abs]; exact hs1)
    rw [sq_abs] at h'
    have := (abs_le.1 h').2
    nlinarith [abs_nonneg s]
  · calc |Real.exp s - 1| = |(Real.exp s - 1 - s) + s| := by ring_nf
      _ ≤ |Real.exp s - 1 - s| + |s| := abs_add_le _ _
      _ ≤ s ^ 2 + |s| := add_le_add h le_rfl
      _ ≤ 2 * |s| := by linarith

variable {n : ℕ} [NeZero n] (S : DomSeq n)

/-- `ω_b = La_{j(x+e_μ)}^{-1}|λ(x + e_μ)|`. -/
def omg (lam : Site n → Mat) (x : Site n) (μ : Fin 4) : ℝ :=
  S.L * ((S.L : ℝ) ^ S.sc (x + unit n μ))⁻¹ * hs (lam (x + unit n μ))

/-- **The term of a bond**: `|tr(D_𝐔μ D_𝐔ν) - tr(∂μ ∂ν)| ≤ (4ε + ε²)ω_b(|∂λ(b)| + ω_b)`. -/
theorem bond_pert_bound [NeZero N] (U : Config N n) (ph : Site n → ℝ) (lam : Site n → Mat) (δ eps : ℝ)
    (hδ0 : 0 ≤ δ) (hδL : δ * S.L ≤ 1 / 128) (heps : 0 ≤ eps) (x : Site n) (μ : Fin 4)
    (hs2 : |ph (x + unit n μ) - ph x| ≤ δ * S.L * ((S.L : ℝ) ^ S.sc (x + unit n μ))⁻¹)
    (hE : ∀ Z : Mat, hs (Ad (U μ x) Z - Z) ≤ eps * S.L * ((S.L : ℝ) ^ S.sc (x + unit n μ))⁻¹ * hs Z) :
    ‖ntr (DU U (conjL ph lam) μ x * DU U (conjR ph lam) μ x) -
        ntr (DU (fun _ _ => 1) (conjL ph lam) μ x * DU (fun _ _ => 1) (conjR ph lam) μ x)‖ ≤
      (4 * eps + eps ^ 2) * (omg S lam x μ * (hs (lam (x + unit n μ) - lam x) + omg S lam x μ)) := by
  obtain ⟨x', hx'⟩ : ∃ x', x' = x + unit n μ := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w : ℝ, w = S.L * ((S.L : ℝ) ^ S.sc x')⁻¹ := ⟨_, rfl⟩
  obtain ⟨s, hsd⟩ : ∃ s : ℝ, s = ph x' - ph x := ⟨_, rfl⟩
  rw [← hx'] at hs2 hE ⊢
  have hL1 : (1 : ℝ) ≤ S.L := by exact_mod_cast (by have := S.three_le_L; omega : 1 ≤ S.L)
  have hw0 : 0 ≤ w := by rw [hw]; positivity
  have hwle : w ≤ S.L := by
    have : ((S.L : ℝ) ^ S.sc x')⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hL1)
    rw [hw]; nlinarith
  have hsb : |s| ≤ δ * w := by rw [hsd, hw, ← mul_assoc]; exact hs2
  have hs128 : |s| ≤ 1 / 128 := by
    have : δ * w ≤ δ * S.L := mul_le_mul_of_nonneg_left hwle hδ0
    linarith
  obtain ⟨hexp2, hexps⟩ := exp_small hs128
  have hexpns := (exp_small (s := -s) (by rwa [abs_neg])).2
  rw [abs_neg] at hexpns
  obtain ⟨D, hD⟩ : ∃ D, D = hs (lam x' - lam x) := ⟨_, rfl⟩
  have hom : omg S lam x μ = w * hs (lam x') := by rw [omg, hw, ← hx']
  rw [← hD, hom]
  set om := w * hs (lam x')
  have hom0 : 0 ≤ om := mul_nonneg hw0 (hs_nonneg _)
  have hD0 : 0 ≤ D := by rw [hD]; exact hs_nonneg _
  -- the decompositions
  set a := conjL ph lam x' - conjL ph lam x
  set b := Ad (U μ x) (conjL ph lam x') - conjL ph lam x'
  set c := conjR ph lam x' - conjR ph lam x
  set d := Ad (U μ x) (conjR ph lam x') - conjR ph lam x'
  have e1 : DU U (conjL ph lam) μ x = a + b := by simp only [DU, a, b, ← hx']; abel
  have e2 : DU U (conjR ph lam) μ x = c + d := by simp only [DU, c, d, ← hx']; abel
  have e3 : DU (fun _ _ => 1) (conjL ph lam) μ x = a := by simp only [DU, Ad_one, a, ← hx']
  have e4 : DU (fun _ _ => 1) (conjR ph lam) μ x = c := by simp only [DU, Ad_one, c, ← hx']
  rw [e1, e2, e3, e4]
  refine (bond_pert a b c d).trans ?_
  have hep := Real.exp_pos (ph x)
  have hen := Real.exp_pos (-ph x)
  have hsx : ph x + s = ph x' := by rw [hsd]; ring
  -- the bounds of the four pieces
  have ha : hs a ≤ Real.exp (ph x) * (D + om) := by
    have ea : a = ((Real.exp (ph x) : ℝ) : ℂ) • (lam x' - lam x)ᴴ +
        (((Real.exp (ph x') - Real.exp (ph x) : ℝ) : ℂ) • (lam x')ᴴ) := by
      simp only [a, conjL, conjTranspose_sub, smul_sub, Complex.ofReal_sub, sub_smul]; abel
    rw [ea]
    refine (hs_add_le _ _).trans ?_
    rw [hs_rsmul, hs_rsmul, hs_conjTranspose, hs_conjTranspose, abs_of_pos hep, ← hD]
    have hd : |Real.exp (ph x') - Real.exp (ph x)| ≤ Real.exp (ph x) * w := by
      have e : Real.exp (ph x') - Real.exp (ph x) = Real.exp (ph x) * (Real.exp s - 1) := by
        rw [mul_sub, mul_one, ← Real.exp_add, hsx]
      rw [e, abs_mul, abs_of_pos hep]
      refine mul_le_mul_of_nonneg_left (hexps.trans ?_) hep.le
      nlinarith
    have := mul_le_mul_of_nonneg_right hd (hs_nonneg (lam x'))
    simp only [om]; nlinarith
  have hc : hs c ≤ Real.exp (-ph x) * (D + om) := by
    have ec : c = ((Real.exp (-ph x) : ℝ) : ℂ) • (lam x' - lam x) +
        (((Real.exp (-ph x') - Real.exp (-ph x) : ℝ) : ℂ) • lam x') := by
      simp only [c, conjR, smul_sub, Complex.ofReal_sub, sub_smul]; abel
    rw [ec]
    refine (hs_add_le _ _).trans ?_
    rw [hs_rsmul, hs_rsmul, abs_of_pos hen, ← hD]
    have hd : |Real.exp (-ph x') - Real.exp (-ph x)| ≤ Real.exp (-ph x) * w := by
      have e : Real.exp (-ph x') - Real.exp (-ph x) = Real.exp (-ph x) * (Real.exp (-s) - 1) := by
        rw [mul_sub, mul_one, ← Real.exp_add, show -ph x + -s = -ph x' by rw [← hsx]; ring]
      rw [e, abs_mul, abs_of_pos hen]
      refine mul_le_mul_of_nonneg_left (hexpns.trans ?_) hen.le
      nlinarith
    have := mul_le_mul_of_nonneg_right hd (hs_nonneg (lam x'))
    simp only [om]; nlinarith
  have hμ : hs (conjL ph lam x') = Real.exp (ph x') * hs (lam x') := by
    simp only [conjL, hs_rsmul, hs_conjTranspose, abs_of_pos (Real.exp_pos _)]
  have hν : hs (conjR ph lam x') = Real.exp (-ph x') * hs (lam x') := by
    simp only [conjR, hs_rsmul, abs_of_pos (Real.exp_pos _)]
  have hb : hs b ≤ eps * Real.exp (ph x') * om := by
    calc hs b ≤ eps * S.L * ((S.L : ℝ) ^ S.sc x')⁻¹ * hs (conjL ph lam x') := hE _
      _ = eps * Real.exp (ph x') * om := by rw [hμ]; simp only [om, hw]; ring
  have hd : hs d ≤ eps * Real.exp (-ph x') * om := by
    calc hs d ≤ eps * S.L * ((S.L : ℝ) ^ S.sc x')⁻¹ * hs (conjR ph lam x') := hE _
      _ = eps * Real.exp (-ph x') * om := by rw [hν]; simp only [om, hw]; ring
  -- the products
  have hr1 : Real.exp (ph x) * Real.exp (-ph x') ≤ 2 := by
    rw [← Real.exp_add]
    refine (Real.exp_le_exp.2 ?_).trans hexp2
    have : ph x + -ph x' = -s := by rw [← hsx]; ring
    rw [this]; exact neg_le_abs s
  have hr2 : Real.exp (ph x') * Real.exp (-ph x) ≤ 2 := by
    rw [← Real.exp_add]
    refine (Real.exp_le_exp.2 ?_).trans hexp2
    have : ph x' + -ph x = s := by rw [← hsx]; ring
    rw [this]; exact le_abs_self s
  have hr3 : Real.exp (ph x') * Real.exp (-ph x') = 1 := by rw [← Real.exp_add]; simp
  have p1 : hs a * hs d ≤ 2 * eps * (om * (D + om)) := by
    calc hs a * hs d ≤ (Real.exp (ph x) * (D + om)) * (eps * Real.exp (-ph x') * om) :=
          mul_le_mul ha hd (hs_nonneg _) (by positivity)
      _ = (Real.exp (ph x) * Real.exp (-ph x')) * eps * (om * (D + om)) := by ring
      _ ≤ 2 * eps * (om * (D + om)) := by
          have : 0 ≤ eps * (om * (D + om)) := by positivity
          nlinarith
  have p2 : hs b * hs c ≤ 2 * eps * (om * (D + om)) := by
    calc hs b * hs c ≤ (eps * Real.exp (ph x') * om) * (Real.exp (-ph x) * (D + om)) :=
          mul_le_mul hb hc (hs_nonneg _) (by positivity)
      _ = (Real.exp (ph x') * Real.exp (-ph x)) * eps * (om * (D + om)) := by ring
      _ ≤ 2 * eps * (om * (D + om)) := by
          have : 0 ≤ eps * (om * (D + om)) := by positivity
          nlinarith
  have p3 : hs b * hs d ≤ eps ^ 2 * (om * (D + om)) := by
    calc hs b * hs d ≤ (eps * Real.exp (ph x') * om) * (eps * Real.exp (-ph x') * om) :=
          mul_le_mul hb hd (hs_nonneg _) (by positivity)
      _ = (Real.exp (ph x') * Real.exp (-ph x')) * eps ^ 2 * (om * om) := by ring
      _ ≤ eps ^ 2 * (om * (D + om)) := by
          rw [hr3, one_mul]
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (by linarith) hom0) (sq_nonneg _)
  linarith

/-- **The Laplacians**: `|Σ_b (tr(D_𝐔μ D_𝐔ν) - tr(∂μ ∂ν))| ≤ (4ε + ε²)6L²N(λ)²`. -/
theorem lap_pert [NeZero N] (U : Config N n) (ph : Site n → ℝ) (lam : Site n → Mat) (δ eps : ℝ)
    (hδ0 : 0 ≤ δ) (hδL : δ * S.L ≤ 1 / 128) (heps : 0 ≤ eps)
    (hph : ∀ x μ, |ph (x + unit n μ) - ph x| ≤ δ * S.L * ((S.L : ℝ) ^ S.sc (x + unit n μ))⁻¹)
    (hE : ∀ x μ, ∀ Z : Mat, hs (Ad (U μ x) Z - Z) ≤ eps * S.L * ((S.L : ℝ) ^ S.sc (x + unit n μ))⁻¹ * hs Z) :
    ‖∑ x, ∑ μ : Fin 4, (ntr (DU U (conjL ph lam) μ x * DU U (conjR ph lam) μ x) -
        ntr (DU (fun _ _ => 1) (conjL ph lam) μ x * DU (fun _ _ => 1) (conjR ph lam) μ x))‖ ≤
      (4 * eps + eps ^ 2) * (6 * (S.L : ℝ) ^ 2) * (dsqM lam + wnormM S lam) := by
  have hL1 : (1 : ℝ) ≤ S.L := by exact_mod_cast (by have := S.three_le_L; omega : 1 ≤ S.L)
  have hLpos : (0 : ℝ) < S.L := by linarith
  refine (norm_sum_le _ _).trans ?_
  refine (sum_le_sum fun x _ => norm_sum_le _ _).trans ?_
  refine (sum_le_sum fun x _ => sum_le_sum fun μ _ =>
    bond_pert_bound S U ph lam δ eps hδ0 hδL heps x μ (hph x μ) (hE x μ)).trans ?_
  simp only [← mul_sum]
  have hK : 0 ≤ 4 * eps + eps ^ 2 := by positivity
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hK
  -- `Σ ω² = 4L²‖λ‖_w²`
  have hom2 : ∑ x, ∑ μ : Fin 4, omg S lam x μ ^ 2 = 4 * (S.L : ℝ) ^ 2 * wnormM S lam := by
    have e : ∀ x μ, omg S lam x μ ^ 2 =
        (S.L : ℝ) ^ 2 * ((((S.L : ℝ) ^ (2 * S.sc (x + unit n μ)))⁻¹) * hs2 (lam (x + unit n μ))) := by
      intro x μ
      simp only [omg, mul_pow, inv_pow, ← hs_sq, pow_mul]; ring
    simp only [e, ← mul_sum]
    rw [Finset.sum_comm]
    simp only [fun μ => sum_shift (n := n) μ (fun x => ((S.L : ℝ) ^ (2 * S.sc x))⁻¹ * hs2 (lam x)), sum_const,
      card_univ, Fintype.card_fin, nsmul_eq_mul, wnormM]
    ring
  -- `ωD ≤ ω²/(2L) + LD²/2`
  have hamgm : ∀ x μ, omg S lam x μ * (hs (lam (x + unit n μ) - lam x) + omg S lam x μ) ≤
      (1 / (2 * S.L) + 1) * omg S lam x μ ^ 2 + S.L / 2 * hs2 (lam (x + unit n μ) - lam x) := by
    intro x μ
    have h := sq_nonneg (omg S lam x μ - S.L * hs (lam (x + unit n μ) - lam x))
    rw [← hs_sq]
    have h2L : (0 : ℝ) < 2 * S.L := by positivity
    have key : omg S lam x μ * hs (lam (x + unit n μ) - lam x) =
        1 / (2 * S.L) * omg S lam x μ ^ 2 + S.L / 2 * hs (lam (x + unit n μ) - lam x) ^ 2 -
          (omg S lam x μ - S.L * hs (lam (x + unit n μ) - lam x)) ^ 2 / (2 * S.L) := by
      field_simp; ring
    have hnn : 0 ≤ (omg S lam x μ - S.L * hs (lam (x + unit n μ) - lam x)) ^ 2 / (2 * S.L) := by positivity
    nlinarith
  calc ∑ x, ∑ μ : Fin 4, omg S lam x μ * (hs (lam (x + unit n μ) - lam x) + omg S lam x μ)
      ≤ ∑ x, ∑ μ : Fin 4, ((1 / (2 * S.L) + 1) * omg S lam x μ ^ 2 +
          S.L / 2 * hs2 (lam (x + unit n μ) - lam x)) := sum_le_sum fun x _ => sum_le_sum fun μ _ => hamgm x μ
    _ = (1 / (2 * S.L) + 1) * (4 * (S.L : ℝ) ^ 2 * wnormM S lam) + S.L / 2 * dsqM lam := by
        simp only [sum_add_distrib, ← mul_sum, hom2, dsqM]
    _ ≤ 6 * (S.L : ℝ) ^ 2 * (dsqM lam + wnormM S lam) := by
        have hW : 0 ≤ wnormM S lam := by
          unfold wnormM; exact sum_nonneg fun _ _ => mul_nonneg (by positivity) (hs2_nonneg _)
        have hDs : 0 ≤ dsqM lam := by unfold dsqM; exact sum_nonneg fun _ _ => sum_nonneg fun _ _ => hs2_nonneg _
        have e : (1 / (2 * S.L) + 1) * (4 * (S.L : ℝ) ^ 2 * wnormM S lam) = (2 * S.L + 4 * S.L ^ 2) * wnormM S lam := by
          field_simp; ring
        rw [e]
        have h1 : (2 * (S.L : ℝ) + 4 * S.L ^ 2) * wnormM S lam ≤ 6 * S.L ^ 2 * wnormM S lam :=
          mul_le_mul_of_nonneg_right (by nlinarith) hW
        have h2 : (S.L : ℝ) / 2 * dsqM lam ≤ 6 * S.L ^ 2 * dsqM lam :=
          mul_le_mul_of_nonneg_right (by nlinarith) hDs
        linarith

/-- `‖λ‖_w²` through the blocks: `Σ_{y ∈ 𝐁}a_{j(y)}^{-2}Σ_{x ∈ Δ(y)}|λ(x)|²`. -/
lemma wnormM_blocks (lam : Site n → Mat) : wnormM S lam = ∑ y ∈ detB S, ((S.L : ℝ) ^ (2 * S.sc y))⁻¹ *
    ∑ o ∈ box 4 (S.L ^ S.sc y), hs2 (lam (phi S (S.sc y) y o)) := by
  rw [wnormM, sum_blocks S]
  refine sum_congr rfl fun y hy => ?_
  obtain ⟨x0, -, rfl⟩ := mem_image.1 hy
  rw [mul_sum, sum_Blk _ (S.sc_le _) (inLat_bc x0)]
  refine sum_congr rfl fun o ho => ?_
  rw [sc_of_mem_Blk S hy (phi_mem _ (S.sc_le _) (inLat_bc x0) ho)]

/-- **The constraint forms**: `|Σ_y 𝖺_ja_j²(tr(Q'_𝐔μ Q'_𝐔ν) - tr(Q'_{id}μ Q'_{id}ν))| ≤ 6√Nη‖λ‖_w²`. -/
theorem cons_pert [NeZero N] (W : Site n → Site n → GLN) (ph : Site n → ℝ) (lam : Site n → Mat) (δ η : ℝ)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 128) (hη : 0 ≤ η)
    (hblock : ∀ y ∈ detB S, ∀ x ∈ Blk S (S.sc y) y, |ph x - ph y| ≤ 2 * δ)
    (hW1 : ∀ y ∈ detB S, ∀ x ∈ Blk S (S.sc y) y, ∀ Z : Mat, hs (Ad (W y x) Z - Z) ≤ η * hs Z)
    (hW2 : ∀ y ∈ detB S, ∀ x ∈ Blk S (S.sc y) y, ∀ Z : Mat, hs (Ad (W y x) Z) ≤ 2 * Real.sqrt N * hs Z) :
    ‖∑ y ∈ detB S, ((aseq 1 S.L (S.sc y) * (S.L : ℝ) ^ (2 * S.sc y) : ℝ) : ℂ) *
        (ntr (avgW S W y (conjL ph lam) * avgW S W y (conjR ph lam)) -
          ntr (avgW S (fun _ _ => 1) y (conjL ph lam) * avgW S (fun _ _ => 1) y (conjR ph lam)))‖ ≤
      6 * Real.sqrt N * η * wnormM S lam := by
  have hN1 : (1 : ℝ) ≤ Real.sqrt N := by
    rw [Real.one_le_sqrt]; exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  rw [wnormM_blocks, mul_sum]
  refine (norm_sum_le _ _).trans (sum_le_sum fun y hy => ?_)
  obtain ⟨x0, -, rfl⟩ := mem_image.1 hy
  set j := S.sc (bc S x0)
  set T := box 4 (S.L ^ j)
  have hlat := inLat_bc (S := S) x0
  have hjk : j ≤ S.k := S.sc_le _
  have hT : 0 < T.card := by simp only [T]; rw [card_box]; have := S.three_le_L; positivity
  have hc : (0 : ℝ) < T.card := by exact_mod_cast hT
  have hmem : ∀ o ∈ T, phi S j (bc S x0) o ∈ Blk S j (bc S x0) := fun o ho => phi_mem _ hjk hlat ho
  -- the bounds of the averages
  set fbar : (Site n → Mat) → ℝ := fun f => (T.card : ℝ)⁻¹ * ∑ o ∈ T, hs (f (phi S j (bc S x0) o))
  have hsc : ∀ X : Mat, hs ((((T.card : ℝ) : ℂ))⁻¹ • X) = (T.card : ℝ)⁻¹ * hs X := fun X => by
    rw [← Complex.ofReal_inv, hs_rsmul, abs_of_pos (inv_pos.2 hc)]
  have hf0 : ∀ f, 0 ≤ fbar f := fun f =>
    mul_nonneg (by positivity) (sum_nonneg fun _ _ => hs_nonneg _)
  have B1 : ∀ f, hs (avgW S W (bc S x0) f - avgW S (fun _ _ => 1) (bc S x0) f) ≤ η * fbar f := by
    intro f
    have e : avgW S W (bc S x0) f - avgW S (fun _ _ => 1) (bc S x0) f = (((T.card : ℝ) : ℂ))⁻¹ •
        ∑ o ∈ T, (Ad (W (bc S x0) (phi S j (bc S x0) o)) (f (phi S j (bc S x0) o)) -
          f (phi S j (bc S x0) o)) := by
      simp only [avgW, Ad_one, ← smul_sub, ← sum_sub_distrib]; rfl
    rw [e, hsc]
    calc (T.card : ℝ)⁻¹ * hs (∑ o ∈ T, (Ad (W (bc S x0) (phi S j (bc S x0) o)) (f (phi S j (bc S x0) o)) -
          f (phi S j (bc S x0) o)))
        ≤ (T.card : ℝ)⁻¹ * ∑ o ∈ T, η * hs (f (phi S j (bc S x0) o)) := by
          refine mul_le_mul_of_nonneg_left ((RegularAverages.hs_sum_le _ _).trans
            (sum_le_sum fun o ho => hW1 _ hy _ (hmem o ho) _)) (by positivity)
      _ = η * fbar f := by simp only [fbar, ← mul_sum]; ring
  have B2 : ∀ f, hs (avgW S W (bc S x0) f) ≤ 2 * Real.sqrt N * fbar f := by
    intro f
    have e : avgW S W (bc S x0) f = (((T.card : ℝ) : ℂ))⁻¹ •
        ∑ o ∈ T, Ad (W (bc S x0) (phi S j (bc S x0) o)) (f (phi S j (bc S x0) o)) := rfl
    rw [e, hsc]
    calc (T.card : ℝ)⁻¹ * hs (∑ o ∈ T, Ad (W (bc S x0) (phi S j (bc S x0) o)) (f (phi S j (bc S x0) o)))
        ≤ (T.card : ℝ)⁻¹ * ∑ o ∈ T, 2 * Real.sqrt N * hs (f (phi S j (bc S x0) o)) := by
          refine mul_le_mul_of_nonneg_left ((RegularAverages.hs_sum_le _ _).trans
            (sum_le_sum fun o ho => hW2 _ hy _ (hmem o ho) _)) (by positivity)
      _ = 2 * Real.sqrt N * fbar f := by simp only [fbar, ← mul_sum]; ring
  have B3 : ∀ f, hs (avgW S (fun _ _ => 1) (bc S x0) f) ≤ fbar f := by
    intro f
    have e : avgW S (fun _ _ => 1) (bc S x0) f = (((T.card : ℝ) : ℂ))⁻¹ •
        ∑ o ∈ T, f (phi S j (bc S x0) o) := by
      simp only [avgW, Ad_one]; rfl
    rw [e, hsc]
    exact mul_le_mul_of_nonneg_left (RegularAverages.hs_sum_le _ _) (by positivity)
  -- the means of `μ` and `ν`
  set lb := (T.card : ℝ)⁻¹ * ∑ o ∈ T, hs (lam (phi S j (bc S x0) o))
  have hμ : fbar (conjL ph lam) ≤ Real.exp (ph (bc S x0) + 2 * δ) * lb := by
    simp only [fbar, lb, mul_sum]
    refine sum_le_sum fun o ho => ?_
    simp only [conjL, hs_rsmul, hs_conjTranspose, abs_of_pos (Real.exp_pos _)]
    have := (abs_le.1 (hblock _ hy _ (hmem o ho))).2
    have he : Real.exp (ph (phi S j (bc S x0) o)) ≤ Real.exp (ph (bc S x0) + 2 * δ) :=
      Real.exp_le_exp.2 (by linarith)
    have := mul_le_mul_of_nonneg_right he (hs_nonneg (lam (phi S j (bc S x0) o)))
    nlinarith [inv_pos.2 hc]
  have hν : fbar (conjR ph lam) ≤ Real.exp (-ph (bc S x0) + 2 * δ) * lb := by
    simp only [fbar, lb, mul_sum]
    refine sum_le_sum fun o ho => ?_
    simp only [conjR, hs_rsmul, abs_of_pos (Real.exp_pos _)]
    have := (abs_le.1 (hblock _ hy _ (hmem o ho))).1
    have he : Real.exp (-ph (phi S j (bc S x0) o)) ≤ Real.exp (-ph (bc S x0) + 2 * δ) :=
      Real.exp_le_exp.2 (by linarith)
    have := mul_le_mul_of_nonneg_right he (hs_nonneg (lam (phi S j (bc S x0) o)))
    nlinarith [inv_pos.2 hc]
  have hlb2 : lb ^ 2 ≤ (T.card : ℝ)⁻¹ * ∑ o ∈ T, hs2 (lam (phi S j (bc S x0) o)) := by
    have h := sq_sum_le_card_mul_sum_sq (s := T) (f := fun o => hs (lam (phi S j (bc S x0) o)))
    simp only [hs_sq] at h
    simp only [lb, mul_pow]
    rw [inv_pow, sq (T.card : ℝ), mul_inv, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [inv_mul_le_iff₀ hc]; linarith
  have h4δ : Real.exp (4 * δ) ≤ 2 := by
    have h := Real.abs_exp_sub_one_sub_id_le (x := 4 * δ) (by rw [abs_of_nonneg (by linarith)]; linarith)
    have := (abs_le.1 h).2
    nlinarith
  have hprod : fbar (conjL ph lam) * fbar (conjR ph lam) ≤ 2 * lb ^ 2 := by
    have hlb0 : 0 ≤ lb := mul_nonneg (by positivity) (sum_nonneg fun _ _ => hs_nonneg _)
    calc fbar (conjL ph lam) * fbar (conjR ph lam)
        ≤ (Real.exp (ph (bc S x0) + 2 * δ) * lb) * (Real.exp (-ph (bc S x0) + 2 * δ) * lb) :=
          mul_le_mul hμ hν (hf0 _) (by positivity)
      _ = Real.exp (4 * δ) * lb ^ 2 := by
          rw [show Real.exp (ph (bc S x0) + 2 * δ) * lb * (Real.exp (-ph (bc S x0) + 2 * δ) * lb) =
            (Real.exp (ph (bc S x0) + 2 * δ) * Real.exp (-ph (bc S x0) + 2 * δ)) * lb ^ 2 by ring,
            ← Real.exp_add]
          congr 2; ring
      _ ≤ 2 * lb ^ 2 := mul_le_mul_of_nonneg_right h4δ (sq_nonneg _)
  -- the term of the block
  have ha := aseq_mem S.L (by have := S.three_le_L; omega) j
  have ha0 : 0 ≤ aseq 1 S.L j := (aseq_pos (aa := 1) one_pos S.L j).le
  have hP : (0 : ℝ) < (S.L : ℝ) ^ (2 * j) := pow_pos (by exact_mod_cast (show 0 < S.L by have := S.three_le_L; omega)) _
  set QWm := avgW S W (bc S x0) (conjL ph lam)
  set QWn := avgW S W (bc S x0) (conjR ph lam)
  set Q1m := avgW S (fun _ _ => 1) (bc S x0) (conjL ph lam)
  set Q1n := avgW S (fun _ _ => 1) (bc S x0) (conjR ph lam)
  have ediff : ntr (QWm * QWn) - ntr (Q1m * Q1n) = ntr ((QWm - Q1m) * QWn) + ntr (Q1m * (QWn - Q1n)) := by
    rw [sub_mul, mul_sub, ntr_sub, ntr_sub]; ring
  have hterm : ‖ntr (QWm * QWn) - ntr (Q1m * Q1n)‖ ≤ 3 * Real.sqrt N * η * (2 * lb ^ 2) := by
    rw [ediff]
    refine (norm_add_le _ _).trans ?_
    have t1 := (norm_ntr_mul_le (QWm - Q1m) QWn).trans
      (mul_le_mul (B1 _) (B2 _) (hs_nonneg _) (mul_nonneg hη (hf0 _)))
    have t2 := (norm_ntr_mul_le Q1m (QWn - Q1n)).trans
      (mul_le_mul (B3 _) (B1 _) (hs_nonneg _) (hf0 _))
    have hpos : 0 ≤ fbar (conjL ph lam) * fbar (conjR ph lam) := mul_nonneg (hf0 _) (hf0 _)
    calc _ ≤ η * fbar (conjL ph lam) * (2 * Real.sqrt N * fbar (conjR ph lam)) +
          fbar (conjL ph lam) * (η * fbar (conjR ph lam)) := add_le_add t1 t2
      _ = (2 * Real.sqrt N + 1) * η * (fbar (conjL ph lam) * fbar (conjR ph lam)) := by ring
      _ ≤ 3 * Real.sqrt N * η * (fbar (conjL ph lam) * fbar (conjR ph lam)) := by
          have : (2 * Real.sqrt N + 1) * η ≤ 3 * Real.sqrt N * η := mul_le_mul_of_nonneg_right (by linarith) hη
          exact mul_le_mul_of_nonneg_right this hpos
      _ ≤ 3 * Real.sqrt N * η * (2 * lb ^ 2) := mul_le_mul_of_nonneg_left hprod (by positivity)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hcard : (T.card : ℝ) = (S.L : ℝ) ^ (2 * j) * (S.L : ℝ) ^ (2 * j) := by
    simp only [T]; rw [card_box]; push_cast; rw [← pow_mul, ← pow_add]; ring_nf
  calc aseq 1 S.L j * (S.L : ℝ) ^ (2 * j) * ‖ntr (QWm * QWn) - ntr (Q1m * Q1n)‖
      ≤ 1 * (S.L : ℝ) ^ (2 * j) * (3 * Real.sqrt N * η * (2 * ((T.card : ℝ)⁻¹ *
          ∑ o ∈ T, hs2 (lam (phi S j (bc S x0) o))))) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_right ha.2 hP.le) (hterm.trans ?_) (norm_nonneg _) (by positivity)
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlb2 (by norm_num)) (by positivity)
    _ = 6 * Real.sqrt N * η * (((S.L : ℝ) ^ (2 * j))⁻¹ * ∑ o ∈ T, hs2 (lam (phi S j (bc S x0) o))) := by
        rw [hcard]; field_simp; ring

/-- **`eq:sf-conjugated`**: `Re Φ_𝐔(e^φλ^*, e^{-φ}λ) ≥ ⅛(‖∂λ‖₂² + ‖λ‖_w²)` when `(4ε + ε²)6L² + 6√Nη ≤ ⅛`. -/
theorem sf_conjugated [NeZero N] (U : Config N n) (W : Site n → Site n → GLN) (ph : Site n → ℝ)
    (lam : Site n → Mat) (δ eps η : ℝ) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / (128 * S.L)) (heps : 0 ≤ eps) (hη : 0 ≤ η)
    (hbond : ∀ x μ, |ph (x + unit n μ) - ph x| ≤ δ * S.L * ((S.L : ℝ) ^ S.sc x)⁻¹ ∧
      |ph (x + unit n μ) - ph x| ≤ δ * S.L * ((S.L : ℝ) ^ S.sc (x + unit n μ))⁻¹)
    (hblock : ∀ y ∈ detB S, ∀ x ∈ Blk S (S.sc y) y, |ph x - ph y| ≤ 2 * δ)
    (hE : ∀ x μ, ∀ Z : Mat, hs (Ad (U μ x) Z - Z) ≤ eps * S.L * ((S.L : ℝ) ^ S.sc (x + unit n μ))⁻¹ * hs Z)
    (hW1 : ∀ y ∈ detB S, ∀ x ∈ Blk S (S.sc y) y, ∀ Z : Mat, hs (Ad (W y x) Z - Z) ≤ η * hs Z)
    (hW2 : ∀ y ∈ detB S, ∀ x ∈ Blk S (S.sc y) y, ∀ Z : Mat, hs (Ad (W y x) Z) ≤ 2 * Real.sqrt N * hs Z)
    (hsmall : (4 * eps + eps ^ 2) * (6 * (S.L : ℝ) ^ 2) + 6 * Real.sqrt N * η ≤ 1 / 8) :
    (1 / 8) * (dsqM lam + wnormM S lam) ≤ (Phi S U W (conjL ph lam) (conjR ph lam)).re := by
  have hL3 : (3 : ℝ) ≤ S.L := by exact_mod_cast S.three_le_L
  have hLpos : (0 : ℝ) < S.L := by linarith
  have hδL : δ * S.L ≤ 1 / 128 := by
    calc δ * S.L ≤ 1 / (128 * S.L) * S.L := mul_le_mul_of_nonneg_right hδ hLpos.le
      _ = 1 / 128 := by field_simp
  have hδ128 : δ ≤ 1 / 128 := by nlinarith
  have htriv := sf_decay_trivial_mat S ph δ hδ0 hδ hbond hblock lam
  have hlap := lap_pert S U ph lam δ eps hδ0 hδL heps (fun x μ => (hbond x μ).2) hE
  have hcons := cons_pert S W ph lam δ η hδ0 hδ128 hη hblock hW1 hW2
  set Dl := ∑ x, ∑ μ : Fin 4, (ntr (DU U (conjL ph lam) μ x * DU U (conjR ph lam) μ x) -
          ntr (DU (fun _ _ => 1) (conjL ph lam) μ x * DU (fun _ _ => 1) (conjR ph lam) μ x))
  set Dc := ∑ y ∈ detB S, ((aseq 1 S.L (S.sc y) * (S.L : ℝ) ^ (2 * S.sc y) : ℝ) : ℂ) *
          (ntr (avgW S W y (conjL ph lam) * avgW S W y (conjR ph lam)) -
            ntr (avgW S (fun _ _ => 1) y (conjL ph lam) * avgW S (fun _ _ => 1) y (conjR ph lam)))
  have ediff : Phi S U W (conjL ph lam) (conjR ph lam) =
      Phi S (fun _ _ => 1) (fun _ _ => 1) (conjL ph lam) (conjR ph lam) + (Dl + Dc) := by
    simp only [Phi, Dl, Dc, mul_sub, sum_sub_distrib]; ring
  rw [ediff, Complex.add_re]
  have hre : -‖Dl + Dc‖ ≤ (Dl + Dc).re := neg_le_of_abs_le (Complex.abs_re_le_norm _)
  have hnorm : ‖Dl + Dc‖ ≤ (4 * eps + eps ^ 2) * (6 * (S.L : ℝ) ^ 2) * (dsqM lam + wnormM S lam) +
      6 * Real.sqrt N * η * wnormM S lam := (norm_add_le _ _).trans (add_le_add hlap hcons)
  have hW : 0 ≤ wnormM S lam := by
    unfold wnormM; exact sum_nonneg fun _ _ => mul_nonneg (by positivity) (hs2_nonneg _)
  have hDs : 0 ≤ dsqM lam := by unfold dsqM; exact sum_nonneg fun _ _ => sum_nonneg fun _ _ => hs2_nonneg _
  have hK : (4 * eps + eps ^ 2) * (6 * (S.L : ℝ) ^ 2) * (dsqM lam + wnormM S lam) +
      6 * Real.sqrt N * η * wnormM S lam ≤ 1 / 8 * (dsqM lam + wnormM S lam) := by
    have h6 : 0 ≤ 6 * Real.sqrt N * η := by positivity
    have h1 : 6 * Real.sqrt N * η * wnormM S lam ≤ 6 * Real.sqrt N * η * (dsqM lam + wnormM S lam) :=
      mul_le_mul_of_nonneg_left (by linarith) h6
    have h2 := mul_le_mul_of_nonneg_right hsmall (add_nonneg hDs hW)
    nlinarith
  linarith

end SmallFieldDecay
end CoreLean

end
