/-
`prop:sf-block` of BALABAN_CORE.tex (`d4ef86a9a5fd`): the entries of the scaled block operator at the complex field
differ from those at the trivial field by `O(α₁ + η)` (the core obtains this from the lemma of Schwarz), on the fine
lattice (`a₀ = 1`):

`|T̂_𝐔[y, y']Z - T̂_id[y, y']Z| ≤ C_T e^{-(δ/32)d(y, y')}|Z|`, `C_T = O(α₁ + η)`,

from `T̂ = a_{y'}⁻⁴Q'G'²Q'^*`, the difference of the averages, of their transposes, and
`G'_𝐔² - G'_id² = G'_𝐔(G'_𝐔 - G'_id) + (G'_𝐔 - G'_id)G'_id` with the composition of block kernel bounds.

* `r1_anti`: `r₁(½, ·)` is antitone.
* `avg_diff`, `lamZ_diff`: the averages and their transposes at `W` and at `id` differ by `η` and `2√Nη`.
* `That_diff`: the bound.
-/
import CoreLean.SFDiff

open Finset Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace CoreLean
namespace SFBounds

open Lattices SeqDom Blocks SmallFieldBlocks SFBox SFBox.SeqDomBox SmallFieldDecay SmallFieldCoercivity
  SequenceOperators CompressedInverse SFLocal

variable (S : SeqDom) {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "GLN" => (Matrix (Fin N) (Fin N) ℂ)ˣ
local notation "NF" => SequenceAverages.N0 S
local notation "RMS" => ((S.R * S.L ^ S.mM : ℕ) : ℝ)
set_option quotPrecheck false in
local notation "jj" => (S.toDomSeq).sc

lemma r1_anti {m m' : ℝ} (hm : 0 < m) (hmm : m ≤ m') :
    (S.toContSeq).r1 (1 / 2) m' ≤ (S.toContSeq).r1 (1 / 2) m := by
  unfold Summation.ContSeq.r1
  refine max_le_max le_rfl ?_
  have hL : (1 : ℝ) ≤ (S.toContSeq).L := by exact_mod_cast (show 1 ≤ S.L by have := S.three_le_L; omega)
  have hlog := Real.log_nonneg hL
  exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)

/-- **The averages at `W` and at `id` differ by `η`.** -/
lemma avg_diff [NeZero N] {W : Site NF → Site NF → GLN} {η : ℝ} (hη : 0 ≤ η)
    (hW1 : ∀ y ∈ detB S.toDomSeq, ∀ x ∈ Blk S.toDomSeq ((S.toDomSeq).sc y) y, ∀ Z : Mat,
      hs (Ad (W y x) Z - Z) ≤ η * hs Z) {y : Site NF} (hy : y ∈ detB S.toDomSeq) {v : Site NF → Mat} {M : ℝ}
    (hv : ∀ x ∈ Blk S.toDomSeq (jj y) y, hs (v x) ≤ M) :
    hs (avgW S.toDomSeq W y v - avgW S.toDomSeq (W1 S) y v) ≤ η * M := by
  have hL : (0 : ℝ) < S.L := by exact_mod_cast S.Lpos
  rw [avgW_blk S.toDomSeq _ hy, avgW_blk S.toDomSeq _ hy, ← smul_sub, ← sum_sub_distrib, RegularAverages.hs_smul]
  simp only [toDomSeq_L, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (pow_pos hL _)]
  have hs1 : hs (∑ x ∈ Blk S.toDomSeq (jj y) y, (Ad (W y x) (v x) - Ad (W1 S y x) (v x))) ≤
      ∑ _x ∈ Blk S.toDomSeq (jj y) y, η * M := by
    refine (RegularAverages.hs_sum_le _ _).trans (sum_le_sum fun x hx => ?_)
    rw [show Ad (W1 S y x) (v x) = v x by simp [Ad]]
    exact (hW1 y hy x hx (v x)).trans (mul_le_mul_of_nonneg_left (hv x hx) hη)
  rw [sum_const, nsmul_eq_mul, card_Blk S hy] at hs1
  calc ((S.L : ℝ) ^ (4 * jj y))⁻¹ * hs (∑ x ∈ Blk S.toDomSeq (jj y) y, (Ad (W y x) (v x) - Ad (W1 S y x) (v x)))
      ≤ ((S.L : ℝ) ^ (4 * jj y))⁻¹ * ((S.L : ℝ) ^ (4 * jj y) * (η * M)) := by gcongr
    _ = η * M := by field_simp

/-- **The transposes at `W` and at `id` differ by `2√Nη`.** -/
lemma lamZ_diff [NeZero N] {W : Site NF → Site NF → GLN} {η : ℝ} (hη : 0 ≤ η)
    (hW1 : ∀ y ∈ detB S.toDomSeq, ∀ x ∈ Blk S.toDomSeq ((S.toDomSeq).sc y) y, ∀ Z : Mat,
      hs (Ad (W y x) Z - Z) ≤ η * hs Z) (hW : WBound S W) {y' : Site NF} (hy' : y' ∈ detB S.toDomSeq)
    (Z : Mat) (x' : Site NF) : hs (lamZ S W y' Z x' - lamZ S (W1 S) y' Z x') ≤ 2 * Real.sqrt N * η * hs Z := by
  by_cases h : bc S.toDomSeq x' = y'
  · have hx : x' ∈ Blk S.toDomSeq (jj y') y' := by rw [← h]; exact mem_blk_bc S x'
    simp only [lamZ, QpStar, h, if_true]
    rw [show Ad (W1 S y' x')⁻¹ Z = Z by simp [Ad],
      show Ad (W y' x')⁻¹ Z - Z = Ad (W y' x')⁻¹ (Z - Ad (W y' x') Z) by rw [Ad_sub, Ad_inv_Ad]]
    refine ((hW y' hy' x' hx _).2).trans ?_
    rw [show Z - Ad (W y' x') Z = -(Ad (W y' x') Z - Z) by abel, SupportCont.hs_neg]
    have := hW1 y' hy' x' hx Z
    nlinarith [Real.sqrt_nonneg (N : ℝ)]
  · have hn : x' ∉ Blk S.toDomSeq (jj y') y' := fun hm => h ((sc_mem_blk S.toDomSeq hy' hm).2)
    rw [lamZ_supp S W hy' Z x' hn, lamZ_supp S (W1 S) hy' Z x' hn, sub_zero]
    simp [hs, hs2, ntr]
    positivity

lemma avgW_sub (W : Site NF → Site NF → GLN) (y : Site NF) (v w : Site NF → Mat) :
    avgW S.toDomSeq W y (v - w) = avgW S.toDomSeq W y v - avgW S.toDomSeq W y w := by
  simp only [avgW, Pi.sub_apply, Ad_sub, sum_sub_distrib, smul_sub]

/-- The constant of `That_diff`. -/
def CTd (S : SeqDom) (N : ℕ) (δ α₁ η : ℝ) : ℝ :=
  (S.L : ℝ) ^ (4 : ℝ) *
    (2 * Real.sqrt N * η * (Cv S δ (Csc S N) (4 * N * (S.L : ℝ) ^ 4) * Cv S δ (Csc S N) (4 * N * (S.L : ℝ) ^ 4) *
        (S.L : ℝ) ^ (4 : ℝ) * (S.toContSeq).c1 (1 / 2) (3 / 4 * δ)) +
      4 * N * η * (Cv S δ (Csc S N) (4 * N * (S.L : ℝ) ^ 4) * Cv S δ (Csc S N) (4 * N * (S.L : ℝ) ^ 4) *
        (S.L : ℝ) ^ (4 : ℝ) * (S.toContSeq).c1 (1 / 2) (3 / 4 * δ)) +
      4 * N * (CD S N δ α₁ η * Cv S δ (Csc S N) (4 * N * (S.L : ℝ) ^ 4) * (S.L : ℝ) ^ (4 : ℝ) *
          (S.toContSeq).c1 (1 / 2) (1 / 8 * δ) +
        Cv S δ (Csc S N) (4 * N * (S.L : ℝ) ^ 4) * CD S N δ α₁ η * (S.L : ℝ) ^ (4 : ℝ) *
          (S.toContSeq).c1 (1 / 2) (1 / 4 * δ)))

namespace ScalarHyp

variable {S} {X : Fin 4 → Site (SequenceAverages.N0 S) → Matrix (Fin N) (Fin N) ℂ} {α₁ : ℝ}
  {W : Site (SequenceAverages.N0 S) → Site (SequenceAverages.N0 S) → (Matrix (Fin N) (Fin N) ℂ)ˣ} {η : ℝ}
  {ΩD : Set (Site (SequenceAverages.N0 S))} {δ : ℝ}
  (H : ScalarHyp S X α₁ W η ΩD δ)
include H

lemma CD_nn [NeZero N] : 0 ≤ CD S N δ α₁ η := by
  have := H.hδ0; have := H.hα0; have := H.hη; have := H.Cv_nn; have := H.Cg_nn
  have hc1 : 0 ≤ (S.toContSeq).c1 (1 / 2) (3 / 4 * δ) := by unfold Summation.ContSeq.c1; positivity
  unfold CD; positivity

/-- **`|T̂_𝐔[y, y']Z - T̂_id[y, y']Z| ≤ C_Te^{-(δ/32)d(y, y')}|Z|`.** -/
theorem That_diff [NeZero N] (hRMa : (S.toContSeq).r1 (1 / 2) (1 / 8 * δ) ≤ RMS)
    (hRMs4 : 32 * Real.log S.L / (1 / 4 * δ) ≤ RMS) {y y' : Site NF} (hy : y ∈ detB S.toDomSeq)
    (hy' : y' ∈ detB S.toDomSeq) (Z : Mat) :
    hs (That S X W ΩD y y' Z - That S (X0 S) (W1 S) ΩD y y' Z) ≤
      CTd S N δ α₁ η * Real.exp (-(1 / 32 * δ * S.dF y y')) * hs Z := by
  have H0 := H.triv (N := N)
  have hδ := H.hδ0
  have hη := H.hη
  have hL : (3 : ℝ) ≤ S.L := by exact_mod_cast S.three_le_L
  have hL0 : (0 : ℝ) < S.L := by linarith
  have hCv := H.Cv_nn
  have hCD := H.CD_nn
  have hZ := hs_nonneg (N := N) Z
  have hc := fun m : ℝ => (show 0 < m → 0 ≤ (S.toContSeq).c1 (1 / 2) m from fun hm => by
    unfold Summation.ContSeq.c1; positivity)
  have hRM34 : (S.toContSeq).r1 (1 / 2) (3 / 4 * δ) ≤ RMS := (r1_anti S (by positivity) (by linarith)).trans hRMa
  have hRM14 : (S.toContSeq).r1 (1 / 2) (1 / 4 * δ) ≤ RMS := (r1_anti S (by positivity) (by linarith)).trans hRMa
  set Cv' := Cv S δ (Csc S N) (4 * N * (S.L : ℝ) ^ 4)
  set GU := Gp' S.toDomSeq (cfgX X) W ΩD
  set G0 := Gp' S.toDomSeq (cfgX (N := N) (X0 S)) (W1 S) ΩD
  have kU : KB S GU Cv' (7 / 8 * δ) 2 0 := H.KB_Gp'
  have k0 : KB S G0 Cv' (7 / 8 * δ) 2 0 := H0.KB_Gp'
  have kD : KB S (GU - G0) (CD S N δ α₁ η) (1 / 4 * δ) 2 0 := H.diff_KB hRM34
  have kUU := KB_comp S kU kU hCv hCv (by norm_num) hδ (m := 3 / 4 * δ) (by positivity) (by linarith) (by linarith)
    H.hRMs hRM34
  have kUD := KB_comp S kD kU hCD hCv (by norm_num) hδ (m := 1 / 8 * δ) (by positivity) (by linarith) (by linarith)
    H.hRMs hRMa
  have kD0 := KB_comp S k0 kD hCv hCD (by norm_num) hδ (m := 1 / 4 * δ) (by positivity) (by linarith) (by linarith)
    H.hRMs hRM14
  have kSq := KB_add S (KB_mono S kUD (by have := hc _ (show 0 < 1 / 8 * δ by positivity); positivity) le_rfl
      (show 1 / 16 * δ ≤ 1 / 8 * δ / 2 by linarith))
    (KB_mono S kD0 (by have := hc _ (show 0 < 1 / 4 * δ by positivity); positivity) le_rfl
      (show 1 / 16 * δ ≤ 1 / 4 * δ / 2 by linarith))
  have hsq : GU * (GU - G0) + (GU - G0) * G0 = GU * GU - G0 * G0 := by rw [mul_sub, sub_mul]; abel
  rw [hsq] at kSq
  simp only [add_zero] at kUU kSq
  -- the three terms
  set lW := lamZ S W y' Z
  set l1 := lamZ S (W1 S) y' Z
  have hsW := lamZ_supp S W hy' Z
  have hs1 := lamZ_supp S (W1 S) hy' Z
  have hbW := lamZ_bound S H.hW hy' Z
  have hb1 := lamZ_bound S (wbound_triv S) hy' Z
  have hbd := lamZ_diff S hη H.hW1 H.hW hy' Z
  set e3 := Real.exp (-(3 / 4 * δ / 2 * S.dF y y'))
  set e16 := Real.exp (-(1 / 16 * δ * S.dF y y'))
  set A := (S.L : ℝ) ^ (2 * jj y) * (S.L : ℝ) ^ (2 * jj y')
  have hA0 : 0 ≤ A := by positivity
  have he : e3 ≤ e16 := Real.exp_le_exp.2 (by have := S.dF_nonneg y y'; nlinarith)
  set CUU := Cv' * Cv' * (S.L : ℝ) ^ (4 : ℝ) * (S.toContSeq).c1 (1 / 2) (3 / 4 * δ)
  set Csq := CD S N δ α₁ η * Cv' * (S.L : ℝ) ^ (4 : ℝ) * (S.toContSeq).c1 (1 / 2) (1 / 8 * δ) +
    Cv' * CD S N δ α₁ η * (S.L : ℝ) ^ (4 : ℝ) * (S.toContSeq).c1 (1 / 2) (1 / 4 * δ)
  have hCUU : 0 ≤ CUU := by have := hc _ (show 0 < 3 / 4 * δ by positivity); positivity
  have t1 : hs (avgW S.toDomSeq W y (GU (GU lW)) - avgW S.toDomSeq (W1 S) y (GU (GU lW))) ≤
      η * (CUU * A * e3 * (2 * Real.sqrt N * hs Z)) := by
    refine avg_diff S hη H.hW1 hy fun x hx => ?_
    have := kUU y hy y' hy' lW _ (by positivity) hsW hbW x hx
    simpa only [Module.End.mul_apply, CUU, A, e3, mul_assoc, add_comm 2 0, zero_add] using this
  have t2 : hs (avgW S.toDomSeq (W1 S) y (GU (GU (lW - l1)))) ≤
      2 * Real.sqrt N * (CUU * A * e3 * (2 * Real.sqrt N * η * hs Z)) := by
    refine avgW_le S (wbound_triv S) hy fun x hx => ?_
    have := kUU y hy y' hy' (lW - l1) _ (by positivity)
      (fun x' hx' => by
        show lW x' - l1 x' = 0
        rw [show lW x' = 0 from hsW x' hx', show l1 x' = 0 from hs1 x' hx', sub_zero]) hbd x hx
    simpa only [Module.End.mul_apply, CUU, A, e3, mul_assoc] using this
  have t3 : hs (avgW S.toDomSeq (W1 S) y ((GU * GU - G0 * G0) l1)) ≤
      2 * Real.sqrt N * (Csq * A * e16 * (2 * Real.sqrt N * hs Z)) := by
    refine avgW_le S (wbound_triv S) hy fun x hx => ?_
    have := kSq y hy y' hy' l1 _ (by positivity) hs1 hb1 x hx
    simpa only [Csq, A, e16, mul_assoc] using this
  -- the decomposition
  have hdec : That S X W ΩD y y' Z - That S (X0 S) (W1 S) ΩD y y' Z =
      (((S.L : ℝ) ^ (4 * jj y') : ℝ) : ℂ)⁻¹ • ((avgW S.toDomSeq W y (GU (GU lW)) -
        avgW S.toDomSeq (W1 S) y (GU (GU lW))) + avgW S.toDomSeq (W1 S) y (GU (GU (lW - l1))) +
          avgW S.toDomSeq (W1 S) y ((GU * GU - G0 * G0) l1)) := by
    simp only [That, ← smul_sub]
    congr 1
    show avgW S.toDomSeq W y (GU (GU lW)) - avgW S.toDomSeq (W1 S) y (G0 (G0 l1)) = _
    rw [map_sub, map_sub, avgW_sub, LinearMap.sub_apply, avgW_sub, Module.End.mul_apply, Module.End.mul_apply]
    abel
  rw [hdec, RegularAverages.hs_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (pow_pos hL0 _)]
  have htot := (hs_add_le _ _).trans (add_le_add ((hs_add_le _ _).trans (add_le_add t1 t2)) t3)
  -- the scale shift `(a_y/a_{y'})² ≤ L⁴e^{δd/32}`
  have hsh := S.scale_shift (δ := 1 / 4 * δ) (by positivity) hRMs4 (σ := ((2 : ℕ) : ℝ)) (by norm_num) y' y
  rw [Real.rpow_natCast, Real.rpow_natCast, ← pow_mul, ← pow_mul, mul_comm (jj y) 2, mul_comm (jj y') 2,
    S.dF_comm y' y] at hsh
  have hAq : ((S.L : ℝ) ^ (4 * jj y'))⁻¹ * A ≤ (S.L : ℝ) ^ (4 : ℝ) * Real.exp (1 / 4 * δ / 8 * S.dF y y') := by
    simp only [A]
    have e4 : (S.L : ℝ) ^ (4 * jj y') = (S.L : ℝ) ^ (2 * jj y') * (S.L : ℝ) ^ (2 * jj y') := by
      rw [← pow_add]; ring_nf
    rw [e4, mul_inv, show ((S.L : ℝ) ^ (2 * jj y'))⁻¹ * ((S.L : ℝ) ^ (2 * jj y'))⁻¹ *
      ((S.L : ℝ) ^ (2 * jj y) * (S.L : ℝ) ^ (2 * jj y')) = (S.L : ℝ) ^ (2 * jj y) / (S.L : ℝ) ^ (2 * jj y') by
        field_simp]
    rw [div_le_iff₀ (by positivity)]; exact hsh
  have hexp : Real.exp (1 / 4 * δ / 8 * S.dF y y') * e16 = Real.exp (-(1 / 32 * δ * S.dF y y')) := by
    simp only [e16]; rw [← Real.exp_add]; ring_nf
  have hN2 : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt (Nat.cast_nonneg _)
  calc ((S.L : ℝ) ^ (4 * jj y'))⁻¹ * hs ((avgW S.toDomSeq W y (GU (GU lW)) - avgW S.toDomSeq (W1 S) y (GU (GU lW))) +
        avgW S.toDomSeq (W1 S) y (GU (GU (lW - l1))) + avgW S.toDomSeq (W1 S) y ((GU * GU - G0 * G0) l1))
      ≤ ((S.L : ℝ) ^ (4 * jj y'))⁻¹ * (η * (CUU * A * e16 * (2 * Real.sqrt N * hs Z)) +
          2 * Real.sqrt N * (CUU * A * e16 * (2 * Real.sqrt N * η * hs Z)) +
          2 * Real.sqrt N * (Csq * A * e16 * (2 * Real.sqrt N * hs Z))) := by
        refine mul_le_mul_of_nonneg_left (htot.trans ?_) (by positivity)
        gcongr
    _ = (((S.L : ℝ) ^ (4 * jj y'))⁻¹ * A) * e16 * hs Z *
          (2 * Real.sqrt N * η * CUU + 4 * (Real.sqrt N * Real.sqrt N) * η * CUU +
            4 * (Real.sqrt N * Real.sqrt N) * Csq) := by ring
    _ ≤ ((S.L : ℝ) ^ (4 : ℝ) * Real.exp (1 / 4 * δ / 8 * S.dF y y')) * e16 * hs Z *
          (2 * Real.sqrt N * η * CUU + 4 * (Real.sqrt N * Real.sqrt N) * η * CUU +
            4 * (Real.sqrt N * Real.sqrt N) * Csq) := by
        have : 0 ≤ Csq := by
          have := hc _ (show 0 < 1 / 8 * δ by positivity); have := hc _ (show 0 < 1 / 4 * δ by positivity)
          positivity
        gcongr
    _ = _ := by
        rw [hN2, mul_assoc ((S.L : ℝ) ^ (4 : ℝ)), hexp]; unfold CTd; ring

end ScalarHyp

end SFBounds
end CoreLean

end
