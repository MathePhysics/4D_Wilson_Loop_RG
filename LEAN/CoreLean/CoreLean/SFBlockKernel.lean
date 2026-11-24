/-
`prop:sf-block` of BALABAN_CORE.tex (`d4ef86a9a5fd`): the scaled block operator as a kernel on `L²(𝐁_D; V)`, `V = M_N(ℂ)`
with the Hilbert–Schmidt inner product (as `VS N 1`), for `lem:kernel-inverse` (`KernelInverse.lean`), on the fine
lattice (`a₀ = 1`).

* `lamZ_add`, `lamZ_smul`, `thatL`: the entries `T̂[y, y']` are complex-linear maps of `M_N(ℂ)`.
* `emb`, `proj`: `M_N(ℂ) ≅ V`; `norm_emb`: `‖emb X‖ = √N|X|`; `inner_emb`: `⟨emb A, emb B⟩ = N tr(A^*B)/N·N`.
* `kerT`: the kernel `T[c, c'] = emb ∘ T̂[c, c'] ∘ proj` on the points `c, c'` of `𝐁_D`; `norm_kerT_le`: an entry bound
  `|T̂[c, c']Z| ≤ k|Z|` gives `‖T[c, c']‖ ≤ k`.
* `DS`: the fine sites with the weighted distance as a pseudometric space.
* `BD`: the points of `𝐁` whose blocks lie in `Ω_D`; `extBD`: extension by `0`; `row_triv`: at the trivial field
  `Σ_{c'}T̂₀[c, c']Z_{c'} = (Q'G'²Q'^*ν)(c)` with `ν = a^{-4}Z`.
* `coercive_kerT`: `Re⟨μ, T₀μ⟩ ≥ c_lo²‖μ‖²` on `L²(𝐁_D; V)`, from `coercive_triv`.
* `ScalarHyp.opBound_T1`: for `0 ≤ θ ≤ δ/64` the conjugation of `T_𝐔 - T_id` by `e^{θd(·, y)}` has norm
  `≤ C_T c₁(½, δ/32)` (the Schur test with `That_diff` and `eq:summation`).
* `ScalarHyp.block_inverse`: `lem:kernel-inverse` applied with `δ_k = δ/4`, `κ = κ_B + 1`, `γ = c_lo²`,
  `θ₀ = δ/64`, `K = c₁(½, δ/8) + 1`, under the smallness `C_T c₁(½, δ/32) ≤ γ/4`: `T_𝐔` is invertible on
  `L²(𝐁_D; V)` and `‖T_𝐔⁻¹[c, c']‖ ≤ (2/γ)e^{-θ_B d(c, c')}` (eq:sf-block-inverse in the scaled form).
-/
import CoreLean.SFBlockDiff
import CoreLean.KernelInverse

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
set_option quotPrecheck false in
local notation "jj" => (S.toDomSeq).sc

lemma lamZ_add (W : Site NF → Site NF → GLN) (y' : Site NF) (Z₁ Z₂ : Mat) :
    lamZ S W y' (Z₁ + Z₂) = lamZ S W y' Z₁ + lamZ S W y' Z₂ := by
  funext x; simp only [lamZ, QpStar, Pi.add_apply]; split_ifs
  · exact Ad_add _ _ _
  · simp [Ad]

lemma lamZ_smul (W : Site NF → Site NF → GLN) (y' : Site NF) (a : ℂ) (Z : Mat) :
    lamZ S W y' (a • Z) = a • lamZ S W y' Z := by
  funext x; simp only [lamZ, QpStar, Pi.smul_apply]; split_ifs
  · exact Ad_smul _ _ _
  · simp [Ad]

lemma avgW_add (W : Site NF → Site NF → GLN) (y : Site NF) (v w : Site NF → Mat) :
    avgW S.toDomSeq W y (v + w) = avgW S.toDomSeq W y v + avgW S.toDomSeq W y w := by
  simp only [avgW, Pi.add_apply, Ad_add, sum_add_distrib, smul_add]

lemma avgW_smul (W : Site NF → Site NF → GLN) (y : Site NF) (a : ℂ) (v : Site NF → Mat) :
    avgW S.toDomSeq W y (a • v) = a • avgW S.toDomSeq W y v := by
  simp only [avgW, Pi.smul_apply, Ad_smul, ← smul_sum]; rw [smul_comm]

/-- The entry `T̂[y, y']` as a complex-linear map. -/
def thatL (X : Fin 4 → Site NF → Mat) (W : Site NF → Site NF → GLN) (ΩD : Set (Site NF)) (y y' : Site NF) :
    Mat →ₗ[ℂ] Mat where
  toFun := That S X W ΩD y y'
  map_add' Z₁ Z₂ := by simp only [That, lamZ_add, map_add, avgW_add, smul_add]
  map_smul' a Z := by
    simp only [That, lamZ_smul, map_smul, avgW_smul, RingHom.id_apply]; rw [smul_comm]

/-- `M_N(ℂ) → V`. -/
def emb (X : Mat) : VS N 1 := vecOf fun _ => X

/-- `V → M_N(ℂ)`. -/
def proj (v : VS N 1) : Mat := matOf v 0

lemma proj_emb (X : Mat) : proj (emb X) = X := by simp [proj, emb]

lemma emb_proj (v : VS N 1) : emb (proj v) = v := by
  rw [emb, proj]; conv_rhs => rw [← vecOf_matOf v]
  congr 1; funext k; rw [Subsingleton.elim k 0]

/-- `emb` and `proj` as linear maps. -/
def embL : Mat →ₗ[ℂ] VS N 1 where
  toFun := emb
  map_add' A B := by ext p; rfl
  map_smul' a A := by ext p; rfl

def projL : VS N 1 →ₗ[ℂ] Mat where
  toFun := proj
  map_add' v w := by ext i j; rfl
  map_smul' a v := by ext i j; rfl

lemma norm_emb (X : Mat) : ‖emb (N := N) X‖ = Real.sqrt N * hs X := by
  rw [← Real.sqrt_sq (norm_nonneg _), normV_sq, Real.sqrt_mul (Nat.cast_nonneg _)]
  simp [emb, hs]

lemma norm_eq_proj (v : VS N 1) : ‖v‖ = Real.sqrt N * hs (proj v) := by
  conv_lhs => rw [← emb_proj v]
  exact norm_emb _

/-- **The kernel** `T[c, c'] = emb ∘ T̂[c, c'] ∘ proj` on the points of `𝐁_D`. -/
def kerT {ι : Type*} (f : ι → Site NF) (X : Fin 4 → Site NF → Mat) (W : Site NF → Site NF → GLN)
    (ΩD : Set (Site NF)) (c c' : ι) : VS N 1 →L[ℂ] VS N 1 :=
  LinearMap.toContinuousLinearMap (embL ∘ₗ thatL S X W ΩD (f c) (f c') ∘ₗ projL)

lemma kerT_apply {ι : Type*} (f : ι → Site NF) (X : Fin 4 → Site NF → Mat) (W : Site NF → Site NF → GLN)
    (ΩD : Set (Site NF)) (c c' : ι) (v : VS N 1) :
    kerT S f X W ΩD c c' v = emb (That S X W ΩD (f c) (f c') (proj v)) := rfl

/-- An entry bound `|T̂[c, c']Z| ≤ k|Z|` gives `‖T[c, c']‖ ≤ k`. -/
lemma norm_kerT_le [NeZero N] {ι : Type*} (f : ι → Site NF) (X X' : Fin 4 → Site NF → Mat)
    (W W' : Site NF → Site NF → GLN) (ΩD : Set (Site NF)) (c c' : ι) {k : ℝ} (hk : 0 ≤ k)
    (h : ∀ Z : Mat, hs (That S X W ΩD (f c) (f c') Z - That S X' W' ΩD (f c) (f c') Z) ≤ k * hs Z) :
    ‖kerT S f X W ΩD c c' - kerT S f X' W' ΩD c c'‖ ≤ k := by
  refine ContinuousLinearMap.opNorm_le_bound _ hk fun v => ?_
  rw [ContinuousLinearMap.sub_apply, kerT_apply, kerT_apply,
    show emb (That S X W ΩD (f c) (f c') (proj v)) - emb (That S X' W' ΩD (f c) (f c') (proj v)) =
      emb (N := N) (That S X W ΩD (f c) (f c') (proj v) - That S X' W' ΩD (f c) (f c') (proj v)) by ext p; rfl,
    norm_emb, norm_eq_proj v]
  have := h (proj v)
  have hN := Real.sqrt_nonneg (N : ℝ)
  nlinarith [hs_nonneg (proj v)]

lemma norm_kerT_le' [NeZero N] {ι : Type*} (f : ι → Site NF) (X : Fin 4 → Site NF → Mat)
    (W : Site NF → Site NF → GLN) (ΩD : Set (Site NF)) (c c' : ι) {k : ℝ} (hk : 0 ≤ k)
    (h : ∀ Z : Mat, hs (That S X W ΩD (f c) (f c') Z) ≤ k * hs Z) : ‖kerT S f X W ΩD c c'‖ ≤ k := by
  refine ContinuousLinearMap.opNorm_le_bound _ hk fun v => ?_
  rw [kerT_apply, norm_emb, norm_eq_proj v]
  have := h (proj v)
  have hN := Real.sqrt_nonneg (N : ℝ)
  nlinarith [hs_nonneg (proj v)]

/-- The fine sites with the weighted distance. -/
def DS (S : SeqDom) : Type := Site (SequenceAverages.N0 S)

instance : PseudoMetricSpace (DS S) where
  dist := S.dF
  dist_self := S.dF_self
  dist_comm := S.dF_comm
  dist_triangle := S.dF_triangle

lemma dist_DS (x x' : DS S) : dist x x' = S.dF x x' := rfl

open scoped Classical in
/-- The points of `𝐁` whose blocks lie in `Ω_D`. -/
def BD (ΩD : Set (Site NF)) : Finset (Site NF) :=
  (detB S.toDomSeq).filter fun y => ∀ x ∈ Blk S.toDomSeq (jj y) y, x ∈ ΩD

open scoped Classical in
lemma BD_sub (ΩD : Set (Site NF)) : BD S ΩD ⊆ detB S.toDomSeq := by
  unfold BD; exact filter_subset _ _

open scoped Classical in
lemma mem_BD {ΩD : Set (Site NF)} {y : Site NF} :
    y ∈ BD S ΩD ↔ y ∈ detB S.toDomSeq ∧ ∀ x ∈ Blk S.toDomSeq (jj y) y, x ∈ ΩD := by
  classical
  unfold BD; rw [mem_filter]

/-- `⟨emb A, emb B⟩ = tr(A^*B)`. -/
lemma inner_emb (A B : Mat) : inner ℂ (emb (N := N) A) (emb B) = (Aᴴ * B).trace := by
  rw [PiLp.inner_apply]
  show ∑ p : Fin 1 × Fin N × Fin N, inner ℂ (A p.2.1 p.2.2) (B p.2.1 p.2.2) = _
  rw [Fintype.sum_prod_type, Fin.sum_univ_one, Fintype.sum_prod_type]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, RCLike.inner_apply]
  rw [Finset.sum_comm]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  simp only [RCLike.star_def]; ring

lemma emb_sum {ι : Type*} (s : Finset ι) (f : ι → Mat) : ∑ i ∈ s, emb (N := N) (f i) = emb (∑ i ∈ s, f i) :=
  (map_sum embL f s).symm

/-- The extension of a family on `𝐁_D` by zero. -/
def extBD {ΩD : Set (Site NF)} (a : BD S ΩD → Mat) : Site NF → Mat :=
  fun y => if h : y ∈ BD S ΩD then a ⟨y, h⟩ else 0

lemma sum_lamZ_triv {ΩD : Set (Site NF)} (a : BD S ΩD → Mat) :
    ∑ c : BD S ΩD, lamZ S (W1 S) c.1 (a c) = QpStar S (W1 S) (extBD S a) := by
  funext x
  rw [Finset.sum_apply, QpStar_triv]
  simp only [lamZ, QpStar_triv, extBD]
  by_cases h : bc S.toDomSeq x ∈ BD S ΩD
  · rw [dif_pos h, Fintype.sum_eq_single ⟨bc S.toDomSeq x, h⟩]
    · simp
    · intro c hc
      rw [if_neg]; intro he; exact hc (Subtype.ext he.symm)
  · rw [dif_neg h]
    refine sum_eq_zero fun c _ => ?_
    rw [if_neg]; intro he; exact h (he ▸ c.2)


lemma avgW_sum (W : Site NF → Site NF → GLN) (y : Site NF) {ι : Type*} (s : Finset ι) (v : ι → Site NF → Mat) :
    avgW S.toDomSeq W y (∑ i ∈ s, v i) = ∑ i ∈ s, avgW S.toDomSeq W y (v i) := by
  let A : (Site NF → Mat) →ₗ[ℂ] Mat :=
    { toFun := fun v => avgW S.toDomSeq W y v, map_add' := avgW_add S W y,
      map_smul' := fun a v => avgW_smul S W y a v }
  exact map_sum A v s

/-- The entries applied to a family on `𝐁_D`: `Σ_{c'}T̂₀[c, c']Z_{c'} = (Q'G'²Q'^*ν)(c)`, `ν = a⁻⁴Z` extended by `0`. -/
lemma row_triv [NeZero N] (ΩD : Set (Site NF)) (Zc : BD S ΩD → Mat) (c : BD S ΩD) :
    ∑ c', That S (X0 S) (W1 S) ΩD c.1 c'.1 (Zc c') =
      avgW S.toDomSeq (W1 S) c.1 (Gp' S.toDomSeq (cfgX (N := N) (X0 S)) (W1 S) ΩD
        (Gp' S.toDomSeq (cfgX (X0 S)) (W1 S) ΩD (QpStar S (W1 S)
          (extBD S fun c' => ((((S.L : ℝ) ^ (4 * jj c'.1)) : ℝ) : ℂ)⁻¹ • Zc c')))) := by
  rw [← sum_lamZ_triv S, map_sum, map_sum, avgW_sum]
  refine sum_congr rfl fun c' _ => ?_
  simp only [That, lamZ_smul, map_smul, avgW_smul]

/-- **The coercivity of the kernel at the trivial field**: `Re⟨μ, T₀μ⟩ ≥ c_lo²‖μ‖²` on `L²(𝐁_D; V)`. -/
theorem coercive_kerT [NeZero N] (ΩD : Set (Site NF)) (μ : L2 (BD S ΩD) (VS N 1)) :
    ((9 / 32) ^ 4 / (864 + 4 * N)) ^ 2 * ‖μ‖ ^ 2 ≤
      RCLike.re (inner ℂ μ (kerApply (kerT S Subtype.val (X0 S) (W1 S) ΩD) μ)) := by
  have hL : (0 : ℝ) < S.L := by exact_mod_cast S.Lpos
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
  set Zc : BD S ΩD → Mat := fun c => proj (μ.ofLp c)
  set ν := extBD S fun c' : BD S ΩD => ((((S.L : ℝ) ^ (4 * jj c'.1)) : ℝ) : ℂ)⁻¹ • Zc c'
  set G0 := Gp' S.toDomSeq (cfgX (N := N) (X0 S)) (W1 S) ΩD
  set B := fun y => avgW S.toDomSeq (W1 S) y (G0 (G0 (QpStar S (W1 S) ν)))
  have hνc : ∀ c : BD S ΩD, ν c.1 = ((((S.L : ℝ) ^ (4 * jj c.1)) : ℝ) : ℂ)⁻¹ • Zc c := fun c => by
    simp only [ν, extBD, dif_pos c.2]
  have hZc : ∀ c : BD S ΩD, Zc c = ((((S.L : ℝ) ^ (4 * jj c.1)) : ℝ) : ℂ) • ν c.1 := fun c => by
    rw [hνc, smul_smul, mul_inv_cancel₀ (by exact_mod_cast (pow_pos hL _).ne'), one_smul]
  -- the inner product
  have hinner : inner ℂ μ (kerApply (kerT S Subtype.val (X0 S) (W1 S) ΩD) μ) =
      (N : ℂ) * ∑ y ∈ detB S.toDomSeq, (((S.L : ℝ) ^ (4 * jj y) : ℝ) : ℂ) * ntr ((ν y)ᴴ * B y) := by
    rw [PiLp.inner_apply]
    have hc : ∀ c : BD S ΩD, inner ℂ (μ.ofLp c) ((kerApply (kerT S Subtype.val (X0 S) (W1 S) ΩD) μ).ofLp c) =
        (N : ℂ) * ((((S.L : ℝ) ^ (4 * jj c.1) : ℝ) : ℂ) * ntr ((ν c.1)ᴴ * B c.1)) := by
      intro c
      simp only [kerApply, WithLp.ofLp_toLp, kerT_apply]
      rw [emb_sum, show (∑ c', That S (X0 S) (W1 S) ΩD c.1 c'.1 (proj (μ.ofLp c'))) =
          ∑ c', That S (X0 S) (W1 S) ΩD c.1 c'.1 (Zc c') from rfl, row_triv,
        ← emb_proj (μ.ofLp c), inner_emb]
      show ((Zc c)ᴴ * B c.1).trace = _
      rw [hZc, conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, smul_mul_assoc, trace_smul, ntr]
      have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
      rw [smul_eq_mul]; field_simp
    rw [sum_congr rfl fun c _ => hc c, ← mul_sum]
    congr 1
    rw [Finset.sum_coe_sort (BD S ΩD) (fun y => (((S.L : ℝ) ^ (4 * jj y) : ℝ) : ℂ) * ntr ((ν y)ᴴ * B y))]
    refine sum_subset (BD_sub S ΩD) fun y _ hy => ?_
    simp only [ν, extBD, dif_neg hy, conjTranspose_zero, zero_mul]
    simp [ntr]
  -- the coercivity of the form
  have hcoer := coercive_triv S ΩD ν (fun y _ hy => by
    by_contra hb
    exact hy (by simp only [ν, extBD]; rw [dif_neg (fun h => hb ((mem_BD S).1 h).2)]))
  -- the norms
  have hSsq : Ssq S ν = ∑ c : BD S ΩD, hs2 (Zc c) := by
    unfold Ssq
    rw [← sum_subset (BD_sub S ΩD) (fun y _ hy => by simp only [ν, extBD, dif_neg hy]; simp [hs2, ntr]),
      ← Finset.sum_coe_sort (BD S ΩD)]
    refine sum_congr rfl fun c _ => ?_
    rw [hνc, ← hs_sq, RegularAverages.hs_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (pow_pos hL _), mul_pow, hs_sq]
    rw [show 8 * jj c.1 = 4 * jj c.1 + 4 * jj c.1 by ring, pow_add]
    field_simp
  have hnorm : ‖μ‖ ^ 2 = N * ∑ c : BD S ΩD, hs2 (Zc c) := by
    rw [norm_sq_L2, mul_sum]
    refine sum_congr rfl fun c _ => ?_
    rw [norm_eq_proj, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _), hs_sq]
  rw [hinner, hnorm]
  rw [show RCLike.re ((N : ℂ) * ∑ y ∈ detB S.toDomSeq, (((S.L : ℝ) ^ (4 * jj y) : ℝ) : ℂ) * ntr ((ν y)ᴴ * B y)) =
    N * (∑ y ∈ detB S.toDomSeq, (((S.L : ℝ) ^ (4 * jj y) : ℝ) : ℂ) * ntr ((ν y)ᴴ * B y)).re from by
      rw [RCLike.re_to_complex, ← Complex.ofReal_natCast, Complex.re_ofReal_mul]]
  rw [hSsq] at hcoer
  have hN := (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  nlinarith

/-- A fine site as a point of `DS`. -/
def toDS (x : Site NF) : DS S := x

/-- `Σ_{c' ∈ 𝐁_D} e^{-(m/2)d(c, c')} ≤ c₁(½, m)`. -/
lemma sum_BD_le {ΩD : Set (Site NF)} {m : ℝ} (hm : 0 < m)
    (hRM : (S.toContSeq).r1 (1 / 2) m ≤ ((S.R * S.L ^ S.mM : ℕ) : ℝ)) (c : BD S ΩD) :
    ∑ c' : BD S ΩD, Real.exp (-(1 / 2 * m * S.dF c.1 c'.1)) ≤ (S.toContSeq).c1 (1 / 2) m := by
  rw [Finset.sum_coe_sort (BD S ΩD) (fun y' => Real.exp (-(1 / 2 * m * S.dF c.1 y')))]
  exact (sum_le_sum_of_subset_of_nonneg (BD_sub S ΩD) fun _ _ _ => (Real.exp_pos _).le).trans
    (S.summation_fine (α := 1 / 2) (by norm_num) hm hRM ((BD_sub S ΩD) c.2))

lemma opBound_mono {ι V : Type*} [Fintype ι] [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    {K : ι → ι → (V →L[ℂ] V)} {M M' : ℝ} (h : OpBound K M) (hM : M ≤ M') : OpBound K M' :=
  fun μ => (h μ).trans (mul_le_mul_of_nonneg_right hM (norm_nonneg _))

namespace ScalarHyp

variable {S} {X : Fin 4 → Site (SequenceAverages.N0 S) → Matrix (Fin N) (Fin N) ℂ} {α₁ : ℝ}
  {W : Site (SequenceAverages.N0 S) → Site (SequenceAverages.N0 S) → (Matrix (Fin N) (Fin N) ℂ)ˣ} {η : ℝ}
  {ΩD : Set (Site (SequenceAverages.N0 S))} {δ : ℝ}
  (H : ScalarHyp S X α₁ W η ΩD δ)
include H

lemma CTd_nn [NeZero N] : 0 ≤ CTd S N δ α₁ η := by
  have := H.hδ0; have := H.hη; have := H.Cv_nn; have := H.CD_nn
  have hc1 : 0 ≤ (S.toContSeq).c1 (1 / 2) (3 / 4 * δ) := by unfold Summation.ContSeq.c1; positivity
  have hc2 : 0 ≤ (S.toContSeq).c1 (1 / 2) (1 / 8 * δ) := by unfold Summation.ContSeq.c1; positivity
  have hc3 : 0 ≤ (S.toContSeq).c1 (1 / 2) (1 / 4 * δ) := by unfold Summation.ContSeq.c1; positivity
  unfold CTd; positivity

/-- **The perturbation**: for `0 ≤ θ ≤ δ/64` the conjugation of `T_𝐔 - T_id` by `e^{θd(·, y)}` has norm
`≤ C_T c₁(½, δ/32)`. -/
theorem opBound_T1 [NeZero N] (hRMb : (S.toContSeq).r1 (1 / 2) (1 / 32 * δ) ≤ ((S.R * S.L ^ S.mM : ℕ) : ℝ))
    (hRMs4 : 32 * Real.log S.L / (1 / 4 * δ) ≤ ((S.R * S.L ^ S.mM : ℕ) : ℝ)) (y : DS S) {θ : ℝ}
    (hθ0 : 0 ≤ θ) (hθ : θ ≤ 1 / 64 * δ) :
    OpBound (conjKer θ (fun c : BD S ΩD => dist (toDS S c.1) y)
      (fun c c' => kerT S Subtype.val X W ΩD c c' - kerT S Subtype.val (X0 S) (W1 S) ΩD c c'))
      (CTd S N δ α₁ η * (S.toContSeq).c1 (1 / 2) (1 / 32 * δ)) := by
  have hδ := H.hδ0
  have hCT := H.CTd_nn
  have hRMa : (S.toContSeq).r1 (1 / 2) (1 / 8 * δ) ≤ ((S.R * S.L ^ S.mM : ℕ) : ℝ) :=
    (r1_anti S (by positivity) (by linarith)).trans hRMb
  set k : BD S ΩD → BD S ΩD → ℝ := fun c c' =>
    CTd S N δ α₁ η * Real.exp (-(1 / 2 * (1 / 32 * δ) * S.dF c.1 c'.1))
  have hentry : ∀ c c', ‖conjKer θ (fun c : BD S ΩD => dist (toDS S c.1) y)
      (fun c c' => kerT S Subtype.val X W ΩD c c' - kerT S Subtype.val (X0 S) (W1 S) ΩD c c') c c'‖ ≤
      k c c' := by
    intro c c'
    have h1 : ‖kerT S Subtype.val X W ΩD c c' - kerT S Subtype.val (X0 S) (W1 S) ΩD c c'‖ ≤
        CTd S N δ α₁ η * Real.exp (-(1 / 32 * δ * S.dF c.1 c'.1)) :=
      norm_kerT_le S Subtype.val X (X0 S) W (W1 S) ΩD c c' (by positivity)
        (fun Z => H.That_diff hRMa hRMs4 ((BD_sub S ΩD) c.2) ((BD_sub S ΩD) c'.2) Z)
    have htri : dist (toDS S c.1) y ≤ dist (toDS S c.1) (toDS S c'.1) + dist (toDS S c'.1) y :=
      dist_triangle _ _ _
    have hd : dist (toDS S c.1) (toDS S c'.1) = S.dF c.1 c'.1 := rfl
    have hd0 : 0 ≤ S.dF c.1 c'.1 := hd ▸ dist_nonneg
    have hρ : θ * (dist (toDS S c.1) y - dist (toDS S c'.1) y) ≤ θ * S.dF c.1 c'.1 :=
      mul_le_mul_of_nonneg_left (by linarith) hθ0
    simp only [conjKer]
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc Real.exp (θ * (dist (toDS S c.1) y - dist (toDS S c'.1) y)) *
          ‖kerT S Subtype.val X W ΩD c c' - kerT S Subtype.val (X0 S) (W1 S) ΩD c c'‖
        ≤ Real.exp (θ * S.dF c.1 c'.1) * (CTd S N δ α₁ η * Real.exp (-(1 / 32 * δ * S.dF c.1 c'.1))) :=
          mul_le_mul (Real.exp_le_exp.2 hρ) h1 (norm_nonneg _) (Real.exp_pos _).le
      _ = CTd S N δ α₁ η * Real.exp (θ * S.dF c.1 c'.1 + -(1 / 32 * δ * S.dF c.1 c'.1)) := by
          rw [mul_left_comm, ← Real.exp_add]
      _ ≤ k c c' := by
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hCT
          nlinarith [mul_le_mul_of_nonneg_right hθ hd0]
  have hrow : ∀ c, ∑ c', k c c' ≤ CTd S N δ α₁ η * (S.toContSeq).c1 (1 / 2) (1 / 32 * δ) := fun c => by
    simp only [k]; rw [← mul_sum]
    exact mul_le_mul_of_nonneg_left (sum_BD_le S (by positivity) hRMb c) hCT
  have hcol : ∀ c', ∑ c, k c c' ≤ CTd S N δ α₁ η * (S.toContSeq).c1 (1 / 2) (1 / 32 * δ) := fun c' => by
    simp only [k]; rw [← mul_sum]
    refine mul_le_mul_of_nonneg_left (le_of_eq_of_le ?_ (sum_BD_le S (by positivity) hRMb c')) hCT
    exact sum_congr rfl fun c _ => by rw [S.dF_comm]
  have := opBound_of_entry _ k hentry hrow hcol
  rwa [max_self] at this

/-- **`prop:sf-block`, the inverse** (eq:sf-block-inverse, scaled form): with `γ = c_lo²` and the smallness
`C_T c₁(½, δ/32) ≤ γ/4`, the kernel `T_𝐔` on `L²(𝐁_D; V)` is invertible and the solution of `T_𝐔u = δ_{c'}w`
satisfies `‖u(c)‖ ≤ (2/γ)e^{-θ_B d(c, c')}‖w‖`, `θ_B = min{δ/64, δ/8, γδ/(24(κ_B + 1)K_B)}`,
`K_B = c₁(½, δ/8) + 1`. -/
theorem block_inverse [NeZero N]
    (hRMb : (S.toContSeq).r1 (1 / 2) (1 / 32 * δ) ≤ ((S.R * S.L ^ S.mM : ℕ) : ℝ))
    (hRMs4 : 32 * Real.log S.L / (1 / 4 * δ) ≤ ((S.R * S.L ^ S.mM : ℕ) : ℝ))
    (hsmallT : CTd S N δ α₁ η * (S.toContSeq).c1 (1 / 2) (1 / 32 * δ) ≤
      ((9 / 32) ^ 4 / (864 + 4 * N)) ^ 2 / 4) :
    Function.Bijective (kerLin (kerT S (Subtype.val : BD S ΩD → Site NF) X W ΩD)) ∧
    ∀ (c c' : BD S ΩD) (u : L2 (BD S ΩD) (VS N 1)) (w : VS N 1),
      kerApply (kerT S (Subtype.val : BD S ΩD → Site NF) X W ΩD) u = CoreLean.single c' w →
      ‖u.ofLp c‖ ≤ 2 / ((9 / 32) ^ 4 / (864 + 4 * N)) ^ 2 *
        Real.exp (-(min (1 / 64 * δ) (min (1 / 4 * δ / 2) (((9 / 32) ^ 4 / (864 + 4 * N)) ^ 2 * (1 / 4 * δ) /
          (6 * (kappaB S N δ + 1) * ((S.toContSeq).c1 (1 / 2) (1 / 8 * δ) + 1))))) * S.dF c.1 c'.1) * ‖w‖ := by
  have hδ := H.hδ0
  have H0 := H.triv (N := N)
  have hRMa : (S.toContSeq).r1 (1 / 2) (1 / 8 * δ) ≤ ((S.R * S.L ^ S.mM : ℕ) : ℝ) :=
    (r1_anti S (by positivity) (by linarith)).trans hRMb
  have hRMc : (S.toContSeq).r1 (1 / 2) (3 / 4 * δ) ≤ ((S.R * S.L ^ S.mM : ℕ) : ℝ) :=
    (r1_anti S (by positivity) (by linarith)).trans hRMa
  have hκ0 : 0 ≤ kappaB S N δ := by
    have := H.Cv_nn
    have hc1 : 0 ≤ (S.toContSeq).c1 (1 / 2) (3 / 4 * δ) := by unfold Summation.ContSeq.c1; positivity
    unfold kappaB CG2; positivity
  have hc1 : 0 ≤ (S.toContSeq).c1 (1 / 2) (1 / 8 * δ) := by unfold Summation.ContSeq.c1; positivity
  set T0 := kerT S (N := N) (Subtype.val : BD S ΩD → Site NF) (X0 S) (W1 S) ΩD
  set T1 : BD S ΩD → BD S ΩD → (VS N 1 →L[ℂ] VS N 1) :=
    fun c c' => kerT S Subtype.val X W ΩD c c' - kerT S Subtype.val (X0 S) (W1 S) ΩD c c'
  have hsum : T0 + T1 = kerT S (Subtype.val : BD S ΩD → Site NF) X W ΩD := by
    funext c c'; simp only [T0, T1, Pi.add_apply, add_sub_cancel]
  rw [← hsum]
  have hγ : (0 : ℝ) < ((9 / 32) ^ 4 / (864 + 4 * N)) ^ 2 := by positivity
  have hδ4 : (0 : ℝ) < 1 / 4 * δ := by positivity
  have hκ : (0 : ℝ) < kappaB S N δ + 1 := by linarith
  have hθ0 : (0 : ℝ) < 1 / 64 * δ := by positivity
  have hK0 : (0 : ℝ) < (S.toContSeq).c1 (1 / 2) (1 / 8 * δ) + 1 := by linarith
  refine kernel_inverse (fun c : BD S ΩD => toDS S c.1) (δ := 1 / 4 * δ) (κ := kappaB S N δ + 1)
    (γ := ((9 / 32) ^ 4 / (864 + 4 * N)) ^ 2) (θ0 := 1 / 64 * δ)
    (K := (S.toContSeq).c1 (1 / 2) (1 / 8 * δ) + 1) hδ4 hκ hγ hθ0 hK0
    (fun c => ?_) T0 T1 (fun c c' => ?_) (coercive_kerT S ΩD) (fun y θ h0 h1 => ?_)
  · refine (le_of_eq_of_le (sum_congr rfl fun c' _ => ?_) (sum_BD_le S (m := 1 / 8 * δ) (by positivity) hRMa c)).trans
      (by linarith)
    show Real.exp (-(1 / 4 * δ / 4) * S.dF c.1 c'.1) = _
    congr 1; ring
  · refine (norm_kerT_le' S Subtype.val (X0 S) (W1 S) ΩD c c' (by positivity)
      (fun Z => H0.That_bound hRMc ((BD_sub S ΩD) c.2) ((BD_sub S ΩD) c'.2) Z)).trans ?_
    show kappaB S N δ * Real.exp (-(1 / 4 * δ * S.dF c.1 c'.1)) ≤
      (kappaB S N δ + 1) * Real.exp (-(1 / 4 * δ) * S.dF c.1 c'.1)
    rw [neg_mul, mul_assoc (1 / 4) δ]
    exact mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
  · exact opBound_mono (H.opBound_T1 hRMb hRMs4 y h0 h1) hsmallT

end ScalarHyp

end SFBounds
end CoreLean

end
