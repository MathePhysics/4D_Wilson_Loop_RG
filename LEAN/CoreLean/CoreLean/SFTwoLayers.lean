/-
`lem:sf-two-layers` of BALABAN_CORE.tex (`aaaa938bb57d`), the step "The finer layer", on the fine lattice at the trivial
configuration: the projection of a sequence whose `N(Q')` contains that of another is dominated by it.

* `Pop_eq_zero_iff`: `Pg = 0` iff `Q'G'g = 0` on `𝐁_D`.
* `Gp_null`: for `λ` in the compressed space with `Q'λ = 0` on `𝐁`, `G'(D^*Dλ) = λ` (the constraint term vanishes).
* `proj_le_of_ker`: for two Hermitian idempotents with `ker P₁ ⊂ ker P₂`, `‖P₂f‖ ≤ ‖P₁f‖`.
* `cen_nest`, `blk_sum_nest`: the blocks of the order `j + 1` are unions of those of the order `j`.
* `oneLayer`, `oneLayer_sc`: the sequence with the single layer `j` on the lattice of `S`.
* `null_incl`: `N(Q'_j) ⊂ N(Q')` for a sequence with the layers `j` and `j + 1`; `Pop_two_le_one`: `‖Pf‖ ≤ ‖P_jf‖`.
-/
import CoreLean.SFProjAlg
import CoreLean.SFComponentsFine

open Finset Matrix

noncomputable section

namespace CoreLean
namespace SFBounds

open Lattices SeqDom Blocks SmallFieldBlocks SFBox SFBox.SeqDomBox SmallFieldDecay SmallFieldCoercivity
  SequenceOperators CompressedInverse SFLocal ConcretePairing

variable (S : SeqDom) {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "GLN" => (Matrix (Fin N) (Fin N) ℂ)ˣ
local notation "NF" => SequenceAverages.N0 S
set_option quotPrecheck false in
local notation "jj" => (S.toDomSeq).sc

/-- **The kernel of `P`**: `Pg = 0` iff `Q'G'g = 0` on `𝐁_D`. -/
theorem Pop_eq_zero_iff [NeZero N] (X : Fin 4 → Site NF → Mat) (W : Site NF → Site NF → GLN) (ΩD : Set (Site NF))
    (hb : Function.Bijective (kerLin (kerT S (Subtype.val : BD S ΩD → Site NF) X W ΩD))) (g : Site NF → Mat) :
    Pop S X W ΩD g = 0 ↔ blkL S ΩD (avgL S W (Gp' S.toDomSeq (cfgX X) W ΩD g)) = 0 := by
  set G := Gp' S.toDomSeq (cfgX X) W ΩD
  set ν := blkL S ΩD (avgL S W (G g))
  have hP : Pop S X W ΩD g = G (QpL S W (unblkL S ΩD (Tinv S X W ΩD ν))) := rfl
  constructor
  · intro h
    rw [hP] at h
    have h1 : kerApply (kerT S (Subtype.val : BD S ΩD → Site NF) X W ΩD) (Tinv S X W ΩD ν) = 0 := by
      rw [← That_kernel, h, map_zero, map_zero, map_zero]
    rw [kerApply_Tinv S X W ΩD hb] at h1
    exact h1
  · intro h
    rw [hP, show ν = 0 from h, map_zero, map_zero, map_zero, map_zero]

/-- **`G'` on the null space of `Q'`**: if `λ` vanishes outside `Ω_D` and `Q'λ = 0` on `𝐁`, then `G'(D^*Dλ) = λ`. -/
theorem Gp_null [NeZero N] (X : Fin 4 → Site NF → Mat) (W : Site NF → Site NF → GLN) (ΩD : Set (Site NF))
    (hK : IsUnit (ckern (piD ΩD) (DeltaS S.toDomSeq (cfgX X) W))) {lam : Site NF → Mat}
    (hD : piD ΩD lam = lam) (hQ : ∀ y ∈ detB S.toDomSeq, avgW S.toDomSeq W y lam = 0) :
    Gp' S.toDomSeq (cfgX X) W ΩD (Ds1L a1 (cfgX X) (D0L a1 (cfgX X) lam)) = lam := by
  have hN : Ncon S.toDomSeq W lam = 0 := by
    funext x
    unfold Ncon
    rw [hQ _ (bc_mem_detB S x)]
    simp only [Ad, Matrix.mul_zero, Matrix.zero_mul, smul_zero, Pi.zero_apply]
  have hΔ : DeltaS S.toDomSeq (cfgX X) W lam = Ds1L a1 (cfgX X) (D0L a1 (cfgX X) lam) := by
    rw [DeltaS_eq, hN, add_zero]
  rw [← hΔ]
  show cinv (piD ΩD) (DeltaS S.toDomSeq (cfgX X) W) (DeltaS S.toDomSeq (cfgX X) W lam) = lam
  have := cinv_T_P (P := piD ΩD) (T := DeltaS S.toDomSeq (cfgX X) W) (piD_idem ΩD) hK lam
  rwa [hD] at this

/-- **The comparison of two orthogonal projections**: Hermitian idempotents with `ker P₁ ⊂ ker P₂` satisfy
`‖P₂f‖² ≤ ‖P₁f‖²`. -/
theorem proj_le_of_ker (P1 P2 : Module.End ℂ (Site NF → Mat))
    (h1 : ∀ f, P1 (P1 f) = P1 f) (h2 : ∀ f, P2 (P2 f) = P2 f)
    (hh2 : ∀ f g, herm S (P2 f) g = herm S f (P2 g))
    (hn2 : ∀ f, ∑ x, hs2 (P2 f x) = (herm S (P2 f) f).re)
    (hker : ∀ g, P1 g = 0 → P2 g = 0) (f : Site NF → Mat) :
    ∑ x, hs2 (P2 f x) ≤ ∑ x, hs2 (P1 f x) := by
  -- `P₂f = P₂P₁f`, since `f - P₁f ∈ ker P₁`
  have e : P2 f = P2 (P1 f) := by
    have : P1 (f - P1 f) = 0 := by rw [map_sub, h1, sub_self]
    have := hker _ this
    rw [map_sub, sub_eq_zero] at this
    exact this
  -- `‖P₂h‖² = Re⟨P₂h, h⟩ ≤ ‖P₂h‖‖h‖`
  set h := P1 f
  have hcs : (herm S (P2 h) h).re ≤ Real.sqrt (∑ x, hs2 (P2 h x)) * Real.sqrt (∑ x, hs2 (h x)) := by
    refine (Complex.re_le_norm _).trans ?_
    unfold herm
    refine (P0_abs_le S _ _).trans ?_
    simp only [cstar, hs_conjTranspose]
    have := Real.sum_mul_le_sqrt_mul_sqrt univ (fun x => hs (P2 h x)) (fun x => hs (h x))
    simp only [hs_sq] at this
    exact this
  have hX := hn2 h
  set X := ∑ x, hs2 (P2 h x)
  set Y := ∑ x, hs2 (h x)
  have hX0 : 0 ≤ X := sum_nonneg fun x _ => by rw [← hs_sq]; exact sq_nonneg _
  have hY0 : 0 ≤ Y := sum_nonneg fun x _ => by rw [← hs_sq]; exact sq_nonneg _
  have hle : X ≤ Y := by
    have h3 : X ≤ Real.sqrt X * Real.sqrt Y := hX ▸ hcs
    rcases hX0.eq_or_lt with h0 | hpos
    · rw [← h0]; exact hY0
    · have hs : Real.sqrt X ≤ Real.sqrt Y := by
        have hsx := Real.sqrt_pos.2 hpos
        have : Real.sqrt X * Real.sqrt X ≤ Real.sqrt X * Real.sqrt Y := by rwa [Real.mul_self_sqrt hX0]
        exact le_of_mul_le_mul_left this hsx
      calc X = Real.sqrt X ^ 2 := (Real.sq_sqrt hX0).symm
        _ ≤ Real.sqrt Y ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hs 2
        _ = Y := Real.sq_sqrt hY0
  rw [e]; exact hle

/-! ### The nesting of the blocks -/

/-- **`B^j(y') ⊂ B^{j+1}(y)` for `y' ∈ B^{j+1}(y)`**: `cen_{j+1} ∘ cen_j = cen_{j+1}`. -/
lemma cen_nest {j : ℕ} (hj : j + 1 ≤ S.k) (x : Site NF) : cen S.L (j + 1) (cen S.L j x) = cen S.L (j + 1) x := by
  set y := cen S.L (j + 1) x
  have hy : InLat S.L (j + 1) y := fun ν => cen1_isMul (L := S.L) (j + 1) (x ν)
  have hxy : x ∈ Blk S.toDomSeq (j + 1) y := by simp only [Blk, mem_filter, mem_univ, true_and]; rfl
  rw [mem_Blk_iff S hj hy, S.mem_Δy] at hxy
  have hU := Δ_eq_iUnion S.L_odd (show 1 ≤ j + 1 by omega) hj (S.ef_mem_TL_of hy)
  have h1 := hxy.1
  rw [hU] at h1
  obtain ⟨x', hx', hxx'⟩ := Set.mem_iUnion₂.1 h1
  have hx'T : x' ∈ S.TL j := by have := hx'.2; simpa using this
  obtain ⟨y0, -, hu⟩ := S.unique_cell (show j ≤ S.k by omega) (S.ef_mem_TL0 x)
  have e1 := hu _ ⟨S.ef_cen_mem_TL j x, S.ef_mem_Δ_cen j x⟩
  have e2 := hu _ ⟨hx'T, by simpa using hxx'⟩
  have hc : S.ef (cen S.L j x) = x' := e1.trans e2.symm
  have hmem : cen S.L j x ∈ Blk S.toDomSeq (j + 1) y := by
    rw [mem_Blk_iff S hj hy, S.mem_Δy]
    exact ⟨by rw [hc]; exact hx'.1, S.ef_mem_TL0 _⟩
  simp only [Blk, mem_filter, mem_univ, true_and] at hmem
  exact hmem

/-- **A block of the scale `j + 1` is the union of the blocks of the scale `j` in it.** -/
lemma blk_sum_nest {M : Type*} [AddCommMonoid M] {j : ℕ} (hj : j + 1 ≤ S.k) (y : Site NF) (f : Site NF → M) :
    ∑ x ∈ Blk S.toDomSeq (j + 1) y, f x =
      ∑ y' ∈ (Blk S.toDomSeq (j + 1) y).image (cen S.L j), ∑ x ∈ Blk S.toDomSeq j y', f x := by
  rw [← sum_fiberwise_of_maps_to (g := cen S.L j) (fun x hx => mem_image_of_mem _ hx)]
  refine sum_congr rfl fun y' hy' => ?_
  congr 1
  ext x
  simp only [mem_filter, Blk, mem_univ, true_and]
  obtain ⟨x0, hx0, rfl⟩ := mem_image.1 hy'
  simp only [Blk, mem_filter, mem_univ, true_and] at hx0
  constructor
  · rintro ⟨-, h⟩; exact h
  · intro h
    refine ⟨?_, h⟩
    have h' : cen S.L j x = cen S.L j x0 := h
    have hx0' : cen S.L (j + 1) x0 = y := hx0
    show cen S.L (j + 1) x = y
    rw [← cen_nest S hj x, h', cen_nest S hj x0]
    exact hx0'

/-! ### The sequence with the single layer of the order `j` -/

open Classical in
/-- **The sequence with the single layer `j`** (`Ω_i = 𝕋` for `i ≤ j`, `Ω_i = ∅` for `i > j`) on the lattice of `S`. -/
def oneLayer (j : ℕ) (hj : j ≤ S.k) : SeqDom where
  L := S.L
  L_odd := S.L_odd
  three_le_L := S.three_le_L
  k := S.k
  mT := S.mT
  one_le_mT := S.one_le_mT
  mM := S.mM
  mM_le := S.mM_le
  R := S.R
  one_le_R := S.one_le_R
  Ω := fun i => if i ≤ j then Set.univ else ∅
  Ω_zero := by simp
  Ω_succ := fun i => by
    by_cases h : i + 1 ≤ j
    · rw [if_pos h, if_pos (by omega)]
    · rw [if_neg h]; exact Set.empty_subset _
  Ω_top := fun i hi => by rw [if_neg (by omega)]
  cubes := fun i _ _ => by
    by_cases h : i ≤ j
    · refine ⟨Lat (ellT S.L S.mT) ((S.L ^ S.mM : ℕ) * sp S.L S.k i), subset_rfl, ?_⟩
      rw [if_pos h]
      ext z
      simp only [Set.mem_univ, true_iff, Set.mem_iUnion]
      have hL := S.Lpos
      obtain ⟨c, hc, hz⟩ := cells_cover (mul_pos (Nat.cast_pos.2 (pow_pos S.Lpos _)) (Lattices.sp_pos S.Lpos i)) z
      exact ⟨c, hc, hz⟩
    · exact ⟨∅, Set.empty_subset _, by rw [if_neg h]; simp⟩
  sep := fun i _ _ hc hn => by
    exfalso
    by_cases h : i ≤ j
    · rw [if_pos h] at hc; simp at hc
    · rw [if_neg (by omega : ¬ (i + 1 ≤ j))] at hn; simp at hn

lemma oneLayer_sc {j : ℕ} (hj : j ≤ S.k) (x : Site NF) : ((oneLayer S j hj).toDomSeq).sc x = j := by
  have hmem : ∀ i, x ∈ ((oneLayer S j hj).toDomSeq).Ω i ↔ i ≤ j := fun i => by
    change S.ef x ∈ (if i ≤ j then Set.univ else ∅) ↔ i ≤ j
    split_ifs with h
    · simp [h]
    · simp [h]
  have h1 := (((oneLayer S j hj).toDomSeq).mem_iff x j).1 ((hmem j).2 le_rfl)
  have h2 := (hmem _).1 ((((oneLayer S j hj).toDomSeq).mem_iff x (((oneLayer S j hj).toDomSeq).sc x)).2 le_rfl)
  omega

/-- At the trivial transports `Q'λ(y) = 0` iff the sum of `λ` over the block vanishes. -/
lemma avgW_triv_eq_zero_iff (D : DomSeq NF) {y : Site NF} (hy : y ∈ detB D) (lam : Site NF → Mat) :
    avgW D (W1 S) y lam = 0 ↔ ∑ x ∈ Blk D (D.sc y) y, lam x = 0 := by
  have hL : (0 : ℝ) < D.L := by exact_mod_cast (show 0 < D.L by have := D.three_le_L; omega)
  rw [avgW_blk D (W1 S) hy lam]
  have e : ∀ x, Ad ((W1 (N := N) S) y x) (lam x) = lam x := fun x => by simp [Ad, W1]
  simp only [e]
  have hc : (((D.L : ℝ) ^ (4 * D.sc y) : ℝ) : ℂ)⁻¹ ≠ 0 :=
    inv_ne_zero (by exact_mod_cast (pow_pos hL _).ne')
  exact smul_eq_zero.trans (or_iff_right hc)

/-- **`N(Q'_j) ⊂ N(Q')`** for a sequence `S` with the layers `j` and `j + 1` only: the averages of the order `j + 1`
are means of those of the order `j`. -/
theorem null_incl {j : ℕ} (hj0 : j ≤ S.k) (hj1 : j + 1 ≤ S.k) (hlow : ∀ i ≤ j, S.Ω i = Set.univ)
    (hhigh : ∀ i, j + 2 ≤ i → S.Ω i = ∅) (lam : Site NF → Mat)
    (h : ∀ y ∈ detB (oneLayer S j hj0).toDomSeq, avgW (oneLayer S j hj0).toDomSeq (W1 S) y lam = 0) :
    ∀ y ∈ detB S.toDomSeq, avgW S.toDomSeq (W1 S) y lam = 0 := by
  set S1 := oneLayer S j hj0
  -- the block sums of the order `j` vanish
  have h0 : ∀ z : Site NF, ∑ x ∈ Blk S.toDomSeq j (cen S.L j z), lam x = 0 := by
    intro z
    have hz : cen S.L j z ∈ detB S1.toDomSeq := by
      refine mem_image.2 ⟨z, mem_univ _, ?_⟩
      show cen S.L ((S1.toDomSeq).sc z) z = _
      rw [oneLayer_sc]
    have := (avgW_triv_eq_zero_iff S S1.toDomSeq hz lam).1 (h _ hz)
    have e : (S1.toDomSeq).sc (cen S.L j z) = j := oneLayer_sc S hj0 _
    calc ∑ x ∈ Blk S.toDomSeq j (cen S.L j z), lam x
        = ∑ x ∈ Blk S1.toDomSeq ((S1.toDomSeq).sc (cen S.L j z)) (cen S.L j z), lam x := by rw [e]; rfl
      _ = 0 := this
  -- the scales of `S` are `j` and `j + 1`
  have hsc : ∀ x, j ≤ jj x ∧ jj x ≤ j + 1 := fun x => by
    constructor
    · exact ((S.toDomSeq).mem_iff x j).1 (by rw [S.mem_toDomSeq_Ω, hlow j le_rfl]; trivial)
    · by_contra hc
      have := ((S.toDomSeq).mem_iff x (j + 2)).2 (by omega)
      rw [S.mem_toDomSeq_Ω, hhigh (j + 2) le_rfl] at this
      exact this
  intro y hy
  rw [avgW_triv_eq_zero_iff S S.toDomSeq hy lam]
  obtain ⟨x0, -, rfl⟩ := mem_image.1 hy
  rw [sc_bc]
  rcases (show jj x0 = j ∨ jj x0 = j + 1 by have := hsc x0; omega) with h1 | h1
  · show ∑ x ∈ Blk S.toDomSeq (jj x0) (cen S.L (jj x0) x0), lam x = 0
    rw [h1]; exact h0 x0
  · show ∑ x ∈ Blk S.toDomSeq (jj x0) (cen S.L (jj x0) x0), lam x = 0
    rw [h1, blk_sum_nest S hj1]
    refine sum_eq_zero fun y' hy' => ?_
    obtain ⟨z, -, rfl⟩ := mem_image.1 hy'
    exact h0 z

lemma piD_univ (f : Site NF → Mat) : piD (Set.univ : Set (Site NF)) f = f := by
  funext x; simp [piD_apply]

/-- The vanishing of `blk(Q'h)` on `𝐁_D = 𝐁` (the torus as the Dirichlet domain). -/
lemma blk_zero_iff (D : SeqDom) (W : Site (SequenceAverages.N0 D) → Site (SequenceAverages.N0 D) → GLN)
    (h : Site (SequenceAverages.N0 D) → Mat) :
    blkL D Set.univ (avgL D W h) = 0 ↔ ∀ y ∈ detB D.toDomSeq, avgW D.toDomSeq W y h = 0 := by
  constructor
  · intro hz y hy
    have hyB : y ∈ BD D Set.univ := (mem_BD D).2 ⟨hy, fun _ _ => Set.mem_univ _⟩
    have := congrArg (fun u : L2 (BD D Set.univ) (VS N 1) => proj (u.ofLp ⟨y, hyB⟩)) hz
    simp only [blkL, LinearMap.coe_mk, AddHom.coe_mk, WithLp.ofLp_toLp, proj_emb] at this
    have e : avgW D.toDomSeq W y h = proj ((0 : L2 (BD D Set.univ) (VS N 1)).ofLp ⟨y, hyB⟩) := this
    rw [e]; ext i k; simp [proj, matOf]
  · intro hz
    ext1 c
    simp only [blkL, LinearMap.coe_mk, AddHom.coe_mk, WithLp.ofLp_toLp]
    show emb (avgW D.toDomSeq W c.1 h) = _
    rw [hz _ ((BD_sub D Set.univ) c.2)]
    ext p; simp [emb, vecOf]

/-- **The finer layer dominates** (`lem:sf-two-layers`, first step): for a sequence `S` with the layers `j` and `j + 1`
only and the torus as the Dirichlet domain, `‖Pf‖ ≤ ‖P_jf‖` at the trivial configuration, `P_j` the projection of the
sequence with the single layer `j`. -/
theorem Pop_two_le_one [NeZero N] {j : ℕ} (hj0 : j ≤ S.k) (hj1 : j + 1 ≤ S.k) (hlow : ∀ i ≤ j, S.Ω i = Set.univ)
    (hhigh : ∀ i, j + 2 ≤ i → S.Ω i = ∅)
    (hb1 : Function.Bijective (kerLin (kerT (N := N) (oneLayer S j hj0) (Subtype.val : BD (oneLayer S j hj0) Set.univ →
      Site (SequenceAverages.N0 (oneLayer S j hj0))) (X0 (oneLayer S j hj0)) (W1 (oneLayer S j hj0)) Set.univ)))
    (hb2 : Function.Bijective (kerLin (kerT (N := N) S (Subtype.val : BD S Set.univ → Site NF) (X0 S) (W1 S) Set.univ)))
    (f : Site NF → Mat) :
    ∑ x, hs2 (Pop S (X0 S) (W1 S) Set.univ f x) ≤
      ∑ x, hs2 (Pop (oneLayer S j hj0) (X0 (oneLayer S j hj0)) (W1 (oneLayer S j hj0)) Set.univ f x) := by
  set S1 := oneLayer S j hj0
  refine proj_le_of_ker S (Pop S1 (X0 S1) (W1 S1) Set.univ) (Pop S (X0 S) (W1 S) Set.univ)
    (Pop_idem S1 _ _ _ hb1) (Pop_idem S _ _ _ hb2) (Pop_herm_triv S Set.univ hb2) (Pop_norm_triv S Set.univ hb2)
    (fun g hg => ?_) f
  set lam := Gp' S1.toDomSeq (cfgX (X0 S1)) (W1 S1) Set.univ g
  have h1 : ∀ y ∈ detB S1.toDomSeq, avgW S1.toDomSeq (W1 S1) y lam = 0 :=
    (blk_zero_iff S1 (W1 S1) lam).1 ((Pop_eq_zero_iff S1 _ _ _ hb1 g).1 hg)
  have h2 : ∀ y ∈ detB S.toDomSeq, avgW S.toDomSeq (W1 S) y lam = 0 := null_incl S hj0 hj1 hlow hhigh lam h1
  -- `D^*Dλ = g`
  have hDD : Ds1L a1 (cfgX (X0 S)) (D0L a1 (cfgX (X0 S)) lam) = g := by
    have hN : Ncon S1.toDomSeq (W1 S1) lam = 0 := by
      funext x
      unfold Ncon
      rw [h1 _ (bc_mem_detB S1 x)]
      simp only [Ad, Matrix.mul_zero, Matrix.zero_mul, smul_zero, Pi.zero_apply]
    have hT : piD Set.univ (DeltaS S1.toDomSeq (cfgX (X0 S1)) (W1 S1) lam) = piD Set.univ g :=
      P_T_cinv (P := piD Set.univ) (T := DeltaS S1.toDomSeq (cfgX (X0 S1)) (W1 S1)) (piD_idem _)
        (hK_triv S1 Set.univ) g
    rw [piD_univ, piD_univ, DeltaS_eq, hN, add_zero] at hT
    exact hT
  have hG : Gp' S.toDomSeq (cfgX (X0 S)) (W1 S) Set.univ g = lam := by
    rw [← hDD]
    exact Gp_null S (X0 S) (W1 S) Set.univ (hK_triv S Set.univ) (piD_univ S lam) h2
  refine (Pop_eq_zero_iff S _ _ _ hb2 g).2 ?_
  rw [hG]
  exact (blk_zero_iff S (W1 S) lam).2 h2

end SFBounds
end CoreLean

end
