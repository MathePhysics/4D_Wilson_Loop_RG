/-
`def:operators`(iii) of BALABAN_CORE.tex (`aaaa938bb57d`) on the fine lattice: the algebra of the projection
`P = G'Q'^*T⁻¹Q'G'` (`Pop` of `SFProjection.lean`), for `lem:sf-two-layers` and `prop:sf-vector-lower`.

* `That_kernel`: `blk ∘ Q' ∘ G'² ∘ Q'^* ∘ unblk` is the kernel `T̂` of `SFBlockKernel` (the scaled operator).
* `Pop_idem`: `P² = P` where `T̂` is invertible.
* `bpair`, `pair_unblk`, `That_symm`, `Tinv_symm`, `Pop_symm`: `T̂`, `T̂⁻¹` and `P` are symmetric for the trace pairings.
* At the trivial configuration: `cstarL`, `Pop_cstar_triv` (`P` commutes with `f ↦ f^*`), `herm`, `Pop_herm_triv`
  (`P` is Hermitian), `Pop_norm_triv` (`‖Pf‖² = Re⟨Pf, f⟩`).
-/
import CoreLean.SFProjection

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

/-- **`T̂ = blk ∘ Q' ∘ G'² ∘ Q'^* ∘ unblk`.** -/
theorem That_kernel (X : Fin 4 → Site NF → Mat) (W : Site NF → Site NF → GLN) (ΩD : Set (Site NF))
    (u : L2 (BD S ΩD) (VS N 1)) :
    blkL S ΩD (avgL S W (Gp' S.toDomSeq (cfgX X) W ΩD (Gp' S.toDomSeq (cfgX X) W ΩD
      (QpL S W (unblkL S ΩD u))))) = kerApply (kerT S (Subtype.val : BD S ΩD → Site NF) X W ΩD) u := by
  ext1 c
  set G := Gp' S.toDomSeq (cfgX X) W ΩD
  have hQ : QpL S W (unblkL S ΩD u) =
      ∑ c' : BD S ΩD, lamZ S W c'.1 (((((S.L : ℝ) ^ (4 * jj c'.1)) : ℝ) : ℂ)⁻¹ • proj (u.ofLp c')) :=
    (sum_lamZ S W _).symm
  rw [hQ, map_sum, map_sum]
  simp only [kerApply_apply, kerT_apply]
  rw [emb_sum]
  show emb (avgW S.toDomSeq W c.1 (∑ c' : BD S ΩD, G (G (lamZ S W c'.1
      (((((S.L : ℝ) ^ (4 * jj c'.1)) : ℝ) : ℂ)⁻¹ • proj (u.ofLp c')))))) = _
  rw [avgW_sum]
  congr 1
  refine sum_congr rfl fun c' _ => ?_
  simp only [That, lamZ_smul, map_smul, avgW_smul]
  rfl

/-- **`P² = P`** where `T̂` is invertible. -/
theorem Pop_idem (X : Fin 4 → Site NF → Mat) (W : Site NF → Site NF → GLN) (ΩD : Set (Site NF))
    (hb : Function.Bijective (kerLin (kerT S (Subtype.val : BD S ΩD → Site NF) X W ΩD))) (f : Site NF → Mat) :
    Pop S X W ΩD (Pop S X W ΩD f) = Pop S X W ΩD f := by
  set G := Gp' S.toDomSeq (cfgX X) W ΩD
  set ν := blkL S ΩD (avgL S W (G f))
  have h1 : Pop S X W ΩD f = G (QpL S W (unblkL S ΩD (Tinv S X W ΩD ν))) := rfl
  have h2 : Pop S X W ΩD (Pop S X W ΩD f) = G (QpL S W (unblkL S ΩD (Tinv S X W ΩD
      (blkL S ΩD (avgL S W (G (G (QpL S W (unblkL S ΩD (Tinv S X W ΩD ν)))))))))) := rfl
  rw [h2, That_kernel, kerApply_Tinv S X W ΩD hb, ← h1]

/-- The trace pairing `Σ_ctr(u(c)w(c))` of functions on `𝐁_D` (in the coordinates of `V`). -/
def bpair {ΩD : Set (Site NF)} (u w : L2 (BD S ΩD) (VS N 1)) : ℂ := ∑ c, ntr (proj (u.ofLp c) * proj (w.ofLp c))

lemma bpair_symm {ΩD : Set (Site NF)} (u w : L2 (BD S ΩD) (VS N 1)) : bpair S u w = bpair S w u := by
  unfold bpair
  refine sum_congr rfl fun c _ => ?_
  simp only [ntr, Matrix.trace_mul_comm (proj (u.ofLp c))]

lemma P0_symm' (f g : Site NF → Mat) : P0 f g = P0 g f := by
  simp only [P0, pairForm0]; exact wpair_symm _ _ _

/-- `⟨Q'^*unblk(u), h⟩ = Σ_ctr(u(c)(Q'h)(c))`. -/
lemma pair_unblk (W : Site NF → Site NF → GLN) (ΩD : Set (Site NF)) (u : L2 (BD S ΩD) (VS N 1)) (h : Site NF → Mat) :
    P0 (QpL S W (unblkL S ΩD u)) h = bpair S u (blkL S ΩD (avgL S W h)) := by
  have hL : (0 : ℝ) < S.L := by exact_mod_cast S.Lpos
  show P0 (QpStar S W (unblkL S ΩD u)) h = _
  rw [← avg_pair S W]
  have hz : ∀ y ∈ detB S.toDomSeq, y ∉ BD S ΩD →
      (((S.L : ℝ) ^ (4 * jj y) : ℝ) : ℂ) * ntr (unblkL S ΩD u y * avgW S.toDomSeq W y h) = 0 := by
    intro y _ hy
    simp only [unblkL, LinearMap.coe_mk, AddHom.coe_mk, extBD, dif_neg hy, zero_mul]
    simp [ntr]
  rw [← sum_subset (BD_sub S ΩD) hz, ← Finset.sum_coe_sort (BD S ΩD)]
  unfold bpair
  refine sum_congr rfl fun c _ => ?_
  have hc : (((S.L : ℝ) ^ (4 * jj c.1) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (pow_pos hL _).ne'
  show (((S.L : ℝ) ^ (4 * jj c.1) : ℝ) : ℂ) * ntr (extBD S (fun c' => ((((S.L : ℝ) ^ (4 * jj c'.1)) : ℝ) : ℂ)⁻¹ •
    proj (u.ofLp c')) c.1 * avgW S.toDomSeq W c.1 h) = ntr (proj (u.ofLp c) * proj (emb (avgW S.toDomSeq W c.1 h)))
  rw [proj_emb]
  simp only [extBD, dif_pos c.2, smul_mul_assoc, ntr_smul, ← mul_assoc, mul_inv_cancel₀ hc, one_mul]

/-- **`T̂` is symmetric** for the trace pairing. -/
theorem That_symm (X : Fin 4 → Site NF → Mat) (W : Site NF → Site NF → GLN) (ΩD : Set (Site NF))
    (hK : IsUnit (ckern (piD ΩD) (DeltaS S.toDomSeq (cfgX X) W))) (u w : L2 (BD S ΩD) (VS N 1)) :
    bpair S (kerApply (kerT S (Subtype.val : BD S ΩD → Site NF) X W ΩD) u) w =
      bpair S u (kerApply (kerT S (Subtype.val : BD S ΩD → Site NF) X W ΩD) w) := by
  set G := Gp' S.toDomSeq (cfgX X) W ΩD
  rw [← That_kernel, ← That_kernel, bpair_symm, ← pair_unblk, ← pair_unblk]
  calc P0 (QpL S W (unblkL S ΩD w)) (G (G (QpL S W (unblkL S ΩD u))))
      = P0 (G (QpL S W (unblkL S ΩD w))) (G (QpL S W (unblkL S ΩD u))) := (Gp'_symm S.toDomSeq _ _ _ hK _ _).symm
    _ = P0 (G (QpL S W (unblkL S ΩD u))) (G (QpL S W (unblkL S ΩD w))) := P0_symm' S _ _
    _ = P0 (QpL S W (unblkL S ΩD u)) (G (G (QpL S W (unblkL S ΩD w)))) := Gp'_symm S.toDomSeq _ _ _ hK _ _

/-- **`T̂⁻¹` is symmetric** for the trace pairing. -/
theorem Tinv_symm (X : Fin 4 → Site NF → Mat) (W : Site NF → Site NF → GLN) (ΩD : Set (Site NF))
    (hK : IsUnit (ckern (piD ΩD) (DeltaS S.toDomSeq (cfgX X) W)))
    (hb : Function.Bijective (kerLin (kerT S (Subtype.val : BD S ΩD → Site NF) X W ΩD))) (u w : L2 (BD S ΩD) (VS N 1)) :
    bpair S (Tinv S X W ΩD u) w = bpair S u (Tinv S X W ΩD w) := by
  conv_lhs => rw [← kerApply_Tinv S X W ΩD hb w]
  rw [← That_symm S X W ΩD hK, kerApply_Tinv S X W ΩD hb]

/-- **`P` is symmetric** for the pairing `⟨·,·⟩` of `0`-forms. -/
theorem Pop_symm (X : Fin 4 → Site NF → Mat) (W : Site NF → Site NF → GLN) (ΩD : Set (Site NF))
    (hK : IsUnit (ckern (piD ΩD) (DeltaS S.toDomSeq (cfgX X) W)))
    (hb : Function.Bijective (kerLin (kerT S (Subtype.val : BD S ΩD → Site NF) X W ΩD))) (f g : Site NF → Mat) :
    P0 (Pop S X W ΩD f) g = P0 f (Pop S X W ΩD g) := by
  set G := Gp' S.toDomSeq (cfgX X) W ΩD
  have h1 : Pop S X W ΩD f = G (QpL S W (unblkL S ΩD (Tinv S X W ΩD (blkL S ΩD (avgL S W (G f)))))) := rfl
  have h2 : Pop S X W ΩD g = G (QpL S W (unblkL S ΩD (Tinv S X W ΩD (blkL S ΩD (avgL S W (G g)))))) := rfl
  rw [h1, h2, Gp'_symm S.toDomSeq _ _ _ hK, pair_unblk, Tinv_symm S X W ΩD hK hb, P0_symm' S f,
    Gp'_symm S.toDomSeq _ _ _ hK, pair_unblk, bpair_symm]

/-! ### The real structure at the trivial configuration -/

/-- `u ↦ u^*` on the functions on `𝐁_D`. -/
def cstarL {ΩD : Set (Site NF)} (u : L2 (BD S ΩD) (VS N 1)) : L2 (BD S ΩD) (VS N 1) :=
  WithLp.toLp 2 fun c => emb ((proj (u.ofLp c))ᴴ)

lemma unblk_cstar {ΩD : Set (Site NF)} (u : L2 (BD S ΩD) (VS N 1)) :
    unblkL S ΩD (cstarL S u) = cstar (unblkL S ΩD u) := by
  funext x
  simp only [unblkL, LinearMap.coe_mk, AddHom.coe_mk, extBD, cstar, cstarL]
  split_ifs with h
  · simp only [WithLp.ofLp_toLp, proj_emb, conjTranspose_smul, star_inv₀, Complex.star_def, Complex.conj_ofReal]
  · simp

lemma blk_cstar {ΩD : Set (Site NF)} (g : Site NF → Mat) : blkL S ΩD (cstar g) = cstarL S (blkL S ΩD g) := by
  ext1 c
  simp only [blkL, LinearMap.coe_mk, AddHom.coe_mk, cstarL, WithLp.ofLp_toLp, proj_emb, cstar]

lemma QpStar_cstar_triv (μ : Site NF → Mat) : QpL S (W1 S) (cstar μ) = cstar (QpL S (W1 S) μ) := by
  funext x; show QpStar S (W1 S) (cstar μ) x = (QpStar S (W1 S) μ x)ᴴ
  simp only [QpStar_triv, cstar]

lemma hU_triv : ∀ ν x, ((cfgX (N := N) (X0 S) ν x : GLN) : Mat) ∈ unitaryGroup (Fin N) ℂ := fun ν x => by
  simp [cfgX, X0]

lemma hW_triv : ∀ y x, ((W1 (N := N) S y x : GLN) : Mat) ∈ unitaryGroup (Fin N) ℂ := fun _ _ => unitary_one

lemma avgL_cstar_triv (v : Site NF → Mat) : avgL S (W1 S) (cstar v) = cstar (avgL S (W1 S) v) := by
  funext y; exact avgW_cstar S.toDomSeq (W1 S) (hW_triv S) y v

lemma Gp_cstar_triv [NeZero N] (ΩD : Set (Site NF)) (f : Site NF → Mat) :
    Gp' S.toDomSeq (cfgX (N := N) (X0 S)) (W1 S) ΩD (cstar f) = cstar (Gp' S.toDomSeq (cfgX (X0 S)) (W1 S) ΩD f) :=
  Gp'_cstar S.toDomSeq _ _ _ (hU_triv S) (hW_triv S) (hK_triv S ΩD) f

lemma That_cstar_triv [NeZero N] (ΩD : Set (Site NF)) (u : L2 (BD S ΩD) (VS N 1)) :
    kerApply (kerT S (Subtype.val : BD S ΩD → Site NF) (X0 S) (W1 S) ΩD) (cstarL S u) =
      cstarL S (kerApply (kerT S (Subtype.val : BD S ΩD → Site NF) (X0 S) (W1 S) ΩD) u) := by
  rw [← That_kernel, ← That_kernel, unblk_cstar, QpStar_cstar_triv, Gp_cstar_triv, Gp_cstar_triv, avgL_cstar_triv,
    blk_cstar]

lemma Tinv_cstar_triv [NeZero N] (ΩD : Set (Site NF))
    (hb : Function.Bijective (kerLin (kerT (N := N) S (Subtype.val : BD S ΩD → Site NF) (X0 S) (W1 S) ΩD)))
    (u : L2 (BD S ΩD) (VS N 1)) :
    Tinv S (X0 S) (W1 S) ΩD (cstarL S u) = cstarL S (Tinv S (X0 S) (W1 S) ΩD u) := by
  apply hb.1
  show kerApply _ _ = kerApply _ _
  rw [kerApply_Tinv S _ _ ΩD hb, That_cstar_triv, kerApply_Tinv S _ _ ΩD hb]

/-- **`P` commutes with `f ↦ f^*`** at the trivial configuration. -/
theorem Pop_cstar_triv [NeZero N] (ΩD : Set (Site NF))
    (hb : Function.Bijective (kerLin (kerT (N := N) S (Subtype.val : BD S ΩD → Site NF) (X0 S) (W1 S) ΩD)))
    (f : Site NF → Mat) : Pop S (X0 S) (W1 S) ΩD (cstar f) = cstar (Pop S (X0 S) (W1 S) ΩD f) := by
  show Gp' S.toDomSeq (cfgX (X0 S)) (W1 S) ΩD (QpL S (W1 S) (unblkL S ΩD (Tinv S (X0 S) (W1 S) ΩD
    (blkL S ΩD (avgL S (W1 S) (Gp' S.toDomSeq (cfgX (X0 S)) (W1 S) ΩD (cstar f))))))) = _
  rw [Gp_cstar_triv, avgL_cstar_triv, blk_cstar, Tinv_cstar_triv S ΩD hb, unblk_cstar, QpStar_cstar_triv,
    Gp_cstar_triv]
  rfl

/-- The Hermitian product `⟨f, g⟩ = Σ_xtr(f(x)^*g(x))` of `0`-forms. -/
def herm (f g : Site NF → Mat) : ℂ := P0 (cstar f) g

/-- **`P` is Hermitian** at the trivial configuration. -/
theorem Pop_herm_triv [NeZero N] (ΩD : Set (Site NF))
    (hb : Function.Bijective (kerLin (kerT (N := N) S (Subtype.val : BD S ΩD → Site NF) (X0 S) (W1 S) ΩD)))
    (f g : Site NF → Mat) : herm S (Pop S (X0 S) (W1 S) ΩD f) g = herm S f (Pop S (X0 S) (W1 S) ΩD g) := by
  unfold herm
  rw [← Pop_cstar_triv S ΩD hb, Pop_symm S _ _ ΩD (hK_triv S ΩD) hb]

/-- **`‖Pf‖² = Re⟨Pf, f⟩`** at the trivial configuration. -/
theorem Pop_norm_triv [NeZero N] (ΩD : Set (Site NF))
    (hb : Function.Bijective (kerLin (kerT (N := N) S (Subtype.val : BD S ΩD → Site NF) (X0 S) (W1 S) ΩD)))
    (f : Site NF → Mat) :
    ∑ x, hs2 (Pop S (X0 S) (W1 S) ΩD f x) = (herm S (Pop S (X0 S) (W1 S) ΩD f) f).re := by
  have h1 : herm S (Pop S (X0 S) (W1 S) ΩD f) (Pop S (X0 S) (W1 S) ΩD f) =
      ((∑ x, hs2 (Pop S (X0 S) (W1 S) ΩD f x) : ℝ) : ℂ) := by
    simp only [herm, P0, pairForm0, ConcretePairing.wpair_apply, a1, Complex.ofReal_one, one_pow, one_mul, cstar]
    push_cast
    refine sum_congr rfl fun x _ => ?_
    rw [Schur.ntr_conj_self, hs_sq]
  have hconj : ∀ f g : Site NF → Mat, herm S f g = starRingEnd ℂ (herm S g f) := fun f g => by
    unfold herm; rw [P0_cstar, P0_symm']
  have h2 : herm S (Pop S (X0 S) (W1 S) ΩD f) (Pop S (X0 S) (W1 S) ΩD f) = herm S f (Pop S (X0 S) (W1 S) ΩD f) := by
    rw [Pop_herm_triv S ΩD hb, Pop_idem S _ _ ΩD hb]
  have h3 := congrArg Complex.re (h1.symm.trans h2)
  rw [Complex.ofReal_re] at h3
  rw [h3, hconj, Complex.conj_re]

end SFBounds
end CoreLean

end
