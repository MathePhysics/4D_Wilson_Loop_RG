/-
Bridge (B3) of `thm:small-field` (BALABAN_CORE.tex, `def:operators`(iii)), the projection: the averages `Q'`, `Q'^*` of
the concrete layer in the fine model.

* `ptOfBP`, `ptOfBP_spec`: the point `crd 0 (y)` of the fine lattice of a point of `BPt`;
* `Qpseq_eq`: `(Q'λ)(y) = avgW(W_𝐔)(y)λ` at that point;
* `extB`, `QpseqStar_eq`: `Q'^*μ = QpStar(W_𝐔)(extB μ)` (`avg_pair`, nondegeneracy of the pairing);
* `commute_cinv`: an idempotent commuting with `P` and `T` commutes with `cinv P T`.
-/
import CoreLean.SFOpBridge

open Finset
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace CoreLean
namespace SFBounds

open Lattices SeqDom Blocks SmallFieldBlocks SFBox SFBox.SeqDomBox SmallFieldDecay SmallFieldCoercivity
  PartitionUnity RegularAverages AxialStraightLattice BoxGeometry ConcretePairing SFLocal

variable (S : SeqDom) {N : ℕ}

local notation "NF" => SequenceAverages.N0 S
set_option quotPrecheck false in
local notation "jj" => (S.toDomSeq).sc

/-- The point of the fine lattice of a point of `BPt`. -/
def ptOfBP (b : SequenceIndex.BPt S) : Site NF := SequenceAverages.crd S 0 b.1.2

lemma ptOfBP_spec (b : SequenceIndex.BPt S) :
    ∃ hb : ptOfBP S b ∈ detB S.toDomSeq, toBP S (ptOfBP S b) hb = b := by
  obtain ⟨⟨j, t⟩, hjk, ⟨hΩ, hTL⟩, hn⟩ := b
  obtain ⟨y, rfl⟩ : t ∈ Set.range (Lattices.emb (N := SequenceAverages.N0 S) S.L S.k S.mT) := by
    rw [range_emb S.Lpos (SequenceAverages.N0_eq S)]; exact T_zero_of_mem S hTL
  have hp : ptOfBP S ⟨(j, Lattices.emb S.L S.k S.mT y), hjk, ⟨hΩ, hTL⟩, hn⟩ = y :=
    SequenceAverages.crd_zero_emb S y
  have hlat : InLat S.L j y := (inLat_iff S.Lpos (SequenceAverages.N0_eq S) y).2 hTL
  have hsc : jj y = j := by
    have h1 : j ≤ jj y := ((S.toDomSeq).mem_iff y j).1 (S.mem_toDomSeq_Ω.2 hΩ)
    have h2 : ¬ (j + 1 ≤ jj y) := fun h => hn (S.mem_toDomSeq_Ω.1 (((S.toDomSeq).mem_iff y (j + 1)).2 h))
    omega
  have hy : y ∈ detB S.toDomSeq := (mem_detB_iff_inLat S y).2 (by rw [hsc]; exact hlat)
  rw [hp]
  refine ⟨hy, ?_⟩
  simp only [toBP, hsc]
  rfl

/-- **`Q'` in the fine model**: `(Q'λ)(b) = avgW(W_𝐔)(y)λ` at the point `y` of `b`. -/
lemma Qpseq_eq (U : Config N NF) (lam : Site NF → Matrix (Fin N) (Fin N) ℂ) (b : SequenceIndex.BPt S) :
    SequenceOperators.Qpseq S (fun _ => True) (fun W => LogM (W : Matrix (Fin N) (Fin N) ℂ)) U lam b =
      avgW S.toDomSeq (Wf S U) (ptOfBP S b) lam := by
  obtain ⟨hb, hbb⟩ := ptOfBP_spec S b
  conv_lhs => rw [← hbb]
  exact Qpseq_toBP S U lam hb

/-- The extension of a function on `BPt` to the fine lattice, by `0` off `detB`. -/
def extB (μ : SequenceIndex.BPt S → Matrix (Fin N) (Fin N) ℂ) : Site NF → Matrix (Fin N) (Fin N) ℂ :=
  fun y => if hy : y ∈ detB S.toDomSeq then μ (toBP S y hy) else 0

/-- **`Q'^*` in the fine model**: `Q'^*μ = QpStar(W_𝐔)(extB μ)`. -/
theorem QpseqStar_eq [NeZero N] (U : Config N NF) (μ : SequenceIndex.BPt S → Matrix (Fin N) (Fin N) ℂ) :
    SequenceOperators.QpseqStar S (fun _ => True) (fun W => LogM (W : Matrix (Fin N) (Fin N) ℂ)) U μ =
      QpStar S (Wf S U) (extB S μ) := by
  set a : ℂ := ((SequenceAverages.a0 S : ℝ) : ℂ)
  have ha : a ≠ 0 := Complex.ofReal_ne_zero.2 (SequenceAverages.a0_pos S).ne'
  have hnd := SequenceOperators.pairForm0_nondegenerate (N := N) (n := NF) (SequenceAverages.a0_pos S)
  have hP : ∀ f g : Site NF → Matrix (Fin N) (Fin N) ℂ,
      SequenceOperators.pairForm0 a f g = a ^ 4 * P0 f g := fun f g => by
    simp only [SequenceOperators.pairForm0, P0, wpair_apply, Finset.mul_sum, a1]
    refine Finset.sum_congr rfl fun x _ => ?_
    push_cast; ring
  rw [← sub_eq_zero]
  refine hnd.1 _ fun lam => ?_
  rw [map_sub, LinearMap.sub_apply, SequenceOperators.QpseqStar_spec, hP, ← avg_pair, sub_eq_zero]
  simp only [SequenceIndex.pairB, CriticalConcrete.pairF, wpair_apply]
  rw [sum_BPt, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y hy => ?_
  rw [dif_pos hy, Qpseq_toBP S U lam hy]
  simp only [extB, dif_pos hy]
  have hay : ((toBP S y hy).ay : ℝ) = (S.L : ℝ) ^ (jj y) * SequenceAverages.a0 S := rfl
  rw [hay]
  push_cast
  ring

section Commute

open CompressedInverse

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- An endomorphism commuting with `P` and `T` commutes with `cinv P T` (when `ckern P T` is invertible). -/
theorem commute_cinv (π P T : Module.End ℂ V) (hπP : ∀ x, π (P x) = P (π x)) (hπT : ∀ x, π (T x) = T (π x))
    (hK : IsUnit (ckern P T)) (x : V) : π (cinv P T x) = cinv P T (π x) := by
  set K := ckern P T
  have hπK : Commute π K := LinearMap.ext fun v => by
    simp only [K, Module.End.mul_apply, ckern_apply, map_add, map_sub, hπP, hπT]
  have hc : Commute π ((hK.unit⁻¹ : (Module.End ℂ V)ˣ) : Module.End ℂ V) :=
    Commute.units_inv_right (by rw [hK.unit_spec]; exact hπK)
  have hinv : Ring.inverse K = ((hK.unit⁻¹ : (Module.End ℂ V)ˣ) : Module.End ℂ V) := by
    have := Ring.inverse_unit hK.unit
    rwa [hK.unit_spec] at this
  rw [cinv_apply, cinv_apply]
  change π (P (Ring.inverse K x)) = P (Ring.inverse K (π x))
  rw [hπP, hinv]
  have := congrArg (fun F : Module.End ℂ V => F x) hc.eq
  simp only [Module.End.mul_apply] at this
  rw [this]

end Commute

/-! ### The projection `P` of the fine model on the torus -/

/-- The restriction of a `0`-form to the points of `𝐁`, as a function on `BPt`. -/
def RpL : (Site NF → Matrix (Fin N) (Fin N) ℂ) →ₗ[ℂ] (SequenceIndex.BPt S → Matrix (Fin N) (Fin N) ℂ) where
  toFun ν b := ν (ptOfBP S b)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- `extB` as a linear map. -/
def extBL : (SequenceIndex.BPt S → Matrix (Fin N) (Fin N) ℂ) →ₗ[ℂ] (Site NF → Matrix (Fin N) (Fin N) ℂ) where
  toFun := extB S
  map_add' μ μ' := by funext y; simp only [extB, Pi.add_apply]; split_ifs <;> simp
  map_smul' c μ := by funext y; simp only [extB, Pi.smul_apply, RingHom.id_apply]; split_ifs <;> simp

lemma ptOfBP_toBP (y : Site NF) (hy : y ∈ detB S.toDomSeq) : ptOfBP S (toBP S y hy) = y :=
  SequenceAverages.crd_zero_emb S y

open scoped Classical in
lemma BD_univ : BD S (Set.univ : Set (Site NF)) = detB S.toDomSeq := by
  ext y; simp [BD]

/-- The block operator `M' = Q'G'²Q'^*` on the functions on `BPt`. -/
def Mc (X : Fin 4 → Site NF → Matrix (Fin N) (Fin N) ℂ) (W : Site NF → Site NF → (Matrix (Fin N) (Fin N) ℂ)ˣ) :
    Module.End ℂ (SequenceIndex.BPt S → Matrix (Fin N) (Fin N) ℂ) :=
  RpL S ∘ₗ avgL S W ∘ₗ Gp' S.toDomSeq (cfgX X) W Set.univ ∘ₗ Gp' S.toDomSeq (cfgX X) W Set.univ ∘ₗ QpL S W ∘ₗ
    extBL S

open scoped Classical in
/-- `T̂ = blk Q'G'²Q'^* unblk`: the operator of the kernel `T̂` of the fine model. -/
lemma kerApply_kerT [NeZero N] (X : Fin 4 → Site NF → Matrix (Fin N) (Fin N) ℂ)
    (W : Site NF → Site NF → (Matrix (Fin N) (Fin N) ℂ)ˣ) (ΩD : Set (Site NF)) (v : L2 (BD S ΩD) (VS N 1)) :
    kerApply (kerT S (Subtype.val : BD S ΩD → Site NF) X W ΩD) v =
      blkL S ΩD (avgL S W (Gp' S.toDomSeq (cfgX X) W ΩD (Gp' S.toDomSeq (cfgX X) W ΩD
        (QpL S W (unblkL S ΩD v))))) := by
  set G := Gp' S.toDomSeq (cfgX X) W ΩD
  have hsum : QpL S W (unblkL S ΩD v) = ∑ c' : BD S ΩD,
      lamZ S W c'.1 (((((S.L : ℝ) ^ (4 * jj c'.1)) : ℝ) : ℂ)⁻¹ • proj (v.ofLp c')) := by
    rw [sum_lamZ]; rfl
  refine PiLp.ext fun c => ?_
  rw [kerApply_apply, hsum, map_sum G, map_sum G, map_sum (avgL S W)]
  change _ = embL ((∑ c' : BD S ΩD, avgL S W (G (G (lamZ S W c'.1
    (((((S.L : ℝ) ^ (4 * jj c'.1)) : ℝ) : ℂ)⁻¹ • proj (v.ofLp c')))))) c.1)
  rw [Finset.sum_apply, map_sum embL]
  refine Finset.sum_congr rfl fun c' _ => ?_
  simp only [kerT_apply, That, embL, LinearMap.coe_mk, AddHom.coe_mk, lamZ_smul, map_smul, avgL, avgW_smul]
  rfl

open scoped Classical in
/-- **`P` of the fine model on the torus**: `P = G'Q'^*M'^{-1}Q'G'` with `M' = Q'G'²Q'^*` on the functions on `BPt`, when
`T̂` and `M'` are invertible. -/
theorem Pop_eq [NeZero N] (X : Fin 4 → Site NF → Matrix (Fin N) (Fin N) ℂ)
    (W : Site NF → Site NF → (Matrix (Fin N) (Fin N) ℂ)ˣ)
    (hT : Function.Bijective (kerLin (kerT S (Subtype.val : BD S Set.univ → Site NF) X W Set.univ)))
    (hM : IsUnit (Mc S X W)) (ν : Site NF → Matrix (Fin N) (Fin N) ℂ) :
    Pop S X W Set.univ ν = Gp' S.toDomSeq (cfgX X) W Set.univ (QpL S W (extBL S (Ring.inverse (Mc S X W)
      (RpL S (avgL S W (Gp' S.toDomSeq (cfgX X) W Set.univ ν)))))) := by
  set G := Gp' S.toDomSeq (cfgX X) W Set.univ
  set g := avgL S W (G ν)
  set u := Tinv S X W Set.univ (blkL S Set.univ g)
  set w := unblkL S Set.univ u
  have h1 := kerApply_Tinv S X W Set.univ hT (blkL S Set.univ g)
  rw [kerApply_kerT] at h1
  -- the values on `𝐁`
  have hR : RpL S (avgL S W (G (G (QpL S W w)))) = RpL S g := by
    funext b
    obtain ⟨hb, -⟩ := ptOfBP_spec S b
    have hbD : ptOfBP S b ∈ BD S Set.univ := by rw [BD_univ]; exact hb
    have := congrArg (fun v : L2 (BD S Set.univ) (VS N 1) => proj (v.ofLp ⟨ptOfBP S b, hbD⟩)) h1
    simp only [blkL, proj_emb, RpL, LinearMap.coe_mk, AddHom.coe_mk, WithLp.ofLp_toLp] at this ⊢
    exact this
  -- `w` lives on `𝐁`
  have hw : extBL S (RpL S w) = w := by
    funext y
    simp only [extBL, extB, RpL, LinearMap.coe_mk, AddHom.coe_mk]
    by_cases hy : y ∈ detB S.toDomSeq
    · rw [dif_pos hy, ptOfBP_toBP]
    · rw [dif_neg hy]
      have hyD : y ∉ BD S Set.univ := by rw [BD_univ]; exact hy
      simp only [w, unblkL, LinearMap.coe_mk, AddHom.coe_mk, extBD, dif_neg hyD]
  have hMw : Mc S X W (RpL S w) = RpL S g := by
    rw [← hR]; simp only [Mc, LinearMap.comp_apply, hw]; rfl
  have hinv : Ring.inverse (Mc S X W) (RpL S g) = RpL S w := by
    rw [← hMw]
    have := congrArg (fun F : Module.End ℂ (SequenceIndex.BPt S → Matrix (Fin N) (Fin N) ℂ) => F (RpL S w))
      (Ring.inverse_mul_cancel _ hM)
    simpa only [Module.End.mul_apply, Module.End.one_apply] using this
  rw [hinv, hw]
  rfl

/-- `cinv π(cπM) = c⁻¹πM⁻¹` for an idempotent `π` commuting with an invertible `M`. -/
lemma cinv_proj_smul {V : Type*} [AddCommGroup V] [Module ℂ V] (π M : Module.End ℂ V) (hπ : ∀ x, π (π x) = π x)
    (hπM : ∀ x, π (M x) = M (π x)) (hM : IsUnit M) {c : ℂ} (hc : c ≠ 0) :
    CompressedInverse.cinv π (c • (π * M)) = c⁻¹ • (π * Ring.inverse M) := by
  rw [cinv_smul π _ hπ hc]
  congr 1
  have hk : CompressedInverse.ckern π (π * M) = CompressedInverse.ckern π M := by
    refine LinearMap.ext fun x => ?_
    simp only [CompressedInverse.ckern_apply, Module.End.mul_apply, hπ]
  have h1 : CompressedInverse.cinv π (π * M) = CompressedInverse.cinv π M := by
    unfold CompressedInverse.cinv; rw [hk]
  have hK1 : IsUnit (CompressedInverse.ckern 1 M) := by
    have : CompressedInverse.ckern 1 M = M := by simp [CompressedInverse.ckern]
    rw [this]; exact hM
  rw [h1, show π = π * 1 from (mul_one π).symm, cinv_proj π 1 M hπ (fun _ => rfl) hπM hK1, mul_one,
    CompressedInverse.cinv_one]

/-- **`P = πP_fine` on the torus** (bridge (B3) for the projection): at `𝐔 = e^{iX}`, `𝖺 = 1`, `Ω_D = 𝕋`, if the maps
`Ad` of the links and of the transports `W_𝐔` commute with `π`, the compressed kernel of `Δ'_𝖺(𝐔)`, `T̂` and `M'`
are invertible, then the projection `P` of the concrete layer is `π` after `Pop` of the fine model. -/
theorem Ps_eq [NeZero N] {G : GaugeGroup N} (hG : G.LieInput) (X : Fin 4 → Site NF → Matrix (Fin N) (Fin N) ℂ)
    (hU : ∀ μ x Z, piProj hG (Ad (cfgX X μ x) Z) = Ad (cfgX X μ x) (piProj hG Z))
    (hW : ∀ y ∈ detB S.toDomSeq, ∀ x ∈ Blk S.toDomSeq (jj y) y, ∀ Z,
      piProj hG (Ad (Wf S (cfgX X) y x) Z) = Ad (Wf S (cfgX X) y x) (piProj hG Z))
    (hK : IsUnit (CompressedInverse.ckern (piD Set.univ) (DeltaS S.toDomSeq (cfgX X) (Wf S (cfgX X)))))
    (hT : Function.Bijective (kerLin (kerT S (Subtype.val : BD S Set.univ → Site NF) X (Wf S (cfgX X)) Set.univ)))
    (hM : IsUnit (Mc S X (Wf S (cfgX X)))) :
    SequenceOperators.Ps S hG (fun _ => True) (fun W => LogM (W : Matrix (Fin N) (Fin N) ℂ)) (cfgX X) 1 Set.univ =
      SequenceOperators.piF0 hG Set.univ * Pop S X (Wf S (cfgX X)) Set.univ := by
  set W := Wf S (cfgX X)
  set a : ℂ := ((SequenceAverages.a0 S : ℝ) : ℂ)
  have ha : a ≠ 0 := Complex.ofReal_ne_zero.2 (SequenceAverages.a0_pos S).ne'
  set π := SequenceOperators.piF0 hG (Set.univ : Set (Site NF))
  set πB := SequenceOperators.piFun hG (SequenceIndex.BPt S)
  set G' := Gp' S.toDomSeq (cfgX X) W Set.univ
  have hcomm := DeltaS_comm_pi S hG (cfgX X) W hU hW
  have hπx : ∀ (g : Site NF → Matrix (Fin N) (Fin N) ℂ) x, π g x = piProj hG (g x) := fun g x => by
    simp [π, SequenceOperators.piF0, Set.indicator_apply]
  have hp0 : piProj hG (0 : Matrix (Fin N) (Fin N) ℂ) = 0 := by
    simpa using proj_smul hG 0 (0 : Matrix (Fin N) (Fin N) ℂ)
  have hπ : ∀ f, π (π f) = π f := fun f => SequenceOperators.piF0_idem hG _ f
  have hπB : ∀ μ, πB (πB μ) = πB μ := fun μ => SequenceOperators.piFun_idem hG _ μ
  have hGp : ∀ f, SequenceOperators.Gp S hG (fun _ => True) (fun W => LogM (W : Matrix (Fin N) (Fin N) ℂ))
      (cfgX X) 1 Set.univ f = a ^ 2 • π (G' f) := fun f => by
    rw [Gp_eq S hG (cfgX X) Set.univ hcomm hK]; rfl
  have hπD : ∀ f, π (piD Set.univ f) = piD Set.univ (π f) := fun f => by
    funext x; simp [piD_apply, hπx]
  have hπG : ∀ f, π (G' f) = G' (π f) := fun f => commute_cinv π _ _ hπD hcomm hK f
  have hQ : ∀ f, SequenceOperators.Qpseq S (fun _ => True) (fun W => LogM (W : Matrix (Fin N) (Fin N) ℂ))
      (cfgX X) f = RpL S (avgL S W f) := fun f => funext fun b => Qpseq_eq S (cfgX X) f b
  have hQs : ∀ μ, SequenceOperators.QpseqStar S (fun _ => True) (fun W => LogM (W : Matrix (Fin N) (Fin N) ℂ))
      (cfgX X) μ = QpL S W (extBL S μ) := fun μ => QpseqStar_eq S (cfgX X) μ
  have hR : ∀ f, RpL S (avgL S W (π f)) = πB (RpL S (avgL S W f)) := fun f => by
    funext b
    obtain ⟨hb, -⟩ := ptOfBP_spec S b
    obtain ⟨hlat, hjk, -⟩ := detB_facts S hb
    simp only [RpL, LinearMap.coe_mk, AddHom.coe_mk, πB, SequenceOperators.piFun, avgL, avgW]
    rw [proj_smul, proj_sum]
    congr 1
    refine Finset.sum_congr rfl fun o ho => ?_
    rw [hπx, hW _ hb _ (phi_mem (S := S.toDomSeq) _ hjk hlat ho)]
  have hWi : ∀ y ∈ detB S.toDomSeq, ∀ x ∈ Blk S.toDomSeq (jj y) y, ∀ Z,
      piProj hG (Ad (W y x)⁻¹ Z) = Ad (W y x)⁻¹ (piProj hG Z) := fun y hy x hx Z => by
    have h := hW y hy x hx (Ad (W y x)⁻¹ Z)
    rw [← Ad_mul, mul_inv_cancel, BlockAverageTransports.Ad_one] at h
    have h2 := congrArg (Ad (W y x)⁻¹) h
    rw [← Ad_mul, inv_mul_cancel, BlockAverageTransports.Ad_one] at h2
    exact h2.symm
  have hE : ∀ μ, QpL S W (extBL S (πB μ)) = π (QpL S W (extBL S μ)) := fun μ => by
    funext x
    rw [hπx]
    simp only [QpL, LinearMap.coe_mk, AddHom.coe_mk, QpStar, extBL, extB, πB, SequenceOperators.piFun]
    have hbc := bc_mem_detB S x
    rw [dif_pos hbc, dif_pos hbc, hWi _ hbc _ (mem_blk_bc S x)]
  set Mc' := Mc S X W
  have hMcπ : ∀ μ, πB (Mc' μ) = Mc' (πB μ) := fun μ => by
    show πB (RpL S (avgL S W (G' (G' (QpL S W (extBL S μ)))))) =
      RpL S (avgL S W (G' (G' (QpL S W (extBL S (πB μ))))))
    rw [← hR, hπG, hπG, hE]
  have hMop : CompressedInverse.Mop (SequenceOperators.Gp S hG (fun _ => True)
      (fun W => LogM (W : Matrix (Fin N) (Fin N) ℂ)) (cfgX X) 1 Set.univ)
      (SequenceOperators.Qpseq S (fun _ => True) (fun W => LogM (W : Matrix (Fin N) (Fin N) ℂ)) (cfgX X))
      (SequenceOperators.QpseqStar S (fun _ => True) (fun W => LogM (W : Matrix (Fin N) (Fin N) ℂ)) (cfgX X)) =
      (a ^ 2 * a ^ 2) • (πB * Mc') := by
    refine LinearMap.ext fun μ => ?_
    simp only [CompressedInverse.Mop, LinearMap.comp_apply, hQs, hGp, hQ, map_smul, smul_smul,
      LinearMap.smul_apply, Module.End.mul_apply]
    congr 1
    rw [← hπG (G' (QpL S W (extBL S μ))), hπ, hR]
    rfl
  have hMi : ∀ m, πB (Ring.inverse Mc' m) = Ring.inverse Mc' (πB m) := fun m => by
    have hcM : Commute πB Mc' := LinearMap.ext fun v => by
      show πB (Mc' v) = Mc' (πB v)
      exact hMcπ v
    have hc : Commute πB ((hM.unit⁻¹ : (Module.End ℂ _)ˣ) : Module.End ℂ _) :=
      Commute.units_inv_right (by rw [hM.unit_spec]; exact hcM)
    have hinv : Ring.inverse Mc' = ((hM.unit⁻¹ : (Module.End ℂ _)ˣ) : Module.End ℂ _) := by
      have := Ring.inverse_unit hM.unit
      rwa [hM.unit_spec] at this
    rw [hinv]
    have := congrArg (fun F : Module.End ℂ (SequenceIndex.BPt S → Matrix (Fin N) (Fin N) ℂ) => F m) hc.eq
    simpa only [Module.End.mul_apply] using this
  have ha4 : a ^ 2 * a ^ 2 ≠ 0 := by positivity
  refine LinearMap.ext fun ν => ?_
  rw [SequenceOperators.Ps, CompressedInverse.Xop_apply, hMop, cinv_proj_smul πB Mc' hπB hMcπ hM ha4]
  simp only [hGp, hQ, hQs, map_smul, LinearMap.smul_apply, Module.End.mul_apply, smul_smul]
  rw [hR, hMi, hπB, ← hMi, hE, ← hπG, hπ, Pop_eq S X W hT hM]
  have hs : a ^ 2 * (a ^ 2 * (a ^ 2 * a ^ 2)⁻¹) = 1 := by field_simp
  rw [hs, one_smul]

/-- **Bridge (B3) for `P` on the torus**: there is `c > 0` such that for a regular field `X` with values in `𝔤^c` and
`α₁L < c` (and `G ⊂ G^c`), when the compressed kernel of `Δ'_𝖺(𝐔)`, `T̂` and `M'` are invertible, the projection `P`
of the concrete layer at `𝐔 = e^{iX}`, `𝖺 = 1`, `Ω_D = 𝕋`, is `πPop` (`Ps_eq`, `Wf_mem_Gc`, `proj_Ad`). -/
theorem Ps_bridge [NeZero N] (G : GaugeGroup N) (hGc : IsClosed G.mats) (hG : G.LieInput) :
    ∃ c : ℝ, 0 < c ∧ ∀ (hRM : 2 * (S.L : ℝ) ≤ ((S.R * S.L ^ S.mM : ℕ) : ℝ))
      (hn : ∀ l, 4 * SequenceAverages.hS S + 4 ≤ MultiscaleAverages.nn (SequenceAverages.hS S) S.mT S.k l)
      (hGG : G.carrier ≤ G.complexified)
      {X : Fin 4 → Site NF → Matrix (Fin N) (Fin N) ℂ} {α₁ : ℝ} (hX : RegField S X α₁) (hα0 : 0 ≤ α₁)
      (hXc : ∀ μ x, X μ x ∈ G.lieC) (hαc : α₁ * S.L < c)
      (hK : IsUnit (CompressedInverse.ckern (piD Set.univ) (DeltaS S.toDomSeq (cfgX X) (Wf S (cfgX X)))))
      (hT : Function.Bijective (kerLin (kerT S (Subtype.val : BD S Set.univ → Site NF) X (Wf S (cfgX X))
        Set.univ)))
      (hM : IsUnit (Mc S X (Wf S (cfgX X)))),
      SequenceOperators.Ps S hG (fun _ => True) (fun W => LogM (W : Matrix (Fin N) (Fin N) ℂ)) (cfgX X) 1 Set.univ =
        SequenceOperators.piF0 hG Set.univ * Pop S X (Wf S (cfgX X)) Set.univ := by
  obtain ⟨c, hc, hW⟩ := Wf_mem_Gc S G hGc
  exact ⟨c, hc, fun hRM hn hGG X α₁ hX hα0 hXc hαc hK hT hM =>
    Ps_eq S hG X (fun μ x Z => proj_Ad hG (cfgX_mem_Gc S hXc μ x) Z)
      (fun y hy x hx Z => proj_Ad hG (hW hRM hn hGG hX hα0 hXc hαc y hy x hx) Z) hK hT hM⟩

end SFBounds
end CoreLean

end
