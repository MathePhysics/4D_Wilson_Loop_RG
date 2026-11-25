/-
Bridge (B3) of `thm:small-field` (BALABAN_CORE.tex, `def:operators`), first part: the operator `Δ'_𝖺` of the concrete
layer at `𝖺 = 1` is `a₀^{-2}` times the operator `Δ'_𝖺(𝐔)` of the fine model with the transports `W_𝐔`.

* `toBP`, `sum_BPt`: the points `𝐁` of `SequenceIndex` (`BPt`) are the pairs `(j(y), ef y)`, `y ∈ detB`;
* `Qpseq_toBP`: `(Q'λ)(y) = avgW(W_𝐔)(y)λ` (`qpcomp_avgW`);
* `pairForm0_DeltaP`: `⟨Δ'_𝖺λ, λ'⟩_{a₀} = a₀²Φ(λ, λ')` at `𝖺 = 1` (`D0L_transpose`, `QpseqStar_spec`, `a_y = L^{j(y)}a₀`);
* `DeltaP_eq`: `Δ'_𝖺 = a₀^{-2}DeltaS(𝐔, W_𝐔)` (`DeltaS_spec`, nondegeneracy of the pairing).
-/
import CoreLean.SFAvgBridge
import CoreLean.SmallFieldOperator

open Finset
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace CoreLean
namespace SFBounds

open Lattices SeqDom Blocks SmallFieldBlocks SFBox SFBox.SeqDomBox SmallFieldDecay SmallFieldCoercivity
  PartitionUnity RegularAverages AxialStraightLattice BoxGeometry ConcretePairing

variable (S : SeqDom) {N : ℕ}

local notation "NF" => SequenceAverages.N0 S
set_option quotPrecheck false in
local notation "jj" => (S.toDomSeq).sc

/-- The point of `𝐁` of `SequenceIndex` of a point `y ∈ detB`: `(j(y), ef y)`. -/
def toBP (y : Site NF) (hy : y ∈ detB S.toDomSeq) : SequenceIndex.BPt S :=
  ⟨(jj y, S.ef y), by
    obtain ⟨-, hjk, hTL, hΩ, hn⟩ := detB_facts S hy
    exact ⟨hjk, ⟨hΩ, hTL⟩, hn⟩⟩

/-- **The sum over `BPt` as the sum over `detB`.** -/
lemma sum_BPt {M : Type*} [AddCommMonoid M] (F : SequenceIndex.BPt S → M) :
    ∑ b : SequenceIndex.BPt S, F b = ∑ y ∈ detB S.toDomSeq, if hy : y ∈ detB S.toDomSeq then F (toBP S y hy) else 0 := by
  have hinj := emb_injective (N := SequenceAverages.N0 S) (L := S.L) (k := S.k) (m := S.mT) S.Lpos
    (SequenceAverages.N0_eq S)
  symm
  refine Finset.sum_bij (fun y hy => toBP S y hy) (fun _ _ => mem_univ _) (fun y hy y' hy' h => ?_)
    (fun b _ => ?_) (fun y hy => by simp only [dif_pos hy])
  · have h' := congrArg Subtype.val h
    simp only [toBP, Prod.mk.injEq] at h'
    exact hinj h'.2
  · obtain ⟨⟨j, t⟩, hjk, ⟨hΩ, hTL⟩, hn⟩ := b
    obtain ⟨y, rfl⟩ : t ∈ Set.range (Lattices.emb (N := SequenceAverages.N0 S) S.L S.k S.mT) := by
      rw [range_emb S.Lpos (SequenceAverages.N0_eq S)]; exact T_zero_of_mem S hTL
    have hlat : InLat S.L j y := (inLat_iff S.Lpos (SequenceAverages.N0_eq S) y).2 hTL
    have hsc : jj y = j := by
      have h1 : j ≤ jj y := ((S.toDomSeq).mem_iff y j).1 (S.mem_toDomSeq_Ω.2 hΩ)
      have h2 : ¬ (j + 1 ≤ jj y) := fun h => hn (S.mem_toDomSeq_Ω.1 (((S.toDomSeq).mem_iff y (j + 1)).2 h))
      omega
    have hy : y ∈ detB S.toDomSeq := (mem_detB_iff_inLat S y).2 (by rw [hsc]; exact hlat)
    refine ⟨y, hy, ?_⟩
    simp only [toBP, hsc]
    rfl

/-- `(Q'λ)(y) = avgW(W_𝐔)(y)λ` at the point of `BPt` of `y ∈ detB`. -/
lemma Qpseq_toBP (U : Config N NF) (lam : Site NF → Matrix (Fin N) (Fin N) ℂ) {y : Site NF}
    (hy : y ∈ detB S.toDomSeq) :
    SequenceOperators.Qpseq S (fun _ => True) (fun W => LogM (W : Matrix (Fin N) (Fin N) ℂ)) U lam (toBP S y hy) =
      avgW S.toDomSeq (Wf S U) y lam := by
  rw [SequenceOperators.Qpseq_apply]
  exact qpcomp_avgW S U lam hy

lemma D0L_eq (a : ℂ) (U : Config N NF) (lam : Site NF → Matrix (Fin N) (Fin N) ℂ) (μ : Fin 4) (x : Site NF) :
    SequenceOperators.D0L a U lam μ x = a⁻¹ • DU U lam μ x := by
  simp [SequenceOperators.D0L_apply, D0, Dfw, DU]

/-- **The form of `Δ'_𝖺` at `𝖺 = 1`**: `⟨Δ'_𝖺λ, λ'⟩_{a₀} = a₀²Φ(λ, λ')` with the transports `W_𝐔`. -/
theorem pairForm0_DeltaP [NeZero N] (U : Config N NF) (lam lam' : Site NF → Matrix (Fin N) (Fin N) ℂ) :
    SequenceOperators.pairForm0 ((SequenceAverages.a0 S : ℝ) : ℂ)
        (SequenceOperators.DeltaP S (fun _ => True) (fun W => LogM (W : Matrix (Fin N) (Fin N) ℂ)) U 1 lam) lam' =
      ((SequenceAverages.a0 S : ℝ) : ℂ) ^ 2 * Phi S.toDomSeq U (Wf S U) lam lam' := by
  set a : ℂ := ((SequenceAverages.a0 S : ℝ) : ℂ)
  have ha : a ≠ 0 := Complex.ofReal_ne_zero.2 (SequenceAverages.a0_pos S).ne'
  simp only [SequenceOperators.DeltaP, LinearMap.add_apply, LinearMap.comp_apply, map_add, LinearMap.add_apply]
  -- the Laplacian
  have h1 : SequenceOperators.pairForm0 a (SequenceOperators.Ds1L a U (SequenceOperators.D0L a U lam)) lam' =
      a ^ 2 * ∑ x, ∑ μ : Fin 4, ntr (DU U lam μ x * DU U lam' μ x) := by
    rw [wpair_symm, ← SequenceOperators.D0L_transpose, pairForm1_apply']
    simp only [wpair_apply, D0L_eq, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun μ _ => ?_
    rw [smul_mul_smul_comm, ntr_smul, ntr, ntr, Matrix.trace_mul_comm (DU U lam' μ x)]
    field_simp
  -- the constraint
  have h2 : SequenceOperators.pairForm0 a
      (SequenceOperators.constraintOp0 S (fun _ => True) (fun W => LogM (W : Matrix (Fin N) (Fin N) ℂ)) U 1 lam) lam' =
      a ^ 2 * ∑ y ∈ detB S.toDomSeq, ((SequenceOperators.aseq 1 S.L (jj y) * (S.L : ℝ) ^ (2 * jj y) : ℝ) : ℂ) *
        ntr (avgW S.toDomSeq (Wf S U) y lam * avgW S.toDomSeq (Wf S U) y lam') := by
    rw [SequenceOperators.constraintOp0, LinearMap.comp_apply, LinearMap.comp_apply, SequenceOperators.QpseqStar_spec]
    simp only [SequenceIndex.pairB, CriticalConcrete.pairF, wpair_apply, mulW, LinearMap.coe_mk, AddHom.coe_mk,
      smul_mul_assoc, ntr_smul]
    rw [sum_BPt, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y hy => ?_
    rw [dif_pos hy, Qpseq_toBP S U lam hy, Qpseq_toBP S U lam' hy]
    have hay : ((toBP S y hy).ay : ℝ) = (S.L : ℝ) ^ (jj y) * SequenceAverages.a0 S := rfl
    have hay' : (((toBP S y hy).ay : ℝ) : ℂ) = ((S.L : ℝ) : ℂ) ^ (jj y) * a := by
      rw [hay]; push_cast; ring
    have hj : (toBP S y hy).1.1 = jj y := rfl
    rw [hj]
    push_cast
    rw [hay']
    field_simp
    push_cast
    ring
  rw [h1, h2]
  unfold Phi
  rw [mul_add]
  rfl

/-- **`Δ'_𝖺 = a₀^{-2}Δ'_𝖺(𝐔)`** (bridge (B3)): at `𝖺 = 1` the operator of the concrete layer is `a₀^{-2}` times the
operator `DeltaS` of the fine model with the transports `W_𝐔`. -/
theorem DeltaP_eq [NeZero N] (U : Config N NF) :
    SequenceOperators.DeltaP S (fun _ => True) (fun W => LogM (W : Matrix (Fin N) (Fin N) ℂ)) U 1 =
      (((SequenceAverages.a0 S : ℝ) : ℂ) ^ 2)⁻¹ • DeltaS S.toDomSeq U (Wf S U) := by
  set a : ℂ := ((SequenceAverages.a0 S : ℝ) : ℂ)
  have ha : a ≠ 0 := Complex.ofReal_ne_zero.2 (SequenceAverages.a0_pos S).ne'
  have hnd := SequenceOperators.pairForm0_nondegenerate (N := N) (n := NF) (SequenceAverages.a0_pos S)
  have hP : ∀ f g : Site NF → Matrix (Fin N) (Fin N) ℂ,
      SequenceOperators.pairForm0 a f g = a ^ 4 * P0 f g := fun f g => by
    simp only [SequenceOperators.pairForm0, P0, wpair_apply, Finset.mul_sum, a1]
    refine Finset.sum_congr rfl fun x _ => ?_
    push_cast; ring
  refine LinearMap.ext fun lam => ?_
  rw [← sub_eq_zero]
  refine hnd.1 _ fun lam' => ?_
  rw [map_sub, LinearMap.sub_apply, pairForm0_DeltaP, LinearMap.smul_apply, map_smul, LinearMap.smul_apply,
    hP, DeltaS_spec, smul_eq_mul]
  field_simp
  ring

end SFBounds
end CoreLean

end
