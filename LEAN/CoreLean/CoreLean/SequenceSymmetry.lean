/-
The symmetry of the operators of a sequence and of a pair for the pairings (BALABAN_CORE.tex `615c66b253fe`, the remark
after `def:landau-operators`: "The operators `Δ_𝖺`, `Δ'_π`, and `Δ^{(2)}_π` are symmetric with respect to
`eq:pairing` ... hence so are `G_π`, `G_1`, `QG_πQ^*`, and `QG_1Q^*`"), with the compressed inverses, and
`thm:critical`(iii), `G̃J = 0`, for the concrete operators in the general compressed case.

* `pairForm0_symm`, `piF0_symm`, `mulW_symm`, `QsWQ_symm`: the pairing of `0`-forms, the compression of `0`-forms, and
  the weights are symmetric; `Q^*WQ` is symmetric for a symmetric `W`.
* `Lap_symm`, `constraintOp0_symm`, `DeltaP_symm`: `Δ_U = D^*D`, `Q'^*𝖺Q'`, `Δ'_𝖺`; `Gp_symm`: `G'`; `Mop_symm`,
  `MinvP_symm`: `Q'G'^2Q'^*` and its inverse; `Rs_symm`: `R`; `DRD_symm`: `DRD^*`; `PcalT_transpose`: `𝒫^T` is the
  transpose of `𝒫`.
* `hess_symm`: `Δ(U)` on the compressed forms (`pair1_hessOp_symm`, whose forms have values in `𝔤^c`);
  `constraintOp_symm`, `DA_symm`: `Q^*𝖺Q`, `Δ_𝖺` on the compressed forms; `Gs_symm`, `Gc_symm`, `Gpi_symm`: `G`, `G_c`,
  `G_π`; `QGcQs_symm`, `MinvC_symm`: `QG_cQ^*` and its inverse.
* `Gtilde_J_sequence`: `G̃J = 0` for a `J` which annihilates the compressed forms `δ` with `Qδ = 0`, from
  `CriticalCompressed.Gtilde_J_c`.
-/
import CoreLean.CriticalSequence
import CoreLean.Potentials

open LinearMap (BilinForm)

noncomputable section

namespace CoreLean
namespace SequenceSymmetry

open Lattices SequenceIndex ConcretePairing SequenceAverages SequenceOperators CompressedInverse PairConcrete
  CriticalSequence

variable {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ

/-! ### Generalities -/

lemma pairForm0_symm {n : ℕ} [NeZero n] (a : ℂ) (l l' : Form0 N n) : pairForm0 a l l' = pairForm0 a l' l :=
  wpair_symm _ _ _

lemma mulW_symm {ι : Type*} [Fintype ι] (v w : ι → ℂ) (f g : ι → Mat) :
    wpair v (mulW w f) g = wpair v f (mulW w g) := by
  simp only [wpair_apply, mulW, LinearMap.coe_mk, AddHom.coe_mk, smul_mul_assoc, mul_smul_comm]

/-- `Q^*WQ` is symmetric for a symmetric `W`. -/
lemma QsWQ_symm {E F : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F] (BE : BilinForm ℂ E)
    (BF : BilinForm ℂ F) (hEs : ∀ x y, BE x y = BE y x) (hFs : ∀ u v, BF u v = BF v u) (Q : E →ₗ[ℂ] F)
    (Qs : F →ₗ[ℂ] E) (hQ : ∀ μ A, BE (Qs μ) A = BF μ (Q A)) (W : F →ₗ[ℂ] F) (hW : ∀ u v, BF (W u) v = BF u (W v))
    (x y : E) : BE (Qs (W (Q x))) y = BE x (Qs (W (Q y))) := by
  calc BE (Qs (W (Q x))) y = BF (W (Q x)) (Q y) := hQ _ _
    _ = BF (Q x) (W (Q y)) := hW _ _
    _ = BF (W (Q y)) (Q x) := hFs _ _
    _ = BE (Qs (W (Q y))) x := (hQ _ _).symm
    _ = BE x (Qs (W (Q y))) := hEs _ _

section Comp

variable [NeZero N] {G : GaugeGroup N} (hG : G.LieInput)

lemma piF0_symm {n : ℕ} [NeZero n] (ΩD : Set (Site n)) (a : ℂ) (l l' : Form0 N n) :
    pairForm0 a (piF0 hG ΩD l) l' = pairForm0 a l (piF0 hG ΩD l') := by
  simp only [wpair_apply]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : x ∈ ΩD
  · simp [piF0, Set.indicator_apply, hx, ntr_proj_symm hG]
  · simp [piF0, Set.indicator_apply, hx, ntr]

end Comp

/-! ### The operators on `0`-forms -/

lemma Lap_symm {n : ℕ} [NeZero n] (a : ℂ) (U : Config N n) (l l' : Form0 N n) :
    pairForm0 a (Ds1L a U (D0L a U l)) l' = pairForm0 a l (Ds1L a U (D0L a U l')) := by
  calc pairForm0 a (Ds1L a U (D0L a U l)) l' = pairForm0 a l' (Ds1L a U (D0L a U l)) := pairForm0_symm _ _ _
    _ = pairForm1 a (D0L a U l') (D0L a U l) := (D0L_transpose a U l' _).symm
    _ = pairForm1 a (D0L a U l) (D0L a U l') := pairForm1_symm _ _ _
    _ = pairForm0 a l (Ds1L a U (D0L a U l')) := D0L_transpose a U l _

variable (S : SeqDom)

section Sequence

variable [NeZero N] {G : GaugeGroup N} (hG : G.LieInput) (d : Data S N)

lemma constraintOp0_symm (l l' : Form0 N (SequenceAverages.N0 S)) :
    pairForm0 (aC S) (constraintOp0 S d.inN d.log d.U d.aa l) l' =
      pairForm0 (aC S) l (constraintOp0 S d.inN d.log d.U d.aa l') :=
  QsWQ_symm (pairForm0 (aC S)) (pairB S N) (pairForm0_symm _) (wpair_symm _) (Qpseq S d.inN d.log d.U)
    (QpseqStar S d.inN d.log d.U) (QpseqStar_spec S d.inN d.log d.U) _ (mulW_symm _ _) l l'

lemma DeltaP_symm (l l' : Form0 N (SequenceAverages.N0 S)) :
    pairForm0 (aC S) (DeltaP S d.inN d.log d.U d.aa l) l' = pairForm0 (aC S) l (DeltaP S d.inN d.log d.U d.aa l') := by
  simp only [DeltaP, LinearMap.add_apply, LinearMap.comp_apply, map_add]
  rw [Lap_symm, constraintOp0_symm]

/-- The hypothesis that `(Δ'_𝖺)^{-1}` exists on the compressed `0`-forms. -/
abbrev UnitG' : Prop := IsUnit (ckern (piF0 hG d.ΩD) (DeltaP S d.inN d.log d.U d.aa))

/-- The hypothesis that `(Q'G'^2Q'^*)^{-1}` exists on the compressed functions on `𝐁`. -/
abbrev UnitM' : Prop := IsUnit (ckern (piFun hG (BPt S))
  (Mop (Gp S hG d.inN d.log d.U d.aa d.ΩD) (Qpseq S d.inN d.log d.U) (QpseqStar S d.inN d.log d.U)))

lemma Gp_symm (hK0 : UnitG' S hG d) (l l' : Form0 N (SequenceAverages.N0 S)) :
    pairForm0 (aC S) (Gp S hG d.inN d.log d.U d.aa d.ΩD l) l' =
      pairForm0 (aC S) l (Gp S hG d.inN d.log d.U d.aa d.ΩD l') :=
  cinv_symm _ (piF0_idem hG d.ΩD) (piF0_symm hG d.ΩD _) (fun a b _ _ => DeltaP_symm S d a b) hK0 l l'

lemma Mop_symm (hK0 : UnitG' S hG d) (u v : BPt S → Mat) :
    pairB S N (Mop (Gp S hG d.inN d.log d.U d.aa d.ΩD) (Qpseq S d.inN d.log d.U) (QpseqStar S d.inN d.log d.U) u) v =
      pairB S N u (Mop (Gp S hG d.inN d.log d.U d.aa d.ΩD) (Qpseq S d.inN d.log d.U) (QpseqStar S d.inN d.log d.U) v) := by
  set G' := Gp S hG d.inN d.log d.U d.aa d.ΩD
  set Qp := Qpseq S d.inN d.log d.U
  set Qps := QpseqStar S d.inN d.log d.U
  show pairB S N (Qp (G' (G' (Qps u)))) v = pairB S N u (Qp (G' (G' (Qps v))))
  calc pairB S N (Qp (G' (G' (Qps u)))) v = pairB S N v (Qp (G' (G' (Qps u)))) := wpair_symm _ _ _
    _ = pairForm0 (aC S) (Qps v) (G' (G' (Qps u))) := (QpseqStar_spec S _ _ _ _ _).symm
    _ = pairForm0 (aC S) (G' (Qps v)) (G' (Qps u)) := (Gp_symm S hG d hK0 _ _).symm
    _ = pairForm0 (aC S) (G' (G' (Qps v))) (Qps u) := (Gp_symm S hG d hK0 _ _).symm
    _ = pairForm0 (aC S) (Qps u) (G' (G' (Qps v))) := pairForm0_symm _ _ _
    _ = pairB S N u (Qp (G' (G' (Qps v)))) := QpseqStar_spec S _ _ _ _ _

lemma MinvP_symm (hK0 : UnitG' S hG d) (hKM' : UnitM' S hG d) (u v : BPt S → Mat) :
    pairB S N (cinv (piFun hG (BPt S)) (Mop (Gp S hG d.inN d.log d.U d.aa d.ΩD) (Qpseq S d.inN d.log d.U)
      (QpseqStar S d.inN d.log d.U)) u) v =
    pairB S N u (cinv (piFun hG (BPt S)) (Mop (Gp S hG d.inN d.log d.U d.aa d.ΩD) (Qpseq S d.inN d.log d.U)
      (QpseqStar S d.inN d.log d.U)) v) :=
  cinv_symm _ (piFun_idem hG _) (piFun_symm hG _) (fun a b _ _ => Mop_symm S hG d hK0 a b) hKM' u v

lemma Rs_symm (hK0 : UnitG' S hG d) (hKM' : UnitM' S hG d) (l l' : Form0 N (SequenceAverages.N0 S)) :
    pairForm0 (aC S) (Rs S hG d.inN d.log d.U d.aa d.ΩD l) l' =
      pairForm0 (aC S) l (Rs S hG d.inN d.log d.U d.aa d.ΩD l') := by
  set G' := Gp S hG d.inN d.log d.U d.aa d.ΩD
  set Qp := Qpseq S d.inN d.log d.U
  set Qps := QpseqStar S d.inN d.log d.U
  set Mi := cinv (piFun hG (BPt S)) (Mop G' Qp Qps)
  have hX : ∀ l l', pairForm0 (aC S) (G' (Qps (Mi (Qp (G' l))))) l' =
      pairForm0 (aC S) l (G' (Qps (Mi (Qp (G' l'))))) := fun l l' => by
    calc pairForm0 (aC S) (G' (Qps (Mi (Qp (G' l))))) l' = pairForm0 (aC S) (Qps (Mi (Qp (G' l)))) (G' l') :=
          Gp_symm S hG d hK0 _ _
      _ = pairB S N (Mi (Qp (G' l))) (Qp (G' l')) := QpseqStar_spec S _ _ _ _ _
      _ = pairB S N (Qp (G' l)) (Mi (Qp (G' l'))) := MinvP_symm S hG d hK0 hKM' _ _
      _ = pairB S N (Mi (Qp (G' l'))) (Qp (G' l)) := wpair_symm _ _ _
      _ = pairForm0 (aC S) (Qps (Mi (Qp (G' l')))) (G' l) := (QpseqStar_spec S _ _ _ _ _).symm
      _ = pairForm0 (aC S) (G' (Qps (Mi (Qp (G' l'))))) l := (Gp_symm S hG d hK0 _ _).symm
      _ = pairForm0 (aC S) l (G' (Qps (Mi (Qp (G' l'))))) := pairForm0_symm _ _ _
  show pairForm0 (aC S) (piF0 hG d.ΩD l - G' (Qps (Mi (Qp (G' l))))) l' =
    pairForm0 (aC S) l (piF0 hG d.ΩD l' - G' (Qps (Mi (Qp (G' l')))))
  rw [map_sub, LinearMap.sub_apply, map_sub, piF0_symm hG d.ΩD, hX]

/-! ### The operators on `1`-forms -/

lemma DRD_symm (hK0 : UnitG' S hG d) (hKM' : UnitM' S hG d) (A B : Form1 N (SequenceAverages.N0 S)) :
    pairForm1 (aC S) (DRD S hG d A) B = pairForm1 (aC S) A (DRD S hG d B) := by
  set R := Rs S hG d.inN d.log d.U d.aa d.ΩD
  show pairForm1 (aC S) (D0L (aC S) d.U (R (Ds1L (aC S) d.U A))) B =
    pairForm1 (aC S) A (D0L (aC S) d.U (R (Ds1L (aC S) d.U B)))
  calc pairForm1 (aC S) (D0L (aC S) d.U (R (Ds1L (aC S) d.U A))) B
      = pairForm0 (aC S) (R (Ds1L (aC S) d.U A)) (Ds1L (aC S) d.U B) := D0L_transpose _ _ _ _
    _ = pairForm0 (aC S) (Ds1L (aC S) d.U A) (R (Ds1L (aC S) d.U B)) := Rs_symm S hG d hK0 hKM' _ _
    _ = pairForm0 (aC S) (R (Ds1L (aC S) d.U B)) (Ds1L (aC S) d.U A) := pairForm0_symm _ _ _
    _ = pairForm1 (aC S) (D0L (aC S) d.U (R (Ds1L (aC S) d.U B))) A := (D0L_transpose _ _ _ _).symm
    _ = pairForm1 (aC S) A (D0L (aC S) d.U (R (Ds1L (aC S) d.U B))) := pairForm1_symm _ _ _

/-- **`𝒫^T = I - DRG'D^*` is the transpose of `𝒫 = I - DG'RD^*`.** -/
theorem PcalT_transpose (hK0 : UnitG' S hG d) (hKM' : UnitM' S hG d) (A B : Form1 N (SequenceAverages.N0 S)) :
    pairForm1 (aC S) (PcalT S hG d A) B = pairForm1 (aC S) A (Pcal S hG d B) := by
  set R := Rs S hG d.inN d.log d.U d.aa d.ΩD
  set G' := Gp S hG d.inN d.log d.U d.aa d.ΩD
  have key : pairForm1 (aC S) (D0L (aC S) d.U (R (G' (Ds1L (aC S) d.U A)))) B =
      pairForm1 (aC S) A (D0L (aC S) d.U (G' (R (Ds1L (aC S) d.U B)))) := by
    calc pairForm1 (aC S) (D0L (aC S) d.U (R (G' (Ds1L (aC S) d.U A)))) B
        = pairForm0 (aC S) (R (G' (Ds1L (aC S) d.U A))) (Ds1L (aC S) d.U B) := D0L_transpose _ _ _ _
      _ = pairForm0 (aC S) (G' (Ds1L (aC S) d.U A)) (R (Ds1L (aC S) d.U B)) := Rs_symm S hG d hK0 hKM' _ _
      _ = pairForm0 (aC S) (Ds1L (aC S) d.U A) (G' (R (Ds1L (aC S) d.U B))) := Gp_symm S hG d hK0 _ _
      _ = pairForm0 (aC S) (G' (R (Ds1L (aC S) d.U B))) (Ds1L (aC S) d.U A) := pairForm0_symm _ _ _
      _ = pairForm1 (aC S) (D0L (aC S) d.U (G' (R (Ds1L (aC S) d.U B)))) A := (D0L_transpose _ _ _ _).symm
      _ = pairForm1 (aC S) A (D0L (aC S) d.U (G' (R (Ds1L (aC S) d.U B)))) := pairForm1_symm _ _ _
  show pairForm1 (aC S) (A - D0L (aC S) d.U (R (G' (Ds1L (aC S) d.U A)))) B =
    pairForm1 (aC S) A (B - D0L (aC S) d.U (G' (R (Ds1L (aC S) d.U B))))
  rw [map_sub, LinearMap.sub_apply, map_sub, key]

/-- `Δ(U)` is symmetric on the compressed forms (their values lie in `𝔤^c`). -/
lemma hess_symm (A B : Form1 N (SequenceAverages.N0 S)) (hA : piF1 hG d.ΩD A = A) (hB : piF1 hG d.ΩD B = B) :
    pairForm1 (aC S) (hessLin (aC S) hG (aC_ne S) d.U A) B = pairForm1 (aC S) A (hessLin (aC S) hG (aC_ne S) d.U B) := by
  have hA' : ∀ μ z, A μ z ∈ G.lieC := fun μ z => by rw [← hA]; exact QLieC.piF1_mem hG _ A μ z
  have hB' : ∀ μ z, B μ z ∈ G.lieC := fun μ z => by rw [← hB]; exact QLieC.piF1_mem hG _ B μ z
  calc pairForm1 (aC S) (hessLin (aC S) hG (aC_ne S) d.U A) B
      = pairForm1 (aC S) B (hessLin (aC S) hG (aC_ne S) d.U A) := pairForm1_symm _ _ _
    _ = pair1 (aC S) B (hessOp (aC S) hG d.U A) := pairForm1_apply _ _ _
    _ = pair1 (aC S) A (hessOp (aC S) hG d.U B) := pair1_hessOp_symm (aC S) hG (aC_ne S) d.U hB' hA'
    _ = pairForm1 (aC S) A (hessLin (aC S) hG (aC_ne S) d.U B) := (pairForm1_apply _ _ _).symm

lemma constraintOp_symm (A B : Form1 N (SequenceAverages.N0 S)) :
    pairForm1 (aC S) (constraintOp S d.inN d.log d.U (d.aa : ℂ) A) B =
      pairForm1 (aC S) A (constraintOp S d.inN d.log d.U (d.aa : ℂ) B) :=
  QsWQ_symm (pairForm1 (aC S)) (pairLB S N) (pairForm1_symm _) (pairLB_symm S N) (Qseq S d.inN d.log d.U)
    (QseqStar S d.inN d.log d.U) (QseqStar_spec S d.inN d.log d.U) _ (mulW_symm _ _) A B

lemma DA_symm (hK0 : UnitG' S hG d) (hKM' : UnitM' S hG d) (A B : Form1 N (SequenceAverages.N0 S))
    (hA : piF1 hG d.ΩD A = A) (hB : piF1 hG d.ΩD B = B) :
    pairForm1 (aC S) (DA S hG d A) B = pairForm1 (aC S) A (DA S hG d B) := by
  simp only [DA, DeltaA, LinearMap.add_apply, map_add]
  rw [hess_symm S hG d A B hA hB, constraintOp_symm S d A B]
  have := DRD_symm S hG d hK0 hKM' A B
  simp only [DRD] at this
  rw [this]

lemma Gs_symm (hK0 : UnitG' S hG d) (hKM' : UnitM' S hG d) (hKG : IsUnit (ckern (piF1 hG d.ΩD) (DA S hG d)))
    (A B : Form1 N (SequenceAverages.N0 S)) :
    pairForm1 (aC S) (Gs S hG d.inN d.log d.U d.aa d.ΩD (aC_ne S) A) B =
      pairForm1 (aC S) A (Gs S hG d.inN d.log d.U d.aa d.ΩD (aC_ne S) B) :=
  cinv_symm _ (piF1_idem hG d.ΩD) (piF1_symm hG d.ΩD _) (fun a b ha hb => DA_symm S hG d hK0 hKM' a b ha hb) hKG A B

lemma Gc_symm (hK0 : UnitG' S hG d) (hKM' : UnitM' S hG d)
    (hKc : IsUnit (ckern (piF1 hG d.ΩD) (DA S hG d - Delta2 S hG d))) (A B : Form1 N (SequenceAverages.N0 S)) :
    pairForm1 (aC S) (Gc S hG d A) B = pairForm1 (aC S) A (Gc S hG d B) := by
  refine cinv_symm _ (piF1_idem hG d.ΩD) (piF1_symm hG d.ΩD _) (fun a b ha hb => ?_) hKc A B
  rw [LinearMap.sub_apply, LinearMap.sub_apply, map_sub, LinearMap.sub_apply, map_sub,
    DA_symm S hG d hK0 hKM' a b ha hb, Delta2_symm]

lemma Gpi_symm (hK0 : UnitG' S hG d) (hKM' : UnitM' S hG d)
    (hKp : IsUnit (ckern (piF1 hG d.ΩD) (DA S hG d - DeltaPi S hG d))) (A B : Form1 N (SequenceAverages.N0 S)) :
    pairForm1 (aC S) (Gpi S hG d A) B = pairForm1 (aC S) A (Gpi S hG d B) := by
  refine cinv_symm _ (piF1_idem hG d.ΩD) (piF1_symm hG d.ΩD _) (fun a b ha hb => ?_) hKp A B
  rw [LinearMap.sub_apply, LinearMap.sub_apply, map_sub, LinearMap.sub_apply, map_sub,
    DA_symm S hG d hK0 hKM' a b ha hb, DeltaPi_symm]

lemma QGcQs_symm (hK0 : UnitG' S hG d) (hKM' : UnitM' S hG d)
    (hKc : IsUnit (ckern (piF1 hG d.ΩD) (DA S hG d - Delta2 S hG d))) (u v : LBond S → Mat) :
    pairLB S N ((Qseq S d.inN d.log d.U ∘ₗ Gc S hG d ∘ₗ QseqStar S d.inN d.log d.U) u) v =
      pairLB S N u ((Qseq S d.inN d.log d.U ∘ₗ Gc S hG d ∘ₗ QseqStar S d.inN d.log d.U) v) := by
  set Gc' := Gc S hG d
  set Q := Qseq S d.inN d.log d.U
  set Qs := QseqStar S d.inN d.log d.U
  show pairLB S N (Q (Gc' (Qs u))) v = pairLB S N u (Q (Gc' (Qs v)))
  calc pairLB S N (Q (Gc' (Qs u))) v = pairLB S N v (Q (Gc' (Qs u))) := pairLB_symm S N _ _
    _ = pairForm1 (aC S) (Qs v) (Gc' (Qs u)) := (QseqStar_spec S _ _ _ _ _).symm
    _ = pairForm1 (aC S) (Gc' (Qs v)) (Qs u) := (Gc_symm S hG d hK0 hKM' hKc _ _).symm
    _ = pairForm1 (aC S) (Qs u) (Gc' (Qs v)) := pairForm1_symm _ _ _
    _ = pairLB S N u (Q (Gc' (Qs v))) := QseqStar_spec S _ _ _ _ _

lemma MinvC_symm (hK0 : UnitG' S hG d) (hKM' : UnitM' S hG d)
    (hKc : IsUnit (ckern (piF1 hG d.ΩD) (DA S hG d - Delta2 S hG d)))
    (hKM : IsUnit (ckern (piFun hG (LBond S)) (Qseq S d.inN d.log d.U ∘ₗ Gc S hG d ∘ₗ QseqStar S d.inN d.log d.U)))
    (u v : LBond S → Mat) :
    pairLB S N (CriticalSequence.Minv S hG d u) v = pairLB S N u (CriticalSequence.Minv S hG d v) :=
  cinv_symm _ (piFun_idem hG _) (piFun_symm hG _) (fun a b _ _ => QGcQs_symm S hG d hK0 hKM' hKc a b) hKM u v

/-- **`thm:critical`(iii), `G̃J = 0`, for a sequence of domains**, any Dirichlet domain and any group: if `J`
annihilates the compressed forms `δ` with `Qδ = 0` (the criticality of `U₀`), then `G̃J = 0`. -/
theorem Gtilde_J_sequence (hK0 : UnitG' S hG d) (hKM' : UnitM' S hG d)
    (hKc : IsUnit (ckern (piF1 hG d.ΩD) (DA S hG d - Delta2 S hG d)))
    (hKM : IsUnit (ckern (piFun hG (LBond S)) (Qseq S d.inN d.log d.U ∘ₗ Gc S hG d ∘ₗ QseqStar S d.inN d.log d.U)))
    (hQpres : ∀ x, piFun hG (LBond S) (Qseq S d.inN d.log d.U (piF1 hG d.ΩD x)) =
      Qseq S d.inN d.log d.U (piF1 hG d.ΩD x))
    (J : Form1 N (SequenceAverages.N0 S))
    (hJ : ∀ δ, piF1 hG d.ΩD δ = δ → Qseq S d.inN d.log d.U δ = 0 → pairForm1 (aC S) J δ = 0) :
    Gtil S hG d J = 0 := by
  rw [Gtil_eq]
  exact CriticalCompressed.Gtilde_J_c (Qseq S d.inN d.log d.U) (QseqStar S d.inN d.log d.U) (Gc S hG d)
    (CriticalSequence.Minv S hG d) (piF1 hG d.ΩD) (piFun hG (LBond S)) (pairForm1 (aC S)) (pairLB S N)
    (pairForm1_nondegenerate (a0_pos S)) (pairForm1_symm _) (pairLB_symm S N) (QseqStar_spec S d.inN d.log d.U)
    (fun x => P_cinv (piF1_idem hG d.ΩD) x) (Gc_symm S hG d hK0 hKM' hKc) (MinvC_symm S hG d hK0 hKM' hKc hKM)
    (fun x => Q_Gtil S hG d hKM x) hQpres J hJ

end Sequence

end SequenceSymmetry
end CoreLean

end
