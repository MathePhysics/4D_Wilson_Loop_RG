/-
Bridge (B3) of `thm:small-field` for the operator `G = Δ_𝖺^{-1}` on `1`-forms, first part: the scaling in the spacing
`a₀` of the differences and of the Hessian, `Δ(U)` at the spacing `a` being `a^{-2}` times `Δ(U)` at the spacing `1`.

* `Dfw_scale`, `Dbw_scale`, `D1_scale`, `Ds2_scale`, `D0L_scale`, `Ds1L_scale`: the differences scale as `a⁻¹`;
* `hessTermBil_scale`, `hessBil_scale`: `β_a = a²β_1` (`pexp` does not depend on `a`);
* `hessOp'_scale` (by the trace characterisation `hessOp'_spec` on `𝔤^c`), `hessOp_scale`, `hessLin_scale`.
-/
import CoreLean.SFVectorComp
import CoreLean.SFProjBridge

open Matrix Complex
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace CoreLean
namespace SFBounds

variable {N n : ℕ} [NeZero n]

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ

lemma Dfw_scale (a : ℂ) (U : Config N n) (μ : Fin 4) (l : Form0 N n) :
    Dfw a U μ l = a⁻¹ • Dfw 1 U μ l := by
  funext x; simp [Dfw, smul_smul]

lemma Dbw_scale (a : ℂ) (U : Config N n) (μ : Fin 4) (l : Form0 N n) :
    Dbw a U μ l = a⁻¹ • Dbw 1 U μ l := by
  funext x; simp [Dbw, smul_smul]

lemma D1_scale (a : ℂ) (U : Config N n) (A : Form1 N n) : D1 a U A = a⁻¹ • D1 1 U A := by
  funext μ ν x; simp only [D1, Pi.smul_apply, Dfw_scale a U μ, Dfw_scale a U ν, smul_sub]

lemma Ds2_scale (a : ℂ) (U : Config N n) (F : Form2 N n) : Ds2 a U F = a⁻¹ • Ds2 1 U F := by
  funext μ x
  simp only [Ds2, Pi.smul_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun ν _ => ?_
  split_ifs
  · rw [Dbw_scale a U ν]; rfl
  · simp

lemma D0_scale (a : ℂ) (U : Config N n) (l : Form0 N n) : D0 a U l = a⁻¹ • D0 1 U l := by
  funext μ x; simp only [D0, Pi.smul_apply, Dfw_scale a U μ]

lemma Ds1_scale (a : ℂ) (U : Config N n) (A : Form1 N n) : Ds1 a U A = a⁻¹ • Ds1 1 U A := by
  funext x
  simp only [Ds1, Pi.smul_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [Dbw_scale a U ν]; rfl

lemma D0L_scale (a : ℂ) (U : Config N n) : SequenceOperators.D0L a U = a⁻¹ • SequenceOperators.D0L 1 U := by
  refine LinearMap.ext fun l => ?_
  simp only [SequenceOperators.D0L_apply, LinearMap.smul_apply, D0_scale a U l]

lemma Ds1L_scale (a : ℂ) (U : Config N n) : SequenceOperators.Ds1L a U = a⁻¹ • SequenceOperators.Ds1L 1 U := by
  refine LinearMap.ext fun A => ?_
  simp only [SequenceOperators.Ds1L_apply, LinearMap.smul_apply, Ds1_scale a U A]

lemma hessTermBil_scale {a : ℂ} (ha : a ≠ 0) (A B : Form1 N n) (U : Config N n) (μ ν : Fin 4) (x : Site n) :
    hessTermBil a A B U μ ν x = a ^ 2 * hessTermBil 1 A B U μ ν x := by
  simp only [hessTermBil, D1_scale a U A, D1_scale a U B, Pi.smul_apply, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, ← smul_add, ntr_smul, one_pow, inv_one, one_smul, mul_one, one_mul]
  field_simp

lemma hessBil_scale {a : ℂ} (ha : a ≠ 0) (A B : Form1 N n) (U : Config N n) :
    hessBil a A B U = a ^ 2 * hessBil 1 A B U := by
  simp only [hessBil, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => ?_
  split_ifs
  · exact hessTermBil_scale ha A B U μ ν x
  · simp

/-- **`Δ'` at the spacing `a`**: `Δ'_a(U) = a^{-2}Δ'_1(U)` (both take values in `𝔤^c` and have the same trace pairings
with `𝔤^c`, `hessOp'_spec`, `hessBil_scale`). -/
lemma hessOp'_scale [NeZero N] {G : GaugeGroup N} (hG : G.LieInput) {a : ℂ} (ha : a ≠ 0) (U : Config N n)
    (A : Form1 N n) : hessOp' a hG U A = (a ^ 2)⁻¹ • hessOp' 1 hG U A := by
  funext μ x
  set D : Mat := hessOp' a hG U A μ x - (a ^ 2)⁻¹ • hessOp' 1 hG U A μ x
  have hDmem : D ∈ G.lieC := by
    have h1 := hessOp'_mem a hG U A μ x
    have h2 := hessOp'_mem 1 hG U A μ x
    exact (GaugeGroup.lieCSubmodule hG).sub_mem h1 ((GaugeGroup.lieCSubmodule hG).smul_mem _ h2)
  have hpair : ∀ Z ∈ G.lieC, ntr (Z * D) = 0 := fun Z hZ => by
    have e1 := hessOp'_spec a hG ha U A μ x hZ
    have e2 := hessOp'_spec 1 hG one_ne_zero U A μ x hZ
    rw [hessBil_scale ha, ← e2] at e1
    simp only [D, Matrix.mul_sub, Matrix.mul_smul, ntr_sub, ntr_smul, one_pow, one_mul] at e1 ⊢
    have ha4 : a ^ 4 ≠ 0 := pow_ne_zero 4 ha
    have hX : ntr (Z * hessOp' a hG U A μ x) = (a ^ 4)⁻¹ * (a ^ 2 * ntr (Z * hessOp' 1 hG U A μ x)) := by
      rw [← e1]; field_simp
    have : ntr (Z * hessOp' a hG U A μ x) = (a ^ 2)⁻¹ * ntr (Z * hessOp' 1 hG U A μ x) := by
      rw [hX]; field_simp
    rw [this, sub_self]
  have h0 := hpair Dᴴ (GaugeGroup.conjTranspose_mem_lieC hDmem)
  have hD : D = 0 := by
    have hc : ntr (D * Dᴴ) = 0 := by unfold ntr at h0 ⊢; rw [Matrix.trace_mul_comm]; exact h0
    rw [ConcretePairing.ntr_mul_conj] at hc
    have hr : (N : ℝ)⁻¹ * ∑ i, ∑ j, Complex.normSq (D j i) = 0 := by exact_mod_cast hc
    have hN : (0 : ℝ) < (N : ℝ)⁻¹ := by have := NeZero.ne N; positivity
    have hs : ∑ i, ∑ j, Complex.normSq (D j i) = 0 := by
      rcases mul_eq_zero.1 hr with h | h
      · exact absurd h hN.ne'
      · exact h
    funext j i
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _).1
      hs i (Finset.mem_univ _)
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => Complex.normSq_nonneg (D j i)).1 h1 j (Finset.mem_univ _)
    simpa using h2
  have := sub_eq_zero.1 hD
  simpa using this

lemma hessOp_scale [NeZero N] {G : GaugeGroup N} (hG : G.LieInput) {a : ℂ} (ha : a ≠ 0) (U : Config N n)
    (A : Form1 N n) : hessOp a hG U A = (a ^ 2)⁻¹ • hessOp 1 hG U A := by
  simp only [hessOp, D1_scale a U A, Ds2_scale a U, hessOp'_scale hG ha, smul_add]
  rw [show Ds2 1 U (a⁻¹ • D1 1 U A) = a⁻¹ • Ds2 1 U (D1 1 U A) by
    funext μ x
    simp only [Ds2, Pi.smul_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun ν _ => ?_
    split_ifs
    · simp only [Dbw, Pi.smul_apply, smul_sub, smul_smul, Ad_smul, mul_comm]
    · simp]
  rw [smul_smul, ← pow_two, inv_pow]

/-- **`Δ(U)` at the spacing `a`**: `hessLin a = a^{-2}hessLin 1`. -/
lemma hessLin_scale [NeZero N] {G : GaugeGroup N} (hG : G.LieInput) {a : ℂ} (ha : a ≠ 0) (ha1 : (1 : ℂ) ≠ 0)
    (U : Config N n) : hessLin a hG ha U = (a ^ 2)⁻¹ • hessLin 1 hG ha1 U := by
  refine LinearMap.ext fun A => ?_
  exact hessOp_scale hG ha U A

section Torus

open Lattices SeqDom Blocks SmallFieldBlocks SFBox SFBox.SeqDomBox SmallFieldDecay SmallFieldCoercivity
  PartitionUnity RegularAverages AxialStraightLattice BoxGeometry ConcretePairing SFLocal

variable (S : SeqDom)

local notation "NF" => SequenceAverages.N0 S
set_option quotPrecheck false in
local notation "jj" => (S.toDomSeq).sc

/-- **`π` commutes with `P` of the fine model on the torus** (with the transports in `G^c`, `Pop_eq`). -/
theorem Pop_comm_pi [NeZero N] {G : GaugeGroup N} (hG : G.LieInput) (X : Fin 4 → Site NF → Matrix (Fin N) (Fin N) ℂ)
    (hU : ∀ μ x Z, piProj hG (Ad (cfgX X μ x) Z) = Ad (cfgX X μ x) (piProj hG Z))
    (hW : ∀ y ∈ detB S.toDomSeq, ∀ x ∈ Blk S.toDomSeq (jj y) y, ∀ Z,
      piProj hG (Ad (Wf S (cfgX X) y x) Z) = Ad (Wf S (cfgX X) y x) (piProj hG Z))
    (hK : IsUnit (CompressedInverse.ckern (piD Set.univ) (DeltaS S.toDomSeq (cfgX X) (Wf S (cfgX X)))))
    (hT : Function.Bijective (kerLin (kerT S (Subtype.val : BD S Set.univ → Site NF) X (Wf S (cfgX X)) Set.univ)))
    (hM : IsUnit (Mc S X (Wf S (cfgX X)))) (ν : Site NF → Matrix (Fin N) (Fin N) ℂ) :
    SequenceOperators.piF0 hG Set.univ (Pop S X (Wf S (cfgX X)) Set.univ ν) =
      Pop S X (Wf S (cfgX X)) Set.univ (SequenceOperators.piF0 hG Set.univ ν) := by
  set W := Wf S (cfgX X)
  set π := SequenceOperators.piF0 hG (Set.univ : Set (Site NF))
  set πB := SequenceOperators.piFun hG (SequenceIndex.BPt S)
  set G' := Gp' S.toDomSeq (cfgX X) W Set.univ
  have hcomm := DeltaS_comm_pi S hG (cfgX X) W hU hW
  have hπx : ∀ (g : Site NF → Matrix (Fin N) (Fin N) ℂ) x, π g x = piProj hG (g x) := fun g x => by
    simp [π, SequenceOperators.piF0, Set.indicator_apply]
  have hπD : ∀ f, π (piD Set.univ f) = piD Set.univ (π f) := fun f => by
    funext x; simp [piD_apply, hπx]
  have hπG : ∀ f, π (G' f) = G' (π f) := fun f => commute_cinv π _ _ hπD hcomm hK f
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
  rw [Pop_eq S X W hT hM, Pop_eq S X W hT hM, hπG, ← hE, hMi, ← hR, hπG]

/-- `D^*_U` commutes with `π` for a configuration with links in `G^c`. -/
lemma Ds1L_comm_pi [NeZero N] {G : GaugeGroup N} (hG : G.LieInput) (U : Config N NF)
    (hU : ∀ μ x, U μ x ∈ G.complexified) (A : Fin 4 → Site NF → Matrix (Fin N) (Fin N) ℂ) :
    SequenceOperators.piF0 hG Set.univ (SequenceOperators.Ds1L 1 U A) =
      SequenceOperators.Ds1L 1 U (SequenceOperators.piF1 hG Set.univ A) := by
  have hp0 : piProj hG (0 : Matrix (Fin N) (Fin N) ℂ) = 0 := by
    simpa using proj_smul hG 0 (0 : Matrix (Fin N) (Fin N) ℂ)
  have hneg : ∀ Z : Matrix (Fin N) (Fin N) ℂ, piProj hG (-Z) = -piProj hG Z := fun Z => by
    simpa using proj_smul hG (-1) Z
  funext x
  simp only [SequenceOperators.piF0, SequenceOperators.piF1, LinearMap.coe_mk, AddHom.coe_mk,
    SequenceOperators.Ds1L_apply, Ds1, Dbw, Set.indicator_apply, Set.mem_univ, if_true, SequenceOperators.bondsOf,
    Set.mem_setOf_eq, and_self, inv_one, one_smul]
  rw [proj_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  have hV : U.val ⟨x, μ, false⟩ ∈ G.complexified := by
    unfold Config.val
    split_ifs <;> first | exact hU _ _ | exact G.complexified.inv_mem (hU _ _)
  rw [sub_eq_add_neg, proj_add, hneg, proj_Ad hG hV, ← sub_eq_add_neg]

end Torus

section TorusVec

open Lattices SeqDom Blocks SmallFieldBlocks SFBox SFBox.SeqDomBox SmallFieldDecay SmallFieldCoercivity
  PartitionUnity RegularAverages AxialStraightLattice BoxGeometry ConcretePairing SFLocal

variable (S : SeqDom)

local notation "NF" => SequenceAverages.N0 S
set_option quotPrecheck false in
local notation "jj" => (S.toDomSeq).sc

/-- The constraint operator of the fine model: `Q_𝖺 = a₀²Q^*𝖺Q` at `𝖺 = 1`. -/
def QOpc (X : Fin 4 → Site NF → Matrix (Fin N) (Fin N) ℂ) : Module.End ℂ (Fin 4 → Site NF → Matrix (Fin N) (Fin N) ℂ) :=
  ((((SequenceAverages.a0 S : ℝ) : ℂ)) ^ 2 * (((1 : ℝ) : ℂ))⁻¹) •
    SequenceAverages.constraintOp S (fun _ => True) (fun W => LogM (W : Matrix (Fin N) (Fin N) ℂ)) (cfgX X)
      ((1 : ℝ) : ℂ)

set_option maxHeartbeats 2000000 in
/-- **`Δ_𝖺 = a₀^{-2}T(𝐔)` on the forms with values in `𝔤^c`** (bridge (B3), torus, `𝖺 = 1`): for `B = π₁A`,
`Δ_𝖺B = a₀^{-2}T(𝐔)B` with `Q_𝖺 = a₀²Q^*𝖺Q` (`hessLin_scale`, `R = π - πP_fine` by `Ps_eq`, `Pop_comm_pi`,
`Ds1L_comm_pi`). -/
theorem DeltaA_piF1 [NeZero N] {G : GaugeGroup N} (hG : G.LieInput) (X : Fin 4 → Site NF → Matrix (Fin N) (Fin N) ℂ)
    (hUc : ∀ μ x, cfgX X μ x ∈ G.complexified)
    (hW : ∀ y ∈ detB S.toDomSeq, ∀ x ∈ Blk S.toDomSeq (jj y) y, ∀ Z,
      piProj hG (Ad (Wf S (cfgX X) y x) Z) = Ad (Wf S (cfgX X) y x) (piProj hG Z))
    (hK : IsUnit (CompressedInverse.ckern (piD Set.univ) (DeltaS S.toDomSeq (cfgX X) (Wf S (cfgX X)))))
    (hT : Function.Bijective (kerLin (kerT S (Subtype.val : BD S Set.univ → Site NF) X (Wf S (cfgX X)) Set.univ)))
    (hM : IsUnit (Mc S X (Wf S (cfgX X)))) (ha : ((SequenceAverages.a0 S : ℝ) : ℂ) ≠ 0)
    (A : Fin 4 → Site NF → Matrix (Fin N) (Fin N) ℂ) :
    SequenceOperators.DeltaA S hG (fun _ => True) (fun W => LogM (W : Matrix (Fin N) (Fin N) ℂ)) (cfgX X) 1
        Set.univ ha (SequenceOperators.piF1 hG Set.univ A) =
      ((((SequenceAverages.a0 S : ℝ) : ℂ)) ^ 2)⁻¹ •
        TU S hG X (Wf S (cfgX X)) (QOpc S X) (SequenceOperators.piF1 hG Set.univ A) := by
  have hU : ∀ μ x Z, piProj hG (Ad (cfgX X μ x) Z) = Ad (cfgX X μ x) (piProj hG Z) := fun μ x Z =>
    proj_Ad hG (hUc μ x) Z
  have hPs := Ps_eq S hG X hU hW hK hT hM
  have hf := Ds1L_comm_pi S hG (cfgX X) hUc A
  have hπ : ∀ g : Site NF → Matrix (Fin N) (Fin N) ℂ,
      SequenceOperators.piF0 hG Set.univ (SequenceOperators.piF0 hG Set.univ g) =
      SequenceOperators.piF0 hG Set.univ g := fun g => SequenceOperators.piF0_idem hG _ g
  have hPc := Pop_comm_pi S hG X hU hW hK hT hM
  have hRs : SequenceOperators.Rs S hG (fun _ => True) (fun W => LogM (W : Matrix (Fin N) (Fin N) ℂ)) (cfgX X) 1
      Set.univ = SequenceOperators.piF0 hG Set.univ -
        SequenceOperators.Ps S hG (fun _ => True) (fun W => LogM (W : Matrix (Fin N) (Fin N) ℂ)) (cfgX X) 1
          Set.univ := rfl
  have hR : SequenceOperators.Rs S hG (fun _ => True) (fun W => LogM (W : Matrix (Fin N) (Fin N) ℂ)) (cfgX X) 1
      Set.univ (SequenceOperators.Ds1L 1 (cfgX X) (SequenceOperators.piF1 hG Set.univ A)) =
      (1 - Pop S X (Wf S (cfgX X)) Set.univ)
        (SequenceOperators.Ds1L 1 (cfgX X) (SequenceOperators.piF1 hG Set.univ A)) := by
    rw [hRs, hPs, ← hf, LinearMap.sub_apply, LinearMap.sub_apply, Module.End.mul_apply, Module.End.one_apply, hπ,
      ← hPc, hπ]
  have hD : SequenceOperators.DeltaA S hG (fun _ => True) (fun W => LogM (W : Matrix (Fin N) (Fin N) ℂ)) (cfgX X) 1
      Set.univ ha (SequenceOperators.piF1 hG Set.univ A) =
      hessLin (((SequenceAverages.a0 S : ℝ) : ℂ)) hG ha (cfgX X) (SequenceOperators.piF1 hG Set.univ A) +
        SequenceOperators.D0L (((SequenceAverages.a0 S : ℝ) : ℂ)) (cfgX X)
          (SequenceOperators.Rs S hG (fun _ => True) (fun W => LogM (W : Matrix (Fin N) (Fin N) ℂ)) (cfgX X) 1
            Set.univ (SequenceOperators.Ds1L (((SequenceAverages.a0 S : ℝ) : ℂ)) (cfgX X)
              (SequenceOperators.piF1 hG Set.univ A))) +
        SequenceAverages.constraintOp S (fun _ => True) (fun W => LogM (W : Matrix (Fin N) (Fin N) ℂ)) (cfgX X)
          ((1 : ℝ) : ℂ) (SequenceOperators.piF1 hG Set.univ A) := rfl
  have hTU : TU S hG X (Wf S (cfgX X)) (QOpc S X) (SequenceOperators.piF1 hG Set.univ A) =
      hessLin 1 hG (one_ne_zero : (1 : ℂ) ≠ 0) (cfgX X) (SequenceOperators.piF1 hG Set.univ A) +
        SequenceOperators.D0L 1 (cfgX X) ((1 - Pop S X (Wf S (cfgX X)) Set.univ)
          (SequenceOperators.Ds1L 1 (cfgX X) (SequenceOperators.piF1 hG Set.univ A))) +
        QOpc S X (SequenceOperators.piF1 hG Set.univ A) := rfl
  rw [hD, hTU, hessLin_scale hG ha (one_ne_zero : (1 : ℂ) ≠ 0), D0L_scale, Ds1L_scale]
  simp only [LinearMap.smul_apply, map_smul, hR]
  simp only [QOpc, LinearMap.smul_apply, smul_add, smul_smul]
  congr 1
  · congr 1
    rw [← pow_two, inv_pow]
  · have ha2 : ((((SequenceAverages.a0 S : ℝ) : ℂ)) ^ 2)⁻¹ * ((((SequenceAverages.a0 S : ℝ) : ℂ)) ^ 2 *
        (((1 : ℝ) : ℂ))⁻¹) = 1 := by field_simp; simp
    rw [ha2, one_smul]

end TorusVec

section TorusG

open Lattices SeqDom Blocks SmallFieldBlocks SFBox SFBox.SeqDomBox SmallFieldDecay SmallFieldCoercivity
  PartitionUnity RegularAverages AxialStraightLattice BoxGeometry ConcretePairing SFLocal

variable (S : SeqDom)

local notation "NF" => SequenceAverages.N0 S
set_option quotPrecheck false in
local notation "jj" => (S.toDomSeq).sc

/-- **`G = a₀²cinv π₁T(𝐔)`** (bridge (B3) for `G`, torus, `𝖺 = 1`): the operator `G = Δ_𝖺^{-1}` of the concrete layer,
compressed to the forms with values in `𝔤^c`, is `a₀²` times the compressed inverse of the fine-model operator `T(𝐔)`
with `Q_𝖺 = a₀²Q^*𝖺Q` (`DeltaA_piF1`, `cinv_smul`). -/
theorem Gs_eq [NeZero N] {G : GaugeGroup N} (hG : G.LieInput) (X : Fin 4 → Site NF → Matrix (Fin N) (Fin N) ℂ)
    (hUc : ∀ μ x, cfgX X μ x ∈ G.complexified)
    (hW : ∀ y ∈ detB S.toDomSeq, ∀ x ∈ Blk S.toDomSeq (jj y) y, ∀ Z,
      piProj hG (Ad (Wf S (cfgX X) y x) Z) = Ad (Wf S (cfgX X) y x) (piProj hG Z))
    (hK : IsUnit (CompressedInverse.ckern (piD Set.univ) (DeltaS S.toDomSeq (cfgX X) (Wf S (cfgX X)))))
    (hT : Function.Bijective (kerLin (kerT S (Subtype.val : BD S Set.univ → Site NF) X (Wf S (cfgX X)) Set.univ)))
    (hM : IsUnit (Mc S X (Wf S (cfgX X)))) (ha : ((SequenceAverages.a0 S : ℝ) : ℂ) ≠ 0) :
    SequenceOperators.Gs S hG (fun _ => True) (fun W => LogM (W : Matrix (Fin N) (Fin N) ℂ)) (cfgX X) 1 Set.univ ha =
      ((((SequenceAverages.a0 S : ℝ) : ℂ)) ^ 2) •
        CompressedInverse.cinv (SequenceOperators.piF1 hG Set.univ) (TU S hG X (Wf S (cfgX X)) (QOpc S X)) := by
  have hk : CompressedInverse.ckern (SequenceOperators.piF1 hG Set.univ)
      (SequenceOperators.DeltaA S hG (fun _ => True) (fun W => LogM (W : Matrix (Fin N) (Fin N) ℂ)) (cfgX X) 1
        Set.univ ha) =
      CompressedInverse.ckern (SequenceOperators.piF1 hG Set.univ)
        (((((SequenceAverages.a0 S : ℝ) : ℂ)) ^ 2)⁻¹ • TU S hG X (Wf S (cfgX X)) (QOpc S X)) := by
    refine LinearMap.ext fun x => ?_
    simp only [CompressedInverse.ckern_apply, LinearMap.smul_apply]
    rw [DeltaA_piF1 S hG X hUc hW hK hT hM ha]
  have hP : ∀ x : Fin 4 → Site NF → Matrix (Fin N) (Fin N) ℂ,
      SequenceOperators.piF1 hG Set.univ (SequenceOperators.piF1 hG Set.univ x) =
        SequenceOperators.piF1 hG Set.univ x := fun x => SequenceOperators.piF1_idem hG _ x
  have ha2 : ((((SequenceAverages.a0 S : ℝ) : ℂ)) ^ 2)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero 2 ha)
  unfold SequenceOperators.Gs
  rw [show CompressedInverse.cinv (SequenceOperators.piF1 hG Set.univ)
      (SequenceOperators.DeltaA S hG (fun _ => True) (fun W => LogM (W : Matrix (Fin N) (Fin N) ℂ)) (cfgX X) 1
        Set.univ ha) = CompressedInverse.cinv (SequenceOperators.piF1 hG Set.univ)
        (((((SequenceAverages.a0 S : ℝ) : ℂ)) ^ 2)⁻¹ • TU S hG X (Wf S (cfgX X)) (QOpc S X)) by
      unfold CompressedInverse.cinv; rw [hk],
    cinv_smul _ _ hP ha2, inv_inv]

end TorusG

section Assembly

open Lattices SeqDom Blocks SmallFieldBlocks SFBox SFBox.SeqDomBox SmallFieldDecay SmallFieldCoercivity
  PartitionUnity RegularAverages AxialStraightLattice BoxGeometry ConcretePairing SFLocal

variable (S : SeqDom)

local notation "NF" => SequenceAverages.N0 S
set_option quotPrecheck false in
local notation "jj" => (S.toDomSeq).sc

/-- **The operators of the concrete layer at a small field, on the torus** (bridges (B2), (B3), `𝖺 = 1`): there is
`c > 0` such that for a regular field `X` with values in `𝔤^c`, `α₁L < c`, `G ⊂ G^c`, and the hypotheses `ScalarHyp`
of the fine model at the transports `W_𝐔` with the smallness of `block_inverse`,
`G' = a₀²πGp'(𝐔, W_𝐔)`, `P = πPop`, and `G = a₀²cinv π₁T(𝐔)` with `Q_𝖺 = a₀²Q^*𝖺Q`. -/
theorem ops_bridge_torus [NeZero N] (G : GaugeGroup N) (hGc : IsClosed G.mats) (hG : G.LieInput) :
    ∃ c : ℝ, 0 < c ∧ ∀ (hRM : 2 * (S.L : ℝ) ≤ ((S.R * S.L ^ S.mM : ℕ) : ℝ))
      (hn : ∀ l, 4 * SequenceAverages.hS S + 4 ≤ MultiscaleAverages.nn (SequenceAverages.hS S) S.mT S.k l)
      (hGG : G.carrier ≤ G.complexified)
      {X : Fin 4 → Site NF → Matrix (Fin N) (Fin N) ℂ} {α₁ η δ : ℝ}
      (H : ScalarHyp S X α₁ (Wf S (cfgX X)) η Set.univ δ)
      (hRMb : (S.toContSeq).r1 (1 / 2) (1 / 32 * δ) ≤ ((S.R * S.L ^ S.mM : ℕ) : ℝ))
      (hRMs4 : 32 * Real.log S.L / (1 / 4 * δ) ≤ ((S.R * S.L ^ S.mM : ℕ) : ℝ))
      (hsmallT : CTd S N δ α₁ η * (S.toContSeq).c1 (1 / 2) (1 / 32 * δ) ≤ ((9 / 32) ^ 4 / (864 + 4 * N)) ^ 2 / 4)
      (hXc : ∀ μ x, X μ x ∈ G.lieC) (hαc : α₁ * S.L < c) (ha : ((SequenceAverages.a0 S : ℝ) : ℂ) ≠ 0),
      SequenceOperators.Gp S hG (fun _ => True) (fun W => LogM (W : Matrix (Fin N) (Fin N) ℂ)) (cfgX X) 1 Set.univ =
          (((SequenceAverages.a0 S : ℝ) : ℂ) ^ 2) •
            (SequenceOperators.piF0 hG Set.univ * Gp' S.toDomSeq (cfgX X) (Wf S (cfgX X)) Set.univ) ∧
        SequenceOperators.Ps S hG (fun _ => True) (fun W => LogM (W : Matrix (Fin N) (Fin N) ℂ)) (cfgX X) 1
            Set.univ = SequenceOperators.piF0 hG Set.univ * Pop S X (Wf S (cfgX X)) Set.univ ∧
        SequenceOperators.Gs S hG (fun _ => True) (fun W => LogM (W : Matrix (Fin N) (Fin N) ℂ)) (cfgX X) 1
            Set.univ ha = ((((SequenceAverages.a0 S : ℝ) : ℂ)) ^ 2) •
          CompressedInverse.cinv (SequenceOperators.piF1 hG Set.univ) (TU S hG X (Wf S (cfgX X)) (QOpc S X)) := by
  obtain ⟨c, hc, hWG⟩ := Wf_mem_Gc S G hGc
  refine ⟨c, hc, fun hRM hn hGG X α₁ η δ H hRMb hRMs4 hsmallT hXc hαc ha => ?_⟩
  have hWc := hWG hRM hn hGG H.hX H.hα0 hXc hαc
  have hUc := cfgX_mem_Gc S hXc
  have hU : ∀ μ x Z, piProj hG (Ad (cfgX X μ x) Z) = Ad (cfgX X μ x) (piProj hG Z) := fun μ x Z =>
    proj_Ad hG (hUc μ x) Z
  have hW : ∀ y ∈ detB S.toDomSeq, ∀ x ∈ Blk S.toDomSeq (jj y) y, ∀ Z,
      piProj hG (Ad (Wf S (cfgX X) y x) Z) = Ad (Wf S (cfgX X) y x) (piProj hG Z) := fun y hy x hx Z =>
    proj_Ad hG (hWc y hy x hx) Z
  have hK := H.hK (N := N)
  have hT := (H.block_inverse hRMb hRMs4 hsmallT).1
  have hM := Mc_isUnit S X (Wf S (cfgX X)) hT
  exact ⟨Gp_eq_Gc S hG hXc Set.univ hWc hK, Ps_eq S hG X hU hW hK hT hM, Gs_eq S hG X hUc hW hK hT hM ha⟩

end Assembly

section HypW

open Lattices SeqDom Blocks SmallFieldBlocks SFBox SFBox.SeqDomBox SmallFieldDecay SmallFieldCoercivity
  PartitionUnity RegularAverages AxialStraightLattice BoxGeometry ConcretePairing SFLocal

variable (S : SeqDom)

local notation "NF" => SequenceAverages.N0 S

/-- **The hypotheses of the fine model at the transports `W_𝐔`** (bridge (B2)): for a regular field `X` with
`α₁L, K_oα₁L ≤ c` and `2CK_oα₁L ≤ log 2`, `ScalarHyp` holds at `W_𝐔` with `η = √N(e^{C'K_oα₁L/2} - 1)` and the
remaining conditions of `ScalarHyp` (`Wf_bounds`). -/
theorem scalarHyp_Wf (G : GaugeGroup N) (hGc : IsClosed G.mats) (hN : 1 ≤ N) :
    ∃ c Ko C C' : ℝ, 0 < c ∧ 0 ≤ Ko ∧ 0 ≤ C ∧ 0 ≤ C' ∧
      ∀ (hRM : 2 * (S.L : ℝ) ≤ ((S.R * S.L ^ S.mM : ℕ) : ℝ))
        (hn : ∀ l, 4 * SequenceAverages.hS S + 4 ≤ MultiscaleAverages.nn (SequenceAverages.hS S) S.mT S.k l)
        {X : Fin 4 → Site NF → Matrix (Fin N) (Fin N) ℂ} {α₁ δ : ℝ} (hX : RegField S X α₁) (hα0 : 0 ≤ α₁)
        (hαc : α₁ * S.L ≤ c) (hKαc : Ko * (α₁ * S.L) ≤ c) (hlog : 2 * C * (Ko * (α₁ * S.L)) ≤ Real.log 2)
        (hα : 64 * (S.L : ℝ) ^ 2 * α₁ ≤ 1)
        (hsmall : (4 * (6 * α₁) + (6 * α₁) ^ 2) * (6 * (S.L : ℝ) ^ 2) +
          6 * Real.sqrt N * (Real.sqrt N * (Real.exp (C' * (Ko * (α₁ * S.L)) / 2) - 1)) ≤ 1 / 8)
        (hRM8 : 8 * (S.L : ℝ) ^ 2 ≤ ((S.R * S.L ^ S.mM : ℕ) : ℝ))
        (hRMs : 32 * Real.log S.L / δ ≤ ((S.R * S.L ^ S.mM : ℕ) : ℝ))
        (hRM1 : (S.toContSeq).r1 (1 / 2) δ ≤ ((S.R * S.L ^ S.mM : ℕ) : ℝ))
        (hδ0 : 0 < δ) (hδ : δ ≤ 1 / (128 * S.L)),
      ScalarHyp S X α₁ (Wf S (cfgX X)) (Real.sqrt N * (Real.exp (C' * (Ko * (α₁ * S.L)) / 2) - 1)) Set.univ δ := by
  obtain ⟨c, Ko, C, C', hc, hKo, hC, hC', hWb⟩ := Wf_bounds S G hGc hN
  refine ⟨c, Ko, C, C', hc, hKo, hC, hC', ?_⟩
  intro hRM hn X α₁ δ hX hα0 hαc hKαc hlog hα hsmall hRM8 hRMs hRM1 hδ0 hδ
  obtain ⟨hW, hW1⟩ := hWb hRM hn hX hα0 hαc hKαc hlog
  have hη : 0 ≤ Real.sqrt N * (Real.exp (C' * (Ko * (α₁ * S.L)) / 2) - 1) := by
    have h0 : 0 ≤ C' * (Ko * (α₁ * S.L)) / 2 := by
      have : (0 : ℝ) ≤ S.L := Nat.cast_nonneg _; positivity
    have := Real.add_one_le_exp (C' * (Ko * (α₁ * S.L)) / 2)
    exact mul_nonneg (Real.sqrt_nonneg _) (by linarith)
  exact ⟨hX, hα0, hα, hη, fun y hy x hx Z => hW1 y hy x hx Z, hW, hsmall, hRM8, hRMs, hRM1, hδ0, hδ,
    fun x _ => Set.mem_univ x⟩

end HypW

section BoundsIV

open Lattices SeqDom Blocks SmallFieldBlocks SFBox SFBox.SeqDomBox SmallFieldDecay SmallFieldCoercivity
  PartitionUnity RegularAverages AxialStraightLattice BoxGeometry ConcretePairing SFLocal

variable (S : SeqDom)

local notation "NF" => SequenceAverages.N0 S
set_option quotPrecheck false in
local notation "jj" => (S.toDomSeq).sc

/-- **`thm:small-field`(iv) for `G'`, the values, on the torus**: at `𝐔 = e^{iX}`, `𝖺 = 1`, for `λ` supported in the
block of `y'` with `|λ| ≤ Λ` and `x` in the block of `y`,
`|(G'λ)(x)| ≤ a₀²C_vL^{2j(y)}e^{-(7/8)δd(y, y')}Λ = C_va_{j(y)}²e^{-(7/8)δd(y, y')}Λ` (`ops_bridge_torus`, `values`,
`|πZ| ≤ |Z|`). -/
theorem Gp_values_torus [NeZero N] (G : GaugeGroup N) (hGc : IsClosed G.mats) (hG : G.LieInput) :
    ∃ c : ℝ, 0 < c ∧ ∀ (hRM : 2 * (S.L : ℝ) ≤ ((S.R * S.L ^ S.mM : ℕ) : ℝ))
      (hn : ∀ l, 4 * SequenceAverages.hS S + 4 ≤ MultiscaleAverages.nn (SequenceAverages.hS S) S.mT S.k l)
      (hGG : G.carrier ≤ G.complexified)
      {X : Fin 4 → Site NF → Matrix (Fin N) (Fin N) ℂ} {α₁ η δ : ℝ}
      (H : ScalarHyp S X α₁ (Wf S (cfgX X)) η Set.univ δ)
      (hRMb : (S.toContSeq).r1 (1 / 2) (1 / 32 * δ) ≤ ((S.R * S.L ^ S.mM : ℕ) : ℝ))
      (hRMs4 : 32 * Real.log S.L / (1 / 4 * δ) ≤ ((S.R * S.L ^ S.mM : ℕ) : ℝ))
      (hsmallT : CTd S N δ α₁ η * (S.toContSeq).c1 (1 / 2) (1 / 32 * δ) ≤ ((9 / 32) ^ 4 / (864 + 4 * N)) ^ 2 / 4)
      (hXc : ∀ μ x, X μ x ∈ G.lieC) (hαc : α₁ * S.L < c)
      {y y' x : Site NF} (hy : y ∈ detB S.toDomSeq) (hy' : y' ∈ detB S.toDomSeq)
      (hx : x ∈ Blk S.toDomSeq (jj y) y) {lam : Site NF → Matrix (Fin N) (Fin N) ℂ} {Λ : ℝ} (hΛ : 0 ≤ Λ)
      (hsupp : ∀ x', x' ∉ Blk S.toDomSeq (jj y') y' → lam x' = 0) (hbd : ∀ x', hs (lam x') ≤ Λ),
      hs (SequenceOperators.Gp S hG (fun _ => True) (fun W => LogM (W : Matrix (Fin N) (Fin N) ℂ)) (cfgX X) 1
          Set.univ lam x) ≤
        (SequenceAverages.a0 S) ^ 2 * (Cv S δ (Csc S N) (4 * N * (S.L : ℝ) ^ 4) *
          Real.exp (-(7 / 8 * δ * S.dF y y')) * ((S.L : ℝ) ^ (2 * jj y) * Λ)) := by
  obtain ⟨c, hc, hB⟩ := ops_bridge_torus S G hGc hG
  refine ⟨c, hc, fun hRM hn hGG X α₁ η δ H hRMb hRMs4 hsmallT hXc hαc y y' x hy hy' hx lam Λ hΛ hsupp hbd => ?_⟩
  have ha : ((SequenceAverages.a0 S : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (SequenceAverages.a0_pos S).ne'
  obtain ⟨hGp, -, -⟩ := hB hRM hn hGG H hRMb hRMs4 hsmallT hXc hαc ha
  rw [hGp]
  have hv := H.values hy hy' hx hΛ hsupp hbd
  have hπx : SequenceOperators.piF0 hG Set.univ (Gp' S.toDomSeq (cfgX X) (Wf S (cfgX X)) Set.univ lam) x =
      piProj hG (Gp' S.toDomSeq (cfgX X) (Wf S (cfgX X)) Set.univ lam x) := by
    simp [SequenceOperators.piF0, Set.indicator_apply]
  simp only [LinearMap.smul_apply, Module.End.mul_apply, Pi.smul_apply]
  rw [hπx]
  have hsm : hs ((((SequenceAverages.a0 S : ℝ) : ℂ) ^ 2) • piProj hG (Gp' S.toDomSeq (cfgX X) (Wf S (cfgX X))
      Set.univ lam x)) = (SequenceAverages.a0 S) ^ 2 * hs (piProj hG (Gp' S.toDomSeq (cfgX X) (Wf S (cfgX X))
      Set.univ lam x)) := by
    have h := hs_smul (((SequenceAverages.a0 S : ℝ) : ℂ) ^ 2) (piProj hG (Gp' S.toDomSeq (cfgX X) (Wf S (cfgX X))
      Set.univ lam x))
    rw [h, norm_pow, Complex.norm_real, Real.norm_of_nonneg (SequenceAverages.a0_pos S).le]
  rw [hsm]
  exact mul_le_mul_of_nonneg_left ((hs_proj_le hG _).trans hv) (by positivity)

end BoundsIV

section BoundsVII

open Lattices SeqDom Blocks SmallFieldBlocks SFBox SFBox.SeqDomBox SmallFieldDecay SmallFieldCoercivity
  PartitionUnity RegularAverages AxialStraightLattice BoxGeometry ConcretePairing SFLocal

variable (S : SeqDom)

local notation "NF" => SequenceAverages.N0 S
set_option quotPrecheck false in
local notation "jj" => (S.toDomSeq).sc

/-- **`thm:small-field`(vii) for `P`, on the torus**: at `𝐔 = e^{iX}`, `𝖺 = 1`, the projection `P` of the concrete
layer has the kernel bound `|(Pf)(x)| ≤ C_PΣ_{x'}a_{y(x')}^{-4}e^{-(7/32)θ_Bd(y(x), y(x'))}|f(x')|` (in the units
`a₀ = 1` of the fine lattice; `ops_bridge_torus`, `P_bound`, `|πZ| ≤ |Z|`). -/
theorem Ps_kernel_torus [NeZero N] (G : GaugeGroup N) (hGc : IsClosed G.mats) (hG : G.LieInput) :
    ∃ c : ℝ, 0 < c ∧ ∀ (hRM : 2 * (S.L : ℝ) ≤ ((S.R * S.L ^ S.mM : ℕ) : ℝ))
      (hn : ∀ l, 4 * SequenceAverages.hS S + 4 ≤ MultiscaleAverages.nn (SequenceAverages.hS S) S.mT S.k l)
      (hGG : G.carrier ≤ G.complexified)
      {X : Fin 4 → Site NF → Matrix (Fin N) (Fin N) ℂ} {α₁ η δ : ℝ}
      (H : ScalarHyp S X α₁ (Wf S (cfgX X)) η Set.univ δ)
      (hRMb : (S.toContSeq).r1 (1 / 2) (1 / 32 * δ) ≤ ((S.R * S.L ^ S.mM : ℕ) : ℝ))
      (hRMs4 : 32 * Real.log S.L / (1 / 4 * δ) ≤ ((S.R * S.L ^ S.mM : ℕ) : ℝ))
      (hsmallT : CTd S N δ α₁ η * (S.toContSeq).c1 (1 / 2) (1 / 32 * δ) ≤ ((9 / 32) ^ 4 / (864 + 4 * N)) ^ 2 / 4)
      (hRMθs : 32 * Real.log S.L / (thetaB S N δ / 2) ≤ ((S.R * S.L ^ S.mM : ℕ) : ℝ))
      (hRMθc : (S.toContSeq).r1 (1 / 2) (7 / 16 * thetaB S N δ) ≤ ((S.R * S.L ^ S.mM : ℕ) : ℝ))
      (hXc : ∀ μ x, X μ x ∈ G.lieC) (hαc : α₁ * S.L < c) (f : Site NF → Matrix (Fin N) (Fin N) ℂ) (x : Site NF),
      hs (SequenceOperators.Ps S hG (fun _ => True) (fun W => LogM (W : Matrix (Fin N) (Fin N) ℂ)) (cfgX X) 1
          Set.univ f x) ≤
        CPk S N δ * ∑ x', ((S.L : ℝ) ^ (4 * jj (bc S.toDomSeq x')))⁻¹ *
          Real.exp (-(7 / 32 * thetaB S N δ * S.dF (bc S.toDomSeq x) (bc S.toDomSeq x'))) * hs (f x') := by
  obtain ⟨c, hc, hB⟩ := ops_bridge_torus S G hGc hG
  refine ⟨c, hc, fun hRM hn hGG X α₁ η δ H hRMb hRMs4 hsmallT hRMθs hRMθc hXc hαc f x => ?_⟩
  have ha : ((SequenceAverages.a0 S : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (SequenceAverages.a0_pos S).ne'
  obtain ⟨-, hPs, -⟩ := hB hRM hn hGG H hRMb hRMs4 hsmallT hXc hαc ha
  rw [hPs]
  have hπx : SequenceOperators.piF0 hG Set.univ (Pop S X (Wf S (cfgX X)) Set.univ f) x =
      piProj hG (Pop S X (Wf S (cfgX X)) Set.univ f x) := by
    simp [SequenceOperators.piF0, Set.indicator_apply]
  rw [Module.End.mul_apply, hπx]
  exact (hs_proj_le hG _).trans (H.P_bound hRMb hRMs4 hsmallT hRMθs hRMθc f x)

end BoundsVII

section BoundsVIII

open Lattices SeqDom Blocks SmallFieldBlocks SFBox SFBox.SeqDomBox SmallFieldDecay SmallFieldCoercivity
  PartitionUnity RegularAverages AxialStraightLattice BoxGeometry ConcretePairing SFLocal

variable (S : SeqDom)

local notation "NF" => SequenceAverages.N0 S

/-- **The decay of `G` from the decay of the compressed fine-model inverse** (`thm:small-field`(viii), the form of
eq:sf-vector-decay): if `G = a₀²cinv π₁T` and the compressed inverse of `T` satisfies the conclusion of
`decay_U_comp` for `J + D^*_𝐔K`, then `v = a₀^{-2}G(J + D^*_𝐔K)` satisfies the same bound. -/
theorem Gs_decay [NeZero N] {G : GaugeGroup N} (hG : G.LieInput) (X : Fin 4 → Site NF → Matrix (Fin N) (Fin N) ℂ)
    (T : Module.End ℂ (Fin 4 → Site NF → Matrix (Fin N) (Fin N) ℂ)) (ha : ((SequenceAverages.a0 S : ℝ) : ℂ) ≠ 0)
    (hGs : SequenceOperators.Gs S hG (fun _ => True) (fun W => LogM (W : Matrix (Fin N) (Fin N) ℂ)) (cfgX X) 1
      Set.univ ha = ((((SequenceAverages.a0 S : ℝ) : ℂ)) ^ 2) •
        CompressedInverse.cinv (SequenceOperators.piF1 hG Set.univ) T)
    (J : Fin 4 → Site NF → Matrix (Fin N) (Fin N) ℂ) (K : Fin 4 → Fin 4 → Site NF → Matrix (Fin N) (Fin N) ℂ)
    (B : (Fin 4 → Site NF → Matrix (Fin N) (Fin N) ℂ) → Prop)
    (hdec : IsUnit (CompressedInverse.ckern (SequenceOperators.piF1 hG Set.univ) T) ∧
      ∀ v, SequenceOperators.piF1 hG Set.univ v = v →
        SequenceOperators.piF1 hG Set.univ (T v) = SequenceOperators.piF1 hG Set.univ (J + DsU S X K) → B v) :
    B (((((SequenceAverages.a0 S : ℝ) : ℂ)) ^ 2)⁻¹ •
      SequenceOperators.Gs S hG (fun _ => True) (fun W => LogM (W : Matrix (Fin N) (Fin N) ℂ)) (cfgX X) 1 Set.univ ha
        (J + DsU S X K)) := by
  have hP : ∀ x : Fin 4 → Site NF → Matrix (Fin N) (Fin N) ℂ,
      SequenceOperators.piF1 hG Set.univ (SequenceOperators.piF1 hG Set.univ x) =
        SequenceOperators.piF1 hG Set.univ x := fun x => SequenceOperators.piF1_idem hG _ x
  have ha2 : ((((SequenceAverages.a0 S : ℝ) : ℂ)) ^ 2) ≠ 0 := pow_ne_zero 2 ha
  rw [hGs, LinearMap.smul_apply, smul_smul, inv_mul_cancel₀ ha2, one_smul]
  exact hdec.2 _ (CompressedInverse.P_cinv hP _) (CompressedInverse.P_T_cinv hP hdec.1 _)

end BoundsVIII

section PiOne

open Lattices SeqDom Blocks SmallFieldBlocks SFBox SFBox.SeqDomBox SmallFieldDecay SmallFieldCoercivity
  PartitionUnity RegularAverages AxialStraightLattice BoxGeometry ConcretePairing SFLocal

variable (S : SeqDom)

local notation "NF" => SequenceAverages.N0 S

lemma piF1_univ_apply [NeZero N] {G : GaugeGroup N} (hG : G.LieInput) (A : Fin 4 → Site NF → Matrix (Fin N) (Fin N) ℂ)
    (μ : Fin 4) (x : Site NF) : SequenceOperators.piF1 hG Set.univ A μ x = piProj hG (A μ x) := by
  simp [SequenceOperators.piF1, SequenceOperators.bondsOf, Set.indicator_apply]

/-- `π₁` commutes with the weights `e^φ`. -/
lemma piF1_expA [NeZero N] {G : GaugeGroup N} (hG : G.LieInput) (ψ : Site NF → ℝ)
    (A : Fin 4 → Site NF → Matrix (Fin N) (Fin N) ℂ) :
    SequenceOperators.piF1 hG Set.univ (expA S ψ A) = expA S ψ (SequenceOperators.piF1 hG Set.univ A) := by
  funext μ x
  simp only [piF1_univ_apply, expA, proj_smul]

/-- `π₁` is symmetric for `⟨B^*, C⟩`. -/
lemma piF1_pair1V [NeZero N] {G : GaugeGroup N} (hG : G.LieInput) (B C : Fin 4 → Site NF → Matrix (Fin N) (Fin N) ℂ) :
    pair1V S (SequenceOperators.piF1 hG Set.univ B) C = pair1V S B (SequenceOperators.piF1 hG Set.univ C) := by
  rw [pair1V_tr, pair1V_tr]
  refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun x _ => ?_
  rw [piF1_univ_apply, piF1_univ_apply, ← proj_conjTranspose]
  have h := ntr_proj_symm hG (B μ x)ᴴ (C μ x)
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  unfold ntr at h
  have := mul_left_cancel₀ (inv_ne_zero hN) h
  exact this

end PiOne

section DecayVIII

open Lattices SeqDom Blocks SmallFieldBlocks SFBox SFBox.SeqDomBox SmallFieldDecay SmallFieldCoercivity
  PartitionUnity RegularAverages AxialStraightLattice BoxGeometry ConcretePairing SFLocal SequenceOperators
  CompressedInverse

variable (S : SeqDom)

local notation "NF" => SequenceAverages.N0 S
local notation "RMS" => ((S.R * S.L ^ S.mM : ℕ) : ℝ)

/-- **`thm:small-field`(viii), the decay of `G`, on the torus**: at `𝐔 = e^{iX}`, `𝖺 = 1`, under `ScalarHyp` at the
transports `W_𝐔` and the hypotheses of `decay_U` with `ε_Q = 96L³δ + 576L²Nε̄(4 + ε̄)` (`constraintOp_hQ`), the operator
`G` of the concrete layer satisfies eq:sf-vector-decay: `v = a₀^{-2}G(J + D^*_𝐔K)` has
`N(e^φv) ≤ c⁻¹(‖e^φJ‖_{w⁻¹} + 3L‖e^φK‖)` (`ops_bridge_torus`, `decay_U_comp`, `Gs_decay`). -/
theorem Gs_decay_torus [NeZero N] (G : GaugeGroup N) (hGc : IsClosed G.mats) (hG : G.LieInput) (hN : 1 ≤ N) :
    ∃ c Ko C : ℝ, 0 < c ∧ 0 ≤ Ko ∧ 0 ≤ C ∧
      ∀ (hRM2' : 2 * (S.L : ℝ) ≤ ((S.R * S.L ^ S.mM : ℕ) : ℝ)) (hRM18 : 18 * (S.L : ℝ) ≤ RMS)
        (hR1' : 1 ≤ S.R * S.L ^ S.mM)
        (hn : ∀ l, 4 * SequenceAverages.hS S + 4 ≤ MultiscaleAverages.nn (SequenceAverages.hS S) S.mT S.k l)
        (hGG : G.carrier ≤ G.complexified)
        {X : Fin 4 → Site NF → Matrix (Fin N) (Fin N) ℂ} {α₁ η δ0 : ℝ}
        (H : ScalarHyp S X α₁ (Wf S (cfgX X)) η Set.univ δ0)
        (hsmallTb : CTd S N δ0 α₁ η * (S.toContSeq).c1 (1 / 2) (1 / 32 * δ0) ≤ ((9 / 32) ^ 4 / (864 + 4 * N)) ^ 2 / 4)
        (hXc : ∀ μ x, X μ x ∈ G.lieC) (hαc : α₁ * S.L < c) (hαc' : α₁ * S.L ≤ c) (hKαc : Ko * (α₁ * S.L) ≤ c)
        (ha : ((SequenceAverages.a0 S : ℝ) : ℂ) ≠ 0)
    (hα512 : α₁ ≤ 1 / 512) (hM : 12 ≤ S.L ^ S.mM) (hR : 12 * S.L ≤ S.R)
    (hRMb : (S.toContSeq).r1 (1 / 2) (1 / 32 * δ0) ≤ RMS) (hRMs4 : 32 * Real.log S.L / (1 / 4 * δ0) ≤ RMS)
    (hsmallT : CTd S N δ0 α₁ η * (S.toContSeq).c1 (1 / 2) (1 / 32 * δ0) ≤ gammaB N / 4)
    (hsmallT0 : CTd S N δ0 0 0 * (S.toContSeq).c1 (1 / 2) (1 / 32 * δ0) ≤ gammaB N / 4)
    (hRMθs : 32 * Real.log S.L / (thetaB S N δ0 / 2) ≤ RMS)
    (hRMθc : (S.toContSeq).r1 (1 / 2) (7 / 16 * thetaB S N δ0) ≤ RMS)
    (hRMc : (S.toContSeq).r1 (1 / 2) (3 / 4 * δ0) ≤ RMS)
    (hRMa : (S.toContSeq).r1 (1 / 2) (1 / 8 * δ0) ≤ RMS)
    (hRMq : (S.toContSeq).r1 (1 / 2) (thetaB S N δ0) ≤ RMS)
    (hRMq2 : (S.toContSeq).r1 (1 / 2) (thetaB S N δ0 / 2) ≤ RMS)
    (hRMs8 : 32 * Real.log S.L / (thetaB S N δ0 / 4 / 2) ≤ RMS)
    (hRMc8 : (S.toContSeq).r1 (1 / 2) (7 / 16 * (thetaB S N δ0 / 4)) ≤ RMS)
    (hRMd2 : (S.toContSeq).r1 (1 / 2) (7 / 16 * (thetaB S N δ0 / 4) / 2) ≤ RMS)
    (hRMds : 32 * Real.log S.L / (2 * (7 / 16 * (thetaB S N δ0 / 4))) ≤ RMS)
    (hRMp2 : (S.toContSeq).r1 (1 / 2) (7 / 16 * thetaB S N δ0 / 2) ≤ RMS)
    (hRMps : 32 * Real.log S.L / (2 * (7 / 16 * thetaB S N δ0)) ≤ RMS)
    (hRMsum : (S.toContSeq).r1 (1 / 2) (7 / 32 * thetaB S N δ0) ≤ RMS)
    (hRMsum2 : (S.toContSeq).r1 (1 / 2) (7 / 32 * thetaB S N δ0 / 2) ≤ RMS)
    (hRMss : 32 * Real.log S.L / (2 * (7 / 32 * thetaB S N δ0)) ≤ RMS)
    (hR1 : 1 ≤ S.R) (hRM2 : 2 * (S.L : ℝ) ≤ RMS) (hRMn : 2 * S.L ≤ S.R * S.L ^ S.mM)
    (hcutS : 8 * Real.exp (-(2 * (kap0 S N δ0 * (((S.L ^ S.mM : ℕ) : ℝ) / S.L)))) *
      Kbar S.L (kap0 S N δ0) (CIone S N δ0 (kap0 S N δ0)) Cbump ≤ 1 / 16)
    {ε : ℝ} (hε0 : 0 < ε) (hε : ε ≤ 1) (hΘ : ThetaIMS S N δ0 (Cloc S.L) ε ≤ 1 / 2)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδθ : δ ≤ 1 / 4 * (7 / 32 * thetaB S N δ0)) (hδL : 16 * S.L * δ ≤ 1)
    (ph : Site NF → ℝ) (hph : ∀ x x', |ph x - ph x'| ≤ δ * S.dF x x')
    (hc : 0 < (2 ^ 13 * Cloc S.L)⁻¹ - Econj S N δ0 α₁ η δ (96 * (S.L : ℝ) ^ 3 * δ + 576 * (S.L : ℝ) ^ 2 * N * ((Real.exp (4 * (S.L : ℝ) ^ 3 * C * (Ko * (α₁ * S.L))) - 1) * (4 + (Real.exp (4 * (S.L : ℝ) ^ 3 * C * (Ko * (α₁ * S.L))) - 1)))))
    (hc0 : 0 < (2 ^ 13 * Cloc S.L)⁻¹ - Econj S N δ0 α₁ η 0 (96 * (S.L : ℝ) ^ 3 * δ + 576 * (S.L : ℝ) ^ 2 * N * ((Real.exp (4 * (S.L : ℝ) ^ 3 * C * (Ko * (α₁ * S.L))) - 1) * (4 + (Real.exp (4 * (S.L : ℝ) ^ 3 * C * (Ko * (α₁ * S.L))) - 1)))))
    (J : Fin 4 → Site NF → Mat) (K : Fin 4 → Fin 4 → Site NF → Mat),
      √(gradNorm S (expA S ph ((((((SequenceAverages.a0 S : ℝ) : ℂ)) ^ 2)⁻¹ • Gs S hG (fun _ => True)
          (fun W => LogM (W : Matrix (Fin N) (Fin N) ℂ)) (cfgX X) 1 Set.univ ha (J + DsU S X K)))) +
        wnorm S (expA S ph ((((((SequenceAverages.a0 S : ℝ) : ℂ)) ^ 2)⁻¹ • Gs S hG (fun _ => True)
          (fun W => LogM (W : Matrix (Fin N) (Fin N) ℂ)) (cfgX X) 1 Set.univ ha (J + DsU S X K))))) ≤
        ((2 ^ 13 * Cloc S.L)⁻¹ - Econj S N δ0 α₁ η δ (96 * (S.L : ℝ) ^ 3 * δ + 576 * (S.L : ℝ) ^ 2 * N * ((Real.exp (4 * (S.L : ℝ) ^ 3 * C * (Ko * (α₁ * S.L))) - 1) * (4 + (Real.exp (4 * (S.L : ℝ) ^ 3 * C * (Ko * (α₁ * S.L))) - 1)))))⁻¹ *
          (√(wInv S (expA S ph J)) + 3 * S.L * √(Knorm S ph K)) := by
  obtain ⟨c1, hc1, hB⟩ := ops_bridge_torus S G hGc hG
  obtain ⟨c2, Ko, C, hc2, hKo, hC, hQ⟩ := constraintOp_hQ S G hGc hN
  refine ⟨min c1 c2, Ko, C, lt_min hc1 hc2, hKo, hC, ?_⟩
  intro hRM2' hRM18 hR1' hn hGG X α₁ η δ0 H hsmallTb hXc hαc hαc' hKαc ha hα512 hM hR hRMb hRMs4 hsmallT
    hsmallT0 hRMθs hRMθc hRMc hRMa hRMq hRMq2 hRMs8 hRMc8 hRMd2 hRMds hRMp2 hRMps hRMsum hRMsum2 hRMss hR1 hRM2
    hRMn hcutS ε hε0 hε hΘ δ hδ hδθ hδL ph hph hc hc0 J K
  have hRMb' := hRMb
  obtain ⟨-, -, hGs⟩ := hB hRM2' hn hGG H hRMb hRMs4 hsmallTb hXc (lt_of_lt_of_le hαc (min_le_left _ _)) ha
  obtain ⟨hQ1, hQ2⟩ := hQ hRM18 hR1' hn H.hX H.hα0 (hαc'.trans (min_le_right _ _)) (hKαc.trans (min_le_right _ _))
    hδ (by linarith) ph hph (aa := ((1 : ℝ) : ℂ)) (by simp)
  have hdec := H.decay_U_comp hG hα512 hM hR hRMb hRMs4 hsmallT hsmallT0 hRMθs hRMθc hRMc hRMa hRMq hRMq2 hRMs8
    hRMc8 hRMd2 hRMds hRMp2 hRMps hRMsum hRMsum2 hRMss hR1 hRM2 hRMn hcutS hε0 hε hΘ hδ hδθ hδL ph hph
    (QOpc S X) hQ1 hQ2 hc hc0 (piF1 hG Set.univ) (fun A => piF1_idem hG _ A) (piF1_expA S hG) (piF1_pair1V S hG) J K
  exact Gs_decay S hG X _ ha hGs J K _ hdec

end DecayVIII

end SFBounds
end CoreLean

end
