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
import CoreLean.RelativeAverageLevelsG

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

/-! ### Two identities of the compressed inverse -/

section CinvAlg

open CompressedInverse

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- **The compressed inverse of a multiple**: `cinv P (cT) = c⁻¹cinv P T` for an idempotent `P` and `c ≠ 0`. -/
theorem cinv_smul (P T : Module.End ℂ V) (hP : ∀ x, P (P x) = P x) {c : ℂ} (hc : c ≠ 0) :
    cinv P (c • T) = c⁻¹ • cinv P T := by
  set K := ckern P T
  set D : Module.End ℂ V := c • P + (1 - P)
  set Di : Module.End ℂ V := c⁻¹ • P + (1 - P)
  have hDK : ckern P (c • T) = D * K := by
    refine LinearMap.ext fun x => ?_
    simp only [K, D, ckern_apply, Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply,
      LinearMap.sub_apply, Module.End.one_apply, map_add, map_sub, map_smul, hP, smul_add, smul_sub]
    abel
  have hD1 : D * Di = 1 := by
    refine LinearMap.ext fun x => ?_
    simp only [D, Di, Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sub_apply,
      Module.End.one_apply, map_add, map_sub, map_smul, hP, smul_add, smul_sub, smul_smul, mul_inv_cancel₀ hc,
      inv_mul_cancel₀ hc, one_smul]
    abel
  have hD2 : Di * D = 1 := by
    refine LinearMap.ext fun x => ?_
    simp only [D, Di, Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sub_apply,
      Module.End.one_apply, map_add, map_sub, map_smul, hP, smul_add, smul_sub, smul_smul, inv_mul_cancel₀ hc,
      mul_inv_cancel₀ hc, one_smul]
    abel
  have hPK : Commute P K := by
    refine LinearMap.ext fun x => ?_
    simp only [K, ckern_apply, Module.End.mul_apply, map_add, map_sub, hP]
  unfold cinv
  rw [hDK]
  change _ = c⁻¹ • (P * Ring.inverse K)
  by_cases hK : IsUnit K
  · set u : (Module.End ℂ V)ˣ := ⟨D, Di, hD1, hD2⟩
    have hDu : D = (u : Module.End ℂ V) := rfl
    have hc' : Commute P ((hK.unit⁻¹ : (Module.End ℂ V)ˣ) : Module.End ℂ V) :=
      Commute.units_inv_right (by rw [hK.unit_spec]; exact hPK)
    rw [hDu, ← hK.unit_spec, ← Units.val_mul, Ring.inverse_unit, Ring.inverse_unit, mul_inv_rev, Units.val_mul]
    have hui : ((u⁻¹ : (Module.End ℂ V)ˣ) : Module.End ℂ V) = Di := rfl
    rw [hui]
    set Ki := ((hK.unit⁻¹ : (Module.End ℂ V)ˣ) : Module.End ℂ V)
    have hcx : ∀ v, P (Ki v) = Ki (P v) := fun v => by
      have := congrArg (fun F : Module.End ℂ V => F v) hc'.eq
      simpa only [Module.End.mul_apply] using this
    refine LinearMap.ext fun x => ?_
    simp only [Di, Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sub_apply,
      Module.End.one_apply, map_add, map_sub, map_smul, hcx, hP]
    abel
  · have hDK' : ¬ IsUnit (D * K) := fun h => hK (by
      have : K = Di * (D * K) := by rw [← mul_assoc, hD2, one_mul]
      rw [this]
      exact IsUnit.mul (⟨⟨Di, D, hD2, hD1⟩, rfl⟩ : IsUnit Di) h)
    rw [Ring.inverse_non_unit _ hK, Ring.inverse_non_unit _ hDK', mul_zero, smul_zero]

/-- **The compressed inverse with a commuting projection**: if `π` is idempotent and commutes with `P` and `T`, and
`ckern P T` is invertible, then `cinv (πP) T = π cinv P T`. -/
theorem cinv_proj (π P T : Module.End ℂ V) (hπ : ∀ x, π (π x) = π x)
    (hπP : ∀ x, π (P x) = P (π x)) (hπT : ∀ x, π (T x) = T (π x)) (hK : IsUnit (ckern P T)) :
    cinv (π * P) T = π * cinv P T := by
  set K := ckern P T
  have hπK : ∀ v, π (K v) = K (π v) := fun v => by
    simp only [K, ckern_apply, map_add, map_sub, hπP, hπT]
  set Ki := ((hK.unit⁻¹ : (Module.End ℂ V)ˣ) : Module.End ℂ V)
  have hπKi : ∀ v, π (Ki v) = Ki (π v) := fun v => by
    have hc : Commute π Ki := Commute.units_inv_right (by
      rw [hK.unit_spec]; exact LinearMap.ext fun x => by simp only [Module.End.mul_apply, hπK])
    have := congrArg (fun F : Module.End ℂ V => F v) hc.eq
    simpa only [Module.End.mul_apply] using this
  have hKKi : ∀ v, K (Ki v) = v := fun v => by
    have := congrArg (fun F : Module.End ℂ V => F v) hK.mul_val_inv
    simpa only [Module.End.mul_apply, Module.End.one_apply] using this
  have hKiK : ∀ v, Ki (K v) = v := fun v => by
    have := congrArg (fun F : Module.End ℂ V => F v) hK.val_inv_mul
    simpa only [Module.End.mul_apply, Module.End.one_apply] using this
  set E : Module.End ℂ V := π * Ki + (1 - π)
  have hKQ : ckern (π * P) T = π * K + (1 - π) := by
    refine LinearMap.ext fun x => ?_
    simp only [K, ckern_apply, Module.End.mul_apply, LinearMap.add_apply, LinearMap.sub_apply, Module.End.one_apply,
      map_add, map_sub, hπP, hπT, hπ]
    abel
  have h1 : ckern (π * P) T * E = 1 := by
    rw [hKQ]
    refine LinearMap.ext fun x => ?_
    simp only [E, Module.End.mul_apply, LinearMap.add_apply, LinearMap.sub_apply, Module.End.one_apply, map_add,
      map_sub, hπ, hπK, hπKi, hKKi, hKiK]
    abel
  have h2 : E * ckern (π * P) T = 1 := by
    rw [hKQ]
    refine LinearMap.ext fun x => ?_
    simp only [E, Module.End.mul_apply, LinearMap.add_apply, LinearMap.sub_apply, Module.End.one_apply, map_add,
      map_sub, hπ, hπK, hπKi, hKKi, hKiK]
    abel
  have hinv : Ring.inverse (ckern (π * P) T) = E := by
    have := Ring.inverse_unit (⟨ckern (π * P) T, E, h1, h2⟩ : (Module.End ℂ V)ˣ)
    simpa using this
  have hinvK : Ring.inverse K = Ki := by
    rw [← hK.unit_spec, Ring.inverse_unit]
  unfold cinv
  change _ = π * (P * Ring.inverse K)
  rw [hinv, hinvK]
  refine LinearMap.ext fun x => ?_
  simp only [E, Module.End.mul_apply, LinearMap.add_apply, LinearMap.sub_apply, Module.End.one_apply, map_add,
    map_sub, hπ, hπP, hπKi]
  abel

end CinvAlg


/-- `piF0 = π·piD`: the compression of the concrete layer is the projection onto `𝔤^c` after the indicator of `Ω_D`. -/
lemma piF0_eq [NeZero N] {G : GaugeGroup N} (hG : G.LieInput) (ΩD : Set (Site NF)) :
    SequenceOperators.piF0 hG ΩD = SequenceOperators.piF0 hG Set.univ * piD ΩD := by
  have hp0 : piProj hG (0 : Matrix (Fin N) (Fin N) ℂ) = 0 := by simpa using proj_smul hG 0 (0 : Matrix (Fin N) (Fin N) ℂ)
  refine LinearMap.ext fun f => funext fun x => ?_
  by_cases hx : x ∈ ΩD <;>
    simp [SequenceOperators.piF0, Module.End.mul_apply, Set.indicator_apply, piD_apply, hx, hp0]

/-- **`G' = a₀²πG'(𝐔, W_𝐔)`** (bridge (B3)): at `𝖺 = 1`, if `π` commutes with `Δ'_𝖺(𝐔)` of the fine model (which holds
when the configuration and the transports lie in `G^c`, `proj_Ad`) and the compressed kernel `ckern (piD Ω_D) Δ'_𝖺(𝐔)`
is invertible, then the operator `G'` of the concrete layer is `a₀²` times `π` after `Gp'` of the fine model
(`DeltaP_eq`, `cinv_smul`, `cinv_proj`). -/
theorem Gp_eq [NeZero N] {G : GaugeGroup N} (hG : G.LieInput) (U : Config N NF) (ΩD : Set (Site NF))
    (hcomm : ∀ f, SequenceOperators.piF0 hG Set.univ (DeltaS S.toDomSeq U (Wf S U) f) =
      DeltaS S.toDomSeq U (Wf S U) (SequenceOperators.piF0 hG Set.univ f))
    (hK : IsUnit (CompressedInverse.ckern (piD ΩD) (DeltaS S.toDomSeq U (Wf S U)))) :
    SequenceOperators.Gp S hG (fun _ => True) (fun W => LogM (W : Matrix (Fin N) (Fin N) ℂ)) U 1 ΩD =
      (((SequenceAverages.a0 S : ℝ) : ℂ) ^ 2) •
        (SequenceOperators.piF0 hG Set.univ * Gp' S.toDomSeq U (Wf S U) ΩD) := by
  set a : ℂ := ((SequenceAverages.a0 S : ℝ) : ℂ)
  have ha : a ≠ 0 := Complex.ofReal_ne_zero.2 (SequenceAverages.a0_pos S).ne'
  set π := SequenceOperators.piF0 hG (Set.univ : Set (Site NF))
  have hπ : ∀ f, π (π f) = π f := fun f => SequenceOperators.piF0_idem hG _ f
  have hp0 : piProj hG (0 : Matrix (Fin N) (Fin N) ℂ) = 0 := by simpa using proj_smul hG 0 (0 : Matrix (Fin N) (Fin N) ℂ)
  have hπD : ∀ f, π (piD ΩD f) = piD ΩD (π f) := fun f => by
    funext x
    simp only [π, SequenceOperators.piF0, LinearMap.coe_mk, AddHom.coe_mk, Set.indicator_apply, Set.mem_univ, if_true,
      piD_apply]
    split_ifs <;> simp [hp0]
  set P : Module.End ℂ (Site NF → Matrix (Fin N) (Fin N) ℂ) := π * piD ΩD
  have hPP : ∀ f, P (P f) = P f := fun f => by
    simp only [P, Module.End.mul_apply]
    rw [hπD (π (piD ΩD f)), hπ, ← hπD, piD_idem]
  unfold SequenceOperators.Gp
  rw [DeltaP_eq, piF0_eq S hG ΩD, cinv_smul _ _ hPP (inv_ne_zero (pow_ne_zero 2 ha)), inv_inv,
    cinv_proj π (piD ΩD) _ hπ hπD hcomm hK]
  rfl

/-- `π` is symmetric for the trace pairing: `ntr(πX·Y) = ntr(X·πY)` (`ntr_mul_proj`). -/
lemma ntr_proj_symm [NeZero N] {G : GaugeGroup N} (hG : G.LieInput) (X Y : Matrix (Fin N) (Fin N) ℂ) :
    ntr (piProj hG X * Y) = ntr (X * piProj hG Y) := by
  rw [← ntr_mul_proj hG (proj_mem hG X) Y]
  rw [show ntr (X * piProj hG Y) = ntr (piProj hG Y * X) by unfold ntr; rw [Matrix.trace_mul_comm]]
  rw [← ntr_mul_proj hG (proj_mem hG Y) X]
  unfold ntr; rw [Matrix.trace_mul_comm]

lemma proj_sum [NeZero N] {G : GaugeGroup N} (hG : G.LieInput) {ι : Type*} (s : Finset ι)
    (f : ι → Matrix (Fin N) (Fin N) ℂ) : piProj hG (∑ i ∈ s, f i) = ∑ i ∈ s, piProj hG (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    simpa using proj_smul hG 0 (0 : Matrix (Fin N) (Fin N) ℂ)
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, proj_add, ih]

/-- **`π` commutes with `Δ'_𝖺(𝐔)` of the fine model** when the maps `Ad` of the links of `𝐔` and of the transports
`W(y, x)` of the blocks of the points of `𝐁` commute with `π` (as they do for elements of `G^c`, `proj_Ad`). -/
theorem DeltaS_comm_pi [NeZero N] {G : GaugeGroup N} (hG : G.LieInput) (U : Config N NF)
    (W : Site NF → Site NF → (Matrix (Fin N) (Fin N) ℂ)ˣ)
    (hU : ∀ μ x Z, piProj hG (Ad (U μ x) Z) = Ad (U μ x) (piProj hG Z))
    (hW : ∀ y ∈ detB S.toDomSeq, ∀ x ∈ Blk S.toDomSeq (jj y) y, ∀ Z,
      piProj hG (Ad (W y x) Z) = Ad (W y x) (piProj hG Z)) (f : Site NF → Matrix (Fin N) (Fin N) ℂ) :
    SequenceOperators.piF0 hG Set.univ (DeltaS S.toDomSeq U W f) =
      DeltaS S.toDomSeq U W (SequenceOperators.piF0 hG Set.univ f) := by
  set π := SequenceOperators.piF0 hG (Set.univ : Set (Site NF))
  have hπx : ∀ (g : Site NF → Matrix (Fin N) (Fin N) ℂ) x, π g x = piProj hG (g x) := fun g x => by
    simp [π, SequenceOperators.piF0, Set.indicator_apply]
  have hP0 : ∀ g g' : Site NF → Matrix (Fin N) (Fin N) ℂ, P0 (π g) g' = P0 g (π g') := fun g g' => by
    simp only [P0, SequenceOperators.pairForm0, wpair_apply, hπx]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [ntr_proj_symm]
  have hneg : ∀ Z : Matrix (Fin N) (Fin N) ℂ, piProj hG (-Z) = -piProj hG Z := fun Z => by
    simpa using proj_smul hG (-1) Z
  have hDU : ∀ g μ x, DU U (π g) μ x = piProj hG (DU U g μ x) := fun g μ x => by
    calc DU U (π g) μ x = Ad (U μ x) (piProj hG (g (x + unit NF μ))) - piProj hG (g x) := by
          simp only [DU, hπx]
      _ = piProj hG (Ad (U μ x) (g (x + unit NF μ))) - piProj hG (g x) := by rw [hU]
      _ = piProj hG (DU U g μ x) := by
          rw [DU, sub_eq_add_neg, sub_eq_add_neg, proj_add, hneg]
  have havg : ∀ g, ∀ y ∈ detB S.toDomSeq, avgW S.toDomSeq W y (π g) = piProj hG (avgW S.toDomSeq W y g) := by
    intro g y hy
    obtain ⟨hlat, hjk, -⟩ := detB_facts S hy
    unfold avgW
    rw [proj_smul, proj_sum]
    have hs : ∑ o ∈ DiscretePoincare.box 4 (S.toDomSeq.L ^ jj y),
        Ad (W y (SmallFieldBlocks.phi S.toDomSeq (jj y) y o)) (π g (SmallFieldBlocks.phi S.toDomSeq (jj y) y o)) =
        ∑ o ∈ DiscretePoincare.box 4 (S.toDomSeq.L ^ jj y),
          piProj hG (Ad (W y (SmallFieldBlocks.phi S.toDomSeq (jj y) y o)) (g (SmallFieldBlocks.phi S.toDomSeq (jj y) y o))) :=
      Finset.sum_congr rfl fun o ho => by rw [hπx, hW y hy _ (phi_mem (S := S.toDomSeq) _ hjk hlat ho)]
    rw [hs]
  have hPhi : ∀ g g', Phi S.toDomSeq U W (π g) g' = Phi S.toDomSeq U W g (π g') := fun g g' => by
    unfold Phi
    exact congrArg₂ (· + ·)
      (Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun μ _ => by rw [hDU, hDU, ntr_proj_symm])
      (Finset.sum_congr rfl fun y hy => by rw [havg g y hy, havg g' y hy, ntr_proj_symm])
  have hnd := P0_nondeg (N := N) (n := NF)
  rw [← sub_eq_zero]
  refine hnd.1 _ fun g => ?_
  rw [map_sub, LinearMap.sub_apply, hP0, DeltaS_spec, DeltaS_spec, hPhi, sub_self]

/-- The links of `e^{iX}` lie in `G^c` for a form `X` with values in `𝔤^c`. -/
lemma cfgX_mem_Gc {G : GaugeGroup N} {X : Fin 4 → Site NF → Matrix (Fin N) (Fin N) ℂ} (hX : ∀ μ x, X μ x ∈ G.lieC)
    (μ : Fin 4) (x : Site NF) : cfgX X μ x ∈ G.complexified :=
  Subgroup.subset_closure ⟨X μ x, hX μ x, rfl⟩

/-- **`G' = a₀²πGp'(𝐔, W_𝐔)` at `𝐔 = e^{iX}`** (bridge (B3)): for `X` with values in `𝔤^c`, if the transports `W_𝐔` of
the blocks of the points of `𝐁` lie in `G^c` (`lem:block-average-transports`) and the compressed kernel of
`Δ'_𝖺(𝐔)` is invertible (`Gp_eq`, `DeltaS_comm_pi`, `proj_Ad`). -/
theorem Gp_eq_Gc [NeZero N] {G : GaugeGroup N} (hG : G.LieInput) {X : Fin 4 → Site NF → Matrix (Fin N) (Fin N) ℂ}
    (hX : ∀ μ x, X μ x ∈ G.lieC) (ΩD : Set (Site NF))
    (hWc : ∀ y ∈ detB S.toDomSeq, ∀ x ∈ Blk S.toDomSeq (jj y) y, Wf S (cfgX X) y x ∈ G.complexified)
    (hK : IsUnit (CompressedInverse.ckern (piD ΩD) (DeltaS S.toDomSeq (cfgX X) (Wf S (cfgX X))))) :
    SequenceOperators.Gp S hG (fun _ => True) (fun W => LogM (W : Matrix (Fin N) (Fin N) ℂ)) (cfgX X) 1 ΩD =
      (((SequenceAverages.a0 S : ℝ) : ℂ) ^ 2) •
        (SequenceOperators.piF0 hG Set.univ * Gp' S.toDomSeq (cfgX X) (Wf S (cfgX X)) ΩD) :=
  Gp_eq S hG (cfgX X) ΩD
    (DeltaS_comm_pi S hG (cfgX X) (Wf S (cfgX X)) (fun μ x Z => proj_Ad hG (cfgX_mem_Gc S hX μ x) Z)
      (fun y hy x hx Z => proj_Ad hG (hWc y hy x hx) Z)) hK

/-- **The transports `W_𝐔` lie in `G^c`** (`lem:block-average-transports`, at `𝐔 = e^{iX}`): for a regular field `X` with
values in `𝔤^c` and `α₁L < c`, and `G ⊂ G^c`, `W_𝐔(y, x) ∈ G^c` on the blocks of the points of `𝐁`
(`block_transports_mem_Gc_from_data`, applied to the levels of `a + E`, `a` the field `X` cut off at the bound of the
region and `E = X - a` vanishing on the region). -/
theorem Wf_mem_Gc (G : GaugeGroup N) (hGc : IsClosed G.mats) :
    ∃ c : ℝ, 0 < c ∧ ∀ (hRM : 2 * (S.L : ℝ) ≤ ((S.R * S.L ^ S.mM : ℕ) : ℝ))
      (hn : ∀ l, 4 * SequenceAverages.hS S + 4 ≤ MultiscaleAverages.nn (SequenceAverages.hS S) S.mT S.k l)
      (hGG : G.carrier ≤ G.complexified)
      {X : Fin 4 → Site NF → Matrix (Fin N) (Fin N) ℂ} {α₁ : ℝ} (hX : RegField S X α₁) (hα0 : 0 ≤ α₁)
      (hXc : ∀ μ x, X μ x ∈ G.lieC) (hαc : α₁ * S.L < c),
      ∀ y ∈ detB S.toDomSeq, ∀ x ∈ Blk S.toDomSeq (jj y) y, Wf S (cfgX X) y x ∈ G.complexified := by
  classical
  set h := SequenceAverages.hS S
  have hh := one_le_hS S S.three_le_L
  obtain ⟨cG, CG, hcG, hCG, hmem⟩ := RelativeAverage.block_transports_mem_Gc_from_data G hGc h hh
  set c := min cG (1 / (4 * (CG + 1)))
  have hc0 : 0 < c := lt_min hcG (by positivity)
  refine ⟨c, hc0, ?_⟩
  intro hRM hn hGG X α₁ hX hα0 hXc hαc y hy x hx
  obtain ⟨hlat, hjk, -⟩ := detB_facts S hy
  set j := jj y
  set base := LevelsBridge.baseOf h S.mT S.k (c0Of S hlat) j
  set Lr : ℝ := ((2 * h + 1 : ℕ) : ℝ)
  have hLr : Lr = S.L := Lr_hS S
  set b : ℝ := α₁ * S.L * ((S.L : ℝ) ^ j)⁻¹
  set aX : Fin 4 → Site NF → Matrix (Fin N) (Fin N) ℂ := fun ρ z => if ‖X ρ z‖ ≤ b then X ρ z else 0
  set E : Fin 4 → Site NF → Matrix (Fin N) (Fin N) ℂ := fun ρ z => X ρ z - aX ρ z
  set Wfa : (Fin 4 → Site NF → Matrix (Fin N) (Fin N) ℂ) →
      ∀ l, Config N (MultiscaleAverages.nn h S.mT S.k l) := fun a l =>
    MultiscaleAverages.Mpow h S.mT S.k (fun _ => True) (fun W => LogM (W : Matrix (Fin N) (Fin N) ℂ))
      (AverageHolo.moveC RelativeAverage.oneC (a + E)) l
  have hE0 : ∀ ρ x', Lat (Lz h) 0 x' → RelativeAverage.Rg h j 0 0 x' →
      RelativeAverage.Rg h j 0 0 (x' + Lz h ^ 0 • Pi.single ρ 1) → E ρ (img h (base 0) 0 x') = 0 := by
    intro ρ x' _ h1 h2
    rw [show base 0 = y from baseOf_zero S hlat, img_zero]
    have hb : ‖X ρ (y + fun σ => ((x' σ : ℤ) : ZMod NF))‖ ≤ b := detB_region_field S hRM hy hX hα0 ρ x' h1 h2
    simp only [E, aX]
    rw [if_pos hb, sub_self]
  have hlt : ∀ l, l < j → l < S.k := fun l hl => lt_of_lt_of_le hl hjk
  have hup : ∀ l, l < j → ∀ x', Lat (Lz h) (l + 1) x' →
      MultiscaleAverages.up h S.mT S.k l (img h (base (l + 1)) (l + 1) x') = img h (base l) l x' := fun l hl x' hx' =>
    LevelsBridge.up_img h S.mT S.k base l (hlt l hl)
      (LevelsBridge.base_up h S.mT S.k (c0Of S hlat) j l hl (hlt l hl)) x' hx'
  have hW := hmem j 0 (MultiscaleAverages.nn h S.mT S.k) hn base (fun _ => RelativeAverage.oneC)
    (fun a => LevelsBridge.Bchain h S.mT S.k a) (fun a => LevelsBridge.gchain h S.mT S.k a) Wfa (fun _ => 0) c 0
    (fun _ _ _ => G.carrier.one_mem)
    (fun l hl ρ x' hx' _ _ => ⟨fun μ' ν' z _ => by simp [LevelsBridge.plaq_oneC, RegularAverages.hs_zero'],
      (RelativeAverage.avgM_oneC _ _ _).symm, fun a =>
        ⟨LevelsBridge.mpow_level h S.mT S.k _ (c0Of S hlat) j l hl (hlt l hl) ρ x' hx', by
          show RelativeAverage.relLog RelativeAverage.oneC (LevelsBridge.Bchain h S.mT S.k a l)
            (MultiscaleAverages.up h S.mT S.k l (img h (base (l + 1)) (l + 1) x')) ρ h = _
          rw [hup l hl x' hx']⟩⟩)
    (fun l hl x' hx' _ a => by
      show LevelsBridge.gchain h S.mT S.k a l (MultiscaleAverages.up h S.mT S.k l (img h (base (l + 1)) (l + 1) x')) *
        RelativeAverage.siteFactor RelativeAverage.oneC (LevelsBridge.Bchain h S.mT S.k a l)
          (MultiscaleAverages.up h S.mT S.k l (img h (base (l + 1)) (l + 1) x')) h = _
      rw [hup l hl x' hx'])
    (fun _ _ => rfl)
    (fun a ρ x' hx' h1 h2 => ⟨by
        show AverageHolo.moveC RelativeAverage.oneC (a + E) ρ (img h (base 0) 0 x') =
          AverageHolo.moveC RelativeAverage.oneC a ρ (img h (base 0) 0 x')
        simp only [AverageHolo.moveC, Pi.add_apply, hE0 ρ x' hx' h1 h2, add_zero], rfl⟩)
    (fun l _ => ⟨le_rfl, by simp⟩) hc0 le_rfl hcG.le (min_le_left _ _)
    (by
      have h1 : c ≤ 1 / (4 * (CG + 1)) := min_le_right _ _
      have h2 : CG * (0 + 2 * c) ≤ CG * (2 * (1 / (4 * (CG + 1)))) := by
        have := mul_le_mul_of_nonneg_left (by linarith : 0 + 2 * c ≤ 2 * (1 / (4 * (CG + 1)))) hCG
        exact this
      have h3 : CG * (2 * (1 / (4 * (CG + 1)))) ≤ 1 := by
        rw [show CG * (2 * (1 / (4 * (CG + 1)))) = CG / (2 * (CG + 1)) by field_simp; ring]
        rw [div_le_one (by positivity)]; linarith
      linarith)
    hGG aX
    (fun ρ z => by
      simp only [aX]; split_ifs
      · exact hXc ρ z
      · exact ⟨0, G.zero_mem_lie, 0, G.zero_mem_lie, by simp⟩)
    (by
      have hpos : (0 : ℝ) < ((S.L : ℝ) ^ j)⁻¹ := by have := S.Lpos; positivity
      have hb' : b < c * (Lr ^ j)⁻¹ := by
        rw [hLr]; simp only [b]; exact mul_lt_mul_of_pos_right hαc hpos
      refine lt_of_le_of_lt ?_ hb'
      refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun ρ => (pi_norm_le_iff_of_nonneg (by positivity)).2 fun z => ?_
      simp only [aX]; split_ifs with hz
      · exact hz
      · rw [norm_zero]; positivity)
    j le_rfl 0 (fun σ => dvd_zero _) (RB_top S j 0).2.1
    ((RelativeAverage.ptEquiv h j).symm
      (fun σ => ⟨SmallFieldBlocks.psi S.toDomSeq j y x σ % (2 * h + 1) ^ j, Nat.mod_lt _ (by positivity)⟩))
  have hXE : aX + E = X := by funext ρ z; simp only [E, Pi.add_apply]; abel
  have hWa : Wfa aX = fun l => MultiscaleAverages.Mpow h S.mT S.k (fun _ => True)
      (fun W => LogM (W : Matrix (Fin N) (Fin N) ℂ)) (cfgX X) l := by
    funext l
    simp only [Wfa, hXE]
    congr 1
    funext ρ z; simp [cfgX, AverageHolo.moveC, RelativeAverage.oneC]
  rw [hWa] at hW
  unfold Wf
  rw [dif_pos hlat]
  exact hW

/-- **Bridge (B3) for `G'`**: there is `c > 0` such that for a regular field `X` with values in `𝔤^c` and `α₁L < c`
(and `G ⊂ G^c`), whenever the compressed kernel of `Δ'_𝖺(𝐔)` is invertible, the operator `G'` of the concrete layer
at `𝐔 = e^{iX}`, `𝖺 = 1`, is `a₀²πGp'(𝐔, W_𝐔)` (`Gp_eq_Gc`, `Wf_mem_Gc`). -/
theorem Gp_bridge [NeZero N] (G : GaugeGroup N) (hGc : IsClosed G.mats) (hG : G.LieInput) :
    ∃ c : ℝ, 0 < c ∧ ∀ (hRM : 2 * (S.L : ℝ) ≤ ((S.R * S.L ^ S.mM : ℕ) : ℝ))
      (hn : ∀ l, 4 * SequenceAverages.hS S + 4 ≤ MultiscaleAverages.nn (SequenceAverages.hS S) S.mT S.k l)
      (hGG : G.carrier ≤ G.complexified)
      {X : Fin 4 → Site NF → Matrix (Fin N) (Fin N) ℂ} {α₁ : ℝ} (hX : RegField S X α₁) (hα0 : 0 ≤ α₁)
      (hXc : ∀ μ x, X μ x ∈ G.lieC) (hαc : α₁ * S.L < c) (ΩD : Set (Site NF))
      (hK : IsUnit (CompressedInverse.ckern (piD ΩD) (DeltaS S.toDomSeq (cfgX X) (Wf S (cfgX X))))),
      SequenceOperators.Gp S hG (fun _ => True) (fun W => LogM (W : Matrix (Fin N) (Fin N) ℂ)) (cfgX X) 1 ΩD =
        (((SequenceAverages.a0 S : ℝ) : ℂ) ^ 2) •
          (SequenceOperators.piF0 hG Set.univ * Gp' S.toDomSeq (cfgX X) (Wf S (cfgX X)) ΩD) := by
  obtain ⟨c, hc, hW⟩ := Wf_mem_Gc S G hGc
  exact ⟨c, hc, fun hRM hn hGG X α₁ hX hα0 hXc hαc ΩD hK =>
    Gp_eq_Gc S hG hXc ΩD (hW hRM hn hGG hX hα0 hXc hαc) hK⟩

end SFBounds
end CoreLean

end
