/-
The inputs at the levels, localised (BALABAN_CORE.tex `615c66b253fe`, `prop:relative-average`, `def:relative-average-order`,
`prop:relative-average-order`). The value of `Q_j(U)A` and of `B^{(j)}` at a bond of the level `j` depends only on the
bonds which feed into it, level by level, through the boxes `B(c₋) ∪ B(c₊)` of the relative averages; the conditions at
the levels (`prop:relative-average` at `M^l(U)`) are needed there only. This replaces the hypotheses over all sites of
the tori `T^{(l)}` of `QLieC.RayLieC`, `RemainderLink.DiffLevel`, `RemainderLink.AnLevel`, which are stronger than the
core's regularity (control on the domains `Ω_j`).

* `relLog_restrict`, `Qlin_restrict`: `(1/i)log𝓜_V(B)(c)` and `Q(V)B(c)` depend on `B` only on the bonds of the box of
  `c` (`RelativeAverage.relAvg_local`); the latter unconditionally (where the map is not differentiable both
  derivatives vanish).
* `ConeClosed Fam K`: a family `Fam l` of bonds of the levels `l ≤ K` is closed under this dependence: with `(κ, y)` in
  `Fam (l + 1)`, every bond of the box of `Ly` lies in `Fam l`. The minimal such family above a bond `c` of the level
  `j` is the set of the bonds on which `c` depends, which lie in the regions `B^{j-l}(c₋) ∪ B^{j-l}(c₊)` of
  `prop:relative-average-order`.
* `RayAt V y κ h`, `AnAt V y κ h`: the conditions at one bond of one level.
* `Qcomp_mem_cone`: `Q_j(U)B` has values in `𝔤^c` on `Fam j` if `B` has on `Fam 0` and `RayAt` holds at the boxes of
  the bonds of the family; `Bseq_comp_analyticAt`: the components of `B^{(j)}` on `Fam j` are analytic at `0` if
  `AnAt` holds there.
-/
import CoreLean.RemainderAnalytic
import CoreLean.QLieC
import CoreLean.SequenceSymmetry

open Filter Topology
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace CoreLean
namespace LocalLevels

open Lattices SequenceIndex MultiscaleAverages SequenceAverages SequenceOperators PairConcrete RelativeAverage
  RemainderLink

attribute [local instance] Classical.propDecidable

variable {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "GLN" => (Matrix (Fin N) (Fin N) ℂ)ˣ

section OneLevel

variable {n : ℕ} [NeZero n]

/-- The restriction `B ↦ restrictF B S` as a continuous linear map. -/
def restrictL (S : Site n → Prop) : (Fin 4 → Site n → Mat) →L[ℂ] (Fin 4 → Site n → Mat) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun B => restrictF B S
      map_add' := fun B B' => by
        funext ν z; simp only [restrictF, Pi.add_apply]; split_ifs <;> simp
      map_smul' := fun c B => by
        funext ν z; simp only [restrictF, Pi.smul_apply, RingHom.id_apply]; split_ifs <;> simp }

lemma restrictL_apply (S : Site n → Prop) (B : Fin 4 → Site n → Mat) : restrictL S B = restrictF B S := rfl

/-- `(1/i)log𝓜_V(B)(c)` depends on `B` only on the bonds of the box of `c`. -/
lemma relLog_restrict {h : ℕ} (hn : 4 * h + 2 ≤ n) (V : Config N n) (B : Fin 4 → Site n → Mat) (y : Site n)
    (κ : Fin 4) : relLog V B y κ h = relLog V (restrictF B (InBoxB y h κ)) y κ h := by
  have hB : ∀ ν z, InBoxB y h κ z → InBoxB y h κ (z + unit n ν) →
      V ν z = V ν z ∧ B ν z = restrictF B (InBoxB y h κ) ν z := fun ν z h1 h2 => by
    refine ⟨rfl, ?_⟩
    simp only [restrictF]
    rw [if_pos ⟨h1, h2⟩]
  simp only [relLog]
  rw [relAvg_local hn hB]

/-- **`Q(V)B(c)` depends on `B` only on the bonds of the box of `c`.** -/
lemma Qlin_restrict {h : ℕ} (hn : 4 * h + 2 ≤ n) (V : Config N n) (B : Fin 4 → Site n → Mat) (y : Site n)
    (κ : Fin 4) : Qlin V y κ h B = Qlin V y κ h (restrictF B (InBoxB y h κ)) := by
  have e : (fun B' => relLog V B' y κ h) = (fun B' => relLog V B' y κ h) ∘ restrictL (InBoxB y h κ) :=
    funext fun B' => relLog_restrict hn V B' y κ
  have hD : fderiv ℂ (fun B' => relLog V B' y κ h) 0 =
      (fderiv ℂ (fun B' => relLog V B' y κ h) 0).comp (restrictL (N := N) (InBoxB y h κ)) := by
    by_cases hd : DifferentiableAt ℂ (fun B' => relLog V B' y κ h) 0
    · have hR0 : restrictL (N := N) (InBoxB y h κ) 0 = 0 := map_zero _
      have hd' : DifferentiableAt ℂ (fun B' => relLog V B' y κ h) (restrictL (N := N) (InBoxB y h κ) 0) := by
        rw [hR0]; exact hd
      calc fderiv ℂ (fun B' => relLog V B' y κ h) 0
          = fderiv ℂ ((fun B' => relLog V B' y κ h) ∘ restrictL (InBoxB y h κ)) 0 :=
            congrArg (fun g => fderiv ℂ g 0) e
        _ = (fderiv ℂ (fun B' => relLog V B' y κ h) (restrictL (N := N) (InBoxB y h κ) 0)).comp
            (fderiv ℂ (restrictL (N := N) (InBoxB y h κ)) 0) :=
            fderiv_comp 0 hd' (restrictL (InBoxB y h κ)).differentiableAt
        _ = (fderiv ℂ (fun B' => relLog V B' y κ h) 0).comp (restrictL (N := N) (InBoxB y h κ)) := by
            rw [hR0, ContinuousLinearMap.fderiv]
    · rw [fderiv_zero_of_not_differentiableAt hd]
      rfl
  simp only [Qlin]
  conv_lhs => rw [ContinuousLinearMap.smul_apply, hD]
  rfl

end OneLevel

/-! ### Families of bonds closed under the dependence -/

variable {G : GaugeGroup N}

/-- The condition of `prop:relative-average` at one bond: `(1/i)log𝓜_V(tB)(c) ∈ 𝔤^c` for small `t`. -/
def RayAt (G : GaugeGroup N) {n : ℕ} [NeZero n] (V : Config N n) (y : Site n) (κ : Fin 4) (h : ℕ) : Prop :=
  ∀ B : Form1 N n, (∀ ρ z, B ρ z ∈ G.lieC) → ∀ᶠ t : ℂ in 𝓝 0, relLog V (t • B) y κ h ∈ G.lieC

/-- The analyticity of `B ↦ (1/i)log𝓜_V(B)(c)` at `0` at one bond. -/
def AnAt {n : ℕ} [NeZero n] (V : Config N n) (y : Site n) (κ : Fin 4) (h : ℕ) : Prop :=
  AnalyticAt ℂ (fun B => relLog V B y κ h) 0

lemma Qlin_mem_at (hG : G.LieInput) {n : ℕ} [NeZero n] {V : Config N n} {h : ℕ} {y : Site n} {κ : Fin 4}
    (hV : RayAt G V y κ h) {B : Form1 N n} (hB : ∀ ρ z, B ρ z ∈ G.lieC) : Qlin V y κ h B ∈ G.lieC := by
  have hd := QLieC.fderiv_mem_of_eventually (fun B' => relLog V B' y κ h) (GaugeGroup.lieCSubmodule hG) B
    (by filter_upwards [hV B hB] with t ht; rwa [GaugeGroup.mem_lieCSubmodule])
  rw [← GaugeGroup.mem_lieCSubmodule hG]
  simp only [Qlin, ContinuousLinearMap.smul_apply]
  exact Submodule.smul_mem _ _ hd

lemma nn_ge (h m k l : ℕ) (hl : l < k) : 4 * h + 2 ≤ nn h m k l := by
  unfold nn
  have : 2 * h + 1 ≤ (2 * h + 1) ^ (m + (k - l)) := Nat.le_self_pow (by omega) _
  omega

variable (h m k : ℕ)

/-- **A family of bonds closed under the dependence of the averages**, on the levels `l ≤ K`. -/
def ConeClosed (Fam : ∀ l, Set (Fin 4 × Site (nn h m k l))) (K : ℕ) : Prop :=
  ∀ l < K, ∀ κ y, (κ, y) ∈ Fam (l + 1) → ∀ ρ z, InBoxB (up h m k l y) h κ z →
    InBoxB (up h m k l y) h κ (z + unit _ ρ) → (ρ, z) ∈ Fam l

/-- **`Q_j(U)B` has values in `𝔤^c` on the family**, if `B` has on `Fam 0` and `RayAt` holds at the boxes of the bonds
of the family. -/
theorem Qcomp_mem_cone (hG : G.LieInput) (inN : GLN → Prop) (log : GLN → Mat) (U : Config N (nn h m k 0))
    (Fam : ∀ l, Set (Fin 4 × Site (nn h m k l))) (K : ℕ) (hK : K ≤ k) (hcl : ConeClosed h m k Fam K)
    (hray : ∀ l < K, ∀ κ y, (κ, y) ∈ Fam (l + 1) → RayAt G (Mpow h m k inN log U l) (up h m k l y) κ h)
    {B : Form1 N (nn h m k 0)} (hB : ∀ ρ z, (ρ, z) ∈ Fam 0 → B ρ z ∈ G.lieC) :
    ∀ j ≤ K, ∀ κ y, (κ, y) ∈ Fam j → Qcomp h m k inN log U j B κ y ∈ G.lieC
  | 0, _ => fun κ y hy => by rw [Qcomp_zero]; exact hB κ y hy
  | j + 1, hj => fun κ y hy => by
      have h0 : (0 : Mat) ∈ G.lieC := by rw [← GaugeGroup.mem_lieCSubmodule hG]; exact Submodule.zero_mem _
      rw [Qcomp_succ, LinearMap.comp_apply, Qstep_apply,
        Qlin_restrict (nn_ge h m k j (by omega))]
      refine Qlin_mem_at hG (hray j (by omega) κ y hy) fun ρ z => ?_
      simp only [restrictF]
      split_ifs with hz
      · exact Qcomp_mem_cone hG inN log U Fam K hK hcl hray hB j (by omega) ρ z
          (hcl j (by omega) κ y hy ρ z hz.1 hz.2)
      · exact h0

/-- **The components of `B^{(j)}` on the family are analytic at `0`** if `AnAt` holds at the boxes of the bonds of the
family. -/
theorem Bseq_comp_analyticAt (inN : GLN → Prop) (log : GLN → Mat) (U : Config N (nn h m k 0))
    (Fam : ∀ l, Set (Fin 4 × Site (nn h m k l))) (K : ℕ) (hK : K ≤ k) (hcl : ConeClosed h m k Fam K)
    (han : ∀ l < K, ∀ κ y, (κ, y) ∈ Fam (l + 1) → AnAt (Mpow h m k inN log U l) (up h m k l y) κ h) :
    ∀ j ≤ K, ∀ κ y, (κ, y) ∈ Fam j → AnalyticAt ℂ (fun B0 => Bseq h m k inN log U B0 j κ y) 0
  | 0, _ => fun κ y _ =>
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Site (nn h m k 0) => Mat) y).comp
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 4 => Site (nn h m k 0) → Mat) κ)).analyticAt 0
  | j + 1, hj => fun κ y hy => by
      have hn := nn_ge h m k j (by omega)
      set S := InBoxB (up h m k j y) h κ
      have e : (fun B0 => Bseq h m k inN log U B0 (j + 1) κ y) =
          fun B0 => relLog (Mpow h m k inN log U j) (restrictF (Bseq h m k inN log U B0 j) S) (up h m k j y) κ h :=
        funext fun B0 => relLog_restrict hn _ _ _ _
      rw [e]
      have hin : AnalyticAt ℂ (fun B0 => restrictF (Bseq h m k inN log U B0 j) S) 0 := by
        refine analyticAt_pi_iff.2 fun ρ => analyticAt_pi_iff.2 fun z => ?_
        by_cases hz : S z ∧ S (z + unit _ ρ)
        · have hc := Bseq_comp_analyticAt inN log U Fam K hK hcl han j (by omega) ρ z
            (hcl j (by omega) κ y hy ρ z hz.1 hz.2)
          simp only [restrictF, if_pos hz]
          exact hc
        · simp only [restrictF, if_neg hz]
          exact analyticAt_const
      have h0 : restrictF (Bseq h m k inN log U 0 j) S = 0 := by
        rw [Bseq_zero]; funext ρ z; simp [restrictF]
      exact (han j (by omega) κ y hy).comp_of_eq hin h0

/-- **`D B^{(j)}(0) = L^jQ_j(U)` on the family**, componentwise, if `AnAt` holds at the boxes of the bonds of the
family. -/
theorem Bseq_comp_hasFDerivAt (inN : GLN → Prop) (log : GLN → Mat) (U : Config N (nn h m k 0))
    (Fam : ∀ l, Set (Fin 4 × Site (nn h m k l))) (K : ℕ) (hK : K ≤ k) (hcl : ConeClosed h m k Fam K)
    (han : ∀ l < K, ∀ κ y, (κ, y) ∈ Fam (l + 1) → AnAt (Mpow h m k inN log U l) (up h m k l y) κ h) :
    ∀ j ≤ K, ∀ κ y, (κ, y) ∈ Fam j → HasFDerivAt (fun B0 => Bseq h m k inN log U B0 j κ y)
      (LinearMap.toContinuousLinearMap ((((2 * h + 1 : ℕ) : ℂ)) ^ j •
        ((LinearMap.proj y) ∘ₗ (LinearMap.proj κ) ∘ₗ Qcomp h m k inN log U j))) 0
  | 0, _ => fun κ y _ => by
      refine (((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Site (nn h m k 0) => Mat) y).comp
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 4 => Site (nn h m k 0) → Mat) κ)).hasFDerivAt
        (x := 0)).congr_fderiv ?_
      ext B : 1
      change B κ y = ((((2 * h + 1 : ℕ) : ℂ)) ^ 0 • Qcomp h m k inN log U 0 B) κ y
      rw [pow_zero, one_smul, Qcomp_zero, LinearMap.id_apply]
  | j + 1, hj => fun κ y hy => by
      have hn := nn_ge h m k j (by omega)
      set S := InBoxB (up h m k j y) h κ
      set V := Mpow h m k inN log U j
      set Lc : ℂ := ((2 * h + 1 : ℕ) : ℂ)
      set D : Form1 N (nn h m k 0) →L[ℂ] Form1 N (nn h m k j) :=
        LinearMap.toContinuousLinearMap (Lc ^ j • Qcomp h m k inN log U j)
      have e : (fun B0 => Bseq h m k inN log U B0 (j + 1) κ y) =
          (fun B => relLog V B (up h m k j y) κ h) ∘ fun B0 => restrictF (Bseq h m k inN log U B0 j) S :=
        funext fun B0 => relLog_restrict hn _ _ _ _
      rw [e]
      -- the restricted forms
      have hin : HasFDerivAt (fun B0 => restrictF (Bseq h m k inN log U B0 j) S) ((restrictL S).comp D) 0 := by
        refine hasFDerivAt_pi'' fun ρ => hasFDerivAt_pi'' fun z => ?_
        by_cases hz : S z ∧ S (z + unit _ ρ)
        · have hc := Bseq_comp_hasFDerivAt inN log U Fam K hK hcl han j (by omega) ρ z
            (hcl j (by omega) κ y hy ρ z hz.1 hz.2)
          have ef : (fun B0 => restrictF (Bseq h m k inN log U B0 j) S ρ z) =
              fun B0 => Bseq h m k inN log U B0 j ρ z :=
            funext fun B0 => by simp only [restrictF, if_pos hz]
          rw [ef]
          refine hc.congr_fderiv ?_
          ext B : 1
          change (Lc ^ j • Qcomp h m k inN log U j B) ρ z = restrictF (Lc ^ j • Qcomp h m k inN log U j B) S ρ z
          simp only [restrictF, if_pos hz]
        · have ef : (fun B0 => restrictF (Bseq h m k inN log U B0 j) S ρ z) = fun _ => (0 : Mat) :=
            funext fun B0 => by simp only [restrictF, if_neg hz]
          rw [ef]
          refine (hasFDerivAt_const (0 : Mat) (0 : Form1 N (nn h m k 0))).congr_fderiv ?_
          ext B : 1
          change (0 : Mat) = restrictF (Lc ^ j • Qcomp h m k inN log U j B) S ρ z
          simp only [restrictF, if_neg hz]
      have h0 : restrictF (Bseq h m k inN log U 0 j) S = 0 := by
        rw [Bseq_zero]; funext ρ z; simp [restrictF]
      have hg : HasFDerivAt (fun B => relLog V B (up h m k j y) κ h)
          (fderiv ℂ (fun B => relLog V B (up h m k j y) κ h) 0)
          ((fun B0 => restrictF (Bseq h m k inN log U B0 j) S) 0) := by
        show HasFDerivAt _ _ (restrictF (Bseq h m k inN log U 0 j) S)
        rw [h0]; exact (han j (by omega) κ y hy).differentiableAt.hasFDerivAt
      refine (hg.comp 0 hin).congr_fderiv ?_
      ext B : 1
      have hQ : ∀ W, fderiv ℂ (fun B => relLog V B (up h m k j y) κ h) 0 W = Lc • Qlin V (up h m k j y) κ h W :=
        fun W => by
          simp only [Qlin, ContinuousLinearMap.smul_apply, smul_smul]
          rw [mul_inv_cancel₀ (RemainderLink.Lc_ne h), one_smul]
      change fderiv ℂ (fun B => relLog V B (up h m k j y) κ h) 0 (restrictF (Lc ^ j • Qcomp h m k inN log U j B) S) =
        (Lc ^ (j + 1) • Qcomp h m k inN log U (j + 1) B) κ y
      have hs : restrictF (Lc ^ j • Qcomp h m k inN log U j B) S = Lc ^ j • restrictF (Qcomp h m k inN log U j B) S :=
        (restrictL S).map_smul _ _
      rw [hs, map_smul, hQ, ← Qlin_restrict hn, Qcomp_succ, LinearMap.comp_apply, Pi.smul_apply, Pi.smul_apply,
        Qstep_apply, smul_smul, pow_succ]

/-! ### The sequence -/

variable (S : SeqDom)

/-- A family of bonds of the levels `l ≤ k` which contains the bonds of the layers. -/
def HasLayers (Fam : ∀ l, Set (Fin 4 × Site (nn (hS S) S.mT S.k l))) : Prop :=
  ∀ c : LBond S, (c.1.2.2, crd S c.1.1 c.1.2.1) ∈ Fam c.1.1

/-- **`Π_FQΠ = QΠ`** from `RayAt` on a closed family containing the bonds of the layers. -/
theorem hQpres_of_cone (hG : G.LieInput) (inN : GLN → Prop) (log : GLN → Mat) (U : Config N (SequenceAverages.N0 S))
    (ΩD : Set (Site (SequenceAverages.N0 S))) (Fam : ∀ l, Set (Fin 4 × Site (nn (hS S) S.mT S.k l)))
    (hcl : ConeClosed (hS S) S.mT S.k Fam S.k) (hFam : HasLayers S Fam)
    (hray : ∀ l < S.k, ∀ κ y, (κ, y) ∈ Fam (l + 1) →
      RayAt G (Mpow (hS S) S.mT S.k inN log U l) (up (hS S) S.mT S.k l y) κ (hS S))
    (x : Form1 N (SequenceAverages.N0 S)) :
    piFun hG (LBond S) (Qseq S inN log U (piF1 hG ΩD x)) = Qseq S inN log U (piF1 hG ΩD x) := by
  funext c
  simp only [piFun, LinearMap.coe_mk, AddHom.coe_mk]
  refine piProj_self hG ?_
  rw [Qseq_apply]
  exact Qcomp_mem_cone (hS S) S.mT S.k hG inN log U Fam S.k le_rfl hcl hray
    (fun ρ z _ => QLieC.piF1_mem hG ΩD x ρ z) c.1.1 c.2.1 _ _ (hFam c)

/-- **`A ↦ B^{(j)}(c)` is analytic at `0`** from `AnAt` on a closed family containing the bonds of the layers. -/
theorem remMap_analyticAt_cone (inN : GLN → Prop) (log : GLN → Mat) (U : Config N (SequenceAverages.N0 S))
    (Fam : ∀ l, Set (Fin 4 × Site (nn (hS S) S.mT S.k l))) (hcl : ConeClosed (hS S) S.mT S.k Fam S.k)
    (hFam : HasLayers S Fam)
    (han : ∀ l < S.k, ∀ κ y, (κ, y) ∈ Fam (l + 1) →
      AnAt (Mpow (hS S) S.mT S.k inN log U l) (up (hS S) S.mT S.k l y) κ (hS S)) (c : LBond S) :
    AnalyticAt ℂ (remMap S inN log U c) 0 := by
  have hB := Bseq_comp_analyticAt (hS S) S.mT S.k inN log U Fam S.k le_rfl hcl han c.1.1 c.2.1 _ _ (hFam c)
  have hs : AnalyticAt ℂ (fun A : Form1 N (SequenceAverages.N0 S) => aC S • A) 0 :=
    analyticAt_id.fun_const_smul (c := aC S)
  exact hB.comp_of_eq hs (smul_zero _)

/-- **`D(A ↦ B^{(j)}(c))(0) = a_c(Q·)(c)`** from `AnAt` on a closed family containing the bonds of the layers. -/
theorem remMap_hasFDerivAt_cone (inN : GLN → Prop) (log : GLN → Mat) (U : Config N (SequenceAverages.N0 S))
    (Fam : ∀ l, Set (Fin 4 × Site (nn (hS S) S.mT S.k l))) (hcl : ConeClosed (hS S) S.mT S.k Fam S.k)
    (hFam : HasLayers S Fam)
    (han : ∀ l < S.k, ∀ κ y, (κ, y) ∈ Fam (l + 1) →
      AnAt (Mpow (hS S) S.mT S.k inN log U l) (up (hS S) S.mT S.k l y) κ (hS S)) (c : LBond S) :
    HasFDerivAt (remMap S inN log U c) (Lseq S inN log U c) 0 := by
  have hB := Bseq_comp_hasFDerivAt (hS S) S.mT S.k inN log U Fam S.k le_rfl hcl han c.1.1 c.2.1 _ _ (hFam c)
  have hs : HasFDerivAt (fun A : Form1 N (SequenceAverages.N0 S) => aC S • A)
      (aC S • ContinuousLinearMap.id ℂ (Form1 N (SequenceAverages.N0 S))) 0 :=
    (hasFDerivAt_id (0 : Form1 N (SequenceAverages.N0 S))).const_smul (aC S)
  have hB' : HasFDerivAt (fun B0 => Bseq (hS S) S.mT S.k inN log U B0 c.1.1 c.1.2.2 (crd S c.1.1 c.1.2.1))
      (LinearMap.toContinuousLinearMap ((((2 * hS S + 1 : ℕ) : ℂ)) ^ c.1.1 •
        ((LinearMap.proj (crd S c.1.1 c.1.2.1)) ∘ₗ (LinearMap.proj c.1.2.2) ∘ₗ
          Qcomp (hS S) S.mT S.k inN log U c.1.1))) (aC S • (0 : Form1 N (SequenceAverages.N0 S))) := by
    rw [smul_zero]; exact hB
  refine (hB'.comp (0 : Form1 N (SequenceAverages.N0 S)) hs).congr_fderiv ?_
  ext A : 1
  change ((((2 * hS S + 1 : ℕ) : ℂ)) ^ c.1.1 • Qcomp (hS S) S.mT S.k inN log U c.1.1 (aC S • A)) c.1.2.2
      (crd S c.1.1 c.1.2.1) =
    ((c.ac : ℝ) : ℂ) • Qcomp (hS S) S.mT S.k inN log U c.1.1 A c.1.2.2 (crd S c.1.1 c.1.2.1)
  rw [map_smul, smul_smul, Pi.smul_apply, Pi.smul_apply, ac_eq]

/-- **The remainder vanishes to the first order**, from `AnAt` on a closed family containing the bonds of the layers. -/
theorem Cseq_hasFDerivAt_cone (inN : GLN → Prop) (log : GLN → Mat) (U : Config N (SequenceAverages.N0 S))
    (Fam : ∀ l, Set (Fin 4 × Site (nn (hS S) S.mT S.k l))) (hcl : ConeClosed (hS S) S.mT S.k Fam S.k)
    (hFam : HasLayers S Fam)
    (han : ∀ l < S.k, ∀ κ y, (κ, y) ∈ Fam (l + 1) →
      AnAt (Mpow (hS S) S.mT S.k inN log U l) (up (hS S) S.mT S.k l y) κ (hS S)) (c : LBond S) :
    HasFDerivAt (Cseq S inN log U c) (0 : Form1 N (SequenceAverages.N0 S) →L[ℂ] Mat) 0 := by
  have h := (remMap_hasFDerivAt_cone S inN log U Fam hcl hFam han c).sub ((Lseq S inN log U c).hasFDerivAt (x := 0))
  rw [sub_self] at h
  exact h

/-- **`𝖢^{(2)}` is symmetric**, from `AnAt` on a closed family containing the bonds of the layers. -/
theorem C2_symm_cone (inN : GLN → Prop) (log : GLN → Mat) (U : Config N (SequenceAverages.N0 S))
    (Fam : ∀ l, Set (Fin 4 × Site (nn (hS S) S.mT S.k l))) (hcl : ConeClosed (hS S) S.mT S.k Fam S.k)
    (hFam : HasLayers S Fam)
    (han : ∀ l < S.k, ∀ κ y, (κ, y) ∈ Fam (l + 1) →
      AnAt (Mpow (hS S) S.mT S.k inN log U l) (up (hS S) S.mT S.k l y) κ (hS S)) (c : LBond S)
    (A₁ A₂ : Form1 N (SequenceAverages.N0 S)) :
    C2 S inN log U A₁ A₂ c = C2 S inN log U A₂ A₁ c :=
  C2_symm S inN log U c (remMap_analyticAt_cone S inN log U Fam hcl hFam han c).contDiffAt A₁ A₂

/-- **`𝖢^{(2)} = (2a_c)^{-1}D²C_j(0)`**, from `AnAt` on a closed family containing the bonds of the layers. -/
theorem C2_eq_remainder_cone (inN : GLN → Prop) (log : GLN → Mat) (U : Config N (SequenceAverages.N0 S))
    (Fam : ∀ l, Set (Fin 4 × Site (nn (hS S) S.mT S.k l))) (hcl : ConeClosed (hS S) S.mT S.k Fam S.k)
    (hFam : HasLayers S Fam)
    (han : ∀ l < S.k, ∀ κ y, (κ, y) ∈ Fam (l + 1) →
      AnAt (Mpow (hS S) S.mT S.k inN log U l) (up (hS S) S.mT S.k l y) κ (hS S)) (c : LBond S)
    (A₁ A₂ : Form1 N (SequenceAverages.N0 S)) :
    C2 S inN log U A₁ A₂ c = (((2 * c.ac : ℝ) : ℂ))⁻¹ • fderiv ℂ (fderiv ℂ (Cseq S inN log U c)) 0 A₁ A₂ :=
  C2_eq_remainder S inN log U c
    ((remMap_analyticAt_cone S inN log U Fam hcl hFam han c).eventually_analyticAt.mono
      fun _ hA => hA.differentiableAt) A₁ A₂

/-- **The polarisation of `Δ^{(2)}`**, from `AnAt` on a closed family containing the bonds of the layers. -/
theorem Delta2_polar_cone [NeZero N] (hG : G.LieInput) (d : Data S N)
    (Fam : ∀ l, Set (Fin 4 × Site (nn (hS S) S.mT S.k l))) (hcl : ConeClosed (hS S) S.mT S.k Fam S.k)
    (hFam : HasLayers S Fam)
    (han : ∀ l < S.k, ∀ κ y, (κ, y) ∈ Fam (l + 1) →
      AnAt (Mpow (hS S) S.mT S.k d.inN d.log d.U l) (up (hS S) S.mT S.k l y) κ (hS S))
    (A₁ A₂ : Form1 N (SequenceAverages.N0 S)) :
    ConcretePairing.pairForm1 (aC S) (Delta2 S hG d A₁) A₂ =
      2 * ConcretePairing.pairForm1 (aC S) (Hpi S hG d (C2 S d.inN d.log d.U A₁ A₂)) d.J :=
  Delta2_polar S hG d (fun c => (remMap_analyticAt_cone S d.inN d.log d.U Fam hcl hFam han c).contDiffAt) A₁ A₂

/-- **`thm:critical`(ii) for a sequence of domains**, any Dirichlet domain and any group, with the conditions of
`prop:relative-average` at the levels required on a closed family containing the bonds of the layers only. -/
theorem critical_ii_sequence_cone [NeZero N] (hG : G.LieInput) (d : Data S N)
    (Fam : ∀ l, Set (Fin 4 × Site (nn (hS S) S.mT S.k l))) (hcl : ConeClosed (hS S) S.mT S.k Fam S.k)
    (hFam : HasLayers S Fam)
    (hray : ∀ l < S.k, ∀ κ y, (κ, y) ∈ Fam (l + 1) →
      RayAt G (Mpow (hS S) S.mT S.k d.inN d.log d.U l) (up (hS S) S.mT S.k l y) κ (hS S))
    (hKG : IsUnit (CompressedInverse.ckern (piF1 hG d.ΩD) (DA S hG d)))
    (hKc : IsUnit (CompressedInverse.ckern (piF1 hG d.ΩD) (DA S hG d - Delta2 S hG d)))
    (hKM0 : IsUnit (CompressedInverse.ckern (piFun hG (LBond S)) (Qseq S d.inN d.log d.U ∘ₗ
      Gs S hG d.inN d.log d.U d.aa d.ΩD (aC_ne S) ∘ₗ QseqStar S d.inN d.log d.U)))
    (hKM : IsUnit (CompressedInverse.ckern (piFun hG (LBond S))
      (Qseq S d.inN d.log d.U ∘ₗ Gc S hG d ∘ₗ QseqStar S d.inN d.log d.U)))
    (Nf : Form1 N (SequenceAverages.N0 S) → Form1 N (SequenceAverages.N0 S))
    (T : Form1 N (SequenceAverages.N0 S) → Form1 N (SequenceAverages.N0 S))
    (X : Form1 N (SequenceAverages.N0 S) → (LBond S → Mat))
    (A0fix : Form1 N (SequenceAverages.N0 S) → Form1 N (SequenceAverages.N0 S))
    (ball : Form1 N (SequenceAverages.N0 S) → Set (Form1 N (SequenceAverages.N0 S)))
    (huniq : ∀ 𝔄, ∀ A₀ ∈ ball 𝔄, CriticalTheorem.Phi0 (Qseq S d.inN d.log d.U) (QseqStar S d.inN d.log d.U)
      (Delta2 S hG d) (Gc S hG d) (CriticalSequence.Minv S hG d) Nf d.J 𝔄 A₀ = A₀ → A₀ = A0fix 𝔄)
    (A A' : Form1 N (SequenceAverages.N0 S)) (hT : T A' = A) (hD : DRD S hG d A' = 0)
    (hX : Qseq S d.inN d.log d.U A' = X A) (hA' : piF1 hG d.ΩD A' = A')
    (hcrit : ∀ δ, piF1 hG d.ΩD δ = δ → Qseq S d.inN d.log d.U δ = 0 →
      ConcretePairing.pairForm1 (aC S) (d.J + (hessLin (aC S) hG (aC_ne S) d.U - Delta2 S hG d) A' + Nf A') δ = 0)
    (hball : A' - H0 S hG d (X A) ∈ ball (H0 S hG d (X A))) :
    A = T (A0fix (H0 S hG d (X A)) + H0 S hG d (X A)) :=
  CriticalSequence.critical_ii_sequence_general S hG d hKG hKc hKM0 hKM
    (hQpres_of_cone S hG d.inN d.log d.U d.ΩD Fam hcl hFam hray) Nf T X A0fix ball huniq A A' hT hD hX hA' hcrit hball

/-- **`thm:critical`(iii), `G̃J = 0`**, with the conditions of `prop:relative-average` at the levels required on a closed
family containing the bonds of the layers only. -/
theorem Gtilde_J_sequence_cone [NeZero N] (hG : G.LieInput) (d : Data S N)
    (Fam : ∀ l, Set (Fin 4 × Site (nn (hS S) S.mT S.k l))) (hcl : ConeClosed (hS S) S.mT S.k Fam S.k)
    (hFam : HasLayers S Fam)
    (hray : ∀ l < S.k, ∀ κ y, (κ, y) ∈ Fam (l + 1) →
      RayAt G (Mpow (hS S) S.mT S.k d.inN d.log d.U l) (up (hS S) S.mT S.k l y) κ (hS S))
    (hK0 : SequenceSymmetry.UnitG' S hG d) (hKM' : SequenceSymmetry.UnitM' S hG d)
    (hKc : IsUnit (CompressedInverse.ckern (piF1 hG d.ΩD) (DA S hG d - Delta2 S hG d)))
    (hKM : IsUnit (CompressedInverse.ckern (piFun hG (LBond S))
      (Qseq S d.inN d.log d.U ∘ₗ Gc S hG d ∘ₗ QseqStar S d.inN d.log d.U)))
    (J : Form1 N (SequenceAverages.N0 S))
    (hJ : ∀ δ, piF1 hG d.ΩD δ = δ → Qseq S d.inN d.log d.U δ = 0 → ConcretePairing.pairForm1 (aC S) J δ = 0) :
    Gtil S hG d J = 0 :=
  SequenceSymmetry.Gtilde_J_sequence S hG d hK0 hKM' hKc hKM
    (hQpres_of_cone S hG d.inN d.log d.U d.ΩD Fam hcl hFam hray) J hJ

end LocalLevels
end CoreLean

end
