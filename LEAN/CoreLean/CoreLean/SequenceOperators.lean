/-
The concrete layer, steps C3 (the averages of `0`-forms), C4, and C5 (`CONCRETE_LAYER.md`): the operators of a sequence
of domains of BALABAN_CORE.tex (`615c66b253fe`, `def:operators`, `def:dirichlet-domain`(i), `def:hessian`).

* `QpStep`, `Qpcomp`: the block average `Q'(V)` of `eq:block-average` at every coarse site, and the composite
  `Q'_j(U) = Q'(U^{(j-1)}) ⋯ Q'(U^{(0)})` of `def:relative-average-order`; `Qpseq`: the average `Q'` of `0`-forms of
  `def:operators`(i), `(Q'λ)(y) = (Q'_j(U)λ)(y)` for `y ∈ Γ_j`; `QpseqStar`, its transpose with respect to `⟨·,·⟩` and
  `Σ_{y ∈ 𝐁}a_{j(y)}⁴tr μ(y)μ'(y)` (`def:operators`(iii)); `aseq`: the numbers `𝖺_j`; `constraintOp0` with the second
  constraint form of `eq:constraint-forms` (`constraintOp0_form`).
* `D0L`, `Ds1L`: `D_U` and `D^*_U` between `0`- and `1`-forms as linear maps, `D^*_U` the transpose of `D_U`
  (`D0L_transpose`); the covariant Laplacian is `D^*_UD_U` (`Lap_eq`).
* `piF0`, `piF1`, `piFun`: the compressions of `def:dirichlet-domain`(i), the indicator of the Dirichlet domain `Ω_D`
  (of its sites, of its bonds) times the projection `π` onto `𝔤^c`, idempotent.
* `DeltaP`, `Gp`, `Rs`, `Ps`, `DeltaA`, `Gs`: `Δ'_𝖺 = Δ_U + Q'^*𝖺Q'`, `G' = (Δ'_𝖺)^{-1}`,
  `R = I - G'Q'^*(Q'G'^2Q'^*)^{-1}Q'G'`, `P = I - R`, `Δ_𝖺 = Δ(U) + DRD^* + Q^*𝖺Q`, `G = (Δ_𝖺)^{-1}`, the inverses taken
  on the compressed forms (`CompressedInverse.cinv`); `R² = R`, `P² = P`, `Q'G'R = 0`, and `G` is a two-sided inverse
  of `Δ_𝖺` on the compressed `1`-forms whenever the inverse exists. `DeltaA_eq` identifies `Δ_𝖺` with the operator
  `Delta_a` of `CriticalTheorem`.
-/
import CoreLean.SequenceAverages
import CoreLean.CompressedInverse
import CoreLean.CubicGradient
import CoreLean.RelativeAverageG

noncomputable section

namespace CoreLean
namespace SequenceOperators

open Lattices SequenceIndex MultiscaleAverages ConcretePairing SequenceAverages CompressedInverse RelativeAverage

variable {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "GLN" => (Matrix (Fin N) (Fin N) ℂ)ˣ

/-! ### The block averages of `0`-forms -/

/-- **The block average** `Q'(V)` at every coarse site, `(Q'(V)λ)(y) = L⁻⁴Σ_{x ∈ B(y)}Ad_{V(Ly, x)}λ(x)`. -/
def QpStep (h m k j : ℕ) (V : Config N (nn h m k j)) : Form0 N (nn h m k j) →ₗ[ℂ] Form0 N (nn h m k (j + 1)) where
  toFun lam y := blockAvg V lam (up h m k j y) h
  map_add' l l' := by
    funext y
    simp only [blockAvg, Pi.add_apply, Ad_add, Finset.sum_add_distrib, smul_add]
  map_smul' c l := by
    funext y
    simp only [blockAvg, Pi.smul_apply, Ad_smul, ← Finset.smul_sum, RingHom.id_apply]
    rw [smul_comm]

lemma QpStep_apply (h m k j : ℕ) (V : Config N (nn h m k j)) (lam : Form0 N (nn h m k j))
    (y : Site (nn h m k (j + 1))) : QpStep h m k j V lam y = blockAvg V lam (up h m k j y) h := rfl

/-- **`Q'_j(U) = Q'(U^{(j-1)}) ⋯ Q'(U^{(0)})`**, `Q'_0 = I`. -/
def Qpcomp (h m k : ℕ) (inN : GLN → Prop) (log : GLN → Mat) (U : Config N (nn h m k 0)) :
    ∀ j, Form0 N (nn h m k 0) →ₗ[ℂ] Form0 N (nn h m k j)
  | 0 => LinearMap.id
  | j + 1 => QpStep h m k j (Mpow h m k inN log U j) ∘ₗ Qpcomp h m k inN log U j

lemma Qpcomp_succ (h m k : ℕ) (inN : GLN → Prop) (log : GLN → Mat) (U : Config N (nn h m k 0)) (j : ℕ) :
    Qpcomp h m k inN log U (j + 1) = QpStep h m k j (Mpow h m k inN log U j) ∘ₗ Qpcomp h m k inN log U j := rfl

variable (S : SeqDom)

/-- **The average of `0`-forms of a sequence**, `(Q'λ)(y) = (Q'_j(U)λ)(y)` for `y ∈ Γ_j`. -/
def Qpseq (inN : GLN → Prop) (log : GLN → Mat) (U : Config N (SequenceAverages.N0 S)) : Form0 N (SequenceAverages.N0 S) →ₗ[ℂ] (BPt S → Mat) :=
  LinearMap.pi fun y => (LinearMap.proj (crd S y.1.1 y.1.2)) ∘ₗ Qpcomp (hS S) S.mT S.k inN log U y.1.1

lemma Qpseq_apply (inN : GLN → Prop) (log : GLN → Mat) (U : Config N (SequenceAverages.N0 S)) (lam : Form0 N (SequenceAverages.N0 S)) (y : BPt S) :
    Qpseq S inN log U lam y = Qpcomp (hS S) S.mT S.k inN log U y.1.1 lam (crd S y.1.1 y.1.2) := rfl

/-- `Q'_0 = I`: at a point of `Γ₀`, `(Q'λ)(y) = λ(y)`. -/
theorem Qpseq_scale_zero (inN : GLN → Prop) (log : GLN → Mat) (U : Config N (SequenceAverages.N0 S)) (lam : Form0 N (SequenceAverages.N0 S))
    (y : BPt S) (hy : y.1.1 = 0) : Qpseq S inN log U lam y = lam (crd S 0 y.1.2) := by
  obtain ⟨⟨j, p⟩, hq⟩ := y
  simp only at hy
  subst hy
  rfl

/-- `⟨λ, λ'⟩ = Σ_x a⁴tr λ(x)λ'(x)` on `0`-forms. -/
abbrev pairForm0 {n : ℕ} [NeZero n] (a : ℂ) : LinearMap.BilinForm ℂ (Form0 N n) := wpair fun _ : Site n => a ^ 4

theorem pairForm0_nondegenerate {n : ℕ} [NeZero n] {r : ℝ} (hr : 0 < r) :
    (pairForm0 (N := N) (n := n) (r : ℂ)).Nondegenerate := by
  have e : (fun _ : Site n => (r : ℂ) ^ 4) = fun _ => ((r ^ 4 : ℝ) : ℂ) := by funext; push_cast; rfl
  simp only [pairForm0, e]
  exact wpair_nondegenerate _ fun _ => by positivity

/-- **`Q'^*`**, the transpose of `Q'`. -/
def QpseqStar (inN : GLN → Prop) (log : GLN → Mat) (U : Config N (SequenceAverages.N0 S)) : (BPt S → Mat) →ₗ[ℂ] Form0 N (SequenceAverages.N0 S) :=
  transpose (pairForm0 ((a0 S : ℝ) : ℂ)) (pairB S N) (pairForm0_nondegenerate (a0_pos S)) (Qpseq S inN log U)

theorem QpseqStar_spec (inN : GLN → Prop) (log : GLN → Mat) (U : Config N (SequenceAverages.N0 S)) (μ : BPt S → Mat)
    (lam : Form0 N (SequenceAverages.N0 S)) :
    pairForm0 ((a0 S : ℝ) : ℂ) (QpseqStar S inN log U μ) lam = pairB S N μ (Qpseq S inN log U lam) :=
  transpose_spec _ _ _ _ μ lam

/-- The numbers `𝖺₀ = 𝖺₁ = 𝖺`, `𝖺_{j+1} = 𝖺𝖺_j/(𝖺L^{-2} + 𝖺_j)` for `j ≥ 1`. -/
def aseq (aa : ℝ) (L : ℕ) : ℕ → ℝ
  | 0 => aa
  | 1 => aa
  | j + 2 => aa * aseq aa L (j + 1) / (aa * ((L : ℝ) ^ 2)⁻¹ + aseq aa L (j + 1))

lemma aseq_pos {aa : ℝ} (ha : 0 < aa) (L : ℕ) : ∀ j, 0 < aseq aa L j
  | 0 => ha
  | 1 => ha
  | j + 2 => by
      have := aseq_pos ha L (j + 1)
      simp only [aseq]
      positivity

/-- **The constraint operator** `Q'^*𝖺Q' = Q'^* ∘ (𝖺_{j(y)}a_y^{-2}) ∘ Q'`. -/
def constraintOp0 (inN : GLN → Prop) (log : GLN → Mat) (U : Config N (SequenceAverages.N0 S)) (aa : ℝ) :
    Form0 N (SequenceAverages.N0 S) →ₗ[ℂ] Form0 N (SequenceAverages.N0 S) :=
  QpseqStar S inN log U ∘ₗ mulW (fun y : BPt S => ((aseq aa S.L y.1.1 : ℝ) : ℂ) * (((y.ay : ℝ) : ℂ) ^ 2)⁻¹) ∘ₗ
    Qpseq S inN log U

/-- **`eq:constraint-forms`**, second line: `⟨λ, Q'^*𝖺Q'λ⟩ = Σ_j 𝖺_jΣ_{y ∈ Γ_j}a_j²tr((Q'λ)(y))²`. -/
theorem constraintOp0_form (inN : GLN → Prop) (log : GLN → Mat) (U : Config N (SequenceAverages.N0 S)) (aa : ℝ)
    (lam : Form0 N (SequenceAverages.N0 S)) :
    pairForm0 ((a0 S : ℝ) : ℂ) (constraintOp0 S inN log U aa lam) lam =
      ∑ y : BPt S, ((aseq aa S.L y.1.1 : ℝ) : ℂ) * ((y.ay : ℝ) : ℂ) ^ 2 *
        ntr (Qpseq S inN log U lam y * Qpseq S inN log U lam y) := by
  rw [constraintOp0, LinearMap.comp_apply, LinearMap.comp_apply, QpseqStar, transpose_spec]
  simp only [pairB, CriticalConcrete.pairF, wpair_apply, mulW, LinearMap.coe_mk, AddHom.coe_mk, smul_mul_assoc,
    ntr_smul]
  refine Finset.sum_congr rfl fun y _ => ?_
  have hy : ((y.ay : ℝ) : ℂ) ≠ 0 := by have := BPt.ay_pos y; exact_mod_cast this.ne'
  push_cast
  field_simp

/-! ### The differences as linear maps -/

section Differences

variable {n : ℕ} [NeZero n] (a : ℂ)

/-- `D_U` from `0`-forms to `1`-forms. -/
def D0L (U : Config N n) : Form0 N n →ₗ[ℂ] Form1 N n where
  toFun := D0 a U
  map_add' l l' := by
    funext μ x
    simp only [D0, Dfw, Pi.add_apply, Ad_add, smul_add, smul_sub]
    abel
  map_smul' c l := by
    funext μ x
    simp only [D0, Dfw, Pi.smul_apply, Ad_smul, RingHom.id_apply, ← smul_sub, smul_comm a⁻¹ c]

/-- `D^*_U` from `1`-forms to `0`-forms. -/
def Ds1L (U : Config N n) : Form1 N n →ₗ[ℂ] Form0 N n where
  toFun := Ds1 a U
  map_add' A A' := by
    funext x
    simp only [Ds1, Dbw, Pi.add_apply, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun μ _ => ?_
    simp only [Ad_add, smul_sub, smul_add]
    abel
  map_smul' c A := by
    funext x
    simp only [Ds1, Dbw, Pi.smul_apply, Ad_smul, RingHom.id_apply, ← smul_sub, smul_comm a⁻¹ c,
      Finset.smul_sum]

lemma D0L_apply (U : Config N n) (l : Form0 N n) : D0L a U l = D0 a U l := rfl

lemma Ds1L_apply (U : Config N n) (A : Form1 N n) : Ds1L a U A = Ds1 a U A := rfl

/-- The covariant Laplacian of `0`-forms is `D^*_UD_U`. -/
theorem Lap_eq (U : Config N n) (l : Form0 N n) : Lap a U l = (Ds1L a U ∘ₗ D0L a U) l := rfl

/-- `D^*_U` is the transpose of `D_U`: `⟨D_Uλ, A⟩ = ⟨λ, D^*_UA⟩`. -/
theorem D0L_transpose (U : Config N n) (l : Form0 N n) (A : Form1 N n) :
    pairForm1 a (D0L a U l) A = pairForm0 a l (Ds1L a U A) := by
  rw [pairForm1_apply, D0L_apply, Ds1L_apply, pair1_D0]
  rfl

end Differences

/-! ### The compressions -/

section Compressions

variable {G : GaugeGroup N} (hG : G.LieInput)

lemma piProj_idem (X : Mat) : piProj hG (piProj hG X) = piProj hG X := piProj_self hG (proj_mem hG X)

variable {n : ℕ} [NeZero n]

/-- The compression of `0`-forms: the indicator of `Ω_D` times `π`. -/
def piF0 (ΩD : Set (Site n)) : Module.End ℂ (Form0 N n) where
  toFun l := ΩD.indicator fun x => piProj hG (l x)
  map_add' l l' := by
    funext x
    by_cases hx : x ∈ ΩD <;> simp [Set.indicator_apply, hx, proj_add]
  map_smul' c l := by
    funext x
    by_cases hx : x ∈ ΩD <;> simp [Set.indicator_apply, hx, proj_smul]

/-- The bonds `(x, x + ae_μ)` of `Ω_D`, those with both ends in it. -/
def bondsOf (ΩD : Set (Site n)) (μ : Fin 4) : Set (Site n) := {x | x ∈ ΩD ∧ x + unit n μ ∈ ΩD}

/-- The compression of `1`-forms: the indicator of the bonds of `Ω_D` times `π`. -/
def piF1 (ΩD : Set (Site n)) : Module.End ℂ (Form1 N n) where
  toFun A μ := (bondsOf ΩD μ).indicator fun x => piProj hG (A μ x)
  map_add' A A' := by
    funext μ x
    by_cases hx : x ∈ bondsOf ΩD μ <;> simp [Set.indicator_apply, hx, proj_add]
  map_smul' c A := by
    funext μ x
    by_cases hx : x ∈ bondsOf ΩD μ <;> simp [Set.indicator_apply, hx, proj_smul]

/-- The compression of functions on a finite set: `π` pointwise. -/
def piFun (ι : Type*) : Module.End ℂ (ι → Mat) where
  toFun f i := piProj hG (f i)
  map_add' f g := by funext i; simp [proj_add]
  map_smul' c f := by funext i; simp [proj_smul]

lemma piF0_idem (ΩD : Set (Site n)) (l : Form0 N n) : piF0 hG ΩD (piF0 hG ΩD l) = piF0 hG ΩD l := by
  funext x
  by_cases hx : x ∈ ΩD <;> simp [piF0, Set.indicator_apply, hx, piProj_idem]

lemma piF1_idem (ΩD : Set (Site n)) (A : Form1 N n) : piF1 hG ΩD (piF1 hG ΩD A) = piF1 hG ΩD A := by
  funext μ x
  by_cases hx : x ∈ bondsOf ΩD μ <;> simp [piF1, Set.indicator_apply, hx, piProj_idem]

lemma piFun_idem (ι : Type*) (f : ι → Mat) : piFun hG ι (piFun hG ι f) = piFun hG ι f := by
  funext i; simp [piFun, piProj_idem]

/-- On the torus and for a group with `𝔤^c = gl(N)` the compressions are the identity. -/
lemma piF1_univ (hall : ∀ X : Mat, X ∈ G.lieC) : piF1 (n := n) hG Set.univ = 1 := by
  ext A μ x
  simp [piF1, bondsOf, piProj_self hG (hall _)]

end Compressions

/-! ### The operators of a sequence -/

section Operators

variable [NeZero N] {G : GaugeGroup N} (hG : G.LieInput)
  (U : Config N (SequenceAverages.N0 S)) (aa : ℝ) (ΩD : Set (Site (SequenceAverages.N0 S)))

/-- **`Δ'_𝖺 = Δ_U + Q'^*𝖺Q'`** on `0`-forms. -/
def DeltaP (inN : GLN → Prop) (log : GLN → Mat) (U : Config N (SequenceAverages.N0 S)) (aa : ℝ) :
    Module.End ℂ (Form0 N (SequenceAverages.N0 S)) :=
  Ds1L ((a0 S : ℝ) : ℂ) U ∘ₗ D0L ((a0 S : ℝ) : ℂ) U + constraintOp0 S inN log U aa

/-- **`G' = (Δ'_𝖺)^{-1}`** on the compressed `0`-forms. -/
def Gp {G : GaugeGroup N} (hG : G.LieInput) (inN : GLN → Prop) (log : GLN → Mat)
    (U : Config N (SequenceAverages.N0 S)) (aa : ℝ) (ΩD : Set (Site (SequenceAverages.N0 S))) :
    Module.End ℂ (Form0 N (SequenceAverages.N0 S)) :=
  cinv (piF0 hG ΩD) (DeltaP S inN log U aa)

/-- **`P = G'Q'^*(Q'G'^2Q'^*)^{-1}Q'G'`**. -/
def Ps {G : GaugeGroup N} (hG : G.LieInput) (inN : GLN → Prop) (log : GLN → Mat)
    (U : Config N (SequenceAverages.N0 S)) (aa : ℝ) (ΩD : Set (Site (SequenceAverages.N0 S))) :
    Module.End ℂ (Form0 N (SequenceAverages.N0 S)) :=
  Xop (piFun hG (BPt S)) (Gp S hG inN log U aa ΩD) (Qpseq S inN log U) (QpseqStar S inN log U)

/-- **`R = I - P`**. -/
def Rs {G : GaugeGroup N} (hG : G.LieInput) (inN : GLN → Prop) (log : GLN → Mat)
    (U : Config N (SequenceAverages.N0 S)) (aa : ℝ) (ΩD : Set (Site (SequenceAverages.N0 S))) :
    Module.End ℂ (Form0 N (SequenceAverages.N0 S)) :=
  Rop (piF0 hG ΩD) (piFun hG (BPt S)) (Gp S hG inN log U aa ΩD) (Qpseq S inN log U) (QpseqStar S inN log U)

/-- **`Δ_𝖺 = Δ(U) + DRD^* + Q^*𝖺Q`** on `1`-forms. -/
def DeltaA {G : GaugeGroup N} (hG : G.LieInput) (inN : GLN → Prop) (log : GLN → Mat)
    (U : Config N (SequenceAverages.N0 S)) (aa : ℝ) (ΩD : Set (Site (SequenceAverages.N0 S)))
    (ha : ((a0 S : ℝ) : ℂ) ≠ 0) : Module.End ℂ (Form1 N (SequenceAverages.N0 S)) :=
  hessLin ((a0 S : ℝ) : ℂ) hG ha U +
    D0L ((a0 S : ℝ) : ℂ) U ∘ₗ Rs S hG inN log U aa ΩD ∘ₗ Ds1L ((a0 S : ℝ) : ℂ) U +
    constraintOp S inN log U (aa : ℂ)

/-- **`G = (Δ_𝖺)^{-1}`** on the compressed `1`-forms. -/
def Gs {G : GaugeGroup N} (hG : G.LieInput) (inN : GLN → Prop) (log : GLN → Mat)
    (U : Config N (SequenceAverages.N0 S)) (aa : ℝ) (ΩD : Set (Site (SequenceAverages.N0 S)))
    (ha : ((a0 S : ℝ) : ℂ) ≠ 0) : Module.End ℂ (Form1 N (SequenceAverages.N0 S)) :=
  cinv (piF1 hG ΩD) (DeltaA S hG inN log U aa ΩD ha)

/-- `Δ_𝖺` is the operator `Delta_a` of `CriticalTheorem` with `Δ = Δ(U)`, `DRD = DRD^*`, `Q^* = QseqStar`, and the
weight `𝖺a_c^{-2}`. -/
theorem DeltaA_eq (inN : GLN → Prop) (log : GLN → Mat) (ha : ((a0 S : ℝ) : ℂ) ≠ 0) :
    DeltaA S hG inN log U aa ΩD ha =
      CriticalTheorem.Delta_a (Qseq S inN log U) (QseqStar S inN log U) (hessLin ((a0 S : ℝ) : ℂ) hG ha U)
        (D0L ((a0 S : ℝ) : ℂ) U ∘ₗ Rs S hG inN log U aa ΩD ∘ₗ Ds1L ((a0 S : ℝ) : ℂ) U)
        (mulW fun c : LBond S => (aa : ℂ) * (((c.ac : ℝ) : ℂ) ^ 2)⁻¹) := rfl

/-- `G'` is supported by the compression on both sides. -/
lemma Gp_supp (inN : GLN → Prop) (log : GLN → Mat) (l : Form0 N (SequenceAverages.N0 S)) :
    piF0 hG ΩD (Gp S hG inN log U aa ΩD l) = Gp S hG inN log U aa ΩD l ∧
      Gp S hG inN log U aa ΩD (piF0 hG ΩD l) = Gp S hG inN log U aa ΩD l :=
  ⟨P_cinv (piF0_idem hG ΩD) l, cinv_P (piF0_idem hG ΩD) l⟩

/-- **`P² = P`**, whenever `(Q'G'^2Q'^*)^{-1}` exists on the compressed functions on `𝐁`. -/
theorem Ps_idem (inN : GLN → Prop) (log : GLN → Mat) (hK : IsUnit (ckern (piFun hG (BPt S))
      (Mop (Gp S hG inN log U aa ΩD) (Qpseq S inN log U) (QpseqStar S inN log U)))) (l : Form0 N (SequenceAverages.N0 S)) :
    Ps S hG inN log U aa ΩD (Ps S hG inN log U aa ΩD l) = Ps S hG inN log U aa ΩD l :=
  Xop_idem (piFun_idem hG _) hK l

/-- **`R² = R`**, whenever `(Q'G'^2Q'^*)^{-1}` exists on the compressed functions on `𝐁`. -/
theorem Rs_idem (inN : GLN → Prop) (log : GLN → Mat) (hK : IsUnit (ckern (piFun hG (BPt S))
      (Mop (Gp S hG inN log U aa ΩD) (Qpseq S inN log U) (QpseqStar S inN log U)))) (l : Form0 N (SequenceAverages.N0 S)) :
    Rs S hG inN log U aa ΩD (Rs S hG inN log U aa ΩD l) = Rs S hG inN log U aa ΩD l :=
  Rop_idem (piF0_idem hG ΩD) (P_cinv (piF0_idem hG ΩD)) (cinv_P (piF0_idem hG ΩD)) (piFun_idem hG _) hK l

/-- **`Q'G'R = 0`** on the compressed functions on `𝐁`. -/
theorem Qp_Gp_Rs (inN : GLN → Prop) (log : GLN → Mat) (hK : IsUnit (ckern (piFun hG (BPt S))
      (Mop (Gp S hG inN log U aa ΩD) (Qpseq S inN log U) (QpseqStar S inN log U)))) (l : Form0 N (SequenceAverages.N0 S)) :
    piFun hG (BPt S) (Qpseq S inN log U (Gp S hG inN log U aa ΩD (Rs S hG inN log U aa ΩD l))) = 0 :=
  Q_G_Rop (cinv_P (piF0_idem hG ΩD)) (piFun_idem hG _) hK l

/-- **`G` inverts `Δ_𝖺`** on the compressed `1`-forms, whenever the inverse exists: `ΠΔ_𝖺GA = ΠA` and
`GΔ_𝖺ΠA = ΠA`. -/
theorem Gs_inverse (inN : GLN → Prop) (log : GLN → Mat) (ha : ((a0 S : ℝ) : ℂ) ≠ 0)
    (hK : IsUnit (ckern (piF1 hG ΩD) (DeltaA S hG inN log U aa ΩD ha))) (A : Form1 N (SequenceAverages.N0 S)) :
    piF1 hG ΩD (DeltaA S hG inN log U aa ΩD ha (Gs S hG inN log U aa ΩD ha A)) = piF1 hG ΩD A ∧
      Gs S hG inN log U aa ΩD ha (DeltaA S hG inN log U aa ΩD ha (piF1 hG ΩD A)) = piF1 hG ΩD A :=
  ⟨P_T_cinv (piF1_idem hG ΩD) hK A, cinv_T_P (piF1_idem hG ΩD) hK A⟩

end Operators

end SequenceOperators
end CoreLean

end
