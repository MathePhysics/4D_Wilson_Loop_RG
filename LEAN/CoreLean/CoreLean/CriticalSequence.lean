/-
The concrete layer, step C7 (`CONCRETE_LAYER.md`), first case: `thm:critical`(ii) of BALABAN_CORE.tex (`615c66b253fe`)
for the operators of a sequence of domains and of a pair (`SequenceOperators`, `PairConcrete`), on the torus
(`Ω_D = 𝕋`) and for a group with `𝔤^c = gl(N)`, where the compressions are the identity and the compressed inverses
are the inverses (`CompressedInverse.cinv_one`).

`critical_ii_sequence`: if `Δ_𝖺`, `Δ_𝖺 - Δ^{(2)}`, `QGQ^*`, and `QG_cQ^*` are invertible (the existence of the inverses
is `thm:propagators` and `prop:second-operators`, stated in the core), then the hypotheses of `critical_ii_concrete` on
the operators hold, and a critical `A` with `A = T(A')`, `DRD^*A' = 0` and `QA' = 𝖷(A)` close to `H₀𝖷(A)` is
`A = 𝓗(𝖷(A)) = T(𝒜₀(H₀𝖷(A)) + H₀𝖷(A))`. What remains as hypotheses are the statements on the nonlinear maps: the
uniqueness of the fixed point of `Φ₀` in the ball (`prop:fixed-points`), the relations `hT`, `hD`, `hX` of the
construction, the criticality `hcrit`, and the smallness `hball`.

`critical_ii_sequence_general`: the same for any Dirichlet domain and any group, through
`CriticalCompressed.critical_ii_c`. The inverses are the compressed ones of the core; the compressions are idempotent
and symmetric for the pairings (`piF1_symm`, `piFun_symm`, from `tr(πX·Y) = tr(X·πY)`, `ntr_proj_symm`), the weight
`𝖺a_c^{-2}` preserves the compressed functions (`mulW_piFun`), and the further inputs are the invertibility of the four
compressed operators, `Q` mapping compressed forms to functions with values in `𝔤^c` (`hQpres`, from
`prop:relative-average`: `(1/i)log𝓜_𝐔(A)(c) ∈ 𝔤^c`), the preimage being a compressed form (`hA'`), and the
criticality on the compressed variations.
-/
import CoreLean.PairConcrete
import CoreLean.CriticalConcrete
import CoreLean.CriticalCompressed
import CoreLean.QLieC

noncomputable section

namespace CoreLean
namespace CriticalSequence

open Lattices SequenceIndex ConcretePairing SequenceAverages SequenceOperators CompressedInverse PairConcrete
  CriticalTheorem CriticalConcrete RelativeAverage

variable {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ

/-- For `𝔤^c = gl(N)` the compression of functions is the identity. -/
lemma piFun_one {G : GaugeGroup N} (hG : G.LieInput) (hall : ∀ X : Mat, X ∈ G.lieC) (ι : Type*) :
    piFun hG ι = 1 := by
  ext f i
  simp [piFun, piProj_self hG (hall _)]

variable (S : SeqDom) [NeZero N] {G : GaugeGroup N} (hG : G.LieInput)

/-- `(QG_cQ^*)^{-1}`, compressed. -/
abbrev Minv (d : Data S N) : Module.End ℂ (LBond S → Mat) :=
  cinv (piFun hG (LBond S)) (Qseq S d.inN d.log d.U ∘ₗ Gc S hG d ∘ₗ QseqStar S d.inN d.log d.U)

/-- `(QGQ^*)^{-1}`, compressed. -/
abbrev M0inv (d : Data S N) : Module.End ℂ (LBond S → Mat) :=
  cinv (piFun hG (LBond S))
    (Qseq S d.inN d.log d.U ∘ₗ Gs S hG d.inN d.log d.U d.aa d.ΩD (aC_ne S) ∘ₗ QseqStar S d.inN d.log d.U)

/-- **`thm:critical`(ii) for a sequence of domains on the torus**, `𝔤^c = gl(N)`: `A = T(𝒜₀(H₀𝖷(A)) + H₀𝖷(A))`. -/
theorem critical_ii_sequence (hall : ∀ X : Mat, X ∈ G.lieC) (d : Data S N) (hΩ : d.ΩD = Set.univ)
    (hUG : IsUnit (DA S hG d)) (hUc : IsUnit (DA S hG d - Delta2 S hG d))
    (hUM0 : IsUnit (Qseq S d.inN d.log d.U ∘ₗ Gs S hG d.inN d.log d.U d.aa d.ΩD (aC_ne S) ∘ₗ
      QseqStar S d.inN d.log d.U))
    (hUM : IsUnit (Qseq S d.inN d.log d.U ∘ₗ Gc S hG d ∘ₗ QseqStar S d.inN d.log d.U))
    (Nf : Form1 N (SequenceAverages.N0 S) → Form1 N (SequenceAverages.N0 S))
    (T : Form1 N (SequenceAverages.N0 S) → Form1 N (SequenceAverages.N0 S))
    (X : Form1 N (SequenceAverages.N0 S) → (LBond S → Mat))
    (A0fix : Form1 N (SequenceAverages.N0 S) → Form1 N (SequenceAverages.N0 S))
    (ball : Form1 N (SequenceAverages.N0 S) → Set (Form1 N (SequenceAverages.N0 S)))
    (huniq : ∀ 𝔄, ∀ A₀ ∈ ball 𝔄, Phi0 (Qseq S d.inN d.log d.U) (QseqStar S d.inN d.log d.U) (Delta2 S hG d)
      (Gc S hG d) (Minv S hG d) Nf d.J 𝔄 A₀ = A₀ → A₀ = A0fix 𝔄)
    (A A' : Form1 N (SequenceAverages.N0 S)) (hT : T A' = A) (hD : DRD S hG d A' = 0)
    (hX : Qseq S d.inN d.log d.U A' = X A)
    (hcrit : ∀ δ, Qseq S d.inN d.log d.U δ = 0 →
      pairForm1 (aC S) (d.J + (hessLin (aC S) hG (aC_ne S) d.U - Delta2 S hG d) A' + Nf A') δ = 0)
    (hball : A' - H0 S hG d (X A) ∈ ball (H0 S hG d (X A))) :
    A = T (A0fix (H0 S hG d (X A)) + H0 S hG d (X A)) := by
  have hP1 : piF1 hG d.ΩD = 1 := by rw [hΩ]; exact piF1_univ hG hall
  have hPF : piFun hG (LBond S) = 1 := piFun_one hG hall _
  have eGc : Gc S hG d = Ring.inverse (DA S hG d - Delta2 S hG d) := by
    simp only [Gc, hP1, cinv_one]
  have eG : Gs S hG d.inN d.log d.U d.aa d.ΩD (aC_ne S) = Ring.inverse (DA S hG d) := by
    simp only [Gs, hP1, cinv_one]
  refine critical_ii_concrete (a0_pos S) (fun c : LBond S => c.ac) (fun c => LBond.ac_pos c)
    (Qseq S d.inN d.log d.U) (hessLin (aC S) hG (aC_ne S) d.U) (Delta2 S hG d) (DRD S hG d) (Gc S hG d)
    (Gs S hG d.inN d.log d.U d.aa d.ΩD (aC_ne S)) (mulW fun c : LBond S => (d.aa : ℂ) * (((c.ac : ℝ) : ℂ) ^ 2)⁻¹)
    (Minv S hG d) (M0inv S hG d) ?_ ?_ ?_ ?_ ?_ Nf d.J T X A0fix ball huniq A A' hT hD hX hcrit hball
  · intro x
    rw [eGc]
    exact LinearMap.congr_fun (Ring.inverse_mul_cancel _ hUc) x
  · intro x
    rw [eGc]
    exact LinearMap.congr_fun (Ring.mul_inverse_cancel _ hUc) x
  · intro ν
    have h := LinearMap.congr_fun (Ring.inverse_mul_cancel _ hUM) ν
    simp only [Minv, hPF, cinv_one]
    exact h
  · intro x
    rw [eG]
    exact LinearMap.congr_fun (Ring.mul_inverse_cancel _ hUG) x
  · intro y
    have h := LinearMap.congr_fun (Ring.mul_inverse_cancel _ hUM0) y
    simp only [M0inv, hPF, cinv_one]
    exact h

/-! ### The general case: any Dirichlet domain, any group -/

omit [NeZero N] in
/-- The weight `𝖺a_c^{-2}` preserves the compressed functions. -/
lemma mulW_piFun {ι : Type*} (w : ι → ℂ) (f : ι → Mat) :
    piFun hG ι (mulW w (piFun hG ι f)) = mulW w (piFun hG ι f) := by
  funext i
  simp [mulW, piFun, proj_smul, piProj_idem]

/-- `tr(πX·Y) = tr(X·πY)`: `π` is symmetric for the bilinear pairing `(X, Y) ↦ tr XY`. -/
lemma ntr_proj_symm (X Y : Mat) : ntr (piProj hG X * Y) = ntr (X * piProj hG Y) := by
  rw [← ntr_mul_proj hG (proj_mem hG X) Y, ntr_mul_comm X, ← ntr_mul_proj hG (proj_mem hG Y) X, ntr_mul_comm]

/-- The compression of `1`-forms is symmetric for `⟨·,·⟩`. -/
lemma piF1_symm {n : ℕ} [NeZero n] (ΩD : Set (Site n)) (a : ℂ) (A B : Form1 N n) :
    pairForm1 a (piF1 hG ΩD A) B = pairForm1 a A (piF1 hG ΩD B) := by
  simp only [pairForm1_apply', wpair_apply]
  refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : x ∈ bondsOf ΩD μ
  · simp [piF1, Set.indicator_apply, hx, ntr_proj_symm hG]
  · simp [piF1, Set.indicator_apply, hx, ntr]

/-- The compression of functions is symmetric for the weighted pairings. -/
lemma piFun_symm {ι : Type*} [Fintype ι] (w : ι → ℂ) (f g : ι → Mat) :
    wpair w (piFun hG ι f) g = wpair w f (piFun hG ι g) := by
  simp only [wpair_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [piFun, ntr_proj_symm hG]

/-- **`thm:critical`(ii) for a sequence of domains**, any Dirichlet domain and any group: if `Δ_𝖺`, `Δ_𝖺 - Δ^{(2)}`,
`QGQ^*`, and `QG_cQ^*` are invertible on the compressed spaces (`thm:propagators`, `prop:second-operators`) and `Q`
maps the compressed forms into the functions with values in `𝔤^c` (`prop:relative-average`), then
`A = T(𝒜₀(H₀𝖷(A)) + H₀𝖷(A))`. -/
theorem critical_ii_sequence_general (d : Data S N)
    (hKG : IsUnit (ckern (piF1 hG d.ΩD) (DA S hG d)))
    (hKc : IsUnit (ckern (piF1 hG d.ΩD) (DA S hG d - Delta2 S hG d)))
    (hKM0 : IsUnit (ckern (piFun hG (LBond S)) (Qseq S d.inN d.log d.U ∘ₗ
      Gs S hG d.inN d.log d.U d.aa d.ΩD (aC_ne S) ∘ₗ QseqStar S d.inN d.log d.U)))
    (hKM : IsUnit (ckern (piFun hG (LBond S))
      (Qseq S d.inN d.log d.U ∘ₗ Gc S hG d ∘ₗ QseqStar S d.inN d.log d.U)))
    (hQpres : ∀ x, piFun hG (LBond S) (Qseq S d.inN d.log d.U (piF1 hG d.ΩD x)) =
      Qseq S d.inN d.log d.U (piF1 hG d.ΩD x))
    (Nf : Form1 N (SequenceAverages.N0 S) → Form1 N (SequenceAverages.N0 S))
    (T : Form1 N (SequenceAverages.N0 S) → Form1 N (SequenceAverages.N0 S))
    (X : Form1 N (SequenceAverages.N0 S) → (LBond S → Mat))
    (A0fix : Form1 N (SequenceAverages.N0 S) → Form1 N (SequenceAverages.N0 S))
    (ball : Form1 N (SequenceAverages.N0 S) → Set (Form1 N (SequenceAverages.N0 S)))
    (huniq : ∀ 𝔄, ∀ A₀ ∈ ball 𝔄, Phi0 (Qseq S d.inN d.log d.U) (QseqStar S d.inN d.log d.U) (Delta2 S hG d)
      (Gc S hG d) (Minv S hG d) Nf d.J 𝔄 A₀ = A₀ → A₀ = A0fix 𝔄)
    (A A' : Form1 N (SequenceAverages.N0 S)) (hT : T A' = A) (hD : DRD S hG d A' = 0)
    (hX : Qseq S d.inN d.log d.U A' = X A) (hA' : piF1 hG d.ΩD A' = A')
    (hcrit : ∀ δ, piF1 hG d.ΩD δ = δ → Qseq S d.inN d.log d.U δ = 0 →
      pairForm1 (aC S) (d.J + (hessLin (aC S) hG (aC_ne S) d.U - Delta2 S hG d) A' + Nf A') δ = 0)
    (hball : A' - H0 S hG d (X A) ∈ ball (H0 S hG d (X A))) :
    A = T (A0fix (H0 S hG d (X A)) + H0 S hG d (X A)) :=
  CriticalCompressed.critical_ii_c (Qseq S d.inN d.log d.U) (QseqStar S d.inN d.log d.U)
    (hessLin (aC S) hG (aC_ne S) d.U) (Delta2 S hG d) (DRD S hG d) (Gc S hG d)
    (Gs S hG d.inN d.log d.U d.aa d.ΩD (aC_ne S)) (mulW fun c : LBond S => (d.aa : ℂ) * (((c.ac : ℝ) : ℂ) ^ 2)⁻¹)
    (Minv S hG d) (M0inv S hG d) (piF1 hG d.ΩD) (piFun hG (LBond S))
    (pairForm1 (aC S)) (pairLB S N) (pairForm1_nondegenerate (a0_pos S)) (pairLB_nondegenerate S N)
    (transpose_spec _ _ _ _) (piF1_idem hG d.ΩD) (piF1_symm hG d.ΩD (aC S)) (piFun_idem hG _)
    (piFun_symm hG _) (fun x => cinv_T_P (piF1_idem hG d.ΩD) hKc x) (fun x => cinv_P (piF1_idem hG d.ΩD) x)
    (fun y => cinv_T_P (piFun_idem hG _) hKM y) (fun x => P_cinv (piF1_idem hG d.ΩD) x)
    (fun x => P_T_cinv (piF1_idem hG d.ΩD) hKG x) (fun y => P_cinv (piFun_idem hG _) y)
    (fun y => P_T_cinv (piFun_idem hG _) hKM0 y) hQpres (mulW_piFun hG _) Nf d.J T X A0fix ball huniq A A' hT hD
    hX hA' hcrit hball

/-- **`thm:critical`(ii) for a sequence of domains**, any Dirichlet domain and any group, with the input `hQpres`
replaced by the conclusion of `prop:relative-average` at the averages `M^j(U)`, `j < k` (`QLieC.hQpres_of_rays`). -/
theorem critical_ii_sequence_rays (d : Data S N)
    (hKG : IsUnit (ckern (piF1 hG d.ΩD) (DA S hG d)))
    (hKc : IsUnit (ckern (piF1 hG d.ΩD) (DA S hG d - Delta2 S hG d)))
    (hKM0 : IsUnit (ckern (piFun hG (LBond S)) (Qseq S d.inN d.log d.U ∘ₗ
      Gs S hG d.inN d.log d.U d.aa d.ΩD (aC_ne S) ∘ₗ QseqStar S d.inN d.log d.U)))
    (hKM : IsUnit (ckern (piFun hG (LBond S))
      (Qseq S d.inN d.log d.U ∘ₗ Gc S hG d ∘ₗ QseqStar S d.inN d.log d.U)))
    (hlev : ∀ j < S.k, QLieC.RayLieC G (MultiscaleAverages.Mpow (hS S) S.mT S.k d.inN d.log d.U j) (hS S))
    (Nf : Form1 N (SequenceAverages.N0 S) → Form1 N (SequenceAverages.N0 S))
    (T : Form1 N (SequenceAverages.N0 S) → Form1 N (SequenceAverages.N0 S))
    (X : Form1 N (SequenceAverages.N0 S) → (LBond S → Mat))
    (A0fix : Form1 N (SequenceAverages.N0 S) → Form1 N (SequenceAverages.N0 S))
    (ball : Form1 N (SequenceAverages.N0 S) → Set (Form1 N (SequenceAverages.N0 S)))
    (huniq : ∀ 𝔄, ∀ A₀ ∈ ball 𝔄, Phi0 (Qseq S d.inN d.log d.U) (QseqStar S d.inN d.log d.U) (Delta2 S hG d)
      (Gc S hG d) (Minv S hG d) Nf d.J 𝔄 A₀ = A₀ → A₀ = A0fix 𝔄)
    (A A' : Form1 N (SequenceAverages.N0 S)) (hT : T A' = A) (hD : DRD S hG d A' = 0)
    (hX : Qseq S d.inN d.log d.U A' = X A) (hA' : piF1 hG d.ΩD A' = A')
    (hcrit : ∀ δ, piF1 hG d.ΩD δ = δ → Qseq S d.inN d.log d.U δ = 0 →
      pairForm1 (aC S) (d.J + (hessLin (aC S) hG (aC_ne S) d.U - Delta2 S hG d) A' + Nf A') δ = 0)
    (hball : A' - H0 S hG d (X A) ∈ ball (H0 S hG d (X A))) :
    A = T (A0fix (H0 S hG d (X A)) + H0 S hG d (X A)) :=
  critical_ii_sequence_general S hG d hKG hKc hKM0 hKM
    (QLieC.hQpres_of_rays S hG d.inN d.log d.U d.ΩD hlev) Nf T X A0fix ball huniq A A' hT hD hX hA' hcrit hball

end CriticalSequence
end CoreLean

end
