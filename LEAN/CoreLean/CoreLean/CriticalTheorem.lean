/-
`thm:critical`(ii) and (iii) of BALABAN_CORE.tex (`615c66b253fe`), proved completely at the level of the operators
which the proofs use. The operators are linear maps between finite-dimensional vector spaces `E` (the `1`-forms) and
`F` (the functions on the bonds of the layers) over a field `K` (in the core `ℂ`, the values in `𝔤^c`), with the
pairings `⟨·,·⟩` of `eq:pairing` on `E` and `(·,·)_w` on `F` as nondegenerate symmetric bilinear forms. The results
of the core which the proofs cite enter as named hypotheses, each with its source:

* the transposition `⟨Q^*μ, A⟩ = (μ, QA)` (`def:landau-operators`(ii));
* `Δ_𝖺 = Δ(U₀) + DRD^* + Q^*𝖺Q` (`def:hessian`), `G = Δ_𝖺⁻¹` (`thm:propagators`(i)),
  `G_c = (Δ_𝖺 - Δ^{(2)})⁻¹`, `(QG_cQ^*)⁻¹`, `(QGQ^*)⁻¹` (`def:second-operators`, `thm:landau-operators`);
* `G̃ = G_c - G_cQ^*(QG_cQ^*)⁻¹QG_c`, `H₀ = GQ^*(QGQ^*)⁻¹` (`eq:second-operators`), `Φ₀` (`eq:fixed-point-maps`),
  `𝓗(𝔟) = T(𝒜₀(H₀𝔟) + H₀𝔟)` (`eq:background-field`);
* for (ii): the preimage `A'` with `T(A') = A`, `RD^*A' = 0`, `QA' = 𝖷(A)` (`prop:linearising`(ii),
  `lem:real-preimage`); the vanishing of the derivative of `F(B) = A(e^{ia₀T(B)}U₀)` at `A'` on the kernel of `Q`,
  written through `eq:functional` (`lem:critical`(iii), `lem:landau-constraint`(i), `lem:admissible-explicit`(iii));
  the uniqueness of the fixed point of `Φ₀` on its ball (`prop:fixed-points`) and the membership of `A' - H₀𝔟` in that
  ball (the step "Uniqueness", whose arithmetic is `ball_arith`);
* for (iii): `𝔊 = G₁𝔓^T` with `Q𝔓 = 0` (`thm:fluctuation-propagator`(ii)); the symmetry of `G_c`
  (`thm:propagators`(i), `def:landau-operators`(iii)); `𝖭(0) = 0` (`prop:potential`(i)), `𝖢(0) = 0`
  (`prop:relative-average-order`(i)); the two uniqueness statements (`prop:fixed-points`, `prop:linearising`(i)).

Main results: `mem_range_transpose` (a form which annihilates `ker Q` lies in the range of `Q^*`), `second_equation`
(the identity `A₀ = Φ₀(A₀)` for `A₀ = A' - H₀𝔟`), `critical_ii` (`A = 𝓗(𝖷(A))`), `frakG_J`, `Gtilde_J` (`𝔊J = 0`,
`G̃J = 0` at a critical `U₀`), `H_zero` (`𝓗(0) = 0`), `ball_arith`.
-/
import Mathlib

open LinearMap (BilinForm)

noncomputable section

namespace CoreLean
namespace CriticalTheorem

variable {K E F : Type*} [Field K] [AddCommGroup E] [Module K E] [AddCommGroup F] [Module K F]

/-! ### The annihilator of the kernel of `Q` -/

/-- **A form which annihilates the kernel of `Q` lies in the range of `Q^*`** ("the pairing being nondegenerate, a
form which annihilates the kernel of `Q` lies in the range of `Q^*`"). -/
theorem mem_range_transpose [FiniteDimensional K E] [FiniteDimensional K F] (BE : BilinForm K E)
    (BF : BilinForm K F) (hE : BE.Nondegenerate) (hF : BF.Nondegenerate) (Q : E →ₗ[K] F) (Qs : F →ₗ[K] E)
    (hQ : ∀ μ A, BE (Qs μ) A = BF μ (Q A)) (f : E) (hf : ∀ δ, Q δ = 0 → BE f δ = 0) : ∃ μ, f = Qs μ := by
  set φ : Module.Dual K E := BE.toDual hE f
  have hφ : φ ∈ (LinearMap.ker Q).dualAnnihilator := by
    rw [Submodule.mem_dualAnnihilator]
    intro δ hδ
    exact hf δ (LinearMap.mem_ker.1 hδ)
  rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker] at hφ
  obtain ⟨ψ, hψ⟩ := hφ
  refine ⟨(BF.toDual hF).symm ψ, ?_⟩
  apply (BE.toDual hE).injective
  ext A
  rw [BilinForm.toDual_def, BilinForm.toDual_def, hQ, BilinForm.apply_toDual_symm_apply]
  have := congrArg (fun χ : Module.Dual K E => χ A) hψ
  simp only [LinearMap.dualMap_apply] at this
  rw [this]
  rfl

/-! ### The operators of the second equation -/

variable (Q : E →ₗ[K] F) (Qs : F →ₗ[K] E) (Δ Δ₂ DRD Gc G : E →ₗ[K] E) (a Minv M0inv : F →ₗ[K] F)

/-- `Δ_𝖺 = Δ(U₀) + DRD^* + Q^*𝖺Q`. -/
def Delta_a : E →ₗ[K] E := Δ + DRD + Qs ∘ₗ a ∘ₗ Q

/-- `G̃ = G_c - G_cQ^*(QG_cQ^*)⁻¹QG_c`. -/
def Gt : E →ₗ[K] E := Gc - Gc ∘ₗ Qs ∘ₗ Minv ∘ₗ Q ∘ₗ Gc

/-- `H_c = G_cQ^*(QG_cQ^*)⁻¹`. -/
def Hc : F →ₗ[K] E := Gc ∘ₗ Qs ∘ₗ Minv

/-- `H₀ = GQ^*(QGQ^*)⁻¹`. -/
def H0 : F →ₗ[K] E := G ∘ₗ Qs ∘ₗ M0inv

/-- `Φ₀(A) = -G̃J + G̃Δ^{(2)}𝔄 - G̃𝖭(A + 𝔄)` (`eq:fixed-point-maps`). -/
def Phi0 (N : E → E) (J 𝔄 A : E) : E :=
  -Gt Q Qs Gc Minv J + Gt Q Qs Gc Minv (Δ₂ 𝔄) - Gt Q Qs Gc Minv (N (A + 𝔄))

/-- `G̃Q^* = 0`, from `(QG_cQ^*)⁻¹QG_cQ^* = I`. -/
lemma Gt_Qs (hM : ∀ ν, Minv (Q (Gc (Qs ν))) = ν) (y : F) : Gt Q Qs Gc Minv (Qs y) = 0 := by
  simp [Gt, hM]

/-- `G̃(Δ_𝖺 - Δ^{(2)}) = I - H_cQ` ("which is the definition of `G̃`"). -/
lemma Gt_inv (hGc : ∀ x, Gc ((Delta_a Q Qs Δ DRD a - Δ₂) x) = x) (x : E) :
    Gt Q Qs Gc Minv ((Delta_a Q Qs Δ DRD a - Δ₂) x) = x - Hc Qs Gc Minv (Q x) := by
  have hy := hGc x
  generalize (Delta_a Q Qs Δ DRD a - Δ₂) x = y at hy ⊢
  simp only [Gt, Hc, LinearMap.sub_apply, LinearMap.comp_apply, hy]

/-- `H_c𝔟 = H₀𝔟 + G̃Δ^{(2)}H₀𝔟`, from `G̃(Δ_𝖺 - Δ^{(2)}) = I - H_cQ`, `G̃Δ_𝖺H₀ = G̃Q^*(QGQ^*)⁻¹ = 0` and `QH₀ = I`. -/
lemma Hc_eq (hGc : ∀ x, Gc ((Delta_a Q Qs Δ DRD a - Δ₂) x) = x) (hM : ∀ ν, Minv (Q (Gc (Qs ν))) = ν)
    (hG : ∀ x, Delta_a Q Qs Δ DRD a (G x) = x) (hM0 : ∀ y, Q (G (Qs (M0inv y))) = y) (b : F) :
    Hc Qs Gc Minv b = H0 Qs G M0inv b + Gt Q Qs Gc Minv (Δ₂ (H0 Qs G M0inv b)) := by
  have h1 := Gt_inv Q Qs Δ Δ₂ DRD Gc a Minv hGc (H0 Qs G M0inv b)
  have h2 : (Delta_a Q Qs Δ DRD a - Δ₂) (H0 Qs G M0inv b) = Qs (M0inv b) - Δ₂ (H0 Qs G M0inv b) := by
    simp only [LinearMap.sub_apply, H0, LinearMap.comp_apply, hG]
  have h3 : Q (H0 Qs G M0inv b) = b := by simp only [H0, LinearMap.comp_apply, hM0]
  rw [h2, map_sub, Gt_Qs Q Qs Gc Minv hM, zero_sub, h3] at h1
  calc Hc Qs Gc Minv b = H0 Qs G M0inv b - (H0 Qs G M0inv b - Hc Qs Gc Minv b) := by abel
    _ = H0 Qs G M0inv b + Gt Q Qs Gc Minv (Δ₂ (H0 Qs G M0inv b)) := by rw [← h1]; abel

/-- **The second equation** (the step "The second equation" of the proof of (ii)): if
`f = J + (Δ(U₀) - Δ^{(2)})A' + 𝖭(A') = Q^*μ`, `RD^*A' = 0` and `QA' = 𝔟`, then `A₀ = A' - H₀𝔟` is a fixed point of
`Φ₀` at `𝔄 = H₀𝔟`. -/
theorem second_equation (hGc : ∀ x, Gc ((Delta_a Q Qs Δ DRD a - Δ₂) x) = x)
    (hGc' : ∀ x, (Delta_a Q Qs Δ DRD a - Δ₂) (Gc x) = x) (hM : ∀ ν, Minv (Q (Gc (Qs ν))) = ν)
    (hG : ∀ x, Delta_a Q Qs Δ DRD a (G x) = x) (hM0 : ∀ y, Q (G (Qs (M0inv y))) = y) (N : E → E) (J A' : E)
    (b μ : F) (hf : J + (Δ - Δ₂) A' + N A' = Qs μ) (hD : DRD A' = 0) (hb : Q A' = b) :
    A' - H0 Qs G M0inv b = Phi0 Q Qs Δ₂ Gc Minv N J (H0 Qs G M0inv b) (A' - H0 Qs G M0inv b) := by
  set ν := μ + a b
  -- `(Δ_𝖺 - Δ^{(2)})A' = Q^*ν - J - 𝖭(A')`
  have h1 : (Delta_a Q Qs Δ DRD a - Δ₂) A' = Qs ν - J - N A' := by
    have : (Delta_a Q Qs Δ DRD a - Δ₂) A' = (Δ - Δ₂) A' + Qs (a b) := by
      simp only [Delta_a, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply, hD, hb]; abel
    rw [this, show (Δ - Δ₂) A' = Qs μ - J - N A' by rw [← hf]; abel]
    simp only [ν, map_add]; abel
  -- apply `G_c`
  have h2 : A' = Gc (Qs ν) - Gc (J + N A') := by
    have e := congrArg Gc h1
    rw [hGc] at e
    calc A' = Gc (Qs ν - J - N A') := e
      _ = Gc (Qs ν) - Gc (J + N A') := by rw [map_sub, map_sub, map_add Gc J (N A')]; abel
  -- apply `Q` and solve for `ν`
  have h3 : ν = Minv (b + Q (Gc (J + N A'))) := by
    have hq : Q (Gc (Qs ν)) = b + Q (Gc (J + N A')) := by
      have := congrArg Q h2
      rw [hb, map_sub] at this
      rw [this]; abel
    rw [← hq, hM]
  -- `A' = H_c𝔟 - G̃(J + 𝖭(A'))`
  have h4 : A' = Hc Qs Gc Minv b - Gt Q Qs Gc Minv (J + N A') := by
    calc A' = Gc (Qs ν) - Gc (J + N A') := h2
      _ = Gc (Qs (Minv (b + Q (Gc (J + N A'))))) - Gc (J + N A') := by rw [h3]
      _ = Hc Qs Gc Minv b - Gt Q Qs Gc Minv (J + N A') := by
        simp only [Hc, Gt, LinearMap.comp_apply, LinearMap.sub_apply, map_add]
        abel
  rw [Hc_eq Q Qs Δ Δ₂ DRD Gc G a Minv M0inv hGc hM hG hM0 b] at h4
  unfold Phi0
  rw [sub_add_cancel]
  conv_lhs => rw [h4]
  rw [map_add]; abel

/-- **`thm:critical`(ii)**: under the named inputs, `A = 𝓗(𝖷(A))` with `𝓗(𝔟) = T(𝒜₀(H₀𝔟) + H₀𝔟)`. -/
theorem critical_ii [FiniteDimensional K E] [FiniteDimensional K F] (BE : BilinForm K E) (BF : BilinForm K F)
    (hE : BE.Nondegenerate) (hF : BF.Nondegenerate) (hQ : ∀ μ A, BE (Qs μ) A = BF μ (Q A))
    (hGc : ∀ x, Gc ((Delta_a Q Qs Δ DRD a - Δ₂) x) = x) (hGc' : ∀ x, (Delta_a Q Qs Δ DRD a - Δ₂) (Gc x) = x)
    (hM : ∀ ν, Minv (Q (Gc (Qs ν))) = ν) (hG : ∀ x, Delta_a Q Qs Δ DRD a (G x) = x)
    (hM0 : ∀ y, Q (G (Qs (M0inv y))) = y) (N : E → E) (J : E)
    (T : E → E) (X : E → F) (A0fix : E → E) (ball : E → Set E)
    -- `prop:fixed-points`: uniqueness of the fixed point of `Φ₀` on its ball
    (huniq : ∀ 𝔄, ∀ A₀ ∈ ball 𝔄, Phi0 Q Qs Δ₂ Gc Minv N J 𝔄 A₀ = A₀ → A₀ = A0fix 𝔄)
    (A A' : E)
    -- `prop:linearising`(ii), `lem:real-preimage`
    (hT : T A' = A) (hD : DRD A' = 0) (hX : Q A' = X A)
    -- criticality through `lem:critical`(iii) and `eq:functional`
    (hcrit : ∀ δ, Q δ = 0 → BE (J + (Δ - Δ₂) A' + N A') δ = 0)
    -- the step "Uniqueness": `A' - H₀𝔟` lies in the ball
    (hball : A' - H0 Qs G M0inv (X A) ∈ ball (H0 Qs G M0inv (X A))) :
    A = T (A0fix (H0 Qs G M0inv (X A)) + H0 Qs G M0inv (X A)) := by
  obtain ⟨μ, hμ⟩ := mem_range_transpose BE BF hE hF Q Qs hQ _ hcrit
  have hfix := second_equation Q Qs Δ Δ₂ DRD Gc G a Minv M0inv hGc hGc' hM hG hM0 N J A' (X A) μ hμ hD hX
  have h := huniq _ _ hball hfix.symm
  rw [← h, sub_add_cancel, hT]

/-! ### Part (iii) -/

/-- **`𝔊J = 0`** at a critical `U₀`: `𝔊 = G₁𝔓^T`, `Q𝔓 = 0`, and `J` annihilates `ker Q`. -/
theorem frakG_J [FiniteDimensional K E] (BE : BilinForm K E) (hE : BE.Nondegenerate) (P Pt G₁ : E →ₗ[K] E)
    (hPt : ∀ x y, BE (Pt x) y = BE x (P y)) (hQP : ∀ g, Q (P g) = 0) (J : E)
    (hJ : ∀ δ, Q δ = 0 → BE J δ = 0) : (G₁ ∘ₗ Pt) J = 0 := by
  have h : Pt J = 0 := by
    apply hE.1
    intro g; rw [hPt]; exact hJ _ (hQP g)
  simp [h]

/-- **`G̃J = 0`** at a critical `U₀`: with `Π = I - G_cQ^*(QG_cQ^*)⁻¹Q`, `QΠ = 0`, `Π^T = I - Q^*(QG_cQ^*)⁻¹QG_c`
by the symmetries of `G_c` and of `QG_cQ^*`, and `G̃ = G_cΠ^T`. -/
theorem Gtilde_J [FiniteDimensional K E] (BE : BilinForm K E) (BF : BilinForm K F) (hE : BE.Nondegenerate)
    (hEs : ∀ x y, BE x y = BE y x) (hFs : ∀ u v, BF u v = BF v u) (hQ : ∀ μ A, BE (Qs μ) A = BF μ (Q A))
    (hGcs : ∀ x y, BE (Gc x) y = BE x (Gc y)) (hM : ∀ ν, Minv (Q (Gc (Qs ν))) = ν)
    (hM' : ∀ y, Q (Gc (Qs (Minv y))) = y) (J : E) (hJ : ∀ δ, Q δ = 0 → BE J δ = 0) :
    Gt Q Qs Gc Minv J = 0 := by
  -- the symmetry of `M = QG_cQ^*` and of its inverse
  have hMs : ∀ u v, BF u (Q (Gc (Qs v))) = BF (Q (Gc (Qs u))) v := fun u v => by
    rw [← hQ, ← hGcs, hEs, hQ, hFs]
  have hMinvs : ∀ u v, BF (Minv u) v = BF u (Minv v) := fun u v => by
    calc BF (Minv u) v = BF (Minv u) (Q (Gc (Qs (Minv v)))) := by rw [hM']
      _ = BF (Q (Gc (Qs (Minv u)))) (Minv v) := hMs _ _
      _ = BF u (Minv v) := by rw [hM']
  set Pi : E →ₗ[K] E := LinearMap.id - Gc ∘ₗ Qs ∘ₗ Minv ∘ₗ Q
  set PiT : E →ₗ[K] E := LinearMap.id - Qs ∘ₗ Minv ∘ₗ Q ∘ₗ Gc
  have hQPi : ∀ g, Q (Pi g) = 0 := fun g => by simp [Pi, hM']
  have hPiT : ∀ x y, BE (PiT x) y = BE x (Pi y) := fun x y => by
    have key : BE (Qs (Minv (Q (Gc x)))) y = BE x (Gc (Qs (Minv (Q y)))) := by
      rw [hQ, hMinvs, hFs, ← hQ, hEs, ← hGcs]
    have e1 : PiT x = x - Qs (Minv (Q (Gc x))) := rfl
    have e2 : Pi y = y - Gc (Qs (Minv (Q y))) := rfl
    rw [e1, e2, map_sub, LinearMap.sub_apply, map_sub, key]
  have hGt : Gt Q Qs Gc Minv = Gc ∘ₗ PiT := by
    ext x
    simp only [Gt, PiT, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.id_apply, map_sub]
  rw [hGt]
  exact frakG_J Q BE hE Pi PiT Gc hPiT hQPi J hJ

/-- **`𝓗(0) = 0`** at a critical `U₀`: `Φ₀` at `𝔄 = 0` is `A ↦ -G̃𝖭(A)` since `G̃J = 0`, and `𝖭(0) = 0`, so `0` is the
fixed point, `𝒜₀(0) = 0`; `𝖣 = 0` solves the linearising equation at `A' = 0` since `𝖢(0) = 0`, so `𝖣(0) = 0` and
`T(0) = 0`. -/
theorem H_zero (N : E → E) (J : E) (A0fix : E → E) (ball : E → Set E)
    (huniq : ∀ 𝔄, ∀ A₀ ∈ ball 𝔄, Phi0 Q Qs Δ₂ Gc Minv N J 𝔄 A₀ = A₀ → A₀ = A0fix 𝔄) (h0ball : (0 : E) ∈ ball 0)
    (hGtJ : Gt Q Qs Gc Minv J = 0) (hN0 : N 0 = 0)
    (Hl : F →ₗ[K] E) (Cfun : E → F) (Dl : E → F) (dball : Set F) (hC0 : Cfun 0 = 0) (hd0 : (0 : F) ∈ dball)
    (hDuniq : ∀ d ∈ dball, d = Cfun (0 - Hl d) → d = Dl 0) :
    (fun A' => A' - Hl (Dl A')) (A0fix (H0 Qs G M0inv 0) + H0 Qs G M0inv 0) = 0 := by
  have hfix : Phi0 Q Qs Δ₂ Gc Minv N J 0 0 = 0 := by simp [Phi0, hGtJ, hN0]
  have hA : A0fix 0 = 0 := (huniq 0 0 h0ball hfix).symm
  have hD : Dl 0 = 0 := (hDuniq 0 hd0 (by simp [hC0])).symm
  simp [hA, hD]

/-- **The arithmetic of the step "Uniqueness"**: from `‖A'‖ ≤ 2a`, `‖𝔟‖ ≤ 2L‖A'‖`, `‖H₀𝔟‖ ≤ B_H‖𝔟‖`,
`(2 + 4LB_H)a ≤ a₄` and the triangle inequality, `‖A' - H₀𝔟‖ ≤ a₄` and `B_H‖𝔟‖ ≤ a₄`. -/
theorem ball_arith {nA nb nH nA0 a L BH a₄ : ℝ} (hL : 0 ≤ L) (hBH : 0 ≤ BH) (hnA : nA ≤ 2 * a) (hnA0' : 0 ≤ nA)
    (hb : nb ≤ 2 * L * nA) (hH : nH ≤ BH * nb) (htri : nA0 ≤ nA + nH) (ha : (2 + 4 * L * BH) * a ≤ a₄) :
    nA0 ≤ a₄ ∧ BH * nb ≤ a₄ := by
  have h1 : BH * nb ≤ BH * (2 * L * (2 * a)) := by
    apply mul_le_mul_of_nonneg_left (hb.trans _) hBH
    exact mul_le_mul_of_nonneg_left hnA (by positivity)
  have ha0 : 0 ≤ a := by linarith
  refine ⟨by nlinarith, by nlinarith⟩

/-! ### The uniqueness from the contraction of `prop:fixed-points` -/

/-- A map with the Lipschitz constant `½` on a set has at most one fixed point there. -/
theorem fixed_unique {X : Type*} [NormedAddCommGroup X] (Φ : X → X) (S : Set X)
    (hlip : ∀ A ∈ S, ∀ B ∈ S, ‖Φ A - Φ B‖ ≤ 1 / 2 * ‖A - B‖) {A B : X} (hA : A ∈ S) (hB : B ∈ S)
    (hfA : Φ A = A) (hfB : Φ B = B) : A = B := by
  have h := hlip A hA B hB
  rw [hfA, hfB] at h
  have : ‖A - B‖ = 0 := le_antisymm (by linarith [norm_nonneg (A - B)]) (norm_nonneg _)
  exact sub_eq_zero.1 (norm_eq_zero.1 this)

/-- **`thm:critical`(ii) with `prop:fixed-points` as stated**: the uniqueness hypothesis of `critical_ii` replaced by
the contraction of `Φ₀` on the closed ball of the radius `a₄` and the membership of `𝒜₀(𝔄)` in it and its fixed-point
property. -/
theorem critical_ii_contraction {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [AddCommGroup F]
    [Module ℂ F] [FiniteDimensional ℂ E] [FiniteDimensional ℂ F] (Q : E →ₗ[ℂ] F) (Qs : F →ₗ[ℂ] E)
    (Δ Δ₂ DRD Gc G : E →ₗ[ℂ] E) (a Minv M0inv : F →ₗ[ℂ] F) (BE : BilinForm ℂ E) (BF : BilinForm ℂ F)
    (hE : BE.Nondegenerate) (hF : BF.Nondegenerate) (hQ : ∀ μ A, BE (Qs μ) A = BF μ (Q A))
    (hGc : ∀ x, Gc ((Delta_a Q Qs Δ DRD a - Δ₂) x) = x) (hGc' : ∀ x, (Delta_a Q Qs Δ DRD a - Δ₂) (Gc x) = x)
    (hM : ∀ ν, Minv (Q (Gc (Qs ν))) = ν) (hG : ∀ x, Delta_a Q Qs Δ DRD a (G x) = x)
    (hM0 : ∀ y, Q (G (Qs (M0inv y))) = y) (N : E → E) (J : E) (T : E → E) (X : E → F) (A0fix : E → E)
    {a₄ : ℝ}
    -- `prop:fixed-points`: `Φ₀` is `½`-Lipschitz on the ball, `𝒜₀(𝔄)` is its fixed point in the ball
    (hlip : ∀ 𝔄, ∀ A ∈ Metric.closedBall (0 : E) a₄, ∀ B ∈ Metric.closedBall (0 : E) a₄,
      ‖Phi0 Q Qs Δ₂ Gc Minv N J 𝔄 A - Phi0 Q Qs Δ₂ Gc Minv N J 𝔄 B‖ ≤ 1 / 2 * ‖A - B‖)
    (hfix : ∀ 𝔄, A0fix 𝔄 ∈ Metric.closedBall (0 : E) a₄ ∧ Phi0 Q Qs Δ₂ Gc Minv N J 𝔄 (A0fix 𝔄) = A0fix 𝔄)
    (A A' : E) (hT : T A' = A) (hD : DRD A' = 0) (hX : Q A' = X A)
    (hcrit : ∀ δ, Q δ = 0 → BE (J + (Δ - Δ₂) A' + N A') δ = 0)
    (hball : ‖A' - H0 Qs G M0inv (X A)‖ ≤ a₄) :
    A = T (A0fix (H0 Qs G M0inv (X A)) + H0 Qs G M0inv (X A)) := by
  refine critical_ii Q Qs Δ Δ₂ DRD Gc G a Minv M0inv BE BF hE hF hQ hGc hGc' hM hG hM0 N J T X A0fix
    (fun _ => Metric.closedBall (0 : E) a₄) ?_ A A' hT hD hX hcrit ?_
  · intro 𝔄 A₀ hA₀ hfA₀
    exact fixed_unique _ _ (hlip 𝔄) hA₀ (hfix 𝔄).1 hfA₀ (hfix 𝔄).2
  · rw [Metric.mem_closedBall, dist_zero_right]; exact hball

end CriticalTheorem
end CoreLean

end
