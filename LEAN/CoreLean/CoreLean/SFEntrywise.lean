/-
The operators of a sequence of domains at the trivial configuration act on the entries of the values: they commute with
every complex-linear map `φ` of `M_N(ℂ)` applied pointwise (fine lattice, `a₀ = 1`). For `lem:sf-one-layer` and
`lem:sf-two-layers`, whose proofs are scalar.

* `pw`, `pwL`: `φ` applied at every site and at every point of `𝐁_D`.
* `D0L_pw`, `Ds1L_pw`, `avgW_pw`, `Ncon_pw`, `DeltaS_pw`, `Gp_pw`, `QpL_pw`, `blk_pw`, `unblk_pw`, `That_pw`, `Tinv_pw`,
  `Pop_pw`: the commutations.
-/
import CoreLean.SFTwoLayers

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

/-- `φ` at every site. -/
def pw (φ : Mat →ₗ[ℂ] Mat) (f : Site NF → Mat) : Site NF → Mat := fun x => φ (f x)

/-- `φ` at every point of `𝐁_D`. -/
def pwL (φ : Mat →ₗ[ℂ] Mat) {ΩD : Set (Site NF)} (u : L2 (BD S ΩD) (VS N 1)) : L2 (BD S ΩD) (VS N 1) :=
  WithLp.toLp 2 fun c => emb (φ (proj (u.ofLp c)))

lemma cfgX_X0 (μ : Fin 4) (x : Site NF) : cfgX (N := N) (X0 S) μ x = 1 := by
  ext1; simp [cfgX, X0]

lemma val_X0 (b : CoreLean.Bond NF) : (cfgX (N := N) (X0 S)).val b = 1 := by
  unfold Config.val; split_ifs <;> simp [cfgX_X0]

lemma Ad_one' (X : Mat) : Ad (1 : GLN) X = X := by simp [Ad]

lemma D0L_pw (φ : Mat →ₗ[ℂ] Mat) (f : Site NF → Mat) (μ : Fin 4) :
    D0L a1 (cfgX (X0 S)) (pw S φ f) μ = pw S φ (D0L a1 (cfgX (X0 S)) f μ) := by
  funext x
  simp only [D0L_apply, D0, Dfw, pw, cfgX_X0, Ad_one', map_smul, map_sub]

lemma Ds1L_pw (φ : Mat →ₗ[ℂ] Mat) (A : Fin 4 → Site NF → Mat) :
    Ds1L a1 (cfgX (X0 S)) (fun μ => pw S φ (A μ)) = pw S φ (Ds1L a1 (cfgX (X0 S)) A) := by
  funext x
  simp only [Ds1L_apply, Ds1, Dbw, pw, val_X0, Ad_one', map_sum, map_smul, map_sub]

lemma avgW_pw (φ : Mat →ₗ[ℂ] Mat) (y : Site NF) (f : Site NF → Mat) :
    avgW S.toDomSeq (W1 S) y (pw S φ f) = φ (avgW S.toDomSeq (W1 S) y f) := by
  simp only [avgW, pw, W1, Ad_one', map_smul, map_sum]

lemma Ncon_pw (φ : Mat →ₗ[ℂ] Mat) (f : Site NF → Mat) :
    Ncon S.toDomSeq (W1 S) (pw S φ f) = pw S φ (Ncon S.toDomSeq (W1 S) f) := by
  funext x
  unfold Ncon
  simp only [pw, avgW_pw, W1, inv_one, Ad_one', map_smul]

lemma DeltaS_pw (φ : Mat →ₗ[ℂ] Mat) (f : Site NF → Mat) :
    DeltaS S.toDomSeq (cfgX (X0 S)) (W1 S) (pw S φ f) = pw S φ (DeltaS S.toDomSeq (cfgX (X0 S)) (W1 S) f) := by
  rw [DeltaS_eq, DeltaS_eq, Ncon_pw]
  have : D0L a1 (cfgX (X0 S)) (pw S φ f) = fun μ => pw S φ (D0L a1 (cfgX (X0 S)) f μ) := funext (D0L_pw S φ f)
  rw [this, Ds1L_pw]
  funext x; simp [pw]

lemma piD_pw (φ : Mat →ₗ[ℂ] Mat) (ΩD : Set (Site NF)) (f : Site NF → Mat) :
    piD ΩD (pw S φ f) = pw S φ (piD ΩD f) := by
  funext x; simp only [piD_apply, pw]; split_ifs <;> simp

/-- An inverse commutes with what its operator commutes with. -/
lemma inverse_comm {V : Type*} [AddCommGroup V] [Module ℂ V] {K : Module.End ℂ V} (hK : IsUnit K) (F : V → V)
    (hF : ∀ v, K (F v) = F (K v)) (v : V) : Ring.inverse K (F v) = F (Ring.inverse K v) := by
  have h1 : ∀ y, K (Ring.inverse K y) = y := fun y => LinearMap.congr_fun (Ring.mul_inverse_cancel _ hK) y
  have h2 : ∀ y, Ring.inverse K (K y) = y := fun y => LinearMap.congr_fun (Ring.inverse_mul_cancel _ hK) y
  conv_lhs => rw [← h1 v, ← hF, h2]

lemma Gp_pw [NeZero N] (φ : Mat →ₗ[ℂ] Mat) (ΩD : Set (Site NF)) (f : Site NF → Mat) :
    Gp' S.toDomSeq (cfgX (X0 S)) (W1 S) ΩD (pw S φ f) = pw S φ (Gp' S.toDomSeq (cfgX (X0 S)) (W1 S) ΩD f) := by
  have hK := hK_triv (N := N) S ΩD
  have hc : ∀ g, ckern (piD ΩD) (DeltaS S.toDomSeq (cfgX (X0 S)) (W1 S)) (pw S φ g) =
      pw S φ (ckern (piD ΩD) (DeltaS S.toDomSeq (cfgX (X0 S)) (W1 S)) g) := fun g => by
    rw [ckern_apply, ckern_apply, piD_pw, DeltaS_pw, piD_pw]
    funext x; simp [pw]
  show cinv (piD ΩD) _ (pw S φ f) = pw S φ (cinv (piD ΩD) _ f)
  rw [cinv_apply, cinv_apply, inverse_comm hK (pw S φ) hc, piD_pw]

lemma QpL_pw (φ : Mat →ₗ[ℂ] Mat) (μ : Site NF → Mat) : QpL S (W1 S) (pw S φ μ) = pw S φ (QpL S (W1 S) μ) := by
  funext x; show QpStar S (W1 S) (pw S φ μ) x = φ (QpStar S (W1 S) μ x)
  simp only [QpStar_triv, pw]

lemma avgL_pw (φ : Mat →ₗ[ℂ] Mat) (f : Site NF → Mat) : avgL S (W1 S) (pw S φ f) = pw S φ (avgL S (W1 S) f) := by
  funext y; exact avgW_pw S φ y f

lemma blk_pw (φ : Mat →ₗ[ℂ] Mat) {ΩD : Set (Site NF)} (g : Site NF → Mat) :
    blkL S ΩD (pw S φ g) = pwL S φ (blkL S ΩD g) := by
  ext1 c
  simp only [blkL, LinearMap.coe_mk, AddHom.coe_mk, pwL, WithLp.ofLp_toLp, proj_emb, pw]

lemma unblk_pw (φ : Mat →ₗ[ℂ] Mat) {ΩD : Set (Site NF)} (u : L2 (BD S ΩD) (VS N 1)) :
    unblkL S ΩD (pwL S φ u) = pw S φ (unblkL S ΩD u) := by
  funext x
  simp only [unblkL, LinearMap.coe_mk, AddHom.coe_mk, extBD, pw, pwL]
  split_ifs with h
  · simp only [WithLp.ofLp_toLp, proj_emb, map_smul]
  · simp

lemma That_pw [NeZero N] (φ : Mat →ₗ[ℂ] Mat) (ΩD : Set (Site NF)) (u : L2 (BD S ΩD) (VS N 1)) :
    kerApply (kerT S (Subtype.val : BD S ΩD → Site NF) (X0 S) (W1 S) ΩD) (pwL S φ u) =
      pwL S φ (kerApply (kerT S (Subtype.val : BD S ΩD → Site NF) (X0 S) (W1 S) ΩD) u) := by
  rw [← That_kernel, ← That_kernel, unblk_pw, QpL_pw, Gp_pw, Gp_pw, avgL_pw, blk_pw]

lemma Tinv_pw [NeZero N] (φ : Mat →ₗ[ℂ] Mat) (ΩD : Set (Site NF))
    (hb : Function.Bijective (kerLin (kerT (N := N) S (Subtype.val : BD S ΩD → Site NF) (X0 S) (W1 S) ΩD)))
    (u : L2 (BD S ΩD) (VS N 1)) :
    Tinv S (X0 S) (W1 S) ΩD (pwL S φ u) = pwL S φ (Tinv S (X0 S) (W1 S) ΩD u) := by
  apply hb.1
  show kerApply _ _ = kerApply _ _
  rw [kerApply_Tinv S _ _ ΩD hb, That_pw, kerApply_Tinv S _ _ ΩD hb]

/-- **`P` commutes with `φ`** at the trivial configuration. -/
theorem Pop_pw [NeZero N] (φ : Mat →ₗ[ℂ] Mat) (ΩD : Set (Site NF))
    (hb : Function.Bijective (kerLin (kerT (N := N) S (Subtype.val : BD S ΩD → Site NF) (X0 S) (W1 S) ΩD)))
    (f : Site NF → Mat) : Pop S (X0 S) (W1 S) ΩD (pw S φ f) = pw S φ (Pop S (X0 S) (W1 S) ΩD f) := by
  show Gp' S.toDomSeq (cfgX (X0 S)) (W1 S) ΩD (QpL S (W1 S) (unblkL S ΩD (Tinv S (X0 S) (W1 S) ΩD
    (blkL S ΩD (avgL S (W1 S) (Gp' S.toDomSeq (cfgX (X0 S)) (W1 S) ΩD (pw S φ f))))))) = _
  rw [Gp_pw, avgL_pw, blk_pw, Tinv_pw S φ ΩD hb, unblk_pw, QpL_pw, Gp_pw]
  rfl

/-! ### The scalar operator -/

/-- The matrix unit `E₀₀`. -/
def E00 [NeZero N] : Mat := Matrix.single 0 0 1

/-- The entry `(a, b)` moved to `(0, 0)`: `X ↦ E₀ₐXE_{b0} = X_{ab}E₀₀`. -/
def phiAB [NeZero N] (a b : Fin N) : Mat →ₗ[ℂ] Mat :=
  (LinearMap.mulLeft ℂ (Matrix.single 0 a (1 : ℂ))).comp (LinearMap.mulRight ℂ (Matrix.single b 0 (1 : ℂ)))

lemma phiAB_apply [NeZero N] (a b : Fin N) (X : Mat) : phiAB a b X = X a b • E00 := by
  simp only [phiAB, LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply, ← Matrix.mul_assoc,
    single_mul_mul_single, one_mul, mul_one, E00]
  ext i j; simp [Matrix.single, smul_eq_mul]

/-- **The scalar operator** `p(φ) = (P(φE₀₀))₀₀`. -/
def ps [NeZero N] (ΩD : Set (Site NF)) (φ : Site NF → ℂ) : Site NF → ℂ :=
  fun x => Pop S (X0 S) (W1 S) ΩD (fun y => φ y • (E00 : Mat)) x 0 0

/-- `P(φE₀₀) = p(φ)E₀₀`. -/
theorem Pop_E00 [NeZero N] (ΩD : Set (Site NF))
    (hb : Function.Bijective (kerLin (kerT (N := N) S (Subtype.val : BD S ΩD → Site NF) (X0 S) (W1 S) ΩD)))
    (φ : Site NF → ℂ) :
    Pop S (X0 S) (W1 S) ΩD (fun y => φ y • (E00 : Mat)) = fun x => ps (N := N) S ΩD φ x • (E00 : Mat) := by
  have e : (fun y => φ y • (E00 : Mat)) = pw S (phiAB 0 0) (fun y => φ y • (E00 : Mat)) := by
    funext y; rw [pw, phiAB_apply, Matrix.smul_apply, E00, Matrix.single_apply_same, smul_eq_mul, mul_one]
  conv_lhs => rw [e, Pop_pw S _ ΩD hb]
  funext x
  simp only [pw, phiAB_apply]
  rfl

/-- **`P` acts on the entries**: `(Pf)_{ab} = p(f_{ab})`. -/
theorem Pop_entry [NeZero N] (ΩD : Set (Site NF))
    (hb : Function.Bijective (kerLin (kerT (N := N) S (Subtype.val : BD S ΩD → Site NF) (X0 S) (W1 S) ΩD)))
    (f : Site NF → Mat) (x : Site NF) (a b : Fin N) :
    Pop S (X0 S) (W1 S) ΩD f x a b = ps (N := N) S ΩD (fun y => f y a b) x := by
  have h := congrFun (Pop_pw (N := N) S (phiAB (N := N) a b : Mat →ₗ[ℂ] Mat) ΩD hb f) x
  have e : pw S (phiAB (N := N) a b) f = fun y => f y a b • (E00 : Mat) := by funext y; exact phiAB_apply a b _
  rw [e, Pop_E00 S ΩD hb] at h
  simp only [pw, phiAB_apply] at h
  have := congrArg (fun M : Mat => M 0 0) h
  simpa [E00, Matrix.single_apply_same] using this.symm

/-! ### The scalar operator: the projection identity and the weak equation -/

lemma E00_mul_E00 [NeZero N] (c d : ℂ) : (c • (E00 : Mat)) * (d • E00) = (c * d) • E00 := by
  simp [E00, smul_smul]

lemma ntr_E00 [NeZero N] : ntr (E00 : Mat) = (N : ℂ)⁻¹ := by
  simp [E00, ntr, Matrix.trace_single_eq_same]

lemma E00_conj [NeZero N] : (E00 : Mat)ᴴ = E00 := by simp [E00]

lemma trace_E00_mul [NeZero N] (M : Mat) : (E00 * M).trace = M 0 0 := by
  simp [E00, Matrix.trace, Matrix.mul_apply, Matrix.single_apply, ite_and]

lemma ntr_mul_E00 [NeZero N] (M : Mat) (c : ℂ) : ntr (M * (c • (E00 : Mat))) = c * M 0 0 * (N : ℂ)⁻¹ := by
  simp only [ntr, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
  rw [Matrix.trace_mul_comm, trace_E00_mul]; ring

lemma hs2_E00 [NeZero N] (c : ℂ) : hs2 (c • (E00 : Mat)) = ‖c‖ ^ 2 * (N : ℝ)⁻¹ := by
  unfold hs2
  rw [conjTranspose_smul, E00_conj, E00_mul_E00, ntr_smul, ntr_E00, Complex.star_def, Complex.conj_mul']
  rw [show ((‖c‖ : ℂ) ^ 2 * (N : ℂ)⁻¹) = (((‖c‖ ^ 2 * (N : ℝ)⁻¹ : ℝ)) : ℂ) by push_cast; ring, Complex.ofReal_re]

lemma herm_E00 [NeZero N] (u w : Site NF → ℂ) :
    herm S (fun x => u x • (E00 : Mat)) (fun x => w x • (E00 : Mat)) =
      (∑ x, starRingEnd ℂ (u x) * w x) * (N : ℂ)⁻¹ := by
  simp only [herm, P0, pairForm0, ConcretePairing.wpair_apply, a1, Complex.ofReal_one, one_pow, one_mul, cstar,
    conjTranspose_smul, E00_conj, E00_mul_E00, ntr_smul, ntr_E00, Complex.star_def, Finset.sum_mul]

/-- **The projection identity for `p`**: `Σ_x|p(φ)(x)|² = Re Σ_x\overline{p(φ)(x)}φ(x)`. -/
theorem ps_norm [NeZero N] (ΩD : Set (Site NF))
    (hb : Function.Bijective (kerLin (kerT (N := N) S (Subtype.val : BD S ΩD → Site NF) (X0 S) (W1 S) ΩD)))
    (φ : Site NF → ℂ) :
    ∑ x, ‖ps (N := N) S ΩD φ x‖ ^ 2 = (∑ x, starRingEnd ℂ (ps (N := N) S ΩD φ x) * φ x).re := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have h := Pop_norm_triv S ΩD hb (fun y => φ y • (E00 : Mat))
  rw [Pop_E00 S ΩD hb, herm_E00] at h
  simp only [hs2_E00, ← Finset.sum_mul] at h
  rw [show ((N : ℂ)⁻¹) = (((N : ℝ)⁻¹ : ℝ) : ℂ) by push_cast; ring, Complex.re_mul_ofReal] at h
  exact mul_right_cancel₀ (inv_ne_zero hN.ne') h

/-- The scalar average `Q'c(y)` of the trivial configuration (the mean over the block). -/
def Qs (D : DomSeq NF) (c : Site NF → ℂ) (y : Site NF) : ℂ :=
  (((DiscretePoincare.box 4 (D.L ^ D.sc y)).card : ℝ) : ℂ)⁻¹ *
    ∑ o ∈ DiscretePoincare.box 4 (D.L ^ D.sc y), c (phi D (D.sc y) y o)

lemma avgW_E00 [NeZero N] (D : DomSeq NF) (c : Site NF → ℂ) (y : Site NF) :
    avgW D (W1 S) y (fun x => c x • (E00 : Mat)) = Qs S D c y • (E00 : Mat) := by
  simp only [avgW, W1, Ad_one', Qs, ← Finset.sum_smul, smul_smul]

lemma Qs_conj (D : DomSeq NF) (c : Site NF → ℂ) (y : Site NF) :
    Qs S D (fun x => starRingEnd ℂ (c x)) y = starRingEnd ℂ (Qs S D c y) := by
  simp only [Qs, map_mul, map_inv₀, Complex.conj_ofReal, map_sum]

lemma DU_E00 [NeZero N] (c : Site NF → ℂ) (μ : Fin 4) (x : Site NF) :
    DU (cfgX (X0 S)) (fun y => c y • (E00 : Mat)) μ x = (c (x + unit NF μ) - c x) • (E00 : Mat) := by
  simp only [DU, cfgX_X0, Ad_one', sub_smul]

/-- **The weak equation of `p`** (torus as the Dirichlet domain): with `v = p(φ)` there is `m` on `𝐁` with
`Σ_{x,μ}\overline{∂_μλ}∂_μv + Σ_y𝖺_{j(y)}a_y²\overline{Q'λ(y)}Q'v(y) = Σ_ya_y⁴\overline{Q'λ(y)}m(y)` for every `λ`. -/
theorem ps_weak [NeZero N]
    (hb : Function.Bijective (kerLin (kerT (N := N) S (Subtype.val : BD S Set.univ → Site NF) (X0 S) (W1 S) Set.univ)))
    (φ : Site NF → ℂ) : ∃ m : Site NF → ℂ, ∀ lam : Site NF → ℂ,
      ∑ x, ∑ μ : Fin 4, starRingEnd ℂ (lam (x + unit NF μ) - lam x) *
          (ps (N := N) S Set.univ φ (x + unit NF μ) - ps (N := N) S Set.univ φ x) +
        ∑ y ∈ detB S.toDomSeq, ((aseq 1 S.L (jj y) * (S.L : ℝ) ^ (2 * jj y) : ℝ) : ℂ) *
          (starRingEnd ℂ (Qs S S.toDomSeq lam y) * Qs S S.toDomSeq (ps (N := N) S Set.univ φ) y) =
      ∑ y ∈ detB S.toDomSeq, (((S.L : ℝ) ^ (4 * jj y) : ℝ) : ℂ) * (starRingEnd ℂ (Qs S S.toDomSeq lam y) * m y) := by
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  set v := ps (N := N) S Set.univ φ
  set G := Gp' S.toDomSeq (cfgX (X0 S)) (W1 S) Set.univ
  set f : Site NF → Mat := fun y => φ y • (E00 : Mat)
  set μM := unblkL S Set.univ (Tinv S (X0 S) (W1 S) Set.univ (blkL S Set.univ (avgL S (W1 S) (G f))))
  refine ⟨fun y => μM y 0 0, fun lam => ?_⟩
  set g : Site NF → Mat := fun x => starRingEnd ℂ (lam x) • (E00 : Mat)
  -- `Δ'(vE₀₀) = Q'^*μ`
  have hP : Pop S (X0 S) (W1 S) Set.univ f = G (QpL S (W1 S) μM) := rfl
  have hΔ : DeltaS S.toDomSeq (cfgX (X0 S)) (W1 S) (fun x => v x • (E00 : Mat)) = QpStar S (W1 S) μM := by
    have h := P_T_cinv (P := piD Set.univ) (T := DeltaS S.toDomSeq (cfgX (X0 S)) (W1 S)) (piD_idem _)
      (hK_triv S Set.univ) (QpL S (W1 S) μM)
    rw [piD_univ, piD_univ] at h
    rw [← Pop_E00 S Set.univ hb φ, hP]
    exact h
  have key : P0 (DeltaS S.toDomSeq (cfgX (X0 S)) (W1 S) (fun x => v x • (E00 : Mat))) g =
      P0 (QpStar S (W1 S) μM) g := by rw [hΔ]
  rw [DeltaS_spec, ← avg_pair S (W1 S)] at key
  simp only [Phi, DU_E00, avgW_E00, E00_mul_E00, ntr_smul, ntr_E00, ntr_mul_E00, g] at key
  simp only [Qs_conj, toDomSeq_L] at key
  have hN' : ((N : ℂ))⁻¹ ≠ 0 := inv_ne_zero hN
  have e1 : ∀ x μ, (v (x + unit NF μ) - v x) * (starRingEnd ℂ (lam (x + unit NF μ)) - starRingEnd ℂ (lam x)) *
      (N : ℂ)⁻¹ = starRingEnd ℂ (lam (x + unit NF μ) - lam x) * (v (x + unit NF μ) - v x) * (N : ℂ)⁻¹ :=
    fun x μ => by rw [map_sub]; ring
  have e2 : ∀ (c : ℂ) (y : Site NF), c * (Qs S S.toDomSeq v y * starRingEnd ℂ (Qs S S.toDomSeq lam y) * (N : ℂ)⁻¹) =
      c * (starRingEnd ℂ (Qs S S.toDomSeq lam y) * Qs S S.toDomSeq v y) * (N : ℂ)⁻¹ := fun c y => by ring
  have e3 : ∀ (c : ℂ) (y : Site NF), c * (starRingEnd ℂ (Qs S S.toDomSeq lam y) * μM y 0 0 * (N : ℂ)⁻¹) =
      c * (starRingEnd ℂ (Qs S S.toDomSeq lam y) * μM y 0 0) * (N : ℂ)⁻¹ := fun c y => by ring
  simp only [e1, e2, e3, ← Finset.sum_mul, ← add_mul] at key
  exact mul_right_cancel₀ hN' key

end SFBounds
end CoreLean

end
