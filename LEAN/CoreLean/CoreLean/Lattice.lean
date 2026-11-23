/-
The lattice of one scale, configurations, plaquettes, and the action of BALABAN_CORE.tex
(`def:lattices`, `def:bonds`, `def:configurations`, `def:action`), and `lem:action`.

Modelling. The lattice `T^{(j)} = (a_j ℤ / ℓ_T ℤ)^4` is described in lattice units as
`Site n = (ZMod n)^4` with `n = ℓ_T / a_j`; the spacing `a_j` enters only the forms and the
differences (`CoreLean.Differences`). A bond is a site, a direction, and an orientation; for
`n ≥ 3` this is the same as the ordered pair `(b_-, b_+)` of `def:bonds`(i). A configuration is
given by its values on the positive bonds and is extended to the negative ones by
`U(b⁻¹) = U(b)⁻¹`, as in `def:configurations`(i). Configurations take values in `GL(N, ℂ)`; the
statements proved here for all such configurations contain those of the core for configurations
with values in `G^c ⊂ GL(N, ℂ)`.
-/
import CoreLean.OpNorm

open Matrix Complex

namespace CoreLean

variable {N n : ℕ} [NeZero n]

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "GLN" => (Matrix (Fin N) (Fin N) ℂ)ˣ

/-- The sites of the lattice of side `n` (in lattice units). -/
abbrev Site (n : ℕ) := Fin 4 → ZMod n

/-- The coordinate unit vector `e_μ`. -/
def unit (n : ℕ) (μ : Fin 4) : Site n := Pi.single μ 1

/-- A bond: its initial site `b_-`, its direction `μ`, and whether it is positive. -/
structure Bond (n : ℕ) where
  site : Site n
  dir : Fin 4
  pos : Bool

namespace Bond

/-- The final site `b_+`. -/
def plus (b : Bond n) : Site n :=
  if b.pos then b.site + unit n b.dir else b.site - unit n b.dir

/-- The reversed bond `b⁻¹ = (b_+, b_-)`. -/
def rev (b : Bond n) : Bond n := ⟨b.plus, b.dir, !b.pos⟩

@[simp] lemma rev_site (b : Bond n) : b.rev.site = b.plus := rfl

lemma rev_plus (b : Bond n) : b.rev.plus = b.site := by
  cases b with
  | mk x μ s => cases s <;> simp [rev, plus]

end Bond

/-- A configuration, given by its values `U_μ(x) = U(x, x + e_μ)` on the positive bonds. -/
abbrev Config (N n : ℕ) := Fin 4 → Site n → (Matrix (Fin N) (Fin N) ℂ)ˣ

namespace Config

/-- The value of a configuration on a bond: `U(x, x - e_μ) = U_μ(x - e_μ)⁻¹`. -/
def val (U : Config N n) (b : Bond n) : GLN :=
  if b.pos then U b.dir b.site else (U b.dir (b.site - unit n b.dir))⁻¹

/-- `U(b⁻¹) = U(b)⁻¹` (`def:configurations`(i)). -/
theorem val_rev (U : Config N n) (b : Bond n) : U.val b.rev = (U.val b)⁻¹ := by
  cases b with
  | mk x μ s => cases s <;> simp [val, Bond.rev, Bond.plus]

/-- The parallel transport `U(γ) = U(b_1) ⋯ U(b_n)` along a path. -/
def hol (U : Config N n) (γ : List (Bond n)) : GLN := (γ.map U.val).prod

/-- A gauge field: a configuration with unitary values. -/
def IsGaugeField (U : Config N n) : Prop :=
  ∀ μ x, ((U μ x : GLN) : Mat) ∈ unitaryGroup (Fin N) ℂ

/-- The action of a complex gauge transformation, `U^u(b) = u(b_-) U(b) u(b_+)⁻¹`
(`eq:gauge-transformation`), on the positive bonds. -/
def gauge (U : Config N n) (u : Site n → GLN) : Config N n :=
  fun μ x => u x * U μ x * (u (x + unit n μ))⁻¹

/-- `U^u(b) = u(b_-) U(b) u(b_+)⁻¹` on every bond. -/
theorem val_gauge (U : Config N n) (u : Site n → GLN) (b : Bond n) :
    (U.gauge u).val b = u b.site * U.val b * (u b.plus)⁻¹ := by
  cases b with
  | mk x μ s =>
    cases s
    · simp only [val, gauge, Bond.plus, Bool.false_eq_true, ↓reduceIte, sub_add_cancel,
        _root_.mul_inv_rev, inv_inv]
      group
    · simp [val, gauge, Bond.plus]

end Config

/-- The boundary `∂p_{μν}(x)` of a plaquette (`def:bonds`(iii)). -/
def plaqPath (μ ν : Fin 4) (x : Site n) : List (Bond n) :=
  [⟨x, μ, true⟩, ⟨x + unit n μ, ν, true⟩, ⟨x + unit n μ + unit n ν, μ, false⟩,
    ⟨x + unit n ν, ν, false⟩]

/-- `U(∂p_{μν}(x))`. -/
def plaq (U : Config N n) (μ ν : Fin 4) (x : Site n) : GLN := U.hol (plaqPath μ ν x)

theorem plaq_eq (U : Config N n) (μ ν : Fin 4) (x : Site n) :
    plaq U μ ν x = U μ x * U ν (x + unit n μ) * (U μ (x + unit n ν))⁻¹ * (U ν x)⁻¹ := by
  simp only [plaq, Config.hol, plaqPath, List.map, List.prod_cons, List.prod_nil, mul_one,
    Config.val, ↓reduceIte, Bool.false_eq_true]
  rw [show x + unit n μ + unit n ν - unit n μ = x + unit n ν by abel,
    show x + unit n ν - unit n ν = x by abel]
  group

/-- `Re W = ½ (W + W⁻¹)` (`eq:real-imaginary`). -/
noncomputable def reW (W : GLN) : Mat := (1 / 2 : ℂ) • ((W : Mat) + ((W⁻¹ : GLN) : Mat))

/-- `Im W = (2i)⁻¹ (W - W⁻¹)` (`eq:real-imaginary`). -/
noncomputable def imW (W : GLN) : Mat := (1 / (2 * I) : ℂ) • ((W : Mat) - ((W⁻¹ : GLN) : Mat))

/-- The summand of the action for the plaquette `p_{μν}(x)`. -/
noncomputable def actionTerm (U : Config N n) (μ ν : Fin 4) (x : Site n) : ℂ :=
  1 - ntr (reW (plaq U μ ν x))

/-- The Yang–Mills action `A(U) = Σ_{p positive} (1 - tr Re U(∂p))` (`eq:action`). -/
noncomputable def action (U : Config N n) : ℂ :=
  ∑ x : Site n, ∑ μ : Fin 4, ∑ ν : Fin 4, if μ < ν then actionTerm U μ ν x else 0

/-- The plaquettes of a gauge field are unitary. -/
lemma plaq_mem_unitary {U : Config N n} (hU : U.IsGaugeField) (μ ν : Fin 4) (x : Site n) :
    ((plaq U μ ν x : GLN) : Mat) ∈ unitaryGroup (Fin N) ℂ := by
  have hinv : ∀ W : GLN, (W : Mat) ∈ unitaryGroup (Fin N) ℂ →
      ((W⁻¹ : GLN) : Mat) ∈ unitaryGroup (Fin N) ℂ := by
    intro W hW
    have : ((W⁻¹ : GLN) : Mat) = star (W : Mat) := by
      have h1 : (W : Mat) * star (W : Mat) = 1 := hW.2
      calc ((W⁻¹ : GLN) : Mat) = ((W⁻¹ : GLN) : Mat) * ((W : Mat) * star (W : Mat)) := by
            rw [h1, Matrix.mul_one]
        _ = star (W : Mat) := by
            rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
    rw [this]; exact Unitary.star_mem hW
  rw [plaq_eq]
  simp only [Units.val_mul]
  exact Submonoid.mul_mem _ (Submonoid.mul_mem _ (Submonoid.mul_mem _ (hU _ _) (hU _ _))
    (hinv _ (hU _ _))) (hinv _ (hU _ _))

/-- For a unitary `W`, `tr Re W = Re tr W`. -/
lemma ntr_reW_of_unitary (W : GLN) (hW : (W : Mat) ∈ unitaryGroup (Fin N) ℂ) :
    ntr (reW W) = ((ntr (W : Mat)).re : ℂ) := by
  have hstar : ((W⁻¹ : GLN) : Mat) = (W : Mat)ᴴ := by
    have h1 : (W : Mat) * star (W : Mat) = 1 := hW.2
    calc ((W⁻¹ : GLN) : Mat) = ((W⁻¹ : GLN) : Mat) * ((W : Mat) * star (W : Mat)) := by
          rw [h1, Matrix.mul_one]
      _ = (W : Mat)ᴴ := by
          rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]; rfl
  unfold reW ntr
  rw [hstar, Matrix.trace_smul, Matrix.trace_add, Matrix.trace_conjTranspose, smul_eq_mul,
    Complex.star_def, Complex.add_conj]
  set t := (W : Mat).trace
  have hre : ((N : ℂ)⁻¹ * t).re = (N : ℝ)⁻¹ * t.re := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.re_ofReal_mul]
  rw [hre]
  push_cast
  ring

/-- `lem:action`(i): for a gauge field,
`A(U) = Σ_p (1 - Re tr U(∂p)) = ½ Σ_p |U(∂p) - 1|² ≥ 0`. -/
theorem action_gaugeField (hN : 0 < N) {U : Config N n} (hU : U.IsGaugeField) :
    action U = ((∑ x : Site n, ∑ μ : Fin 4, ∑ ν : Fin 4,
        if μ < ν then 1 - (ntr ((plaq U μ ν x : GLN) : Mat)).re else 0 : ℝ) : ℂ) ∧
    action U = ((∑ x : Site n, ∑ μ : Fin 4, ∑ ν : Fin 4,
        if μ < ν then (1 / 2) * hs (((plaq U μ ν x : GLN) : Mat) - 1) ^ 2 else 0 : ℝ) : ℂ) ∧
    0 ≤ ∑ x : Site n, ∑ μ : Fin 4, ∑ ν : Fin 4,
        (if μ < ν then (1 / 2) * hs (((plaq U μ ν x : GLN) : Mat) - 1) ^ 2 else 0 : ℝ) := by
  have h1 : action U = ((∑ x : Site n, ∑ μ : Fin 4, ∑ ν : Fin 4,
      if μ < ν then 1 - (ntr ((plaq U μ ν x : GLN) : Mat)).re else 0 : ℝ) : ℂ) := by
    unfold action actionTerm
    push_cast
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun μ _ =>
      Finset.sum_congr rfl fun ν _ => ?_
    split_ifs
    · rw [ntr_reW_of_unitary _ (plaq_mem_unitary hU μ ν x)]; push_cast; ring
    · rfl
  refine ⟨h1, ?_, ?_⟩
  · rw [h1]
    congr 1
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun μ _ =>
      Finset.sum_congr rfl fun ν _ => ?_
    split_ifs
    · exact plaquette_norm hN _ (plaq_mem_unitary hU μ ν x)
    · rfl
  · refine Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun μ _ =>
      Finset.sum_nonneg fun ν _ => ?_
    split_ifs
    · exact mul_nonneg (by norm_num) (sq_nonneg _)
    · exact le_refl 0

/-- The plaquettes of a gauge transform: `U^u(∂p_{μν}(x)) = u(x) U(∂p_{μν}(x)) u(x)⁻¹`. -/
theorem plaq_gauge (U : Config N n) (u : Site n → GLN) (μ ν : Fin 4) (x : Site n) :
    plaq (U.gauge u) μ ν x = u x * plaq U μ ν x * (u x)⁻¹ := by
  rw [plaq_eq, plaq_eq]
  simp only [Config.gauge]
  rw [show x + unit n μ + unit n ν = x + unit n ν + unit n μ by abel]
  group

/-- The trace is invariant under conjugation. -/
lemma trace_conj (u : GLN) (X : Mat) :
    ((u : Mat) * X * ((u⁻¹ : GLN) : Mat)).trace = X.trace := by
  rw [Matrix.trace_mul_cycle, Units.inv_mul, Matrix.one_mul]

lemma conj_inv (u W : GLN) : (u * W * u⁻¹)⁻¹ = u * W⁻¹ * u⁻¹ := by group

lemma reW_conj (u W : GLN) : reW (u * W * u⁻¹) = (u : Mat) * reW W * ((u⁻¹ : GLN) : Mat) := by
  unfold reW
  rw [conj_inv]
  simp only [Units.val_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul]

lemma imW_conj (u W : GLN) : imW (u * W * u⁻¹) = (u : Mat) * imW W * ((u⁻¹ : GLN) : Mat) := by
  unfold imW
  rw [conj_inv]
  simp only [Units.val_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul]

/-- `lem:action`(ii): `Im U^u(∂p_{μν}(x)) = Ad_{u(x)} Im U(∂p_{μν}(x))`. -/
theorem imW_plaq_gauge (U : Config N n) (u : Site n → GLN) (μ ν : Fin 4) (x : Site n) :
    imW (plaq (U.gauge u) μ ν x) =
      ((u x : GLN) : Mat) * imW (plaq U μ ν x) * (((u x)⁻¹ : GLN) : Mat) := by
  rw [plaq_gauge, imW_conj]

/-- The four bonds `b_1, …, b_4` of `∂p_{μν}(x)`, indexed from `0`. -/
def plaqBond (μ ν : Fin 4) (x : Site n) : Fin 4 → Bond n :=
  ![⟨x, μ, true⟩, ⟨x + unit n μ, ν, true⟩, ⟨x + unit n μ + unit n ν, μ, false⟩,
    ⟨x + unit n ν, ν, false⟩]

lemma plaq_eq_bonds (U : Config N n) (μ ν : Fin 4) (x : Site n) :
    plaq U μ ν x = U.val (plaqBond μ ν x 0) * U.val (plaqBond μ ν x 1) *
      U.val (plaqBond μ ν x 2) * U.val (plaqBond μ ν x 3) := by
  simp only [plaq, Config.hol, plaqPath, List.map, List.prod_cons, List.prod_nil, mul_one,
    plaqBond]
  simp [mul_assoc]

/-- The indeterminates for the entries of `U(b_k)` (`false`) and of `U(b_k)⁻¹` (`true`). -/
noncomputable def polyMat (k : Fin 4) (inv : Bool) :
    Matrix (Fin N) (Fin N) (MvPolynomial (Fin 4 × Bool × Fin N × Fin N) ℂ) :=
  fun i j => MvPolynomial.X (k, inv, i, j)

/-- The entries of the matrices `U(b_k)` and `U(b_k)⁻¹`, `b_k` the bonds of `∂p_{μν}(x)`. -/
def plaqEntries (U : Config N n) (μ ν : Fin 4) (x : Site n) :
    Fin 4 × Bool × Fin N × Fin N → ℂ :=
  fun q => if q.2.1 then (((U.val (plaqBond μ ν x q.1))⁻¹ : GLN) : Mat) q.2.2.1 q.2.2.2
    else ((U.val (plaqBond μ ν x q.1) : GLN) : Mat) q.2.2.1 q.2.2.2

lemma map_polyMat (U : Config N n) (μ ν : Fin 4) (x : Site n) (k : Fin 4) (inv : Bool) :
    (polyMat k inv).map (MvPolynomial.eval (plaqEntries U μ ν x)) =
      if inv then (((U.val (plaqBond μ ν x k))⁻¹ : GLN) : Mat)
      else ((U.val (plaqBond μ ν x k) : GLN) : Mat) := by
  ext i j
  cases inv <;> simp [polyMat, plaqEntries]

/-- `lem:action`(iii): the summand of `eq:action` for `p = p_{μν}(x)` is a polynomial in the
entries of the matrices `U(b)` and `U(b)⁻¹` for the four bonds `b` of `∂p`, one polynomial for all
configurations and all `x`. -/
theorem actionTerm_polynomial (μ ν : Fin 4) :
    ∃ P : MvPolynomial (Fin 4 × Bool × Fin N × Fin N) ℂ, ∀ (U : Config N n) (x : Site n),
      actionTerm U μ ν x = MvPolynomial.eval (plaqEntries U μ ν x) P := by
  refine ⟨1 - MvPolynomial.C ((N : ℂ)⁻¹ * (1 / 2)) *
    ((polyMat 0 false * polyMat 1 false * polyMat 2 false * polyMat 3 false).trace +
      (polyMat 3 true * polyMat 2 true * polyMat 1 true * polyMat 0 true).trace), ?_⟩
  intro U x
  rw [map_sub, map_one, map_mul, MvPolynomial.eval_C, map_add,
    AddMonoidHom.map_trace (MvPolynomial.eval (plaqEntries U μ ν x)),
    AddMonoidHom.map_trace (MvPolynomial.eval (plaqEntries U μ ν x))]
  simp only [Matrix.map_mul, map_polyMat, Bool.false_eq_true, ↓reduceIte]
  unfold actionTerm reW ntr
  rw [plaq_eq_bonds, Matrix.trace_smul, Matrix.trace_add, smul_eq_mul]
  have hinv : (U.val (plaqBond μ ν x 0) * U.val (plaqBond μ ν x 1) * U.val (plaqBond μ ν x 2) *
      U.val (plaqBond μ ν x 3))⁻¹ = (U.val (plaqBond μ ν x 3))⁻¹ * (U.val (plaqBond μ ν x 2))⁻¹ *
      (U.val (plaqBond μ ν x 1))⁻¹ * (U.val (plaqBond μ ν x 0))⁻¹ := by group
  rw [hinv]
  simp only [Units.val_mul]
  ring

/-- `lem:action`(ii): `A(U^u) = A(U)` for every complex gauge transformation `u`. -/
theorem action_gauge (U : Config N n) (u : Site n → GLN) : action (U.gauge u) = action U := by
  unfold action actionTerm
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun μ _ =>
    Finset.sum_congr rfl fun ν _ => ?_
  rw [plaq_gauge, reW_conj, ntr, trace_conj, ← ntr]

end CoreLean
