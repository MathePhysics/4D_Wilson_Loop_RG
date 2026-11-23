/-
The non-abelian Stokes bounds behind the plaquette counts of BALABAN_CORE.tex (`a7d5e1f955b0`,
rechecked at `5bdadc538330`): `lem:average`(v), `lem:moved-transports`(iii), and `lem:axial-smallness`
move a path across plaquettes, and the value of a gauge field changes by a product of conjugates of
plaquette variables, each of which differs from `id` by at most the bound of the plaquettes.

* `unit_square`: the holonomy of a unit square, `U(r₀)U(t')(U(t)U(r₁))⁻¹`, is a conjugate of a plaquette
  variable or of its inverse, by a value of the field (four cases of orientation).
* `ladder`: for a connected path `γ` and its translate `γ'` by one bond `r` in the direction `ρ`,
  `‖U(r₀)U(γ')(U(γ)U(r_end))⁻¹ - id‖ ≤ |γ|β`, if the plaquettes of the squares between `γ` and `γ'` are at
  most `β` in `‖·‖`.
* `iterated_ladder`: the same for the translate by `k` bonds, with the bound `k|γ|β`.

The plaquette hypothesis is local: only the plaquettes with all four corners in a set `R` of sites enter.
-/
import CoreLean.Lattice
import CoreLean.ChartAverage
import CoreLean.AxialSmallness

open Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace CoreLean

namespace LatticePaths

set_option linter.unusedSectionVars false

variable {N n : ℕ} [NeZero n]

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "GLN" => (Matrix (Fin N) (Fin N) ℂ)ˣ
local notation "UG" => unitaryGroup (Fin N) ℂ

/-! ### Unitary elements of `GL(N, ℂ)` -/

/-- An element of `GL(N, ℂ)` with a unitary matrix. -/
def IsU (g : GLN) : Prop := (g : Mat) ∈ UG

lemma inv_val_eq_star {g : GLN} (hg : IsU g) : ((g⁻¹ : GLN) : Mat) = star (g : Mat) := by
  have h := (mem_unitaryGroup_iff).1 hg
  calc ((g⁻¹ : GLN) : Mat) = ((g⁻¹ : GLN) : Mat) * ((g : Mat) * star (g : Mat)) := by rw [h, mul_one]
    _ = star (g : Mat) := by rw [← mul_assoc, Units.inv_mul, one_mul]

lemma IsU.mul {g h : GLN} (hg : IsU g) (hh : IsU h) : IsU (g * h) := by
  unfold IsU; rw [Units.val_mul]; exact Submonoid.mul_mem _ hg hh

lemma IsU.inv {g : GLN} (hg : IsU g) : IsU g⁻¹ := by
  unfold IsU; rw [inv_val_eq_star hg]; exact Unitary.star_mem hg

lemma IsU.one : IsU (1 : GLN) := by unfold IsU; rw [Units.val_one]; exact Submonoid.one_mem _

lemma norm_mul_sub_one_le {g h : GLN} (hg : IsU g) :
    ‖((g * h : GLN) : Mat) - 1‖ ≤ ‖(g : Mat) - 1‖ + ‖(h : Mat) - 1‖ := by
  rw [Units.val_mul]
  have e : (g : Mat) * h - 1 = g * ((h : Mat) - 1) + ((g : Mat) - 1) := by noncomm_ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [CStarRing.norm_mem_unitary_mul _ hg]
  linarith

lemma norm_conj_sub_one' {g h : GLN} (hg : IsU g) :
    ‖((g * h * g⁻¹ : GLN) : Mat) - 1‖ = ‖(h : Mat) - 1‖ := by
  rw [Units.val_mul, Units.val_mul, inv_val_eq_star hg]
  exact AxialSmallness.norm_conj_sub_one hg _

lemma norm_inv_sub_one' {g : GLN} (hg : IsU g) : ‖((g⁻¹ : GLN) : Mat) - 1‖ = ‖(g : Mat) - 1‖ := by
  rw [inv_val_eq_star hg]
  exact AxialSmallness.norm_star_sub_one hg

/-! ### Values of a gauge field -/

variable {U : Config N n}

lemma val_isU (hU : U.IsGaugeField) (b : Bond n) : IsU (U.val b) := by
  unfold Config.val
  split_ifs
  · exact hU _ _
  · exact IsU.inv (hU _ _)

lemma hol_isU (hU : U.IsGaugeField) (γ : List (Bond n)) : IsU (U.hol γ) := by
  induction γ with
  | nil => simpa [Config.hol] using IsU.one
  | cons b γ ih =>
    simp only [Config.hol, List.map_cons, List.prod_cons]
    exact (val_isU hU b).mul ih

lemma hol_cons (b : Bond n) (γ : List (Bond n)) : U.hol (b :: γ) = U.val b * U.hol γ := by
  simp [Config.hol]

lemma hol_append (γ δ : List (Bond n)) : U.hol (γ ++ δ) = U.hol γ * U.hol δ := by
  simp [Config.hol, List.map_append, List.prod_append]

@[simp] lemma hol_nil : U.hol ([] : List (Bond n)) = 1 := by simp [Config.hol]

lemma plaq_self (μ : Fin 4) (x : Site n) : plaq U μ μ x = 1 := by
  rw [plaq_eq]; group

/-! ### Paths -/

/-- The translate of a bond by a vector. -/
def _root_.CoreLean.Bond.shift (b : Bond n) (v : Site n) : Bond n := ⟨b.site + v, b.dir, b.pos⟩

lemma _root_.CoreLean.Bond.shift_plus (b : Bond n) (v : Site n) : (b.shift v).plus = b.plus + v := by
  cases b with
  | mk x μ s => cases s <;> simp [Bond.shift, Bond.plus] <;> abel

lemma _root_.CoreLean.Bond.shift_shift (b : Bond n) (u v : Site n) : (b.shift u).shift v = b.shift (u + v) := by
  simp [Bond.shift, add_assoc]

/-- The unit vector `±e_ρ`. -/
def dvec (ρ : Fin 4) (s : Bool) : Site n := if s then unit n ρ else -unit n ρ

lemma rung_plus (z : Site n) (ρ : Fin 4) (s : Bool) : (⟨z, ρ, s⟩ : Bond n).plus = z + dvec ρ s := by
  cases s <;> simp [Bond.plus, dvec, sub_eq_add_neg]

/-- A connected path starting at `z`. -/
def Chain : Site n → List (Bond n) → Prop
  | _, [] => True
  | z, b :: l => b.site = z ∧ Chain b.plus l

/-- The end point of a path starting at `z`. -/
def endpt : Site n → List (Bond n) → Site n
  | z, [] => z
  | _, b :: l => endpt b.plus l

lemma chain_shift (v : Site n) : ∀ (γ : List (Bond n)) (z : Site n), Chain z γ →
    Chain (z + v) (γ.map (Bond.shift · v))
  | [], _, _ => trivial
  | b :: l, z, ⟨h1, h2⟩ => by
    refine ⟨by simp [Bond.shift, h1], ?_⟩
    rw [Bond.shift_plus]
    exact chain_shift v l b.plus h2

lemma endpt_shift (v : Site n) : ∀ (γ : List (Bond n)) (z : Site n),
    endpt (z + v) (γ.map (Bond.shift · v)) = endpt z γ + v
  | [], _ => rfl
  | b :: l, z => by
    simp only [List.map_cons, endpt]
    rw [Bond.shift_plus]
    exact endpt_shift v l b.plus

lemma map_shift_shift (γ : List (Bond n)) (u v : Site n) :
    (γ.map (Bond.shift · u)).map (Bond.shift · v) = γ.map (Bond.shift · (u + v)) := by
  simp [List.map_map, Function.comp_def, Bond.shift_shift]

/-! ### The unit square -/

/-- All four corners of the plaquette `p_{μν}(x)` lie in `R`. -/
def PlaqIn (R : Set (Site n)) (μ ν : Fin 4) (x : Site n) : Prop :=
  x ∈ R ∧ x + unit n μ ∈ R ∧ x + unit n ν ∈ R ∧ x + unit n μ + unit n ν ∈ R

/-- The plaquettes with corners in `R` are at most `β` in `‖·‖`. -/
def PlaqBound (U : Config N n) (R : Set (Site n)) (β : ℝ) : Prop :=
  ∀ μ ν x, μ ≠ ν → PlaqIn R μ ν x → ‖((plaq U μ ν x : GLN) : Mat) - 1‖ ≤ β

lemma plaqBound_all {R : Set (Site n)} {β : ℝ} (hβ : 0 ≤ β) (hP : PlaqBound U R β) :
    ∀ μ ν x, PlaqIn R μ ν x → ‖((plaq U μ ν x : GLN) : Mat) - 1‖ ≤ β := by
  intro μ ν x hx
  by_cases h : μ = ν
  · subst h; rw [plaq_self]; simpa using hβ
  · exact hP μ ν x h hx

/-- The unit square spanned by a bond `t` and the bond `r = (z, z ± e_ρ)` at its beginning: its corners
`t₋, t₊, t₋ ± e_ρ, t₊ ± e_ρ` lie in `R`, so its holonomy `U(r₀)U(t')(U(t)U(r₁))⁻¹` is at most `β`. -/
lemma mem_of_eq {R : Set (Site n)} {x y : Site n} (h : x ∈ R) (e : x = y) : y ∈ R := e ▸ h

lemma norm_sub_one_eq_of_eq {X Y : GLN} (h : X = Y) : ‖(X : Mat) - 1‖ = ‖(Y : Mat) - 1‖ := by rw [h]

theorem unit_square (hU : U.IsGaugeField) {R : Set (Site n)} {β : ℝ} (hβ : 0 ≤ β)
    (hP : PlaqBound U R β) (z : Site n) (μ ρ : Fin 4) (tp s : Bool)
    (hR : z ∈ R ∧ (⟨z, μ, tp⟩ : Bond n).plus ∈ R ∧ z + dvec ρ s ∈ R ∧
      (⟨z, μ, tp⟩ : Bond n).plus + dvec ρ s ∈ R) :
    ‖((U.val ⟨z, ρ, s⟩ * U.val ((⟨z, μ, tp⟩ : Bond n).shift (dvec ρ s)) *
      (U.val ⟨z, μ, tp⟩ * U.val ⟨(⟨z, μ, tp⟩ : Bond n).plus, ρ, s⟩)⁻¹ : GLN) : Mat) - 1‖ ≤ β := by
  have hPa := plaqBound_all hβ hP
  have hpU : ∀ μ ν x, IsU (plaq U μ ν x) := fun μ ν x => hol_isU hU _
  have hUu : ∀ μ x, IsU (U μ x) := fun μ x => hU μ x
  obtain ⟨h1, h2, h3, h4⟩ := hR
  cases tp <;> cases s <;>
    simp only [Bond.plus, Bond.shift, dvec, Bool.false_eq_true, ↓reduceIte] at h2 h3 h4
  · -- backwards step, backwards rung: a conjugate of `p_{μρ}(w)⁻¹`, `w = z - e_μ - e_ρ`
    rw [norm_sub_one_eq_of_eq (Y := ((U ρ (z - unit n ρ))⁻¹ * (U μ (z - unit n μ - unit n ρ))⁻¹) *
      (plaq U μ ρ (z - unit n μ - unit n ρ))⁻¹ *
      ((U ρ (z - unit n ρ))⁻¹ * (U μ (z - unit n μ - unit n ρ))⁻¹)⁻¹) ?_]
    · rw [norm_conj_sub_one' ((hUu _ _).inv.mul (hUu _ _).inv), norm_inv_sub_one' (hpU _ _ _)]
      refine hPa _ _ _ ⟨?_, ?_, ?_, ?_⟩ <;>
        first
          | (refine mem_of_eq h1 ?_; abel1) | (refine mem_of_eq h2 ?_; abel1)
          | (refine mem_of_eq h3 ?_; abel1) | (refine mem_of_eq h4 ?_; abel1)
    · simp only [Config.val, Bond.plus, Bond.shift, dvec, Bool.false_eq_true, ↓reduceIte]
      rw [plaq_eq]; abel_nf; group
  · -- backwards step, forwards rung: a conjugate of `p_{ρμ}(w)⁻¹`, `w = z - e_μ`
    rw [norm_sub_one_eq_of_eq (Y := (U μ (z - unit n μ))⁻¹ * (plaq U ρ μ (z - unit n μ))⁻¹ *
      ((U μ (z - unit n μ))⁻¹)⁻¹) ?_]
    · rw [norm_conj_sub_one' (hUu _ _).inv, norm_inv_sub_one' (hpU _ _ _)]
      refine hPa _ _ _ ⟨?_, ?_, ?_, ?_⟩ <;>
        first
          | (refine mem_of_eq h1 ?_; abel1) | (refine mem_of_eq h2 ?_; abel1)
          | (refine mem_of_eq h3 ?_; abel1) | (refine mem_of_eq h4 ?_; abel1)
    · simp only [Config.val, Bond.plus, Bond.shift, dvec, Bool.false_eq_true, ↓reduceIte]
      rw [plaq_eq]; abel_nf; group
  · -- forwards step, backwards rung: a conjugate of `p_{μρ}(w)`, `w = z - e_ρ`
    rw [norm_sub_one_eq_of_eq (Y := (U ρ (z - unit n ρ))⁻¹ * plaq U μ ρ (z - unit n ρ) *
      ((U ρ (z - unit n ρ))⁻¹)⁻¹) ?_]
    · rw [norm_conj_sub_one' (hUu _ _).inv]
      refine hPa _ _ _ ⟨?_, ?_, ?_, ?_⟩ <;>
        first
          | (refine mem_of_eq h1 ?_; abel1) | (refine mem_of_eq h2 ?_; abel1)
          | (refine mem_of_eq h3 ?_; abel1) | (refine mem_of_eq h4 ?_; abel1)
    · simp only [Config.val, Bond.plus, Bond.shift, dvec, Bool.false_eq_true, ↓reduceIte]
      rw [plaq_eq]; abel_nf; group
  · -- forwards step, forwards rung: `p_{ρμ}(z)`
    rw [norm_sub_one_eq_of_eq (Y := plaq U ρ μ z) ?_]
    · refine hPa _ _ _ ⟨?_, ?_, ?_, ?_⟩ <;>
        first
          | (refine mem_of_eq h1 ?_; abel1) | (refine mem_of_eq h2 ?_; abel1)
          | (refine mem_of_eq h3 ?_; abel1) | (refine mem_of_eq h4 ?_; abel1)
    · simp only [Config.val, Bond.plus, Bond.shift, dvec, Bool.false_eq_true, ↓reduceIte]
      rw [plaq_eq]; abel_nf; group

/-! ### Ladders -/

/-- The squares between a path `γ` from `z` and its translate by `±e_ρ` have their corners in `R`. -/
def LadderIn (R : Set (Site n)) (d : Site n) (γ : List (Bond n)) : Prop :=
  ∀ t ∈ γ, t.site ∈ R ∧ t.plus ∈ R ∧ t.site + d ∈ R ∧ t.plus + d ∈ R

/-- The ladder: `‖U(r_z)U(γ')(U(γ)U(r_{z'}))⁻¹ - id‖ ≤ |γ|β` for the translate `γ'` of a path `γ` from `z`
to `z'` by `±e_ρ`, with the rungs `r_z = (z, z ± e_ρ)`. -/
theorem ladder (hU : U.IsGaugeField) {R : Set (Site n)} {β : ℝ} (hβ : 0 ≤ β)
    (hP : PlaqBound U R β) (ρ : Fin 4) (s : Bool) :
    ∀ (γ : List (Bond n)) (z : Site n), Chain z γ → LadderIn R (dvec ρ s) γ →
      ‖((U.val ⟨z, ρ, s⟩ * U.hol (γ.map (Bond.shift · (dvec ρ s))) *
        (U.hol γ * U.val ⟨endpt z γ, ρ, s⟩)⁻¹ : GLN) : Mat) - 1‖ ≤ γ.length * β
  | [], z, _, _ => by simp [endpt]
  | t :: γ, z, ⟨hz, hc⟩, hR => by
    subst hz
    have hsq : ‖((U.val ⟨t.site, ρ, s⟩ * U.val (t.shift (dvec ρ s)) *
        (U.val t * U.val ⟨t.plus, ρ, s⟩)⁻¹ : GLN) : Mat) - 1‖ ≤ β :=
      unit_square hU hβ hP t.site t.dir ρ t.pos s (hR t List.mem_cons_self)
    have ih := ladder hU hβ hP ρ s γ t.plus hc (fun t' ht' => hR t' (List.mem_cons_of_mem _ ht'))
    simp only [List.map_cons, hol_cons, endpt, List.length_cons, Nat.cast_add, Nat.cast_one]
    set Q := U.val ⟨t.site, ρ, s⟩ * U.val (t.shift (dvec ρ s)) * (U.val t * U.val ⟨t.plus, ρ, s⟩)⁻¹
    set C := U.val ⟨t.plus, ρ, s⟩ * U.hol (γ.map (Bond.shift · (dvec ρ s))) *
      (U.hol γ * U.val ⟨endpt t.plus γ, ρ, s⟩)⁻¹
    have e : U.val ⟨t.site, ρ, s⟩ * (U.val (t.shift (dvec ρ s)) *
        U.hol (γ.map (Bond.shift · (dvec ρ s)))) *
        (U.val t * U.hol γ * U.val ⟨endpt t.plus γ, ρ, s⟩)⁻¹ = Q * (U.val t * C * (U.val t)⁻¹) := by
      simp only [Q, C]; group
    rw [show U.val t * U.hol γ * U.val ⟨endpt t.plus γ, ρ, s⟩ =
      U.val t * U.hol γ * U.val ⟨endpt t.plus γ, ρ, s⟩ from rfl] at e
    calc ‖((U.val ⟨t.site, ρ, s⟩ * (U.val (t.shift (dvec ρ s)) *
          U.hol (γ.map (Bond.shift · (dvec ρ s)))) *
          (U.val t * U.hol γ * U.val ⟨endpt t.plus γ, ρ, s⟩)⁻¹ : GLN) : Mat) - 1‖
        = ‖((Q * (U.val t * C * (U.val t)⁻¹) : GLN) : Mat) - 1‖ := by rw [e]
      _ ≤ ‖(Q : Mat) - 1‖ + ‖((U.val t * C * (U.val t)⁻¹ : GLN) : Mat) - 1‖ := by
          refine norm_mul_sub_one_le ?_
          simp only [Q]
          exact (((val_isU hU _).mul (val_isU hU _)).mul ((val_isU hU _).mul (val_isU hU _)).inv)
      _ = ‖(Q : Mat) - 1‖ + ‖(C : Mat) - 1‖ := by rw [norm_conj_sub_one' (val_isU hU t)]
      _ ≤ β + γ.length * β := add_le_add hsq ih
      _ = (γ.length + 1) * β := by ring

/-! ### Segments and iterated ladders -/

/-- The straight path of `k` bonds from `z` in the direction `±e_ρ`. -/
def seg (ρ : Fin 4) (s : Bool) : Site n → ℕ → List (Bond n)
  | _, 0 => []
  | z, k + 1 => ⟨z, ρ, s⟩ :: seg ρ s (z + dvec ρ s) k

lemma chain_seg (ρ : Fin 4) (s : Bool) : ∀ (k : ℕ) (z : Site n), Chain z (seg ρ s z k)
  | 0, _ => trivial
  | k + 1, z => ⟨rfl, by rw [rung_plus]; exact chain_seg ρ s k _⟩

lemma endpt_seg (ρ : Fin 4) (s : Bool) : ∀ (k : ℕ) (z : Site n),
    endpt z (seg ρ s z k) = z + k • dvec ρ s
  | 0, z => by simp [seg, endpt]
  | k + 1, z => by
    simp only [seg, endpt]
    rw [rung_plus, endpt_seg ρ s k, succ_nsmul]
    abel

lemma length_seg (ρ : Fin 4) (s : Bool) : ∀ (k : ℕ) (z : Site n), (seg ρ s z k).length = k
  | 0, _ => rfl
  | k + 1, z => by simp [seg, length_seg ρ s k]

lemma map_shift_seg (ρ : Fin 4) (s : Bool) (v : Site n) : ∀ (k : ℕ) (z : Site n),
    (seg ρ s z k).map (Bond.shift · v) = seg ρ s (z + v) k
  | 0, _ => rfl
  | k + 1, z => by
    simp only [seg, List.map_cons]
    rw [map_shift_seg ρ s v k, show z + dvec ρ s + v = z + v + dvec ρ s by abel]
    rfl

lemma map_shift_zero (γ : List (Bond n)) : γ.map (Bond.shift · 0) = γ := by
  simp [Bond.shift]

/-- The iterated ladder: for the translate of a path `γ` from `z` by `k` bonds `±e_ρ`,
`‖U([z, z + kd])U(γ')(U(γ)U([z', z' + kd]))⁻¹ - id‖ ≤ k|γ|β`. -/
theorem iterated_ladder (hU : U.IsGaugeField) {R : Set (Site n)} {β : ℝ} (hβ : 0 ≤ β)
    (hP : PlaqBound U R β) (ρ : Fin 4) (s : Bool) (k : ℕ) :
    ∀ (γ : List (Bond n)) (z : Site n), Chain z γ →
      (∀ j < k, LadderIn R (dvec ρ s) (γ.map (Bond.shift · (j • dvec ρ s)))) →
      ‖((U.hol (seg ρ s z k) * U.hol (γ.map (Bond.shift · (k • dvec ρ s))) *
        (U.hol γ * U.hol (seg ρ s (endpt z γ) k))⁻¹ : GLN) : Mat) - 1‖ ≤ k * γ.length * β := by
  induction k with
  | zero => intro γ z _ _; simp [seg, map_shift_zero]
  | succ k ih =>
    intro γ z hc hR
    have hc₁ : Chain (z + dvec ρ s) (γ.map (Bond.shift · (dvec ρ s))) := chain_shift _ γ z hc
    have hXk := ih (γ.map (Bond.shift · (dvec ρ s))) (z + dvec ρ s) hc₁ (fun j hj => by
      have := hR (j + 1) (by omega)
      rwa [map_shift_shift, show dvec ρ s + j • dvec ρ s = (j + 1) • dvec ρ s by
        rw [succ_nsmul]; abel])
    have hY := ladder hU hβ hP ρ s γ z hc (by simpa [map_shift_zero] using hR 0 (by omega))
    rw [endpt_shift, List.length_map, map_shift_shift,
      show dvec ρ s + k • dvec ρ s = (k + 1) • dvec ρ s by rw [succ_nsmul]; abel] at hXk
    have hconj : IsU (U.val ⟨z, ρ, s⟩ * (U.hol (seg ρ s (z + dvec ρ s) k) *
        U.hol (γ.map (Bond.shift · ((k + 1) • dvec ρ s))) *
        (U.hol (γ.map (Bond.shift · (dvec ρ s))) * U.hol (seg ρ s (endpt z γ + dvec ρ s) k))⁻¹) *
        (U.val ⟨z, ρ, s⟩)⁻¹) :=
      (((val_isU hU _).mul (((hol_isU hU _).mul (hol_isU hU _)).mul
        ((hol_isU hU _).mul (hol_isU hU _)).inv)).mul (val_isU hU _).inv)
    rw [norm_sub_one_eq_of_eq (Y := (U.val ⟨z, ρ, s⟩ * (U.hol (seg ρ s (z + dvec ρ s) k) *
        U.hol (γ.map (Bond.shift · ((k + 1) • dvec ρ s))) *
        (U.hol (γ.map (Bond.shift · (dvec ρ s))) * U.hol (seg ρ s (endpt z γ + dvec ρ s) k))⁻¹) *
        (U.val ⟨z, ρ, s⟩)⁻¹) *
      (U.val ⟨z, ρ, s⟩ * U.hol (γ.map (Bond.shift · (dvec ρ s))) *
        (U.hol γ * U.val ⟨endpt z γ, ρ, s⟩)⁻¹)) ?_]
    · refine (norm_mul_sub_one_le hconj).trans ?_
      rw [norm_conj_sub_one' (val_isU hU _)]
      refine (add_le_add hXk hY).trans (le_of_eq ?_)
      push_cast; ring
    · simp only [seg, hol_cons]
      group

/-! ### Signed segments and rectangles -/

/-- The straight path from `z` to `z + k e_μ`, `k ∈ ℤ`. -/
def segZ (μ : Fin 4) (z : Site n) (k : ℤ) : List (Bond n) :=
  if 0 ≤ k then seg μ true z k.toNat else seg μ false z (-k).toNat

/-- The sign and the length of a signed segment. -/
def sgn (k : ℤ) : Bool := decide (0 ≤ k)

lemma segZ_eq (μ : Fin 4) (z : Site n) (k : ℤ) : segZ μ z k = seg μ (sgn k) z k.natAbs := by
  unfold segZ sgn
  by_cases h : 0 ≤ k
  · simp only [h, ↓reduceIte, decide_true]; congr 1; omega
  · simp only [h, ↓reduceIte, decide_false]; congr 1; omega

lemma natAbs_smul_dvec (μ : Fin 4) (k : ℤ) : k.natAbs • dvec μ (sgn k) = k • (unit n μ : Site n) := by
  unfold sgn dvec
  by_cases h : 0 ≤ k
  · simp only [h, decide_true, ↓reduceIte]
    rw [← natCast_zsmul, Int.natCast_natAbs, abs_of_nonneg h]
  · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte]
    rw [smul_neg, ← natCast_zsmul, Int.natCast_natAbs, abs_of_neg (lt_of_not_ge h), neg_smul,
      neg_neg]

lemma endpt_segZ (μ : Fin 4) (z : Site n) (k : ℤ) : endpt z (segZ μ z k) = z + k • unit n μ := by
  rw [segZ_eq, endpt_seg, natAbs_smul_dvec]

lemma chain_segZ (μ : Fin 4) (z : Site n) (k : ℤ) : Chain z (segZ μ z k) := by
  rw [segZ_eq]; exact chain_seg _ _ _ _

lemma length_segZ (μ : Fin 4) (z : Site n) (k : ℤ) : (segZ μ z k).length = k.natAbs := by
  rw [segZ_eq, length_seg]

lemma map_shift_segZ (μ : Fin 4) (v z : Site n) (k : ℤ) :
    (segZ μ z k).map (Bond.shift · v) = segZ μ (z + v) k := by
  rw [segZ_eq, segZ_eq, map_shift_seg]

/-- The rectangle: the two paths along the sides `a e_μ` and `b e_ν` of a rectangle from `q` differ by
at most `|a||b|β`, when the squares of the rectangle have their corners in `R`. -/
theorem rectangle (hU : U.IsGaugeField) {R : Set (Site n)} {β : ℝ} (hβ : 0 ≤ β)
    (hP : PlaqBound U R β) (μ ν : Fin 4) (q : Site n) (a b : ℤ)
    (hR : ∀ j < a.natAbs, LadderIn R (dvec μ (sgn a))
      ((segZ ν q b).map (Bond.shift · (j • dvec μ (sgn a))))) :
    ‖((U.hol (segZ μ q a ++ segZ ν (q + a • unit n μ) b) *
      (U.hol (segZ ν q b ++ segZ μ (q + b • unit n ν) a))⁻¹ : GLN) : Mat) - 1‖ ≤
      a.natAbs * b.natAbs * β := by
  have h := iterated_ladder hU hβ hP μ (sgn a) a.natAbs (segZ ν q b) q (chain_segZ ν q b) hR
  rw [map_shift_segZ, natAbs_smul_dvec, endpt_segZ, length_segZ, ← segZ_eq, ← segZ_eq] at h
  rw [hol_append, hol_append]
  convert h using 3

/-! ### Boxes -/

/-- The point `y + Σ_σ m_σ e_σ` with integer offsets `m`. -/
def ofs (y : Site n) (m : Fin 4 → ℤ) : Site n := y + fun σ => (m σ : ZMod n)

lemma ofs_add_single (y : Site n) (m : Fin 4 → ℤ) (μ : Fin 4) (k : ℤ) :
    ofs y (m + Pi.single μ k) = ofs y m + k • unit n μ := by
  unfold ofs unit
  funext σ
  by_cases h : σ = μ
  · subst h; simp [add_assoc]
  · simp [Pi.single_apply, h]

lemma ofs_zero (y : Site n) : ofs y 0 = y := by unfold ofs; ext σ; simp

/-- The offsets in the box `lo ≤ m ≤ hi`. -/
def InBox (lo hi m : Fin 4 → ℤ) : Prop := ∀ σ, lo σ ≤ m σ ∧ m σ ≤ hi σ

/-- The box `{y + Σ m_σ e_σ | lo ≤ m ≤ hi}` of sites. -/
def boxR (y : Site n) (lo hi : Fin 4 → ℤ) : Set (Site n) := {p | ∃ m, InBox lo hi m ∧ p = ofs y m}

/-- `x` lies between `0` and `a`. -/
def Btw (x a : ℤ) : Prop := min 0 a ≤ x ∧ x ≤ max 0 a

/-- A rectangle with three corners in a box lies in the box. -/
lemma inBox_rect {lo hi o : Fin 4 → ℤ} {μ ν : Fin 4} {a b i j : ℤ} (hμν : μ ≠ ν)
    (h0 : InBox lo hi o) (ha : InBox lo hi (o + Pi.single μ a)) (hb : InBox lo hi (o + Pi.single ν b))
    (hj : Btw j a) (hib : Btw i b) : InBox lo hi (o + Pi.single ν i + Pi.single μ j) := by
  intro σ
  have h0σ := h0 σ; have haσ := ha σ; have hbσ := hb σ
  unfold Btw at hib hj
  by_cases hσμ : σ = μ
  · subst hσμ
    simp only [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hμν, add_zero] at haσ hbσ ⊢
    omega
  · by_cases hσν : σ = ν
    · subst hσν
      simp only [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hσμ, add_zero] at haσ hbσ ⊢
      omega
    · simp only [Pi.add_apply, Pi.single_eq_of_ne hσμ, Pi.single_eq_of_ne hσν, add_zero] at haσ hbσ ⊢
      omega

/-- The signed integer `±i` of `i` steps `±e_ρ`. -/
def zi (s : Bool) (i : ℕ) : ℤ := if s then (i : ℤ) else -(i : ℤ)

lemma nsmul_dvec (ρ : Fin 4) (s : Bool) (i : ℕ) : i • dvec ρ s = zi s i • (unit n ρ : Site n) := by
  unfold zi dvec
  cases s <;> simp [smul_neg, natCast_zsmul]

lemma btw_zi {a : ℤ} {i : ℕ} (h : i ≤ a.natAbs) : Btw (zi (sgn a) i) a := by
  unfold Btw zi sgn
  by_cases h0 : 0 ≤ a
  · simp only [h0, decide_true, ↓reduceIte]; omega
  · simp only [h0, decide_false, Bool.false_eq_true, ↓reduceIte]; omega

lemma mem_seg_iff {ρ : Fin 4} {s : Bool} : ∀ {k : ℕ} {z : Site n} {t : Bond n}, t ∈ seg ρ s z k →
    ∃ i < k, t.site = z + i • dvec ρ s ∧ t.plus = z + (i + 1) • dvec ρ s
  | 0, _, _, h => by simp [seg] at h
  | k + 1, z, t, h => by
    simp only [seg, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨0, by omega, by simp, by rw [rung_plus]; simp⟩
    · obtain ⟨i, hi, hs, hp⟩ := mem_seg_iff h
      refine ⟨i + 1, by omega, ?_, ?_⟩
      · rw [hs, succ_nsmul]; abel
      · rw [hp, succ_nsmul (n := i + 1)]; abel

/-- The squares between `segZ ν (y + o) b` and its translates by `j e_μ`, `j < |a|`, lie in a box which
contains three corners of the rectangle. -/
lemma rect_ladderIn {y : Site n} {lo hi o : Fin 4 → ℤ} {μ ν : Fin 4} (hμν : μ ≠ ν) {a b : ℤ}
    (h0 : InBox lo hi o) (ha : InBox lo hi (o + Pi.single μ a)) (hb : InBox lo hi (o + Pi.single ν b)) :
    ∀ j < a.natAbs, LadderIn (boxR y lo hi) (dvec μ (sgn a))
      ((segZ ν (ofs y o) b).map (Bond.shift · (j • dvec μ (sgn a)))) := by
  intro j hj t ht
  obtain ⟨t₀, ht₀, rfl⟩ := List.mem_map.1 ht
  rw [segZ_eq] at ht₀
  obtain ⟨i, hib, hs, hp⟩ := mem_seg_iff ht₀
  have hpt : ∀ i' j' : ℕ, i' ≤ b.natAbs → j' ≤ a.natAbs →
      ofs y o + i' • dvec ν (sgn b) + j' • dvec μ (sgn a) ∈ boxR y lo hi := fun i' j' hi' hj' =>
    ⟨_, inBox_rect hμν h0 ha hb (btw_zi hj') (btw_zi hi'), by
      rw [ofs_add_single, ofs_add_single, nsmul_dvec, nsmul_dvec]⟩
  simp only [Bond.shift_plus]
  refine ⟨?_, ?_, ?_, ?_⟩
  · show t₀.site + j • dvec μ (sgn a) ∈ _
    rw [hs]; exact hpt i j (by omega) (by omega)
  · rw [hp]; exact hpt (i + 1) j (by omega) (by omega)
  · show t₀.site + j • dvec μ (sgn a) + dvec μ (sgn a) ∈ _
    rw [hs, add_assoc, ← succ_nsmul]; exact hpt i (j + 1) (by omega) (by omega)
  · rw [hp, add_assoc, ← succ_nsmul]; exact hpt (i + 1) (j + 1) (by omega) (by omega)

/-! ### Staircase paths and the exchange of two coordinates -/

/-- The staircase path from `y + o` which traverses the coordinates of the list in order, `m_μ` bonds
in the direction `e_μ` for each (`def:block-paths`(i)). -/
def stair (y : Site n) (m : Fin 4 → ℤ) : List (Fin 4) → (Fin 4 → ℤ) → List (Bond n)
  | [], _ => []
  | μ :: l, o => segZ μ (ofs y o) (m μ) ++ stair y m l (o + Pi.single μ (m μ))

/-- The offsets of the coordinates of a list. -/
def offs (m : Fin 4 → ℤ) (P : List (Fin 4)) : Fin 4 → ℤ := (P.map fun σ => Pi.single σ (m σ)).sum

lemma stair_append (y : Site n) (m : Fin 4 → ℤ) : ∀ (P l : List (Fin 4)) (o : Fin 4 → ℤ),
    stair y m (P ++ l) o = stair y m P o ++ stair y m l (o + offs m P)
  | [], l, o => by simp [stair, offs]
  | μ :: P, l, o => by
    simp only [List.cons_append, stair, stair_append y m P l, List.append_assoc, offs, List.map_cons,
      List.sum_cons, add_assoc]

/-- Exchanging two consecutive coordinates `μ ≠ ν` changes the holonomy by at most `|m_μ||m_ν|β`. -/
theorem stair_swap (hU : U.IsGaugeField) {y : Site n} {lo hi : Fin 4 → ℤ} {β : ℝ} (hβ : 0 ≤ β)
    (hP : PlaqBound U (boxR y lo hi) β) (m : Fin 4 → ℤ) (P S : List (Fin 4)) {μ ν : Fin 4}
    (hμν : μ ≠ ν) (o : Fin 4 → ℤ) (h0 : InBox lo hi (o + offs m P))
    (ha : InBox lo hi (o + offs m P + Pi.single μ (m μ)))
    (hb : InBox lo hi (o + offs m P + Pi.single ν (m ν))) :
    ‖((U.hol (stair y m (P ++ μ :: ν :: S) o) * (U.hol (stair y m (P ++ ν :: μ :: S) o))⁻¹ : GLN) :
      Mat) - 1‖ ≤ (m μ).natAbs * (m ν).natAbs * β := by
  have hrect := rectangle hU hβ hP μ ν (ofs y (o + offs m P)) (m μ) (m ν)
    (rect_ladderIn hμν h0 ha hb)
  set R1 := U.hol (segZ μ (ofs y (o + offs m P)) (m μ) ++
    segZ ν (ofs y (o + offs m P) + m μ • unit n μ) (m ν))
  set R2 := U.hol (segZ ν (ofs y (o + offs m P)) (m ν) ++
    segZ μ (ofs y (o + offs m P) + m ν • unit n ν) (m μ))
  set HS := U.hol (stair y m S (o + offs m P + Pi.single μ (m μ) + Pi.single ν (m ν)))
  have e1 : U.hol (stair y m (P ++ μ :: ν :: S) o) = U.hol (stair y m P o) * (R1 * HS) := by
    rw [stair_append]
    simp only [R1, HS, stair, hol_append, ofs_add_single, mul_assoc]
  have e2 : U.hol (stair y m (P ++ ν :: μ :: S) o) = U.hol (stair y m P o) * (R2 * HS) := by
    rw [stair_append]
    simp only [R2, HS, stair, hol_append, ofs_add_single, mul_assoc]
    rw [show o + offs m P + Pi.single ν (m ν) + Pi.single μ (m μ) =
      o + offs m P + Pi.single μ (m μ) + Pi.single ν (m ν) by abel]
  rw [e1, e2, norm_sub_one_eq_of_eq (Y := U.hol (stair y m P o) * (R1 * R2⁻¹) *
    (U.hol (stair y m P o))⁻¹) (by group), norm_conj_sub_one' (hol_isU hU _)]
  exact hrect

/-! ### At most six exchanges: the paths of `𝐆(y, x)` -/

/-- One step of the bubble sort: the first descent is exchanged. -/
def bstep : List (Fin 4) → List (Fin 4)
  | a :: b :: l => if b < a then b :: a :: l else a :: bstep (b :: l)
  | l => l

lemma bstep_cases : ∀ l : List (Fin 4), bstep l = l ∨
    ∃ P S μ ν, μ ≠ ν ∧ l = P ++ μ :: ν :: S ∧ bstep l = P ++ ν :: μ :: S
  | [] => Or.inl rfl
  | [_] => Or.inl rfl
  | a :: b :: l => by
    by_cases h : b < a
    · exact Or.inr ⟨[], l, a, b, (ne_of_lt h).symm, rfl, by simp [bstep, h]⟩
    · rcases bstep_cases (b :: l) with h' | ⟨P, S, μ, ν, hne, hl, hb⟩
      · exact Or.inl (by simp [bstep, h, h'])
      · exact Or.inr ⟨a :: P, S, μ, ν, hne, by rw [hl]; rfl, by simp [bstep, h, hb]⟩

lemma bstep_perm : ∀ l : List (Fin 4), (bstep l).Perm l
  | [] => List.Perm.refl _
  | [_] => List.Perm.refl _
  | a :: b :: l => by
    by_cases h : b < a
    · simp only [bstep, h, ↓reduceIte]; exact List.Perm.swap a b l
    · simp only [bstep, h, ↓reduceIte]; exact (bstep_perm (b :: l)).cons a

lemma bstep_six_aux : ∀ a b c d : Fin 4, [a, b, c, d].Nodup → bstep^[6] [a, b, c, d] = [0, 1, 2, 3] := by
  decide

/-- Six steps of the bubble sort sort every ordering of the four coordinates. -/
lemma bstep_six (l : List (Fin 4)) (hl : l.Perm [0, 1, 2, 3]) : bstep^[6] l = [0, 1, 2, 3] := by
  have hlen := hl.length_eq
  have hnd : l.Nodup := hl.nodup_iff.2 (by decide)
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, l⟩⟩⟩⟩⟩ <;> simp at hlen
  exact bstep_six_aux a b c d hnd

lemma offs_nodup (m : Fin 4 → ℤ) : ∀ P : List (Fin 4), P.Nodup →
    ∀ σ, offs m P σ = if σ ∈ P then m σ else 0
  | [], _, σ => by simp [offs]
  | μ :: P, h, σ => by
    have hμ : μ ∉ P := (List.nodup_cons.1 h).1
    have ih := offs_nodup m P (List.nodup_cons.1 h).2 σ
    simp only [offs, List.map_cons, List.sum_cons, Pi.add_apply] at ih ⊢
    rw [ih]
    by_cases h1 : σ = μ
    · subst h1; simp [hμ]
    · simp [Pi.single_apply, h1]

lemma inBox_sel {lo hi m : Fin 4 → ℤ} (h0 : InBox lo hi 0) (hm : InBox lo hi m) (v : Fin 4 → ℤ)
    (hv : ∀ σ, v σ = 0 ∨ v σ = m σ) : InBox lo hi v := by
  intro σ
  rcases hv σ with h | h <;> rw [h]
  · exact h0 σ
  · exact hm σ

/-- The paths of `𝐆(y, x)` (one for every ordering `l` of the coordinates) differ from the axial path
`Γ_x` (the coordinates in increasing order) by at most `6h²β`, if the offsets `m` of `x` from `y` are at
most `h` and the plaquettes in a box which contains `0` and `m` are at most `β`. -/
theorem blockPaths_bound (hU : U.IsGaugeField) {y : Site n} {lo hi : Fin 4 → ℤ} {β : ℝ} (hβ : 0 ≤ β)
    (hP : PlaqBound U (boxR y lo hi) β) (m : Fin 4 → ℤ) (h0 : InBox lo hi 0) (hm : InBox lo hi m)
    {h : ℝ} (hh : ∀ σ, ((m σ).natAbs : ℝ) ≤ h) (l : List (Fin 4))
    (hl : l.Perm [0, 1, 2, 3]) :
    ‖((U.hol (stair y m l 0) * (U.hol (stair y m [0, 1, 2, 3] 0))⁻¹ : GLN) : Mat) - 1‖ ≤
      6 * h ^ 2 * β := by
  have hh0 : 0 ≤ h := (Nat.cast_nonneg _).trans (hh 0)
  have hnd : ([0, 1, 2, 3] : List (Fin 4)).Nodup := by decide
  -- one step of the bubble sort costs at most `h²β`
  have step : ∀ l' : List (Fin 4), l'.Perm [0, 1, 2, 3] →
      ‖((U.hol (stair y m l' 0) * (U.hol (stair y m (bstep l') 0))⁻¹ : GLN) : Mat) - 1‖ ≤
        h ^ 2 * β := by
    intro l' hl'
    rcases bstep_cases l' with e | ⟨P, S, μ, ν, hne, rfl, hb⟩
    · rw [e, mul_inv_cancel, Units.val_one, sub_self, norm_zero]; positivity
    · rw [hb]
      have hnd' : (P ++ μ :: ν :: S).Nodup := hl'.nodup_iff.2 hnd
      have hP' : P.Nodup := (List.nodup_append.1 hnd').1
      have hμP : μ ∉ P := fun h' => by
        have := (List.nodup_append.1 hnd').2.2; simp at this; exact (this μ h').1 rfl
      have hνP : ν ∉ P := fun h' => by
        have := (List.nodup_append.1 hnd').2.2; simp at this; exact (this ν h').2.1 rfl
      have hoffs := offs_nodup m P hP'
      have hsel : ∀ σ, (0 + offs m P) σ = 0 ∨ (0 + offs m P) σ = m σ := fun σ => by
        simp only [zero_add, hoffs]; split_ifs <;> simp
      have hsel1 : ∀ τ, τ ∉ P → ∀ σ, ((0 + offs m P + Pi.single τ (m τ) : Fin 4 → ℤ)) σ = 0 ∨
          ((0 + offs m P + Pi.single τ (m τ) : Fin 4 → ℤ)) σ = m σ := fun τ hτ σ => by
        simp only [zero_add, Pi.add_apply, hoffs]
        by_cases h1 : σ = τ
        · subst h1; simp [hτ]
        · simp only [Pi.single_eq_of_ne h1, add_zero]; split_ifs <;> simp
      refine (stair_swap hU hβ hP m P S hne 0 (inBox_sel h0 hm _ hsel)
        (inBox_sel h0 hm _ (hsel1 μ hμP)) (inBox_sel h0 hm _ (hsel1 ν hνP))).trans ?_
      rw [sq]
      have := mul_le_mul (hh μ) (hh ν) (Nat.cast_nonneg _) hh0
      nlinarith
  have hperm : ∀ k, (bstep^[k] l).Perm [0, 1, 2, 3] := by
    intro k
    induction k with
    | zero => exact hl
    | succ k ih => rw [Function.iterate_succ_apply']; exact (bstep_perm _).trans ih
  -- telescoping along the bubble sort
  have hk : ∀ k : ℕ, ‖((U.hol (stair y m l 0) * (U.hol (stair y m (bstep^[k] l) 0))⁻¹ : GLN) :
      Mat) - 1‖ ≤ k * (h ^ 2 * β) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      rw [norm_sub_one_eq_of_eq (Y := (U.hol (stair y m l 0) * (U.hol (stair y m (bstep^[k] l) 0))⁻¹) *
        (U.hol (stair y m (bstep^[k] l) 0) * (U.hol (stair y m (bstep (bstep^[k] l)) 0))⁻¹))
        (by group)]
      refine (norm_mul_sub_one_le ((hol_isU hU _).mul (hol_isU hU _).inv)).trans
        ((add_le_add ih (step _ (hperm k))).trans (le_of_eq ?_))
      push_cast; ring
  have := hk 6
  rw [bstep_six l hl] at this
  linarith

/-! ### Strips: a bond against the staircase paths to its two ends -/

lemma seg_succ_end (ρ : Fin 4) (s : Bool) : ∀ (k : ℕ) (z : Site n),
    seg ρ s z (k + 1) = seg ρ s z k ++ [⟨z + k • dvec ρ s, ρ, s⟩]
  | 0, z => by simp [seg]
  | k + 1, z => by
    have ih := seg_succ_end ρ s k (z + dvec ρ s)
    show (⟨z, ρ, s⟩ : Bond n) :: seg ρ s (z + dvec ρ s) (k + 1) =
      ((⟨z, ρ, s⟩ : Bond n) :: seg ρ s (z + dvec ρ s) k) ++ _
    rw [ih, List.cons_append, show z + dvec ρ s + k • dvec ρ s = z + (k + 1) • dvec ρ s by
      rw [succ_nsmul]; abel]

/-- Extending a signed segment by one bond in the positive direction. -/
lemma hol_segZ_succ (ρ : Fin 4) (q : Site n) (k : ℤ) :
    U.hol (segZ ρ q (k + 1)) = U.hol (segZ ρ q k) * U.val ⟨q + k • unit n ρ, ρ, true⟩ := by
  by_cases hk : 0 ≤ k
  · have e1 : segZ ρ q (k + 1) = seg ρ true q (k.toNat + 1) := by
      unfold segZ; simp only [show (0 : ℤ) ≤ k + 1 by omega, ↓reduceIte]; congr 1; omega
    have e2 : segZ ρ q k = seg ρ true q k.toNat := by
      unfold segZ; simp only [hk, ↓reduceIte]
    rw [e1, e2, seg_succ_end, hol_append, hol_cons, hol_nil, mul_one]
    congr 3
    rw [show dvec ρ true = (unit n ρ : Site n) by simp [dvec], ← natCast_zsmul,
      Int.toNat_of_nonneg hk]
  · have hm : (((-(k + 1)).toNat : ℕ) : ℤ) = -(k + 1) := Int.toNat_of_nonneg (by omega)
    have e1 : segZ ρ q (k + 1) = seg ρ false q (-(k + 1)).toNat := by
      unfold segZ
      by_cases h0 : 0 ≤ k + 1
      · have h1 : k + 1 = 0 := by omega
        rw [h1]; simp [seg]
      · simp only [h0, ↓reduceIte]
    have e2 : segZ ρ q k = seg ρ false q ((-(k + 1)).toNat + 1) := by
      unfold segZ; simp only [hk, ↓reduceIte]; congr 1; omega
    have e3 : U.val ⟨q + (-(k + 1)).toNat • dvec ρ false, ρ, false⟩ =
        (U.val ⟨q + k • unit n ρ, ρ, true⟩)⁻¹ := by
      simp only [Config.val, dvec, Bool.false_eq_true, ↓reduceIte]
      congr 2
      rw [smul_neg, ← natCast_zsmul, hm, neg_smul, neg_neg, add_smul, one_smul]
      abel
    rw [e1, e2, seg_succ_end, hol_append, hol_cons, hol_nil, mul_one, e3, inv_mul_cancel_right]

lemma chain_append : ∀ (γ δ : List (Bond n)) (z : Site n), Chain z γ → Chain (endpt z γ) δ →
    Chain z (γ ++ δ)
  | [], _, _, _, h => h
  | _ :: γ, δ, _, ⟨h1, h2⟩, h => ⟨h1, chain_append γ δ _ h2 h⟩

lemma endpt_append : ∀ (γ δ : List (Bond n)) (z : Site n), endpt z (γ ++ δ) = endpt (endpt z γ) δ
  | [], _, _ => rfl
  | b :: γ, δ, _ => endpt_append γ δ b.plus

lemma offs_append (m : Fin 4 → ℤ) (P l : List (Fin 4)) : offs m (P ++ l) = offs m P + offs m l := by
  simp [offs, List.sum_append]

lemma chain_endpt_stair (y : Site n) (m : Fin 4 → ℤ) : ∀ (l : List (Fin 4)) (o : Fin 4 → ℤ),
    Chain (ofs y o) (stair y m l o) ∧ endpt (ofs y o) (stair y m l o) = ofs y (o + offs m l)
  | [], o => ⟨by simp [stair, Chain], by simp [stair, offs, endpt]⟩
  | μ :: l, o => by
    obtain ⟨hc, he⟩ := chain_endpt_stair y m l (o + Pi.single μ (m μ))
    have hseg : endpt (ofs y o) (segZ μ (ofs y o) (m μ)) = ofs y (o + Pi.single μ (m μ)) := by
      rw [endpt_segZ, ofs_add_single]
    simp only [stair]
    refine ⟨chain_append _ _ _ (chain_segZ _ _ _) (by rw [hseg]; exact hc), ?_⟩
    rw [endpt_append, hseg, he]
    simp only [offs, List.map_cons, List.sum_cons, add_assoc]

lemma length_stair (y : Site n) (m : Fin 4 → ℤ) : ∀ (l : List (Fin 4)) (o : Fin 4 → ℤ),
    (stair y m l o).length = (l.map fun σ => (m σ).natAbs).sum
  | [], _ => rfl
  | μ :: l, o => by
    simp only [stair, List.length_append, length_segZ, length_stair y m l, List.map_cons,
      List.sum_cons]

lemma stair_congr (y : Site n) {m m' : Fin 4 → ℤ} : ∀ (l : List (Fin 4)) (o : Fin 4 → ℤ),
    (∀ σ ∈ l, m σ = m' σ) → stair y m l o = stair y m' l o
  | [], _, _ => rfl
  | μ :: l, o, h => by
    simp only [stair]
    rw [h μ (by simp), stair_congr y l _ (fun σ hσ => h σ (by simp [hσ]))]

lemma offs_congr {m m' : Fin 4 → ℤ} (l : List (Fin 4)) (h : ∀ σ ∈ l, m σ = m' σ) :
    offs m l = offs m' l := by
  unfold offs
  rw [List.map_congr_left (fun σ hσ => by rw [h σ hσ])]

lemma stair_shift (y : Site n) (m : Fin 4 → ℤ) (ρ : Fin 4) : ∀ (l : List (Fin 4)) (o : Fin 4 → ℤ),
    stair y m l (o + Pi.single ρ 1) = (stair y m l o).map (Bond.shift · (unit n ρ))
  | [], _ => rfl
  | μ :: l, o => by
    simp only [stair, List.map_append]
    rw [map_shift_segZ, ofs_add_single, one_smul,
      show o + Pi.single ρ 1 + Pi.single μ (m μ) = o + Pi.single μ (m μ) + Pi.single ρ 1 by abel]
    congr 1
    exact stair_shift y m ρ l _

/-- The offsets `v` of the points of a staircase path from `y + o`: unchanged off the list, between
`0` and `m_σ` from `o` on it. -/
def Partial (o m : Fin 4 → ℤ) (l : List (Fin 4)) (v : Fin 4 → ℤ) : Prop :=
  ∀ σ, (σ ∉ l → v σ = o σ) ∧ (σ ∈ l → Btw (v σ - o σ) (m σ))

lemma mem_stair (y : Site n) (m : Fin 4 → ℤ) : ∀ (l : List (Fin 4)) (o : Fin 4 → ℤ), l.Nodup →
    ∀ t ∈ stair y m l o, ∃ v v', Partial o m l v ∧ Partial o m l v' ∧ t.site = ofs y v ∧
      t.plus = ofs y v'
  | [], _, _, t, ht => by simp [stair] at ht
  | μ :: l, o, hnd, t, ht => by
    have hμ : μ ∉ l := (List.nodup_cons.1 hnd).1
    simp only [stair, List.mem_append] at ht
    rcases ht with ht | ht
    · rw [segZ_eq] at ht
      obtain ⟨i, hi, hs, hp⟩ := mem_seg_iff ht
      have key : ∀ i' : ℕ, i' ≤ (m μ).natAbs →
          Partial o m (μ :: l) (o + Pi.single μ (zi (sgn (m μ)) i')) := by
        intro i' hi' σ
        by_cases h : σ = μ
        · rw [h]
          refine ⟨fun h' => absurd (by simp) h', fun _ => ?_⟩
          simpa using btw_zi hi'
        · refine ⟨fun _ => by simp [Pi.single_eq_of_ne h], fun _ => ?_⟩
          simp only [Pi.add_apply, Pi.single_eq_of_ne h, add_zero, sub_self]
          unfold Btw; omega
      refine ⟨_, _, key i (by omega), key (i + 1) (by omega), ?_, ?_⟩
      · rw [hs, ofs_add_single, nsmul_dvec]
      · rw [hp, ofs_add_single, nsmul_dvec]
    · obtain ⟨v, v', hv, hv', hs, hp⟩ := mem_stair y m l _ (List.nodup_cons.1 hnd).2 t ht
      have lift : ∀ w, Partial (o + Pi.single μ (m μ)) m l w → Partial o m (μ :: l) w := by
        intro w hw σ
        obtain ⟨h1, h2⟩ := hw σ
        by_cases h : σ = μ
        · rw [h] at h1 h2 ⊢
          have h3 := h1 hμ
          simp only [Pi.add_apply, Pi.single_eq_same] at h3
          refine ⟨fun h' => absurd (by simp) h', fun _ => ?_⟩
          rw [h3]; unfold Btw; omega
        · simp only [Pi.add_apply, Pi.single_eq_of_ne h, add_zero] at h1 h2
          refine ⟨fun h' => h1 (fun h'' => h' (List.mem_cons_of_mem _ h'')), fun h' => ?_⟩
          rcases List.mem_cons.1 h' with h'' | h''
          · exact absurd h'' h
          · exact h2 h''
      exact ⟨v, v', lift v hv, lift v' hv', hs, hp⟩

/-- The points of the tail of a staircase after the coordinate `ρ` have offsets between `0` and `m`,
equal to `m_ρ` in the coordinate `ρ`. -/
lemma partial_tail {m : Fin 4 → ℤ} {P S : List (Fin 4)} {ρ : Fin 4} (hnd : (P ++ ρ :: S).Nodup)
    {v : Fin 4 → ℤ} (hv : Partial (0 + offs m P + Pi.single ρ (m ρ)) m S v) :
    ∀ σ, Btw (v σ) (m σ) ∧ (σ = ρ → v σ = m σ) := by
  have hdisj := (List.nodup_append.1 hnd).2.2
  have hρP : ρ ∉ P := fun h => hdisj ρ h ρ (by simp) rfl
  have hρS : ρ ∉ S := (List.nodup_cons.1 (List.nodup_append.1 hnd).2.1).1
  have hoffs := offs_nodup m P (List.nodup_append.1 hnd).1
  intro σ
  obtain ⟨h1, h2⟩ := hv σ
  simp only [Pi.add_apply, Pi.zero_apply, zero_add, hoffs] at h1 h2
  by_cases hσS : σ ∈ S
  · have hσP : σ ∉ P := fun h => hdisj σ h σ (by simp [hσS]) rfl
    have hσρ : σ ≠ ρ := fun h => hρS (h ▸ hσS)
    have h3 := h2 hσS
    simp only [hσP, ↓reduceIte, Pi.single_eq_of_ne hσρ, add_zero, sub_zero] at h3
    exact ⟨h3, fun h => absurd h hσρ⟩
  · have h3 := h1 hσS
    by_cases hσρ : σ = ρ
    · rw [hσρ] at h3 ⊢
      simp only [hρP, ↓reduceIte, Pi.single_eq_same, zero_add] at h3
      rw [h3]; exact ⟨by unfold Btw; omega, fun _ => rfl⟩
    · simp only [Pi.single_eq_of_ne hσρ, add_zero] at h3
      rw [h3]
      refine ⟨?_, fun h => absurd h hσρ⟩
      split_ifs <;> (unfold Btw; omega)

/-- `eq:axial-strip`: for the bond `b = (w, w + e_ρ)` with `w = y + Σ m_σ e_σ`, the staircase paths
`τ_w`, `τ_{w + e_ρ}` (same order of the coordinates) satisfy `‖U(τ_w)U(b)U(τ_{w+e_ρ})⁻¹ - id‖ ≤
(Σ_{σ after ρ} |m_σ|)β`, if the plaquettes in a box containing `0`, `m`, `m + e_ρ` are at most `β`. -/
theorem strip (hU : U.IsGaugeField) {y : Site n} {lo hi : Fin 4 → ℤ} {β : ℝ} (hβ : 0 ≤ β)
    (hP : PlaqBound U (boxR y lo hi) β) (m : Fin 4 → ℤ) (P S : List (Fin 4)) (ρ : Fin 4)
    (hnd : (P ++ ρ :: S).Nodup) (h0 : InBox lo hi 0) (hm : InBox lo hi m)
    (hm' : InBox lo hi (m + Pi.single ρ 1)) :
    ‖((U.hol (stair y m (P ++ ρ :: S) 0) * U.val ⟨ofs y (offs m (P ++ ρ :: S)), ρ, true⟩ *
      (U.hol (stair y (m + Pi.single ρ 1) (P ++ ρ :: S) 0))⁻¹ : GLN) : Mat) - 1‖ ≤
      (S.map fun σ => (m σ).natAbs).sum * β := by
  have hdisj := (List.nodup_append.1 hnd).2.2
  have hρP : ρ ∉ P := fun h => hdisj ρ h ρ (by simp) rfl
  have hρS : ρ ∉ S := (List.nodup_cons.1 (List.nodup_append.1 hnd).2.1).1
  have hSnd : S.Nodup := (List.nodup_cons.1 (List.nodup_append.1 hnd).2.1).2
  have hd : dvec ρ true = (unit n ρ : Site n) := by simp [dvec]
  have hag : ∀ σ, σ ≠ ρ → m σ = (m + Pi.single ρ 1 : Fin 4 → ℤ) σ := fun σ h => by
    simp [Pi.single_eq_of_ne h]
  have hagP : ∀ σ ∈ P, m σ = (m + Pi.single ρ 1 : Fin 4 → ℤ) σ := fun σ hσ => hag σ (fun h => hρP (h ▸ hσ))
  have hagS : ∀ σ ∈ S, m σ = (m + Pi.single ρ 1 : Fin 4 → ℤ) σ := fun σ hσ => hag σ (fun h => hρS (h ▸ hσ))
  have hmρ : (m + Pi.single ρ 1 : Fin 4 → ℤ) ρ = m ρ + 1 := by simp
  -- the two paths split at the coordinate `ρ`
  have e1 : U.hol (stair y m (P ++ ρ :: S) 0) = U.hol (stair y m P 0) *
      (U.hol (segZ ρ (ofs y (0 + offs m P)) (m ρ)) *
        U.hol (stair y m S (0 + offs m P + Pi.single ρ (m ρ)))) := by
    rw [stair_append]; simp only [stair, hol_append]
  have e2 : U.hol (stair y (m + Pi.single ρ 1) (P ++ ρ :: S) 0) = U.hol (stair y m P 0) *
      (U.hol (segZ ρ (ofs y (0 + offs m P)) (m ρ)) *
        U.val ⟨ofs y (0 + offs m P + Pi.single ρ (m ρ)), ρ, true⟩ *
        U.hol ((stair y m S (0 + offs m P + Pi.single ρ (m ρ))).map (Bond.shift · (unit n ρ)))) := by
    rw [stair_append, ← stair_congr y P 0 hagP, ← offs_congr P hagP]
    simp only [stair, hol_append]
    rw [hmρ, hol_segZ_succ, ← stair_congr y S _ hagS, Pi.single_add, ← add_assoc, stair_shift,
      ofs_add_single]
  have hb : ofs y (offs m (P ++ ρ :: S)) = ofs y (0 + offs m P + Pi.single ρ (m ρ) + offs m S) := by
    congr 1
    simp only [offs, List.map_append, List.map_cons, List.sum_append, List.sum_cons]
    abel
  -- the ladder along the tail
  have hlad : LadderIn (boxR y lo hi) (dvec ρ true)
      (stair y m S (0 + offs m P + Pi.single ρ (m ρ))) := by
    intro t ht
    obtain ⟨v, v', hv, hv', hs, hp⟩ := mem_stair y m S _ hSnd t ht
    have inb : ∀ w, Partial (0 + offs m P + Pi.single ρ (m ρ)) m S w →
        ofs y w ∈ boxR y lo hi ∧ ofs y w + dvec ρ true ∈ boxR y lo hi := by
      intro w hw
      have hbw := partial_tail hnd hw
      refine ⟨⟨w, fun σ => ?_, rfl⟩, ⟨w + Pi.single ρ 1, fun σ => ?_, by
        rw [ofs_add_single, one_smul, hd]⟩⟩
      · obtain ⟨a1, a2⟩ := h0 σ; obtain ⟨b1, b2⟩ := hm σ; obtain ⟨c1, c2⟩ := (hbw σ).1
        simp only [Pi.zero_apply] at a1 a2
        constructor <;> omega
      · by_cases h : σ = ρ
        · rw [h]
          have h3 := (hbw ρ).2 rfl
          obtain ⟨d1, d2⟩ := hm' ρ
          simp only [Pi.add_apply, Pi.single_eq_same] at d1 d2 ⊢
          constructor <;> omega
        · obtain ⟨a1, a2⟩ := h0 σ; obtain ⟨b1, b2⟩ := hm σ; obtain ⟨c1, c2⟩ := (hbw σ).1
          simp only [Pi.zero_apply] at a1 a2
          simp only [Pi.add_apply, Pi.single_eq_of_ne h, add_zero]
          constructor <;> omega
    obtain ⟨i1, i2⟩ := inb v hv
    obtain ⟨j1, j2⟩ := inb v' hv'
    rw [hs, hp]
    exact ⟨i1, j1, i2, j2⟩
  obtain ⟨hc, he⟩ := chain_endpt_stair y m S (0 + offs m P + Pi.single ρ (m ρ))
  have hL := ladder hU hβ hP ρ true _ _ hc hlad
  rw [hd, he, length_stair] at hL
  rw [e1, e2, hb, norm_sub_one_eq_of_eq (Y := (U.hol (stair y m P 0) *
      U.hol (segZ ρ (ofs y (0 + offs m P)) (m ρ))) *
    (U.val ⟨ofs y (0 + offs m P + Pi.single ρ (m ρ)), ρ, true⟩ *
      U.hol ((stair y m S (0 + offs m P + Pi.single ρ (m ρ))).map (Bond.shift · (unit n ρ))) *
      (U.hol (stair y m S (0 + offs m P + Pi.single ρ (m ρ))) *
        U.val ⟨ofs y (0 + offs m P + Pi.single ρ (m ρ) + offs m S), ρ, true⟩)⁻¹)⁻¹ *
    (U.hol (stair y m P 0) * U.hol (segZ ρ (ofs y (0 + offs m P)) (m ρ)))⁻¹) (by group),
    norm_conj_sub_one' ((hol_isU hU _).mul (hol_isU hU _)),
    norm_inv_sub_one' (((val_isU hU _).mul (hol_isU hU _)).mul
      ((hol_isU hU _).mul (val_isU hU _)).inv)]
  exact hL

/-! ### Moving a segment to the front: the operator `R_z` -/

lemma stair_cons (y : Site n) (m : Fin 4 → ℤ) (μ : Fin 4) (l : List (Fin 4)) (o : Fin 4 → ℤ) :
    stair y m (μ :: l) o = segZ μ (ofs y o) (m μ) ++ stair y m l (o + Pi.single μ (m μ)) := rfl

lemma ofs_ofs (y : Site n) (s v : Fin 4 → ℤ) : ofs (ofs y s) v = ofs y (s + v) := by
  unfold ofs
  funext σ
  simp [add_assoc]

lemma stair_base (y : Site n) (m : Fin 4 → ℤ) (s : Fin 4 → ℤ) : ∀ (l : List (Fin 4)) (o : Fin 4 → ℤ),
    stair (ofs y s) m l o = stair y m l (s + o)
  | [], _ => rfl
  | μ :: l, o => by
    rw [stair_cons, stair_cons, ofs_ofs, stair_base y m s l, add_assoc]

lemma segZ_zero (μ : Fin 4) (q : Site n) : segZ μ q 0 = [] := by simp [segZ, seg]

/-- The holonomy of a signed segment of length `a + b` is that of the segment of length `a` followed by
the one of length `b`, for all integers `a`, `b` (the bonds traversed back and forth cancel). -/
lemma hol_segZ_add (μ : Fin 4) (q : Site n) (a b : ℤ) :
    U.hol (segZ μ q (a + b)) = U.hol (segZ μ q a) * U.hol (segZ μ (q + a • unit n μ) b) := by
  induction b using Int.induction_on with
  | zero => simp [segZ_zero]
  | succ k ih =>
    rw [← add_assoc, hol_segZ_succ, hol_segZ_succ, ih, mul_assoc, add_smul, add_assoc]
  | pred k ih =>
    have h1 := hol_segZ_succ (U := U) μ q (a + (-(k : ℤ) - 1))
    have h2 := hol_segZ_succ (U := U) μ (q + a • unit n μ) (-(k : ℤ) - 1)
    rw [show a + (-(k : ℤ) - 1) + 1 = a + -(k : ℤ) by ring, ih] at h1
    rw [show -(k : ℤ) - 1 + 1 = -(k : ℤ) by ring] at h2
    rw [h2, show q + a • unit n μ + (-(k : ℤ) - 1) • unit n μ = q + (a + (-(k : ℤ) - 1)) • unit n μ by
      rw [add_smul, add_assoc]] at h1
    apply mul_right_cancel (b := U.val ⟨q + (a + (-(k : ℤ) - 1)) • unit n μ, μ, true⟩)
    rw [← h1, mul_assoc]

/-- Moving the coordinate `μ` from before the coordinates `Pre` to after them changes the holonomy of a
staircase by at most `|w_μ|(Σ_{σ ∈ Pre}|w_σ|)β`, if the plaquettes in a box containing `0` and `w` are at
most `β`. -/
theorem move_back (hU : U.IsGaugeField) {y : Site n} {lo hi : Fin 4 → ℤ} {β : ℝ} (hβ : 0 ≤ β)
    (hP : PlaqBound U (boxR y lo hi) β) (w : Fin 4 → ℤ) (μ : Fin 4) (h0 : InBox lo hi 0)
    (hw : InBox lo hi w) : ∀ (Pre Q S : List (Fin 4)), (Q ++ μ :: (Pre ++ S)).Nodup →
      ‖((U.hol (stair y w (Q ++ μ :: (Pre ++ S)) 0) * (U.hol (stair y w (Q ++ Pre ++ μ :: S) 0))⁻¹ :
        GLN) : Mat) - 1‖ ≤ (w μ).natAbs * (Pre.map fun σ => (w σ).natAbs).sum * β
  | [], Q, S, _ => by simp
  | p :: Pre, Q, S, hnd => by
    have hdisj := (List.nodup_append.1 hnd).2.2
    have hQ : Q.Nodup := (List.nodup_append.1 hnd).1
    have hμQ : μ ∉ Q := fun h => hdisj μ h μ (by simp) rfl
    have hpQ : p ∉ Q := fun h => hdisj p h p (by simp) rfl
    have hμp : μ ≠ p := fun h => (List.nodup_cons.1 (List.nodup_append.1 hnd).2.1).1 (by simp [h])
    have hoffs := offs_nodup w Q hQ
    have hsel : ∀ σ, (0 + offs w Q) σ = 0 ∨ (0 + offs w Q) σ = w σ := fun σ => by
      simp only [zero_add, hoffs]; split_ifs <;> simp
    have hsel1 : ∀ τ, τ ∉ Q → ∀ σ, ((0 + offs w Q + Pi.single τ (w τ) : Fin 4 → ℤ)) σ = 0 ∨
        ((0 + offs w Q + Pi.single τ (w τ) : Fin 4 → ℤ)) σ = w σ := fun τ hτ σ => by
      simp only [zero_add, Pi.add_apply, hoffs]
      by_cases h1 : σ = τ
      · subst h1; simp [hτ]
      · simp only [Pi.single_eq_of_ne h1, add_zero]; split_ifs <;> simp
    have hswap := stair_swap hU hβ hP w Q (Pre ++ S) hμp 0 (inBox_sel h0 hw _ hsel)
      (inBox_sel h0 hw _ (hsel1 μ hμQ)) (inBox_sel h0 hw _ (hsel1 p hpQ))
    have hnd' : (Q ++ [p] ++ μ :: (Pre ++ S)).Nodup := by
      rw [List.append_assoc, List.singleton_append]
      exact (List.Perm.append_left Q (List.Perm.swap μ p (Pre ++ S))).nodup_iff.2 hnd
    have ih := move_back hU hβ hP w μ h0 hw Pre (Q ++ [p]) S hnd'
    simp only [List.append_assoc, List.cons_append, List.singleton_append, List.nil_append] at ih ⊢
    rw [norm_sub_one_eq_of_eq (Y := (U.hol (stair y w (Q ++ μ :: p :: (Pre ++ S)) 0) *
      (U.hol (stair y w (Q ++ p :: μ :: (Pre ++ S)) 0))⁻¹) *
      (U.hol (stair y w (Q ++ p :: μ :: (Pre ++ S)) 0) *
      (U.hol (stair y w (Q ++ p :: (Pre ++ μ :: S)) 0))⁻¹)) (by group)]
    refine (norm_mul_sub_one_le ((hol_isU hU _).mul (hol_isU hU _).inv)).trans
      ((add_le_add hswap ih).trans (le_of_eq ?_))
    simp only [List.map_cons, List.sum_cons]
    push_cast; ring

/-- The operator `R_z` of `lem:axial-smallness`: the staircase path from `y` with the offsets
`n + L e_μ` and the path which first runs the segment of `L` bonds in the direction `e_μ` and then the
staircase from `y + L e_μ` with the offsets `n` (both in the order `Pre, μ, Post`) differ by at most
`|L|(Σ_{σ ∈ Pre}|n_σ|)β`, if the plaquettes in a box containing `0` and `n` with `n_μ` replaced by `L`
are at most `β`. -/
theorem front_segment (hU : U.IsGaugeField) {y : Site n} {lo hi : Fin 4 → ℤ} {β : ℝ} (hβ : 0 ≤ β)
    (hP : PlaqBound U (boxR y lo hi) β) (m : Fin 4 → ℤ) (Pre Post : List (Fin 4)) (μ : Fin 4)
    (hnd : (Pre ++ μ :: Post).Nodup) (L : ℤ) (h0 : InBox lo hi 0)
    (hw : InBox lo hi (Function.update m μ L)) :
    ‖((U.hol (stair y (m + Pi.single μ L) (Pre ++ μ :: Post) 0) *
      (U.hol (segZ μ y L) * U.hol (stair (ofs y (Pi.single μ L)) m (Pre ++ μ :: Post) 0))⁻¹ : GLN) :
        Mat) - 1‖ ≤ L.natAbs * (Pre.map fun σ => (m σ).natAbs).sum * β := by
  have hdisj := (List.nodup_append.1 hnd).2.2
  have hμPre : μ ∉ Pre := fun h => hdisj μ h μ (by simp) rfl
  have hμPost : μ ∉ Post := (List.nodup_cons.1 (List.nodup_append.1 hnd).2.1).1
  have hPre : (μ :: Pre).Nodup := List.nodup_cons.2 ⟨hμPre, (List.nodup_append.1 hnd).1⟩
  have hwμ : Function.update m μ L μ = L := by simp
  have hwPre : ∀ σ ∈ Pre, m σ = Function.update m μ L σ := fun σ hσ => by
    rw [Function.update_of_ne (by rintro rfl; exact hμPre hσ : σ ≠ μ)]
  have hmPre : ∀ σ ∈ Pre, (m + Pi.single μ L : Fin 4 → ℤ) σ = m σ := fun σ hσ => by
    simp [Pi.single_eq_of_ne (fun h => hμPre (h ▸ hσ) : σ ≠ μ)]
  have hmPost : ∀ σ ∈ Post, (m + Pi.single μ L : Fin 4 → ℤ) σ = m σ := fun σ hσ => by
    simp [Pi.single_eq_of_ne (fun h => hμPost (h ▸ hσ) : σ ≠ μ)]
  have hmμ : (m + Pi.single μ L : Fin 4 → ℤ) μ = L + m μ := by simp [add_comm]
  -- the cost of moving the segment
  have hmove := move_back hU hβ hP (Function.update m μ L) μ h0 hw Pre [] [] (by simpa using hPre)
  simp only [List.nil_append, List.append_nil] at hmove
  rw [hwμ, List.map_congr_left (fun σ hσ => by rw [← hwPre σ hσ])] at hmove
  -- the common tail
  have hT : U.hol (stair (ofs y (Pi.single μ L)) m (μ :: Post) (0 + offs m Pre)) =
      U.hol (segZ μ (ofs y (0 + offs m Pre) + L • unit n μ) (m μ)) *
        U.hol (stair y m Post (0 + offs m Pre + Pi.single μ (L + m μ))) := by
    rw [stair_cons, hol_append, ofs_ofs, stair_base, add_comm (Pi.single μ L : Fin 4 → ℤ) (0 + offs m Pre),
      ofs_add_single, show Pi.single μ L + (0 + offs m Pre + Pi.single μ (m μ)) =
        0 + offs m Pre + Pi.single μ (L + m μ) by rw [Pi.single_add]; abel]
  have hτ : U.hol (stair y (m + Pi.single μ L) (Pre ++ μ :: Post) 0) =
      U.hol (stair y (Function.update m μ L) Pre 0) * U.hol (segZ μ (ofs y (0 + offs m Pre)) L) *
        (U.hol (segZ μ (ofs y (0 + offs m Pre) + L • unit n μ) (m μ)) *
          U.hol (stair y m Post (0 + offs m Pre + Pi.single μ (L + m μ)))) := by
    rw [stair_append, hol_append, stair_congr y Pre 0 hmPre, stair_congr y Pre 0 hwPre,
      offs_congr Pre hmPre, stair_cons, hol_append, hmμ, hol_segZ_add, stair_congr y Post _ hmPost]
    group
  have hA : U.hol (stair y (Function.update m μ L) (Pre ++ [μ]) 0) =
      U.hol (stair y (Function.update m μ L) Pre 0) * U.hol (segZ μ (ofs y (0 + offs m Pre)) L) := by
    rw [stair_append, hol_append, ← offs_congr Pre hwPre, stair_cons, hwμ, hol_append]
    simp only [stair, hol_nil, mul_one]
  have hc : U.hol (segZ μ y L) * U.hol (stair (ofs y (Pi.single μ L)) m (Pre ++ μ :: Post) 0) =
      U.hol (stair y (Function.update m μ L) (μ :: Pre) 0) *
        U.hol (stair (ofs y (Pi.single μ L)) m (μ :: Post) (0 + offs m Pre)) := by
    have hs : stair y (Function.update m μ L) (μ :: Pre) 0 =
        segZ μ y L ++ stair (ofs y (Pi.single μ L)) m Pre 0 := by
      rw [stair_cons, hwμ, ofs_zero, stair_base, add_zero, zero_add, stair_congr y Pre _ hwPre]
    rw [stair_append, hol_append, hs, hol_append, mul_assoc]
  rw [hτ, hc, hT, norm_sub_one_eq_of_eq (Y := (U.hol (stair y (Function.update m μ L) (μ :: Pre) 0) *
      (U.hol (stair y (Function.update m μ L) Pre 0) *
        U.hol (segZ μ (ofs y (0 + offs m Pre)) L))⁻¹)⁻¹) (by group),
    norm_inv_sub_one' ((hol_isU hU _).mul ((hol_isU hU _).mul (hol_isU hU _)).inv), ← hA]
  exact hmove

/-! ### Any two orderings: at most six exchanges -/

lemma sum_natAbs_le (w : Fin 4 → ℤ) {h : ℝ} (hh : ∀ σ, ((w σ).natAbs : ℝ) ≤ h) :
    ∀ l : List (Fin 4), (((l.map fun σ => (w σ).natAbs).sum : ℕ) : ℝ) ≤ l.length * h
  | [] => by simp
  | σ :: l => by
    have := sum_natAbs_le w hh l
    rw [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_succ, add_mul, one_mul]
    linarith [hh σ]

/-- Two orderings `l`, `l'` of `k` distinct coordinates (after a common prefix `Q`) are related by
insertion: the first coordinate of `l'` is moved to the front, and so on. Each pair of coordinates is
exchanged at most once, so the holonomies differ by at most `(k(k-1)/2)h²β` if `|w_σ| ≤ h`. -/
theorem perm_bound (hU : U.IsGaugeField) {y : Site n} {lo hi : Fin 4 → ℤ} {β : ℝ} (hβ : 0 ≤ β)
    (hP : PlaqBound U (boxR y lo hi) β) (w : Fin 4 → ℤ) (h0 : InBox lo hi 0) (hw : InBox lo hi w)
    {h : ℝ} (hh : ∀ σ, ((w σ).natAbs : ℝ) ≤ h) :
    ∀ (l' l Q : List (Fin 4)), l.Perm l' → (Q ++ l).Nodup →
      ‖((U.hol (stair y w (Q ++ l) 0) * (U.hol (stair y w (Q ++ l') 0))⁻¹ : GLN) : Mat) - 1‖ ≤
        (l.length * (l.length - 1) / 2 : ℝ) * h ^ 2 * β
  | [], l, Q, hp, _ => by
    rw [List.perm_nil.1 hp]; simp
  | μ :: l', l, Q, hp, hnd => by
    have hh0 : 0 ≤ h := (Nat.cast_nonneg _).trans (hh 0)
    obtain ⟨Pre, Post, rfl⟩ := List.append_of_mem (hp.symm.subset (by simp) : μ ∈ l)
    have hnd2 : (Q ++ μ :: (Pre ++ Post)).Nodup :=
      (List.Perm.append_left Q List.perm_middle).nodup_iff.1 hnd
    have hmv := move_back hU hβ hP w μ h0 hw Pre Q Post hnd2
    simp only [List.append_assoc] at hmv
    have hp2 : (Pre ++ Post).Perm l' := (List.perm_middle.symm.trans hp).cons_inv
    have ih := perm_bound hU hβ hP w h0 hw hh l' (Pre ++ Post) (Q ++ [μ]) hp2
      (by simpa [List.append_assoc] using hnd2)
    simp only [List.append_assoc, List.singleton_append] at ih
    rw [norm_sub_one_eq_of_eq (Y := (U.hol (stair y w (Q ++ μ :: (Pre ++ Post)) 0) *
      (U.hol (stair y w (Q ++ (Pre ++ μ :: Post)) 0))⁻¹)⁻¹ *
      (U.hol (stair y w (Q ++ μ :: (Pre ++ Post)) 0) * (U.hol (stair y w (Q ++ μ :: l') 0))⁻¹))
      (by group)]
    refine (norm_mul_sub_one_le (((hol_isU hU _).mul (hol_isU hU _).inv).inv)).trans ?_
    rw [norm_inv_sub_one' ((hol_isU hU _).mul (hol_isU hU _).inv)]
    have hs := sum_natAbs_le w hh Pre
    have e1 : ((w μ).natAbs : ℝ) * (((Pre.map fun σ => (w σ).natAbs).sum : ℕ) : ℝ) * β ≤
        Pre.length * h ^ 2 * β := by
      have := mul_le_mul (hh μ) hs (Nat.cast_nonneg _) hh0
      have e : h * (Pre.length * h) = Pre.length * h ^ 2 := by ring
      rw [e] at this
      exact mul_le_mul_of_nonneg_right this hβ
    refine (add_le_add (hmv.trans e1) ih).trans ?_
    have hpos : 0 ≤ h ^ 2 * β := mul_nonneg (sq_nonneg h) hβ
    have hb : (0 : ℝ) ≤ Post.length := Nat.cast_nonneg _
    simp only [List.length_append, List.length_cons]
    push_cast
    nlinarith [mul_nonneg hb hpos]

/-- Two paths of `𝐆(y, x)` (`def:block-paths`(i)) differ by at most `6h²β`. -/
theorem paths_pair_bound (hU : U.IsGaugeField) {y : Site n} {lo hi : Fin 4 → ℤ} {β : ℝ} (hβ : 0 ≤ β)
    (hP : PlaqBound U (boxR y lo hi) β) (m : Fin 4 → ℤ) (h0 : InBox lo hi 0) (hm : InBox lo hi m)
    {h : ℝ} (hh : ∀ σ, ((m σ).natAbs : ℝ) ≤ h) (l l' : List (Fin 4)) (hl : l.Perm [0, 1, 2, 3])
    (hl' : l'.Perm [0, 1, 2, 3]) :
    ‖((U.hol (stair y m l 0) * (U.hol (stair y m l' 0))⁻¹ : GLN) : Mat) - 1‖ ≤ 6 * h ^ 2 * β := by
  have := perm_bound hU hβ hP m h0 hm hh l' l [] (hl.trans hl'.symm)
    (by simpa using hl.nodup_iff.2 (by decide))
  rw [List.nil_append, List.nil_append, hl.length_eq] at this
  have e : ((([0, 1, 2, 3] : List (Fin 4)).length : ℝ) * (([0, 1, 2, 3] : List (Fin 4)).length - 1) /
    2) = 6 := by norm_num
  rwa [e] at this

/-! ### The loops of a coarse bond: `lem:average`(v) -/

lemma plaqBound_mono {R R' : Set (Site n)} {β : ℝ} (hRR : R' ⊆ R) (hP : PlaqBound U R β) :
    PlaqBound U R' β :=
  fun μ ν x h ⟨h1, h2, h3, h4⟩ => hP μ ν x h ⟨hRR h1, hRR h2, hRR h3, hRR h4⟩

lemma boxR_shift_subset (y : Site n) (s lo hi : Fin 4 → ℤ) :
    boxR (ofs y s) (lo - s) (hi - s) ⊆ boxR y lo hi := by
  rintro p ⟨v, hv, rfl⟩
  refine ⟨s + v, fun σ => ?_, ofs_ofs y s v⟩
  obtain ⟨h1, h2⟩ := hv σ
  simp only [Pi.sub_apply, Pi.add_apply] at h1 h2 ⊢
  constructor <;> omega

lemma inBox_shift {lo hi s v : Fin 4 → ℤ} (h : InBox lo hi (s + v)) : InBox (lo - s) (hi - s) v := by
  intro σ
  obtain ⟨h1, h2⟩ := h σ
  simp only [Pi.sub_apply, Pi.add_apply] at h1 h2 ⊢
  constructor <;> omega

lemma stair_shift_nat (y : Site n) (m : Fin 4 → ℤ) (μ : Fin 4) (l : List (Fin 4)) (o : Fin 4 → ℤ) :
    ∀ k : ℕ, stair y m l (o + Pi.single μ (k : ℤ)) = (stair y m l o).map (Bond.shift · (k • unit n μ))
  | 0 => by simp [map_shift_zero]
  | k + 1 => by
    rw [show o + Pi.single μ (((k + 1 : ℕ)) : ℤ) = (o + Pi.single μ (k : ℤ)) + Pi.single μ 1 by
        push_cast; rw [Pi.single_add]; abel,
      stair_shift, stair_shift_nat y m μ l o k, map_shift_shift, succ_nsmul]

lemma offs_perm (m : Fin 4 → ℤ) {l : List (Fin 4)} (hl : l.Perm [0, 1, 2, 3]) : offs m l = m := by
  funext σ
  have hσ : σ ∈ l := hl.mem_iff.2 (by fin_cases σ <;> simp)
  rw [offs_nodup m l (hl.nodup_iff.2 (by decide))]
  simp only [hσ, ↓reduceIte]

/-- The loop bound of `lem:average`(v). For the coarse bond `c` from `c₋ = y` to `c₊ = y + Le_μ`, a
point `x = y + Σ m_σ e_σ` with `|m_σ| ≤ h`, `Γ ∈ 𝐆(c₋, x)` and `Γ' ∈ 𝐆(c₊, x')` (orderings `l`, `l'`),
the loop `ℓ_c(x, Γ, Γ') = Γ [x, x'] Γ'⁻¹ [c]⁻¹` satisfies `‖U(ℓ) - id‖ ≤ (4Lh + 6h²)β`, if the plaquettes
in a box containing `0`, `m`, `Le_μ`, and `Le_μ + m` are at most `β`. With `h = (L - 1)/2` this is at
most `4L²β`. -/
theorem loop_bound (hU : U.IsGaugeField) {y : Site n} {lo hi : Fin 4 → ℤ} {β : ℝ} (hβ : 0 ≤ β)
    (hP : PlaqBound U (boxR y lo hi) β) (μ : Fin 4) (L : ℕ) (m : Fin 4 → ℤ) {h : ℝ}
    (hh : ∀ σ, ((m σ).natAbs : ℝ) ≤ h) (h0 : InBox lo hi 0) (hm : InBox lo hi m)
    (hL : InBox lo hi (Pi.single μ (L : ℤ))) (hmL : InBox lo hi (Pi.single μ (L : ℤ) + m))
    (l l' : List (Fin 4)) (hl : l.Perm [0, 1, 2, 3]) (hl' : l'.Perm [0, 1, 2, 3]) :
    ‖((U.hol (stair y m l 0) * U.hol (segZ μ (ofs y m) L) *
        (U.hol (stair (ofs y (Pi.single μ (L : ℤ))) m l' 0))⁻¹ * (U.hol (segZ μ y L))⁻¹ : GLN) :
        Mat) - 1‖ ≤ (4 * L * h + 6 * h ^ 2) * β := by
  have hd : dvec μ true = (unit n μ : Site n) := by simp [dvec]
  have hnd : l.Nodup := hl.nodup_iff.2 (by decide)
  have hmem : ∀ σ, σ ∈ l := fun σ => hl.mem_iff.2 (by fin_cases σ <;> simp)
  have hseg : ∀ z : Site n, segZ μ z (L : ℤ) = seg μ true z L := fun z => by
    rw [segZ_eq]; simp [sgn]
  obtain ⟨hc, he⟩ := chain_endpt_stair y m l 0
  rw [ofs_zero] at hc
  rw [ofs_zero, zero_add, offs_perm m hl] at he
  -- the squares swept by the translation of `Γ` lie in the box
  have hR : ∀ j < L, LadderIn (boxR y lo hi) (dvec μ true)
      ((stair y m l 0).map (Bond.shift · (j • dvec μ true))) := by
    intro j hj t ht
    obtain ⟨t₀, ht₀, rfl⟩ := List.mem_map.1 ht
    obtain ⟨v, v', hv, hv', hs, hp⟩ := mem_stair y m l 0 hnd t₀ ht₀
    have inb : ∀ w, Partial 0 m l w → ∀ j' : ℕ, j' ≤ L →
        ofs y w + j' • dvec μ true ∈ boxR y lo hi := by
      intro w hw j' hj'
      refine ⟨w + Pi.single μ (j' : ℤ), fun σ => ?_, by rw [ofs_add_single, hd, natCast_zsmul]⟩
      have hb : Btw (w σ) (m σ) := by simpa using (hw σ).2 (hmem σ)
      obtain ⟨a1, a2⟩ := h0 σ
      obtain ⟨b1, b2⟩ := hm σ
      simp only [Pi.zero_apply] at a1 a2
      unfold Btw at hb
      by_cases hσ : σ = μ
      · rw [hσ] at hb a1 a2 b1 b2 ⊢
        obtain ⟨c1, c2⟩ := hL μ
        obtain ⟨d1, d2⟩ := hmL μ
        simp only [Pi.add_apply, Pi.single_eq_same] at c1 c2 d1 d2 ⊢
        constructor <;> omega
      · simp only [Pi.add_apply, Pi.single_eq_of_ne hσ, add_zero]
        constructor <;> omega
    simp only [Bond.shift_plus]
    refine ⟨?_, ?_, ?_, ?_⟩
    · show t₀.site + j • dvec μ true ∈ _
      rw [hs]; exact inb v hv j hj.le
    · rw [hp]; exact inb v' hv' j hj.le
    · show t₀.site + j • dvec μ true + dvec μ true ∈ _
      rw [hs, add_assoc, ← succ_nsmul]; exact inb v hv (j + 1) hj
    · rw [hp, add_assoc, ← succ_nsmul]; exact inb v' hv' (j + 1) hj
  -- the strip swept by `Γ`
  have hsh : (stair y m l 0).map (Bond.shift · (L • dvec μ true)) =
      stair (ofs y (Pi.single μ (L : ℤ))) m l 0 := by
    rw [stair_base, add_zero, hd, ← stair_shift_nat y m μ l 0 L, zero_add]
  have hlad := iterated_ladder hU hβ hP μ true L (stair y m l 0) y hc hR
  rw [hsh, he, ← hseg, ← hseg, length_stair] at hlad
  -- the two paths of `𝐆(c₊, x')`
  have hpair := paths_pair_bound hU hβ
    (plaqBound_mono (boxR_shift_subset y (Pi.single μ (L : ℤ)) lo hi) hP) m
    (inBox_shift (by simpa using hL)) (inBox_shift hmL) hh l l' hl hl'
  have hlen := sum_natAbs_le m hh l
  rw [hl.length_eq, show ((([0, 1, 2, 3] : List (Fin 4)).length : ℕ) : ℝ) = 4 by norm_num] at hlen
  rw [norm_sub_one_eq_of_eq (Y := (U.hol (segZ μ y L) *
      U.hol (stair (ofs y (Pi.single μ (L : ℤ))) m l 0) *
      (U.hol (stair y m l 0) * U.hol (segZ μ (ofs y m) L))⁻¹)⁻¹ *
    (U.hol (segZ μ y L) * (U.hol (stair (ofs y (Pi.single μ (L : ℤ))) m l 0) *
      (U.hol (stair (ofs y (Pi.single μ (L : ℤ))) m l' 0))⁻¹) * (U.hol (segZ μ y L))⁻¹)) (by group)]
  refine (norm_mul_sub_one_le ((((hol_isU hU _).mul (hol_isU hU _)).mul
    ((hol_isU hU _).mul (hol_isU hU _)).inv).inv)).trans ?_
  rw [norm_inv_sub_one' (((hol_isU hU _).mul (hol_isU hU _)).mul
      ((hol_isU hU _).mul (hol_isU hU _)).inv), norm_conj_sub_one' (hol_isU hU _)]
  have h1 : (L : ℝ) * (((l.map fun σ => (m σ).natAbs).sum : ℕ) : ℝ) * β ≤ L * (4 * h) * β :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlen (Nat.cast_nonneg _)) hβ
  nlinarith [hlad, hpair, h1]

end LatticePaths

end CoreLean

end
