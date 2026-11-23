/-
`lem:wide-class` of BALABAN_CORE.tex in the covering space.

The core takes a cube which is larger than the torus in the covering space, with the lifted domains and
fields. Here all the cubes of the wide class are taken there: points of `ℤ⁴` project to the fine lattice
(`proj`), a cube is a box `{c ≤ z < c + s}` of `ℤ⁴`, it is a union of cubes of the grid of side
`Ma_j = L^{j+m}` if `c_ν + h ≡ 0 mod L^{j+m}` (`h = (L^{j+m} - 1)/2`, the grid of the cells of scale
`j + m`) and `L^{j+m} ∣ s`, and its membership in the domains is that of its projection. The projection
does not increase `|·|_∞`, so the separation holds for the lifts.
-/
import CoreLean.WideClass

open Finset
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace CoreLean

namespace Blocks

variable {N : ℕ} [NeZero N]

/-- A point of the covering space `ℤ⁴`. -/
abbrev Zp := Fin 4 → ℤ

/-- The projection `ℤ⁴ → (ℤ/N)⁴`. -/
def proj (z : Zp) : Pt N := fun ν => (z ν : ZMod N)

/-- `|z - z'|_∞` in `ℤ⁴`. -/
def supZ (z z' : Zp) : ℕ := univ.sup fun ν => (z ν - z' ν).natAbs

lemma natAbs_le_supZ (z z' : Zp) (ν : Fin 4) : (z ν - z' ν).natAbs ≤ supZ z z' :=
  le_sup (f := fun ν => (z ν - z' ν).natAbs) (mem_univ ν)

lemma dinf_proj_le (z z' : Zp) : dinf (proj (N := N) z) (proj z') ≤ supZ z z' := by
  refine Finset.sup_le fun ν _ => ?_
  have : (proj (N := N) z) ν - (proj z') ν = ((z ν - z' ν : ℤ) : ZMod N) := by
    simp [proj]
  rw [this]
  exact (cd_intCast_le _).trans (natAbs_le_supZ z z' ν)

/-- The box `{c ≤ z < c + s}`. -/
def Box (c : Zp) (s : ℕ) : Set Zp := {z | ∀ ν, c ν ≤ z ν ∧ z ν < c ν + s}

lemma supZ_lt_of_box {c : Zp} {s : ℕ} {z z' : Zp} (hz : z ∈ Box c s) (hz' : z' ∈ Box c s)
    (hs : 0 < s) : supZ z z' < s := by
  unfold supZ
  rw [Finset.sup_lt_iff hs]
  intro ν _
  have h1 := hz ν
  have h2 := hz' ν
  omega

namespace DomSeq

variable (S : DomSeq N)

/-- A cube of the class (`hi = 20Ma_j`) or of the wide class (`hi = 20LMa_j`) of the index `j`, of the
block size `M = L^m`, in the covering space. -/
def LiftCube (m j hi : ℕ) (c : Zp) (s : ℕ) : Prop :=
  (∀ ν, (c ν + half S.L (j + m)) % (S.L ^ (j + m) : ℤ) = 0) ∧ S.L ^ (j + m) ∣ s ∧
    10 * S.L ^ m * S.L ^ j ≤ s ∧ s ≤ hi ∧
    (∀ z ∈ Box c s, proj z ∈ S.Ω j ∧ proj z ∉ S.Ω (j + 2)) ∧
    ∃ z ∈ Box c s, proj z ∈ S.Ω j ∧ proj z ∉ S.Ω (j + 1)

/-- The separation for lifts. -/
lemma sep_lift (j : ℕ) {z z' : Zp} (hz : proj z ∉ S.Ω j) (hz' : proj z' ∈ S.Ω (j + 1)) :
    S.RM * (S.L : ℝ) ^ j < supZ z z' := by
  have := S.sep' j _ hz _ hz'
  have h2 : (dinf (proj (N := N) z) (proj z') : ℝ) ≤ supZ z z' := by
    exact_mod_cast dinf_proj_le z z'
  linarith

/-- `lem:wide-class`(i) in the covering space, for the boxes of the grid of side `Ma_i` of side
`10Ma_i` which contain a point of the layer `i`: such a box is a cube of the wide class of the index `i`,
or `i ≥ 1` and it is one of the index `i - 1`. -/
theorem wide_class_lift {m : ℕ} (hRM : 21 * (S.L : ℝ) * (S.L : ℝ) ^ m ≤ S.RM) {i : ℕ}
    (hi : i ≤ S.k) {c : Zp} (hc : ∀ ν, (c ν + half S.L (i + m)) % (S.L ^ (i + m) : ℤ) = 0)
    {z₀ : Zp} (hz₀ : z₀ ∈ Box c (10 * S.L ^ m * S.L ^ i)) (hz₀i : proj z₀ ∈ S.Ω i)
    (hz₀i1 : proj z₀ ∉ S.Ω (i + 1)) :
    S.LiftCube m i (20 * S.L * S.L ^ m * S.L ^ i) c (10 * S.L ^ m * S.L ^ i) ∨
      (1 ≤ i ∧ S.LiftCube m (i - 1) (20 * S.L * S.L ^ m * S.L ^ (i - 1)) c
        (10 * S.L ^ m * S.L ^ i)) := by
  have hL := S.L_pos
  have hL3 : (3 : ℝ) ≤ S.L := by exact_mod_cast S.three_le_L
  have hLm : (0 : ℝ) < (S.L : ℝ) ^ m := pow_pos hL _
  have hLi : (0 : ℝ) < (S.L : ℝ) ^ i := pow_pos hL _
  set s := 10 * S.L ^ m * S.L ^ i
  have hspos : 0 < s := by have := S.three_le_L; positivity
  have hdiam : ∀ z ∈ Box c s, ∀ z' ∈ Box c s, (supZ z z' : ℝ) < 10 * (S.L : ℝ) ^ m * (S.L : ℝ) ^ i := by
    intro z hz z' hz'
    have := supZ_lt_of_box hz hz' hspos
    have : (supZ z z' : ℝ) < (s : ℝ) := by exact_mod_cast this
    simpa [s] using this
  have hdvd : S.L ^ (i + m) ∣ s := ⟨10, by simp only [s]; ring⟩
  by_cases hsub : ∀ z ∈ Box c s, proj z ∈ S.Ω i
  · left
    refine ⟨hc, hdvd, le_rfl, ?_, fun z hz => ⟨hsub z hz, fun hz2 => ?_⟩, z₀, hz₀, hz₀i, hz₀i1⟩
    · have := S.three_le_L
      calc s = 10 * S.L ^ m * S.L ^ i := rfl
        _ ≤ 20 * S.L * S.L ^ m * S.L ^ i := by
            have : 10 ≤ 20 * S.L := by omega
            calc 10 * S.L ^ m * S.L ^ i ≤ 20 * S.L * S.L ^ m * S.L ^ i := by gcongr
              _ = 20 * S.L * S.L ^ m * S.L ^ i := rfl
    · have hsep := S.sep_lift (i + 1) hz₀i1 hz2
      have hd := hdiam z₀ hz₀ z hz
      have : 10 * (S.L : ℝ) ^ m * (S.L : ℝ) ^ i ≤ S.RM * (S.L : ℝ) ^ (i + 1) := by
        rw [pow_succ]
        have h1 : 10 * (S.L : ℝ) ^ m * (S.L : ℝ) ^ i ≤ 21 * S.L * (S.L : ℝ) ^ m * ((S.L : ℝ) ^ i * S.L) := by
          have hP := mul_pos hLm hLi
          have h10 : (10 : ℝ) ≤ 21 * S.L * S.L := by nlinarith
          calc 10 * (S.L : ℝ) ^ m * (S.L : ℝ) ^ i = 10 * ((S.L : ℝ) ^ m * (S.L : ℝ) ^ i) := by ring
            _ ≤ (21 * S.L * S.L) * ((S.L : ℝ) ^ m * (S.L : ℝ) ^ i) :=
                mul_le_mul_of_nonneg_right h10 hP.le
            _ = 21 * S.L * (S.L : ℝ) ^ m * ((S.L : ℝ) ^ i * S.L) := by ring
        nlinarith [mul_le_mul_of_nonneg_right hRM (by positivity : (0 : ℝ) ≤ (S.L : ℝ) ^ i * S.L)]
      linarith
  · right
    push_neg at hsub
    obtain ⟨z₁, hz₁, hz₁i⟩ := hsub
    have hi1 : 1 ≤ i := by
      by_contra h
      have : i = 0 := by omega
      subst this
      exact hz₁i (by rw [S.Ω_zero]; trivial)
    have e : (S.L : ℝ) ^ i = S.L * (S.L : ℝ) ^ (i - 1) := by
      rw [← pow_succ']; congr 1; omega
    have hLi1 : (0 : ℝ) < (S.L : ℝ) ^ (i - 1) := pow_pos hL _
    have hin : ∀ z ∈ Box c s, proj z ∈ S.Ω (i - 1) := by
      intro z hz
      by_contra h'
      have hsep := S.sep_lift (i - 1) h' (by rwa [Nat.sub_add_cancel hi1])
      have hd := hdiam z hz z₀ hz₀
      rw [e] at hd
      nlinarith [mul_le_mul_of_nonneg_right hRM hLi1.le, mul_pos hLm hLi1]
    refine ⟨hi1, ?_, ?_, ?_, ?_, fun z hz => ⟨hin z hz, fun hz2 => ?_⟩, z₁, hz₁, hin z₁ hz₁, ?_⟩
    · intro ν
      have h1 := hc ν
      -- the grid of side `Ma_{i-1}` refines that of side `Ma_i`
      have hodd1 := two_half_add_one S.L_odd (i + m)
      have hodd2 := two_half_add_one S.L_odd (i - 1 + m)
      have hpow : S.L ^ (i + m) = S.L ^ (i - 1 + m) * S.L := by
        rw [← pow_succ]; congr 1; omega
      obtain ⟨l, hl⟩ := S.L_odd
      -- `h_{i+m} = L^{i-1+m} l + h_{i-1+m}`
      have hh : half S.L (i + m) = S.L ^ (i - 1 + m) * l + half S.L (i - 1 + m) := by
        generalize half S.L (i + m) = H at *
        generalize half S.L (i - 1 + m) = H' at *
        rw [hpow] at hodd1
        generalize S.L ^ (i - 1 + m) = A at *
        rw [hl] at hodd1
        nlinarith
      have hdv : (S.L ^ (i - 1 + m) : ℤ) ∣ c ν + half S.L (i + m) := by
        have := Int.dvd_of_emod_eq_zero h1
        exact (Int.natCast_dvd_natCast.mpr ⟨S.L, hpow⟩).trans this
      rw [hh] at hdv
      push_cast at hdv
      have : (S.L ^ (i - 1 + m) : ℤ) ∣ c ν + half S.L (i - 1 + m) := by
        have := dvd_sub hdv (dvd_mul_right (S.L ^ (i - 1 + m) : ℤ) (l : ℤ))
        simpa [add_comm, add_left_comm, add_assoc, sub_eq_add_neg] using this
      exact Int.emod_eq_zero_of_dvd this
    · rw [show i - 1 + m = i + m - 1 by omega]
      exact (pow_dvd_pow _ (by omega)).trans hdvd
    · calc 10 * S.L ^ m * S.L ^ (i - 1) ≤ 10 * S.L ^ m * S.L ^ i := by
            gcongr
            · have := S.three_le_L; omega
            · omega
        _ = s := rfl
    · calc s = 10 * S.L ^ m * S.L ^ i := rfl
        _ ≤ 20 * S.L ^ m * S.L ^ i := by gcongr; norm_num
        _ = 20 * S.L * S.L ^ m * S.L ^ (i - 1) := by
            rw [show i = i - 1 + 1 by omega, pow_succ]; simp only [Nat.add_sub_cancel]; ring
    · rw [show i - 1 + 2 = i + 1 by omega] at hz2
      have hsep := S.sep_lift i hz₁i hz2
      have hd := hdiam z₁ hz₁ z hz
      have : 10 * (S.L : ℝ) ^ m * (S.L : ℝ) ^ i ≤ S.RM * (S.L : ℝ) ^ i := by
        nlinarith [mul_le_mul_of_nonneg_right hRM hLi.le, mul_pos hLm hLi]
      linarith
    · rwa [Nat.sub_add_cancel hi1]

/-! ### The box of `10⁴` grid cubes around a point -/

/-- The corner of the box of `10⁴` cubes of the grid of side `G = L^g` around `z`: the cell of `z` is
the sixth in each direction. -/
def boxCorner (g : ℕ) (z : Zp) : Zp :=
  fun ν => (S.L ^ g : ℤ) * ((z ν + half S.L g) / (S.L ^ g : ℤ)) - half S.L g - 4 * (S.L ^ g : ℤ)

lemma boxCorner_aligned (g : ℕ) (z : Zp) (ν : Fin 4) :
    (S.boxCorner g z ν + half S.L g) % (S.L ^ g : ℤ) = 0 := by
  unfold boxCorner
  have : (S.L ^ g : ℤ) * ((z ν + half S.L g) / (S.L ^ g : ℤ)) - half S.L g - 4 * (S.L ^ g : ℤ) +
      half S.L g = (S.L ^ g : ℤ) * ((z ν + half S.L g) / (S.L ^ g : ℤ) - 4) := by ring
  rw [this, Int.mul_emod_right]

/-- The box contains the points within `4L^g` of `z`. -/
lemma mem_box_of_near {g : ℕ} (z w : Zp) {r : ℕ} (hr : r ≤ 4 * S.L ^ g)
    (hw : ∀ ν, (w ν - z ν).natAbs ≤ r) : w ∈ Box (S.boxCorner g z) (10 * S.L ^ g) := by
  have hodd := two_half_add_one S.L_odd g
  have hpos : (0 : ℤ) < (S.L ^ g : ℤ) := by have := S.three_le_L; positivity
  intro ν
  have hq := Int.mul_ediv_add_emod (z ν + half S.L g) (S.L ^ g : ℤ)
  have hr1 := Int.emod_nonneg (z ν + half S.L g) hpos.ne'
  have hr2 := Int.emod_lt_of_pos (z ν + half S.L g) hpos
  have hw' := hw ν
  have hoddZ : (2 * (half S.L g : ℤ) + 1 : ℤ) = (S.L : ℤ) ^ g := by exact_mod_cast hodd
  have hLg : ((S.L ^ g : ℕ) : ℤ) = (S.L : ℤ) ^ g := by push_cast; rfl
  have hrZ : (r : ℤ) ≤ 4 * (S.L : ℤ) ^ g := by exact_mod_cast hr
  unfold boxCorner
  push_cast at hq hr1 hr2 hpos ⊢
  generalize (z ν + half S.L g) / (S.L : ℤ) ^ g = q at *
  generalize (z ν + half S.L g) % (S.L : ℤ) ^ g = ρ at *
  generalize (S.L : ℤ) ^ g = G at *
  constructor <;> omega

/-! ### The regularity on the wide class -/

variable {K : ℕ}

local notation "Mat" => Matrix (Fin K) (Fin K) ℂ
local notation "GLN" => (Matrix (Fin K) (Fin K) ℂ)ˣ

/-- The unit vector `e_μ` of `ℤ⁴`. -/
def ez (μ : Fin 4) : Zp := Pi.single μ 1

lemma proj_add_ez (z : Zp) (μ : Fin 4) : proj (N := N) (z + ez μ) = proj z + unit N μ := by
  funext ν
  simp only [proj, Pi.add_apply, ez, unit, Pi.single_apply]
  split_ifs <;> push_cast <;> ring

/-- `(D_{id}A)_{νμ}(z) = ∂_νA_μ(z) - ∂_μA_ν(z)` (`def:differences`(ii), `η = 1`). -/
def DA (A : Fin 4 → Zp → Mat) (ν μ : Fin 4) (z : Zp) : Mat :=
  (A μ (z + ez ν) - A μ z) - (A ν (z + ez μ) - A ν z)

/-- `(D^*_{id}D_{id}A)_μ(z) = Σ_ν ((D_{id}A)_{νμ}(z - e_ν) - (D_{id}A)_{νμ}(z))` (`η = 1`). -/
def DsDA (A : Fin 4 → Zp → Mat) (μ : Fin 4) (z : Zp) : Mat :=
  ∑ ν, (DA A ν μ (z - ez ν) - DA A ν μ z)

/-- `U` is regular on the wide class of the block size `L^m` with the constant `α₀`
(`def:regular-pairs`(ii), first order), the cubes being taken in the covering space: on every cube of
the wide class there are a gauge transformation `u` with values in `G` and a `1`-form `A` with values in
`𝔤` with `U^u = e^{iA}` on its bonds, `‖A‖ ≤ (s/a_j)α₀a_j⁻¹` on its bonds, and
`‖A_ν(z + e_μ) - A_ν(z)‖ ≤ (s/a_j)α₀a_j⁻²` at its sites with the neighbours concerned in the cube.
The regularity is required for the cubes whose projection lies in a set `R` (the torus, or the set
`Ω_D^r` of `thm:propagators` for a Dirichlet domain). -/
def RegWide (G : GaugeGroup K) (m : ℕ) (U : Config K N) (α₀ : ℝ) (R : Set (Pt N))
    (two : Bool := false) : Prop :=
  ∀ j ≤ S.k, ∀ (c : Zp) (s : ℕ), S.LiftCube m j (20 * S.L * S.L ^ m * S.L ^ j) c s →
    (∀ z ∈ Box c s, proj z ∈ R) →
    ∃ (u : Zp → GLN) (A : Fin 4 → Zp → Mat),
      (∀ z ∈ Box c s, u z ∈ G.carrier) ∧
      (∀ μ z, z ∈ Box c s → z + ez μ ∈ Box c s →
        A μ z ∈ G.lie ∧ u z * U μ (proj z) * (u (z + ez μ))⁻¹ = expU (Complex.I • A μ z) ∧
          ‖A μ z‖ ≤ ((s : ℝ) / (S.L : ℝ) ^ j) * α₀ / (S.L : ℝ) ^ j) ∧
      (∀ μ ν z, z ∈ Box c s → z + ez μ ∈ Box c s → z + ez ν ∈ Box c s →
        z + ez μ + ez ν ∈ Box c s →
        ‖A ν (z + ez μ) - A ν z‖ ≤ ((s : ℝ) / (S.L : ℝ) ^ j) * α₀ / (S.L : ℝ) ^ (2 * j)) ∧
      (two = true → ∀ μ z, (∀ w, supZ w z ≤ 1 → w ∈ Box c s) →
        ‖DsDA A μ z‖ ≤ ((s : ℝ) / (S.L : ℝ) ^ j) * α₀ / (S.L : ℝ) ^ (3 * j))

/-- The gauge on the box around a point of the layer `i` (`eq:wide-cube`): with `i' = max{i - 1, 0}`,
`‖A‖ ≤ 10LMα₀/a_{i'}` and `‖∂A‖ ≤ 10LMα₀/a_{i'}²`. -/
theorem wide_cube {G : GaugeGroup K} {m : ℕ} (hRM : 21 * (S.L : ℝ) * (S.L : ℝ) ^ m ≤ S.RM)
    {U : Config K N} {α₀ : ℝ} (hα0 : 0 ≤ α₀) {R : Set (Pt N)} {two : Bool}
    (hreg : S.RegWide G m U α₀ R two) (z₀ : Zp)
    (hR : ∀ z ∈ Box (S.boxCorner (S.sc (proj z₀) + m) z₀) (10 * S.L ^ (S.sc (proj z₀) + m)),
      proj z ∈ R) :
    ∃ (u : Zp → GLN) (A : Fin 4 → Zp → Mat),
      (∀ z ∈ Box (S.boxCorner (S.sc (proj z₀) + m) z₀) (10 * S.L ^ (S.sc (proj z₀) + m)),
        u z ∈ G.carrier) ∧
      (∀ μ z, z ∈ Box (S.boxCorner (S.sc (proj z₀) + m) z₀) (10 * S.L ^ (S.sc (proj z₀) + m)) →
        z + ez μ ∈ Box (S.boxCorner (S.sc (proj z₀) + m) z₀) (10 * S.L ^ (S.sc (proj z₀) + m)) →
        A μ z ∈ G.lie ∧ u z * U μ (proj z) * (u (z + ez μ))⁻¹ = expU (Complex.I • A μ z) ∧
          ‖A μ z‖ ≤ 10 * S.L * (S.L : ℝ) ^ m * α₀ / (S.L : ℝ) ^ (S.sc (proj z₀) - 1)) ∧
      (∀ μ ν z, z ∈ Box (S.boxCorner (S.sc (proj z₀) + m) z₀) (10 * S.L ^ (S.sc (proj z₀) + m)) →
        z + ez μ ∈ Box (S.boxCorner (S.sc (proj z₀) + m) z₀) (10 * S.L ^ (S.sc (proj z₀) + m)) →
        z + ez ν ∈ Box (S.boxCorner (S.sc (proj z₀) + m) z₀) (10 * S.L ^ (S.sc (proj z₀) + m)) →
        z + ez μ + ez ν ∈ Box (S.boxCorner (S.sc (proj z₀) + m) z₀)
          (10 * S.L ^ (S.sc (proj z₀) + m)) →
        ‖A ν (z + ez μ) - A ν z‖ ≤
          10 * S.L * (S.L : ℝ) ^ m * α₀ / (S.L : ℝ) ^ (2 * (S.sc (proj z₀) - 1))) ∧
      (two = true → ∀ μ z, (∀ w, supZ w z ≤ 1 →
          w ∈ Box (S.boxCorner (S.sc (proj z₀) + m) z₀) (10 * S.L ^ (S.sc (proj z₀) + m))) →
        ‖DsDA A μ z‖ ≤ 10 * S.L * (S.L : ℝ) ^ m * α₀ / (S.L : ℝ) ^ (3 * (S.sc (proj z₀) - 1))) := by
  set i := S.sc (proj z₀)
  have hL := S.L_pos
  have hL1 : (1 : ℝ) ≤ S.L := by have := S.three_le_L; exact_mod_cast (by omega : 1 ≤ S.L)
  have hside : 10 * S.L ^ (i + m) = 10 * S.L ^ m * S.L ^ i := by rw [pow_add]; ring
  have hz₀ : z₀ ∈ Box (S.boxCorner (i + m) z₀) (10 * S.L ^ m * S.L ^ i) := by
    rw [← hside]
    exact S.mem_box_of_near z₀ z₀ (r := 0) (Nat.zero_le _) (fun ν => by simp)
  have hcls := S.wide_class_lift hRM (S.sc_le _) (fun ν => S.boxCorner_aligned (i + m) z₀ ν) hz₀
    (S.mem_sc _) (S.not_mem_sc_succ _)
  rw [hside]
  rw [hside] at hR
  rcases hcls with hc | ⟨hi1, hc⟩
  · -- a cube of the index `i`
    obtain ⟨u, A, hu, hA, hdA, hdd⟩ := hreg i (S.sc_le _) _ _ hc hR
    have hP : (0 : ℝ) ≤ 10 * (S.L : ℝ) ^ m * α₀ := by positivity
    have e1 : ((10 * S.L ^ m * S.L ^ i : ℕ) : ℝ) / (S.L : ℝ) ^ i * α₀ / (S.L : ℝ) ^ i =
        10 * (S.L : ℝ) ^ m * α₀ / (S.L : ℝ) ^ i := by
      push_cast; field_simp
    have e2 : ((10 * S.L ^ m * S.L ^ i : ℕ) : ℝ) / (S.L : ℝ) ^ i * α₀ / (S.L : ℝ) ^ (2 * i) =
        10 * (S.L : ℝ) ^ m * α₀ / (S.L : ℝ) ^ (2 * i) := by
      push_cast; field_simp
    have e3 : ((10 * S.L ^ m * S.L ^ i : ℕ) : ℝ) / (S.L : ℝ) ^ i * α₀ / (S.L : ℝ) ^ (3 * i) =
        10 * (S.L : ℝ) ^ m * α₀ / (S.L : ℝ) ^ (3 * i) := by
      push_cast; field_simp
    refine ⟨u, A, hu, fun μ z hz hz' => ?_, fun μ ν z h1 h2 h3 h4 => ?_, fun h2 μ z hz => ?_⟩
    rotate_left 2
    · have a3 := hdd h2 μ z hz
      rw [e3] at a3
      refine a3.trans ?_
      rw [div_le_div_iff₀ (pow_pos hL _) (pow_pos hL _)]
      have h : (S.L : ℝ) ^ (3 * (i - 1)) ≤ S.L * (S.L : ℝ) ^ (3 * i) := by
        rw [← pow_succ']; exact pow_le_pow_right₀ hL1 (by omega)
      calc 10 * (S.L : ℝ) ^ m * α₀ * (S.L : ℝ) ^ (3 * (i - 1))
          ≤ 10 * (S.L : ℝ) ^ m * α₀ * (S.L * (S.L : ℝ) ^ (3 * i)) := mul_le_mul_of_nonneg_left h hP
        _ = 10 * S.L * (S.L : ℝ) ^ m * α₀ * (S.L : ℝ) ^ (3 * i) := by ring
    · obtain ⟨a1, a2, a3⟩ := hA μ z hz hz'
      rw [e1] at a3
      refine ⟨a1, a2, a3.trans ?_⟩
      rw [div_le_div_iff₀ (pow_pos hL _) (pow_pos hL _)]
      have h : (S.L : ℝ) ^ (i - 1) ≤ S.L * (S.L : ℝ) ^ i := by
        rw [← pow_succ']; exact pow_le_pow_right₀ hL1 (by omega)
      calc 10 * (S.L : ℝ) ^ m * α₀ * (S.L : ℝ) ^ (i - 1)
          ≤ 10 * (S.L : ℝ) ^ m * α₀ * (S.L * (S.L : ℝ) ^ i) := mul_le_mul_of_nonneg_left h hP
        _ = 10 * S.L * (S.L : ℝ) ^ m * α₀ * (S.L : ℝ) ^ i := by ring
    · have a3 := hdA μ ν z h1 h2 h3 h4
      rw [e2] at a3
      refine a3.trans ?_
      rw [div_le_div_iff₀ (pow_pos hL _) (pow_pos hL _)]
      have h : (S.L : ℝ) ^ (2 * (i - 1)) ≤ S.L * (S.L : ℝ) ^ (2 * i) := by
        rw [← pow_succ']; exact pow_le_pow_right₀ hL1 (by omega)
      calc 10 * (S.L : ℝ) ^ m * α₀ * (S.L : ℝ) ^ (2 * (i - 1))
          ≤ 10 * (S.L : ℝ) ^ m * α₀ * (S.L * (S.L : ℝ) ^ (2 * i)) := mul_le_mul_of_nonneg_left h hP
        _ = 10 * S.L * (S.L : ℝ) ^ m * α₀ * (S.L : ℝ) ^ (2 * i) := by ring
  · -- a cube of the index `i - 1`
    obtain ⟨u, A, hu, hA, hdA, hdd⟩ :=
      hreg (i - 1) (by have := S.sc_le (proj z₀); omega) _ _ hc hR
    have e : ((10 * S.L ^ m * S.L ^ i : ℕ) : ℝ) / (S.L : ℝ) ^ (i - 1) = 10 * S.L * (S.L : ℝ) ^ m := by
      push_cast
      rw [show i = i - 1 + 1 by omega, pow_succ]
      simp only [Nat.add_sub_cancel]
      field_simp
    refine ⟨u, A, hu, fun μ z hz hz' => ?_, fun μ ν z h1 h2 h3 h4 => ?_, fun h2 μ z hz => ?_⟩
    · obtain ⟨a1, a2, a3⟩ := hA μ z hz hz'
      refine ⟨a1, a2, a3.trans (le_of_eq ?_)⟩
      rw [e]
    · refine (hdA μ ν z h1 h2 h3 h4).trans (le_of_eq ?_)
      rw [e]
    · refine (hdd h2 μ z hz).trans (le_of_eq ?_)
      rw [e]

/-- The box around a point of `Ω_D^+` lies in `Ω_D^r`: its points are within `10Ma_i ≤ 20Ma_i` of the
point, `i` its scale. -/
lemma box_in_R {R Dp : Set (Pt N)} {m : ℕ}
    (hD : ∀ y ∈ Dp, ∀ z, (dinf z y : ℝ) ≤ 20 * (S.L : ℝ) ^ m * (S.L : ℝ) ^ S.sc y → z ∈ R)
    {z₀ : Zp} (hz₀ : proj z₀ ∈ Dp) :
    ∀ z ∈ Box (S.boxCorner (S.sc (proj z₀) + m) z₀) (10 * S.L ^ (S.sc (proj z₀) + m)),
      proj z ∈ R := by
  intro z hz
  have h0 : z₀ ∈ Box (S.boxCorner (S.sc (proj z₀) + m) z₀) (10 * S.L ^ (S.sc (proj z₀) + m)) :=
    S.mem_box_of_near z₀ z₀ (r := 0) (Nat.zero_le _) (fun ν => by simp)
  have hpos : 0 < 10 * S.L ^ (S.sc (proj z₀) + m) := by have := S.three_le_L; positivity
  have h1 := supZ_lt_of_box hz h0 hpos
  have h2 := dinf_proj_le (N := N) z z₀
  refine hD _ hz₀ _ ?_
  have : dinf (proj (N := N) z) (proj z₀) ≤ 10 * S.L ^ (S.sc (proj z₀) + m) := by omega
  have h3 : (dinf (proj (N := N) z) (proj z₀) : ℝ) ≤ 10 * (S.L : ℝ) ^ m * (S.L : ℝ) ^ S.sc (proj z₀) := by
    rw [pow_add] at this
    have : (dinf (proj (N := N) z) (proj z₀) : ℝ) ≤ ((10 * (S.L ^ S.sc (proj z₀) * S.L ^ m) : ℕ) : ℝ) := by
      exact_mod_cast this
    push_cast at this
    linarith
  have hp : (0 : ℝ) ≤ (S.L : ℝ) ^ m * (S.L : ℝ) ^ S.sc (proj z₀) := by
    have := S.L_pos; positivity
  linarith

/-! ### The sites: `eq:wide-gauge` -/

/-- `lem:wide-class`(ii), the gauge at a site: for a site `x` (lifted to `xt`) of the layer `i`, on the
cube `|z - xt|_∞ ≤ 4a_i` there are a gauge transformation with values in `G` and a `1`-form `A` with
values in `𝔤` with `U^u = e^{iA}`, `a_{i'}‖A‖ ≤ 10LMα₀` and `a_{i'}²‖∂A‖ ≤ 10LMα₀`, `i' = max{i - 1, 0}`
(`eq:wide-gauge`). -/
theorem wide_gauge {G : GaugeGroup K} {m : ℕ} (hRM : 21 * (S.L : ℝ) * (S.L : ℝ) ^ m ≤ S.RM)
    {U : Config K N} {α₀ : ℝ} (hα0 : 0 ≤ α₀) {R Dp : Set (Pt N)} {two : Bool}
    (hreg : S.RegWide G m U α₀ R two)
    (hD : ∀ y ∈ Dp, ∀ z, (dinf z y : ℝ) ≤ 20 * (S.L : ℝ) ^ m * (S.L : ℝ) ^ S.sc y → z ∈ R)
    (x : Zp) (hx : proj x ∈ Dp) :
    ∃ (u : Zp → GLN) (A : Fin 4 → Zp → Mat),
      (∀ z, supZ z x ≤ 4 * S.L ^ S.sc (proj x) → u z ∈ G.carrier) ∧
      (∀ μ z, supZ z x ≤ 4 * S.L ^ S.sc (proj x) → supZ (z + ez μ) x ≤ 4 * S.L ^ S.sc (proj x) →
        A μ z ∈ G.lie ∧ u z * U μ (proj z) * (u (z + ez μ))⁻¹ = expU (Complex.I • A μ z) ∧
          (S.L : ℝ) ^ (S.sc (proj x) - 1) * ‖A μ z‖ ≤ 10 * S.L * (S.L : ℝ) ^ m * α₀) ∧
      (∀ μ ν z, supZ z x ≤ 4 * S.L ^ S.sc (proj x) → supZ (z + ez μ) x ≤ 4 * S.L ^ S.sc (proj x) →
        supZ (z + ez ν) x ≤ 4 * S.L ^ S.sc (proj x) →
        supZ (z + ez μ + ez ν) x ≤ 4 * S.L ^ S.sc (proj x) →
        ((S.L : ℝ) ^ (S.sc (proj x) - 1)) ^ 2 * ‖A ν (z + ez μ) - A ν z‖ ≤
          10 * S.L * (S.L : ℝ) ^ m * α₀) ∧
      (two = true → ∀ μ z, (∀ w, supZ w z ≤ 1 → supZ w x ≤ 4 * S.L ^ S.sc (proj x)) →
        ((S.L : ℝ) ^ (S.sc (proj x) - 1)) ^ 3 * ‖DsDA A μ z‖ ≤ 10 * S.L * (S.L : ℝ) ^ m * α₀) := by
  have hL := S.L_pos
  obtain ⟨u, A, hu, hA, hdA, hdd⟩ := S.wide_cube hRM hα0 hreg x (S.box_in_R hD hx)
  have hin : ∀ z, supZ z x ≤ 4 * S.L ^ S.sc (proj x) →
      z ∈ Box (S.boxCorner (S.sc (proj x) + m) x) (10 * S.L ^ (S.sc (proj x) + m)) := by
    intro z hz
    refine S.mem_box_of_near x z (r := 4 * S.L ^ S.sc (proj x)) ?_ fun ν => ?_
    · rw [pow_add]
      have : 1 ≤ S.L ^ m := Nat.one_le_pow _ _ (by have := S.three_le_L; omega)
      nlinarith
    · exact (natAbs_le_supZ z x ν).trans hz
  have hp : (0 : ℝ) < (S.L : ℝ) ^ (S.sc (proj x) - 1) := pow_pos hL _
  refine ⟨u, A, fun z hz => hu z (hin z hz), fun μ z hz hz' => ?_, fun μ ν z h1 h2 h3 h4 => ?_,
    fun htwo μ z hz => ?_⟩
  · obtain ⟨a1, a2, a3⟩ := hA μ z (hin z hz) (hin _ hz')
    refine ⟨a1, a2, ?_⟩
    rw [le_div_iff₀ hp] at a3
    linarith
  · have a3 := hdA μ ν z (hin z h1) (hin _ h2) (hin _ h3) (hin _ h4)
    rw [le_div_iff₀ (pow_pos hL _), pow_mul'] at a3
    linarith
  · have a3 := hdd htwo μ z (fun w hw => hin w (hz w hw))
    rw [le_div_iff₀ (pow_pos hL _), pow_mul'] at a3
    linarith

/-! ### The plaquettes: `eq:wide-plaquettes` -/

/-- `e^s - 1 - s ≤ s²` for `0 ≤ s ≤ 1/8`, in the form `φ₃(s) + s²/2 ≤ s²`. -/
lemma phi3_add_le {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ 1 / 8) : phi3 s + s ^ 2 / 2 ≤ s ^ 2 := by
  have h1 := phi3_le hs0
  have h2 : Real.exp s ≤ 2 := by
    have e : Real.exp s ≤ Real.exp (1 / 8) := Real.exp_le_exp.mpr hs
    have : Real.exp (1 / 8) < 2 := by
      have := Real.exp_one_lt_d9
      have e8 : Real.exp (1 / 8) ^ 8 = Real.exp 1 := by rw [← Real.exp_nat_mul]; norm_num
      by_contra h
      push_neg at h
      have : (2 : ℝ) ^ 8 ≤ Real.exp (1 / 8) ^ 8 := pow_le_pow_left₀ (by norm_num) h 8
      linarith
    linarith
  have : s ^ 3 * Real.exp s ≤ s ^ 2 / 2 := by
    have : s * Real.exp s ≤ 1 / 2 := by nlinarith
    nlinarith [sq_nonneg s]
  linarith

/-- `lem:wide-class`(ii), `eq:wide-plaquettes`: for a gauge field which is regular on the wide class
with `320LMα₀ ≤ 1`, every plaquette of `Ω_j` satisfies `|U(∂p) - 1| ≤ 30L³Mα₀(η/a_j)²`; the core's
bound, with the factor `√N`, follows. -/
theorem wide_plaquettes {G : GaugeGroup K} [NeZero K] {m : ℕ}
    (hRM : 21 * (S.L : ℝ) * (S.L : ℝ) ^ m ≤ S.RM) {U : Config K N} {α₀ : ℝ} (hα0 : 0 ≤ α₀)
    (hα : 320 * S.L * (S.L : ℝ) ^ m * α₀ ≤ 1) {R Dp : Set (Pt N)} {two : Bool}
    (hreg : S.RegWide G m U α₀ R two)
    (hD : ∀ y ∈ Dp, ∀ z, (dinf z y : ℝ) ≤ 20 * (S.L : ℝ) ^ m * (S.L : ℝ) ^ S.sc y → z ∈ R)
    {j : ℕ} (μ ν : Fin 4)
    {x : Pt N} (hp : x ∈ S.Ω j ∧ x + unit N μ ∈ S.Ω j ∧ x + unit N ν ∈ S.Ω j ∧
      x + unit N μ + unit N ν ∈ S.Ω j)
    (hpD : x ∈ Dp ∧ x + unit N μ ∈ Dp ∧ x + unit N ν ∈ Dp ∧ x + unit N μ + unit N ν ∈ Dp) :
    hs (((plaq U μ ν x : GLN) : Mat) - 1) ≤
      30 * S.L ^ 3 * (S.L : ℝ) ^ m * α₀ / ((S.L : ℝ) ^ j) ^ 2 := by
  have hL := S.L_pos
  have hL1 : (1 : ℝ) ≤ S.L := by have := S.three_le_L; exact_mod_cast (by omega : 1 ≤ S.L)
  -- the lifted corners
  set xt : Zp := fun κ => ((x κ).val : ℤ)
  have hxt : proj (N := N) xt = x := by funext κ; simp [proj, xt]
  have p1 : proj (N := N) (xt + ez μ) = x + unit N μ := by rw [proj_add_ez, hxt]
  have p2 : proj (N := N) (xt + ez ν) = x + unit N ν := by rw [proj_add_ez, hxt]
  have p3 : proj (N := N) (xt + ez μ + ez ν) = x + unit N μ + unit N ν := by
    rw [proj_add_ez, proj_add_ez, hxt]
  set C : Finset Zp := {xt, xt + ez μ, xt + ez ν, xt + ez μ + ez ν}
  -- a corner of the smallest scale
  obtain ⟨w, hw, -⟩ := Finset.exists_min_image C (fun w => S.sc (proj (N := N) w)) ⟨xt, by simp [C]⟩
  set i := S.sc (proj (N := N) w)
  have hji : j ≤ i := by
    simp only [C, mem_insert, mem_singleton] at hw
    rcases hw with rfl | rfl | rfl | rfl
    · exact (S.mem_iff _ _).mp (by rw [hxt]; exact hp.1)
    · exact (S.mem_iff _ _).mp (by rw [p1]; exact hp.2.1)
    · exact (S.mem_iff _ _).mp (by rw [p2]; exact hp.2.2.1)
    · exact (S.mem_iff _ _).mp (by rw [p3]; exact hp.2.2.2)
  -- the corners lie in the box around `w`
  have hc : ∀ c ∈ C, ∀ κ, 0 ≤ c κ - xt κ ∧ c κ - xt κ ≤ 2 := by
    intro c hc κ
    simp only [C, mem_insert, mem_singleton] at hc
    rcases hc with rfl | rfl | rfl | rfl
    · simp
    · simp only [ez, Pi.add_apply, Pi.single_apply, add_sub_cancel_left]; split_ifs <;> omega
    · simp only [ez, Pi.add_apply, Pi.single_apply, add_sub_cancel_left]; split_ifs <;> omega
    · simp only [ez, Pi.add_apply, Pi.single_apply]; split_ifs <;> omega
  have hwD : proj (N := N) w ∈ Dp := by
    simp only [C, mem_insert, mem_singleton] at hw
    rcases hw with rfl | rfl | rfl | rfl
    · rw [hxt]; exact hpD.1
    · rw [p1]; exact hpD.2.1
    · rw [p2]; exact hpD.2.2.1
    · rw [p3]; exact hpD.2.2.2
  obtain ⟨u, A, hu, hA, hdA, -⟩ := S.wide_cube hRM hα0 hreg w (S.box_in_R hD hwD)
  have hinbox : ∀ c ∈ C, c ∈ Box (S.boxCorner (i + m) w) (10 * S.L ^ (i + m)) := fun c hcC =>
    S.mem_box_of_near w c (r := 2) (by
      have : 1 ≤ S.L ^ (i + m) := Nat.one_le_pow _ _ (by have := S.three_le_L; omega)
      omega) (fun κ => by have h1 := hc c hcC κ; have h2 := hc w hw κ; omega)
  have b0 := hinbox xt (by simp [C])
  have b1 := hinbox (xt + ez μ) (by simp [C])
  have b2 := hinbox (xt + ez ν) (by simp [C])
  have b3 := hinbox (xt + ez μ + ez ν) (by simp [C])
  have e21 : xt + ez ν + ez μ = xt + ez μ + ez ν := by abel
  -- the gauge relations on the four bonds
  obtain ⟨-, g1, n1⟩ := hA μ xt b0 b1
  obtain ⟨-, g2, n2⟩ := hA ν (xt + ez μ) b1 b3
  obtain ⟨-, g3, n3⟩ := hA μ (xt + ez ν) b2 (by rw [e21]; exact b3)
  obtain ⟨-, g4, n4⟩ := hA ν xt b0 b2
  rw [hxt] at g1 g4
  rw [p1] at g2
  rw [p2, e21] at g3
  -- `U^u(∂p) = e^{iA₁} e^{iA₂'} e^{-iA₁'} e^{-iA₂}`
  have hP : u xt * plaq U μ ν x * (u xt)⁻¹ =
      expU (Complex.I • A μ xt) * expU (Complex.I • A ν (xt + ez μ)) *
        (expU (Complex.I • A μ (xt + ez ν)))⁻¹ * (expU (Complex.I • A ν xt))⁻¹ := by
    rw [← g1, ← g2, ← g3, ← g4, plaq_eq]
    group
  set P : Mat := ((u xt * plaq U μ ν x * (u xt)⁻¹ : GLN) : Mat)
  have hPexp : P = NormedSpace.exp (Complex.I • A μ xt) *
      NormedSpace.exp (Complex.I • A ν (xt + ez μ)) *
      NormedSpace.exp (Complex.I • -A μ (xt + ez ν)) * NormedSpace.exp (Complex.I • -A ν xt) := by
    simp only [P]
    rw [hP]
    simp only [Units.val_mul, expU_val, expU_inv_val, smul_neg]
  -- the truncation of the product
  obtain ⟨-, hQ, hR⟩ := (((trunc_exp (A μ xt)).mul (norm_nonneg _) (norm_nonneg _)
    (trunc_exp (A ν (xt + ez μ)))).mul (add_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)
    (trunc_exp (-A μ (xt + ez ν)))).mul
    (add_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)) (norm_nonneg _)
    (trunc_exp (-A ν xt))
  rw [← hPexp] at hR
  set s := ‖A μ xt‖ + ‖A ν (xt + ez μ)‖ + ‖-A μ (xt + ez ν)‖ + ‖-A ν xt‖
  set Sv := A μ xt + A ν (xt + ez μ) - A μ (xt + ez ν) - A ν xt
  -- the bounds of `A` and of its differences
  set B := 10 * S.L * (S.L : ℝ) ^ m * α₀
  have hp' : (0 : ℝ) < (S.L : ℝ) ^ (i - 1) := pow_pos hL _
  have hB0 : 0 ≤ B := by positivity
  have hBA : B / (S.L : ℝ) ^ (i - 1) ≤ 1 / 32 := by
    rw [div_le_iff₀ hp']
    have h1 : (1 : ℝ) ≤ (S.L : ℝ) ^ (i - 1) := one_le_pow₀ hL1
    have h2 : B ≤ 1 / 32 := by simp only [B]; linarith
    nlinarith
  have hs : s ≤ 4 * (B / (S.L : ℝ) ^ (i - 1)) := by
    simp only [s, norm_neg]; linarith
  have hs0 : 0 ≤ s := by positivity
  have hS : ‖Sv‖ ≤ 2 * (B / (S.L : ℝ) ^ (2 * (i - 1))) := by
    have d1 := hdA μ ν xt b0 b1 b2 b3
    have d2 := hdA ν μ xt b0 b2 b1 (by rw [e21]; exact b3)
    have e : Sv = (A ν (xt + ez μ) - A ν xt) - (A μ (xt + ez ν) - A μ xt) := by
      simp only [Sv]; abel
    rw [e]
    refine (norm_sub_le _ _).trans ?_
    linarith
  have hPm1 : ‖P - 1‖ ≤ ‖Sv‖ + s ^ 2 := by
    set Lp := Complex.I • A μ xt + Complex.I • A ν (xt + ez μ) + Complex.I • -A μ (xt + ez ν) +
      Complex.I • -A ν xt
    have hLp : Lp = Complex.I • Sv := by simp only [Lp, Sv, smul_add, smul_sub, smul_neg]; abel
    have key : ∀ Qm : Mat, ‖P - (1 + Lp + Qm)‖ ≤ phi3 s → ‖Qm‖ ≤ s ^ 2 / 2 →
        ‖P - 1‖ ≤ ‖Sv‖ + s ^ 2 := by
      intro Qm h1 h2
      have e : P - 1 = Lp + Qm + (P - (1 + Lp + Qm)) := by abel
      rw [e]
      refine (norm_add_le _ _).trans ?_
      refine (add_le_add (norm_add_le _ _) le_rfl).trans ?_
      have hnL : ‖Lp‖ = ‖Sv‖ := by rw [hLp, norm_I_smul]
      have := phi3_add_le hs0 (by linarith)
      linarith
    exact key _ hR hQ
  -- the plaquette
  have hu0 : ((u xt : GLN) : Mat) ∈ Matrix.unitaryGroup (Fin K) ℂ := G.unitary _ (hu xt b0)
  have hconj : ((plaq U μ ν x : GLN) : Mat) - 1 =
      (((u xt)⁻¹ : GLN) : Mat) * (P - 1) * ((u xt : GLN) : Mat) := by
    simp only [P, Units.val_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul]
    simp only [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
    rw [Matrix.mul_assoc _ (((u xt)⁻¹ : GLN) : Mat), Units.inv_mul, Matrix.mul_one]
  rw [hconj, hs_unitary_mul _ _ _ (SupportCont.unitary_inv hu0) hu0]
  refine (hs_le_opNorm (NeZero.pos K) _).trans (hPm1.trans ?_)
  -- the constants
  have hLi : (S.L : ℝ) ^ (2 * i) ≤ (S.L : ℝ) ^ 2 * (S.L : ℝ) ^ (2 * (i - 1)) := by
    rw [← pow_add]; exact pow_le_pow_right₀ hL1 (by omega)
  have hLj : ((S.L : ℝ) ^ j) ^ 2 ≤ (S.L : ℝ) ^ (2 * i) := by
    rw [← pow_mul, mul_comm]; exact pow_le_pow_right₀ hL1 (by omega)
  have hp2 : (0 : ℝ) < (S.L : ℝ) ^ (2 * (i - 1)) := pow_pos hL _
  have hpj : (0 : ℝ) < ((S.L : ℝ) ^ j) ^ 2 := by positivity
  have hsq : s ^ 2 ≤ 16 * B ^ 2 / (S.L : ℝ) ^ (2 * (i - 1)) := by
    have : s ^ 2 ≤ (4 * (B / (S.L : ℝ) ^ (i - 1))) ^ 2 := pow_le_pow_left₀ hs0 hs 2
    refine this.trans (le_of_eq ?_)
    rw [mul_pow, div_pow, ← pow_mul, mul_comm (i - 1) 2]; ring
  have hB2 : 16 * B ^ 2 ≤ B := by
    have : 16 * B ≤ 1 := by simp only [B]; linarith
    nlinarith
  calc ‖Sv‖ + s ^ 2 ≤ 2 * (B / (S.L : ℝ) ^ (2 * (i - 1))) + 16 * B ^ 2 / (S.L : ℝ) ^ (2 * (i - 1)) :=
        add_le_add hS hsq
    _ ≤ 3 * B / (S.L : ℝ) ^ (2 * (i - 1)) := by
        rw [show 2 * (B / (S.L : ℝ) ^ (2 * (i - 1))) + 16 * B ^ 2 / (S.L : ℝ) ^ (2 * (i - 1)) =
          (2 * B + 16 * B ^ 2) / (S.L : ℝ) ^ (2 * (i - 1)) by ring]
        exact div_le_div_of_nonneg_right (by linarith) hp2.le
    _ ≤ 3 * B * (S.L : ℝ) ^ 2 / (S.L : ℝ) ^ (2 * i) := by
        rw [div_le_div_iff₀ hp2 (pow_pos hL _)]
        nlinarith [mul_le_mul_of_nonneg_left hLi (by positivity : (0 : ℝ) ≤ 3 * B)]
    _ ≤ 3 * B * (S.L : ℝ) ^ 2 / ((S.L : ℝ) ^ j) ^ 2 :=
        div_le_div_of_nonneg_left (by positivity) hpj hLj
    _ = 30 * S.L ^ 3 * (S.L : ℝ) ^ m * α₀ / ((S.L : ℝ) ^ j) ^ 2 := by simp only [B]; ring

/-- `lem:wide-class`(ii) on the torus: `eq:wide-plaquettes` for every plaquette of `Ω_j`, for a gauge
field which is regular on the whole wide class. -/
theorem wide_plaquettes_torus {G : GaugeGroup K} [NeZero K] {m : ℕ}
    (hRM : 21 * (S.L : ℝ) * (S.L : ℝ) ^ m ≤ S.RM) {U : Config K N} {α₀ : ℝ} (hα0 : 0 ≤ α₀)
    (hα : 320 * S.L * (S.L : ℝ) ^ m * α₀ ≤ 1) (hreg : S.RegWide G m U α₀ Set.univ) {j : ℕ}
    (μ ν : Fin 4) {x : Pt N} (hp : x ∈ S.Ω j ∧ x + unit N μ ∈ S.Ω j ∧ x + unit N ν ∈ S.Ω j ∧
      x + unit N μ + unit N ν ∈ S.Ω j) :
    hs (((plaq U μ ν x : GLN) : Mat) - 1) ≤
      30 * S.L ^ 3 * (S.L : ℝ) ^ m * α₀ / ((S.L : ℝ) ^ j) ^ 2 :=
  S.wide_plaquettes hRM hα0 hα (Dp := Set.univ) hreg (fun _ _ _ _ => trivial) μ ν hp
    ⟨trivial, trivial, trivial, trivial⟩

end DomSeq

end Blocks

end CoreLean
