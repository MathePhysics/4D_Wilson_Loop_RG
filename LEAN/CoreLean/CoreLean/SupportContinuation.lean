/-
`lem:support-continuation` of BALABAN_CORE.tex: the continuation of a field beyond a support.

Model. Fine lattice `Site n`, spacing `a = η`. The support `W`, the set `𝒩`, and `Ω₁` are sets of
sites; the bonds and the plaquettes of a set are those with all ends and all corners in it. The defining
property of a support used by the proof is that a site outside `W` is at an `ℓ^∞`-distance of more
than `M₁` (fine units) from `Ω₁`; the proof uses `M₁ ≥ 2` (the corners of the plaquettes of a bond lie
within `2η` of each other), and the core's support has `M₁ ≥ L² ≥ 9`. The continuation `Ũ` equals `U`
on the bonds of `W` and `V` on the others. Of `U ∈ 𝔘_W(α)` the proof uses the plaquette bound of the
layer `0`, `|U(∂p) - 1| ≤ α` for the plaquettes of `W` (`eq:plaquette-regular` with `j = 0`).

The conclusion is the one the proof establishes, from which `eq:base-setting` with the constant
`6N(α + 4α')` is read off: on the plaquettes of `W` the field `Ũ` is `U`; a plaquette of `𝒩` which is
not one of `W` has no corner in `Ω₁` (it lies in the layer `0`) and `|Ũ(∂p) - 1| ≤ α + 4α'`; at a bond
of `𝒩` all of whose plaquettes are plaquettes of `𝒩` the current of `Ũ` is that of `U` if the six
plaquettes are plaquettes of `W`, and otherwise none of them has a corner in `Ω₁` (the bond lies in the
layer `0`) and `‖J(Ũ)(b)‖ ≤ 6N(α + 4α')η⁻³`.
-/
import CoreLean.BlockPartition
import CoreLean.HessianBound

open scoped Matrix.Norms.L2Operator Classical
open Matrix Finset

noncomputable section

namespace CoreLean

namespace SupportCont

variable {N n : ℕ} [NeZero n]

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "GLN" => (Matrix (Fin N) (Fin N) ℂ)ˣ

/-! ### Unitary matrices -/

lemma hs_neg (X : Mat) : hs (-X) = hs X := by
  unfold hs hs2; simp [Matrix.conjTranspose_neg]

lemma hs_sub_comm (X Y : Mat) : hs (X - Y) = hs (Y - X) := by rw [← neg_sub, hs_neg]

lemma unitary_inv {W : GLN} (h : (W : Mat) ∈ unitaryGroup (Fin N) ℂ) :
    ((W⁻¹ : GLN) : Mat) ∈ unitaryGroup (Fin N) ℂ :=
  mem_unitaryUnits.mp (inv_mem_unitaryUnits (mem_unitaryUnits.mpr h))

lemma unitary_mul {W W' : GLN} (h : (W : Mat) ∈ unitaryGroup (Fin N) ℂ)
    (h' : (W' : Mat) ∈ unitaryGroup (Fin N) ℂ) : ((W * W' : GLN) : Mat) ∈ unitaryGroup (Fin N) ℂ := by
  rw [Units.val_mul]; exact Submonoid.mul_mem _ h h'

/-- `|W₁W₂ - W₁'W₂'| ≤ |W₁ - W₁'| + |W₂ - W₂'|` for unitary `W₂`, `W₁'`. -/
lemma hs_mul_sub_mul_le {W₁ W₂ W₁' W₂' : Mat} (h₂ : W₂ ∈ unitaryGroup (Fin N) ℂ)
    (h₁' : W₁' ∈ unitaryGroup (Fin N) ℂ) :
    hs (W₁ * W₂ - W₁' * W₂') ≤ hs (W₁ - W₁') + hs (W₂ - W₂') := by
  have e : W₁ * W₂ - W₁' * W₂' = (W₁ - W₁') * W₂ + W₁' * (W₂ - W₂') := by noncomm_ring
  rw [e]
  refine (hs_add_le _ _).trans (add_le_add (le_of_eq ?_) (le_of_eq ?_))
  · have := hs_unitary_mul 1 W₂ (W₁ - W₁') (Submonoid.one_mem _) h₂
    rwa [Matrix.one_mul] at this
  · have := hs_unitary_mul W₁' 1 (W₂ - W₂') h₁' (Submonoid.one_mem _)
    rwa [Matrix.mul_one] at this

/-- `|W⁻¹ - W'⁻¹| = |W - W'|` for unitary `W`, `W'`. -/
lemma hs_inv_sub_inv {W W' : GLN} (h : (W : Mat) ∈ unitaryGroup (Fin N) ℂ)
    (h' : (W' : Mat) ∈ unitaryGroup (Fin N) ℂ) :
    hs (((W⁻¹ : GLN) : Mat) - ((W'⁻¹ : GLN) : Mat)) = hs ((W : Mat) - (W' : Mat)) := by
  have e : ((W'⁻¹ : GLN) : Mat) - ((W⁻¹ : GLN) : Mat) =
      ((W⁻¹ : GLN) : Mat) * ((W : Mat) - (W' : Mat)) * ((W'⁻¹ : GLN) : Mat) := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Units.inv_mul, Matrix.one_mul, Matrix.mul_assoc,
      Units.mul_inv, Matrix.mul_one]
  rw [hs_sub_comm, e, hs_unitary_mul _ _ _ (unitary_inv h) (unitary_inv h')]

/-- `|Ũ(∂p) - V(∂p)| ≤ Σ_b |Ũ(b) - V(b)|` for the plaquette of unitary bonds. -/
lemma hs_plaq_sub_le (U V : Config N n) (μ ν : Fin 4) (x : Site n)
    (hU : ∀ W ∈ [U μ x, U ν (x + unit n μ), U μ (x + unit n ν), U ν x],
      ((W : GLN) : Mat) ∈ unitaryGroup (Fin N) ℂ)
    (hV : ∀ W ∈ [V μ x, V ν (x + unit n μ), V μ (x + unit n ν), V ν x],
      ((W : GLN) : Mat) ∈ unitaryGroup (Fin N) ℂ) :
    hs (((plaq U μ ν x : GLN) : Mat) - ((plaq V μ ν x : GLN) : Mat)) ≤
      hs (((U μ x : GLN) : Mat) - ((V μ x : GLN) : Mat)) +
        hs (((U ν (x + unit n μ) : GLN) : Mat) - ((V ν (x + unit n μ) : GLN) : Mat)) +
        hs (((U μ (x + unit n ν) : GLN) : Mat) - ((V μ (x + unit n ν) : GLN) : Mat)) +
        hs (((U ν x : GLN) : Mat) - ((V ν x : GLN) : Mat)) := by
  have u1 := hU (U μ x) (by simp); have u2 := hU (U ν (x + unit n μ)) (by simp)
  have u3 := hU (U μ (x + unit n ν)) (by simp); have u4 := hU (U ν x) (by simp)
  have v1 := hV (V μ x) (by simp); have v2 := hV (V ν (x + unit n μ)) (by simp)
  have v3 := hV (V μ (x + unit n ν)) (by simp); have v4 := hV (V ν x) (by simp)
  rw [plaq_eq, plaq_eq]
  simp only [Units.val_mul]
  -- peel off the factors from the right
  refine (hs_mul_sub_mul_le (unitary_inv u4) (unitary_mul (unitary_mul v1 v2)
    (unitary_inv v3))).trans ?_
  rw [hs_inv_sub_inv u4 v4]
  gcongr
  refine (hs_mul_sub_mul_le (unitary_inv u3) (unitary_mul v1 v2)).trans ?_
  rw [hs_inv_sub_inv u3 v3]
  gcongr
  exact hs_mul_sub_mul_le u2 v1

/-! ### The current from six plaquettes -/

variable (a : ℂ) {G : GaugeGroup N}

/-- `‖Im W‖ ≤ ‖W - 1‖` for unitary `W`. -/
lemma opNorm_imW_le {W : GLN} (hW : (W : Mat) ∈ unitaryGroup (Fin N) ℂ) :
    ‖imW W‖ ≤ ‖(W : Mat) - 1‖ := by
  have hinv : ‖(1 : Mat) - ((W⁻¹ : GLN) : Mat)‖ = ‖(W : Mat) - 1‖ := by
    have e : (1 : Mat) - ((W⁻¹ : GLN) : Mat) = ((W⁻¹ : GLN) : Mat) * ((W : Mat) - 1) * 1 := by
      rw [Matrix.mul_one, Matrix.mul_sub, Units.inv_mul, Matrix.mul_one]
    rw [e, opNorm_unitary_mul _ _ _ (unitary_inv hW) (Submonoid.one_mem _)]
  unfold imW
  rw [norm_smul]
  have h2 : ‖(1 / (2 * Complex.I) : ℂ)‖ = 1 / 2 := by
    rw [norm_div, norm_one, norm_mul, Complex.norm_I, mul_one, Complex.norm_two]
  rw [h2]
  have e : (W : Mat) - ((W⁻¹ : GLN) : Mat) = ((W : Mat) - 1) + (1 - ((W⁻¹ : GLN) : Mat)) := by abel
  rw [e]
  have := norm_add_le ((W : Mat) - 1) (1 - ((W⁻¹ : GLN) : Mat))
  rw [hinv] at this
  linarith [norm_nonneg ((W : Mat) - 1)]

/-- `‖F(U)(p)‖ ≤ N a⁻²|U(∂p) - 1|` (`lem:norms`(i), (iv)). -/
lemma opNorm_curv_le [NeZero N] (hG : G.LieInput) (U : Config N n) (μ ν : Fin 4) (x : Site n)
    (hp : ((plaq U μ ν x : GLN) : Mat) ∈ unitaryGroup (Fin N) ℂ) :
    ‖curv a hG U μ ν x‖ ≤ (‖a‖ ^ 2)⁻¹ * (N * hs ((plaq U μ ν x : Mat) - 1)) := by
  unfold curv
  rw [norm_smul, norm_inv, norm_pow]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hN : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt (Nat.cast_nonneg N)
  calc ‖piProj hG (imW (plaq U μ ν x))‖ ≤ Real.sqrt N * ‖imW (plaq U μ ν x)‖ := opNorm_proj_le hG _
    _ ≤ Real.sqrt N * ‖(plaq U μ ν x : Mat) - 1‖ :=
        mul_le_mul_of_nonneg_left (opNorm_imW_le hp) (Real.sqrt_nonneg _)
    _ ≤ Real.sqrt N * (Real.sqrt N * hs ((plaq U μ ν x : Mat) - 1)) :=
        mul_le_mul_of_nonneg_left (opNorm_le_sqrt_mul_hs _) (Real.sqrt_nonneg _)
    _ = N * hs ((plaq U μ ν x : Mat) - 1) := by rw [← mul_assoc, hN]

lemma opNorm_Ad_unitary {W : GLN} (hW : (W : Mat) ∈ unitaryGroup (Fin N) ℂ) (X : Mat) :
    ‖Ad W X‖ = ‖X‖ := opNorm_unitary_mul _ _ _ hW (unitary_inv hW)

/-- The six plaquettes of the bond `(x, x + e_μ)`: `p_{νμ}(x)` and `p_{νμ}(x - e_ν)`, `ν ≠ μ`. -/
def Six (P : Fin 4 → Fin 4 → Site n → Prop) (μ : Fin 4) (x : Site n) : Prop :=
  ∀ ν, ν ≠ μ → P ν μ x ∧ P ν μ (x - unit n ν)

/-- `‖J(U)(b)‖ ≤ 6Nε|a|⁻³` if the six plaquettes of `b` satisfy `|U(∂p) - 1| ≤ ε`. -/
theorem opNorm_current_le [NeZero N] (hG : G.LieInput) (U : Config N n) (μ : Fin 4) (x : Site n)
    {ε : ℝ} (hunit : ∀ ν, ν ≠ μ → ((U ν (x - unit n ν) : GLN) : Mat) ∈ unitaryGroup (Fin N) ℂ)
    (hpu : Six (fun ν μ y => ((plaq U ν μ y : GLN) : Mat) ∈ unitaryGroup (Fin N) ℂ) μ x)
    (hpl : Six (fun ν μ y => hs ((plaq U ν μ y : Mat) - 1) ≤ ε) μ x) :
    ‖current a hG U μ x‖ ≤ 6 * N * ε / ‖a‖ ^ 3 := by
  have hε : 0 ≤ ε := by
    obtain ⟨ν, hν⟩ : ∃ ν : Fin 4, ν ≠ μ := by
      by_cases h : μ = 0
      · exact ⟨1, by rw [h]; decide⟩
      · exact ⟨0, fun e => h e.symm⟩
    exact (hs_nonneg _).trans (hpl ν hν).1
  set C : ℝ := (‖a‖ ^ 2)⁻¹ * (N * ε)
  have hF : ∀ ν, ν ≠ μ → ‖curv a hG U ν μ x‖ ≤ C ∧ ‖curv a hG U ν μ (x - unit n ν)‖ ≤ C := by
    intro ν hν
    constructor
    · exact (opNorm_curv_le a hG U ν μ x (hpu ν hν).1).trans
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hpl ν hν).1 (Nat.cast_nonneg _))
          (by positivity))
    · exact (opNorm_curv_le a hG U ν μ _ (hpu ν hν).2).trans
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hpl ν hν).2 (Nat.cast_nonneg _))
          (by positivity))
  have hterm : ∀ ν, ‖(if ν ≠ μ then Dbw a U ν (curv a hG U ν μ) x else 0)‖ ≤
      if ν ≠ μ then ‖a‖⁻¹ * (2 * C) else 0 := by
    intro ν
    split_ifs with hν
    · unfold Dbw
      rw [norm_smul, norm_inv]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      have hval : U.val ⟨x, ν, false⟩ = (U ν (x - unit n ν))⁻¹ := by simp [Config.val]
      rw [hval]
      refine (norm_sub_le _ _).trans ?_
      rw [opNorm_Ad_unitary (unitary_inv (hunit ν hν))]
      linarith [(hF ν hν).1, (hF ν hν).2]
    · simp
  unfold current Ds2
  refine (norm_sum_le _ _).trans ((sum_le_sum fun ν _ => hterm ν).trans ?_)
  rw [sum_ite, sum_const_zero, add_zero, sum_const, filter_ne' univ μ, card_erase_of_mem (mem_univ _),
    card_univ, Fintype.card_fin, nsmul_eq_mul]
  have ha3 : ‖a‖ ^ 3 = ‖a‖ * ‖a‖ ^ 2 := by ring
  by_cases ha : ‖a‖ = 0
  · simp [ha, C]
  · have hpos : 0 < ‖a‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm ha)
    simp only [C]
    field_simp
    ring_nf
    norm_num

/-- The bonds of `p_{νμ}(y)` agree for `U` and `U'`. -/
def BondsAgree (U U' : Config N n) (ν μ : Fin 4) (y : Site n) : Prop :=
  U ν y = U' ν y ∧ U μ (y + unit n ν) = U' μ (y + unit n ν) ∧
    U ν (y + unit n μ) = U' ν (y + unit n μ) ∧ U μ y = U' μ y

/-- The current at `b` depends only on the field on the bonds of the six plaquettes of `b`. -/
theorem current_local (hG : G.LieInput) (U U' : Config N n) (μ : Fin 4) (x : Site n)
    (h : Six (BondsAgree U U') μ x) : current a hG U μ x = current a hG U' μ x := by
  unfold current Ds2
  refine sum_congr rfl fun ν _ => ?_
  split_ifs with hν
  · obtain ⟨⟨a1, a2, a3, a4⟩, ⟨b1, b2, b3, b4⟩⟩ := h ν hν
    have hval : ∀ V : Config N n, V.val ⟨x, ν, false⟩ = (V ν (x - unit n ν))⁻¹ := fun V => by
      simp [Config.val]
    simp only [Dbw, curv, hval, plaq_eq, a1, a2, a3, a4, b1, b2, b3, b4]
  · rfl

/-! ### The geometry of a support -/

/-- `z` differs from `x` by at most `1` in each coordinate. -/
def Near1 (x z : Site n) : Prop := ∀ κ, ∃ t : ℤ, |t| ≤ 1 ∧ z κ - x κ = (t : ZMod n)

lemma dinf_le_two {x z z' : Site n} (hz : Near1 x z) (hz' : Near1 x z') :
    Blocks.dinf z z' ≤ 2 := by
  refine Finset.sup_le fun κ _ => ?_
  obtain ⟨t, ht, e⟩ := hz κ
  obtain ⟨t', ht', e'⟩ := hz' κ
  have : z κ - z' κ = ((t - t' : ℤ) : ZMod n) := by
    rw [show z κ - z' κ = (z κ - x κ) - (z' κ - x κ) by ring, e, e']; push_cast; ring
  rw [this]
  refine (Blocks.cd_intCast_le _).trans ?_
  have := abs_le.mp ht; have := abs_le.mp ht'
  omega

lemma near1_add (x : Site n) (s t : ℤ) (hs : |s| ≤ 1) (ht : |t| ≤ 1) {ν μ : Fin 4} (hνμ : ν ≠ μ) :
    Near1 x (x + (s : ZMod n) • unit n ν + (t : ZMod n) • unit n μ) := by
  intro κ
  simp only [Pi.add_apply, Pi.smul_apply, unit, Pi.single_apply, smul_eq_mul, add_sub_cancel_left]
  by_cases h1 : κ = ν
  · subst h1
    refine ⟨s, hs, ?_⟩
    simp [hνμ]
  · by_cases h2 : κ = μ
    · subst h2; refine ⟨t, ht, ?_⟩; simp [h1]
    · refine ⟨0, by simp, ?_⟩; simp [h1, h2]

/-- The corners of the six plaquettes of the bond `(x, x + e_μ)` differ from `x` by at most `1` in each
coordinate: those of `p_{νμ}(x)` and of `p_{νμ}(x - e_ν)`. -/
lemma near1_corners {μ ν : Fin 4} (hνμ : ν ≠ μ) (x : Site n) :
    (Near1 x x ∧ Near1 x (x + unit n ν) ∧ Near1 x (x + unit n μ) ∧
      Near1 x (x + unit n ν + unit n μ)) ∧
    (Near1 x (x - unit n ν) ∧ Near1 x (x - unit n ν + unit n ν) ∧
      Near1 x (x - unit n ν + unit n μ) ∧ Near1 x (x - unit n ν + unit n ν + unit n μ)) := by
  have key : ∀ s t : ℤ, |s| ≤ 1 → |t| ≤ 1 →
      Near1 x (x + (s : ZMod n) • unit n ν + (t : ZMod n) • unit n μ) :=
    fun s t hs ht => near1_add x s t hs ht hνμ
  have k00 := key 0 0 (by simp) (by simp)
  have k10 := key 1 0 (by simp) (by simp)
  have k01 := key 0 1 (by simp) (by simp)
  have k11 := key 1 1 (by simp) (by simp)
  have km0 := key (-1) 0 (by simp) (by simp)
  have km1 := key (-1) 1 (by simp) (by simp)
  simp only [Int.cast_zero, Int.cast_one, Int.cast_neg, zero_smul, one_smul, neg_smul,
    add_zero] at k00 k10 k01 k11 km0 km1
  refine ⟨⟨k00, k10, ?_, k11⟩, ⟨?_, ?_, ?_, ?_⟩⟩
  · simpa using k01
  · simpa [sub_eq_add_neg] using km0
  · simpa using k00
  · simpa [sub_eq_add_neg] using km1
  · simpa using k01

/-- The plaquette `p_{νμ}(y)` has all its corners in `S`. -/
def PlaqOf (S : Set (Site n)) (ν μ : Fin 4) (y : Site n) : Prop :=
  y ∈ S ∧ y + unit n ν ∈ S ∧ y + unit n μ ∈ S ∧ y + unit n ν + unit n μ ∈ S

/-- The plaquette `p_{νμ}(y)` has no corner in `S`. -/
def NoCorner (S : Set (Site n)) (ν μ : Fin 4) (y : Site n) : Prop :=
  y ∉ S ∧ y + unit n ν ∉ S ∧ y + unit n μ ∉ S ∧ y + unit n ν + unit n μ ∉ S

/-- The bond `(y, y + e_μ)` has both ends in `S`. -/
def BondOf (S : Set (Site n)) (μ : Fin 4) (y : Site n) : Prop := y ∈ S ∧ y + unit n μ ∈ S

/-- If one of the six plaquettes of a bond has a corner outside the support `W`, then none of them has
a corner in `Ω₁`. -/
lemma six_noCorner {W Ω₁ : Set (Site n)} {M₁ : ℕ} (hM : 2 ≤ M₁)
    (hW : ∀ z ∉ W, ∀ z' ∈ Ω₁, M₁ < Blocks.dinf z z') {μ : Fin 4} {x : Site n}
    (h : ¬ Six (PlaqOf W) μ x) : Six (NoCorner Ω₁) μ x := by
  -- a corner outside `W`
  obtain ⟨z, hzn, hzW⟩ : ∃ z, Near1 x z ∧ z ∉ W := by
    simp only [Six, not_forall] at h
    obtain ⟨ν, hν, hn⟩ := h
    obtain ⟨⟨c1, c2, c3, c4⟩, ⟨c5, c6, c7, c8⟩⟩ := near1_corners (n := n) hν x
    simp only [PlaqOf, not_and_or] at hn
    rcases hn with (h1 | h1 | h1 | h1) | (h1 | h1 | h1 | h1)
    · exact ⟨_, c1, h1⟩
    · exact ⟨_, c2, h1⟩
    · exact ⟨_, c3, h1⟩
    · exact ⟨_, c4, h1⟩
    · exact ⟨_, c5, h1⟩
    · exact ⟨_, c6, h1⟩
    · exact ⟨_, c7, h1⟩
    · exact ⟨_, c8, h1⟩
  have hnot : ∀ z', Near1 x z' → z' ∉ Ω₁ := fun z' hz' hmem => by
    have := hW z hzW z' hmem
    have := dinf_le_two hzn hz'
    omega
  intro ν hν
  obtain ⟨⟨c1, c2, c3, c4⟩, ⟨c5, c6, c7, c8⟩⟩ := near1_corners (n := n) hν x
  exact ⟨⟨hnot _ c1, hnot _ c2, hnot _ c3, hnot _ c4⟩,
    ⟨hnot _ c5, hnot _ c6, hnot _ c7, hnot _ c8⟩⟩

/-- A plaquette with a corner outside the support has no corner in `Ω₁`. -/
lemma plaq_noCorner {W Ω₁ : Set (Site n)} {M₁ : ℕ} (hM : 2 ≤ M₁)
    (hW : ∀ z ∉ W, ∀ z' ∈ Ω₁, M₁ < Blocks.dinf z z') {ν μ : Fin 4} (hνμ : ν ≠ μ) {y : Site n}
    (h : ¬ PlaqOf W ν μ y) : NoCorner Ω₁ ν μ y := by
  obtain ⟨⟨c1, c2, c3, c4⟩, -⟩ := near1_corners (n := n) hνμ y
  obtain ⟨z, hzn, hzW⟩ : ∃ z, Near1 y z ∧ z ∉ W := by
    simp only [PlaqOf, not_and_or] at h
    rcases h with h1 | h1 | h1 | h1
    · exact ⟨_, c1, h1⟩
    · exact ⟨_, c2, h1⟩
    · exact ⟨_, c3, h1⟩
    · exact ⟨_, c4, h1⟩
  have hnot : ∀ z', Near1 y z' → z' ∉ Ω₁ := fun z' hz' hmem => by
    have := hW z hzW z' hmem
    have := dinf_le_two hzn hz'
    omega
  exact ⟨hnot _ c1, hnot _ c2, hnot _ c3, hnot _ c4⟩

/-! ### The continuation -/

/-- The continuation of `U` by `V`: `U` on the bonds of `W`, `V` on the others. -/
def cont (W : Set (Site n)) (U V : Config N n) : Config N n :=
  fun μ y => if BondOf W μ y then U μ y else V μ y

/-- The hypotheses of `lem:support-continuation`. -/
structure Hyp (W 𝒩 Ω₁ : Set (Site n)) (M₁ : ℕ) (U V : Config N n) (α α' : ℝ) : Prop where
  two_le : 2 ≤ M₁
  supp : ∀ z ∉ W, ∀ z' ∈ Ω₁, M₁ < Blocks.dinf z z'
  V_unit : ∀ μ y, BondOf 𝒩 μ y → y ∉ Ω₁ → y + unit n μ ∉ Ω₁ →
    ((V μ y : GLN) : Mat) ∈ unitaryGroup (Fin N) ℂ
  V_plaq : ∀ ν μ y, ν ≠ μ → PlaqOf 𝒩 ν μ y → NoCorner Ω₁ ν μ y →
    hs (((plaq V ν μ y : GLN) : Mat) - 1) ≤ α
  U_unit : ∀ μ y, BondOf W μ y → ((U μ y : GLN) : Mat) ∈ unitaryGroup (Fin N) ℂ
  U_plaq : ∀ ν μ y, ν ≠ μ → PlaqOf W ν μ y → hs (((plaq U ν μ y : GLN) : Mat) - 1) ≤ α
  close : ∀ μ y, BondOf W μ y → y ∉ Ω₁ → y + unit n μ ∉ Ω₁ →
    hs (((U μ y : GLN) : Mat) - ((V μ y : GLN) : Mat)) ≤ α'
  α'_nonneg : 0 ≤ α'

variable {W 𝒩 Ω₁ : Set (Site n)} {M₁ : ℕ} {U V : Config N n} {α α' : ℝ}

lemma hs_zero : hs (0 : Mat) = 0 := by simp [hs, hs2, ntr]

/-- The bonds of a plaquette of `S` are bonds of `S`. -/
lemma plaqOf_bonds {S : Set (Site n)} {ν μ : Fin 4} {y : Site n} (h : PlaqOf S ν μ y) :
    BondOf S ν y ∧ BondOf S μ (y + unit n ν) ∧ BondOf S ν (y + unit n μ) ∧ BondOf S μ y := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨⟨h1, h2⟩, ⟨h2, h4⟩, ⟨h3, ?_⟩, ⟨h1, h3⟩⟩
  rwa [add_right_comm]

/-- The bonds of a plaquette with no corner in `S` have no end in `S`. -/
lemma noCorner_bonds {S : Set (Site n)} {ν μ : Fin 4} {y : Site n} (h : NoCorner S ν μ y) :
    (y ∉ S ∧ y + unit n ν ∉ S) ∧ (y + unit n ν ∉ S ∧ y + unit n ν + unit n μ ∉ S) ∧
      (y + unit n μ ∉ S ∧ y + unit n μ + unit n ν ∉ S) ∧ (y ∉ S ∧ y + unit n μ ∉ S) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨⟨h1, h2⟩, ⟨h2, h4⟩, ⟨h3, ?_⟩, ⟨h1, h3⟩⟩
  rwa [add_right_comm]

/-- On a bond of `𝒩` with no end in `Ω₁` the continuation is unitary and within `α'` of `V`. -/
lemma cont_bond (H : Hyp W 𝒩 Ω₁ M₁ U V α α') {κ : Fin 4} {z : Site n} (hb : BondOf 𝒩 κ z)
    (h1 : z ∉ Ω₁) (h2 : z + unit n κ ∉ Ω₁) :
    ((cont W U V κ z : GLN) : Mat) ∈ unitaryGroup (Fin N) ℂ ∧
      hs (((cont W U V κ z : GLN) : Mat) - ((V κ z : GLN) : Mat)) ≤ α' := by
  unfold cont
  split_ifs with hW
  · exact ⟨H.U_unit κ z hW, H.close κ z hW h1 h2⟩
  · rw [sub_self, hs_zero]; exact ⟨H.V_unit κ z hb h1 h2, H.α'_nonneg⟩

/-- On the plaquettes of `W` the continuation is `U`. -/
lemma plaq_cont_of_W {ν μ : Fin 4} {y : Site n} (h : PlaqOf W ν μ y) :
    plaq (cont W U V) ν μ y = plaq U ν μ y := by
  obtain ⟨b1, b2, b3, b4⟩ := plaqOf_bonds h
  simp only [plaq_eq, cont, if_pos b1, if_pos b2, if_pos b3, if_pos b4]

/-- The plaquettes of a plaquette of `𝒩` with no corner in `Ω₁` are unitary for the continuation. -/
lemma plaq_cont_unitary (H : Hyp W 𝒩 Ω₁ M₁ U V α α') {ν μ : Fin 4} {y : Site n}
    (hp : PlaqOf 𝒩 ν μ y) (hnc : NoCorner Ω₁ ν μ y) :
    (∀ X ∈ [cont W U V ν y, cont W U V μ (y + unit n ν), cont W U V ν (y + unit n μ),
      cont W U V μ y], ((X : GLN) : Mat) ∈ unitaryGroup (Fin N) ℂ) ∧
    (∀ X ∈ [V ν y, V μ (y + unit n ν), V ν (y + unit n μ), V μ y],
      ((X : GLN) : Mat) ∈ unitaryGroup (Fin N) ℂ) := by
  obtain ⟨b1, b2, b3, b4⟩ := plaqOf_bonds hp
  obtain ⟨⟨e1, e1'⟩, ⟨e2, e2'⟩, ⟨e3, e3'⟩, ⟨e4, e4'⟩⟩ := noCorner_bonds hnc
  refine ⟨fun X hX => ?_, fun X hX => ?_⟩
  · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hX
    rcases hX with rfl | rfl | rfl | rfl
    · exact (cont_bond H b1 e1 e1').1
    · exact (cont_bond H b2 e2 e2').1
    · exact (cont_bond H b3 e3 e3').1
    · exact (cont_bond H b4 e4 e4').1
  · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hX
    rcases hX with rfl | rfl | rfl | rfl
    · exact H.V_unit _ _ b1 e1 e1'
    · exact H.V_unit _ _ b2 e2 e2'
    · exact H.V_unit _ _ b3 e3 e3'
    · exact H.V_unit _ _ b4 e4 e4'

/-- `lem:support-continuation` for the plaquettes: a plaquette of `𝒩` which is not one of `W` has no
corner in `Ω₁`, and `|Ũ(∂p) - 1| ≤ α + 4α'`. -/
theorem plaq_cont (H : Hyp W 𝒩 Ω₁ M₁ U V α α') {ν μ : Fin 4} (hνμ : ν ≠ μ) {y : Site n}
    (hp : PlaqOf 𝒩 ν μ y) (hpW : ¬ PlaqOf W ν μ y) :
    NoCorner Ω₁ ν μ y ∧ hs (((plaq (cont W U V) ν μ y : GLN) : Mat) - 1) ≤ α + 4 * α' := by
  have hnc := plaq_noCorner H.two_le H.supp hνμ hpW
  refine ⟨hnc, ?_⟩
  obtain ⟨hu, hv⟩ := plaq_cont_unitary H hp hnc
  obtain ⟨b1, b2, b3, b4⟩ := plaqOf_bonds hp
  obtain ⟨⟨e1, e1'⟩, ⟨e2, e2'⟩, ⟨e3, e3'⟩, ⟨e4, e4'⟩⟩ := noCorner_bonds hnc
  have h4 := hs_plaq_sub_le (cont W U V) V ν μ y hu hv
  have d1 := (cont_bond H b1 e1 e1').2
  have d2 := (cont_bond H b2 e2 e2').2
  have d3 := (cont_bond H b3 e3 e3').2
  have d4 := (cont_bond H b4 e4 e4').2
  have hV := H.V_plaq ν μ y hνμ hp hnc
  have htri : hs (((plaq (cont W U V) ν μ y : GLN) : Mat) - 1) ≤
      hs (((plaq (cont W U V) ν μ y : GLN) : Mat) - ((plaq V ν μ y : GLN) : Mat)) +
        hs (((plaq V ν μ y : GLN) : Mat) - 1) := by
    have := hs_add_le (((plaq (cont W U V) ν μ y : GLN) : Mat) - ((plaq V ν μ y : GLN) : Mat))
      (((plaq V ν μ y : GLN) : Mat) - 1)
    rwa [sub_add_sub_cancel] at this
  linarith

/-- `lem:support-continuation` for the current: at a bond of `𝒩` all of whose plaquettes are
plaquettes of `𝒩`, the current of `Ũ` is that of `U` if the six plaquettes are plaquettes of `W`;
otherwise none of them has a corner in `Ω₁` and `‖J(Ũ)(b)‖ ≤ 6N(α + 4α')η⁻³`. -/
theorem current_cont [NeZero N] (hG : G.LieInput) (H : Hyp W 𝒩 Ω₁ M₁ U V α α') {μ : Fin 4}
    {x : Site n} (h𝒩 : Six (PlaqOf 𝒩) μ x) :
    (Six (PlaqOf W) μ x → current a hG (cont W U V) μ x = current a hG U μ x) ∧
    (¬ Six (PlaqOf W) μ x → Six (NoCorner Ω₁) μ x ∧
      ‖current a hG (cont W U V) μ x‖ ≤ 6 * N * (α + 4 * α') / ‖a‖ ^ 3) := by
  constructor
  · intro hW
    refine current_local a hG _ _ μ x fun ν hν => ?_
    have agree : ∀ {y}, PlaqOf W ν μ y → BondsAgree (cont W U V) U ν μ y := fun {y} hp => by
      obtain ⟨b1, b2, b3, b4⟩ := plaqOf_bonds hp
      simp only [BondsAgree, cont, if_pos b1, if_pos b2, if_pos b3, if_pos b4, and_self]
    exact ⟨agree (hW ν hν).1, agree (hW ν hν).2⟩
  · intro hW
    have hnc := six_noCorner H.two_le H.supp hW
    refine ⟨hnc, opNorm_current_le a hG _ μ x ?_ ?_ ?_⟩
    · -- the transport `Ũ(x, x - e_ν)`
      intro ν hν
      obtain ⟨b1, -, -, -⟩ := plaqOf_bonds (h𝒩 ν hν).2
      obtain ⟨⟨e1, e1'⟩, -, -, -⟩ := noCorner_bonds (hnc ν hν).2
      exact (cont_bond H b1 e1 e1').1
    · -- the six plaquettes are unitary
      have hu : ∀ {ν y}, PlaqOf 𝒩 ν μ y → NoCorner Ω₁ ν μ y →
          ((plaq (cont W U V) ν μ y : GLN) : Mat) ∈ unitaryGroup (Fin N) ℂ := fun {ν y} hp hn => by
        obtain ⟨hu, -⟩ := plaq_cont_unitary H hp hn
        rw [plaq_eq]
        exact unitary_mul (unitary_mul (unitary_mul (hu (cont W U V ν y) (by simp))
          (hu (cont W U V μ (y + unit n ν)) (by simp)))
          (unitary_inv (hu (cont W U V ν (y + unit n μ)) (by simp))))
          (unitary_inv (hu (cont W U V μ y) (by simp)))
      intro ν hν
      exact ⟨hu (h𝒩 ν hν).1 (hnc ν hν).1, hu (h𝒩 ν hν).2 (hnc ν hν).2⟩
    · -- the six plaquettes are within `α + 4α'` of `1`
      have hb : ∀ {ν y}, PlaqOf 𝒩 ν μ y → ν ≠ μ →
          hs (((plaq (cont W U V) ν μ y : GLN) : Mat) - 1) ≤ α + 4 * α' := fun {ν y} hp hν => by
        by_cases hpW : PlaqOf W ν μ y
        · rw [plaq_cont_of_W hpW]
          linarith [H.U_plaq ν μ y hν hpW, H.α'_nonneg]
        · exact (plaq_cont H hν hp hpW).2
      intro ν hν
      exact ⟨hb (h𝒩 ν hν).1 hν, hb (h𝒩 ν hν).2 hν⟩

end SupportCont

end CoreLean
