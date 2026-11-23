/-
`cor:axial-straight` of BALABAN_CORE.tex (`ac1c7014d508`) with its plaquette hypothesis at the finest scale
only: the bounds on the plaquettes of `M^i(U)`, `i < j`, inside `𝖡` follow from `prop:regular-averages`(ii)
applied to each plaquette of `T^{(i)}` with corners in `𝖡`, whose blocks of order `i` lie in `𝖡`.
* `inB_of_inR`: the blocks of order `i - l` of the corners of a plaquette of `T^{(i)}` with corners in `𝖡`
  lie in `𝖡`.
* `decode`: a plaquette of the torus `T^{(i)}` with corners in the image of `𝖡` is the image of a plaquette
  with corners in `𝖡`, when the torus has at least `3L^{j-i}` sites in each direction.
* `plaq_levels`: the plaquette bounds `√N·2αL^{-2(j-i)}` of `axial_straight_lattice`.
* `axial_regular`: `cor:axial-straight` with `|U(∂p) - id| ≤ α(η/a_j)²` on `T^{(0)}` as the plaquette hypothesis.
-/
import CoreLean.RegularAveragesII
import CoreLean.AxialStraightLattice

open Matrix NormedSpace
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace CoreLean

namespace AxialRegular

open LatticePaths LatticeKappa BoxGeometry AxialStraightLattice AxialReference RegularAverages

set_option linter.unusedSectionVars false

variable {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "GLN" => (Matrix (Fin N) (Fin N) ℂ)ˣ

/-! ### Coordinates -/

lemma lat_mono {h m i : ℕ} (hmi : m ≤ i) {x : Fin 4 → ℤ} (hx : Lat (Lz h) i x) : Lat (Lz h) m x :=
  fun σ => (pow_dvd_pow _ hmi).trans (hx σ)

lemma lat_zero' {h : ℕ} (x : Fin 4 → ℤ) : Lat (Lz h) 0 x := fun σ => by simp

lemma img_img {n : ℕ} [NeZero n] {h m : ℕ} (y : Site n) {x x' : Fin 4 → ℤ} (hx : Lat (Lz h) m x)
    (hx' : Lat (Lz h) m x') : img h (img h y m x) m x' = img h y m (x + x') := by
  conv_lhs => rw [img]
  rw [img_add y hx, ← qt_spec hx']

lemma ev_eq_smul' (h l : ℕ) (ρ : Fin 4) : ev (Lz h) l ρ = Lz h ^ l • Pi.single ρ 1 := by
  funext σ
  simp only [ev, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
  split_ifs <;> simp

/-- Two vectors whose sites agree and which differ by less than `n` in each coordinate are equal. -/
lemma ofs_inj_lt {n : ℕ} [NeZero n] (y : Site n) {a b : Fin 4 → ℤ} (e : ofs y a = ofs y b)
    (hab : ∀ σ, |a σ - b σ| < n) : a = b := by
  funext σ
  have h1 : ((a σ : ℤ) : ZMod n) = ((b σ : ℤ) : ZMod n) := by
    have := congrFun e σ
    simpa [ofs] using this
  have h2 : (n : ℤ) ∣ b σ - a σ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 h1
  have := Int.eq_zero_of_abs_lt_dvd h2 (by rw [abs_sub_comm]; exact hab σ)
  linarith

/-- Two points of `T^{(i)}` with the same site of a torus of at least `3L^{j-i}` sites per direction,
which differ by less than `3L^j` in each coordinate, are equal. -/
lemma decode_pt {n : ℕ} [NeZero n] {h i j : ℕ} (hij : i ≤ j) (hn : 3 * Lz h ^ (j - i) ≤ (n : ℤ))
    (y : Site n) {a b : Fin 4 → ℤ} (ha : Lat (Lz h) i a) (hb : Lat (Lz h) i b)
    (e : img h y i a = img h y i b) (hab : ∀ σ, |a σ - b σ| < 3 * Lz h ^ j) : a = b := by
  have hP : 0 < Lz h ^ i := pow_pos (Lz_pos h) i
  have hpow : Lz h ^ j = Lz h ^ i * Lz h ^ (j - i) := by rw [← pow_add, Nat.add_sub_cancel' hij]
  have hq : qt h i a = qt h i b := by
    refine ofs_inj_lt y e fun σ => ?_
    have hd : a σ - b σ = Lz h ^ i * (qt h i a σ - qt h i b σ) := by
      have e1 := congrFun (qt_spec ha) σ
      have e2 := congrFun (qt_spec hb) σ
      simp only [Pi.smul_apply, smul_eq_mul] at e1 e2
      rw [mul_sub, ← e1, ← e2]
    have h1 := hab σ
    rw [hd, abs_mul, abs_of_pos hP, hpow, mul_comm 3, mul_assoc] at h1
    have := lt_of_mul_lt_mul_left h1 hP.le
    linarith
  rw [qt_spec ha, qt_spec hb, hq]

/-- The coordinates of a point of `𝖡`. -/
lemma inB_bound {h j : ℕ} {μ : Fin 4} {x : Fin 4 → ℤ} (hx : InB (Lz h) j μ x) (σ : Fin 4) :
    -(Lz h ^ j - 1) ≤ 2 * x σ ∧ 2 * x σ ≤ 3 * Lz h ^ j - 1 := by
  obtain ⟨h1, h2, h3⟩ := (inB_iff (Lz_odd h) (Lz_one h) x).1 hx
  have hp : 0 < Lz h ^ j := pow_pos (Lz_pos h) j
  by_cases hσ : σ = μ
  · subst hσ; exact ⟨h2, h3⟩
  · obtain ⟨a, b⟩ := h1 σ hσ; constructor <;> linarith

/-- A plaquette of the torus `T^{(i)}`, `i < j`, with corners in the image of `𝖡` is the image of the
plaquette of `T^{(i)}` with the first corner `x` and with its four corners in `𝖡`. -/
lemma decode {n : ℕ} [NeZero n] {h i j : ℕ} (hh : 1 ≤ h) (hij : i < j) (hn : 3 * Lz h ^ (j - i) ≤ (n : ℤ))
    (y : Site n) {μ μ' ν' : Fin 4} {z : Site n} (hz : PlaqIn (Reg h j μ i y) μ' ν' z) :
    ∃ x, Lat (Lz h) i x ∧ z = img h y i x ∧ InB (Lz h) j μ x ∧
      InB (Lz h) j μ (x + Lz h ^ i • Pi.single μ' 1) ∧ InB (Lz h) j μ (x + Lz h ^ i • Pi.single ν' 1) ∧
      InB (Lz h) j μ (x + Lz h ^ i • Pi.single μ' 1 + Lz h ^ i • Pi.single ν' 1) := by
  obtain ⟨⟨x, hxl, hxB, rfl⟩, ⟨x1, hx1l, hx1B, e1⟩, ⟨x2, hx2l, hx2B, e2⟩, ⟨x3, hx3l, hx3B, e3⟩⟩ := hz
  have hP : 0 < Lz h ^ i := pow_pos (Lz_pos h) i
  have hPj : 3 * Lz h ^ i ≤ Lz h ^ j := by
    have hpow : Lz h ^ j = Lz h ^ i * Lz h ^ (j - i) := by rw [← pow_add, Nat.add_sub_cancel' hij.le]
    have : Lz h ≤ Lz h ^ (j - i) := by
      calc Lz h = Lz h ^ 1 := (pow_one _).symm
        _ ≤ Lz h ^ (j - i) := pow_le_pow_right₀ (Lz_one h) (by omega)
    have h3 : (3 : ℤ) ≤ Lz h ^ (j - i) := by
      have : (3 : ℤ) ≤ Lz h := by unfold Lz; omega
      linarith
    rw [hpow]; nlinarith
  have hl1 : ∀ ρ, Lat (Lz h) i (x + Lz h ^ i • Pi.single ρ 1) := fun ρ σ => dvd_add (hxl σ) (lat_smul _ σ)
  have hl2 : Lat (Lz h) i (x + Lz h ^ i • Pi.single μ' 1 + Lz h ^ i • Pi.single ν' 1) :=
    fun σ => dvd_add (hl1 μ' σ) (lat_smul _ σ)
  have hshift : ∀ (w : Fin 4 → ℤ) ρ σ, |(w + Lz h ^ i • Pi.single ρ 1 : Fin 4 → ℤ) σ - w σ| ≤ Lz h ^ i :=
    fun w ρ σ => by
      simp only [Pi.add_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, add_sub_cancel_left]
      split_ifs <;> simp [abs_of_pos hP, hP.le]
  have far : ∀ (a b : Fin 4 → ℤ), InB (Lz h) j μ b → (∀ σ, |a σ - x σ| ≤ 2 * Lz h ^ i) →
      ∀ σ, |a σ - b σ| < 3 * Lz h ^ j := fun a b hb ha σ => by
    have u := inB_bound hxB σ
    have v := inB_bound hb σ
    have w := abs_le.1 (ha σ)
    rw [abs_lt]; constructor <;> linarith
  have k1 : x + Lz h ^ i • Pi.single μ' 1 = x1 := by
    refine decode_pt hij.le hn y (hl1 μ') hx1l (by rw [← img_unit y hxl]; exact e1) ?_
    exact far _ _ hx1B fun σ => (hshift x μ' σ).trans (by linarith)
  have k2 : x + Lz h ^ i • Pi.single ν' 1 = x2 := by
    refine decode_pt hij.le hn y (hl1 ν') hx2l (by rw [← img_unit y hxl]; exact e2) ?_
    exact far _ _ hx2B fun σ => (hshift x ν' σ).trans (by linarith)
  have k3 : x + Lz h ^ i • Pi.single μ' 1 + Lz h ^ i • Pi.single ν' 1 = x3 := by
    refine decode_pt hij.le hn y hl2 hx3l
      (by rw [← img_unit y (hl1 μ'), ← img_unit y hxl]; exact e3) ?_
    refine far _ _ hx3B fun σ => ?_
    have a1 := hshift (x + Lz h ^ i • Pi.single μ' 1) ν' σ
    have a2 := hshift x μ' σ
    calc |(x + Lz h ^ i • Pi.single μ' 1 + Lz h ^ i • Pi.single ν' 1 : Fin 4 → ℤ) σ - x σ|
        ≤ |(x + Lz h ^ i • Pi.single μ' 1 + Lz h ^ i • Pi.single ν' 1 : Fin 4 → ℤ) σ -
            (x + Lz h ^ i • Pi.single μ' 1 : Fin 4 → ℤ) σ| +
          |(x + Lz h ^ i • Pi.single μ' 1 : Fin 4 → ℤ) σ - x σ| := abs_sub_le _ _ _
      _ ≤ 2 * Lz h ^ i := by linarith
  exact ⟨x, hxl, rfl, hxB, k1 ▸ hx1B, k2 ▸ hx2B, k3 ▸ hx3B⟩

/-- The blocks of order `i - l` of the corners of a plaquette of `T^{(i)}` with corners in `𝖡` lie in
`𝖡`: the point `x + x'`, with `x'` in the region `InR` of order `i - l` of the plaquette translated to the
origin, lies in `𝖡`. -/
lemma inB_of_inR {h i j l : ℕ} (hij : i ≤ j) (hli : l ≤ i) {μ μ' ν' : Fin 4} (hμν' : μ' ≠ ν')
    {x : Fin 4 → ℤ} (hx : Lat (Lz h) i x)
    (hc : ∀ c : Fin 4 → ℤ, (c μ' = 0 ∨ c μ' = Lz h ^ i) → (c ν' = 0 ∨ c ν' = Lz h ^ i) →
      (∀ σ, σ ≠ μ' → σ ≠ ν' → c σ = 0) → InB (Lz h) j μ (x + c))
    {x' : Fin 4 → ℤ} (hx' : Lat (Lz h) l x') (hR : InR h i μ' ν' l x') : InB (Lz h) j μ (x + x') := by
  obtain ⟨c, hc1, hc2, hc3, hxc⟩ := (inR_iff_blocks hli hμν' hx').1 hR
  have hcB := hc c hc1 hc2 hc3
  have hcl : Lat (Lz h) i (x + c) := fun σ => by
    refine dvd_add (hx σ) ?_
    by_cases h1 : σ = μ'
    · subst h1; rcases hc1 with e | e <;> simp [e]
    by_cases h2 : σ = ν'
    · subst h2; rcases hc2 with e | e <;> simp [e]
    · rw [hc3 σ h1 h2]; exact dvd_zero _
  have hblk : Blk (Lz h) i (x + c) (x + x') := fun σ => by
    have e := two_Hw h i l
    have hl1 : 1 ≤ Lz h ^ l := one_le_pow₀ (Lz_one h)
    have a := abs_le.1 (hxc σ)
    simp only [Pi.add_apply]
    constructor <;> linarith
  have hLo := Lz_odd h
  have hL1 := Lz_one h
  rcases hcB with hB | hB
  · exact Or.inl (incl hLo hL1 hij hcl (zero_lat hLo hL1 j) hB hblk)
  · exact Or.inr (incl hLo hL1 hij hcl (cp_lat hLo hL1) hB hblk)

/-- The corners of the plaquette `p_{μ'ν'}(x)` in `𝖡` give the corner condition of `inB_of_inR`. -/
lemma corners_inB {h i j : ℕ} {μ μ' ν' : Fin 4} (hμν' : μ' ≠ ν') {x : Fin 4 → ℤ}
    (h0 : InB (Lz h) j μ x) (h1 : InB (Lz h) j μ (x + Lz h ^ i • Pi.single μ' 1))
    (h2 : InB (Lz h) j μ (x + Lz h ^ i • Pi.single ν' 1))
    (h3 : InB (Lz h) j μ (x + Lz h ^ i • Pi.single μ' 1 + Lz h ^ i • Pi.single ν' 1)) :
    ∀ c : Fin 4 → ℤ, (c μ' = 0 ∨ c μ' = Lz h ^ i) → (c ν' = 0 ∨ c ν' = Lz h ^ i) →
      (∀ σ, σ ≠ μ' → σ ≠ ν' → c σ = 0) → InB (Lz h) j μ (x + c) := by
  intro c hc1 hc2 hc3
  have hce : c = Pi.single μ' (c μ') + Pi.single ν' (c ν') := by
    funext σ
    by_cases e1 : σ = μ'
    · subst e1; simp [Pi.single_eq_of_ne hμν']
    by_cases e2 : σ = ν'
    · subst e2; simp [Pi.single_eq_of_ne e1]
    · simp [Pi.single_eq_of_ne e1, Pi.single_eq_of_ne e2, hc3 σ e1 e2]
  have hs : ∀ ρ, (Pi.single ρ (Lz h ^ i) : Fin 4 → ℤ) = Lz h ^ i • Pi.single ρ 1 := fun ρ => by
    rw [← ev, ev_eq_smul']
  rw [hce]
  rcases hc1 with a | a <;> rcases hc2 with b | b <;> rw [a, b] <;>
    simp only [Pi.single_zero, add_zero, zero_add, hs, ← add_assoc]
  · exact h0
  · exact h2
  · exact h1
  · exact h3

/-- A torus of at least `3L^{j-i}` sites per direction, `i < j`, has at least `3L = 6h + 3`. -/
lemma torus_ge {n h i j : ℕ} (hij : i < j) (hn : 3 * Lz h ^ (j - i) ≤ (n : ℤ)) : 6 * h + 3 ≤ n := by
  have : Lz h ≤ Lz h ^ (j - i) := by
    calc Lz h = Lz h ^ 1 := (pow_one _).symm
      _ ≤ Lz h ^ (j - i) := pow_le_pow_right₀ (Lz_one h) (by omega)
  have hL : Lz h = 2 * h + 1 := rfl
  have : ((6 * h + 3 : ℕ) : ℤ) ≤ n := by push_cast; linarith
  exact_mod_cast this

set_option maxHeartbeats 2000000 in
/-- The plaquette bounds of `cor:axial-straight` at the scales `i < j`, from the bound at the finest scale:
if `|M^0(U)(∂p) - id| ≤ α(η/a_j)² = αL^{-2j}` for the plaquettes of `T^{(0)}` with corners in `𝖡`, and the
fields `V_i` are the iterated averages on the bonds of `T^{(i)}` in `𝖡`, then `‖V_i(∂p) - id‖ ≤
√N·2αL^{-2(j-i)}` for the plaquettes of `T^{(i)}` with corners in `𝖡`: `prop:regular-averages`(ii) with
`α' = αL^{-2(j-i)}` at each such plaquette, whose blocks of order `i` lie in `𝖡`, and `lem:norms`(i). -/
theorem plaq_levels (G : GaugeGroup N) (hG : IsClosed G.mats) (hN : 1 ≤ N) :
    ∃ c₂ : ℝ, 0 < c₂ ∧ ∀ (h : ℕ), 1 ≤ h → ∀ (j : ℕ) (μ : Fin 4) (nn : ℕ → ℕ) [∀ i, NeZero (nn i)],
      (∀ i, i < j → 3 * Lz h ^ (j - i) ≤ (nn i : ℤ)) →
      ∀ (base : ∀ i, Site (nn i)) (V : ∀ i, Config N (nn i)), (∀ i, i < j → IsGField G (V i)) →
      ∀ {ι : Type} [Fintype ι] {P : ι → Type} [∀ x, Fintype (P x)] (off : ι → Fin 4 → ℤ)
        (ord : ∀ x, P x → List (Fin 4)), 0 < Fintype.card ι → (∀ x, 0 < Fintype.card (P x)) →
      (∀ x, InM h (off x)) → (∀ x Γ, (ord x Γ).Perm [0, 1, 2, 3]) →
      (∀ i, i < j → ∀ ct : Bd (Lz h) j μ (i + 1),
        (V (i + 1)).val ⟨img h (base (i + 1)) (i + 1) ct.1.1, ct.1.2, true⟩ =
          avgB G (V i) (img h (base i) i ct.1.1) ct.1.2 (2 * h + 1) off ord) →
      ∀ α : ℝ, 0 ≤ α → α ≤ c₂ →
      (∀ μ' ν' z, PlaqIn (Reg h j μ 0 (base 0)) μ' ν' z →
        hs (((plaq (V 0) μ' ν' z : GLN) : Mat) - 1) ≤ α * ((((2 * h + 1 : ℕ) : ℝ) ^ 2)⁻¹) ^ j) →
      ∀ i, i < j → PlaqBound (V i) (Reg h j μ i (base i))
        (Real.sqrt N * (2 * α * ((((2 * h + 1 : ℕ) : ℝ)) ^ 2)⁻¹ ^ (j - i))) := by
  obtain ⟨c₂, hc₂, HII⟩ := regular_averages_ii G hG hN
  refine ⟨c₂, hc₂, ?_⟩
  intro h hh j μ nn _ hn base V hV ι _ P _ off ord hι hP hoff hord hrel α hα hαc hU i hi μ' ν' z hμν' hz
  obtain ⟨x, hxl, rfl, h0, h1, h2, h3⟩ := decode hh hi (hn i hi) (base i) hz
  have hcorn := corners_inB hμν' h0 h1 h2 h3
  set K : ℝ := ((2 * h + 1 : ℕ) : ℝ) ^ 2 with hK
  have hK1 : 1 ≤ K := by
    have : (1 : ℝ) ≤ ((2 * h + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 2 * h + 1)
    rw [hK]; nlinarith
  set α' : ℝ := α * K⁻¹ ^ (j - i) with hα'
  have hKi0 : 0 ≤ K⁻¹ := by positivity
  have hKi1 : K⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hK1
  have hα'0 : 0 ≤ α' := by positivity
  have hα'α : α' ≤ α := mul_le_of_le_one_right hα (pow_le_one₀ hKi0 hKi1)
  have hxm : ∀ m, m ≤ i → Lat (Lz h) m x := fun m hm => lat_mono hm hxl
  -- the tori of the levels below `i`
  have htor : ∀ l, l < i → 4 * h + 4 ≤ nn l := fun l hl => by
    have := torus_ge (by omega : l < j) (hn l (by omega))
    omega
  -- the averages, re-based at `x`
  have hrel' : ∀ l, l < i → ∀ (ρ : Fin 4) (x' : Fin 4 → ℤ), Lat (Lz h) (l + 1) x' →
      InR h i μ' ν' (l + 1) x' → InR h i μ' ν' (l + 1) (x' + Lz h ^ (l + 1) • Pi.single ρ 1) →
      V (l + 1) ρ (img h (img h (base (l + 1)) (l + 1) x) (l + 1) x') =
        avgB G (V l) (img h (img h (base l) l x) l x') ρ (2 * h + 1) off ord := by
    intro l hl ρ x' hx' hR1 hR2
    rw [img_img _ (hxm (l + 1) (by omega)) hx', img_img _ (hxm l (by omega)) (lat_le hx')]
    have hB1 := inB_of_inR hi.le (by omega) hμν' hxl hcorn hx' hR1
    have hB2 : InB (Lz h) j μ (x + x' + ev (Lz h) (l + 1) ρ) := by
      rw [ev_eq_smul', add_assoc]
      exact inB_of_inR hi.le (by omega) hμν' hxl hcorn (fun σ => dvd_add (hx' σ) (lat_smul _ σ)) hR2
    have := hrel l (by omega) ⟨(x + x', ρ), fun σ => dvd_add (hxm (l + 1) (by omega) σ) (hx' σ), hB1, hB2⟩
    rw [← this]
    rfl
  -- the plaquettes at the finest scale, re-based at `x`
  have hbase' : ∀ μ'' ν'' x', PlaqR h i μ' ν' 0 μ'' ν'' x' →
      hs (((plaq (V 0) μ'' ν'' (img h (img h (base 0) 0 x) 0 x') : GLN) : Mat) - 1) ≤ α' * K⁻¹ ^ i := by
    intro μ'' ν'' x' hp
    obtain ⟨hl0, r0, r1, r2, r3⟩ := hp
    rw [img_img _ (hxm 0 (by omega)) hl0]
    have hB : ∀ w, InR h i μ' ν' 0 w → InB (Lz h) j μ (x + w) := fun w hw =>
      inB_of_inR hi.le (by omega) hμν' hxl hcorn (lat_zero' w) hw
    have hPI : PlaqIn (Reg h j μ 0 (base 0)) μ'' ν'' (img h (base 0) 0 (x + x')) := by
      refine ⟨⟨x + x', lat_zero' _, hB x' r0, rfl⟩,
        ⟨x + x' + Lz h ^ 0 • Pi.single μ'' 1, lat_zero' _, ?_, img_unit _ (lat_zero' _) μ''⟩,
        ⟨x + x' + Lz h ^ 0 • Pi.single ν'' 1, lat_zero' _, ?_, img_unit _ (lat_zero' _) ν''⟩,
        ⟨x + x' + Lz h ^ 0 • Pi.single μ'' 1 + Lz h ^ 0 • Pi.single ν'' 1, lat_zero' _, ?_, ?_⟩⟩
      · rw [add_assoc]; exact hB _ r1
      · rw [add_assoc]; exact hB _ r2
      · have e : x + x' + Lz h ^ 0 • Pi.single μ'' 1 + Lz h ^ 0 • Pi.single ν'' 1 =
            x + (x' + Lz h ^ 0 • Pi.single μ'' 1 + Lz h ^ 0 • Pi.single ν'' 1) := by abel
        rw [e]; exact hB _ r3
      · rw [img_unit _ (lat_zero' _) μ'', img_unit _ (lat_zero' _) ν'']
    refine (hU μ'' ν'' _ hPI).trans (le_of_eq ?_)
    rw [hα', mul_assoc, ← pow_add, Nat.sub_add_cancel hi.le]
  obtain ⟨hfin, hfin2⟩ := HII h hh i μ' ν' hμν' nn htor (fun l => img h (base l) l x) V
    (fun l hl => hV l (by omega)) off ord hι hP hoff hord hrel' α' hα'0 (hα'α.trans hαc) hbase'
  have hf : hs (((plaq (V i) μ' ν' (img h (base i) i x) : GLN) : Mat) - 1) ≤ 2 * α' := hfin.trans hfin2
  calc ‖((plaq (V i) μ' ν' (img h (base i) i x) : GLN) : Mat) - 1‖
      ≤ Real.sqrt N * hs (((plaq (V i) μ' ν' (img h (base i) i x) : GLN) : Mat) - 1) :=
        opNorm_le_sqrt_mul_hs _
    _ ≤ Real.sqrt N * (2 * α') := mul_le_mul_of_nonneg_left hf (Real.sqrt_nonneg _)
    _ = Real.sqrt N * (2 * α * K⁻¹ ^ (j - i)) := by rw [hα']; ring

/-- **`cor:axial-straight`** with the plaquette hypothesis at the finest scale only, as in the core:
`|U(∂p) - id| ≤ α(η/a_j)²` for the plaquettes of `T^{(0)}` with corners in `𝖡`, `α ≤ c`, the axial gauge, and
the iterated averages `M^i(U)` on the bonds of `T^{(i)}` in `𝖡` (one family of paths `𝐆` at both ends, as in
`def:block-paths`); then `‖M^i(U)(b) - s(b)‖ ≤ 4C_axα`, `C_ax = 59√N`, for `0 ≤ i ≤ j` and the positive bonds
of `T^{(i)}` in `𝖡`. The tori `T^{(i)}`, `i < j`, have at least `3L^{j-i}` sites in each direction, as in the
core (`T^{(i)}` has `L^{m_T + k - i}` with `m_T ≥ 1`, `j ≤ k`). -/
theorem axial_regular (G : GaugeGroup N) (hG : IsClosed G.mats) (hN : 1 ≤ N) (h : ℕ) (hh : 1 ≤ h)
    {ι : Type} [Fintype ι] {P : ι → Type} [∀ x, Fintype (P x)] :
    ∃ c : ℝ, 0 < c ∧ ∀ (j : ℕ), 1 ≤ j → ∀ (μ : Fin 4) (nn : ℕ → ℕ) [∀ i, NeZero (nn i)],
      (∀ i, i < j → 3 * Lz h ^ (j - i) ≤ (nn i : ℤ)) →
      ∀ (base : ∀ i, Site (nn i)) (V : ∀ i, Config N (nn i)), (∀ i, i < j → IsGField G (V i)) →
      ∀ α : ℝ, 0 ≤ α → α ≤ c →
      (∀ μ' ν' z, PlaqIn (Reg h j μ 0 (base 0)) μ' ν' z →
        hs (((plaq (V 0) μ' ν' z : GLN) : Mat) - 1) ≤ α * ((((2 * h + 1 : ℕ) : ℝ) ^ 2)⁻¹) ^ j) →
      ∀ (off : ι → Fin 4 → ℤ) (ord : ∀ x, P x → List (Fin 4)), 0 < Fintype.card ι →
      (∀ x, 0 < Fintype.card (P x)) → (∀ x Γ, (ord x Γ).Perm [0, 1, 2, 3]) → (∀ x, InM h (off x)) →
      ∀ {k : ℕ} (_hk : 0 < k) (l : Fin k → List (Fin 4)), (∀ Γ, (l Γ).Perm [0, 1, 2, 3]) →
      ∀ x₀, l x₀ = [0, 1, 2, 3] →
      (∀ i, i < j → ∀ z, Lat (Lz h) (i + 1) z → InB (Lz h) j μ z → ∀ m, InM h m →
        IsMeanOf (fun Γ => (V i).hol (stair (img h (base i) i z) m (l Γ) 0)) x₀ 1) →
      (∀ i, i < j → ∀ ct : Bd (Lz h) j μ (i + 1),
        (V (i + 1)).val ⟨img h (base (i + 1)) (i + 1) ct.1.1, ct.1.2, true⟩ =
          avgB G (V i) (img h (base i) i ct.1.1) ct.1.2 (2 * h + 1) off ord) →
      ∀ i, i ≤ j → ∀ b : Bd (Lz h) j μ i,
        ‖(((V i).val ⟨img h (base i) i b.1.1, b.1.2, true⟩ : GLN) : Mat) -
          sval (Lz h) j μ (1 : Mat) (((V j).val ⟨img h (base j) j 0, μ, true⟩ : GLN) : Mat) i b‖ ≤
          4 * (59 * Real.sqrt N) * α := by
  obtain ⟨c₂, hc₂, HPL⟩ := plaq_levels G hG hN
  obtain ⟨c, hc, HAX⟩ := axial_straight_lattice (N := N) G hG hN h hh (ι := ι) (P := P) (P' := P)
  refine ⟨min c₂ (c / 2), lt_min hc₂ (by linarith), ?_⟩
  intro j hj μ nn _ hn base V hV α hα hαc hU off ord hι hP hord hoff k hk l hl x₀ hx₀ haxial hrel
  have hplaq := HPL h hh j μ nn hn base V hV off ord hι hP hoff hord hrel α hα
    (hαc.trans (min_le_left _ _)) hU
  have hn' : ∀ i, i < j → 4 * h + 2 ≤ nn i := fun i hi => by
    have := torus_ge hi (hn i hi)
    omega
  have hαc' : 2 * α ≤ c := by linarith [hαc.trans (min_le_right _ _)]
  exact HAX j hj μ nn hn' base V hV α hα hαc' hplaq off ord ord hord hord hoff hk l hl x₀ hx₀ haxial hrel

end AxialRegular

end CoreLean

end
