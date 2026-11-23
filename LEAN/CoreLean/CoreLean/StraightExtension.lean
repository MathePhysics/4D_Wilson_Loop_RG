/-
`lem:chain-transport`(iii) of BALABAN_CORE.tex (`0c2967992d08`): the averages of a straight extension, in the
two blocks `𝖡 = B^j(c'₋) ∪ B^j(c'₊)` of a bond `c'` of `T^{(j)}`.

The straight extension `Q^{s*}_jV` (`def:cube-minimiser`(i)) is, on the positive bonds of `T^{(0)}` in `𝖡`,
`id` if both ends lie in one block and `V(c')` if the bond runs from `B^j(c'₋)` to `B^j(c'₊)`: the function
`sval` of `BoxGeometry` at the order `0`. The proof of the core is an induction: a field of `T^{(i)}` of this
kind (`id` inside the blocks of the order `j - i`, `V(c')` between them) has an average of the same kind on
`T^{(i+1)}`.
* `val_agree`, `hol_agree`: a field equal to `V₀` on the bonds inside `B(c̃₋) ∪ B(c̃₊)` has the holonomies of
  `V₀` along the paths in it; so its average on `c̃` is that of `V₀`, which is `W` (`avg_V0`).
* `level_step`: a block field of the order `j - i` agrees with `V₀` for every bond `c̃` of `T^{(i+1)}` in `𝖡`,
  with `W = s(c̃)`, by `sval_one` and `sval_between`.
* `straight_extension_averages`: `M^i(Q^{s*}_jV)(b) = s(b)` for `0 ≤ i ≤ j` and the positive bonds `b` of
  `T^{(i)}` in `𝖡`: `V(⟨y₋, y₊⟩)` between the blocks, `id` inside one.
-/
import CoreLean.AxialRegular

open Matrix NormedSpace
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace CoreLean

namespace StraightExtension

open LatticePaths LatticeKappa BoxGeometry AxialStraightLattice AxialReference RegularAverages AxialRegular

set_option linter.unusedSectionVars false

variable {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "GLN" => (Matrix (Fin N) (Fin N) ℂ)ˣ

variable {n : ℕ} [NeZero n]

lemma ofs_rep (y : Site n) (h : ℕ) (x : Site n) : ofs y (rep y h x) = x := by
  funext σ
  simp only [ofs, Pi.add_apply, rep_cast]
  ring

lemma rep_bounds {y : Site n} {h : ℕ} {μ : Fin 4} {w : Site n} (hw : Bm y h w ∨ Bp y h μ w) (σ : Fin 4) :
    -(h : ℤ) ≤ rep y h w σ ∧ rep y h w σ ≤ 3 * h + 1 := by
  rcases hw with hw | hw
  · have := hw σ; constructor <;> omega
  · by_cases hσ : σ = μ
    · have := (hw σ).2 hσ; constructor <;> omega
    · have := (hw σ).1 hσ; constructor <;> omega

/-- The offset of the neighbour, for `4h + 4 ≤ n`. -/
lemma rep_succ {y : Site n} {h : ℕ} (hn : 4 * h + 4 ≤ n) {μ : Fin 4} {w : Site n}
    (hw : Bm y h w ∨ Bp y h μ w) (σ : Fin 4) :
    rep y h (w + unit n σ) = rep y h w + Pi.single σ 1 := by
  funext τ
  symm
  have hb := rep_bounds hw τ
  have hs : (Pi.single σ (1 : ℤ) : Fin 4 → ℤ) τ = 0 ∨ (Pi.single σ (1 : ℤ) : Fin 4 → ℤ) τ = 1 := by
    by_cases h' : τ = σ
    · subst h'; simp
    · simp [Pi.single_eq_of_ne h']
  refine rep_unique y h ?_ ?_ ?_
  · simp only [Pi.add_apply]; rcases hs with e | e <;> rw [e] <;> omega
  · simp only [Pi.add_apply]; rcases hs with e | e <;> rw [e] <;> omega
  · simp only [Pi.add_apply]
    push_cast
    rw [rep_cast]
    by_cases h' : τ = σ
    · subst h'; simp [unit]; ring
    · simp [unit, Pi.single_eq_of_ne h']

/-! ### Fields equal to `V₀` inside the two blocks -/

lemma val_agree {V : Config N n} {y : Site n} {h : ℕ} {μ : Fin 4} {W : GLN}
    (hV : ∀ (w : Site n) σ, (Bm y h w ∨ Bp y h μ w) → (Bm y h (w + unit n σ) ∨ Bp y h μ (w + unit n σ)) →
      V σ w = V0 y h μ W σ w)
    (t : Bond n) (hs : Bm y h t.site ∨ Bp y h μ t.site) (hp : Bm y h t.plus ∨ Bp y h μ t.plus) :
    V.val t = (V0 y h μ W).val t := by
  obtain ⟨w, σ, s⟩ := t
  cases s
  · simp only [Bond.plus, Bool.false_eq_true, ↓reduceIte] at hs hp
    simp only [Config.val, Bool.false_eq_true, ↓reduceIte]
    rw [hV (w - unit n σ) σ hp (by rwa [sub_add_cancel])]
  · simp only [Bond.plus, ↓reduceIte] at hs hp
    simp only [Config.val, ↓reduceIte]
    exact hV w σ hs hp

lemma hol_agree {V : Config N n} {y : Site n} {h : ℕ} {μ : Fin 4} {W : GLN}
    (hV : ∀ (w : Site n) σ, (Bm y h w ∨ Bp y h μ w) → (Bm y h (w + unit n σ) ∨ Bp y h μ (w + unit n σ)) →
      V σ w = V0 y h μ W σ w) :
    ∀ γ : List (Bond n), (∀ t ∈ γ, (Bm y h t.site ∨ Bp y h μ t.site) ∧ (Bm y h t.plus ∨ Bp y h μ t.plus)) →
      V.hol γ = (V0 y h μ W).hol γ
  | [], _ => rfl
  | t :: γ, hγ => by
    rw [hol_cons, hol_cons, val_agree hV t (hγ t (by simp)).1 (hγ t (by simp)).2,
      hol_agree hV γ fun t' ht' => hγ t' (by simp [ht'])]

/-- The sites `y + c + ie_μ`, `|c| ≤ h`, `0 ≤ i ≤ L`, lie in `B(c̃₋) ∪ B(c̃₊)`. -/
lemma box_pt {y : Site n} {h : ℕ} (hn : 4 * h + 2 ≤ n) (μ : Fin 4) {c : Fin 4 → ℤ} (hc : InM h c)
    {i : ℕ} (hi : i ≤ 2 * h + 1) :
    Bm y h (ofs y (c + Pi.single μ (i : ℤ))) ∨ Bp y h μ (ofs y (c + Pi.single μ (i : ℤ))) := by
  by_cases hle : c μ + i ≤ h
  · left
    refine bm_ofs hn fun σ => ?_
    by_cases hσ : σ = μ
    · subst hσ; have := hc σ; simp only [Pi.add_apply, Pi.single_eq_same]; constructor <;> omega
    · simpa [Pi.single_eq_of_ne hσ] using hc σ
  · right
    refine bp_ofs hn fun σ => ⟨fun hσ => by simpa [Pi.single_eq_of_ne hσ] using hc σ, fun hσ => ?_⟩
    subst hσ
    have := hc σ
    simp only [Pi.add_apply, Pi.single_eq_same]
    constructor <;> omega

/-- The bonds of all paths of the average on `c̃ = (y, y + Le_μ)` have their ends in `B(c̃₋) ∪ B(c̃₊)`. -/
lemma paths_in {y : Site n} {h : ℕ} (hn : 4 * h + 2 ≤ n) (μ : Fin 4) {c : Fin 4 → ℤ} (hc : InM h c)
    (l : List (Fin 4)) (hl : l.Nodup) :
    (∀ t ∈ stair y c l 0, (Bm y h t.site ∨ Bp y h μ t.site) ∧ (Bm y h t.plus ∨ Bp y h μ t.plus)) ∧
    (∀ t ∈ stair (ofs y (Pi.single μ ((2 * h + 1 : ℕ) : ℤ))) c l 0,
      (Bm y h t.site ∨ Bp y h μ t.site) ∧ (Bm y h t.plus ∨ Bp y h μ t.plus)) ∧
    (∀ t ∈ segZ μ (ofs y c) ((2 * h + 1 : ℕ) : ℤ),
      (Bm y h t.site ∨ Bp y h μ t.site) ∧ (Bm y h t.plus ∨ Bp y h μ t.plus)) := by
  refine ⟨fun t ht => ?_, fun t ht => ?_, fun t ht => ?_⟩
  · obtain ⟨v, v', hv, hv', hs, hp⟩ := stair_ends y y 0 c (ofs_zero y).symm hc l hl t ht
    rw [zero_add] at hs hp
    exact ⟨hs ▸ Or.inl (bm_ofs hn hv), hp ▸ Or.inl (bm_ofs hn hv')⟩
  · obtain ⟨v, v', hv, hv', hs, hp⟩ := stair_ends y _ _ c rfl hc l hl t ht
    exact ⟨hs ▸ Or.inr (bp_ofs hn (inP_shift hv)), hp ▸ Or.inr (bp_ofs hn (inP_shift hv'))⟩
  · obtain ⟨i, hi, hs, hp⟩ := seg_ends y _ c rfl μ (2 * h + 1) t ht
    exact ⟨hs ▸ box_pt hn μ hc hi.le, hp ▸ box_pt hn μ hc hi⟩

/-! ### One level -/

/-- A block field of the order `j - i` on the bonds of `T^{(i)}` in `𝖡` has, on every bond `c̃` of
`T^{(i+1)}` in `𝖡`, the average `s(c̃)`. -/
theorem level_step (G : GaugeGroup N) {h j i : ℕ} (hij : i < j) {μ : Fin 4} {nn : ℕ → ℕ}
    [∀ i, NeZero (nn i)] (hn : 4 * h + 4 ≤ nn i) (base : ∀ i, Site (nn i)) (V : ∀ i, Config N (nn i))
    (W : GLN) {ι : Type*} [Fintype ι] {P P' : ι → Type*} [∀ x, Fintype (P x)] [∀ x, Fintype (P' x)]
    (off : ι → Fin 4 → ℤ) (ord : ∀ x, P x → List (Fin 4)) (ord' : ∀ x, P' x → List (Fin 4))
    (hord : ∀ x Γ, (ord x Γ).Perm [0, 1, 2, 3]) (hord' : ∀ x Γ', (ord' x Γ').Perm [0, 1, 2, 3])
    (hoff : ∀ x, InM h (off x))
    (hcl : ∀ b : Bd (Lz h) j μ i,
      (V i).val ⟨img h (base i) i b.1.1, b.1.2, true⟩ = sval (Lz h) j μ (1 : GLN) W i b)
    (ct : Bd (Lz h) j μ (i + 1)) :
    Average.avg G.inChart G.chartLog
        (fun x Γ => (V i).hol (stair (img h (base i) i ct.1.1) (off x) (ord x Γ) 0))
        (fun x => (V i).hol (segZ ct.1.2 (ofs (img h (base i) i ct.1.1) (off x)) ((2 * h + 1 : ℕ) : ℤ)))
        (fun x Γ' => (V i).hol (stair (ofs (img h (base i) i ct.1.1)
          (Pi.single ct.1.2 ((2 * h + 1 : ℕ) : ℤ) : Fin 4 → ℤ)) (off x) (ord' x Γ') 0))
        ((V i).hol (segZ ct.1.2 (img h (base i) i ct.1.1) ((2 * h + 1 : ℕ) : ℤ))) =
      sval (Lz h) j μ (1 : GLN) W (i + 1) ct := by
  have hLo := Lz_odd h
  have hL1 := Lz_one h
  have hn2 : 4 * h + 2 ≤ nn i := by omega
  set z := ct.1.1 with hzd
  set ρ := ct.1.2 with hρd
  set y := img h (base i) i z with hyd
  set W' := sval (Lz h) j μ (1 : GLN) W (i + 1) ct with hW'
  have hz : Lat (Lz h) (i + 1) z := ct.2.1
  have hzi : Lat (Lz h) i z := lat_le hz
  have hev : ev (Lz h) (i + 1) ρ = Lz h ^ i • (Pi.single ρ ((2 * h + 1 : ℕ) : ℤ) : Fin 4 → ℤ) := by
    rw [shift_eq, ev_eq_smul']
  -- the blocks of `c̃` from the offsets
  have blkM : ∀ v, InM h v → Blk (Lz h) (i + 1) z (z + Lz h ^ i • v) := fun v hv => blk_of_inM z hv
  have blkP : ∀ v, InP h ρ v → Blk (Lz h) (i + 1) (z + ev (Lz h) (i + 1) ρ) (z + Lz h ^ i • v) := by
    intro v hv
    have hm : InM h (v - (Pi.single ρ ((2 * h + 1 : ℕ) : ℤ) : Fin 4 → ℤ)) := fun σ => by
      by_cases hσ : σ = ρ
      · rw [hσ]; have := (hv ρ).2 rfl; simp only [Pi.sub_apply, Pi.single_eq_same]; push_cast
        constructor <;> omega
      · simpa [Pi.single_eq_of_ne hσ] using (hv σ).1 hσ
    have := blk_of_inM (z + ev (Lz h) (i + 1) ρ) (i := i) hm
    convert this using 1
    rw [hev, smul_sub]; abel
  -- the block field agrees with `V₀`
  have hV : ∀ (w : Site (nn i)) σ, (Bm y h w ∨ Bp y h ρ w) →
      (Bm y h (w + unit (nn i) σ) ∨ Bp y h ρ (w + unit (nn i) σ)) → (V i) σ w = V0 y h ρ W' σ w := by
    intro w σ hw hw'
    set v := rep y h w with hvd
    have hv' : rep y h (w + unit (nn i) σ) = v + Pi.single σ 1 := rep_succ hn hw σ
    have hwv : w = img h (base i) i (z + Lz h ^ i • v) := by
      rw [← img_add (base i) hzi v, ← hyd, ofs_rep]
    have inMP : ∀ (u : Site (nn i)), (Bm y h u ∨ Bp y h ρ u) →
        (Blk (Lz h) (i + 1) z (z + Lz h ^ i • rep y h u) ∨
          Blk (Lz h) (i + 1) (z + ev (Lz h) (i + 1) ρ) (z + Lz h ^ i • rep y h u)) := fun u hu => by
      rcases hu with hu | hu
      · exact Or.inl (blkM _ hu)
      · exact Or.inr (blkP _ hu)
    have hp1 : z + Lz h ^ i • v + ev (Lz h) i σ = z + Lz h ^ i • rep y h (w + unit (nn i) σ) := by
      rw [hv', smul_add, ev_eq_smul', add_assoc]
    have hB0 : InB (Lz h) j μ (z + Lz h ^ i • v) := blocks_sub_B hLo hL1 hij ct _ (inMP w hw)
    have hB1 : InB (Lz h) j μ (z + Lz h ^ i • v + ev (Lz h) i σ) := by
      rw [hp1]; exact blocks_sub_B hLo hL1 hij ct _ (inMP _ hw')
    let b : Bd (Lz h) j μ i := ⟨(z + Lz h ^ i • v, σ), fun τ => dvd_add (hzi τ) (lat_smul v τ), hB0, hB1⟩
    have hb := hcl b
    have hval : (V i).val ⟨img h (base i) i b.1.1, b.1.2, true⟩ = (V i) σ w := by
      rw [hwv]; rfl
    rw [← hval, hb]
    simp only [V0]
    by_cases hc : σ = ρ ∧ Bm y h w ∧ Bp y h ρ (w + unit (nn i) ρ)
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hc)]
      obtain ⟨hσ, hm, hp⟩ := hc
      subst hσ
      refine sval_between hLo hL1 (1 : GLN) W hij b ct ⟨blkM v hm, ?_⟩
      show Blk (Lz h) (i + 1) (z + ev (Lz h) (i + 1) ρ) (z + Lz h ^ i • v + ev (Lz h) i ρ)
      rw [hp1]; exact blkP _ hp
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hc)]
      refine sval_one hLo hL1 (1 : GLN) W hij b ct ?_
      show ∃ z', (z' = z ∨ z' = z + ev (Lz h) (i + 1) ρ) ∧ Blk (Lz h) (i + 1) z' (z + Lz h ^ i • v) ∧
        Blk (Lz h) (i + 1) z' (z + Lz h ^ i • v + ev (Lz h) i σ)
      rw [hp1]
      have kM : ∀ u, Bm y h u → rep y h u ρ ≤ h := fun u hu => (hu ρ).2
      have kP : ∀ u, Bp y h ρ u → (h : ℤ) + 1 ≤ rep y h u ρ := fun u hu => ((hu ρ).2 rfl).1
      have hstep : rep y h (w + unit (nn i) σ) ρ = v ρ + (Pi.single σ (1 : ℤ) : Fin 4 → ℤ) ρ := by
        rw [hv']; rfl
      rcases hw with hm | hp <;> rcases hw' with hm' | hp'
      · exact ⟨z, Or.inl rfl, blkM _ hm, blkM _ hm'⟩
      · exfalso
        have e1 : v ρ ≤ h := kM w hm
        have e2 := kP _ hp'
        by_cases hσ : σ = ρ
        · subst hσ; exact hc ⟨rfl, hm, hp'⟩
        · rw [hstep, Pi.single_eq_of_ne (Ne.symm hσ)] at e2; omega
      · exfalso
        have e1 : (h : ℤ) + 1 ≤ v ρ := kP w hp
        have e2 := kM _ hm'
        rw [hstep] at e2
        have : 0 ≤ (Pi.single σ (1 : ℤ) : Fin 4 → ℤ) ρ := by
          by_cases hσ : ρ = σ
          · subst hσ; simp
          · simp [Pi.single_eq_of_ne hσ]
        omega
      · exact ⟨z + ev (Lz h) (i + 1) ρ, Or.inr rfl, blkP _ hp, blkP _ hp'⟩
  -- the average is that of `V₀`
  have hnd : ∀ x Γ, (ord x Γ).Nodup := fun x Γ => (hord x Γ).nodup_iff.2 (by decide)
  have hnd' : ∀ x Γ', (ord' x Γ').Nodup := fun x Γ' => (hord' x Γ').nodup_iff.2 (by decide)
  have e1 : ∀ x Γ, (V i).hol (stair y (off x) (ord x Γ) 0) = (V0 y h ρ W').hol (stair y (off x) (ord x Γ) 0) :=
    fun x Γ => hol_agree hV _ (paths_in hn2 ρ (hoff x) _ (hnd x Γ)).1
  have e2 : ∀ x, (V i).hol (segZ ρ (ofs y (off x)) ((2 * h + 1 : ℕ) : ℤ)) =
      (V0 y h ρ W').hol (segZ ρ (ofs y (off x)) ((2 * h + 1 : ℕ) : ℤ)) :=
    fun x => hol_agree hV _ (paths_in hn2 ρ (hoff x) [] List.nodup_nil).2.2
  have e3 : ∀ x Γ', (V i).hol (stair (ofs y (Pi.single ρ ((2 * h + 1 : ℕ) : ℤ) : Fin 4 → ℤ)) (off x)
      (ord' x Γ') 0) = (V0 y h ρ W').hol (stair (ofs y (Pi.single ρ ((2 * h + 1 : ℕ) : ℤ) : Fin 4 → ℤ))
      (off x) (ord' x Γ') 0) :=
    fun x Γ' => hol_agree hV _ (paths_in hn2 ρ (hoff x) _ (hnd' x Γ')).2.1
  have e4 : (V i).hol (segZ ρ y ((2 * h + 1 : ℕ) : ℤ)) = (V0 y h ρ W').hol (segZ ρ y ((2 * h + 1 : ℕ) : ℤ)) := by
    have := (paths_in (y := y) hn2 ρ (inM_zero h) [] List.nodup_nil).2.2
    rw [ofs_zero] at this
    exact hol_agree hV _ this
  simp only [e1, e2, e3, e4]
  exact (avg_V0 hn2 G off hoff ord ord' hnd hnd').2

/-- **`lem:chain-transport`(iii)** in `𝖡`: if `V_0 = Q^{s*}_jV` on the positive bonds of `T^{(0)}` in `𝖡`
(`id` inside one block, `W = V(c')` from `B^j(c'₋)` to `B^j(c'₊)`), and `V_{i+1} = M(V_i)` on the bonds of
`T^{(i+1)}` in `𝖡`, then `M^i(Q^{s*}_jV)(b) = s(b)` for `0 ≤ i ≤ j` and every positive bond `b` of `T^{(i)}` in
`𝖡`: `V(c')` if `b` runs from `B^j(c'₋)` to `B^j(c'₊)`, `id` if both ends lie in one of the two blocks. The
tori `T^{(i)}`, `i < j`, have at least `4h + 4` sites in each direction. -/
theorem straight_extension_averages (G : GaugeGroup N) {h j : ℕ} (μ : Fin 4) (nn : ℕ → ℕ)
    [∀ i, NeZero (nn i)] (hn : ∀ i, i < j → 4 * h + 4 ≤ nn i) (base : ∀ i, Site (nn i))
    (V : ∀ i, Config N (nn i)) (W : GLN) {ι : Type*} [Fintype ι] {P P' : ι → Type*}
    [∀ x, Fintype (P x)] [∀ x, Fintype (P' x)] (off : ι → Fin 4 → ℤ) (ord : ∀ x, P x → List (Fin 4))
    (ord' : ∀ x, P' x → List (Fin 4)) (hord : ∀ x Γ, (ord x Γ).Perm [0, 1, 2, 3])
    (hord' : ∀ x Γ', (ord' x Γ').Perm [0, 1, 2, 3]) (hoff : ∀ x, InM h (off x))
    (h0 : ∀ b : Bd (Lz h) j μ 0,
      (V 0).val ⟨img h (base 0) 0 b.1.1, b.1.2, true⟩ = sval (Lz h) j μ (1 : GLN) W 0 b)
    (hrel : ∀ i, i < j → ∀ ct : Bd (Lz h) j μ (i + 1),
      (V (i + 1)).val ⟨img h (base (i + 1)) (i + 1) ct.1.1, ct.1.2, true⟩ =
        Average.avg G.inChart G.chartLog
          (fun x Γ => (V i).hol (stair (img h (base i) i ct.1.1) (off x) (ord x Γ) 0))
          (fun x => (V i).hol
            (segZ ct.1.2 (ofs (img h (base i) i ct.1.1) (off x)) ((2 * h + 1 : ℕ) : ℤ)))
          (fun x Γ' => (V i).hol (stair (ofs (img h (base i) i ct.1.1)
            (Pi.single ct.1.2 ((2 * h + 1 : ℕ) : ℤ) : Fin 4 → ℤ)) (off x) (ord' x Γ') 0))
          ((V i).hol (segZ ct.1.2 (img h (base i) i ct.1.1) ((2 * h + 1 : ℕ) : ℤ)))) :
    ∀ i, i ≤ j → ∀ b : Bd (Lz h) j μ i,
      (V i).val ⟨img h (base i) i b.1.1, b.1.2, true⟩ = sval (Lz h) j μ (1 : GLN) W i b := by
  intro i
  induction i with
  | zero => exact fun _ => h0
  | succ i ih =>
    intro hi b
    rw [hrel i hi b]
    exact level_step G hi (hn i hi) base V W off ord ord' hord hord' hoff (ih (Nat.le_of_succ_le hi)) b

end StraightExtension

end CoreLean

end
