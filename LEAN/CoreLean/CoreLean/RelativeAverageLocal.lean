/-
`prop:relative-average`(i) of BALABAN_CORE.tex (`d8bdc4ac1777`), the locality of the transports and of the site
factors: the transports from `y` and the site factor at `y` depend only on the values of `𝐔` and of `aA` on the bonds
with both ends in `B(y)`.

* `stair_in_block`: the paths of `𝐆(y, x)` run through bonds with both ends in `B(y)` (from the proof of
  `StraightExtension.paths_in`).
* `trans_local`, `siteFactor_local`; `avgM_local` (`lem:average`(ii) for the average with `Log`); `relAvg_local`:
  `𝓜_𝐔(A)(c)` depends only on the bonds with both ends in `B(c₋) ∪ B(c₊)` (`bp_of_bm_plus`: `B(c₊)` lies in the
  region `Bp` of the bond).
-/
import CoreLean.RelativeAverageHolo
import CoreLean.AverageLocality

open Matrix NormedSpace

noncomputable section

namespace CoreLean
namespace RelativeAverage

open LatticePaths LatticeKappa RegularAverages BlockPaths AverageHolo MeanTransports AxialReference
  StraightExtension

variable {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "GLN" => (Matrix (Fin N) (Fin N) ℂ)ˣ

variable {n : ℕ} [NeZero n]

/-- The staircase paths from `y` to the points of `B(y)` run through bonds with both ends in `B(y)`. -/
lemma stair_in_block {y : Site n} {h : ℕ} (hn : 4 * h + 2 ≤ n) {c : Fin 4 → ℤ} (hc : InM h c)
    (l : List (Fin 4)) (hl : l.Nodup) : ∀ t ∈ stair y c l 0, Bm y h t.site ∧ Bm y h t.plus := by
  intro t ht
  obtain ⟨v, v', hv, hv', hs, hp⟩ := stair_ends y y 0 c (ofs_zero y).symm hc l hl t ht
  rw [zero_add] at hs hp
  exact ⟨hs ▸ bm_ofs hn hv, hp ▸ bm_ofs hn hv'⟩

/-- Agreement on the positive bonds of a block gives agreement on all its bonds. -/
lemma val_eq_of_pos {V V' : Config N n} {S : Site n → Prop}
    (hVV : ∀ μ z, S z → S (z + unit n μ) → V μ z = V' μ z) :
    ∀ t : Bond n, S t.site → S t.plus → V.val t = V'.val t := by
  rintro ⟨z, μ, s⟩ h1 h2
  cases s
  · simp only [Config.val, Bool.false_eq_true, ↓reduceIte]
    simp only [Bond.plus, Bool.false_eq_true, ↓reduceIte] at h1 h2
    rw [hVV μ (z - unit n μ) h2 (by rwa [sub_add_cancel])]
  · simp only [Config.val, ↓reduceIte]
    simp only [Bond.plus, ↓reduceIte] at h1 h2
    exact hVV μ z h1 h2

/-- **Locality of the transports**: `𝐔(y, x)` depends only on the values of `𝐔` on the bonds with both ends in
`B(y)`. -/
theorem trans_local {h : ℕ} (hn : 4 * h + 2 ≤ n) {y : Site n} {V V' : Config N n}
    (hVV : ∀ μ z, Bm y h z → Bm y h (z + unit n μ) → V μ z = V' μ z) (x : Pts h) :
    trans V y h x = trans V' y h x := by
  have hhol : ∀ Γ, holG V y h x Γ = holG V' y h x Γ := fun Γ =>
    hol_congr_of _ fun t ht => by
      have hnd : (ordG h x Γ).Nodup := (ordG_perm h x Γ).nodup_iff.2 (by decide)
      obtain ⟨h1, h2⟩ := stair_in_block hn (offP_inM h x) _ hnd t ht
      exact val_eq_of_pos hVV t h1 h2
  have he : expsG V y h x = expsG V' y h x := by
    funext i; simp only [expsG, hhol]
  simp only [trans, he, hhol]

/-- **Locality of the site factors**: `v_𝐔(A)(y)` depends only on the values of `𝐔` and `aA` on the bonds with
both ends in `B(y)`. -/
theorem siteFactor_local {h : ℕ} (hn : 4 * h + 2 ≤ n) {y : Site n} {V V' : Config N n}
    {B B' : Fin 4 → Site n → Mat}
    (hVV : ∀ μ z, Bm y h z → Bm y h (z + unit n μ) → V μ z = V' μ z ∧ B μ z = B' μ z) :
    siteFactor V B y h = siteFactor V' B' y h := by
  have h1 : ∀ x, trans V y h x = trans V' y h x := trans_local hn fun μ z hz hz' => (hVV μ z hz hz').1
  have h2 : ∀ x, trans (moveC V B) y h x = trans (moveC V' B') y h x := trans_local hn fun μ z hz hz' => by
    simp only [moveC, (hVV μ z hz hz').1, (hVV μ z hz hz').2]
  simp only [siteFactor, h1, h2]

/-- The bonds of a reversed path are the reverses of its bonds. -/
lemma mem_rv_iff {γ : List (Bond n)} {t : Bond n} : t ∈ rv γ ↔ t.rev ∈ γ := by
  simp only [rv, List.mem_reverse, List.mem_map]
  constructor
  · rintro ⟨b, hb, rfl⟩
    have : b.rev.rev = b := by cases b with | mk x μ s => cases s <;> simp [Bond.rev, Bond.plus]
    rwa [this]
  · intro ht
    refine ⟨t.rev, ht, ?_⟩
    cases t with | mk x μ s => cases s <;> simp [Bond.rev, Bond.plus]

/-- **Locality of the average** with `Log`: `M(𝐔)(c)` depends only on the values of `𝐔` on the bonds with both
ends in `B(c₋) ∪ B(c₊)` (`lem:average`(ii) for `avgLogU`). -/
theorem avgM_local {h : ℕ} (hn : 4 * h + 2 ≤ n) {y : Site n} {μ : Fin 4} {V V' : Config N n}
    (hVV : ∀ ν z, (Bm y h z ∨ Bp y h μ z) → (Bm y h (z + unit n ν) ∨ Bp y h μ (z + unit n ν)) →
      V ν z = V' ν z) :
    avgM V y μ h = avgM V' y μ h := by
  have hval := val_eq_of_pos (S := fun z => Bm y h z ∨ Bp y h μ z) hVV
  have hpath : ∀ γ : List (Bond n), (∀ t ∈ γ, (Bm y h t.site ∨ Bp y h μ t.site) ∧
      (Bm y h t.plus ∨ Bp y h μ t.plus)) → V.hol γ = V'.hol γ := fun γ hγ =>
    hol_congr_of γ fun t ht => hval t (hγ t ht).1 (hγ t ht).2
  have hrv : ∀ γ : List (Bond n), (∀ t ∈ γ, (Bm y h t.site ∨ Bp y h μ t.site) ∧
      (Bm y h t.plus ∨ Bp y h μ t.plus)) → ∀ t ∈ rv γ, (Bm y h t.site ∨ Bp y h μ t.site) ∧
      (Bm y h t.plus ∨ Bp y h μ t.plus) := fun γ hγ t ht => by
    have := hγ _ (mem_rv_iff.1 ht)
    rw [Bond.rev_site, Bond.rev_plus] at this
    exact ⟨this.2, this.1⟩
  have hseg : ∀ t ∈ segZ μ y ((2 * h + 1 : ℕ) : ℤ), (Bm y h t.site ∨ Bp y h μ t.site) ∧
      (Bm y h t.plus ∨ Bp y h μ t.plus) := by
    have := (paths_in (y := y) hn μ (inM_zero h) [] List.nodup_nil).2.2
    rwa [ofs_zero] at this
  have hloop : ∀ x Γ Γ', V.hol (lpath (ι := Pts h) (P := fun x => Ords (offP h x)) y μ (2 * h + 1) (offP h)
      (ordG h) x Γ Γ') = V'.hol (lpath (ι := Pts h) (P := fun x => Ords (offP h x)) y μ (2 * h + 1) (offP h)
      (ordG h) x Γ Γ') := fun x Γ Γ' => by
    refine hpath _ fun t ht => ?_
    have hnd : ∀ Γ : Ords (offP h x), (ordG h x Γ).Nodup := fun Γ => (ordG_perm h x Γ).nodup_iff.2 (by decide)
    simp only [lpath, List.mem_append] at ht
    rcases ht with ((ht | ht) | ht) | ht
    · exact (paths_in hn μ (offP_inM h x) _ (hnd Γ)).1 t ht
    · exact (paths_in hn μ (offP_inM h x) [] List.nodup_nil).2.2 t ht
    · exact hrv _ (paths_in hn μ (offP_inM h x) _ (hnd Γ')).2.1 t ht
    · exact hrv _ hseg t ht
  unfold avgM avgLogU betaLog
  simp only [hloop, hpath _ hseg]

/-- The block `B(c₊)` of the upper end lies in the region `Bp` of the bond. -/
lemma bp_of_bm_plus {h : ℕ} (hn : 4 * h + 2 ≤ n) {y : Site n} {μ : Fin 4} {z : Site n}
    (hz : Bm (cPlus y μ h) h z) : Bp y h μ z := by
  have e := ofs_rep (cPlus y μ h) h z
  rw [← e, cPlus, ofs_ofs]
  exact bp_ofs hn (inP_shift hz)

/-- **`prop:relative-average`(i), locality of `𝓜`**: `𝓜_𝐔(A)(c)` depends only on the values of `𝐔` and `aA` on
the bonds with both ends in `B(c₋) ∪ B(c₊)`. -/
theorem relAvg_local {h : ℕ} (hn : 4 * h + 2 ≤ n) {y : Site n} {μ : Fin 4} {V V' : Config N n}
    {B B' : Fin 4 → Site n → Mat}
    (hVV : ∀ ν z, (Bm y h z ∨ Bp y h μ z) → (Bm y h (z + unit n ν) ∨ Bp y h μ (z + unit n ν)) →
      V ν z = V' ν z ∧ B ν z = B' ν z) :
    relAvg V B y μ h = relAvg V' B' y μ h := by
  have h1 : siteFactor V B y h = siteFactor V' B' y h :=
    siteFactor_local hn fun ν z hz hz' => hVV ν z (Or.inl hz) (Or.inl hz')
  have h2 : siteFactor V B (cPlus y μ h) h = siteFactor V' B' (cPlus y μ h) h :=
    siteFactor_local hn fun ν z hz hz' =>
      hVV ν z (Or.inr (bp_of_bm_plus hn hz)) (Or.inr (bp_of_bm_plus hn hz'))
  have h3 : avgM V y μ h = avgM V' y μ h := avgM_local hn fun ν z hz hz' => (hVV ν z hz hz').1
  have h4 : avgM (moveC V B) y μ h = avgM (moveC V' B') y μ h := avgM_local hn fun ν z hz hz' => by
    simp only [moveC, (hVV ν z hz hz').1, (hVV ν z hz hz').2]
  simp only [relAvg, h1, h2, h3, h4]

end RelativeAverage
end CoreLean

end
