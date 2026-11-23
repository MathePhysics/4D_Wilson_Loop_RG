/-
`lem:average`(ii) of BALABAN_CORE.tex (`f1da63a7f109`), locality, on the lattice: `M(U)(c)` depends only on
the values of `U` on the bonds with both ends in `B(c₋) ∪ B(c₊)`.

* `hol_congr_of`: two configurations equal on the bonds of a path have the same holonomy along it.
* `average_locality`: all the paths of the average on `c = (y, y + Le_μ)` run through bonds with both ends in
  `B(c₋) ∪ B(c₊)` (`StraightExtension.paths_in`), so two configurations which agree on these bonds have the
  same average.
-/
import CoreLean.StraightExtension

open Matrix NormedSpace

noncomputable section

namespace CoreLean

namespace StraightExtension

open LatticePaths LatticeKappa AxialReference RegularAverages

variable {N : ℕ}

local notation "GLN" => (Matrix (Fin N) (Fin N) ℂ)ˣ

variable {n : ℕ} [NeZero n]

lemma hol_congr_of {U U' : Config N n} :
    ∀ γ : List (Bond n), (∀ t ∈ γ, U.val t = U'.val t) → U.hol γ = U'.hol γ
  | [], _ => rfl
  | t :: γ, h => by
    rw [hol_cons, hol_cons, h t (by simp), hol_congr_of γ fun t' ht' => h t' (by simp [ht'])]

/-- **`lem:average`(ii)** on the lattice: the average on `c = (y, y + Le_μ)` depends only on the values on the
bonds with both ends in `B(c₋) ∪ B(c₊)`. -/
theorem average_locality (G : GaugeGroup N) {h : ℕ} (hn : 4 * h + 2 ≤ n) (y : Site n) (μ : Fin 4)
    {ι : Type*} [Fintype ι] {P : ι → Type*} [∀ x, Fintype (P x)] (off : ι → Fin 4 → ℤ)
    (ord : ∀ x, P x → List (Fin 4)) (hoff : ∀ x, InM h (off x))
    (hord : ∀ x Γ, (ord x Γ).Perm [0, 1, 2, 3]) (U U' : Config N n)
    (hUU : ∀ t : Bond n, (Bm y h t.site ∨ Bp y h μ t.site) → (Bm y h t.plus ∨ Bp y h μ t.plus) →
      U.val t = U'.val t) :
    avgB G U y μ (2 * h + 1) off ord = avgB G U' y μ (2 * h + 1) off ord := by
  have hnd : ∀ x Γ, (ord x Γ).Nodup := fun x Γ => (hord x Γ).nodup_iff.2 (by decide)
  have hpath : ∀ γ : List (Bond n), (∀ t ∈ γ, (Bm y h t.site ∨ Bp y h μ t.site) ∧
      (Bm y h t.plus ∨ Bp y h μ t.plus)) → U.hol γ = U'.hol γ := fun γ hγ =>
    hol_congr_of γ fun t ht => hUU t (hγ t ht).1 (hγ t ht).2
  have e1 : ∀ x Γ, U.hol (stair y (off x) (ord x Γ) 0) = U'.hol (stair y (off x) (ord x Γ) 0) :=
    fun x Γ => hpath _ (paths_in hn μ (hoff x) _ (hnd x Γ)).1
  have e2 : ∀ x, U.hol (segZ μ (ofs y (off x)) ((2 * h + 1 : ℕ) : ℤ)) =
      U'.hol (segZ μ (ofs y (off x)) ((2 * h + 1 : ℕ) : ℤ)) :=
    fun x => hpath _ (paths_in hn μ (hoff x) [] List.nodup_nil).2.2
  have e3 : ∀ x Γ', U.hol (stair (ofs y (Pi.single μ ((2 * h + 1 : ℕ) : ℤ) : Fin 4 → ℤ)) (off x)
      (ord x Γ') 0) = U'.hol (stair (ofs y (Pi.single μ ((2 * h + 1 : ℕ) : ℤ) : Fin 4 → ℤ))
      (off x) (ord x Γ') 0) :=
    fun x Γ' => hpath _ (paths_in hn μ (hoff x) _ (hnd x Γ')).2.1
  have e4 : U.hol (segZ μ y ((2 * h + 1 : ℕ) : ℤ)) = U'.hol (segZ μ y ((2 * h + 1 : ℕ) : ℤ)) := by
    have := (paths_in (y := y) hn μ (inM_zero h) [] List.nodup_nil).2.2
    rw [ofs_zero] at this
    exact hpath _ this
  unfold avgB
  simp only [e1, e2, e3, e4]

/-! ### Translations -/

/-- The translate `(θU)(b) = U(θ⁻¹b)` by `t`. -/
def translate (U : Config N n) (t : Site n) : Config N n := fun μ z => U μ (z - t)

omit [NeZero n] in
lemma val_translate (U : Config N n) (t : Site n) (b : Bond n) :
    (translate U t).val (b.shift t) = U.val b := by
  obtain ⟨z, μ, s⟩ := b
  cases s
  · simp only [Config.val, Bond.shift, translate, Bool.false_eq_true, ↓reduceIte]
    rw [show z + t - unit n μ - t = z - unit n μ by abel]
  · simp only [Config.val, Bond.shift, translate, ↓reduceIte, add_sub_cancel_right]

lemma hol_translate (U : Config N n) (t : Site n) :
    ∀ γ : List (Bond n), (translate U t).hol (γ.map (Bond.shift · t)) = U.hol γ
  | [] => rfl
  | b :: γ => by
    rw [List.map_cons, hol_cons, hol_cons, val_translate, hol_translate U t γ]

omit [NeZero n] in
lemma ofs_add_base (y t : Site n) (m : Fin 4 → ℤ) : ofs (y + t) m = ofs y m + t := by
  unfold ofs; abel

lemma stair_translate (y t : Site n) (m : Fin 4 → ℤ) :
    ∀ (l : List (Fin 4)) (o : Fin 4 → ℤ), stair (y + t) m l o = (stair y m l o).map (Bond.shift · t)
  | [], _ => rfl
  | μ :: l, o => by
    simp only [stair, List.map_append]
    rw [ofs_add_base, ← map_shift_segZ, stair_translate y t m l]

/-- **`lem:average`(iv)** for the translations: `M(θU)(θc) = M(U)(c)` for the translation `θ` by `t`. -/
theorem average_translate (G : GaugeGroup N) (U : Config N n) (t y : Site n) (μ : Fin 4) (L : ℕ)
    {ι : Type*} [Fintype ι] {P : ι → Type*} [∀ x, Fintype (P x)] (off : ι → Fin 4 → ℤ)
    (ord : ∀ x, P x → List (Fin 4)) :
    avgB G (translate U t) (y + t) μ L off ord = avgB G U y μ L off ord := by
  unfold avgB
  simp only [stair_translate, ofs_add_base, ← map_shift_segZ, hol_translate]

end StraightExtension

end CoreLean

end
