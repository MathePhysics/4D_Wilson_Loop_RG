/-
`lem:average`(iv) of BALABAN_CORE.tex (`29033ef0c1e5`) for the family `𝐆(y, x)` of `def:block-paths`, for the
average with the chart (real fields) and for the extension with `Log` (complex `B`, `lem:average`(vi)).

Both averages are `Average.avg inN log` applied to the transports along the four kinds of paths of the bond
(`avgZ`): the chart average `avgB` is `avgZ G.inChart G.chartLog`, the extension `avgLogZ` is
`avgZ (fun _ => True) Log`. So every statement is proved once, for all `inN` and `log`.

* `avgZ_congr`, `avgZ_translate`, `avgZ_perm`, `avgZ_refl`: the symmetries for arbitrary families.
* `avgZ_reindex`: two families give the same average when a bijection of the points and bijections of the
  paths match the offsets and the paths (as lists of bonds, not as orderings: the coordinates with `n_μ = 0`
  contribute no bonds, and their place in an ordering does not matter).
* `avgZ_neg`: the average at the bond `(y + Le_κ, y)` of length `-L` is the inverse of the average at
  `(y, y + Le_κ)`, for a logarithm with the properties of `lem:chart`(i) (`Average.LogInput`).
* `avgG`: the average for the family `𝐆` (`BlockPaths`: points `Pts h`, offsets `offP`, orderings `Ords`,
  `ordG`). A permutation `σ` maps the points by `x ↦ x ∘ σ⁻¹` (`ePerm`) and the orderings by `Γ ↦ σΓ`
  (`fPerm`); a reflection maps the points by `n_μ ↦ -n_μ` (`eRefl`) and keeps the orderings (`fRefl`).
  `avgG_translate`, `avgG_perm`, `avgG_refl`: `M(θV)(θc) = M(V)(c)` for the family `𝐆` at both bonds, and
  `loopsG_*`: the loops of `θc` of `θV` are those of `c` of `V`.
* `avgB_perm_G`, `avgB_refl_G`, `avgB_refl_self_G`: the chart average for `G`-valued fields; for the reflection
  in the direction of the bond, `M(RU)(c') = M(U)(c)⁻¹` with `c' = (Ry - Le_μ, Ry)` the positive bond of `Rc`.
* `average_refl_self_complex`: the same for `𝐔_B`, `B` complex, as in `average_analytic`.
-/
import CoreLean.AverageSymmetry
import CoreLean.BlockPaths

open Matrix NormedSpace
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace CoreLean

namespace AverageHolo

open LatticePaths LatticeKappa RegularAverages BlockPaths

set_option linter.unusedSectionVars false

variable {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "GLN" => (Matrix (Fin N) (Fin N) ℂ)ˣ

variable {n : ℕ} [NeZero n]

/-! ### The average for any logarithm -/

section Generic

variable {ι : Type*} [Fintype ι] {P : ι → Type*} [∀ x, Fintype (P x)]

/-- The average `M(V)(c)`, `c = (y, y + Le_κ)`, `L ∈ ℤ`, with the logarithm `log` on the set `inN`. -/
def avgZ (inN : GLN → Prop) (log : GLN → Mat) (V : Config N n) (y : Site n) (κ : Fin 4) (L : ℤ)
    (off : ι → Fin 4 → ℤ) (ord : ∀ x, P x → List (Fin 4)) : GLN :=
  Average.avg inN log (fun x Γ => V.hol (stair y (off x) (ord x Γ) 0))
    (fun x => V.hol (segZ κ (ofs y (off x)) L))
    (fun x Γ' => V.hol (stair (ofs y (Pi.single κ L)) (off x) (ord x Γ') 0)) (V.hol (segZ κ y L))

/-- The chart average is `avgZ` with the chart. -/
lemma avgB_eq_avgZ (G : GaugeGroup N) (V : Config N n) (y : Site n) (κ : Fin 4) (L : ℕ)
    (off : ι → Fin 4 → ℤ) (ord : ∀ x, P x → List (Fin 4)) :
    avgB G V y κ L off ord = avgZ G.inChart G.chartLog V y κ L off ord := rfl

lemma loop_eq_holZ (V : Config N n) (y : Site n) (κ : Fin 4) (L : ℤ) (off : ι → Fin 4 → ℤ)
    (ord : ∀ x, P x → List (Fin 4)) (x : ι) (Γ Γ' : P x) :
    Average.loop (fun x Γ => V.hol (stair y (off x) (ord x Γ) 0)) (fun x => V.hol (segZ κ (ofs y (off x)) L))
      (fun x Γ' => V.hol (stair (ofs y (Pi.single κ L)) (off x) (ord x Γ') 0)) (V.hol (segZ κ y L)) x Γ Γ' =
      V.hol (lpathZ y κ L off ord x Γ Γ') := by
  rw [hol_lpathZ]; rfl

/-- The extension with `Log` is `avgZ` with `Log` on all of `GL(N)`. -/
lemma avgLogZ_eq_avgZ (V : Config N n) (y : Site n) (κ : Fin 4) (L : ℤ) (off : ι → Fin 4 → ℤ)
    (ord : ∀ x, P x → List (Fin 4)) :
    avgLogZ V y κ L off ord = avgZ (fun _ => True) (fun W => LogM (W : Mat)) V y κ L off ord := by
  unfold avgZ Average.avg
  rw [if_pos fun _ _ _ => trivial]
  unfold avgLogZ betaLogZ Average.beta
  simp only [loop_eq_holZ]

/-- The average depends only on the transports along the four kinds of paths. -/
theorem avgZ_congr (inN : GLN → Prop) (log : GLN → Mat) {V V' : Config N n} {y y' : Site n}
    {κ κ' : Fin 4} {L L' : ℤ} {off off' : ι → Fin 4 → ℤ} {ord ord' : ∀ x, P x → List (Fin 4)}
    (hp : Pieces V y κ L off ord V' y' κ' L' off' ord') :
    avgZ inN log V' y' κ' L' off' ord' = avgZ inN log V y κ L off ord := by
  obtain ⟨h1, h2, h3, h4⟩ := hp
  unfold avgZ
  simp only [h1, h2, h3, h4]

theorem avgZ_translate (inN : GLN → Prop) (log : GLN → Mat) (V : Config N n) (t y : Site n) (κ : Fin 4)
    (L : ℤ) (off : ι → Fin 4 → ℤ) (ord : ∀ x, P x → List (Fin 4)) :
    avgZ inN log (StraightExtension.translate V t) (y + t) κ L off ord = avgZ inN log V y κ L off ord :=
  avgZ_congr inN log (pieces_translate V t y κ L off ord)

theorem avgZ_perm (inN : GLN → Prop) (log : GLN → Mat) (σ : Equiv.Perm (Fin 4)) (V : Config N n)
    (y : Site n) (κ : Fin 4) (L : ℤ) (off : ι → Fin 4 → ℤ) (ord : ∀ x, P x → List (Fin 4)) :
    avgZ inN log (permC σ V) (permSite σ y) (σ κ) L (fun x ν => off x (σ.symm ν))
        (fun x Γ => (ord x Γ).map σ) = avgZ inN log V y κ L off ord :=
  avgZ_congr inN log (pieces_perm σ V y κ L off ord)

theorem avgZ_refl (inN : GLN → Prop) (log : GLN → Mat) (μ : Fin 4) (V : Config N n) (y : Site n)
    (κ : Fin 4) (L : ℤ) (off : ι → Fin 4 → ℤ) (ord : ∀ x, P x → List (Fin 4)) :
    avgZ inN log (reflC μ V) (reflSite μ y) κ (if κ = μ then -L else L) (fun x => reflV μ (off x)) ord =
      avgZ inN log V y κ L off ord :=
  avgZ_congr inN log (pieces_refl μ V y κ L off ord)

variable {ι' : Type*} [Fintype ι'] {P' : ι' → Type*} [∀ x, Fintype (P' x)]

/-- Under a reindexing which matches the offsets and the paths, the loops correspond. -/
lemma hol_lpathZ_reindex (V : Config N n) (y : Site n) (κ : Fin 4) (L : ℤ) (off : ι → Fin 4 → ℤ)
    (ord : ∀ x, P x → List (Fin 4)) (off' : ι' → Fin 4 → ℤ) (ord' : ∀ x, P' x → List (Fin 4))
    (e : ι ≃ ι') (f : ∀ x, P x ≃ P' (e x)) (hoff : ∀ x, off' (e x) = off x)
    (hstair : ∀ x Γ (w : Site n), stair w (off x) (ord' (e x) (f x Γ)) 0 = stair w (off x) (ord x Γ) 0)
    (x : ι) (Γ Γ' : P x) :
    V.hol (lpathZ y κ L off' ord' (e x) (f x Γ) (f x Γ')) = V.hol (lpathZ y κ L off ord x Γ Γ') := by
  simp only [lpathZ, hoff, hstair]

/-- Under a reindexing, a property holds for all loops of one family iff it holds for those of the other. -/
lemma forall_lpathZ_reindex (Q : GLN → Prop) (V : Config N n) (y : Site n) (κ : Fin 4) (L : ℤ)
    (off : ι → Fin 4 → ℤ) (ord : ∀ x, P x → List (Fin 4)) (off' : ι' → Fin 4 → ℤ)
    (ord' : ∀ x, P' x → List (Fin 4)) (e : ι ≃ ι') (f : ∀ x, P x ≃ P' (e x))
    (hoff : ∀ x, off' (e x) = off x)
    (hstair : ∀ x Γ (w : Site n), stair w (off x) (ord' (e x) (f x Γ)) 0 = stair w (off x) (ord x Γ) 0) :
    (∀ x' Γ Γ', Q (V.hol (lpathZ y κ L off' ord' x' Γ Γ'))) ↔
      ∀ x Γ Γ', Q (V.hol (lpathZ y κ L off ord x Γ Γ')) := by
  have hl := hol_lpathZ_reindex V y κ L off ord off' ord' e f hoff hstair
  constructor
  · intro H x Γ Γ'
    rw [← hl]
    exact H _ _ _
  · intro H x' Γ Γ'
    obtain ⟨x, rfl⟩ := e.surjective x'
    obtain ⟨γ, rfl⟩ := (f x).surjective Γ
    obtain ⟨γ', rfl⟩ := (f x).surjective Γ'
    rw [hl]
    exact H _ _ _

/-- **Reindexing.** A bijection `e` of the points and bijections `f x` of the paths which match the offsets
and the paths (as lists of bonds) do not change the average. -/
theorem avgZ_reindex (inN : GLN → Prop) (log : GLN → Mat) (V : Config N n) (y : Site n) (κ : Fin 4)
    (L : ℤ) (off : ι → Fin 4 → ℤ) (ord : ∀ x, P x → List (Fin 4)) (off' : ι' → Fin 4 → ℤ)
    (ord' : ∀ x, P' x → List (Fin 4)) (e : ι ≃ ι') (f : ∀ x, P x ≃ P' (e x))
    (hoff : ∀ x, off' (e x) = off x)
    (hstair : ∀ x Γ (w : Site n), stair w (off x) (ord' (e x) (f x Γ)) 0 = stair w (off x) (ord x Γ) 0) :
    avgZ inN log V y κ L off' ord' = avgZ inN log V y κ L off ord := by
  have hl := hol_lpathZ_reindex V y κ L off ord off' ord' e f hoff hstair
  have hiff := forall_lpathZ_reindex inN V y κ L off ord off' ord' e f hoff hstair
  unfold avgZ Average.avg Average.beta
  simp only [loop_eq_holZ]
  split_ifs with h1 h2 h3
  · congr 3
    refine (Equiv.sum_comp e _).symm.trans (Finset.sum_congr rfl fun x _ => ?_)
    have hw : Average.wt P' P' (e x) = Average.wt P P x := by
      unfold Average.wt
      rw [← Fintype.card_congr e, ← Fintype.card_congr (f x)]
    refine (Equiv.sum_comp (f x) _).symm.trans (Finset.sum_congr rfl fun Γ _ => ?_)
    refine (Equiv.sum_comp (f x) _).symm.trans (Finset.sum_congr rfl fun Γ' _ => ?_)
    rw [hl, hw]
  · exact absurd (hiff.1 fun x Γ Γ' => by simpa only [loop_eq_holZ] using h1 x Γ Γ')
      (fun H => h2 fun x Γ Γ' => by simpa only [loop_eq_holZ] using H x Γ Γ')
  · exact absurd (hiff.2 fun x Γ Γ' => by simpa only [loop_eq_holZ] using h3 x Γ Γ')
      (fun H => h1 fun x Γ Γ' => by simpa only [loop_eq_holZ] using H x Γ Γ')
  · rfl

/-- **The bond of negative length.** For a logarithm with the properties of `lem:chart`(i) on a subgroup
`S` containing `V([c])`, the average at `(y + Le_κ, y)` is `M(V)(c)⁻¹` (`lem:average`(i)). -/
theorem avgZ_neg {S : Subgroup GLN} {inN : GLN → Prop} {log : GLN → Mat}
    (hL : Average.LogInput S inN log) (V : Config N n) (y : Site n) (κ : Fin 4) (L : ℤ)
    (off : ι → Fin 4 → ℤ) (ord : ∀ x, P x → List (Fin 4)) (hk : V.hol (segZ κ y L) ∈ S) :
    avgZ inN log V (ofs y (Pi.single κ L)) κ (-L) off ord = (avgZ inN log V y κ L off ord)⁻¹ := by
  have e0 : ofs (ofs y (Pi.single κ L)) (Pi.single κ (-L)) = y := by
    rw [ofs_ofs, ← Pi.single_add, add_neg_cancel, Pi.single_zero, ofs_zero]
  have e1 : ∀ x, ofs (ofs y (Pi.single κ L)) (off x) = ofs (ofs y (off x)) (Pi.single κ L) := fun x => by
    rw [ofs_ofs, ofs_ofs, add_comm]
  have hk' : V.hol (segZ κ (ofs y (Pi.single κ L)) (-L)) = (V.hol (segZ κ y L))⁻¹ := by
    rw [ofs_single, hol_segZ_neg]
  have hh : ∀ x, V.hol (segZ κ (ofs (ofs y (Pi.single κ L)) (off x)) (-L)) =
      (V.hol (segZ κ (ofs y (off x)) L))⁻¹ := fun x => by
    rw [e1, ofs_single, hol_segZ_neg]
  unfold avgZ
  simp only [e0, hh, hk']
  exact Average.avg_reverse hL _ _ _ _ hk

/-- The loops of the bond of negative length are the conjugates of the inverses of those of `c`. -/
lemma hol_lpathZ_neg (V : Config N n) (y : Site n) (κ : Fin 4) (L : ℤ) (off : ι → Fin 4 → ℤ)
    (ord : ∀ x, P x → List (Fin 4)) (x : ι) (Γ Γ' : P x) :
    V.hol (lpathZ (ofs y (Pi.single κ L)) κ (-L) off ord x Γ Γ') =
      (V.hol (segZ κ y L))⁻¹ * (V.hol (lpathZ y κ L off ord x Γ' Γ))⁻¹ * V.hol (segZ κ y L) := by
  have e0 : ofs (ofs y (Pi.single κ L)) (Pi.single κ (-L)) = y := by
    rw [ofs_ofs, ← Pi.single_add, add_neg_cancel, Pi.single_zero, ofs_zero]
  have e1 : ofs (ofs y (Pi.single κ L)) (off x) = ofs (ofs y (off x)) (Pi.single κ L) := by
    rw [ofs_ofs, ofs_ofs, add_comm]
  rw [hol_lpathZ, hol_lpathZ, e0, e1, ofs_single, ofs_single, hol_segZ_neg, hol_segZ_neg, ← ofs_single]
  group

end Generic

/-! ### The family `𝐆` -/

/-- The average for the family `𝐆(y, x)` of `def:block-paths` at both ends of the bond. -/
def avgG (inN : GLN → Prop) (log : GLN → Mat) (V : Config N n) (y : Site n) (κ : Fin 4) (h : ℕ)
    (L : ℤ) : GLN :=
  avgZ (ι := Pts h) (P := fun x => Ords (offP h x)) inN log V y κ L (offP h) (ordG h)

/-- The bijection `x ↦ x ∘ σ⁻¹` of the points of a block. -/
def permPt (σ : Equiv.Perm (Fin 4)) {h : ℕ} (x : Pts h) : Pts h := fun ν => x (σ.symm ν)

def ePerm (σ : Equiv.Perm (Fin 4)) (h : ℕ) : Pts h ≃ Pts h where
  toFun := permPt σ
  invFun := permPt σ.symm
  left_inv x := by funext ν; simp [permPt]
  right_inv x := by funext ν; simp [permPt]

lemma supp_perm (σ : Equiv.Perm (Fin 4)) (v : Fin 4 → ℤ) :
    ((supp v).map σ).Perm (supp (fun ν => v (σ.symm ν))) := by
  have hnd : ∀ w : Fin 4 → ℤ, (supp w).Nodup := fun w => List.Nodup.filter _ (by decide)
  have hall : ∀ a : Fin 4, a ∈ ([0, 1, 2, 3] : List (Fin 4)) := by decide
  refine (List.perm_ext_iff_of_nodup ((hnd v).map σ.injective) (hnd _)).2 fun a => ?_
  rw [List.mem_map]
  unfold supp
  constructor
  · rintro ⟨b, hb, rfl⟩
    rw [List.mem_filter] at hb ⊢
    exact ⟨hall _, by simpa using hb.2⟩
  · intro ha
    rw [List.mem_filter] at ha
    exact ⟨σ.symm a, List.mem_filter.2 ⟨hall _, by simpa using ha.2⟩, by simp⟩

lemma ords_map_mem (σ : Equiv.Perm (Fin 4)) {v w : Fin 4 → ℤ} (hw : w = fun ν => v (σ.symm ν))
    (Γ : Ords v) : Γ.1.map σ ∈ (supp w).permutations.toFinset := by
  subst hw
  exact List.mem_toFinset.2 (List.mem_permutations.2 (((ords_perm Γ).map σ).trans (supp_perm σ v)))

/-- The bijection `Γ ↦ σΓ` of the orderings. -/
def fPerm (σ : Equiv.Perm (Fin 4)) (h : ℕ) (x : Pts h) : Ords (offP h x) ≃ Ords (offP h (ePerm σ h x)) where
  toFun Γ := ⟨Γ.1.map σ, ords_map_mem σ rfl Γ⟩
  invFun Γ := ⟨Γ.1.map σ.symm, ords_map_mem σ.symm (by funext ν; simp [offP, ePerm, permPt]) Γ⟩
  left_inv Γ := Subtype.ext (by simp [List.map_map])
  right_inv Γ := Subtype.ext (by simp [List.map_map])

lemma stair_perm_G (σ : Equiv.Perm (Fin 4)) (h : ℕ) (x : Pts h) (Γ : Ords (offP h x)) (w : Site n) :
    stair w (fun ν => offP h x (σ.symm ν)) (ordG h (ePerm σ h x) (fPerm σ h x Γ)) 0 =
      stair w (fun ν => offP h x (σ.symm ν)) ((ordG h x Γ).map σ) 0 := by
  have hz : stair w (fun ν => offP h x (σ.symm ν)) ((zer (offP h x)).map σ)
      (0 + offs (fun ν => offP h x (σ.symm ν)) (Γ.1.map σ)) = [] := by
    refine stair_zero_coords w _ _ _ fun ν hν => ?_
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hν
    simpa [zer] using (List.mem_filter.1 hb).2
  have hl : stair w (fun ν => offP h x (σ.symm ν)) (ordG h (ePerm σ h x) (fPerm σ h x Γ)) 0 =
      stair w (fun ν => offP h x (σ.symm ν)) (Γ.1.map σ) 0 :=
    stair_ordG h w (ePerm σ h x) (fPerm σ h x Γ) 0
  rw [hl, ordG, List.map_append, stair_append, hz, List.append_nil]

/-- **`lem:average`(iv) for the family `𝐆`, the permutations of the coordinates**, for every logarithm and
every configuration. -/
theorem avgG_perm (inN : GLN → Prop) (log : GLN → Mat) (σ : Equiv.Perm (Fin 4)) (V : Config N n)
    (y : Site n) (κ : Fin 4) (h : ℕ) (L : ℤ) :
    avgG inN log (permC σ V) (permSite σ y) (σ κ) h L = avgG inN log V y κ h L := by
  unfold avgG
  rw [avgZ_reindex inN log (permC σ V) _ _ L (fun x ν => offP h x (σ.symm ν))
    (fun x Γ => (ordG h x Γ).map σ) (offP h) (ordG h) (ePerm σ h) (fPerm σ h) (fun _ => rfl)
    (fun x Γ w => stair_perm_G σ h x Γ w)]
  exact avgZ_perm inN log σ V y κ L (offP h) (ordG h)

/-- The loops of `θc` of `θV` for the family `𝐆` are those of `c` of `V`. -/
theorem loopsG_perm (Q : GLN → Prop) (σ : Equiv.Perm (Fin 4)) (V : Config N n) (y : Site n) (κ : Fin 4)
    (h : ℕ) (L : ℤ) :
    (∀ x Γ Γ', Q ((permC σ V).hol (lpathZ (permSite σ y) (σ κ) L (offP h) (ordG h) x Γ Γ'))) ↔
      ∀ x Γ Γ', Q (V.hol (lpathZ y κ L (offP h) (ordG h) x Γ Γ')) := by
  rw [forall_lpathZ_reindex Q (permC σ V) _ _ L (fun x ν => offP h x (σ.symm ν))
    (fun x Γ => (ordG h x Γ).map σ) (offP h) (ordG h) (ePerm σ h) (fPerm σ h) (fun _ => rfl)
    (fun x Γ w => stair_perm_G σ h x Γ w)]
  simp only [hol_lpathZ_of_pieces (pieces_perm σ V y κ L (offP h) (ordG h))]

/-- The reflection `n_μ ↦ -n_μ` of the points of a block. -/
def reflPt (μ : Fin 4) {h : ℕ} (x : Pts h) : Pts h := fun ν => if ν = μ then Fin.rev (x ν) else x ν

lemma reflPt_invol (μ : Fin 4) (h : ℕ) : Function.Involutive (reflPt μ (h := h)) := fun x => by
  funext ν
  by_cases hν : ν = μ <;> simp [reflPt, hν]

def eRefl (μ : Fin 4) (h : ℕ) : Pts h ≃ Pts h := (reflPt_invol μ h).toPerm _

lemma offP_reflPt (μ : Fin 4) {h : ℕ} (x : Pts h) : offP h (eRefl μ h x) = reflV μ (offP h x) := by
  funext ν
  have hx := (x ν).isLt
  by_cases hν : ν = μ
  · subst hν
    simp only [eRefl, Function.Involutive.coe_toPerm, reflPt, offP, reflV, ↓reduceIte, Fin.val_rev]
    omega
  · simp [eRefl, reflPt, offP, reflV, hν]

lemma supp_reflV (μ : Fin 4) (v : Fin 4 → ℤ) : supp (reflV μ v) = supp v := by
  unfold supp
  refine List.filter_congr fun σ _ => ?_
  unfold reflV
  split_ifs <;> simp

lemma zer_reflV (μ : Fin 4) (v : Fin 4 → ℤ) : zer (reflV μ v) = zer v := by
  unfold zer
  refine List.filter_congr fun σ _ => ?_
  unfold reflV
  split_ifs <;> simp

/-- The orderings of a point and of its reflection are the same. -/
def fRefl (μ : Fin 4) (h : ℕ) (x : Pts h) : Ords (offP h x) ≃ Ords (offP h (eRefl μ h x)) :=
  Equiv.subtypeEquivRight fun Γ => by rw [offP_reflPt, supp_reflV]

lemma stair_refl_G (μ : Fin 4) (h : ℕ) (x : Pts h) (Γ : Ords (offP h x)) (w : Site n) :
    stair w (reflV μ (offP h x)) (ordG h (eRefl μ h x) (fRefl μ h x Γ)) 0 =
      stair w (reflV μ (offP h x)) (ordG h x Γ) 0 := by
  have hv : (fRefl μ h x Γ).1 = Γ.1 := rfl
  unfold ordG
  rw [hv, offP_reflPt, zer_reflV]

/-- **`lem:average`(iv) for the family `𝐆`, the reflections `x_μ ↦ -x_μ`**, for every logarithm and every
configuration; the reflected bond has length `-L` if `κ = μ`. -/
theorem avgG_refl (inN : GLN → Prop) (log : GLN → Mat) (μ : Fin 4) (V : Config N n) (y : Site n)
    (κ : Fin 4) (h : ℕ) (L : ℤ) :
    avgG inN log (reflC μ V) (reflSite μ y) κ h (if κ = μ then -L else L) = avgG inN log V y κ h L := by
  unfold avgG
  rw [avgZ_reindex inN log (reflC μ V) _ _ _ (fun x => reflV μ (offP h x)) (ordG h) (offP h) (ordG h)
    (eRefl μ h) (fRefl μ h) (offP_reflPt μ) (fun x Γ w => stair_refl_G μ h x Γ w)]
  exact avgZ_refl inN log μ V y κ L (offP h) (ordG h)

theorem loopsG_refl (Q : GLN → Prop) (μ : Fin 4) (V : Config N n) (y : Site n) (κ : Fin 4) (h : ℕ)
    (L : ℤ) :
    (∀ x Γ Γ', Q ((reflC μ V).hol (lpathZ (reflSite μ y) κ (if κ = μ then -L else L) (offP h) (ordG h)
      x Γ Γ'))) ↔ ∀ x Γ Γ', Q (V.hol (lpathZ y κ L (offP h) (ordG h) x Γ Γ')) := by
  rw [forall_lpathZ_reindex Q (reflC μ V) _ _ _ (fun x => reflV μ (offP h x)) (ordG h) (offP h) (ordG h)
    (eRefl μ h) (fRefl μ h) (offP_reflPt μ) (fun x Γ w => stair_refl_G μ h x Γ w)]
  simp only [hol_lpathZ_of_pieces (pieces_refl μ V y κ L (offP h) (ordG h))]

/-- **`lem:average`(iv) for the family `𝐆`, the translations.** -/
theorem avgG_translate (inN : GLN → Prop) (log : GLN → Mat) (V : Config N n) (t y : Site n) (κ : Fin 4)
    (h : ℕ) (L : ℤ) :
    avgG inN log (StraightExtension.translate V t) (y + t) κ h L = avgG inN log V y κ h L :=
  avgZ_translate inN log V t y κ L (offP h) (ordG h)

theorem loopsG_translate (Q : GLN → Prop) (V : Config N n) (t y : Site n) (κ : Fin 4) (h : ℕ) (L : ℤ) :
    (∀ x Γ Γ', Q ((StraightExtension.translate V t).hol (lpathZ (y + t) κ L (offP h) (ordG h) x Γ Γ'))) ↔
      ∀ x Γ Γ', Q (V.hol (lpathZ y κ L (offP h) (ordG h) x Γ Γ')) := by
  simp only [hol_lpathZ_of_pieces (pieces_translate V t y κ L (offP h) (ordG h))]

/-! ### The chart average for `G`-valued fields -/

lemma ofs_neg_single (y : Site n) (κ : Fin 4) (L : ℤ) :
    ofs (ofs y (Pi.single κ (-L))) (Pi.single κ L) = y := by
  rw [ofs_ofs, ← Pi.single_add, neg_add_cancel, Pi.single_zero, ofs_zero]

/-- **`lem:average`(iv), the chart average, the reflection in the direction of the bond**: for a `G`-valued
`U`, `c = (y, y + Le_μ)`, and the positive bond `c' = (Ry - Le_μ, Ry)` of the reflected bond `Rc`,
`M(RU)(c') = M(U)(c)⁻¹`, with the family `𝐆` at both bonds. The permutations and the other reflections
are `avgG_perm` and `avgG_refl` with `avgB_eq_avgZ`. -/
theorem avgB_refl_self_G (G : GaugeGroup N) {U : Config N n} (hU : IsGField G U) (μ : Fin 4) (y : Site n)
    (h L : ℕ) :
    avgB G (reflC μ U) (ofs (reflSite μ y) (Pi.single μ (-(L : ℤ)))) μ L (offP h) (ordG h) =
      (avgB G U y μ L (offP h) (ordG h))⁻¹ := by
  have hR := avgG_refl G.inChart G.chartLog μ U y μ h L
  rw [if_pos rfl] at hR
  have hk : (reflC μ U).hol (segZ μ (ofs (reflSite μ y) (Pi.single μ (-(L : ℤ)))) L) ∈ G.carrier :=
    (act_isGField hU _).hol_mem _
  have hn := avgZ_neg (GaugeGroup.logInput (G := G)) (reflC μ U) (ofs (reflSite μ y) (Pi.single μ (-(L : ℤ)))) μ
    L (offP h) (ordG h) hk
  rw [ofs_neg_single] at hn
  unfold avgG at hR
  rw [avgB_eq_avgZ, avgB_eq_avgZ, ← hR, hn, inv_inv]

/-! ### Complex `B` -/

/-- **`lem:average`(iv) for complex `B`, the reflection in the direction of the bond**, with the family `𝐆`:
for `U`, `B` as in `average_analytic` at `c = (y, y + Le_μ)`, the reflected configuration
`R𝐔_B = e^{iB'}RU` (`average_refl_complex`) satisfies the hypotheses of `average_analytic` at the positive
bond `c' = (Ry - Le_μ, Ry)` of `Rc`, its loops of `c'` are within `¼` of `id`, and
`M(R𝐔_B)(c') = M(𝐔_B)(c)⁻¹`. -/
theorem average_refl_self_complex (G : GaugeGroup N) (hG : IsClosed G.mats) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ {n : ℕ} [NeZero n] (U : Config N n), IsGField G U → ∀ (h : ℕ) (y : Site n)
      (μ : Fin 4),
      (∀ x Γ Γ', ‖((U.hol (lpath y μ (2 * h + 1) (offP h) (ordG h) x Γ Γ') : GLN) : Mat) - 1‖ ≤ c₀) →
      ∀ B : Fin 4 → Site n → Mat, ‖B‖ < c₀ / ((2 * h + 1 : ℕ) : ℝ) →
        (∀ x Γ Γ', ‖(((reflC μ U).hol (lpath (ofs (reflSite μ y) (Pi.single μ (-((2 * h + 1 : ℕ) : ℤ)))) μ
          (2 * h + 1) (offP h) (ordG h) x Γ Γ') : GLN) : Mat) - 1‖ ≤ c₀) ∧
        (∀ x Γ Γ', ‖(((reflC μ (moveC U B)).hol (lpath (ofs (reflSite μ y)
          (Pi.single μ (-((2 * h + 1 : ℕ) : ℤ)))) μ (2 * h + 1) (offP h) (ordG h) x Γ Γ') : GLN) : Mat) - 1‖ ≤
          1 / 4) ∧
        avgLogU (reflC μ (moveC U B)) (ofs (reflSite μ y) (Pi.single μ (-((2 * h + 1 : ℕ) : ℤ)))) μ (2 * h + 1)
          (offP h) (ordG h) = (avgLogU (moveC U B) y μ (2 * h + 1) (offP h) (ordG h))⁻¹ := by
  obtain ⟨c₀, hc₀, H⟩ := average_analytic G hG
  refine ⟨c₀, hc₀, ?_⟩
  intro n _ U hU h y μ hloops B hB
  set L : ℕ := 2 * h + 1 with hLdef
  set y' := ofs (reflSite μ y) (Pi.single μ (-(L : ℤ))) with hy'
  have hRU : IsGField G (reflC μ U) := act_isGField hU _
  -- the loops of `c'` of `RU` are unitary conjugates of the inverses of the loops of `Rc`
  have hRc : ∀ x Γ Γ', ‖(((reflC μ U).hol (lpathZ (reflSite μ y) μ (-(L : ℤ)) (offP h) (ordG h) x Γ Γ') :
      GLN) : Mat) - 1‖ ≤ c₀ := by
    have := (loopsG_refl (fun W : GLN => ‖(W : Mat) - 1‖ ≤ c₀) μ U y μ h L).2 hloops
    rwa [if_pos rfl] at this
  have hc' : ∀ x Γ Γ', ‖(((reflC μ U).hol (lpath y' μ L (offP h) (ordG h) x Γ Γ') : GLN) : Mat) - 1‖ ≤ c₀ := by
    intro x Γ Γ'
    have e := hol_lpathZ_neg (reflC μ U) y' μ L (offP h) (ordG h) x Γ' Γ
    rw [hy', ofs_neg_single] at e
    have hk := hol_isU hRU.gauge (segZ μ y' L)
    have hW := hol_isU hRU.gauge (lpathZ y' μ L (offP h) (ordG h) x Γ Γ')
    have hb := hRc x Γ' Γ
    rw [e, show ((reflC μ U).hol (segZ μ y' L))⁻¹ * ((reflC μ U).hol (lpathZ y' μ L (offP h) (ordG h) x Γ Γ'))⁻¹ *
        (reflC μ U).hol (segZ μ y' L) = ((reflC μ U).hol (segZ μ y' L))⁻¹ *
        ((reflC μ U).hol (lpathZ y' μ L (offP h) (ordG h) x Γ Γ'))⁻¹ * ((reflC μ U).hol (segZ μ y' L))⁻¹⁻¹ by
        rw [inv_inv], norm_conj_sub_one' hk.inv, norm_inv_sub_one' hW] at hb
    exact hb
  -- `R𝐔_B = e^{iB'}RU` with `‖B'‖ ≤ ‖B‖`, and the domain at `c'`
  have hmv : reflC μ (moveC U B) = moveC (reflC μ U) (actF (reflB μ) U B) := act_moveC (reflB μ) U B
  have hB' : ‖actF (reflB μ) U B‖ < c₀ / (L : ℝ) := (norm_actF_le hU _ B).trans_lt hB
  obtain ⟨hdom, -, -, -⟩ := H (reflC μ U) hRU h y' μ (offP h) (ordG h) (fun x => offP_inM h x)
    (fun x Γ => ordG_perm h x Γ) hc'
  have hd := hdom _ hB'
  have hd' : ∀ x Γ Γ', ‖(((reflC μ (moveC U B)).hol (lpath y' μ L (offP h) (ordG h) x Γ Γ') : GLN) : Mat) -
      1‖ ≤ 1 / 4 := by
    intro x Γ Γ'
    have := hd x Γ Γ'
    rwa [← hmv] at this
  refine ⟨hc', hd', ?_⟩
  -- `M(R𝐔_B)(c')⁻¹ = M(R𝐔_B)(Rc) = M(𝐔_B)(c)`
  have hrev := avgLogURev_eq (reflC μ (moveC U B)) y' μ L (offP h) (ordG h) hd'
  have hneg := avgLogZ_neg (reflC μ (moveC U B)) y' μ L (offP h) (ordG h)
  rw [hy', ofs_neg_single] at hneg
  have hR := avgG_refl (fun _ => True) (fun W => LogM (W : Mat)) μ (moveC U B) y μ h L
  rw [if_pos rfl] at hR
  unfold avgG at hR
  rw [← avgLogZ_eq_avgZ, ← avgLogZ_eq_avgZ, hneg, ← hy', hrev] at hR
  rw [avgLogU_eq_avgLogZ (moveC U B), ← hR, inv_inv]

end AverageHolo

end CoreLean

end
