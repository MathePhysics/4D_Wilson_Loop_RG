/-
`lem:average`(iv) of BALABAN_CORE.tex (`541e505b8b38`), the symmetry, for the extension with the series `Log`,
hence for complex `B` (`lem:average`(vi)), on the lattice: `M(θV)(θc) = M(V)(c)` for the translations, the
permutations of the coordinates, and the reflections `x_μ ↦ -x_μ`, for every configuration `V`.

The formula `M(V)(c) = e^{iβ_c}V([c])` with `Log` (`avgLogZ`, for a bond `c = (y, y + Le_κ)` with a signed
length `L ∈ ℤ`, so that the reflected bond `(Ry, Ry - Le_μ)` is covered) depends on `V` only through the
transports along the paths of `c`; a symmetry `θ` maps the paths of `c` to those of `θc`, with the offsets and
orderings transformed, and `(θV)(θγ) = V(γ)`. So no domain condition enters. The families of `θc` here are
the images of those of `c`; `AverageCanonical.lean` identifies them with the family `𝐆` of `θc` by a
reindexing.

* `act`, `act_val`, `act_hol`: `(θV)(b) = V(θ⁻¹b)` for a map of bonds commuting with the reversal.
* `Pieces`, `avgLogZ_congr`, `hol_lpathZ_of_pieces`: the value and the loops depend only on the transports of
  the four kinds of paths.
* `avgLogZ_translate`, `avgLogZ_perm`, `avgLogZ_refl`: the three symmetries.
* `avgLogZ_neg`: the formula at the bond `(y + Le_κ, y)` (length `-L`) is `avgLogURev`, so that with
  `avgLogURev_eq` it is `M(V)(c)⁻¹`.
* `translate_moveC`, `permC_moveC`, `act_moveC` (the reflections): `θ(e^{iB}U) = e^{iB'}(θU)` with `‖B'‖ ≤ ‖B‖` and `B'` with
  values in `𝔤^c` if `B` has; for the reflection in the direction `μ`, `B'_μ = -Ad_{U_μ}^{-1}B_μ` at the
  reflected bond.
-/
import CoreLean.AverageReverse
import CoreLean.AverageLocality

open Matrix NormedSpace
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace CoreLean

namespace AverageHolo

open LatticePaths LatticeKappa RegularAverages

set_option linter.unusedSectionVars false

variable {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "GLN" => (Matrix (Fin N) (Fin N) ℂ)ˣ

variable {n : ℕ} [NeZero n]

/-! ### Configurations moved by maps of bonds -/

/-- The configuration `(θU)(b) = U(T b)`, `T = θ⁻¹`, given by its values on the positive bonds. -/
def act (T : Bond n → Bond n) (U : Config N n) : Config N n := fun ν z => U.val (T ⟨z, ν, true⟩)

lemma act_val {T : Bond n → Bond n} (hT : ∀ b, T b.rev = (T b).rev) (U : Config N n) (b : Bond n) :
    (act T U).val b = U.val (T b) := by
  obtain ⟨z, μ, s⟩ := b
  cases s
  · have hb : (⟨z, μ, false⟩ : Bond n) = (⟨z - unit n μ, μ, true⟩ : Bond n).rev := by
      simp [Bond.rev, Bond.plus]
    rw [hb, Config.val_rev, hT, Config.val_rev]
    rfl
  · rfl

lemma act_hol {T : Bond n → Bond n} (hT : ∀ b, T b.rev = (T b).rev) (U : Config N n) :
    ∀ γ : List (Bond n), (act T U).hol γ = U.hol (γ.map T)
  | [] => rfl
  | b :: γ => by rw [List.map_cons, hol_cons, hol_cons, act_val hT, act_hol hT U γ]

/-! ### The formula for a bond of signed length -/

variable {ι : Type*} [Fintype ι] {P : ι → Type*} [∀ x, Fintype (P x)]

/-- The loop `ℓ_c(x, Γ, Γ')` of the bond `c = (y, y + Le_κ)`, `L ∈ ℤ`. -/
def lpathZ (y : Site n) (κ : Fin 4) (L : ℤ) (off : ι → Fin 4 → ℤ) (ord : ∀ x, P x → List (Fin 4)) (x : ι)
    (Γ Γ' : P x) : List (Bond n) :=
  stair y (off x) (ord x Γ) 0 ++ segZ κ (ofs y (off x)) L ++
    rv (stair (ofs y (Pi.single κ L)) (off x) (ord x Γ') 0) ++ rv (segZ κ y L)

/-- `β_c` with the series `Log`. -/
def betaLogZ (V : Config N n) (y : Site n) (κ : Fin 4) (L : ℤ) (off : ι → Fin 4 → ℤ)
    (ord : ∀ x, P x → List (Fin 4)) : Mat :=
  ∑ x, ∑ Γ, ∑ Γ', Average.wt P P x • ((1 / Complex.I : ℂ) •
    LogM ((V.hol (lpathZ y κ L off ord x Γ Γ') : GLN) : Mat))

/-- `M(V)(c) = e^{iβ_c}V([c])` with the series `Log`, for `c = (y, y + Le_κ)`, `L ∈ ℤ`. -/
def avgLogZ (V : Config N n) (y : Site n) (κ : Fin 4) (L : ℤ) (off : ι → Fin 4 → ℤ)
    (ord : ∀ x, P x → List (Fin 4)) : GLN :=
  expU (Complex.I • betaLogZ V y κ L off ord) * V.hol (segZ κ y L)

/-- For `L ∈ ℕ` this is the formula of `average_analytic`. -/
lemma avgLogU_eq_avgLogZ (V : Config N n) (y : Site n) (κ : Fin 4) (L : ℕ) (off : ι → Fin 4 → ℤ)
    (ord : ∀ x, P x → List (Fin 4)) : avgLogU V y κ L off ord = avgLogZ V y κ L off ord := rfl

lemma hol_lpathZ (V : Config N n) (y : Site n) (κ : Fin 4) (L : ℤ) (off : ι → Fin 4 → ℤ)
    (ord : ∀ x, P x → List (Fin 4)) (x : ι) (Γ Γ' : P x) :
    V.hol (lpathZ y κ L off ord x Γ Γ') = V.hol (stair y (off x) (ord x Γ) 0) *
      V.hol (segZ κ (ofs y (off x)) L) * (V.hol (stair (ofs y (Pi.single κ L)) (off x) (ord x Γ') 0))⁻¹ *
      (V.hol (segZ κ y L))⁻¹ := by
  simp only [lpathZ, hol_append, rv, Transports.hol_rev]

/-- The transports of `V'` along the four kinds of paths of `c' = (y', y' + L'e_{κ'})` with the families
`off'`, `ord'` are those of `V` along the paths of `c = (y, y + Le_κ)` with `off`, `ord`. -/
def Pieces (V : Config N n) (y : Site n) (κ : Fin 4) (L : ℤ) (off : ι → Fin 4 → ℤ)
    (ord : ∀ x, P x → List (Fin 4)) (V' : Config N n) (y' : Site n) (κ' : Fin 4) (L' : ℤ)
    (off' : ι → Fin 4 → ℤ) (ord' : ∀ x, P x → List (Fin 4)) : Prop :=
  (∀ x Γ, V'.hol (stair y' (off' x) (ord' x Γ) 0) = V.hol (stair y (off x) (ord x Γ) 0)) ∧
  (∀ x, V'.hol (segZ κ' (ofs y' (off' x)) L') = V.hol (segZ κ (ofs y (off x)) L)) ∧
  (∀ x Γ, V'.hol (stair (ofs y' (Pi.single κ' L')) (off' x) (ord' x Γ) 0) =
    V.hol (stair (ofs y (Pi.single κ L)) (off x) (ord x Γ) 0)) ∧
  V'.hol (segZ κ' y' L') = V.hol (segZ κ y L)

/-- With the same transports along the paths, the loops have the same transports. -/
theorem hol_lpathZ_of_pieces {V V' : Config N n} {y y' : Site n} {κ κ' : Fin 4} {L L' : ℤ}
    {off off' : ι → Fin 4 → ℤ} {ord ord' : ∀ x, P x → List (Fin 4)}
    (hp : Pieces V y κ L off ord V' y' κ' L' off' ord') (x : ι) (Γ Γ' : P x) :
    V'.hol (lpathZ y' κ' L' off' ord' x Γ Γ') = V.hol (lpathZ y κ L off ord x Γ Γ') := by
  rw [hol_lpathZ, hol_lpathZ, hp.1, hp.2.1, hp.2.2.1, hp.2.2.2]

/-- The value depends only on the transports along the four kinds of paths. -/
theorem avgLogZ_congr {V V' : Config N n} {y y' : Site n} {κ κ' : Fin 4} {L L' : ℤ}
    {off off' : ι → Fin 4 → ℤ} {ord ord' : ∀ x, P x → List (Fin 4)}
    (hp : Pieces V y κ L off ord V' y' κ' L' off' ord') :
    avgLogZ V' y' κ' L' off' ord' = avgLogZ V y κ L off ord := by
  unfold avgLogZ betaLogZ
  simp only [hol_lpathZ_of_pieces hp, hp.2.2.2]

/-! ### Translations -/

lemma pieces_translate (V : Config N n) (t y : Site n) (κ : Fin 4) (L : ℤ) (off : ι → Fin 4 → ℤ)
    (ord : ∀ x, P x → List (Fin 4)) :
    Pieces V y κ L off ord (StraightExtension.translate V t) (y + t) κ L off ord := by
  refine ⟨fun x Γ => ?_, fun x => ?_, fun x Γ => ?_, ?_⟩
  · rw [StraightExtension.stair_translate, StraightExtension.hol_translate]
  · rw [StraightExtension.ofs_add_base, ← map_shift_segZ, StraightExtension.hol_translate]
  · rw [StraightExtension.ofs_add_base, StraightExtension.stair_translate, StraightExtension.hol_translate]
  · rw [← map_shift_segZ, StraightExtension.hol_translate]

/-- **`lem:average`(iv)** for the translations, for every configuration. -/
theorem avgLogZ_translate (V : Config N n) (t y : Site n) (κ : Fin 4) (L : ℤ) (off : ι → Fin 4 → ℤ)
    (ord : ∀ x, P x → List (Fin 4)) :
    avgLogZ (StraightExtension.translate V t) (y + t) κ L off ord = avgLogZ V y κ L off ord :=
  avgLogZ_congr (pieces_translate V t y κ L off ord)

/-- `θ(e^{iB}U) = e^{iθB}θU` for the translations. -/
lemma translate_moveC (U : Config N n) (B : Fin 4 → Site n → Mat) (t : Site n) :
    StraightExtension.translate (moveC U B) t =
      moveC (StraightExtension.translate U t) (fun ρ z => B ρ (z - t)) := rfl

/-! ### Permutations of the coordinates -/

/-- The permuted site `(θz)_ν = z_{σ⁻¹ν}`, so that `θe_μ = e_{σμ}`. -/
def permSite (σ : Equiv.Perm (Fin 4)) (z : Site n) : Site n := fun ν => z (σ.symm ν)

/-- The permuted bond. -/
def permB (σ : Equiv.Perm (Fin 4)) (b : Bond n) : Bond n := ⟨permSite σ b.site, σ b.dir, b.pos⟩

/-- The permuted configuration `(θU)(b) = U(θ⁻¹b)`. -/
def permC (σ : Equiv.Perm (Fin 4)) (U : Config N n) : Config N n := act (permB σ.symm) U

lemma permSite_unit (σ : Equiv.Perm (Fin 4)) (μ : Fin 4) : permSite σ (unit n μ) = unit n (σ μ) := by
  funext ν
  simp only [permSite, unit, Pi.single_apply, Equiv.symm_apply_eq]

lemma permSite_add (σ : Equiv.Perm (Fin 4)) (z w : Site n) :
    permSite σ (z + w) = permSite σ z + permSite σ w := rfl

lemma permSite_sub (σ : Equiv.Perm (Fin 4)) (z w : Site n) :
    permSite σ (z - w) = permSite σ z - permSite σ w := rfl

lemma permSite_neg (σ : Equiv.Perm (Fin 4)) (z : Site n) : permSite σ (-z) = -permSite σ z := rfl

lemma permSite_dvec (σ : Equiv.Perm (Fin 4)) (μ : Fin 4) (s : Bool) :
    permSite σ (dvec μ s : Site n) = dvec (σ μ) s := by
  cases s <;> simp [dvec, permSite_neg, permSite_unit]

lemma permSite_ofs (σ : Equiv.Perm (Fin 4)) (y : Site n) (m : Fin 4 → ℤ) :
    permSite σ (ofs y m) = ofs (permSite σ y) (fun ν => m (σ.symm ν)) := rfl

lemma permB_rev (σ : Equiv.Perm (Fin 4)) (b : Bond n) : permB σ b.rev = (permB σ b).rev := by
  obtain ⟨z, μ, s⟩ := b
  cases s <;> simp [permB, Bond.rev, Bond.plus, permSite_add, permSite_sub, permSite_unit]

lemma permSite_symm (σ : Equiv.Perm (Fin 4)) (z : Site n) : permSite σ.symm (permSite σ z) = z := by
  funext ν
  simp only [permSite, Equiv.symm_symm, Equiv.symm_apply_apply]

lemma permB_symm (σ : Equiv.Perm (Fin 4)) (b : Bond n) : permB σ.symm (permB σ b) = b := by
  obtain ⟨z, μ, s⟩ := b
  simp [permB, permSite_symm]

lemma permC_hol (σ : Equiv.Perm (Fin 4)) (U : Config N n) (γ : List (Bond n)) :
    (permC σ U).hol (γ.map (permB σ)) = U.hol γ := by
  rw [permC, act_hol (permB_rev σ.symm), List.map_map]
  have : (permB σ.symm ∘ permB σ : Bond n → Bond n) = id := funext (permB_symm σ)
  rw [this, List.map_id]

lemma map_permB_seg (σ : Equiv.Perm (Fin 4)) (ρ : Fin 4) (s : Bool) :
    ∀ (k : ℕ) (z : Site n), (seg ρ s z k).map (permB σ) = seg (σ ρ) s (permSite σ z) k
  | 0, _ => rfl
  | k + 1, z => by
    simp only [seg, List.map_cons]
    rw [map_permB_seg σ ρ s k, permSite_add, permSite_dvec]
    rfl

lemma map_permB_segZ (σ : Equiv.Perm (Fin 4)) (ρ : Fin 4) (z : Site n) (k : ℤ) :
    (segZ ρ z k).map (permB σ) = segZ (σ ρ) (permSite σ z) k := by
  rw [segZ_eq, segZ_eq, map_permB_seg]

lemma single_comp_symm (σ : Equiv.Perm (Fin 4)) (κ : Fin 4) (L : ℤ) :
    (fun ν => (Pi.single κ L : Fin 4 → ℤ) (σ.symm ν)) = Pi.single (σ κ) L := by
  funext ν
  simp only [Pi.single_apply, Equiv.symm_apply_eq]

lemma map_permB_stair (σ : Equiv.Perm (Fin 4)) (y : Site n) (m : Fin 4 → ℤ) :
    ∀ (l : List (Fin 4)) (o : Fin 4 → ℤ), (stair y m l o).map (permB σ) =
      stair (permSite σ y) (fun ν => m (σ.symm ν)) (l.map σ) (fun ν => o (σ.symm ν))
  | [], _ => rfl
  | μ :: l, o => by
    simp only [stair, List.map_append, List.map_cons]
    rw [map_permB_segZ, permSite_ofs, map_permB_stair σ y m l, Equiv.symm_apply_apply]
    congr 2
    funext ν
    simp only [Pi.add_apply, Pi.single_apply, Equiv.symm_apply_eq, Equiv.symm_apply_apply]

lemma pieces_perm (σ : Equiv.Perm (Fin 4)) (V : Config N n) (y : Site n) (κ : Fin 4) (L : ℤ)
    (off : ι → Fin 4 → ℤ) (ord : ∀ x, P x → List (Fin 4)) :
    Pieces V y κ L off ord (permC σ V) (permSite σ y) (σ κ) L (fun x ν => off x (σ.symm ν))
      (fun x Γ => (ord x Γ).map σ) := by
  refine ⟨fun x Γ => ?_, fun x => ?_, fun x Γ => ?_, ?_⟩
  · rw [← permC_hol σ V, map_permB_stair]; rfl
  · rw [← permC_hol σ V, map_permB_segZ, permSite_ofs]
  · rw [← permC_hol σ V, map_permB_stair, permSite_ofs, single_comp_symm]; rfl
  · rw [← permC_hol σ V, map_permB_segZ]

/-- **`lem:average`(iv)** for the permutations of the coordinates, for every configuration: the paths of
`θc` are the images of those of `c`, with the offsets `m ∘ σ⁻¹` and the orderings mapped by `σ`. -/
theorem avgLogZ_perm (σ : Equiv.Perm (Fin 4)) (V : Config N n) (y : Site n) (κ : Fin 4) (L : ℤ)
    (off : ι → Fin 4 → ℤ) (ord : ∀ x, P x → List (Fin 4)) :
    avgLogZ (permC σ V) (permSite σ y) (σ κ) L (fun x ν => off x (σ.symm ν))
        (fun x Γ => (ord x Γ).map σ) = avgLogZ V y κ L off ord :=
  avgLogZ_congr (pieces_perm σ V y κ L off ord)

/-- The permuted families are again families of offsets in the box and of orderings. -/
lemma perm_families (σ : Equiv.Perm (Fin 4)) {h : ℕ} {m : Fin 4 → ℤ} (hm : AxialReference.InM h m)
    {l : List (Fin 4)} (hl : l.Perm [0, 1, 2, 3]) :
    AxialReference.InM h (fun ν => m (σ.symm ν)) ∧ (l.map σ).Perm [0, 1, 2, 3] := by
  refine ⟨fun ν => hm _, (hl.map σ).trans ?_⟩
  have hall : ∀ a : Fin 4, a ∈ ([0, 1, 2, 3] : List (Fin 4)) := by decide
  have hnd : ([0, 1, 2, 3] : List (Fin 4)).Nodup := by decide
  refine (List.perm_ext_iff_of_nodup (hnd.map σ.injective) hnd).2 fun a => ?_
  refine ⟨fun _ => hall a, fun _ => List.mem_map.2 ⟨σ.symm a, hall _, by simp⟩⟩

/-- The permuted form `(θB)_ν(z) = B_{σ⁻¹ν}(θ⁻¹z)`. -/
def permF (σ : Equiv.Perm (Fin 4)) (B : Fin 4 → Site n → Mat) : Fin 4 → Site n → Mat :=
  fun ν z => B (σ.symm ν) (permSite σ.symm z)

/-- `θ(e^{iB}U) = e^{iθB}θU` for the permutations. -/
lemma permC_moveC (σ : Equiv.Perm (Fin 4)) (U : Config N n) (B : Fin 4 → Site n → Mat) :
    permC σ (moveC U B) = moveC (permC σ U) (permF σ B) := rfl

/-! ### Reflections -/

/-- The reflection `x_μ ↦ -x_μ` of the sites. -/
def reflSite (μ : Fin 4) (z : Site n) : Site n := fun ν => if ν = μ then -z ν else z ν

/-- The reflection of the integer offsets. -/
def reflV (μ : Fin 4) (m : Fin 4 → ℤ) : Fin 4 → ℤ := fun ν => if ν = μ then -m ν else m ν

/-- The reflected bond: a bond in the direction `μ` changes its orientation. -/
def reflB (μ : Fin 4) (b : Bond n) : Bond n :=
  ⟨reflSite μ b.site, b.dir, if b.dir = μ then !b.pos else b.pos⟩

/-- The reflected configuration `(θU)(b) = U(θb)`. -/
def reflC (μ : Fin 4) (U : Config N n) : Config N n := act (reflB μ) U

lemma reflSite_add (μ : Fin 4) (z w : Site n) : reflSite μ (z + w) = reflSite μ z + reflSite μ w := by
  funext ν; simp only [reflSite, Pi.add_apply]; split_ifs <;> abel

lemma reflSite_sub (μ : Fin 4) (z w : Site n) : reflSite μ (z - w) = reflSite μ z - reflSite μ w := by
  funext ν; simp only [reflSite, Pi.sub_apply]; split_ifs <;> abel

lemma reflSite_unit (μ ν : Fin 4) :
    reflSite μ (unit n ν) = if ν = μ then -unit n ν else unit n ν := by
  funext ρ
  by_cases h : ν = μ
  · subst h; by_cases hρ : ρ = ν <;> simp [reflSite, unit, Pi.single_apply, hρ]
  · by_cases hρ : ρ = μ
    · subst hρ; simp [reflSite, unit, Pi.single_apply, h, Ne.symm h]
    · simp [reflSite, unit, h, hρ]

lemma reflSite_neg (μ : Fin 4) (z : Site n) : reflSite μ (-z) = -reflSite μ z := by
  funext ρ; simp only [reflSite, Pi.neg_apply]; split_ifs <;> rfl

lemma reflSite_dvec (μ ν : Fin 4) (s : Bool) :
    reflSite μ (dvec ν s : Site n) = dvec ν (if ν = μ then !s else s) := by
  by_cases h : ν = μ <;> cases s <;> simp [dvec, h, reflSite_neg, reflSite_unit]

lemma reflSite_reflSite (μ : Fin 4) (z : Site n) : reflSite μ (reflSite μ z) = z := by
  funext ν; simp only [reflSite]; split_ifs <;> simp

lemma reflSite_ofs (μ : Fin 4) (y : Site n) (m : Fin 4 → ℤ) :
    reflSite μ (ofs y m) = ofs (reflSite μ y) (reflV μ m) := by
  funext ν
  simp only [reflSite, reflV, ofs, Pi.add_apply]
  split_ifs <;> push_cast <;> ring

lemma reflV_zero (μ : Fin 4) : reflV μ 0 = 0 := by
  funext ν; simp [reflV]

lemma reflV_add_single (μ : Fin 4) (o m : Fin 4 → ℤ) (ν : Fin 4) :
    reflV μ (o + Pi.single ν (m ν)) = reflV μ o + Pi.single ν (reflV μ m ν) := by
  funext ρ
  unfold reflV
  by_cases h1 : ρ = μ <;> by_cases h2 : ρ = ν <;> subst_vars <;> simp [Pi.single_apply, *] <;> ring

lemma reflV_single (μ κ : Fin 4) (L : ℤ) :
    reflV μ (Pi.single κ L) = Pi.single κ (if κ = μ then -L else L) := by
  funext ρ
  unfold reflV
  by_cases h1 : ρ = μ <;> by_cases h2 : ρ = κ <;> subst_vars <;> simp [Pi.single_apply, *]

lemma reflB_rev (μ : Fin 4) (b : Bond n) : reflB μ b.rev = (reflB μ b).rev := by
  obtain ⟨z, ν, s⟩ := b
  by_cases h : ν = μ <;> cases s <;>
    simp [reflB, Bond.rev, Bond.plus, h, reflSite_add, reflSite_sub, reflSite_unit, reflSite_neg,
      sub_eq_add_neg]

lemma reflB_reflB (μ : Fin 4) (b : Bond n) : reflB μ (reflB μ b) = b := by
  obtain ⟨z, ν, s⟩ := b
  by_cases h : ν = μ <;> simp [reflB, h, reflSite_reflSite]

lemma reflC_hol (μ : Fin 4) (U : Config N n) (γ : List (Bond n)) :
    (reflC μ U).hol (γ.map (reflB μ)) = U.hol γ := by
  rw [reflC, act_hol (reflB_rev μ), List.map_map]
  have : (reflB μ ∘ reflB μ : Bond n → Bond n) = id := funext (reflB_reflB μ)
  rw [this, List.map_id]

lemma map_reflB_seg (μ ρ : Fin 4) (s : Bool) :
    ∀ (k : ℕ) (z : Site n), (seg ρ s z k).map (reflB μ) =
      seg ρ (if ρ = μ then !s else s) (reflSite μ z) k
  | 0, _ => rfl
  | k + 1, z => by
    simp only [seg, List.map_cons]
    rw [map_reflB_seg μ ρ s k, reflSite_add, reflSite_dvec]
    rfl

lemma map_reflB_segZ (μ ρ : Fin 4) (z : Site n) (k : ℤ) :
    (segZ ρ z k).map (reflB μ) = segZ ρ (reflSite μ z) (if ρ = μ then -k else k) := by
  rw [segZ_eq, segZ_eq, map_reflB_seg]
  by_cases hρ : ρ = μ
  · simp only [hρ, ↓reduceIte, Int.natAbs_neg]
    rcases eq_or_ne k 0 with rfl | hk
    · simp [seg]
    · congr 1
      unfold sgn
      by_cases h0 : 0 ≤ k
      · have : ¬ (0 ≤ -k) := by omega
        simp [h0, this] <;> omega
      · have : 0 ≤ -k := by omega
        simp [h0, this] <;> omega
  · simp [hρ]

lemma map_reflB_stair (μ : Fin 4) (y : Site n) (m : Fin 4 → ℤ) :
    ∀ (l : List (Fin 4)) (o : Fin 4 → ℤ), (stair y m l o).map (reflB μ) =
      stair (reflSite μ y) (reflV μ m) l (reflV μ o)
  | [], _ => rfl
  | ν :: l, o => by
    simp only [stair, List.map_append]
    rw [map_reflB_segZ, reflSite_ofs, map_reflB_stair μ y m l, reflV_add_single]
    rfl

lemma pieces_refl (μ : Fin 4) (V : Config N n) (y : Site n) (κ : Fin 4) (L : ℤ)
    (off : ι → Fin 4 → ℤ) (ord : ∀ x, P x → List (Fin 4)) :
    Pieces V y κ L off ord (reflC μ V) (reflSite μ y) κ (if κ = μ then -L else L)
      (fun x => reflV μ (off x)) ord := by
  refine ⟨fun x Γ => ?_, fun x => ?_, fun x Γ => ?_, ?_⟩
  · rw [← reflC_hol μ V, map_reflB_stair, reflV_zero]
  · rw [← reflC_hol μ V, map_reflB_segZ, reflSite_ofs]
  · rw [← reflC_hol μ V, map_reflB_stair, reflSite_ofs, reflV_zero, reflV_single]
  · rw [← reflC_hol μ V, map_reflB_segZ]

/-- **`lem:average`(iv)** for the reflection `x_μ ↦ -x_μ`, for every configuration: the paths of
`θc = (Ry, Ry + L'e_κ)`, `L' = -L` if `κ = μ` and `L' = L` otherwise, are the images of those of `c`, with
the reflected offsets and the same orderings. -/
theorem avgLogZ_refl (μ : Fin 4) (V : Config N n) (y : Site n) (κ : Fin 4) (L : ℤ)
    (off : ι → Fin 4 → ℤ) (ord : ∀ x, P x → List (Fin 4)) :
    avgLogZ (reflC μ V) (reflSite μ y) κ (if κ = μ then -L else L) (fun x => reflV μ (off x)) ord =
      avgLogZ V y κ L off ord :=
  avgLogZ_congr (pieces_refl μ V y κ L off ord)

/-- The reflected families are again families of offsets in the box. -/
lemma reflV_inM (μ : Fin 4) {h : ℕ} {m : Fin 4 → ℤ} (hm : AxialReference.InM h m) :
    AxialReference.InM h (reflV μ m) := fun ν => by
  have := hm ν
  unfold reflV; split_ifs <;> constructor <;> linarith [this.1, this.2]

/-! ### The bond of negative length and the consistency -/

lemma hol_segZ_neg (V : Config N n) (κ : Fin 4) (z : Site n) (L : ℤ) :
    V.hol (segZ κ (z + L • unit n κ) (-L)) = (V.hol (segZ κ z L))⁻¹ := by
  have h := hol_segZ_add (U := V) κ z L (-L)
  rw [add_neg_cancel, segZ_zero, hol_nil] at h
  exact (eq_inv_of_mul_eq_one_right h.symm)

lemma ofs_single (y : Site n) (κ : Fin 4) (L : ℤ) : ofs y (Pi.single κ L) = y + L • unit n κ := by
  rw [← ofs_zero y, ← ofs_add_single, zero_add, ofs_zero]

/-- The formula at the bond `(y + Le_κ, y)` of length `-L` is the formula of `avgLogURev`. -/
theorem avgLogZ_neg (V : Config N n) (y : Site n) (κ : Fin 4) (L : ℕ) (off : ι → Fin 4 → ℤ)
    (ord : ∀ x, P x → List (Fin 4)) :
    avgLogZ V (ofs y (Pi.single κ (L : ℤ))) κ (-(L : ℤ)) off ord = avgLogURev V y κ L off ord := by
  have e0 : ofs (ofs y (Pi.single κ (L : ℤ))) (Pi.single κ (-(L : ℤ))) = y := by
    rw [ofs_ofs, ← Pi.single_add, add_neg_cancel, Pi.single_zero, ofs_zero]
  have e1 : ∀ x, ofs (ofs y (Pi.single κ (L : ℤ))) (off x) =
      ofs (ofs y (off x)) (Pi.single κ (L : ℤ)) := fun x => by
    rw [ofs_ofs, ofs_ofs, add_comm]
  have hk : V.hol (segZ κ (ofs y (Pi.single κ (L : ℤ))) (-(L : ℤ))) = (V.hol (segZ κ y L))⁻¹ := by
    rw [ofs_single, hol_segZ_neg]
  have hh : ∀ x, V.hol (segZ κ (ofs (ofs y (Pi.single κ (L : ℤ))) (off x)) (-(L : ℤ))) =
      (V.hol (segZ κ (ofs y (off x)) L))⁻¹ := fun x => by
    rw [e1, ofs_single, hol_segZ_neg]
  have hl : ∀ x (Γ Γ' : P x), V.hol (lpathZ (ofs y (Pi.single κ (L : ℤ))) κ (-(L : ℤ)) off ord x Γ Γ') =
      V.hol (lpathRev y κ L off ord x Γ Γ') := fun x Γ Γ' => by
    rw [hol_lpathZ, e0, hk, hh, inv_inv]
    simp only [lpathRev, hol_append, rv, Transports.hol_rev]
  unfold avgLogZ avgLogURev betaLogZ betaLogRev
  simp only [hl, hk, rv, Transports.hol_rev]

/-- The formula at the bond `(y', y' - Le_κ)` is `avgLogURev` at `(y' - Le_κ, y')`. -/
theorem avgLogZ_neg' (V : Config N n) (y' : Site n) (κ : Fin 4) (L : ℕ) (off : ι → Fin 4 → ℤ)
    (ord : ∀ x, P x → List (Fin 4)) :
    avgLogZ V y' κ (-(L : ℤ)) off ord = avgLogURev V (ofs y' (Pi.single κ (-(L : ℤ)))) κ L off ord := by
  have e : ofs (ofs y' (Pi.single κ (-(L : ℤ)))) (Pi.single κ (L : ℤ)) = y' := by
    rw [ofs_ofs, ← Pi.single_add, neg_add_cancel, Pi.single_zero, ofs_zero]
  rw [← avgLogZ_neg, e]

/-! ### Complex `B` -/

/-- The exponents of the moved configuration: `B'_ν(z) = Y_{T(z, z + e_ν)}`, the exponent of `𝐔_B` relative
to `U` at the bond `T(z, z + e_ν)` (`Yb`). -/
def actF (T : Bond n → Bond n) (U : Config N n) (B : Fin 4 → Site n → Mat) : Fin 4 → Site n → Mat :=
  fun ν z => Yb U B (T ⟨z, ν, true⟩)

/-- `θ(e^{iB}U) = e^{iB'}θU` with `B' = actF T U B`. -/
lemma act_moveC (T : Bond n → Bond n) (U : Config N n) (B : Fin 4 → Site n → Mat) :
    act T (moveC U B) = moveC (act T U) (actF T U B) :=
  funext fun _ => funext fun _ => val_moveC U B _

lemma act_isGField {G : GaugeGroup N} {U : Config N n} (hU : IsGField G U) (T : Bond n → Bond n) :
    IsGField G (act T U) := fun ν z => by
  show U.val _ ∈ G.carrier
  unfold Config.val
  split_ifs
  · exact hU _ _
  · exact G.carrier.inv_mem (hU _ _)

lemma norm_actF_le {G : GaugeGroup N} {U : Config N n} (hU : IsGField G U) (T : Bond n → Bond n)
    (B : Fin 4 → Site n → Mat) : ‖actF T U B‖ ≤ ‖B‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg B)).2 fun _ =>
    (pi_norm_le_iff_of_nonneg (norm_nonneg B)).2 fun _ => norm_Yb_le hU B _

lemma actF_lieC {G : GaugeGroup N} {U : Config N n} (hU : IsGField G U) (T : Bond n → Bond n)
    {B : Fin 4 → Site n → Mat} (hB : ∀ ρ z, B ρ z ∈ G.lieC) : ∀ ρ z, actF T U B ρ z ∈ G.lieC :=
  fun _ _ => Yb_lieC hU hB _

lemma norm_shiftF_le (B : Fin 4 → Site n → Mat) (f : Fin 4 → Site n → Fin 4) (g : Fin 4 → Site n → Site n) :
    ‖(fun ρ z => B (f ρ z) (g ρ z))‖ ≤ ‖B‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg B)).2 fun ρ => (pi_norm_le_iff_of_nonneg (norm_nonneg B)).2
    fun z => (norm_le_pi_norm (B (f ρ z)) (g ρ z)).trans (norm_le_pi_norm B (f ρ z))

/-- **`lem:average`(iv) for complex `B`, the translations.** For a `G`-valued `U` and a form `B`:
`θ𝐔_B = 𝐔'_{B'}` with `U' = θU` `G`-valued, `‖B'‖_∞ ≤ ‖B‖_∞`, `B'` with values in `𝔤^c` if `B` has, the
loops of `θc` of `U'` equal to those of `c` of `U` (so that `U'`, `B'` satisfy the hypotheses of
`average_analytic` at `θc` when `U`, `B` do at `c`), and `M(θ𝐔_B)(θc) = M(𝐔_B)(c)`. -/
theorem average_translate_complex {G : GaugeGroup N} (t : Site n) {U : Config N n}
    (hU : IsGField G U) (B : Fin 4 → Site n → Mat) (y : Site n) (κ : Fin 4) (L : ℤ)
    (off : ι → Fin 4 → ℤ) (ord : ∀ x, P x → List (Fin 4)) :
    StraightExtension.translate (moveC U B) t =
        moveC (StraightExtension.translate U t) (fun ρ z => B ρ (z - t)) ∧
      IsGField G (StraightExtension.translate U t) ∧ ‖(fun ρ z => B ρ (z - t))‖ ≤ ‖B‖ ∧
      ((∀ ρ z, B ρ z ∈ G.lieC) → ∀ ρ z, B ρ (z - t) ∈ G.lieC) ∧
      (∀ x Γ Γ', (StraightExtension.translate U t).hol (lpathZ (y + t) κ L off ord x Γ Γ') =
        U.hol (lpathZ y κ L off ord x Γ Γ')) ∧
      avgLogZ (StraightExtension.translate (moveC U B) t) (y + t) κ L off ord =
        avgLogZ (moveC U B) y κ L off ord :=
  ⟨rfl, fun ρ z => hU ρ (z - t), norm_shiftF_le B (fun ρ _ => ρ) (fun _ z => z - t),
    fun hB ρ z => hB ρ (z - t), hol_lpathZ_of_pieces (pieces_translate U t y κ L off ord),
    avgLogZ_translate (moveC U B) t y κ L off ord⟩

/-- **`lem:average`(iv) for complex `B`, the permutations of the coordinates**, as
`average_translate_complex`, with the permuted families (which are again families of offsets in the box and
of orderings, `perm_families`). -/
theorem average_perm_complex {G : GaugeGroup N} (σ : Equiv.Perm (Fin 4)) {U : Config N n}
    (hU : IsGField G U) (B : Fin 4 → Site n → Mat) (y : Site n) (κ : Fin 4) (L : ℤ)
    (off : ι → Fin 4 → ℤ) (ord : ∀ x, P x → List (Fin 4)) :
    permC σ (moveC U B) = moveC (permC σ U) (permF σ B) ∧ IsGField G (permC σ U) ∧
      ‖permF σ B‖ ≤ ‖B‖ ∧ ((∀ ρ z, B ρ z ∈ G.lieC) → ∀ ρ z, permF σ B ρ z ∈ G.lieC) ∧
      (∀ x Γ Γ', (permC σ U).hol (lpathZ (permSite σ y) (σ κ) L (fun x ν => off x (σ.symm ν))
        (fun x Γ => (ord x Γ).map σ) x Γ Γ') = U.hol (lpathZ y κ L off ord x Γ Γ')) ∧
      avgLogZ (permC σ (moveC U B)) (permSite σ y) (σ κ) L (fun x ν => off x (σ.symm ν))
        (fun x Γ => (ord x Γ).map σ) = avgLogZ (moveC U B) y κ L off ord :=
  ⟨permC_moveC σ U B, act_isGField hU _,
    norm_shiftF_le B (fun ρ _ => σ.symm ρ) (fun _ z => permSite σ.symm z),
    fun hB ρ z => hB _ _, hol_lpathZ_of_pieces (pieces_perm σ U y κ L off ord),
    avgLogZ_perm σ (moveC U B) y κ L off ord⟩

/-- **`lem:average`(iv) for complex `B`, the reflections `x_μ ↦ -x_μ`**, as `average_translate_complex`,
with the reflected offsets (again in the box, `reflV_inM`) and `B' = actF (reflB μ) U B`
(`B'_μ(z) = -Ad_{U_μ(Rz - e_μ)}^{-1}B_μ(Rz - e_μ)`, `B'_ν(z) = B_ν(Rz)` for `ν ≠ μ`). The reflected bond is
`(Ry, Ry + L'e_κ)` with `L' = -L` if `κ = μ`; then `avgLogZ_neg'` and `avgLogURev_eq` identify the value with
the inverse of the value at the bond `(Ry - Le_μ, Ry)` of positive length. -/
theorem average_refl_complex {G : GaugeGroup N} (μ : Fin 4) {U : Config N n}
    (hU : IsGField G U) (B : Fin 4 → Site n → Mat) (y : Site n) (κ : Fin 4) (L : ℤ)
    (off : ι → Fin 4 → ℤ) (ord : ∀ x, P x → List (Fin 4)) :
    reflC μ (moveC U B) = moveC (reflC μ U) (actF (reflB μ) U B) ∧ IsGField G (reflC μ U) ∧
      ‖actF (reflB μ) U B‖ ≤ ‖B‖ ∧
      ((∀ ρ z, B ρ z ∈ G.lieC) → ∀ ρ z, actF (reflB μ) U B ρ z ∈ G.lieC) ∧
      (∀ x Γ Γ', (reflC μ U).hol (lpathZ (reflSite μ y) κ (if κ = μ then -L else L)
        (fun x => reflV μ (off x)) ord x Γ Γ') = U.hol (lpathZ y κ L off ord x Γ Γ')) ∧
      avgLogZ (reflC μ (moveC U B)) (reflSite μ y) κ (if κ = μ then -L else L)
        (fun x => reflV μ (off x)) ord = avgLogZ (moveC U B) y κ L off ord :=
  ⟨act_moveC _ U B, act_isGField hU _, norm_actF_le hU _ B, actF_lieC hU _,
    hol_lpathZ_of_pieces (pieces_refl μ U y κ L off ord), avgLogZ_refl μ (moveC U B) y κ L off ord⟩

end AverageHolo

end CoreLean

end
