/-
`prop:relative-average`(viii) of BALABAN_CORE.tex (`d8bdc4ac1777`): one function for all positions and all tori.

The transports from `c₋` and `c₊`, the site factors, the averages, and `𝓜_𝐔(A)(c)` at the bond `c = (y, y + Le_μ)`
depend only on the values `𝐔_ν(y + v)`, `aA_ν(y + v)` on the positive bonds of the integer box
`R = {v | -h ≤ v_σ ≤ 3h + 1}` (`InR`), and not on `y` or on the torus (`relAvg_transfer`). In particular they are the
values of the functions on the torus of size `4h + 2` at the base point `0`, applied to the transported data
(`relAvg_reference`).
-/
import CoreLean.RelativeAverageBox

open Matrix NormedSpace

noncomputable section

namespace CoreLean
namespace RelativeAverage

open LatticePaths LatticeKappa RegularAverages BlockPaths AverageHolo MeanTransports AxialReference

variable {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "GLN" => (Matrix (Fin N) (Fin N) ℂ)ˣ

/-- The integer box `R = [-h, 3h + 1]⁴` of the bond. -/
def InR (h : ℕ) (v : Fin 4 → ℤ) : Prop := ∀ σ, -(h : ℤ) ≤ v σ ∧ v σ ≤ 3 * h + 1

variable {n n' : ℕ} [NeZero n] [NeZero n']

/-- Two configurations and forms agree on the box of the bond, from the base points `y` and `y'`. -/
def Agree (h : ℕ) (V : Config N n) (B : Fin 4 → Site n → Mat) (y : Site n) (V' : Config N n')
    (B' : Fin 4 → Site n' → Mat) (y' : Site n') : Prop :=
  ∀ v, InR h v → ∀ ν, V ν (ofs y v) = V' ν (ofs y' v) ∧ B ν (ofs y v) = B' ν (ofs y' v)

lemma stair_shift (y : Site n) (w m : Fin 4 → ℤ) :
    ∀ (l : List (Fin 4)) (o : Fin 4 → ℤ), stair (ofs y w) m l o = stair y m l (w + o)
  | [], _ => rfl
  | μ :: l, o => by
    simp only [stair, ofs_ofs, stair_shift y w m l, add_assoc]

lemma holG_eq (V : Config N n) (y : Site n) (h : ℕ) (w : Fin 4 → ℤ) (x : Pts h) (Γ : Ords (offP h x)) :
    holG V (ofs y w) h x Γ = holI (fC V y) (istair (offP h x) (ordG h x Γ) w) := by
  rw [holG, stair_shift, add_zero, stair_map, hol_map]

lemma fC_moveC (V : Config N n) (B : Fin 4 → Site n → Mat) (y : Site n) (v : Fin 4 → ℤ) (ν : Fin 4) :
    fC (moveC V B) y v ν = expU (Complex.I • B ν (ofs y v)) * V ν (ofs y v) := rfl

/-- Agreement on the box gives equal holonomies along integer paths with positions in the box. -/
lemma holI_agree {h : ℕ} {V : Config N n} {B : Fin 4 → Site n → Mat} {y : Site n} {V' : Config N n'}
    {B' : Fin 4 → Site n' → Mat} {y' : Site n'} (hA : Agree h V B y V' B' y') (γ : List IBond)
    (hγ : ∀ b ∈ γ, InR h (ipos b)) :
    holI (fC V y) γ = holI (fC V' y') γ ∧ holI (fC (moveC V B) y) γ = holI (fC (moveC V' B') y') γ := by
  constructor
  · exact holI_congr γ fun b hb => valI_congr (by simp only [fC]; exact (hA _ (hγ b hb) _).1)
  · exact holI_congr γ fun b hb => valI_congr (by
      rw [fC_moveC, fC_moveC, (hA _ (hγ b hb) _).1, (hA _ (hγ b hb) _).2])

/-- The offsets `w` of the two ends of the bond, whose blocks lie in the box. -/
def EndOK (h : ℕ) (w : Fin 4 → ℤ) : Prop := ∀ σ, -(h : ℤ) ≤ w σ - h ∧ w σ + h ≤ 3 * h + 1

lemma block_inR {h : ℕ} {w : Fin 4 → ℤ} (hw : EndOK h w) (x : Pts h) (Γ : Ords (offP h x)) :
    ∀ b ∈ istair (offP h x) (ordG h x Γ) w, InR h (ipos b) := fun b hb σ => by
  have h1 := ipos_block x Γ w b hb σ
  have h2 := hw σ
  constructor <;> omega

lemma holG_agree {h : ℕ} {V : Config N n} {B : Fin 4 → Site n → Mat} {y : Site n} {V' : Config N n'}
    {B' : Fin 4 → Site n' → Mat} {y' : Site n'} (hA : Agree h V B y V' B' y') {w : Fin 4 → ℤ} (hw : EndOK h w)
    (x : Pts h) (Γ : Ords (offP h x)) :
    holG V (ofs y w) h x Γ = holG V' (ofs y' w) h x Γ ∧
      holG (moveC V B) (ofs y w) h x Γ = holG (moveC V' B') (ofs y' w) h x Γ := by
  rw [holG_eq, holG_eq, holG_eq, holG_eq]
  exact holI_agree hA _ (block_inR hw x Γ)

lemma trans_agree {h : ℕ} {V : Config N n} {B : Fin 4 → Site n → Mat} {y : Site n} {V' : Config N n'}
    {B' : Fin 4 → Site n' → Mat} {y' : Site n'} (hA : Agree h V B y V' B' y') {w : Fin 4 → ℤ} (hw : EndOK h w)
    (x : Pts h) :
    trans V (ofs y w) h x = trans V' (ofs y' w) h x ∧
      trans (moveC V B) (ofs y w) h x = trans (moveC V' B') (ofs y' w) h x := by
  have h1 : ∀ Γ, holG V (ofs y w) h x Γ = holG V' (ofs y' w) h x Γ := fun Γ => (holG_agree hA hw x Γ).1
  have h2 : ∀ Γ, holG (moveC V B) (ofs y w) h x Γ = holG (moveC V' B') (ofs y' w) h x Γ := fun Γ =>
    (holG_agree hA hw x Γ).2
  constructor
  · have he : expsG V (ofs y w) h x = expsG V' (ofs y' w) h x := by funext i; simp only [expsG, h1]
    simp only [trans, he, h1]
  · have he : expsG (moveC V B) (ofs y w) h x = expsG (moveC V' B') (ofs y' w) h x := by
      funext i; simp only [expsG, h2]
    simp only [trans, he, h2]

/-- **Transfer of the site factors.** -/
theorem siteFactor_agree {h : ℕ} {V : Config N n} {B : Fin 4 → Site n → Mat} {y : Site n} {V' : Config N n'}
    {B' : Fin 4 → Site n' → Mat} {y' : Site n'} (hA : Agree h V B y V' B' y') {w : Fin 4 → ℤ} (hw : EndOK h w) :
    siteFactor V B (ofs y w) h = siteFactor V' B' (ofs y' w) h := by
  simp only [siteFactor, (trans_agree hA hw _).1, (trans_agree hA hw _).2]

/-! ### The loops and the average -/

/-- The integer loop `ℓ_c(x, Γ, Γ')`. -/
def ilpath (μ : Fin 4) (h : ℕ) (x : Pts h) (Γ Γ' : Ords (offP h x)) : List IBond :=
  istair (offP h x) (ordG h x Γ) 0 ++ isegZ μ (offP h x) ((2 * h + 1 : ℕ) : ℤ) ++
    irv (istair (offP h x) (ordG h x Γ') (Pi.single μ ((2 * h + 1 : ℕ) : ℤ))) ++
    irv (isegZ μ 0 ((2 * h + 1 : ℕ) : ℤ))

lemma lpath_map (y : Site n) (μ : Fin 4) (h : ℕ) (x : Pts h) (Γ Γ' : Ords (offP h x)) :
    lpath (ι := Pts h) (P := fun x => Ords (offP h x)) y μ (2 * h + 1) (offP h) (ordG h) x Γ Γ' =
      (ilpath μ h x Γ Γ').map (ib y) := by
  simp only [lpath, ilpath, List.map_append]
  rw [stair_map, segZ_map, stair_shift, add_zero, stair_map, rv_map]
  conv_lhs => rw [show segZ μ y ((2 * h + 1 : ℕ) : ℤ) = segZ μ (ofs y 0) ((2 * h + 1 : ℕ) : ℤ) by rw [ofs_zero]]
  rw [segZ_map, rv_map]

lemma mem_irv {γ : List IBond} {b : IBond} (hb : b ∈ irv γ) : ∃ b' ∈ γ, ipos b = ipos b' := by
  simp only [irv, List.mem_reverse, List.mem_map] at hb
  obtain ⟨b', hb', rfl⟩ := hb
  exact ⟨b', hb', ipos_irev b'⟩

lemma ilpath_inR (μ : Fin 4) (h : ℕ) (x : Pts h) (Γ Γ' : Ords (offP h x)) :
    ∀ b ∈ ilpath μ h x Γ Γ', InR h (ipos b) := by
  have hc := offP_inM h x
  have h0 : EndOK h 0 := fun σ => by simp; omega
  have hL : EndOK h (Pi.single μ ((2 * h + 1 : ℕ) : ℤ)) := fun σ => by
    by_cases hσ : σ = μ
    · subst hσ; simp; omega
    · simp [Pi.single_eq_of_ne hσ]; omega
  intro b hb
  simp only [ilpath, List.mem_append] at hb
  rcases hb with ((hb | hb) | hb) | hb
  · exact block_inR h0 x Γ b hb
  · intro σ
    obtain ⟨h1, h2, h3⟩ := ipos_isegZ μ (offP h x) _ b hb
    have := hc σ
    by_cases hσ : σ = μ
    · subst hσ; push_cast at h2 h3; constructor <;> omega
    · rw [h1 σ hσ]; constructor <;> omega
  · obtain ⟨b', hb', he⟩ := mem_irv hb
    rw [he]; exact block_inR hL x Γ' b' hb'
  · obtain ⟨b', hb', he⟩ := mem_irv hb
    rw [he]
    intro σ
    obtain ⟨h1, h2, h3⟩ := ipos_isegZ μ 0 _ b' hb'
    by_cases hσ : σ = μ
    · subst hσ; simp at h2 h3; push_cast at h2 h3; constructor <;> omega
    · rw [h1 σ hσ]; simp only [Pi.zero_apply]; constructor <;> omega

lemma segc_inR (μ : Fin 4) (h : ℕ) : ∀ b ∈ isegZ μ 0 ((2 * h + 1 : ℕ) : ℤ), InR h (ipos b) := by
  intro b hb σ
  obtain ⟨h1, h2, h3⟩ := ipos_isegZ μ 0 _ b hb
  by_cases hσ : σ = μ
  · subst hσ; simp at h2 h3; push_cast at h2 h3; constructor <;> omega
  · rw [h1 σ hσ]; simp only [Pi.zero_apply]; constructor <;> omega

/-- **Transfer of the averages.** -/
theorem avgM_agree {h : ℕ} {V : Config N n} {B : Fin 4 → Site n → Mat} {y : Site n} {V' : Config N n'}
    {B' : Fin 4 → Site n' → Mat} {y' : Site n'} (μ : Fin 4) (hA : Agree h V B y V' B' y') :
    avgM V y μ h = avgM V' y' μ h ∧ avgM (moveC V B) y μ h = avgM (moveC V' B') y' μ h := by
  have hloop : ∀ x Γ Γ', (V.hol (lpath (ι := Pts h) (P := fun x => Ords (offP h x)) y μ (2 * h + 1) (offP h)
      (ordG h) x Γ Γ') = V'.hol (lpath (ι := Pts h) (P := fun x => Ords (offP h x)) y' μ (2 * h + 1) (offP h)
      (ordG h) x Γ Γ')) ∧ ((moveC V B).hol (lpath (ι := Pts h) (P := fun x => Ords (offP h x)) y μ (2 * h + 1)
      (offP h) (ordG h) x Γ Γ') = (moveC V' B').hol (lpath (ι := Pts h) (P := fun x => Ords (offP h x)) y' μ
      (2 * h + 1) (offP h) (ordG h) x Γ Γ')) := fun x Γ Γ' => by
    rw [lpath_map, lpath_map, hol_map, hol_map, hol_map, hol_map]
    exact holI_agree hA _ (ilpath_inR μ h x Γ Γ')
  have hseg : V.hol (segZ μ y ((2 * h + 1 : ℕ) : ℤ)) = V'.hol (segZ μ y' ((2 * h + 1 : ℕ) : ℤ)) ∧
      (moveC V B).hol (segZ μ y ((2 * h + 1 : ℕ) : ℤ)) = (moveC V' B').hol (segZ μ y' ((2 * h + 1 : ℕ) : ℤ)) := by
    have e := segZ_map y μ 0 ((2 * h + 1 : ℕ) : ℤ)
    have e' := segZ_map y' μ 0 ((2 * h + 1 : ℕ) : ℤ)
    rw [ofs_zero] at e e'
    rw [e, e', hol_map, hol_map, hol_map, hol_map]
    exact holI_agree hA _ (segc_inR μ h)
  constructor
  · unfold avgM avgLogU betaLog
    simp only [fun x Γ Γ' => (hloop x Γ Γ').1, hseg.1]
  · unfold avgM avgLogU betaLog
    simp only [fun x Γ Γ' => (hloop x Γ Γ').2, hseg.2]

/-- **`prop:relative-average`(viii)**: `𝓜_𝐔(A)(c)` depends only on the data on the box of the bond, not on `y` or on
the torus. -/
theorem relAvg_transfer {h : ℕ} {V : Config N n} {B : Fin 4 → Site n → Mat} {y : Site n} {V' : Config N n'}
    {B' : Fin 4 → Site n' → Mat} {y' : Site n'} (μ : Fin 4) (hA : Agree h V B y V' B' y') :
    relAvg V B y μ h = relAvg V' B' y' μ h := by
  have h0 : EndOK h 0 := fun σ => by simp; omega
  have hL : EndOK h (Pi.single μ ((2 * h + 1 : ℕ) : ℤ)) := fun σ => by
    by_cases hσ : σ = μ
    · subst hσ; simp; omega
    · simp [Pi.single_eq_of_ne hσ]; omega
  have hs0 := siteFactor_agree hA h0
  have hsL := siteFactor_agree hA hL
  rw [ofs_zero, ofs_zero] at hs0
  simp only [relAvg, cPlus, hs0, hsL, (avgM_agree μ hA).1, (avgM_agree μ hA).2]

/-! ### The reference torus -/

/-- The data on the reference torus of size `4h + 2` at the base point `0`. -/
def refConfig (h : ℕ) (V : Config N n) (y : Site n) : Config N (4 * h + 2) :=
  fun ν z => V ν (ofs y (rep (0 : Site (4 * h + 2)) h z))

def refForm (h : ℕ) (B : Fin 4 → Site n → Mat) (y : Site n) : Fin 4 → Site (4 * h + 2) → Mat :=
  fun ν z => B ν (ofs y (rep (0 : Site (4 * h + 2)) h z))

instance (h : ℕ) : NeZero (4 * h + 2) := ⟨by omega⟩

lemma agree_ref (h : ℕ) (V : Config N n) (B : Fin 4 → Site n → Mat) (y : Site n) :
    Agree h V B y (refConfig h V y) (refForm h B y) 0 := by
  intro v hv ν
  have hr : rep (0 : Site (4 * h + 2)) h (ofs 0 v) = v := rep_ofs 0 h fun σ => by
    have := hv σ; push_cast; constructor <;> omega
  simp only [refConfig, refForm, hr, and_self]

/-- **`prop:relative-average`(viii), the reference function**: `𝓜_𝐔(A)(c)` is the value of the relative average of the
reference torus at the bond `(0, Le_μ)`, applied to the data of the box. -/
theorem relAvg_reference (h : ℕ) (V : Config N n) (B : Fin 4 → Site n → Mat) (y : Site n) (μ : Fin 4) :
    relAvg V B y μ h = relAvg (refConfig h V y) (refForm h B y) 0 μ h :=
  relAvg_transfer μ (agree_ref h V B y)

end RelativeAverage
end CoreLean

end
