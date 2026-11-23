/-
`prop:relative-average`(viii) of BALABAN_CORE.tex (`d8bdc4ac1777`), first part: the paths of the averages are the
images of paths of `ℤ⁴`, and their holonomies are functions of the values `f(v, ν) = 𝐔_ν(y + v)` on the bonds of a
fixed box of `ℤ⁴`, which do not depend on `y` or on the torus.

* `IBond`, `ib y`: the bonds of `ℤ⁴` and their images `(v, ν, s) ↦ (y + v, ν, s)` in the torus.
* `iseg`, `isegZ`, `istair`: the integer versions of `seg`, `segZ`, `stair`; `seg_map`, `segZ_map`, `stair_map`.
* `holI f γ`: the holonomy of the integer configuration `f`; `hol_map`: `𝐔(ib y γ) = holI f_{𝐔,y} γ`.
* `irv`, `rv_map`: reversal commutes with the images.
-/
import CoreLean.RelativeAverageGaugeDir

open Matrix NormedSpace

noncomputable section

namespace CoreLean
namespace RelativeAverage

open LatticePaths LatticeKappa RegularAverages BlockPaths AverageHolo MeanTransports AxialReference

variable {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "GLN" => (Matrix (Fin N) (Fin N) ℂ)ˣ

/-- A bond of `ℤ⁴`: its initial point, its direction, and its orientation. -/
abbrev IBond := (Fin 4 → ℤ) × Fin 4 × Bool

/-- The displacement `±e_ρ` of a step. -/
def idv (ρ : Fin 4) (s : Bool) : Fin 4 → ℤ := if s then Pi.single ρ 1 else -Pi.single ρ 1

/-- The integer segment of `k` steps from `v` in the direction `±e_ρ`. -/
def iseg (ρ : Fin 4) (s : Bool) : (Fin 4 → ℤ) → ℕ → List IBond
  | _, 0 => []
  | v, k + 1 => (v, ρ, s) :: iseg ρ s (v + idv ρ s) k

/-- The integer segment from `v` to `v + ke_μ`. -/
def isegZ (μ : Fin 4) (v : Fin 4 → ℤ) (k : ℤ) : List IBond :=
  if 0 ≤ k then iseg μ true v k.toNat else iseg μ false v (-k).toNat

/-- The integer staircase path. -/
def istair (m : Fin 4 → ℤ) : List (Fin 4) → (Fin 4 → ℤ) → List IBond
  | [], _ => []
  | μ :: l, o => isegZ μ o (m μ) ++ istair m l (o + Pi.single μ (m μ))

/-- The reversed integer bond. -/
def irev (b : IBond) : IBond := (b.1 + idv b.2.1 b.2.2, b.2.1, !b.2.2)

/-- The reversed integer path. -/
def irv (γ : List IBond) : List IBond := (γ.map irev).reverse

/-- The value of an integer configuration `f(v, ν) = 𝐔_ν(v)` on an integer bond. -/
def valI (f : (Fin 4 → ℤ) → Fin 4 → GLN) (b : IBond) : GLN :=
  if b.2.2 then f b.1 b.2.1 else (f (b.1 - Pi.single b.2.1 1) b.2.1)⁻¹

/-- The holonomy of an integer configuration along an integer path. -/
def holI (f : (Fin 4 → ℤ) → Fin 4 → GLN) (γ : List IBond) : GLN := (γ.map (valI f)).prod

variable {n : ℕ} [NeZero n]

/-- The image of an integer bond in the torus, from the base point `y`. -/
def ib (y : Site n) (b : IBond) : Bond n := ⟨ofs y b.1, b.2.1, b.2.2⟩

/-- The integer configuration `f_{𝐔,y}(v, ν) = 𝐔_ν(y + v)`. -/
def fC (V : Config N n) (y : Site n) : (Fin 4 → ℤ) → Fin 4 → GLN := fun v ν => V ν (ofs y v)

lemma ofs_idv (y : Site n) (v : Fin 4 → ℤ) (ρ : Fin 4) (s : Bool) :
    ofs y (v + idv ρ s) = ofs y v + dvec ρ s := by
  cases s
  · simp only [idv, dvec, Bool.false_eq_true, ↓reduceIte, ← sub_eq_add_neg]
    rw [show v - Pi.single ρ 1 = v + Pi.single ρ (-1) by funext σ; by_cases h : σ = ρ <;> simp [h, sub_eq_add_neg],
      ofs_add_single]
    simp [unit, sub_eq_add_neg]
  · simp only [idv, dvec, ↓reduceIte]
    rw [ofs_add_single]; simp

lemma seg_map (y : Site n) (ρ : Fin 4) (s : Bool) :
    ∀ (k : ℕ) (v : Fin 4 → ℤ), seg ρ s (ofs y v) k = (iseg ρ s v k).map (ib y)
  | 0, _ => rfl
  | k + 1, v => by
    simp only [seg, iseg, List.map_cons, ib]
    rw [← ofs_idv, seg_map y ρ s k]

lemma segZ_map (y : Site n) (μ : Fin 4) (v : Fin 4 → ℤ) (k : ℤ) :
    segZ μ (ofs y v) k = (isegZ μ v k).map (ib y) := by
  unfold segZ isegZ
  split_ifs <;> exact seg_map y μ _ _ v

lemma stair_map (y : Site n) (m : Fin 4 → ℤ) :
    ∀ (l : List (Fin 4)) (o : Fin 4 → ℤ), stair y m l o = (istair m l o).map (ib y)
  | [], _ => rfl
  | μ :: l, o => by
    simp only [stair, istair, List.map_append]
    rw [segZ_map, stair_map y m l]

lemma rev_ib (y : Site n) (b : IBond) : (ib y b).rev = ib y (irev b) := by
  obtain ⟨v, ν, s⟩ := b
  simp only [Bond.rev, ib, irev]
  rw [ofs_idv, ← rung_plus]

lemma rv_map (y : Site n) (γ : List IBond) : rv (γ.map (ib y)) = (irv γ).map (ib y) := by
  simp only [rv, irv, List.map_map, List.map_reverse]
  congr 1
  refine List.map_congr_left fun b _ => ?_
  simp only [Function.comp_apply, rev_ib]

/-- The value of a configuration on the image of an integer bond. -/
lemma val_ib (V : Config N n) (y : Site n) (b : IBond) : V.val (ib y b) = valI (fC V y) b := by
  obtain ⟨v, ν, s⟩ := b
  cases s
  · simp only [Config.val, ib, valI, fC, Bool.false_eq_true, ↓reduceIte]
    congr 2
    rw [show v - Pi.single ν 1 = v + Pi.single ν (-1) by funext σ; by_cases h : σ = ν <;> simp [h, sub_eq_add_neg],
      ofs_add_single]
    simp [unit, sub_eq_add_neg]
  · simp [Config.val, ib, valI, fC]

/-- **The holonomy of the image of an integer path** is the holonomy of the integer configuration `f_{𝐔,y}`. -/
theorem hol_map (V : Config N n) (y : Site n) (γ : List IBond) : V.hol (γ.map (ib y)) = holI (fC V y) γ := by
  simp only [Config.hol, holI, List.map_map]
  congr 1
  exact List.map_congr_left fun b _ => val_ib V y b

/-- Integer configurations which agree on the positive bonds used by a path have the same holonomy along it. -/
lemma holI_congr {f g : (Fin 4 → ℤ) → Fin 4 → GLN} :
    ∀ γ : List IBond, (∀ b ∈ γ, valI f b = valI g b) → holI f γ = holI g γ
  | [], _ => rfl
  | b :: γ, h => by
    have ih := holI_congr γ fun b' hb' => h b' (by simp [hb'])
    simp only [holI, List.map_cons, List.prod_cons] at ih ⊢
    rw [h b (by simp), ih]

/-! ### The positive bonds used by the paths -/

/-- The positive bond whose value enters the value on `b`: `b` itself if positive, `b⁻¹` otherwise. -/
def ipos (b : IBond) : Fin 4 → ℤ := if b.2.2 then b.1 else b.1 - Pi.single b.2.1 1

lemma valI_congr {f g : (Fin 4 → ℤ) → Fin 4 → GLN} {b : IBond} (h : f (ipos b) b.2.1 = g (ipos b) b.2.1) :
    valI f b = valI g b := by
  obtain ⟨v, ν, s⟩ := b
  cases s <;> simp_all [valI, ipos]

lemma ipos_irev (b : IBond) : ipos (irev b) = ipos b := by
  obtain ⟨v, ν, s⟩ := b
  cases s <;> simp [ipos, irev, idv, sub_eq_add_neg, add_assoc]

/-- The positions of a segment: only the coordinate `ρ` moves, within `k` steps of `v`. -/
lemma ipos_iseg (ρ : Fin 4) (s : Bool) : ∀ (k : ℕ) (v : Fin 4 → ℤ), ∀ b ∈ iseg ρ s v k,
    (∀ σ, σ ≠ ρ → ipos b σ = v σ) ∧ b.2.1 = ρ ∧
      (if s then v ρ ≤ ipos b ρ ∧ ipos b ρ ≤ v ρ + k - 1 else v ρ - k ≤ ipos b ρ ∧ ipos b ρ ≤ v ρ - 1)
  | 0, _, b, hb => by simp [iseg] at hb
  | k + 1, v, b, hb => by
    simp only [iseg, List.mem_cons] at hb
    rcases hb with rfl | hb
    · refine ⟨fun σ hσ => ?_, rfl, ?_⟩
      · cases s <;> simp [ipos, Pi.single_apply, hσ]
      · cases s <;> simp [ipos] <;> omega
    · obtain ⟨h1, h2, h3⟩ := ipos_iseg ρ s k (v + idv ρ s) b hb
      refine ⟨fun σ hσ => ?_, h2, ?_⟩
      · rw [h1 σ hσ]; cases s <;> simp [idv, Pi.single_apply, hσ]
      · cases s <;> simp [idv] at h3 ⊢ <;> push_cast at h3 ⊢ <;> omega

lemma ipos_isegZ (μ : Fin 4) (v : Fin 4 → ℤ) (k : ℤ) : ∀ b ∈ isegZ μ v k,
    (∀ σ, σ ≠ μ → ipos b σ = v σ) ∧ min (v μ) (v μ + k) ≤ ipos b μ ∧ ipos b μ ≤ max (v μ) (v μ + k) := by
  intro b hb
  unfold isegZ at hb
  split_ifs at hb with hk
  · obtain ⟨h1, -, h3⟩ := ipos_iseg μ true _ v b hb
    simp only [↓reduceIte] at h3
    refine ⟨h1, ?_, ?_⟩ <;> omega
  · obtain ⟨h1, -, h3⟩ := ipos_iseg μ false _ v b hb
    simp only [Bool.false_eq_true, ↓reduceIte] at h3
    refine ⟨h1, ?_, ?_⟩ <;> omega

/-- The positions of a staircase path: unchanged off the list, between `o_σ` and `o_σ + m_σ` on it. -/
lemma ipos_istair (m : Fin 4 → ℤ) : ∀ (l : List (Fin 4)) (o : Fin 4 → ℤ), l.Nodup → ∀ b ∈ istair m l o, ∀ σ,
    (σ ∉ l → ipos b σ = o σ) ∧ (σ ∈ l → min (o σ) (o σ + m σ) ≤ ipos b σ ∧ ipos b σ ≤ max (o σ) (o σ + m σ))
  | [], _, _, b, hb, _ => by simp [istair] at hb
  | μ :: l, o, hnd, b, hb, σ => by
    have hμ : μ ∉ l := (List.nodup_cons.1 hnd).1
    simp only [istair, List.mem_append] at hb
    rcases hb with hb | hb
    · obtain ⟨h1, h2, h3⟩ := ipos_isegZ μ o (m μ) b hb
      by_cases hσ : σ = μ
      · subst hσ
        exact ⟨fun h => absurd (List.mem_cons_self) h, fun _ => ⟨h2, h3⟩⟩
      · rw [h1 σ hσ]
        refine ⟨fun _ => rfl, fun _ => ⟨?_, ?_⟩⟩ <;> omega
    · have := ipos_istair m l _ (List.nodup_cons.1 hnd).2 b hb σ
      by_cases hσ : σ = μ
      · subst hσ
        have e := this.1 hμ
        simp only [Pi.add_apply, Pi.single_eq_same] at e
        exact ⟨fun h => absurd (List.mem_cons_self) h, fun _ => ⟨by omega, by omega⟩⟩
      · simp only [Pi.add_apply, Pi.single_eq_of_ne hσ, add_zero] at this
        refine ⟨fun h => this.1 (fun h' => h (List.mem_cons_of_mem _ h')), fun h => ?_⟩
        exact this.2 ((List.mem_cons.1 h).resolve_left hσ)

/-- The positions of the block paths of `𝐆(y, x)`, from the offset `o`, lie in `o + [-h, h]⁴`. -/
lemma ipos_block {h : ℕ} (x : Pts h) (Γ : Ords (offP h x)) (o : Fin 4 → ℤ) :
    ∀ b ∈ istair (offP h x) (ordG h x Γ) o, ∀ σ, o σ - h ≤ ipos b σ ∧ ipos b σ ≤ o σ + h := by
  intro b hb σ
  have hnd : (ordG h x Γ).Nodup := (ordG_perm h x Γ).nodup_iff.2 (by decide)
  have hc := (offP_inM h x) σ
  have := ipos_istair (offP h x) _ o hnd b hb σ
  by_cases hσ : σ ∈ ordG h x Γ
  · obtain ⟨h1, h2⟩ := this.2 hσ
    constructor <;> omega
  · rw [this.1 hσ]; constructor <;> omega

end RelativeAverage
end CoreLean

end
