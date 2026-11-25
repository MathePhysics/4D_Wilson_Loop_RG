/-
The bridge from the chain of averages of `MultiscaleAverages` (the tori `T^{(j)}` of the sides `nn h m k j`, the map
`up : T^{(j+1)} → T^{(j)}`, `y ↦ Ly`) to the per-level framework of `RelativeAverageLevels` and
`RelativeAverageKernels` (the sites `img h (base l) l x = base l + x/Lˡ` of the points `x ∈ Lˡℤ⁴`).

* `up_natCast`, `up_add`, `up_intCast`: `up` is the group homomorphism `y ↦ Ly`.
* `up_ofs`: `up (ofs y v) = ofs (up y) (Lv)`.
* `up_img`: for base points with `up (base (l+1)) = base l`, `up (img (l+1) x) = img l x` on `L^{l+1}ℤ⁴`.
-/
import CoreLean.MultiscaleAverages
import CoreLean.AxialStraightLattice
import CoreLean.RelativeAverageTrivial
import CoreLean.RelativeAverageLevels
import CoreLean.AverageKernelsDiff

open Finset
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace CoreLean
namespace LevelsBridge

open MultiscaleAverages LatticePaths AxialStraightLattice RelativeAverage AverageHolo LatticeKappa

variable (h m k : ℕ)

/-- The key congruence: `L·(s mod n') ≡ L·s mod Ln'`. -/
lemma cast_mul_mod (L n' s : ℕ) : (((L * (s % n') : ℕ)) : ZMod (L * n')) = ((L * s : ℕ) : ZMod (L * n')) := by
  rw [ZMod.natCast_eq_natCast_iff', Nat.mul_mod_mul_left, Nat.mul_mod_mul_left, Nat.mod_mod]

lemma up_apply (j : ℕ) (y : Site (nn h m k (j + 1))) (ν : Fin 4) :
    up h m k j y ν = (((2 * h + 1) * (y ν).val : ℕ) : ZMod (nn h m k j)) := rfl

/-- `up` is additive. -/
lemma up_add (j : ℕ) (hj : j < k) (y z : Site (nn h m k (j + 1))) :
    up h m k j (y + z) = up h m k j y + up h m k j z := by
  funext ν
  simp only [up_apply, Pi.add_apply]
  have hn := nn_succ h m k j hj
  rw [ZMod.val_add, ← Nat.cast_add, ← mul_add]
  rw [show ((2 * h + 1) * (((y ν).val + (z ν).val) % nn h m k (j + 1)) : ℕ) =
    (2 * h + 1) * (((y ν).val + (z ν).val) % nn h m k (j + 1)) from rfl]
  have := cast_mul_mod (2 * h + 1) (nn h m k (j + 1)) ((y ν).val + (z ν).val)
  rw [← hn] at this
  exact this

/-- `up` of an integer point: `up (v : ℤ⁴) = Lv`. -/
lemma up_intCast (j : ℕ) (hj : j < k) (v : Fin 4 → ℤ) :
    up h m k j (fun σ => (v σ : ZMod (nn h m k (j + 1)))) = fun σ => (((2 * h + 1 : ℕ) : ℤ) * v σ : ZMod (nn h m k j)) := by
  funext ν
  simp only [up_apply]
  have hn := nn_succ h m k j hj
  have hv : (((v ν : ZMod (nn h m k (j + 1)))).val : ℤ) = v ν % (nn h m k (j + 1) : ℤ) := ZMod.val_intCast _
  have e1 : (((2 * h + 1) * (v ν : ZMod (nn h m k (j + 1))).val : ℕ) : ZMod (nn h m k j)) =
      ((((2 * h + 1 : ℕ) : ℤ) * (((v ν : ZMod (nn h m k (j + 1)))).val : ℤ) : ℤ) : ZMod (nn h m k j)) := by
    push_cast; ring
  have e2 : ((((2 * h + 1 : ℕ) : ℤ) : ZMod (nn h m k j)) * ((v ν : ℤ) : ZMod (nn h m k j))) =
      ((((2 * h + 1 : ℕ) : ℤ) * v ν : ℤ) : ZMod (nn h m k j)) := by push_cast; ring
  rw [e1, hv, e2, ZMod.intCast_eq_intCast_iff', hn]
  push_cast
  rw [Int.mul_emod_mul_of_pos _ _ (by positivity), Int.mul_emod_mul_of_pos _ _ (by positivity), Int.emod_emod]

/-- `up (y + v) = up y + Lv`. -/
lemma up_ofs (j : ℕ) (hj : j < k) (y : Site (nn h m k (j + 1))) (v : Fin 4 → ℤ) :
    up h m k j (ofs y v) = ofs (up h m k j y) (fun σ => Lz h * v σ) := by
  unfold ofs
  rw [up_add h m k j hj, up_intCast h m k j hj]
  congr 1
  funext σ
  simp only [Lz]
  push_cast
  ring

open BoxGeometry in
/-- **The sites of the levels**: for base points with `up (base (l+1)) = base l`,
`up (img (l+1) x) = img l x` for `x ∈ L^{l+1}ℤ⁴`. -/
lemma up_img (base : ∀ l, Site (nn h m k l)) (l : ℕ) (hl : l < k)
    (hbase : up h m k l (base (l + 1)) = base l) (x : Fin 4 → ℤ) (hx : Lat (Lz h) (l + 1) x) :
    up h m k l (img h (base (l + 1)) (l + 1) x) = img h (base l) l x := by
  unfold img
  rw [up_ofs h m k l hl, hbase]
  congr 1
  funext σ
  obtain ⟨q, hq⟩ := hx σ
  have hL : Lz h ≠ 0 := by unfold Lz; omega
  simp only [qt, hq]
  rw [Int.mul_ediv_cancel_left _ (pow_ne_zero _ hL), pow_succ, mul_comm (Lz h ^ l) (Lz h), mul_assoc,
    mul_left_comm, Int.mul_ediv_cancel_left _ (pow_ne_zero _ hL)]

/-- **The base points of the levels**: `base_l = L^{j-l}c` for an integer point `c` of the top level `j`. -/
def baseOf (c : Fin 4 → ℤ) (j l : ℕ) : Site (nn h m k l) := fun σ => ((Lz h ^ (j - l) * c σ : ℤ) : ZMod (nn h m k l))

lemma base_up (c : Fin 4 → ℤ) (j l : ℕ) (hl : l < j) (hlk : l < k) :
    up h m k l (baseOf h m k c j (l + 1)) = baseOf h m k c j l := by
  unfold baseOf
  rw [up_intCast h m k l hlk]
  funext σ
  have e : j - l = (j - (l + 1)) + 1 := by omega
  simp only [Lz]
  rw [e, pow_succ]
  push_cast
  ring

variable {N : ℕ}

open BoxGeometry in
/-- **The levels of the chain are the levels of the framework**: with the canonical average (`LogM`),
`M^{l+1}(U)(img (l+1) x) = avgM(M^l(U))(img l x)` (`Mcfg_LogM` and `up_img`). -/
lemma mpow_level (U : Config N (nn h m k 0)) (c : Fin 4 → ℤ) (j l : ℕ) (hl : l < j) (hlk : l < k) (ρ : Fin 4)
    (x : Fin 4 → ℤ) (hx : Lat (Lz h) (l + 1) x) :
    Mpow h m k (fun _ => True) (fun W => LogM (W : Matrix (Fin N) (Fin N) ℂ)) U (l + 1) ρ
        (img h (baseOf h m k c j (l + 1)) (l + 1) x) =
      avgM (Mpow h m k (fun _ => True) (fun W => LogM (W : Matrix (Fin N) (Fin N) ℂ)) U l)
        (img h (baseOf h m k c j l) l x) ρ h := by
  change Mcfg h m k (fun _ => True) (fun W => LogM (W : Matrix (Fin N) (Fin N) ℂ)) l
    (Mpow h m k (fun _ => True) (fun W => LogM (W : Matrix (Fin N) (Fin N) ℂ)) U l) ρ
      (img h (baseOf h m k c j (l + 1)) (l + 1) x) = _
  rw [Mcfg_LogM, up_img h m k (baseOf h m k c j) l hlk (base_up h m k c j l hl hlk) x hx]

/-- The levels of the trivial configuration are trivial. -/
lemma mpow_oneC : ∀ l, Mpow h m k (fun _ => True) (fun W => LogM (W : Matrix (Fin N) (Fin N) ℂ)) oneC l = oneC
  | 0 => rfl
  | l + 1 => by
      funext ρ y
      change Mcfg h m k (fun _ => True) (fun W => LogM (W : Matrix (Fin N) (Fin N) ℂ)) l
        (Mpow h m k (fun _ => True) (fun W => LogM (W : Matrix (Fin N) (Fin N) ℂ)) oneC l) ρ y = _
      rw [mpow_oneC l, Mcfg_LogM, avgM_oneC]
      rfl

/-! ### The levels of `e^{iX}` -/

/-- The forms of the levels of the pair `(0, X)` at the trivial gauge field: `B'_{l+1}(y) = (1/i)Log𝓜_{id}(B'_l)(Ly)`. -/
def Bchain (A0 : Fin 4 → Site (nn h m k 0) → Matrix (Fin N) (Fin N) ℂ) :
    ∀ l, Fin 4 → Site (nn h m k l) → Matrix (Fin N) (Fin N) ℂ
  | 0 => A0
  | l + 1 => fun ρ y => relLog oneC (Bchain A0 l) (up h m k l y) ρ h

/-- The gauge transformations of the levels: `g'_{l+1}(y) = g'_l(Ly)·(site factor)`. -/
def gchain (A0 : Fin 4 → Site (nn h m k 0) → Matrix (Fin N) (Fin N) ℂ) :
    ∀ l, Site (nn h m k l) → (Matrix (Fin N) (Fin N) ℂ)ˣ
  | 0 => fun _ => 1
  | l + 1 => fun y => gchain A0 l (up h m k l y) * siteFactor oneC (Bchain h m k A0 l) (up h m k l y) h

lemma relLog_zero' {n : ℕ} [NeZero n] (V : Config N n) (y : Site n) (μ : Fin 4) :
    relLog V 0 y μ h = 0 := by
  simp [relLog, relAvg_zero, AxialReference.LogM_one]

lemma plaq_oneC {n : ℕ} [NeZero n] (μ ν : Fin 4) (y : Site n) : plaq (oneC (N := N)) μ ν y = 1 := by
  unfold plaq
  exact hol_oneC _

open BoxGeometry in
/-- **`prop:relative-average-order` for `𝐔 = e^{iX}`** (the chain of averages of the trivial field moved by `X`): if
`‖X‖ ≤ t'L^{-n}` on the region of the level `0`, `t' ≤ c`, then on the region of every level `l ≤ n`,
`M^l(e^{iX}) = e^{iA'_l}` with `‖A'_l‖ ≤ K_ot'L^{-(n-l)}` (`order_levels` with `U_l = id`, `B = 0`, `g = 1`). -/
theorem levels_expX (G : GaugeGroup N) (hGc : IsClosed G.mats) (hN : 1 ≤ N) (hh : 1 ≤ h) :
    ∃ c Ko : ℝ, 0 < c ∧ 0 ≤ Ko ∧ ∀ (nl : ℕ) (μ : Fin 4), nl ≤ k → (∀ l, 4 * h + 4 ≤ nn h m k l) →
      ∀ (c0 : Fin 4 → ℤ) (X : Fin 4 → Site (nn h m k 0) → Matrix (Fin N) (Fin N) ℂ) (t' : ℝ),
      (∀ ρ x, Lat (Lz h) 0 x → Rg h nl μ 0 x → Rg h nl μ 0 (x + Lz h ^ 0 • Pi.single ρ 1) →
        ‖X ρ (img h (baseOf h m k c0 nl 0) 0 x)‖ ≤ t' * ((((2 * h + 1 : ℕ) : ℝ)) ^ nl)⁻¹) →
      0 ≤ t' → t' ≤ c →
      ∀ l, l ≤ nl → ∀ ρ x, Lat (Lz h) l x → Rg h nl μ l x → Rg h nl μ l (x + Lz h ^ l • Pi.single ρ 1) →
        ∃ A'l : Matrix (Fin N) (Fin N) ℂ,
          Mpow h m k (fun _ => True) (fun W => LogM (W : Matrix (Fin N) (Fin N) ℂ)) (moveC oneC X) l ρ
              (img h (baseOf h m k c0 nl l) l x) = expU (Complex.I • A'l) ∧
            ‖A'l‖ ≤ Ko * t' * ((((2 * h + 1 : ℕ) : ℝ)) ^ (nl - l))⁻¹ := by
  obtain ⟨c, C₁, Ko, hc, hC₁, hKo, hord⟩ := order_levels G hGc hN h hh
  refine ⟨c, Ko, hc, hKo, ?_⟩
  intro nl μ hnl hn c0 X t' hX ht0 htc l hl ρ x hx1 hx2 hx3
  set V : ∀ l, Config N (nn h m k l) := fun l =>
    Mpow h m k (fun _ => True) (fun W => LogM (W : Matrix (Fin N) (Fin N) ℂ)) (moveC oneC X) l
  have hlev := hord nl μ (nn h m k) hn (baseOf h m k c0 nl) (fun _ => oneC) V V (Bchain h m k X)
    (fun _ => 0) (gchain h m k X) (fun _ _ => 1) 0 t' 0
    (fun _ => fun _ _ => (G.carrier.one_mem))
    (fun l hl ρ x hx _ _ => by
      have hlk : l < k := lt_of_lt_of_le hl hnl
      have hup := up_img h m k (baseOf h m k c0 nl) l hlk (base_up h m k c0 nl l hl hlk) x hx
      refine ⟨(avgM_oneC _ _ _).symm, mpow_level h m k _ c0 nl l hl hlk ρ x hx,
        mpow_level h m k _ c0 nl l hl hlk ρ x hx, ?_, (relLog_zero' h _ _ _).symm⟩
      show relLog oneC (Bchain h m k X l) (up h m k l (img h (baseOf h m k c0 nl (l + 1)) (l + 1) x)) ρ h = _
      rw [hup])
    (fun l hl x hx _ => by
      have hlk : l < k := lt_of_lt_of_le hl hnl
      have hup := up_img h m k (baseOf h m k c0 nl) l hlk (base_up h m k c0 nl l hl hlk) x hx
      refine ⟨?_, by simp [siteFactor_zero]⟩
      show gchain h m k X l (up h m k l (img h (baseOf h m k c0 nl (l + 1)) (l + 1) x)) *
        siteFactor oneC (Bchain h m k X l) (up h m k l (img h (baseOf h m k c0 nl (l + 1)) (l + 1) x)) h = _
      rw [hup])
    (fun _ => rfl) (fun _ => rfl)
    (fun ρ x _ _ _ => ⟨rfl, by simp [V, moveC_zero], hX ρ x ‹_› ‹_› ‹_›, by simp⟩)
    (fun μ' ν' x _ _ _ _ _ => by simp [plaq_oneC, RegularAverages.hs_zero'])
    le_rfl ht0 le_rfl hc.le htc hc.le l hl
  obtain ⟨⟨A'l, hA, hAn⟩, -, -⟩ := hlev.1 ρ x hx1 hx2 hx3
  exact ⟨A'l, by simpa [oneC] using hA, hAn⟩

/-! ### The difference of the composite linear parts at `e^{iX}` and at `id` -/

lemma oneC_gauge {n : ℕ} [NeZero n] : (oneC : Config N n).IsGaugeField := fun _ _ => by
  simpa [oneC] using (Matrix.unitaryGroup (Fin N) ℂ).one_mem

lemma qcomp_succ_apply (U : Config N (nn h m k 0)) (B : Fin 4 → Site (nn h m k 0) → Matrix (Fin N) (Fin N) ℂ)
    (l : ℕ) (ρ : Fin 4) (y : Site (nn h m k (l + 1))) :
    Qcomp h m k (fun _ => True) (fun W => LogM (W : Matrix (Fin N) (Fin N) ℂ)) U (l + 1) B ρ y =
      Qlin (Mpow h m k (fun _ => True) (fun W => LogM (W : Matrix (Fin N) (Fin N) ℂ)) U l) (up h m k l y) ρ h
        (Qcomp h m k (fun _ => True) (fun W => LogM (W : Matrix (Fin N) (Fin N) ℂ)) U l B) := rfl

open BoxGeometry Classical in
/-- **`Q_n(e^{iX}) - Q_n(id)` in the per-level norms**: with `E_l = Lˡ(Q_l(e^{iX}) - Q_l(id))B` and `‖X‖ ≤ t'L^{-n}`
on the region of the level `0`, `t', K_ot' ≤ c`, `‖E_n‖_{1,n} ≤ (e^{Σ_l 8L³CK_ot'L^{-(n-l)}} - 1)L^{-3n}‖B‖_{1,0}`
(`levels_expX` and `average_kernels_diff`). -/
theorem qcomp_diff (G : GaugeGroup N) (hGc : IsClosed G.mats) (hN : 1 ≤ N) (hh : 1 ≤ h) :
    ∃ c Ko C : ℝ, 0 < c ∧ 0 ≤ Ko ∧ 0 ≤ C ∧ ∀ (nl : ℕ) (μ : Fin 4), nl ≤ k → (∀ l, 4 * h + 4 ≤ nn h m k l) →
      ∀ (c0 : Fin 4 → ℤ) (X B : Fin 4 → Site (nn h m k 0) → Matrix (Fin N) (Fin N) ℂ) (t' : ℝ),
      (∀ ρ x, Lat (Lz h) 0 x → Rg h nl μ 0 x → Rg h nl μ 0 (x + Lz h ^ 0 • Pi.single ρ 1) →
        ‖X ρ (img h (baseOf h m k c0 nl 0) 0 x)‖ ≤ t' * ((((2 * h + 1 : ℕ) : ℝ)) ^ nl)⁻¹) →
      0 ≤ t' → t' ≤ c → Ko * t' ≤ c →
      ell1 h nl μ nl (fun x ν => ‖(((((2 * h + 1 : ℕ) : ℂ)) ^ nl) •
          (Qcomp h m k (fun _ => True) (fun W => LogM (W : Matrix (Fin N) (Fin N) ℂ)) (moveC oneC X) nl B -
            Qcomp h m k (fun _ => True) (fun W => LogM (W : Matrix (Fin N) (Fin N) ℂ)) oneC nl B)) ν
              (img h (baseOf h m k c0 nl nl) nl x)‖) ≤
        (Real.exp (∑ l ∈ Finset.range nl, 8 * (((2 * h + 1 : ℕ) : ℝ)) ^ 3 * C *
            (Ko * t' * ((((2 * h + 1 : ℕ) : ℝ)) ^ (nl - l))⁻¹)) - 1) *
          (((((2 * h + 1 : ℕ) : ℝ) ^ 3)⁻¹) ^ nl *
            ell1 h nl μ 0 (fun x ν => ‖B ν (img h (baseOf h m k c0 nl 0) 0 x)‖)) := by
  obtain ⟨c1, Ko, hc1, hKo, hlev⟩ := levels_expX h m k G hGc hN hh
  obtain ⟨c2, C, hc2, hC, hdiff⟩ := average_kernels_diff (N := N) h
  refine ⟨min c1 c2, Ko, C, lt_min hc1 hc2, hKo, hC, ?_⟩
  intro nl μ hnl hn c0 X B t' hX ht0 htc hKtc
  set Lc : ℂ := ((2 * h + 1 : ℕ) : ℂ)
  set Lr : ℝ := ((2 * h + 1 : ℕ) : ℝ)
  have hL1 : (1 : ℝ) ≤ Lr := by simp only [Lr]; push_cast; have : (0 : ℝ) ≤ h := Nat.cast_nonneg _; linarith
  set U' := moveC oneC X
  set V : ∀ l, Config N (nn h m k l) := fun l =>
    Mpow h m k (fun _ => True) (fun W => LogM (W : Matrix (Fin N) (Fin N) ℂ)) U' l
  set base := baseOf h m k c0 nl
  set a₁ : ℕ → ℝ := fun l => Ko * t' * (Lr ^ (nl - l))⁻¹
  have ha₁c : ∀ l, 0 ≤ a₁ l ∧ a₁ l ≤ c2 := fun l => by
    have hp : (Lr ^ (nl - l))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hL1)
    have h0 : 0 ≤ Ko * t' := mul_nonneg hKo ht0
    refine ⟨by positivity, ?_⟩
    calc a₁ l ≤ Ko * t' * 1 := mul_le_mul_of_nonneg_left hp h0
      _ ≤ c2 := by rw [mul_one]; exact hKtc.trans (min_le_right _ _)
  -- the fields of the levels, by choice
  set A'f : ∀ l, Fin 4 → Site (nn h m k l) → Matrix (Fin N) (Fin N) ℂ := fun l ν z =>
    if hz : ∃ A : Matrix (Fin N) (Fin N) ℂ, V l ν z = expU (Complex.I • A) ∧ ‖A‖ ≤ a₁ l then hz.choose else 0
  have hreg : ∀ l, l ≤ nl → ∀ ν x, Lat (Lz h) l x → Rg h nl μ l x → Rg h nl μ l (x + Lz h ^ l • Pi.single ν 1) →
      V l ν (img h (base l) l x) = expU (Complex.I • A'f l ν (img h (base l) l x)) ∧
        ‖A'f l ν (img h (base l) l x)‖ ≤ a₁ l := by
    intro l hl ν x hx1 hx2 hx3
    have hex : ∃ A : Matrix (Fin N) (Fin N) ℂ, V l ν (img h (base l) l x) = expU (Complex.I • A) ∧ ‖A‖ ≤ a₁ l :=
      hlev nl μ hnl hn c0 X t' hX ht0 (htc.trans (min_le_left _ _)) l hl ν x hx1 hx2 hx3
    simp only [A'f, dif_pos hex]
    exact hex.choose_spec
  -- the two chains
  set D : ∀ l, Fin 4 → Site (nn h m k l) → Matrix (Fin N) (Fin N) ℂ := fun l =>
    Lc ^ l • Qcomp h m k (fun _ => True) (fun W => LogM (W : Matrix (Fin N) (Fin N) ℂ)) oneC l B
  set E : ∀ l, Fin 4 → Site (nn h m k l) → Matrix (Fin N) (Fin N) ℂ := fun l =>
    Lc ^ l • (Qcomp h m k (fun _ => True) (fun W => LogM (W : Matrix (Fin N) (Fin N) ℂ)) U' l B -
      Qcomp h m k (fun _ => True) (fun W => LogM (W : Matrix (Fin N) (Fin N) ℂ)) oneC l B)
  have hup : ∀ l, l < nl → ∀ x, Lat (Lz h) (l + 1) x →
      up h m k l (img h (base (l + 1)) (l + 1) x) = img h (base l) l x := fun l hl x hx =>
    up_img h m k base l (lt_of_lt_of_le hl hnl) (base_up h m k c0 nl l hl (lt_of_lt_of_le hl hnl)) x hx
  have h := hdiff nl μ (nn h m k) hn base (fun _ => oneC) V A'f E D a₁ (fun _ => oneC_gauge)
    (fun l hl ν x hx1 hx2 hx3 => by
      rw [(hreg l hl.le ν x hx1 hx2 hx3).1]
      simp [moveC, oneC])
    (fun l hl ρ x hx q0 q1 => ⟨fun μ' ν' z _ => by simp [plaq_oneC, RegularAverages.hs_zero'],
      fun ν z hb => by
        obtain ⟨x', hx', r0, r1, rfl⟩ := box_site (hn l) (base l) hx q0 q1 hb
        exact (hreg l hl.le ν x' hx' r0 r1).2⟩)
    (fun l _ => ha₁c l)
    (fun l hl ρ x hx _ _ => by
      simp only [D, Pi.smul_apply, qcomp_succ_apply, mpow_oneC, hup l hl x hx, map_smul, smul_smul, pow_succ]
      ring_nf)
    (fun l hl ρ x hx _ _ => by
      have hsum : E l + D l = Lc ^ l • Qcomp h m k (fun _ => True)
          (fun W => LogM (W : Matrix (Fin N) (Fin N) ℂ)) U' l B := by
        simp only [E, D, smul_sub, sub_add_cancel]
      rw [add_sub_assoc', ← smul_add, ← map_add, hsum]
      simp only [E, Pi.smul_apply, Pi.sub_apply, qcomp_succ_apply, mpow_oneC, hup l hl x hx, map_smul, smul_smul,
        pow_succ, smul_sub]
      simp only [V, D, map_smul, smul_smul]
      ring_nf)
    (by simp [E, ell1])
  simpa [D, E] using h

end LevelsBridge
end CoreLean

end
