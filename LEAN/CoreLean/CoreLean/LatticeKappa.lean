/-
The geometric hypothesis of `kappa_bound` (MeanTransports) discharged on the lattice: for a `G`-valued field
whose plaquettes in a box containing `y` and `x = y + Σ m_σ e_σ` are at most `β`, the staircase paths of
`𝐆(y, x)` (`def:block-paths`(i), one for each ordering of the four coordinates) satisfy
`‖W(Γ)W(Γ_x)⁻¹ - 1‖ ≤ 6h²β` with `h ≥ |m_σ|` (`blockPaths_bound`), and hence the conclusions of
`kappa_bound` with `b = 6h²β`: `W(Γ) = e^{iY(Γ)}W(Γ_x)`, `Y(Γ) ∈ 𝔤`, `‖Y(Γ)‖ ≤ (π/2)b`, the mean satisfies
`eq:group-mean`, and `‖mean - W(Γ_x)‖ ≤ 2πb`.
-/
import CoreLean.MeanTransports
import CoreLean.LatticePaths

open Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace CoreLean

namespace LatticeKappa

open LatticePaths MeanTransports

set_option linter.unusedSectionVars false


variable {N n : ℕ} [NeZero n]

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "GLN" => (Matrix (Fin N) (Fin N) ℂ)ˣ

/-- A configuration with values in the gauge group `G`. -/
def IsGField (G : GaugeGroup N) (U : Config N n) : Prop := ∀ μ x, U μ x ∈ G.carrier

lemma IsGField.gauge {G : GaugeGroup N} {U : Config N n} (hU : IsGField G U) : U.IsGaugeField :=
  fun μ x => G.unitary _ (hU μ x)

lemma IsGField.val_mem {G : GaugeGroup N} {U : Config N n} (hU : IsGField G U) (b : Bond n) :
    U.val b ∈ G.carrier := by
  unfold Config.val
  split_ifs
  · exact hU _ _
  · exact G.carrier.inv_mem (hU _ _)

lemma IsGField.hol_mem {G : GaugeGroup N} {U : Config N n} (hU : IsGField G U) (γ : List (Bond n)) :
    U.hol γ ∈ G.carrier := by
  induction γ with
  | nil => simp [Config.hol]
  | cons b γ ih =>
    simp only [Config.hol, List.map_cons, List.prod_cons]
    exact G.carrier.mul_mem (hU.val_mem b) ih

/-- `kappa_bound` on the lattice. For a family `l` of orderings of the four coordinates containing the
increasing one at `x`, the transports `W(Γ) = U(stair(l Γ))` of a `G`-valued field whose plaquettes in a
box containing the offsets `0` and `m` are at most `β`, with `|m_σ| ≤ h` and `b = 6h²β` small, admit
`Y(Γ) ∈ 𝔤` with `W(Γ) = e^{iY(Γ)}W(Γ_x)` and `‖Y(Γ)‖ ≤ (π/2)b`; the mean satisfies `eq:group-mean` and is
within `2πb` of `W(Γ_x)`. -/
theorem kappa_lattice (G : GaugeGroup N) (hG : IsClosed G.mats) :
    ∃ r : ℝ, 0 < r ∧ ∀ {n : ℕ} [NeZero n] (U : Config N n), IsGField G U → ∀ (y : Site n) (lo hi : Fin 4 → ℤ) (β : ℝ),
      0 ≤ β → PlaqBound U (boxR y lo hi) β → ∀ (m : Fin 4 → ℤ), InBox lo hi 0 → InBox lo hi m →
      ∀ (h : ℝ), (∀ σ, ((m σ).natAbs : ℝ) ≤ h) → 6 * h ^ 2 * β ≤ r →
      512 * (Real.pi / 2 * (6 * h ^ 2 * β)) ≤ 1 →
      ∀ {k : ℕ} (_hk : 0 < k) (l : Fin k → List (Fin 4)), (∀ Γ, (l Γ).Perm [0, 1, 2, 3]) →
      ∀ x, l x = [0, 1, 2, 3] →
      ∃ Y : Fin k → Mat,
        (∀ Γ, U.hol (stair y m (l Γ) 0) = expU (Complex.I • Y Γ) * U.hol (stair y m (l x) 0) ∧
          Y Γ ∈ G.lie ∧ ‖Y Γ‖ ≤ Real.pi / 2 * (6 * h ^ 2 * β)) ∧
        (∑ Γ, LogM ((U.hol (stair y m (l Γ) 0) * (mean Y (U.hol (stair y m (l x) 0)))⁻¹ : GLN) :
          Mat) = 0) ∧
        ‖((mean Y (U.hol (stair y m (l x) 0)) : GLN) : Mat) - U.hol (stair y m (l x) 0)‖ ≤
          2 * Real.pi * (6 * h ^ 2 * β) := by
  obtain ⟨r, hr0, hκ⟩ := GaugeGroup'.kappa_bound G hG
  refine ⟨r, hr0, fun U hU y lo hi β hβ hP m h0 hm h hh hbr hb512 k hk l hl x hx => ?_⟩
  refine hκ hk (fun Γ => U.hol (stair y m (l Γ) 0)) x (fun Γ => hU.hol_mem _) _ hbr hb512
    (fun Γ => ?_)
  show ‖((U.hol (stair y m (l Γ) 0) * (U.hol (stair y m (l x) 0))⁻¹ : GLN) : Mat) - 1‖ ≤ _
  rw [hx]
  exact blockPaths_bound hU.gauge hβ hP m h0 hm hh (l Γ) (hl Γ)

/-- The 24 paths of `𝐆(y, x)`: every ordering of the coordinates satisfies the hypothesis of
`kappa_lattice`, and the increasing ordering is one of them. -/
lemma permutations_family :
    (∀ l ∈ ([0, 1, 2, 3] : List (Fin 4)).permutations, l.Perm [0, 1, 2, 3]) ∧
      [0, 1, 2, 3] ∈ ([0, 1, 2, 3] : List (Fin 4)).permutations ∧
      ([0, 1, 2, 3] : List (Fin 4)).permutations.length = 24 :=
  ⟨fun _ hl => List.mem_permutations.1 hl, List.mem_permutations.2 (List.Perm.refl _),
    by rw [List.length_permutations]; rfl⟩

/-! ### The mean transport -/

/-- `def:group-mean`(i) with `W₁ = W(x)`: `T = e^{iZ}W(x)` with `‖Z‖ ≤ 2⁻⁸` solves `eq:group-mean`.
By `lem:group-mean` the mean does not depend on the order of the elements, and `4ϱ_m ≤ 2⁻⁸`, so the
mean transport `W_m(y, x)` of `def:transports` satisfies this for `W(Γ)`, `Γ ∈ 𝐆(y, x)`, and the
increasing ordering at `x`. -/
def IsMeanOf {k : ℕ} (W : Fin k → GLN) (x : Fin k) (T : GLN) : Prop :=
  ∃ Z : Mat, ‖Z‖ ≤ 1 / 256 ∧ T = expU (Complex.I • Z) * W x ∧
    ∑ Γ, LogM ((W Γ * T⁻¹ : GLN) : Mat) = 0

/-- `eq:axial-path-transport` for the rule `m` on the lattice: the mean transport is within `2πb`,
`b = 6h²β`, of the value on the axial path. -/
theorem transport_lattice (G : GaugeGroup N) (hG : IsClosed G.mats) :
    ∃ r : ℝ, 0 < r ∧ ∀ {n : ℕ} [NeZero n] (U : Config N n), IsGField G U → ∀ (y : Site n) (lo hi : Fin 4 → ℤ) (β : ℝ),
      0 ≤ β → PlaqBound U (boxR y lo hi) β → ∀ (m : Fin 4 → ℤ), InBox lo hi 0 → InBox lo hi m →
      ∀ (h : ℝ), (∀ σ, ((m σ).natAbs : ℝ) ≤ h) → 6 * h ^ 2 * β ≤ r →
      512 * (Real.pi / 2 * (6 * h ^ 2 * β)) ≤ 1 →
      ∀ {k : ℕ} (_hk : 0 < k) (l : Fin k → List (Fin 4)), (∀ Γ, (l Γ).Perm [0, 1, 2, 3]) →
      ∀ x, l x = [0, 1, 2, 3] → ∀ T : GLN, IsMeanOf (fun Γ => U.hol (stair y m (l Γ) 0)) x T →
      ‖(T : Mat) - U.hol (stair y m [0, 1, 2, 3] 0)‖ ≤ 2 * Real.pi * (6 * h ^ 2 * β) := by
  obtain ⟨r, hr0, hκ⟩ := kappa_lattice G hG
  refine ⟨r, hr0, fun U hU y lo hi β hβ hP m h0 hm h hh hbr hb512 k hk l hl x hx T hT => ?_⟩
  obtain ⟨Y, hY, -, hbound⟩ := hκ U hU y lo hi β hβ hP m h0 hm h hh hbr hb512 hk l hl x hx
  obtain ⟨Z, hZ, hTZ, hsum⟩ := hT
  beta_reduce at hTZ hsum
  have hY512 : ∀ Γ, ‖Y Γ‖ ≤ 1 / 512 := fun Γ => (hY Γ).2.2.trans (by linarith)
  have hsum' : ∑ Γ, LogM (((expU (Complex.I • Y Γ) * U.hol (stair y m (l x) 0)) *
      (expU (Complex.I • Z) * U.hol (stair y m (l x) 0))⁻¹ : GLN) : Mat) = 0 := by
    rw [← hsum]
    refine Finset.sum_congr rfl fun Γ _ => ?_
    rw [hTZ, (hY Γ).1]
  have hZY := mean_unique hk hY512 (U.hol (stair y m (l x) 0)) hZ hsum'
  have hTm : T = mean Y (U.hol (stair y m (l x) 0)) := by rw [hTZ, hZY]; rfl
  rw [hTm, ← hx]
  exact hbound

/-! ### `lem:axial-smallness` for a bond in one block -/

lemma norm_mul_inv_sub_one'' {g h : GLN} (hh : LatticePaths.IsU h) :
    ‖((g * h⁻¹ : GLN) : Mat) - 1‖ = ‖(g : Mat) - h‖ := by
  rw [Units.val_mul, LatticePaths.inv_val_eq_star hh]
  exact AxialSmallness.norm_mul_star_sub_one hh

/-- `lem:axial-smallness` for a bond `b = (w, w + e_ρ)` in one block `B(y)`, rule `m`, on the lattice:
two `G`-valued fields whose plaquettes in the box are at most `β` (hypothesis (i)) and whose mean
transports to `w` and to `w + e_ρ` agree (hypothesis (ii): one matrix is the mean of both families)
satisfy `‖V(b)V₀(b)⁻¹ - id‖ ≤ 8πb + 2(Σ_{σ > ρ}|m_σ|)β`, `b = 6h²β`. With the core's numbers
(`2πb ≤ 10√Nα₀`, `3Lβ ≤ √Nα₀`) this is the bound `(4κ + 2√N)α₀` of the proof. -/
theorem axial_one_block_lattice (G : GaugeGroup N) (hG : IsClosed G.mats) :
    ∃ r : ℝ, 0 < r ∧ ∀ {n : ℕ} [NeZero n] (V V0 : Config N n), IsGField G V → IsGField G V0 →
      ∀ (y : Site n) (lo hi : Fin 4 → ℤ) (β : ℝ), 0 ≤ β → PlaqBound V (boxR y lo hi) β →
      PlaqBound V0 (boxR y lo hi) β → ∀ (m : Fin 4 → ℤ) (P S : List (Fin 4)) (ρ : Fin 4),
      P ++ ρ :: S = [0, 1, 2, 3] → InBox lo hi 0 → InBox lo hi m → InBox lo hi (m + Pi.single ρ 1) →
      ∀ (h : ℝ), (∀ σ, ((m σ).natAbs : ℝ) ≤ h) →
      (∀ σ, (((m + Pi.single ρ 1 : Fin 4 → ℤ) σ).natAbs : ℝ) ≤ h) → 6 * h ^ 2 * β ≤ r →
      512 * (Real.pi / 2 * (6 * h ^ 2 * β)) ≤ 1 →
      ∀ {k : ℕ} (_hk : 0 < k) (l : Fin k → List (Fin 4)), (∀ Γ, (l Γ).Perm [0, 1, 2, 3]) →
      ∀ x, l x = [0, 1, 2, 3] → ∀ T T' : GLN,
      IsMeanOf (fun Γ => V.hol (stair y m (l Γ) 0)) x T →
      IsMeanOf (fun Γ => V0.hol (stair y m (l Γ) 0)) x T →
      IsMeanOf (fun Γ => V.hol (stair y (m + Pi.single ρ 1) (l Γ) 0)) x T' →
      IsMeanOf (fun Γ => V0.hol (stair y (m + Pi.single ρ 1) (l Γ) 0)) x T' →
      ‖((V.val ⟨ofs y m, ρ, true⟩ * (V0.val ⟨ofs y m, ρ, true⟩)⁻¹ : GLN) : Mat) - 1‖ ≤
        8 * Real.pi * (6 * h ^ 2 * β) + 2 * ((S.map fun σ => (m σ).natAbs).sum * β) := by
  obtain ⟨r, hr0, htr⟩ := transport_lattice G hG
  refine ⟨r, hr0, fun V V0 hV hV0 y lo hi β hβ hPV hPV0 m P S ρ hPS h0 hm hm' h hh hh' hbr hb512
    k hk l hl x hx T T' hT hT0 hT' hT0' => ?_⟩
  have hnd : (P ++ ρ :: S).Nodup := by rw [hPS]; decide
  have hoffs : offs m (P ++ ρ :: S) = m := offs_perm m (by rw [hPS])
  -- the transports
  have t1 := htr V hV y lo hi β hβ hPV m h0 hm h hh hbr hb512 hk l hl x hx T hT
  have t2 := htr V0 hV0 y lo hi β hβ hPV0 m h0 hm h hh hbr hb512 hk l hl x hx T hT0
  have t3 := htr V hV y lo hi β hβ hPV _ h0 hm' h hh' hbr hb512 hk l hl x hx T' hT'
  have t4 := htr V0 hV0 y lo hi β hβ hPV0 _ h0 hm' h hh' hbr hb512 hk l hl x hx T' hT0'
  rw [← hPS] at t1 t2 t3 t4
  -- the strips
  have s1 := strip hV.gauge hβ hPV m P S ρ hnd h0 hm hm'
  have s2 := strip hV0.gauge hβ hPV0 m P S ρ hnd h0 hm hm'
  rw [hoffs] at s1 s2
  set A := V.hol (stair y m (P ++ ρ :: S) 0)
  set A' := V.hol (stair y (m + Pi.single ρ 1) (P ++ ρ :: S) 0)
  set B := V0.hol (stair y m (P ++ ρ :: S) 0)
  set B' := V0.hol (stair y (m + Pi.single ρ 1) (P ++ ρ :: S) 0)
  set v := V.val ⟨ofs y m, ρ, true⟩
  set v0 := V0.val ⟨ofs y m, ρ, true⟩
  have uA : IsU A := hol_isU hV.gauge _
  have uA' : IsU A' := hol_isU hV.gauge _
  have uB : IsU B := hol_isU hV0.gauge _
  have uB' : IsU B' := hol_isU hV0.gauge _
  have uv : IsU v := val_isU hV.gauge _
  have uv0 : IsU v0 := val_isU hV0.gauge _
  -- `eq:axial-path-difference` at both ends
  have d1 : ‖((B * A⁻¹ : GLN) : Mat) - 1‖ ≤ 2 * (2 * Real.pi * (6 * h ^ 2 * β)) := by
    rw [norm_mul_inv_sub_one'' uA]
    calc ‖(B : Mat) - A‖ = ‖((T : Mat) - A) - ((T : Mat) - B)‖ := by congr 1; abel
      _ ≤ ‖(T : Mat) - A‖ + ‖(T : Mat) - B‖ := norm_sub_le _ _
      _ ≤ _ := by linarith
  have d2 : ‖((A' * B'⁻¹ : GLN) : Mat) - 1‖ ≤ 2 * (2 * Real.pi * (6 * h ^ 2 * β)) := by
    rw [norm_mul_inv_sub_one'' uB']
    calc ‖(A' : Mat) - B'‖ = ‖((T' : Mat) - B') - ((T' : Mat) - A')‖ := by congr 1; abel
      _ ≤ ‖(T' : Mat) - B'‖ + ‖(T' : Mat) - A'‖ := norm_sub_le _ _
      _ ≤ _ := by linarith
  -- `eq:axial-bond-reduction`
  rw [norm_sub_one_eq_of_eq (Y := B⁻¹ * ((B * A⁻¹) * (A * v * A'⁻¹) * (A' * B'⁻¹) *
    (B * v0 * B'⁻¹)⁻¹) * B⁻¹⁻¹) (by group), norm_conj_sub_one' uB.inv]
  have u1 : IsU (B * A⁻¹) := uB.mul uA.inv
  have u2 : IsU (A * v * A'⁻¹) := (uA.mul uv).mul uA'.inv
  have u3 : IsU (A' * B'⁻¹) := uA'.mul uB'.inv
  refine (norm_mul_sub_one_le ((u1.mul u2).mul u3)).trans ?_
  rw [norm_inv_sub_one' ((uB.mul uv0).mul uB'.inv)]
  have e1 := norm_mul_sub_one_le (u1.mul u2) (h := A' * B'⁻¹)
  have e2 := norm_mul_sub_one_le u1 (h := A * v * A'⁻¹)
  linarith

/-! ### The factor `e^{-iβ_c}` on the lattice -/

/-- `avg_path_factor` with the loops of `def:block-paths` on the lattice: for the coarse bond from `y`
to `y + Le_μ`, points `x = y + Σ off(x)_σ e_σ` with `|off(x)_σ| ≤ h`, and orderings of the coordinates
for the paths of `𝐆(c₋, x)` and `𝐆(c₊, x')`, a `G`-valued field whose plaquettes in the box are at most
`√Nα` (`lem:norms`(i) from `|·| ≤ α`) has `U([c]) = E · M(U)(c)` with `E ∈ G`, `‖E - id‖ ≤ 7√NL²α`, when
`4Lh + 6h² ≤ 4L²` (true for `h = (L - 1)/2`). -/
theorem avg_path_factor_lattice (G : GaugeGroup N) (hG : IsClosed G.mats) {ι : Type*} [Fintype ι]
    {P P' : ι → Type*} [∀ x, Fintype (P x)] [∀ x, Fintype (P' x)] :
    ∃ rG : ℝ, 0 < rG ∧ ∀ {n : ℕ} [NeZero n] (U : Config N n), IsGField G U → ∀ (y : Site n) (lo hi : Fin 4 → ℤ)
      (μ : Fin 4) (L : ℕ) (α h : ℝ), 0 ≤ α → PlaqBound U (boxR y lo hi) (Real.sqrt N * α) →
      α ≤ rG / (8 * Real.sqrt N * (L : ℝ) ^ 2) → 7 * Real.sqrt N * (L : ℝ) ^ 2 * α ≤ Real.pi →
      4 * L * h + 6 * h ^ 2 ≤ 4 * (L : ℝ) ^ 2 →
      ∀ (off : ι → Fin 4 → ℤ) (ord : ∀ x, P x → List (Fin 4)) (ord' : ∀ x, P' x → List (Fin 4)),
      (∀ x Γ, (ord x Γ).Perm [0, 1, 2, 3]) → (∀ x Γ', (ord' x Γ').Perm [0, 1, 2, 3]) →
      (∀ x σ, ((off x σ).natAbs : ℝ) ≤ h) → InBox lo hi 0 → (∀ x, InBox lo hi (off x)) →
      InBox lo hi (Pi.single μ (L : ℤ)) → (∀ x, InBox lo hi (Pi.single μ (L : ℤ) + off x)) →
      ∃ E : GLN, E ∈ G.carrier ∧
        U.hol (segZ μ y L) = E * Average.avg G.inChart G.chartLog
          (fun x Γ => U.hol (stair y (off x) (ord x Γ) 0)) (fun x => U.hol (segZ μ (ofs y (off x)) L))
          (fun x Γ' => U.hol (stair (ofs y (Pi.single μ (L : ℤ))) (off x) (ord' x Γ') 0))
          (U.hol (segZ μ y L)) ∧
        ‖(E : Mat) - 1‖ ≤ 7 * Real.sqrt N * (L : ℝ) ^ 2 * α := by
  obtain ⟨rG, hr0, hav⟩ := MeanTransports.GaugeGroup'.avg_path_factor (P := P) (P' := P') G hG
  refine ⟨rG, hr0, fun U hU y lo hi μ L α h hα hP hαr hπ hLh off ord ord' hord hord' hh h0 hoff hL
    hLoff => ?_⟩
  refine hav _ _ _ _ L α hα hαr hπ (fun x Γ Γ' => ?_) (fun x Γ Γ' => ?_)
  · unfold Average.loop
    exact G.carrier.mul_mem (G.carrier.mul_mem (G.carrier.mul_mem (hU.hol_mem _) (hU.hol_mem _))
      (G.carrier.inv_mem (hU.hol_mem _))) (G.carrier.inv_mem (hU.hol_mem _))
  · unfold Average.loop
    have hsα : 0 ≤ Real.sqrt N * α := mul_nonneg (Real.sqrt_nonneg _) hα
    refine (loop_bound hU.gauge hsα hP μ L (off x) (hh x) h0 (hoff x) hL (hLoff x) (ord x Γ)
      (ord' x Γ') (hord x Γ) (hord' x Γ')).trans ?_
    have := mul_le_mul_of_nonneg_right hLh hsα
    nlinarith

/-! ### `lem:axial-smallness` for a bond between the two blocks -/

lemma norm_mul6_sub_one_le {a b c d e f : GLN} (ha : IsU a) (hb : IsU b) (hc : IsU c) (hd : IsU d)
    (he : IsU e) : ‖((a * b * c * d * e * f : GLN) : Mat) - 1‖ ≤ ‖(a : Mat) - 1‖ + ‖(b : Mat) - 1‖ +
      ‖(c : Mat) - 1‖ + ‖(d : Mat) - 1‖ + ‖(e : Mat) - 1‖ + ‖(f : Mat) - 1‖ := by
  have h5 := norm_mul_sub_one_le ((((ha.mul hb).mul hc).mul hd).mul he) (h := f)
  have h4 := norm_mul_sub_one_le (((ha.mul hb).mul hc).mul hd) (h := e)
  have h3 := norm_mul_sub_one_le ((ha.mul hb).mul hc) (h := d)
  have h2 := norm_mul_sub_one_le (ha.mul hb) (h := c)
  have h1 := norm_mul_sub_one_le ha (h := b)
  linarith

lemma isU_of_mem {G : GaugeGroup N} {g : GLN} (hg : g ∈ G.carrier) : IsU g := G.unitary _ hg

/-- `lem:axial-smallness` for the bond `b = (w, w + e_μ)` between the blocks `B(c₋)` and `B(c₊)`,
`c₊ = c₋ + Le_μ`, rule `m`, on the lattice, with the paths from `y = c₋`. The offsets of `w` from `c₋`
are `m`, those of `z = w + e_μ` from `c₊` are `n'` (`n' + Le_μ = m + e_μ`). Hypotheses: (i) the
plaquettes of both fields in the box are at most `√Nα`; (ii) the mean transports to `w` from `c₋` and
to `z` from `c₊` agree; (iii) `‖M(V)(c)M(V₀)(c)⁻¹ - id‖ ≤ α₁`. Then `‖V(b)V₀(b)⁻¹ - id‖` is at most
`8πb + 2L(Σ_{σ<μ}|n'_σ|)√Nα + 14√NL²α + α₁ + 2(Σ_{σ>μ}|m_σ|)√Nα`, `b = 6h²√Nα`: the bound
`(19√N + 4κ)α₀ + α₁` of the proof with the core's numbers. -/
theorem axial_between_lattice (G : GaugeGroup N) (hG : IsClosed G.mats) {ι : Type*} [Fintype ι]
    {P P' : ι → Type*} [∀ x, Fintype (P x)] [∀ x, Fintype (P' x)] :
    ∃ r : ℝ, 0 < r ∧ ∃ rG : ℝ, 0 < rG ∧ ∀ {n : ℕ} [NeZero n] (V V0 : Config N n), IsGField G V → IsGField G V0 →
      ∀ (y : Site n) (lo hi : Fin 4 → ℤ) (μ : Fin 4) (L : ℕ) (α h : ℝ), 0 ≤ α →
      PlaqBound V (boxR y lo hi) (Real.sqrt N * α) → PlaqBound V0 (boxR y lo hi) (Real.sqrt N * α) →
      α ≤ rG / (8 * Real.sqrt N * (L : ℝ) ^ 2) → 7 * Real.sqrt N * (L : ℝ) ^ 2 * α ≤ Real.pi →
      4 * L * h + 6 * h ^ 2 ≤ 4 * (L : ℝ) ^ 2 → 6 * h ^ 2 * (Real.sqrt N * α) ≤ r →
      512 * (Real.pi / 2 * (6 * h ^ 2 * (Real.sqrt N * α))) ≤ 1 →
      ∀ (off : ι → Fin 4 → ℤ) (ord : ∀ x, P x → List (Fin 4)) (ord' : ∀ x, P' x → List (Fin 4)),
      (∀ x Γ, (ord x Γ).Perm [0, 1, 2, 3]) → (∀ x Γ', (ord' x Γ').Perm [0, 1, 2, 3]) →
      (∀ x σ, ((off x σ).natAbs : ℝ) ≤ h) → InBox lo hi 0 → (∀ x, InBox lo hi (off x)) →
      InBox lo hi (Pi.single μ (L : ℤ)) → (∀ x, InBox lo hi (Pi.single μ (L : ℤ) + off x)) →
      ∀ (m n' : Fin 4 → ℤ) (Pre Post : List (Fin 4)), Pre ++ μ :: Post = [0, 1, 2, 3] →
      n' + Pi.single μ (L : ℤ) = m + Pi.single μ 1 → InBox lo hi m →
      InBox lo hi (m + Pi.single μ 1) → InBox lo hi (Function.update n' μ (L : ℤ)) →
      InBox lo hi (Pi.single μ (L : ℤ) + n') →
      (∀ σ, ((m σ).natAbs : ℝ) ≤ h) → (∀ σ, ((n' σ).natAbs : ℝ) ≤ h) →
      ∀ {k : ℕ} (_hk : 0 < k) (l : Fin k → List (Fin 4)), (∀ Γ, (l Γ).Perm [0, 1, 2, 3]) →
      ∀ x, l x = [0, 1, 2, 3] → ∀ T T' : GLN,
      IsMeanOf (fun Γ => V.hol (stair y m (l Γ) 0)) x T →
      IsMeanOf (fun Γ => V0.hol (stair y m (l Γ) 0)) x T →
      IsMeanOf (fun Γ => V.hol (stair (ofs y (Pi.single μ (L : ℤ))) n' (l Γ) 0)) x T' →
      IsMeanOf (fun Γ => V0.hol (stair (ofs y (Pi.single μ (L : ℤ))) n' (l Γ) 0)) x T' →
      ∀ (MV MV0 : GLN), MV = Average.avg G.inChart G.chartLog
          (fun x Γ => V.hol (stair y (off x) (ord x Γ) 0)) (fun x => V.hol (segZ μ (ofs y (off x)) L))
          (fun x Γ' => V.hol (stair (ofs y (Pi.single μ (L : ℤ))) (off x) (ord' x Γ') 0))
          (V.hol (segZ μ y L)) →
      MV0 = Average.avg G.inChart G.chartLog
          (fun x Γ => V0.hol (stair y (off x) (ord x Γ) 0)) (fun x => V0.hol (segZ μ (ofs y (off x)) L))
          (fun x Γ' => V0.hol (stair (ofs y (Pi.single μ (L : ℤ))) (off x) (ord' x Γ') 0))
          (V0.hol (segZ μ y L)) →
      ∀ α₁ : ℝ, ‖((MV * MV0⁻¹ : GLN) : Mat) - 1‖ ≤ α₁ →
      ‖((V.val ⟨ofs y m, μ, true⟩ * (V0.val ⟨ofs y m, μ, true⟩)⁻¹ : GLN) : Mat) - 1‖ ≤
        8 * Real.pi * (6 * h ^ 2 * (Real.sqrt N * α)) +
        2 * (L * (Pre.map fun σ => (n' σ).natAbs).sum * (Real.sqrt N * α)) +
        14 * Real.sqrt N * (L : ℝ) ^ 2 * α + α₁ +
        2 * ((Post.map fun σ => (m σ).natAbs).sum * (Real.sqrt N * α)) := by
  obtain ⟨r, hr0, htr⟩ := transport_lattice G hG
  obtain ⟨rG, hrG0, hav⟩ := avg_path_factor_lattice (P := P) (P' := P') G hG
  refine ⟨r, hr0, rG, hrG0, fun V V0 hV hV0 y lo hi μ L α h hα hPV hPV0 hαr hπ hLh hbr hb512 off ord
    ord' hord hord' hoh h0 hoff hL hLoff m n' Pre Post hPS hz hm hm1 hupd hLn hmh hnh k hk l hl x hx
    T T' hT hT0 hT' hT0' MV MV0 hMV hMV0 α₁ hα₁ => ?_⟩
  have hβ : 0 ≤ Real.sqrt N * α := mul_nonneg (Real.sqrt_nonneg _) hα
  have hnd : (Pre ++ μ :: Post).Nodup := by rw [hPS]; decide
  have hoffs : offs m (Pre ++ μ :: Post) = m := offs_perm m (by rw [hPS])
  -- the transports at `c₋` and at `c₊`
  have t1 := htr V hV y lo hi _ hβ hPV m h0 hm h hmh hbr hb512 hk l hl x hx T hT
  have t2 := htr V0 hV0 y lo hi _ hβ hPV0 m h0 hm h hmh hbr hb512 hk l hl x hx T hT0
  have hPV' := plaqBound_mono (boxR_shift_subset y (Pi.single μ (L : ℤ)) lo hi) hPV
  have hPV0' := plaqBound_mono (boxR_shift_subset y (Pi.single μ (L : ℤ)) lo hi) hPV0
  have h0' : InBox (lo - Pi.single μ (L : ℤ)) (hi - Pi.single μ (L : ℤ)) 0 :=
    inBox_shift (by simpa using hL)
  have hn' : InBox (lo - Pi.single μ (L : ℤ)) (hi - Pi.single μ (L : ℤ)) n' := inBox_shift hLn
  have t3 := htr V hV _ _ _ _ hβ hPV' n' h0' hn' h hnh hbr hb512 hk l hl x hx T' hT'
  have t4 := htr V0 hV0 _ _ _ _ hβ hPV0' n' h0' hn' h hnh hbr hb512 hk l hl x hx T' hT0'
  rw [← hPS] at t1 t2 t3 t4
  -- the strips from `c₋`
  have s1 := strip hV.gauge hβ hPV m Pre Post μ hnd h0 hm hm1
  have s2 := strip hV0.gauge hβ hPV0 m Pre Post μ hnd h0 hm hm1
  rw [hoffs] at s1 s2
  -- moving `[c]` to the front
  have f1 := front_segment hV.gauge hβ hPV n' Pre Post μ hnd (L : ℤ) h0 hupd
  have f2 := front_segment hV0.gauge hβ hPV0 n' Pre Post μ hnd (L : ℤ) h0 hupd
  rw [hz, Int.natAbs_natCast] at f1 f2
  -- the averages: `V([c]) = E · M(V)(c)`
  obtain ⟨E, hE, hK, hEb⟩ := hav V hV y lo hi μ L α h hα hPV hαr hπ hLh off ord ord' hord hord'
    hoh h0 hoff hL hLoff
  obtain ⟨E0, hE0, hK0, hE0b⟩ := hav V0 hV0 y lo hi μ L α h hα hPV0 hαr hπ hLh off ord ord' hord
    hord' hoh h0 hoff hL hLoff
  have hK' : V.hol (segZ μ y L) = E * MV := by rw [hK, hMV]
  have hK0' : V0.hol (segZ μ y L) = E0 * MV0 := by rw [hK0, hMV0]
  have uE := isU_of_mem hE
  have uE0 := isU_of_mem hE0
  have uMV : IsU MV := by
    have e : MV = E⁻¹ * V.hol (segZ μ y L) := by rw [hK']; group
    rw [e]; exact isU_of_mem (G.carrier.mul_mem (G.carrier.inv_mem hE) (hV.hol_mem _))
  have uMV0 : IsU MV0 := by
    have e : MV0 = E0⁻¹ * V0.hol (segZ μ y L) := by rw [hK0']; group
    rw [e]; exact isU_of_mem (G.carrier.mul_mem (G.carrier.inv_mem hE0) (hV0.hol_mem _))
  set A := V.hol (stair y m (Pre ++ μ :: Post) 0)
  set A' := V.hol (stair y (m + Pi.single μ 1) (Pre ++ μ :: Post) 0)
  set B := V0.hol (stair y m (Pre ++ μ :: Post) 0)
  set B' := V0.hol (stair y (m + Pi.single μ 1) (Pre ++ μ :: Post) 0)
  set VΓ := V.hol (stair (ofs y (Pi.single μ (L : ℤ))) n' (Pre ++ μ :: Post) 0)
  set V0Γ := V0.hol (stair (ofs y (Pi.single μ (L : ℤ))) n' (Pre ++ μ :: Post) 0)
  set v := V.val ⟨ofs y m, μ, true⟩
  set v0 := V0.val ⟨ofs y m, μ, true⟩
  have uA : IsU A := hol_isU hV.gauge _
  have uA' : IsU A' := hol_isU hV.gauge _
  have uB : IsU B := hol_isU hV0.gauge _
  have uB' : IsU B' := hol_isU hV0.gauge _
  have uVΓ : IsU VΓ := hol_isU hV.gauge _
  have uV0Γ : IsU V0Γ := hol_isU hV0.gauge _
  have uv : IsU v := val_isU hV.gauge _
  have uv0 : IsU v0 := val_isU hV0.gauge _
  -- `D(w)`, the end in `B(c₋)`
  have d1 : ‖((B * A⁻¹ : GLN) : Mat) - 1‖ ≤ 2 * (2 * Real.pi * (6 * h ^ 2 * (Real.sqrt N * α))) := by
    rw [norm_mul_inv_sub_one'' uA]
    calc ‖(B : Mat) - A‖ = ‖((T : Mat) - A) - ((T : Mat) - B)‖ := by congr 1; abel
      _ ≤ ‖(T : Mat) - A‖ + ‖(T : Mat) - B‖ := norm_sub_le _ _
      _ ≤ _ := by linarith
  -- `D(z)`, the end in `B(c₊)`: `V(τ_z) = R_z E M(V)(c) V(Γ_z)`
  have uR : IsU (A' * (E * MV * VΓ)⁻¹) := uA'.mul ((uE.mul uMV).mul uVΓ).inv
  have uR0 : IsU (B' * (E0 * MV0 * V0Γ)⁻¹) := uB'.mul ((uE0.mul uMV0).mul uV0Γ).inv
  have hR : ‖((A' * (E * MV * VΓ)⁻¹ : GLN) : Mat) - 1‖ ≤
      L * (Pre.map fun σ => (n' σ).natAbs).sum * (Real.sqrt N * α) := by
    rw [show E * MV * VΓ = V.hol (segZ μ y L) * VΓ by rw [hK']]
    exact f1
  have hR0 : ‖((B' * (E0 * MV0 * V0Γ)⁻¹ : GLN) : Mat) - 1‖ ≤
      L * (Pre.map fun σ => (n' σ).natAbs).sum * (Real.sqrt N * α) := by
    rw [show E0 * MV0 * V0Γ = V0.hol (segZ μ y L) * V0Γ by rw [hK0']]
    exact f2
  have hΓ : ‖(VΓ : Mat) - V0Γ‖ ≤ 2 * (2 * Real.pi * (6 * h ^ 2 * (Real.sqrt N * α))) := by
    calc ‖(VΓ : Mat) - V0Γ‖ = ‖((T' : Mat) - V0Γ) - ((T' : Mat) - VΓ)‖ := by congr 1; abel
      _ ≤ ‖(T' : Mat) - V0Γ‖ + ‖(T' : Mat) - VΓ‖ := norm_sub_le _ _
      _ ≤ _ := by linarith
  have dz : ‖((A' * B'⁻¹ : GLN) : Mat) - 1‖ ≤
      2 * (L * (Pre.map fun σ => (n' σ).natAbs).sum * (Real.sqrt N * α)) +
      14 * Real.sqrt N * (L : ℝ) ^ 2 * α + α₁ +
      2 * (2 * Real.pi * (6 * h ^ 2 * (Real.sqrt N * α))) := by
    rw [norm_sub_one_eq_of_eq (Y := (A' * (E * MV * VΓ)⁻¹) * E * (MV * MV0⁻¹) *
      (MV0 * (VΓ * V0Γ⁻¹) * MV0⁻¹) * E0⁻¹ * (B' * (E0 * MV0 * V0Γ)⁻¹)⁻¹) (by group)]
    refine (norm_mul6_sub_one_le uR uE (uMV.mul uMV0.inv)
      ((uMV0.mul (uVΓ.mul uV0Γ.inv)).mul uMV0.inv) uE0.inv).trans ?_
    rw [norm_conj_sub_one' uMV0, norm_mul_inv_sub_one'' uV0Γ, norm_inv_sub_one' uE0,
      norm_inv_sub_one' uR0]
    linarith
  -- `eq:axial-bond-reduction`
  rw [norm_sub_one_eq_of_eq (Y := B⁻¹ * ((B * A⁻¹) * (A * v * A'⁻¹) * (A' * B'⁻¹) *
    (B * v0 * B'⁻¹)⁻¹) * B⁻¹⁻¹) (by group), norm_conj_sub_one' uB.inv]
  have u1 : IsU (B * A⁻¹) := uB.mul uA.inv
  have u2 : IsU (A * v * A'⁻¹) := (uA.mul uv).mul uA'.inv
  have u3 : IsU (A' * B'⁻¹) := uA'.mul uB'.inv
  refine (norm_mul_sub_one_le ((u1.mul u2).mul u3)).trans ?_
  rw [norm_inv_sub_one' ((uB.mul uv0).mul uB'.inv)]
  have e1 := norm_mul_sub_one_le (u1.mul u2) (h := A' * B'⁻¹)
  have e2 := norm_mul_sub_one_le u1 (h := A * v * A'⁻¹)
  linarith

/-! ### `lem:moved-transports`(iii) on the lattice -/

/-- `lem:moved-transports`(iii): for a `G`-valued field whose plaquettes in the box are at most `β`,
the transports along the paths of `𝐆(y, x)` are `U(Γ) = e^{iX_Γ}U_m(y, x)` with `‖X_Γ‖ ≤ 4q`,
`q = (π/2)·6h²β`; with `24πh²β ≤ ϱ_G/4` this is the hypothesis of (ii). The second hypothesis of (ii),
`‖Ad_{U(γ)}Z‖ ≤ 2‖Z‖`, holds for unitary `U(γ)` with the constant one. -/
theorem moved_iii_lattice (G : GaugeGroup N) (hG : IsClosed G.mats) :
    ∃ r : ℝ, 0 < r ∧ ∀ {n : ℕ} [NeZero n] (U : Config N n), IsGField G U → ∀ (y : Site n) (lo hi : Fin 4 → ℤ) (β : ℝ),
      0 ≤ β → PlaqBound U (boxR y lo hi) β → ∀ (m : Fin 4 → ℤ), InBox lo hi 0 → InBox lo hi m →
      ∀ (h : ℝ), (∀ σ, ((m σ).natAbs : ℝ) ≤ h) → 6 * h ^ 2 * β ≤ r →
      512 * (Real.pi / 2 * (6 * h ^ 2 * β)) ≤ 1 →
      ∀ {k : ℕ} (_hk : 0 < k) (l : Fin k → List (Fin 4)), (∀ Γ, (l Γ).Perm [0, 1, 2, 3]) →
      ∀ x, l x = [0, 1, 2, 3] → ∀ T : GLN, IsMeanOf (fun Γ => U.hol (stair y m (l Γ) 0)) x T →
      ∃ X : Fin k → Mat, ∀ Γ, U.hol (stair y m (l Γ) 0) = expU (Complex.I • X Γ) * T ∧
        ‖X Γ‖ ≤ 4 * (Real.pi / 2 * (6 * h ^ 2 * β)) := by
  obtain ⟨r, hr0, hκ⟩ := kappa_lattice G hG
  refine ⟨r, hr0, fun U hU y lo hi β hβ hP m h0 hm h hh hbr hb512 k hk l hl x hx T hT => ?_⟩
  obtain ⟨Y, hY, -, -⟩ := hκ U hU y lo hi β hβ hP m h0 hm h hh hbr hb512 hk l hl x hx
  obtain ⟨Z, hZ, hTZ, hsum⟩ := hT
  beta_reduce at hTZ hsum
  have hY512 : ∀ Γ, ‖Y Γ‖ ≤ 1 / 512 := fun Γ => (hY Γ).2.2.trans (by linarith)
  have hsum' : ∑ Γ, LogM (((expU (Complex.I • Y Γ) * U.hol (stair y m (l x) 0)) *
      (expU (Complex.I • Z) * U.hol (stair y m (l x) 0))⁻¹ : GLN) : Mat) = 0 := by
    rw [← hsum]
    refine Finset.sum_congr rfl fun Γ _ => ?_
    rw [hTZ, (hY Γ).1]
  have hZY := mean_unique hk hY512 (U.hol (stair y m (l x) 0)) hZ hsum'
  have hq0 : 0 ≤ Real.pi / 2 * (6 * h ^ 2 * β) := (norm_nonneg _).trans (hY x).2.2
  have hV : ‖meanV Y‖ ≤ 2 * (Real.pi / 2 * (6 * h ^ 2 * β)) :=
    norm_meanV_le hk hY512 _ (fun Γ => (hY Γ).2.2)
  have hWx : U.hol (stair y m (l x) 0) = expU (Complex.I • -meanV Y) * T := by
    rw [hTZ, hZY, expU_I_neg]; group
  refine ⟨fun Γ => psi (Y Γ) (-meanV Y), fun Γ => ⟨?_, ?_⟩⟩
  · have hlt : ‖Y Γ‖ + ‖-meanV Y‖ < Real.log 2 := by
      rw [norm_neg]; linarith [log_two_gt_eighth, (hY Γ).2.2]
    rw [(hY Γ).1, hWx, ← mul_assoc]
    congr 1
    ext1
    rw [Units.val_mul]
    exact (exp_I_psi hlt).symm
  · have h1 := norm_psi_sub_add_le (Y := Y Γ) (Z := -meanV Y) (by linarith [hY512 Γ])
      (by rw [norm_neg]; linarith)
    rw [norm_neg] at h1
    have h2 : ‖psi (Y Γ) (-meanV Y)‖ ≤ ‖Y Γ‖ + ‖meanV Y‖ + 256 * ‖meanV Y‖ * ‖Y Γ‖ := by
      have := norm_add_le (psi (Y Γ) (-meanV Y) - Y Γ - -meanV Y) (Y Γ + -meanV Y)
      have e : psi (Y Γ) (-meanV Y) - Y Γ - -meanV Y + (Y Γ + -meanV Y) = psi (Y Γ) (-meanV Y) := by
        abel
      rw [e] at this
      have h3 : ‖Y Γ + -meanV Y‖ ≤ ‖Y Γ‖ + ‖meanV Y‖ := by
        have := norm_add_le (Y Γ) (-meanV Y); rwa [norm_neg] at this
      linarith
    have hYΓ := (hY Γ).2.2
    have h4 : 256 * ‖meanV Y‖ * ‖Y Γ‖ ≤ (Real.pi / 2 * (6 * h ^ 2 * β)) := by
      have := mul_le_mul hV hYΓ (norm_nonneg _) (by positivity)
      nlinarith
    show ‖psi (Y Γ) (-meanV Y)‖ ≤ _
    linarith

end LatticeKappa

end CoreLean

end
