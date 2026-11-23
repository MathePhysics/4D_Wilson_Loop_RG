/-
`lem:average`(vi) of BALABAN_CORE.tex (`ec0276e6e8e6`), the analyticity of the average, on the lattice.

For a `1`-form `B = aA` with matrix values (on the positive bonds) and the configuration
`𝐔_B = e^{iB}U` (`moveC`), the formula `M(𝐔_B)(c) = e^{iβ_c}𝐔_B([c])`, `β_c = Σ w (1/i) Log 𝐔_B(ℓ)`, with the
series `Log` in place of the chart logarithm (`avgLogU`), is analytic in `B` on the ball `‖B‖_∞ < r_M`, is the
average for `B` with values in `𝔤`, has `β_c ∈ 𝔤^c` for `B` with values in `𝔤^c` and values in `G^c` if `G` is
connected, and is covariant under every complex gauge transformation.

This file, the tools:
* `moveC`, `val_moveC`, `hol_decomp`: `𝐔_B(γ) = (Π_k e^{iY_k})U(γ)` with `Y_k = ±Ad_{U(…)}B(b_k)`, `‖Y_k‖ ≤ ‖B‖`,
  and `Y_k ∈ 𝔤^c` if `B` has values in `𝔤^c` (the factors `e^{±iB}` moved to the left).
* `analyticAt_hol`: `B ↦ 𝐔_B(γ)` is analytic everywhere (a product of exponentials and constant matrices).
* `exists_exp_prod_lieC`: a product of exponentials of small elements of `𝔤^c` is `e^{iZ}` with `Z ∈ 𝔤^c`.
* `carrier_le_complexified`: a connected `G` lies in `G^c`.
-/
import CoreLean.AverageDomain
import CoreLean.GroupMeanII
import CoreLean.CloseTransports

open Matrix NormedSpace Filter Topology
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace CoreLean

namespace AverageHolo

open LatticePaths LatticeKappa RegularAverages

set_option linter.unusedSectionVars false

variable {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "GLN" => (Matrix (Fin N) (Fin N) ℂ)ˣ

/-! ### `𝔤^c` -/

lemma lieC_neg {G : GaugeGroup N} {X : Mat} (hX : X ∈ G.lieC) : -X ∈ G.lieC := by
  obtain ⟨A, hA, B, hB, rfl⟩ := hX
  exact ⟨-A, G.neg_mem_lie hA, -B, G.neg_mem_lie hB, by rw [smul_neg, neg_add]⟩

/-- `Ad_W` maps `𝔤^c` into itself for `W ∈ G`. -/
lemma Ad_lieC {G : GaugeGroup N} {W : GLN} (hW : W ∈ G.carrier) {X : Mat} (hX : X ∈ G.lieC) :
    Ad W X ∈ G.lieC := by
  obtain ⟨A, hA, B, hB, rfl⟩ := hX
  exact ⟨Ad W A, GaugeGroup.Ad_mem_lie hW hA, Ad W B, GaugeGroup.Ad_mem_lie hW hB,
    by rw [Ad_add, Ad_smul]⟩

lemma lie_subset_lieC' {G : GaugeGroup N} {X : Mat} (hX : X ∈ G.lie) : X ∈ G.lieC :=
  ⟨X, hX, 0, G.zero_mem_lie, by simp⟩

/-- A product of exponentials of small elements of `𝔤^c` is `e^{iZ}` with `Z ∈ 𝔤^c`, `‖Z‖ ≤ 2|l|s`. -/
theorem exists_exp_prod_lieC {G : GaugeGroup N} (hG : G.LieInput) (l : List Mat) {s : ℝ} (hs : 0 ≤ s)
    (hl : ∀ Y ∈ l, ‖Y‖ ≤ s) (hlC : ∀ Y ∈ l, Y ∈ G.lieC) (h512 : 512 * l.length * s ≤ 1) :
    ∃ Z ∈ G.lieC, expU (Complex.I • Z) = (l.map fun Y => expU (Complex.I • Y)).prod ∧
      ‖Z‖ ≤ 2 * l.length * s := by
  induction l with
  | nil => exact ⟨0, G.zero_mem_lie |> lie_subset_lieC', by simp, by simp⟩
  | cons Y l ih =>
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at h512 ⊢
    have hk : (0 : ℝ) ≤ l.length := Nat.cast_nonneg _
    obtain ⟨Z, hZC, hZe, hZn⟩ := ih (fun Y' hY' => hl Y' (by simp [hY']))
      (fun Y' hY' => hlC Y' (by simp [hY'])) (by nlinarith)
    have hY := hl Y (by simp)
    have hs512 : s ≤ 1 / 512 := by nlinarith
    have hZs : 2 * l.length * s ≤ 1 / 256 := by nlinarith
    have hl2 := Real.log_two_gt_d9
    refine ⟨psi Y Z, psi_mem hG (hlC Y (by simp)) hZC (by linarith), ?_, ?_⟩
    · rw [List.map_cons, List.prod_cons, ← hZe]
      exact (LatticeKappa.expU_mul_expU (by linarith)).symm
    · refine (LatticeKappa.norm_psi_le' (by linarith) (by linarith)).trans ?_
      have : 256 * (‖Y‖ * ‖Z‖) ≤ s := by
        have h1 : ‖Y‖ * ‖Z‖ ≤ s * (2 * l.length * s) :=
          mul_le_mul hY hZn (norm_nonneg _) hs
        nlinarith
      nlinarith

/-! ### The moved configuration -/

variable {n : ℕ} [NeZero n]

/-- `𝐔_B = e^{iB}U` on the positive bonds. -/
def moveC (U : Config N n) (B : Fin 4 → Site n → Mat) : Config N n :=
  fun ρ z => expU (Complex.I • B ρ z) * U ρ z

/-- The exponent of a bond of `𝐔_B` relative to `U`. -/
def Yb (U : Config N n) (B : Fin 4 → Site n → Mat) (t : Bond n) : Mat :=
  if t.pos then B t.dir t.site else -Ad (U t.dir (t.site - unit n t.dir))⁻¹ (B t.dir (t.site - unit n t.dir))

lemma val_moveC (U : Config N n) (B : Fin 4 → Site n → Mat) (t : Bond n) :
    (moveC U B).val t = expU (Complex.I • Yb U B t) * U.val t := by
  obtain ⟨z, ρ, s⟩ := t
  cases s
  · simp only [Config.val, moveC, Yb, Bool.false_eq_true, ↓reduceIte, _root_.mul_inv_rev]
    rw [show Complex.I • -Ad (U ρ (z - unit n ρ))⁻¹ (B ρ (z - unit n ρ)) =
        Ad (U ρ (z - unit n ρ))⁻¹ (-(Complex.I • B ρ (z - unit n ρ))) by rw [Ad_neg, Ad_smul, smul_neg],
      ← expU_conj, ← expU_inv]
    group
  · simp only [Config.val, moveC, Yb, ↓reduceIte]

lemma norm_Yb_le {G : GaugeGroup N} {U : Config N n} (hU : IsGField G U) (B : Fin 4 → Site n → Mat)
    (t : Bond n) : ‖Yb U B t‖ ≤ ‖B‖ := by
  have hB : ∀ ρ z, ‖B ρ z‖ ≤ ‖B‖ := fun ρ z => (norm_le_pi_norm (B ρ) z).trans (norm_le_pi_norm B ρ)
  unfold Yb
  split_ifs
  · exact hB _ _
  · rw [norm_neg, GaugeGroup.opNorm_Ad (G.carrier.inv_mem (hU _ _))]
    exact hB _ _

lemma Yb_lieC {G : GaugeGroup N} {U : Config N n} (hU : IsGField G U) {B : Fin 4 → Site n → Mat}
    (hB : ∀ ρ z, B ρ z ∈ G.lieC) (t : Bond n) : Yb U B t ∈ G.lieC := by
  unfold Yb
  split_ifs
  · exact hB _ _
  · exact lieC_neg (Ad_lieC (G.carrier.inv_mem (hU _ _)) (hB _ _))

lemma conj_prod_expU (W : GLN) : ∀ l : List Mat,
    W * (l.map fun Y => expU (Complex.I • Y)).prod * W⁻¹ =
      ((l.map (Ad W)).map fun Y => expU (Complex.I • Y)).prod
  | [] => by simp
  | Y :: l => by
    simp only [List.map_cons, List.prod_cons]
    rw [← conj_prod_expU W l, ← Ad_smul, ← expU_conj]
    group

/-- `𝐔_B(γ) = (Π_k e^{iY_k})U(γ)`. -/
theorem hol_decomp {G : GaugeGroup N} {U : Config N n} (hU : IsGField G U) (B : Fin 4 → Site n → Mat) :
    ∀ γ : List (Bond n), ∃ l : List Mat, l.length = γ.length ∧ (∀ Y ∈ l, ‖Y‖ ≤ ‖B‖) ∧
      ((∀ ρ z, B ρ z ∈ G.lieC) → ∀ Y ∈ l, Y ∈ G.lieC) ∧
      (moveC U B).hol γ = (l.map fun Y => expU (Complex.I • Y)).prod * U.hol γ
  | [] => ⟨[], rfl, by simp, by simp, by simp [Config.hol]⟩
  | t :: γ => by
    obtain ⟨l, hl, hln, hlC, he⟩ := hol_decomp hU B γ
    refine ⟨Yb U B t :: l.map (Ad (U.val t)), by simp [hl], ?_, ?_, ?_⟩
    · intro Y hY
      simp only [List.mem_cons, List.mem_map] at hY
      rcases hY with rfl | ⟨Y', hY', rfl⟩
      · exact norm_Yb_le hU B t
      · rw [GaugeGroup.opNorm_Ad (hU.val_mem t)]; exact hln Y' hY'
    · intro hB Y hY
      simp only [List.mem_cons, List.mem_map] at hY
      rcases hY with rfl | ⟨Y', hY', rfl⟩
      · exact Yb_lieC hU hB t
      · exact Ad_lieC (hU.val_mem t) (hlC hB Y' hY')
    · rw [hol_cons, hol_cons, val_moveC, he, List.map_cons, List.prod_cons,
        ← conj_prod_expU (U.val t) l]
      group

/-! ### Analyticity of the holonomies -/

lemma val_moveC_mat (U : Config N n) (B : Fin 4 → Site n → Mat) (t : Bond n) :
    (((moveC U B).val t : GLN) : Mat) =
      if t.pos then exp (Complex.I • B t.dir t.site) * ((U t.dir t.site : GLN) : Mat)
      else (((U t.dir (t.site - unit n t.dir))⁻¹ : GLN) : Mat) *
        exp (-(Complex.I • B t.dir (t.site - unit n t.dir))) := by
  obtain ⟨z, ρ, s⟩ := t
  cases s
  · simp only [Config.val, moveC, Bool.false_eq_true, ↓reduceIte, _root_.mul_inv_rev, Units.val_mul, expU_inv,
      expU_val]
  · simp only [Config.val, moveC, ↓reduceIte, Units.val_mul, expU_val]

/-- `B ↦ 𝐔_B(γ)` is analytic. -/
theorem analyticAt_hol (U : Config N n) (B₀ : Fin 4 → Site n → Mat) :
    ∀ γ : List (Bond n), AnalyticAt ℂ (fun B => (((moveC U B).hol γ : GLN) : Mat)) B₀
  | [] => by simp only [Config.hol, List.map_nil, List.prod_nil, Units.val_one]; exact analyticAt_const
  | t :: γ => by
    have hrest := analyticAt_hol U B₀ γ
    have hev : ∀ (ρ : Fin 4) (z : Site n),
        AnalyticAt ℂ (fun B : Fin 4 → Site n → Mat => Complex.I • B ρ z) B₀ := fun ρ z => by
      have h1 : AnalyticAt ℂ (fun B : Fin 4 → Site n → Mat => B ρ) B₀ :=
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 4 => Site n → Mat) ρ).analyticAt B₀
      have h2 : AnalyticAt ℂ (fun F : Site n → Mat => F z) (B₀ ρ) :=
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Site n => Mat) z).analyticAt _
      exact (AnalyticAt.comp (f := fun B : Fin 4 → Site n → Mat => B ρ) (x := B₀) h2 h1).const_smul
        (c := Complex.I)
    have hval : AnalyticAt ℂ (fun B => (((moveC U B).val t : GLN) : Mat)) B₀ := by
      simp only [val_moveC_mat]
      split_ifs
      · exact ((exp_analytic _).comp (hev _ _)).mul analyticAt_const
      · exact analyticAt_const.mul ((exp_analytic _).comp (hev _ _).neg)
    have e : (fun B => (((moveC U B).hol (t :: γ) : GLN) : Mat)) =
        fun B => (((moveC U B).val t : GLN) : Mat) * (((moveC U B).hol γ : GLN) : Mat) := by
      funext B; rw [hol_cons, Units.val_mul]
    rw [e]
    exact hval.mul hrest

/-! ### Connected gauge groups -/

/-- A connected `G` lies in `G^c`: the subgroup `G ∩ G^c` contains the neighbourhood of `id` of
`lem:chart`(ii), so it is open and closed in `G`. -/
theorem carrier_le_complexified (G : GaugeGroup N) (hG : IsClosed G.mats)
    (hconn : IsConnected (G.carrier : Set GLN)) : G.carrier ≤ G.complexified := by
  obtain ⟨r, hr0, -, hch⟩ := GaugeGroup.chart_ii (G := G) hG
  have : ConnectedSpace G.carrier := isConnected_iff_connectedSpace.1 hconn
  set H : Subgroup G.carrier := G.complexified.subgroupOf G.carrier with hH
  have hnhds : (H : Set G.carrier) ∈ 𝓝 (1 : G.carrier) := by
    have hcont : Continuous fun g : G.carrier => (((g : GLN) : Mat)) :=
      Units.continuous_val.comp continuous_subtype_val
    have hopen : IsOpen {g : G.carrier | ‖((g : GLN) : Mat) - 1‖ < r} :=
      isOpen_lt (continuous_norm.comp (hcont.sub continuous_const)) continuous_const
    refine Filter.mem_of_superset (hopen.mem_nhds (by simp [hr0])) fun g hg => ?_
    obtain ⟨A, hA, -, hAe, -, -⟩ := hch g g.2 (le_of_lt hg)
    show (g : GLN) ∈ G.complexified
    have : (g : GLN) = expU (Complex.I • A) := Units.ext (by rw [expU_val]; exact hAe.symm)
    rw [this]
    exact Subgroup.subset_closure ⟨A, lie_subset_lieC' hA, rfl⟩
  have hHo : IsOpen (H : Set G.carrier) := Subgroup.isOpen_of_mem_nhds H hnhds
  have hHc : IsClosed (H : Set G.carrier) := Subgroup.isClosed_of_isOpen H hHo
  have htop : (H : Set G.carrier) = Set.univ :=
    (IsClopen.eq_univ ⟨hHc, hHo⟩ ⟨1, H.one_mem⟩)
  intro g hg
  have : (⟨g, hg⟩ : G.carrier) ∈ H := by rw [← SetLike.mem_coe, htop]; trivial
  exact this

/-! ### The average with the series `Log` -/

lemma analyticAt_finsum' {α E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] (s : Finset α) (f : α → E → F) {x : E}
    (h : ∀ i ∈ s, AnalyticAt ℂ (f i) x) : AnalyticAt ℂ (fun y => ∑ i ∈ s, f i y) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using analyticAt_const
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

variable {ι : Type*} [Fintype ι] {P : ι → Type*} [∀ x, Fintype (P x)]

/-- The loop `ℓ_c(x, Γ, Γ')` as a path. -/
def lpath (y : Site n) (κ : Fin 4) (L : ℕ) (off : ι → Fin 4 → ℤ) (ord : ∀ x, P x → List (Fin 4)) (x : ι)
    (Γ Γ' : P x) : List (Bond n) :=
  stair y (off x) (ord x Γ) 0 ++ segZ κ (ofs y (off x)) L ++
    rv (stair (ofs y (Pi.single κ (L : ℤ))) (off x) (ord x Γ') 0) ++ rv (segZ κ y L)

/-- `β_c` with the series `Log`. -/
def betaLog (V : Config N n) (y : Site n) (κ : Fin 4) (L : ℕ) (off : ι → Fin 4 → ℤ)
    (ord : ∀ x, P x → List (Fin 4)) : Mat :=
  ∑ x, ∑ Γ, ∑ Γ', Average.wt P P x • ((1 / Complex.I : ℂ) •
    LogM ((V.hol (lpath y κ L off ord x Γ Γ') : GLN) : Mat))

/-- `M(V)(c) = e^{iβ_c}V([c])` with the series `Log`. -/
def avgLogU (V : Config N n) (y : Site n) (κ : Fin 4) (L : ℕ) (off : ι → Fin 4 → ℤ)
    (ord : ∀ x, P x → List (Fin 4)) : GLN :=
  expU (Complex.I • betaLog V y κ L off ord) * V.hol (segZ κ y L)

lemma loop_eq_hol (V : Config N n) (y : Site n) (κ : Fin 4) (L : ℕ) (off : ι → Fin 4 → ℤ)
    (ord : ∀ x, P x → List (Fin 4)) (x : ι) (Γ Γ' : P x) :
    Average.loop (fun x Γ => V.hol (stair y (off x) (ord x Γ) 0))
      (fun x => V.hol (segZ κ (ofs y (off x)) L))
      (fun x Γ' => V.hol (stair (ofs y (Pi.single κ (L : ℤ))) (off x) (ord x Γ') 0))
      (V.hol (segZ κ y L)) x Γ Γ' = V.hol (lpath y κ L off ord x Γ Γ') := by
  simp only [Average.loop, lpath, hol_append, rv, Transports.hol_rev]

/-- **`lem:average`(iii)** for the extension: covariance under every complex gauge transformation. -/
theorem avgLogU_gauge (V : Config N n) (u : Site n → GLN) (y : Site n) (κ : Fin 4) (L : ℕ)
    (off : ι → Fin 4 → ℤ) (ord : ∀ x, P x → List (Fin 4)) (hord : ∀ x Γ, (ord x Γ).Perm [0, 1, 2, 3]) :
    avgLogU (V.gauge u) y κ L off ord =
      u y * avgLogU V y κ L off ord * (u (ofs y (Pi.single κ (L : ℤ))))⁻¹ := by
  have est : ∀ (w : Site n) x (Γ : P x), (V.gauge u).hol (stair w (off x) (ord x Γ) 0) =
      u w * V.hol (stair w (off x) (ord x Γ) 0) * (u (ofs w (off x)))⁻¹ := fun w x Γ => by
    have hc := chain_endpt_stair w (off x) (ord x Γ) 0
    rw [ofs_zero, zero_add, offs_perm _ (hord x Γ)] at hc
    rw [hol_gauge V u _ w hc.1, hc.2]
  have eseg : ∀ (w : Site n), (V.gauge u).hol (segZ κ w (L : ℤ)) =
      u w * V.hol (segZ κ w (L : ℤ)) * (u (w + (L : ℤ) • unit n κ))⁻¹ := fun w => by
    rw [hol_gauge V u _ w (chain_segZ κ w _), endpt_segZ]
  have e1 : ∀ x, ofs y (off x) + (L : ℤ) • unit n κ = ofs (ofs y (Pi.single κ (L : ℤ))) (off x) := fun x => by
    rw [ofs_ofs, add_comm (Pi.single κ _) (off x), ofs_add_single]
  have e2 : y + (L : ℤ) • unit n κ = ofs y (Pi.single κ (L : ℤ)) := by
    rw [← ofs_zero y, ← ofs_add_single, zero_add, ofs_zero]
  have hloop : ∀ x Γ Γ', (V.gauge u).hol (lpath y κ L off ord x Γ Γ') =
      u y * V.hol (lpath y κ L off ord x Γ Γ') * (u y)⁻¹ := fun x Γ Γ' => by
    rw [← loop_eq_hol, ← loop_eq_hol]
    simp only [Average.loop, est, eseg, e1, e2]
    group
  have hβ : betaLog (V.gauge u) y κ L off ord = Ad (u y) (betaLog V y κ L off ord) := by
    unfold betaLog
    simp only [hloop, Ad_sum, Ad_smul]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun Γ _ =>
      Finset.sum_congr rfl fun Γ' _ => ?_
    rw [Units.val_mul, Units.val_mul, ← LogM_conj]
    rfl
  unfold avgLogU
  rw [hβ, eseg, e2, ← Ad_smul, ← expU_conj]
  group

/-- **`lem:average`(ii)** for the extension: two configurations which agree on the paths of the average
have the same extension. -/
theorem avgLogU_congr (V V' : Config N n) (y : Site n) (κ : Fin 4) (L : ℕ) (off : ι → Fin 4 → ℤ)
    (ord : ∀ x, P x → List (Fin 4))
    (hg : ∀ x Γ, V.hol (stair y (off x) (ord x Γ) 0) = V'.hol (stair y (off x) (ord x Γ) 0))
    (hg' : ∀ x Γ, V.hol (stair (ofs y (Pi.single κ (L : ℤ))) (off x) (ord x Γ) 0) =
      V'.hol (stair (ofs y (Pi.single κ (L : ℤ))) (off x) (ord x Γ) 0))
    (hh : ∀ x, V.hol (segZ κ (ofs y (off x)) L) = V'.hol (segZ κ (ofs y (off x)) L))
    (hk : V.hol (segZ κ y L) = V'.hol (segZ κ y L)) :
    avgLogU V y κ L off ord = avgLogU V' y κ L off ord := by
  have hl : ∀ x Γ Γ', V.hol (lpath y κ L off ord x Γ Γ') = V'.hol (lpath y κ L off ord x Γ Γ') :=
    fun x Γ Γ' => by simp only [lpath, hol_append, rv, Transports.hol_rev, hg, hg', hh, hk]
  unfold avgLogU betaLog
  simp only [hl, hk]

/-- The lengths of the loops. -/
lemma length_lpath {h : ℕ} (y : Site n) (κ : Fin 4) (off : ι → Fin 4 → ℤ) (ord : ∀ x, P x → List (Fin 4))
    (hoff : ∀ x, AxialReference.InM h (off x)) (hord : ∀ x Γ, (ord x Γ).Perm [0, 1, 2, 3]) (x : ι)
    (Γ Γ' : P x) : (lpath y κ (2 * h + 1) off ord x Γ Γ').length ≤ 6 * (2 * h + 1) := by
  have hlen : ∀ (Γ : P x) (w : Site n), (stair w (off x) (ord x Γ) 0).length ≤ 4 * h := fun Γ w => by
    rw [length_stair, ((hord x Γ).map _).sum_eq]
    have := hoff x
    have h0 := this 0; have h1 := this 1; have h2 := this 2; have h3 := this 3
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    omega
  have := hlen Γ y
  have := hlen Γ' (ofs y (Pi.single κ ((2 * h + 1 : ℕ) : ℤ)))
  simp only [lpath, List.length_append, length_rv, length_segZ, Int.natAbs_natCast]
  omega

set_option maxHeartbeats 4000000 in
/-- **`lem:average`(vi)** on the lattice: for a `G`-valued `U` whose loops of `c = (y, y + Le_μ)` are within
`c₀` of `id` (as in (v)) and the forms `B = aA` with `‖B‖_∞ < c₀/L`:
1. the loops of `𝐔_B = e^{iB}U` are within `min(r_G, ½)/2 ≤ ¼` of `id`, in the domain of `Log`;
2. `B ↦ M(𝐔_B)(c) = e^{iβ_c}𝐔_B([c])`, with `Log`, is analytic on this ball;
3. for `B` with values in `𝔤` it is the average of the gauge field `𝐔_B`;
4. for `B` with values in `𝔤^c`, `β_c ∈ 𝔤^c`, and `M(𝐔_B)(c) ∈ G^c` if `G ⊂ G^c` (e.g. `G` connected,
   `carrier_le_complexified`). -/
theorem average_analytic (G : GaugeGroup N) (hG : IsClosed G.mats) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ {n : ℕ} [NeZero n] (U : Config N n), IsGField G U →
      ∀ (h : ℕ) (y : Site n) (μ : Fin 4) {ι : Type} [Fintype ι] {P : ι → Type} [∀ x, Fintype (P x)]
      (off : ι → Fin 4 → ℤ) (ord : ∀ x, P x → List (Fin 4)), (∀ x, AxialReference.InM h (off x)) →
      (∀ x Γ, (ord x Γ).Perm [0, 1, 2, 3]) →
      (∀ x Γ Γ', ‖((U.hol (lpath y μ (2 * h + 1) off ord x Γ Γ') : GLN) : Mat) - 1‖ ≤ c₀) →
      (∀ B : Fin 4 → Site n → Mat, ‖B‖ < c₀ / ((2 * h + 1 : ℕ) : ℝ) → ∀ x Γ Γ',
        ‖(((moveC U B).hol (lpath y μ (2 * h + 1) off ord x Γ Γ') : GLN) : Mat) - 1‖ ≤ 1 / 4) ∧
      AnalyticOnNhd ℂ (fun B => ((avgLogU (moveC U B) y μ (2 * h + 1) off ord : GLN) : Mat))
        {B | ‖B‖ < c₀ / ((2 * h + 1 : ℕ) : ℝ)} ∧
      (∀ B : Fin 4 → Site n → Mat, ‖B‖ < c₀ / ((2 * h + 1 : ℕ) : ℝ) → (∀ ρ z, B ρ z ∈ G.lie) →
        avgB G (moveC U B) y μ (2 * h + 1) off ord = avgLogU (moveC U B) y μ (2 * h + 1) off ord) ∧
      (G.LieInput → ∀ B : Fin 4 → Site n → Mat, ‖B‖ < c₀ / ((2 * h + 1 : ℕ) : ℝ) →
        (∀ ρ z, B ρ z ∈ G.lieC) → betaLog (moveC U B) y μ (2 * h + 1) off ord ∈ G.lieC ∧
          (G.carrier ≤ G.complexified →
            avgLogU (moveC U B) y μ (2 * h + 1) off ord ∈ G.complexified)) := by
  obtain ⟨r, hr0, hr1, hch⟩ := GaugeGroup.chart_ii (G := G) hG
  set ρ0 : ℝ := min r (1 / 2) with hρ0
  have hρ00 : 0 < ρ0 := lt_min hr0 (by norm_num)
  have hρr : ρ0 ≤ r := min_le_left _ _
  have hρh : ρ0 ≤ 1 / 2 := min_le_right _ _
  refine ⟨ρ0 / 2048, by positivity, ?_⟩
  intro n _ U hU h y μ ι _ P _ off ord hoff hord hloops
  set Lr : ℝ := ((2 * h + 1 : ℕ) : ℝ) with hLr
  have hL1 : (1 : ℝ) ≤ Lr := by rw [hLr]; exact_mod_cast (by omega : 1 ≤ 2 * h + 1)
  have hl2 := Real.log_two_gt_d9
  -- the loops of `𝐔_B`
  have hlen : ∀ x Γ Γ', ((lpath y μ (2 * h + 1) off ord x Γ Γ').length : ℝ) ≤ 6 * Lr := fun x Γ Γ' => by
    have := length_lpath y μ off ord hoff hord x Γ Γ'
    rw [hLr]; exact_mod_cast this
  have hEbd : ∀ B : Fin 4 → Site n → Mat, ‖B‖ < ρ0 / 2048 / Lr → ∀ x Γ Γ', ∃ l : List Mat,
      (∀ Y ∈ l, ‖Y‖ ≤ ‖B‖) ∧ ((∀ ρ z, B ρ z ∈ G.lieC) → ∀ Y ∈ l, Y ∈ G.lieC) ∧
      (l.length : ℝ) * ‖B‖ ≤ 6 * (ρ0 / 2048) ∧ (l.length : ℝ) ≤ 6 * Lr ∧
      (moveC U B).hol (lpath y μ (2 * h + 1) off ord x Γ Γ') =
        (l.map fun Y => expU (Complex.I • Y)).prod * U.hol (lpath y μ (2 * h + 1) off ord x Γ Γ') :=
    fun B hB x Γ Γ' => by
      obtain ⟨l, hl, hln, hlC, he⟩ := hol_decomp hU B (lpath y μ (2 * h + 1) off ord x Γ Γ')
      have hll : (l.length : ℝ) ≤ 6 * Lr := by rw [hl]; exact hlen x Γ Γ'
      refine ⟨l, hln, hlC, ?_, hll, he⟩
      have hBL : ‖B‖ * Lr ≤ ρ0 / 2048 := by
        rw [lt_div_iff₀ (by linarith)] at hB; linarith
      calc (l.length : ℝ) * ‖B‖ ≤ 6 * Lr * ‖B‖ := mul_le_mul_of_nonneg_right hll (norm_nonneg _)
        _ = 6 * (‖B‖ * Lr) := by ring
        _ ≤ 6 * (ρ0 / 2048) := by linarith
  have hnear : ∀ B : Fin 4 → Site n → Mat, ‖B‖ < ρ0 / 2048 / Lr → ∀ x Γ Γ',
      ‖(((moveC U B).hol (lpath y μ (2 * h + 1) off ord x Γ Γ') : GLN) : Mat) - 1‖ ≤ ρ0 / 2 :=
    fun B hB x Γ Γ' => by
      obtain ⟨l, hln, -, hlB, -, he⟩ := hEbd B hB x Γ Γ'
      have hT : ((l.map fun Y => Complex.I • Y).map norm).sum ≤ 6 * (ρ0 / 2048) := by
        have := List.sum_le_length_nsmul ((l.map fun Y => Complex.I • Y).map norm) ‖B‖
          (by simpa [norm_I_smul'] using hln)
        simp only [List.length_map, nsmul_eq_mul] at this
        linarith
      have hE := (prod_exp_small (l.map fun Y => Complex.I • Y) hT (by linarith)).2
      have hEv : (((l.map fun Y => expU (Complex.I • Y)).prod : GLN) : Mat) =
          ((l.map fun Y => Complex.I • Y).map exp).prod := by
        rw [MeanTransports.val_prod_expU]; simp [List.map_map, Function.comp_def]
      rw [← hEv] at hE
      rw [he]
      have hUu : ((U.hol (lpath y μ (2 * h + 1) off ord x Γ Γ') : GLN) : Mat) ∈
          Matrix.unitaryGroup (Fin N) ℂ := hol_isU hU.gauge _
      rw [Units.val_mul]
      have e : (((l.map fun Y => expU (Complex.I • Y)).prod : GLN) : Mat) *
          ((U.hol (lpath y μ (2 * h + 1) off ord x Γ Γ') : GLN) : Mat) - 1 =
          ((((l.map fun Y => expU (Complex.I • Y)).prod : GLN) : Mat) - 1) *
            ((U.hol (lpath y μ (2 * h + 1) off ord x Γ Γ') : GLN) : Mat) +
          (((U.hol (lpath y μ (2 * h + 1) off ord x Γ Γ') : GLN) : Mat) - 1) := by noncomm_ring
      rw [e]
      refine (norm_add_le _ _).trans ?_
      rw [CStarRing.norm_mul_mem_unitary _ hUu]
      have := hloops x Γ Γ'
      linarith
  have hdom : ∀ B : Fin 4 → Site n → Mat, ‖B‖ < ρ0 / 2048 / Lr → ∀ x Γ Γ',
      ‖(((moveC U B).hol (lpath y μ (2 * h + 1) off ord x Γ Γ') : GLN) : Mat) - 1‖ ≤ 1 / 4 :=
    fun B hB x Γ Γ' => (hnear B hB x Γ Γ').trans (by linarith)
  refine ⟨hdom, ?_, ?_, ?_⟩
  · -- analyticity
    intro B₀ hB₀
    have hlog : ∀ x Γ Γ', AnalyticAt ℂ (fun B => LogM (((moveC U B).hol
        (lpath y μ (2 * h + 1) off ord x Γ Γ') : GLN) : Mat)) B₀ := fun x Γ Γ' =>
      (analyticOnNhd_LogM _ (by simpa using (hdom B₀ hB₀ x Γ Γ').trans_lt (by norm_num))).comp
        (analyticAt_hol U B₀ _)
    have hβ : AnalyticAt ℂ (fun B => betaLog (moveC U B) y μ (2 * h + 1) off ord) B₀ := by
      unfold betaLog
      refine analyticAt_finsum' _ _ fun x _ => analyticAt_finsum' _ _ fun Γ _ =>
        analyticAt_finsum' _ _ fun Γ' _ => ?_
      exact ((hlog x Γ Γ').const_smul (c := (1 / Complex.I : ℂ))).const_smul (c := Average.wt P P x)
    have : (fun B => ((avgLogU (moveC U B) y μ (2 * h + 1) off ord : GLN) : Mat)) =
        fun B => exp (Complex.I • betaLog (moveC U B) y μ (2 * h + 1) off ord) *
          (((moveC U B).hol (segZ μ y ((2 * h + 1 : ℕ) : ℤ)) : GLN) : Mat) := by
      funext B; simp [avgLogU, Units.val_mul, expU_val]
    rw [this]
    exact ((exp_analytic _).comp (hβ.const_smul (c := Complex.I))).mul (analyticAt_hol U B₀ _)
  · -- the average for `B` with values in `𝔤`
    intro B hB hBl
    have hVG : IsGField G (moveC U B) := fun ρ z =>
      G.carrier.mul_mem (by simpa using (hBl ρ z).2 1) (hU ρ z)
    have hchart : ∀ x Γ Γ', G.inChart ((moveC U B).hol (lpath y μ (2 * h + 1) off ord x Γ Γ')) ∧
        G.chartLog ((moveC U B).hol (lpath y μ (2 * h + 1) off ord x Γ Γ')) =
          LogM (((moveC U B).hol (lpath y μ (2 * h + 1) off ord x Γ Γ') : GLN) : Mat) := fun x Γ Γ' => by
      obtain ⟨A', hA', hn', he', hl', -⟩ := hch _ (hVG.hol_mem _) ((hnear B hB x Γ Γ').trans (by linarith))
      obtain ⟨hin, hlg⟩ := GaugeGroup.chartLog_eq hA' hn' he'.symm
      exact ⟨hin, hlg.trans hl'.symm⟩
    unfold avgB avgLogU Average.avg
    have hall : ∀ x Γ Γ', G.inChart (Average.loop
        (fun x Γ => (moveC U B).hol (stair y (off x) (ord x Γ) 0))
        (fun x => (moveC U B).hol (segZ μ (ofs y (off x)) ((2 * h + 1 : ℕ) : ℤ)))
        (fun x Γ' => (moveC U B).hol (stair (ofs y (Pi.single μ ((2 * h + 1 : ℕ) : ℤ))) (off x)
          (ord x Γ') 0))
        ((moveC U B).hol (segZ μ y ((2 * h + 1 : ℕ) : ℤ))) x Γ Γ') := fun x Γ Γ' => by
      rw [loop_eq_hol]; exact (hchart x Γ Γ').1
    simp only [hall, implies_true, ↓reduceIte]
    congr 2
    unfold Average.beta betaLog
    simp only [loop_eq_hol, (hchart _ _ _).2]
  · -- `β_c ∈ 𝔤^c` and the values in `G^c`
    intro hGl B hB hBC
    have hterm : ∀ x Γ Γ', (1 / Complex.I : ℂ) •
        LogM (((moveC U B).hol (lpath y μ (2 * h + 1) off ord x Γ Γ') : GLN) : Mat) ∈ G.lieC := by
      intro x Γ Γ'
      obtain ⟨l, hln, hlC, hlB, hll, he⟩ := hEbd B hB x Γ Γ'
      have h512 : 512 * l.length * ‖B‖ ≤ 1 := by nlinarith
      obtain ⟨ZE, hZEC, hZEe, hZEn⟩ := exists_exp_prod_lieC hGl l (norm_nonneg _) hln (hlC hBC) h512
      have hZE : ‖ZE‖ ≤ 12 * (ρ0 / 2048) := by nlinarith
      obtain ⟨X, hX, hXn, hXe, -, -⟩ := hch _ (hU.hol_mem _) ((hloops x Γ Γ').trans (by linarith))
      have hX3 := (ChartBounds.chart_iii hX.1 hXn.le).2.1
      rw [hXe] at hX3
      have hXs : ‖X‖ ≤ Real.pi / 2 * (ρ0 / 2048) :=
        hX3.trans (mul_le_mul_of_nonneg_left (hloops x Γ Γ') (by positivity))
      have hpi := Real.pi_lt_d2
      have hXs' : ‖X‖ ≤ 2 * (ρ0 / 2048) := hXs.trans (by nlinarith)
      have hUX : U.hol (lpath y μ (2 * h + 1) off ord x Γ Γ') = expU (Complex.I • X) :=
        Units.ext (by rw [expU_val]; exact hXe.symm)
      have hW : (moveC U B).hol (lpath y μ (2 * h + 1) off ord x Γ Γ') =
          expU (Complex.I • psi ZE X) := by
        rw [he, ← hZEe, hUX, LatticeKappa.expU_mul_expU (by linarith)]
      have hWn : ‖psi ZE X‖ ≤ 1 / 4 := norm_psi_le (by linarith) (by linarith)
      rw [hW, expU_val, LogM_exp (by rw [norm_I_smul']; linarith), smul_smul,
        one_div, inv_mul_cancel₀ Complex.I_ne_zero, one_smul]
      exact psi_mem hGl hZEC (lie_subset_lieC' hX) (by linarith)
    have hβC : betaLog (moveC U B) y μ (2 * h + 1) off ord ∈ G.lieC := by
      show betaLog (moveC U B) y μ (2 * h + 1) off ord ∈ GaugeGroup.lieCSubmodule hGl
      unfold betaLog
      refine Submodule.sum_mem _ fun x _ => Submodule.sum_mem _ fun Γ _ => Submodule.sum_mem _ fun Γ' _ => ?_
      exact Submodule.smul_mem _ _ (hterm x Γ Γ')
    refine ⟨hβC, fun hcon => ?_⟩
    unfold avgLogU
    refine G.complexified.mul_mem (Subgroup.subset_closure ⟨_, hβC, rfl⟩) ?_
    obtain ⟨l, -, -, hlC, he⟩ := hol_decomp hU B (segZ μ y ((2 * h + 1 : ℕ) : ℤ))
    rw [he]
    refine G.complexified.mul_mem (G.complexified.list_prod_mem fun g hg => ?_) (hcon (hU.hol_mem _))
    simp only [List.mem_map] at hg
    obtain ⟨Y, hY, rfl⟩ := hg
    exact Subgroup.subset_closure ⟨Y, hlC hBC Y hY, rfl⟩

end AverageHolo

end CoreLean

end
