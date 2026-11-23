/-
`lem:close-transports` of BALABAN_CORE.tex (`f1da63a7f109`) on the lattice: the mean transports of two
gauge fields which are close on the bonds of a block.

* `hol_ratio`: `‖V(γ)V₀(γ)⁻¹ - id‖ ≤ |γ|α` if `‖V(b)V₀(b)⁻¹ - id‖ ≤ α` on the bonds of `γ` (the factors moved
  to the left, conjugate by unitary matrices).
* `isMeanOf_unique`: the mean transport is unique when the exponents relative to the reference are small.
* `isMeanOf_mem`: the mean of elements of `G` lies in `G` (`group_mean_lie`).
* `close_transports`: for `V₀`, `V` `G`-valued on the block `B(y)`, with the plaquettes of `V₀` at most `β` and
  `‖V(b)V₀(b)⁻¹ - id‖ ≤ α` on the bonds, `L²β` and `Lα` small: the mean transports of `V` are defined, and for
  every mean transport `T` of `V` and the mean transport `T₀` of `V₀`, `TT₀⁻¹ = e^{iZ}` with `Z ∈ 𝔤` and
  `‖Z‖ ≤ 8πLα ≤ 48πLα`.
-/
import CoreLean.LatticeKappa
import CoreLean.GroupMeanII

open Matrix NormedSpace
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace CoreLean

namespace LatticeKappa

open LatticePaths MeanTransports GroupMean

set_option linter.unusedSectionVars false

variable {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "GLN" => (Matrix (Fin N) (Fin N) ℂ)ˣ

variable {n : ℕ} [NeZero n]

/-- The holonomies of two close fields. -/
theorem hol_ratio {V V0 : Config N n} (hV : V.IsGaugeField) (hV0 : V0.IsGaugeField) {α : ℝ} :
    ∀ γ : List (Bond n), (∀ t ∈ γ, ‖((V.val t * (V0.val t)⁻¹ : GLN) : Mat) - 1‖ ≤ α) →
      ‖((V.hol γ * (V0.hol γ)⁻¹ : GLN) : Mat) - 1‖ ≤ γ.length * α
  | [], _ => by simp [Config.hol]
  | t :: γ, hγ => by
    have ih := hol_ratio hV hV0 γ fun t' ht' => hγ t' (by simp [ht'])
    have ht := hγ t (by simp)
    have e : V.hol (t :: γ) * (V0.hol (t :: γ))⁻¹ =
        (V.val t * (V0.val t)⁻¹) * (V0.val t * (V.hol γ * (V0.hol γ)⁻¹) * (V0.val t)⁻¹) := by
      rw [hol_cons, hol_cons]; group
    rw [e]
    have hu : IsU (V.val t * (V0.val t)⁻¹) := (val_isU hV t).mul (val_isU hV0 t).inv
    refine (norm_mul_sub_one_le hu).trans ?_
    rw [norm_conj_sub_one' (val_isU hV0 t)]
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
    linarith

/-- The uniqueness of the mean transport. -/
theorem isMeanOf_unique {k : ℕ} (hk : 0 < k) (W : Fin k → GLN) (x₀ : Fin k) (Y : Fin k → Mat)
    (hW : ∀ Γ, W Γ = expU (Complex.I • Y Γ) * W x₀) (hY : ∀ Γ, ‖Y Γ‖ ≤ 1 / 512) {T T' : GLN}
    (hT : IsMeanOf W x₀ T) (hT' : IsMeanOf W x₀ T') : T = T' := by
  have key : ∀ T, IsMeanOf W x₀ T → T = mean Y (W x₀) := fun T hT => by
    obtain ⟨Z, hZ, hTZ, hsum⟩ := hT
    have hsum' : ∑ Γ, LogM (((expU (Complex.I • Y Γ) * W x₀) * (expU (Complex.I • Z) * W x₀)⁻¹ : GLN) :
        Mat) = 0 := by
      rw [← hsum]
      refine Finset.sum_congr rfl fun Γ _ => ?_
      rw [← hW Γ, hTZ]
    rw [hTZ, mean_unique hk hY (W x₀) hZ hsum']
    rfl
  rw [key T hT, key T' hT']

/-- The mean of elements of `G` with exponents in `𝔤` lies in `G`. -/
theorem isMeanOf_mem (G : GaugeGroup N) (hG : IsClosed G.mats) :
    ∃ c : ℝ, 0 < c ∧ ∀ {k : ℕ} (_hk : 0 < k) (W : Fin k → GLN) (x₀ : Fin k) (Y : Fin k → Mat) (M : ℝ),
      W x₀ ∈ G.carrier → (∀ Γ, W Γ = expU (Complex.I • Y Γ) * W x₀) → (∀ Γ, Y Γ ∈ G.lie) →
      (∀ Γ, ‖Y Γ‖ ≤ M) → 512 * M ≤ 1 → 2 * M ≤ c → ∀ T, IsMeanOf W x₀ T → T ∈ G.carrier := by
  obtain ⟨c, hc0, Hc⟩ := group_mean_lie G hG
  refine ⟨c, hc0, fun {k} hk W x₀ Y M hWx hW hYl hYM hM hMc T hT => ?_⟩
  have hY512 : ∀ Γ, ‖Y Γ‖ ≤ 1 / 512 := fun Γ => (hYM Γ).trans (by linarith)
  obtain ⟨Z₀, hZ₀l, hZ₀n, hZ₀s, -⟩ := Hc hk Y M hYM hM hMc hYl
  have hZ₀ : Z₀ = meanV Y := meanV_unique hk hY512 (by linarith) hZ₀s
  have hT' : IsMeanOf W x₀ (mean Y (W x₀)) := by
    refine ⟨meanV Y, (meanV_spec hk hY512).1, rfl, ?_⟩
    have := mean_spec hk hY512 (W x₀)
    rw [← this]
    refine Finset.sum_congr rfl fun Γ _ => ?_
    rw [← hW Γ]
  rw [isMeanOf_unique hk W x₀ Y hW hY512 hT hT']
  show expU (Complex.I • meanV Y) * W x₀ ∈ G.carrier
  rw [← hZ₀]
  exact G.carrier.mul_mem (by simpa using hZ₀l.2 1) hWx

/-- `‖Ψ(A, B)‖ ≤ ‖A‖ + ‖B‖ + 256‖A‖‖B‖` for `‖A‖, ‖B‖ ≤ 1/32`. -/
lemma norm_psi_le' {A B : Mat} (hA : ‖A‖ ≤ 1 / 32) (hB : ‖B‖ ≤ 1 / 32) :
    ‖psi A B‖ ≤ ‖A‖ + ‖B‖ + 256 * (‖A‖ * ‖B‖) := by
  have h := psi_lipschitz (X := 0) (Y := 0) (X' := A) (Y' := B) (by simp) (by simp) hA hB
  rw [psi_zero_right (by simp)] at h
  simp only [sub_zero, norm_zero, zero_mul, add_zero] at h
  have e : psi A B = (psi A B - A - B) + A + B := by abel
  rw [e]
  have := norm_add_le (psi A B - A - B + A) B
  have := norm_add_le (psi A B - A - B) A
  nlinarith [norm_nonneg A, norm_nonneg B]

/-- `e^{iA}e^{iB} = e^{iΨ(A, B)}` as units. -/
lemma expU_mul_expU {A B : Mat} (h : ‖A‖ + ‖B‖ < Real.log 2) :
    expU (Complex.I • A) * expU (Complex.I • B) = expU (Complex.I • psi A B) :=
  Units.ext (by rw [Units.val_mul, expU_val, expU_val, expU_val, exp_I_psi h])

set_option maxHeartbeats 4000000 in
/-- **`lem:close-transports`** on the lattice: for `G`-valued `V₀`, `V` on the block `B(y)` with
`‖V₀(∂p) - id‖ ≤ β` on the plaquettes of the block and `‖V(b)V₀(b)⁻¹ - id‖ ≤ α` on its bonds, `L²β ≤ R` and
`Lα ≤ R`: the mean transports of `V` to the points `x = y + m` of the block are defined, and every mean
transport `T` of `V` and the mean transport `T₀` of `V₀` satisfy `TT₀⁻¹ = e^{iZ}` with `Z ∈ 𝔤` and
`‖Z‖ ≤ 48πLα`. -/
theorem close_transports (G : GaugeGroup N) (hG : IsClosed G.mats) :
    ∃ R : ℝ, 0 < R ∧ ∀ {n : ℕ} [NeZero n] (V0 V : Config N n), IsGField G V0 → IsGField G V →
      ∀ (y : Site n) (h : ℕ) (β α : ℝ), 0 ≤ β → 0 ≤ α →
      PlaqBound V0 (boxR y (AxialReference.loB h) (fun _ => (h : ℤ))) β →
      ((2 * h + 1 : ℕ) : ℝ) ^ 2 * β ≤ R → ((2 * h + 1 : ℕ) : ℝ) * α ≤ R →
      (∀ t : Bond n, (∃ v, AxialReference.InM h v ∧ t.site = ofs y v) →
        (∃ v, AxialReference.InM h v ∧ t.plus = ofs y v) →
        ‖((V.val t * (V0.val t)⁻¹ : GLN) : Mat) - 1‖ ≤ α) →
      ∀ (m : Fin 4 → ℤ), AxialReference.InM h m → ∀ {k : ℕ} (_hk : 0 < k) (l : Fin k → List (Fin 4)),
      (∀ Γ, (l Γ).Perm [0, 1, 2, 3]) → ∀ x₀, l x₀ = [0, 1, 2, 3] → ∀ T0 : GLN,
      IsMeanOf (fun Γ => V0.hol (stair y m (l Γ) 0)) x₀ T0 →
      (∃ T, IsMeanOf (fun Γ => V.hol (stair y m (l Γ) 0)) x₀ T) ∧
      ∀ T, IsMeanOf (fun Γ => V.hol (stair y m (l Γ) 0)) x₀ T →
        ∃ Z ∈ G.lie, T * T0⁻¹ = expU (Complex.I • Z) ∧
          ‖Z‖ ≤ 48 * Real.pi * ((2 * h + 1 : ℕ) : ℝ) * α := by
  obtain ⟨r_m, hr_m, Hm⟩ := moved_iii_lattice G hG
  obtain ⟨r_e, hr_e, He⟩ := elements_of_G G hG
  obtain ⟨c_g, hc_g, Hg⟩ := isMeanOf_mem G hG
  obtain ⟨r_c, hr_c, -, hch⟩ := GaugeGroup.chart_ii (G := G) hG
  set R0 : ℝ := min (min r_m r_e) (min r_c (min c_g (1 / 4096))) with hR0
  have hR00 : 0 < R0 := lt_min (lt_min hr_m hr_e) (lt_min hr_c (lt_min hc_g (by norm_num)))
  have hRm : R0 ≤ r_m := (min_le_left _ _).trans (min_le_left _ _)
  have hRe : R0 ≤ r_e := (min_le_left _ _).trans (min_le_right _ _)
  have hRc : R0 ≤ r_c := (min_le_right _ _).trans (min_le_left _ _)
  have hRg : R0 ≤ c_g := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hR4 : R0 ≤ 1 / 4096 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨R0 / 1000, by positivity, ?_⟩
  intro n _ V0 V hV0 hV y h β α hβ hα hPB hLβ hLα hVV0 m hm k hk l hl x₀ hx₀ T0 hT0
  have hpi := Real.pi_lt_d2
  have hl2 := Real.log_two_gt_d9
  have hpi0 := Real.pi_pos
  set Lr : ℝ := ((2 * h + 1 : ℕ) : ℝ) with hLr
  have hLr' : Lr = 2 * h + 1 := by rw [hLr]; push_cast; ring
  have hh0 : (0 : ℝ) ≤ h := Nat.cast_nonneg h
  have h2h : 2 * (h : ℝ) ≤ Lr := by rw [hLr']; linarith
  have hL1 : (1 : ℝ) ≤ Lr := by rw [hLr']; linarith
  -- the smallness
  have h6 : 6 * (h : ℝ) ^ 2 * β ≤ 3 / 2 * (R0 / 1000) := by
    have : 6 * (h : ℝ) ^ 2 ≤ 3 / 2 * Lr ^ 2 := by nlinarith
    nlinarith
  have hqβ : Real.pi / 2 * (6 * (h : ℝ) ^ 2 * β) ≤ 3 * (R0 / 1000) := by nlinarith
  have hαL : 4 * (h : ℝ) * α ≤ 2 * (R0 / 1000) := by nlinarith
  -- the transports of `V₀`
  have hbox : ∀ v, AxialReference.InM h v → LatticePaths.InBox (AxialReference.loB h) (fun _ => (h : ℤ)) v :=
    fun v hv σ => ⟨(hv σ).1, (hv σ).2⟩
  obtain ⟨X, hX⟩ := Hm V0 hV0 y _ _ β hβ hPB m (hbox 0 (AxialReference.inM_zero h)) (hbox m hm) (h : ℝ)
    (AxialReference.natAbs_le hm) (by linarith) (by nlinarith) hk l hl x₀ hx₀ T0 hT0
  set q0 : ℝ := 4 * (Real.pi / 2 * (6 * (h : ℝ) ^ 2 * β)) with hq0
  have hq0b : q0 ≤ 12 * (R0 / 1000) := by rw [hq0]; linarith
  have hq00 : 0 ≤ q0 := (norm_nonneg _).trans (hX x₀).2
  have hXn : ∀ Γ, ‖X Γ‖ ≤ q0 := fun Γ => (hX Γ).2
  -- the lengths of the paths
  have hlen : ∀ Γ, ((stair y m (l Γ) 0).length : ℝ) ≤ 4 * h := fun Γ => by
    have : (stair y m (l Γ) 0).length ≤ 4 * h := by
      rw [length_stair, ((hl Γ).map _).sum_eq]
      have h0 := hm 0; have h1 := hm 1; have h2 := hm 2; have h3 := hm 3
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      omega
    exact_mod_cast this
  have hnd : ∀ Γ, (l Γ).Nodup := fun Γ => (hl Γ).nodup_iff.2 (by decide)
  -- `V(Γ)V₀(Γ)⁻¹ = e^{iY_Γ}`
  have hrat : ∀ Γ, ‖((V.hol (stair y m (l Γ) 0) * (V0.hol (stair y m (l Γ) 0))⁻¹ : GLN) : Mat) - 1‖ ≤
      4 * h * α := fun Γ => by
    refine (hol_ratio hV.gauge hV0.gauge _ fun t ht => ?_).trans
      (mul_le_mul_of_nonneg_right (hlen Γ) hα)
    obtain ⟨v, v', hv, hv', hs, hp⟩ := RegularAverages.stair_ends y y 0 m (ofs_zero y).symm hm _ (hnd Γ) t ht
    rw [zero_add] at hs hp
    exact hVV0 t ⟨v, hv, hs⟩ ⟨v', hv', hp⟩
  have hY : ∀ Γ, ∃ Y ∈ G.lie, V.hol (stair y m (l Γ) 0) * (V0.hol (stair y m (l Γ) 0))⁻¹ =
      expU (Complex.I • Y) ∧ ‖Y‖ ≤ Real.pi / 2 * (4 * h * α) := fun Γ =>
    He _ _ (hV.hol_mem _) (hV0.hol_mem _) _ (hrat Γ) (by linarith)
  choose Y hYl hYe hYn using hY
  have hYn' : ∀ Γ, ‖Y Γ‖ ≤ 4 * (R0 / 1000) := fun Γ => by nlinarith [hYn Γ]
  -- `V(Γ) = e^{iX'_Γ}T₀`, `X'_Γ = Ψ(Y_Γ, X_Γ)`
  set X' : Fin k → Mat := fun Γ => psi (Y Γ) (X Γ) with hX'd
  have hVX : ∀ Γ, V.hol (stair y m (l Γ) 0) = expU (Complex.I • X' Γ) * T0 := fun Γ => by
    have e1 : V.hol (stair y m (l Γ) 0) = expU (Complex.I • Y Γ) * V0.hol (stair y m (l Γ) 0) := by
      rw [← hYe Γ]; group
    rw [e1, (hX Γ).1, ← mul_assoc, expU_mul_expU (by linarith [hYn' Γ, hXn Γ])]
  have hdX : ∀ Γ, ‖X' Γ - X Γ‖ ≤ 2 * ‖Y Γ‖ := fun Γ => by
    have h1 := psi_lipschitz (X := 0) (Y := X Γ) (X' := Y Γ) (Y' := X Γ) (by simp)
      (by linarith [hXn Γ]) (by linarith [hYn' Γ]) (by linarith [hXn Γ])
    rw [psi_zero_left (by linarith [hXn Γ])] at h1
    simp only [sub_zero, sub_self, norm_zero, mul_zero, add_zero] at h1
    have e : X' Γ - X Γ = (psi (Y Γ) (X Γ) - X Γ - Y Γ) + Y Γ := by rw [hX'd]; abel
    rw [e]
    have := norm_add_le (psi (Y Γ) (X Γ) - X Γ - Y Γ) (Y Γ)
    have h2 : 256 * (‖X Γ‖ * ‖Y Γ‖) ≤ ‖Y Γ‖ := by
      have : 256 * ‖X Γ‖ ≤ 1 := by linarith [hXn Γ]
      nlinarith [norm_nonneg (Y Γ)]
    linarith
  have hX'n : ∀ Γ, ‖X' Γ‖ ≤ 20 * (R0 / 1000) := fun Γ => by
    have := norm_sub_norm_le (X' Γ) (X Γ)
    linarith [hdX Γ, hYn' Γ, hXn Γ]
  have hX512 : ∀ Γ, ‖X Γ‖ ≤ 1 / 512 := fun Γ => by linarith [hXn Γ]
  have hX'512 : ∀ Γ, ‖X' Γ‖ ≤ 1 / 512 := fun Γ => by linarith [hX'n Γ]
  -- `𝗆({e^{iX_Γ}}) = id`
  have hmX : meanV X = 0 := by
    obtain ⟨-, -, -, hsum⟩ := hT0
    have hsX : ∑ Γ, X Γ = 0 := by
      have e : ∀ Γ, LogM (((V0.hol (stair y m (l Γ) 0) * T0⁻¹ : GLN)) : Mat) = Complex.I • X Γ :=
        fun Γ => by
          rw [(hX Γ).1, mul_inv_cancel_right, expU_val]
          exact LogM_exp (by rw [norm_I_smul']; linarith [hXn Γ])
      simp only [e] at hsum
      rw [← Finset.smul_sum, smul_eq_zero] at hsum
      exact hsum.resolve_left Complex.I_ne_zero
    refine (meanV_unique hk hX512 (by simp) ?_).symm
    simp only [neg_zero]
    rw [Finset.sum_congr rfl fun Γ _ => psi_zero_right (by linarith [hXn Γ])]
    exact hsX
  -- the mean transport of `V`
  have hdmax : ∀ Γ, ‖X' Γ - X Γ‖ ≤ 2 * (Real.pi / 2 * (4 * h * α)) := fun Γ =>
    (hdX Γ).trans (by linarith [hYn Γ])
  have hZn : ‖meanV X'‖ ≤ 8 * (Real.pi / 2 * (4 * h * α)) := by
    have := meanV_lipschitz hk hX512 hX'512 hdmax
    rw [hmX, sub_zero] at this
    linarith
  have hZ48 : ‖meanV X'‖ ≤ 48 * Real.pi * Lr * α := by
    have k := mul_le_mul_of_nonneg_left h2h (by positivity : 0 ≤ Real.pi * α)
    have : 8 * (Real.pi / 2 * (4 * h * α)) ≤ 48 * Real.pi * Lr * α := by nlinarith
    linarith
  have hZs : ‖meanV X'‖ ≤ 48 * (R0 / 1000) := by nlinarith
  set T' : GLN := expU (Complex.I • meanV X') * T0 with hT'd
  -- the exponents relative to `V(Γ_{x₀})`
  have hrel : ∀ Γ, V.hol (stair y m (l Γ) 0) =
      expU (Complex.I • psi (X' Γ) (-X' x₀)) * V.hol (stair y m (l x₀) 0) := fun Γ => by
    rw [← expU_mul_expU (by rw [norm_neg]; linarith [hX'n Γ, hX'n x₀]), hVX Γ, hVX x₀,
      show expU (Complex.I • -X' x₀) = (expU (Complex.I • X' x₀))⁻¹ by rw [expU_inv, smul_neg]]
    group
  have hrel512 : ∀ Γ, ‖psi (X' Γ) (-X' x₀)‖ ≤ 1 / 512 := fun Γ => by
    have := norm_psi_le' (A := X' Γ) (B := -X' x₀) (by linarith [hX'n Γ])
      (by rw [norm_neg]; linarith [hX'n x₀])
    rw [norm_neg] at this
    nlinarith [hX'n Γ, hX'n x₀, norm_nonneg (X' Γ), norm_nonneg (X' x₀)]
  have hT'mean : IsMeanOf (fun Γ => V.hol (stair y m (l Γ) 0)) x₀ T' := by
    refine ⟨psi (meanV X') (-X' x₀), ?_, ?_, ?_⟩
    · have := norm_psi_le' (A := meanV X') (B := -X' x₀) (by linarith) (by rw [norm_neg]; linarith [hX'n x₀])
      rw [norm_neg] at this
      nlinarith [hX'n x₀, norm_nonneg (meanV X'), norm_nonneg (X' x₀)]
    · show T' = expU (Complex.I • psi (meanV X') (-X' x₀)) * V.hol (stair y m (l x₀) 0)
      rw [← expU_mul_expU (by rw [norm_neg]; linarith [hX'n x₀]), hVX x₀,
        show expU (Complex.I • -X' x₀) = (expU (Complex.I • X' x₀))⁻¹ by rw [expU_inv, smul_neg], hT'd]
      group
    · have := mean_spec hk hX'512 T0
      rw [← this]
      refine Finset.sum_congr rfl fun Γ _ => ?_
      show LogM ((V.hol (stair y m (l Γ) 0) * T'⁻¹ : GLN) : Mat) = _
      rw [hVX Γ]
      rfl
  have huniq : ∀ T, IsMeanOf (fun Γ => V.hol (stair y m (l Γ) 0)) x₀ T → T = T' := fun T hT =>
    isMeanOf_unique hk _ x₀ _ hrel hrel512 hT hT'mean
  -- `T₀` and `T'` lie in `G`
  have hdist : ∀ (A B : Mat), ‖A‖ ≤ 1 / 64 → ‖B‖ ≤ 1 / 64 →
      ‖((expU (Complex.I • A) * expU (Complex.I • -B) : GLN) : Mat) - 1‖ ≤ 2 * (‖A‖ + ‖B‖) := by
    intro A B hA hB
    have hT : (([Complex.I • A, Complex.I • -B]).map norm).sum ≤ ‖A‖ + ‖B‖ := by
      simp [norm_I_smul']
    have := (RegularAverages.prod_exp_small _ hT (by linarith)).2
    simpa [Units.val_mul, expU_val] using this
  have hT0G : T0 ∈ G.carrier := by
    have hel : ∀ Γ, ∃ Ye ∈ G.lie, V0.hol (stair y m (l Γ) 0) * (V0.hol (stair y m (l x₀) 0))⁻¹ =
        expU (Complex.I • Ye) ∧ ‖Ye‖ ≤ Real.pi / 2 * (2 * (q0 + q0)) := fun Γ => by
      refine He _ _ (hV0.hol_mem _) (hV0.hol_mem _) _ ?_ (by nlinarith)
      have e : V0.hol (stair y m (l Γ) 0) * (V0.hol (stair y m (l x₀) 0))⁻¹ =
          expU (Complex.I • X Γ) * expU (Complex.I • -X x₀) := by
        rw [(hX Γ).1, (hX x₀).1,
          show expU (Complex.I • -X x₀) = (expU (Complex.I • X x₀))⁻¹ by rw [expU_inv, smul_neg]]
        group
      rw [e]
      exact (hdist _ _ (by linarith [hXn Γ]) (by linarith [hXn x₀])).trans (by linarith [hXn Γ, hXn x₀])
    choose Ye hYel hYee hYen using hel
    refine Hg hk _ x₀ Ye (Real.pi / 2 * (2 * (q0 + q0))) (hV0.hol_mem _) (fun Γ => ?_) hYel hYen
      (by nlinarith) (by nlinarith) T0 hT0
    rw [← hYee Γ]; group
  have hT'G : T' ∈ G.carrier := by
    have hel : ∀ Γ, ∃ Ye ∈ G.lie, V.hol (stair y m (l Γ) 0) * (V.hol (stair y m (l x₀) 0))⁻¹ =
        expU (Complex.I • Ye) ∧ ‖Ye‖ ≤ Real.pi / 2 * (2 * (40 * (R0 / 1000))) := fun Γ => by
      refine He _ _ (hV.hol_mem _) (hV.hol_mem _) _ ?_ (by nlinarith)
      have e : V.hol (stair y m (l Γ) 0) * (V.hol (stair y m (l x₀) 0))⁻¹ =
          expU (Complex.I • X' Γ) * expU (Complex.I • -X' x₀) := by
        rw [hVX Γ, hVX x₀,
          show expU (Complex.I • -X' x₀) = (expU (Complex.I • X' x₀))⁻¹ by rw [expU_inv, smul_neg]]
        group
      rw [e]
      exact (hdist _ _ (by linarith [hX'n Γ]) (by linarith [hX'n x₀])).trans
        (by linarith [hX'n Γ, hX'n x₀])
    choose Ye hYel hYee hYen using hel
    refine Hg hk _ x₀ Ye (Real.pi / 2 * (2 * (40 * (R0 / 1000)))) (hV.hol_mem _) (fun Γ => ?_) hYel
      hYen (by nlinarith) (by nlinarith) T' hT'mean
    rw [← hYee Γ]; group
  -- `Z ∈ 𝔤` by the chart
  have hZl : meanV X' ∈ G.lie := by
    have hW : T' * T0⁻¹ = expU (Complex.I • meanV X') := by rw [hT'd]; group
    have hWG : T' * T0⁻¹ ∈ G.carrier := G.carrier.mul_mem hT'G (G.carrier.inv_mem hT0G)
    have hWn : ‖((T' * T0⁻¹ : GLN) : Mat) - 1‖ ≤ r_c := by
      rw [hW]
      have hT : (([Complex.I • meanV X']).map norm).sum ≤ ‖meanV X'‖ := by simp [norm_I_smul']
      have := (RegularAverages.prod_exp_small _ hT (by linarith)).2
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at this
      rw [expU_val]
      linarith
    obtain ⟨A, hA, -, -, hlog, -⟩ := hch _ hWG hWn
    have h1 : LogM ((T' * T0⁻¹ : GLN) : Mat) = Complex.I • meanV X' := by
      rw [hW, expU_val]
      exact LogM_exp (by rw [norm_I_smul']; linarith)
    rw [h1] at hlog
    rw [smul_right_injective Mat Complex.I_ne_zero hlog]
    exact hA
  refine ⟨⟨T', hT'mean⟩, fun T hT => ⟨meanV X', hZl, ?_, hZ48⟩⟩
  rw [huniq T hT, hT'd]
  group

end LatticeKappa

end CoreLean

end
