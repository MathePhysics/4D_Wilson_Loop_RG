/-
The difference of the linear parts of the averages at a complex field and at the trivial field, for the input
`hQ` of `lem:sf-vector-decay` (step (4) of "The complex field"), by a recursion over the levels in place of the
lemma of Schwarz.

* `kernel_step_diff`: one step, `E_{l+1} = LQ(V_l)E_l + (LQ(V_l) - Q₀(U_l))D_l` gives
  `‖E_{l+1}‖_{1,l+1} ≤ (L^{-3} + 8Cα_l)‖E_l‖_{1,l} + 8Cα_l‖D_l‖_{1,l}` (`pert_bound`, the counts of `kernel_step`).
-/
import CoreLean.RelativeAverageKernels

open Matrix NormedSpace Filter Topology Metric
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace CoreLean
namespace RelativeAverage

open LatticePaths LatticeKappa RegularAverages BlockPaths AverageHolo MeanTransports AxialReference
  AxialStraightLattice BoxGeometry StraightExtension

variable {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "GLN" => (Matrix (Fin N) (Fin N) ℂ)ˣ

/-- **The accumulation of the differences**: `x₀ = 0` and `x_{l+1} ≤ q(1 + β_l)x_l + qβ_lq^ld₀` give
`x_l ≤ (e^{Σ_{i<l}β_i} - 1)q^ld₀`. -/
lemma accum_le {q d0 : ℝ} (hq : 0 ≤ q) (hd0 : 0 ≤ d0) (x β : ℕ → ℝ) (hβ : ∀ l, 0 ≤ β l) (hx0 : x 0 = 0)
    (n : ℕ) (hrec : ∀ l, l < n → x (l + 1) ≤ q * (1 + β l) * x l + q * β l * (q ^ l * d0)) :
    ∀ l, l ≤ n → x l ≤ (Real.exp (∑ i ∈ Finset.range l, β i) - 1) * (q ^ l * d0) := by
  intro l
  induction l with
  | zero => intro _; simp [hx0]
  | succ l ih =>
    intro hl
    have h1 := ih (by omega)
    have h2 := hrec l (by omega)
    set s := ∑ i ∈ Finset.range l, β i
    have hs : 0 ≤ s := Finset.sum_nonneg fun i _ => hβ i
    have hes : 1 ≤ Real.exp s := Real.one_le_exp hs
    have hqd : 0 ≤ q ^ l * d0 := by positivity
    have hb := hβ l
    have hexp : 1 + β l ≤ Real.exp (β l) := by linarith [Real.add_one_le_exp (β l)]
    have hc : 0 ≤ q * (1 + β l) := by positivity
    rw [Finset.sum_range_succ, Real.exp_add, pow_succ]
    calc x (l + 1) ≤ q * (1 + β l) * x l + q * β l * (q ^ l * d0) := h2
      _ ≤ q * (1 + β l) * ((Real.exp s - 1) * (q ^ l * d0)) + q * β l * (q ^ l * d0) := by gcongr
      _ = q * (q ^ l * d0) * ((1 + β l) * Real.exp s - 1) := by ring
      _ ≤ q * (q ^ l * d0) * (Real.exp (β l) * Real.exp s - 1) := by
          gcongr
      _ = (Real.exp s * Real.exp (β l) - 1) * (q ^ l * q * d0) := by ring

open Classical in
/-- **One step of the difference**: if `E_{l+1} = LQ(V_l)E_l + (LQ(V_l) - Q₀(U_l))D_l` on the region, then
`‖E_{l+1}‖_{1,l+1} ≤ (L^{-3} + 8Cα_l)‖E_l‖_{1,l} + 8Cα_l‖D_l‖_{1,l}`, `α_l = α₀⁽ˡ⁾ + α₁⁽ˡ⁾`. -/
theorem kernel_step_diff (h : ℕ) :
    ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧ ∀ (nl : ℕ) (μ : Fin 4) (nn : ℕ → ℕ) [∀ l, NeZero (nn l)],
      (∀ l, 4 * h + 4 ≤ nn l) → ∀ (base : ∀ l, Site (nn l)) (U V : ∀ l, Config N (nn l))
      (A' E D : ∀ l, Fin 4 → Site (nn l) → Mat) (a₀ a₁ : ℕ → ℝ),
      (∀ l, U l |>.IsGaugeField) →
      (∀ l, l < nl → ∀ ν x, Lat (Lz h) l x → Rg h nl μ l x → Rg h nl μ l (x + Lz h ^ l • Pi.single ν 1) →
        V l ν (img h (base l) l x) = moveC (U l) (A' l) ν (img h (base l) l x)) →
      (∀ l, l < nl → ∀ ρ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x →
        Rg h nl μ (l + 1) (x + Lz h ^ (l + 1) • Pi.single ρ 1) →
        (∀ μ' ν' z, PlaqIn (boxR (img h (base l) l x) (loD h) (hiD h ρ ρ)) μ' ν' z →
          hs (((plaq (U l) μ' ν' z : GLN) : Mat) - 1) ≤ a₀ l) ∧
        (∀ ν z, BoxBond (img h (base l) l x) h ρ ν z → ‖A' l ν z‖ ≤ a₁ l)) →
      (∀ l, l < nl → 0 ≤ a₀ l ∧ 0 ≤ a₁ l ∧ a₀ l ≤ c ∧ a₁ l ≤ c) →
      (∀ l, l < nl → ∀ ρ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x →
        Rg h nl μ (l + 1) (x + Lz h ^ (l + 1) • Pi.single ρ 1) →
        E (l + 1) ρ (img h (base (l + 1)) (l + 1) x) =
          ((2 * h + 1 : ℕ) : ℂ) • Qlin (V l) (img h (base l) l x) ρ h (E l) +
            (((2 * h + 1 : ℕ) : ℂ) • Qlin (V l) (img h (base l) l x) ρ h (D l) -
              Q0L (U l) (img h (base l) l x) ρ h (D l))) →
      ∀ l, l < nl →
        ell1 h nl μ (l + 1) (fun x ν => ‖E (l + 1) ν (img h (base (l + 1)) (l + 1) x)‖) ≤
          ((((2 * h + 1 : ℕ) : ℝ) ^ 3)⁻¹ + 8 * C * (a₀ l + a₁ l)) *
            ell1 h nl μ l (fun x ν => ‖E l ν (img h (base l) l x)‖) +
          8 * C * (a₀ l + a₁ l) * ell1 h nl μ l (fun x ν => ‖D l ν (img h (base l) l x)‖) := by
  choose cp Cp hcp hCp hpert using fun ρ : Fin 4 => pert_bound (N := N) h ρ
  set c := Finset.univ.inf' Finset.univ_nonempty cp
  set C := Finset.univ.sup' Finset.univ_nonempty Cp
  have hc0 : 0 < c := (Finset.lt_inf'_iff _).2 fun ρ _ => hcp ρ
  have hcle : ∀ ρ, c ≤ cp ρ := fun ρ => Finset.inf'_le _ (Finset.mem_univ ρ)
  have hCle : ∀ ρ, Cp ρ ≤ C := fun ρ => Finset.le_sup' _ (Finset.mem_univ ρ)
  have hC0 : 0 ≤ C := (hCp 0).trans (hCle 0)
  refine ⟨c, C, hc0, hC0, ?_⟩
  intro nl μ nn _ hn base U V A' E D a₀ a₁ hU hVU hdat ha hE l hl
  have hn2 : 4 * h + 2 ≤ nn l := by have := hn l; omega
  obtain ⟨ha0, ha1, ha0c, ha1c⟩ := ha l hl
  set f : (Fin 4 → ℤ) → Fin 4 → ℝ := fun x ν => ‖E l ν (img h (base l) l x)‖ with hf
  set g : (Fin 4 → ℤ) → Fin 4 → ℝ := fun x ν => ‖D l ν (img h (base l) l x)‖ with hg
  have hf0 : ∀ x ν, 0 ≤ f x ν := fun x ν => norm_nonneg _
  have hg0 : ∀ x ν, 0 ≤ g x ν := fun x ν => norm_nonneg _
  set Lr : ℝ := ((2 * h + 1 : ℕ) : ℝ) with hLr
  have hL0 : 0 < Lr := by positivity
  set α := a₀ l + a₁ l
  have hα0 : 0 ≤ α := by positivity
  -- the bound at one bond of the level `l + 1`
  have hbond : ∀ x ρ, (if RB h nl μ (l + 1) x ρ then ‖E (l + 1) ρ (img h (base (l + 1)) (l + 1) x)‖ else 0) ≤
      (Lr ^ 4)⁻¹ * ∑ xp : Pts h, ∑ j ∈ Finset.range (2 * h + 1),
        (if RB h nl μ (l + 1) x ρ then f (x + Lz h ^ l • (offP h xp + (j : ℤ) • Pi.single ρ 1)) ρ else 0) +
      C * α * ∑ x' ∈ boxPts h nl l, ∑ ν : Fin 4,
        (if RB h nl μ (l + 1) x ρ ∧ RB h nl μ l x' ν ∧ Pbox h l x ρ x' ν then f x' ν else 0) +
      C * α * ∑ x' ∈ boxPts h nl l, ∑ ν : Fin 4,
        (if RB h nl μ (l + 1) x ρ ∧ RB h nl μ l x' ν ∧ Pbox h l x ρ x' ν then g x' ν else 0) := by
    intro x ρ
    by_cases hb : RB h nl μ (l + 1) x ρ
    · obtain ⟨hx, q0, q1⟩ := hb
      have hb' : RB h nl μ (l + 1) x ρ := ⟨hx, q0, q1⟩
      simp only [hb', if_true, true_and]
      set y := img h (base l) l x
      have hbox : ∀ ν z, (Bm y h z ∨ Bp y h ρ z) → (Bm y h (z + unit (nn l) ν) ∨ Bp y h ρ (z + unit (nn l) ν)) →
          V l ν z = moveC (U l) (A' l) ν z := fun ν z h1 h2 => by
        obtain ⟨x', hx', r0, r1, rfl⟩ := box_site (hn l) (base l) hx q0 q1 ⟨h1, h2⟩
        exact hVU l hl ν x' hx' r0 r1
      have hQ : Qlin (V l) y ρ h = Qlin (moveC (U l) (A' l)) y ρ h := by
        simp only [Qlin, relLog_fun_local (y := y) (μ := ρ) (h := h) hn2 hbox]
      obtain ⟨hpl, hA⟩ := hdat l hl ρ x hx q0 q1
      have hpE := hpert ρ (U l) (hU l) (hn l) y (a₀ l) (a₁ l) ha0 ha1 (ha0c.trans (hcle ρ)) (ha1c.trans (hcle ρ))
        hpl (A' l) hA (E l)
      have hpD := hpert ρ (U l) (hU l) (hn l) y (a₀ l) (a₁ l) ha0 ha1 (ha0c.trans (hcle ρ)) (ha1c.trans (hcle ρ))
        hpl (A' l) hA (D l)
      have hq := norm_Q0L_lines (h := h) (hU l) y ρ (E l)
      have hRE := restrict_le_sum_box (nl := nl) (μ := μ) (hn l) (base l) hx q0 q1 (E l)
      have hRD := restrict_le_sum_box (nl := nl) (μ := μ) (hn l) (base l) hx q0 q1 (D l)
      have hxl := lat_succ_le hx
      have hlines : ∑ xp : Pts h, ∑ j ∈ Finset.range (2 * h + 1),
          ‖E l ρ (ofs y (offP h xp) + j • unit (nn l) ρ)‖ =
          ∑ xp : Pts h, ∑ j ∈ Finset.range (2 * h + 1), f (x + Lz h ^ l • (offP h xp + (j : ℤ) • Pi.single ρ 1)) ρ := by
        refine Finset.sum_congr rfl fun xp _ => Finset.sum_congr rfl fun j _ => ?_
        simp only [hf, y, line_site (base l) hxl ρ xp j]
      rw [hE l hl ρ x hx q0 q1, hQ]
      have e : ((2 * h + 1 : ℕ) : ℂ) • Qlin (moveC (U l) (A' l)) y ρ h (E l) +
          (((2 * h + 1 : ℕ) : ℂ) • Qlin (moveC (U l) (A' l)) y ρ h (D l) - Q0L (U l) y ρ h (D l)) =
          Q0L (U l) y ρ h (E l) + (((2 * h + 1 : ℕ) : ℂ) • Qlin (moveC (U l) (A' l)) y ρ h (E l) -
            Q0L (U l) y ρ h (E l)) +
          (((2 * h + 1 : ℕ) : ℂ) • Qlin (moveC (U l) (A' l)) y ρ h (D l) - Q0L (U l) y ρ h (D l)) := by abel
      rw [e]
      have hCα : Cp ρ * α ≤ C * α := mul_le_mul_of_nonneg_right (hCle ρ) hα0
      refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add ?_ ?_)) ?_)
      · rw [← hlines]; exact hq
      · refine hpE.trans ?_
        calc Cp ρ * α * ‖restrictF (E l) (InBoxB y h ρ)‖ ≤ C * α * ‖restrictF (E l) (InBoxB y h ρ)‖ :=
              mul_le_mul_of_nonneg_right hCα (norm_nonneg _)
          _ ≤ C * α * _ := mul_le_mul_of_nonneg_left hRE (by positivity)
      · refine hpD.trans ?_
        calc Cp ρ * α * ‖restrictF (D l) (InBoxB y h ρ)‖ ≤ C * α * ‖restrictF (D l) (InBoxB y h ρ)‖ :=
              mul_le_mul_of_nonneg_right hCα (norm_nonneg _)
          _ ≤ C * α * _ := mul_le_mul_of_nonneg_left hRD (by positivity)
    · rw [if_neg hb]
      have h1 : 0 ≤ (Lr ^ 4)⁻¹ * ∑ xp : Pts h, ∑ j ∈ Finset.range (2 * h + 1),
          (if RB h nl μ (l + 1) x ρ then f (x + Lz h ^ l • (offP h xp + (j : ℤ) • Pi.single ρ 1)) ρ else 0) :=
        mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by
          split_ifs <;> first | exact hf0 _ _ | exact le_rfl)
      have h2 : 0 ≤ C * α * ∑ x' ∈ boxPts h nl l, ∑ ν : Fin 4,
          (if RB h nl μ (l + 1) x ρ ∧ RB h nl μ l x' ν ∧ Pbox h l x ρ x' ν then f x' ν else 0) :=
        mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by
          split_ifs <;> first | exact hf0 _ _ | exact le_rfl)
      have h3 : 0 ≤ C * α * ∑ x' ∈ boxPts h nl l, ∑ ν : Fin 4,
          (if RB h nl μ (l + 1) x ρ ∧ RB h nl μ l x' ν ∧ Pbox h l x ρ x' ν then g x' ν else 0) :=
        mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by
          split_ifs <;> first | exact hg0 _ _ | exact le_rfl)
      linarith
  -- sum over the bonds of the level `l + 1`
  have hlin := sum_lines_le h nl l μ hf0
  have hbxf := sum_box_le h nl l μ hf0
  have hbxg := sum_box_le h nl l μ hg0
  have hsum : ell1 h nl μ (l + 1) (fun x ν => ‖E (l + 1) ν (img h (base (l + 1)) (l + 1) x)‖) ≤
      (Lr ^ 4)⁻¹ * ∑ x ∈ boxPts h nl (l + 1), ∑ ρ : Fin 4, ∑ xp : Pts h, ∑ j ∈ Finset.range (2 * h + 1),
        (if RB h nl μ (l + 1) x ρ then f (x + Lz h ^ l • (offP h xp + (j : ℤ) • Pi.single ρ 1)) ρ else 0) +
      C * α * ∑ x ∈ boxPts h nl (l + 1), ∑ ρ : Fin 4, ∑ x' ∈ boxPts h nl l, ∑ ν : Fin 4,
        (if RB h nl μ (l + 1) x ρ ∧ RB h nl μ l x' ν ∧ Pbox h l x ρ x' ν then f x' ν else 0) +
      C * α * ∑ x ∈ boxPts h nl (l + 1), ∑ ρ : Fin 4, ∑ x' ∈ boxPts h nl l, ∑ ν : Fin 4,
        (if RB h nl μ (l + 1) x ρ ∧ RB h nl μ l x' ν ∧ Pbox h l x ρ x' ν then g x' ν else 0) := by
    simp only [ell1, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun ρ _ => by
      simpa only [Finset.mul_sum] using hbond x ρ
  refine hsum.trans ?_
  have hCα0 : 0 ≤ C * α := by positivity
  calc (Lr ^ 4)⁻¹ * _ + C * α * _ + C * α * _ ≤
        (Lr ^ 4)⁻¹ * (Lr * ell1 h nl μ l f) + C * α * (8 * ell1 h nl μ l f) + C * α * (8 * ell1 h nl μ l g) :=
        add_le_add (add_le_add (mul_le_mul_of_nonneg_left hlin (by positivity))
          (mul_le_mul_of_nonneg_left hbxf hCα0)) (mul_le_mul_of_nonneg_left hbxg hCα0)
    _ = _ := by field_simp


open Classical in
/-- **The difference of the composite linear parts** (`lem:average-kernels` for `Q_n(𝐔) - Q_n(U)` at a gauge field with
trivial plaquettes, by the recursion over the levels in place of the lemma of Schwarz): with `D_{l+1} = LQ(U_l)D_l`,
`E_{l+1} = LQ(V_l)E_l + (LQ(V_l) - LQ(U_l))D_l`, `E_0 = 0`, `V_l = e^{iA'_l}U_l` with `‖A'_l‖ ≤ a₁⁽ˡ⁾ ≤ c` on the boxes,
`‖E_n‖_{1,n} ≤ (e^{Σ_l 8L³Ca₁⁽ˡ⁾} - 1)L^{-3n}‖D_0‖_{1,0}`. -/
theorem average_kernels_diff (h : ℕ) :
    ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧ ∀ (nl : ℕ) (μ : Fin 4) (nn : ℕ → ℕ) [∀ l, NeZero (nn l)],
      (∀ l, 4 * h + 4 ≤ nn l) → ∀ (base : ∀ l, Site (nn l)) (U V : ∀ l, Config N (nn l))
      (A' E D : ∀ l, Fin 4 → Site (nn l) → Mat) (a₁ : ℕ → ℝ),
      (∀ l, U l |>.IsGaugeField) →
      (∀ l, l < nl → ∀ ν x, Lat (Lz h) l x → Rg h nl μ l x → Rg h nl μ l (x + Lz h ^ l • Pi.single ν 1) →
        V l ν (img h (base l) l x) = moveC (U l) (A' l) ν (img h (base l) l x)) →
      (∀ l, l < nl → ∀ ρ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x →
        Rg h nl μ (l + 1) (x + Lz h ^ (l + 1) • Pi.single ρ 1) →
        (∀ μ' ν' z, PlaqIn (boxR (img h (base l) l x) (loD h) (hiD h ρ ρ)) μ' ν' z →
          hs (((plaq (U l) μ' ν' z : GLN) : Mat) - 1) ≤ 0) ∧
        (∀ ν z, BoxBond (img h (base l) l x) h ρ ν z → ‖A' l ν z‖ ≤ a₁ l)) →
      (∀ l, l < nl → 0 ≤ a₁ l ∧ a₁ l ≤ c) →
      (∀ l, l < nl → ∀ ρ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x →
        Rg h nl μ (l + 1) (x + Lz h ^ (l + 1) • Pi.single ρ 1) →
        D (l + 1) ρ (img h (base (l + 1)) (l + 1) x) =
          ((2 * h + 1 : ℕ) : ℂ) • Qlin (U l) (img h (base l) l x) ρ h (D l)) →
      (∀ l, l < nl → ∀ ρ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x →
        Rg h nl μ (l + 1) (x + Lz h ^ (l + 1) • Pi.single ρ 1) →
        E (l + 1) ρ (img h (base (l + 1)) (l + 1) x) =
          ((2 * h + 1 : ℕ) : ℂ) • Qlin (V l) (img h (base l) l x) ρ h (E l) +
            (((2 * h + 1 : ℕ) : ℂ) • Qlin (V l) (img h (base l) l x) ρ h (D l) -
              ((2 * h + 1 : ℕ) : ℂ) • Qlin (U l) (img h (base l) l x) ρ h (D l))) →
      ell1 h nl μ 0 (fun x ν => ‖E 0 ν (img h (base 0) 0 x)‖) = 0 →
      ell1 h nl μ nl (fun x ν => ‖E nl ν (img h (base nl) nl x)‖) ≤
        (Real.exp (∑ l ∈ Finset.range nl, 8 * (((2 * h + 1 : ℕ) : ℝ)) ^ 3 * C * a₁ l) - 1) *
          (((((2 * h + 1 : ℕ) : ℝ) ^ 3)⁻¹) ^ nl * ell1 h nl μ 0 (fun x ν => ‖D 0 ν (img h (base 0) 0 x)‖)) := by
  obtain ⟨c1, C1, hc1, hC1, hstep⟩ := kernel_step_diff (N := N) h
  obtain ⟨c2, C2, hc2, hC2, hks⟩ := kernel_step (N := N) h
  choose cp Cp hcp hCp hpert using fun ρ : Fin 4 => pert_bound (N := N) h ρ
  refine ⟨c1, C1, hc1, hC1, ?_⟩
  intro nl μ nn _ hn base U V A' E D a₁ hU hVU hdat ha hD hE hE0
  set Lr : ℝ := ((2 * h + 1 : ℕ) : ℝ) with hLr
  have hL0 : 0 < Lr := by positivity
  set q : ℝ := (Lr ^ 3)⁻¹ with hq
  have hq0 : 0 < q := by positivity
  -- `LQ(U_l) = Q₀(U_l)` on the boxes (trivial plaquettes)
  have hQ0 : ∀ l, l < nl → ∀ ρ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x →
      Rg h nl μ (l + 1) (x + Lz h ^ (l + 1) • Pi.single ρ 1) → ∀ B : Fin 4 → Site (nn l) → Mat,
      ((2 * h + 1 : ℕ) : ℂ) • Qlin (U l) (img h (base l) l x) ρ h B = Q0L (U l) (img h (base l) l x) ρ h B := by
    intro l hl ρ x hx q0 q1 B
    have hp := hpert ρ (U l) (hU l) (hn l) (img h (base l) l x) 0 0 le_rfl le_rfl (hcp ρ).le (hcp ρ).le
      (hdat l hl ρ x hx q0 q1).1 0 (fun _ _ _ => by simp) B
    rw [moveC_zero] at hp
    simp only [add_zero, mul_zero, zero_mul] at hp
    exact sub_eq_zero.1 (norm_le_zero_iff.1 hp)
  -- the chain of `U` contracts by `L^{-3}`
  have hDs := hks nl μ nn hn base U U (fun _ => 0) D (fun _ => 0) (fun _ => 0) hU
    (fun l _ ν x _ _ _ => by rw [moveC_zero]) (fun l hl ρ x hx q0 q1 => ⟨(hdat l hl ρ x hx q0 q1).1,
      fun _ _ _ => by simp⟩) (fun _ _ => ⟨le_rfl, le_rfl, hc2.le, hc2.le⟩) hD
  set d : ℕ → ℝ := fun l => ell1 h nl μ l (fun x ν => ‖D l ν (img h (base l) l x)‖)
  have hd : ∀ l, l ≤ nl → d l ≤ q ^ l * d 0 := by
    intro l
    induction l with
    | zero => intro _; simp
    | succ l ih =>
      intro hl
      have h1 := hDs l (by omega)
      simp only [add_zero, mul_zero] at h1
      have h2 := ih (by omega)
      calc d (l + 1) ≤ q * d l := h1
        _ ≤ q * (q ^ l * d 0) := mul_le_mul_of_nonneg_left h2 hq0.le
        _ = q ^ (l + 1) * d 0 := by ring
  -- the recursion of the differences
  have hrec := hstep nl μ nn hn base U V A' E D (fun _ => 0) a₁ hU hVU hdat
    (fun l hl => ⟨le_rfl, (ha l hl).1, hc1.le, (ha l hl).2⟩)
    (fun l hl ρ x hx q0 q1 => by rw [hE l hl ρ x hx q0 q1, hQ0 l hl ρ x hx q0 q1])
  set xs : ℕ → ℝ := fun l => ell1 h nl μ l (fun x ν => ‖E l ν (img h (base l) l x)‖)
  set β : ℕ → ℝ := fun l => 8 * Lr ^ 3 * C1 * a₁ l
  have hd0 : 0 ≤ d 0 := ell1_nonneg fun _ _ => norm_nonneg _
  have hβ0 : ∀ l, 0 ≤ (if l < nl then β l else 0) := fun l => by
    split_ifs with hl
    · exact mul_nonneg (by positivity) (ha l hl).1
    · exact le_rfl
  have hacc := accum_le hq0.le hd0 xs (fun l => if l < nl then β l else 0) hβ0 hE0 nl
    (fun l hl => by
      rw [if_pos hl]
      have h1 := hrec l hl
      simp only [zero_add] at h1
      have hdl := hd l hl.le
      have hβq : 8 * C1 * a₁ l = q * β l := by simp only [β, hq]; field_simp
      have hc : 0 ≤ 8 * C1 * a₁ l := mul_nonneg (by positivity) (ha l hl).1
      calc xs (l + 1) ≤ (q + 8 * C1 * a₁ l) * xs l + 8 * C1 * a₁ l * d l := h1
        _ ≤ (q + 8 * C1 * a₁ l) * xs l + 8 * C1 * a₁ l * (q ^ l * d 0) := by gcongr
        _ = q * (1 + β l) * xs l + q * β l * (q ^ l * d 0) := by rw [hβq]; ring) nl le_rfl
  have hsum : ∑ i ∈ Finset.range nl, (if i < nl then β i else 0) = ∑ i ∈ Finset.range nl, β i :=
    Finset.sum_congr rfl fun i hi => by rw [if_pos (Finset.mem_range.1 hi)]
  rw [hsum] at hacc
  exact hacc

end RelativeAverage
end CoreLean

end
