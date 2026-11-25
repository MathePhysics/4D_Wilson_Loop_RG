/-
`lem:block-average-transports` of BALABAN_CORE.tex, the transports at a trivial background, in the per-level framework:
when the configurations of the levels are `e^{iA'_l}` (the background `U_l = id`) with `‖A'_l‖ ≤ a_l`,
`a_l ≤ eL^{-(n-l)}`, the composite transports `W(y, x)` of `Q'_l` satisfy `‖Ad_{W(y,x)}Z - Z‖ ≤ (e^{Ce/2} - 1)‖Z‖`
(the input `|Ad_W Z - Z| ≤ η|Z|` of the fine model, `ScalarHyp.hW1`).

* `block_transports_close`: by induction over the levels as in `block_transports_bound`, with the transports of the
  trivial configuration equal to `1` (`trans_oneC`) and `1 + ε ≤ e^ε`.
-/
import CoreLean.RelativeAverageKernels
import CoreLean.LevelsBridge

open Matrix NormedSpace Filter Topology Metric
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace CoreLean
namespace RelativeAverage

open LatticePaths LatticeKappa RegularAverages BlockPaths AverageHolo MeanTransports AxialReference BoxGeometry AxialStraightLattice

variable {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "GLN" => (Matrix (Fin N) (Fin N) ℂ)ˣ

/-- **The composite transports at a trivial background are close to `1`**: under the data of the levels with
`U_l = id`, `‖Ad_{W(y,x)}Z - Z‖ ≤ (e^{Ce/2} - 1)‖Z‖`. -/
theorem block_transports_close (h : ℕ) :
    ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧ ∀ (nl : ℕ) (μ : Fin 4) (nn : ℕ → ℕ) [∀ l, NeZero (nn l)],
      (∀ l, 4 * h + 4 ≤ nn l) → ∀ (base : ∀ l, Site (nn l)) (V : ∀ l, Config N (nn l))
      (A' : ∀ l, Fin 4 → Site (nn l) → Mat) (a₁ : ℕ → ℝ) (e : ℝ),
      (∀ l, l < nl → ∀ ν x, Lat (Lz h) l x → Rg h nl μ l x → Rg h nl μ l (x + Lz h ^ l • Pi.single ν 1) →
        V l ν (img h (base l) l x) = moveC oneC (A' l) ν (img h (base l) l x)) →
      (∀ l, l < nl → ∀ ρ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x →
        Rg h nl μ (l + 1) (x + Lz h ^ (l + 1) • Pi.single ρ 1) →
        ∀ ν z, BoxBond (img h (base l) l x) h ρ ν z → ‖A' l ν z‖ ≤ a₁ l) →
      (∀ l, l < nl → 0 ≤ a₁ l ∧ a₁ l ≤ e * ((((2 * h + 1 : ℕ) : ℝ)) ^ (nl - l))⁻¹) →
      0 ≤ e → e ≤ c → 3 ≤ (((2 * h + 1 : ℕ) : ℝ)) →
      ∀ l, l ≤ nl → ∀ y, Lat (Lz h) l y → Rg h nl μ l y → ∀ (p : Fin l → Pts h) (Z : Mat),
        ‖Ad (WB h nn base V l y p) Z - Z‖ ≤ (Real.exp (C * e / 2) - 1) * ‖Z‖ := by
  classical
  choose cn Cn hcn hCn hni using fun ρ : Fin 4 => trans_near_iso (N := N) h ρ
  set c := Finset.univ.inf' Finset.univ_nonempty cn
  set C := Finset.univ.sup' Finset.univ_nonempty Cn
  have hcn' : ∀ ρ, c ≤ cn ρ := fun ρ => Finset.inf'_le _ (Finset.mem_univ ρ)
  have hCn' : ∀ ρ, Cn ρ ≤ C := fun ρ => Finset.le_sup' _ (Finset.mem_univ ρ)
  have hc0 : 0 < c := (Finset.lt_inf'_iff _).2 fun ρ _ => hcn ρ
  have hC0 : 0 ≤ C := (hCn 0).trans (hCn' 0)
  refine ⟨c, C, hc0, hC0, ?_⟩
  intro nl μ nn _ hn base V A' a₁ e hVU hdat ha he hec hL3
  set Lr : ℝ := ((2 * h + 1 : ℕ) : ℝ) with hLr
  have hp1 : ∀ m, (Lr ^ m)⁻¹ ≤ 1 := fun m => inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith))
  set ε : ℕ → ℝ := fun l => if l < nl then C * a₁ l else 0 with hε
  have hε0 : ∀ l, 0 ≤ ε l := fun l => by
    simp only [hε]; split_ifs with hl
    · exact mul_nonneg hC0 (ha l hl).1
    · exact le_rfl
  have hεsum : ∑ m ∈ Finset.range nl, ε m ≤ C * e / 2 := by
    have hg := geom_partial hL3 nl nl le_rfl
    simp only [Nat.sub_self, pow_zero, _root_.inv_one, mul_one] at hg
    calc ∑ m ∈ Finset.range nl, ε m ≤ ∑ m ∈ Finset.range nl, C * e * (Lr ^ (nl - m))⁻¹ :=
          Finset.sum_le_sum fun m hm => by
            have hm' := Finset.mem_range.1 hm
            simp only [hε, if_pos hm']
            have := (ha m hm').2
            nlinarith [mul_le_mul_of_nonneg_left this hC0]
      _ = C * e * ∑ m ∈ Finset.range nl, (Lr ^ (nl - m))⁻¹ := by rw [Finset.mul_sum]
      _ ≤ C * e * (1 / 2) := mul_le_mul_of_nonneg_left hg (by positivity)
      _ = _ := by ring
  -- the invariant: `‖Ad_W Z - Z‖ ≤ (exp(Σ_{m<l}ε_m) - 1)‖Z‖`
  have hinv : ∀ l, l ≤ nl → ∀ y, Lat (Lz h) l y → Rg h nl μ l y → ∀ (p : Fin l → Pts h) (Z : Mat),
      ‖Ad (WB h nn base V l y p) Z - Z‖ ≤ (Real.exp (∑ m ∈ Finset.range l, ε m) - 1) * ‖Z‖ := by
    intro l
    induction l with
    | zero => intro _ y _ _ p Z; simp [WB, Ad]
    | succ l ih =>
      intro hl y hy hR p Z
      have hll : l < nl := by omega
      have hn2 : 4 * h + 2 ≤ nn l := by have := hn l; omega
      obtain ⟨ha1, ha1e⟩ := ha l hll
      have ha1c : a₁ l ≤ e := by have := hp1 (nl - l); nlinarith
      obtain ⟨x', b, hx', r0, r1, hb⟩ := rg_end_img (base l) hl hy hR
      have hA := hdat l hll μ x' hx' r0 r1
      set z₀ := ofs (img h (base l) l x') (endW h μ b)
      have ht : ∀ xx, trans (V l) z₀ h xx = trans (moveC oneC (A' l)) z₀ h xx :=
        trans_local hn2 fun ν z h1 h2 => by
          obtain ⟨x'', hx'', s0, s1, rfl⟩ := box_site (hn l) (base l) hx' r0 r1 (boxBond_of_end hn2 b h1 h2)
          exact hVU l hll ν x'' hx'' s0 s1
      have hεl : ε l = C * a₁ l := by simp only [hε, if_pos hll]
      have hclose : ∀ W : Mat, ‖Ad (trans (moveC oneC (A' l)) z₀ h (p 0)) W - W‖ ≤ ε l * ‖W‖ := fun W => by
        have h0 := hni μ (oneC : Config N (nn l)) LevelsBridge.oneC_gauge (hn l) (img h (base l) l x') 0 (a₁ l)
          le_rfl ha1 (hcn μ).le ((ha1c.trans hec).trans (hcn' μ))
          (fun μ' ν' z _ => by simp [LevelsBridge.plaq_oneC, RegularAverages.hs_zero'])
          (A' l) hA b (p 0) W
        rw [trans_oneC, BlockAverageTransports.Ad_one] at h0
        refine h0.trans ?_
        rw [hεl]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hCn' μ) ha1) (norm_nonneg _)
      have hih := ih hll.le (y + Lz h ^ l • offP h (p 0)) (lat_add_smul (lat_succ_le hy) _) (rg_site hR (p 0))
        (Fin.tail p)
      have hWdef : WB h nn base V (l + 1) y p =
          trans (moveC oneC (A' l)) z₀ h (p 0) * WB h nn base V l (y + Lz h ^ l • offP h (p 0)) (Fin.tail p) := by
        simp only [WB, hb, ht]
      set W' := WB h nn base V l (y + Lz h ^ l • offP h (p 0)) (Fin.tail p)
      set T := trans (moveC oneC (A' l)) z₀ h (p 0)
      set s := ∑ m ∈ Finset.range l, ε m
      have hs0 : 0 ≤ s := Finset.sum_nonneg fun m _ => hε0 m
      have hd0 : 0 ≤ Real.exp s - 1 := by linarith [Real.add_one_le_exp s]
      have hW'Z : ‖Ad W' Z‖ ≤ Real.exp s * ‖Z‖ := by
        have := norm_add_le (Ad W' Z - Z) Z
        rw [sub_add_cancel] at this
        have := hih Z
        nlinarith [norm_nonneg Z]
      rw [hWdef, Ad_mul, Finset.sum_range_succ]
      have e1 : Ad T (Ad W' Z) - Z = (Ad T (Ad W' Z) - Ad W' Z) + (Ad W' Z - Z) := by abel
      rw [e1]
      have hεle := Real.add_one_le_exp (ε l)
      calc ‖(Ad T (Ad W' Z) - Ad W' Z) + (Ad W' Z - Z)‖
          ≤ ‖Ad T (Ad W' Z) - Ad W' Z‖ + ‖Ad W' Z - Z‖ := norm_add_le _ _
        _ ≤ ε l * (Real.exp s * ‖Z‖) + (Real.exp s - 1) * ‖Z‖ :=
            add_le_add ((hclose _).trans (mul_le_mul_of_nonneg_left hW'Z (hε0 l))) (hih Z)
        _ = ((1 + ε l) * Real.exp s - 1) * ‖Z‖ := by ring
        _ ≤ (Real.exp (ε l) * Real.exp s - 1) * ‖Z‖ := by
            gcongr
            linarith
        _ = (Real.exp (s + ε l) - 1) * ‖Z‖ := by rw [Real.exp_add]; ring
  intro l hl y hy hR p Z
  refine (hinv l hl y hy hR p Z).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
  have hs : ∑ m ∈ Finset.range l, ε m ≤ ∑ m ∈ Finset.range nl, ε m :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hl) fun m _ _ => hε0 m
  have := Real.exp_le_exp.2 (hs.trans hεsum)
  linarith

end RelativeAverage
end CoreLean

end
