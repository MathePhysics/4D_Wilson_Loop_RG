/-
`prop:relative-average-order`(i) of BALABAN_CORE.tex (`fe7d249fe3af`), the locality: the averages `M^l`, the forms
`A^{(l)}`, and the gauge transformations `𝐠_l` (hence `v_n`) of the levels depend only on the data on `𝖡_c`.

* `levels_local`: for two families `(V, B, 𝐠)` and `(V', B', 𝐠')` with the recursions `V_{l+1} = M(V_l)`,
  `B_{l+1} = (1/i) log 𝓜_{V_l}(B_l)`, and `𝐠_{l+1} = 𝐠_l v_{V_l}(B_l)` on the regions, if the data of the level `0`
  agree on the region of the level `0` (the bonds of `𝖡_c` and the sites of `Bⁿ(c₋) ∪ Bⁿ(c₊)`), then the data of every
  level `l ≤ n` agree on the region of the level `l`.
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

/-- The centre of a block. -/
def ctr (h : ℕ) : Pts h := fun _ => ⟨h, by omega⟩

lemma offP_ctr (h : ℕ) : offP h (ctr h) = 0 := by funext σ; simp [offP, ctr]

/-- **The locality of the levels** (`prop:relative-average-order`(i)): the averages, the forms, and the gauge
transformations of the levels depend only on the data of the level `0` on its region. -/
theorem levels_local (h nl : ℕ) (μ : Fin 4) (nn : ℕ → ℕ) [∀ l, NeZero (nn l)] (hn : ∀ l, 4 * h + 4 ≤ nn l)
    (base : ∀ l, Site (nn l)) (V V' : ∀ l, Config N (nn l)) (B B' : ∀ l, Fin 4 → Site (nn l) → Mat)
    (g g' : ∀ l, Site (nn l) → GLN)
    (hrel : ∀ l, l < nl → ∀ ρ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x →
      Rg h nl μ (l + 1) (x + Lz h ^ (l + 1) • Pi.single ρ 1) →
      V (l + 1) ρ (img h (base (l + 1)) (l + 1) x) = avgM (V l) (img h (base l) l x) ρ h ∧
      V' (l + 1) ρ (img h (base (l + 1)) (l + 1) x) = avgM (V' l) (img h (base l) l x) ρ h ∧
      B (l + 1) ρ (img h (base (l + 1)) (l + 1) x) = relLog (V l) (B l) (img h (base l) l x) ρ h ∧
      B' (l + 1) ρ (img h (base (l + 1)) (l + 1) x) = relLog (V' l) (B' l) (img h (base l) l x) ρ h)
    (hg : ∀ l, l < nl → ∀ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x →
      g (l + 1) (img h (base (l + 1)) (l + 1) x) = g l (img h (base l) l x) * siteFactor (V l) (B l) (img h (base l) l x) h ∧
      g' (l + 1) (img h (base (l + 1)) (l + 1) x) =
        g' l (img h (base l) l x) * siteFactor (V' l) (B' l) (img h (base l) l x) h)
    (h0 : ∀ ρ x, Lat (Lz h) 0 x → Rg h nl μ 0 x → Rg h nl μ 0 (x + Lz h ^ 0 • Pi.single ρ 1) →
      V 0 ρ (img h (base 0) 0 x) = V' 0 ρ (img h (base 0) 0 x) ∧
      B 0 ρ (img h (base 0) 0 x) = B' 0 ρ (img h (base 0) 0 x))
    (hg0 : ∀ x, Lat (Lz h) 0 x → Rg h nl μ 0 x → g 0 (img h (base 0) 0 x) = g' 0 (img h (base 0) 0 x)) :
    ∀ l, l ≤ nl →
      (∀ ρ x, Lat (Lz h) l x → Rg h nl μ l x → Rg h nl μ l (x + Lz h ^ l • Pi.single ρ 1) →
        V l ρ (img h (base l) l x) = V' l ρ (img h (base l) l x) ∧
        B l ρ (img h (base l) l x) = B' l ρ (img h (base l) l x)) ∧
      (∀ x, Lat (Lz h) l x → Rg h nl μ l x → g l (img h (base l) l x) = g' l (img h (base l) l x)) := by
  intro l
  induction l with
  | zero => intro _; exact ⟨h0, hg0⟩
  | succ l ih =>
    intro hl
    have hll : l < nl := by omega
    have hn2 : 4 * h + 2 ≤ nn l := by have := hn l; omega
    obtain ⟨ihb, ihs⟩ := ih hll.le
    -- the data of the level `l` agree on the bonds of the box of a bond of the level `l + 1`
    have hbox : ∀ ρ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x →
        Rg h nl μ (l + 1) (x + Lz h ^ (l + 1) • Pi.single ρ 1) → ∀ ν z, BoxBond (img h (base l) l x) h ρ ν z →
        V l ν z = V' l ν z ∧ B l ν z = B' l ν z := fun ρ x hx q0 q1 ν z hb => by
      obtain ⟨x'', hx'', r0, r1, rfl⟩ := box_site (hn l) (base l) hx q0 q1 hb
      exact ihb ν x'' hx'' r0 r1
    refine ⟨fun ρ x hx q0 q1 => ?_, fun x hx hR => ?_⟩
    · obtain ⟨hV, hV', hB, hB'⟩ := hrel l hll ρ x hx q0 q1
      rw [hV, hV', hB, hB']
      refine ⟨avgM_local hn2 fun ν z h1 h2 => (hbox ρ x hx q0 q1 ν z ⟨h1, h2⟩).1, ?_⟩
      simp only [relLog]
      rw [relAvg_local hn2 fun ν z h1 h2 => hbox ρ x hx q0 q1 ν z ⟨h1, h2⟩]
    · obtain ⟨hgl, hgl'⟩ := hg l hll x hx hR
      rw [hgl, hgl']
      have hRl : Rg h nl μ l x := by
        have := rg_site hR (ctr h)
        rwa [offP_ctr, smul_zero, add_zero] at this
      have hs : siteFactor (V l) (B l) (img h (base l) l x) h = siteFactor (V' l) (B' l) (img h (base l) l x) h := by
        obtain ⟨x', b, hx', r0, r1, hb⟩ := rg_end_img (base l) hl hx hR
        rw [hb]
        exact siteFactor_local hn2 fun ν z hz hz' => hbox μ x' hx' r0 r1 ν z (boxBond_of_end hn2 b hz hz')
      rw [ihs x (lat_succ_le hx) hRl, hs]

end RelativeAverage
end CoreLean

end
