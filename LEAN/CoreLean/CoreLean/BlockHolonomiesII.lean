/-
`lem:block-holonomies`(ii) of BALABAN_CORE.tex (`7374c382ba1b`): the counts of the moves across plaquettes.

* `RedTo U α m γ δ`: `γ` is moved to `δ` by `m` moves across plaquettes with `|U(∂p) - id| ≤ α` and free cancellations of
  backtracks; `redTo_trans`, `redTo_context`, `reduces_of_redTo` (with `Reduces` of `BlockHolonomies.lean`).
* `square_bdry`: the unit square spanned by a bond `b` at `z` and a rung `r = (z, z ± e_ρ)` is a plaquette read from its
  corner `z`; `ladder`: the rung is moved along a path of `k` bonds by `k` moves, `[r_z] γ' ↦ γ [r_{z'}]` for the
  translate `γ'` of `γ`.
-/
import CoreLean.BlockHolonomies
import CoreLean.BlockPaths

open Matrix NormedSpace
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace CoreLean
namespace BlockHolonomies

open AverageHolo RegularAverages LatticePaths

variable {N : ℕ} {n : ℕ} [NeZero n]

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "GLN" => (Matrix (Fin N) (Fin N) ℂ)ˣ

/-- `RedTo U α m γ δ`: `γ` is moved to `δ` by `m` moves across plaquettes `p` with `|U(∂p) - id| ≤ α`, a move replacing
`γ₁σγ₂` by `γ₁σ'γ₂` with `σσ'⁻¹ = ∂p` read from a corner, and by cancellations of backtracks `bb⁻¹`. -/
inductive RedTo (U : Config N n) (α : ℝ) : ℕ → List (Bond n) → List (Bond n) → Prop
  | refl (γ : List (Bond n)) : RedTo U α 0 γ γ
  | cancel {m : ℕ} (γ₁ γ₂ δ : List (Bond n)) (b : Bond n) :
      RedTo U α m (γ₁ ++ γ₂) δ → RedTo U α m (γ₁ ++ [b, b.rev] ++ γ₂) δ
  | move {m : ℕ} (γ₁ σ σ' γ₂ δ : List (Bond n)) (μ ν : Fin 4) (x : Site n)
      (hp : IsPlaqBdry (σ ++ rv σ') μ ν x) (hα : hs (((plaq U μ ν x : GLN) : Mat) - 1) ≤ α) :
      RedTo U α m (γ₁ ++ σ' ++ γ₂) δ → RedTo U α (m + 1) (γ₁ ++ σ ++ γ₂) δ

variable {U : Config N n} {α : ℝ}

theorem reduces_of_redTo {m : ℕ} {γ δ : List (Bond n)} (h : RedTo U α m γ δ) :
    ∀ {m' : ℕ}, Reduces U α m' δ → Reduces U α (m + m') γ := by
  induction h with
  | refl γ => intro m' hd; simpa using hd
  | cancel γ₁ γ₂ δ b _ ih => intro m' hd; exact Reduces.cancel γ₁ γ₂ b (ih hd)
  | move γ₁ σ σ' γ₂ δ μ ν x hp hα _ ih =>
    intro m' hd
    have := Reduces.move γ₁ σ σ' γ₂ μ ν x hp hα (ih hd)
    rwa [Nat.add_right_comm] at this

theorem redTo_trans {m m' : ℕ} {γ δ ε : List (Bond n)} (h : RedTo U α m γ δ) (h' : RedTo U α m' δ ε) :
    RedTo U α (m + m') γ ε := by
  induction h with
  | refl γ => simpa using h'
  | cancel γ₁ γ₂ δ b _ ih => exact RedTo.cancel γ₁ γ₂ ε b (ih h')
  | move γ₁ σ σ' γ₂ δ μ ν x hp hα _ ih =>
    have := RedTo.move γ₁ σ σ' γ₂ ε μ ν x hp hα (ih h')
    rwa [Nat.add_right_comm] at this

theorem redTo_context {m : ℕ} {γ δ : List (Bond n)} (h : RedTo U α m γ δ) (p q : List (Bond n)) :
    RedTo U α m (p ++ γ ++ q) (p ++ δ ++ q) := by
  induction h with
  | refl γ => exact RedTo.refl _
  | cancel γ₁ γ₂ δ b _ ih =>
    have := RedTo.cancel (p ++ γ₁) (γ₂ ++ q) (p ++ δ ++ q) b (by simpa [List.append_assoc] using ih)
    simpa [List.append_assoc] using this
  | move γ₁ σ σ' γ₂ δ μ ν x hp hα _ ih =>
    have := RedTo.move (p ++ γ₁) σ σ' (γ₂ ++ q) (p ++ δ ++ q) μ ν x hp hα (by simpa [List.append_assoc] using ih)
    simpa [List.append_assoc] using this

/-- A path followed by its reverse cancels to the trivial path. -/
theorem redTo_cancel_rv : ∀ γ : List (Bond n), RedTo U α 0 (γ ++ rv γ) []
  | [] => by simpa [rv] using RedTo.refl (U := U) (α := α) []
  | b :: γ => by
    have ih := redTo_cancel_rv γ
    have e : b :: γ ++ rv (b :: γ) = [b] ++ (γ ++ rv γ) ++ [b.rev] := by simp [rv]
    rw [e]
    have h1 := redTo_context ih [b] [b.rev]
    have h2 : RedTo U α 0 ([] ++ [b, b.rev] ++ []) [] := RedTo.cancel [] [] [] b (RedTo.refl _)
    simpa using redTo_trans h1 h2

/-- The four corners of the unit square spanned by a bond `b` at `z` and the step `d = ±e_ρ`. -/
def SqIn (R : Set (Site n)) (b : Bond n) (d : Site n) : Prop :=
  b.site ∈ R ∧ b.plus ∈ R ∧ b.site + d ∈ R ∧ b.plus + d ∈ R

/-- **The unit square**: for a bond `b` at `z` and a rung `r = (z, ρ, s)`, `[r, b'] [b, r']⁻¹`, with the translate `b'` of `b`
by `d = ±e_ρ` and the rung `r'` at `b₊`, is a plaquette read from its corner `z`, whose corners are those of the square. -/
theorem square_bdry (b : Bond n) (ρ : Fin 4) (s : Bool) :
    ∃ μ' ν' x', IsPlaqBdry ([⟨b.site, ρ, s⟩, b.shift (dvec ρ s)] ++ rv [b, ⟨b.plus, ρ, s⟩]) μ' ν' x' ∧
      ∀ R : Set (Site n), SqIn R b (dvec ρ s) → PlaqIn R μ' ν' x' := by
  obtain ⟨z, μ, p⟩ := b
  cases p <;> cases s
  · -- backwards bond, backwards rung: `p_{ρμ}(z - e_μ - e_ρ)` rotated by two
    refine ⟨ρ, μ, z - unit n μ - unit n ρ, ⟨2, Or.inl ?_⟩, fun R hR => ?_⟩
    · simp only [rv, plaqPath, Bond.shift, Bond.rev, Bond.plus, dvec, Bool.false_eq_true, ↓reduceIte,
        List.map_cons, List.map_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
        List.singleton_append, Bool.not_false]
      simp only [List.rotate, List.length_cons, List.length_nil]
      norm_num
      all_goals (repeat' apply And.intro)
      all_goals first | rfl | abel
    · obtain ⟨h1, h2, h3, h4⟩ := hR
      simp only [Bond.plus, dvec, Bool.false_eq_true, ↓reduceIte] at h1 h2 h3 h4
      refine ⟨mem_of_eq h4 (by abel), mem_of_eq h2 (by abel), mem_of_eq h3 (by abel), mem_of_eq h1 (by abel)⟩
  · -- backwards bond, forwards rung: `p_{μρ}(z - e_μ)` rotated by one
    refine ⟨μ, ρ, z - unit n μ, ⟨1, Or.inl ?_⟩, fun R hR => ?_⟩
    · simp only [rv, plaqPath, Bond.shift, Bond.rev, Bond.plus, dvec, Bool.false_eq_true, ↓reduceIte,
        List.map_cons, List.map_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
        List.singleton_append, Bool.not_false, Bool.not_true]
      simp only [List.rotate, List.length_cons, List.length_nil]
      norm_num
      all_goals (repeat' apply And.intro)
      all_goals first | rfl | abel
    · obtain ⟨h1, h2, h3, h4⟩ := hR
      simp only [Bond.plus, dvec, Bool.false_eq_true, ↓reduceIte] at h1 h2 h3 h4
      refine ⟨mem_of_eq h2 (by abel), mem_of_eq h1 (by abel), mem_of_eq h4 (by abel), mem_of_eq h3 (by abel)⟩
  · -- forwards bond, backwards rung: `p_{μρ}(z - e_ρ)` rotated by three
    refine ⟨μ, ρ, z - unit n ρ, ⟨3, Or.inl ?_⟩, fun R hR => ?_⟩
    · simp only [rv, plaqPath, Bond.shift, Bond.rev, Bond.plus, dvec, Bool.false_eq_true, ↓reduceIte,
        List.map_cons, List.map_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
        List.singleton_append, Bool.not_false, Bool.not_true]
      simp only [List.rotate, List.length_cons, List.length_nil]
      norm_num
      all_goals (repeat' apply And.intro)
      all_goals first | rfl | abel
    · obtain ⟨h1, h2, h3, h4⟩ := hR
      simp only [Bond.plus, dvec, Bool.false_eq_true, ↓reduceIte] at h1 h2 h3 h4
      refine ⟨mem_of_eq h3 (by abel), mem_of_eq h4 (by abel), mem_of_eq h1 (by abel), mem_of_eq h2 (by abel)⟩
  · -- forwards bond, forwards rung: `p_{ρμ}(z)`
    refine ⟨ρ, μ, z, ⟨0, Or.inl ?_⟩, fun R hR => ?_⟩
    · simp only [rv, plaqPath, Bond.shift, Bond.rev, Bond.plus, dvec, ↓reduceIte,
        List.map_cons, List.map_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
        List.singleton_append, Bool.not_true, List.rotate_zero]
      all_goals (repeat' apply And.intro)
      all_goals first | rfl | abel
    · obtain ⟨h1, h2, h3, h4⟩ := hR
      simp only [Bond.plus, dvec, ↓reduceIte] at h1 h2 h3 h4
      refine ⟨mem_of_eq h1 (by abel), mem_of_eq h3 (by abel), mem_of_eq h2 (by abel), mem_of_eq h4 (by abel)⟩

/-- The plaquettes with corners in `R` are at most `α` in the Hilbert–Schmidt norm. -/
def PlaqBoundHS (U : Config N n) (R : Set (Site n)) (α : ℝ) : Prop :=
  ∀ μ ν x, PlaqIn R μ ν x → hs (((plaq U μ ν x : GLN) : Mat) - 1) ≤ α

/-- **The ladder**: a rung `r_z = (z, ρ, s)` is moved along a path `γ` from `z` of `k` bonds, whose unit squares with the
step `d = ±e_ρ` have their corners in `R`, by `k` moves across plaquettes with corners in `R`:
`[r_z] γ' ↦ γ [r_{z'}]`, `γ'` the translate of `γ` by `d` and `z'` the end of `γ`. -/
theorem ladder_moves {R : Set (Site n)} (hP : PlaqBoundHS U R α) (ρ : Fin 4) (s : Bool) :
    ∀ (γ : List (Bond n)) (z : Site n), Chain z γ → LadderIn R (dvec ρ s) γ →
      RedTo U α γ.length ([⟨z, ρ, s⟩] ++ γ.map (Bond.shift · (dvec ρ s))) (γ ++ [⟨endpt z γ, ρ, s⟩])
  | [], z, _, _ => by simpa [endpt] using RedTo.refl (U := U) (α := α) [(⟨z, ρ, s⟩ : Bond n)]
  | b :: γ, z, ⟨hbz, hch⟩, hL => by
    subst hbz
    obtain ⟨μ', ν', x', hp, hcorn⟩ := square_bdry b ρ s
    have hb := hL b (List.mem_cons_self)
    have hα : hs (((plaq U μ' ν' x' : GLN) : Mat) - 1) ≤ α := hP μ' ν' x' (hcorn R hb)
    have ih := ladder_moves hP ρ s γ b.plus hch (fun t ht => hL t (List.mem_cons_of_mem _ ht))
    have hc := redTo_context ih [b] []
    have hm := RedTo.move [] [⟨b.site, ρ, s⟩, b.shift (dvec ρ s)] [b, ⟨b.plus, ρ, s⟩]
      (γ.map (Bond.shift · (dvec ρ s))) ([b] ++ (γ ++ [⟨endpt b.plus γ, ρ, s⟩]) ++ []) μ' ν' x' hp hα
      (by simpa using hc)
    simpa [endpt] using hm

/-! ### Reversal -/

lemma bond_rev_rev (b : Bond n) : b.rev.rev = b := by
  cases b with | mk x μ s => cases s <;> simp [Bond.rev, Bond.plus]

lemma rv_rv (γ : List (Bond n)) : rv (rv γ) = γ := by
  simp [rv, List.map_reverse, List.map_map, Function.comp_def, bond_rev_rev]

lemma rv_append (γ δ : List (Bond n)) : rv (γ ++ δ) = rv δ ++ rv γ := by
  simp [rv]

lemma rv_rotate (l : List (Bond n)) (k : ℕ) : rv (l.rotate k) = (rv l).rotate (l.length - k % l.length) := by
  simp only [rv, List.map_rotate]
  rw [List.reverse_rotate, List.length_map]

/-- A rotation of the reversal of `∂p` is the reversal of a rotation. -/
lemma rv_plaq_rotate (μ ν : Fin 4) (x : Site n) (m : ℕ) :
    ∃ k, (rv (plaqPath μ ν x)).rotate m = rv ((plaqPath μ ν x).rotate k) := by
  refine ⟨4 - m % 4, ?_⟩
  rw [rv_rotate]
  have hl : (plaqPath μ ν x).length = 4 := rfl
  rw [hl, ← List.rotate_mod, ← List.rotate_mod (rv (plaqPath μ ν x)) (4 - (4 - m % 4) % 4)]
  have hl' : (rv (plaqPath μ ν x)).length = 4 := by simp [rv, hl]
  rw [hl']
  congr 1
  omega

lemma isPlaqBdry_rotate {P : List (Bond n)} {μ ν : Fin 4} {x : Site n} (hP : IsPlaqBdry P μ ν x) (j : ℕ) :
    IsPlaqBdry (P.rotate j) μ ν x := by
  obtain ⟨k, rfl | rfl⟩ := hP
  · exact ⟨k + j, Or.inl (List.rotate_rotate _ _ _)⟩
  · rw [rv_rotate, List.rotate_rotate]
    obtain ⟨k'', hk''⟩ := rv_plaq_rotate μ ν x
      ((plaqPath μ ν x).length - k % (plaqPath μ ν x).length + j)
    exact ⟨k'', Or.inr hk''⟩

lemma isPlaqBdry_rv {P : List (Bond n)} {μ ν : Fin 4} {x : Site n} (hP : IsPlaqBdry P μ ν x) :
    IsPlaqBdry (rv P) μ ν x := by
  obtain ⟨k, rfl | rfl⟩ := hP
  · exact ⟨k, Or.inr rfl⟩
  · exact ⟨k, Or.inl (rv_rv _)⟩

/-- **Reversal**: the reversed paths are moved by the reversed moves. -/
theorem redTo_rv {m : ℕ} {γ δ : List (Bond n)} (h : RedTo U α m γ δ) : RedTo U α m (rv γ) (rv δ) := by
  induction h with
  | refl γ => exact RedTo.refl _
  | cancel γ₁ γ₂ δ b _ ih =>
    have e1 : rv (γ₁ ++ [b, b.rev] ++ γ₂) = rv γ₂ ++ [b, b.rev] ++ rv γ₁ := by
      simp [rv, bond_rev_rev]
    have e2 : rv (γ₁ ++ γ₂) = rv γ₂ ++ rv γ₁ := rv_append _ _
    rw [e1]
    exact RedTo.cancel (rv γ₂) (rv γ₁) (rv δ) b (by rw [← e2]; exact ih)
  | move γ₁ σ σ' γ₂ δ μ ν x hp hα _ ih =>
    have e1 : rv (γ₁ ++ σ ++ γ₂) = rv γ₂ ++ rv σ ++ rv γ₁ := by simp [rv_append, List.append_assoc]
    have e2 : rv (γ₁ ++ σ' ++ γ₂) = rv γ₂ ++ rv σ' ++ rv γ₁ := by simp [rv_append, List.append_assoc]
    have hp' : IsPlaqBdry (rv σ ++ rv (rv σ')) μ ν x := by
      rw [rv_rv]
      have h1 := isPlaqBdry_rv hp
      rw [rv_append, rv_rv] at h1
      have h2 := isPlaqBdry_rotate h1 σ'.length
      rwa [List.rotate_append_length_eq] at h2
    rw [e1]
    exact RedTo.move (rv γ₂) (rv σ) (rv σ') (rv γ₁) (rv δ) μ ν x hp' hα (by rw [← e2]; exact ih)

/-! ### Rectangles -/

/-- **The rectangle**: the two boundary paths of an `a × b` rectangle, spanned by `a` steps `e = ±e_μ` and `b` steps
`d = ±e_ν` from `w`, whose grid points lie in `R`, are related by `ab` moves: the rung `(w, w + d)` is moved along the side
of `a` bonds by `a` moves (`ladder_moves`), and the remaining `a × (b - 1)` rectangle by induction. -/
theorem rectangle_moves {R : Set (Site n)} (hP : PlaqBoundHS U R α) (μ ν : Fin 4) (sa sb : Bool) (a : ℕ) :
    ∀ (b : ℕ) (w : Site n), (∀ i j, i ≤ a → j ≤ b → w + i • dvec μ sa + j • dvec ν sb ∈ R) →
      RedTo U α (a * b) (seg ν sb w b ++ seg μ sa (w + b • dvec ν sb) a)
        (seg μ sa w a ++ seg ν sb (w + a • dvec μ sa) b)
  | 0, w, _ => by simpa [seg] using RedTo.refl (U := U) (α := α) (seg μ sa w a)
  | b + 1, w, hR => by
    have ih := rectangle_moves hP μ ν sa sb a b (w + dvec ν sb) fun i j hi hj => by
      have := hR i (j + 1) hi (by omega)
      refine mem_of_eq this ?_
      rw [succ_nsmul]; abel
    have hL : LadderIn R (dvec ν sb) (seg μ sa w a) := fun t ht => by
      obtain ⟨i, hi, hs, hp⟩ := mem_seg_iff ht
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hs]; simpa using hR i 0 hi.le (by omega)
      · rw [hp]; simpa using hR (i + 1) 0 hi (by omega)
      · rw [hs]; simpa using hR i 1 hi.le (by omega)
      · rw [hp]; simpa using hR (i + 1) 1 hi (by omega)
    have hlad := ladder_moves hP ν sb (seg μ sa w a) w (chain_seg μ sa a w) hL
    rw [length_seg, map_shift_seg, endpt_seg] at hlad
    have hc1 := redTo_context ih [⟨w, ν, sb⟩] []
    have hc2 := redTo_context hlad [] (seg ν sb (w + dvec ν sb + a • dvec μ sa) b)
    simp only [List.append_assoc, List.nil_append, List.append_nil, List.singleton_append,
      List.cons_append] at hc1 hc2
    have htot := redTo_trans hc1 hc2
    have e1 : w + (b + 1) • dvec ν sb = w + dvec ν sb + b • dvec ν sb := by rw [succ_nsmul]; abel
    have e2 : w + dvec ν sb + a • dvec μ sa = w + a • dvec μ sa + dvec ν sb := by abel
    rw [show a * (b + 1) = a * b + a by ring]
    simp only [seg, e1, List.cons_append, List.append_assoc, List.singleton_append]
    rw [← e2]
    exact htot

/-! ### Staircase paths -/

/-- **The exchange of two consecutive coordinates**: `stair(… ν μ …) ↦ stair(… μ ν …)` by `|m_μ||m_ν|` moves across the
plaquettes of the rectangle they span, whose grid points lie in `R`. -/
theorem stair_swap_moves {R : Set (Site n)} (hP : PlaqBoundHS U R α) (y : Site n) (m : Fin 4 → ℤ) (μ ν : Fin 4)
    (S : List (Fin 4)) (o : Fin 4 → ℤ)
    (hR : ∀ i j : ℕ, i ≤ (m μ).natAbs → j ≤ (m ν).natAbs →
      ofs y o + i • dvec μ (sgn (m μ)) + j • dvec ν (sgn (m ν)) ∈ R) :
    RedTo U α ((m μ).natAbs * (m ν).natAbs) (stair y m (ν :: μ :: S) o) (stair y m (μ :: ν :: S) o) := by
  have hrect := rectangle_moves hP μ ν (sgn (m μ)) (sgn (m ν)) (m μ).natAbs (m ν).natAbs (ofs y o) hR
  have hc := redTo_context hrect [] (stair y m S (o + Pi.single μ (m μ) + Pi.single ν (m ν)))
  simp only [List.nil_append] at hc
  have e1 : stair y m (ν :: μ :: S) o =
      seg ν (sgn (m ν)) (ofs y o) (m ν).natAbs ++
        seg μ (sgn (m μ)) (ofs y o + (m ν).natAbs • dvec ν (sgn (m ν))) (m μ).natAbs ++
        stair y m S (o + Pi.single μ (m μ) + Pi.single ν (m ν)) := by
    simp only [stair, segZ_eq, List.append_assoc]
    rw [ofs_add_single, ← natAbs_smul_dvec, add_right_comm o]
  have e2 : stair y m (μ :: ν :: S) o =
      seg μ (sgn (m μ)) (ofs y o) (m μ).natAbs ++
        seg ν (sgn (m ν)) (ofs y o + (m μ).natAbs • dvec μ (sgn (m μ))) (m ν).natAbs ++
        stair y m S (o + Pi.single μ (m μ) + Pi.single ν (m ν)) := by
    simp only [stair, segZ_eq, List.append_assoc]
    rw [ofs_add_single, ← natAbs_smul_dvec]
  rw [e1, e2]
  exact hc

/-! ### Orderings of the coordinates -/

/-- `RedLe U α M γ δ`: `γ` is moved to `δ` by at most `M` moves. -/
def RedLe (U : Config N n) (α : ℝ) (M : ℕ) (γ δ : List (Bond n)) : Prop := ∃ m ≤ M, RedTo U α m γ δ

lemma redLe_trans {M M' : ℕ} {γ δ ε : List (Bond n)} (h : RedLe U α M γ δ) (h' : RedLe U α M' δ ε) :
    RedLe U α (M + M') γ ε := by
  obtain ⟨m, hm, hr⟩ := h; obtain ⟨m', hm', hr'⟩ := h'
  exact ⟨m + m', by omega, redTo_trans hr hr'⟩

lemma redLe_mono {M M' : ℕ} {γ δ : List (Bond n)} (h : RedLe U α M γ δ) (hM : M ≤ M') : RedLe U α M' γ δ := by
  obtain ⟨m, hm, hr⟩ := h; exact ⟨m, by omega, hr⟩

/-- The points of the block `B(y)`: `y + v`, `|v_σ| ≤ h`. -/
def RegB (y : Site n) (h : ℕ) : Set (Site n) := {z | ∃ v, AxialReference.InM h v ∧ z = ofs y v}

/-- The grid of the rectangle of two coordinates `μ ≠ ν` at an offset whose coordinates are `0` or `m_σ`, and `0` in `μ`
and `ν`, lies in the block, for `|m_σ| ≤ h`. -/
lemma grid_mem (y : Site n) {h : ℕ} {m o : Fin 4 → ℤ} {μ ν : Fin 4} (hμν : μ ≠ ν) (hm : ∀ σ, (m σ).natAbs ≤ h)
    (ho : ∀ σ, o σ = 0 ∨ o σ = m σ) (hoμ : o μ = 0) (hoν : o ν = 0) :
    ∀ i j : ℕ, i ≤ (m μ).natAbs → j ≤ (m ν).natAbs →
      ofs y o + i • dvec μ (sgn (m μ)) + j • dvec ν (sgn (m ν)) ∈ RegB y h := by
  intro i j hi hj
  refine ⟨o + Pi.single μ (zi (sgn (m μ)) i) + Pi.single ν (zi (sgn (m ν)) j), fun σ => ?_, ?_⟩
  · have b1 := btw_zi hi
    have b2 := btw_zi hj
    unfold LatticePaths.Btw at b1 b2
    have h1 := hm μ
    have h2 := hm ν
    have h3 := hm σ
    simp only [Pi.add_apply, Pi.single_apply]
    by_cases hσμ : σ = μ
    · subst hσμ
      simp only [if_true, if_neg hμν, hoμ]
      constructor <;> omega
    · by_cases hσν : σ = ν
      · subst hσν
        simp only [if_neg hσμ, if_true, hoν]
        constructor <;> omega
      · simp only [if_neg hσμ, if_neg hσν]
        rcases ho σ with h0 | h0 <;> rw [h0] <;> constructor <;> omega
  · rw [ofs_add_single, ofs_add_single, nsmul_dvec, nsmul_dvec]

/-- The exchange of two consecutive coordinates after a prefix `Q`. -/
lemma stair_swap_at {R : Set (Site n)} (hP : PlaqBoundHS U R α) (y : Site n) (m : Fin 4 → ℤ) (μ ν : Fin 4)
    (Q S : List (Fin 4)) (o : Fin 4 → ℤ)
    (hR : ∀ i j : ℕ, i ≤ (m μ).natAbs → j ≤ (m ν).natAbs →
      ofs y (o + offs m Q) + i • dvec μ (sgn (m μ)) + j • dvec ν (sgn (m ν)) ∈ R) :
    RedTo U α ((m μ).natAbs * (m ν).natAbs) (stair y m (Q ++ ν :: μ :: S) o) (stair y m (Q ++ μ :: ν :: S) o) := by
  rw [stair_append, stair_append]
  have := redTo_context (stair_swap_moves hP y m μ ν S (o + offs m Q) hR) (stair y m Q o) []
  simpa only [List.append_nil] using this

/-- The number of the adjacent exchanges of the bubble sort: `0, 0, 1, 3, 6, …`. -/
def bub : ℕ → ℕ
  | 0 => 0
  | k + 1 => k + bub k

set_option maxHeartbeats 4000000 in
/-- **Moving a coordinate to the front**: `stair(Q A a B) ↦ stair(Q a A B)` by at most `|A|h²` moves in the block. -/
theorem stair_move_front (y : Site n) {h : ℕ} (hP : PlaqBoundHS U (RegB y h) α) (m : Fin 4 → ℤ)
    (hm : ∀ σ, (m σ).natAbs ≤ h) (a : Fin 4) (B : List (Fin 4)) :
    ∀ (A Q : List (Fin 4)) (o : Fin 4 → ℤ), (Q ++ A ++ a :: B).Nodup → (∀ σ, o σ = 0 ∨ o σ = m σ) →
      (∀ σ ∈ Q ++ A ++ a :: B, o σ = 0) →
      RedLe U α (A.length * h ^ 2) (stair y m (Q ++ A ++ a :: B) o) (stair y m (Q ++ a :: (A ++ B)) o)
  | [], Q, o, _, _, _ => ⟨0, by simp, by simpa using RedTo.refl (U := U) (α := α) (stair y m (Q ++ a :: B) o)⟩
  | c :: A, Q, o, hnd, ho, ho0 => by
    have ih := stair_move_front y hP m hm a B A (Q ++ [c]) o (by simpa using hnd) ho (by simpa using ho0)
    -- the exchange of `c` and `a` after `Q`
    have hnd' : (Q ++ c :: a :: (A ++ B)).Nodup := by
      have hp : (Q ++ (c :: (A ++ a :: B))).Perm (Q ++ (c :: a :: (A ++ B))) :=
        List.Perm.append_left Q (List.perm_middle.cons c)
      have hnd2 : (Q ++ (c :: (A ++ a :: B))).Nodup := by simpa [List.append_assoc] using hnd
      exact hp.nodup_iff.1 hnd2
    have hca : c ≠ a := by
      intro hca; subst hca
      have := (List.nodup_append.1 hnd').2.1
      simp at this
    have hcQ : c ∉ Q := fun hc => by
      have := List.disjoint_of_nodup_append hnd' hc
      simp at this
    have haQ : a ∉ Q := fun ha => by
      have := List.disjoint_of_nodup_append hnd' ha
      simp at this
    have hQnd : Q.Nodup := (List.nodup_append.1 hnd').1
    have hoff : ∀ σ, (o + offs m Q) σ = 0 ∨ (o + offs m Q) σ = m σ := fun σ => by
      simp only [Pi.add_apply, offs_nodup m Q hQnd σ]
      by_cases hσ : σ ∈ Q
      · rw [if_pos hσ, ho0 σ (by simp [hσ])]; right; ring
      · rw [if_neg hσ, add_zero]; exact ho σ
    have hoa : (o + offs m Q) a = 0 := by
      simp only [Pi.add_apply, offs_nodup m Q hQnd a, if_neg haQ, add_zero]
      exact ho0 a (by simp)
    have hoc : (o + offs m Q) c = 0 := by
      simp only [Pi.add_apply, offs_nodup m Q hQnd c, if_neg hcQ, add_zero]
      exact ho0 c (by simp)
    have hsw := stair_swap_at hP y m a c Q (A ++ B) o (grid_mem y (Ne.symm hca) hm hoff hoa hoc)
    have hsw' : RedLe U α (h ^ 2) (stair y m (Q ++ [c] ++ a :: (A ++ B)) o) (stair y m (Q ++ a :: (c :: A ++ B)) o) := by
      refine ⟨_, ?_, by simpa [List.append_assoc] using hsw⟩
      have := hm a; have := hm c
      calc (m a).natAbs * (m c).natAbs ≤ h * h := Nat.mul_le_mul (hm a) (hm c)
        _ = h ^ 2 := (sq h).symm
    have ih' : RedLe U α (A.length * h ^ 2) (stair y m (Q ++ c :: A ++ a :: B) o)
        (stair y m (Q ++ [c] ++ a :: (A ++ B)) o) := by simpa [List.append_assoc] using ih
    have := redLe_trans ih' hsw'
    refine redLe_mono (by simpa [List.append_assoc] using this) ?_
    simp only [List.length_cons]; ring_nf; omega

set_option maxHeartbeats 4000000 in
/-- **Any two orderings**: `stair(Q l₁) ↦ stair(Q l₂)` for a permutation `l₂` of `l₁` by at most `bub(|l₁|)h²` moves in
the block (bubble sort: move the first coordinate of `l₂` to the front, and recurse). -/
theorem stair_perm (y : Site n) {h : ℕ} (hP : PlaqBoundHS U (RegB y h) α) (m : Fin 4 → ℤ)
    (hm : ∀ σ, (m σ).natAbs ≤ h) :
    ∀ (l₂ l₁ Q : List (Fin 4)) (o : Fin 4 → ℤ), l₁.Perm l₂ → (Q ++ l₁).Nodup → (∀ σ, o σ = 0 ∨ o σ = m σ) →
      (∀ σ ∈ Q ++ l₁, o σ = 0) →
      RedLe U α (bub l₁.length * h ^ 2) (stair y m (Q ++ l₁) o) (stair y m (Q ++ l₂) o)
  | [], l₁, Q, o, hp, _, _, _ => by
    rw [List.perm_nil.1 hp]
    exact ⟨0, by simp, RedTo.refl _⟩
  | a :: l₂, l₁, Q, o, hp, hnd, ho, ho0 => by
    have ha : a ∈ l₁ := hp.symm.subset (List.mem_cons_self)
    obtain ⟨A, B, rfl⟩ := List.append_of_mem ha
    have h1 := stair_move_front y hP m hm a B A Q o (by simpa [List.append_assoc] using hnd) ho
      (by simpa [List.append_assoc] using ho0)
    have hp' : (A ++ B).Perm l₂ := (List.perm_middle.symm.trans hp).cons_inv
    have hnd' : (Q ++ [a] ++ (A ++ B)).Nodup := by
      have : (Q ++ (A ++ a :: B)).Perm (Q ++ [a] ++ (A ++ B)) := by
        simpa [List.append_assoc] using List.Perm.append_left Q (List.perm_middle (l₁ := A) (l₂ := B) (a := a))
      exact this.nodup_iff.1 hnd
    have h2 := stair_perm y hP m hm l₂ (A ++ B) (Q ++ [a]) o hp' hnd' ho (fun σ hσ => ho0 σ (by
      simp only [List.mem_append, List.mem_cons, List.mem_singleton] at hσ ⊢; tauto))
    have h1' : RedLe U α (A.length * h ^ 2) (stair y m (Q ++ (A ++ a :: B)) o) (stair y m (Q ++ [a] ++ (A ++ B)) o) := by
      simpa [List.append_assoc] using h1
    have h2' : RedLe U α (bub (A ++ B).length * h ^ 2) (stair y m (Q ++ [a] ++ (A ++ B)) o)
        (stair y m (Q ++ a :: l₂) o) := by simpa [List.append_assoc] using h2
    refine redLe_mono (redLe_trans h1' h2') ?_
    have hlen : (A ++ a :: B).length = (A ++ B).length + 1 := by simp; omega
    rw [hlen, bub, List.length_append]
    have : A.length ≤ A.length + B.length := Nat.le_add_right _ _
    nlinarith [Nat.zero_le (h ^ 2)]

/-- **`lem:block-holonomies`(ii), the first assertion**: for two paths `Γ, Γ' ∈ 𝐆(y, x)`, `Γ` is moved to `Γ'` by at most
`6h² ≤ 3L²/2` moves across plaquettes with corners in `B(y)`, and `ΓΓ'⁻¹` is reduced to the trivial path by as many. -/
theorem block_holonomies_ii_paths (y : Site n) {h : ℕ} (hP : PlaqBoundHS U (RegB y h) α) (x : BlockPaths.Pts h)
    (Γ Γ' : BlockPaths.Ords (BlockPaths.offP h x)) :
    RedLe U α (6 * h ^ 2) (stair y (BlockPaths.offP h x) (BlockPaths.ordG h x Γ) 0)
        (stair y (BlockPaths.offP h x) (BlockPaths.ordG h x Γ') 0) ∧
      (∃ m ≤ 6 * h ^ 2, Reduces U α m (stair y (BlockPaths.offP h x) (BlockPaths.ordG h x Γ) 0 ++
        rv (stair y (BlockPaths.offP h x) (BlockPaths.ordG h x Γ') 0))) ∧
      4 * (6 * h ^ 2) ≤ 6 * (2 * h + 1) ^ 2 := by
  have hm : ∀ σ, (BlockPaths.offP h x σ).natAbs ≤ h := fun σ => by
    have := BlockPaths.offP_inM h x σ; omega
  have hp1 := BlockPaths.ordG_perm h x Γ
  have hp2 := BlockPaths.ordG_perm h x Γ'
  have hnd : ([] ++ BlockPaths.ordG h x Γ).Nodup := by simpa using hp1.nodup_iff.2 (by decide)
  have hlen : (BlockPaths.ordG h x Γ).length = 4 := by simpa using hp1.length_eq
  have h1 := stair_perm y hP (BlockPaths.offP h x) hm (BlockPaths.ordG h x Γ') (BlockPaths.ordG h x Γ) [] 0
    (hp1.trans hp2.symm) hnd (fun σ => Or.inl rfl) (fun σ _ => rfl)
  rw [hlen] at h1
  simp only [List.nil_append] at h1
  have h6 : bub 4 = 6 := rfl
  rw [h6] at h1
  have harith : 4 * (6 * h ^ 2) ≤ 6 * (2 * h + 1) ^ 2 := by
    have e : 6 * (2 * h + 1) ^ 2 = 4 * (6 * h ^ 2) + (24 * h + 6) := by ring
    rw [e]; exact Nat.le_add_right _ _
  refine ⟨h1, ?_, harith⟩
  obtain ⟨m, hm6, hr⟩ := h1
  have hc := redTo_context hr [] (rv (stair y (BlockPaths.offP h x) (BlockPaths.ordG h x Γ') 0))
  simp only [List.nil_append] at hc
  have hz := reduces_of_redTo (redTo_trans hc (redTo_cancel_rv _)) (m' := 0) Reduces.nil
  exact ⟨m + 0, by omega, by simpa using hz⟩

/-! ### Strips -/

set_option maxHeartbeats 4000000 in
/-- **The strip**: a path `γ` from `z` and its translate by `k` steps `d = ±e_κ` bound a strip of `k|γ|` unit squares,
and `[z, z + kd] γ'' ↦ γ [z', z' + kd]` by `k|γ|` moves (`k` ladders), when the corners of the squares lie in `R`. -/
theorem strip_moves {R : Set (Site n)} (hP : PlaqBoundHS U R α) (κ : Fin 4) (s : Bool) :
    ∀ (k : ℕ) (γ : List (Bond n)) (z : Site n), Chain z γ →
      (∀ t ∈ γ, ∀ j : ℕ, j ≤ k → t.site + j • dvec κ s ∈ R ∧ t.plus + j • dvec κ s ∈ R) →
      RedTo U α (k * γ.length) (seg κ s z k ++ γ.map (Bond.shift · (k • dvec κ s)))
        (γ ++ seg κ s (endpt z γ) k)
  | 0, γ, z, _, _ => by simpa [seg, map_shift_zero] using RedTo.refl (U := U) (α := α) γ
  | k + 1, γ, z, hch, hR => by
    set d := dvec (n := n) κ s
    have ih := strip_moves hP κ s k (γ.map (Bond.shift · d)) (z + d) (chain_shift d γ z hch) (fun t' ht' j hj => by
      obtain ⟨t, ht, rfl⟩ := List.mem_map.1 ht'
      obtain ⟨h1, h2⟩ := hR t ht (j + 1) (by omega)
      refine ⟨mem_of_eq h1 ?_, mem_of_eq h2 ?_⟩
      · simp only [Bond.shift, succ_nsmul]; abel
      · rw [Bond.shift_plus, succ_nsmul]; abel)
    have hL : LadderIn R d γ := fun t ht => by
      obtain ⟨h1, h2⟩ := hR t ht 0 (by omega)
      obtain ⟨h3, h4⟩ := hR t ht 1 (by omega)
      simp only [zero_smul, add_zero, one_smul] at h1 h2 h3 h4
      exact ⟨h1, h2, h3, h4⟩
    have hlad := ladder_moves hP κ s γ z hch hL
    have hc1 := redTo_context ih [⟨z, κ, s⟩] []
    have hc2 := redTo_context hlad [] (seg κ s (endpt z γ + d) k)
    rw [map_shift_shift, endpt_shift, List.length_map] at hc1
    simp only [List.append_assoc, List.nil_append, List.append_nil, List.singleton_append,
      List.cons_append] at hc1 hc2
    have htot := redTo_trans hc1 hc2
    rw [show (k + 1) * γ.length = k * γ.length + γ.length by ring]
    have e1 : (k + 1) • d = d + k • d := by rw [succ_nsmul]; abel
    simp only [seg, e1, List.cons_append, List.append_assoc, List.singleton_append]
    exact htot

/-! ### The loops of a bond -/

lemma stair_add_base (y v : Site n) (m : Fin 4 → ℤ) : ∀ (l : List (Fin 4)) (o : Fin 4 → ℤ),
    stair (y + v) m l o = (stair y m l o).map (Bond.shift · v)
  | [], _ => rfl
  | μ :: l, o => by
    simp only [stair, List.map_append]
    rw [stair_add_base y v m l, map_shift_segZ]
    congr 2
    unfold ofs; funext σ; simp only [Pi.add_apply]; abel

lemma length_stair_le {h : ℕ} (w : Site n) {c : Fin 4 → ℤ} (hc : AxialReference.InM h c) {l : List (Fin 4)}
    (hl : l.Perm [0, 1, 2, 3]) : (stair w c l 0).length ≤ 4 * h := by
  rw [length_stair, (hl.map _).sum_eq]
  have h0 := hc 0; have h1 := hc 1; have h2 := hc 2; have h3 := hc 3
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  omega

set_option maxHeartbeats 8000000 in
/-- **`lem:block-holonomies`(ii), the second assertion**: for a bond `c = (y, y + Le_κ)`, `L = 2h + 1`, every loop
`ℓ_c(x, Γ, Γ')` has at most `6L` bonds and is reduced to the trivial path by at most `4L²` moves across plaquettes with
corners in `B(c₋) ∪ B(c₊)`: `Γ'` is moved to the translate of `Γ` by at most `6h²` moves in `B(c₊)`
(`block_holonomies_ii_paths`), the loop which remains bounds the strip swept by `Γ` (`strip_moves`, at most `L` moves for
each of the at most `4h` bonds of `Γ`), and the rest cancels. -/
theorem block_holonomies_ii_loops (y : Site n) {h : ℕ} (κ : Fin 4)
    (hP : PlaqBoundHS U (RegB y h ∪ RegB (ofs y (Pi.single κ ((2 * h + 1 : ℕ) : ℤ))) h) α) (x : BlockPaths.Pts h)
    (Γ Γ' : BlockPaths.Ords (BlockPaths.offP h x)) :
    (∃ m ≤ 4 * (2 * h + 1) ^ 2, Reduces U α m (AverageHolo.lpath (ι := BlockPaths.Pts h)
        (P := fun x => BlockPaths.Ords (BlockPaths.offP h x)) y κ (2 * h + 1) (BlockPaths.offP h) (BlockPaths.ordG h)
        x Γ Γ')) ∧
      (AverageHolo.lpath (ι := BlockPaths.Pts h) (P := fun x => BlockPaths.Ords (BlockPaths.offP h x)) y κ (2 * h + 1)
        (BlockPaths.offP h) (BlockPaths.ordG h) x Γ Γ').length ≤ 6 * (2 * h + 1) := by
  set L := 2 * h + 1 with hL
  set cp := ofs y (Pi.single κ (L : ℤ)) with hcp
  set G := stair y (BlockPaths.offP h x) (BlockPaths.ordG h x Γ) 0 with hG
  set G'' := stair cp (BlockPaths.offP h x) (BlockPaths.ordG h x Γ') 0 with hG''
  set Gc := stair cp (BlockPaths.offP h x) (BlockPaths.ordG h x Γ) 0 with hGc
  have hcp' : cp = y + L • dvec (n := n) κ true := by
    rw [hcp, show (Pi.single κ (L : ℤ) : Fin 4 → ℤ) = 0 + Pi.single κ (L : ℤ) by simp, ofs_add_single, ofs_zero]
    simp [dvec]
  have hGcG : Gc = G.map (Bond.shift · (L • dvec κ true)) := by
    rw [hGc, hG, hcp', stair_add_base]
  have hperm := BlockPaths.ordG_perm h x Γ
  have hinM := BlockPaths.offP_inM h x
  -- the end point and the chain of `Γ`
  obtain ⟨hch0, hend0⟩ := chain_endpt_stair y (BlockPaths.offP h x) (BlockPaths.ordG h x Γ) 0
  rw [ofs_zero] at hch0
  rw [ofs_zero, zero_add, offs_perm _ hperm] at hend0
  -- the straight paths
  have hSx : segZ κ (ofs y (BlockPaths.offP h x)) (L : ℤ) = seg κ true (endpt y G) L := by
    rw [segZ_eq, hend0]; simp [sgn]
  have hS0 : segZ κ y (L : ℤ) = seg κ true y L := by rw [segZ_eq]; simp [sgn]
  have hloop : AverageHolo.lpath (ι := BlockPaths.Pts h) (P := fun x => BlockPaths.Ords (BlockPaths.offP h x)) y κ L
      (BlockPaths.offP h) (BlockPaths.ordG h) x Γ Γ' = G ++ seg κ true (endpt y G) L ++ rv G'' ++ rv (seg κ true y L) := by
    simp only [AverageHolo.lpath]
    rw [← hSx, ← hS0]
  -- the plaquettes of the two blocks
  have hPp : PlaqBoundHS U (RegB cp h) α := fun μ ν z hz => hP μ ν z (by
    obtain ⟨h1, h2, h3, h4⟩ := hz
    exact ⟨Or.inr h1, Or.inr h2, Or.inr h3, Or.inr h4⟩)
  -- step A: `Γ'` to the translate of `Γ`
  obtain ⟨mA, hmA, hA⟩ := (block_holonomies_ii_paths cp hPp x Γ' Γ).1
  have hA' := redTo_context (redTo_rv hA) (G ++ seg κ true (endpt y G) L) (rv (seg κ true y L))
  -- step B: the strip
  have hcorner : ∀ t ∈ G, ∀ j : ℕ, j ≤ L →
      t.site + j • dvec κ true ∈ RegB y h ∪ RegB cp h ∧ t.plus + j • dvec κ true ∈ RegB y h ∪ RegB cp h := by
    intro t ht j hj
    obtain ⟨v, v', hv, hv', hs, hp⟩ := stair_ends y y 0 (BlockPaths.offP h x) (ofs_zero y).symm hinM
      (BlockPaths.ordG h x Γ) (hperm.nodup_iff.2 (by decide)) t ht
    rw [zero_add] at hs hp
    have key : ∀ w : Fin 4 → ℤ, AxialReference.InM h w → ofs y w + j • dvec κ true ∈ RegB y h ∪ RegB cp h := by
      intro w hw
      have e : ofs y w + j • dvec κ true = ofs y (w + Pi.single κ (j : ℤ)) := by
        rw [ofs_add_single]; simp [dvec]
      rw [e]
      by_cases hk : w κ + j ≤ h
      · left
        refine ⟨w + Pi.single κ (j : ℤ), fun σ => ?_, rfl⟩
        have := hw σ
        simp only [Pi.add_apply, Pi.single_apply]
        split_ifs with hσ
        · subst hσ; constructor <;> omega
        · simpa using this
      · right
        refine ⟨w + Pi.single κ ((j : ℤ) - L), fun σ => ?_, ?_⟩
        · have := hw σ
          simp only [Pi.add_apply, Pi.single_apply]
          split_ifs with hσ
          · subst hσ; constructor <;> omega
          · simpa using this
        · rw [hcp, ofs_ofs]
          congr 1
          funext σ
          simp only [Pi.add_apply, Pi.single_apply]
          split_ifs <;> ring
    exact ⟨hs ▸ key v hv, hp ▸ key v' hv'⟩
  have hstrip := strip_moves hP κ true L G y hch0 hcorner
  rw [← hGcG] at hstrip
  have hB := redTo_context (redTo_rv hstrip) (G ++ seg κ true (endpt y G) L) []
  rw [rv_append, rv_append] at hB
  -- step C: cancellation
  have hC := redTo_cancel_rv (U := U) (α := α) (G ++ seg κ true (endpt y G) L)
  rw [rv_append] at hC
  -- assembly
  have hAB : RedTo U α (mA + L * G.length) (G ++ seg κ true (endpt y G) L ++ rv G'' ++ rv (seg κ true y L))
      (G ++ seg κ true (endpt y G) L ++ (rv (seg κ true (endpt y G) L) ++ rv G)) := by
    refine redTo_trans hA' ?_
    simpa only [List.append_assoc, List.append_nil] using hB
  have hABC := redTo_trans hAB (by simpa only [List.append_assoc] using hC)
  have hred := reduces_of_redTo hABC (m' := 0) Reduces.nil
  have hGlen : G.length ≤ 4 * h := length_stair_le y hinM hperm
  refine ⟨⟨mA + L * G.length + 0, ?_, (by rw [hloop]; simpa using hred)⟩, ?_⟩
  · have h1 : L * G.length ≤ L * (4 * h) := Nat.mul_le_mul_left L hGlen
    have e : 4 * L ^ 2 = 6 * h ^ 2 + L * (4 * h) + (2 * h ^ 2 + 12 * h + 4) := by rw [hL]; ring
    omega
  · exact AverageHolo.length_lpath y κ (BlockPaths.offP h) (BlockPaths.ordG h) (fun x => BlockPaths.offP_inM h x)
      (fun x Γ => BlockPaths.ordG_perm h x Γ) x Γ Γ'

/-- **The loops of a bond are close to `id`** (`lem:block-holonomies`(i) and (ii) together, the step of
`lem:average-domain`(i)): for a gauge field whose plaquettes with corners in `B(c₋) ∪ B(c₊)` are at most `α`,
`|U(ℓ) - id| ≤ 4L²α` and `‖U(ℓ) - id‖ ≤ √N·4L²α` for every loop `ℓ` of `c`. -/
theorem loop_close (hU : U.IsGaugeField) (hα : 0 ≤ α) (y : Site n) {h : ℕ} (κ : Fin 4)
    (hP : PlaqBoundHS U (RegB y h ∪ RegB (ofs y (Pi.single κ ((2 * h + 1 : ℕ) : ℤ))) h) α) (x : BlockPaths.Pts h)
    (Γ Γ' : BlockPaths.Ords (BlockPaths.offP h x)) :
    hs (((U.hol (AverageHolo.lpath (ι := BlockPaths.Pts h) (P := fun x => BlockPaths.Ords (BlockPaths.offP h x)) y κ
        (2 * h + 1) (BlockPaths.offP h) (BlockPaths.ordG h) x Γ Γ') : GLN) : Mat) - 1) ≤ 4 * (2 * h + 1) ^ 2 * α ∧
    ‖((U.hol (AverageHolo.lpath (ι := BlockPaths.Pts h) (P := fun x => BlockPaths.Ords (BlockPaths.offP h x)) y κ
        (2 * h + 1) (BlockPaths.offP h) (BlockPaths.ordG h) x Γ Γ') : GLN) : Mat) - 1‖ ≤
      Real.sqrt N * (4 * (2 * h + 1) ^ 2 * α) := by
  obtain ⟨⟨m, hm, hr⟩, -⟩ := block_holonomies_ii_loops y κ hP x Γ Γ'
  obtain ⟨h1, h2⟩ := block_holonomies_i hU hr
  have hm' : (m : ℝ) * α ≤ 4 * (2 * h + 1) ^ 2 * α := by
    have : (m : ℝ) ≤ 4 * (2 * h + 1) ^ 2 := by exact_mod_cast hm
    exact mul_le_mul_of_nonneg_right this hα
  exact ⟨h1.trans hm', h2.trans (mul_le_mul_of_nonneg_left hm' (Real.sqrt_nonneg _))⟩

end BlockHolonomies
end CoreLean

end
