/-
The closed tour of a connected finite union of curves, used in the proof of `lem:cube-count` of
BALABAN_CORE.tex.

The core doubles every segment of a connected union `G` of segments, takes a closed walk which
traverses every arc once, and parametrises it by length, obtaining a map `γ : [0, 2λ] → G` onto `G`
with `|γ(t) - γ(t')|_∞ ≤ |t - t'|`, where `λ` is the total length. We prove the same conclusion in
any metric space for a finite family of `1`-Lipschitz curves `c_i : [0, ℓ_i] → E` whose union is
connected, without the Euler walk: the tour is built by adding one curve at a time, each new curve
meeting the curves already traversed (by connectedness), and inserting the detour
`p → c(0) → c(ℓ) → p` of length `2ℓ` at a time at which the tour passes through a common point `p`.
-/
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.MetricSpace.Pseudo.Real

open Set

namespace CoreLean

variable {E : Type*} [MetricSpace E]

/-! ### Gluing paths -/

/-- `f` up to time `a`, `g` after. -/
noncomputable def glue (a : ℝ) (f g : ℝ → E) : ℝ → E := fun t => if t ≤ a then f t else g t

lemma glue_of_le {a t : ℝ} {f g : ℝ → E} (h : t ≤ a) : glue a f g t = f t := if_pos h

lemma glue_of_ge {a t : ℝ} {f g : ℝ → E} (hfg : f a = g a) (h : a ≤ t) : glue a f g t = g t := by
  unfold glue
  split_ifs with h'
  · rw [le_antisymm h' h, hfg]
  · rfl

lemma dist_le_of_lip {f : ℝ → E} (hf : LipschitzWith 1 f) (t t' : ℝ) :
    dist (f t) (f t') ≤ |t - t'| := by
  simpa [Real.dist_eq] using hf.dist_le_mul t t'

lemma lipschitzWith_glue {a : ℝ} {f g : ℝ → E} (hf : LipschitzWith 1 f) (hg : LipschitzWith 1 g)
    (hfg : f a = g a) : LipschitzWith 1 (glue a f g) := by
  refine LipschitzWith.of_dist_le_mul fun t t' => ?_
  simp only [NNReal.coe_one, one_mul, Real.dist_eq]
  wlog htt : t ≤ t' generalizing t t'
  · rw [dist_comm, abs_sub_comm]; exact this t' t (le_of_not_ge htt)
  rcases le_total t' a with h | h
  · rw [glue_of_le (htt.trans h), glue_of_le h]; exact dist_le_of_lip hf t t'
  rcases le_total t a with h' | h'
  · rw [glue_of_le h', glue_of_ge hfg h]
    calc dist (f t) (g t') ≤ dist (f t) (f a) + dist (g a) (g t') := by
          rw [hfg]; exact dist_triangle _ _ _
      _ ≤ |t - a| + |a - t'| := add_le_add (dist_le_of_lip hf t a) (dist_le_of_lip hg a t')
      _ = |t - t'| := by
          rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith),
            abs_of_nonpos (by linarith)]; ring
  · rw [glue_of_ge hfg h', glue_of_ge hfg h]; exact dist_le_of_lip hg t t'

lemma lipschitzWith_comp_sub_left {f : ℝ → E} (hf : LipschitzWith 1 f) (a : ℝ) :
    LipschitzWith 1 (fun t => f (a - t)) :=
  LipschitzWith.of_dist_le_mul fun t t' => by
    simp only [NNReal.coe_one, one_mul, Real.dist_eq]
    refine (dist_le_of_lip hf _ _).trans (le_of_eq ?_)
    rw [show a - t - (a - t') = -(t - t') by ring, abs_neg]

lemma lipschitzWith_comp_add {f : ℝ → E} (hf : LipschitzWith 1 f) (a : ℝ) :
    LipschitzWith 1 (fun t => f (t + a)) :=
  LipschitzWith.of_dist_le_mul fun t t' => by
    simp only [NNReal.coe_one, one_mul, Real.dist_eq]
    refine (dist_le_of_lip hf _ _).trans (le_of_eq ?_)
    rw [show t + a - (t' + a) = t - t' by ring]

/-! ### Curves and tours -/

/-- A curve `c : [0, ℓ] → E`, `1`-Lipschitz, so that `ℓ` bounds its length. -/
structure Curve (E : Type*) [MetricSpace E] where
  c : ℝ → E
  len : ℝ
  lip : LipschitzWith 1 c
  len_nonneg : 0 ≤ len

/-- The image `c([0, ℓ])`. -/
def Curve.img (σ : Curve E) : Set E := σ.c '' Icc 0 σ.len

lemma Curve.isCompact_img (σ : Curve E) : IsCompact σ.img :=
  isCompact_Icc.image σ.lip.continuous

lemma Curve.img_nonempty (σ : Curve E) : σ.img.Nonempty :=
  ⟨σ.c 0, 0, ⟨le_rfl, σ.len_nonneg⟩, rfl⟩

/-- A closed `1`-Lipschitz path on `[0, T]` passing through every point of `U`. -/
def IsTour (Γ : ℝ → E) (T : ℝ) (U : Set E) : Prop :=
  LipschitzWith 1 Γ ∧ Γ 0 = Γ T ∧ U ⊆ Γ '' Icc 0 T

lemma IsTour.mono {Γ : ℝ → E} {T : ℝ} {U U' : Set E} (h : IsTour Γ T U) (hU : U' ⊆ U) :
    IsTour Γ T U' := ⟨h.1, h.2.1, hU.trans h.2.2⟩

/-- Two points of a tour of length `T` are at distance at most `T / 2`. -/
lemma IsTour.dist_le {Γ : ℝ → E} {T : ℝ} {U : Set E} (h : IsTour Γ T U) {x y : E} (hx : x ∈ U)
    (hy : y ∈ U) : dist x y ≤ T / 2 := by
  obtain ⟨t, ht, rfl⟩ := h.2.2 hx
  obtain ⟨t', ht', rfl⟩ := h.2.2 hy
  clear hx hy
  wlog htt : t' ≤ t generalizing t t'
  · rw [dist_comm]; exact this t' ht' t ht (le_of_not_ge htt)
  rcases le_total (t - t') (T / 2) with hc | hc
  · refine (dist_le_of_lip h.1 t t').trans ?_
    rw [abs_of_nonneg (by linarith)]; exact hc
  · calc dist (Γ t) (Γ t') ≤ dist (Γ t) (Γ T) + dist (Γ 0) (Γ t') := by
          rw [h.2.1]; exact dist_triangle _ _ _
      _ ≤ |t - T| + |0 - t'| := add_le_add (dist_le_of_lip h.1 _ _) (dist_le_of_lip h.1 _ _)
      _ ≤ T / 2 := by
          rw [abs_of_nonpos (by linarith [ht.2]), abs_of_nonpos (by linarith [ht'.1])]
          linarith

/-- Inserting a curve through a point of a tour: the tour grows by `2ℓ`. -/
theorem IsTour.splice {Γ : ℝ → E} {T : ℝ} {U : Set E} (hΓ : IsTour Γ T U) (σ : Curve E)
    {t0 : ℝ} (ht0 : t0 ∈ Icc 0 T) (hp : Γ t0 ∈ σ.img) :
    ∃ Γ', IsTour Γ' (T + 2 * σ.len) (U ∪ σ.img) := by
  obtain ⟨u0, hu0, hpu⟩ := hp
  set ℓ := σ.len with hℓ
  have hℓ0 : 0 ≤ ℓ := σ.len_nonneg
  -- the detour `p → c(0) → c(ℓ) → p` on `[0, 2ℓ]`
  set δ : ℝ → E := glue u0 (fun τ => σ.c (u0 - τ))
    (glue (u0 + ℓ) (fun τ => σ.c (τ + -u0)) (fun τ => σ.c ((2 * ℓ + u0) - τ))) with hδ
  have hm2 : σ.c (u0 + ℓ + -u0) = σ.c (2 * ℓ + u0 - (u0 + ℓ)) := by ring_nf
  have hm1 : σ.c (u0 - u0) = glue (u0 + ℓ) (fun τ => σ.c (τ + -u0))
      (fun τ => σ.c ((2 * ℓ + u0) - τ)) u0 := by
    rw [glue_of_le (by linarith)]; ring_nf
  have hδlip : LipschitzWith 1 δ :=
    lipschitzWith_glue (lipschitzWith_comp_sub_left σ.lip u0)
      (lipschitzWith_glue (lipschitzWith_comp_add σ.lip _) (lipschitzWith_comp_sub_left σ.lip _) hm2)
      hm1
  have hδ0 : δ 0 = Γ t0 := by
    rw [hδ, glue_of_le hu0.1, sub_zero, hpu]
  have hδmid : ∀ u ∈ Icc 0 ℓ, δ (u0 + u) = σ.c u := fun u hu => by
    rw [hδ, glue_of_ge hm1 (by linarith [hu.1]), glue_of_le (by linarith [hu.2])]
    ring_nf
  have hδ2 : δ (2 * ℓ) = Γ t0 := by
    rw [hδ, glue_of_ge hm1 (by linarith [hu0.2]), glue_of_ge hm2 (by linarith [hu0.2]), ← hpu]
    ring_nf
  -- the new tour
  set Γ' : ℝ → E := glue t0 Γ (glue (t0 + 2 * ℓ) (fun τ => δ (τ + -t0))
    (fun τ => Γ (τ + -(2 * ℓ)))) with hΓ'
  have hn2 : δ (t0 + 2 * ℓ + -t0) = Γ (t0 + 2 * ℓ + -(2 * ℓ)) := by
    rw [show t0 + 2 * ℓ + -t0 = 2 * ℓ by ring, show t0 + 2 * ℓ + -(2 * ℓ) = t0 by ring, hδ2]
  have hn1 : Γ t0 = glue (t0 + 2 * ℓ) (fun τ => δ (τ + -t0)) (fun τ => Γ (τ + -(2 * ℓ))) t0 := by
    rw [glue_of_le (by linarith), add_neg_cancel, hδ0]
  refine ⟨Γ', lipschitzWith_glue hΓ.1 (lipschitzWith_glue (lipschitzWith_comp_add hδlip _)
    (lipschitzWith_comp_add hΓ.1 _) hn2) hn1, ?_, ?_⟩
  · rw [hΓ', glue_of_le ht0.1, glue_of_ge hn1 (by linarith [ht0.2]),
      glue_of_ge hn2 (by linarith [ht0.2]), add_neg_cancel_right]
    exact hΓ.2.1
  · rintro x (hx | hx)
    · obtain ⟨t, ht, rfl⟩ := hΓ.2.2 hx
      rcases le_total t t0 with h | h
      · exact ⟨t, ⟨ht.1, by linarith [ht.2]⟩, glue_of_le h⟩
      · refine ⟨t + 2 * ℓ, ⟨by linarith [ht.1], by linarith [ht.2]⟩, ?_⟩
        rw [hΓ', glue_of_ge hn1 (by linarith), glue_of_ge hn2 (by linarith), add_neg_cancel_right]
    · obtain ⟨u, hu, rfl⟩ := hx
      refine ⟨t0 + (u0 + u), ⟨by linarith [ht0.1, hu0.1, hu.1],
        by linarith [ht0.2, hu0.2, hu.2]⟩, ?_⟩
      rw [hΓ', glue_of_ge hn1 (by linarith [hu0.1, hu.1]),
        glue_of_le (by linarith [hu0.2, hu.2]), show t0 + (u0 + u) + -t0 = u0 + u by ring,
        hδmid u hu]

/-- A connected union of finitely many curves has a closed tour of twice their total length. -/
theorem exists_tour {ι : Type*} (S : Finset ι) (σ : ι → Curve E) (hS : S.Nonempty)
    (hconn : IsPreconnected (⋃ i ∈ S, (σ i).img)) :
    ∃ Γ, IsTour Γ (2 * ∑ i ∈ S, (σ i).len) (⋃ i ∈ S, (σ i).img) := by
  classical
  -- grow the set `A` of curves already traversed
  have key : ∀ n : ℕ, ∀ A ⊆ S, A.Nonempty → (S \ A).card = n →
      (∃ Γ, IsTour Γ (2 * ∑ i ∈ A, (σ i).len) (⋃ i ∈ A, (σ i).img)) →
      ∃ Γ, IsTour Γ (2 * ∑ i ∈ S, (σ i).len) (⋃ i ∈ S, (σ i).img) := by
    intro n
    induction n with
    | zero =>
      intro A hA _ hcard hT
      have : A = S := Finset.Subset.antisymm hA (Finset.sdiff_eq_empty_iff_subset.1
        (Finset.card_eq_zero.1 hcard))
      rw [← this]; exact hT
    | succ n ih =>
      intro A hA hAne hcard ⟨Γ, hΓ⟩
      obtain ⟨i0, hi0⟩ := hAne
      obtain ⟨j0, hj0⟩ : (S \ A).Nonempty := Finset.card_pos.1 (by omega)
      -- a curve outside `A` meets a curve of `A`
      have hclosed : ∀ B : Finset ι, IsClosed (⋃ i ∈ B, (σ i).img) := fun B =>
        isClosed_biUnion_finset fun i _ => (σ i).isCompact_img.isClosed
      have hcover : (⋃ i ∈ S, (σ i).img) ⊆ (⋃ i ∈ A, (σ i).img) ∪ ⋃ i ∈ S \ A, (σ i).img := by
        intro x hx
        simp only [mem_iUnion, mem_union] at hx ⊢
        obtain ⟨i, hi, hx⟩ := hx
        by_cases hiA : i ∈ A
        · exact Or.inl ⟨i, hiA, hx⟩
        · exact Or.inr ⟨i, Finset.mem_sdiff.2 ⟨hi, hiA⟩, hx⟩
      have hne1 : ((⋃ i ∈ S, (σ i).img) ∩ ⋃ i ∈ A, (σ i).img).Nonempty := by
        obtain ⟨x, hx⟩ := (σ i0).img_nonempty
        exact ⟨x, mem_biUnion (hA hi0) hx, mem_biUnion hi0 hx⟩
      have hne2 : ((⋃ i ∈ S, (σ i).img) ∩ ⋃ i ∈ S \ A, (σ i).img).Nonempty := by
        obtain ⟨x, hx⟩ := (σ j0).img_nonempty
        exact ⟨x, mem_biUnion (Finset.mem_sdiff.1 hj0).1 hx, mem_biUnion hj0 hx⟩
      obtain ⟨x, -, hxA, hxB⟩ := isPreconnected_closed_iff.1 hconn _ _ (hclosed A)
        (hclosed (S \ A)) hcover hne1 hne2
      simp only [mem_iUnion] at hxA hxB
      obtain ⟨i, hi, hxi⟩ := hxA
      obtain ⟨j, hj, hxj⟩ := hxB
      have hjA : j ∉ A := (Finset.mem_sdiff.1 hj).2
      -- splice the curve `j` in
      obtain ⟨t0, ht0, hxt⟩ := hΓ.2.2 (mem_biUnion hi hxi)
      obtain ⟨Γ', hΓ'⟩ := hΓ.splice (σ j) ht0 (hxt ▸ hxj)
      refine ih (insert j A) (Finset.insert_subset (Finset.mem_sdiff.1 hj).1 hA)
        ⟨j, Finset.mem_insert_self j A⟩ ?_ ⟨Γ', ?_⟩
      · rw [Finset.sdiff_insert, Finset.card_erase_of_mem hj, hcard, Nat.add_sub_cancel]
      · rw [Finset.sum_insert hjA, mul_add, add_comm]
        refine hΓ'.mono fun y hy => ?_
        simp only [mem_iUnion, Finset.mem_insert] at hy
        obtain ⟨k, hk | hk, hy⟩ := hy
        · exact Or.inr (hk ▸ hy)
        · exact Or.inl (mem_biUnion hk hy)
  obtain ⟨i0, hi0⟩ := hS
  -- the first curve: splice it into the constant tour of length `0`
  have h0 : IsTour (fun _ : ℝ => (σ i0).c 0) 0 ∅ :=
    ⟨(LipschitzWith.const _).weaken zero_le_one, rfl, empty_subset _⟩
  obtain ⟨Γ, hΓ⟩ := h0.splice (σ i0) ⟨le_rfl, le_rfl⟩
    ⟨0, ⟨le_rfl, (σ i0).len_nonneg⟩, rfl⟩
  refine key _ {i0} (Finset.singleton_subset_iff.2 hi0) (Finset.singleton_nonempty i0) rfl
    ⟨Γ, ?_⟩
  rw [Finset.sum_singleton]
  rw [zero_add] at hΓ
  refine hΓ.mono fun y hy => ?_
  simp only [Finset.mem_singleton, iUnion_iUnion_eq_left] at hy
  exact Or.inr hy

end CoreLean
