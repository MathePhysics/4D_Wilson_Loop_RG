/-
`thm:polymer-logarithm` of BALABAN_CORE.tex (`733037410da1`) on a grid of the torus: the grid of side `s` with `N`
cubes in each direction (`lem:cube-count`), polymers the connected unions of cubes, two unions `X ≁ X'` if they share a
cube or a wall of a cube (`def:polymers`), and `d = size s N` the linear size. With `κ₂ = 2¹⁰(3 log 2 + 1)`,
`c₇ = (9e^{2⁹}(2^{6·2¹⁰} + 1))⁻¹`, `C₇ = e^{3κ₂}/c₇`, `κ ≥ κ₂`, `0 ≤ ε ≤ c₇e^{-3κ}` and `|H(Z)| ≤ εe^{-κd(Z)}`:
`Ξ ≠ 0`, `log Ξ = Σ_XE(X)` with absolutely convergent series, `E(X) = 0` unless `X` is connected, and
`|E(X)| ≤ C₇εe^{-(κ - κ₂)d(X)}`; holomorphy in a parameter. The proof is the core's: the criterion
`eq:kotecky-preiss` for `h̄ = ε'e^{-κ₂d}`, `a = (ε'/c₇)#`, `ε' = εe^{3κ}`, from `eq:cube-count` and `eq:domain-sum`;
the abstract theorem (`ClusterLogXi`); and the decay from `d(X) ≤ Σ_id(Z_i) + 3(m - 1)` for a sequence with a connected
graph of incompatibility (`lem:contracted-geometry`(iv) with `D_i = ∅`) and `eq:cluster-sum` at `Z₀ = {Q}`.
-/
import CoreLean.ClusterLogXi
import CoreLean.ContractedCoarse

open Finset

set_option maxRecDepth 100000

noncomputable section

namespace CoreLean
namespace PolymerGrid

open Classical
open TreeGraph

variable {s : ℝ} {N : ℕ} [NeZero N]

/-- The cubes of the grid of side `s` with `N` cubes in each direction, by their centres. -/
abbrev Cube (N : ℕ) := Fin 4 → ZMod N

/-- `X ≁ X'`: the unions of cubes share a cube or a wall of a cube. -/
def NotSim (X X' : Finset (Cube N)) : Prop := ∃ c ∈ X, ∃ c' ∈ X', c = c' ∨ (wallGraph (ZMod N)).Adj c c'

/-- A connected union of cubes. -/
def IsConn (X : Finset (Cube N)) : Prop := ((wallGraph (ZMod N)).induce (X : Set (Cube N))).Connected

/-- The incompatibility of the polymers of `P`. -/
def incP (P : Finset (Finset (Cube N))) : P → P → Prop := fun Z Z' => NotSim Z.1 Z'.1

lemma IsConn.nonempty {X : Finset (Cube N)} (h : IsConn X) : X.Nonempty := by
  obtain ⟨⟨c, hc⟩⟩ := SimpleGraph.Connected.nonempty h
  exact ⟨c, hc⟩

lemma notSim_refl {X : Finset (Cube N)} (h : X.Nonempty) : NotSim X X := by
  obtain ⟨c, hc⟩ := h
  exact ⟨c, hc, c, hc, Or.inl rfl⟩

lemma notSim_symm {X X' : Finset (Cube N)} (h : NotSim X X') : NotSim X' X := by
  obtain ⟨c, hc, c', hc', h⟩ := h
  exact ⟨c', hc', c, hc, h.elim (fun e => Or.inl e.symm) fun h => Or.inr h.symm⟩

/-! ### The constants -/

/-- `κ₂ = 2¹⁰(3 log 2 + 1)`. -/
def kappa2 : ℝ := 2 ^ 10 * (3 * Real.log 2 + 1)

/-- `2^{6·2¹⁰} + 1`, the bound of `eq:domain-sum`. -/
def D7 : ℝ := 2 ^ (6 * 2 ^ 10) + 1

lemma D7_eq : D7 = 2 ^ (6 * 2 ^ 10) + 1 := rfl

lemma pow_two_add_one_pos (n : ℕ) : (0 : ℝ) < 2 ^ n + 1 := by positivity

lemma D7_pos : 0 < D7 := pow_two_add_one_pos _

/-- `c₇ = (9e^{2⁹}(2^{6·2¹⁰} + 1))⁻¹`. -/
def c7 : ℝ := (9 * Real.exp (2 ^ 9) * D7)⁻¹

/-- `C₇ = e^{3κ₂}/c₇`. -/
def C7 : ℝ := Real.exp (3 * kappa2) / c7

lemma c7_pos : 0 < c7 := inv_pos.2 (mul_pos (mul_pos (by norm_num) (Real.exp_pos _)) D7_pos)

lemma kappa2_nonneg : 0 ≤ kappa2 := by
  unfold kappa2
  have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
  positivity

lemma kappa2_sub : kappa2 - 2 ^ 9 = 2 ^ 9 * (6 * Real.log 2 + 1) := by unfold kappa2; ring

/-! ### The criterion of Kotecký and Preiss -/

/-- The cubes of `M` and those which share a wall with one of them. -/
def nbhd (M : Finset (Cube N)) : Finset (Cube N) :=
  M.biUnion fun c => insert c (Finset.univ.image (wallNbr (ZMod N) c))

lemma card_nbhd (M : Finset (Cube N)) : (nbhd M).card ≤ 9 * M.card := by
  refine (Finset.card_biUnion_le).trans ?_
  calc ∑ c ∈ M, (insert c (Finset.univ.image (wallNbr (ZMod N) c))).card ≤ ∑ c ∈ M, 9 :=
        Finset.sum_le_sum fun c _ => (Finset.card_insert_le _ _).trans (by
          have := Finset.card_image_le (s := (Finset.univ : Finset (Fin 4 × Bool))) (f := wallNbr (ZMod N) c)
          simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool] at this
          omega)
    _ = 9 * M.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

lemma exists_mem_nbhd {Z M : Finset (Cube N)} (h : NotSim Z M) : ∃ c ∈ Z, c ∈ nbhd M := by
  obtain ⟨c, hc, c', hc', h⟩ := h
  refine ⟨c, hc, Finset.mem_biUnion.2 ⟨c', hc', ?_⟩⟩
  rcases h with rfl | h
  · exact Finset.mem_insert_self _ _
  · obtain ⟨-, p, hp⟩ := h.symm
    exact Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨p, Finset.mem_univ _, hp.symm⟩)

/-- **The criterion** (the step "The criterion" of the proof): for `0 ≤ ε' ≤ c₇`, `h̄ = ε'e^{-κ₂d}` and
`a = (ε'/c₇)#`, every union `M` of cubes satisfies `Σ_{Z ∈ 𝒫, Z ≁ M}h̄(Z)e^{a(Z)} ≤ (ε'/c₇)#(M)`. -/
theorem criterion (hs : 0 < s) (P : Finset (Finset (Cube N))) (hP : ∀ Z ∈ P, IsConn Z) {ε' : ℝ}
    (hε'0 : 0 ≤ ε') (hε' : ε' ≤ c7) (M : Finset (Cube N)) :
    ∑ Z ∈ (Finset.univ : Finset P).filter (fun Z => NotSim Z.1 M),
      ε' * Real.exp (-kappa2 * size s N Z.1) * Real.exp (ε' / c7 * Z.1.card) ≤ ε' / c7 * M.card := by
  have hc7 : 0 < c7 := c7_pos
  obtain ⟨κ', hκ'⟩ : ∃ κ' : ℝ, κ' = kappa2 - 2 ^ 9 := ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : P → ℝ, g = fun Z => ε' * Real.exp (2 ^ 9) * Real.exp (-κ' * size s N Z.1) :=
    ⟨_, rfl⟩
  have hg0 : ∀ Z, 0 ≤ g Z := fun Z => by rw [hg]; positivity
  -- the term bound `h̄e^{a} ≤ ε'e^{2⁹}e^{-(κ₂ - 2⁹)d}`
  have hterm : ∀ Z : P, ε' * Real.exp (-kappa2 * size s N Z.1) * Real.exp (ε' / c7 * Z.1.card) ≤ g Z := by
    intro Z
    have hd := size_nonneg (N := N) hs Z.1
    have hcard := card_le_size hs (hP Z.1 Z.2)
    have ha : ε' / c7 * Z.1.card ≤ Z.1.card := by
      have : ε' / c7 ≤ 1 := (div_le_one hc7).2 hε'
      exact mul_le_of_le_one_left (Nat.cast_nonneg _) this
    have hexp : -kappa2 * size s N Z.1 + ε' / c7 * Z.1.card ≤ 2 ^ 9 + -κ' * size s N Z.1 := by
      rw [hκ']; nlinarith
    rw [hg, mul_assoc, ← Real.exp_add]
    simp only
    rw [mul_assoc, ← Real.exp_add]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hexp) hε'0
  -- each polymer `≁ M` contains a cube of `nbhd M`
  have hcover : ∑ Z ∈ (Finset.univ : Finset P).filter (fun Z => NotSim Z.1 M), g Z ≤
      ∑ x ∈ nbhd M, ∑ Z ∈ (Finset.univ : Finset P).filter (fun Z => x ∈ Z.1), g Z := by
    calc ∑ Z ∈ (Finset.univ : Finset P).filter (fun Z => NotSim Z.1 M), g Z
        ≤ ∑ Z ∈ (Finset.univ : Finset P).filter (fun Z => NotSim Z.1 M),
            ∑ x ∈ nbhd M, (if x ∈ Z.1 then g Z else 0) := by
          refine Finset.sum_le_sum fun Z hZ => ?_
          obtain ⟨c, hcZ, hcM⟩ := exists_mem_nbhd (Finset.mem_filter.1 hZ).2
          calc g Z = (if c ∈ Z.1 then g Z else 0) := (if_pos hcZ).symm
            _ ≤ _ := Finset.single_le_sum (f := fun x => if x ∈ Z.1 then g Z else 0)
                (fun x _ => by split_ifs; exact hg0 Z; exact le_rfl) hcM
      _ ≤ ∑ Z : P, ∑ x ∈ nbhd M, (if x ∈ Z.1 then g Z else 0) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun Z _ _ =>
            Finset.sum_nonneg fun x _ => by split_ifs; exact hg0 Z; exact le_rfl
      _ = ∑ x ∈ nbhd M, ∑ Z ∈ (Finset.univ : Finset P).filter (fun Z => x ∈ Z.1), g Z := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun x _ => (Finset.sum_filter _ _).symm
  -- `eq:domain-sum` at each cube
  have hdom : ∀ x, ∑ Z ∈ (Finset.univ : Finset P).filter (fun Z => x ∈ Z.1), g Z ≤
      ε' * Real.exp (2 ^ 9) * D7 := by
    intro x
    rw [hg, ← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hκ'' : 2 ^ 9 * (6 * Real.log 2 + 1) ≤ κ' := by rw [hκ', kappa2_sub]
    have h := domain_sum_finset (wallGraph (ZMod N)) (wallGraph_degree_le _) (size_nonneg hs)
      (fun X _ hconn => card_le_size hs hconn) hκ''
      (((Finset.univ : Finset P).filter (fun Z => x ∈ Z.1)).image Subtype.val) (fun X hX => by
        obtain ⟨Z, hZ, rfl⟩ := Finset.mem_image.1 hX
        exact ⟨(Finset.mem_filter.1 hZ).2, hP Z.1 Z.2⟩)
    rw [Finset.sum_image fun Z _ Z' _ h => Subtype.ext h, ← D7_eq] at h
    exact h
  calc _ ≤ ∑ Z ∈ (Finset.univ : Finset P).filter (fun Z => NotSim Z.1 M), g Z :=
        Finset.sum_le_sum fun Z _ => hterm Z
    _ ≤ ∑ x ∈ nbhd M, ε' * Real.exp (2 ^ 9) * D7 :=
        hcover.trans (Finset.sum_le_sum fun x _ => hdom x)
    _ = (nbhd M).card * (ε' * Real.exp (2 ^ 9) * D7) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (9 * M.card : ℕ) * (ε' * Real.exp (2 ^ 9) * D7) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast card_nbhd M) (by have := D7_pos; positivity)
    _ = ε' / c7 * M.card := by
        rw [c7, div_inv_eq_mul]
        push_cast
        ring

/-! ### The geometry of the clusters -/

lemma conn_mono {α β : Type*} {Vs : Finset α} {ends : β → Sym2 α} {S T : Finset β} (h : Conn Vs ends S)
    (hST : S ⊆ T) : Conn Vs ends T := fun x hx y hy =>
  Relation.ReflTransGen.lift id (fun _ _ ⟨e, he, hab⟩ => ⟨e, hST he, hab⟩) _ _ (h x hx y hy)

/-- Connectedness through a relation on all the cubes. -/
lemma isConn_iff {X : Finset (Cube N)} :
    IsConn X ↔ X.Nonempty ∧ ∀ a ∈ X, ∀ b ∈ X,
      Relation.ReflTransGen (fun u v => (wallGraph (ZMod N)).Adj u v ∧ u ∈ X ∧ v ∈ X) a b := by
  constructor
  · intro hX
    refine ⟨hX.nonempty, fun a ha b hb => ?_⟩
    have hr := (SimpleGraph.reachable_iff_reflTransGen _ _).1
      (SimpleGraph.Connected.preconnected hX ⟨a, ha⟩ ⟨b, hb⟩)
    exact Relation.ReflTransGen.lift
      (p := fun u v => (wallGraph (ZMod N)).Adj u v ∧ u ∈ X ∧ v ∈ X)
      (fun v : (X : Set (Cube N)) => v.1) (fun v w hvw => ⟨hvw, v.2, w.2⟩) _ _ hr
  · rintro ⟨⟨c, hc⟩, h⟩
    unfold IsConn
    rw [SimpleGraph.connected_iff]
    refine ⟨fun u v => ?_, ⟨⟨c, hc⟩⟩⟩
    rw [SimpleGraph.reachable_iff_reflTransGen]
    have key : ∀ b, Relation.ReflTransGen (fun u v => (wallGraph (ZMod N)).Adj u v ∧ u ∈ X ∧ v ∈ X) u.1 b →
        ∀ hb : b ∈ X, Relation.ReflTransGen ((wallGraph (ZMod N)).induce (X : Set (Cube N))).Adj u ⟨b, hb⟩ := by
      intro b hub
      induction hub with
      | refl => intro _; exact Relation.ReflTransGen.refl
      | @tail b' b'' _ hstep ih =>
        intro hb''
        exact (ih hstep.2.1).tail hstep.1
    exact key v.1 (h u.1 u.2 v.1 v.2) v.2

/-- `ρ^T = 0` unless the graph of incompatibility is connected. -/
lemma conn_of_ursS_ne {Q : Type*} [Fintype Q] {inc : Q → Q → Prop} {m : ℕ} (hm : 1 ≤ m) (Z : Fin m → Q)
    (h : ursS inc Z ≠ 0) : Conn (Finset.univ : Finset (Fin m)) id (incG inc Z) := by
  by_contra hc
  apply h
  rw [ursS_eq_ursell]
  have hb := (ursell_bound inc hm Z).1
  have h0 : treeCount inc Z = 0 := by
    unfold treeCount tau
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro S hS hS'
    exact hc (conn_mono hS'.1 (Finset.mem_powerset.1 hS))
  rw [h0, Nat.cast_zero] at hb
  exact abs_nonpos_iff.1 hb

/-- A connected graph of incompatibility joins any two indices by a chain of incompatible polymers. -/
lemma chain_of_conn {Q : Type*} {inc : Q → Q → Prop} (hsymm : ∀ a b, inc a b → inc b a) {m : ℕ} (Z : Fin m → Q)
    (h : Conn (Finset.univ : Finset (Fin m)) id (incG inc Z)) (x y : Fin m) :
    Relation.ReflTransGen (fun i j => inc (Z i) (Z j)) x y := by
  refine Relation.ReflTransGen.lift id (fun i j ⟨e, he, hij⟩ => ?_) _ _
    (h x (Finset.mem_univ _) y (Finset.mem_univ _))
  obtain ⟨-, i', j', he', hinc⟩ := Finset.mem_filter.1 he
  simp only [id] at hij
  rw [hij, Sym2.eq_iff] at he'
  rcases he' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hinc
  · exact hsymm _ _ hinc

variable (hs : 0 < s)
include hs

/-- **The union of a cluster** with a connected graph of incompatibility is connected, and
`d(X) ≤ Σ_id(Z_i) + 3(m - 1)`. -/
theorem cluster_union (P : Finset (Finset (Cube N))) (hP : ∀ Z ∈ P, IsConn Z) {m : ℕ} (hm : 1 ≤ m) (Z : Fin m → P)
    (h : ursS (incP P) Z ≠ 0) :
    IsConn (unionOf Subtype.val Z) ∧
      size s N (unionOf Subtype.val Z) ≤ ∑ i, size s N (Z i).1 + 3 * ((m : ℝ) - 1) := by
  set X := unionOf Subtype.val Z with hX
  have hmem : ∀ i, (Z i).1 ⊆ X := fun i c hc => by
    rw [hX, unionOf, Finset.mem_sup]; exact ⟨i, Finset.mem_univ _, hc⟩
  have hchain := chain_of_conn (fun a b => notSim_symm) Z (conn_of_ursS_ne hm Z h)
  -- connectedness
  have hconn : IsConn X := by
    refine isConn_iff.2 ⟨?_, fun a ha b hb => ?_⟩
    · obtain ⟨c, hc⟩ := (hP _ (Z ⟨0, hm⟩).2).nonempty
      exact ⟨c, hmem _ hc⟩
    · set R := fun u v => (wallGraph (ZMod N)).Adj u v ∧ u ∈ X ∧ v ∈ X
      have within : ∀ i, ∀ u ∈ (Z i).1, ∀ v ∈ (Z i).1, Relation.ReflTransGen R u v := by
        intro i u hu v hv
        have := (isConn_iff.1 (hP _ (Z i).2)).2 u hu v hv
        exact Relation.ReflTransGen.lift id (fun p q hpq => ⟨hpq.1, hmem i hpq.2.1, hmem i hpq.2.2⟩) _ _ this
      rw [hX, unionOf, Finset.mem_sup] at ha hb
      obtain ⟨x, -, hax⟩ := ha
      obtain ⟨y, -, hby⟩ := hb
      have key : ∀ y', Relation.ReflTransGen (fun i j => incP P (Z i) (Z j)) x y' →
          ∀ b' ∈ (Z y').1, Relation.ReflTransGen R a b' := by
        intro y' hxy
        induction hxy with
        | refl => exact fun b' hb' => within x a hax b' hb'
        | @tail y1 y2 _ h12 ih =>
          intro b' hb'
          obtain ⟨c, hc, c', hc', hcc⟩ := h12
          refine (ih c hc).trans (Relation.ReflTransGen.trans ?_ (within y2 c' hc' b' hb'))
          rcases hcc with rfl | hadj
          · exact Relation.ReflTransGen.refl
          · exact Relation.ReflTransGen.single ⟨hadj, hmem y1 hc, hmem y2 hc'⟩
      exact key y (hchain x y) b hby
  refine ⟨hconn, ?_⟩
  -- `lem:contracted-geometry`(iv) with `D_i = ∅`
  have hiv := Contracted.Grid.contracted_iv (g := Contracted.Grid.unitGrid s N hs) (ι := Fin m) (Z := X) hconn
    (fun i => (Z i).1) (fun i => hP _ (Z i).2) hmem (fun _ => ∅) (fun _ => Finset.empty_subset _)
  have h1 : (Finset.univ.biUnion fun _ : Fin m => (∅ : Finset (Contracted.Grid.unitGrid s N hs).Idx)) = ∅ :=
    Finset.eq_empty_of_forall_notMem fun c hc => by
      obtain ⟨_, _, h⟩ := Finset.mem_biUnion.1 hc
      exact Finset.notMem_empty _ h
  have hsub : X ⊆ Finset.univ.biUnion fun i => (Z i).1 := fun c hc => by
    rw [hX, unionOf, Finset.mem_sup] at hc
    obtain ⟨i, -, hi⟩ := hc
    exact Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hi⟩
  have hcard : (X \ Finset.univ.biUnion fun i => (Z i).1).card = 0 :=
    Finset.card_eq_zero.2 (Finset.sdiff_eq_empty_iff_subset.2 hsub)
  have h3 : (Finset.univ.filter fun _ : Fin m => (∅ : Finset (Contracted.Grid.unitGrid s N hs).Idx) = ∅).card = m :=
    by simp
  have h4 : (Finset.univ.filter fun _ : Fin m => (∅ : Finset (Contracted.Grid.unitGrid s N hs).Idx).Nonempty).card =
      0 := by simp
  have hsum : ∑ i, (Contracted.Grid.unitGrid s N hs).d (Z i).1 ∅ = ∑ i, size s N (Z i).1 :=
    Finset.sum_congr rfl fun i _ => Contracted.Grid.d_empty_eq_size s N hs _
  rw [h1] at hiv
  refine (Contracted.Grid.d_empty_eq_size s N hs X).symm.le.trans (hiv.trans (le_of_eq ?_))
  have key : ∀ (A : ℝ) (k1 k2 k3 : ℕ), A = ∑ i, size s N (Z i).1 → k1 = 0 → k2 = m → k3 = 0 →
      A + 3 * (k1 : ℝ) + 3 * ((k2 : ℝ) + k3 - 1) = ∑ i, size s N (Z i).1 + 3 * ((m : ℝ) - 1) := by
    intro A k1 k2 k3 hA h1' h2' h3'
    subst hA h1' h2' h3'
    simp
  exact key _ _ _ _ hsum hcard h3 h4

/-! ### The theorem -/

/-- The data of the criterion: `ε' = εe^{3κ}`, `h̄ = ε'e^{-κ₂d}`, `a = (ε'/c₇)#`, and the hypotheses of the abstract
theorem which they satisfy. -/
lemma setup (P : Finset (Finset (Cube N))) (hP : ∀ Z ∈ P, IsConn Z) {κ ε : ℝ} (hκ : kappa2 ≤ κ) (hε0 : 0 ≤ ε)
    (hε : ε ≤ c7 * Real.exp (-3 * κ)) :
    0 ≤ ε * Real.exp (3 * κ) ∧ ε * Real.exp (3 * κ) ≤ c7 ∧ (∀ Z : P, incP P Z Z) ∧
      (∀ Z Z' : P, incP P Z Z' → incP P Z' Z) ∧
      Cluster.KP (incP P) Finset.univ (fun Z => ε * Real.exp (3 * κ) * Real.exp (-kappa2 * size s N Z.1))
        (fun Z => ε * Real.exp (3 * κ) / c7 * Z.1.card) := by
  have hε'0 : 0 ≤ ε * Real.exp (3 * κ) := mul_nonneg hε0 (Real.exp_pos _).le
  have hε' : ε * Real.exp (3 * κ) ≤ c7 := by
    calc ε * Real.exp (3 * κ) ≤ c7 * Real.exp (-3 * κ) * Real.exp (3 * κ) :=
          mul_le_mul_of_nonneg_right hε (Real.exp_pos _).le
      _ = c7 := by rw [mul_assoc, ← Real.exp_add]; simp
  exact ⟨hε'0, hε', fun Z => notSim_refl (hP Z.1 Z.2).nonempty, fun Z Z' h => notSim_symm h,
    fun Z _ => criterion hs P hP hε'0 hε' Z.1⟩

lemma bound_le_hbar (P : Finset (Finset (Cube N))) {κ ε : ℝ} (hκ : kappa2 ≤ κ) (hε0 : 0 ≤ ε) (Z : P) :
    ε * Real.exp (-κ * size s N Z.1) ≤ ε * Real.exp (3 * κ) * Real.exp (-kappa2 * size s N Z.1) := by
  have hd := size_nonneg (N := N) hs Z.1
  have hk := kappa2_nonneg
  rw [mul_assoc, ← Real.exp_add]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hε0
  nlinarith [mul_nonneg (sub_nonneg.2 hκ) hd]

/-- **`thm:polymer-logarithm`** on the grid. Let `𝒫` be a finite set of polymers (connected unions of cubes),
`κ ≥ κ₂`, `0 ≤ ε ≤ c₇e^{-3κ}`, and `|H(Z)| ≤ εe^{-κd(Z)}`. Then `Ξ ≠ 0`; the continuous logarithm `L` of
`t ↦ Ξ(tH)` on `[0, 1]` with `L(0) = 0` (unique by `clog_unique`) has `L(1) = Σ_{m ≥ 1}c_m(H)/m!`, absolutely
convergent; this series is `Σ_XE(X)` over the unions `X` of cubes of the polymers, each `E(X)` absolutely convergent;
`E(X) = 0` unless `X` is connected; and `|E(X)| ≤ C₇εe^{-(κ - κ₂)d(X)}` for every union `X` of cubes. -/
theorem polymer_logarithm (P : Finset (Finset (Cube N))) (hP : ∀ Z ∈ P, IsConn Z) {κ ε : ℝ} (hκ : kappa2 ≤ κ)
    (hε0 : 0 ≤ ε) (hε : ε ≤ c7 * Real.exp (-3 * κ)) (H : P → ℂ)
    (hH : ∀ Z, ‖H Z‖ ≤ ε * Real.exp (-κ * size s N Z.1)) :
    Cluster.Xi (incP P) Finset.univ H ≠ 0 ∧
      (∃ L : ℝ → ℂ, ContinuousOn L (Set.Icc 0 1) ∧ L 0 = 0 ∧
        (∀ t ∈ Set.Icc (0 : ℝ) 1, Complex.exp (L t) = Cluster.Xi (incP P) Finset.univ (fun Z => (t : ℂ) * H Z)) ∧
        HasSum (logTerm (incP P) H) (L 1)) ∧
      Summable (fun k => ‖logTerm (incP P) H k‖) ∧
      (∀ X, Summable fun k => ‖unionTerm (incP P) Subtype.val H X k‖) ∧
      HasSum (logTerm (incP P) H)
        (∑ X ∈ ((Finset.univ : Finset P).sup Subtype.val).powerset, EX (incP P) Subtype.val H X) ∧
      (∀ X, EX (incP P) Subtype.val H X ≠ 0 → IsConn X) ∧
      (∀ X, ‖EX (incP P) Subtype.val H X‖ ≤ C7 * ε * Real.exp (-(κ - kappa2) * size s N X)) := by
  obtain ⟨hε'0, hε', hrefl, hsymm, hKP⟩ := setup hs P hP hκ hε0 hε
  set ε' := ε * Real.exp (3 * κ) with hε'def
  set w : P → ℝ := fun Z => ε' * Real.exp (-kappa2 * size s N Z.1) with hwdef
  set a : P → ℝ := fun Z => ε' / c7 * Z.1.card with hadef
  have hw : ∀ Z, 0 ≤ w Z := fun Z => mul_nonneg hε'0 (Real.exp_pos _).le
  have hHw : ∀ Z, ‖H Z‖ ≤ w Z := fun Z => (hH Z).trans (bound_le_hbar hs P hκ hε0 Z)
  obtain ⟨hXi, L, hLc, hL0, hLe, hLabs, hLs⟩ := polymer_log hrefl hsymm w a hw hKP H hHw
  obtain ⟨habs, -, hsumX⟩ := log_eq_sum_EX hrefl hsymm w a hw hKP H hHw Subtype.val
  have hc7 := c7_pos
  have hC7 : 0 < C7 := div_pos (Real.exp_pos _) hc7
  -- the vanishing of `E(X)` for the sets of cubes which are not the union of a cluster with `ρ^T ≠ 0`
  have hzero : ∀ X, (∀ (k : ℕ) (Z : Fin (k + 1) → P), unionOf Subtype.val Z = X → ursS (incP P) Z = 0) →
      EX (incP P) Subtype.val H X = 0 := by
    intro X hX
    unfold EX
    convert tsum_zero with k
    unfold unionTerm
    rw [Finset.sum_eq_zero fun Z _ => ?_, mul_zero]
    split_ifs with h
    · rw [hX k Z h, Int.cast_zero, zero_mul]
    · rfl
  refine ⟨hXi, ⟨L, hLc, hL0, hLe, hLs⟩, hLabs, habs, hsumX, fun X hX => ?_, fun X => ?_⟩
  · by_contra hc
    exact hX (hzero X fun k Z hZ => by
      by_contra hU
      exact hc (hZ ▸ (cluster_union hs P hP (Nat.succ_pos k) Z hU).1))
  · by_cases hXe : X = ∅
    · rw [hzero X fun k Z hZ => ?_, norm_zero]
      · positivity
      · exfalso
        obtain ⟨c, hc⟩ := (hP _ (Z 0).2).nonempty
        have : c ∈ unionOf Subtype.val Z := by
          rw [unionOf, Finset.mem_sup]; exact ⟨0, Finset.mem_univ _, hc⟩
        rw [hZ, hXe] at this
        exact Finset.notMem_empty c this
    obtain ⟨q, hq⟩ := Finset.nonempty_iff_ne_empty.2 hXe
    set Nq := (Finset.univ : Finset P).filter (fun Z' => NotSim Z'.1 {q}) with hNq
    set B := Real.exp (-(κ - kappa2) * size s N X) * Real.exp (-3 * (κ - kappa2)) with hB
    have hB0 : 0 ≤ B := by positivity
    have hterm : ∀ k, ‖unionTerm (incP P) Subtype.val H X k‖ ≤ B * clusterTerm (incP P) w Nq k := by
      intro k
      unfold unionTerm clusterTerm
      rw [norm_mul, norm_inv, Complex.norm_natCast, mul_left_comm, Finset.mul_sum]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun Z _ => ?_)
      by_cases hZX : unionOf Subtype.val Z = X
      · rw [if_pos hZX]
        have hmeet : ∃ i, Z i ∈ Nq := by
          rw [← hZX, unionOf, Finset.mem_sup] at hq
          obtain ⟨i, -, hi⟩ := hq
          exact ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, q, hi, q, Finset.mem_singleton_self q, Or.inl rfl⟩⟩
        rw [if_pos hmeet]
        by_cases hU : ursS (incP P) Z = 0
        · rw [hU]; simp
        · have hd := (cluster_union hs P hP (Nat.succ_pos k) Z hU).2
          rw [hZX] at hd
          rw [norm_mul, Complex.norm_intCast, norm_prod]
          push_cast
          rw [mul_left_comm]
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          set Sd := ∑ i, size s N (Z i).1 with hSd
          have hprodH : ∏ i, ‖H (Z i)‖ ≤ ε ^ (k + 1) * Real.exp (-κ * Sd) := by
            calc ∏ i, ‖H (Z i)‖ ≤ ∏ i, (ε * Real.exp (-κ * size s N (Z i).1)) :=
                  Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) fun i _ => hH _
              _ = ε ^ (k + 1) * Real.exp (-κ * Sd) := by
                  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
                    ← Real.exp_sum, hSd, Finset.mul_sum]
          have hprodw : ∏ i, w (Z i) =
              ε ^ (k + 1) * Real.exp ((k + 1 : ℕ) * (3 * κ)) * Real.exp (-kappa2 * Sd) := by
            rw [hwdef]
            simp only
            rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.exp_sum,
              hε'def, mul_pow, ← Real.exp_nat_mul, hSd, Finset.mul_sum]
          rw [hprodw]
          refine hprodH.trans ?_
          have hexp : -κ * Sd ≤ -(κ - kappa2) * size s N X + -3 * (κ - kappa2) + (k + 1 : ℕ) * (3 * κ) +
              -kappa2 * Sd := by
            have h1 := mul_le_mul_of_nonneg_left hd (sub_nonneg.2 hκ)
            have h2 := mul_nonneg kappa2_nonneg (Nat.cast_nonneg (α := ℝ) k)
            push_cast at h1 ⊢
            nlinarith [kappa2_nonneg]
          calc ε ^ (k + 1) * Real.exp (-κ * Sd)
              ≤ ε ^ (k + 1) * Real.exp (-(κ - kappa2) * size s N X + -3 * (κ - kappa2) +
                  (k + 1 : ℕ) * (3 * κ) + -kappa2 * Sd) :=
                mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hexp) (pow_nonneg hε0 _)
            _ = B * (ε ^ (k + 1) * Real.exp ((k + 1 : ℕ) * (3 * κ)) * Real.exp (-kappa2 * Sd)) := by
                rw [hB, Real.exp_add, Real.exp_add, Real.exp_add]; ring
      · rw [if_neg hZX, norm_zero]
        refine mul_nonneg hB0 ?_
        split_ifs
        · exact mul_nonneg (abs_nonneg _) (Finset.prod_nonneg fun i _ => hw _)
        · exact le_rfl
    have hcs : Summable (clusterTerm (incP P) w Nq) := summable_clusterTerm hrefl hsymm w a hw hKP Nq
    have htsum : ∑' k, clusterTerm (incP P) w Nq k ≤ ∑ Z ∈ Nq, w Z * Real.exp (a Z) :=
      Real.tsum_le_of_sum_range_le (clusterTerm_nonneg w hw Nq) fun K => cluster_sum hrefl hsymm w a hw hKP Nq K
    have hcrit : ∑ Z ∈ Nq, w Z * Real.exp (a Z) ≤ ε' / c7 := by
      have := criterion hs P hP hε'0 hε' {q}
      rw [Finset.card_singleton, Nat.cast_one, mul_one] at this
      exact this
    have hexp3 : Real.exp (-3 * (κ - kappa2)) * Real.exp (3 * κ) = Real.exp (3 * kappa2) := by
      rw [← Real.exp_add]; ring_nf
    calc ‖EX (incP P) Subtype.val H X‖ ≤ ∑' k, ‖unionTerm (incP P) Subtype.val H X k‖ :=
          norm_tsum_le_tsum_norm (habs X)
      _ ≤ ∑' k, B * clusterTerm (incP P) w Nq k := Summable.tsum_le_tsum hterm (habs X) (hcs.mul_left B)
      _ = B * ∑' k, clusterTerm (incP P) w Nq k := tsum_mul_left
      _ ≤ B * (ε' / c7) := mul_le_mul_of_nonneg_left (htsum.trans hcrit) hB0
      _ = Real.exp (-(κ - kappa2) * size s N X) * (Real.exp (-3 * (κ - kappa2)) * Real.exp (3 * κ)) * ε / c7 := by
          rw [hB, hε'def]; ring
      _ = C7 * ε * Real.exp (-(κ - kappa2) * size s N X) := by
          rw [hexp3, C7]; ring

/-- **Holomorphy** (the last sentence of `thm:polymer-logarithm`): if the activities depend holomorphically on a
parameter `ζ` in an open `U ⊆ ℂ` with the bound `|H_ζ(Z)| ≤ εe^{-κd(Z)}` uniform on `U`, then `log Ξ = Σ_mc_m(H_ζ)/m!`
and every `E_ζ(X)` are holomorphic on `U`. -/
theorem polymer_logarithm_holomorphic (P : Finset (Finset (Cube N))) (hP : ∀ Z ∈ P, IsConn Z) {κ ε : ℝ}
    (hκ : kappa2 ≤ κ) (hε0 : 0 ≤ ε) (hε : ε ≤ c7 * Real.exp (-3 * κ)) {U : Set ℂ} (hU : IsOpen U)
    (H : ℂ → P → ℂ) (hHd : ∀ Z, DifferentiableOn ℂ (fun ζ => H ζ Z) U)
    (hH : ∀ ζ ∈ U, ∀ Z, ‖H ζ Z‖ ≤ ε * Real.exp (-κ * size s N Z.1)) (X : Finset (Cube N)) :
    DifferentiableOn ℂ (fun ζ => ∑' k, logTerm (incP P) (H ζ) k) U ∧
      DifferentiableOn ℂ (fun ζ => EX (incP P) Subtype.val (H ζ) X) U := by
  obtain ⟨hε'0, -, hrefl, hsymm, hKP⟩ := setup hs P hP hκ hε0 hε
  exact polymer_log_holomorphic hrefl hsymm _ _ (fun Z => mul_nonneg hε'0 (Real.exp_pos _).le) hKP hU H hHd
    (fun ζ hζ Z => (hH ζ hζ Z).trans (bound_le_hbar hs P hκ hε0 Z)) Subtype.val X

end PolymerGrid
end CoreLean

end
