import CoreLean.WilsonLoop.Lattice

/-!
# Sanity checks: gauge invariance of the loop observables

Checks on the definitions of `CoreLean.WilsonLoop.Lattice`.

## Main definitions

* `CoreLean.WilsonLoop.GField.gauge`: the action of a gauge transformation
  `u : Site n → G.carrier` on the gauge fields with values in `G`.
* `CoreLean.WilsonLoop.IsPathFromTo x γ y`: the bonds of `γ` are consecutive and lead from `x` to
  `y`.
* `CoreLean.WilsonLoop.Loop.rotate`: the same loop with another first bond.

## Main statements

* `CoreLean.WilsonLoop.GField.toConfig_gauge`: the configuration of a gauge transformed field is
  the gauge transform `CoreLean.Config.gauge` of its configuration.
* `CoreLean.WilsonLoop.hol_gauge`, `CoreLean.WilsonLoop.GField.hol_gauge`: a gauge transformation
  multiplies the parallel transport along a path by the values of the gauge function at its two
  ends.
* `CoreLean.WilsonLoop.IsPathFromTo.refinePath`: for `n ≠ 0`, a path of the lattice with `n` sites
  per side, read on the lattice with `r * n` sites per side, is a path between the images of its
  ends.
* `CoreLean.WilsonLoop.Loop.closed_refinePath`: for `n ≠ 0`, a loop read on the finer lattice is
  closed in the sense of `CoreLean.WilsonLoop.Loop.closed`.
* `CoreLean.WilsonLoop.Loop.hol_gauge`: a gauge transformation of the finer lattice conjugates
  the holonomy of a loop.
* `CoreLean.WilsonLoop.Ensemble.observable_gauge`: the observable of a loop ensemble is gauge
  invariant.
* `CoreLean.WilsonLoop.Loop.character_hol_rotate`: the character of the holonomy of a loop does
  not depend on which bond of the loop is the first.

The gauge invariance of the action is `CoreLean.action_gauge`.
-/

namespace CoreLean

namespace WilsonLoop

variable {N n : ℕ}

local notation "GLN" => (Matrix (Fin N) (Fin N) ℂ)ˣ

/-! ### Paths -/

/-- `IsPathFromTo x γ y`: the bonds of `γ` are consecutive (each ends where the next one
begins), the first begins at `x`, and the last ends at `y`.  The empty list is a path from `x`
to `x`.  `CoreLean.IsPath x γ` of `CoreLean.Transports` is this condition without the end. -/
def IsPathFromTo : Site n → List (Bond n) → Site n → Prop
  | x, [], y => x = y
  | x, b :: γ, y => b.site = x ∧ IsPathFromTo b.plus γ y

/-- The empty list is a path from `x` to `y` if and only if `x = y`. -/
@[simp] theorem isPathFromTo_nil {x y : Site n} : IsPathFromTo x [] y ↔ x = y := Iff.rfl

/-- A path from `x` to `y` is a bond which begins at `x`, followed by a path from its end to
`y`. -/
@[simp] theorem isPathFromTo_cons {x y : Site n} {b : Bond n} {γ : List (Bond n)} :
    IsPathFromTo x (b :: γ) y ↔ b.site = x ∧ IsPathFromTo b.plus γ y := Iff.rfl

/-- A path from `x` to `y` followed by a path from `y` to `z` is a path from `x` to `z`. -/
theorem IsPathFromTo.append {x y z : Site n} {γ₁ γ₂ : List (Bond n)} (h₁ : IsPathFromTo x γ₁ y)
    (h₂ : IsPathFromTo y γ₂ z) : IsPathFromTo x (γ₁ ++ γ₂) z := by
  induction γ₁ generalizing x with
  | nil => rwa [List.nil_append, isPathFromTo_nil.1 h₁]
  | cons b γ ih =>
    obtain ⟨hb, h₁⟩ := isPathFromTo_cons.1 h₁
    exact isPathFromTo_cons.2 ⟨hb, ih h₁⟩

/-- Bonds `f 0, …, f (r - 1)`, each of which ends where the next one begins, are a path from the
initial site of `f 0` to the initial site of `f r`. -/
theorem isPathFromTo_map_range (f : ℕ → Bond n) (hf : ∀ j, (f j).plus = (f (j + 1)).site) (r : ℕ) :
    IsPathFromTo (f 0).site ((List.range r).map f) (f r).site := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [List.range_succ, List.map_append]
    exact ih.append (by simpa using hf r)

/-- The condition of `Loop.closed` on the consecutive bonds `a, l, c`, in terms of paths. -/
theorem isPathFromTo_iff_zip (a c : Bond n) (l : List (Bond n)) :
    IsPathFromTo a.plus l c.site ↔ ∀ p ∈ (a :: l).zip (l ++ [c]), p.1.plus = p.2.site := by
  induction l generalizing a with
  | nil => simp
  | cons d l ih =>
    rw [isPathFromTo_cons, ih d, List.cons_append, List.zip_cons_cons, List.forall_mem_cons]
    exact and_congr_left' eq_comm

/-- A path from a site to itself is closed in the sense of `Loop.closed`: each bond ends where
the next one begins, and the last bond ends where the first one begins. -/
theorem IsPathFromTo.closed {x : Site n} {γ : List (Bond n)} (h : IsPathFromTo x γ x) :
    ∀ p ∈ γ.zip (γ.rotate 1), p.1.plus = p.2.site := by
  cases γ with
  | nil => simp
  | cons b l =>
    obtain ⟨rfl, hl⟩ := isPathFromTo_cons.1 h
    simpa using (isPathFromTo_iff_zip b b l).1 hl

/-! ### The inclusion of the coarse lattice in the fine lattice -/

/-- The inclusion of the coarse lattice maps the origin to the origin. -/
theorem scaleSite_zero (r : ℕ) : scaleSite r (0 : Site n) = 0 := by
  funext μ
  simp [scaleSite]

/-- The inclusion of the coarse lattice is additive if `n ≠ 0`. -/
theorem scaleSite_add [NeZero n] (r : ℕ) (x y : Site n) :
    scaleSite r (x + y) = scaleSite r x + scaleSite r y := by
  funext μ
  simp only [scaleSite, Pi.add_apply]
  rw [← Nat.cast_add, ZMod.natCast_eq_natCast_iff, ZMod.val_add, ← Nat.mul_add]
  simp [Nat.ModEq, Nat.mul_mod_mul_left]

/-- The inclusion of the coarse lattice commutes with negation if `n ≠ 0`. -/
theorem scaleSite_neg [NeZero n] (r : ℕ) (x : Site n) : scaleSite r (-x) = -scaleSite r x := by
  rw [eq_neg_iff_add_eq_zero, ← scaleSite_add, neg_add_cancel, scaleSite_zero]

/-- A unit vector of the coarse lattice is `r` unit vectors of the fine lattice. -/
theorem scaleSite_unit (r : ℕ) (μ : Fin 4) : scaleSite r (unit n μ) = r • unit (r * n) μ := by
  funext ν
  by_cases hν : ν = μ <;>
    simp [scaleSite, unit, hν, ZMod.val_one_eq_one_mod, ← Nat.mul_mod_mul_left]

/-- The image of the final site of a bond of the coarse lattice is `r` steps of the fine lattice
from the image of its initial site. -/
theorem scaleSite_plus [NeZero n] (r : ℕ) (b : Bond n) :
    scaleSite r b.plus =
      scaleSite r b.site + (if b.pos then (r : ℤ) else -(r : ℤ)) • unit (r * n) b.dir := by
  unfold Bond.plus
  split_ifs
  · rw [scaleSite_add, scaleSite_unit, natCast_zsmul]
  · rw [sub_eq_add_neg, scaleSite_add, scaleSite_neg, scaleSite_unit, neg_smul, natCast_zsmul]

/-! ### Reading a path on the finer lattice -/

/-- Reading the empty path on the finer lattice. -/
@[simp] theorem refinePath_nil (r : ℕ) : refinePath r ([] : List (Bond n)) = [] := rfl

/-- Reading a path on the finer lattice, bond by bond. -/
theorem refinePath_cons (r : ℕ) (b : Bond n) (γ : List (Bond n)) :
    refinePath r (b :: γ) = refineBond r b ++ refinePath r γ := rfl

/-- Reading a concatenation of paths on the finer lattice. -/
theorem refinePath_append (r : ℕ) (γ₁ γ₂ : List (Bond n)) :
    refinePath r (γ₁ ++ γ₂) = refinePath r γ₁ ++ refinePath r γ₂ :=
  List.flatMap_append

/-- For `r = 0` the refined path is empty. -/
@[simp] theorem refinePath_zero (γ : List (Bond n)) : refinePath 0 γ = [] := by
  simp [refinePath, refineBond]

/-- The bonds of `refineBond r b`, indexed by `j < r`: the definition. -/
theorem refineBond_eq_map (r : ℕ) (b : Bond n) :
    refineBond r b = (List.range r).map fun j : ℕ ↦
      ⟨scaleSite r b.site + (if b.pos then (j : ℤ) else -(j : ℤ)) • unit (r * n) b.dir,
        b.dir, b.pos⟩ :=
  rfl

/-- For `n ≠ 0`, a bond read on the finer lattice is a path from the image of its initial site
to the image of its final site. -/
theorem isPathFromTo_refineBond [NeZero n] (r : ℕ) (b : Bond n) :
    IsPathFromTo (scaleSite r b.site) (refineBond r b) (scaleSite r b.plus) := by
  have h := isPathFromTo_map_range (fun j : ℕ ↦ (⟨scaleSite r b.site +
    (if b.pos then (j : ℤ) else -(j : ℤ)) • unit (r * n) b.dir, b.dir, b.pos⟩ : Bond (r * n)))
    (fun j ↦ ?_) r
  · rw [refineBond_eq_map, scaleSite_plus]
    simpa only [Nat.cast_zero, neg_zero, ite_self, zero_smul, add_zero] using h
  · obtain ⟨x, μ, s⟩ := b
    cases s <;> simp only [Bond.plus, Bool.false_eq_true, ↓reduceIte] <;> push_cast <;> module

/-- For `n ≠ 0`, a path from `x` to `y` read on the finer lattice is a path from the image of
`x` to the image of `y`. -/
theorem IsPathFromTo.refinePath [NeZero n] (r : ℕ) {x y : Site n} {γ : List (Bond n)}
    (h : IsPathFromTo x γ y) : IsPathFromTo (scaleSite r x) (refinePath r γ) (scaleSite r y) := by
  induction γ generalizing x with
  | nil => exact congrArg (scaleSite r) h
  | cons b γ ih =>
    obtain ⟨rfl, hγ⟩ := isPathFromTo_cons.1 h
    rw [refinePath_cons]
    exact (isPathFromTo_refineBond r b).append (ih hγ)

/-! ### Loops -/

/-- A loop has a bond. -/
theorem Loop.bonds_ne_nil (C : Loop n) : C.bonds ≠ [] :=
  List.ne_nil_of_length_pos (lt_of_lt_of_le (by norm_num) C.three_le)

/-- The bonds of a loop are a path from its base point to its base point. -/
theorem Loop.isPathFromTo (C : Loop n) : IsPathFromTo C.base C.bonds C.base := by
  obtain ⟨bonds, h3, hc, hn⟩ := C
  cases bonds with
  | nil => simp at h3
  | cons b l =>
    change IsPathFromTo b.site (b :: l) b.site
    exact isPathFromTo_cons.2 ⟨rfl, (isPathFromTo_iff_zip b b l).2 (by simpa using hc)⟩

/-- For `n ≠ 0`, a loop read on the finer lattice is a path from the image of its base point to
itself. -/
theorem Loop.isPathFromTo_refinePath [NeZero n] (C : Loop n) (r : ℕ) :
    IsPathFromTo (scaleSite r C.base) (refinePath r C.bonds) (scaleSite r C.base) :=
  C.isPathFromTo.refinePath r

/-- For `n ≠ 0`, a loop read on the finer lattice is closed: each bond ends where the next one
begins, and the last bond ends where the first one begins. -/
theorem Loop.closed_refinePath [NeZero n] (C : Loop n) (r : ℕ) :
    ∀ p ∈ (refinePath r C.bonds).zip ((refinePath r C.bonds).rotate 1), p.1.plus = p.2.site :=
  (C.isPathFromTo_refinePath r).closed

/-! ### Gauge transformations -/

/-- The parallel transport along a concatenation of paths. -/
theorem hol_append (U : Config N n) (γ₁ γ₂ : List (Bond n)) :
    U.hol (γ₁ ++ γ₂) = U.hol γ₁ * U.hol γ₂ := by
  simp [Config.hol]

/-- A gauge transformation `u` multiplies the parallel transport along a path from `x` to `y` by
`u x` on the left and by `(u y)⁻¹` on the right. -/
theorem hol_gauge [NeZero n] (U : Config N n) (u : Site n → GLN) {x y : Site n}
    {γ : List (Bond n)} (h : IsPathFromTo x γ y) :
    (U.gauge u).hol γ = u x * U.hol γ * (u y)⁻¹ := by
  induction γ generalizing x with
  | nil => simp [Config.hol, isPathFromTo_nil.1 h]
  | cons b γ ih =>
    obtain ⟨rfl, hγ⟩ := isPathFromTo_cons.1 h
    have h' := ih hγ
    simp only [Config.hol, List.map_cons, List.prod_cons] at h' ⊢
    rw [h', Config.val_gauge]
    group

section GField

variable {G : GaugeGroup N}

/-- The action of a gauge transformation `u` on a gauge field with values in `G`:
`V^u_μ(x) = u(x) V_μ(x) u(x + e_μ)⁻¹`. -/
def GField.gauge (V : GField G n) (u : Site n → G.carrier) : GField G n :=
  fun μ x ↦ u x * V μ x * (u (x + unit n μ))⁻¹

/-- The configuration of a gauge transformed field is the gauge transform of its
configuration. -/
theorem GField.toConfig_gauge (V : GField G n) (u : Site n → G.carrier) :
    (V.gauge u).toConfig = V.toConfig.gauge fun x ↦ (u x : GLN) := rfl

/-- The parallel transport along the empty path is `1`. -/
@[simp] theorem GField.hol_nil (V : GField G n) : V.hol [] = 1 := rfl

/-- The parallel transport of a gauge field with values in `G` along a concatenation of
paths. -/
theorem GField.hol_append (V : GField G n) (γ₁ γ₂ : List (Bond n)) :
    V.hol (γ₁ ++ γ₂) = V.hol γ₁ * V.hol γ₂ :=
  Subtype.ext (WilsonLoop.hol_append V.toConfig γ₁ γ₂)

/-- A gauge transformation `u` multiplies the parallel transport of a gauge field with values in
`G` along a path from `x` to `y` by `u x` on the left and by `(u y)⁻¹` on the right. -/
theorem GField.hol_gauge [NeZero n] (V : GField G n) (u : Site n → G.carrier) {x y : Site n}
    {γ : List (Bond n)} (h : IsPathFromTo x γ y) :
    (V.gauge u).hol γ = u x * V.hol γ * (u y)⁻¹ :=
  Subtype.ext (WilsonLoop.hol_gauge V.toConfig (fun x ↦ (u x : GLN)) h)

/-- For `n ≠ 0`, a gauge transformation of the finer lattice conjugates the holonomy of a loop
by its value at the image of the base point. -/
theorem Loop.hol_gauge [NeZero n] (C : Loop n) (r : ℕ) (u : Site (r * n) → G.carrier)
    (V : GField G (r * n)) :
    C.hol r (V.gauge u) =
      u (scaleSite r C.base) * C.hol r V * (u (scaleSite r C.base))⁻¹ := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp [Loop.hol]
  · have : NeZero (r * n) := ⟨Nat.mul_ne_zero hr.ne' (NeZero.ne n)⟩
    exact GField.hol_gauge V u (C.isPathFromTo_refinePath r)

/-! ### Gauge invariance of the observables -/

/-- The character of a product does not depend on the order of the factors. -/
theorem Irrep.character_mul_comm (π : Irrep G) (a b : G.carrier) :
    π.character (a * b) = π.character (b * a) := by
  unfold Irrep.character ntr
  rw [map_mul, map_mul, Submonoid.coe_mul, Submonoid.coe_mul, Matrix.trace_mul_comm]

/-- Characters are class functions. -/
theorem Irrep.character_conj (π : Irrep G) (g x : G.carrier) :
    π.character (g * x * g⁻¹) = π.character x := by
  rw [π.character_mul_comm, inv_mul_cancel_left]

/-- For `n ≠ 0`, the observable of a loop ensemble is invariant under the gauge transformations
of the finer lattice. -/
theorem Ensemble.observable_gauge [NeZero n] (E : Ensemble n G) (r : ℕ)
    (u : Site (r * n) → G.carrier) (V : GField G (r * n)) :
    E.observable r (V.gauge u) = E.observable r V := by
  simp only [Ensemble.observable, Loop.hol_gauge, Irrep.character_conj]

/-! ### Independence of the first bond -/

/-- The same loop with its bonds rotated: `C.rotate k` begins with the bond of `C` which follows
its first `k` bonds, and `C.rotate 1` begins with the second bond of `C`. -/
def Loop.rotate (C : Loop n) (k : ℕ) : Loop n where
  bonds := C.bonds.rotate k
  three_le := by rw [List.length_rotate]; exact C.three_le
  closed p hp := by
    refine C.closed p ?_
    rwa [List.rotate_rotate, add_comm, ← List.rotate_rotate, List.zip,
      ← List.zipWith_rotate_distrib _ _ _ _ (List.length_rotate ..).symm, List.mem_rotate] at hp
  nodup := by
    rw [List.map_rotate]
    exact List.nodup_rotate.2 C.nodup

/-- The bonds of a rotated loop. -/
@[simp] theorem Loop.rotate_bonds (C : Loop n) (k : ℕ) :
    (C.rotate k).bonds = C.bonds.rotate k := rfl

/-- The character of the holonomy of a path of the coarse lattice, read on the finer lattice,
does not change when the bonds of the path are rotated. -/
theorem character_hol_refinePath_rotate (π : Irrep G) (r : ℕ) (V : GField G (r * n))
    (γ : List (Bond n)) (k : ℕ) :
    π.character (V.hol (refinePath r (γ.rotate k))) = π.character (V.hol (refinePath r γ)) := by
  rw [List.rotate_eq_drop_append_take_mod, refinePath_append, GField.hol_append,
    π.character_mul_comm, ← GField.hol_append, ← refinePath_append, List.take_append_drop]

/-- The character of the holonomy of a loop does not depend on which bond of the loop is the
first. -/
theorem Loop.character_hol_rotate (C : Loop n) (k : ℕ) (π : Irrep G) (r : ℕ)
    (V : GField G (r * n)) :
    π.character ((C.rotate k).hol r V) = π.character (C.hol r V) :=
  character_hol_refinePath_rotate π r V C.bonds k

end GField

/-! ### The hypothesis `n ≠ 0`

For `n = 0` the lattice is `ℤ⁴` and `ZMod.val` is the absolute value, so `scaleSite r` folds the
lattice and is not additive; `scaleSite_add` and `isPathFromTo_refineBond` fail. -/

example : ¬ ∀ x y : Site 0, scaleSite 1 (x + y) = scaleSite 1 x + scaleSite 1 y :=
  fun h ↦ absurd (congrFun (h (-unit 0 0) (unit 0 0)) 0) (by decide)

end WilsonLoop

end CoreLean
