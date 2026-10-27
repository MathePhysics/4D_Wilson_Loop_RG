# D2.6 closure and D2 map: triage of round 29 (four reports read in full; repairs 25 Oct, finished 18:3x, date)

Round 29 had two parts:
- §4 of the D2.6 closure after the round-28 repairs (it1-d26-s4-20261025-r10);
- the merged map D2.4(12)–(13), never reviewed in its corrected form.

All ran on claude-opus-5-5 through the CLI route. No fatal item. Two serious items, both in the map (12cd S1, 13m S-A), repaired below. No new OPEN item.

## Packet failures and the split

The single map packet it1-d2-4s12m-20261025-r1 (494 KB, all of (12)–(13)) failed twice (r1, r1b): the reviewer used up its 128k output budget and the gateway refused a continuation (review.txt is 96 bytes). It was split into three packets, one part each (verification/isolated_reviewer/build_round29b_review_packets_20261025.py):
- it1-d2-4s12cd-20261025-r1 for (12)(c)–(d);
- it1-d2-4s12ef-20261025-r1 for (12)(e)–(f);
- it1-d2-4s13m-20261025-r1 for (12)(g) and (13).

All three returned complete reports.

## s4 r10 (§4, kind (γ))

Verdict: correct in substance and correctly labelled up to one minor residue; O6 and O3 open as stated. No fatal, no serious.

- m-1: the species of class (1) is written "of species att, lw or wrap(j) (class (1))" in 4.2's and 4.3's labels and in 4.5's body and label.
- m-2: §8 *For the user's review* now reads "kind-(γ) groups without an inherited att/lw/wrap member (touched or not), whose set lifts → att(k+1, coll); (ii) fails iff a component meets Ω_kᶜ or a traversal of I(𝒢) is not contained in Ω_k".
- Nits 1–9, all repaired:
  1. "M′ = 1 in the first": the condition is ε₁ ≤ a₁.
  2. (187)'s O(1) is logged as a reading of VAR's convention, p.291.
  3. "ε₂ ≤ B₅ε₁".
  4. (γ2) now uses a point p′ ∈ n′ ∩ Ω_kᶜ.
  5. "(2.1(c)–(d))".
  6. Class (1)'s O6 attribution is noted as conservative for members whose producing group depended on ω only through ω₀.
  7. §8 *Derived* is aligned with 4.3's label.
  8. ε_H ≤ 1 and ε_H ≤ C₁^{VAR}ε̄₁/(2c_V) were added to §8 *Conditions*.
  9. The wording of rule change (4) was corrected.

## Map (12)(c)–(d) (it1-d2-4s12cd-20261025-r1)

Verdict: no fatal; one serious item (S1); minors m1–m16.

- **S1** (Lemma (3), the covering lemma: "the union of the intervals of 𝒢_j and of the gaps … is a connected arc covered by ∪win(v)").
  - The defect: a group's members can be joined by a link whose arcs do not meet, so the union need not be one arc. If it is, the gap need not lie in the windows.
  - Repaired by a new arc rule in D2.2(6)(d), the **linked hull**:
    - The pieces are I(M) (the smallest arc containing M's slot arcs), the old intervals, and the member arcs J_{W′}.
    - The joined pairs are those of the three rules, plus incompatible members of one occurrence.
    - The linked hull is the pieces plus the shorter arc of each joined pair, enlarged to the ends of any old interval it cuts.
    - The group arc is the union of the classes' linked hulls, connected by overlaps.
  - With windows |win(v)| = |int(v)| + 40(diam_v + 1), where diam_v is the largest ℓ∞-distance from a support point to int(v), this gives I(𝒢) ⊂ ∪win(v) and length ≤ Σ_v|win(v)|.
  - The map's l.904–l.912 (*The arc hull*, *Norms*, *Arcs*) and (12)(c) were rewritten to match.
  - The constants were rederived:
    - n_{k+1}(M) ≤ 20M#(M) + 48(M/L)Σσ_k(W);
    - the sh(M) display;
    - sh(W) ≤ (ν_r/4)σ_k + (ν_e/8 + ν_e/L)ext_k + c_sh + c_πα|win(W)|;
    - c_sh := 2ν_f(16 + 10240/L + 41/M) + 2ν_e(2 + 41/M);
    - L₀ = 5000 is unchanged.
  - The new arc rule is a decision for the user (below).
- m1, m1′, m2: |win(v)| = |int(v)| + 40(diam_v + 1) with diam_v as above; #(v) is summed over the pieces.
- m3: Γ-vertex windows are the members' windows.
- m4: τ := ν_f/16, with the product split stated before 1 + x ≤ C_τe^{τx}.
- m5, m6: the extent parts were moved to the extent budget. sh(W)'s extent part is (ν_e/8 + ν_e/L)ext_k, and the total is (5/8 + 2/L)ν_e.
- m7: vacuum-link clusters are counted in the support. An M-vertex at Δ includes Δ ∈ supp 𝒞, as stated in (12)(f).
- m8: the third rule was added to the W-vertex description.
- m9: 𝒱(M) is a set of pairs (T, 𝒞).
- m10: the 2^s stays only in the sum over T.
- m11: "+ (the transport part)".
- m12: L ≥ 486 is explained by (10)(b) l.1454 (λ_L = L/2, δ = (1−2/L)/10), giving r = (L+2)κ/4.
- m13: C_box ≥ 4 gives ν_e ≤ ν/8. Stated at l.292, l.1531 and l.1549; closure §6.5 updated.
- m14: L ≥ 6 is now in the cube-share lemma.
- m15: (11)(c)(β)'s a′ factor e^{(ν_r/16)σ_k} is kept separate from the transports.
- m16: the evaluation point of an untouched W is stated.
- The transports condition is now c_πα_{1,k+1}·4096M ≤ ν.
- Old-W reserve: 7/8 used.

| Item | Share |
|---|---|
| sh | 1/4 |
| transports | 1/16 |
| b | 1/4 |
| windows | 1/8 |
| a | 1/16 |
| a′ | 1/16 |
| M share parts | 1/16 |

## Map (12)(e)–(f) (it1-d2-4s12ef-20261025-r1)

Verdict: no fatal, no serious; minors m1–m11.

- m1 ("L^{−1}(1+β₀)⁶ ≤ 1/8 by (1+β₀)⁸ < L" does not follow):
  - The recursion now uses ρ̃_k/ρ̃_{k+1} ≤ (1+β₀)⁸, ρ_k ≤ (1+β₀)⁶ρ_{k+1} and pl_k ≤ (1+β₀)pl_{k+1}.
  - So θ_k := L^{−1}(1+β₀)^{15} + (1+β₀)⁷[…].
  - The new condition 8(1+β₀)^{15} ≤ L holds for L ≥ 5000 and β₀ ≤ 1/2, which CRE allows (D2.2(6)(f) *L.*).
- m2 (double use of the reserved unit): two units per cube of M are reserved, one for (e)'s window decay and one for (13)(c)'s vacuum tail.
  - A cube of M∖D′ costs log 64 + log 2 + 2 + 1/8 + 23c + 142ν_f + 221ν_e ≤ 8 for ν ≤ 1/1000, against r/648 ≥ 8.
  - The π_k-cube cost was updated the same way.
  - r/648 ≥ 8 holds since r = (L+2)κ/4 ≥ 1250κ and κ ≥ κ_D′.
- m3: the interaction clause uses s(W′) := sh + b + (ν_r/8 + ν_r/16)σ.
  - a(W″) ≤ (ν_r/16)σ under ε̂ ≤ ν_r/(1296M).
  - (5.11) gives (ν_r/32)σ under ε̂ ≤ ν_r/(2592M).
- m4: the cube-position sums carry the box factor, so the root classes use ε̄^{old} := max(Lε^{old}_t, L⁴ε^{old}_c), and likewise ε̄^{ref,k}.
- m5: at k = 1 the c-version is (c4-6-5) with V3 L4608 ("the physical and reference data having the same numerical majorant"), checked against V3.
- m6: an M-vertex's positions include supp 𝒞 of its vacuum links (count paid by 𝒞's spare e^{#(𝒞)/4}).
- m7 ((T2)): the split is now e^{−ν_e#(G_M)}e^{−(κ_s−ν_e)#(G_M)} before (11)(d), under κ_s − ν_e ≥ κ_s^{(12)}. The bridges lie in the components (closure §5.2 (T1)).
- m8 ((T0)): n, b_n/ᾱ_n and K′ are defined. The re-run's ε^{new} is first order and serves (e)'s smallness only, not an amplitude.
- m9: the touched insertions are counted in two stages.
  - First, domains meeting a component: ≤ 81#(G_M) positions, ε̄^{old}. This fixes I(M).
  - Second, intervals in I(M): ≤ L·n_{k+1}(M) positions.
  - Total ≤ e^{(#(G_M)+#(M))/8}. The Σσ_k part of n_{k+1}(M) is charged to the first-stage W's b/2.
- m10: the share constant was renamed c_sh. The reference coefficient of the trivial group is written c_{{W}}. The closure's and map l.308's c_W is stated as c_W := c_sh.
- m11: the equality case q = p₀ of (R-m′) is dropped. It would need R-m's C_i chosen after κ_s and M (C_T ∝ e^{16κ_s}), which R-m doesn't give. (R-m′) is q > p₀ only, and the closure's equality-case phrases (§5.0, §5.2, §8) were removed.
- Also: "F(v) … = λb e^{b/2}" was changed to "≤", and the root-sum note was added (a bond of X(𝒢) off C costs a factor 16).

## Map (12)(g), (13) (it1-d2-4s13m-20261025-r1)

Verdict: (a), (b) and (d) are correct given (12), up to labels and conditions. (c) gives a correct single-step input for (Z-d) with G = 2, but is not a k-uniform induction. One serious item, S-A; minors m1–m12.

- **S-A** (the input/output weights of ε^{diff} do not match, and the Γ-vertex part of ε^{diff}_{k+1} is not produced). Repaired as the reviewer proposed:
  - ε^{diff}_k is the per-position sum, cubes included, with the full (ii-w) weight on the insertions and (S-w)'s weight on the step-k groups. It contains e^{sh+b} and the window and box spares up to e^{2c_sh}.
  - The Γ-vertices are bounded through the cluster level. This gives K₀ := (1 + 2e^{2c_sh+1})C_ve^{2c_sh} and ε̄^{diff}_k := L⁴K₀ε^{diff}_k.
  - The cluster level is run with FV Thm 5.4's split a = a°, d = ν_rσ + ν_e·ext + 2c_sh + 1. The KP check uses exactly (12)(f)'s weight times e^{2c_sh+1}, and gives Σ|ΔΦ°|e^{d} ≤ 2e^{2c_sh+1}δ_{k+1}.
  - The unweighted form (d = 0) stays (Z-d)'s input with G = 2.
  - D2.3(4)(Z-e)(I), (O) are restated in this per-position form.
  - (Z-h)(I)₁, (O)₁ are stated per position, with the full weights absorbed by e^{4η𝔰} as in (12)(b) *Base*.
- m1 (vacuum-tail threshold):
  - Non-embedding clusters have dependence diameter ≥ ι/4, hence support diameter ≥ ι/8 under (TC), and #(𝒞) ≥ ι/(8M).
  - So tail ≤ 36c#(M)e^{−ι/(32M)}, and c := min(c₁, 1/(32M)).
  - c_{k+1} = min(c₁, ν/(512M)) is unchanged for ν ≤ 16.
  - D2.3(4) l.1122, l.1126, l.1127 updated.
- m2: two marks give F₂ ≤ 6λλ′b·e^{3b/4}. This closes with T ≤ e^{b/2}, F ≤ λbe^{b/2} and be^{−b/4} ≤ 4/e. The reviewer's constant was 5; 6 is used.
- m3: δ_{k+1} is defined at every position, cubes included.
- m4: the second reserved unit (see 12ef m2).
- m5: ε^{new} + ε̄^{old} + ε̄^{ref,k} ≤ C″C_S′ρ_{k+1}pl_{k+1}. C⁎ := 4C_winC_vacC″C_S′, covering the Y and c parts.
- m6: the carry is fixed in the relative-amplitude form: per traversal L^{−1}(ρ̃_k/ρ̃_{k+1}) ≤ L^{−1}(1+β₀)⁸, times (1+β₀)⁷ from ρ_k·pl_k. So the coefficient is L^{−1}(1+β₀)^{15} ≤ 1/8, and C_rel^{(k+1)} ≤ ¼e^{−c(L−1)ι}C_rel^{(k)} + C⁎.
- m7 (labels):
  - "settled" was replaced by "proposed in SW closure §1–§3 (pl = 2; for review, not reviewed)".
  - "(R)(a) as restated" now reads "(7)(R) as restated in D2.3(4)".
  - "the polylog unless 2q₀ ≥ p₀ + q₁" now reads "the polylog of (11)(g), absorbed in pl = 1 + (log g_k^{−2})^{(q₁−q₀)₊}". The exponent p₀ + q₁ − 2q₀ ≤ q₁ − q₀ since q₀ ≥ p₀. The same change was made in the gaps block, l.170.
  - The gaps block's "C_KPτ_k²" now reads "C_KPρ_{k+1}·pl".
- m8 (conditions):
  - (12)(g) now refers to (13)(d)'s list.
  - (13)(d) lists κ_D′, L₀, 8(1+β₀)^{15} ≤ L, C_box ≥ 4A_E, κ_s^{(12)} (+ν_e under (T2)), M ≥ 100, c_πα·4096M ≤ ν, (8)'s condition, r/648 ≥ 8, (10)–(11) (972A ≤ δλ_Lκ, with 324A dropped as redundant; R-L3; 20c_πM‖a′‖_∞ ≤ 1 on (4)(e)'s arcs), ν ≤ 1/1000, R-m with (R-m′), (TC), η_w and g_K small.
  - "C_box ≥ 4A_E is its constraint here; the SW route uses C_box ≥ 6, for review".
- m9: the (13) heading now reads "(a)–(b) reviewed in an earlier form, no fatal finding; (c)–(d) for re-review".
- m10: (13)(a) uses V3's d_T (periodic ℓ∞ + 1_{i≠j}, V3 L1196, checked). So ext ≥ C_boxt − 2 and C_S := e^{2ν_e}C_S′. (12)(b) l.1531 was updated to match.
- m11: (5)'s and (6)'s C_new = C_gC_S·pl/c₀ (l.361, l.1378).
- m12: "b_W^Δ in place of b_W, proportional to sup|ΔY_W|/ᾱ" in (13)(c) and (Z-h).

## Closure edits made with the map repairs

- 5.2: |win(D)| = |int(D)| + 40(diam_D + 1) ≤ 82Mσ(D).
- 5.2 (T3): E′_𝒢 := Σ_v(|win(v)|/M + 2).
- 5.5: c_W := c_sh with the map's formula, and sh(W) ≤ (ν_r/4)σ_k + c_W for a fixed member.
- §6.5: ν_e ≤ ν/8.
- The equality-case phrases were removed from §5.0, §5.2, §5.6 and §8.
- §9.4: c_{{W}} = 0.

## Decisions for the user (new this round)

- The D2.2(6)(d) arc rule: the linked hull (above).
- L₀ = 5000 with κ_D′ (unchanged value, rederived).
- (R-m′) := q > p₀ only.
- The (T2) split before (11)(d).
- β₀ ≤ 1/2 (8(1+β₀)^{15} ≤ L).

## Next

Round 30: small re-review packets for the two serious repairs:
- S1: D2.2(6)(d) and (12)(c)–(d);
- S-A: (13)(c) with D2.3(4)(Z-e), (Z-h).

Hashes after the repairs:
- map 992851bd9993, 1614 lines;
- closure 0eaf3f9a4ba4, 177 lines;
- V4 b35c60e537b8, unchanged.
