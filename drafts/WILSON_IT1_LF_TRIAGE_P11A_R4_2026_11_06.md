# Packet 11a r4 Triage (LF #0.17 and #4.1–#4.9-3)

Review: verification/isolated_reviewer/reviews/lf-p11a-20261106-r4/review.md (full round of part 11a), on LF 218183a287fc, labels 4b2d2037cc39, and table e02c753f1f9d.

## Verdict

r4 has no fatal or serious finding, one minor finding, m-A, and two trivial findings, t-A and t-B. So it is **not clean**. r3's m-1 and trivial points are resolved; the earlier findings remain resolved.

## Repairs

| Finding | Lines | Repair |
|---|---|---|
| m-A | #4.7-1-4-1, #4.7-1-4-1-1 | Bałaban uses 𝐁₁ also at its own data at U_{k,Λ}, the base of LFR II (1.57) (p.371 l.36–37, #4.546). There the 𝐁₁ minimiser is U_{k,Λ} = U_k(V″⌈_{Λ^c}, V_Λ^{(A)}) of (1.56), whose determining set has the whole lattice as its bottom domain (#4.7-1-4); so on 𝐁₁'s bottom strip it has the bounds of #4.7-2 in the units a_j ≥ a_0 of its own layers, hence at a_0. "only through" became "at the data of (1.53)", and #4.7-1-4-1-1's first sentence is restricted to those data. |
| t-A | #4.7-1-4-3 | "there the covering is run A's" now reads "there run B's own covering applies, its layers being run A's". |
| t-B | new #4.7-1-4-2-1 | The sums of at most 2d second differences in ∂*∂A and ΔA (VAR (10), PBG (3.36)) are within 2d times the bound for m = 2, at the pinned strips and on T_{1.70}. No line claims them within C₀ or C₀^{ms}. |
| 6c₀^d | #4.9-1-1 | No change: valid, and Bałaban's printed form of (2.58). |
| Ũ, a_j (definition check) | #4.5-2-1, #4.6, #4.7, #4.59, #4.595, #5.1, #5.30 | Ũ := MU^B is defined once, at its first use #4.5-2-1 (run B's configuration blocked to run A's lattice); #4.7, #4.59, #4.595, and #5.30 cite it. a_j = εL^j is table row #T2.3, cited at #4.6 and #5.1. |

## Pre-check

- **m-A source.** LFR II p.371 l.36–37 (corrected file): U_1 = U_{𝐁₁}(V″⌈_{Λ^c}, M^k(U_{k,Λ})⌈_{Λ∩Ω″_k}, (M^·(U_{k,Λ}))^{−1}M^·(U_{k,Λ})⌈_{Z″_k}) = (exp iη𝐇_{𝐁₁}(−(1/i)log M^·(U_{k,Λ})⌈_{Z″_k})U_{k,Λ})^{u_1^{−1}}, with U_{k,Λ} = U_k(V″⌈_{Λ^c}, V_Λ^{(A)}) of (1.56) (l.28–30). At the base the datum on Z″_k is M^·(U_{k,Λ}), not 1.
- **Inverse powers.** The bounds of #4.7-2 are C₀^{ms}ε₁ times a_j^{−1}, a_j^{−2}, a_j^{−3}; a_j ≥ a_0 gives them at a_0.
- **t-B.** ∂*∂A has 2(d − 1) second differences per bond and ΔA has d per site, both ≤ 2d. The operative regularity of (b) is (9.2) (F, ∇F, A); PBG (3.36) carries an unspecified O(1).
- **Definition check.** build_packet.py now refuses a part whose symbols are defined again in the LF, in balaban_proofs/, or in a table row; 11a passes with 0 conflicts. The remaining LF repeats (97 symbols) belong to later packets.
- **Lines.** #4.5-2-1, #4.7-1-4-1, and #4.7-1-4-3 split at sentence boundaries (new #4.5-2-1-1, #4.7-1-4-1-0, #4.7-1-4-3-0); every line of the part is ≤ 613 characters. CR 0; no duplicate line tags; every citation resolves.

## Repaired files

LF a4bf700750d6, table e02c753f1f9d, labels 9d999873d0aa.
