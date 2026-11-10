# Triage of lf-p13b2-20261108-r15

## Verdict

- r15 was a full round of 13b2 (#4.561–#4.565-1, #4.567–#4.568, with #4.559–#4.560-0 as context) at LF db3245af7967, table 6d09b1b5054d, and labels 971e7d7d5325.
- **Fatal:** none. **Serious:** none.
- **Minor:** three.
  - m1: run B's VAR (19) bound, read in run A's blocks on T_{1.70}, costs L² in the field strength, which #4.565-1's 2C_act lacked.
  - m2: #4.517's "for ε₂ small" was not quantified, so (T-c) could not be checked to contain it.
  - m3: V′ meant VAR's data deviation in "V′V₀", and also the integration variables on Λ two lines earlier.
- **Trivial:** o2–o6. **Housekeeping:** LABELS and #T11.33, still with the table's owner.
- The round is not clean, so 13b2's clean count drops from 1 (13b r14) to 0.

## Repairs

| Finding | Line | Issue | Repair |
|---|---|---|---|
| m1 | #4.563-2.1, new #4.563-2.1-1, #4.563-3, new #4.563-3-1, #4.565-1 | Run B's move 3ε₂/a_j² is in its own indexing; in run A's blocks on T_{1.70} it is 3L²ε₂/a_j² | #4.563-2.1 now ends "…and the field strength by ≤ 3ε₂/a_j², in each run's own layers." #4.563-2.1-1: "On T_{1.70} run B's spacing is ≥ a_j/L at each point of run A's layer j (#4.5-2, #4.5-2-1), so in run A's indexing, in which d_y is read (#4.51-0), run B's move is ≤ 3L²ε₂/a_j², as in #4.364 and #4.508-0. The moved plaquette variable is YU^r(∂p) with abs(Y − 1) the move and abs(Y) ≤ 1 + 3ε₂ ≤ 2, so under either indexing the plaquettes of this Landau representative are ≤ c_plC₀^{ms}ε₁′/a_j², c_pl := 4 + 3L²B₅^c/C₀^{ms}." #4.563-3 now reads "action density per point of run A's layer j". #4.565-1 cites #4.563-3 for each run's density in run A's blocks. The enlarged c_pl carries this into C_act, C_dc(M) and #4.198-1, all constants of L and M |
| m2 | #4.517, #4.561-1.2, #4.561-1-2, #4.561.1-1.3-1.1 | "for ε₂ small" unquantified | #4.517: "so abs(log u) ≤ 4c_Gdε₂ when 2dε₂ ≤ r_G (table #T4.10), the exponents of the transported factors that fix u, along the contour and in the normalisation, then summing to ≤ 2dε₂, within the radius of the BCH series". (T-c) (#4.561-1.2) lists "#4.517's 2dε₂ ≤ r_G". #4.561-1-2 gives 2dε₂^{AL} ≤ r_G at the base 1. #4.561.1-1.3-1.1 cites the condition by name |
| m3 | #4.561.1 | V′ with two meanings | "…and V′ VAR's data deviation of (172), not the integration variables V′ on Λ (#4.559-1.1) or the minima V′^X₀." The rest of the line moves to the new #4.561.1-0.0, which keeps c_av's definition |
| o2 | #4.564 | The range #4.565–#4.568 is loose | "the Lemma gives the bounds of #4.565-1 and #4.566 per point of the history, Cauchy's estimate those of #4.567, and #4.568 absorbs them." |
| o3 | #4.561-1 | (173)'s inequality also needs B₃ ≥ 1 | "needs VAR's C₁ ≥ 1 and B₃ ≥ 1 (#T3.13)" |
| o4 | #4.563-2, #4.563-2.1 | The doubling 2C₀^{ms} → 4C₀^{ms} was unexplained | #4.563-2 keeps 2C₀^{ms}ε₁′/a_j², "under either indexing (#4.48.0-0, #4.7-2, #4.560-2)". #4.563-2.1's commutator term is 8C₀^{ms}ε₁′ (4 × 2C₀^{ms}). The 4 of c_pl is now derived: abs(Y) ≤ 2 times U^r's 2C₀^{ms} |
| o5 | new #4.563-3-1 | C_act's count was not written | "So a point carries at most ½d(d − 1) plaquettes of the spacing a_j, each ≤ (c_plC₀^{ms}ε₁′)², times the weight (g″)^{−2} ≤ 2g_{j(x)}^{−2} (#4.41-1-1), and d(d − 1) ≤ d². On T_{1.70} run B's plaquettes of the spacing a_j/L in such a point sum to the same bound in run A's field strength (#4.563-2.1-1), their number L^d cancelling the factor L^{−d} of the spacing." |
| o6 | #4.567, new #4.567-0 | Cauchy's supremum was not named | #4.567 ends "…on which (T-c) gives U″_k analytic." #4.567-0: "The supremum in Cauchy's estimate is given by the bounds of #4.563-2–#4.563-3-1, which use only U^r and (19) at ε₂, and Proposition 9 at C₁ = C_{V′} gives (19) at ε₂ on this whole domain." |

## Checks

- **m1, re-derived.**
  - **Spacings on T_{1.70}** (#4.5-2, #4.5-2-1). Ω^B_1 (spacing ε/L) extends to the distance M₁a_0 from Ω^c and lies where run A has its layer 0 (spacing a_0 = ε, to the distance M₁a_1). Ω^B_2 (spacing a_0) runs from M₁a_0 to 2M₁a_1, where run A has its layer 0 up to M₁a_1 and its layer 1 (spacing a_1 = La_0) beyond. So run B's spacing is ≥ 1/L times run A's at every point. Off T_{1.70} the layers coincide.
  - **The move.** VAR (19) for run B gives η_B abs(𝐇) < ε₂L^{−j} on run B's layer j, at the spacing a^B. Its field strength ≤ 3ε₂/(a^B)² ≤ 3L²ε₂/a_j² at run A's spacing a_j.
  - **#4.563-2.1's arithmetic.** The first-order term is ≤ 2ε₂L^{−2j}. The commutator term is ≤ 4 abs(U^r(∂p) − 1)η abs(𝐇) ≤ 4·2C₀^{ms}ε₁′ε₂L^{−3j}. The second order is ≤ 16ε₂²L^{−2j}. So the total is ≤ (2 + 8C₀^{ms}ε₁′ + 16ε₂)ε₂L^{−2j}, and this is ≤ 3ε₂L^{−2j} under (T-c)'s 16C₀^{ms}ε₁′ + 16ε₂ ≤ 1.
  - **The plaquette.** abs(YU^r(∂p) − 1) ≤ abs(Y) abs(U^r(∂p) − 1) + abs(Y − 1). This gives a field strength ≤ (2·2C₀^{ms}ε₁′ + 3L²ε₂)/a_j² = c_plC₀^{ms}ε₁′/a_j².
  - **The count.** A plaquette term is η^{d−4}(1 − Re tr X) ≤ η^{d−4}(η² abs(F))² = η^d abs(F)². Run B's L^d points of spacing a_j/L in a point of run A's layer j give L^d(a_j/L)^d abs(F)² = a_j^d abs(F)², as run A's own plaquettes do.
  - **Consumers.**
    - #4.565-1: d_y = a_y(U^A) − a_y^B(U^B) (#4.51-0), so it is ≤ 2C_act per point of run A's blocks.
    - #4.198-1 (line "The plaquettes are ≤ c_plC₀^{ms}ε₁′/a_j²"), per point of Λ at the scale k: the larger c_pl only weakens it.
    - #4.563-2.2's c_4 hypothesis uses each run's own layers, (4C₀^{ms}ε₁′ + 3ε₂)/a_j², and is unchanged.
    - Table row #T12.9-1 states c_pl := 4 + 3B₅^c/C₀^{ms}; the new value is sent to the table's owner.
- **m2.** The contour of B^j(y) has at most dL^j bonds, each with η abs(𝐇) ≤ ε₂L^{−j}, so its factors' exponents sum to ≤ dε₂. The normalisation R̄₀u^j = 1 adds at most as much, so ≤ 2dε₂ in all. Inside the radius r_G the BCH series converges, and 4c_Gdε₂ ≤ 1 keeps abs(log u) ≤ 4c_Gdε₂. #4.517's other uses (#4.198-0, #4.517's ū, ι's problem at ε₂^ι) run under (T-c) or at smaller ε₂.
- **o6.** #4.563-2–#4.563-3-1 use only U^r's real bound and VAR (19) at ε₂. Proposition 9 at C₁ = C_{V′} gives (19) at ε₂ = B₅^cε₁′ for all data with abs(V′ − 1) < C_{V′}ε₁′.
- **Line lengths.**
  - #4.561.1 285, #4.561.1-0.0 about 410, #4.561-1.2 620, #4.561-1-2 597, #4.563-2 486, #4.563-2.1 544, #4.563-2.1-1 476, #4.563-3 526, #4.563-3-1 404, #4.564 195, #4.565-1 294, #4.567 about 470 and #4.567-0 about 200 characters.
  - #4.517 (§4(d)) is 1,858 characters. It was already far over the limit, like 672 lines of the note, and it will be split in §4(d)'s packet.
- No CRLF. The new tags #4.561.1-0.0, #4.563-2.1-1, #4.563-3-1 and #4.567-0 were unused.

## Rounds

- 13b2: count 0. Next round on it: r16, narrow, on the lines changed here and their consumers, then a full r17.
- Order: 13a1 r11 (narrow; pre-check below), then 13b2 r16 (narrow), then 13a1 r12 (full), then 13b2 r17 (full).

## Pre-check of lf-p13a1-20261108-r11 (narrow)

- **Spec.** specs\spec_p13a1_r11.json, prior lf-p13a1-20261108-r10, extract #4.43–#4.50-2. The named steps are the lines changed since r10 (#4.44, #4.44-2-1, #4.46-0, #4.47, #4.47-0, #4.48-3, #4.48-3.0.0, #4.50 and #4.50-1.1.1-1), with their consumers #4.44-2, #4.46-0-1, #4.47-1, #4.48-3.1, #4.48-4 and #4.50-0. --check gives 0 conflicts (7 allowed).
- **Re-read.** I re-read every changed line. Two were reworded in the pass:
  - #4.46-0: "a factor depending on G";
  - #4.50: "≤ ε₁ (#4.43-1.2)". #4.43-1.2's C(M) ≥ 8(1 + κ_s)C_𝔛(M) and R_k ≥ 1 give C_𝔛(M)ε_k ≤ ε₁.
- **Re-checks.**
  - **VAR (172).** p.305 l.33–36: "abs(V′ − 1) < C₁ε₁, hence V′ = e^{iB′}, abs(B′) < 2C₁ε₁ on 𝔅_k, for ε₁ sufficiently small". Its C₁ is C₁′ here.
  - **The principal logarithm.** For hermitian B′ with abs(B′) < π, the principal logarithm of e^{iB′} is iB′, so 𝔛 = B′ ∈ 𝔤.
  - **#4.50-0.** 2C₁κ_Λε₁/(NC_Φ(M)) ≥ 2C_𝔛(M)ε₁ ≥ ‖𝔛‖_∞, by C₁ ≥ NC_𝔛(M)C_Φ(M)/κ_Λ.
  - **The weighted kernel (#4.47).** 15/16 ≥ ½, so it lies below #4.9-2-2's kernel.
- **Unchanged by this triage.** The repairs above touch no line of 13a1, and none of its lines cites c_pl, C_act, #4.517 or #4.561.1.
- **Size.** The extract is the whole part (about 21.8k characters), with the named steps under review and the rest as context.
- No known weak point and no OPEN is in these lines.

## SHAs

LF db3245af7967 (r15's snapshot) → 3ce883373224 (13a1 pre-check rewordings) → c178f72a210d (this triage's repairs). Table 6d09b1b5054d (unchanged).
