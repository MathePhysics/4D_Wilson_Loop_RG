# LF packet 12b, round 5 (full): triage

Review: verification/isolated_reviewer/reviews/lf-p12b-20261106-r5/review.md. Under review: LF d523fd2a521f (labels cbec9b3be3ca), table 1e392e405632.

## Verdict

No fatal or serious finding. There is one minor finding and one trivium, so r5 is not clean. All r4 findings are repaired (Q6). Every r5 finding was checked against the print and repaired in place.

## Repairs

- **Minor M1 (#3.70).** "Their bounds are those of (1.24) with ε_m replaced by α_{0,m} (p.190 l.7–37)" misdescribed the print. The spaces (1.64)–(1.69) run from p.190 l.13 to p.191 l.21. They bound seven quantities, with the coefficients 1 − βΣ_{i=h+1}^j2^{−|m−i|} − βΣ_{q=m+1}^k2^{−(q−m)} (p.190 l.25, and l.42 at m = j) and powers of L₀ that differ from (1.24)'s. The line is split, and the comparison is now derived on each domain of (1.24):
  - **#3.70** keeps the spaces, "modelled on (1.24)" (p.190 l.9–10), and CRE (2.28)'s C₀ and C₁, which #3.96-1-1 cites.
  - **#3.70-1.** The plaquette entry α_{0,m}η²(L^mη)^{−2} equals α_{0,m}(L^{k−m}η)² at η = L^{−k} (CRE p.276 l.7). Each coefficient is > 1 − 4β = ½, since the sum over i is < 3 and the sum over q is < 1. The space's power of L₀ is at least (1.24)'s on the same domain: L₀^{2max{0,m−k₀}} against L₀^{2max{0,m−k₀−1}}, and L₀^{2(j−m)} against L₀^{2(j−m−1)}. The domains match by (1.11)–(1.12): (Ω″_m∖Ω″_{m+1}) ∩ Z = Z″_{m+1}∖Z″_m for m > h, and Z″_{h+1} ∩ Ω_h for m = h (p.179 l.27–36).
  - **#3.70-2.** (1.24)'s coefficients are ≤ 3(1 − β/2) (p.182 l.13, with c = 3 at l.17). So the plaquette bound holds on the soft support once α_{0,m}/ε_m ≥ 6(1 + 2κ_s), which q₀ > p₀ (#T1.2) gives for γ small.
  - **#3.70-3.** A′ = 0 at real configurations, so the α_{1,m} bounds hold. The other bounds carry α_{0,m} with the same coefficient and power of L₀, or with that power and BCM ((1.65), (1.67), (1.69)).
- **Trivium t1 (#3.80-2).** (1.76) is itself the expression obtained by the integration over V_k⌈_Λ (p.193 l.44–p.194 l.3). The line now says that (1.99) is the density after that integration, whose integrals on the components satisfying (i), (ii) are those of (1.76) (p.200 l.44–50).
- **Referee's remark, outside the packet (Cauchy #C8.6.5).** The remark was right: the cutoff is on |B′|, not on |V′ − 1|. #C8.6.5 now reads "the soft form of the cutoff |B′| < M₀g_j^{−1}ε_j of LFR II p.356 l.37". The cutoff is at p.356 l.37, and t = M₀ε_j/g_j = M₀p₀(g_j).
- **Not findings, left unchanged.**
  - #3.94-1's |Λ^{(k)}| is the union bound over the bond b in {∃b : t ≤ |B′(b)| < s_bt}.
  - #3.78's κ_s < 1/44 is the exact condition for 22(1 + 2κ_s) < 23.

## Pre-check for lf-p12b-20261106-r6

- **Changed tags** (gate): #3.70, #3.70-1, #3.70-2, #3.70-3, and #3.80-2. Their lengths are 266, 532, 292, 459, and 394 characters.
- **Each claim checked against the print.** LFR I:
  - p.179 l.8–39 ((1.10)–(1.12));
  - p.181 l.25–52 and p.182 l.1–21 ((1.23), (1.24), c, and β);
  - p.190 in full and p.191 l.1–47 ((1.64)–(1.69) and the descending property);
  - p.193 l.38–46, p.194 l.1–10, p.200 l.44–55, and p.201 l.1–17 ((1.76) and (1.99)).
  CRE p.261 (the spaces of (2.34)–(2.39), for the role of 𝕁) and p.276 l.7 (η = L^{−k}). LFR II p.356 l.33–38 (the cutoff of #C8.6.5).
- **Inequalities.** On the soft support f < (1 + 2κ_s)T, and (1 + 2κ_s)·3(1 − β/2)L₀^aε_m ≤ ½L₀^bα_{0,m} holds for b ≥ a and α_{0,m}/ε_m ≥ 6(1 + 2κ_s). Both sides are strict, as in the print.
- **Consumers.**
  - #3.96-1-1 cites "CRE (2.28)'s C₁ of #3.70", which is still in #3.70.
  - No live note cites #3.70, #3.80-2, or #C8.6.5 elsewhere; the only other hits are labels, the handover, and old triage files.
  - The Cauchy labels are fixed at b7c584f0e065, and the C8.6.5 row is unchanged.
- **Table.** β = 1/8 is cited through #3.24, and q₀ > p₀ through #T1.2. No new symbol is introduced.
- **Size.** 20.9k (r5: 19.8k). The growth is #3.70's comparison, which is new mathematics. There are 0 definition conflicts.
- **Pins.** LF de345faea9a2 (labels 64cfa7e59c2a), table 1e392e405632, Cauchy 2ee116c1123f.
- **Spec.** spec_p12b_r6.json is a full round. Its claim (a) and Q1 now name #3.70–#3.70-3.
- **Status.** Built; awaiting the user's go.
