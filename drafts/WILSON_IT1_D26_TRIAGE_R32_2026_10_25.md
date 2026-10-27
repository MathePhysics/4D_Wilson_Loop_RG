# D2 map: triage of round 32

Review read in full: it1-d2-4s12s1-20261025-r4 (S1: D2.2(6)(d), D2.4(12)(c)–(d)).

Verdict: the S1 repair is correct and sufficient, with no fatal or serious items. N-1, m-a and m-b are repaired. All constants of (12)(d) check.

User decision recorded: β₀ ≤ 1/2 is accepted. CRE (2.6), p.255, allows it: "β₀ > 0 can be chosen arbitrarily small, if g is sufficiently small". The map now says "accepted by the user" at (12)(f) and (13)(d).

User decision recorded: L ≥ L₀ = 5000 is accepted. It is the lower bound of (12)(d), where (1106·17/16 + 41/8)/L₀ ≤ 1/4. The map now says "accepted by the user" at (12)(d), (12)(g) and (13)(d). κ ≥ κ_D′ remains for the user's review.

## Items

- **m-c (UNCLEAR, predates round 31): the domain of 𝒢 and the vacuum links.** The reviewer offered two outcomes:
  - the vacuum-link factors are scalars given ℓ; or
  - they are field-dependent, and then a further merging rule is needed.

  The second holds. D2.2(6)(c) defines δΨ(M) and δΨ_≥(T) as the field-dependent parts, which vanish only at (1, 0, 0). Only Q° and Q_k(𝔅) are numbers.

  Checking this also exposed a locality gap. Unexpanded, e^{−δΨ(M)} and e^{x_T} − 1 depend on the fields on every cluster incompatible with M. Cov(k) asks for a function of the fields on a domain X_W (l.622).

  Repairs:
  - **D2.2(6)(c) *Localisation* (new, exact).**
    - Put y_𝒞 := φ^T(𝒞; 𝐔, 𝐉, ω′) − φ^T(𝒞; 1, 0, 0). Expand e^{−δΨ(M)} = Σ_𝒦∏(e^{−y_𝒞} − 1) and e^{ε_TδΨ_≥(T)} − 1 = Σ_{𝒦≠∅}∏(e^{ε_Ty_𝒞} − 1), over finite sets of clusters.
    - Each term is local, because RG2 p.14 says "The function H(Z) is localized in the interior of Z with respect to the external gauge fields". y_𝒞 is invariant by (b5).
    - The chosen clusters are the vacuum links. Those of δΨ(M) sit at M (T = {M}); those of a scalar link sit at the first M of T. A cluster chosen by several factors is one link.
  - **D2.2(6)(d), new vacuum-link rule.** Merge two groups when a vacuum link of one is incompatible with a marked polymer or a vacuum link of the other.
    - Old insertions against vacuum links are the second rule's case.
    - Members of old occurrences are old insertions of their group, by the third rule.
    - The rule is added to the joined pairs and to the class-form compatibility list.
    - The domain of 𝒢 is defined as the union of its marked polymers' domains, its vacuum links' supports and its old insertions' domains, touched or not. The occurrence factors are scalars.
  - **D2.4(12)(c).**
    - 𝒱(M) includes the self-energy links (T = {M}).
    - Lemma (3) states that the touched-W second-rule pair and the vacuum-link pairs are (ii) pairs, since X_{W₀} and supp 𝒞 lie in supp v_M. This also covers n-1.
    - *The vacuum factors* is redone in the expanded form:
      - a cluster is chosen by n_𝒞 ≤ 2^s factors, and the sum over the nonempty choices is ≤ n_𝒞u_𝒞e^{n_𝒞u_𝒞};
      - the factors e^{nu}e^{|y|} are bounded per M by e^{5c#(M)}, using 4e^{2c} ≤ 5 with c = (9/64)e^{−4κ};
      - the flat factors become e^{6c#(M)} (e^{c#(M)} from Ψ°);
      - each cluster keeps the weight 2|φ^T|_sup with the 2^s choice.
  - **(12)(f).**
    - The cube cost has 24c, with 143ν_f per n-3. The first bound is ≤ 8: 6.977 + 0.143 + 0.221 + 24c.
    - κ_s^{(12)} = 80c_Dr + 324c_D(L⁴log2 + 9) + 16 still dominates, since 4(log 128 + 2.125 + 0.364 + 24c) < 36.
  - **Closure, line 66.**
    - The flat budget is e^{6c#(M)} → e^{11c#(M)}.
    - The clusters of δΨ(M) not meeting the collar are (12)(c)'s vacuum links.
- **n-1.** Covered by the Lemma (3) note above.
- **n-2.** Packet artefact. No change.
- **n-3.** 142ν_f → 143ν_f in both cube costs of (12)(f).

Line counts are unchanged: map 1614, closure 177. V4 b35c60e537b8 is unchanged.

## Next

Round 33 reviews the m-c repair as one packet, it1-d2-4s12mc-20261025-r1. It carries D2.2(6)(c)–(d) and D2.4(12)(c), with D2.4(2)(e)–(g) as context.
