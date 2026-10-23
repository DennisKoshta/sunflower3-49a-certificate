# sunflower3 certificate format (v1)

A certificate describes a periodic DEGKM gluing chain. It proves a lower bound on the Erdős–Szemerédi 3-sunflower-free
capacity μ₃ (Tao's table, constant 49a).

## File

Plain ASCII text with LF line endings. Lines starting with `#` are comments and may appear anywhere. Apart from
comments:

```
sunflower3 v1
block <n> <p> <q> <m>
<m lines, one member each>
block <n> <p> <q> <m>
<m lines>
...
```

- At least one block. Each block is a family of subsets of the ground set {0, …, n−1}, with 3 ≤ n ≤ 64.
  - `p` is the block's **in-port** and `q` its **out-port**. They are integers with 0 ≤ p, q < n and p ≠ q.
  - `m` is the number of members, and exactly `m` member lines follow.
- A member line lists the member's points as decimal integers in strictly increasing order, separated by single
  spaces, with no leading or trailing space. The empty set is written `-`.
- Tokens are decimal integers without signs or leading zeros (`0` itself is allowed). Anything else, including CR
  characters or trailing junk, makes the certificate invalid.

## Validity

Each block 𝓑 must satisfy:

1. **Distinct members.**
2. **Sperner:** no member is a proper subset of another.
3. **3-sunflower-free:** there are no three distinct members A, B, C with A∩B = A∩C = B∩C.
4. **Port counts.** Let N_ab = #{D ∈ 𝓑 : [p ∈ D] = a, [q ∈ D] = b} for a, b ∈ {0,1}. All four N_ab must be ≥ 1.

## Score

Each block i has the transfer matrix T_i = [[N₁₀, N₁₁], [N₀₀, N₀₁]] (row 0, then row 1). Let P = T₁T₂⋯T_k be the
product in file order, ρ its Perron root, and L = Σᵢ (nᵢ − 2) the number of points per period. Then

  **μ₃ ≥ ρ^{1/L}**,  where ρ = (tr P + √((P₀₀ − P₁₁)² + 4P₀₁P₁₀)) / 2.

A verifier should report ρ exactly, as a quadratic surd. It should compare ρ^{1/L} against a record ρ′^{1/L′} exactly
through ρ^{L′} vs ρ′^{L}, using rigorous rational enclosures of the surds or integer arithmetic. Floats are not
enough.

## Why this is a bound (the argument the verifier relies on)

**Gluing lemma** (Deuber–Erdős–Gunderson–Kostochka–Meyer 1997, Lemma 4.4). Let 𝓐 and 𝓑 be Sperner, 3-sunflower-free
families on disjoint ground sets X and Y, and let a ∈ X and b ∈ Y. Then

  𝓖 = {(C∖a) ∪ D : a ∈ C ∈ 𝓐, b ∉ D ∈ 𝓑} ∪ {C ∪ (D∖b) : a ∉ C ∈ 𝓐, b ∈ D ∈ 𝓑}

is Sperner and 3-sunflower-free on (X ∪ Y) ∖ {a, b}, and has |𝓐_a||𝓑_{b̄}| + |𝓐_{ā}||𝓑_b| members.

**Chain.** Repeat the blocks periodically (1, 2, …, k, 1, 2, …). R₁ is a copy of block 1, and R_{j+1} glues the
out-port of the last copy in R_j to the in-port of a fresh copy of the next block. Every R_j is Sperner and
sunflower-free.

Let (u_j, w_j) count the members of R_j that avoid and contain the current out-port. Then
(u_{j+1}, w_{j+1}) = (u_j, w_j)·T, where T is the next block's matrix, because members containing the out-port pair
with copy members avoiding the in-port. All T_i are positive, so every product of them is positive and so is
(u₁, w₁). Hence after t full periods |R| ≥ c·ρ^t for some c > 0, on L·t + O(1) points. Since f is nondecreasing and
lim f(n)^{1/n} exists, μ₃ ≥ ρ^{1/L}.

## Checking cost

The exhaustive check is cheap. For each member S, group the other members by their intersection with S. A sunflower
through S exists iff some group holds two members whose parts outside S are disjoint. This covers every triple. Sperner
and distinctness are pairwise checks.

## Reference values

| Certificate | Blocks (n, m) | ρ | Rate |
|---|---|---|---|
| Cla2026 F | (10, 75) | 20 + 2√66 | 1.5664286622… |
| Cla2026 F, H alternating | (10, 75), (11, 121) | 1042 + 2√261207 | 1.5666969787… |
| PR #237 B′ (open, unmerged) | (19, 4364), ports 0, 1 | 1127 + √925536 | 1.5678015201… |
