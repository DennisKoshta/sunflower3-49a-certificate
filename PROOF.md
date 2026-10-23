# Proof of μ₃ ≥ (64728 + √3018723123)^{1/26} = 1.5678599024…

Here μ₃ = lim f(n)^{1/n} is the 3-sunflower-free capacity (constant 49a in Tao's optimization-problems table), where
f(n) is the largest size of a 3-sunflower-free family of subsets of an n-set. A 3-sunflower is a triple of distinct
sets A, B, C with A∩B = A∩C = B∩C. A family is *valid* if it is Sperner and 3-sunflower-free.

The proof has three parts:
- the block 𝓑 (252,292 sets on 28 points, the certificate) is valid (§1–§4);
- chaining copies of 𝓑 gives valid families of size at least cρ^t on 26t+2 points (§5);
- the comparisons with the previous values (§6).

Validity of 𝓑 is proved twice. `check.c` (and, independently, `verify_independent.py`) checks every pair and triple
of the certificate exhaustively, with no lemma. `verify.py` checks the hypotheses of the argument in §3–§4. Either
check alone suffices.

## 1. Ingredients ([Cla2026])

- **F**: 75 sets on the 10 edges of K₅ (vertices 0,…,4): the 5 stars K₁,₄, the 10 graphs K₂,₃, and the 60 graphs
  whose complement is a chair.
- **H**: 121 sets on ℤ₁₁: the images of {0,…,6}, {0,1,2,3,4,6,7} and {0,1,2,6,9} under x ↦ ax+b, with a a nonzero
  square mod 11 and b ∈ ℤ₁₁. Of these sets, 46 avoid 0 and 75 contain it.

Both are valid; `verify.py` rebuilds them from these definitions and checks this by brute force. H has one further
property, also checked by `verify.py`:

> **(P)** the sets D ∖ {0}, D ∈ H, are nonempty and pairwise intersecting.

## 2. Gluing lemma ([DEGKM1997], Lemma 4.4)

Let 𝓐 and 𝓒 be valid families on disjoint ground sets X and Y, and let a ∈ X and b ∈ Y. Then

  glue(𝓐, a; 𝓒, b) = {(C∖a) ∪ D : a ∈ C ∈ 𝓐, b ∉ D ∈ 𝓒} ∪ {C ∪ (D∖b) : a ∉ C ∈ 𝓐, b ∈ D ∈ 𝓒}

is valid on (X ∪ Y) ∖ {a, b}, and has |𝓐_a|·|𝓒_{b̄}| + |𝓐_{ā}|·|𝓒_b| members.

## 3. The block

**Points.** The 28 points of the certificate are:

| index | point |
|---|---|
| 0–7 | the K₅ edges 01, 02, 12, 13, 14, 23, 24, 34 |
| 8–17 | the points 1,…,10 of a copy H₁ of H |
| 18–27 | the points 1,…,10 of a copy H₂ of H |

The edges e₁ = (0,3) and e₂ = (0,4) are used up by the gluing. The chain ports are p = 01 (point 0) and q = 02
(point 1).

**Pendant parts.** For an edge set C and a pendant Hᵢ glued at eᵢ, the possible Hᵢ-parts of C are:
- Q ∈ Hᵢ° = {D : D ∈ H, 0 ∉ D} (46 choices) if eᵢ ∈ C;
- Q ∈ Hᵢ¹ = {D∖{0} : D ∈ H, 0 ∈ D} (75 choices) if eᵢ ∉ C.

By (P), every possible Hᵢ-part is nonempty, and any two of them intersect.

**Members.** 𝓑 = 𝓟 ∪ 𝓐₁′ ∪ 𝓐₂′ ∪ 𝓦, where:

1. **𝓟, product sets** (250,659): (C ∖ {e₁, e₂}) ∪ Q₁ ∪ Q₂ for C ∈ F, with Q₁ and Q₂ chosen as above. This is
   glue(glue(F, e₁; H, 0), e₂; H, 0).
2. **𝓐₁′, additions at H₁** (806): (T ∖ e₂) ∪ Q₂ for T ∈ A₁, with Q₂ an H₂-part chosen according to whether e₂ ∈ T. The
   H₁-part is empty. The 15 edge sets of A₁ avoid e₁:
   ```
   01 02 04 12 13 14 23 | 01 04 13 23 24 | 01 02 12 13 14 23 24 | 02 04 12 13 14 23 24 | 02 04 12 13 34
   01 02 14 23 34 | 01 04 12 13 14 23 34 | 01 02 04 13 14 24 34 | 01 02 12 13 14 24 34 | 01 04 12 13 14 24 34
   01 02 04 12 23 24 34 | 01 02 12 13 23 24 34 | 01 04 12 14 23 24 34 | 02 04 12 14 23 24 34 | 02 04 13 14 23 24 34
   ```
3. **𝓐₂′, additions at H₂** (806): (T ∖ e₁) ∪ Q₁ for T ∈ A₂, with the roles of the pendants swapped. The 15 edge sets of
   A₂ avoid e₂:
   ```
   02 03 13 14 24 | 01 02 03 12 14 23 24 | 01 02 12 13 14 23 24 | 01 03 12 13 14 23 24 | 01 02 03 12 13 14 34
   01 02 14 23 34 | 01 03 12 13 14 23 34 | 02 03 12 13 14 23 34 | 01 03 12 24 34 | 01 02 12 13 14 24 34
   01 02 03 13 23 24 34 | 01 02 12 13 23 24 34 | 02 03 12 13 23 24 34 | 02 03 12 14 23 24 34 | 01 03 13 14 23 24 34
   ```
4. **𝓦, 21 further sets.**
   - 20 sets inside H₁, with no edge and no H₂ point (points of ℤ₁₁):
     ```
     1 2 3 5 6 8 | 2 3 4 6 7 9 | 1 2 3 4 5 7 8 9 | 1 2 4 5 6 7 8 9 | 1 3 4 5 6 7 8 9 | 1 2 3 4 5 6 7 10
     3 4 5 7 8 10 | 1 2 3 4 6 7 8 10 | 1 2 4 5 6 7 8 10 | 1 2 3 4 5 6 9 10 | 1 2 3 4 5 7 9 10 | 1 5 6 7 9 10
     1 2 4 8 9 10 | 1 3 4 5 6 8 9 10 | 2 3 4 5 6 8 9 10 | 1 2 3 5 7 8 9 10 | 1 2 3 6 7 8 9 10 | 1 3 4 6 7 8 9 10
     2 3 5 6 7 8 9 10 | 2 4 5 6 7 8 9 10
     ```
   - the set {12, 14, 23} ∪ H₂: three edges and all ten points of H₂, with an empty H₁-part.

   No set of 𝓦 contains p or q.

Total: 250,659 + 806 + 806 + 21 = 252,292. `verify.py` rebuilds 𝓑 from this description and checks that it equals
the certificate's block as a set.

## 4. Validity of 𝓑

### Lemma A (adding sets with an empty pendant part)

Let Z and Y be disjoint ground sets, and let 𝓖 = 𝓖₁ ∪ 𝓖₀ be a family on Z ∪ Y such that:

1. every member of 𝓖₁ has a nonempty Y-part, and the Y-parts of any two members of 𝓖₁ intersect;
2. every member of 𝓖₀ lies inside Z;
3. 𝓖₁ and 𝓖₀ are each valid;
4. no member of 𝓖₀ is contained in a member of 𝓖₁;
5. there is no 3-sunflower {G, T₁, T₂} with G ∈ 𝓖₁ and T₁, T₂ ∈ 𝓖₀.

Then 𝓖 is valid.

*Proof.*
- *Sperner.* A member of 𝓖₁ is never inside a member of 𝓖₀, because its Y-part is nonempty. The reverse is excluded
  by condition 4, and pairs inside 𝓖₁ or inside 𝓖₀ by condition 3.
- *No 3-sunflower.*
  - Triples inside 𝓖₁ or inside 𝓖₀ are excluded by condition 3.
  - Triples with exactly one member of 𝓖₁ are excluded by condition 5.
  - Take G, G′ ∈ 𝓖₁ and T ∈ 𝓖₀. Then G ∩ G′ meets Y, but G ∩ T does not, so G ∩ G′ ≠ G ∩ T. ∎

### One pendant

Let K be valid on X with x ∈ X, and let P be valid with root r, such that the sets D ∖ r (D ∈ P) are nonempty and
pairwise intersecting. Let 𝓖₁ = glue(K, x; P, r), valid by §2, and let Y be P's points other than r. Write

  K′ = {C ∖ x : x ∈ C ∈ K} ∪ {C : x ∉ C ∈ K}.

Every member of 𝓖₁ is C′ ∪ Q with C′ ∈ K′ and ∅ ≠ Q ⊆ Y, and condition 1 of Lemma A holds. Let A be a family on X∖x
(so Z = X∖x). For T ⊆ Z we have T ⊆ C′ ∪ Q iff T ⊆ C′, and (C′ ∪ Q) ∩ T = C′ ∩ T. So conditions 3–5 for 𝓖₀ = A
become **core-level conditions**:

- (a) A is valid;
- (b) no T ∈ A lies inside a member of K′;
- (c) there is no C′ ∈ K′ and T₁ ≠ T₂ ∈ A with C′ ∩ T₁ = C′ ∩ T₂ = T₁ ∩ T₂.

If (a)–(c) hold, then glue(K, x; P, r) ∪ A is valid. `verify.py` checks (a)–(c) for K = F with A = A₁ at x = e₁, and
with A = A₂ at x = e₂.

### Two pendants

**Claim.** 𝓑₀ = 𝓟 ∪ 𝓐₁′ ∪ 𝓐₂′ is valid.

*Proof.* Apply Lemma A with Y = H₁'s points, 𝓖₀ = 𝓐₁′ and 𝓖₁ = 𝓟 ∪ 𝓐₂′.

- **𝓖₁ is valid.** By the one-pendant case at e₂, F ⊗ H₂ ∪ A₂ is valid, where F ⊗ H₂ = glue(F, e₂; H, 0). Every
  member of this family is a set of edges other than e₂, together with H₂ points. Gluing H₁ at e₁ gives exactly
  𝓟 ∪ 𝓐₂′, which is valid by §2.
- **Condition 1.** Every member of 𝓖₁ has an H₁-part as in §3. By (P), that part is nonempty, and any two such parts
  intersect.
- **Condition 2.** Members of 𝓐₁′ have an empty H₁-part.
- **𝓖₀ is valid, and conditions 4–5 hold against 𝓟.** By the one-pendant case at e₁, F ⊗ H₁ ∪ A₁ is valid.
  Gluing H₂ at e₂ gives 𝓟 ∪ 𝓐₁′, which is valid by §2. It contains 𝓖₀ and every triple and pair used in conditions 4
  and 5 with G ∈ 𝓟.
- **Conditions 4–5 against X ∈ 𝓐₂′.** X has an empty H₂-part. Members T, T′ of 𝓐₁′ have nonempty H₂-parts, and any
  two of them intersect, by (P).
  - T ⊄ X, so condition 4 holds.
  - T ∩ T′ meets H₂ but X ∩ T does not, so X ∩ T ≠ T ∩ T′, and condition 5 holds. ∎

The same induction, with Lemma A applied at one pendant at a time, handles any number of pendants hung at distinct
points of K, each with the property of (P).

### The 21 further sets

𝓑 = 𝓑₀ ∪ 𝓦, and 𝓑₀ is valid. So 𝓑 is valid iff every pair and every triple of distinct members of 𝓑 that involves a
member of 𝓦 is neither a containment nor a 3-sunflower. `verify.py --pure --extra` checks exactly this,
exhaustively, against the whole block. It needs no lemma. For the triples it buckets the members by their
intersection with each set of 𝓦.

## 5. Chain count

Let N_ab = #{B ∈ 𝓑 : [p ∈ B] = a, [q ∈ B] = b}:

| | N₀₀ | N₀₁ = N₁₀ | N₁₁ |
|---|---|---|---|
| product sets 𝓟 | 33948 | 64360 | 87991 |
| additions at H₁ (𝓐₁′) | 0 | 184 | 438 |
| additions at H₂ (𝓐₂′) | 0 | 184 | 438 |
| 20 sets inside H₁ | 20 | 0 | 0 |
| {12, 14, 23} ∪ H₂ | 1 | 0 | 0 |
| **𝓑** | **33969** | **64728** | **88867** |

**The chain.** R₁ is a copy of 𝓑. R_{t+1} = glue(R_t, q_t; 𝓑_{t+1}, p), where 𝓑_{t+1} is a fresh copy of 𝓑 and q_t
is the out-port q of the last copy in R_t. By §2 every R_t is valid. R_t has 26t + 2 points.

**The count.** Let u_t and w_t count the members of R_t that avoid and that contain q_t. Members of R_t containing
q_t pair with copy members avoiding p, and members avoiding q_t pair with copy members containing p. Hence

  (u_{t+1}, w_{t+1}) = (u_t, w_t) · T,  T = [[N₁₀, N₁₁], [N₀₀, N₀₁]] = [[64728, 88867], [33969, 64728]],

with (u₁, w₁) = (N₀₀ + N₁₀, N₀₁ + N₁₁).

**The bound.** T is positive, with Perron root ρ = 64728 + √(88867·33969) = 64728 + √3018723123 ≈ 119670.9078. The
start vector (u₁, w₁) is positive, so |R_t| = u_t + w_t ≥ c·ρ^t for some c > 0. Hence f(26t+2) ≥ c·ρ^t. Since the
limit defining μ₃ exists,

  **μ₃ ≥ ρ^{1/26} = (64728 + √3018723123)^{1/26} = 1.5678599024…**

## 6. Exact comparisons (integer arithmetic; `verify.py` checks each one)

Since ⌊√3018723123⌋ = 54942, we have ρ > 119670.

- **Against PR #237** [Syl2026], with 17 points per period. ρ′ = 1127 + √925536 < 1127 + 963 = 2090. The claim
  ρ^{1/26} > ρ′^{1/17} is equivalent to ρ^{17} > ρ′^{26}. This follows from 119670^{17} > 2090^{26}, an inequality
  between two 87-digit integers.
- **Against [Cla2026]**, with 17 points per period. ρ″ = 1042 + 2√261207 = 1042 + √1044828 < 1042 + 1023 = 2065,
  and 119670^{17} > 2065^{26}.
- **Ten digits.** Let L = 64728·10⁶ + ⌊√(3018723123·10¹²)⌋ = 119670907849. Then L/10⁶ < ρ < (L+1)/10⁶. Also
  15678599024^{26}·10⁶ < L·10^{260} and 15678599025^{26}·10⁶ > (L+1)·10^{260}. Hence
  1.5678599024 < ρ^{1/26} < 1.5678599025.

## References

- [DEGKM1997] W. Deuber, P. Erdős, D. S. Gunderson, A. V. Kostochka, A. G. Meyer, *Intersection statements for
  systems of sets*, J. Combin. Theory Ser. A 79 (1997), 118–132. Lemma 4.4.
- [IRSI2026] the exact 2×2 transfer-matrix count of the chain, https://github.com/Aspect5/sunflower-free-capacity.
- [Cla2026] the families F and H, https://github.com/joshua17-create/sunflower-lower-bound.
- [Syl2026] / PR #237 (https://github.com/teorth/optimizationproblems/pull/237), Sylla: gluing H to F as a pendant,
  and augmenting with sets whose pendant part is empty, https://github.com/xSyllaa/sunflower-pendant-chain.
