# A two-pendant augmented base family for the 3-sunflower-free capacity

**Claim.** μ₃ ≥ (64728 + √3018723123)^{1/26} = 1.5678599024…

Here μ₃ is the Erdős–Szemerédi 3-sunflower-free capacity, constant 49a in
[Tao's optimization-problems table](https://teorth.github.io/optimizationproblems/constants/49a.html). The bound is
the limit of a gluing chain of copies of one block. The block is a Sperner, 3-sunflower-free family of 252,292 sets
on 28 points, with port counts N₀₀ = 33969, N₀₁ = N₁₀ = 64728, N₁₁ = 88867. Its transfer matrix
[[64728, 88867], [33969, 64728]] has Perron root ρ = 64728 + √(88867·33969), and each copy adds 26 points.

The bound improves the listed value (1042 + 2√261207)^{1/17} = 1.5666969787… [Cla2026], and the value
(1127 + √925536)^{1/17} = 1.5678015201… proposed in
[PR #237](https://github.com/teorth/optimizationproblems/pull/237).

## Files

| file | content |
|---|---|
| `two_pendant_extra_1.5678599.txt.xz` | the certificate: the block, in the format of `FORMAT.md` |
| `FORMAT.md` | the certificate format, and why a valid certificate proves the bound |
| `PROOF.md` | the construction, the augmentation lemma (Lemma A) and its two-pendant induction, the chain count, and the exact comparisons |
| `check.c` | exhaustive Sperner and 3-sunflower checker in C; it uses no lemma |
| `verify.py` | standard-library Python 3. It rebuilds the block from the construction in `PROOF.md`, checks the hypotheses of the proof, checks every pair and triple through the 21 sets not covered by Lemma A, and proves the comparisons with integer arithmetic |
| `verify_independent.py` | a second exhaustive checker, written by a separate agent from `FORMAT.md` alone |
| `SHA256SUMS` | hashes of all files, and of the uncompressed certificate |

## How to reproduce

```
xz -dk two_pendant_extra_1.5678599.txt.xz          # keeps the .xz; writes two_pendant_extra_1.5678599.txt
sha256sum -c SHA256SUMS                            # the .txt line is 10ee18f93204468f3611d2c909a9eee443f3b4769cf7fddd964209edfebd4838

cc -O2 check.c -o check                            # add -fopenmp to use several threads
xz -dc two_pendant_extra_1.5678599.txt.xz | ./check
# prints the port counts, then "OK 252292" and "ALL BLOCKS OK" (about 15 min on 2 threads)

python3 verify.py two_pendant_extra_1.5678599.txt.xz --pure --extra
# standard library only; ends with "ALL CHECKS PASS" (about 20 s)

python3 verify_independent.py two_pendant_extra_1.5678599.txt
# needs Python >= 3.10 with numpy, numba and mpmath; reads the uncompressed file; prints VALID and the rate (about 11 min)
```

Validity of the block is the only fact the bound needs, and either `check.c` or `verify_independent.py` establishes
it on its own. `verify.py` establishes it from the proof in `PROOF.md`. The chain argument is in `FORMAT.md` and in
`PROOF.md`, §5.

## Credits

- Deuber, Erdős, Gunderson, Kostochka and Meyer [DEGKM1997], for the gluing lemma (Lemma 4.4).
- [IRSI2026] (https://github.com/Aspect5/sunflower-free-capacity), for the gluing chain and its exact 2×2
  transfer-matrix count.
- [Cla2026] (https://github.com/joshua17-create/sunflower-lower-bound), for the families F (75 sets on the edges of
  K₅) and H (121 sets on ℤ₁₁).
- [PR #237](https://github.com/teorth/optimizationproblems/pull/237)
  (https://github.com/xSyllaa/sunflower-pendant-chain), for gluing H to F as a pendant, and for the idea of
  augmenting with sets whose pendant part is empty. This construction applies that idea at two pendants at once,
  and inside a pendant.
- T. Tao and contributors, for the table.

## Disclosure (AI use)

This result was found and prepared with Claude (Anthropic, Claude Opus 5.5), directed by Dennis Koshta, who takes
responsibility for it. That covers the computer search over augmented multi-pendant gluings of the [Cla2026]
families, the certificate, the checkers, and the text. A second Claude agent checked the certificate exhaustively
with its own checker (`verify_independent.py`). It wrote that checker from the certificate format specification
only, without access to the construction code. The result is not peer-reviewed, and no human mathematician has
checked the argument.

## Licence

MIT; see `LICENSE`.
