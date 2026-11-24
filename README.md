# New lower bounds on the Shannon capacity of C7 and C13

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24517880.svg)](https://doi.org/10.5281/zenodo.24517880)

| Graph | Previous best | New lower bound | Dimension |
|---|---|---|---|
| $C_7$ | 3.2588387054 (L. Tang, 2026) | **3.2588405877** | 700 |
| $C_{13}$ | 6.3029270716 (G. Long, 2026) | **6.3029303591** | 522 |

Each bound comes from an explicit independent set in a strong power $C_n^{\boxtimes d}$ of exact size $M$, so that $\Theta(C_n) \ge M^{1/d}$. Two words of $\mathbb{Z}_n^d$ are confusable if they differ by at most 1 (mod $n$) in every coordinate.

## Method

### Framework

The constructions use the seven-family framework of Buys, Polak and Zuiddam (BPZ).

- **Seven-family representation.** This is a tuple of seven independent sets labeled B, N, A, D, O, H, V. A fixed list of eleven label pairs must be *separated*: no word of one set is confusable with a word of the other.
- **Combining representations.** Admissible rules combine several representations into a new one, and a terminal code, a set of pairwise separated label words, turns representations into an independent set. The size of that set is a sum of products of family sizes.
- **Gao gadgets.** A Gao gadget (Y. Gao) is an independent set with private pairs, two transversals and an auxiliary set. Gao's product combines two gadgets into a larger one.
- **Heterogeneous products.** R. Tandon showed that the three side codebooks of the product may be chosen freely, as long as they are independent. The size of the product depends on them only through two exact counts, $j$ and $q$.

### $C_7$

We start from L. Tang's construction (dimension 680) and change it in three ways.

1. **Flat label codes as side codebooks.** Earlier constructions use images of main codes of pure Gao products as side codebooks. We use instead codes built directly on the label families of the 5-dimensional base gadget $G_5$: for a set $K$ of pairwise separated label words over $k$ copies of $G_5$, the union of the products of families, mapped by the automorphism
   $$s^*(x) = (x_0,\; 2 - x_2,\; x_4,\; x_1,\; 2 - x_3)$$
   in each copy, is independent. Good codes $K$ are found as weighted independent sets in a strong power of the label conflict graph. In dimension 45 the new codebook has $j = 121990569825869329058799$ (Tang: $121947917749163375722991$).
2. **An improved 10-dimensional codebook $J^+$.** Tandon's $J^+$ is obtained from $(T \times T)(I_{10})$ by eight exchanges along private pairs. We use 272 exchanges, found by an exact integer program: Tandon's eight, twelve disjoint 15-for-15 exchanges and 84 one-for-one swaps. The size stays 134753, and the count $C_1$ rises from 27488 to 27512.
3. **Deeper nesting.** Tang nests patterns to depth 2. With exact counting we nest to depth 5, recomputing the neutral codebook along each chain.

The top level applies the BPZ rule $S_{3b}$ and terminal code $K_{4a}$ to three gadgets of dimensions 40, 80 and 55, giving dimension $4 \cdot 175 = 700$.

### $C_{13}$: avoidance re-classification

In the BPZ framework, the words in families A and D are assigned by fixed substitution tables. Some of them, however, are far from families H, V and O.

**Lemma.** Let $(F_l)$ be a seven-family representation and $Y = F_H \cup F_V \cup F_O$. Any words of $F_A$ or $F_D$ that are not confusable with any word of $Y$ can be moved to $F_N$, and the result is again a seven-family representation.

Moving words into N usually increases the final count, because N carries the largest weight. To know exactly which words may be moved at each step of a schedule, we propagate exact *flag tables*. These record, for each word, which families it is confusable with, and they are kept conservative after each move.

Applied to G. Long's schedule over the BPZ base system in $C_{13}^{\boxtimes 6}$ (49 nodes, terminal code $K_{3a}$, dimension $6 \cdot 87 = 522$), with re-classification at six internal nodes and at the three terminal children, this gives $\Theta(C_{13}) \ge 6.302930359067765$.

## Certificates and verification

Both bounds are certified by exact integer computation. The certificate files `c7/certificate.txt` and `c13/certificate.txt` contain the integers $M$ (360 and 418 digits).

- **Calibration.** Before computing the new bounds, the verifiers reproduce exactly:
  - the published BPZ certificates for $C_7$ and $C_{13}$;
  - Tandon's and Tang's intermediate counts, and Tang's $C_7$ integer;
  - Long's $C_{13}$ certificate.
- **Independent check.** Separately written programs, which share no code with the verifiers, recompute both integers, and a brute-force test checks the re-classification lemma on random instances.

Each of the following runs with Python 3 and numpy, without arguments:

```
python3 c7/verify.py
python3 c13/verify.py
python3 independent_check/check_c7.py
python3 independent_check/check_c13.py
python3 independent_check/check_lemma.py
```

Expected outputs and checksums are stored next to each script.

## Credits

This work builds on:
- C. E. Shannon (1956);
- S. Polak and A. Schrijver (2019);
- Y. Gao (2026);
- P. Buys, S. Polak and J. Zuiddam (2026);
- R. Tandon (2026);
- L. Tang (2026);
- G. Long (2026).

The files in `c13/data/` come from the public repositories of BPZ and Long, under their licenses (see `NOTICE`).

The search strategy was conceived by the author and the code developed through many a back and forth with Claude.

## Citation

Emirhan Inan, *Certificates for new lower bounds on the Shannon capacity of C7 and C13* (2026). https://doi.org/10.5281/zenodo.24517880

## License

CC BY 4.0 (see `LICENSE`), except the third-party files listed in `NOTICE`.
