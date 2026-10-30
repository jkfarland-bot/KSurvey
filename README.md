# KSurvey (QuarticSurvey)

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.23624362.svg)](https://doi.org/10.5281/zenodo.23624362)

Lean 4 / Mathlib formalization accompanying J. S. Farland, *The coordinates of a quartic
L-value: a formalized survey of the classical facts*.

The survey claims nothing new. Every statement is classical and attributed in the paper; this
repository verifies the elementary core.

Toolchain: `leanprover/lean4:v4.35.0`, Mathlib `v4.35.0`.

```
lake exe cache get
lake build
```

No `sorry`, no `native_decide`. Every main theorem depends only on `propext`,
`Classical.choice` and `Quot.sound` (`#print axioms`).

Setting (Sections 1 to 4 of the survey): `p` prime, `χ : MulChar (ZMod p) GaussianInt` with
`orderOf χ = 4`, `p % 8 = 5`, and `5 < p` where the coset sums enter. Setting of Section 5 (the
2-power levels, file `Levels`): `χ : MulChar (ZMod p) ℂ`, odd (`χ (-1) = -1`), with `χ ^ m = 1` for
some `0 < m < p - 1` in place of "p is not a Fermat prime". Sums run over least nonnegative
residues `n.val`.

| Survey | Lean | File |
|---|---|---|
| Prop. 1.1 (odd orders are even) | `apply_neg_one_of_odd_orderOf` | Basic |
| Prop. 1.1 (order two is real) | `apply_of_orderOf_two` | Basic |
| Prop. 1.1 (order four: odd iff `p ≡ 5 mod 8`) | `quartic_apply_neg_one`, `quartic_apply_neg_one_of_one` | Basic |
| `χ(2) = ± i` | `quartic_apply_two` | Basic |
| Def. 3.3 (the pin exists and is unique) | `existsUnique_pinned` | Pin |
| the two quartic characters are `χ`, `χ ^ 3` | `quartic_eq_or_eq_pow_three` | Pin |
| Prop. 3.1 (integrality) | `p_dvd_cosetSum` | CosetSums |
| Prop. 3.1 (class sizes) | `card_class` | CosetSums |
| Prop. 3.1 (pairing) | `S_add_S_neg` | CosetSums |
| Prop. 3.1 (`β = k + i t`) | `T_eq` | CosetSums |
| Prop. 3.2 (oddness) | `odd_k`, `odd_t` | CosetSums |
| conjugation fixes `k`, negates `t` | `k_pow_three`, `t_pow_three` | CosetSums |
| Prop. 2.1 (trace) | `trace_eq` | Reconstruction |
| Prop. 3.4 (`a² + b² = p`) | `jacobiSum_norm` | Jacobi |
| Prop. 3.4 (`a ≡ -1`, `b ≡ 2 mod 4`) | `jacobiSum_mod_four` | Jacobi |
| Prop. 3.4 (`J(χ̄,χ̄) = conj J(χ,χ)`) | `jacobiSum_pow_three` | Jacobi |
| Prop. 3.5, (6) (5) (4) | `two_A`, `two_B`, `five_k`, `five_t`, `hudson_S` | Quarters |
| Thm. 3.6 (formal part) | `reconstruction` | Reconstruction |
| Prop. 4.1 | `fixed_base_collapse` | FixedBase |
| SUZ (6) at `m = 1, N = p, r = 2` | `half_sum` | FixedBase |
| Prop. 5.1 (`B_{1,ψ} = 0` for even `ψ ≠ 1`; lower levels vanish) | `even_T_eq_zero`, `levelSum_even` | Levels |
| Prop. 5.2 (integrality and pairing at level `2^a`) | `p_dvd_levelSum`, `levelSum_add_neg`, `card_level_eq` | Levels |
| Prop. 5.2 (expansion `B_{1,χ} = Σ d_r ζ^r`) | `level_expansion` | Levels |
| Prop. 5.2 (parity of the coordinates) | `level_parity`, `card_kernel_odd` | Levels |
| Prop. 5.3 (level invariant, sum over odd exponents; oddness) | `level_trace`, `level_parity` | Levels |

Quoted, not formalized: `N(β) = 2h*(p)` (needs class numbers of number fields), the `L(1, χ)`
normalization, the general Szmidt–Urbanowicz–Zagier formula, and `b ≡ -2 (mod 8)` under the pin
(needs the quartic character of 2), and in Prop. 5.3 the identification of the sum over odd
exponents with the field trace, and the identification of the fibres `{χ = ζ^r}` with the cosets
`g^r H`.

## Citation

Software: J. S. Farland, *KSurvey: Lean formalization of the quartic L-value survey*, Zenodo,
2026, [doi:10.5281/zenodo.23624362](https://doi.org/10.5281/zenodo.23624362) (all versions; v1.0 is
[doi:10.5281/zenodo.23624363](https://doi.org/10.5281/zenodo.23624363)). Version 1.1 adds `Levels`.

Paper: J. S. Farland, *The coordinates of a quartic L-value: a formalized survey of the classical
facts*, preprint, Zenodo, 2026, [doi:10.5281/zenodo.23624516](https://doi.org/10.5281/zenodo.23624516)
(all versions; v1 is [doi:10.5281/zenodo.23624517](https://doi.org/10.5281/zenodo.23624517)).
Version 2 of the survey (adds Section 5, the 2-power levels) is in `paper/` as LaTeX source and PDF.
