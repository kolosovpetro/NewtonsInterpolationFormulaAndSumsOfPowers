# Newton's interpolation formula and sums of powers

## Abstract

In this manuscript we derive formulas for multifold sums of powers by utilizing Newton's interpolation formula.
Furthermore, we provide formulas for multifold sums of powers in terms of Stirling numbers of the second kind and Eulerian numbers.


## Metadata

- **MSC2010:** 05A19, 05A10, 41A15, 11B83
- **Keywords:** Sums of powers, Newton's interpolation formula, Finite differences, Binomial coefficients, Faulhaber's formula, Bernoulli numbers, Bernoulli polynomials Interpolation, Approximation, Discrete convolution, Combinatorics, Polynomial identities, Central factorial numbers, Stirling numbers, Eulerian numbers, Worpitzky identity, Pascal's triangle, OEIS
- **License:** This work is licensed under a [CC BY 4.0 License](https://creativecommons.org/licenses/by/4.0/)
- **DOI:** https://doi.org/10.5281/zenodo.18040979
- **Web Version:** https://kolosovpetro.github.io/math/test
- **Sources:** https://github.com/kolosovpetro/NewtonsInterpolationFormulaAndSumsOfPowers
- **ORCID:** https://orcid.org/0000-0002-6544-8880
- **Email:** kolosovp94@gmail.com

## Related projects

- [Newton's interpolation formula and sums of powers (2025)](https://github.com/kolosovpetro/NewtonsInterpolationFormulaAndSumsOfPowers)
- [Sums of powers via central finite differences and Newton's formula (2025)](https://github.com/kolosovpetro/SumsOfPowersViaCentralFiniteDifferencesAndNewtonFormula)
- [Sums of powers via backward finite differences and Newton's formula (2026)](https://github.com/kolosovpetro/SumsOfPowersViaBackwardFiniteDifferencesAndNewtonFormula)

## OEIS

- https://oeis.org/A131689 - Triangle of numbers T(n,k) = k!*Stirling2(n,k) read by rows, T(n, k) for 0 <= k <= n.
- https://oeis.org/A028246 - Triangular array a(n,k) = (1/k)*Sum_{i=0..k} (-1)^(k-i)*binomial(k,i)*i^n; n >= 1, 1 <= k <= n, read by rows.
- https://oeis.org/A038719 - Triangle T(n,k) (0 <= k <= n) giving number of chains of length k in partially ordered set formed from subsets of n-set by inclusion.
- https://oeis.org/A391552 - Triangle read by rows: T(n,k) = Sum_{j=0..k} (-1)^(k-j) * binomial(k,j) * (3+j)^n.
- https://oeis.org/A391633 - Triangle read by rows: T(n,k) = Sum_{j=0..k} (-1)^(k-j) * binomial(k,j) * (4+j)^n.
- https://oeis.org/A391635 - Triangle read by rows: T(n,k) = Sum_{j=0..k} (-1)^(k-j) * binomial(k,j) * (5+j)^n.

## References

- Knuth, D. E. (1993). Johann Faulhaber and sums of powers. Mathematics of Computation, 61(203), 277–294. https://arxiv.org/abs/math/9207222
- Newton, I., & Chittenden, N. W. (1850). Newton's Principia: The mathematical principles of natural philosophy. New-York: D. Adee. https://archive.org/details/bub_gb_KaAIAAAAIAAJ/page/466/mode/2up
- Graham, R. L., Knuth, D. E., & Patashnik, O. (1994). Concrete mathematics: A foundation for computer science (2nd ed.). Addison-Wesley Publishing Company, Inc. https://archive.org/details/concrete-mathematics
- Pfaff, T. J. (2007). Deriving a formula for sums of powers of integers. Pi Mu Epsilon Journal, 12(7), 425–430. https://www.jstor.org/stable/24340705
- Sloane, N. J. A., et al. (2003). The on-line encyclopedia of integer sequences. https://oeis.org/
- Cereceda, J. L. (2022). Sums of powers of integers and generalized Stirling numbers of the second kind. arXiv preprint arXiv:2211.11648. https://arxiv.org/abs/2211.11648
- Worpitzky, J. (1883). Studien über die bernoullischen und eulerschen zahlen. Journal für die reine und angewandte Mathematik, 94, 203–232. http://eudml.org/doc/148532
- Steffensen, J. F. (1927). Interpolation. Williams & Wilkins. https://www.amazon.com/-/de/Interpolation-Second-Dover-Books-Mathematics-ebook/dp/B00GHQVON8
- Carlitz, L., & Riordan, J. (1963). The divided central differences of zero. Canadian Journal of Mathematics, 15, 94–100. https://doi.org/10.4153/CJM-1963-010-8
- Riordan, J. (1968). Combinatorial identities (Vol. 217). Wiley New York. https://www.amazon.com/-/de/Combinatorial-Identities-Probability-Mathematical-Statistics/dp/0471722758
- Scheuer, M. (2020). Reference request: identity in central factorial numbers. https://math.stackexchange.com/a/3665722/463487
- Kolosov, P. (2025). Mathematica programs for finite differences, Stirling numbers, and sums of powers. GitHub repository. https://github.com/kolosovpetro/NewtonsInterpolationFormulaAndSumsOfPowers/tree/main/mathematica
- Kolosov, P. (2025). Newton's interpolation formula and sums of powers. Zenodo. https://doi.org/10.5281/zenodo.18040979
- Kolosov, P. (2025). Sums of powers via central finite differences and Newton's formula. Zenodo. https://doi.org/10.5281/zenodo.18096789
- Kolosov, P. (2026). Sums of powers via backward finite differences and Newton's formula. Zenodo. https://doi.org/10.5281/zenodo.18118011

## Pandoc compile command

- `pandoc NewtonsInterpolationFormulaAndSumsOfPowers.tex --mathjax --standalone --citeproc --bibliography=NewtonsInterpolationFormulaAndSumsOfPowers.bib --csl=chicago-author-date.csl -o index.html`