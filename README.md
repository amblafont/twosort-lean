This project was edited by [Aristotle](https://aristotle.harmonic.fun).

To cite Aristotle:
- Tag @Aristotle-Harmonic on GitHub PRs/issues
- Add as co-author to commits:
```
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
```

# cartexp-aristotle

## The paper

This project formalises results of *For Generalised Algebraic Theories, Two Sorts Are Enough*
(`s_csl.tex`, appendices `s-appendices_csl.tex`). File and declaration names follow the paper
(e.g. `Lexp`, `ColaxSliceCart`, `twoSortification`, `famFunctor`, `coreProjectionMorphism`), and the
docstrings cite the paper as `[Paper, §n, Kind `label`]`, using the LaTeX labels of the sources.
See `PAPER_REFERENCES.md` for the full correspondence and the root file `CartexpAristotle.lean`
for an overview by section.

## Building

The project targets Lean `v4.28.0` (see `lean-toolchain`) and the Mathlib commit pinned in
`lake-manifest.json` (`8f9d9cff6bd728b17a24e163c9402775d9e6a365`). Build with

```
lake exe cache get
lake build CartexpAristotle
```

Two pieces of the development exist only because this Mathlib version lacks something newer
Mathlib provides:

* `CartexpAristotle/ChosenPullback.lean` is a local stand-in for Mathlib's `ChosenPullback`. It has
  the five fields `pullback`, `p₁`, `p₂`, `condition`, `isLimit` (no base projection `p` with
  `hp₁`/`hp₂`).
* `CategoryTheory.Comma.fstSndJointlyReflectLimit` (top of `CartexpAristotle/UniversalNatTrans.lean`)
  is a local proof that the two projections of a comma category jointly reflect limits. Unlike the
  newer Mathlib lemma it assumes that the right-hand functor `R` preserves the limit of the second
  projection; at its only use `R` is the identity, so this always holds.
