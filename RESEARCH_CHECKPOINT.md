# Checked partial circuit bounds

This checkpoint publishes Jaredcastorena's current checked mathematics for the P vs NP effort. It contains partial results, with the remaining claims stated explicitly.

## Main graph batch

[Partial984](lean/Partial984/README.md) proves **25 of the 31 total circuit lower bounds** in L-meta-984: cases **0–18 and 21–26**. Cases **19, 20, 27, 28, 29, and 30** remain open in this work.

`twentyfive_totals` is the proved conjunction. `conditional_missing_six` gives the full statement only under six explicit missing-case premises. The four modules have been checked together in dependency order using Lean 4.36.0. Their final theorems depend only on `propext`, `Classical.choice`, and `Quot.sound`.

This modular checkpoint does not meet the site's requirements for a completed, single-file L-meta-984 submission. Its standalone candidate also exceeds the site's 512 KiB limit.

## Additional checked studies

The files below are standalone studies. Compile them separately: some intentionally repeat helper namespaces from the main packet.

| Source | Checked result | Remaining gap |
|---|---|---|
| [Case27](lean/Partial984/Studies/Case27.lean) | At least seven OR gates and eleven total gates; any circuit below twelve has exactly four AND gates and seven OR gates; central-edge AND exclusions | Total lower bound twelve |
| [SecondCollision](lean/Partial984/Studies/SecondCollision.lean) | A finite collision theorem for semantic functions | Extraction from an arbitrary circuit |
| [ThetaFirstOr](lean/Partial984/Studies/ThetaFirstOr.lean) | A hypothetical small theta circuit reduces to six first-OR forms | Excluding those six forms in the circuit model |
| [Case28](lean/Partial984/Studies/Case28.lean) | At least seven OR gates; total twelve when there are at least five AND gates | The four-AND case |
| [PartialAnd](lean/Partial984/Studies/PartialAnd.lean) | Four-AND lower bounds for three specified intermediate functions between edge-deleted and original graphs | The required circuit rewrite and the full total bounds |
| [Case29Control](lean/Partial984/Studies/Case29Control.lean) | A twelve-gate, four-AND circuit showing that an intermediate AND can create an unwanted pair | This is a control, not a below-bound counterexample |
| [QuotientControls](lean/Partial984/Studies/QuotientControls.lean) | Ten-gate circuits for two specified quotient graphs | These controls do not prove the dense graph lower bounds |
| [Partial1343](lean/Partial1343/Bounds.lean) | At least five AND gates for the eleven-vertex function, plus an exact twenty-two-gate construction | The conjectured total lower bound twenty-two |

The exported proof bodies match their successfully checked versions; one blank line had trailing spaces removed. Unfinished prototypes and failed proof files are excluded. Reused fleet proofs retain their source attributions in comments.

## Checking

Use this repository's pinned Lean and Mathlib versions. From `lean/`, prepare the dependencies:

```sh
lake exe cache get
lake build PEqualNP.Defs
```

Then follow the [four-module build instructions](lean/Partial984/README.md). A standalone study can be checked with, for example:

```sh
lake env lean Partial984/Studies/Case27.lean
lake env lean Partial1343/Bounds.lean
```

Some finite kernel certificates take several minutes and substantial memory. The main packet's largest module used approximately 29 GiB during verification.
