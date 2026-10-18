# L∞ Permutation Removal Lemma — Lean 4 formalization

A Lean 4 / Mathlib formalization of V. H. Le, R. Shi, F. Wei, "L∞ Permutation Removal Lemma".
Each of the paper's 67 numbered items has a Lean counterpart: every theorem, lemma, claim, fact
and corollary (including Theorems 1.1, 1.2 and 4.1) is stated and proved, and every definition and
construction is defined, with no `sorry` and only Lean's standard axioms. Release `v1.0` follows
the numbering and statements of the paper's version of 12 October 2026.

- **Start here:** [`CERTIFICATE.md`](CERTIFICATE.md). It explains what certifies the proofs, how to
  re-check them, and shows the main statements and definitions next to the paper's wording, with a
  guide to the Lean notation for readers who do not know Lean.
- `Certificate.lean`: the four main theorems restated in full, plus the axiom check.
- `LinfPermRemoval/`: the formalization; `LinfPermRemoval/Main.lean` maps each numbered result of
  the paper to its Lean name.

Check:

```
git checkout v1.0
lake exe cache get
lake build
lake env lean Certificate.lean
```

Lean `v4.35.0`, Mathlib `fcd79238d34137c492bb55aef27aba0916e0a36f`.
