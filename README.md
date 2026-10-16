# L∞ Permutation Removal Lemma — Lean 4 formalization

A Lean 4 / Mathlib formalization of V. H. Le, R. Shi, F. Wei, "L∞ Permutation Removal Lemma"
(unpublished manuscript). Every numbered result of the paper (67: Theorems 1.1, 1.2, 4.1 and all
lemmas, claims, facts, corollaries, definitions and constructions) is stated and proved, with no
`sorry` and only Lean's standard axioms.

- **Start here:** [`CERTIFICATE.md`](CERTIFICATE.md). It explains what certifies the proofs, how to
  re-check them, and shows the main statements and definitions next to the paper's wording.
- `Certificate.lean`: the four main theorems restated in full, plus the axiom check.
- `LinfPermRemoval/`: the formalization; `LinfPermRemoval/Main.lean` maps each numbered result of
  the paper to its Lean name.

Check:

```
lake exe cache get
lake build
lake env lean Certificate.lean
```

Lean `v4.35.0`, Mathlib `fcd79238d34137c492bb55aef27aba0916e0a36f`. Private: the paper is
unpublished; do not make this repository public without the authors' agreement.
