# Certificate of correctness — L∞ Permutation Removal Lemma (Le, Shi, Wei)

This repository is a Lean 4 formalization of the main results of V. H. Le, R. Shi, F. Wei,
"L∞ Permutation Removal Lemma" (unpublished manuscript; GPT-edited version of the authors' draft,
file dated 2026-10-12). Paper locations below are line numbers of that `.tex` file ("tex l.N").

## 1. What certifies the proofs

A Lean formalization certifies a theorem through three things together:

1. **The statements.** The Lean statements of the main theorems, and the definitions they use, say
   what the paper says. This is the only part a person has to read. Sections 3 and 4 below put
   each statement and definition next to the paper's wording.
2. **The kernel check.** Lean's kernel accepts every proof in the repository. Nobody needs to read
   the proofs; `lake build` re-checks all of them.
3. **The axiom check.** Nothing is assumed beyond Lean's three standard axioms (`propext`,
   `Classical.choice`, `Quot.sound`): no `sorry`, no extra `axiom`.

The proofs themselves (about 12,000 lines in `LinfPermRemoval/`) need not be read. Every numbered
result of the paper (all 67: theorems, lemmas, claims, facts, corollaries, definitions,
constructions) is stated and proved there. The main theorems are proved from them, so reading the
four statements of section 3 and the definitions of section 4 is enough to accept the main
theorems.

## 2. How to check it yourself

Requirements: `elan` (the Lean installer; https://github.com/leanprover/elan) and `git`.

```
git clone <this repository>
cd <repository>
lake exe cache get        # downloads Mathlib's prebuilt files (a few GB)
lake build                # kernel-checks every proof; must end "Build completed successfully"
lake env lean Certificate.lean
```

The last command restates the four main theorems with their full statements (each `example` must
be accepted) and prints, for each, the axioms it uses. Expected output, four lines of the form:

```
'LinfPermRemoval.thm_1_2' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Versions: Lean `v4.35.0` (`lean-toolchain`), Mathlib commit
`fcd79238d34137c492bb55aef27aba0916e0a36f` (`lakefile.toml`). This repository was built from scratch
with exactly these on 2026-10-15; `Certificate.lean` printed the four lines above.

## 3. The main theorems

Conventions used throughout. Lean permutations `Perm (Fin n)` act on {0, …, n−1}: the paper's
position i is Lean's i − 1, and the paper's value π(i) is Lean's value + 1. The paper's patterns
are written in one-line notation through `oneLine σ = [σ(1), …, σ(k)]` (1-based).

### Theorem 1.1, first part (tex l.121–123)

> Let σ ∈ {(12), (21), (132), (231), (312), (213)}. For every n ≥ 2, every permutation π ∈ S_n,
> and every ε > 0, if π is ε-far from σ-free with respect to ρ∞, then π contains at least ε(n−1)
> σ-copies.

```lean
theorem thm_1_1_lower {k : ℕ} (σ : Perm (Fin k)) (hσ : oneLine σ ∈ linearPatterns)
    (n : ℕ) (hn : 2 ≤ n) (π : Perm (Fin n)) (ε : ℝ) (hε : 0 < ε)
    (hfar : IsFarFromFree ε σ π) :
    ε * ((n : ℝ) - 1) ≤ (numCopies σ π : ℝ)
```

`linearPatterns` is the list [[1,2], [2,1], [1,3,2], [2,3,1], [3,1,2], [2,1,3]]. Note: the proof does
not use ε > 0 (for ε ≤ 0 the claim is trivial); the hypothesis is kept to match the paper.

### Theorem 1.1, converse (tex l.122)

> Conversely, for each such σ, for 0 < ε ≤ 1/16 and all sufficiently large n (depending on σ and
> ε), there is an ε-far permutation π ∈ S_n with N_σ(π) ≤ 6εn.

```lean
theorem thm_1_1_upper {k : ℕ} (σ : Perm (Fin k)) (hσ : oneLine σ ∈ linearPatterns)
    (ε : ℝ) (hε : 0 < ε) (hε' : ε ≤ 1 / 16) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∃ π : Perm (Fin n),
      IsFarFromFree ε σ π ∧ (numCopies σ π : ℝ) ≤ 6 * ε * n
```

### Theorem 1.2 (tex l.131–133)

> For any permutation σ of length k, if k ≥ 4 or σ = (123) or (321), there exist ε_σ > 0 and n₀(k)
> such that, for every n ≥ n₀(k), there is a permutation π ∈ S_n that is ε_σ-far from σ-free with
> respect to ρ∞, yet contains only one copy of σ.

```lean
theorem thm_1_2 (k : ℕ) :
    ∃ n₀ : ℕ, ∀ σ : Perm (Fin k), ThmHyp σ →
      ∃ ε : ℝ, 0 < ε ∧ ∀ n ≥ n₀, ∃ π : Perm (Fin n),
        IsFarFromFree ε σ π ∧ numCopies σ π = 1
```

The order of quantifiers matches the paper: n₀ is chosen before σ, so it depends only on k, while
ε depends on σ. "Contains only one copy" is `numCopies σ π = 1`.

### Theorem 4.1 (tex l.612–619), the construction behind Theorem 1.2

> Let σ ∈ S_k, where either k ≥ 4 or σ ∈ {(123), (321)}. There exists N₀(k) such that, for every
> N ≥ N₀(k), there is an N-point set Π ⊂ ℝ² associated with a permutation π ∈ S_N with the
> following properties. If Σ = {(i, σ(i)) : i ∈ [k]} is the canonical point set of σ, then Σ ⊆ Π
> and Σ is the unique σ-copy in Π. Moreover, for every i ∈ [k−1], |Π ∩ H_i| ≥ (N−k)/(2k) and
> |Π ∩ V_i| ≥ (N−k)/(2k).

```lean
theorem thm_4_1 (k : ℕ) : ∃ N₀ : ℕ, ∀ σ : Perm (Fin k), ThmHyp σ → GeomConclusion σ N₀
```

`GeomConclusion` is spelled out in section 4.

## 4. The definitions these statements use

Each Lean definition is in `LinfPermRemoval/Basic.lean`, `Section3.lean` or `Geometry.lean`.

- **σ-copy, N_σ(π)** (tex l.117–119). `IsCopy σ π S`: the index set S has k elements and, listed
  increasingly as i₁ < ⋯ < i_k, satisfies π(i_a) < π(i_b) ⇔ σ(a) < σ(b). `numCopies σ π` is the
  number of such S, and `IsFree σ π` means `numCopies σ π = 0`.
  ```lean
  def IsCopy (σ : Perm (Fin k)) (π : Perm (Fin n)) (S : Finset (Fin n)) : Prop :=
    ∃ h : S.card = k, ∀ a b : Fin k,
      π (S.orderEmbOfFin h a) < π (S.orderEmbOfFin h b) ↔ σ a < σ b
  noncomputable def numCopies (σ : Perm (Fin k)) (π : Perm (Fin n)) : ℕ :=
    ((Finset.univ : Finset (Finset (Fin n))).filter (IsCopy σ π)).card
  ```
- **ρ∞, Definition 2.2** (tex l.189–192): ρ∞(π₁, π₂) = 1/(n−1) · min over θ ∈ S_n of
  max over i of max{|i − θ(i)|, |π₁(i) − π₂(θ(i))|}.
  ```lean
  def maxDisp (π₁ π₂ θ : Perm (Fin n)) : ℕ :=
    Finset.univ.sup fun i : Fin n =>
      max ((i : ℤ) - (θ i : ℤ)).natAbs ((π₁ i : ℤ) - (π₂ (θ i) : ℤ)).natAbs
  noncomputable def rhoInf (π₁ π₂ : Perm (Fin n)) : ℝ :=
    ((Finset.univ.inf' Finset.univ_nonempty (maxDisp π₁ π₂) : ℕ) : ℝ) / ((n : ℝ) - 1)
  ```
  The paper defines ρ∞ only for n ≥ 2. For n ≤ 1, Lean gives the formula a value (dividing by
  0 or −1), but no main statement depends on it: Theorem 1.1's lower bound assumes n ≥ 2, and the
  others choose n large.
- **ε-far, Definition 2.3** (tex l.234–236): π is ε-far from a property P if the minimum of
  ρ∞(π, γ) over the length-n permutations γ with P is at least ε.
  ```lean
  def IsFar (ε : ℝ) (π : Perm (Fin n)) (Pn : Set (Perm (Fin n))) : Prop :=
    ∀ γ ∈ Pn, ε ≤ rhoInf π γ
  def IsFarFromFree (ε : ℝ) (σ : Perm (Fin k)) (π : Perm (Fin n)) : Prop :=
    IsFar ε π {γ | IsFree σ γ}
  ```
  "Every σ-free γ is at ρ∞-distance at least ε" is the paper's minimum whenever a σ-free
  permutation of length n exists. One always does for patterns of length k ≥ 2 (the identity or
  the decreasing permutation), which covers every main statement.
- **The hypothesis of Theorems 1.2 and 4.1**: k ≥ 4, or σ = (123) or (321).
  ```lean
  def ThmHyp (σ : Perm (Fin k)) : Prop :=
    4 ≤ k ∨ oneLine σ = [1, 2, 3] ∨ oneLine σ = [3, 2, 1]
  ```
- **Point set associated with a permutation, Definition 2.1** (tex l.165–175): points
  (x₁, y₁), …, (x_n, y_n) with x₁ < ⋯ < x_n, distinct y's, and π(i) the rank of y_i. In Lean,
  `Represents π Θ` says the list Θ has strictly increasing x-coordinates and
  y_i < y_j ⇔ π(i) < π(j); `IsAssoc P π` says the finite set P is such a list.
  ```lean
  def Represents (π : Perm (Fin n)) (Θ : Fin n → ℝ × ℝ) : Prop :=
    StrictMono (fun i => (Θ i).1) ∧ ∀ i j, (Θ i).2 < (Θ j).2 ↔ π i < π j
  def IsAssoc (P : Finset (ℝ × ℝ)) (π : Perm (Fin n)) : Prop :=
    ∃ Θ : Fin n → ℝ × ℝ, Represents π Θ ∧ P = Finset.univ.image Θ
  ```
- **Canonical point set** (tex l.180–182): Σ = {(i, σ(i))}, 1-based.
  ```lean
  def canonPt (π : Perm (Fin n)) (i : Fin n) : ℝ × ℝ := ((i : ℝ) + 1, ((π i : ℕ) : ℝ) + 1)
  noncomputable def canon (π : Perm (Fin n)) : Finset (ℝ × ℝ) := Finset.univ.image (canonPt π)
  ```
- **"Σ is the unique σ-copy in Π"**: a σ-copy in a point set D is a list Θ of k points of D ordered
  like σ (`CopyIn`); uniqueness says Σ ⊆ P and every σ-copy in P has point set Σ.
  ```lean
  def CopyIn (σ : Perm (Fin k)) (Θ : Fin k → ℝ × ℝ) (D : Set (ℝ × ℝ)) : Prop :=
    Represents σ Θ ∧ ∀ i, Θ i ∈ D
  def IsUniqueCopy (σ : Perm (Fin k)) (P : Set (ℝ × ℝ)) : Prop :=
    (↑(canon σ) : Set (ℝ × ℝ)) ⊆ P ∧
      ∀ Θ : Fin k → ℝ × ℝ, CopyIn σ Θ P → Finset.univ.image Θ = canon σ
  ```
- **Stripes** (tex l.618): H_i = ℝ × (i, i+1), V_i = (i, i+1) × ℝ.
  ```lean
  def hStripe (i : ℕ) : Set (ℝ × ℝ) := {p | (i : ℝ) < p.2 ∧ p.2 < (i : ℝ) + 1}
  def vStripe (i : ℕ) : Set (ℝ × ℝ) := {p | (i : ℝ) < p.1 ∧ p.1 < (i : ℝ) + 1}
  ```
- **The conclusion of Theorem 4.1 for one σ with threshold N₀**:
  ```lean
  def GeomConclusion (σ : Perm (Fin k)) (N₀ : ℕ) : Prop :=
    ∀ N ≥ N₀, ∃ (P : Finset (ℝ × ℝ)) (π : Perm (Fin N)),
      IsAssoc P π ∧ IsUniqueCopy σ ↑P ∧
      ∀ i : ℕ, 1 ≤ i → i ≤ k - 1 →
        ((N : ℝ) - k) / (2 * k) ≤ ((P.filter (· ∈ hStripe i)).card : ℝ) ∧
        ((N : ℝ) - k) / (2 * k) ≤ ((P.filter (· ∈ vStripe i)).card : ℝ)
  ```
  The point set is a `Finset` associated with π ∈ S_N, so it has exactly N points.
- **One-line notation** and the six patterns of Theorem 1.1:
  ```lean
  def oneLine (σ : Perm (Fin k)) : List ℕ := List.ofFn fun i => (σ i : ℕ) + 1
  def linearPatterns : List (List ℕ) := [[1, 2], [2, 1], [1, 3, 2], [2, 3, 1], [3, 1, 2], [2, 1, 3]]
  ```

## 5. What has and has not been reviewed

- **The kernel check and the axiom check** are mechanical and reproducible by anyone with the
  commands of section 2.
- **Faithfulness of the statements** (part 1 of section 1) is a human judgement. During the
  formalization, independent AI reviewers compared every Lean statement with the paper in both
  directions, and all 67 passed. The statements were approved by the AI agent on the project
  owner's instruction, *not* by a mathematician. A mathematician's reading of sections 3 and 4 is
  the step that completes the certificate in the usual sense.
- **Differences from the paper that a reader should know.** Each is a convention, not a change of
  meaning: the 0-based/1-based conversion above; the value of ρ∞ for n ≤ 1, which no main
  statement uses; "ε-far" read as "far from every σ-free permutation", equivalent here because one
  always exists. Some hypotheses stated in the paper are not needed by the Lean proofs and are
  kept so that the statements are the paper's; for the main theorems this is only ε > 0 in
  Theorem 1.1's lower bound.
- The full audit report, with the record of every review, the list of the 67 results with their
  Lean names (`LinfPermRemoval/Main.lean`), the proof routes that differ from the paper, and the
  statements that hold only vacuously (claims inside proofs by contradiction), is kept separately
  (private repository `ZRTMRH/formalization-audits`, branch `le-shi-wei-linf`, file
  `le-shi-wei-linf/REPORT.pdf`).
