# Certificate of correctness — L∞ Permutation Removal Lemma (Le, Shi, Wei)

This repository is a Lean 4 formalization of V. H. Le, R. Shi, F. Wei, "L∞ Permutation Removal
Lemma". Release `v1.0` of this repository follows the statements and the numbering of the
paper's numbered results in its version of 12 October 2026. Paper references below are to that
numbering (Theorem 1.1, Definition 2.2, …), its sections (§1.1, §2, …) and its pages.

## 1. What certifies the proofs

A Lean formalization certifies a theorem through three things together:

1. **The statements.** The Lean statements of the main theorems, and the definitions they use, say
   what the paper says. This is the only part a person has to read. Sections 3 and 4 below put
   each statement and definition next to the paper's wording, and section 1a explains the Lean
   notation they use.
2. **The kernel check.** Lean's kernel accepts every proof in the repository. Nobody needs to read
   the proofs; `lake build` re-checks all of them.
3. **The axiom check.** Nothing is assumed beyond Lean's three standard axioms (`propext`,
   `Classical.choice`, `Quot.sound`): no `sorry`, no extra `axiom`.

The proofs themselves (about 12,000 lines in `LinfPermRemoval/`) need not be read. Each of the
paper's 67 numbered items has a Lean counterpart there (listed in `LinfPermRemoval/Main.lean`):
every theorem, lemma, claim, fact and corollary is stated and proved, and every definition and
construction is defined. Some claims made inside proofs by contradiction are stated, as in the
paper, under the hypothesis being refuted (see section 5). Reading the four Lean statements of
section 3 (Theorem 1.1 in two parts, Theorems 1.2 and 4.1) and the definitions of section 4 is
enough to accept the main theorems: the kernel check covers everything else.

## 1a. Reading the Lean statements (no Lean knowledge assumed)

| Lean | Meaning |
|---|---|
| `theorem name (x : A) (h : P) : Q` | For every `x` of type `A`, if `P` holds then `Q` holds. Each `(h : P)` before the final colon is a hypothesis; the text after the final colon is the conclusion. |
| `{k : ℕ}` | like `(k : ℕ)` ("for every natural number k"); the braces only mean Lean infers `k` itself |
| `def name … : T := body` | Defines `name` (of type `T`) to be `body`. `Prop` means "a statement". |
| `∀ n ≥ n₀, …` / `∃ x : A, …` | For every `n ≥ n₀`, … / there is an `x` in `A` such that … |
| `∃ (P : A) (π : B), …` | there are `P` in `A` and `π` in `B` such that … |
| `fun i => e` | the function i ↦ e |
| `A → B` (as a type), `σ a` | functions from `A` to `B` (so `Fin n → ℝ × ℝ` is a list of n points); `σ a` is σ(a) |
| `(π₁ π₂ θ : Perm (Fin n))` | several variables of the same type at once |
| `[a, b, c]` | a list |
| `k`, `n` appearing free in a `def` | arbitrary natural numbers (declared once per file as `variable {n k : ℕ}`) |
| `{γ \| P γ}` | the set {γ : P(γ)} |
| `(· ∈ A)` | the condition "∈ A" (so `s.filter (· ∈ A)` is s ∩ A) |
| `P ∧ Q`, `P ∨ Q`, `P → Q`, `P ↔ Q` | and, or, implies, if and only if |
| `ℕ`, `ℤ`, `ℝ` | natural numbers (including 0), integers, real numbers |
| `Fin n` | the set {0, 1, …, n−1} |
| `Perm (Fin n)` | permutations of {0, …, n−1}, i.e. S_n (see the conventions in section 3) |
| `(n : ℝ)`, `(i : ℤ)` | the number `n` regarded as a real number; the element `i` of `Fin n` regarded as an integer. In `6 * ε * n` or `(N : ℝ) - k` the conversion of `n`, `k` to ℝ is implicit. |
| `↑P` | the same set `P`, regarded as a set rather than a finite set (a conversion) |
| `k - 1` on ℕ | ordinary subtraction when k ≥ 1 (Lean sets 0 − 1 = 0 on ℕ) |
| `List.ofFn f` | the list [f(0), f(1), …, f(k−1)] |
| `Finset A`, `Set A` | finite subsets of `A`, subsets of `A` |
| `S.card` | the number of elements of the finite set `S` |
| `Finset.univ` | the set of all elements of a finite type |
| `s.filter p` | the elements of `s` satisfying `p` |
| `s.image f` | the image `f(s)` |
| `ℝ × ℝ`, `p.1`, `p.2` | the plane ℝ², the x- and y-coordinate of a point `p` |
| `(z).natAbs` | the absolute value of an integer `z` |
| `StrictMono f` | `f` is strictly increasing |
| `Finset.univ.sup f`, `Finset.univ.inf' Finset.univ_nonempty f` | the maximum, the minimum of `f` over all elements (`Finset.univ_nonempty` is the proof that there is at least one element, which a minimum needs) |
| `Finset (Finset (Fin n))` | the finite family of all subsets of {0, …, n−1} |
| `∃ h : S.card = k, …` | `S` has exactly `k` elements, and (using that) … |
| `S.orderEmbOfFin h a` | the `a`-th smallest element of `S` (counting from 0) |
| `noncomputable`, `open Classical in` | technical markers; they do not affect the meaning |

## 2. How to check it yourself

Requirements: `elan` (the Lean installer; https://github.com/leanprover/elan) and `git`.

```
git clone https://github.com/ZRTMRH/le-shi-wei-linf-lean.git
cd le-shi-wei-linf-lean
git checkout v1.0         # the release that corresponds to the paper
lake exe cache get        # downloads Mathlib's prebuilt files (a few GB)
lake build                # kernel-checks every proof; must end "Build completed successfully"
lake env lean Certificate.lean
```

The last command restates the four main statements in full (each `example` must
be accepted) and prints, for each, the axioms it uses. Expected output, four lines of the form:

```
'LinfPermRemoval.thm_1_2' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Versions: Lean `v4.35.0` (`lean-toolchain`), Mathlib commit
`fcd79238d34137c492bb55aef27aba0916e0a36f` (`lakefile.toml`). This repository was built from a
fresh clone with exactly these on 2026-10-17; `Certificate.lean` printed the four lines above.

## 3. The main theorems

Conventions used throughout. Lean permutations `Perm (Fin n)` act on {0, …, n−1}. A paper
permutation π of [n] corresponds to the Lean permutation π' with π(i) = π'(i − 1) + 1. Where this
shift matters:

- it is applied explicitly in `canonPt` (the canonical point (i, π(i)) is built as
  (i' + 1, π'(i') + 1)), in `oneLine` (which lists π(1), …, π(n)), and hence in the stripes H_i,
  V_i, which are placed between these 1-based points;
- it cancels where only comparisons or differences of positions and values occur: `IsCopy`
  (π(i_a) < π(i_b) ⇔ σ(a) < σ(b)), `maxDisp` (|i − θ(i)|, |π₁(i) − π₂(θ(i))|), and `Represents`.

The paper's patterns are written in one-line notation through `oneLine σ = [σ(1), …, σ(k)]`.

Theorems 1.1 and 1.2 are in `LinfPermRemoval/MainTheorems.lean`, Theorem 4.1 in
`LinfPermRemoval/Section4Main.lean`.

### Theorem 1.1, first part (§1.1)

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

### Theorem 1.1, converse (§1.1, last sentence of Theorem 1.1)

> Conversely, for each such σ, for 0 < ε ≤ 1/16 and all sufficiently large n (depending on σ and
> ε), there is an ε-far permutation π ∈ S_n with N_σ(π) ≤ 6εn.

```lean
theorem thm_1_1_upper {k : ℕ} (σ : Perm (Fin k)) (hσ : oneLine σ ∈ linearPatterns)
    (ε : ℝ) (hε : 0 < ε) (hε' : ε ≤ 1 / 16) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∃ π : Perm (Fin n),
      IsFarFromFree ε σ π ∧ (numCopies σ π : ℝ) ≤ 6 * ε * n
```

"ε-far" here means ε-far from σ-free, as in the first part.

### Theorem 1.2 (§1.1)

> For any permutation σ of length k, if k ≥ 4 or σ = (123) or (321), there exist ε_σ > 0 and n₀(k)
> such that, for every n ≥ n₀(k), there is a permutation π ∈ S_n that is ε_σ-far from σ-free with
> respect to ρ∞, yet contains only one copy of σ.

```lean
theorem thm_1_2 (k : ℕ) :
    ∃ n₀ : ℕ, ∀ σ : Perm (Fin k), ThmHyp σ →
      ∃ ε : ℝ, 0 < ε ∧ ∀ n ≥ n₀, ∃ π : Perm (Fin n),
        IsFarFromFree ε σ π ∧ numCopies σ π = 1
```

The paper writes n₀(k): the threshold depends only on k, while ε_σ depends on σ. Lean expresses
this by choosing n₀ before σ. Since S_k is finite, this is equivalent to choosing a threshold for
each σ separately (take the largest). For k ≤ 3 the statement is about σ = (123), (321) only, and
for k ≤ 2 about no σ at all, as in the paper. "Contains only one copy" is `numCopies σ π = 1`.

### Theorem 4.1 (§4), the construction behind Theorem 1.2

> Let σ ∈ S_k, where either k ≥ 4 or σ ∈ {(123), (321)}. There exists N₀(k) such that, for every
> N ≥ N₀(k), there is an N-point set Π ⊂ ℝ² associated with a permutation π ∈ S_N with the
> following properties. If Σ = {(i, σ(i)) : i ∈ [k]} is the canonical point set of σ, then Σ ⊆ Π
> and Σ is the unique σ-copy in Π. Moreover, for every i ∈ [k−1], |Π ∩ H_i| ≥ (N−k)/(2k) and
> |Π ∩ V_i| ≥ (N−k)/(2k), where H_i = ℝ × (i, i+1) and V_i = (i, i+1) × ℝ.

```lean
theorem thm_4_1 (k : ℕ) : ∃ N₀ : ℕ, ∀ σ : Perm (Fin k), ThmHyp σ → GeomConclusion σ N₀
```

`GeomConclusion` is spelled out in section 4. As in Theorem 1.2, the paper's N₀(k) is expressed by
choosing N₀ before σ, which is equivalent because S_k is finite.

## 4. The definitions these statements use

Each Lean definition is in `LinfPermRemoval/Basic.lean`, `Section3.lean` or `Geometry.lean`.

- **σ-copy, N_σ(π)** (§1.1, before Theorem 1.1). `IsCopy σ π S`: the index set S has k elements
  and, listed increasingly as i₁ < ⋯ < i_k, satisfies π(i_a) < π(i_b) ⇔ σ(a) < σ(b).
  `numCopies σ π` is the number of such S, and `IsFree σ π` means `numCopies σ π = 0`.
  ```lean
  def IsCopy (σ : Perm (Fin k)) (π : Perm (Fin n)) (S : Finset (Fin n)) : Prop :=
    ∃ h : S.card = k, ∀ a b : Fin k,
      π (S.orderEmbOfFin h a) < π (S.orderEmbOfFin h b) ↔ σ a < σ b
  open Classical in
  noncomputable def numCopies (σ : Perm (Fin k)) (π : Perm (Fin n)) : ℕ :=
    ((Finset.univ : Finset (Finset (Fin n))).filter (IsCopy σ π)).card
  ```
- **ρ∞, Definition 2.2**: ρ∞(π₁, π₂) = 1/(n−1) · min over θ ∈ S_n of
  max over i of max{|i − θ(i)|, |π₁(i) − π₂(θ(i))|}.
  ```lean
  def maxDisp (π₁ π₂ θ : Perm (Fin n)) : ℕ :=
    Finset.univ.sup fun i : Fin n =>
      max ((i : ℤ) - (θ i : ℤ)).natAbs ((π₁ i : ℤ) - (π₂ (θ i) : ℤ)).natAbs
  noncomputable def rhoInf (π₁ π₂ : Perm (Fin n)) : ℝ :=
    ((Finset.univ.inf' Finset.univ_nonempty (maxDisp π₁ π₂) : ℕ) : ℝ) / ((n : ℝ) - 1)
  ```
  The paper defines ρ∞ only for n ≥ 2. For n ≤ 1, Lean's formula gives the value 0 (the numerator
  is 0 for n ≤ 1, and Lean sets x/0 = 0), but no main statement depends on it: Theorem 1.1's lower bound
  assumes n ≥ 2, and the other statements hold for all n ≥ n₀, in particular for all
  n ≥ max(n₀, 2), which is the paper's statement. The paper's triangle inequality for ρ∞ (the
  Remark "Metric property" in §2), used in the proof of Theorem 1.1, is proved in Lean, in the form
  multiplied by n − 1 (for n ≠ 1), as `mul_rhoInf_triangle`.
- **ε-far, Definition 2.3**: π is ε-far from a property P if the minimum of ρ∞(π, γ) over the
  length-n permutations γ with P is at least ε.
  ```lean
  def IsFar (ε : ℝ) (π : Perm (Fin n)) (Pn : Set (Perm (Fin n))) : Prop :=
    ∀ γ ∈ Pn, ε ≤ rhoInf π γ
  def IsFarFromFree (ε : ℝ) (σ : Perm (Fin k)) (π : Perm (Fin n)) : Prop :=
    IsFar ε π {γ | IsFree σ γ}
  ```
  "Every σ-free γ is at ρ∞-distance at least ε" is the paper's minimum whenever a σ-free
  permutation of length n exists. One always does for patterns of length k ≥ 2 (the identity or
  the decreasing permutation), which covers every main statement.
- **The hypothesis of Theorems 1.2 and 4.1**: k ≥ 4, or σ = (123) or (321). (`oneLine σ = [1, 2, 3]`
  forces k = 3.)
  ```lean
  def ThmHyp (σ : Perm (Fin k)) : Prop :=
    4 ≤ k ∨ oneLine σ = [1, 2, 3] ∨ oneLine σ = [3, 2, 1]
  ```
- **Point set associated with a permutation, Definition 2.1**: points (x₁, y₁), …, (x_n, y_n)
  with x₁ < ⋯ < x_n, distinct y's, and π(i) the rank of y_i. In Lean, `Represents π Θ` says the
  list Θ has strictly increasing x-coordinates and y_i < y_j ⇔ π(i) < π(j); `IsAssoc P π` says the
  finite set P is such a list.
  ```lean
  def Represents (π : Perm (Fin n)) (Θ : Fin n → ℝ × ℝ) : Prop :=
    StrictMono (fun i => (Θ i).1) ∧ ∀ i j, (Θ i).2 < (Θ j).2 ↔ π i < π j
  def IsAssoc (P : Finset (ℝ × ℝ)) (π : Perm (Fin n)) : Prop :=
    ∃ Θ : Fin n → ℝ × ℝ, Represents π Θ ∧ P = Finset.univ.image Θ
  ```
- **Canonical point set** (§2, after Definition 2.1): Σ = {(i, σ(i))}, 1-based.
  ```lean
  def canonPt (π : Perm (Fin n)) (i : Fin n) : ℝ × ℝ := ((i : ℝ) + 1, ((π i : ℕ) : ℝ) + 1)
  noncomputable def canon (π : Perm (Fin n)) : Finset (ℝ × ℝ) := Finset.univ.image (canonPt π)
  ```
- **"Σ is the unique σ-copy in Π"**: the paper uses "σ-copy in a point set" without a displayed
  definition (§4, p. 11: "Whenever Θ is a σ-copy, θ denotes the permutation associated with Θ;
  thus θ ≅ σ"; Claim 4.3: "a k-point set associated with a permutation isomorphic to σ"). Lean's
  formal reading: a σ-copy in a point set D is a list Θ of k points of D ordered like σ
  (`CopyIn`); uniqueness says Σ ⊆ P and every σ-copy in P has point set Σ.
  ```lean
  def CopyIn (σ : Perm (Fin k)) (Θ : Fin k → ℝ × ℝ) (D : Set (ℝ × ℝ)) : Prop :=
    Represents σ Θ ∧ ∀ i, Θ i ∈ D
  def IsUniqueCopy (σ : Perm (Fin k)) (P : Set (ℝ × ℝ)) : Prop :=
    (↑(canon σ) : Set (ℝ × ℝ)) ⊆ P ∧
      ∀ Θ : Fin k → ℝ × ℝ, CopyIn σ Θ P → Finset.univ.image Θ = canon σ
  ```
- **Stripes** (§4, Theorem 4.1): H_i = ℝ × (i, i+1), V_i = (i, i+1) × ℝ.
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
  formalization, separate Claude instances (each given a single criterion and no access to the
  others' reviews) compared every Lean statement with the paper in both directions, and all 67
  passed. These reviewers are instances of the same AI model that wrote the code, so they are not
  independent in the way a human referee is. The authors of the paper have read and approved this
  certificate.
  Sections 1a, 3 and 4 are written so that a mathematician can check the main statements against
  the paper without knowing Lean.
- **Differences from the paper that a reader should know.** Each is a convention or a formal
  reading, not a change of meaning:
  - the 0-based/1-based conversion of section 3;
  - the value of ρ∞ for n ≤ 1, which no main statement uses;
  - "ε-far" read as "far from every σ-free permutation", equivalent here because a σ-free
    permutation always exists for k ≥ 2;
  - `IsFar` is defined for every real ε, while Definition 2.3 is stated for ε > 0; every main
    statement assumes ε > 0 or produces ε > 0;
  - the thresholds n₀(k), N₀(k) of Theorems 1.2 and 4.1 are expressed by choosing them before σ,
    equivalent because S_k is finite;
  - "σ-copy in a point set", used without a displayed definition in the paper, is read as
    `CopyIn` (section 4).

  Some hypotheses stated in the paper are not needed by the Lean proofs and are kept so that the
  statements are the paper's; for the main theorems this is only ε > 0 in Theorem 1.1's lower
  bound.
- **Intermediate results.** `LinfPermRemoval/Main.lean` lists the 67 numbered items with their
  Lean names. Some proofs of intermediate results take a different route from the paper's. Several
  claims made inside the paper's proofs by contradiction are stated, as in the paper, under the
  hypothesis being refuted; since that hypothesis never holds, they are true only vacuously. Their
  Lean docstrings say so (search the sources for "vacuously"). Neither point affects the main
  statements, which are proved outright. A detailed audit report (the record of every review and
  the list of differing proof routes) is available from the authors on request.

## 6. How this formalization was produced

The Lean code was written by Claude (Anthropic's AI model), running in Claude Code, under an
autoformalization and auditing workflow designed and directed by Daniel Zhou. Separate Claude
instances, each given one criterion and no access to the others' reviews, audited the Lean
statements against the paper and the proofs for substance (see section 5 for what this does and
does not establish). The formalization builds on Lean's Mathlib library.
