import LinfPermRemoval

/-!
# Certificate: the main theorems, as checked by Lean

Each `example` below restates one main theorem of the paper with its full Lean statement and has
Lean confirm that the library proves exactly that statement. A reader who accepts the definitions
used here (listed in `CERTIFICATE.md`, with the paper's wording next to each) needs to read
nothing else: every proof in the library is checked by Lean's kernel.

Check with:  `lake build && lake env lean Certificate.lean`
The `#print axioms` lines must show only `propext`, `Classical.choice`, `Quot.sound`
(Lean's standard axioms): no `sorry`, no additional axiom.
-/

open Equiv LinfPermRemoval

/-- **Theorem 1.1, lower bound.** For σ ∈ {(12),(21),(132),(231),(312),(213)}, n ≥ 2, ε > 0:
if π ∈ S_n is ε-far from σ-free with respect to ρ_∞, then N_σ(π) ≥ ε(n-1). -/
example {k : ℕ} (σ : Perm (Fin k)) (hσ : oneLine σ ∈ linearPatterns)
    (n : ℕ) (hn : 2 ≤ n) (π : Perm (Fin n)) (ε : ℝ) (hε : 0 < ε)
    (hfar : IsFarFromFree ε σ π) :
    ε * ((n : ℝ) - 1) ≤ (numCopies σ π : ℝ) :=
  thm_1_1_lower σ hσ n hn π ε hε hfar

/-- **Theorem 1.1, converse.** For the same σ and 0 < ε ≤ 1/16, for all sufficiently large n there
is an ε-far π ∈ S_n with N_σ(π) ≤ 6εn. -/
example {k : ℕ} (σ : Perm (Fin k)) (hσ : oneLine σ ∈ linearPatterns)
    (ε : ℝ) (hε : 0 < ε) (hε' : ε ≤ 1 / 16) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∃ π : Perm (Fin n),
      IsFarFromFree ε σ π ∧ (numCopies σ π : ℝ) ≤ 6 * ε * n :=
  thm_1_1_upper σ hσ ε hε hε'

/-- **Theorem 1.2.** For σ of length k with k ≥ 4 or σ ∈ {(123),(321)}, there are ε_σ > 0 and
n₀(k) such that for every n ≥ n₀(k) some π ∈ S_n is ε_σ-far from σ-free yet has exactly one
σ-copy. (The threshold n₀ is chosen before σ, so it depends only on k.) -/
example (k : ℕ) :
    ∃ n₀ : ℕ, ∀ σ : Perm (Fin k), ThmHyp σ →
      ∃ ε : ℝ, 0 < ε ∧ ∀ n ≥ n₀, ∃ π : Perm (Fin n),
        IsFarFromFree ε σ π ∧ numCopies σ π = 1 :=
  thm_1_2 k

/-- **Theorem 4.1** (the geometric construction behind Theorem 1.2). -/
example (k : ℕ) : ∃ N₀ : ℕ, ∀ σ : Perm (Fin k), ThmHyp σ → GeomConclusion σ N₀ :=
  thm_4_1 k

#print axioms thm_1_1_lower
#print axioms thm_1_1_upper
#print axioms thm_1_2
#print axioms thm_4_1
