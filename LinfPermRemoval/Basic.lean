/-
Formalization of V. H. Le, R. Shi, F. Wei, "$L_\infty$ Permutation Removal Lemma"
(unpublished manuscript). Not part of Mathlib.
-/
import Mathlib

/-!
# Basic definitions (Section 1 and Section 2 of the paper)

Conventions used throughout the project.

* A permutation of length `n` is `π : Equiv.Perm (Fin n)`. Lean's `Fin n` is `{0, …, n-1}`,
  whereas the paper writes `[n] = {1, …, n}`: the paper's position `i` is the Lean index `i - 1`
  and the paper's value `π(i)` is the Lean value `π (i - 1) + 1`. Every statement below converts
  explicitly; distances such as `|i - θ(i)|` are unaffected by the shift.
* Patterns are written in the paper's one-line notation through `oneLine`, e.g.
  `oneLine σ = [1, 3, 2]` is the paper's `σ = (132)`.
* Points of the plane are `ℝ × ℝ`; `p.1` is the paper's `p_x` and `p.2` its `p_y`. Point sets in
  the plane keep the paper's 1-based coordinates (the canonical point of position `i` is
  `(i, π(i))` with `i ∈ [n]`), so the segments of Section 4 are written with the paper's numbers.
-/

open Equiv Finset

namespace LinfPermRemoval

variable {n k : ℕ}

/-! ## Permutations, patterns and copies (Section 1, tex l.117–119) -/

/-- The one-line notation of a permutation, 1-based: `oneLine σ = [σ(1), …, σ(k)]`.
For instance the paper's pattern `(132)` is the `σ : Perm (Fin 3)` with
`oneLine σ = [1, 3, 2]`. -/
def oneLine (σ : Perm (Fin k)) : List ℕ := List.ofFn fun i => (σ i : ℕ) + 1

/-- A `σ`-copy in `π` (tex l.117–118): a set `S` of `k` indices which, listed increasingly as
`i_1 < ⋯ < i_k` (this is `S.orderEmbOfFin`), satisfies `π(i_a) < π(i_b) ↔ σ(a) < σ(b)` for all
`a, b`. -/
def IsCopy (σ : Perm (Fin k)) (π : Perm (Fin n)) (S : Finset (Fin n)) : Prop :=
  ∃ h : S.card = k, ∀ a b : Fin k,
    π (S.orderEmbOfFin h a) < π (S.orderEmbOfFin h b) ↔ σ a < σ b

open Classical in
/-- `N_σ(π)`, the number of `σ`-copies in `π` (tex l.119). -/
noncomputable def numCopies (σ : Perm (Fin k)) (π : Perm (Fin n)) : ℕ :=
  ((Finset.univ : Finset (Finset (Fin n))).filter (IsCopy σ π)).card

/-- `π` is `σ`-free when `N_σ(π) = 0` (tex l.119). -/
def IsFree (σ : Perm (Fin k)) (π : Perm (Fin n)) : Prop := numCopies σ π = 0

/-! ## Point sets associated with a permutation (Definition 2.1) -/

/-- `Θ` lists the points of a point set associated with `π`, in increasing `x`-order
(Definition 2.1): the `x`-coordinates `x_1 < ⋯ < x_n` are strictly increasing, and the `y`-rank
of the `i`-th point is `π(i)`, i.e. `y_i < y_j ↔ π(i) < π(j)` (this also forces the
`y`-coordinates to be pairwise distinct). The paper's `Π(i)` is `Θ i`, and its `Π⁻¹(j)` is
`Θ (π.symm j)`. -/
def Represents (π : Perm (Fin n)) (Θ : Fin n → ℝ × ℝ) : Prop :=
  StrictMono (fun i => (Θ i).1) ∧ ∀ i j, (Θ i).2 < (Θ j).2 ↔ π i < π j

/-- **Definition 2.1.** A finite point set `P ⊂ ℝ²` is associated with the permutation `π` of
length `n` if its points can be listed as `(x_1, y_1), …, (x_n, y_n)` with
`x_1 < x_2 < ⋯ < x_n`, the `y`-coordinates pairwise distinct, and `π(i)` the rank of `y_i`. -/
def IsAssoc (P : Finset (ℝ × ℝ)) (π : Perm (Fin n)) : Prop :=
  ∃ Θ : Fin n → ℝ × ℝ, Represents π Θ ∧ P = Finset.univ.image Θ

/-- "`P` is associated with a permutation" (with no permutation named): `P` is associated with
some permutation of length `|P|`.

The paper's uniqueness lemmas assume it (e.g. tex l.724), and the Lean statements of Lemmas 4.5,
4.10, 4.13, 4.16, 4.20, 4.29, 4.40 and Corollary 4.35 keep it to match the paper, but their proofs
do not use it: uniqueness holds for every point set in the support. -/
def IsPermPointSet (P : Finset (ℝ × ℝ)) : Prop := ∃ π : Perm (Fin P.card), IsAssoc P π

/-- The canonical point of position `i` (paper: `Π_π(i) = (i, π(i))`, 1-based), tex l.180–182. -/
def canonPt (π : Perm (Fin n)) (i : Fin n) : ℝ × ℝ := ((i : ℝ) + 1, ((π i : ℕ) : ℝ) + 1)

/-- The canonical point set `Π_π = {(i, π(i)) : 1 ≤ i ≤ n} ⊂ [n] × [n]` (tex l.180–182). -/
noncomputable def canon (π : Perm (Fin n)) : Finset (ℝ × ℝ) := Finset.univ.image (canonPt π)

/-! ## The distance `ρ_∞` (Definition 2.2) -/

/-- `max_{1 ≤ i ≤ n} max{|i - θ(i)|, |π₁(i) - π₂(θ(i))|}` for a matching `θ ∈ S_n`. -/
def maxDisp (π₁ π₂ θ : Perm (Fin n)) : ℕ :=
  Finset.univ.sup fun i : Fin n =>
    max ((i : ℤ) - (θ i : ℤ)).natAbs ((π₁ i : ℤ) - (π₂ (θ i) : ℤ)).natAbs

/-- **Definition 2.2.** `ρ_∞(π₁, π₂) = (1/(n-1)) min_{θ ∈ S_n} max_i max{|i-θ(i)|, |π₁(i)-π₂(θ(i))|}`.
The paper defines it only for `n ≥ 2`; for `n ≤ 1` the Lean value is a junk value (division by
`0` or by `-1`), and every statement using it assumes `n ≥ 2` or is insensitive to it. -/
noncomputable def rhoInf (π₁ π₂ : Perm (Fin n)) : ℝ :=
  ((Finset.univ.inf' Finset.univ_nonempty (maxDisp π₁ π₂) : ℕ) : ℝ) / ((n : ℝ) - 1)

/-! ## Being far from a property (Definition 2.3) -/

/-- **Definition 2.3.** `π` (of length `n`) is `ε`-far from the property whose length-`n` members
form `Pn` if `min_{γ ∈ Pn} ρ_∞(π, γ) ≥ ε`, i.e. every `γ ∈ Pn` has `ρ_∞(π, γ) ≥ ε`.
(When `Pn` is empty the paper's minimum does not exist; this definition is then vacuously true.
For the property "`σ`-free" with `|σ| ≥ 2`, `Pn` is never empty.) -/
def IsFar (ε : ℝ) (π : Perm (Fin n)) (Pn : Set (Perm (Fin n))) : Prop :=
  ∀ γ ∈ Pn, ε ≤ rhoInf π γ

/-- `π` is `ε`-far from being `σ`-free. -/
def IsFarFromFree (ε : ℝ) (σ : Perm (Fin k)) (π : Perm (Fin n)) : Prop :=
  IsFar ε π {γ | IsFree σ γ}

/-! ## Fact 2.4 -/

namespace BAS

lemma isCopy_image_of_strictMono {σ : Perm (Fin k)} {π : Perm (Fin n)} (f : Fin k → Fin n)
    (hf : StrictMono f) (hv : ∀ a b, π (f a) < π (f b) ↔ σ a < σ b) :
    IsCopy σ π (univ.image f) := by
  have hc : (univ.image f).card = k := by
    rw [card_image_of_injective _ hf.injective, card_univ, Fintype.card_fin]
  refine ⟨hc, ?_⟩
  have := orderEmbOfFin_unique hc (f := f) (fun x => mem_image_of_mem f (mem_univ x)) hf
  intro a b
  rw [← this]
  exact hv a b

lemma not_isCopy_of_isFree {σ : Perm (Fin k)} {γ : Perm (Fin n)} (h : IsFree σ γ)
    (S : Finset (Fin n)) : ¬ IsCopy σ γ S := by
  classical
  intro hS
  unfold IsFree numCopies at h
  rw [card_eq_zero, filter_eq_empty_iff] at h
  exact h (mem_univ S) (by convert hS)

lemma exists_matching (π₁ π₂ : Perm (Fin n)) : ∃ θ : Perm (Fin n),
    (rhoInf π₁ π₂) = (maxDisp π₁ π₂ θ : ℝ) / ((n : ℝ) - 1) := by
  obtain ⟨θ, -, hθ⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty (α := Perm (Fin n)))
    (maxDisp π₁ π₂)
  exact ⟨θ, by rw [rhoInf, hθ]⟩

lemma disp_le (π₁ π₂ θ : Perm (Fin n)) (i : Fin n) :
    ((i : ℤ) - (θ i : ℤ)).natAbs ≤ maxDisp π₁ π₂ θ ∧
    ((π₁ i : ℤ) - (π₂ (θ i) : ℤ)).natAbs ≤ maxDisp π₁ π₂ θ := by
  have h := Finset.le_sup (f := fun i : Fin n =>
    max ((i : ℤ) - (θ i : ℤ)).natAbs ((π₁ i : ℤ) - (π₂ (θ i) : ℤ)).natAbs) (mem_univ i)
  exact ⟨le_trans (le_max_left _ _) h, le_trans (le_max_right _ _) h⟩

end BAS

/-- **Fact 2.4.** If the indices `S` form a `σ`-copy in `π` and any two distinct indices of `S`
are at least `2ε(n-1)` apart both in position and in value, then `π` is `ε`-far from being
`σ`-free. (The ambient conventions of Definitions 2.2–2.3, `ε > 0` and `n ≥ 2`, are kept as
hypotheses.) The proof does not use `hε : 0 < ε`, an ambient convention rather than a hypothesis of
Fact 2.4 itself (tex l.243–247); for `ε ≤ 0` the statement is trivially true. It is kept to match
the paper. -/
theorem fact_2_4 (σ : Perm (Fin k)) (π : Perm (Fin n)) (S : Finset (Fin n)) (ε : ℝ)
    (hε : 0 < ε) (hn : 2 ≤ n) (hS : IsCopy σ π S)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
      2 * ε * ((n : ℝ) - 1) ≤ |(i : ℝ) - (j : ℝ)| ∧
      2 * ε * ((n : ℝ) - 1) ≤ |((π i : ℕ) : ℝ) - ((π j : ℕ) : ℝ)|) :
    IsFarFromFree ε σ π := by
  intro γ hγ
  by_contra hlt
  push Not at hlt
  obtain ⟨θ, hθ⟩ := BAS.exists_matching π γ
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  set m : ℕ := maxDisp π γ θ with hm
  have hmε : (m : ℝ) < ε * ((n : ℝ) - 1) := by
    rw [hθ, div_lt_iff₀ hn1] at hlt
    exact hlt
  obtain ⟨hc, hcop⟩ := hS
  set f := S.orderEmbOfFin hc with hf
  have hfS : ∀ a, f a ∈ S := fun a => S.orderEmbOfFin_mem hc a
  have dx : ∀ i : Fin n, |((i : ℕ) : ℝ) - ((θ i : ℕ) : ℝ)| ≤ m := by
    intro i
    have h := (BAS.disp_le π γ θ i).1
    have e : ((((i : ℤ) - (θ i : ℤ)).natAbs : ℕ) : ℝ) = |((i : ℕ) : ℝ) - ((θ i : ℕ) : ℝ)| := by
      rw [Nat.cast_natAbs]; push_cast; rfl
    rw [← e]; exact_mod_cast h
  have dy : ∀ i : Fin n, |((π i : ℕ) : ℝ) - ((γ (θ i) : ℕ) : ℝ)| ≤ m := by
    intro i
    have h := (BAS.disp_le π γ θ i).2
    have e : ((((π i : ℤ) - (γ (θ i) : ℤ)).natAbs : ℕ) : ℝ) =
        |((π i : ℕ) : ℝ) - ((γ (θ i) : ℕ) : ℝ)| := by
      rw [Nat.cast_natAbs]; push_cast; rfl
    rw [← e]; exact_mod_cast h
  have hmono : StrictMono (fun a => θ (f a)) := by
    intro a b hab
    have hfab : f a < f b := f.strictMono hab
    have hne : f a ≠ f b := ne_of_lt hfab
    have hgap := (hsep _ (hfS a) _ (hfS b) hne).1
    have hlt' : ((f a : ℕ) : ℝ) < ((f b : ℕ) : ℝ) := by exact_mod_cast hfab
    rw [abs_sub_comm, abs_of_pos (by linarith)] at hgap
    have h1 := dx (f a); have h2 := dx (f b)
    rw [abs_le] at h1 h2
    have : ((θ (f a) : ℕ) : ℝ) < ((θ (f b) : ℕ) : ℝ) := by nlinarith
    exact_mod_cast this
  have hval : ∀ a b, π (f a) < π (f b) → γ (θ (f a)) < γ (θ (f b)) := by
    intro a b hab
    have hne : f a ≠ f b := fun h => by rw [h] at hab; exact lt_irrefl _ hab
    have hgap := (hsep _ (hfS a) _ (hfS b) hne).2
    have hlt' : ((π (f a) : ℕ) : ℝ) < ((π (f b) : ℕ) : ℝ) := by exact_mod_cast hab
    rw [abs_sub_comm, abs_of_pos (by linarith)] at hgap
    have h1 := dy (f a); have h2 := dy (f b)
    rw [abs_le] at h1 h2
    have : ((γ (θ (f a)) : ℕ) : ℝ) < ((γ (θ (f b)) : ℕ) : ℝ) := by nlinarith
    exact_mod_cast this
  have hcopy : IsCopy σ γ (univ.image fun a => θ (f a)) := by
    refine BAS.isCopy_image_of_strictMono _ hmono ?_
    intro a b
    constructor
    · intro h
      rcases lt_trichotomy (π (f a)) (π (f b)) with h' | h' | h'
      · exact (hcop a b).1 h'
      · have := f.injective (π.injective h'); subst this; exact absurd h (lt_irrefl _)
      · exact absurd (hval b a h') (not_lt.2 h.le)
    · intro h
      exact hval a b ((hcop a b).2 h)
  exact BAS.not_isCopy_of_isFree hγ _ hcopy


/-! ## Tests of the definitions -/

/-- The paper's pattern `(132)`. -/
def p132 : Perm (Fin 3) := Equiv.swap 1 2

example : oneLine p132 = [1, 3, 2] := by decide

/-- The identity of length 2 is the paper's `(12)`. -/
example : oneLine (1 : Perm (Fin 2)) = [1, 2] := by decide

/-- `{0, 2}` (paper: positions 1 and 3) is a `(12)`-copy in the identity of length 3. -/
example : IsCopy (1 : Perm (Fin 2)) (1 : Perm (Fin 3)) {0, 2} := by
  refine ⟨rfl, ?_⟩
  have h0 := Finset.orderEmbOfFin_zero (s := ({0, 2} : Finset (Fin 3))) rfl (by norm_num)
  have h1 := Finset.orderEmbOfFin_last (s := ({0, 2} : Finset (Fin 3))) rfl (by norm_num)
  have e0 : ({0, 2} : Finset (Fin 3)).min' (by simp) = 0 := by decide
  have e1 : ({0, 2} : Finset (Fin 3)).max' (by simp) = 2 := by decide
  intro a b
  fin_cases a <;> fin_cases b <;> simp_all

/-- In the decreasing permutation of length 3, `{0, 2}` is not a `(12)`-copy. -/
example : ¬ IsCopy (1 : Perm (Fin 2)) (Fin.revPerm : Perm (Fin 3)) {0, 2} := by
  rintro ⟨h, hab⟩
  have h0 := Finset.orderEmbOfFin_zero (s := ({0, 2} : Finset (Fin 3))) h (by norm_num)
  have h1 := Finset.orderEmbOfFin_last (s := ({0, 2} : Finset (Fin 3))) h (by norm_num)
  have e0 : ({0, 2} : Finset (Fin 3)).min' (by simp) = 0 := by decide
  have e1 : ({0, 2} : Finset (Fin 3)).max' (by simp) = 2 := by decide
  have := (hab 0 1).2 (by decide)
  simp_all

/-- `ρ_∞((12), (21)) = 1`: both matchings move some point by `1`, and `n - 1 = 1`. -/
example : rhoInf (1 : Perm (Fin 2)) (Equiv.swap 0 1) = 1 := by
  have h : Finset.univ.inf' Finset.univ_nonempty
      (maxDisp (1 : Perm (Fin 2)) (Equiv.swap 0 1)) = 1 := by
    decide
  simp only [rhoInf, h]
  norm_num

/-- `ρ_∞((123), (321)) = 2/2 = 1`: the best matching moves `(1,1)` and `(3,3)` by `2`. -/
example : Finset.univ.inf' Finset.univ_nonempty
    (maxDisp (1 : Perm (Fin 3)) (Fin.revPerm : Perm (Fin 3))) = 2 := by
  decide

/-- `ρ_∞(π, π) = 0` for a sample `π` (the identity matching moves nothing). -/
example : Finset.univ.inf' Finset.univ_nonempty
    (maxDisp (Equiv.swap (0 : Fin 3) 2) (Equiv.swap (0 : Fin 3) 2)) = 0 := by
  decide

end LinfPermRemoval
