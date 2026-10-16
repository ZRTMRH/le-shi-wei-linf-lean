/-
Formalization of V. H. Le, R. Shi, F. Wei, "$L_\infty$ Permutation Removal Lemma"
(unpublished manuscript). Not part of Mathlib.
-/
import LinfPermRemoval.Basic

/-!
# Section 4: the geometric framework

Section 4 works with point sets in the plane. Notation, all in the paper's 1-based conventions:

* `sval σ i` is the paper's `σ(i)` and `spos σ j` its `σ⁻¹(j)`, for `1 ≤ i, j ≤ k` (both are `0`
  outside that range, a value never used);
* `lv σ = ℓ = σ(1)`, `rv σ = r = σ(k)`, `bp σ = b = σ⁻¹(1)`, `up σ = u = σ⁻¹(k)` (tex l.638);
* `canon σ = Σ = {(i, σ(i))}` and `sig σ i = Σ(i)`, `sigInv σ j = Σ⁻¹(j)`;
* a `σ`-copy in a set `D` is a function `Θ : Fin k → ℝ × ℝ` listing `k` points of `D` in
  increasing `x`-order whose `y`-ranks follow `σ` (`Represents σ Θ`); its point set is
  `univ.image Θ`. The paper's `Θ(i)` is `th Θ i` and its `Θ⁻¹(j)` is `thInv σ Θ j` (1-based);
* `openSeg a v = {a + t v : 0 < t < 1}`, `closedSeg a v T = {a + t v : 0 ≤ t ≤ T}`,
  `lattice = ℤ²`;
* `hStripe i = H_i = ℝ × (i, i+1)`, `vStripe i = V_i = (i, i+1) × ℝ`.
-/

open Equiv Finset

namespace LinfPermRemoval

variable {n k : ℕ}

/-! ## 1-based access to permutations and copies -/

/-- The paper's `σ(i)` for `1 ≤ i ≤ k` (1-based value); `0` outside that range. -/
def sval (σ : Perm (Fin k)) (i : ℕ) : ℕ :=
  if h : 1 ≤ i ∧ i ≤ k then (σ ⟨i - 1, by omega⟩ : ℕ) + 1 else 0

/-- The paper's `σ⁻¹(j)` for `1 ≤ j ≤ k` (1-based position); `0` outside that range. -/
def spos (σ : Perm (Fin k)) (j : ℕ) : ℕ :=
  if h : 1 ≤ j ∧ j ≤ k then (σ.symm ⟨j - 1, by omega⟩ : ℕ) + 1 else 0

/-- `ℓ = σ(1)`. -/
def lv (σ : Perm (Fin k)) : ℕ := sval σ 1
/-- `r = σ(k)`. -/
def rv (σ : Perm (Fin k)) : ℕ := sval σ k
/-- `b = σ⁻¹(1)`. -/
def bp (σ : Perm (Fin k)) : ℕ := spos σ 1
/-- `u = σ⁻¹(k)`. -/
def up (σ : Perm (Fin k)) : ℕ := spos σ k

/-- The paper's `Θ(i)` (1-based): the `i`-th point of `Θ` in the `x`-order; `0` outside
`1 ≤ i ≤ k`. -/
def th (Θ : Fin k → ℝ × ℝ) (i : ℕ) : ℝ × ℝ :=
  if h : 1 ≤ i ∧ i ≤ k then Θ ⟨i - 1, by omega⟩ else 0

/-- The paper's `Θ⁻¹(j)` (1-based): the point of `Θ` whose `y`-rank is `j`. For a copy of `σ`
this is the point in position `σ⁻¹(j)`. -/
def thInv (σ : Perm (Fin k)) (Θ : Fin k → ℝ × ℝ) (j : ℕ) : ℝ × ℝ :=
  if h : 1 ≤ j ∧ j ≤ k then Θ (σ.symm ⟨j - 1, by omega⟩) else 0

/-- `Σ(i) = (i, σ(i))`. -/
def sig (σ : Perm (Fin k)) (i : ℕ) : ℝ × ℝ := th (canonPt σ) i

/-- `Σ⁻¹(j) = (σ⁻¹(j), j)`. -/
def sigInv (σ : Perm (Fin k)) (j : ℕ) : ℝ × ℝ := thInv σ (canonPt σ) j

/-- `Θ` is a `σ`-copy lying in `D`: `Θ` represents `σ` (Definition 2.1) and every point of `Θ`
is in `D`. -/
def CopyIn (σ : Perm (Fin k)) (Θ : Fin k → ℝ × ℝ) (D : Set (ℝ × ℝ)) : Prop :=
  Represents σ Θ ∧ ∀ i, Θ i ∈ D

/-- "`Σ` is the unique `σ`-copy in `P`": `Σ ⊆ P`, and every `σ`-copy in `P` has point set `Σ`. -/
def IsUniqueCopy (σ : Perm (Fin k)) (P : Set (ℝ × ℝ)) : Prop :=
  (↑(canon σ) : Set (ℝ × ℝ)) ⊆ P ∧
    ∀ Θ : Fin k → ℝ × ℝ, CopyIn σ Θ P → Finset.univ.image Θ = canon σ

/-! ## Segments, stripes, slopes -/

/-- `ℤ² ⊂ ℝ²`. -/
def lattice : Set (ℝ × ℝ) := {p | ∃ a b : ℤ, p = ((a : ℝ), (b : ℝ))}

/-- The open segment `{a + t v : 0 < t < 1}`. -/
def openSeg (a v : ℝ × ℝ) : Set (ℝ × ℝ) :=
  {p | ∃ t : ℝ, 0 < t ∧ t < 1 ∧ p = (a.1 + t * v.1, a.2 + t * v.2)}

/-- The closed segment `{a + t v : 0 ≤ t ≤ T}`. -/
def closedSeg (a v : ℝ × ℝ) (T : ℝ) : Set (ℝ × ℝ) :=
  {p | ∃ t : ℝ, 0 ≤ t ∧ t ≤ T ∧ p = (a.1 + t * v.1, a.2 + t * v.2)}

/-- The horizontal stripe `H_i = ℝ × (i, i+1)`. -/
def hStripe (i : ℕ) : Set (ℝ × ℝ) := {p | (i : ℝ) < p.2 ∧ p.2 < (i : ℝ) + 1}

/-- The vertical stripe `V_i = (i, i+1) × ℝ`. -/
def vStripe (i : ℕ) : Set (ℝ × ℝ) := {p | (i : ℝ) < p.1 ∧ p.1 < (i : ℝ) + 1}

/-- **Definition 4.2 (positive slope).** For any two distinct points `p, q ∈ P`,
`p_x < q_x ↔ p_y < q_y`. -/
def PosSlope (P : Set (ℝ × ℝ)) : Prop :=
  ∀ p ∈ P, ∀ q ∈ P, p ≠ q → (p.1 < q.1 ↔ p.2 < q.2)

/-- **Definition 4.2 (negative slope).** For any two distinct points `p, q ∈ P`,
`p_x < q_x ↔ p_y > q_y`. -/
def NegSlope (P : Set (ℝ × ℝ)) : Prop :=
  ∀ p ∈ P, ∀ q ∈ P, p ≠ q → (p.1 < q.1 ↔ q.2 < p.2)

/-! ## The conclusion of Theorem 4.1 -/

open Classical in
/-- The conclusion of Theorem 4.1 for one pattern `σ ∈ S_k` with threshold `N₀`: for every
`N ≥ N₀` there is an `N`-point set `Π ⊂ ℝ²` associated with some `π ∈ S_N` such that `Σ ⊆ Π`,
`Σ` is the unique `σ`-copy in `Π`, and every stripe `H_i`, `V_i` (`i ∈ [k-1]`) contains at least
`(N - k)/(2k)` points of `Π`. -/
def GeomConclusion (σ : Perm (Fin k)) (N₀ : ℕ) : Prop :=
  ∀ N ≥ N₀, ∃ (P : Finset (ℝ × ℝ)) (π : Perm (Fin N)),
    IsAssoc P π ∧ IsUniqueCopy σ ↑P ∧
    ∀ i : ℕ, 1 ≤ i → i ≤ k - 1 →
      ((N : ℝ) - k) / (2 * k) ≤ ((P.filter (· ∈ hStripe i)).card : ℝ) ∧
      ((N : ℝ) - k) / (2 * k) ≤ ((P.filter (· ∈ vStripe i)).card : ℝ)

/-- The hypothesis on the pattern in Theorems 1.2 and 4.1: `k ≥ 4`, or `σ ∈ {(123), (321)}`. -/
def ThmHyp (σ : Perm (Fin k)) : Prop :=
  4 ≤ k ∨ oneLine σ = [1, 2, 3] ∨ oneLine σ = [3, 2, 1]

/-! ## Claim 4.3 -/

namespace GEO

/-- `sval σ (m+1) = σ m + 1` (0-based `m`). -/
theorem sval_succ (σ : Perm (Fin k)) (m : ℕ) (hm : m < k) :
    sval σ (m + 1) = (σ ⟨m, hm⟩ : ℕ) + 1 := by
  unfold sval
  split_ifs with h
  · rfl
  · omega

/-- `spos σ (m+1) = σ⁻¹ m + 1` (0-based `m`). -/
theorem spos_succ (σ : Perm (Fin k)) (m : ℕ) (hm : m < k) :
    spos σ (m + 1) = (σ.symm ⟨m, hm⟩ : ℕ) + 1 := by
  unfold spos
  split_ifs with h
  · rfl
  · omega

/-- `th Θ (m+1) = Θ m` (0-based `m`). -/
theorem th_succ (Θ : Fin k → ℝ × ℝ) (m : ℕ) (hm : m < k) : th Θ (m + 1) = Θ ⟨m, hm⟩ := by
  unfold th
  split_ifs with h
  · rfl
  · omega

/-- `thInv σ Θ (m+1) = Θ (σ⁻¹ m)` (0-based `m`). -/
theorem thInv_succ (σ : Perm (Fin k)) (Θ : Fin k → ℝ × ℝ) (m : ℕ) (hm : m < k) :
    thInv σ Θ (m + 1) = Θ (σ.symm ⟨m, hm⟩) := by
  unfold thInv
  split_ifs with h
  · rfl
  · omega

/-- A set of negative slope contains no two points increasing in both coordinates. -/
theorem not_negSlope {P : Set (ℝ × ℝ)} (hP : NegSlope P) {p q : ℝ × ℝ} (hp : p ∈ P)
    (hq : q ∈ P) (hx : p.1 < q.1) (hy : p.2 < q.2) : False := by
  have hne : p ≠ q := fun h => by rw [h] at hx; exact lt_irrefl _ hx
  have := (hP p hp q hq hne).1 hx
  linarith

/-- A set of positive slope contains no two points increasing in `x` and decreasing in `y`. -/
theorem not_posSlope {P : Set (ℝ × ℝ)} (hP : PosSlope P) {p q : ℝ × ℝ} (hp : p ∈ P)
    (hq : q ∈ P) (hx : p.1 < q.1) (hy : q.2 < p.2) : False := by
  have hne : p ≠ q := fun h => by rw [h] at hx; exact lt_irrefl _ hx
  have := (hP p hp q hq hne).1 hx
  linarith

/-- The argument of Claim 4.3 (1) for a pair of points of a copy in `x`-order: two points
`Θ a, Θ b` (`a < b`) of a `σ`-copy cannot both lie in a set `P` that has negative slope when
`σ a < σ b` and positive slope when `σ b < σ a`. -/
theorem pair_x {σ : Perm (Fin k)} {Θ : Fin k → ℝ × ℝ} (hrep : Represents σ Θ)
    {P : Set (ℝ × ℝ)} {a b : Fin k} (hab : a < b) (ha : Θ a ∈ P) (hb : Θ b ∈ P)
    (hslope : (σ a < σ b → NegSlope P) ∧ (σ b < σ a → PosSlope P)) : False := by
  have hx : (Θ a).1 < (Θ b).1 := hrep.1 hab
  rcases lt_or_gt_of_ne (σ.injective.ne hab.ne) with h | h
  · exact not_negSlope (hslope.1 h) ha hb hx ((hrep.2 a b).2 h)
  · exact not_posSlope (hslope.2 h) ha hb hx ((hrep.2 b a).2 h)

/-- The argument of Claim 4.3 (1) for a pair of points of a copy in `y`-order: two points
`Θ a, Θ b` with `σ a < σ b` cannot both lie in a set `P` that has negative slope when `a < b`
and positive slope when `b < a`. -/
theorem pair_y {σ : Perm (Fin k)} {Θ : Fin k → ℝ × ℝ} (hrep : Represents σ Θ)
    {P : Set (ℝ × ℝ)} {a b : Fin k} (hab : σ a < σ b) (ha : Θ a ∈ P) (hb : Θ b ∈ P)
    (hslope : (a < b → NegSlope P) ∧ (b < a → PosSlope P)) : False := by
  have hy : (Θ a).2 < (Θ b).2 := (hrep.2 a b).2 hab
  have hne : a ≠ b := fun h => by rw [h] at hab; exact lt_irrefl _ hab
  rcases lt_or_gt_of_ne hne with h | h
  · exact not_negSlope (hslope.1 h) ha hb (hrep.1 h) hy
  · exact not_posSlope (hslope.2 h) hb ha (hrep.1 h) hy

end GEO

/-- **Claim 4.3 (1).** Let `D ⊇ Σ` and let `Θ ⊆ D` be a `σ`-copy. If `P_L = {p ∈ D : p_x < 1}` has
negative slope when `σ(1) < σ(2)` and positive slope when `σ(1) > σ(2)`, then
`Θ ∩ P_L ⊆ {Θ(1)}`. The proof does not use `hD : Σ ⊆ D`; the paper states it (tex l.654), and it is
kept to match the paper. -/
theorem claim_4_3_1 (σ : Perm (Fin k)) (hk : 2 ≤ k) (D : Set (ℝ × ℝ))
    (hD : (↑(canon σ) : Set (ℝ × ℝ)) ⊆ D) (Θ : Fin k → ℝ × ℝ) (hΘ : CopyIn σ Θ D)
    (hslope : (sval σ 1 < sval σ 2 → NegSlope {p | p ∈ D ∧ p.1 < 1}) ∧
      (sval σ 2 < sval σ 1 → PosSlope {p | p ∈ D ∧ p.1 < 1})) :
    ∀ i, Θ i ∈ {p | p ∈ D ∧ p.1 < 1} → Θ i = th Θ 1 := by
  obtain ⟨hrep, hin⟩ := hΘ
  intro i hi
  have hab : (⟨0, by omega⟩ : Fin k) < ⟨1, by omega⟩ := Fin.lt_def.2 (by simp)
  rw [show th Θ 1 = Θ ⟨0, by omega⟩ from GEO.th_succ Θ 0 (by omega)]
  by_contra hne
  have hi1 : 1 ≤ (i : ℕ) := by
    rcases Nat.eq_zero_or_pos (i : ℕ) with h | h
    · exact absurd (congrArg Θ (Fin.ext h)) hne
    · exact h
  have hxb : (Θ ⟨1, by omega⟩).1 ≤ (Θ i).1 := hrep.1.monotone (Fin.le_def.2 hi1)
  have hxa := hrep.1 hab
  refine GEO.pair_x (P := {p | p ∈ D ∧ p.1 < 1}) hrep hab
    ⟨hin _, by linarith [hi.2]⟩ ⟨hin _, by linarith [hi.2]⟩ ?_
  rw [show sval σ 1 = _ from GEO.sval_succ σ 0 (by omega),
    show sval σ 2 = _ from GEO.sval_succ σ 1 (by omega)] at hslope
  refine ⟨fun h => hslope.1 ?_, fun h => hslope.2 ?_⟩ <;>
    · have := Fin.lt_def.1 h
      omega

/-- **Claim 4.3 (2).** With `P_R = {p ∈ D : p_x > k}` of negative slope when `σ(k-1) < σ(k)` and
positive slope when `σ(k-1) > σ(k)`: `Θ ∩ P_R ⊆ {Θ(k)}`. The proof does not use `hD : Σ ⊆ D`; the
paper states it (tex l.654), and it is kept to match the paper. -/
theorem claim_4_3_2 (σ : Perm (Fin k)) (hk : 2 ≤ k) (D : Set (ℝ × ℝ))
    (hD : (↑(canon σ) : Set (ℝ × ℝ)) ⊆ D) (Θ : Fin k → ℝ × ℝ) (hΘ : CopyIn σ Θ D)
    (hslope : (sval σ (k - 1) < sval σ k → NegSlope {p | p ∈ D ∧ (k : ℝ) < p.1}) ∧
      (sval σ k < sval σ (k - 1) → PosSlope {p | p ∈ D ∧ (k : ℝ) < p.1})) :
    ∀ i, Θ i ∈ {p | p ∈ D ∧ (k : ℝ) < p.1} → Θ i = th Θ k := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  obtain ⟨hrep, hin⟩ := hΘ
  intro i hi
  have hab : (⟨m, by omega⟩ : Fin (m + 2)) < ⟨m + 1, by omega⟩ := Fin.lt_def.2 (by simp)
  rw [show th Θ (m + 2) = Θ ⟨m + 1, by omega⟩ from GEO.th_succ Θ (m + 1) (by omega)]
  by_contra hne
  have hi1 : (i : ℕ) ≤ m := by
    by_contra h
    exact hne (congrArg Θ (Fin.ext (by dsimp only; omega)))
  have hxa : (Θ i).1 ≤ (Θ ⟨m, by omega⟩).1 := hrep.1.monotone (Fin.le_def.2 hi1)
  have hxb := hrep.1 hab
  refine GEO.pair_x (P := {p | p ∈ D ∧ ((m + 2 : ℕ) : ℝ) < p.1}) hrep hab
    ⟨hin _, by linarith [hi.2]⟩ ⟨hin _, by linarith [hi.2]⟩ ?_
  rw [show m + 2 - 1 = m + 1 by omega, show sval σ (m + 1) = _ from GEO.sval_succ σ m (by omega),
    show sval σ (m + 2) = _ from GEO.sval_succ σ (m + 1) (by omega)] at hslope
  refine ⟨fun h => hslope.1 ?_, fun h => hslope.2 ?_⟩ <;>
    · have := Fin.lt_def.1 h
      omega

/-- **Claim 4.3 (3).** With `P_B = {p ∈ D : p_y < 1}` of negative slope when
`σ⁻¹(1) < σ⁻¹(2)` and positive slope when `σ⁻¹(1) > σ⁻¹(2)`: `Θ ∩ P_B ⊆ {Θ⁻¹(1)}`. The proof does
not use `hD : Σ ⊆ D`; the paper states it (tex l.654), and it is kept to match the paper. -/
theorem claim_4_3_3 (σ : Perm (Fin k)) (hk : 2 ≤ k) (D : Set (ℝ × ℝ))
    (hD : (↑(canon σ) : Set (ℝ × ℝ)) ⊆ D) (Θ : Fin k → ℝ × ℝ) (hΘ : CopyIn σ Θ D)
    (hslope : (spos σ 1 < spos σ 2 → NegSlope {p | p ∈ D ∧ p.2 < 1}) ∧
      (spos σ 2 < spos σ 1 → PosSlope {p | p ∈ D ∧ p.2 < 1})) :
    ∀ i, Θ i ∈ {p | p ∈ D ∧ p.2 < 1} → Θ i = thInv σ Θ 1 := by
  obtain ⟨hrep, hin⟩ := hΘ
  intro i hi
  set a : Fin k := σ.symm ⟨0, by omega⟩ with ha
  set b : Fin k := σ.symm ⟨1, by omega⟩ with hb
  have hab : σ a < σ b := by simp [ha, hb, Fin.lt_def]
  rw [show thInv σ Θ 1 = Θ a from GEO.thInv_succ σ Θ 0 (by omega)]
  by_contra hne
  have hi1 : σ b ≤ σ i := by
    rw [hb, Equiv.apply_symm_apply, Fin.le_def]
    rcases Nat.eq_zero_or_pos (σ i : ℕ) with h | h
    · refine absurd (congrArg Θ ?_) hne
      rw [ha, Equiv.eq_symm_apply]
      exact Fin.ext h
    · exact h
  have hyb : (Θ b).2 ≤ (Θ i).2 := by
    rcases hi1.lt_or_eq with h | h
    · exact ((hrep.2 b i).2 h).le
    · rw [σ.injective h]
  have hya := (hrep.2 a b).2 hab
  refine GEO.pair_y (P := {p | p ∈ D ∧ p.2 < 1}) hrep hab
    ⟨hin _, by linarith [hi.2]⟩ ⟨hin _, by linarith [hi.2]⟩ ?_
  rw [show spos σ 1 = _ from GEO.spos_succ σ 0 (by omega),
    show spos σ 2 = _ from GEO.spos_succ σ 1 (by omega)] at hslope
  refine ⟨fun h => hslope.1 ?_, fun h => hslope.2 ?_⟩ <;>
    · have := Fin.lt_def.1 h
      omega

/-- **Claim 4.3 (4).** With `P_U = {p ∈ D : p_y > k}` of negative slope when
`σ⁻¹(k-1) < σ⁻¹(k)` and positive slope when `σ⁻¹(k-1) > σ⁻¹(k)`: `Θ ∩ P_U ⊆ {Θ⁻¹(k)}`. The proof
does not use `hD : Σ ⊆ D`; the paper states it (tex l.654), and it is kept to match the paper. -/
theorem claim_4_3_4 (σ : Perm (Fin k)) (hk : 2 ≤ k) (D : Set (ℝ × ℝ))
    (hD : (↑(canon σ) : Set (ℝ × ℝ)) ⊆ D) (Θ : Fin k → ℝ × ℝ) (hΘ : CopyIn σ Θ D)
    (hslope : (spos σ (k - 1) < spos σ k → NegSlope {p | p ∈ D ∧ (k : ℝ) < p.2}) ∧
      (spos σ k < spos σ (k - 1) → PosSlope {p | p ∈ D ∧ (k : ℝ) < p.2})) :
    ∀ i, Θ i ∈ {p | p ∈ D ∧ (k : ℝ) < p.2} → Θ i = thInv σ Θ k := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  obtain ⟨hrep, hin⟩ := hΘ
  intro i hi
  set a : Fin (m + 2) := σ.symm ⟨m, by omega⟩ with ha
  set b : Fin (m + 2) := σ.symm ⟨m + 1, by omega⟩ with hb
  have hab : σ a < σ b := by simp [ha, hb, Fin.lt_def]
  rw [show thInv σ Θ (m + 2) = Θ b from GEO.thInv_succ σ Θ (m + 1) (by omega)]
  by_contra hne
  have hi1 : σ i ≤ σ a := by
    rw [ha, Equiv.apply_symm_apply, Fin.le_def]
    show (σ i : ℕ) ≤ m
    by_contra h
    refine hne (congrArg Θ ?_)
    rw [hb, Equiv.eq_symm_apply]
    exact Fin.ext (by dsimp only; omega)
  have hya : (Θ i).2 ≤ (Θ a).2 := by
    rcases hi1.lt_or_eq with h | h
    · exact ((hrep.2 i a).2 h).le
    · rw [σ.injective h]
  have hyb := (hrep.2 a b).2 hab
  refine GEO.pair_y (P := {p | p ∈ D ∧ ((m + 2 : ℕ) : ℝ) < p.2}) hrep hab
    ⟨hin _, by linarith [hi.2]⟩ ⟨hin _, by linarith [hi.2]⟩ ?_
  rw [show m + 2 - 1 = m + 1 by omega, show spos σ (m + 1) = _ from GEO.spos_succ σ m (by omega),
    show spos σ (m + 2) = _ from GEO.spos_succ σ (m + 1) (by omega)] at hslope
  refine ⟨fun h => hslope.1 ?_, fun h => hslope.2 ?_⟩ <;>
    · have := Fin.lt_def.1 h
      omega

/-! ## Pattern families excluded by the later subsections -/

/-- Subsection 4.1, first family: `σ = (ℓ(ℓ-1)⋯21)(k(k-1)⋯(r+1)r)` with `r = ℓ + 1` and
`1 ≤ ℓ ≤ k - 1`: positions `1..ℓ` carry `ℓ, …, 1` and positions `ℓ+1..k` carry `k, …, ℓ+1`. -/
def IsTwoBlockA (σ : Perm (Fin k)) (ℓ : ℕ) : Prop :=
  1 ≤ ℓ ∧ ℓ + 1 ≤ k ∧
    ∀ i, 1 ≤ i → i ≤ k → sval σ i = if i ≤ ℓ then ℓ + 1 - i else k + ℓ + 1 - i

/-- Subsection 4.1, second family: `σ = (ℓ(ℓ+1)⋯(k-1)k)(12⋯(r-1)r)` with `ℓ = r + 1` and
`1 ≤ r ≤ k - 1`: positions `1..k-r` carry `r+1, …, k` and positions `k-r+1..k` carry `1, …, r`. -/
def IsTwoBlockB (σ : Perm (Fin k)) (r : ℕ) : Prop :=
  1 ≤ r ∧ r + 1 ≤ k ∧
    ∀ i, 1 ≤ i → i ≤ k → sval σ i = if i ≤ k - r then r + i else i - (k - r)

/-- `σ` is one of the patterns of Subsection 4.1 ("two monotone blocks"). -/
def IsTwoBlock (σ : Perm (Fin k)) : Prop := (∃ ℓ, IsTwoBlockA σ ℓ) ∨ (∃ r, IsTwoBlockB σ r)

/-- `σ` is one of the four patterns `(31524), (24153), (42513), (35142)` of Subsection 4.2. -/
def IsExcFive (σ : Perm (Fin k)) : Prop :=
  oneLine σ ∈ [[3, 1, 5, 2, 4], [2, 4, 1, 5, 3], [4, 2, 5, 1, 3], [3, 5, 1, 4, 2]]

/-! ## Tests -/

example : sval (Equiv.swap (1 : Fin 3) 2) 2 = 3 := by decide
example : spos (Equiv.swap (1 : Fin 3) 2) 2 = 3 := by decide
/-- `sval` is `0` outside `[1, k]`. -/
example : sval (1 : Perm (Fin 3)) 0 = 0 ∧ sval (1 : Perm (Fin 3)) 4 = 0 := by decide

/-- `(132)` is the two-block pattern with `ℓ = 1`. -/
example : IsTwoBlockA (Equiv.swap (1 : Fin 3) 2) 1 := by
  refine ⟨le_rfl, by norm_num, ?_⟩
  intro i h1 h2
  interval_cases i <;> decide

/-- `(2143)` is the two-block pattern with `ℓ = 2`. -/
example : IsTwoBlockA (Equiv.swap (0 : Fin 4) 1 * Equiv.swap 2 3) 2 := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  intro i h1 h2
  interval_cases i <;> decide

/-- `(231)` is the second-family two-block pattern with `r = 1`. -/
example : IsTwoBlockB (Equiv.swap (0 : Fin 3) 2 * Equiv.swap 0 1) 1 := by
  refine ⟨le_rfl, by norm_num, ?_⟩
  intro i h1 h2
  interval_cases i <;> decide

example : oneLine (Equiv.swap (0 : Fin 3) 2 * Equiv.swap 0 1) = [2, 3, 1] := by decide

end LinfPermRemoval
