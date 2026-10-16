/-
Formalization of V. H. Le, R. Shi, F. Wei, "$L_\infty$ Permutation Removal Lemma"
(unpublished manuscript). Not part of Mathlib.
-/
import LinfPermRemoval.Geometry

/-!
# Subsection 4.1: patterns with two monotone blocks

After a dihedral symmetry the paper treats `σ = (ℓ(ℓ-1)⋯21)(k(k-1)⋯(r+1)r)`, `r = ℓ + 1`
(`IsTwoBlockA σ ℓ`), in two cases: the boundary case `ℓ = 1` (Construction 4.4, Lemma 4.5) and
the interior case `2 ≤ ℓ`, `r ≤ k - 1`, `ℓ ≤ k/2` (Construction 4.9, Lemma 4.10).

The claims inside the proofs of Lemmas 4.5 and 4.10 are steps of proofs by contradiction: their
context fixes a `σ`-copy `Θ ≠ Σ`, which the lemma shows cannot exist. Their hypothesis bundles
(`Ctx45`, `Ctx410`) are therefore unsatisfiable by design once the lemma is proved; the bundle
without the field `ne` is satisfiable (take `Θ = Σ`).
-/

open Equiv Finset

namespace LinfPermRemoval

variable {k : ℕ}

namespace TB

/-! ### General facts on copies and canonical points (auxiliary) -/

lemma th_eq (Θ : Fin k → ℝ × ℝ) {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ k) :
    th Θ i = Θ ⟨i - 1, by omega⟩ := by
  simp [th, h1, h2]

lemma sval_eq (σ : Perm (Fin k)) {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ k) :
    sval σ i = (σ ⟨i - 1, by omega⟩ : ℕ) + 1 := by
  simp [sval, h1, h2]

lemma sig_eq (σ : Perm (Fin k)) {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ k) :
    sig σ i = ((i : ℝ), ((sval σ i : ℕ) : ℝ)) := by
  rw [sig, th_eq _ h1 h2, sval_eq σ h1 h2]
  simp only [canonPt, Prod.mk.injEq]
  constructor
  · rw [Nat.cast_sub h1]; ring
  · push_cast; ring

lemma mem_canon (σ : Perm (Fin k)) {p : ℝ × ℝ} :
    p ∈ canon σ ↔ ∃ i, 1 ≤ i ∧ i ≤ k ∧ p = sig σ i := by
  constructor
  · intro hp
    obtain ⟨m, -, rfl⟩ := Finset.mem_image.mp hp
    refine ⟨m.1 + 1, by omega, m.2, ?_⟩
    rw [sig, th_eq _ (by omega) m.2]
    simp
  · rintro ⟨i, h1, h2, rfl⟩
    rw [sig, th_eq _ h1 h2]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ _)

lemma copy_x {σ : Perm (Fin k)} {Θ : Fin k → ℝ × ℝ} (hΘ : Represents σ Θ) {i i' : ℕ}
    (h1 : 1 ≤ i) (h : i < i') (h2 : i' ≤ k) : (th Θ i).1 < (th Θ i').1 := by
  rw [th_eq Θ h1 (by omega), th_eq Θ (by omega) h2]
  apply hΘ.1
  show i - 1 < i' - 1
  omega

lemma copy_x_le {σ : Perm (Fin k)} {Θ : Fin k → ℝ × ℝ} (hΘ : Represents σ Θ) {i i' : ℕ}
    (h1 : 1 ≤ i) (h : i ≤ i') (h2 : i' ≤ k) : (th Θ i).1 ≤ (th Θ i').1 := by
  rcases h.lt_or_eq with h | rfl
  · exact (copy_x hΘ h1 h h2).le
  · exact le_rfl

lemma copy_y {σ : Perm (Fin k)} {Θ : Fin k → ℝ × ℝ} (hΘ : Represents σ Θ) {i i' : ℕ}
    (h1 : 1 ≤ i) (h2 : i ≤ k) (h1' : 1 ≤ i') (h2' : i' ≤ k) :
    (th Θ i).2 < (th Θ i').2 ↔ sval σ i < sval σ i' := by
  rw [th_eq Θ h1 h2, th_eq Θ h1' h2', sval_eq σ h1 h2, sval_eq σ h1' h2', hΘ.2, Fin.lt_def]
  omega

lemma copy_inj {σ : Perm (Fin k)} {Θ : Fin k → ℝ × ℝ} (hΘ : Represents σ Θ) {i i' : ℕ}
    (h1 : 1 ≤ i) (h2 : i ≤ k) (h1' : 1 ≤ i') (h2' : i' ≤ k) (h : th Θ i = th Θ i') :
    i = i' := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have := copy_x hΘ h1 hlt h2'; rw [h] at this; exact lt_irrefl _ this
  · have := copy_x hΘ h1' hlt h2; rw [h] at this; exact lt_irrefl _ this

lemma copy_mem {σ : Perm (Fin k)} {Θ : Fin k → ℝ × ℝ} {D : Set (ℝ × ℝ)} (hc : CopyIn σ Θ D)
    {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ k) : th Θ i ∈ D := by
  rw [th_eq Θ h1 h2]; exact hc.2 _

/-- If the point set of a copy is not `Σ`, some point of the copy is not canonical. -/
lemma exists_not_canon {σ : Perm (Fin k)} {Θ : Fin k → ℝ × ℝ} (hΘ : Represents σ Θ)
    (hne : Finset.univ.image Θ ≠ canon σ) : ∃ i, 1 ≤ i ∧ i ≤ k ∧ th Θ i ∉ canon σ := by
  by_contra hcon
  push Not at hcon
  have hinj : Function.Injective Θ := by
    intro a b hab
    exact hΘ.1.injective (by simp only [hab])
  apply hne
  apply Finset.eq_of_subset_of_card_le
  · intro p hp
    obtain ⟨m, -, rfl⟩ := Finset.mem_image.mp hp
    have := hcon (m.1 + 1) (by omega) m.2
    rw [th_eq Θ (by omega) m.2] at this
    simpa using this
  · rw [Finset.card_image_of_injective _ hinj, canon]
    exact (Finset.card_image_le).trans (by simp)

/-- `n`-step integer chain: if `c 0 < c 1 < ⋯ < c d` are integers and `c d ≤ B`, then
`c i ≤ B - (d - i)`. -/
lemma chain_up (c : ℕ → ℝ) (B : ℤ) (d : ℕ) (hint : ∀ i ≤ d, ∃ z : ℤ, c i = z)
    (hlt : ∀ i < d, c i < c (i + 1)) (hB : c d ≤ B) :
    ∀ m ≤ d, c (d - m) ≤ (B : ℝ) - m := by
  intro m
  induction m with
  | zero => intro _; simpa using hB
  | succ m ih =>
    intro hm
    have h1 := ih (by omega)
    have h2 := hlt (d - (m + 1)) (by omega)
    have h3 : d - (m + 1) + 1 = d - m := by omega
    rw [h3] at h2
    obtain ⟨z, hz⟩ := hint (d - (m + 1)) (by omega)
    obtain ⟨w, hw⟩ := hint (d - m) (by omega)
    rw [hz, hw] at h2
    rw [hw] at h1
    rw [hz]
    have h4 : z < w := by exact_mod_cast h2
    have h5 : (z : ℝ) ≤ w - 1 := by exact_mod_cast (by omega : z ≤ w - 1)
    push_cast
    linarith

/-- The pattern of `IsTwoBlockA σ ℓ`, as values. -/
lemma vA {σ : Perm (Fin k)} {ℓ : ℕ} (hσ : IsTwoBlockA σ ℓ) {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ k) :
    sval σ i = if i ≤ ℓ then ℓ + 1 - i else k + ℓ + 1 - i := hσ.2.2 i h1 h2

/-- Comparison of `y`-coordinates of a copy of `IsTwoBlockA σ ℓ`. -/
lemma yA {σ : Perm (Fin k)} {ℓ : ℕ} (hσ : IsTwoBlockA σ ℓ) {Θ : Fin k → ℝ × ℝ}
    (hΘ : Represents σ Θ) {i i' : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ k) (h1' : 1 ≤ i') (h2' : i' ≤ k) :
    (th Θ i).2 < (th Θ i').2 ↔
      (if i ≤ ℓ then ℓ + 1 - i else k + ℓ + 1 - i) <
        (if i' ≤ ℓ then ℓ + 1 - i' else k + ℓ + 1 - i') := by
  rw [copy_y hΘ h1 h2 h1' h2', vA hσ h1 h2, vA hσ h1' h2']

end TB

/-! ## The boundary case `ℓ = 1` -/

/-- **Construction 4.4.** `P_0 = (0, k+1) + t(-1,-1)`, `0 < t < 1`, and `P_i = P_0 + (i, -i)`
for `i ∈ ℤ`; so `P_i` has `x ∈ (i-1, i)`, `y ∈ (k-i, k-i+1)`. -/
def P44 (k : ℕ) (i : ℤ) : Set (ℝ × ℝ) :=
  openSeg ((i : ℝ), (k : ℝ) + 1 - (i : ℝ)) (-1, -1)

/-- **Construction 4.4.** `P_M = ⋃_{i=1}^{k} P_i`. -/
def PM44 (k : ℕ) : Set (ℝ × ℝ) := ⋃ i ∈ Set.Icc (1 : ℤ) k, P44 k i

namespace TB

/-! ### Auxiliary development for Lemma 4.5 -/

lemma mem_P44 {i : ℤ} {p : ℝ × ℝ} (hp : p ∈ P44 k i) :
    (i : ℝ) - 1 < p.1 ∧ p.1 < i ∧ (k : ℝ) - i < p.2 ∧ p.2 < (k : ℝ) - i + 1 ∧
      p.2 = p.1 + k + 1 - 2 * i := by
  simp only [P44, openSeg, Set.mem_ofPred_eq] at hp
  obtain ⟨t, ht0, ht1, rfl⟩ := hp
  refine ⟨by linarith, by linarith, by linarith, by linarith, by ring⟩

lemma mem_P44n {m : ℕ} {p : ℝ × ℝ} (hp : p ∈ P44 k m) :
    (m : ℝ) - 1 < p.1 ∧ p.1 < m ∧ (k : ℝ) - m < p.2 ∧ p.2 < (k : ℝ) - m + 1 ∧
      p.2 = p.1 + k + 1 - 2 * m := by
  have := mem_P44 hp
  push_cast at this
  exact this

/-- `P_i` has positive slope (Construction 4.4). -/
lemma slope_P44 {i : ℤ} {p q : ℝ × ℝ} (hp : p ∈ P44 k i) (hq : q ∈ P44 k i) :
    p.1 < q.1 ↔ p.2 < q.2 := by
  have := (mem_P44 hp).2.2.2.2; have := (mem_P44 hq).2.2.2.2
  constructor <;> intro <;> linarith

/-- The points of `D = Σ ∪ P_M` (Construction 4.4). -/
lemma mem_D45 (σ : Perm (Fin k)) {p : ℝ × ℝ}
    (hp : p ∈ (↑(canon σ) : Set (ℝ × ℝ)) ∪ PM44 k) :
    (∃ i, 1 ≤ i ∧ i ≤ k ∧ p = sig σ i) ∨ ∃ m : ℕ, 1 ≤ m ∧ m ≤ k ∧ p ∈ P44 k m := by
  rcases hp with hp | hp
  · exact Or.inl ((mem_canon σ).1 hp)
  · right
    simp only [PM44, Set.mem_iUnion, Set.mem_Icc, exists_prop] at hp
    obtain ⟨m, ⟨h1, h2⟩, hm⟩ := hp
    lift m to ℕ using (by omega)
    exact ⟨m, by exact_mod_cast h1, by exact_mod_cast h2, hm⟩

lemma sig1 (σ : Perm (Fin k)) (hσ : IsTwoBlockA σ 1) : sig σ 1 = (1, 1) := by
  have hk : 1 ≤ k := by have := hσ.2.1; omega
  rw [sig_eq σ le_rfl hk, vA hσ le_rfl hk]
  simp

lemma sigU (σ : Perm (Fin k)) (hσ : IsTwoBlockA σ 1) {i : ℕ} (h1 : 2 ≤ i) (h2 : i ≤ k) :
    sig σ i = ((i : ℝ), (k : ℝ) + 2 - i) := by
  rw [sig_eq σ (by omega) h2, vA hσ (by omega) h2, ite_eq_right (by omega)]
  simp only [Prod.mk.injEq, true_and]
  rw [Nat.cast_sub (by omega)]
  push_cast; ring

/-- `Θ_U` is decreasing: no two of its points increase in both coordinates. -/
lemma hU45 {σ : Perm (Fin k)} (hσ : IsTwoBlockA σ 1) {Θ : Fin k → ℝ × ℝ}
    (hΘ : Represents σ Θ) {i i' : ℕ} (h1 : 2 ≤ i) (h2 : i ≤ k) (h1' : 2 ≤ i') (h2' : i' ≤ k) :
    ¬ ((th Θ i).1 < (th Θ i').1 ∧ (th Θ i).2 < (th Θ i').2) := by
  rintro ⟨hx, hy⟩
  rw [yA hσ hΘ (by omega) h2 (by omega) h2'] at hy
  rcases lt_trichotomy i i' with h | rfl | h
  · split_ifs at hy <;> omega
  · exact lt_irrefl _ hx
  · exact absurd hx (not_lt.mpr (copy_x hΘ (by omega) h h2).le)

/-- Every point of `Θ_U` lies strictly northeast of `Θ(1)`. -/
lemma hNE45 {σ : Perm (Fin k)} (hσ : IsTwoBlockA σ 1) {Θ : Fin k → ℝ × ℝ}
    (hΘ : Represents σ Θ) {i : ℕ} (h1 : 2 ≤ i) (h2 : i ≤ k) :
    (th Θ 1).1 < (th Θ i).1 ∧ (th Θ 1).2 < (th Θ i).2 :=
  ⟨copy_x hΘ le_rfl (by omega) h2,
    (yA hσ hΘ le_rfl (by omega) (by omega) h2).2 (by split_ifs <;> omega)⟩

/-- For `2 ≤ i₀ ≤ k` with `i₀ = m` or `i₀ = m + 1`, the canonical point `Σ(i₀)` lies strictly
northeast of every point of `P_m` (`Σ(1)` is excluded: it is not northeast of `P_1`). -/
lemma sigNE45 (σ : Perm (Fin k)) (hσ : IsTwoBlockA σ 1) {m : ℕ} {p : ℝ × ℝ}
    (hp : p ∈ P44 k m) {i0 : ℕ} (h1 : 2 ≤ i0) (h2 : i0 ≤ k) (h3 : i0 = m ∨ i0 = m + 1) :
    p.1 < (sig σ i0).1 ∧ p.2 < (sig σ i0).2 := by
  obtain ⟨a1, a2, a3, a4, -⟩ := mem_P44n hp
  rw [sigU σ hσ h1 h2]
  have e1 : (m : ℝ) ≤ i0 := by exact_mod_cast (by omega : m ≤ i0)
  have e2 : (i0 : ℝ) ≤ m + 1 := by exact_mod_cast (by omega : i0 ≤ m + 1)
  constructor <;> simp only <;> linarith

/-- The points of `D` strictly northeast of a point of `P_m` are on `P_m` or are `Σ(m)` or
`Σ(m+1)` (tex l.744). -/
lemma NE45 (σ : Perm (Fin k)) (hσ : IsTwoBlockA σ 1) (hk : 2 ≤ k) {m : ℕ} {p q : ℝ × ℝ}
    (hp : p ∈ P44 k m) (hq : q ∈ (↑(canon σ) : Set (ℝ × ℝ)) ∪ PM44 k)
    (hx : p.1 < q.1) (hy : p.2 < q.2) :
    q ∈ P44 k m ∨ ∃ i0, 2 ≤ i0 ∧ i0 ≤ k ∧ (i0 = m ∨ i0 = m + 1) ∧ q = sig σ i0 := by
  obtain ⟨a1, a2, a3, a4, -⟩ := mem_P44n hp
  rcases mem_D45 σ hq with ⟨i, h1, h2, rfl⟩ | ⟨m', h1, h2, hq'⟩
  · right
    rcases (show i = 1 ∨ 2 ≤ i by omega) with rfl | hi
    · exfalso
      rw [sig1 σ hσ] at hx hy
      simp only at hx hy
      have e1 : (m : ℤ) - 1 < 1 := by exact_mod_cast (show (m : ℝ) - 1 < 1 by linarith)
      have e2 : (k : ℤ) - m < 1 := by exact_mod_cast (show (k : ℝ) - m < 1 by linarith)
      omega
    · refine ⟨i, hi, h2, ?_, rfl⟩
      rw [sigU σ hσ hi h2] at hx hy
      simp only at hx hy
      have e1 : (m : ℤ) - 1 < i := by exact_mod_cast (show (m : ℝ) - 1 < i by linarith)
      have e2 : (k : ℤ) - m < k + 2 - i := by
        exact_mod_cast (show (k : ℝ) - m < k + 2 - i by linarith)
      omega
  · left
    obtain ⟨b1, b2, b3, b4, -⟩ := mem_P44n hq'
    have e1 : (m : ℤ) - 1 < m' := by exact_mod_cast (show (m : ℝ) - 1 < m' by linarith)
    have e2 : (k : ℤ) - m < k - m' + 1 := by
      exact_mod_cast (show (k : ℝ) - m < k - m' + 1 by linarith)
    have : m' = m := by omega
    subst this
    exact hq'

/-- Claim 4.6, with explicit hypotheses (no use of `Θ ≠ Σ`). In the case `Θ(1) ∈ P_j`, the
three points `Θ(2), Θ(3), Θ(4)` are used. -/
lemma c46 (σ : Perm (Fin k)) (hσ : IsTwoBlockA σ 1) (hk : 4 ≤ k) (Θ : Fin k → ℝ × ℝ)
    (hc : CopyIn σ Θ (↑(canon σ) ∪ PM44 k)) : th Θ 1 = sig σ 1 := by
  have hΘ := hc.1
  rcases mem_D45 σ (copy_mem hc le_rfl (by omega : 1 ≤ k)) with
    ⟨m, hm1, hmk, hm⟩ | ⟨m, hm1, hmk, hm⟩
  · rcases (show m = 1 ∨ 2 ≤ m by omega) with rfl | hm2
    · exact hm
    · exfalso
      obtain ⟨hx, hy⟩ := hNE45 hσ hΘ (i := 2) le_rfl (by omega)
      rw [hm, sigU σ hσ hm2 hmk] at hx hy
      simp only at hx hy
      rcases mem_D45 σ (copy_mem hc (by omega : 1 ≤ 2) (by omega : 2 ≤ k)) with
        ⟨m', h1, h2, hq⟩ | ⟨m', h1, h2, hq⟩
      · rw [hq] at hx hy
        rcases (show m' = 1 ∨ 2 ≤ m' by omega) with rfl | hm2'
        · rw [sig1 σ hσ] at hx
          simp only at hx
          have : m < 1 := by exact_mod_cast hx
          omega
        · rw [sigU σ hσ hm2' h2] at hx hy
          simp only at hx hy
          have e1 : m < m' := by exact_mod_cast hx
          have e2 : (m' : ℤ) < m := by
            exact_mod_cast (show (m' : ℝ) < m by linarith)
          omega
      · obtain ⟨b1, b2, b3, b4, -⟩ := mem_P44n hq
        have e1 : (m : ℤ) < m' := by exact_mod_cast (show (m : ℝ) < m' by linarith)
        have e2 : (k : ℤ) + 2 - m < k - m' + 1 := by
          exact_mod_cast (show (k : ℝ) + 2 - m < k - m' + 1 by linarith)
        omega
  · exfalso
    have hcl : ∀ i, 2 ≤ i → i ≤ k → th Θ i ∈ P44 k m ∨
        ∃ i0, 2 ≤ i0 ∧ i0 ≤ k ∧ (i0 = m ∨ i0 = m + 1) ∧ th Θ i = sig σ i0 :=
      fun i h1 h2 => NE45 σ hσ (by omega) hm (copy_mem hc (by omega) h2)
        (hNE45 hσ hΘ h1 h2).1 (hNE45 hσ hΘ h1 h2).2
    have hbad : ∀ a b, 2 ≤ a → a ≤ k → 2 ≤ b → b ≤ k → a ≠ b → th Θ a ∈ P44 k m →
        (th Θ b ∈ P44 k m ∨
          ∃ i0, 2 ≤ i0 ∧ i0 ≤ k ∧ (i0 = m ∨ i0 = m + 1) ∧ th Θ b = sig σ i0) → False := by
      intro a b ha1 ha2 hb1 hb2 hab ha hb
      rcases hb with hb | ⟨i0, h1, h2, h3, hb⟩
      · rcases lt_or_gt_of_ne hab with h | h
        · have hx := copy_x hΘ (by omega) h hb2
          exact hU45 hσ hΘ ha1 ha2 hb1 hb2 ⟨hx, (slope_P44 ha hb).1 hx⟩
        · have hx := copy_x hΘ (by omega) h ha2
          exact hU45 hσ hΘ hb1 hb2 ha1 ha2 ⟨hx, (slope_P44 hb ha).1 hx⟩
      · have := sigNE45 σ hσ ha h1 h2 h3
        rw [← hb] at this
        exact hU45 hσ hΘ ha1 ha2 hb1 hb2 this
    rcases hcl 2 le_rfl (by omega) with h2' | ⟨i2, a1, a2, a3, e2⟩
    · exact hbad 2 3 le_rfl (by omega) (by omega) (by omega) (by omega) h2'
        (hcl 3 (by omega) (by omega))
    rcases hcl 3 (by omega) (by omega) with h3' | ⟨i3, b1, b2, b3, e3⟩
    · exact hbad 3 2 (by omega) (by omega) le_rfl (by omega) (by omega) h3'
        (Or.inr ⟨i2, a1, a2, a3, e2⟩)
    rcases hcl 4 (by omega) (by omega) with h4' | ⟨i4, c1, c2, c3, e4⟩
    · exact hbad 4 2 (by omega) (by omega) le_rfl (by omega) (by omega) h4'
        (Or.inr ⟨i2, a1, a2, a3, e2⟩)
    rcases (show i2 = i3 ∨ i2 = i4 ∨ i3 = i4 by omega) with h | h | h
    · have := copy_inj hΘ (i := 2) (i' := 3) (by omega) (by omega) (by omega) (by omega)
        (by rw [e2, e3, h])
      omega
    · have := copy_inj hΘ (i := 2) (i' := 4) (by omega) (by omega) (by omega) (by omega)
        (by rw [e2, e4, h])
      omega
    · have := copy_inj hΘ (i := 3) (i' := 4) (by omega) (by omega) (by omega) (by omega)
        (by rw [e3, e4, h])
      omega

/-- Claim 4.7, with explicit hypotheses. -/
lemma c47 (σ : Perm (Fin k)) (hσ : IsTwoBlockA σ 1) (hk : 4 ≤ k) (Θ : Fin k → ℝ × ℝ)
    (hc : CopyIn σ Θ (↑(canon σ) ∪ PM44 k)) :
    ∀ i : ℕ, 2 ≤ i → i ≤ k → th Θ i ∉ P44 k 1 ∧ th Θ i ∉ P44 k k := by
  intro i h1 h2
  have h46 := c46 σ hσ hk Θ hc
  obtain ⟨hx, hy⟩ := hNE45 hσ hc.1 h1 h2
  rw [h46, sig1 σ hσ] at hx hy
  simp only at hx hy
  constructor
  · intro h
    have := (mem_P44 h).2.1
    push_cast at this
    linarith
  · intro h
    have := (mem_P44 h).2.2.2.1
    push_cast at this
    linarith

/-- The sets `S_s` of the proof of Lemma 4.5 (tex l.760), for the chosen `j`. This is the
same set as `S45 σ j s` (which the frozen file defines only after `lemma_4_5`); see the
`example` right after `S45`. -/
def Cell45 (σ : Perm (Fin k)) (j s : ℕ) : Set (ℝ × ℝ) :=
  if s < j then P44 k s ∪ {sig σ s}
  else if s = j then P44 k s ∪ {sig σ j, sig σ (j + 1)}
  else P44 k s ∪ {sig σ (s + 1)}

/-- A point of `Θ_U` in `S_s` is on `P_s`, or `s ≠ j` and it is the single canonical point of
`S_s`. -/
lemma cell45_cases (σ : Perm (Fin k)) (hσ : IsTwoBlockA σ 1) (Θ : Fin k → ℝ × ℝ)
    (hΘ : Represents σ Θ) (j : ℕ) (hj : 2 ≤ j ∧ j ≤ k - 1)
    (hjU : ∃ i, 2 ≤ i ∧ i ≤ k ∧ th Θ i ∈ P44 k j) {s i : ℕ} (h1 : 2 ≤ i) (h2 : i ≤ k) (hs : th Θ i ∈ Cell45 σ j s) :
    th Θ i ∈ P44 k s ∨ (s ≠ j ∧ th Θ i = sig σ (if s < j then s else s + 1)) := by
  unfold Cell45 at hs
  split_ifs at hs with hsj hsj'
  · rcases hs with hs | hs
    · exact Or.inl hs
    · exact Or.inr ⟨by omega, by rw [ite_eq_left hsj]; exact hs⟩
  · subst hsj'
    rcases hs with hs | hs
    · exact Or.inl hs
    · exfalso
      obtain ⟨i1, a1, a2, a3⟩ := hjU
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
      rcases hs with hs | hs
      · have := sigNE45 σ hσ a3 (i0 := s) hj.1 (by omega) (Or.inl rfl)
        rw [← hs] at this
        exact hU45 hσ hΘ a1 a2 h1 h2 this
      · have := sigNE45 σ hσ a3 (i0 := s + 1) (by omega) (by omega) (Or.inr rfl)
        rw [← hs] at this
        exact hU45 hσ hΘ a1 a2 h1 h2 this
  · rcases hs with hs | hs
    · exact Or.inl hs
    · exact Or.inr ⟨hsj', by rw [ite_eq_right hsj]; exact hs⟩

/-- Claim 4.8, core: two points of `Θ_U` in the same `S_s` coincide. -/
lemma c48core (σ : Perm (Fin k)) (hσ : IsTwoBlockA σ 1) (Θ : Fin k → ℝ × ℝ)
    (hΘ : Represents σ Θ) (j : ℕ) (hj : 2 ≤ j ∧ j ≤ k - 1)
    (hjU : ∃ i, 2 ≤ i ∧ i ≤ k ∧ th Θ i ∈ P44 k j) {s : ℕ} (hs1 : 2 ≤ s) (hs2 : s ≤ k - 1)
    {i i' : ℕ} (h1 : 2 ≤ i) (h2 : i ≤ k) (h1' : 2 ≤ i') (h2' : i' ≤ k)
    (hi : th Θ i ∈ Cell45 σ j s) (hi' : th Θ i' ∈ Cell45 σ j s) : i = i' := by
  -- the ordered case
  have key : ∀ a b, 2 ≤ a → a ≤ k → 2 ≤ b → b ≤ k → a < b →
      th Θ a ∈ Cell45 σ j s → th Θ b ∈ Cell45 σ j s → False := by
    intro a b ha1 ha2 hb1 hb2 hab ha hb
    have hx := copy_x hΘ (by omega) hab hb2
    have hc0 : 2 ≤ (if s < j then s else s + 1) ∧ (if s < j then s else s + 1) ≤ k ∧
        ((if s < j then s else s + 1) = s ∨ (if s < j then s else s + 1) = s + 1) := by
      split_ifs <;> omega
    rcases cell45_cases σ hσ Θ hΘ j hj hjU ha1 ha2 ha with ha | ⟨-, ha⟩ <;>
      rcases cell45_cases σ hσ Θ hΘ j hj hjU hb1 hb2 hb with hb | ⟨-, hb⟩
    · exact hU45 hσ hΘ ha1 ha2 hb1 hb2 ⟨hx, (slope_P44 ha hb).1 hx⟩
    · have := sigNE45 σ hσ ha hc0.1 hc0.2.1 hc0.2.2
      rw [← hb] at this
      exact hU45 hσ hΘ ha1 ha2 hb1 hb2 this
    · have := sigNE45 σ hσ hb hc0.1 hc0.2.1 hc0.2.2
      rw [← ha] at this
      linarith [this.1]
    · rw [ha, hb] at hx
      exact lt_irrefl _ hx
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact key i i' h1 h2 h1' h2' h hi hi'
  · exact key i' i h1' h2' h1 h2 h hi' hi

/-- The contradiction of Lemma 4.5: a copy `Θ ≠ Σ` in `D = Σ ∪ P_M` does not exist. The final
count sends each point of `Θ_U` to a cell `S_s` containing it (injectively by Claim 4.8). -/
lemma false45 (σ : Perm (Fin k)) (hσ : IsTwoBlockA σ 1) (hk : 4 ≤ k) (Θ : Fin k → ℝ × ℝ)
    (hc : CopyIn σ Θ (↑(canon σ) ∪ PM44 k)) (hne : Finset.univ.image Θ ≠ canon σ) : False := by
  have hΘ := hc.1
  have h46 := c46 σ hσ hk Θ hc
  have h47 := c47 σ hσ hk Θ hc
  -- a point of `Θ_U` on some `P_j`, `2 ≤ j ≤ k - 1`
  obtain ⟨i0, a1, a2, a3⟩ := exists_not_canon hΘ hne
  have hi0 : 2 ≤ i0 := by
    by_contra h
    have : i0 = 1 := by omega
    subst this
    exact a3 ((mem_canon σ).2 ⟨1, le_rfl, a2, h46⟩)
  obtain ⟨j, hj1, hjk, hjP⟩ : ∃ m : ℕ, 1 ≤ m ∧ m ≤ k ∧ th Θ i0 ∈ P44 k m := by
    rcases mem_D45 σ (copy_mem hc a1 a2) with ⟨m, b1, b2, b3⟩ | h
    · exact absurd ((mem_canon σ).2 ⟨m, b1, b2, b3⟩) a3
    · exact h
  have hj : 2 ≤ j ∧ j ≤ k - 1 := by
    constructor
    · by_contra h
      have : j = 1 := by omega
      subst this
      exact (h47 i0 hi0 a2).1 (by exact_mod_cast hjP)
    · by_contra h
      have : j = k := by omega
      subst this
      exact (h47 i0 hi0 a2).2 hjP
  have hjU : ∃ i, 2 ≤ i ∧ i ≤ k ∧ th Θ i ∈ P44 k j := ⟨i0, hi0, a2, hjP⟩
  have hcard := Finset.card_le_card_of_forall_subsingleton
    (s := Finset.Icc 2 k) (t := Finset.Icc 2 (k - 1)) (fun i s => th Θ i ∈ Cell45 σ j s)
    (by
      intro i hi
      rw [Finset.mem_Icc] at hi
      rcases mem_D45 σ (copy_mem hc (by omega) hi.2) with ⟨m, b1, b2, b3⟩ | ⟨m, b1, b2, b3⟩
      · have hm2 : 2 ≤ m := by
          by_contra h
          have : m = 1 := by omega
          subst this
          have := copy_inj hΘ (i := i) (i' := 1) (by omega) hi.2 le_rfl (by omega)
            (by rw [b3, h46])
          omega
        rcases (show m < j ∨ m = j ∨ m = j + 1 ∨ j + 1 < m by omega) with h | h | h | h
        · refine ⟨m, Finset.mem_Icc.2 ⟨hm2, by omega⟩, ?_⟩
          simp only [Cell45, ite_eq_left h]
          exact Or.inr b3
        · refine ⟨m, Finset.mem_Icc.2 ⟨hm2, by omega⟩, ?_⟩
          simp only [Cell45, ite_eq_right (show ¬ m < j by omega), ite_eq_left h]
          right; left; rw [b3, h]
        · refine ⟨j, Finset.mem_Icc.2 ⟨hj.1, hj.2⟩, ?_⟩
          simp only [Cell45, lt_irrefl, ite_false, ite_true]
          right; right; rw [b3, h]; rfl
        · refine ⟨m - 1, Finset.mem_Icc.2 ⟨by omega, by omega⟩, ?_⟩
          simp only [Cell45, ite_eq_right (show ¬ m - 1 < j by omega),
            ite_eq_right (show ¬ m - 1 = j by omega)]
          right; rw [b3, show m - 1 + 1 = m by omega]; rfl
      · have hm2 : 2 ≤ m := by
          by_contra h
          have : m = 1 := by omega
          subst this
          exact (h47 i (by omega) hi.2).1 (by exact_mod_cast b3)
        have hmk : m ≤ k - 1 := by
          by_contra h
          have : m = k := by omega
          subst this
          exact (h47 i (by omega) hi.2).2 b3
        refine ⟨m, Finset.mem_Icc.2 ⟨hm2, hmk⟩, ?_⟩
        unfold Cell45
        split_ifs <;> exact Or.inl b3)
    (by
      intro s hs a ha b hb
      rw [Finset.mem_Icc] at hs
      simp only [Set.mem_ofPred_eq, Finset.mem_Icc] at ha hb
      exact c48core σ hσ Θ hΘ j hj hjU hs.1 hs.2 ha.1.1 ha.1.2 hb.1.1 hb.1.2 ha.2 hb.2)
  simp only [Nat.card_Icc] at hcard
  omega

end TB

/-- **Lemma 4.5.** Let `σ = (1 k (k-1) ⋯ 3 2)` with `k ≥ 4`. If `Π` is associated with a
permutation and `Σ ⊆ Π ⊆ Σ ∪ P_M` (Construction 4.4), then `Σ` is the unique `σ`-copy in `Π`. The
proof does not use `hP : IsPermPointSet P`; the paper states it (tex l.724), and it is kept to match
the paper. -/
theorem lemma_4_5 (σ : Perm (Fin k)) (hσ : IsTwoBlockA σ 1) (hk : 4 ≤ k)
    (P : Finset (ℝ × ℝ)) (hP : IsPermPointSet P)
    (h₁ : (↑(canon σ) : Set (ℝ × ℝ)) ⊆ ↑P) (h₂ : (↑P : Set (ℝ × ℝ)) ⊆ ↑(canon σ) ∪ PM44 k) :
    IsUniqueCopy σ ↑P := by
  refine ⟨h₁, fun Θ hΘ => ?_⟩
  by_contra hne
  exact TB.false45 σ hσ hk Θ ⟨hΘ.1, fun i => h₂ (hΘ.2 i)⟩ hne

/-- The context of the proof of Lemma 4.5 (tex l.730): `σ = (1 k ⋯ 2)`, `k ≥ 4`, and
`Θ ⊆ D = Σ ∪ P_M` a `σ`-copy distinct from `Σ`. A proof by contradiction refuting this
context is `lemma_4_5`. -/
structure Ctx45 (σ : Perm (Fin k)) (Θ : Fin k → ℝ × ℝ) : Prop where
  pattern : IsTwoBlockA σ 1
  hk : 4 ≤ k
  copy : CopyIn σ Θ (↑(canon σ) ∪ PM44 k)
  ne : Finset.univ.image Θ ≠ canon σ

/-- **Claim 4.6.** `Θ(1) = Σ(1)`.

A step of the proof by contradiction of Lemma 4.5 (tex l.730): its context `Ctx45` cannot be
satisfied, because `lemma_4_5` proves `Σ` is the only copy, so the claim holds only vacuously, as in
the paper. Its proof does not use `ne` (`Θ ≠ Σ`). -/
theorem claim_4_6 (σ : Perm (Fin k)) (Θ : Fin k → ℝ × ℝ) (hc : Ctx45 σ Θ) :
    th Θ 1 = sig σ 1 := by
  exact TB.c46 σ hc.pattern hc.hk Θ hc.copy

/-- **Claim 4.7.** With `Θ_U = {Θ(i) : 2 ≤ i ≤ k}`: `Θ_U ∩ P_1 = Θ_U ∩ P_k = ∅`.

A step of the proof by contradiction of Lemma 4.5 (tex l.730): its context `Ctx45` cannot be
satisfied, because `lemma_4_5` proves `Σ` is the only copy, so the claim holds only vacuously, as in
the paper. Its proof does not use `ne` (`Θ ≠ Σ`). -/
theorem claim_4_7 (σ : Perm (Fin k)) (Θ : Fin k → ℝ × ℝ) (hc : Ctx45 σ Θ) :
    ∀ i : ℕ, 2 ≤ i → i ≤ k → th Θ i ∉ P44 k 1 ∧ th Θ i ∉ P44 k k := by
  exact TB.c47 σ hc.pattern hc.hk Θ hc.copy

/-- The sets `S_s` of the proof of Lemma 4.5 (tex l.760), for the chosen `j`:
`S_s = P_s ∪ {Σ(s)}` for `s < j`, `S_j = P_j ∪ {Σ(j), Σ(j+1)}`, `S_s = P_s ∪ {Σ(s+1)}` for
`s > j`. -/
def S45 (σ : Perm (Fin k)) (j s : ℕ) : Set (ℝ × ℝ) :=
  if s < j then P44 k s ∪ {sig σ s}
  else if s = j then P44 k s ∪ {sig σ j, sig σ (j + 1)}
  else P44 k s ∪ {sig σ (s + 1)}

/- `TB.Cell45` is `S45` (by `rfl`): the bridge between the proof-local `TB.Cell45` and the
paper's `S45`, recorded as a checked example. -/
example (σ : Perm (Fin k)) (j s : ℕ) : TB.Cell45 σ j s = S45 σ j s := rfl

open Classical in
/-- **Claim 4.8.** For `j ∈ {2, …, k-1}` with `Θ_U ∩ P_j ≠ ∅`, and every `2 ≤ s ≤ k-1`:
`|Θ_U ∩ S_s| ≤ 1`.

A step of the proof by contradiction of Lemma 4.5 (tex l.730): its context `Ctx45` cannot be
satisfied, because `lemma_4_5` proves `Σ` is the only copy, so the claim holds only vacuously, as in
the paper. Its proof does not use `ne` (`Θ ≠ Σ`), `hk : 4 ≤ k`, or the support condition `Θ ⊆ D`
(only that `Θ` is a `σ`-copy, `hc.copy.1`). -/
theorem claim_4_8 (σ : Perm (Fin k)) (Θ : Fin k → ℝ × ℝ) (hc : Ctx45 σ Θ) (j : ℕ)
    (hj : 2 ≤ j ∧ j ≤ k - 1) (hjU : ∃ i, 2 ≤ i ∧ i ≤ k ∧ th Θ i ∈ P44 k j) :
    ∀ s : ℕ, 2 ≤ s → s ≤ k - 1 →
      ((Finset.Icc 2 k).filter fun i => th Θ i ∈ S45 σ j s).card ≤ 1 := by
  intro s hs1 hs2
  rw [Finset.card_le_one]
  intro a ha b hb
  simp only [Finset.mem_filter, Finset.mem_Icc] at ha hb
  exact TB.c48core σ hc.pattern Θ hc.copy.1 j hj hjU hs1 hs2 ha.1.1 ha.1.2 hb.1.1 hb.1.2
    ha.2 hb.2

/-! ## The interior case `2 ≤ ℓ, r ≤ k - 1` -/

/-- **Construction 4.9.** `P_0 = (ℓ, ℓ) + t(1,1)`, `0 < t < 1`, and `P_i = P_0 + (-i, i)` for every
integer `i`; so `P_i` has `x ∈ (ℓ-i, ℓ-i+1)`, `y ∈ (ℓ+i, ℓ+i+1)`. -/
def P49 (ℓ : ℕ) (i : ℤ) : Set (ℝ × ℝ) :=
  openSeg ((ℓ : ℝ) - (i : ℝ), (ℓ : ℝ) + (i : ℝ)) (1, 1)

/-- **Construction 4.9.** `P_M = ⋃_{i = -k+ℓ+1}^{k-ℓ-1} P_i`. -/
def PM49 (k ℓ : ℕ) : Set (ℝ × ℝ) :=
  ⋃ i ∈ Set.Icc (-(k : ℤ) + ℓ + 1) ((k : ℤ) - ℓ - 1), P49 ℓ i

namespace TB

/-! ### Auxiliary development for Lemma 4.10 -/

lemma copy_y_le {σ : Perm (Fin k)} {ℓ : ℕ} (hσ : IsTwoBlockA σ ℓ) {Θ : Fin k → ℝ × ℝ}
    (hΘ : Represents σ Θ) {i i' : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ k) (h1' : 1 ≤ i') (h2' : i' ≤ k)
    (h : (if i ≤ ℓ then ℓ + 1 - i else k + ℓ + 1 - i) ≤
        (if i' ≤ ℓ then ℓ + 1 - i' else k + ℓ + 1 - i')) :
    (th Θ i).2 ≤ (th Θ i').2 := by
  refine le_of_not_gt fun h' => ?_
  rw [yA hσ hΘ h1' h2' h1 h2] at h'
  omega

/-- Integrality and range of the coordinates of a canonical point. -/
lemma canon_coords (σ : Perm (Fin k)) {p : ℝ × ℝ} (hp : p ∈ canon σ) :
    (∃ z : ℤ, p.1 = z) ∧ (∃ z : ℤ, p.2 = z) ∧ (1 : ℝ) ≤ p.1 ∧ p.1 ≤ k ∧ (1 : ℝ) ≤ p.2 ∧
      p.2 ≤ k := by
  obtain ⟨i, h1, h2, rfl⟩ := (mem_canon σ).1 hp
  rw [sig_eq σ h1 h2]
  have e1 : 1 ≤ sval σ i := by rw [sval_eq σ h1 h2]; omega
  have e2 : sval σ i ≤ k := by
    rw [sval_eq σ h1 h2]; have := (σ ⟨i - 1, by omega⟩).isLt; omega
  refine ⟨⟨i, by simp⟩, ⟨sval σ i, by simp⟩, ?_, ?_, ?_, ?_⟩ <;> simp only <;> exact_mod_cast
    (by omega)

lemma mem_P49 {ℓ : ℕ} {i : ℤ} {p : ℝ × ℝ} (hp : p ∈ P49 ℓ i) :
    (ℓ : ℝ) - i < p.1 ∧ p.1 < (ℓ : ℝ) - i + 1 ∧ (ℓ : ℝ) + i < p.2 ∧ p.2 < (ℓ : ℝ) + i + 1 ∧
      p.2 = p.1 + 2 * i := by
  simp only [P49, openSeg, Set.mem_ofPred_eq] at hp
  obtain ⟨t, ht0, ht1, rfl⟩ := hp
  refine ⟨by linarith, by linarith, by linarith, by linarith, by ring⟩

/-- `P_i` has positive slope (Construction 4.9). -/
lemma slope_P49 {ℓ : ℕ} {i : ℤ} {p q : ℝ × ℝ} (hp : p ∈ P49 ℓ i) (hq : q ∈ P49 ℓ i) :
    p.1 < q.1 ↔ p.2 < q.2 := by
  have := (mem_P49 hp).2.2.2.2; have := (mem_P49 hq).2.2.2.2
  constructor <;> intro <;> linarith

lemma mem_PM49 {ℓ : ℕ} {p : ℝ × ℝ} (hp : p ∈ PM49 k ℓ) : ∃ j : ℤ, p ∈ P49 ℓ j := by
  simp only [PM49, Set.mem_iUnion, exists_prop] at hp
  obtain ⟨j, -, hj⟩ := hp
  exact ⟨j, hj⟩

/-- A point of `D = Σ ∪ P_M` whose `x`-coordinate lies in `(ℓ - j, ℓ - j + 1)` lies on `P_j`. -/
lemma stripx49 (σ : Perm (Fin k)) {ℓ : ℕ} {p : ℝ × ℝ}
    (hp : p ∈ (↑(canon σ) : Set (ℝ × ℝ)) ∪ PM49 k ℓ) {j : ℤ} (h1 : (ℓ : ℝ) - j < p.1)
    (h2 : p.1 < (ℓ : ℝ) - j + 1) : p ∈ P49 ℓ j := by
  rcases hp with hp | hp
  · exfalso
    obtain ⟨⟨z, hz⟩, -⟩ := canon_coords σ hp
    rw [hz] at h1 h2
    have e1 : (ℓ : ℤ) - j < z := by exact_mod_cast h1
    have e2 : z < (ℓ : ℤ) - j + 1 := by exact_mod_cast h2
    omega
  · obtain ⟨j', hj'⟩ := mem_PM49 hp
    obtain ⟨b1, b2, -, -, -⟩ := mem_P49 hj'
    have e1 : (ℓ : ℤ) - j < ℓ - j' + 1 := by
      exact_mod_cast (show (ℓ : ℝ) - j < ℓ - j' + 1 by linarith)
    have e2 : (ℓ : ℤ) - j' < ℓ - j + 1 := by
      exact_mod_cast (show (ℓ : ℝ) - j' < ℓ - j + 1 by linarith)
    have : j' = j := by omega
    rwa [this] at hj'

/-- A point of `D = Σ ∪ P_M` whose `y`-coordinate lies in `(ℓ + j, ℓ + j + 1)` lies on `P_j`. -/
lemma stripy49 (σ : Perm (Fin k)) {ℓ : ℕ} {p : ℝ × ℝ}
    (hp : p ∈ (↑(canon σ) : Set (ℝ × ℝ)) ∪ PM49 k ℓ) {j : ℤ} (h1 : (ℓ : ℝ) + j < p.2)
    (h2 : p.2 < (ℓ : ℝ) + j + 1) : p ∈ P49 ℓ j := by
  rcases hp with hp | hp
  · exfalso
    obtain ⟨-, ⟨z, hz⟩, -⟩ := canon_coords σ hp
    rw [hz] at h1 h2
    have e1 : (ℓ : ℤ) + j < z := by exact_mod_cast h1
    have e2 : z < (ℓ : ℤ) + j + 1 := by exact_mod_cast h2
    omega
  · obtain ⟨j', hj'⟩ := mem_PM49 hp
    obtain ⟨-, -, b3, b4, -⟩ := mem_P49 hj'
    have e1 : (ℓ : ℤ) + j < ℓ + j' + 1 := by
      exact_mod_cast (show (ℓ : ℝ) + j < ℓ + j' + 1 by linarith)
    have e2 : (ℓ : ℤ) + j' < ℓ + j + 1 := by
      exact_mod_cast (show (ℓ : ℝ) + j' < ℓ + j + 1 by linarith)
    have : j' = j := by omega
    rwa [this] at hj'

/-- Distinct segments `P_j`, `P_{j'}` are coordinate-incomparable. -/
lemma incomp49 {ℓ : ℕ} {j j' : ℤ} {p q : ℝ × ℝ} (hp : p ∈ P49 ℓ j) (hq : q ∈ P49 ℓ j')
    (hx : p.1 < q.1) (hy : p.2 < q.2) : j = j' := by
  obtain ⟨a1, -, a3, -, -⟩ := mem_P49 hp
  obtain ⟨-, b2, -, b4, -⟩ := mem_P49 hq
  have e1 : (ℓ : ℤ) - j < ℓ - j' + 1 := by
    exact_mod_cast (show (ℓ : ℝ) - j < ℓ - j' + 1 by linarith)
  have e2 : (ℓ : ℤ) + j < ℓ + j' + 1 := by
    exact_mod_cast (show (ℓ : ℝ) + j < ℓ + j' + 1 by linarith)
  omega

/-- Claim 4.11 with explicit hypotheses (case `a ≤ ℓ`, northeast). -/
lemma c411 (σ : Perm (Fin k)) (ℓ : ℕ) (hσ : IsTwoBlockA σ ℓ)
    (hr : ℓ + 1 ≤ k - 1) (Θ : Fin k → ℝ × ℝ) (hc : CopyIn σ Θ (↑(canon σ) ∪ PM49 k ℓ))
    (a : ℕ) (ha : 1 ≤ a ∧ a ≤ ℓ) (j : ℤ) (haj : th Θ a ∈ P49 ℓ j) :
    ∀ i : ℕ, ℓ + 1 ≤ i → i ≤ k → th Θ i ∉ PM49 k ℓ := by
  intro h hh1 hh2 hP
  have hΘ := hc.1
  obtain ⟨j', hj'⟩ := mem_PM49 hP
  have hx : (th Θ a).1 < (th Θ h).1 := copy_x hΘ ha.1 (by omega) hh2
  have hy : (th Θ a).2 < (th Θ h).2 :=
    (yA hσ hΘ ha.1 (by omega) (by omega) hh2).2 (by split_ifs <;> omega)
  have := incomp49 haj hj' hx hy
  subst this
  obtain ⟨a1, a2, a3, a4, -⟩ := mem_P49 haj
  obtain ⟨b1, b2, b3, b4, -⟩ := mem_P49 hj'
  have hr' : th Θ (ℓ + 1) ∈ P49 ℓ j := by
    have e1 : (th Θ a).1 < (th Θ (ℓ + 1)).1 := copy_x hΘ ha.1 (by omega) (by omega)
    have e2 : (th Θ (ℓ + 1)).1 ≤ (th Θ h).1 := copy_x_le hΘ (by omega) hh1 hh2
    exact stripx49 σ (copy_mem hc (by omega) (by omega)) (by linarith) (by linarith)
  have hk' : th Θ k ∈ P49 ℓ j := by
    have e1 : (th Θ a).2 < (th Θ k).2 :=
      (yA hσ hΘ ha.1 (by omega) (by omega) le_rfl).2 (by split_ifs <;> omega)
    have e2 : (th Θ k).2 ≤ (th Θ h).2 :=
      copy_y_le hσ hΘ (by omega) le_rfl (by omega) hh2 (by split_ifs <;> omega)
    exact stripy49 σ (copy_mem hc (by omega) le_rfl) (by linarith) (by linarith)
  have := (slope_P49 hr' hk').1 (copy_x hΘ (i := ℓ + 1) (i' := k) (by omega) (by omega) le_rfl)
  rw [yA hσ hΘ (by omega) (by omega) (by omega) le_rfl] at this
  split_ifs at this <;> omega

/-- Claim 4.11, southwest version (case `a ≥ r`): the lower block avoids `P_M`. -/
lemma c411sw (σ : Perm (Fin k)) (ℓ : ℕ) (hσ : IsTwoBlockA σ ℓ) (hℓ : 2 ≤ ℓ)
    (Θ : Fin k → ℝ × ℝ) (hc : CopyIn σ Θ (↑(canon σ) ∪ PM49 k ℓ))
    (a : ℕ) (ha : ℓ + 1 ≤ a ∧ a ≤ k) (j : ℤ) (haj : th Θ a ∈ P49 ℓ j) :
    ∀ i : ℕ, 1 ≤ i → i ≤ ℓ → th Θ i ∉ PM49 k ℓ := by
  intro h hh1 hh2 hP
  have hΘ := hc.1
  obtain ⟨j', hj'⟩ := mem_PM49 hP
  have hx : (th Θ h).1 < (th Θ a).1 := copy_x hΘ hh1 (by omega) ha.2
  have hy : (th Θ h).2 < (th Θ a).2 :=
    (yA hσ hΘ hh1 (by omega) (by omega) ha.2).2 (by split_ifs <;> omega)
  have := incomp49 hj' haj hx hy
  subst this
  obtain ⟨a1, a2, a3, a4, -⟩ := mem_P49 haj
  obtain ⟨b1, b2, b3, b4, -⟩ := mem_P49 hj'
  have hl : th Θ ℓ ∈ P49 ℓ j' := by
    have e1 : (th Θ h).1 ≤ (th Θ ℓ).1 := copy_x_le hΘ hh1 hh2 (by omega)
    have e2 : (th Θ ℓ).1 < (th Θ a).1 := copy_x hΘ (by omega) (by omega) ha.2
    exact stripx49 σ (copy_mem hc (by omega) (by omega)) (by linarith) (by linarith)
  have h1 : th Θ 1 ∈ P49 ℓ j' := by
    have e1 : (th Θ h).2 ≤ (th Θ 1).2 :=
      copy_y_le hσ hΘ hh1 (by omega) le_rfl (by omega) (by split_ifs <;> omega)
    have e2 : (th Θ 1).2 < (th Θ a).2 :=
      (yA hσ hΘ le_rfl (by omega) (by omega) ha.2).2 (by split_ifs <;> omega)
    exact stripy49 σ (copy_mem hc le_rfl (by omega)) (by linarith) (by linarith)
  have := (slope_P49 h1 hl).1 (copy_x hΘ (i := 1) (i' := ℓ) le_rfl (by omega) (by omega))
  rw [yA hσ hΘ le_rfl (by omega) (by omega) (by omega)] at this
  split_ifs at this <;> omega

/-- Identification step of Lemma 4.10 (tex l.842): if `Θ(p), …, Θ(q)` are canonical, with
`Θ(p)_x ≥ p` and `Θ(q)_x ≤ q`, then `Θ(i) = Σ(i)` for `p ≤ i ≤ q` (their `x`-coordinates are
`q - p + 1` strictly increasing integers in `[p, q]`). -/
lemma ident {σ : Perm (Fin k)} {Θ : Fin k → ℝ × ℝ} (hΘ : Represents σ Θ) {p q : ℕ}
    (hcan : ∀ i, p ≤ i → i ≤ q → th Θ i ∈ canon σ) (hp1 : 1 ≤ p) (hqk : q ≤ k)
    (hp : (p : ℝ) ≤ (th Θ p).1) (hq : (th Θ q).1 ≤ q) :
    ∀ i, p ≤ i → i ≤ q → th Θ i = sig σ i := by
  intro i hi1 hi2
  have hup := chain_up (fun m => (th Θ (p + m)).1) q (q - p)
    (fun m hm => (canon_coords σ (hcan _ (by omega) (by omega))).1)
    (fun m hm => copy_x hΘ (by omega) (by omega) (by omega))
    (by simp only [show p + (q - p) = q by omega]; exact_mod_cast hq)
    (q - i) (by omega)
  have hlo := chain_up (fun m => -(th Θ (q - m)).1) (-(p : ℤ)) (q - p)
    (fun m hm => by
      obtain ⟨z, hz⟩ := (canon_coords σ (hcan (q - m) (by omega) (by omega))).1
      exact ⟨-z, by simp [hz]⟩)
    (fun m hm => by
      have := copy_x hΘ (i := q - (m + 1)) (i' := q - m) (by omega) (by omega) (by omega)
      linarith)
    (by simp only [show q - (q - p) = p by omega]; push_cast; linarith)
    (i - p) (by omega)
  beta_reduce at hup hlo
  rw [show p + (q - p - (q - i)) = i by omega, Nat.cast_sub hi2] at hup
  rw [show q - (q - p - (i - p)) = i by omega, Nat.cast_sub hi1] at hlo
  push_cast at hup hlo
  obtain ⟨m, hm1, hm2, hm⟩ := (mem_canon σ).1 (hcan i hi1 hi2)
  have hx : (th Θ i).1 = i := by linarith
  rw [hm, sig_eq σ hm1 hm2] at hx
  simp only at hx
  have : m = i := by exact_mod_cast hx
  rw [hm, this]

/-- The contradiction of Lemma 4.10: a copy `Θ ≠ Σ` in `D = Σ ∪ P_M` does not exist (both cases
`a ≤ ℓ` and `a ≥ r`). The hypothesis `ℓ ≤ k/2` is not needed. -/
lemma false410 (σ : Perm (Fin k)) (ℓ : ℕ) (hσ : IsTwoBlockA σ ℓ) (hℓ : 2 ≤ ℓ)
    (hr : ℓ + 1 ≤ k - 1) (Θ : Fin k → ℝ × ℝ) (hc : CopyIn σ Θ (↑(canon σ) ∪ PM49 k ℓ))
    (hne : Finset.univ.image Θ ≠ canon σ) : False := by
  have hΘ := hc.1
  obtain ⟨a, a1, a2, a3⟩ := exists_not_canon hΘ hne
  obtain ⟨j, hj⟩ : ∃ j : ℤ, th Θ a ∈ P49 ℓ j := by
    rcases copy_mem hc a1 a2 with h | h
    · exact absurd h a3
    · exact mem_PM49 h
  obtain ⟨c1, c2, c3, c4, -⟩ := mem_P49 hj
  have hcan : ∀ i, 1 ≤ i → i ≤ k → th Θ i ∉ PM49 k ℓ → th Θ i ∈ canon σ := by
    intro i h1 h2 h
    rcases copy_mem hc h1 h2 with h' | h'
    · exact h'
    · exact absurd h' h
  rcases le_or_gt a ℓ with ha | ha
  · -- `a ≤ ℓ`: the upper block is canonical (Claim 4.11)
    have hU := c411 σ ℓ hσ hr Θ hc a ⟨a1, ha⟩ j hj
    have hUc : ∀ i, ℓ + 1 ≤ i → i ≤ k → th Θ i ∈ canon σ :=
      fun i h1 h2 => hcan i (by omega) h2 (hU i h1 h2)
    -- `Θ(r)_x ≤ r`
    have hxr : (th Θ (ℓ + 1)).1 ≤ ℓ + 1 := by
      have := chain_up (fun i => (th Θ (ℓ + 1 + i)).1) k (k - (ℓ + 1))
        (fun i hi => (canon_coords σ (hUc _ (by omega) (by omega))).1)
        (fun i hi => copy_x hΘ (by omega) (by omega) (by omega))
        (by
          simp only [show ℓ + 1 + (k - (ℓ + 1)) = k by omega]
          exact (canon_coords σ (hUc k (by omega) le_rfl)).2.2.2.1)
        (k - (ℓ + 1)) le_rfl
      simp only [Nat.sub_self, add_zero] at this
      rw [Nat.cast_sub (by omega)] at this
      push_cast at this
      linarith
    -- `Θ(k)_y ≤ r`
    have hyk : (th Θ k).2 ≤ ℓ + 1 := by
      have := chain_up (fun i => (th Θ (k - i)).2) k (k - (ℓ + 1))
        (fun i hi => (canon_coords σ (hUc _ (by omega) (by omega))).2.1)
        (fun i hi => (yA hσ hΘ (by omega) (by omega) (by omega) (by omega)).2
          (by split_ifs <;> omega))
        (by
          simp only [show k - (k - (ℓ + 1)) = ℓ + 1 by omega]
          exact (canon_coords σ (hUc (ℓ + 1) le_rfl (by omega))).2.2.2.2.2)
        (k - (ℓ + 1)) le_rfl
      simp only [Nat.sub_self, Nat.sub_zero] at this
      rw [Nat.cast_sub (by omega)] at this
      push_cast at this
      linarith
    have hxa : (th Θ a).1 < (th Θ (ℓ + 1)).1 := copy_x hΘ a1 (by omega) (by omega)
    have hya : (th Θ a).2 < (th Θ k).2 :=
      (yA hσ hΘ a1 a2 (by omega) le_rfl).2 (by split_ifs <;> omega)
    have hj0 : j = 0 := by
      have e1 : (ℓ : ℤ) - j < ℓ + 1 := by
        exact_mod_cast (show (ℓ : ℝ) - j < ℓ + 1 by linarith)
      have e2 : (ℓ : ℤ) + j < ℓ + 1 := by
        exact_mod_cast (show (ℓ : ℝ) + j < ℓ + 1 by linarith)
      omega
    subst hj0
    push_cast at c1 c3
    -- `Θ(i) = Σ(i)` for `r ≤ i ≤ k` (tex l.842)
    have hid : ∀ i, ℓ + 1 ≤ i → i ≤ k → th Θ i = sig σ i := by
      refine ident hΘ hUc (by omega) le_rfl ?_
        (canon_coords σ (hUc k (by omega) le_rfl)).2.2.2.1
      obtain ⟨z, hz⟩ := (canon_coords σ (hUc (ℓ + 1) le_rfl (by omega))).1
      have e1 : (ℓ : ℝ) < z := by rw [← hz]; linarith
      have e2 : (ℓ : ℤ) < z := by exact_mod_cast e1
      rw [hz]; push_cast; exact_mod_cast (show (ℓ : ℤ) + 1 ≤ z by omega)
    have hxr' : (th Θ (ℓ + 1)).1 = ℓ + 1 := by
      rw [hid _ le_rfl (by omega), sig_eq σ (by omega) (by omega)]; push_cast; ring
    have hyk' : (th Θ k).2 = ℓ + 1 := by
      rw [hid k (by omega) le_rfl, sig_eq σ (by omega) le_rfl, vA hσ (by omega) le_rfl,
        ite_eq_right (by omega), Nat.cast_sub (by omega)]
      push_cast; ring
    clear hxr hyk
    have hl : th Θ ℓ ∈ P49 ℓ 0 := by
      have e1 : (th Θ a).1 ≤ (th Θ ℓ).1 := copy_x_le hΘ a1 ha (by omega)
      have e2 : (th Θ ℓ).1 < (th Θ (ℓ + 1)).1 := copy_x hΘ (by omega) (by omega) (by omega)
      exact stripx49 σ (copy_mem hc (by omega) (by omega)) (by push_cast; linarith)
        (by push_cast; linarith)
    have h1 : th Θ 1 ∈ P49 ℓ 0 := by
      have e1 : (th Θ a).2 ≤ (th Θ 1).2 :=
        copy_y_le hσ hΘ a1 a2 le_rfl (by omega) (by split_ifs <;> omega)
      have e2 : (th Θ 1).2 < (th Θ k).2 :=
        (yA hσ hΘ le_rfl (by omega) (by omega) le_rfl).2 (by split_ifs <;> omega)
      exact stripy49 σ (copy_mem hc le_rfl (by omega)) (by push_cast; linarith)
        (by push_cast; linarith)
    have := (slope_P49 h1 hl).1 (copy_x hΘ (i := 1) (i' := ℓ) le_rfl (by omega) (by omega))
    rw [yA hσ hΘ le_rfl (by omega) (by omega) (by omega)] at this
    split_ifs at this <;> omega
  · -- `a ≥ r`: the same argument with southwest in place of northeast
    have hL := c411sw σ ℓ hσ hℓ Θ hc a ⟨ha, a2⟩ j hj
    have hLc : ∀ i, 1 ≤ i → i ≤ ℓ → th Θ i ∈ canon σ :=
      fun i h1 h2 => hcan i h1 (by omega) (hL i h1 h2)
    -- `Θ(ℓ)_x ≥ ℓ`
    have hxl : (ℓ : ℝ) ≤ (th Θ ℓ).1 := by
      have := chain_up (fun i => -(th Θ (ℓ - i)).1) (-1) (ℓ - 1)
        (fun i hi => by
          obtain ⟨z, hz⟩ := (canon_coords σ (hLc (ℓ - i) (by omega) (by omega))).1
          exact ⟨-z, by simp [hz]⟩)
        (fun i hi => by
          have := copy_x hΘ (i := ℓ - (i + 1)) (i' := ℓ - i) (by omega) (by omega) (by omega)
          linarith)
        (by
          simp only [show ℓ - (ℓ - 1) = 1 by omega]
          have := (canon_coords σ (hLc 1 le_rfl (by omega))).2.2.1
          push_cast; linarith)
        (ℓ - 1) le_rfl
      simp only [Nat.sub_self, Nat.sub_zero] at this
      rw [Nat.cast_sub (by omega)] at this
      push_cast at this
      linarith
    -- `Θ(1)_y ≥ ℓ`
    have hy1 : (ℓ : ℝ) ≤ (th Θ 1).2 := by
      have := chain_up (fun i => -(th Θ (1 + i)).2) (-1) (ℓ - 1)
        (fun i hi => by
          obtain ⟨z, hz⟩ := (canon_coords σ (hLc (1 + i) (by omega) (by omega))).2.1
          exact ⟨-z, by simp [hz]⟩)
        (fun i hi => by
          have := (yA hσ hΘ (i := 1 + (i + 1)) (i' := 1 + i) (by omega) (by omega) (by omega)
            (by omega)).2 (by split_ifs <;> omega)
          linarith)
        (by
          simp only [show 1 + (ℓ - 1) = ℓ by omega]
          have := (canon_coords σ (hLc ℓ (by omega) le_rfl)).2.2.2.2.1
          push_cast; linarith)
        (ℓ - 1) le_rfl
      simp only [Nat.sub_self, add_zero] at this
      rw [Nat.cast_sub (by omega)] at this
      push_cast at this
      linarith
    have hxa : (th Θ ℓ).1 < (th Θ a).1 := copy_x hΘ (by omega) ha a2
    have hya : (th Θ 1).2 < (th Θ a).2 :=
      (yA hσ hΘ le_rfl (by omega) a1 a2).2 (by split_ifs <;> omega)
    have hj0 : j = 0 := by
      have e1 : (ℓ : ℤ) < ℓ - j + 1 := by
        exact_mod_cast (show (ℓ : ℝ) < ℓ - j + 1 by linarith)
      have e2 : (ℓ : ℤ) < ℓ + j + 1 := by
        exact_mod_cast (show (ℓ : ℝ) < ℓ + j + 1 by linarith)
      omega
    subst hj0
    push_cast at c2 c4
    -- `Θ(i) = Σ(i)` for `1 ≤ i ≤ ℓ` (southwest mirror of tex l.842)
    have hid : ∀ i, 1 ≤ i → i ≤ ℓ → th Θ i = sig σ i := by
      refine ident hΘ hLc le_rfl (by omega)
        (by exact_mod_cast (canon_coords σ (hLc 1 le_rfl (by omega))).2.2.1) ?_
      obtain ⟨z, hz⟩ := (canon_coords σ (hLc ℓ (by omega) le_rfl)).1
      have e1 : (z : ℝ) < ℓ + 1 := by rw [← hz]; linarith
      have e2 : z < (ℓ : ℤ) + 1 := by exact_mod_cast e1
      rw [hz]; exact_mod_cast (show z ≤ (ℓ : ℤ) by omega)
    have hxl' : (th Θ ℓ).1 = ℓ := by
      rw [hid ℓ (by omega) le_rfl, sig_eq σ (by omega) (by omega)]
    have hy1' : (th Θ 1).2 = ℓ := by
      rw [hid 1 le_rfl (by omega), sig_eq σ le_rfl (by omega), vA hσ le_rfl (by omega),
        ite_eq_left (by omega)]
      simp
    clear hxl hy1
    have hr' : th Θ (ℓ + 1) ∈ P49 ℓ 0 := by
      have e1 : (th Θ ℓ).1 < (th Θ (ℓ + 1)).1 := copy_x hΘ (by omega) (by omega) (by omega)
      have e2 : (th Θ (ℓ + 1)).1 ≤ (th Θ a).1 := copy_x_le hΘ (by omega) ha a2
      exact stripx49 σ (copy_mem hc (by omega) (by omega)) (by push_cast; linarith)
        (by push_cast; linarith)
    have hk' : th Θ k ∈ P49 ℓ 0 := by
      have e1 : (th Θ 1).2 < (th Θ k).2 :=
        (yA hσ hΘ le_rfl (by omega) (by omega) le_rfl).2 (by split_ifs <;> omega)
      have e2 : (th Θ k).2 ≤ (th Θ a).2 :=
        copy_y_le hσ hΘ (by omega) le_rfl a1 a2 (by split_ifs <;> omega)
      exact stripy49 σ (copy_mem hc (by omega) le_rfl) (by push_cast; linarith)
        (by push_cast; linarith)
    have := (slope_P49 hr' hk').1
      (copy_x hΘ (i := ℓ + 1) (i' := k) (by omega) (by omega) le_rfl)
    rw [yA hσ hΘ (by omega) (by omega) (by omega) le_rfl] at this
    split_ifs at this <;> omega

end TB

/-- **Lemma 4.10.** Let `σ = (ℓ(ℓ-1)⋯1)(k(k-1)⋯r)`, `r = ℓ+1`, with `2 ≤ ℓ`, `r ≤ k-1` and
(after the reverse-complement symmetry) `ℓ ≤ k/2`. If `Π` is associated with a permutation and
`Σ ⊆ Π ⊆ Σ ∪ P_M` (Construction 4.9), then `Σ` is the unique `σ`-copy in `Π`. The proof does not use
`hP : IsPermPointSet P` (tex l.815) or the normalization `hhalf : 2ℓ ≤ k` (tex l.779); the paper
states both, and they are kept to match the paper. -/
theorem lemma_4_10 (σ : Perm (Fin k)) (ℓ : ℕ) (hσ : IsTwoBlockA σ ℓ) (hℓ : 2 ≤ ℓ)
    (hr : ℓ + 1 ≤ k - 1) (hhalf : 2 * ℓ ≤ k)
    (P : Finset (ℝ × ℝ)) (hP : IsPermPointSet P)
    (h₁ : (↑(canon σ) : Set (ℝ × ℝ)) ⊆ ↑P) (h₂ : (↑P : Set (ℝ × ℝ)) ⊆ ↑(canon σ) ∪ PM49 k ℓ) :
    IsUniqueCopy σ ↑P := by
  refine ⟨h₁, fun Θ hΘ => ?_⟩
  by_contra hne
  exact TB.false410 σ ℓ hσ hℓ hr Θ ⟨hΘ.1, fun i => h₂ (hΘ.2 i)⟩ hne

/-- The context of the proof of Lemma 4.10 (tex l.821): the hypotheses of Lemma 4.10 and
`Θ ⊆ D = Σ ∪ P_M` a `σ`-copy distinct from `Σ`. A proof by contradiction refuting this context
is `lemma_4_10`. -/
structure Ctx410 (σ : Perm (Fin k)) (ℓ : ℕ) (Θ : Fin k → ℝ × ℝ) : Prop where
  pattern : IsTwoBlockA σ ℓ
  hℓ : 2 ≤ ℓ
  hr : ℓ + 1 ≤ k - 1
  hhalf : 2 * ℓ ≤ k
  copy : CopyIn σ Θ (↑(canon σ) ∪ PM49 k ℓ)
  ne : Finset.univ.image Θ ≠ canon σ

/-- **Claim 4.11.** In the case `Θ(a) ∈ P_j` with `a ≤ ℓ`: `Θ_U ∩ P_M = ∅`, where
`Θ_U = {Θ(i) : r ≤ i ≤ k}`.

A step of the proof by contradiction of Lemma 4.10 (tex l.821): its context `Ctx410` cannot be
satisfied, because `lemma_4_10` proves `Σ` is the only copy, so the claim holds only vacuously, as
in the paper. Its proof does not use `ne` (`Θ ≠ Σ`), the fields `hℓ` and `hhalf` (`ℓ ≤ k/2`), or the
binder `hj` (the range of the segment index `j`). -/
theorem claim_4_11 (σ : Perm (Fin k)) (ℓ : ℕ) (Θ : Fin k → ℝ × ℝ) (hc : Ctx410 σ ℓ Θ)
    (a : ℕ) (ha : 1 ≤ a ∧ a ≤ ℓ) (j : ℤ) (hj : -(k : ℤ) + ℓ + 1 ≤ j ∧ j ≤ (k : ℤ) - ℓ - 1)
    (haj : th Θ a ∈ P49 ℓ j) :
    ∀ i : ℕ, ℓ + 1 ≤ i → i ≤ k → th Θ i ∉ PM49 k ℓ := by
  exact TB.c411 σ ℓ hc.pattern hc.hr Θ hc.copy a ha j haj

end LinfPermRemoval
