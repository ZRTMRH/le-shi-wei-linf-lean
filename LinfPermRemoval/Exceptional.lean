/-
Formalization of V. H. Le, R. Shi, F. Wei, "$L_\infty$ Permutation Removal Lemma"
(unpublished manuscript). Not part of Mathlib.
-/
import LinfPermRemoval.Geometry

/-!
# Subsection 4.2: the patterns `(31524)`, `(24153)`, `(42513)`, `(35142)`

After a dihedral symmetry the paper treats `σ = (31524)` (`oneLine σ = [3, 1, 5, 2, 4]`).

The claim inside the proof of Lemma 4.13 is a step of a proof by contradiction: its context
(`Ctx413`) fixes a `σ`-copy `Θ ≠ Σ`, which `lemma_4_13` shows cannot exist; the bundle without
the field `ne` is satisfiable (take `Θ = Σ`).
-/

open Equiv Finset

namespace LinfPermRemoval

/-- **Construction 4.12.** `I_M = (1,5) + t(1,-1)`, `0 ≤ t ≤ 2`, and `P_M = I_M ∖ ℤ²`. -/
def PM412 : Set (ℝ × ℝ) := closedSeg (1, 5) (1, -1) 2 \ lattice

/-- **Construction 4.12.** `I_B = (3,1) + t(1,-1)`, `0 ≤ t ≤ 2`, and `P_B = I_B ∖ ℤ²`. -/
def PB412 : Set (ℝ × ℝ) := closedSeg (3, 1) (1, -1) 2 \ lattice

/-- **Construction 4.12.** `I_R = (5,3) + t(1,-1)`, `0 ≤ t ≤ 2`, and `P_R = I_R ∖ ℤ²`. -/
def PR412 : Set (ℝ × ℝ) := closedSeg (5, 3) (1, -1) 2 \ lattice

namespace EX

/-- The values of `σ = (31524)` (0-based). -/
theorem sigma_vals {σ : Perm (Fin 5)} (hσ : oneLine σ = [3, 1, 5, 2, 4]) :
    σ 0 = 2 ∧ σ 1 = 0 ∧ σ 2 = 4 ∧ σ 3 = 1 ∧ σ 4 = 3 := by
  simp only [oneLine, List.ofFn_succ, List.ofFn_zero, List.cons.injEq] at hσ
  obtain ⟨h0, h1, h2, h3, h4, -⟩ := hσ
  refine ⟨Fin.ext ?_, Fin.ext ?_, Fin.ext ?_, Fin.ext ?_, Fin.ext ?_⟩ <;>
    simp_all

/-- A point of `I ∖ ℤ²`, `I = a + t(1,-1)` (`0 ≤ t ≤ 2`) with integral endpoints, lies strictly
between the endpoints in `x` and on the line `x + y = a.1 + a.2`. -/
theorem seg_mem {a b : ℝ} (ha : ((a, b) : ℝ × ℝ) ∈ lattice)
    (hb : ((a + 2, b - 2) : ℝ × ℝ) ∈ lattice) {p : ℝ × ℝ}
    (hp : p ∈ closedSeg (a, b) (1, -1) 2 \ lattice) :
    a < p.1 ∧ p.1 < a + 2 ∧ p.1 + p.2 = a + b := by
  obtain ⟨⟨t, ht0, ht2, rfl⟩, hnl⟩ := hp
  simp only
  rcases eq_or_lt_of_le ht0 with h | h
  · subst h; exact absurd (by simpa using ha) hnl
  rcases eq_or_lt_of_le ht2 with h' | h'
  · subst h'; exact absurd (by convert hb using 2 <;> ring) hnl
  refine ⟨by linarith, by linarith, by ring⟩

theorem lat (a b : ℤ) : (((a : ℝ), (b : ℝ)) : ℝ × ℝ) ∈ lattice := ⟨a, b, rfl⟩

/-- Every point of `D = Σ ∪ P_M ∪ P_B ∪ P_R` is one of the five points of `Σ` or lies on one of
the open segments `x + y = 6, 1 < x < 3`; `x + y = 4, 3 < x < 5`; `x + y = 8, 5 < x < 7`. -/
theorem mem_D {σ : Perm (Fin 5)} (hσ : oneLine σ = [3, 1, 5, 2, 4]) {p : ℝ × ℝ}
    (hp : p ∈ (↑(canon σ) : Set (ℝ × ℝ)) ∪ PM412 ∪ PB412 ∪ PR412) :
    (p.1 = 1 ∧ p.2 = 3) ∨ (p.1 = 2 ∧ p.2 = 1) ∨ (p.1 = 3 ∧ p.2 = 5) ∨ (p.1 = 4 ∧ p.2 = 2) ∨
      (p.1 = 5 ∧ p.2 = 4) ∨ (p.1 + p.2 = 6 ∧ 1 < p.1 ∧ p.1 < 3) ∨
      (p.1 + p.2 = 4 ∧ 3 < p.1 ∧ p.1 < 5) ∨ (p.1 + p.2 = 8 ∧ 5 < p.1 ∧ p.1 < 7) := by
  obtain ⟨s0, s1, s2, s3, s4⟩ := sigma_vals hσ
  rcases hp with ((hp | hp) | hp) | hp
  · simp only [canon, coe_image, coe_univ, Set.image_univ, Set.mem_range] at hp
    obtain ⟨i, rfl⟩ := hp
    fin_cases i <;> simp [canonPt, s0, s1, s2, s3, s4] <;> norm_num
  · have := seg_mem (by simpa using lat 1 5) (by convert lat 3 3 using 2 <;> norm_num) hp
    norm_num at this; right; right; right; right; right; left; refine ⟨?_, ?_, ?_⟩ <;> linarith
  · have := seg_mem (by simpa using lat 3 1) (by convert lat 5 (-1) using 2 <;> norm_num) hp
    norm_num at this; right; right; right; right; right; right; left
    refine ⟨?_, ?_, ?_⟩ <;> linarith
  · have := seg_mem (by simpa using lat 5 3) (by convert lat 7 1 using 2 <;> norm_num) hp
    norm_num at this; right; right; right; right; right; right; right
    refine ⟨?_, ?_, ?_⟩ <;> linarith

/-- Every `σ`-copy in `D` sits exactly at the points of `Σ`. -/
theorem coords {σ : Perm (Fin 5)} (hσ : oneLine σ = [3, 1, 5, 2, 4]) {Θ : Fin 5 → ℝ × ℝ}
    (hc : CopyIn σ Θ (↑(canon σ) ∪ PM412 ∪ PB412 ∪ PR412)) : ∀ i, Θ i = canonPt σ i := by
  obtain ⟨s0, s1, s2, s3, s4⟩ := sigma_vals hσ
  obtain ⟨⟨hx, hy⟩, hD⟩ := hc
  have x01 : (Θ 0).1 < (Θ 1).1 := hx (by decide)
  have x12 : (Θ 1).1 < (Θ 2).1 := hx (by decide)
  have x23 : (Θ 2).1 < (Θ 3).1 := hx (by decide)
  have x34 : (Θ 3).1 < (Θ 4).1 := hx (by decide)
  have y13 : (Θ 1).2 < (Θ 3).2 := (hy 1 3).2 (by rw [s1, s3]; decide)
  have y30 : (Θ 3).2 < (Θ 0).2 := (hy 3 0).2 (by rw [s3, s0]; decide)
  have y04 : (Θ 0).2 < (Θ 4).2 := (hy 0 4).2 (by rw [s0, s4]; decide)
  have y42 : (Θ 4).2 < (Θ 2).2 := (hy 4 2).2 (by rw [s4, s2]; decide)
  have m0 := mem_D hσ (hD 0)
  have m1 := mem_D hσ (hD 1)
  have m2 := mem_D hσ (hD 2)
  have m3 := mem_D hσ (hD 3)
  have m4 := mem_D hσ (hD 4)
  suffices h : (Θ 0).1 = 1 ∧ (Θ 0).2 = 3 ∧ (Θ 1).1 = 2 ∧ (Θ 1).2 = 1 ∧ (Θ 2).1 = 3 ∧
      (Θ 2).2 = 5 ∧ (Θ 3).1 = 4 ∧ (Θ 3).2 = 2 ∧ (Θ 4).1 = 5 ∧ (Θ 4).2 = 4 by
    obtain ⟨a0, b0, a1, b1, a2, b2, a3, b3, a4, b4⟩ := h
    intro i
    fin_cases i <;> ext <;> simp [canonPt, *] <;> norm_num
  -- split on the piece of `D` containing each point, discarding cases by the `x`- and `y`-order
  rcases m0 with (⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ |
      ⟨_, _, _⟩ | ⟨_, _, _⟩ | ⟨_, _, _⟩) <;>
    rcases m1 with (⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ |
      ⟨_, _, _⟩ | ⟨_, _, _⟩ | ⟨_, _, _⟩) <;>
    (try (exfalso; linarith)) <;>
    rcases m3 with (⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ |
      ⟨_, _, _⟩ | ⟨_, _, _⟩ | ⟨_, _, _⟩) <;>
    (try (exfalso; linarith)) <;>
    rcases m2 with (⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ |
      ⟨_, _, _⟩ | ⟨_, _, _⟩ | ⟨_, _, _⟩) <;>
    (try (exfalso; linarith)) <;>
    rcases m4 with (⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ |
      ⟨_, _, _⟩ | ⟨_, _, _⟩ | ⟨_, _, _⟩) <;>
    first
    | (exfalso; linarith)
    | (refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith)

/-- Every `σ`-copy in `D` has point set `Σ`. -/
theorem image_eq {σ : Perm (Fin 5)} (hσ : oneLine σ = [3, 1, 5, 2, 4]) {Θ : Fin 5 → ℝ × ℝ}
    (hc : CopyIn σ Θ (↑(canon σ) ∪ PM412 ∪ PB412 ∪ PR412)) :
    Finset.univ.image Θ = canon σ := by
  rw [canon, funext (coords hσ hc)]

end EX

/-- **Lemma 4.13.** Let `σ = (31524)`. If `Π` is associated with a permutation and
`Σ ⊆ Π ⊆ Σ ∪ P_M ∪ P_B ∪ P_R` (Construction 4.12), then `Σ` is the unique `σ`-copy in `Π`. The proof
does not use `hP : IsPermPointSet P`; the paper states it (tex l.884), and it is kept to match the
paper. -/
theorem lemma_4_13 (σ : Perm (Fin 5)) (hσ : oneLine σ = [3, 1, 5, 2, 4])
    (P : Finset (ℝ × ℝ)) (hP : IsPermPointSet P)
    (h₁ : (↑(canon σ) : Set (ℝ × ℝ)) ⊆ ↑P)
    (h₂ : (↑P : Set (ℝ × ℝ)) ⊆ ↑(canon σ) ∪ PM412 ∪ PB412 ∪ PR412) :
    IsUniqueCopy σ ↑P :=
  ⟨h₁, fun _ hc => EX.image_eq hσ ⟨hc.1, fun i => h₂ (hc.2 i)⟩⟩

/-- The context of the proof of Lemma 4.13 (tex l.890): `σ = (31524)` and
`Θ ⊆ D = Σ ∪ P_M ∪ P_B ∪ P_R` a `σ`-copy distinct from `Σ`. A proof by contradiction refuting
this context is `lemma_4_13`. -/
structure Ctx413 (σ : Perm (Fin 5)) (Θ : Fin 5 → ℝ × ℝ) : Prop where
  pattern : oneLine σ = [3, 1, 5, 2, 4]
  copy : CopyIn σ Θ (↑(canon σ) ∪ PM412 ∪ PB412 ∪ PR412)
  ne : Finset.univ.image Θ ≠ canon σ

/-- **Claim 4.14.** `Θ ∩ P_B = Θ ∩ P_R = ∅`.

A step of the proof by contradiction of Lemma 4.13 (tex l.890): its context `Ctx413` cannot be
satisfied, because `lemma_4_13` proves `Σ` is the only copy, so the claim holds only vacuously, as
in the paper. Its proof uses `ne`: it is exactly this refutation. -/
theorem claim_4_14 (σ : Perm (Fin 5)) (Θ : Fin 5 → ℝ × ℝ) (hc : Ctx413 σ Θ) :
    ∀ i, Θ i ∉ PB412 ∧ Θ i ∉ PR412 :=
  absurd (EX.image_eq hc.pattern hc.copy) hc.ne

end LinfPermRemoval
