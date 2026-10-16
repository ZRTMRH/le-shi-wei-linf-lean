/-
Formalization of V. H. Le, R. Shi, F. Wei, "$L_\infty$ Permutation Removal Lemma"
(unpublished manuscript). Not part of Mathlib.
-/
import LinfPermRemoval.TwoBlocks
import LinfPermRemoval.Exceptional
import LinfPermRemoval.Coincident
import LinfPermRemoval.TwoInternal

/-!
# Theorem 4.1 (the geometric construction theorem)
-/

open Equiv Finset

namespace LinfPermRemoval

namespace S4

open DISC

variable {k : ℕ}

theorem segH (a v : ℝ × ℝ) (T s : ℝ) (i : ℕ) (hv2 : v.2 ≠ 0) (hs : 0 ≤ s)
    (hT : s + 1 ≤ T) (h1 : (i : ℝ) ≤ a.2 + s * v.2) (h2 : a.2 + s * v.2 ≤ (i : ℝ) + 1)
    (h3 : (i : ℝ) ≤ a.2 + s * v.2 + v.2) (h4 : a.2 + s * v.2 + v.2 ≤ (i : ℝ) + 1) :
    ∀ p ∈ openSeg (a.1 + s * v.1, a.2 + s * v.2) v,
      p ∈ closedSeg a v T ∧ p ∉ lattice ∧ p ∈ hStripe i := by
  intro p hp
  have hH : p ∈ hStripe i := openSeg_subset_hStripe _ v i hv2 h1 h2 h3 h4 hp
  refine ⟨?_, notMem_lattice_of_hStripe hH, hH⟩
  obtain ⟨t, ht0, ht1, rfl⟩ := hp
  exact ⟨s + t, by linarith, by linarith, by simp only [Prod.mk.injEq]; constructor <;> ring⟩

theorem segV (a v : ℝ × ℝ) (T s : ℝ) (i : ℕ) (hv1 : v.1 ≠ 0) (hs : 0 ≤ s)
    (hT : s + 1 ≤ T) (h1 : (i : ℝ) ≤ a.1 + s * v.1) (h2 : a.1 + s * v.1 ≤ (i : ℝ) + 1)
    (h3 : (i : ℝ) ≤ a.1 + s * v.1 + v.1) (h4 : a.1 + s * v.1 + v.1 ≤ (i : ℝ) + 1) :
    ∀ p ∈ openSeg (a.1 + s * v.1, a.2 + s * v.2) v,
      p ∈ closedSeg a v T ∧ p ∉ lattice ∧ p ∈ vStripe i := by
  intro p hp
  have hV : p ∈ vStripe i := openSeg_subset_vStripe _ v i hv1 h1 h2 h3 h4 hp
  refine ⟨?_, notMem_lattice_of_vStripe hV, hV⟩
  obtain ⟨t, ht0, ht1, rfl⟩ := hp
  exact ⟨s + t, by linarith, by linarith, by simp only [Prod.mk.injEq]; constructor <;> ring⟩

theorem segH' (D : Set (ℝ × ℝ)) (a v : ℝ × ℝ) (T s : ℝ) (i : ℕ) (hv1 : v.1 ≠ 0)
    (hv2 : v.2 ≠ 0) (hs : 0 ≤ s)
    (hT : s + 1 ≤ T) (h1 : (i : ℝ) ≤ a.2 + s * v.2) (h2 : a.2 + s * v.2 ≤ (i : ℝ) + 1)
    (h3 : (i : ℝ) ≤ a.2 + s * v.2 + v.2) (h4 : a.2 + s * v.2 + v.2 ≤ (i : ℝ) + 1)
    (hD : ∀ p, p ∈ closedSeg a v T → p ∉ lattice → p ∈ hStripe i → p ∈ D) :
    ∃ a' v' : ℝ × ℝ, v'.1 ≠ 0 ∧ v'.2 ≠ 0 ∧ openSeg a' v' ⊆ D ∧ openSeg a' v' ⊆ hStripe i := by
  have := segH a v T s i hv2 hs hT h1 h2 h3 h4
  exact ⟨_, v, hv1, hv2, fun p hp => hD p (this p hp).1 (this p hp).2.1 (this p hp).2.2,
    fun p hp => (this p hp).2.2⟩

theorem segV' (D : Set (ℝ × ℝ)) (a v : ℝ × ℝ) (T s : ℝ) (i : ℕ) (hv1 : v.1 ≠ 0)
    (hv2 : v.2 ≠ 0) (hs : 0 ≤ s)
    (hT : s + 1 ≤ T) (h1 : (i : ℝ) ≤ a.1 + s * v.1) (h2 : a.1 + s * v.1 ≤ (i : ℝ) + 1)
    (h3 : (i : ℝ) ≤ a.1 + s * v.1 + v.1) (h4 : a.1 + s * v.1 + v.1 ≤ (i : ℝ) + 1)
    (hD : ∀ p, p ∈ closedSeg a v T → p ∉ lattice → p ∈ vStripe i → p ∈ D) :
    ∃ a' v' : ℝ × ℝ, v'.1 ≠ 0 ∧ v'.2 ≠ 0 ∧ openSeg a' v' ⊆ D ∧ openSeg a' v' ⊆ vStripe i := by
  have := segV a v T s i hv1 hs hT h1 h2 h3 h4
  exact ⟨_, v, hv1, hv2, fun p hp => hD p (this p hp).1 (this p hp).2.1 (this p hp).2.2,
    fun p hp => (this p hp).2.2⟩

/-! ### Coverage for Construction 4.4 -/

theorem cover44 :
    (∀ i, 1 ≤ i → i ≤ k - 1 → ∃ a v : ℝ × ℝ, v.1 ≠ 0 ∧ v.2 ≠ 0 ∧
      openSeg a v ⊆ PM44 k ∧ openSeg a v ⊆ hStripe i) ∧
    (∀ i, 1 ≤ i → i ≤ k - 1 → ∃ a v : ℝ × ℝ, v.1 ≠ 0 ∧ v.2 ≠ 0 ∧
      openSeg a v ⊆ PM44 k ∧ openSeg a v ⊆ vStripe i) := by
  constructor
  · intro i h1 h2
    have hik : ((k - i : ℕ) : ℝ) = (k : ℝ) - i := by rw [Nat.cast_sub (by omega)]
    refine ⟨((((k - i : ℕ) : ℤ) : ℝ), (k : ℝ) + 1 - (((k - i : ℕ) : ℤ) : ℝ)), (-1, -1),
      by norm_num, by norm_num, fun p hp => Set.mem_iUnion₂.2 ⟨((k - i : ℕ) : ℤ),
        ⟨by omega, by omega⟩, hp⟩, ?_⟩
    apply openSeg_subset_hStripe _ _ i (by norm_num) <;> push_cast [hik] <;> linarith
  · intro i h1 h2
    refine ⟨((((i + 1 : ℕ) : ℤ) : ℝ), (k : ℝ) + 1 - (((i + 1 : ℕ) : ℤ) : ℝ)), (-1, -1),
      by norm_num, by norm_num, fun p hp => Set.mem_iUnion₂.2 ⟨((i + 1 : ℕ) : ℤ),
        ⟨by omega, by omega⟩, hp⟩, ?_⟩
    apply openSeg_subset_vStripe _ _ i (by norm_num) <;> push_cast <;> linarith

/-! ### Coverage for Construction 4.9 -/

theorem cover49 {ℓ : ℕ} (hhalf : 2 * ℓ ≤ k) :
    (∀ i, 1 ≤ i → i ≤ k - 1 → ∃ a v : ℝ × ℝ, v.1 ≠ 0 ∧ v.2 ≠ 0 ∧
      openSeg a v ⊆ PM49 k ℓ ∧ openSeg a v ⊆ hStripe i) ∧
    (∀ i, 1 ≤ i → i ≤ k - 1 → ∃ a v : ℝ × ℝ, v.1 ≠ 0 ∧ v.2 ≠ 0 ∧
      openSeg a v ⊆ PM49 k ℓ ∧ openSeg a v ⊆ vStripe i) := by
  constructor
  · intro i h1 h2
    refine ⟨((ℓ : ℝ) - (((i : ℤ) - ℓ : ℤ) : ℝ), (ℓ : ℝ) + (((i : ℤ) - ℓ : ℤ) : ℝ)), (1, 1),
      by norm_num, by norm_num, fun p hp => Set.mem_iUnion₂.2 ⟨(i : ℤ) - ℓ,
        ⟨by omega, by omega⟩, hp⟩, ?_⟩
    apply openSeg_subset_hStripe _ _ i (by norm_num) <;> push_cast <;> linarith
  · intro i h1 h2
    refine ⟨((ℓ : ℝ) - (((ℓ : ℤ) - i : ℤ) : ℝ), (ℓ : ℝ) + (((ℓ : ℤ) - i : ℤ) : ℝ)), (1, 1),
      by norm_num, by norm_num, fun p hp => Set.mem_iUnion₂.2 ⟨(ℓ : ℤ) - i,
        ⟨by omega, by omega⟩, hp⟩, ?_⟩
    apply openSeg_subset_vStripe _ _ i (by norm_num) <;> push_cast <;> linarith


/-! ### Symmetry helpers -/

theorem of_revP {σ : Perm (Fin k)} {N : ℕ} (h : GeomConclusion (revP σ) N) :
    GeomConclusion σ N := by simpa using geomConclusion_revP h

theorem of_compP {σ : Perm (Fin k)} {N : ℕ} (h : GeomConclusion (compP σ) N) :
    GeomConclusion σ N := by simpa using geomConclusion_compP h

theorem of_rc {σ : Perm (Fin k)} {N : ℕ} (h : GeomConclusion (compP (revP σ)) N) :
    GeomConclusion σ N := of_revP (of_compP h)

/-! ### Subsection 4.1 -/

theorem four_le_of_twoBlockA_one {σ : Perm (Fin k)} (hT : ThmHyp σ) (hA : IsTwoBlockA σ 1) :
    4 ≤ k := by
  rcases thmHyp_cases hT with h | ⟨rfl, h | h⟩
  · exact h
  · subst h
    have := hA.2.2 2 (by norm_num) (by norm_num)
    revert this; decide
  · subst h
    have := hA.2.2 1 (by norm_num) (by norm_num)
    revert this; decide

theorem good45 {σ : Perm (Fin k)} (hA : IsTwoBlockA σ 1) (hk : 4 ≤ k) :
    GeomConclusion σ (N0 k) :=
  geomConclusion_of_segs σ (by omega) (PM44 k) cover44.1 cover44.2
    fun P hP h1 h2 => lemma_4_5 σ hA hk P hP h1 h2

theorem good410 {σ : Perm (Fin k)} {ℓ : ℕ} (hA : IsTwoBlockA σ ℓ) (hℓ : 2 ≤ ℓ)
    (hr : ℓ + 1 ≤ k - 1) (hhalf : 2 * ℓ ≤ k) : GeomConclusion σ (N0 k) :=
  geomConclusion_of_segs σ (by omega) (PM49 k ℓ) (cover49 hhalf).1
    (cover49 hhalf).2 fun P hP h1 h2 => lemma_4_10 σ ℓ hA hℓ hr hhalf P hP h1 h2

theorem goodA {σ : Perm (Fin k)} {ℓ : ℕ} (hT : ThmHyp σ) (hA : IsTwoBlockA σ ℓ) :
    GeomConclusion σ (N0 k) := by
  have hrc : IsTwoBlockA (compP (revP σ)) (k - ℓ) := isTwoBlockB_compP (isTwoBlockA_revP hA)
  have hTrc : ThmHyp (compP (revP σ)) := thmHyp_compP (thmHyp_revP hT)
  obtain ⟨h1, h2, -⟩ := id hA
  by_cases hl1 : ℓ = 1
  · subst hl1; exact good45 hA (four_le_of_twoBlockA_one hT hA)
  by_cases hlk : ℓ = k - 1
  · have e : k - ℓ = 1 := by omega
    rw [e] at hrc
    exact of_rc (good45 hrc (four_le_of_twoBlockA_one hTrc hrc))
  by_cases hh : 2 * ℓ ≤ k
  · exact good410 hA (by omega) (by omega) hh
  · exact of_rc (good410 hrc (by omega) (by omega) (by omega))

theorem goodTB {σ : Perm (Fin k)} (hT : ThmHyp σ) (h : IsTwoBlock σ) :
    GeomConclusion σ (N0 k) := by
  rcases h with ⟨ℓ, hA⟩ | ⟨r, hB⟩
  · exact goodA hT hA
  · exact of_revP (goodA (thmHyp_revP hT) (isTwoBlockB_revP hB))


/-! ### Subsection 4.2 -/

theorem good413 {σ : Perm (Fin 5)} (hσ : oneLine σ = [3, 1, 5, 2, 4]) :
    GeomConclusion σ (N0 5) := by
  refine geomConclusion_of_segs σ (by norm_num) (PM412 ∪ PB412 ∪ PR412) ?_ ?_
    fun P hP h1 h2 => lemma_4_13 σ hσ P hP h1 (h2.trans fun p hp => ?_)
  · intro i h1 h2
    have h2' : i ≤ 4 := h2
    interval_cases i
    · exact segH' _ (5, 3) (1, -1) 2 1 1 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        fun p h1 h2 _ => Or.inr ⟨h1, h2⟩
    · exact segH' _ (5, 3) (1, -1) 2 0 2 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        fun p h1 h2 _ => Or.inr ⟨h1, h2⟩
    · exact segH' _ (1, 5) (1, -1) 2 1 3 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        fun p h1 h2 _ => Or.inl (Or.inl ⟨h1, h2⟩)
    · exact segH' _ (1, 5) (1, -1) 2 0 4 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        fun p h1 h2 _ => Or.inl (Or.inl ⟨h1, h2⟩)
  · intro i h1 h2
    have h2' : i ≤ 4 := h2
    interval_cases i
    · exact segV' _ (1, 5) (1, -1) 2 0 1 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        fun p h1 h2 _ => Or.inl (Or.inl ⟨h1, h2⟩)
    · exact segV' _ (1, 5) (1, -1) 2 1 2 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        fun p h1 h2 _ => Or.inl (Or.inl ⟨h1, h2⟩)
    · exact segV' _ (3, 1) (1, -1) 2 0 3 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        fun p h1 h2 _ => Or.inl (Or.inr ⟨h1, h2⟩)
    · exact segV' _ (3, 1) (1, -1) 2 1 4 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        fun p h1 h2 _ => Or.inl (Or.inr ⟨h1, h2⟩)
  · simp only [Set.mem_union] at hp ⊢
    tauto

theorem goodExc5 {σ : Perm (Fin 5)} (h : IsExcFive σ) : GeomConclusion σ (N0 5) := by
  have h0 : GeomConclusion e31524 (N0 5) := good413 (by decide)
  obtain ⟨hk, h | h | h | h⟩ := isExcFive_cases h
  · subst h; exact h0
  · subst h
    have e : e24153 = invP e31524 := by decide
    rw [e]; exact geomConclusion_invP h0
  · subst h
    have e : e42513 = revP e31524 := by decide
    rw [e]; exact geomConclusion_revP h0
  · subst h
    have e : e35142 = compP e31524 := by decide
    rw [e]; exact geomConclusion_compP h0

theorem goodExc {σ : Perm (Fin k)} (h : IsExcFive σ) : GeomConclusion σ (N0 k) := by
  obtain ⟨rfl, -⟩ := isExcFive_cases h
  exact goodExc5 h


/-! ### Subsection 4.3 -/

/-- Closing numeric side conditions of the segment helpers. -/
local macro "s4_lin" : tactic => `(tactic| first | (norm_num <;> linarith) | linarith | norm_num)

theorem good416 {σ : Perm (Fin k)} (hσ : Hyp416 σ) : GeomConclusion σ (N0 k) := by
  have hk3 := thmHyp_three_le hσ.thm
  have hk : (3 : ℝ) ≤ k := by exact_mod_cast hk3
  refine geomConclusion_of_segs' σ (by omega) (D415 σ) (fun p hp => Or.inl (Or.inl (Or.inl
    (Or.inl hp)))) ?_ ?_ fun P hP h1 h2 => lemma_4_16 σ hσ P hP h1 h2
  · intro i h1 h2
    have hi1 : (1 : ℝ) ≤ i := by exact_mod_cast h1
    have hi2 : (i : ℝ) ≤ k - 1 := by
      have : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
      rw [← this]; exact_mod_cast h2
    by_cases hi : i = 1
    · subst hi
      by_cases c : sval σ k ≠ 2
      · exact segH' _ ((k : ℝ), 2) (1, -1) 1 0 1 (by s4_lin) (by s4_lin) (by s4_lin) (by s4_lin) (by s4_lin)
          (by s4_lin) (by s4_lin) (by s4_lin) fun p h1 h2 _ => Or.inl (Or.inl (Or.inr
            (by unfold PR415; rw [ite_eq_left c]; exact ⟨h1, h2⟩)))
      · exact segH' _ (2, 1) (1, 1) 1 0 1 (by s4_lin) (by s4_lin) (by s4_lin) (by s4_lin) (by s4_lin)
          (by s4_lin) (by s4_lin) (by s4_lin) fun p h1 h2 _ => Or.inl (Or.inl (Or.inr
            (by unfold PR415; rw [ite_eq_right c]; exact ⟨h1, h2⟩)))
    have hi2' : (2 : ℝ) ≤ i := by
      have : 2 ≤ i := by omega
      exact_mod_cast this
    by_cases c : sval σ 2 ≠ k
    · exact segH' _ (1, 2) (-1, 1) ((k : ℝ) - 2) ((i : ℝ) - 2) i (by s4_lin) (by s4_lin) (by s4_lin)
        (by s4_lin) (by s4_lin) (by s4_lin) (by s4_lin) (by s4_lin) fun p h1 h2 _ => Or.inl (Or.inl (Or.inl
          (Or.inr (by unfold PL415; rw [ite_eq_left c]; exact ⟨h1, h2⟩))))
    by_cases hi' : i = 2
    · subst hi'
      exact segH' _ (1, 2) (1, 1) 1 0 2 (by s4_lin) (by s4_lin) (by s4_lin) (by s4_lin) (by s4_lin)
        (by s4_lin) (by s4_lin) (by s4_lin) fun p h1 h2 _ => Or.inr
          (by unfold PU415; rw [ite_eq_right c]; exact ⟨h1, h2⟩)
    have hi3 : (3 : ℝ) ≤ i := by
      have : 3 ≤ i := by omega
      exact_mod_cast this
    exact segH' _ (1, 3) (-1, 1) ((k : ℝ) - 3) ((i : ℝ) - 3) i (by s4_lin) (by s4_lin) (by s4_lin)
      (by s4_lin) (by s4_lin) (by s4_lin) (by s4_lin) (by s4_lin) fun p h1 h2 _ => Or.inl (Or.inl (Or.inl
        (Or.inr (by unfold PL415; rw [ite_eq_right c]; exact ⟨h1, h2⟩))))
  · intro i h1 h2
    have hi1 : (1 : ℝ) ≤ i := by exact_mod_cast h1
    have hi2 : (i : ℝ) ≤ k - 1 := by
      have : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
      rw [← this]; exact_mod_cast h2
    by_cases hi : i = 1
    · subst hi
      by_cases c : sval σ 2 ≠ k
      · exact segV' _ (2, (k : ℝ)) (-1, 1) 1 0 1 (by s4_lin) (by s4_lin) (by s4_lin) (by s4_lin) (by s4_lin)
          (by s4_lin) (by s4_lin) (by s4_lin) fun p h1 h2 _ => Or.inr
            (by unfold PU415; rw [ite_eq_left c]; exact ⟨h1, h2⟩)
      · exact segV' _ (1, 2) (1, 1) 1 0 1 (by s4_lin) (by s4_lin) (by s4_lin) (by s4_lin) (by s4_lin)
          (by s4_lin) (by s4_lin) (by s4_lin) fun p h1 h2 _ => Or.inr
            (by unfold PU415; rw [ite_eq_right c]; exact ⟨h1, h2⟩)
    have hi2' : (2 : ℝ) ≤ i := by
      have : 2 ≤ i := by omega
      exact_mod_cast this
    by_cases c : sval σ k ≠ 2
    · exact segV' _ (2, 1) (1, -1) ((k : ℝ) - 2) ((i : ℝ) - 2) i (by s4_lin) (by s4_lin) (by s4_lin)
        (by s4_lin) (by s4_lin) (by s4_lin) (by s4_lin) (by s4_lin) fun p h1 h2 _ => Or.inl (Or.inr
          (by unfold PB415; rw [ite_eq_left c]; exact ⟨h1, h2⟩))
    by_cases hi' : i = 2
    · subst hi'
      exact segV' _ (2, 1) (1, 1) 1 0 2 (by s4_lin) (by s4_lin) (by s4_lin) (by s4_lin) (by s4_lin)
        (by s4_lin) (by s4_lin) (by s4_lin) fun p h1 h2 _ => Or.inl (Or.inl (Or.inr
          (by unfold PR415; rw [ite_eq_right c]; exact ⟨h1, h2⟩)))
    have hi3 : (3 : ℝ) ≤ i := by
      have : 3 ≤ i := by omega
      exact_mod_cast this
    exact segV' _ (3, 1) (1, -1) ((k : ℝ) - 3) ((i : ℝ) - 3) i (by s4_lin) (by s4_lin) (by s4_lin)
      (by s4_lin) (by s4_lin) (by s4_lin) (by s4_lin) (by s4_lin) fun p h1 h2 _ => Or.inl (Or.inr
        (by unfold PB415; rw [ite_eq_right c]; exact ⟨h1, h2⟩))


theorem goodCoinc {σ : Perm (Fin k)} (hT : ThmHyp σ) (h41 : ¬ IsTwoBlock σ)
    (h42 : ¬ IsExcFive σ) (h : lv σ = 1 ∨ lv σ = k ∨ rv σ = 1 ∨ rv σ = k) :
    GeomConclusion σ (N0 k) := by
  have hk : 1 ≤ k := by have := thmHyp_three_le hT; omega
  have mk : ∀ τ : Perm (Fin k), ThmHyp τ → ¬ IsTwoBlock τ → ¬ IsExcFive τ → lv τ = 1 →
      GeomConclusion τ (N0 k) := fun τ h1 h2 h3 h4 => good416 ⟨h4, h2, h3, h1⟩
  rcases h with h | h | h | h
  · exact mk σ hT h41 h42 h
  · exact of_compP (mk _ (thmHyp_compP hT) (by rwa [isTwoBlock_compP_iff])
      (by rwa [isExcFive_compP_iff]) (by rw [lv_compP _ hk, h]; omega))
  · exact of_revP (mk _ (thmHyp_revP hT) (by rwa [isTwoBlock_revP_iff])
      (by rwa [isExcFive_revP_iff]) (by rw [lv_revP, h]))
  · exact of_rc (mk _ (thmHyp_compP (thmHyp_revP hT))
      (by rwa [isTwoBlock_compP_iff, isTwoBlock_revP_iff])
      (by rwa [isExcFive_compP_iff, isExcFive_revP_iff]) (by rw [lv_compP _ hk, lv_revP, h]; omega))

/-! ### Subsection 4.4: Construction 4.39 covers every stripe -/

theorem good440 {σ : Perm (Fin k)} (hσ : Hyp440 σ) : GeomConclusion σ (N0 k) := by
  obtain ⟨hst, hlr, hbu, -, -, -, -⟩ := id hσ
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with rfl | h
    · simp [lv, rv, sval] at hlr
    · exact h
  have hl1 : 1 ≤ lv σ := one_le_sval σ le_rfl hk1
  have hrk : rv σ ≤ k := sval_le σ k
  have hb1 : 1 ≤ bp σ := one_le_spos σ le_rfl hk1
  have huk : up σ ≤ k := spos_le σ k
  have hl2 := hst.l_ne
  have hr2 := hst.r_ne
  have hk4 : 4 ≤ k := by omega
  have hkR : (4 : ℝ) ≤ k := by exact_mod_cast hk4
  have hlR : (lv σ : ℝ) + 1 = rv σ := by exact_mod_cast hlr
  have hbR : (bp σ : ℝ) + 1 = up σ := by exact_mod_cast hbu
  have hlt : lv σ < rv σ := by omega
  have hbt : bp σ < up σ := by omega
  refine geomConclusion_of_segs' σ (by omega) (D439 σ)
    (fun p hp => Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl hp)))))) ?_ ?_
    fun P hP h1 h2 => lemma_4_40 σ hσ P hP h1 h2
  · intro i h1 h2
    have hi1 : (1 : ℝ) ≤ i := by exact_mod_cast h1
    have hi2 : (i : ℝ) ≤ k - 1 := by
      have : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
      rw [← this]; exact_mod_cast h2
    rcases lt_trichotomy i (lv σ) with hi | rfl | hi
    · -- `P_R` covers `H_i` for `i ≤ r - 2`
      have hiR : (i : ℝ) + 1 ≤ (rv σ : ℝ) - 1 := by
        have : i + 2 ≤ rv σ := by omega
        have : ((i + 2 : ℕ) : ℝ) ≤ rv σ := by exact_mod_cast this
        push_cast at this; linarith
      have side : ∀ p : ℝ × ℝ, p ∈ hStripe i →
          (if lv σ < rv σ then p.2 < (rv σ : ℝ) - 1 else (rv σ : ℝ) + 1 < p.2) := by
        intro p hp; rw [ite_eq_left hlt]; linarith [hp.2]
      by_cases c : rv σ < sval σ (k - 1)
      · exact segH' _ ((k : ℝ), 1) (1, 1) ((k : ℝ) - 1) ((i : ℝ) - 1) i (by s4_lin) (by s4_lin)
          (by s4_lin) (by s4_lin) (by s4_lin) (by s4_lin) (by s4_lin) (by s4_lin) fun p h1 h2 h3 =>
            Or.inl (Or.inl (Or.inl (Or.inl (Or.inr
              ⟨⟨by unfold IR419; rw [ite_eq_left c]; exact h1, h2⟩, side p h3⟩))))
      · exact segH' _ ((k : ℝ), (k : ℝ)) (1, -1) ((k : ℝ) - 1) ((k : ℝ) - 1 - i) i (by s4_lin)
          (by s4_lin) (by s4_lin) (by s4_lin) (by s4_lin) (by s4_lin) (by s4_lin) (by s4_lin) fun p h1 h2 h3 =>
            Or.inl (Or.inl (Or.inl (Or.inl (Or.inr
              ⟨⟨by unfold IR419; rw [ite_eq_right c]; exact h1, h2⟩, side p h3⟩))))
    · -- `P_H` covers `H_ℓ`
      exact ⟨_, (1, 1), by norm_num, by norm_num, fun p hp => Or.inl (Or.inr hp),
        openSeg_subset_hStripe _ _ _ (by norm_num) (by s4_lin) (by s4_lin) (by s4_lin) (by s4_lin)⟩
    · -- `P_L` covers `H_i` for `i ≥ ℓ + 1`
      have hiL : (lv σ : ℝ) + 1 ≤ i := by
        have : lv σ + 1 ≤ i := by omega
        exact_mod_cast this
      have side : ∀ p : ℝ × ℝ, p ∈ hStripe i →
          (if lv σ < rv σ then (lv σ : ℝ) + 1 < p.2 else p.2 < (lv σ : ℝ) - 1) := by
        intro p hp; rw [ite_eq_left hlt]; linarith [hp.1]
      by_cases c : lv σ < sval σ 2
      · exact segH' _ (1, 1) (-1, 1) ((k : ℝ) - 1) ((i : ℝ) - 1) i (by s4_lin) (by s4_lin)
          (by s4_lin) (by s4_lin) (by s4_lin) (by s4_lin) (by s4_lin) (by s4_lin) fun p h1 h2 h3 =>
            Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr
              ⟨⟨by unfold IL419; rw [ite_eq_left c]; exact h1, h2⟩, side p h3⟩)))))
      · exact segH' _ (1, (k : ℝ)) (-1, -1) ((k : ℝ) - 1) ((k : ℝ) - 1 - i) i (by s4_lin)
          (by s4_lin) (by s4_lin) (by s4_lin) (by s4_lin) (by s4_lin) (by s4_lin) (by s4_lin) fun p h1 h2 h3 =>
            Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr
              ⟨⟨by unfold IL419; rw [ite_eq_right c]; exact h1, h2⟩, side p h3⟩)))))
  · intro i h1 h2
    have hi1 : (1 : ℝ) ≤ i := by exact_mod_cast h1
    have hi2 : (i : ℝ) ≤ k - 1 := by
      have : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
      rw [← this]; exact_mod_cast h2
    rcases lt_trichotomy i (bp σ) with hi | rfl | hi
    · -- `P_U` covers `V_i` for `i ≤ u - 2`
      have hiU : (i : ℝ) + 1 ≤ (up σ : ℝ) - 1 := by
        have : i + 2 ≤ up σ := by omega
        have : ((i + 2 : ℕ) : ℝ) ≤ up σ := by exact_mod_cast this
        push_cast at this; linarith
      have side : ∀ p : ℝ × ℝ, p ∈ vStripe i →
          (if bp σ < up σ then p.1 < (up σ : ℝ) - 1 else (up σ : ℝ) + 1 < p.1) := by
        intro p hp; rw [ite_eq_left hbt]; linarith [hp.2]
      by_cases c : up σ < spos σ (k - 1)
      · exact segV' _ (1, (k : ℝ)) (1, 1) ((k : ℝ) - 1) ((i : ℝ) - 1) i (by s4_lin) (by s4_lin)
          (by s4_lin) (by s4_lin) (by s4_lin) (by s4_lin) (by s4_lin) (by s4_lin) fun p h1 h2 h3 =>
            Or.inl (Or.inl (Or.inr
              ⟨⟨by unfold IU419; rw [ite_eq_left c]; exact h1, h2⟩, side p h3⟩))
      · exact segV' _ ((k : ℝ), (k : ℝ)) (-1, 1) ((k : ℝ) - 1) ((k : ℝ) - 1 - i) i (by s4_lin)
          (by s4_lin) (by s4_lin) (by s4_lin) (by s4_lin) (by s4_lin) (by s4_lin) (by s4_lin) fun p h1 h2 h3 =>
            Or.inl (Or.inl (Or.inr
              ⟨⟨by unfold IU419; rw [ite_eq_right c]; exact h1, h2⟩, side p h3⟩))
    · -- `P_V` covers `V_b = V_{u-1}`
      exact ⟨_, (1, 1), by norm_num, by norm_num, fun p hp => Or.inr hp,
        openSeg_subset_vStripe _ _ _ (by norm_num) (by s4_lin) (by s4_lin) (by s4_lin) (by s4_lin)⟩
    · -- `P_B` covers `V_i` for `i ≥ b + 1`
      have hiB : (bp σ : ℝ) + 1 ≤ i := by
        have : bp σ + 1 ≤ i := by omega
        exact_mod_cast this
      have side : ∀ p : ℝ × ℝ, p ∈ vStripe i →
          (if bp σ < up σ then (bp σ : ℝ) + 1 < p.1 else p.1 < (bp σ : ℝ) - 1) := by
        intro p hp; rw [ite_eq_left hbt]; linarith [hp.1]
      by_cases c : bp σ < spos σ 2
      · exact segV' _ (1, 1) (1, -1) ((k : ℝ) - 1) ((i : ℝ) - 1) i (by s4_lin) (by s4_lin)
          (by s4_lin) (by s4_lin) (by s4_lin) (by s4_lin) (by s4_lin) (by s4_lin) fun p h1 h2 h3 =>
            Or.inl (Or.inl (Or.inl (Or.inr
              ⟨⟨by unfold IB419; rw [ite_eq_left c]; exact h1, h2⟩, side p h3⟩)))
      · exact segV' _ ((k : ℝ), 1) (-1, -1) ((k : ℝ) - 1) ((k : ℝ) - 1 - i) i (by s4_lin)
          (by s4_lin) (by s4_lin) (by s4_lin) (by s4_lin) (by s4_lin) (by s4_lin) (by s4_lin) fun p h1 h2 h3 =>
            Or.inl (Or.inl (Or.inl (Or.inr
              ⟨⟨by unfold IB419; rw [ite_eq_right c]; exact h1, h2⟩, side p h3⟩)))


/-! ### Subsection 4.4: the case analysis -/

theorem rd_mono {σ : Perm (Fin k)} (h : RD σ) {i : ℕ} (hi : up σ ≤ i) :
    ∀ j, i < j → j ≤ k → sval σ j < sval σ i := by
  intro j hij hjk
  induction j with
  | zero => omega
  | succ j ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h' | rfl
    · exact (h j (by omega) (by omega)).trans (ih h' (by omega))
    · exact h i hi (by omega)

/-- Basic ranges under the standing hypotheses of Subsection 4.4. -/
theorem st_facts {σ : Perm (Fin k)} (hst : Standing44 σ) :
    3 ≤ k ∧ 2 ≤ lv σ ∧ lv σ ≤ k - 1 ∧ 2 ≤ rv σ ∧ rv σ ≤ k - 1 ∧ 2 ≤ bp σ ∧ bp σ ≤ k - 1 ∧
      2 ≤ up σ ∧ up σ ≤ k - 1 ∧ lv σ ≠ rv σ ∧ bp σ ≠ up σ := by
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with rfl | h
    · exact absurd (sval_le σ 1) (by have := hst.l_ne.2; unfold lv at this; omega)
    · exact h
  have hl1 : 1 ≤ lv σ := one_le_sval σ le_rfl hk1
  have hlk : lv σ ≤ k := sval_le σ 1
  have hr1 : 1 ≤ rv σ := one_le_sval σ hk1 le_rfl
  have hrk : rv σ ≤ k := sval_le σ k
  have hb1 : 1 ≤ bp σ := one_le_spos σ le_rfl hk1
  have hbk : bp σ ≤ k := spos_le σ 1
  have hu1 : 1 ≤ up σ := one_le_spos σ hk1 le_rfl
  have huk : up σ ≤ k := spos_le σ k
  have hb1' : bp σ ≠ 1 := fun h => hst.l_ne.1 ((bp_eq_one_iff σ).1 h)
  have hbk' : bp σ ≠ k := fun h => hst.r_ne.1 ((bp_eq_k_iff σ hk1).1 h)
  have hu1' : up σ ≠ 1 := fun h => hst.l_ne.2 ((up_eq_one_iff σ hk1).1 h)
  have huk' : up σ ≠ k := fun h => hst.r_ne.2 ((up_eq_k_iff σ hk1).1 h)
  have hk3 : 3 ≤ k := by have := hst.l_ne; omega
  have hlr : lv σ ≠ rv σ := by
    intro h
    have e1 : spos σ (lv σ) = 1 := spos_sval σ le_rfl hk1
    have e2 : spos σ (rv σ) = k := spos_sval σ hk1 le_rfl
    rw [h] at e1; omega
  have hbu : bp σ ≠ up σ := by
    intro h
    have e1 : sval σ (bp σ) = 1 := sval_spos σ le_rfl hk1
    have e2 : sval σ (up σ) = k := sval_spos σ hk1 le_rfl
    rw [h] at e1; omega
  have := hst.l_ne; have := hst.r_ne
  omega

theorem standing_revP {σ : Perm (Fin k)} (hst : Standing44 σ) : Standing44 (revP σ) :=
  ⟨by rw [isTwoBlock_revP_iff]; exact hst.not41, by rw [isExcFive_revP_iff]; exact hst.not42,
    by rw [lv_revP]; exact hst.r_ne, by rw [rv_revP]; exact hst.l_ne⟩

theorem standing_compP {σ : Perm (Fin k)} (hst : Standing44 σ) : Standing44 (compP σ) := by
  have := st_facts hst
  refine ⟨by rw [isTwoBlock_compP_iff]; exact hst.not41,
    by rw [isExcFive_compP_iff]; exact hst.not42, ?_, ?_⟩
  · rw [lv_compP _ (by omega)]; omega
  · rw [rv_compP _ (by omega)]; omega

theorem spos_rc (σ : Perm (Fin k)) {j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ k) :
    spos (compP (revP σ)) j = k + 1 - spos σ (k + 1 - j) := by
  rw [spos_compP _ h1 h2, spos_revP _ (by omega) (by omega)]

/-- The simultaneous exceptional case (tex l.1465–1474), after the symmetry making (4.18) hold:
either Corollary 4.38 applies, or (RD) fails, so its exception is (4.20) and Lemma 4.40
applies. -/
theorem lemA (M N38 : ℕ) (hM0 : N0 k ≤ M) (hM : N38 ≤ M)
    (h38 : ∀ σ : Perm (Fin k), Standing44 σ → bp σ + 1 = up σ →
      ¬ (lv σ + 1 = rv σ ∧
        ((LD σ ∧ ¬ RD σ ∧ sval σ 2 < sval σ (up σ + 1) ∧ sval σ (up σ + 1) < lv σ) ∨
         (RD σ ∧ ¬ LD σ ∧ rv σ < sval σ (bp σ - 1) ∧ sval σ (bp σ - 1) < sval σ (k - 1)))) →
      GeomConclusion σ N38)
    {σ : Perm (Fin k)} (hst : Standing44 σ) (hbu : bp σ + 1 = up σ)
    (hud : UD σ) (hpos : up σ < spos σ (lv σ - 1) ∧ spos σ (lv σ - 1) < spos σ (k - 1)) :
    GeomConclusion σ M := by
  obtain ⟨hk3, hl2, hlk, -⟩ := st_facts hst
  by_cases hex : lv σ + 1 = rv σ ∧
      ((LD σ ∧ ¬ RD σ ∧ sval σ 2 < sval σ (up σ + 1) ∧ sval σ (up σ + 1) < lv σ) ∨
       (RD σ ∧ ¬ LD σ ∧ rv σ < sval σ (bp σ - 1) ∧ sval σ (bp σ - 1) < sval σ (k - 1)))
  · rcases hex.2 with ⟨hld, -, hval⟩ | ⟨hrd, -⟩
    · exact GeomConclusion.mono (good440 ⟨hst, hex.1, hbu, hpos, hval, hud, hld⟩) hM0
    · exfalso
      have hq : spos σ (k - 1) ≤ k := spos_le σ _
      have := rd_mono hrd (le_of_lt hpos.1) _ hpos.2 hq
      rw [sval_spos σ (by omega) (by omega), sval_spos σ (by omega) (by omega)] at this
      omega
  · exact GeomConclusion.mono (h38 σ hst hbu hex) hM

/-- Corollary 4.37 together with the simultaneous exceptional case: `ℓ = r - 1`. -/
theorem lemB (M N37 N38 : ℕ) (hM0 : N0 k ≤ M) (hM7 : N37 ≤ M) (hM8 : N38 ≤ M)
    (h37 : ∀ σ : Perm (Fin k), Standing44 σ → lv σ + 1 = rv σ →
      ¬ (bp σ + 1 = up σ ∧
        ((UD σ ∧ ¬ BD σ ∧ up σ < spos σ (lv σ - 1) ∧ spos σ (lv σ - 1) < spos σ (k - 1)) ∨
         (BD σ ∧ ¬ UD σ ∧ spos σ 2 < spos σ (rv σ + 1) ∧ spos σ (rv σ + 1) < bp σ))) →
      GeomConclusion σ N37)
    (h38 : ∀ σ : Perm (Fin k), Standing44 σ → bp σ + 1 = up σ →
      ¬ (lv σ + 1 = rv σ ∧
        ((LD σ ∧ ¬ RD σ ∧ sval σ 2 < sval σ (up σ + 1) ∧ sval σ (up σ + 1) < lv σ) ∨
         (RD σ ∧ ¬ LD σ ∧ rv σ < sval σ (bp σ - 1) ∧ sval σ (bp σ - 1) < sval σ (k - 1)))) →
      GeomConclusion σ N38)
    {σ : Perm (Fin k)} (hst : Standing44 σ) (hlr : lv σ + 1 = rv σ) :
    GeomConclusion σ M := by
  obtain ⟨hk3, hl2, hlk, hr2, hrk, hb2, hbk, hu2, huk, -⟩ := st_facts hst
  by_cases hex : bp σ + 1 = up σ ∧
      ((UD σ ∧ ¬ BD σ ∧ up σ < spos σ (lv σ - 1) ∧ spos σ (lv σ - 1) < spos σ (k - 1)) ∨
       (BD σ ∧ ¬ UD σ ∧ spos σ 2 < spos σ (rv σ + 1) ∧ spos σ (rv σ + 1) < bp σ))
  · rcases hex.2 with ⟨hud, -, hpos⟩ | ⟨hbd, -, hineq⟩
    · exact lemA M N38 hM0 hM8 h38 hst hex.1 hud hpos
    · -- the reverse-complement symmetry turns (b) into (a)
      have hk1 : 1 ≤ k := by omega
      set τ := compP (revP σ) with hτ
      have hlτ : lv τ = k + 1 - rv σ := by rw [hτ, lv_compP _ hk1, lv_revP]
      have hrτ : rv τ = k + 1 - lv σ := by rw [hτ, rv_compP _ hk1, rv_revP]
      have hbτ : bp τ = k + 1 - up σ := by rw [hτ, bp_compP, up_revP _ hk1]
      have huτ : up τ = k + 1 - bp σ := by rw [hτ, up_compP, bp_revP _ hk1]
      have hsτ : ∀ j, 1 ≤ j → j ≤ k → spos τ j = k + 1 - spos σ (k + 1 - j) :=
        fun j h1 h2 => spos_rc σ h1 h2
      have hpk : ∀ j, spos σ j ≤ k := spos_le σ
      refine of_rc (lemA M N38 hM0 hM8 h38 (standing_compP (standing_revP hst)) ?_ ?_ ?_)
      · rw [hbτ, huτ]; have := hex.1; omega
      · intro j hj1 hj2
        rw [hrτ] at hj1
        have := hbd (k - j) (by omega) (by omega)
        rw [hsτ _ (by omega) (by omega), hsτ _ (by omega) (by omega)]
        have e1 : k + 1 - (j + 1) = k - j := by omega
        have e2 : k + 1 - j = k - j + 1 := by omega
        rw [e1, e2]
        have := hpk (k - j); have := hpk (k - j + 1)
        omega
      · rw [huτ, hlτ, hsτ _ (by omega) (by omega), hsτ _ (by omega) (by omega)]
        have e1 : k + 1 - (k + 1 - rv σ - 1) = rv σ + 1 := by omega
        have e2 : k + 1 - (k - 1) = 2 := by omega
        rw [e1, e2]
        have := hpk 2; have := hpk (rv σ + 1)
        omega
  · exact GeomConclusion.mono (h37 σ hst hlr hex) hM7


/-- Subsection 4.4: Corollaries 4.27, 4.37, 4.38 and the simultaneous exceptional case, after
the symmetries `ℓ = r + 1 ↦ ℓ = r - 1` (reverse) and `b = u + 1 ↦ b = u - 1` (complement). -/
theorem goodSt (M N27 N37 N38 : ℕ) (hM0 : N0 k ≤ M) (hM27 : N27 ≤ M) (hM7 : N37 ≤ M)
    (hM8 : N38 ≤ M)
    (h27 : ∀ σ : Perm (Fin k), Standing44 σ →
      2 ≤ |(lv σ : ℤ) - rv σ| → 2 ≤ |(bp σ : ℤ) - up σ| → GeomConclusion σ N27)
    (h37 : ∀ σ : Perm (Fin k), Standing44 σ → lv σ + 1 = rv σ →
      ¬ (bp σ + 1 = up σ ∧
        ((UD σ ∧ ¬ BD σ ∧ up σ < spos σ (lv σ - 1) ∧ spos σ (lv σ - 1) < spos σ (k - 1)) ∨
         (BD σ ∧ ¬ UD σ ∧ spos σ 2 < spos σ (rv σ + 1) ∧ spos σ (rv σ + 1) < bp σ))) →
      GeomConclusion σ N37)
    (h38 : ∀ σ : Perm (Fin k), Standing44 σ → bp σ + 1 = up σ →
      ¬ (lv σ + 1 = rv σ ∧
        ((LD σ ∧ ¬ RD σ ∧ sval σ 2 < sval σ (up σ + 1) ∧ sval σ (up σ + 1) < lv σ) ∨
         (RD σ ∧ ¬ LD σ ∧ rv σ < sval σ (bp σ - 1) ∧ sval σ (bp σ - 1) < sval σ (k - 1)))) →
      GeomConclusion σ N38)
    {σ : Perm (Fin k)} (hst : Standing44 σ) : GeomConclusion σ M := by
  obtain ⟨hk3, hl2, hlk, hr2, hrk, hb2, hbk, hu2, huk, hlr, hbu⟩ := st_facts hst
  have hk1 : 1 ≤ k := by omega
  by_cases h1 : lv σ + 1 = rv σ
  · exact lemB M N37 N38 hM0 hM7 hM8 h37 h38 hst h1
  by_cases h2 : rv σ + 1 = lv σ
  · exact of_revP (lemB M N37 N38 hM0 hM7 hM8 h37 h38 (standing_revP hst)
      (by rw [lv_revP, rv_revP]; exact h2))
  by_cases h3 : bp σ + 1 = up σ
  · exact GeomConclusion.mono (h38 σ hst h3 fun h => h1 h.1) hM8
  by_cases h4 : up σ + 1 = bp σ
  · refine of_compP (GeomConclusion.mono (h38 (compP σ) (standing_compP hst)
      (by rw [bp_compP, up_compP]; exact h4) fun h => h2 ?_) hM8)
    have := h.1
    rw [lv_compP _ hk1, rv_compP _ hk1] at this
    omega
  · refine GeomConclusion.mono (h27 σ hst ?_ ?_) hM27
    · rw [le_abs]; omega
    · rw [le_abs]; omega

end S4

/-- **Theorem 4.1.** Let `σ ∈ S_k` with `k ≥ 4` or `σ ∈ {(123), (321)}`. There is `N₀(k)` such
that for every `N ≥ N₀(k)` there is an `N`-point set `Π ⊂ ℝ²` associated with a permutation
`π ∈ S_N` such that the canonical point set `Σ = {(i, σ(i))}` of `σ` satisfies `Σ ⊆ Π`, `Σ` is
the unique `σ`-copy in `Π`, and `|Π ∩ H_i| ≥ (N-k)/(2k)` and `|Π ∩ V_i| ≥ (N-k)/(2k)` for every
`i ∈ [k-1]`. (`N₀` depends only on `k`: it is chosen before `σ`.) -/
theorem thm_4_1 (k : ℕ) : ∃ N₀ : ℕ, ∀ σ : Perm (Fin k), ThmHyp σ → GeomConclusion σ N₀ := by
  obtain ⟨N27, h27⟩ := cor_4_27 k
  obtain ⟨N37, h37⟩ := cor_4_37 k
  obtain ⟨N38, h38⟩ := cor_4_38 k
  refine ⟨max (DISC.N0 k) (max N27 (max N37 N38)), fun σ hT => ?_⟩
  have hM0 : DISC.N0 k ≤ max (DISC.N0 k) (max N27 (max N37 N38)) := by omega
  by_cases hTB : IsTwoBlock σ
  · exact DISC.GeomConclusion.mono (S4.goodTB hT hTB) hM0
  by_cases hE : IsExcFive σ
  · exact DISC.GeomConclusion.mono (S4.goodExc hE) hM0
  by_cases hC : lv σ = 1 ∨ lv σ = k ∨ rv σ = 1 ∨ rv σ = k
  · exact DISC.GeomConclusion.mono (S4.goodCoinc hT hTB hE hC) hM0
  · push Not at hC
    exact S4.goodSt _ N27 N37 N38 hM0 (by omega) (by omega) (by omega) h27 h37 h38
      ⟨hTB, hE, ⟨hC.1, hC.2.1⟩, ⟨hC.2.2.1, hC.2.2.2⟩⟩

end LinfPermRemoval
