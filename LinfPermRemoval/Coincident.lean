/-
Formalization of V. H. Le, R. Shi, F. Wei, "$L_\infty$ Permutation Removal Lemma"
(unpublished manuscript). Not part of Mathlib.
-/
import LinfPermRemoval.Geometry

/-!
# Subsection 4.3: patterns with a coincident boundary point

Standing assumption (tex l.920–923): `{σ(1), σ(k)} ∩ {1, k} ≠ ∅`, `σ` not covered by
Subsections 4.1–4.2, and, after a dihedral symmetry, `L = B`, i.e. `σ(1) = 1`. The hypothesis
of Theorem 4.1 (`k ≥ 4` or `σ ∈ {(123), (321)}`) is also in force (it is used at tex l.1008).

The claims inside the proof of Lemma 4.16 are stated for an arbitrary `σ`-copy `Θ ⊆ D`
(the paper's proof is direct, not by contradiction). Claims 4.17 and 4.18 are used inside its
sub-argument by contradiction at tex l.986–988 (Claim 4.17 through the proof of Claim 4.18,
tex l.979), whose case conditions never hold for a copy; so these claims hold only vacuously.
-/

open Equiv Finset

namespace LinfPermRemoval

variable {k : ℕ}

/-- **Construction 4.15**, `I_L`: `(1,2) + t(-1,1)`, `0 ≤ t ≤ k-2`, if `σ(2) ≠ k`;
`(1,3) + t(-1,1)`, `0 ≤ t ≤ k-3`, if `σ(2) = k`. `P_L = I_L ∖ ℤ²`. -/
noncomputable def PL415 (σ : Perm (Fin k)) : Set (ℝ × ℝ) :=
  (if sval σ 2 ≠ k then closedSeg (1, 2) (-1, 1) ((k : ℝ) - 2)
    else closedSeg (1, 3) (-1, 1) ((k : ℝ) - 3)) \ lattice

/-- **Construction 4.15**, `I_U`: `(2,k) + t(-1,1)`, `0 ≤ t ≤ 1`, if `σ(2) ≠ k`;
`(1,2) + t(1,1)`, `0 ≤ t ≤ 1`, if `σ(2) = k`. `P_U = I_U ∖ ℤ²`. -/
noncomputable def PU415 (σ : Perm (Fin k)) : Set (ℝ × ℝ) :=
  (if sval σ 2 ≠ k then closedSeg (2, (k : ℝ)) (-1, 1) 1
    else closedSeg (1, 2) (1, 1) 1) \ lattice

/-- **Construction 4.15**, `I_B`: `(2,1) + t(1,-1)`, `0 ≤ t ≤ k-2`, if `σ(k) ≠ 2`;
`(3,1) + t(1,-1)`, `0 ≤ t ≤ k-3`, if `σ(k) = 2`. `P_B = I_B ∖ ℤ²`. -/
noncomputable def PB415 (σ : Perm (Fin k)) : Set (ℝ × ℝ) :=
  (if sval σ k ≠ 2 then closedSeg (2, 1) (1, -1) ((k : ℝ) - 2)
    else closedSeg (3, 1) (1, -1) ((k : ℝ) - 3)) \ lattice

/-- **Construction 4.15**, `I_R`: `(k,2) + t(1,-1)`, `0 ≤ t ≤ 1`, if `σ(k) ≠ 2`;
`(2,1) + t(1,1)`, `0 ≤ t ≤ 1`, if `σ(k) = 2`. `P_R = I_R ∖ ℤ²`. -/
noncomputable def PR415 (σ : Perm (Fin k)) : Set (ℝ × ℝ) :=
  (if sval σ k ≠ 2 then closedSeg ((k : ℝ), 2) (1, -1) 1
    else closedSeg (2, 1) (1, 1) 1) \ lattice

/-- The support `D = Σ ∪ P_L ∪ P_R ∪ P_B ∪ P_U` of Construction 4.15. -/
noncomputable def D415 (σ : Perm (Fin k)) : Set (ℝ × ℝ) :=
  ↑(canon σ) ∪ PL415 σ ∪ PR415 σ ∪ PB415 σ ∪ PU415 σ

/-- The standing hypotheses of Lemma 4.16: `σ(1) = 1`, `σ` not covered by Subsections 4.1 or
4.2, and the hypothesis of Theorem 4.1. The field `not42` (tex l.922) is not used by the proofs of
Lemma 4.16 and Claims 4.17–4.18 (it even follows from `first`), and `not41` is not used by Claims
4.17–4.18; they are kept to match the paper. -/
structure Hyp416 (σ : Perm (Fin k)) : Prop where
  first : lv σ = 1
  not41 : ¬ IsTwoBlock σ
  not42 : ¬ IsExcFive σ
  thm : ThmHyp σ

namespace CO

/-! ### Auxiliary development for Subsection 4.3 -/

lemma seg_pos {a v p : ℝ × ℝ} {T : ℝ} (hp : p ∈ closedSeg a v T) (ha : a ∈ lattice)
    (hnl : p ∉ lattice) : ∃ t : ℝ, 0 < t ∧ t ≤ T ∧ p = (a.1 + t * v.1, a.2 + t * v.2) := by
  obtain ⟨t, h0, hT, rfl⟩ := hp
  rcases h0.lt_or_eq with h | rfl
  · exact ⟨t, h, hT, rfl⟩
  · exfalso; apply hnl; simpa using ha

lemma seg_pos1 {a v p : ℝ × ℝ} (hp : p ∈ closedSeg a v 1) (ha : a ∈ lattice)
    (hb : (a.1 + v.1, a.2 + v.2) ∈ lattice) (hnl : p ∉ lattice) :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧ p = (a.1 + t * v.1, a.2 + t * v.2) := by
  obtain ⟨t, h0, h1, rfl⟩ := seg_pos hp ha hnl
  rcases h1.lt_or_eq with h | rfl
  · exact ⟨t, h0, h, rfl⟩
  · exfalso; apply hnl; simpa using hb

lemma int_lattice (a b : ℤ) : ((a : ℝ), (b : ℝ)) ∈ lattice := ⟨a, b, rfl⟩

lemma sval_succ (σ : Perm (Fin k)) (i : ℕ) (h : i < k) :
    sval σ (i + 1) = (σ ⟨i, h⟩ : ℕ) + 1 := by
  unfold sval
  split_ifs with hh
  · rfl
  · omega

lemma PL_facts {σ : Perm (Fin k)} {p : ℝ × ℝ} (hp : p ∈ PL415 σ) :
    p.1 < 1 ∧ 2 < p.2 ∧ p.2 ≤ k ∧ (sval σ 2 = k → 3 < p.2) ∧
      p.1 + p.2 = if sval σ 2 ≠ k then 3 else 4 := by
  obtain ⟨hI, hnl⟩ := hp
  split_ifs at hI ⊢ with h
  · obtain ⟨t, ht, hT, rfl⟩ := seg_pos hI (by exact_mod_cast int_lattice 1 2) hnl
    refine ⟨by simp; linarith, by simp; linarith, by simp; linarith, fun h' => absurd h' h,
      by simp; ring⟩
  · obtain ⟨t, ht, hT, rfl⟩ := seg_pos hI (by exact_mod_cast int_lattice 1 3) hnl
    refine ⟨by simp; linarith, by simp; linarith, by simp; linarith, fun _ => by simp; linarith,
      by simp; ring⟩

lemma PU_facts {σ : Perm (Fin k)} {p : ℝ × ℝ} (hp : p ∈ PU415 σ) :
    1 < p.1 ∧ p.1 < 2 ∧ (sval σ 2 ≠ k → (k : ℝ) < p.2 ∧ p.1 + p.2 = k + 2) ∧
      (sval σ 2 = k → 2 < p.2 ∧ p.2 < 3 ∧ p.2 = p.1 + 1) := by
  obtain ⟨hI, hnl⟩ := hp
  split_ifs at hI with h
  · obtain ⟨t, ht, hT, rfl⟩ := seg_pos1 hI (by exact_mod_cast int_lattice 2 k)
      (by norm_num; exact_mod_cast int_lattice 1 (k + 1)) hnl
    refine ⟨by simp; linarith, by simp; linarith, fun _ => ⟨by simp; linarith, by simp; ring⟩,
      fun h' => absurd h' h⟩
  · obtain ⟨t, ht, hT, rfl⟩ := seg_pos1 hI (by exact_mod_cast int_lattice 1 2)
      (by norm_num; exact_mod_cast int_lattice 2 3) hnl
    refine ⟨by simp; linarith, by simp; linarith, fun h' => absurd h' (by simpa using h),
      fun _ => ⟨by simp; linarith, by simp; linarith, by simp; ring⟩⟩

lemma PB_facts {σ : Perm (Fin k)} {p : ℝ × ℝ} (hp : p ∈ PB415 σ) : p.2 < 1 ∧ 2 < p.1 := by
  obtain ⟨hI, hnl⟩ := hp
  split_ifs at hI with h
  · obtain ⟨t, ht, hT, rfl⟩ := seg_pos hI (by exact_mod_cast int_lattice 2 1) hnl
    exact ⟨by simp; linarith, by simp; linarith⟩
  · obtain ⟨t, ht, hT, rfl⟩ := seg_pos hI (by exact_mod_cast int_lattice 3 1) hnl
    exact ⟨by simp; linarith, by simp; linarith⟩

lemma PR_facts {σ : Perm (Fin k)} (hk : 2 ≤ k) {p : ℝ × ℝ} (hp : p ∈ PR415 σ) :
    2 < p.1 ∧ 1 < p.2 ∧ p.2 < 2 ∧ (sval σ k ≠ 2 → (k : ℝ) < p.1 ∧ p.1 + p.2 = k + 2) ∧
      (sval σ k = 2 → p.1 < 3 ∧ p.2 = p.1 - 1) := by
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  obtain ⟨hI, hnl⟩ := hp
  split_ifs at hI with h
  · obtain ⟨t, ht, hT, rfl⟩ := seg_pos1 hI (by exact_mod_cast int_lattice k 2)
      (by norm_num; exact_mod_cast int_lattice (k + 1) 1) hnl
    refine ⟨by simp; linarith, by simp; linarith, by simp; linarith,
      fun _ => ⟨by simp; linarith, by simp; ring⟩, fun h' => absurd h' h⟩
  · obtain ⟨t, ht, hT, rfl⟩ := seg_pos1 hI (by exact_mod_cast int_lattice 2 1)
      (by norm_num; exact_mod_cast int_lattice 3 2) hnl
    refine ⟨by simp; linarith, by simp; linarith, by simp; linarith,
      fun h' => absurd h' (by simpa using h), fun _ => ⟨by simp; linarith, by simp; ring⟩⟩

lemma memD {σ : Perm (Fin k)} {p : ℝ × ℝ} (h : p ∈ D415 σ) :
    (∃ m, p = canonPt σ m) ∨ p ∈ PL415 σ ∨ p ∈ PU415 σ ∨ p ∈ PB415 σ ∨ p ∈ PR415 σ := by
  rcases h with ((((h | h) | h) | h) | h)
  · left
    simp only [canon, Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at h
    obtain ⟨m, rfl⟩ := h
    exact ⟨m, rfl⟩
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inl h))

lemma floor_succ (n : ℕ) : ⌊(n : ℝ) + 1⌋₊ = n + 1 := by
  rw [show (n : ℝ) + 1 = ((n + 1 : ℕ) : ℝ) by push_cast; ring]
  exact Nat.floor_natCast _

section copy

variable {σ : Perm (Fin k)} {Θ : Fin k → ℝ × ℝ}

lemma xlt (hR : Represents σ Θ) {a b : Fin k} (h : a.val < b.val) : (Θ a).1 < (Θ b).1 :=
  hR.1 h

lemma xle (hR : Represents σ Θ) {a b : Fin k} (h : a.val ≤ b.val) : (Θ a).1 ≤ (Θ b).1 :=
  hR.1.monotone h

lemma ylt (hR : Represents σ Θ) {a b : Fin k} (h : (σ a : ℕ) < σ b) : (Θ a).2 < (Θ b).2 :=
  (hR.2 a b).2 h

lemma sig_lt_of_y (hR : Represents σ Θ) {a b : Fin k} (h : (Θ a).2 < (Θ b).2) :
    (σ a : ℕ) < σ b :=
  (hR.2 a b).1 h

lemma y_inj (hR : Represents σ Θ) {a b : Fin k} (h : (Θ a).2 = (Θ b).2) : a = b := by
  by_contra hne
  have h1 : σ a ≠ σ b := fun e => hne (σ.injective e)
  rcases lt_or_gt_of_ne (Fin.val_injective.ne h1) with h' | h'
  · have := ylt hR h'; linarith
  · have := ylt hR h'; linarith

lemma y0_lt (hR : Represents σ Θ) (h0 : ∀ j : Fin k, j.val = 0 → (σ j : ℕ) = 0)
    {a b : Fin k} (ha : a.val = 0) (hb : b.val ≠ 0) : (Θ a).2 < (Θ b).2 := by
  apply ylt hR
  rw [h0 a ha]
  have h1 : σ b ≠ σ a := fun e => hb (by rw [σ.injective e]; exact ha)
  have h2 : (σ b : ℕ) ≠ 0 := by
    intro e; apply h1; ext; rw [e, h0 a ha]
  omega

lemma lt_top {a b : Fin k} (htop : (σ a : ℕ) + 1 = k) (hb : b ≠ a) : (σ b : ℕ) < σ a := by
  have h1 := (σ b).isLt
  have h2 : (σ b : ℕ) ≠ σ a := Fin.val_injective.ne fun e => hb (σ.injective e)
  omega

lemma canon_x (m : Fin k) : (canonPt σ m).1 = (m.val : ℝ) + 1 := rfl
lemma canon_y (m : Fin k) : (canonPt σ m).2 = ((σ m : ℕ) : ℝ) + 1 := rfl

lemma x_lt_one_PL (hk : 2 ≤ k) {p : ℝ × ℝ} (hp : p ∈ D415 σ) (hx : p.1 < 1) :
    p ∈ PL415 σ := by
  rcases memD hp with ⟨m, rfl⟩ | h | h | h | h
  · rw [canon_x] at hx
    have : (0 : ℝ) ≤ (m.val : ℝ) := Nat.cast_nonneg _
    linarith
  · exact h
  · linarith [(PU_facts h).1]
  · linarith [(PB_facts h).2]
  · linarith [(PR_facts hk h).1]

lemma notPU_le_k (hk : 2 ≤ k) {p : ℝ × ℝ} (hp : p ∈ D415 σ) (hU : p ∉ PU415 σ) :
    p.2 ≤ k := by
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  rcases memD hp with ⟨m, rfl⟩ | h | h | h | h
  · rw [canon_y]
    have : (σ m : ℕ) + 1 ≤ k := (σ m).isLt
    exact_mod_cast this
  · exact (PL_facts h).2.2.1
  · exact absurd h hU
  · linarith [(PB_facts h).1]
  · linarith [(PR_facts hk h).2.2.1]

/-- A copy meeting `P_L` meets it only at `Θ(1)`. A step inside the sub-argument by contradiction of
Lemma 4.16's proof "First suppose `Θ ∩ P_L ≠ ∅` … a contradiction" (tex l.986–988): its hypotheses
can never all hold, since `CO.noPL` shows that a copy never meets `P_L`. Used inside `CO.c418LU`,
`CO.noPL` and the proof of `claim_4_17`. -/
lemma PL_only0 (h0 : ∀ j : Fin k, j.val = 0 → (σ j : ℕ) = 0)
    (hΘ : CopyIn σ Θ (D415 σ)) {i : Fin k} (hi : Θ i ∈ PL415 σ) : i.val = 0 := by
  by_contra hne
  have hx := xlt hΘ.1 (a := ⟨0, by omega⟩) (b := i) (by show 0 < i.val; omega)
  have hzL : Θ ⟨0, by omega⟩ ∈ PL415 σ :=
    x_lt_one_PL (by omega) (hΘ.2 _) (by linarith [(PL_facts hi).1])
  have hy := y0_lt hΘ.1 h0 (a := ⟨0, by omega⟩) (b := i) rfl hne
  have h1 := (PL_facts hi).2.2.2.2
  have h2 := (PL_facts hzL).2.2.2.2
  rw [← h2] at h1
  linarith

/-- If `σ(2) ≠ k`, a copy cannot have `Θ(2) ∈ P_U` (it would be the maximum point of `Θ`). A step
inside the sub-argument by contradiction of Lemma 4.16's proof for `Θ ∩ P_U ≠ ∅` (tex l.990–1009,
the case `σ(2) ≠ k` at l.998): its conclusion is `False`, so its hypotheses can never all hold (it
refutes them itself). Used inside `CO.c418LU` and `CO.noPU`. -/
lemma maxAt1 (hk : 2 ≤ k) (h0 : ∀ j : Fin k, j.val = 0 → (σ j : ℕ) = 0)
    (hΘ : CopyIn σ Θ (D415 σ)) (hne : sval σ 2 ≠ k) (h1 : Θ ⟨1, by omega⟩ ∈ PU415 σ) :
    False := by
  have hall : ∀ j, (σ j : ℕ) ≤ σ ⟨1, by omega⟩ := by
    intro j
    by_cases hj : j.val = 1
    · rw [show j = ⟨1, by omega⟩ from Fin.ext hj]
    by_cases hj0 : j.val = 0
    · rw [h0 j hj0]; omega
    have hx := xlt hΘ.1 (a := ⟨1, by omega⟩) (b := j) (by show 1 < j.val; omega)
    have hU1 := (PU_facts h1).2.2.1 hne
    by_cases hjU : Θ j ∈ PU415 σ
    · have hU2 := (PU_facts hjU).2.2.1 hne
      exact (sig_lt_of_y hΘ.1 (by linarith)).le
    · have := notPU_le_k hk (hΘ.2 j) hjU
      exact (sig_lt_of_y hΘ.1 (by linarith)).le
  have h2 := hall (σ.symm ⟨k - 1, by omega⟩)
  simp only [Equiv.apply_symm_apply] at h2
  apply hne
  rw [show (2 : ℕ) = 1 + 1 from rfl, sval_succ σ 1 (by omega)]
  have := (σ ⟨1, by omega⟩).isLt
  omega

/-- Claim 4.18, L/U half. -/
lemma c418LU (hk : 2 ≤ k) (h0 : ∀ j : Fin k, j.val = 0 → (σ j : ℕ) = 0)
    (hΘ : CopyIn σ Θ (D415 σ)) :
    ¬ ((∃ i, Θ i ∈ PL415 σ) ∧ (∃ i, Θ i ∈ PU415 σ)) := by
  rintro ⟨⟨i, hi⟩, ⟨i', hi'⟩⟩
  have hiz : i = ⟨0, by omega⟩ := Fin.ext (PL_only0 h0 hΘ hi)
  rw [hiz] at hi
  have hi'0 : i'.val ≠ 0 := by
    intro e
    rw [show i' = ⟨0, by omega⟩ from Fin.ext e] at hi'
    linarith [(PL_facts hi).1, (PU_facts hi').1]
  have hxo : (Θ ⟨1, by omega⟩).1 < 2 :=
    lt_of_le_of_lt (xle hΘ.1 (show 1 ≤ i'.val by omega)) (PU_facts hi').2.1
  have hyo := y0_lt hΘ.1 h0 (a := ⟨0, by omega⟩) (b := ⟨1, by omega⟩) rfl (by simp)
  have hzy := (PL_facts hi).2.1
  rcases memD (hΘ.2 ⟨1, by omega⟩) with ⟨m, hm⟩ | h | h | h | h
  · rw [hm, canon_x] at hxo
    rw [hm, canon_y] at hyo
    have hm1 : (m.val : ℝ) < 1 := by linarith
    have hm0 : m.val = 0 := by
      have : m.val < 1 := by exact_mod_cast hm1
      omega
    rw [h0 m hm0] at hyo
    simp at hyo
    linarith
  · exact absurd (PL_only0 h0 hΘ h) (by simp)
  · by_cases hc : sval σ 2 = k
    · linarith [(PL_facts hi).2.2.2.1 hc, ((PU_facts h).2.2.2 hc).2.1]
    · exact maxAt1 hk h0 hΘ hc h
  · linarith [(PB_facts h).2]
  · linarith [(PR_facts hk h).1]

lemma pigeon (hR : Represents σ Θ) (S : Finset (Fin k))
    (hS : ∀ j ∈ S, (∃ m, Θ j = canonPt σ m) ∧ 2 < (Θ j).2) : S.card ≤ k - 2 := by
  have hc := Finset.card_le_card_of_injOn (fun j => ⌊(Θ j).2⌋₊) (s := S) (t := Finset.Icc 3 k) ?_ ?_
  · simpa using hc
  · intro j hj
    obtain ⟨⟨m, hm⟩, hy⟩ := hS j (Finset.mem_coe.1 hj)
    rw [hm, canon_y] at hy
    simp only [hm, canon_y, floor_succ, Finset.coe_Icc, Set.mem_Icc]
    have h3 : (2 : ℝ) < ((σ m : ℕ) + 1 : ℕ) := by push_cast; linarith
    have h4 : 2 < (σ m : ℕ) + 1 := by exact_mod_cast h3
    have := (σ m).isLt
    omega
  · intro a ha b hb hab
    obtain ⟨⟨m, hm⟩, -⟩ := hS a (Finset.mem_coe.1 ha)
    obtain ⟨⟨m', hm'⟩, -⟩ := hS b (Finset.mem_coe.1 hb)
    apply y_inj hR
    simp only [hm, hm', canon_y, floor_succ] at hab ⊢
    have : (σ m : ℕ) = σ m' := by omega
    rw [this]

/-- Lemma 4.16, `P_L` part: a copy avoids `P_L`. -/
lemma noPL (hk : 2 ≤ k) (h0 : ∀ j : Fin k, j.val = 0 → (σ j : ℕ) = 0)
    (hΘ : CopyIn σ Θ (D415 σ)) (i : Fin k) : Θ i ∉ PL415 σ := by
  intro hi
  have hiz : i = ⟨0, by omega⟩ := Fin.ext (PL_only0 h0 hΘ hi)
  rw [hiz] at hi
  have hzy := (PL_facts hi).2.1
  have hc := pigeon hΘ.1 (Finset.univ.erase ⟨0, by omega⟩) ?_
  · rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin] at hc
    omega
  intro j hj
  have hj0 : j.val ≠ 0 := fun e => (Finset.mem_erase.1 hj).1 (Fin.ext e)
  have hy := y0_lt hΘ.1 h0 (a := ⟨0, by omega⟩) (b := j) rfl hj0
  refine ⟨?_, by linarith⟩
  rcases memD (hΘ.2 j) with ⟨m, hm⟩ | h | h | h | h
  · exact ⟨m, hm⟩
  · exact absurd (PL_only0 h0 hΘ h) hj0
  · exact absurd ⟨⟨_, hi⟩, ⟨_, h⟩⟩ (c418LU hk h0 hΘ)
  · linarith [(PB_facts h).1]
  · linarith [(PR_facts hk h).2.2.1]

end copy

section rho

variable {σ : Perm (Fin k)}

/-- From `σ(1) = 1`, `σ(2) = k` and `σ` decreasing on positions `3, …, k`, `σ` is the pattern
`ρ = (1 k (k-1) ⋯ 2)` (0-based: `σ j + j = k` for `j ≥ 1`). -/
lemma rho_of_anti (hk : 2 ≤ k) (h0 : ∀ j : Fin k, j.val = 0 → (σ j : ℕ) = 0)
    (htop : (σ ⟨1, by omega⟩ : ℕ) + 1 = k)
    (hanti : ∀ a b : Fin k, 2 ≤ a.val → a.val < b.val → (σ b : ℕ) < σ a) :
    ∀ j : Fin k, 1 ≤ j.val → (σ j : ℕ) + j.val = k := by
  have hstep : ∀ n (h : n + 1 < k), 1 ≤ n → (σ ⟨n + 1, h⟩ : ℕ) < σ ⟨n, by omega⟩ := by
    intro n h hn
    rcases Nat.eq_or_lt_of_le hn with e | hlt
    · subst e
      exact lt_top htop (by simp [Fin.ext_iff])
    · exact hanti _ _ (by simp; omega) (by simp)
  have hup : ∀ n (h : n < k), 1 ≤ n → (σ ⟨n, h⟩ : ℕ) + n ≤ k := by
    intro n
    induction n with
    | zero => intro h hn; omega
    | succ n ih =>
      intro h hn
      rcases Nat.eq_zero_or_pos n with rfl | hpos
      · simp only [zero_add] at htop ⊢; omega
      · have h1 := ih (by omega) hpos
        have h2 := hstep n h hpos
        omega
  have hlow : ∀ d n (h : n < k), n + d = k - 1 → 1 ≤ n → k ≤ (σ ⟨n, h⟩ : ℕ) + n := by
    intro d
    induction d with
    | zero =>
      intro n h hd hn
      have : (σ ⟨n, h⟩ : ℕ) ≠ 0 := by
        intro e
        have := σ.injective (Fin.ext (e.trans (h0 ⟨0, by omega⟩ rfl).symm))
        simp [Fin.ext_iff] at this
        omega
      omega
    | succ d ih =>
      intro n h hd hn
      have h1 := ih (n + 1) (by omega) (by omega) (by omega)
      have h2 := hstep n (by omega) hn
      omega
  intro j hj
  have h1 := hup j.val j.isLt hj
  have h2 := hlow (k - 1 - j.val) j.val j.isLt (by omega) hj
  simp only [Fin.eta] at h1 h2
  omega

lemma rho_of_rho_symm (h0 : ∀ j : Fin k, j.val = 0 → (σ j : ℕ) = 0)
    (hρ : ∀ j : Fin k, 1 ≤ j.val → (σ.symm j : ℕ) + j.val = k) :
    ∀ j : Fin k, 1 ≤ j.val → (σ j : ℕ) + j.val = k := by
  intro j hj
  have hm : (σ j).val ≠ 0 := by
    intro e
    have := σ.injective (Fin.ext (e.trans (h0 ⟨0, by omega⟩ rfl).symm))
    rw [this] at hj
    simp at hj
  have := hρ (σ j) (by omega)
  rw [Equiv.symm_apply_apply] at this
  omega

lemma twoBlockA_of_rho (hk : 2 ≤ k) (h0 : ∀ j : Fin k, j.val = 0 → (σ j : ℕ) = 0)
    (hρ : ∀ j : Fin k, 1 ≤ j.val → (σ j : ℕ) + j.val = k) : IsTwoBlockA σ 1 := by
  refine ⟨le_rfl, by omega, ?_⟩
  intro i h1 h2
  obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by omega⟩
  rw [sval_succ σ n (by omega)]
  split_ifs with h
  · have : n = 0 := by omega
    subst this
    rw [h0 _ rfl]
  · have := hρ ⟨n, by omega⟩ (by simp; omega)
    simp only at this
    omega

end rho

section copy2

variable {σ : Perm (Fin k)} {Θ : Fin k → ℝ × ℝ}

/-- Lemma 4.16, `P_U` part: if `k ≥ 3`, `σ(1) = 1` and `σ ≠ ρ`, a copy avoids `P_U`. (That the
copy avoids `P_L` is not assumed: it is derived inside the proof from `noPL`.) -/
lemma noPU (hk : 3 ≤ k) (h0 : ∀ j : Fin k, j.val = 0 → (σ j : ℕ) = 0)
    (hρ : ¬ ∀ j : Fin k, 1 ≤ j.val → (σ j : ℕ) + j.val = k)
    (hΘ : CopyIn σ Θ (D415 σ)) (i : Fin k) : Θ i ∉ PU415 σ := by
  intro hi
  have hk2 : 2 ≤ k := by omega
  have hnoPL := noPL hk2 h0 hΘ
  have hR := hΘ.1
  have hxi := (PU_facts hi).2.1
  -- Step 1: `Θ(1) = Σ(1)`.
  have hU1 : Θ ⟨0, by omega⟩ = canonPt σ ⟨0, by omega⟩ := by
    have hxz : (Θ ⟨0, by omega⟩).1 ≤ (Θ i).1 := xle hR (show 0 ≤ i.val by omega)
    rcases memD (hΘ.2 ⟨0, by omega⟩) with ⟨m, hm⟩ | h | h | h | h
    · have : m.val = 0 := by
        rw [hm, canon_x] at hxz
        have : (m.val : ℝ) < 1 := by linarith
        have : m.val < 1 := by exact_mod_cast this
        omega
      rw [hm, show m = ⟨0, by omega⟩ from Fin.ext this]
    · exact absurd h (hnoPL _)
    · exfalso
      have hyo := y0_lt hR h0 (a := ⟨0, by omega⟩) (b := ⟨1, by omega⟩) rfl (by simp)
      have hxo := xlt hR (a := ⟨0, by omega⟩) (b := ⟨1, by omega⟩) (by simp)
      by_cases hc : sval σ 2 = k
      · have htop : (σ ⟨1, by omega⟩ : ℕ) + 1 = k := by
          have : sval σ 2 = (σ ⟨1, by omega⟩ : ℕ) + 1 := sval_succ σ 1 (by omega)
          omega
        have hzy := ((PU_facts h).2.2.2 hc).1
        rcases memD (hΘ.2 ⟨1, by omega⟩) with ⟨m, hm⟩ | h1 | h1 | h1 | h1
        · have hm1 : 1 ≤ m.val := by
            rw [hm, canon_x] at hxo
            by_contra hcon
            have : m.val = 0 := by omega
            rw [this] at hxo
            simp at hxo
            linarith [(PU_facts h).1]
          have hc' := pigeon hR (Finset.univ.erase ⟨0, by omega⟩) ?_
          · rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
              Fintype.card_fin] at hc'
            omega
          intro j hj
          have hj0 : j.val ≠ 0 := fun e => (Finset.mem_erase.1 hj).1 (Fin.ext e)
          have hy := y0_lt hR h0 (a := ⟨0, by omega⟩) (b := j) rfl hj0
          have hxj : (Θ ⟨1, by omega⟩).1 ≤ (Θ j).1 := xle hR (show 1 ≤ j.val by omega)
          have hx2 : (2 : ℝ) ≤ (Θ ⟨1, by omega⟩).1 := by
            rw [hm, canon_x]
            have : (1 : ℝ) ≤ m.val := by exact_mod_cast hm1
            linarith
          refine ⟨?_, by linarith⟩
          rcases memD (hΘ.2 j) with ⟨m', hm'⟩ | h2 | h2 | h2 | h2
          · exact ⟨m', hm'⟩
          · exact absurd h2 (hnoPL _)
          · linarith [(PU_facts h2).2.1]
          · linarith [(PB_facts h2).1]
          · linarith [(PR_facts hk2 h2).2.2.1]
        · exact absurd h1 (hnoPL _)
        · have hw2 := y0_lt hR h0 (a := ⟨0, by omega⟩) (b := ⟨2, by omega⟩) rfl (by simp)
          have hw1 := ylt hR (lt_top (a := ⟨1, by omega⟩) (b := ⟨2, by omega⟩) htop
            (by simp [Fin.ext_iff]))
          have hxw := xlt hR (a := ⟨1, by omega⟩) (b := ⟨2, by omega⟩) (by simp)
          have hy1 := ((PU_facts h1).2.2.2 hc).2.1
          rcases memD (hΘ.2 ⟨2, by omega⟩) with ⟨m, hm⟩ | h2 | h2 | h2 | h2
          · rw [hm, canon_y] at hw2 hw1
            have a1 : (2 : ℝ) < ((σ m : ℕ) + 1 : ℕ) := by push_cast; linarith
            have a2 : (((σ m : ℕ) + 1 : ℕ) : ℝ) < 3 := by push_cast; linarith
            have b1 : 2 < (σ m : ℕ) + 1 := by exact_mod_cast a1
            have b2 : (σ m : ℕ) + 1 < 3 := by exact_mod_cast a2
            omega
          · exact absurd h2 (hnoPL _)
          · have e1 := ((PU_facts h1).2.2.2 hc).2.2
            have e2 := ((PU_facts h2).2.2.2 hc).2.2
            linarith
          · linarith [(PB_facts h2).1]
          · linarith [(PR_facts hk2 h2).2.2.1]
        · linarith [(PB_facts h1).1]
        · linarith [(PR_facts hk2 h1).2.2.1]
      · have hzy := (PU_facts h).2.2.1 hc
        by_cases h1 : Θ ⟨1, by omega⟩ ∈ PU415 σ
        · have := (PU_facts h1).2.2.1 hc
          linarith
        · have := notPU_le_k hk2 (hΘ.2 _) h1
          linarith
    · linarith [(PB_facts h).2]
    · linarith [(PR_facts hk2 h).1]
  have hxz1 : (Θ ⟨0, by omega⟩).1 = 1 := by rw [hU1, canon_x]; simp
  have hi0 : i.val ≠ 0 := by
    intro e
    have := (PU_facts hi).1
    rw [show i = ⟨0, by omega⟩ from Fin.ext e, hxz1] at this
    exact lt_irrefl _ this
  -- Step 2: `Θ(2) ∈ P_U`.
  have hO : Θ ⟨1, by omega⟩ ∈ PU415 σ := by
    have hxo := xlt hR (a := ⟨0, by omega⟩) (b := ⟨1, by omega⟩) (by simp)
    have hxo2 : (Θ ⟨1, by omega⟩).1 < 2 :=
      lt_of_le_of_lt (xle hR (show 1 ≤ i.val by omega)) hxi
    rcases memD (hΘ.2 ⟨1, by omega⟩) with ⟨m, hm⟩ | h | h | h | h
    · exfalso
      rw [hm, canon_x] at hxo hxo2
      rw [hxz1] at hxo
      have a1 : (0 : ℝ) < m.val := by linarith
      have a2 : (m.val : ℝ) < 1 := by linarith
      have : 0 < m.val := by exact_mod_cast a1
      have : m.val < 1 := by exact_mod_cast a2
      omega
    · exact absurd h (hnoPL _)
    · exact h
    · linarith [(PB_facts h).2]
    · linarith [(PR_facts hk2 h).1]
  by_cases hc : sval σ 2 = k
  swap
  · exact maxAt1 hk2 h0 hΘ hc hO
  have htop : (σ ⟨1, by omega⟩ : ℕ) + 1 = k := by
    have : sval σ 2 = (σ ⟨1, by omega⟩ : ℕ) + 1 := sval_succ σ 1 (by omega)
    omega
  have hy1 := (PU_facts hO).2.2.2 hc
  -- Step 3: the tail `Θ(3), …, Θ(k)` lies in `P_R ∪ {Σ⁻¹(2)}`.
  have htail : ∀ j : Fin k, 2 ≤ j.val →
      (∃ m, Θ j = canonPt σ m ∧ (σ m : ℕ) = 1) ∨ Θ j ∈ PR415 σ := by
    intro j hj
    have hyj0 : 1 < (Θ j).2 := by
      have := y0_lt hR h0 (a := ⟨0, by omega⟩) (b := j) rfl (by omega)
      rw [hU1, canon_y, h0 _ rfl] at this
      simpa using this
    have hyj1 : (Θ j).2 < (Θ ⟨1, by omega⟩).2 :=
      ylt hR (lt_top htop (fun e => by rw [e] at hj; simp at hj))
    have hxj := xlt hR (a := ⟨1, by omega⟩) (b := j) (show 1 < j.val by omega)
    rcases memD (hΘ.2 j) with ⟨m, hm⟩ | h | h | h | h
    · left
      refine ⟨m, hm, ?_⟩
      rw [hm, canon_y] at hyj0 hyj1
      have a1 : (1 : ℝ) < ((σ m : ℕ) + 1 : ℕ) := by push_cast; linarith
      have a2 : (((σ m : ℕ) + 1 : ℕ) : ℝ) < 3 := by push_cast; linarith
      have : 1 < (σ m : ℕ) + 1 := by exact_mod_cast a1
      have : (σ m : ℕ) + 1 < 3 := by exact_mod_cast a2
      omega
    · exact absurd h (hnoPL _)
    · exfalso
      have := ((PU_facts h).2.2.2 hc).2.2
      linarith [hy1.2.2]
    · linarith [(PB_facts h).1]
    · exact Or.inr h
  apply hρ
  by_cases hr : sval σ k = 2
  · have hlast : (σ ⟨k - 1, by omega⟩ : ℕ) = 1 := by
      have := sval_succ σ (k - 1) (by omega)
      rw [show k - 1 + 1 = k by omega, hr] at this
      omega
    rcases Nat.eq_or_lt_of_le hk with e | hk4
    · -- `k = 3`: `σ = (132) = ρ`
      intro j hj
      rcases (show j.val = 1 ∨ j.val = k - 1 by omega) with e1 | e2
      · rw [show j = ⟨1, by omega⟩ from Fin.ext e1]
        simp only
        omega
      · rw [show j = ⟨k - 1, by omega⟩ from Fin.ext e2]
        simp only
        omega
    · exfalso
      have hab := xlt hR (a := ⟨k - 2, by omega⟩) (b := ⟨k - 1, by omega⟩) (by simp; omega)
      have hσab : (σ ⟨k - 1, by omega⟩ : ℕ) < σ ⟨k - 2, by omega⟩ := by
        rw [hlast]
        have n1 : (σ ⟨k - 2, by omega⟩ : ℕ) ≠ σ ⟨k - 1, by omega⟩ := fun e => by
          have := σ.injective (Fin.ext e)
          simp [Fin.ext_iff] at this
          omega
        have n0 : (σ ⟨k - 2, by omega⟩ : ℕ) ≠ σ ⟨0, by omega⟩ := fun e => by
          have := σ.injective (Fin.ext e)
          simp [Fin.ext_iff] at this
          omega
        rw [hlast] at n1
        rw [h0 ⟨0, by omega⟩ rfl] at n0
        omega
      have hy := ylt hR hσab
      rcases htail ⟨k - 2, by omega⟩ (by simp; omega) with ⟨m, hm, hm1⟩ | ha
      · rcases htail ⟨k - 1, by omega⟩ (by simp; omega) with ⟨m', hm', hm1'⟩ | hb
        · have : (Θ ⟨k - 2, by omega⟩).2 = (Θ ⟨k - 1, by omega⟩).2 := by
            rw [hm, hm', canon_y, canon_y, hm1, hm1']
          have := y_inj hR this
          simp [Fin.ext_iff] at this
          omega
        · have hmk : m = ⟨k - 1, by omega⟩ := σ.injective (Fin.ext (by rw [hm1, hlast]))
          rw [hm, canon_x, hmk] at hab
          have : (3 : ℝ) ≤ ((k - 1 : ℕ) : ℝ) := by exact_mod_cast (show 3 ≤ k - 1 by omega)
          simp only at hab
          linarith [((PR_facts hk2 hb).2.2.2.2 hr).1]
      · rcases htail ⟨k - 1, by omega⟩ (by simp; omega) with ⟨m', hm', hm1'⟩ | hb
        · have : (Θ ⟨k - 1, by omega⟩).2 = 2 := by
            rw [hm', canon_y, hm1']
            norm_num
          linarith [(PR_facts hk2 ha).2.2.1]
        · have e1 := ((PR_facts hk2 ha).2.2.2.2 hr).2
          have e2 := ((PR_facts hk2 hb).2.2.2.2 hr).2
          linarith
  · have hlast : (σ ⟨k - 1, by omega⟩ : ℕ) ≠ 1 := by
      intro e
      apply hr
      have := sval_succ σ (k - 1) (by omega)
      rw [show k - 1 + 1 = k by omega] at this
      rw [this, e]
    apply rho_of_anti hk2 h0 htop
    intro a b ha hab
    have hxab := xlt hR hab
    rcases htail a ha with ⟨m, hm, hm1⟩ | hPa
    · rcases htail b (by omega) with ⟨m', hm', hm1'⟩ | hPb
      · exfalso
        have : (Θ a).2 = (Θ b).2 := by rw [hm, hm', canon_y, canon_y, hm1, hm1']
        have := y_inj hR this
        rw [this] at hab
        omega
      · apply sig_lt_of_y hR
        have : (Θ a).2 = 2 := by
          rw [hm, canon_y, hm1]
          norm_num
        linarith [(PR_facts hk2 hPb).2.2.1]
    · rcases htail b (by omega) with ⟨m', hm', hm1'⟩ | hPb
      · exfalso
        have hm'k : m'.val ≠ k - 1 := by
          intro e
          apply hlast
          have : σ ⟨k - 1, by omega⟩ = σ m' := congrArg σ (Fin.ext e.symm)
          rw [this]
          exact hm1'
        have h1 : m'.val + 2 ≤ k := by have := m'.isLt; omega
        have h2 : (m'.val : ℝ) + 2 ≤ k := by exact_mod_cast h1
        rw [hm', canon_x] at hxab
        have := ((PR_facts hk2 hPa).2.2.2.1 hr).1
        linarith
      · apply sig_lt_of_y hR
        have e1 := ((PR_facts hk2 hPa).2.2.2.1 hr).2
        have e2 := ((PR_facts hk2 hPb).2.2.2.1 hr).2
        linarith

end copy2

/-! ### Reflection across the line `y = x` -/

lemma swap_lattice (p : ℝ × ℝ) : p.swap ∈ lattice ↔ p ∈ lattice := by
  constructor
  · rintro ⟨a, b, h⟩
    refine ⟨b, a, ?_⟩
    rw [← Prod.swap_swap p, h]
    rfl
  · rintro ⟨a, b, h⟩
    exact ⟨b, a, by rw [h]; rfl⟩

lemma swap_seg {a1 a2 v1 v2 T : ℝ} {p : ℝ × ℝ} :
    p.swap ∈ closedSeg (a2, a1) (v2, v1) T ↔ p ∈ closedSeg (a1, a2) (v1, v2) T := by
  simp only [closedSeg, Set.mem_ofPred_eq, Prod.ext_iff, Prod.fst_swap, Prod.snd_swap]
  constructor <;> rintro ⟨t, h1, h2, h3, h4⟩ <;> exact ⟨t, h1, h2, h4, h3⟩

section refl

variable {σ : Perm (Fin k)}

lemma sval_symm (hk : 2 ≤ k) : sval σ.symm 2 = k ↔ sval σ k = 2 := by
  have e1 : sval σ.symm 2 = (σ.symm ⟨1, by omega⟩ : ℕ) + 1 := sval_succ σ.symm 1 (by omega)
  have e2 : sval σ k = (σ ⟨k - 1, by omega⟩ : ℕ) + 1 := by
    have := sval_succ σ (k - 1) (by omega)
    rwa [show k - 1 + 1 = k by omega] at this
  rw [e1, e2]
  constructor
  · intro h
    have : σ.symm ⟨1, by omega⟩ = ⟨k - 1, by omega⟩ := Fin.ext (by simp only; omega)
    rw [← this, Equiv.apply_symm_apply]
  · intro h
    have : σ ⟨k - 1, by omega⟩ = ⟨1, by omega⟩ := Fin.ext (by simp only; omega)
    rw [← this, Equiv.symm_apply_apply]
    show k - 1 + 1 = k
    omega

lemma swap_PL (hk : 2 ≤ k) {p : ℝ × ℝ} : p.swap ∈ PL415 σ.symm ↔ p ∈ PB415 σ := by
  have hs := sval_symm (σ := σ) hk
  simp only [PL415, PB415, Set.mem_sdiff, swap_lattice]
  split_ifs with h1 h2 h2
  · rw [swap_seg]
  · exact absurd (hs.2 (not_not.1 h2)) h1
  · exact absurd (hs.1 (not_not.1 h1)) h2
  · rw [swap_seg]

lemma swap_PU (hk : 2 ≤ k) {p : ℝ × ℝ} : p.swap ∈ PU415 σ.symm ↔ p ∈ PR415 σ := by
  have hs := sval_symm (σ := σ) hk
  simp only [PU415, PR415, Set.mem_sdiff, swap_lattice]
  split_ifs with h1 h2 h2
  · rw [swap_seg]
  · exact absurd (hs.2 (not_not.1 h2)) h1
  · exact absurd (hs.1 (not_not.1 h1)) h2
  · rw [swap_seg]

lemma swap_canon {p : ℝ × ℝ} (h : p ∈ (↑(canon σ) : Set (ℝ × ℝ))) :
    p.swap ∈ (↑(canon σ.symm) : Set (ℝ × ℝ)) := by
  simp only [canon, Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at h ⊢
  obtain ⟨m, rfl⟩ := h
  exact ⟨σ m, by simp [canonPt]⟩

lemma swap_D (hk : 2 ≤ k) {p : ℝ × ℝ} (h : p ∈ D415 σ) : p.swap ∈ D415 σ.symm := by
  rcases h with ((((h | h) | h) | h) | h)
  · exact Or.inl (Or.inl (Or.inl (Or.inl (swap_canon h))))
  · refine Or.inl (Or.inr ((swap_PL (σ := σ.symm) hk).1 ?_))
    rw [Prod.swap_swap, Equiv.symm_symm]
    exact h
  · exact Or.inr ((swap_PU hk).2 h)
  · exact Or.inl (Or.inl (Or.inl (Or.inr ((swap_PL hk).2 h))))
  · refine Or.inl (Or.inl (Or.inr ((swap_PU (σ := σ.symm) hk).1 ?_)))
    rw [Prod.swap_swap, Equiv.symm_symm]
    exact h

/-- The reflection of a copy `Θ` of `σ` across `y = x`: a copy of `σ⁻¹`. -/
def reflCopy (σ : Perm (Fin k)) (Θ : Fin k → ℝ × ℝ) : Fin k → ℝ × ℝ :=
  fun j => (Θ (σ.symm j)).swap

lemma reflCopy_copy (hk : 2 ≤ k) {Θ : Fin k → ℝ × ℝ} (hΘ : CopyIn σ Θ (D415 σ)) :
    CopyIn σ.symm (reflCopy σ Θ) (D415 σ.symm) := by
  refine ⟨⟨?_, ?_⟩, fun j => swap_D hk (hΘ.2 _)⟩
  · intro a b hab
    simp only [reflCopy, Prod.fst_swap]
    apply ylt hΘ.1
    simp only [Equiv.apply_symm_apply]
    exact hab
  · intro a b
    simp only [reflCopy, Prod.snd_swap]
    exact hΘ.1.1.lt_iff_lt

lemma reflCopy_apply (Θ : Fin k → ℝ × ℝ) (i : Fin k) :
    reflCopy σ Θ (σ i) = (Θ i).swap := by
  simp [reflCopy]

lemma h0_symm (h0 : ∀ j : Fin k, j.val = 0 → (σ j : ℕ) = 0) :
    ∀ j : Fin k, j.val = 0 → (σ.symm j : ℕ) = 0 := by
  intro j hj
  have : σ j = j := Fin.ext (by rw [h0 j hj, hj])
  have h2 : σ.symm j = j := by rw [Equiv.symm_apply_eq]; exact this.symm
  rw [h2, hj]

/-- The standing hypotheses give `k ≥ 3`, `σ(1) = 1` and `σ ≠ ρ`. -/
lemma hyp_facts (hσ : Hyp416 σ) :
    3 ≤ k ∧ (∀ j : Fin k, j.val = 0 → (σ j : ℕ) = 0) ∧
      ¬ ∀ j : Fin k, 1 ≤ j.val → (σ j : ℕ) + j.val = k := by
  have hk : 3 ≤ k := by
    rcases hσ.thm with h | h | h
    · omega
    · have := congrArg List.length h
      simp [oneLine] at this
      omega
    · have := congrArg List.length h
      simp [oneLine] at this
      omega
  have h0 : ∀ j : Fin k, j.val = 0 → (σ j : ℕ) = 0 := by
    intro j hj
    have h1 : sval σ 1 = (σ ⟨0, by omega⟩ : ℕ) + 1 := sval_succ σ 0 (by omega)
    have h2 : lv σ = sval σ 1 := rfl
    have h3 := hσ.first
    rw [show j = ⟨0, by omega⟩ from Fin.ext hj]
    omega
  refine ⟨hk, h0, fun hr => hσ.not41 (Or.inl ⟨1, twoBlockA_of_rho (by omega) h0 hr⟩)⟩

variable {Θ : Fin k → ℝ × ℝ}

/-- Lemma 4.16, `P_B` part, by reflection. -/
lemma noPB (hk : 2 ≤ k) (h0 : ∀ j : Fin k, j.val = 0 → (σ j : ℕ) = 0)
    (hΘ : CopyIn σ Θ (D415 σ)) (i : Fin k) : Θ i ∉ PB415 σ := by
  intro h
  apply noPL hk (h0_symm h0) (reflCopy_copy hk hΘ) (σ i)
  rw [reflCopy_apply]
  exact (swap_PL hk).2 h

/-- Lemma 4.16, `P_R` part, by reflection. -/
lemma noPR (hk : 3 ≤ k) (h0 : ∀ j : Fin k, j.val = 0 → (σ j : ℕ) = 0)
    (hρ : ¬ ∀ j : Fin k, 1 ≤ j.val → (σ j : ℕ) + j.val = k)
    (hΘ : CopyIn σ Θ (D415 σ)) (i : Fin k) : Θ i ∉ PR415 σ := by
  intro h
  apply noPU hk (h0_symm h0) (fun hr => hρ (rho_of_rho_symm h0 hr))
    (reflCopy_copy (by omega) hΘ) (σ i)
  rw [reflCopy_apply]
  exact (swap_PU (by omega)).2 h

/-- Claim 4.18, `B/R` half, by reflection. -/
lemma c418BR (hk : 2 ≤ k) (h0 : ∀ j : Fin k, j.val = 0 → (σ j : ℕ) = 0)
    (hΘ : CopyIn σ Θ (D415 σ)) :
    ¬ ((∃ i, Θ i ∈ PB415 σ) ∧ (∃ i, Θ i ∈ PR415 σ)) := by
  rintro ⟨⟨i, hi⟩, ⟨i', hi'⟩⟩
  refine c418LU hk (h0_symm h0) (reflCopy_copy hk hΘ) ⟨⟨σ i, ?_⟩, ⟨σ i', ?_⟩⟩
  · rw [reflCopy_apply]; exact (swap_PL hk).2 hi
  · rw [reflCopy_apply]; exact (swap_PU hk).2 hi'

lemma sig_one (hk : 1 ≤ k) : sig σ 1 = canonPt σ ⟨0, by omega⟩ := by
  unfold sig th
  split_ifs with h
  · rfl
  · omega

end refl

end CO

/-- **Lemma 4.16.** Under the standing hypotheses of Subsection 4.3 (with `σ(1) = 1`), if `Π` is
associated with a permutation and `Σ ⊆ Π ⊆ Σ ∪ P_L ∪ P_R ∪ P_B ∪ P_U` (Construction 4.15), then
`Σ` is the unique `σ`-copy in `Π`. The proof does not use `hP : IsPermPointSet P` (tex l.951) or
`Hyp416.not42` (σ is none of the four patterns (31524), (24153), (42513), (35142) of
Subsection 4.2, tex l.922; it even follows from `σ(1) = 1`); the paper states
both, and they are kept to match the paper. -/
theorem lemma_4_16 (σ : Perm (Fin k)) (hσ : Hyp416 σ)
    (P : Finset (ℝ × ℝ)) (hP : IsPermPointSet P)
    (h₁ : (↑(canon σ) : Set (ℝ × ℝ)) ⊆ ↑P) (h₂ : (↑P : Set (ℝ × ℝ)) ⊆ D415 σ) :
    IsUniqueCopy σ ↑P := by
  obtain ⟨hk, h0, hρ⟩ := CO.hyp_facts hσ
  refine ⟨h₁, fun Θ hΘ => ?_⟩
  have hΘ' : CopyIn σ Θ (D415 σ) := ⟨hΘ.1, fun i => h₂ (hΘ.2 i)⟩
  have hsub : Finset.univ.image Θ ⊆ canon σ := by
    intro p hp
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hp
    rcases CO.memD (hΘ'.2 i) with ⟨m, hm⟩ | h | h | h | h
    · rw [hm]
      exact Finset.mem_image_of_mem _ (Finset.mem_univ m)
    · exact absurd h (CO.noPL (by omega) h0 hΘ' i)
    · exact absurd h (CO.noPU hk h0 hρ hΘ' i)
    · exact absurd h (CO.noPB (by omega) h0 hΘ' i)
    · exact absurd h (CO.noPR hk h0 hρ hΘ' i)
  have hinj : Function.Injective Θ := fun a b h => hΘ.1.1.injective (by simp only [h])
  refine Finset.eq_of_subset_of_card_le hsub ?_
  rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  exact (Finset.card_image_le).trans (by simp)

/-- **Claim 4.17.** For a `σ`-copy `Θ ⊆ D` (Lemma 4.16's setting): if `Θ ∩ P_L ≠ ∅` then
`Σ(1) ∉ Θ`; likewise if `Θ ∩ P_B ≠ ∅` then `Σ(1) ∉ Θ`.

Used inside the sub-argument by contradiction of Lemma 4.16's proof "First suppose `Θ ∩ P_L ≠ ∅` … a
contradiction" (tex l.986–988) through the proof of Claim 4.18 (tex l.979), whose case conditions
never hold for a copy (`lemma_4_16`); so the claim holds only vacuously. Its proof does not use
`Hyp416.not41`/`not42` (tex l.922), which are kept to match the paper. -/
theorem claim_4_17 (σ : Perm (Fin k)) (hσ : Hyp416 σ) (Θ : Fin k → ℝ × ℝ)
    (hΘ : CopyIn σ Θ (D415 σ)) :
    ((∃ i, Θ i ∈ PL415 σ) → ∀ i, Θ i ≠ sig σ 1) ∧
    ((∃ i, Θ i ∈ PB415 σ) → ∀ i, Θ i ≠ sig σ 1) := by
  obtain ⟨hk, h0, -⟩ := CO.hyp_facts hσ
  have hR := hΘ.1
  have hs : ∀ j, Θ j = sig σ 1 → (Θ j).1 = 1 ∧ (Θ j).2 = 1 := by
    intro j hj
    rw [hj, CO.sig_one (by omega), CO.canon_x, CO.canon_y, h0 _ rfl]
    simp
  constructor
  · rintro ⟨i, hi⟩ j hj
    have hi0 : i = ⟨0, by omega⟩ := Fin.ext (CO.PL_only0 h0 hΘ hi)
    rw [hi0] at hi
    have hyi := (CO.PL_facts hi).2.1
    obtain ⟨-, hyj⟩ := hs j hj
    by_cases hj0 : j.val = 0
    · rw [show j = ⟨0, by omega⟩ from Fin.ext hj0] at hyj
      linarith
    · have := CO.y0_lt hR h0 (a := ⟨0, by omega⟩) (b := j) rfl hj0
      linarith
  · rintro ⟨i, hi⟩ j hj
    have hyi := (CO.PB_facts hi).1
    obtain ⟨hxj, hyj⟩ := hs j hj
    by_cases hj0 : j.val = 0
    · have := CO.sig_lt_of_y hR (a := i) (b := j) (by linarith)
      rw [h0 j hj0] at this
      omega
    · have hx := CO.xlt hR (a := ⟨0, by omega⟩) (b := j) (by show 0 < j.val; omega)
      have hL := CO.x_lt_one_PL (by omega) (hΘ.2 ⟨0, by omega⟩) (by linarith)
      have := CO.y0_lt hR h0 (a := ⟨0, by omega⟩) (b := j) rfl hj0
      linarith [(CO.PL_facts hL).2.1]

/-- **Claim 4.18.** `Θ` cannot meet both `P_L` and `P_U`; likewise it cannot meet both `P_B` and
`P_R`.

Used inside the sub-argument by contradiction of Lemma 4.16's proof "First suppose `Θ ∩ P_L ≠ ∅` … a
contradiction" (tex l.986–988), whose case conditions never hold for a copy (`lemma_4_16`); so the
claim holds only vacuously. Its proof does not use `Hyp416.not41`/`not42` (tex l.922), which are
kept to match the paper. -/
theorem claim_4_18 (σ : Perm (Fin k)) (hσ : Hyp416 σ) (Θ : Fin k → ℝ × ℝ)
    (hΘ : CopyIn σ Θ (D415 σ)) :
    ¬ ((∃ i, Θ i ∈ PL415 σ) ∧ (∃ i, Θ i ∈ PU415 σ)) ∧
    ¬ ((∃ i, Θ i ∈ PB415 σ) ∧ (∃ i, Θ i ∈ PR415 σ)) := by
  obtain ⟨hk, h0, -⟩ := CO.hyp_facts hσ
  exact ⟨CO.c418LU (by omega) h0 hΘ, CO.c418BR (by omega) h0 hΘ⟩

end LinfPermRemoval
