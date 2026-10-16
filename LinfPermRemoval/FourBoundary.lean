/-
Formalization of V. H. Le, R. Shi, F. Wei, "$L_\infty$ Permutation Removal Lemma"
(unpublished manuscript). Not part of Mathlib.
-/
import LinfPermRemoval.Geometry
import LinfPermRemoval.Discretize

/-!
# Subsection 4.4: the four boundary points are distinct

Standing hypotheses (tex l.1018–1023, `Standing44`): `σ` is not covered by Subsections 4.1 or
4.2, and `{σ(1), σ(k)} ∩ {1, k} = ∅`, so the boundary points `L = Σ(1)`, `R = Σ(k)`,
`B = Σ⁻¹(1)`, `U = Σ⁻¹(k)` are pairwise distinct.

The claims inside the proof of Lemma 4.20 are steps of a proof by contradiction: their context
(`Ctx420`) fixes a `σ`-copy `Θ ⊆ Π` with `Θ ≠ Σ`, which `lemma_4_20` shows cannot exist. The
bundle without the field `ne` is satisfiable (take `Θ = Σ`). Claims 4.23–4.26 additionally assume
the normalization (4.5) `Θ ∩ P_L ≠ ∅` and `ℓ < r` that the paper makes "by the dihedral
symmetries".
-/

open Equiv Finset

namespace LinfPermRemoval

variable {k : ℕ}

/-- The standing hypotheses of Subsection 4.4 (tex l.1018). The field `not42 : ¬ IsExcFive σ`
excludes all four patterns (31524), (24153), (42513), (35142) of Subsection 4.2. No argument needs
`not42` except the proof of Lemma 4.40 (`lemma_4_40`). Other proofs project it only to pass it on to
a reflected pattern: `cor_4_38` uses it to build `Standing44 (antiD σ)` for Corollary 4.37, which
does not need it, and `S4.standing_revP`/`S4.standing_compP` transfer it under the symmetries of
Section 4. FourBoundary.lean and UnitGap.lean compile with the field deleted (and its transfer line
in `cor_4_38` removed; audit probe `substantiveness@14`,
`fourboundary_unitgap_without_not42.lean`). The field is kept to match the paper. -/
structure Standing44 (σ : Perm (Fin k)) : Prop where
  not41 : ¬ IsTwoBlock σ
  not42 : ¬ IsExcFive σ
  l_ne : lv σ ≠ 1 ∧ lv σ ≠ k
  r_ne : rv σ ≠ 1 ∧ rv σ ≠ k

/-! ## Construction 4.19 -/

/-- `I_L = (1,1) + t(-1,1)` if `σ(2) > ℓ`, `(1,k) + t(-1,-1)` if `σ(2) < ℓ`; `0 ≤ t ≤ k-1`. -/
noncomputable def IL419 (σ : Perm (Fin k)) : Set (ℝ × ℝ) :=
  if lv σ < sval σ 2 then closedSeg (1, 1) (-1, 1) ((k : ℝ) - 1)
  else closedSeg (1, (k : ℝ)) (-1, -1) ((k : ℝ) - 1)

/-- `I_R = (k,1) + t(1,1)` if `σ(k-1) > r`, `(k,k) + t(1,-1)` if `σ(k-1) < r`; `0 ≤ t ≤ k-1`. -/
noncomputable def IR419 (σ : Perm (Fin k)) : Set (ℝ × ℝ) :=
  if rv σ < sval σ (k - 1) then closedSeg ((k : ℝ), 1) (1, 1) ((k : ℝ) - 1)
  else closedSeg ((k : ℝ), (k : ℝ)) (1, -1) ((k : ℝ) - 1)

/-- `I_B = (1,1) + t(1,-1)` if `σ⁻¹(2) > b`, `(k,1) + t(-1,-1)` if `σ⁻¹(2) < b`;
`0 ≤ t ≤ k-1`. -/
noncomputable def IB419 (σ : Perm (Fin k)) : Set (ℝ × ℝ) :=
  if bp σ < spos σ 2 then closedSeg (1, 1) (1, -1) ((k : ℝ) - 1)
  else closedSeg ((k : ℝ), 1) (-1, -1) ((k : ℝ) - 1)

/-- `I_U = (1,k) + t(1,1)` if `σ⁻¹(k-1) > u`, `(k,k) + t(-1,1)` if `σ⁻¹(k-1) < u`;
`0 ≤ t ≤ k-1`. -/
noncomputable def IU419 (σ : Perm (Fin k)) : Set (ℝ × ℝ) :=
  if up σ < spos σ (k - 1) then closedSeg (1, (k : ℝ)) (1, 1) ((k : ℝ) - 1)
  else closedSeg ((k : ℝ), (k : ℝ)) (-1, 1) ((k : ℝ) - 1)

/-- **Construction 4.19**, `P_L`: `{p ∈ I_L ∖ ℤ² : p_y > ℓ+1}` if `ℓ < r`,
`{p ∈ I_L ∖ ℤ² : p_y < ℓ-1}` if `ℓ > r`. -/
noncomputable def PL419 (σ : Perm (Fin k)) : Set (ℝ × ℝ) :=
  {p | p ∈ IL419 σ \ lattice ∧
    (if lv σ < rv σ then (lv σ : ℝ) + 1 < p.2 else p.2 < (lv σ : ℝ) - 1)}

/-- **Construction 4.19**, `P_R`: `{p ∈ I_R ∖ ℤ² : p_y < r-1}` if `ℓ < r`,
`{p ∈ I_R ∖ ℤ² : p_y > r+1}` if `ℓ > r`. -/
noncomputable def PR419 (σ : Perm (Fin k)) : Set (ℝ × ℝ) :=
  {p | p ∈ IR419 σ \ lattice ∧
    (if lv σ < rv σ then p.2 < (rv σ : ℝ) - 1 else (rv σ : ℝ) + 1 < p.2)}

/-- **Construction 4.19**, `P_B`: `{p ∈ I_B ∖ ℤ² : p_x > b+1}` if `b < u`,
`{p ∈ I_B ∖ ℤ² : p_x < b-1}` if `b > u`. -/
noncomputable def PB419 (σ : Perm (Fin k)) : Set (ℝ × ℝ) :=
  {p | p ∈ IB419 σ \ lattice ∧
    (if bp σ < up σ then (bp σ : ℝ) + 1 < p.1 else p.1 < (bp σ : ℝ) - 1)}

/-- **Construction 4.19**, `P_U`: `{p ∈ I_U ∖ ℤ² : p_x < u-1}` if `b < u`,
`{p ∈ I_U ∖ ℤ² : p_x > u+1}` if `b > u`. -/
noncomputable def PU419 (σ : Perm (Fin k)) : Set (ℝ × ℝ) :=
  {p | p ∈ IU419 σ \ lattice ∧
    (if bp σ < up σ then p.1 < (up σ : ℝ) - 1 else (up σ : ℝ) + 1 < p.1)}

/-- The support `Σ ∪ P_L ∪ P_R ∪ P_B ∪ P_U` of Construction 4.19. -/
noncomputable def D419 (σ : Perm (Fin k)) : Set (ℝ × ℝ) :=
  ↑(canon σ) ∪ PL419 σ ∪ PR419 σ ∪ PB419 σ ∪ PU419 σ

/-! ## Auxiliary development (abstract context of the proof of Lemma 4.20) -/

namespace FB

/-! ### 1-based API -/

lemma sval_fin (σ : Perm (Fin k)) (i : Fin k) : sval σ (i.val + 1) = (σ i : ℕ) + 1 := by
  unfold sval
  split_ifs with h
  · simp
  · exact absurd ⟨by omega, by omega⟩ h

lemma spos_fin (σ : Perm (Fin k)) (j : Fin k) : spos σ (j.val + 1) = (σ.symm j : ℕ) + 1 := by
  unfold spos
  split_ifs with h
  · simp
  · exact absurd ⟨by omega, by omega⟩ h

lemma th_fin (Θ : Fin k → ℝ × ℝ) (i : Fin k) : th Θ (i.val + 1) = Θ i := by
  unfold th
  split_ifs with h
  · simp
  · exact absurd ⟨by omega, by omega⟩ h

lemma thInv_fin (σ : Perm (Fin k)) (Θ : Fin k → ℝ × ℝ) (j : Fin k) :
    thInv σ Θ (j.val + 1) = Θ (σ.symm j) := by
  unfold thInv
  split_ifs with h
  · simp
  · exact absurd ⟨by omega, by omega⟩ h

/-- Every in-range 1-based index is `i.val + 1` for some `i : Fin k`. -/
lemma exists_fin {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ k) : ∃ a : Fin k, i = a.val + 1 :=
  ⟨⟨i - 1, by omega⟩, by simp; omega⟩

lemma sval_mem (σ : Perm (Fin k)) {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ k) :
    1 ≤ sval σ i ∧ sval σ i ≤ k := by
  obtain ⟨a, rfl⟩ := exists_fin h1 h2
  rw [sval_fin]; have := (σ a).isLt; omega

lemma spos_mem (σ : Perm (Fin k)) {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ k) :
    1 ≤ spos σ i ∧ spos σ i ≤ k := by
  obtain ⟨a, rfl⟩ := exists_fin h1 h2
  rw [spos_fin]; have := (σ.symm a).isLt; omega

lemma spos_sval (σ : Perm (Fin k)) {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ k) :
    spos σ (sval σ i) = i := by
  obtain ⟨a, rfl⟩ := exists_fin h1 h2
  rw [sval_fin, spos_fin]; simp

lemma sval_spos (σ : Perm (Fin k)) {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ k) :
    sval σ (spos σ i) = i := by
  obtain ⟨a, rfl⟩ := exists_fin h1 h2
  rw [spos_fin, sval_fin]; simp

lemma sval_inj (σ : Perm (Fin k)) {i j : ℕ} (hi1 : 1 ≤ i) (hi2 : i ≤ k) (hj1 : 1 ≤ j)
    (hj2 : j ≤ k) (h : sval σ i = sval σ j) : i = j := by
  rw [← spos_sval σ hi1 hi2, h, spos_sval σ hj1 hj2]

lemma spos_inj (σ : Perm (Fin k)) {i j : ℕ} (hi1 : 1 ≤ i) (hi2 : i ≤ k) (hj1 : 1 ≤ j)
    (hj2 : j ≤ k) (h : spos σ i = spos σ j) : i = j := by
  rw [← sval_spos σ hi1 hi2, h, sval_spos σ hj1 hj2]

lemma thInv_eq (σ : Perm (Fin k)) (Θ : Fin k → ℝ × ℝ) {j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ k) :
    thInv σ Θ j = th Θ (spos σ j) := by
  obtain ⟨a, rfl⟩ := exists_fin h1 h2
  rw [thInv_fin, spos_fin, th_fin]

lemma th_eq_thInv (σ : Perm (Fin k)) (Θ : Fin k → ℝ × ℝ) {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ k) :
    th Θ i = thInv σ Θ (sval σ i) := by
  have := sval_mem σ h1 h2
  rw [thInv_eq σ Θ this.1 this.2, spos_sval σ h1 h2]

lemma sig_eq (σ : Perm (Fin k)) {m : ℕ} (h1 : 1 ≤ m) (h2 : m ≤ k) :
    sig σ m = ((m : ℝ), (sval σ m : ℝ)) := by
  obtain ⟨a, rfl⟩ := exists_fin h1 h2
  rw [sig, th_fin, sval_fin, canonPt]; push_cast; rfl

lemma sigInv_eq (σ : Perm (Fin k)) {j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ k) :
    sigInv σ j = ((spos σ j : ℝ), (j : ℝ)) := by
  rw [sigInv, thInv_eq σ _ h1 h2, ← sig, sig_eq σ (spos_mem σ h1 h2).1 (spos_mem σ h1 h2).2,
    sval_spos σ h1 h2]

/-- A canonical point, 1-based: `(m, σ(m))` with `1 ≤ m ≤ k`. -/
def Can (σ : Perm (Fin k)) (p : ℝ × ℝ) : Prop :=
  ∃ m : ℕ, 1 ≤ m ∧ m ≤ k ∧ p = ((m : ℝ), (sval σ m : ℝ))

lemma mem_canon_iff (σ : Perm (Fin k)) (p : ℝ × ℝ) : p ∈ canon σ ↔ Can σ p := by
  constructor
  · intro h
    simp only [canon, Finset.mem_image, Finset.mem_univ, true_and] at h
    obtain ⟨a, rfl⟩ := h
    refine ⟨a.val + 1, by omega, by omega, ?_⟩
    rw [sval_fin, canonPt]; push_cast; rfl
  · rintro ⟨m, h1, h2, rfl⟩
    obtain ⟨a, rfl⟩ := exists_fin h1 h2
    simp only [canon, Finset.mem_image, Finset.mem_univ, true_and]
    refine ⟨a, ?_⟩
    rw [sval_fin, canonPt]; push_cast; rfl

/-- Strict monotonicity of the `x`-coordinates of a copy, 1-based. -/
lemma th_x_lt {σ : Perm (Fin k)} {Θ : Fin k → ℝ × ℝ} (h : Represents σ Θ) {i j : ℕ}
    (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ k) : (th Θ i).1 < (th Θ j).1 := by
  obtain ⟨a, rfl⟩ := exists_fin (k := k) hi (by omega)
  obtain ⟨b, rfl⟩ := exists_fin (k := k) (by omega) hj
  rw [th_fin, th_fin]
  exact h.1 (Fin.mk_lt_mk.mpr (by omega))

lemma th_x_le {σ : Perm (Fin k)} {Θ : Fin k → ℝ × ℝ} (h : Represents σ Θ) {i j : ℕ}
    (hi : 1 ≤ i) (hij : i ≤ j) (hj : j ≤ k) : (th Θ i).1 ≤ (th Θ j).1 := by
  rcases hij.lt_or_eq with h' | rfl
  · exact (th_x_lt h hi h' hj).le
  · exact le_rfl

/-- The `y`-order of a copy, 1-based. -/
lemma th_y_lt_iff {σ : Perm (Fin k)} {Θ : Fin k → ℝ × ℝ} (h : Represents σ Θ) {i j : ℕ}
    (hi1 : 1 ≤ i) (hi2 : i ≤ k) (hj1 : 1 ≤ j) (hj2 : j ≤ k) :
    (th Θ i).2 < (th Θ j).2 ↔ sval σ i < sval σ j := by
  obtain ⟨a, rfl⟩ := exists_fin hi1 hi2
  obtain ⟨b, rfl⟩ := exists_fin hj1 hj2
  rw [th_fin, th_fin, sval_fin, sval_fin, h.2 a b, Fin.lt_def]
  omega

lemma thInv_y_lt {σ : Perm (Fin k)} {Θ : Fin k → ℝ × ℝ} (h : Represents σ Θ) {i j : ℕ}
    (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ k) : (thInv σ Θ i).2 < (thInv σ Θ j).2 := by
  have hi' := spos_mem σ hi (by omega : i ≤ k)
  have hj' := spos_mem σ (by omega : 1 ≤ j) hj
  rw [thInv_eq σ Θ hi (by omega), thInv_eq σ Θ (by omega) hj,
    th_y_lt_iff h hi'.1 hi'.2 hj'.1 hj'.2, sval_spos σ hi (by omega), sval_spos σ (by omega) hj]
  exact hij

lemma th_inj {σ : Perm (Fin k)} {Θ : Fin k → ℝ × ℝ} (h : Represents σ Θ) {i j : ℕ}
    (hi1 : 1 ≤ i) (hi2 : i ≤ k) (hj1 : 1 ≤ j) (hj2 : j ≤ k) (he : th Θ i = th Θ j) : i = j := by
  rcases lt_trichotomy i j with hl | rfl | hl
  · have := th_x_lt h hi1 hl hj2; rw [he] at this; exact absurd this (lt_irrefl _)
  · rfl
  · have := th_x_lt h hj1 hl hi2; rw [he] at this; exact absurd this (lt_irrefl _)


/-! ### Integrality of canonical points -/

lemma Can.bounds {σ : Perm (Fin k)} {p : ℝ × ℝ} (hp : Can σ p) :
    1 ≤ p.1 ∧ p.1 ≤ k ∧ 1 ≤ p.2 ∧ p.2 ≤ k := by
  obtain ⟨m, h1, h2, rfl⟩ := hp
  have := sval_mem σ h1 h2
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only <;> exact_mod_cast (by omega)

lemma int_succ_le {a : ℝ} (m : ℕ) (ha : a = (m : ℝ)) (z : ℤ) (h : (z : ℝ) < a) :
    (z : ℝ) + 1 ≤ a := by
  subst ha
  have h' : z < (m : ℤ) := by exact_mod_cast h
  have : z + 1 ≤ (m : ℤ) := h'
  exact_mod_cast this

lemma int_le_pred {a : ℝ} (m : ℕ) (ha : a = (m : ℝ)) (z : ℤ) (h : a < (z : ℝ)) :
    a ≤ (z : ℝ) - 1 := by
  subst ha
  have h' : (m : ℤ) < z := by exact_mod_cast h
  have : (m : ℤ) ≤ z - 1 := by omega
  have : ((m : ℤ) : ℝ) ≤ ((z - 1 : ℤ) : ℝ) := by exact_mod_cast this
  push_cast at this; exact this

lemma Can.x_succ {σ : Perm (Fin k)} {p : ℝ × ℝ} (hp : Can σ p) (z : ℤ) (h : (z : ℝ) < p.1) :
    (z : ℝ) + 1 ≤ p.1 := by
  obtain ⟨m, -, -, rfl⟩ := hp; exact int_succ_le m rfl z h

lemma Can.x_pred {σ : Perm (Fin k)} {p : ℝ × ℝ} (hp : Can σ p) (z : ℤ) (h : p.1 < (z : ℝ)) :
    p.1 ≤ (z : ℝ) - 1 := by
  obtain ⟨m, -, -, rfl⟩ := hp; exact int_le_pred m rfl z h

lemma Can.y_succ {σ : Perm (Fin k)} {p : ℝ × ℝ} (hp : Can σ p) (z : ℤ) (h : (z : ℝ) < p.2) :
    (z : ℝ) + 1 ≤ p.2 := by
  obtain ⟨m, -, -, rfl⟩ := hp; exact int_succ_le _ rfl z h

lemma Can.y_pred {σ : Perm (Fin k)} {p : ℝ × ℝ} (hp : Can σ p) (z : ℤ) (h : p.2 < (z : ℝ)) :
    p.2 ≤ (z : ℝ) - 1 := by
  obtain ⟨m, -, -, rfl⟩ := hp; exact int_le_pred _ rfl z h

/-- A canonical point with `x`-coordinate `n` is `Σ(n)`. -/
lemma Can.eq_sig {σ : Perm (Fin k)} {p : ℝ × ℝ} (hp : Can σ p) {n : ℕ} (h : p.1 = (n : ℝ)) :
    p = sig σ n := by
  obtain ⟨m, h1, h2, rfl⟩ := hp
  have h' : (m : ℝ) = n := h
  have : m = n := by exact_mod_cast h'
  subst this
  rw [sig_eq σ h1 h2]

/-! ### The abstract context -/

/-- Allowed shape of a point of `Θ ∩ P_L` (position `1`), as used by the proof. -/
def LTy (σ : Perm (Fin k)) (p : ℝ × ℝ) : Prop :=
  p.1 < 1 ∧ (lv σ < rv σ → (lv σ : ℝ) + 1 < p.2) ∧ (rv σ < lv σ → p.2 < (lv σ : ℝ) - 1)

/-- Allowed shape of a point of `Θ ∩ P_R` (position `k`). -/
def RTy (σ : Perm (Fin k)) (p : ℝ × ℝ) : Prop :=
  (k : ℝ) < p.1 ∧ (lv σ < rv σ → p.2 < (rv σ : ℝ) - 1) ∧ (rv σ < lv σ → (rv σ : ℝ) + 1 < p.2)

/-- Allowed shape of a point of `Θ ∩ P_B` (rank `1`). -/
def BTy (σ : Perm (Fin k)) (p : ℝ × ℝ) : Prop :=
  p.2 < 1 ∧ (bp σ < up σ → (bp σ : ℝ) + 1 < p.1) ∧ (up σ < bp σ → p.1 < (bp σ : ℝ) - 1)

/-- Allowed shape of a point of `Θ ∩ P_U` (rank `k`). -/
def UTy (σ : Perm (Fin k)) (p : ℝ × ℝ) : Prop :=
  (k : ℝ) < p.2 ∧ (bp σ < up σ → p.1 < (up σ : ℝ) - 1) ∧ (up σ < bp σ → (up σ : ℝ) + 1 < p.1)

/-- The abstract context of the proof of Lemma 4.20: a copy `Θ` of `σ`, each of whose points is
canonical or of one of the four boundary types allowed by (4.4), with the trimming bounds of
Construction 4.19. -/
structure Abs (σ : Perm (Fin k)) (Θ : Fin k → ℝ × ℝ) : Prop where
  rep : Represents σ Θ
  hl : 1 < lv σ ∧ lv σ < k
  hr : 1 < rv σ ∧ rv σ < k
  hb : 1 < bp σ ∧ bp σ < k
  hu : 1 < up σ ∧ up σ < k
  pt : ∀ i : ℕ, 1 ≤ i → i ≤ k → Can σ (th Θ i) ∨ (i = 1 ∧ LTy σ (th Θ i)) ∨
    (i = k ∧ RTy σ (th Θ i)) ∨ (sval σ i = 1 ∧ BTy σ (th Θ i)) ∨ (sval σ i = k ∧ UTy σ (th Θ i))

variable {σ : Perm (Fin k)} {Θ : Fin k → ℝ × ℝ}

lemma Abs.ptInv (hA : Abs σ Θ) {j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ k) :
    Can σ (thInv σ Θ j) ∨ (j = lv σ ∧ LTy σ (thInv σ Θ j)) ∨ (j = rv σ ∧ RTy σ (thInv σ Θ j)) ∨
      (j = 1 ∧ BTy σ (thInv σ Θ j)) ∨ (j = k ∧ UTy σ (thInv σ Θ j)) := by
  have hm := spos_mem σ h1 h2
  have hs := sval_spos σ h1 h2
  rw [thInv_eq σ Θ h1 h2]
  rcases hA.pt _ hm.1 hm.2 with h | ⟨he, h⟩ | ⟨he, h⟩ | ⟨he, h⟩ | ⟨he, h⟩
  · exact Or.inl h
  · refine Or.inr (Or.inl ⟨?_, h⟩); rw [← hs, he]; rfl
  · refine Or.inr (Or.inr (Or.inl ⟨?_, h⟩)); rw [← hs, he]; rfl
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hs ▸ he, h⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hs ▸ he, h⟩)))

lemma Abs.k3 (hA : Abs σ Θ) : 3 ≤ k := by
  have := hA.hl; have := hA.hr
  have : lv σ ≠ rv σ := by
    intro h
    have := sval_inj σ (i := 1) (j := k) le_rfl (by omega) (by omega) le_rfl h
    omega
  omega

lemma Abs.lr (hA : Abs σ Θ) : lv σ < rv σ ∨ rv σ < lv σ := by
  have := hA.k3
  have : lv σ ≠ rv σ := by
    intro e
    have := sval_inj σ (i := 1) (j := k) le_rfl (by omega) (by omega) le_rfl e
    omega
  omega

/-! ### Claim 4.21 on the abstract context -/

lemma Abs.c21_1 (hA : Abs σ Θ) (j : ℕ) (h1 : 1 ≤ j) (h2 : j < k)
    (h : (j : ℝ) < (thInv σ Θ j).2) : ((j : ℝ) + 1) < (thInv σ Θ (j + 1)).2 := by
  have hlt := thInv_y_lt hA.rep h1 (lt_add_one j) (by omega)
  suffices (j : ℝ) + 1 ≤ (thInv σ Θ j).2 by linarith
  rcases hA.ptInv h1 h2.le with hc | ⟨he, hL, h3, h4⟩ | ⟨he, hR, h3, h4⟩ | ⟨he, hB, -⟩ |
      ⟨he, -⟩
  · exact_mod_cast hc.y_succ j (by exact_mod_cast h)
  · subst he
    rcases hA.lr with hlr | hlr
    · linarith [h3 hlr]
    · linarith [h4 hlr]
  · subst he
    rcases hA.lr with hlr | hlr
    · linarith [h3 hlr]
    · linarith [h4 hlr]
  · have : (1 : ℝ) ≤ j := by exact_mod_cast h1
    linarith
  · omega

lemma Abs.bu (hA : Abs σ Θ) : bp σ < up σ ∨ up σ < bp σ := by
  have := hA.k3
  have : bp σ ≠ up σ := by
    intro e
    have := spos_inj σ (i := 1) (j := k) le_rfl (by omega) (by omega) le_rfl e
    omega
  omega

lemma eq_bp_of {σ : Perm (Fin k)} {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ k) (h : sval σ i = 1) :
    i = bp σ := by
  rw [bp, ← h, spos_sval σ h1 h2]

lemma eq_up_of {σ : Perm (Fin k)} {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ k) (h : sval σ i = k) :
    i = up σ := by
  have := spos_sval σ h1 h2
  rw [h] at this; exact this.symm

lemma Abs.c21_2 (hA : Abs σ Θ) (j : ℕ) (h1 : 1 < j) (h2 : j ≤ k)
    (h : (thInv σ Θ j).2 < (j : ℝ)) : (thInv σ Θ (j - 1)).2 < (j : ℝ) - 1 := by
  have hlt := thInv_y_lt hA.rep (i := j - 1) (by omega) (by omega) h2
  suffices (thInv σ Θ j).2 ≤ (j : ℝ) - 1 by linarith
  have hj1 : (1 : ℝ) < j := by exact_mod_cast h1
  have hjk : (j : ℝ) ≤ k := by exact_mod_cast h2
  rcases hA.ptInv h1.le h2 with hc | ⟨he, hL, h3, h4⟩ | ⟨he, hR, h3, h4⟩ | ⟨he, hB, -⟩ |
      ⟨he, hU, -⟩
  · exact_mod_cast hc.y_pred j (by exact_mod_cast h)
  · subst he
    rcases hA.lr with hlr | hlr
    · linarith [h3 hlr]
    · linarith [h4 hlr]
  · subst he
    rcases hA.lr with hlr | hlr
    · linarith [h3 hlr]
    · linarith [h4 hlr]
  · omega
  · linarith

lemma Abs.c21_3 (hA : Abs σ Θ) (i : ℕ) (h1 : 1 ≤ i) (h2 : i < k)
    (h : (i : ℝ) < (th Θ i).1) : ((i : ℝ) + 1) < (th Θ (i + 1)).1 := by
  have hlt := th_x_lt hA.rep h1 (lt_add_one i) (by omega)
  suffices (i : ℝ) + 1 ≤ (th Θ i).1 by linarith
  have hi1 : (1 : ℝ) ≤ i := by exact_mod_cast h1
  have hik : (i : ℝ) < k := by exact_mod_cast h2
  rcases hA.pt i h1 h2.le with hc | ⟨he, hL, -⟩ | ⟨he, -⟩ | ⟨he, hB, h3, h4⟩ |
      ⟨he, hU, h3, h4⟩
  · exact_mod_cast hc.x_succ i (by exact_mod_cast h)
  · linarith
  · omega
  · have := eq_bp_of h1 h2.le he; subst this
    rcases hA.bu with hbu | hbu
    · linarith [h3 hbu]
    · linarith [h4 hbu]
  · have := eq_up_of h1 h2.le he; subst this
    rcases hA.bu with hbu | hbu
    · linarith [h3 hbu]
    · linarith [h4 hbu]

lemma Abs.c21_4 (hA : Abs σ Θ) (i : ℕ) (h1 : 1 < i) (h2 : i ≤ k)
    (h : (th Θ i).1 < (i : ℝ)) : (th Θ (i - 1)).1 < (i : ℝ) - 1 := by
  have hlt := th_x_lt hA.rep (i := i - 1) (by omega) (by omega) h2
  suffices (th Θ i).1 ≤ (i : ℝ) - 1 by linarith
  have hi1 : (1 : ℝ) < i := by exact_mod_cast h1
  have hik : (i : ℝ) ≤ k := by exact_mod_cast h2
  rcases hA.pt i h1.le h2 with hc | ⟨he, hL, -⟩ | ⟨he, hR, -⟩ | ⟨he, hB, h3, h4⟩ |
      ⟨he, hU, h3, h4⟩
  · exact_mod_cast hc.x_pred i (by exact_mod_cast h)
  · omega
  · subst he; linarith
  · have := eq_bp_of h1.le h2 he; subst this
    rcases hA.bu with hbu | hbu
    · linarith [h3 hbu]
    · linarith [h4 hbu]
  · have := eq_up_of h1.le h2 he; subst this
    rcases hA.bu with hbu | hbu
    · linarith [h3 hbu]
    · linarith [h4 hbu]

/-! ### Corollary 4.22 on the abstract context -/

/-- Downward induction on `[a, j]`. -/
lemma down_ind {P : ℕ → Prop} {a j : ℕ} (hj : P j) (hs : ∀ s, a ≤ s → s < j → P (s + 1) → P s) :
    ∀ s, a ≤ s → s ≤ j → P s := by
  have key : ∀ d s, a ≤ s → j = s + d → P s := by
    intro d
    induction d with
    | zero => intro s _ h; simpa [h] using hj
    | succ d ih =>
      intro s has h
      exact hs s has (by omega) (ih (s + 1) (by omega) (by omega))
  intro s has hsj
  exact key (j - s) s has (by omega)

lemma Abs.c22_1 (hA : Abs σ Θ) (j : ℕ) (h1 : 1 ≤ j) (h : (j : ℝ) < (thInv σ Θ j).2) :
    ∀ s : ℕ, j ≤ s → s ≤ k → (s : ℝ) < (thInv σ Θ s).2 := by
  intro s hs hsk
  induction s, hs using Nat.le_induction with
  | base => exact h
  | succ s hs ih =>
    have := hA.c21_1 s (by omega) (by omega) (ih (by omega))
    push_cast; exact this

lemma Abs.c22_2 (hA : Abs σ Θ) (j : ℕ) (h2 : j ≤ k) (h : (thInv σ Θ j).2 < (j : ℝ)) :
    ∀ s : ℕ, 1 ≤ s → s ≤ j → (thInv σ Θ s).2 < (s : ℝ) := by
  refine down_ind (P := fun s => (thInv σ Θ s).2 < (s : ℝ)) h ?_
  intro s hs1 hs ih
  have := hA.c21_2 (s + 1) (by omega) (by omega) ih
  simpa using this

lemma Abs.c22_3 (hA : Abs σ Θ) (i : ℕ) (h1 : 1 ≤ i) (h : (i : ℝ) < (th Θ i).1) :
    ∀ s : ℕ, i ≤ s → s ≤ k → (s : ℝ) < (th Θ s).1 := by
  intro s hs hsk
  induction s, hs using Nat.le_induction with
  | base => exact h
  | succ s hs ih =>
    have := hA.c21_3 s (by omega) (by omega) (ih (by omega))
    push_cast; exact this

lemma Abs.c22_4 (hA : Abs σ Θ) (i : ℕ) (h2 : i ≤ k) (h : (th Θ i).1 < (i : ℝ)) :
    ∀ s : ℕ, 1 ≤ s → s ≤ i → (th Θ s).1 < (s : ℝ) := by
  refine down_ind (P := fun s => (th Θ s).1 < (s : ℝ)) h ?_
  intro s hs1 hs ih
  have := hA.c21_4 (s + 1) (by omega) (by omega) ih
  simpa using this

/-! ### The normalized case (4.5) on the abstract context -/

lemma Abs.L1 (hA : Abs σ Θ) (hn : (th Θ 1).1 < 1) : LTy σ (th Θ 1) := by
  have := hA.k3; have := hA.hl
  rcases hA.pt 1 le_rfl (by omega) with hc | ⟨-, h⟩ | ⟨he, -⟩ | ⟨he, -⟩ | ⟨he, -⟩
  · linarith [hc.bounds.1]
  · exact h
  · omega
  · exact absurd he (by rw [← lv]; omega)
  · exact absurd he (by rw [← lv]; omega)

lemma Abs.c23 (hA : Abs σ Θ) (hn : (th Θ 1).1 < 1) (hlr : lv σ < rv σ) :
    thInv σ Θ (lv σ) = th Θ 1 ∧ (lv σ : ℝ) + 1 < (thInv σ Θ (lv σ)).2 := by
  have := hA.k3
  have he : thInv σ Θ (lv σ) = th Θ 1 := (th_eq_thInv σ Θ le_rfl (by omega)).symm
  exact ⟨he, he ▸ (hA.L1 hn).2.1 hlr⟩

lemma Abs.c24 (hA : Abs σ Θ) (hn : (th Θ 1).1 < 1) (hlr : lv σ < rv σ) :
    (rv σ : ℝ) < (th Θ k).2 ∧ Can σ (th Θ k) := by
  have := hA.k3; have := hA.hl; have := hA.hr
  obtain ⟨-, h23⟩ := hA.c23 hn hlr
  have h1 := hA.c22_1 (lv σ) (by omega) (by linarith) (rv σ) hlr.le (by omega)
  have hk : th Θ k = thInv σ Θ (rv σ) := th_eq_thInv σ Θ (by omega) le_rfl
  rw [← hk] at h1
  refine ⟨h1, ?_⟩
  rcases hA.pt k (by omega) le_rfl with hc | ⟨he, -⟩ | ⟨-, hR⟩ | ⟨he, -⟩ | ⟨he, -⟩
  · exact hc
  · omega
  · linarith [hR.2.1 hlr]
  · exact absurd he (by rw [← rv]; omega)
  · exact absurd he (by rw [← rv]; omega)

lemma Abs.c25 (hA : Abs σ Θ) (hn : (th Θ 1).1 < 1) (hlr : lv σ < rv σ) :
    (k : ℝ) < (thInv σ Θ k).2 ∧ UTy σ (thInv σ Θ k) ∧ bp σ < up σ ∧
      (thInv σ Θ k).1 < (up σ : ℝ) - 1 ∧ (thInv σ Θ 1).1 < (bp σ : ℝ) ∧ Can σ (thInv σ Θ 1) := by
  have := hA.k3; have := hA.hl; have := hA.hr; have := hA.hb; have := hA.hu
  obtain ⟨-, h23⟩ := hA.c23 hn hlr
  obtain ⟨-, h24⟩ := hA.c24 hn hlr
  have hy := hA.c22_1 (lv σ) (by omega) (by linarith) k (by omega) le_rfl
  have hU : UTy σ (thInv σ Θ k) := by
    rcases hA.ptInv (j := k) (by omega) le_rfl with hc | ⟨he, -⟩ | ⟨he, -⟩ | ⟨he, -⟩ | ⟨-, h⟩
    · linarith [hc.bounds.2.2.2]
    · omega
    · omega
    · omega
    · exact h
  have hku : thInv σ Θ k = th Θ (up σ) := thInv_eq σ Θ (by omega) le_rfl
  have hbu : bp σ < up σ := by
    rcases hA.bu with h | h
    · exact h
    · exfalso
      have h1 := hU.2.2 h
      rw [hku] at h1
      have := hA.c22_3 (up σ) (by omega) (by linarith) k (by omega) le_rfl
      linarith [h24.bounds.2.1]
  have hx := hU.2.1 hbu
  have h1b : thInv σ Θ 1 = th Θ (bp σ) := thInv_eq σ Θ le_rfl (by omega)
  have hxb : (thInv σ Θ 1).1 < (bp σ : ℝ) := by
    rw [h1b]
    rw [hku] at hx
    exact hA.c22_4 (up σ) (by omega) (by linarith) (bp σ) (by omega) hbu.le
  refine ⟨hy, hU, hbu, hx, hxb, ?_⟩
  rcases hA.ptInv (j := 1) le_rfl (by omega) with hc | ⟨he, -⟩ | ⟨he, -⟩ | ⟨-, hB⟩ | ⟨he, -⟩
  · exact hc
  · omega
  · omega
  · linarith [hB.2.1 hbu]
  · omega

/-- Points at positions other than `1` and `u` are canonical (normalized case). -/
lemma Abs.can_of (hA : Abs σ Θ) (hn : (th Θ 1).1 < 1) (hlr : lv σ < rv σ) {i : ℕ}
    (h1 : 1 ≤ i) (h2 : i ≤ k) (hi1 : i ≠ 1) (hiu : i ≠ up σ) : Can σ (th Θ i) := by
  have := hA.k3; have := hA.hb
  by_cases hik : i = k
  · subst hik; exact (hA.c24 hn hlr).2
  by_cases hib : i = bp σ
  · subst hib
    have h := (hA.c25 hn hlr).2.2.2.2.2
    rwa [thInv_eq σ Θ le_rfl (by omega)] at h
  rcases hA.pt i h1 h2 with hc | ⟨he, -⟩ | ⟨he, -⟩ | ⟨he, -⟩ | ⟨he, -⟩
  · exact hc
  · exact absurd he hi1
  · exact absurd he hik
  · exact absurd (eq_bp_of h1 h2 he) hib
  · exact absurd (eq_up_of h1 h2 he) hiu

lemma sval_bp (σ : Perm (Fin k)) (hk : 1 ≤ k) : sval σ (bp σ) = 1 := sval_spos σ le_rfl hk

lemma sval_up (σ : Perm (Fin k)) (hk : 1 ≤ k) : sval σ (up σ) = k := sval_spos σ hk le_rfl

/-- In the normalized case every point of `Θ` has `y ≥ 2` (the level of `Σ(b)` is unused). -/
lemma Abs.y_ge_two (hA : Abs σ Θ) (hn : (th Θ 1).1 < 1) (hlr : lv σ < rv σ) {i : ℕ}
    (h1 : 1 ≤ i) (h2 : i ≤ k) : 2 ≤ (th Θ i).2 := by
  have := hA.k3; have := hA.hb
  obtain ⟨-, -, -, -, hxb, hcb⟩ := hA.c25 hn hlr
  rw [thInv_eq σ Θ le_rfl (by omega)] at hxb hcb
  change Can σ (th Θ (bp σ)) at hcb
  change (th Θ (bp σ)).1 < _ at hxb
  have hb2 : 2 ≤ (th Θ (bp σ)).2 := by
    obtain ⟨m, hm1, hmk, he⟩ := hcb
    rw [he] at hxb ⊢
    have hxb' : (m : ℝ) < (bp σ : ℝ) := hxb
    have hmb : m < bp σ := by exact_mod_cast hxb'
    have : sval σ m ≠ 1 := by
      intro h; have := eq_bp_of hm1 hmk h; omega
    have := (sval_mem σ hm1 hmk).1
    show (2 : ℝ) ≤ (sval σ m : ℝ)
    exact_mod_cast (by omega : 2 ≤ sval σ m)
  by_cases hib : i = bp σ
  · rw [hib]; exact hb2
  · have hlt : (th Θ (bp σ)).2 < (th Θ i).2 := by
      rw [th_y_lt_iff hA.rep (by omega) (by omega) h1 h2, sval_bp σ (by omega)]
      have := (sval_mem σ h1 h2).1
      have : sval σ i ≠ 1 := fun h => hib (eq_bp_of h1 h2 h)
      omega
    linarith

/-- **Claim 4.26 (1)** on the abstract context, in the form: `b = u - 1`, and
`Θ(i)_x = i - 1` for `i ∉ {1, u}`. -/
lemma Abs.c26_x (hA : Abs σ Θ) (hn : (th Θ 1).1 < 1) (hlr : lv σ < rv σ) :
    bp σ + 1 = up σ ∧ ∀ i : ℕ, 1 ≤ i → i ≤ k → i ≠ 1 → i ≠ up σ → (th Θ i).1 = (i : ℝ) - 1 := by
  have := hA.k3; have := hA.hb; have := hA.hu; have := hA.hr; have := hA.hl
  obtain ⟨hyk, -, hbu, hxu, -, -⟩ := hA.c25 hn hlr
  obtain ⟨hr24, hck⟩ := hA.c24 hn hlr
  have hku : thInv σ Θ k = th Θ (up σ) := thInv_eq σ Θ (by omega) le_rfl
  rw [hku] at hxu hyk
  have hcan := fun i h1 h2 hi1 hiu => hA.can_of hn hlr (i := i) h1 h2 hi1 hiu
  -- first block, lower bound
  have lo1 : ∀ i, 2 ≤ i → i ≤ up σ - 1 → (i : ℝ) - 1 ≤ (th Θ i).1 := by
    intro i hi hiu
    induction i, hi using Nat.le_induction with
    | base =>
      have := (hcan 2 (by omega) (by omega) (by omega) (by omega)).bounds.1
      norm_num; exact this
    | succ i hi ih =>
      have h1 := ih (by omega)
      have h2 := th_x_lt hA.rep (i := i) (j := i + 1) (by omega) (by omega) (by omega)
      have h3 := (hcan (i + 1) (by omega) (by omega) (by omega) (by omega)).x_succ
        ((i : ℤ) - 1) (by push_cast; linarith)
      push_cast at h3 ⊢; linarith
  -- first block, upper bound
  have hi1 : ∀ i, 2 ≤ i → i ≤ up σ - 1 → (th Θ i).1 = (i : ℝ) - 1 := by
    intro i hi hiu
    have up1 : ∀ s, 2 ≤ s → s ≤ up σ - 1 → (th Θ s).1 ≤ (s : ℝ) - 1 := by
      refine down_ind (P := fun s => (th Θ s).1 ≤ (s : ℝ) - 1) ?_ ?_
      · have h2 := th_x_lt hA.rep (i := up σ - 1) (j := up σ) (by omega) (by omega) (by omega)
        have h3 := (hcan (up σ - 1) (by omega) (by omega) (by omega) (by omega)).x_pred
          ((up σ : ℤ) - 1) (by push_cast; linarith)
        have : ((up σ - 1 : ℕ) : ℝ) = (up σ : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega)]; simp
        rw [this]; push_cast at h3; linarith
      · intro s hs hsj ih
        have h2 := th_x_lt hA.rep (i := s) (j := s + 1) (by omega) (by omega) (by omega)
        have h3 := (hcan s (by omega) (by omega) (by omega) (by omega)).x_pred
          (s : ℤ) (by push_cast at ih ⊢; linarith)
        push_cast at h3; exact h3
    exact le_antisymm (up1 i hi hiu) (lo1 i hi hiu)
  have hy2 := fun i h1 h2 => hA.y_ge_two hn hlr (i := i) h1 h2
  -- `b = u - 1`
  have hb : bp σ + 1 = up σ := by
    by_contra hne
    have hx := hi1 (bp σ + 1) (by omega) (by omega)
    have he := (hcan (bp σ + 1) (by omega) (by omega) (by omega) (by omega)).eq_sig
      (n := bp σ) (by rw [hx]; push_cast; ring)
    have := hy2 (bp σ + 1) (by omega) (by omega)
    rw [he, sig_eq σ (by omega) (by omega), sval_bp σ (by omega)] at this
    norm_num at this
  refine ⟨hb, ?_⟩
  -- second block, lower bound
  have lo2 : ∀ i, up σ + 1 ≤ i → i ≤ k → (i : ℝ) - 1 ≤ (th Θ i).1 := by
    intro i hi hik
    induction i, hi using Nat.le_induction with
    | base =>
      have hc := hcan (up σ + 1) (by omega) (by omega) (by omega) (by omega)
      have h1 := th_x_lt hA.rep (i := up σ) (j := up σ + 1) (by omega) (by omega) (by omega)
      have h2 := th_x_lt hA.rep (i := up σ - 1) (j := up σ) (by omega) (by omega) (by omega)
      have h3 := hi1 (up σ - 1) (by omega) le_rfl
      have hc' : ((up σ - 1 : ℕ) : ℝ) = (up σ : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega)]; simp
      rw [hc'] at h3
      have h4 := hc.x_succ ((up σ : ℤ) - 2) (by push_cast; linarith)
      push_cast at h4
      rcases h4.lt_or_eq with h5 | h5
      · have h6 := hc.x_succ ((up σ : ℤ) - 1) (by push_cast; linarith)
        push_cast at h6 ⊢; linarith
      · exfalso
        have he := hc.eq_sig (n := bp σ) (by
          rw [← h5]; have : ((bp σ : ℕ) : ℝ) = (up σ : ℝ) - 1 := by
            rw [← hb]; push_cast; ring
          rw [this]; ring)
        have := hy2 (up σ + 1) (by omega) (by omega)
        rw [he, sig_eq σ (by omega) (by omega), sval_bp σ (by omega)] at this
        norm_num at this
    | succ i hi ih =>
      have h1 := ih (by omega)
      have h2 := th_x_lt hA.rep (i := i) (j := i + 1) (by omega) (by omega) (by omega)
      have h3 := (hcan (i + 1) (by omega) (by omega) (by omega) (by omega)).x_succ
        ((i : ℤ) - 1) (by push_cast; linarith)
      push_cast at h3 ⊢; linarith
  -- second block, upper bound
  have up2 : ∀ s, up σ + 1 ≤ s → s ≤ k → (th Θ s).1 ≤ (s : ℝ) - 1 := by
    refine down_ind (P := fun s => (th Θ s).1 ≤ (s : ℝ) - 1) ?_ ?_
    · obtain ⟨m, hm1, hmk, he⟩ := hck
      rw [he] at hr24 ⊢
      have hr24' : (rv σ : ℝ) < (sval σ m : ℝ) := hr24
      have hr : rv σ < sval σ m := by exact_mod_cast hr24'
      have hmk' : m ≠ k := by rintro rfl; exact absurd hr (lt_irrefl _)
      show (m : ℝ) ≤ (k : ℝ) - 1
      have : m + 1 ≤ k := by omega
      have : ((m + 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast this
      push_cast at this; linarith
    · intro s hs hsj ih
      have h2 := th_x_lt hA.rep (i := s) (j := s + 1) (by omega) (by omega) (by omega)
      have h3 := (hcan s (by omega) (by omega) (by omega) (by omega)).x_pred
        (s : ℤ) (by push_cast at ih ⊢; linarith)
      push_cast at h3; exact h3
  intro i h1 h2 hi1' hiu
  rcases lt_or_gt_of_ne hiu with h | h
  · exact hi1 i (by omega) (by omega)
  · exact le_antisymm (up2 i (by omega) h2) (lo2 i (by omega) h2)

/-- Two decreasing blocks `σ(1) > ⋯ > σ(u-1)` and `σ(u) = k > ⋯ > σ(k)` with `σ(1) < σ(k)`
force the two-block shape `(ℓ ⋯ 1)(k ⋯ ℓ+1)` with `u = r = ℓ + 1`. -/
lemma twoBlock_formula (σ : Perm (Fin k)) (u : ℕ) (hu : 2 ≤ u) (huk : u ≤ k)
    (hsu : sval σ u = k) (hlr : lv σ < rv σ)
    (hdec1 : ∀ i, 1 ≤ i → i + 1 ≤ u - 1 → sval σ (i + 1) < sval σ i)
    (hdec2 : ∀ i, u ≤ i → i + 1 ≤ k → sval σ (i + 1) < sval σ i) :
    u = lv σ + 1 ∧ rv σ = lv σ + 1 ∧
      ∀ i, 1 ≤ i → i ≤ k → sval σ i = if i ≤ lv σ then lv σ + 1 - i else k + lv σ + 1 - i := by
  have hA : ∀ i, 1 ≤ i → i ≤ u - 1 → sval σ i + i ≤ lv σ + 1 := by
    intro i hi hiu
    induction i, hi using Nat.le_induction with
    | base => rw [lv]
    | succ i hi ih => have := ih (by omega); have := hdec1 i hi hiu; omega
  have hC : ∀ i, u ≤ i → i ≤ k → rv σ + k ≤ sval σ i + i := by
    refine down_ind (P := fun i => rv σ + k ≤ sval σ i + i) (by rw [rv]) ?_
    intro s hs hsk ih
    have := hdec2 s hs (by omega); omega
  have hE : ∀ i, 1 ≤ i → i ≤ u - 1 → u ≤ sval σ i + i := by
    refine down_ind (P := fun i => u ≤ sval σ i + i) ?_ ?_
    · have := (sval_mem σ (i := u - 1) (by omega) (by omega)).1; omega
    · intro s hs hsk ih
      have := hdec1 s hs (by omega); omega
  have hF : ∀ i, u ≤ i → i ≤ k → sval σ i + i ≤ k + u := by
    intro i hi hik
    induction i, hi using Nat.le_induction with
    | base => omega
    | succ i hi ih => have := ih (by omega); have := hdec2 i hi hik; omega
  have h1 := hA (u - 1) (by omega) le_rfl
  have h1' := (sval_mem σ (i := u - 1) (by omega) (by omega)).1
  have h2 := hC u le_rfl huk
  have hul : u = lv σ + 1 := by omega
  refine ⟨hul, by omega, ?_⟩
  intro i h1 h2
  split_ifs with h
  · have := hA i h1 (by omega); have := hE i h1 (by omega); omega
  · have := hC i (by omega) h2; have := hF i (by omega) h2; omega

/-- The two decreasing blocks (4.10)–(4.11) in the normalized case. -/
lemma Abs.c26_dec (hA : Abs σ Θ) (hn : (th Θ 1).1 < 1) (hlr : lv σ < rv σ) :
    (∀ i, 1 ≤ i → i + 1 ≤ up σ - 1 → sval σ (i + 1) < sval σ i) ∧
    (∀ i, up σ ≤ i → i + 1 ≤ k → sval σ (i + 1) < sval σ i) := by
  have := hA.k3; have := hA.hb; have := hA.hu; have := hA.hr; have := hA.hl
  obtain ⟨hb, hx⟩ := hA.c26_x hn hlr
  have hsig : ∀ i, 1 ≤ i → i ≤ k → i ≠ 1 → i ≠ up σ → th Θ i = sig σ (i - 1) := by
    intro i h1 h2 h3 h4
    refine (hA.can_of hn hlr h1 h2 h3 h4).eq_sig ?_
    rw [hx i h1 h2 h3 h4, Nat.cast_sub (by omega)]; simp
  -- `Θ(i)_y = σ(i - 1)` for `i ∉ {1, u}`
  have hy : ∀ i, 1 ≤ i → i ≤ k → i ≠ 1 → i ≠ up σ → (th Θ i).2 = (sval σ (i - 1) : ℝ) := by
    intro i h1 h2 h3 h4
    rw [hsig i h1 h2 h3 h4, sig_eq σ (by omega) (by omega)]
  -- shifting a descent
  have step : ∀ i, 2 ≤ i → i + 1 ≤ k → i ≠ up σ → i + 1 ≠ up σ →
      sval σ i < sval σ (i - 1) → sval σ (i + 1) < sval σ i := by
    intro i h1 h2 h3 h4 h
    have := (th_y_lt_iff hA.rep (i := i + 1) (j := i) (by omega) (by omega) (by omega)
      (by omega)).mp (by
        rw [hy i (by omega) (by omega) (by omega) h3, hy (i + 1) (by omega) h2 (by omega) h4]
        simp only [Nat.add_sub_cancel]; exact_mod_cast h)
    exact this
  obtain ⟨he23, h23⟩ := hA.c23 hn hlr
  obtain ⟨hyk, -⟩ := hA.c25 hn hlr
  rw [thInv_eq σ Θ (by omega) le_rfl] at hyk
  change (k : ℝ) < (th Θ (up σ)).2 at hyk
  rw [he23] at h23
  constructor
  · intro i hi hiu
    induction i, hi using Nat.le_induction with
    | base =>
      refine (th_y_lt_iff hA.rep (i := 2) (j := 1) (by omega) (by omega) le_rfl
        (by omega)).mp ?_
      rw [hy 2 (by omega) (by omega) (by omega) (by omega)]
      change ((sval σ 1 : ℕ) : ℝ) < _
      rw [← lv]; linarith
    | succ i hi ih => exact step (i + 1) (by omega) (by omega) (by omega) (by omega) (ih (by omega))
  · intro i hi hik
    induction i, hi using Nat.le_induction with
    | base =>
      refine (th_y_lt_iff hA.rep (i := up σ + 1) (j := up σ) (by omega) (by omega) (by omega)
        (by omega)).mp ?_
      rw [hy (up σ + 1) (by omega) (by omega) (by omega) (by omega), Nat.add_sub_cancel,
        sval_up σ (by omega)]
      exact hyk
    | succ i hi ih => exact step (i + 1) (by omega) (by omega) (by omega) (by omega) (ih (by omega))

/-- The explicit two-block formula in the normalized case. -/
lemma Abs.formula (hA : Abs σ Θ) (hn : (th Θ 1).1 < 1) (hlr : lv σ < rv σ) :
    up σ = lv σ + 1 ∧ rv σ = lv σ + 1 ∧
      ∀ i, 1 ≤ i → i ≤ k → sval σ i = if i ≤ lv σ then lv σ + 1 - i else k + lv σ + 1 - i := by
  have := hA.k3; have := hA.hu
  obtain ⟨d1, d2⟩ := hA.c26_dec hn hlr
  exact twoBlock_formula σ (up σ) (by omega) (by omega) (sval_up σ (by omega)) hlr d1 d2

/-- **The final contradiction**, positive form: in the normalized case `σ` is a two-block
pattern of Subsection 4.1. -/
lemma Abs.twoBlockA (hA : Abs σ Θ) (hn : (th Θ 1).1 < 1) (hlr : lv σ < rv σ) :
    IsTwoBlockA σ (lv σ) := by
  have := hA.hl
  obtain ⟨-, -, hf⟩ := hA.formula hn hlr
  exact ⟨by omega, by omega, hf⟩

/-- **Claim 4.26** on the abstract context (normalized case). -/
lemma Abs.c26 (hA : Abs σ Θ) (hn : (th Θ 1).1 < 1) (hlr : lv σ < rv σ) :
    ((up σ : ℝ) - 2 < (thInv σ Θ k).1 ∧ thInv σ Θ k = th Θ (up σ) ∧
      (thInv σ Θ k).1 < (up σ : ℝ) - 1 ∧ bp σ + 1 = up σ ∧
      ∀ i : ℕ, 1 ≤ i → i ≤ k → i ≠ 1 → i ≠ up σ → th Θ i = sig σ (i - 1)) ∧
    ((lv σ : ℝ) + 1 < (th Θ 1).2 ∧ th Θ 1 = thInv σ Θ (lv σ) ∧
      (th Θ 1).2 < (lv σ : ℝ) + 2 ∧ rv σ = lv σ + 1 ∧
      ∀ j : ℕ, 1 ≤ j → j ≤ k → j ≠ lv σ → j ≠ k → thInv σ Θ j = sigInv σ (j + 1)) := by
  have := hA.k3; have := hA.hb; have := hA.hu; have := hA.hr; have := hA.hl
  obtain ⟨hb, hx⟩ := hA.c26_x hn hlr
  have hsig : ∀ i, 1 ≤ i → i ≤ k → i ≠ 1 → i ≠ up σ → th Θ i = sig σ (i - 1) := by
    intro i h1 h2 h3 h4
    refine (hA.can_of hn hlr h1 h2 h3 h4).eq_sig ?_
    rw [hx i h1 h2 h3 h4, Nat.cast_sub (by omega)]; simp
  obtain ⟨hu', hr', hf⟩ := hA.formula hn hlr
  obtain ⟨he23, h23⟩ := hA.c23 hn hlr
  obtain ⟨-, -, -, hxu, -, -⟩ := hA.c25 hn hlr
  have hku : thInv σ Θ k = th Θ (up σ) := thInv_eq σ Θ (by omega) le_rfl
  refine ⟨⟨?_, hku, hxu, hb, hsig⟩, ⟨he23 ▸ h23, he23.symm, ?_, hr', ?_⟩⟩
  · rw [hku]
    have h1 := th_x_lt hA.rep (i := up σ - 1) (j := up σ) (by omega) (by omega) (by omega)
    rw [hx (up σ - 1) (by omega) (by omega) (by omega) (by omega),
      Nat.cast_sub (by omega)] at h1
    push_cast at h1; linarith
  · have h1 := (th_y_lt_iff hA.rep (i := 1) (j := k) le_rfl (by omega) (by omega) le_rfl).mpr
      (by change lv σ < rv σ; exact hlr)
    have hk1 : sval σ (k - 1) = lv σ + 2 := by
      have := hf (k - 1) (by omega) (by omega)
      split_ifs at this <;> omega
    rw [hsig k (by omega) le_rfl (by omega) (by omega), sig_eq σ (by omega) (by omega),
      hk1] at h1
    push_cast at h1; exact h1
  · intro j h1 h2 hjl hjk
    have hm := spos_mem σ h1 h2
    have hs := sval_spos σ h1 h2
    have hi1 : spos σ j ≠ 1 := by intro h; rw [h] at hs; exact hjl hs.symm
    have hiu : spos σ j ≠ up σ := by
      intro h; rw [h, sval_up σ (by omega)] at hs; exact hjk hs.symm
    have hval : sval σ (spos σ j - 1) = j + 1 := by
      have e1 := hf (spos σ j) hm.1 hm.2
      have e2 := hf (spos σ j - 1) (by omega) (by omega)
      rw [hs] at e1
      split_ifs at e1 e2 <;> omega
    rw [thInv_eq σ Θ h1 h2, hsig _ hm.1 hm.2 hi1 hiu, sig_eq σ (by omega) (by omega),
      sigInv_eq σ (by omega) (by omega), hval, ← hval, spos_sval σ (by omega) (by omega)]

/-! ### Reflection 1: top-bottom flip -/

/-- The pattern reflected top-bottom: `σv(i) = k + 1 - σ(i)`. -/
def flipVσ (σ : Perm (Fin k)) : Perm (Fin k) := σ.trans Fin.revPerm

/-- The copy reflected top-bottom: `(x, y) ↦ (x, k + 1 - y)`. -/
def flipVΘ (Θ : Fin k → ℝ × ℝ) : Fin k → ℝ × ℝ := fun i => ((Θ i).1, (k : ℝ) + 1 - (Θ i).2)

lemma sval_flipV (σ : Perm (Fin k)) {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ k) :
    sval (flipVσ σ) i = k + 1 - sval σ i := by
  obtain ⟨a, rfl⟩ := exists_fin h1 h2
  rw [sval_fin, sval_fin]
  simp only [flipVσ, Equiv.trans_apply, Fin.revPerm_apply, Fin.val_rev]
  have := (σ a).isLt; omega

lemma spos_flipV (σ : Perm (Fin k)) {j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ k) :
    spos (flipVσ σ) j = spos σ (k + 1 - j) := by
  obtain ⟨a, rfl⟩ := exists_fin h1 h2
  have : k + 1 - (a.val + 1) = (Fin.rev a).val + 1 := by rw [Fin.val_rev]; omega
  rw [spos_fin, this, spos_fin]
  simp [flipVσ, Fin.revPerm_symm]

lemma th_flipV (Θ : Fin k → ℝ × ℝ) {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ k) :
    th (flipVΘ Θ) i = ((th Θ i).1, (k : ℝ) + 1 - (th Θ i).2) := by
  obtain ⟨a, rfl⟩ := exists_fin h1 h2
  rw [th_fin, th_fin]; rfl

lemma Abs.flipV (hA : Abs σ Θ) : Abs (flipVσ σ) (flipVΘ Θ) := by
  have := hA.k3; have hl := hA.hl; have hr := hA.hr; have hb := hA.hb; have hu := hA.hu
  have elv : lv (flipVσ σ) = k + 1 - lv σ := sval_flipV σ le_rfl (by omega)
  have erv : rv (flipVσ σ) = k + 1 - rv σ := sval_flipV σ (by omega) le_rfl
  have ebp : bp (flipVσ σ) = up σ := by
    rw [bp, spos_flipV σ le_rfl (by omega)]; rfl
  have eup : up (flipVσ σ) = bp σ := by
    rw [up, spos_flipV σ (by omega) le_rfl]; congr 1; omega
  have rlv : (lv (flipVσ σ) : ℝ) = (k : ℝ) + 1 - lv σ := by
    rw [elv, Nat.cast_sub (by omega)]; push_cast; ring
  have rrv : (rv (flipVσ σ) : ℝ) = (k : ℝ) + 1 - rv σ := by
    rw [erv, Nat.cast_sub (by omega)]; push_cast; ring
  refine ⟨⟨hA.rep.1, fun i j => ?_⟩, by omega, by omega, by omega, by omega, ?_⟩
  · simp only [flipVΘ, flipVσ, Equiv.trans_apply, Fin.revPerm_apply, Fin.rev_lt_rev]
    rw [← hA.rep.2 j i]; constructor <;> intro h <;> linarith
  intro i h1 h2
  rw [th_flipV Θ h1 h2]
  have hsv := sval_flipV σ h1 h2
  have hm := sval_mem σ h1 h2
  rcases hA.pt i h1 h2 with ⟨m, hm1, hmk, he⟩ | ⟨he, hx, h3, h4⟩ | ⟨he, hx, h3, h4⟩ |
      ⟨he, hy, h3, h4⟩ | ⟨he, hy, h3, h4⟩
  · left
    refine ⟨m, hm1, hmk, ?_⟩
    rw [he, sval_flipV σ hm1 hmk, Nat.cast_sub (by have := sval_mem σ hm1 hmk; omega)]
    push_cast; rfl
  · refine Or.inr (Or.inl ⟨he, hx, fun h => ?_, fun h => ?_⟩)
    · have : rv σ < lv σ := by omega
      have := h4 this; simp only; rw [rlv]; linarith
    · have : lv σ < rv σ := by omega
      have := h3 this; simp only; rw [rlv]; linarith
  · refine Or.inr (Or.inr (Or.inl ⟨he, hx, fun h => ?_, fun h => ?_⟩))
    · have : rv σ < lv σ := by omega
      have := h4 this; simp only; rw [rrv]; linarith
    · have : lv σ < rv σ := by omega
      have := h3 this; simp only; rw [rrv]; linarith
  · refine Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, by simp only; linarith, ?_, ?_⟩)))
    · rw [ebp, eup]; exact h4
    · rw [ebp, eup]; exact h3
  · refine Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by simp only; linarith, ?_, ?_⟩)))
    · rw [ebp, eup]; exact h4
    · rw [ebp, eup]; exact h3

lemma twoBlock_of_flipV (σ : Perm (Fin k)) (h : IsTwoBlock (flipVσ σ)) : IsTwoBlock σ := by
  rcases h with ⟨ℓ, h1, h2, hf⟩ | ⟨r, h1, h2, hf⟩
  · refine Or.inr ⟨k - ℓ, by omega, by omega, fun i hi1 hi2 => ?_⟩
    have hv := hf i hi1 hi2; rw [sval_flipV σ hi1 hi2] at hv
    have hm := sval_mem σ hi1 hi2
    split_ifs at hv ⊢ <;> omega
  · refine Or.inl ⟨k - r, by omega, by omega, fun i hi1 hi2 => ?_⟩
    have hv := hf i hi1 hi2; rw [sval_flipV σ hi1 hi2] at hv
    have hm := sval_mem σ hi1 hi2
    split_ifs at hv ⊢ <;> omega

/-! ### Reflection 2: left-right flip -/

/-- The pattern reflected left-right: `σh(i) = σ(k + 1 - i)`. -/
def flipHσ (σ : Perm (Fin k)) : Perm (Fin k) := Fin.revPerm.trans σ

/-- The copy reflected left-right: `(x, y) ↦ (k + 1 - x, y)`, re-listed in `x`-order. -/
def flipHΘ (Θ : Fin k → ℝ × ℝ) : Fin k → ℝ × ℝ :=
  fun i => ((k : ℝ) + 1 - (Θ (Fin.rev i)).1, (Θ (Fin.rev i)).2)

lemma sval_flipH (σ : Perm (Fin k)) {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ k) :
    sval (flipHσ σ) i = sval σ (k + 1 - i) := by
  obtain ⟨a, rfl⟩ := exists_fin h1 h2
  have : k + 1 - (a.val + 1) = (Fin.rev a).val + 1 := by rw [Fin.val_rev]; omega
  rw [this, sval_fin, sval_fin]; rfl

lemma spos_flipH (σ : Perm (Fin k)) {j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ k) :
    spos (flipHσ σ) j = k + 1 - spos σ j := by
  obtain ⟨a, rfl⟩ := exists_fin h1 h2
  rw [spos_fin, spos_fin]
  simp only [flipHσ, Equiv.symm_trans_apply, Fin.revPerm_symm, Fin.revPerm_apply, Fin.val_rev]
  have := (σ.symm a).isLt; omega

lemma th_flipH (Θ : Fin k → ℝ × ℝ) {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ k) :
    th (flipHΘ Θ) i = ((k : ℝ) + 1 - (th Θ (k + 1 - i)).1, (th Θ (k + 1 - i)).2) := by
  obtain ⟨a, rfl⟩ := exists_fin h1 h2
  have : k + 1 - (a.val + 1) = (Fin.rev a).val + 1 := by rw [Fin.val_rev]; omega
  rw [this, th_fin, th_fin]; rfl

lemma Abs.flipH (hA : Abs σ Θ) : Abs (flipHσ σ) (flipHΘ Θ) := by
  have := hA.k3; have hl := hA.hl; have hr := hA.hr; have hb := hA.hb; have hu := hA.hu
  have elv : lv (flipHσ σ) = rv σ := by rw [lv, sval_flipH σ le_rfl (by omega)]; rfl
  have erv : rv (flipHσ σ) = lv σ := by
    rw [rv, sval_flipH σ (by omega) le_rfl, show k + 1 - k = 1 by omega]; rfl
  have ebp : bp (flipHσ σ) = k + 1 - bp σ := spos_flipH σ le_rfl (by omega)
  have eup : up (flipHσ σ) = k + 1 - up σ := spos_flipH σ (by omega) le_rfl
  have rbp : (bp (flipHσ σ) : ℝ) = (k : ℝ) + 1 - bp σ := by
    rw [ebp, Nat.cast_sub (by omega)]; push_cast; ring
  have rup : (up (flipHσ σ) : ℝ) = (k : ℝ) + 1 - up σ := by
    rw [eup, Nat.cast_sub (by omega)]; push_cast; ring
  refine ⟨⟨fun i j hij => ?_, fun i j => hA.rep.2 _ _⟩, by omega, by omega, by omega, by omega,
    ?_⟩
  · simp only [flipHΘ]
    have := hA.rep.1 (Fin.rev_lt_rev.mpr hij); linarith
  intro i h1 h2
  rw [th_flipH Θ h1 h2]
  have hsv := sval_flipH σ h1 h2
  rcases hA.pt (k + 1 - i) (by omega) (by omega) with ⟨m, hm1, hmk, he⟩ | ⟨he, hx, h3, h4⟩ |
      ⟨he, hx, h3, h4⟩ | ⟨he, hy, h3, h4⟩ | ⟨he, hy, h3, h4⟩
  · left
    refine ⟨k + 1 - m, by omega, by omega, ?_⟩
    rw [he, sval_flipH σ (by omega) (by omega), show k + 1 - (k + 1 - m) = m by omega,
      Nat.cast_sub (by omega)]
    push_cast; rfl
  · refine Or.inr (Or.inr (Or.inl ⟨by omega, by simp only; linarith, fun h => ?_, fun h => ?_⟩))
    · simp only [elv, erv] at h ⊢; exact h4 h
    · simp only [elv, erv] at h ⊢; exact h3 h
  · refine Or.inr (Or.inl ⟨by omega, by simp only; linarith, fun h => ?_, fun h => ?_⟩)
    · simp only [elv, erv] at h ⊢; exact h4 h
    · simp only [elv, erv] at h ⊢; exact h3 h
  · refine Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, hy, fun h => ?_, fun h => ?_⟩)))
    · have := h4 (by omega); simp only; rw [rbp]; linarith
    · have := h3 (by omega); simp only; rw [rbp]; linarith
  · refine Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, hy, fun h => ?_, fun h => ?_⟩)))
    · have := h4 (by omega); simp only; rw [rup]; linarith
    · have := h3 (by omega); simp only; rw [rup]; linarith

lemma twoBlock_of_flipH (σ : Perm (Fin k)) (h : IsTwoBlock (flipHσ σ)) : IsTwoBlock σ := by
  rcases h with ⟨ℓ, h1, h2, hf⟩ | ⟨r, h1, h2, hf⟩
  · refine Or.inr ⟨ℓ, h1, h2, fun i hi1 hi2 => ?_⟩
    have hv := hf (k + 1 - i) (by omega) (by omega)
    rw [sval_flipH σ (by omega) (by omega), show k + 1 - (k + 1 - i) = i by omega] at hv
    split_ifs at hv ⊢ <;> omega
  · refine Or.inl ⟨r, h1, h2, fun i hi1 hi2 => ?_⟩
    have hv := hf (k + 1 - i) (by omega) (by omega)
    rw [sval_flipH σ (by omega) (by omega), show k + 1 - (k + 1 - i) = i by omega] at hv
    split_ifs at hv ⊢ <;> omega

/-! ### Reflection 3: exchanging the coordinates (`σ ↦ σ⁻¹`) -/

/-- The copy reflected in the diagonal, re-listed in `x`-order (a copy of `σ⁻¹`). -/
def swapΘ (σ : Perm (Fin k)) (Θ : Fin k → ℝ × ℝ) : Fin k → ℝ × ℝ :=
  fun j => ((Θ (σ.symm j)).2, (Θ (σ.symm j)).1)

lemma sval_symm (σ : Perm (Fin k)) (i : ℕ) : sval σ.symm i = spos σ i := rfl

lemma th_swap (σ : Perm (Fin k)) (Θ : Fin k → ℝ × ℝ) (j : ℕ) :
    th (swapΘ σ Θ) j = (thInv σ Θ j).swap := by
  unfold th thInv; split_ifs <;> rfl

lemma Abs.swap (hA : Abs σ Θ) : Abs σ.symm (swapΘ σ Θ) := by
  have := hA.k3
  refine ⟨⟨fun i j hij => ?_, fun i j => hA.rep.1.lt_iff_lt⟩, hA.hb, hA.hu, hA.hl, hA.hr, ?_⟩
  · simp only [swapΘ]; rw [hA.rep.2]; simpa using hij
  intro j h1 h2
  rw [th_swap]
  rcases hA.ptInv h1 h2 with ⟨m, hm1, hmk, he⟩ | ⟨he, h⟩ | ⟨he, h⟩ | ⟨he, h⟩ | ⟨he, h⟩
  · left
    have := sval_mem σ hm1 hmk
    refine ⟨sval σ m, this.1, this.2, ?_⟩
    rw [he, sval_symm, spos_sval σ hm1 hmk]; rfl
  · refine Or.inr (Or.inr (Or.inr (Or.inl ⟨?_, h⟩)))
    rw [sval_symm, he]; exact spos_sval σ le_rfl (by omega)
  · refine Or.inr (Or.inr (Or.inr (Or.inr ⟨?_, h⟩)))
    rw [sval_symm, he]; exact spos_sval σ (by omega) le_rfl
  · exact Or.inr (Or.inl ⟨he, h⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨he, h⟩))

lemma twoBlock_of_symm (σ : Perm (Fin k)) (h : IsTwoBlock σ.symm) : IsTwoBlock σ := by
  rcases h with ⟨ℓ, h1, h2, hf⟩ | ⟨r, h1, h2, hf⟩
  · refine Or.inl ⟨ℓ, h1, h2, fun i hi1 hi2 => ?_⟩
    have hm := sval_mem σ hi1 hi2
    have hv := hf (sval σ i) hm.1 hm.2
    rw [sval_symm, spos_sval σ hi1 hi2] at hv
    split_ifs at hv ⊢ <;> omega
  · refine Or.inr ⟨k - r, by omega, by omega, fun i hi1 hi2 => ?_⟩
    have hm := sval_mem σ hi1 hi2
    have hv := hf (sval σ i) hm.1 hm.2
    rw [sval_symm, spos_sval σ hi1 hi2] at hv
    split_ifs at hv ⊢ <;> omega

/-! ### Reduction of all cases to the normalized one -/

lemma Abs.twoBlock_of_L (hA : Abs σ Θ) (hn : (th Θ 1).1 < 1) : IsTwoBlock σ := by
  have := hA.k3; have := hA.hl; have := hA.hr
  rcases hA.lr with hlr | hlr
  · exact Or.inl ⟨_, hA.twoBlockA hn hlr⟩
  · refine twoBlock_of_flipV σ (Or.inl ⟨_, hA.flipV.twoBlockA ?_ ?_⟩)
    · rw [th_flipV Θ le_rfl (by omega)]; exact hn
    · rw [lv, rv, sval_flipV σ le_rfl (by omega), sval_flipV σ (by omega) le_rfl]
      change k + 1 - lv σ < k + 1 - rv σ
      omega

lemma Abs.twoBlock_of_R (hA : Abs σ Θ) (hn : (k : ℝ) < (th Θ k).1) : IsTwoBlock σ := by
  have := hA.k3
  refine twoBlock_of_flipH σ (hA.flipH.twoBlock_of_L ?_)
  rw [th_flipH Θ le_rfl (by omega), show k + 1 - 1 = k by omega]
  simp only; linarith

lemma Abs.twoBlock_of_B (hA : Abs σ Θ) (hn : (thInv σ Θ 1).2 < 1) : IsTwoBlock σ := by
  refine twoBlock_of_symm σ (hA.swap.twoBlock_of_L ?_)
  rw [th_swap]; exact hn

lemma Abs.twoBlock_of_U (hA : Abs σ Θ) (hn : (k : ℝ) < (thInv σ Θ k).2) : IsTwoBlock σ := by
  refine twoBlock_of_symm σ (hA.swap.twoBlock_of_R ?_)
  rw [th_swap]; exact hn

/-- Outside Subsection 4.1, every point of `Θ` is canonical. -/
lemma Abs.all_can (hA : Abs σ Θ) (hnot : ¬ IsTwoBlock σ) {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ k) :
    Can σ (th Θ i) := by
  rcases hA.pt i h1 h2 with hc | ⟨he, hx, -⟩ | ⟨he, hx, -⟩ | ⟨he, hy, -⟩ | ⟨he, hy, -⟩
  · exact hc
  · subst he; exact absurd (hA.twoBlock_of_L hx) hnot
  · subst he; exact absurd (hA.twoBlock_of_R hx) hnot
  · rw [th_eq_thInv σ Θ h1 h2, he] at hy; exact absurd (hA.twoBlock_of_B hy) hnot
  · rw [th_eq_thInv σ Θ h1 h2, he] at hy; exact absurd (hA.twoBlock_of_U hy) hnot

/-- Outside Subsection 4.1, `Θ = Σ`. -/
lemma Abs.image_eq (hA : Abs σ Θ) (hnot : ¬ IsTwoBlock σ) :
    Finset.univ.image Θ = canon σ := by
  have hsub : Finset.univ.image Θ ⊆ canon σ := by
    intro p hp
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hp
    obtain ⟨a, rfl⟩ := hp
    rw [mem_canon_iff, ← th_fin Θ a]
    exact hA.all_can hnot (by omega) (by omega)
  have hinj : Function.Injective Θ := fun a b h => hA.rep.1.injective (by simp only [h])
  refine Finset.eq_of_subset_of_card_le hsub ?_
  rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  exact (Finset.card_image_le).trans (by simp)


/-! ### The concrete boundary sets of Construction 4.19 -/

lemma seg_pos {a v p : ℝ × ℝ} {T : ℝ} (hp : p ∈ closedSeg a v T) (ha : a ∈ lattice)
    (hnl : p ∉ lattice) : ∃ t : ℝ, 0 < t ∧ t ≤ T ∧ p = (a.1 + t * v.1, a.2 + t * v.2) := by
  obtain ⟨t, h0, hT, rfl⟩ := hp
  rcases h0.lt_or_eq with h | rfl
  · exact ⟨t, h, hT, rfl⟩
  · exfalso; apply hnl; simpa using ha

lemma one_k_lattice (a b : ℕ) : ((a : ℝ), (b : ℝ)) ∈ lattice := ⟨a, b, by simp⟩

lemma negSlope_of_sub {S : Set (ℝ × ℝ)} {a : ℝ × ℝ} {c T : ℝ}
    (h : S ⊆ closedSeg a (c, -c) T) : NegSlope S := by
  intro p hp q hq _
  obtain ⟨t, -, -, rfl⟩ := h hp
  obtain ⟨s, -, -, rfl⟩ := h hq
  simp only
  constructor <;> intro h' <;> linarith

lemma posSlope_of_sub {S : Set (ℝ × ℝ)} {a : ℝ × ℝ} {c T : ℝ}
    (h : S ⊆ closedSeg a (c, c) T) : PosSlope S := by
  intro p hp q hq _
  obtain ⟨t, -, -, rfl⟩ := h hp
  obtain ⟨s, -, -, rfl⟩ := h hq
  simp only
  constructor <;> intro h' <;> linarith

lemma PL_coord (σ : Perm (Fin k)) {p : ℝ × ℝ} (hp : p ∈ PL419 σ) :
    p.1 < 1 ∧ 1 ≤ p.2 ∧ p.2 ≤ k := by
  obtain ⟨⟨hI, hnl⟩, -⟩ := hp
  unfold IL419 at hI
  split_ifs at hI
  · obtain ⟨t, ht, hT, rfl⟩ := seg_pos hI (by exact_mod_cast one_k_lattice 1 1) hnl
    simp only; refine ⟨by linarith, by linarith, by linarith⟩
  · obtain ⟨t, ht, hT, rfl⟩ := seg_pos hI (by exact_mod_cast one_k_lattice 1 k) hnl
    simp only; refine ⟨by linarith, by linarith, by linarith⟩

lemma PR_coord (σ : Perm (Fin k)) {p : ℝ × ℝ} (hp : p ∈ PR419 σ) :
    (k : ℝ) < p.1 ∧ 1 ≤ p.2 ∧ p.2 ≤ k := by
  obtain ⟨⟨hI, hnl⟩, -⟩ := hp
  unfold IR419 at hI
  split_ifs at hI
  · obtain ⟨t, ht, hT, rfl⟩ := seg_pos hI (by exact_mod_cast one_k_lattice k 1) hnl
    simp only; refine ⟨by linarith, by linarith, by linarith⟩
  · obtain ⟨t, ht, hT, rfl⟩ := seg_pos hI (one_k_lattice k k) hnl
    simp only; refine ⟨by linarith, by linarith, by linarith⟩

lemma PB_coord (σ : Perm (Fin k)) {p : ℝ × ℝ} (hp : p ∈ PB419 σ) :
    p.2 < 1 ∧ 1 ≤ p.1 ∧ p.1 ≤ k := by
  obtain ⟨⟨hI, hnl⟩, -⟩ := hp
  unfold IB419 at hI
  split_ifs at hI
  · obtain ⟨t, ht, hT, rfl⟩ := seg_pos hI (by exact_mod_cast one_k_lattice 1 1) hnl
    simp only; refine ⟨by linarith, by linarith, by linarith⟩
  · obtain ⟨t, ht, hT, rfl⟩ := seg_pos hI (by exact_mod_cast one_k_lattice k 1) hnl
    simp only; refine ⟨by linarith, by linarith, by linarith⟩

lemma PU_coord (σ : Perm (Fin k)) {p : ℝ × ℝ} (hp : p ∈ PU419 σ) :
    (k : ℝ) < p.2 ∧ 1 ≤ p.1 ∧ p.1 ≤ k := by
  obtain ⟨⟨hI, hnl⟩, -⟩ := hp
  unfold IU419 at hI
  split_ifs at hI
  · obtain ⟨t, ht, hT, rfl⟩ := seg_pos hI (by exact_mod_cast one_k_lattice 1 k) hnl
    simp only; refine ⟨by linarith, by linarith, by linarith⟩
  · obtain ⟨t, ht, hT, rfl⟩ := seg_pos hI (one_k_lattice k k) hnl
    simp only; refine ⟨by linarith, by linarith, by linarith⟩

/-- A point of the support `D` of Construction 4.19 lies in one of its five parts `Σ`, `P_L`,
`P_R`, `P_B`, `P_U`. -/
lemma mem_D419 (σ : Perm (Fin k)) {p : ℝ × ℝ} (hp : p ∈ D419 σ) :
    p ∈ canon σ ∨ p ∈ PL419 σ ∨ p ∈ PR419 σ ∨ p ∈ PB419 σ ∨ p ∈ PU419 σ := by
  rcases hp with (((h | h) | h) | h) | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h)))

lemma left_sub (σ : Perm (Fin k)) {D : Set (ℝ × ℝ)} (hD : D ⊆ D419 σ) :
    {p | p ∈ D ∧ p.1 < 1} ⊆ IL419 σ := by
  rintro p ⟨hp, hx⟩
  rcases mem_D419 σ (hD hp) with h | h | h | h | h
  · linarith [((mem_canon_iff σ p).mp h).bounds.1]
  · exact h.1.1
  · have := (PR_coord σ h).1; have : (1 : ℝ) ≤ k := by
      have := (PR_coord σ h).2; linarith
    linarith
  · linarith [(PB_coord σ h).2.1]
  · linarith [(PU_coord σ h).2.1]

lemma right_sub (σ : Perm (Fin k)) {D : Set (ℝ × ℝ)} (hD : D ⊆ D419 σ) :
    {p | p ∈ D ∧ (k : ℝ) < p.1} ⊆ IR419 σ := by
  rintro p ⟨hp, hx⟩
  rcases mem_D419 σ (hD hp) with h | h | h | h | h
  · linarith [((mem_canon_iff σ p).mp h).bounds.2.1]
  · have := (PL_coord σ h); linarith
  · exact h.1.1
  · linarith [(PB_coord σ h).2.2]
  · linarith [(PU_coord σ h).2.2]

lemma bottom_sub (σ : Perm (Fin k)) {D : Set (ℝ × ℝ)} (hD : D ⊆ D419 σ) :
    {p | p ∈ D ∧ p.2 < 1} ⊆ IB419 σ := by
  rintro p ⟨hp, hy⟩
  rcases mem_D419 σ (hD hp) with h | h | h | h | h
  · linarith [((mem_canon_iff σ p).mp h).bounds.2.2.1]
  · linarith [(PL_coord σ h).2.1]
  · linarith [(PR_coord σ h).2.1]
  · exact h.1.1
  · have := (PU_coord σ h); linarith

lemma top_sub (σ : Perm (Fin k)) {D : Set (ℝ × ℝ)} (hD : D ⊆ D419 σ) :
    {p | p ∈ D ∧ (k : ℝ) < p.2} ⊆ IU419 σ := by
  rintro p ⟨hp, hy⟩
  rcases mem_D419 σ (hD hp) with h | h | h | h | h
  · linarith [((mem_canon_iff σ p).mp h).bounds.2.2.2]
  · linarith [(PL_coord σ h).2.2]
  · linarith [(PR_coord σ h).2.2]
  · have := (PB_coord σ h); linarith
  · exact h.1.1

/-- The slope hypotheses of Claim 4.3 hold for Construction 4.19, so (4.4) holds. -/
lemma abs_of (σ : Perm (Fin k)) (hl : lv σ ≠ 1 ∧ lv σ ≠ k) (hr : rv σ ≠ 1 ∧ rv σ ≠ k)
    (D : Set (ℝ × ℝ)) (h₁ : (↑(canon σ) : Set (ℝ × ℝ)) ⊆ D) (h₂ : D ⊆ D419 σ)
    (Θ : Fin k → ℝ × ℝ) (hΘ : CopyIn σ Θ D) : Abs σ Θ := by
  have hk1 : 1 ≤ k := by
    by_contra h
    have : lv σ = 0 := by unfold lv sval; split_ifs <;> omega
    omega
  have hlm := sval_mem σ (i := 1) le_rfl hk1
  have hrm := sval_mem σ (i := k) hk1 le_rfl
  change 1 ≤ lv σ ∧ lv σ ≤ k at hlm
  change 1 ≤ rv σ ∧ rv σ ≤ k at hrm
  have hk : 2 ≤ k := by omega
  have hbm := spos_mem σ (i := 1) le_rfl hk1
  have hum := spos_mem σ (i := k) hk1 le_rfl
  change 1 ≤ bp σ ∧ bp σ ≤ k at hbm
  change 1 ≤ up σ ∧ up σ ≤ k at hum
  have sb : sval σ (bp σ) = 1 := sval_bp σ hk1
  have su : sval σ (up σ) = k := sval_up σ hk1
  have hb : 1 < bp σ ∧ bp σ < k := by
    constructor
    · by_contra h
      have : bp σ = 1 := by omega
      rw [this] at sb; exact hl.1 sb
    · by_contra h
      have : bp σ = k := by omega
      rw [this] at sb; exact hr.1 sb
  have hu : 1 < up σ ∧ up σ < k := by
    constructor
    · by_contra h
      have : up σ = 1 := by omega
      rw [this] at su; exact hl.2 su
    · by_contra h
      have : up σ = k := by omega
      rw [this] at su; exact hr.2 su
  have hDΘ := fun i => h₂ (hΘ.2 i)
  -- (4.4), from Claim 4.3
  have e1 := claim_4_3_1 σ hk D h₁ Θ hΘ ⟨fun h => ?_, fun h => ?_⟩
  rotate_left
  · apply negSlope_of_sub (a := (1, 1)) (c := -1) (T := (k : ℝ) - 1)
    intro p hp; have := left_sub σ h₂ hp; unfold IL419 at this
    split_ifs at this with hc
    · simpa using this
    · exact absurd h hc
  · apply posSlope_of_sub (a := (1, (k : ℝ))) (c := -1) (T := (k : ℝ) - 1)
    intro p hp; have := left_sub σ h₂ hp; unfold IL419 at this
    split_ifs at this with hc
    · exact absurd hc (by change ¬ sval σ 1 < sval σ 2; omega)
    · simpa using this
  have e2 := claim_4_3_2 σ hk D h₁ Θ hΘ ⟨fun h => ?_, fun h => ?_⟩
  rotate_left
  · apply negSlope_of_sub (a := ((k : ℝ), (k : ℝ))) (c := 1) (T := (k : ℝ) - 1)
    intro p hp; have := right_sub σ h₂ hp; unfold IR419 at this
    split_ifs at this with hc
    · exact absurd hc (by change ¬ sval σ k < sval σ (k - 1); omega)
    · simpa using this
  · apply posSlope_of_sub (a := ((k : ℝ), 1)) (c := 1) (T := (k : ℝ) - 1)
    intro p hp; have := right_sub σ h₂ hp; unfold IR419 at this
    split_ifs at this with hc
    · simpa using this
    · exact absurd h hc
  have e3 := claim_4_3_3 σ hk D h₁ Θ hΘ ⟨fun h => ?_, fun h => ?_⟩
  rotate_left
  · apply negSlope_of_sub (a := (1, 1)) (c := 1) (T := (k : ℝ) - 1)
    intro p hp; have := bottom_sub σ h₂ hp; unfold IB419 at this
    split_ifs at this with hc
    · simpa using this
    · exact absurd h hc
  · apply posSlope_of_sub (a := ((k : ℝ), 1)) (c := -1) (T := (k : ℝ) - 1)
    intro p hp; have := bottom_sub σ h₂ hp; unfold IB419 at this
    split_ifs at this with hc
    · exact absurd hc (by change ¬ spos σ 1 < spos σ 2; omega)
    · simpa using this
  have e4 := claim_4_3_4 σ hk D h₁ Θ hΘ ⟨fun h => ?_, fun h => ?_⟩
  rotate_left
  · apply negSlope_of_sub (a := ((k : ℝ), (k : ℝ))) (c := -1) (T := (k : ℝ) - 1)
    intro p hp; have := top_sub σ h₂ hp; unfold IU419 at this
    split_ifs at this with hc
    · exact absurd hc (by change ¬ spos σ k < spos σ (k - 1); omega)
    · simpa using this
  · apply posSlope_of_sub (a := (1, (k : ℝ))) (c := 1) (T := (k : ℝ) - 1)
    intro p hp; have := top_sub σ h₂ hp; unfold IU419 at this
    split_ifs at this with hc
    · simpa using this
    · exact absurd h hc
  refine ⟨hΘ.1, by omega, by omega, hb, hu, ?_⟩
  intro i h1 h2
  obtain ⟨a, rfl⟩ := exists_fin h1 h2
  rw [th_fin]
  rcases mem_D419 σ (hDΘ a) with h | h | h | h | h
  · exact Or.inl ((mem_canon_iff σ _).mp h)
  · -- `Θ ∩ P_L ⊆ {Θ(1)}`
    have hx := (PL_coord σ h).1
    have he := e1 a ⟨hΘ.2 a, hx⟩
    rw [← th_fin Θ a] at he
    have := th_inj hΘ.1 (by omega) (by omega) le_rfl (by omega) he
    refine Or.inr (Or.inl ⟨this, hx, fun hlr => ?_, fun hlr => ?_⟩)
    · have := h.2; split_ifs at this; exact this
    · have := h.2; split_ifs at this with hc
      · omega
      · exact this
  · have hx := (PR_coord σ h).1
    have he := e2 a ⟨hΘ.2 a, hx⟩
    rw [← th_fin Θ a] at he
    have := th_inj hΘ.1 (by omega) (by omega) (by omega) le_rfl he
    refine Or.inr (Or.inr (Or.inl ⟨this, hx, fun hlr => ?_, fun hlr => ?_⟩))
    · have := h.2; split_ifs at this; exact this
    · have := h.2; split_ifs at this with hc
      · omega
      · exact this
  · have hy := (PB_coord σ h).1
    have he := e3 a ⟨hΘ.2 a, hy⟩
    rw [← th_fin Θ a, thInv_eq σ Θ le_rfl hk1] at he
    have := th_inj hΘ.1 (by omega) (by omega) hbm.1 hbm.2 he
    refine Or.inr (Or.inr (Or.inr (Or.inl ⟨by rw [this]; exact sb, hy, fun hbu => ?_,
      fun hbu => ?_⟩)))
    · have := h.2; split_ifs at this; exact this
    · have := h.2; split_ifs at this with hc
      · omega
      · exact this
  · have hy := (PU_coord σ h).1
    have he := e4 a ⟨hΘ.2 a, hy⟩
    rw [← th_fin Θ a, thInv_eq σ Θ hk1 le_rfl] at he
    have := th_inj hΘ.1 (by omega) (by omega) hum.1 hum.2 he
    refine Or.inr (Or.inr (Or.inr (Or.inr ⟨by rw [this]; exact su, hy, fun hbu => ?_,
      fun hbu => ?_⟩)))
    · have := h.2; split_ifs at this; exact this
    · have := h.2; split_ifs at this with hc
      · omega
      · exact this

end FB

/-! ## Lemma 4.20 and its proof's claims -/

/-- **Lemma 4.20.** Under the standing hypotheses of Subsection 4.4, if `Π` is associated with a
permutation and `Σ ⊆ Π ⊆ Σ ∪ P_L ∪ P_R ∪ P_B ∪ P_U` (Construction 4.19), then `Σ` is the
unique `σ`-copy in `Π`. The proof does not use `hP : IsPermPointSet P` (tex l.1060) or
`Standing44.not42` (tex l.1018); the paper states both, and they are kept to match the paper. -/
theorem lemma_4_20 (σ : Perm (Fin k)) (hσ : Standing44 σ)
    (P : Finset (ℝ × ℝ)) (hP : IsPermPointSet P)
    (h₁ : (↑(canon σ) : Set (ℝ × ℝ)) ⊆ ↑P) (h₂ : (↑P : Set (ℝ × ℝ)) ⊆ D419 σ) :
    IsUniqueCopy σ ↑P := by
  refine ⟨h₁, fun Θ hΘ => ?_⟩
  exact (FB.abs_of σ hσ.l_ne hσ.r_ne _ h₁ h₂ Θ hΘ).image_eq hσ.not41

/-- The context of the proof of Lemma 4.20 (tex l.1066): the hypotheses of Lemma 4.20 and a
`σ`-copy `Θ ⊆ Π` with `Θ ≠ Σ`. A proof by contradiction refuting this context is
`lemma_4_20`. -/
structure Ctx420 (σ : Perm (Fin k)) (P : Finset (ℝ × ℝ)) (Θ : Fin k → ℝ × ℝ) : Prop where
  standing : Standing44 σ
  assoc : IsPermPointSet P
  sub₁ : (↑(canon σ) : Set (ℝ × ℝ)) ⊆ ↑P
  sub₂ : (↑P : Set (ℝ × ℝ)) ⊆ D419 σ
  copy : CopyIn σ Θ ↑P
  ne : Finset.univ.image Θ ≠ canon σ

namespace FB

/-- The context of Lemma 4.20 gives the abstract context (via (4.4), i.e. Claim 4.3). -/
lemma abs_ctx {σ : Perm (Fin k)} {P : Finset (ℝ × ℝ)} {Θ : Fin k → ℝ × ℝ}
    (hc : Ctx420 σ P Θ) : Abs σ Θ :=
  abs_of σ hc.standing.l_ne hc.standing.r_ne _ hc.sub₁ hc.sub₂ Θ hc.copy

lemma thInv_mem_D {σ : Perm (Fin k)} {P : Finset (ℝ × ℝ)} {Θ : Fin k → ℝ × ℝ}
    (hsub : (↑P : Set (ℝ × ℝ)) ⊆ D419 σ) (hcopy : CopyIn σ Θ ↑P) {j : ℕ} (h1 : 1 ≤ j)
    (h2 : j ≤ k) : thInv σ Θ j ∈ D419 σ := by
  obtain ⟨a, rfl⟩ := exists_fin h1 h2
  rw [thInv_fin]; exact hsub (hcopy.2 _)

end FB

/-- **Claim 4.21** (propagation), statements 1–4 (1-based `i, j`):
1. if `j < k` and `Θ⁻¹(j)_y > j`, then `Θ⁻¹(j+1)_y > j+1`;
2. if `j > 1` and `Θ⁻¹(j)_y < j`, then `Θ⁻¹(j-1)_y < j-1`;
3. if `i < k` and `Θ(i)_x > i`, then `Θ(i+1)_x > i+1`;
4. if `i > 1` and `Θ(i)_x < i`, then `Θ(i-1)_x < i-1`.

A step of the proof by contradiction of Lemma 4.20 (tex l.1066): its context `Ctx420` cannot be
satisfied, because `lemma_4_20` proves `Σ` is the only copy, so the claim holds only vacuously, as
in the paper. Its proof does not use `ne` (`Θ ≠ Σ`), `assoc` (`Π` associated with a permutation), or
`Standing44.not41`/`not42`. -/
theorem claim_4_21 (σ : Perm (Fin k)) (P : Finset (ℝ × ℝ)) (Θ : Fin k → ℝ × ℝ)
    (hc : Ctx420 σ P Θ) :
    (∀ j : ℕ, 1 ≤ j → j < k → (j : ℝ) < (thInv σ Θ j).2 →
      ((j : ℝ) + 1) < (thInv σ Θ (j + 1)).2) ∧
    (∀ j : ℕ, 1 < j → j ≤ k → (thInv σ Θ j).2 < (j : ℝ) →
      (thInv σ Θ (j - 1)).2 < (j : ℝ) - 1) ∧
    (∀ i : ℕ, 1 ≤ i → i < k → (i : ℝ) < (th Θ i).1 → ((i : ℝ) + 1) < (th Θ (i + 1)).1) ∧
    (∀ i : ℕ, 1 < i → i ≤ k → (th Θ i).1 < (i : ℝ) → (th Θ (i - 1)).1 < (i : ℝ) - 1) := by
  have hA := FB.abs_ctx hc
  exact ⟨hA.c21_1, hA.c21_2, hA.c21_3, hA.c21_4⟩

/-- **Corollary 4.22** (iterated propagation), statements 1–4:
1. if `Θ⁻¹(j)_y > j`, then `Θ⁻¹(s)_y > s` for `j ≤ s ≤ k`;
2. if `Θ⁻¹(j)_y < j`, then `Θ⁻¹(s)_y < s` for `1 ≤ s ≤ j`;
3. if `Θ(i)_x > i`, then `Θ(s)_x > s` for `i ≤ s ≤ k`;
4. if `Θ(i)_x < i`, then `Θ(s)_x < s` for `1 ≤ s ≤ i`.

A step of the proof by contradiction of Lemma 4.20 (tex l.1066): its context `Ctx420` cannot be
satisfied, because `lemma_4_20` proves `Σ` is the only copy, so the claim holds only vacuously, as
in the paper. Its proof does not use `ne` (`Θ ≠ Σ`), `assoc` (`Π` associated with a permutation), or
`Standing44.not41`/`not42`. -/
theorem cor_4_22 (σ : Perm (Fin k)) (P : Finset (ℝ × ℝ)) (Θ : Fin k → ℝ × ℝ)
    (hc : Ctx420 σ P Θ) :
    (∀ j : ℕ, 1 ≤ j → j ≤ k → (j : ℝ) < (thInv σ Θ j).2 →
      ∀ s : ℕ, j ≤ s → s ≤ k → (s : ℝ) < (thInv σ Θ s).2) ∧
    (∀ j : ℕ, 1 ≤ j → j ≤ k → (thInv σ Θ j).2 < (j : ℝ) →
      ∀ s : ℕ, 1 ≤ s → s ≤ j → (thInv σ Θ s).2 < (s : ℝ)) ∧
    (∀ i : ℕ, 1 ≤ i → i ≤ k → (i : ℝ) < (th Θ i).1 →
      ∀ s : ℕ, i ≤ s → s ≤ k → (s : ℝ) < (th Θ s).1) ∧
    (∀ i : ℕ, 1 ≤ i → i ≤ k → (th Θ i).1 < (i : ℝ) →
      ∀ s : ℕ, 1 ≤ s → s ≤ i → (th Θ s).1 < (s : ℝ)) := by
  have hA := FB.abs_ctx hc
  exact ⟨fun j h1 _ h => hA.c22_1 j h1 h, fun j _ h2 h => hA.c22_2 j h2 h,
    fun i h1 _ h => hA.c22_3 i h1 h, fun i _ h2 h => hA.c22_4 i h2 h⟩

/-- The normalization (4.5): `Θ ∩ P_L ≠ ∅` and `ℓ < r`. -/
def Norm45 (σ : Perm (Fin k)) (Θ : Fin k → ℝ × ℝ) : Prop :=
  (∃ i, Θ i ∈ PL419 σ) ∧ lv σ < rv σ

namespace FB

/-- If some point of `Θ` lies on `P_L` (the first half of the normalization (4.5)), the leftmost
point of `Θ` lies left of the canonical square. Only `Represents σ Θ` is needed (not the context
`Ctx420` of Lemma 4.20's proof by contradiction, nor `ℓ < r`).
Used inside the proofs of `claim_4_23`–`claim_4_26`. -/
lemma norm_x {σ : Perm (Fin k)} {Θ : Fin k → ℝ × ℝ}
    (hrep : Represents σ Θ) (hn : ∃ i, Θ i ∈ PL419 σ) : (th Θ 1).1 < 1 := by
  obtain ⟨a, ha⟩ := hn
  have h1 := (PL_coord σ ha).1
  have h2 := th_x_le hrep (i := 1) (j := a.val + 1) le_rfl (by omega) (by omega)
  rw [th_fin] at h2
  linarith

end FB

/-- **Claim 4.23.** Under (4.5): `Θ⁻¹(ℓ) = Θ(1)` and `Θ⁻¹(ℓ)_y > ℓ + 1`.

A step of the proof by contradiction of Lemma 4.20 (tex l.1066): its context `Ctx420` cannot be
satisfied, because `lemma_4_20` proves `Σ` is the only copy, so the claim holds only vacuously, as
in the paper. Its proof does not use `ne` (`Θ ≠ Σ`), `assoc` (`Π` associated with a permutation), or
`Standing44.not41`/`not42`. -/
theorem claim_4_23 (σ : Perm (Fin k)) (P : Finset (ℝ × ℝ)) (Θ : Fin k → ℝ × ℝ)
    (hc : Ctx420 σ P Θ) (hn : Norm45 σ Θ) :
    thInv σ Θ (lv σ) = th Θ 1 ∧ (lv σ : ℝ) + 1 < (thInv σ Θ (lv σ)).2 := by
  exact (FB.abs_ctx hc).c23 (FB.norm_x hc.copy.1 hn.1) hn.2

/-- **Claim 4.24.** Under (4.5): `Θ(k)_y > r` and `Θ(k) ∈ Σ`.

A step of the proof by contradiction of Lemma 4.20 (tex l.1066): its context `Ctx420` cannot be
satisfied, because `lemma_4_20` proves `Σ` is the only copy, so the claim holds only vacuously, as
in the paper. Its proof does not use `ne` (`Θ ≠ Σ`), `assoc` (`Π` associated with a permutation), or
`Standing44.not41`/`not42`. -/
theorem claim_4_24 (σ : Perm (Fin k)) (P : Finset (ℝ × ℝ)) (Θ : Fin k → ℝ × ℝ)
    (hc : Ctx420 σ P Θ) (hn : Norm45 σ Θ) :
    (rv σ : ℝ) < (th Θ k).2 ∧ th Θ k ∈ canon σ := by
  obtain ⟨h1, h2⟩ := (FB.abs_ctx hc).c24 (FB.norm_x hc.copy.1 hn.1) hn.2
  exact ⟨h1, (FB.mem_canon_iff σ _).mpr h2⟩

/-- **Claim 4.25.** Under (4.5): `Θ⁻¹(k) ∈ P_U`, `b < u`, `Θ⁻¹(k)_x < u - 1`, and
`Θ⁻¹(1)_x < b`, `Θ⁻¹(1) ∈ Σ`.

A step of the proof by contradiction of Lemma 4.20 (tex l.1066): its context `Ctx420` cannot be
satisfied, because `lemma_4_20` proves `Σ` is the only copy, so the claim holds only vacuously, as
in the paper. Its proof does not use `ne` (`Θ ≠ Σ`), `assoc` (`Π` associated with a permutation), or
`Standing44.not41`/`not42`. -/
theorem claim_4_25 (σ : Perm (Fin k)) (P : Finset (ℝ × ℝ)) (Θ : Fin k → ℝ × ℝ)
    (hc : Ctx420 σ P Θ) (hn : Norm45 σ Θ) :
    thInv σ Θ k ∈ PU419 σ ∧ bp σ < up σ ∧ (thInv σ Θ k).1 < (up σ : ℝ) - 1 ∧
      (thInv σ Θ 1).1 < (bp σ : ℝ) ∧ thInv σ Θ 1 ∈ canon σ := by
  have hA := FB.abs_ctx hc
  have := hA.k3
  obtain ⟨hy, -, hbu, hx, hxb, hcan⟩ := hA.c25 (FB.norm_x hc.copy.1 hn.1) hn.2
  refine ⟨?_, hbu, hx, hxb, (FB.mem_canon_iff σ _).mpr hcan⟩
  -- the only part of the support above `y = k` is `P_U`
  rcases FB.mem_D419 σ (FB.thInv_mem_D hc.sub₂ hc.copy (j := k) (by omega) le_rfl) with
    h | h | h | h | h
  · linarith [((FB.mem_canon_iff σ _).mp h).bounds.2.2.2]
  · linarith [(FB.PL_coord σ h).2.2]
  · linarith [(FB.PR_coord σ h).2.2]
  · have := (FB.PB_coord σ h).1; have : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
    linarith
  · exact h

/-- **Claim 4.26.** Under (4.5):
1. `u - 2 < Θ⁻¹(k)_x = Θ(u)_x < u - 1`, `b = u - 1`, and `Θ(i) = Σ(i-1)` for every
   `i ∈ [k] ∖ {1, u}` (4.6);
2. `ℓ + 1 < Θ(1)_y = Θ⁻¹(ℓ)_y < ℓ + 2`, `r = ℓ + 1`, and `Θ⁻¹(j) = Σ⁻¹(j+1)` for every
   `j ∈ [k] ∖ {ℓ, k}` (4.7).

A step of the proof by contradiction of Lemma 4.20 (tex l.1066): its context `Ctx420` cannot be
satisfied, because `lemma_4_20` proves `Σ` is the only copy, so the claim holds only vacuously, as
in the paper. Its proof does not use `ne` (`Θ ≠ Σ`), `assoc` (`Π` associated with a permutation), or
`Standing44.not41`/`not42`. -/
theorem claim_4_26 (σ : Perm (Fin k)) (P : Finset (ℝ × ℝ)) (Θ : Fin k → ℝ × ℝ)
    (hc : Ctx420 σ P Θ) (hn : Norm45 σ Θ) :
    ((up σ : ℝ) - 2 < (thInv σ Θ k).1 ∧ thInv σ Θ k = th Θ (up σ) ∧
      (thInv σ Θ k).1 < (up σ : ℝ) - 1 ∧ bp σ + 1 = up σ ∧
      ∀ i : ℕ, 1 ≤ i → i ≤ k → i ≠ 1 → i ≠ up σ → th Θ i = sig σ (i - 1)) ∧
    ((lv σ : ℝ) + 1 < (th Θ 1).2 ∧ th Θ 1 = thInv σ Θ (lv σ) ∧
      (th Θ 1).2 < (lv σ : ℝ) + 2 ∧ rv σ = lv σ + 1 ∧
      ∀ j : ℕ, 1 ≤ j → j ≤ k → j ≠ lv σ → j ≠ k → thInv σ Θ j = sigInv σ (j + 1)) := by
  exact (FB.abs_ctx hc).c26 (FB.norm_x hc.copy.1 hn.1) hn.2

namespace FB27

/-- A diagonal closed segment `a + [0, k-1] v` running from the bottom (`a_y = 1`, `v_y = 1`) or
from the top (`a_y = k`, `v_y = -1`) contains a non-axis-parallel open subsegment inside every
horizontal stripe `H_i`, `1 ≤ i ≤ k-1`. -/
lemma seg_h (a v : ℝ × ℝ) (hv1 : v.1 ≠ 0)
    (hv : (v.2 = 1 ∧ a.2 = 1) ∨ (v.2 = -1 ∧ a.2 = (k : ℝ))) {i : ℕ} (hi1 : 1 ≤ i)
    (hi2 : i ≤ k - 1) :
    ∃ a' v' : ℝ × ℝ, v'.1 ≠ 0 ∧ v'.2 ≠ 0 ∧ openSeg a' v' ⊆ closedSeg a v ((k : ℝ) - 1) ∧
      openSeg a' v' ⊆ hStripe i := by
  have hi1' : (1 : ℝ) ≤ i := by exact_mod_cast hi1
  have hi2' : (i : ℝ) + 1 ≤ k := by
    have : i + 1 ≤ k := by omega
    exact_mod_cast this
  rcases hv with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine ⟨(a.1 + ((i : ℝ) - 1) * v.1, a.2 + ((i : ℝ) - 1) * v.2), (1 * v.1, 1 * v.2),
      by simpa using hv1, by simp [h1],
      DISC.openSeg_subset_closedSeg a v _ 1 _ (by linarith) (by norm_num) (by linarith),
      DISC.openSeg_subset_hStripe _ _ i (by simp [h1]) ?_ ?_ ?_ ?_⟩ <;>
      simp only [h1, h2] <;> linarith
  · refine ⟨(a.1 + ((k : ℝ) - 1 - i) * v.1, a.2 + ((k : ℝ) - 1 - i) * v.2), (1 * v.1, 1 * v.2),
      by simpa using hv1, by simp [h1],
      DISC.openSeg_subset_closedSeg a v _ 1 _ (by linarith) (by norm_num) (by linarith),
      DISC.openSeg_subset_hStripe _ _ i (by simp [h1]) ?_ ?_ ?_ ?_⟩ <;>
      simp only [h1, h2] <;> linarith

/-- The vertical analogue of `seg_h`. -/
lemma seg_v (a v : ℝ × ℝ) (hv2 : v.2 ≠ 0)
    (hv : (v.1 = 1 ∧ a.1 = 1) ∨ (v.1 = -1 ∧ a.1 = (k : ℝ))) {i : ℕ} (hi1 : 1 ≤ i)
    (hi2 : i ≤ k - 1) :
    ∃ a' v' : ℝ × ℝ, v'.1 ≠ 0 ∧ v'.2 ≠ 0 ∧ openSeg a' v' ⊆ closedSeg a v ((k : ℝ) - 1) ∧
      openSeg a' v' ⊆ vStripe i := by
  have hi1' : (1 : ℝ) ≤ i := by exact_mod_cast hi1
  have hi2' : (i : ℝ) + 1 ≤ k := by
    have : i + 1 ≤ k := by omega
    exact_mod_cast this
  rcases hv with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine ⟨(a.1 + ((i : ℝ) - 1) * v.1, a.2 + ((i : ℝ) - 1) * v.2), (1 * v.1, 1 * v.2),
      by simp [h1], by simpa using hv2,
      DISC.openSeg_subset_closedSeg a v _ 1 _ (by linarith) (by norm_num) (by linarith),
      DISC.openSeg_subset_vStripe _ _ i (by simp [h1]) ?_ ?_ ?_ ?_⟩ <;>
      simp only [h1, h2] <;> linarith
  · refine ⟨(a.1 + ((k : ℝ) - 1 - i) * v.1, a.2 + ((k : ℝ) - 1 - i) * v.2), (1 * v.1, 1 * v.2),
      by simp [h1], by simpa using hv2,
      DISC.openSeg_subset_closedSeg a v _ 1 _ (by linarith) (by norm_num) (by linarith),
      DISC.openSeg_subset_vStripe _ _ i (by simp [h1]) ?_ ?_ ?_ ?_⟩ <;>
      simp only [h1, h2] <;> linarith

/-- Both branches of `I_L` are diagonal segments of the shape required by `seg_h`. -/
lemma IL_form (σ : Perm (Fin k)) : ∃ a v : ℝ × ℝ, IL419 σ = closedSeg a v ((k : ℝ) - 1) ∧
    v.1 ≠ 0 ∧ ((v.2 = 1 ∧ a.2 = 1) ∨ (v.2 = -1 ∧ a.2 = (k : ℝ))) := by
  unfold IL419; split_ifs
  · exact ⟨_, _, rfl, by norm_num, Or.inl ⟨rfl, rfl⟩⟩
  · exact ⟨_, _, rfl, by norm_num, Or.inr ⟨rfl, rfl⟩⟩

lemma IR_form (σ : Perm (Fin k)) : ∃ a v : ℝ × ℝ, IR419 σ = closedSeg a v ((k : ℝ) - 1) ∧
    v.1 ≠ 0 ∧ ((v.2 = 1 ∧ a.2 = 1) ∨ (v.2 = -1 ∧ a.2 = (k : ℝ))) := by
  unfold IR419; split_ifs
  · exact ⟨_, _, rfl, by norm_num, Or.inl ⟨rfl, rfl⟩⟩
  · exact ⟨_, _, rfl, by norm_num, Or.inr ⟨rfl, rfl⟩⟩

lemma IB_form (σ : Perm (Fin k)) : ∃ a v : ℝ × ℝ, IB419 σ = closedSeg a v ((k : ℝ) - 1) ∧
    v.2 ≠ 0 ∧ ((v.1 = 1 ∧ a.1 = 1) ∨ (v.1 = -1 ∧ a.1 = (k : ℝ))) := by
  unfold IB419; split_ifs
  · exact ⟨_, _, rfl, by norm_num, Or.inl ⟨rfl, rfl⟩⟩
  · exact ⟨_, _, rfl, by norm_num, Or.inr ⟨rfl, rfl⟩⟩

lemma IU_form (σ : Perm (Fin k)) : ∃ a v : ℝ × ℝ, IU419 σ = closedSeg a v ((k : ℝ) - 1) ∧
    v.2 ≠ 0 ∧ ((v.1 = 1 ∧ a.1 = 1) ∨ (v.1 = -1 ∧ a.1 = (k : ℝ))) := by
  unfold IU419; split_ifs
  · exact ⟨_, _, rfl, by norm_num, Or.inl ⟨rfl, rfl⟩⟩
  · exact ⟨_, _, rfl, by norm_num, Or.inr ⟨rfl, rfl⟩⟩

/-- A diagonal segment `I` of the shape of `seg_h` yields, in `H_i`, an open subsegment inside
`{p ∈ I ∖ ℤ² : c p_y}` whenever `c` holds on `(i, i+1)`. -/
lemma cover_h {I : Set (ℝ × ℝ)} (hI : ∃ a v : ℝ × ℝ, I = closedSeg a v ((k : ℝ) - 1) ∧
    v.1 ≠ 0 ∧ ((v.2 = 1 ∧ a.2 = 1) ∨ (v.2 = -1 ∧ a.2 = (k : ℝ)))) (c : ℝ → Prop) {i : ℕ}
    (hi1 : 1 ≤ i) (hi2 : i ≤ k - 1) (hc : ∀ y, (i : ℝ) < y → y < (i : ℝ) + 1 → c y) :
    ∃ a' v' : ℝ × ℝ, v'.1 ≠ 0 ∧ v'.2 ≠ 0 ∧ openSeg a' v' ⊆ {p | p ∈ I \ lattice ∧ c p.2} ∧
      openSeg a' v' ⊆ hStripe i := by
  obtain ⟨a, v, rfl, hv1, hv⟩ := hI
  obtain ⟨a', v', h1, h2, h3, h4⟩ := seg_h (k := k) a v hv1 hv hi1 hi2
  refine ⟨a', v', h1, h2, fun p hp => ⟨⟨h3 hp, DISC.notMem_lattice_of_hStripe (h4 hp)⟩,
    hc _ (h4 hp).1 (h4 hp).2⟩, h4⟩

/-- The vertical analogue of `cover_h`. -/
lemma cover_v {I : Set (ℝ × ℝ)} (hI : ∃ a v : ℝ × ℝ, I = closedSeg a v ((k : ℝ) - 1) ∧
    v.2 ≠ 0 ∧ ((v.1 = 1 ∧ a.1 = 1) ∨ (v.1 = -1 ∧ a.1 = (k : ℝ)))) (c : ℝ → Prop) {i : ℕ}
    (hi1 : 1 ≤ i) (hi2 : i ≤ k - 1) (hc : ∀ x, (i : ℝ) < x → x < (i : ℝ) + 1 → c x) :
    ∃ a' v' : ℝ × ℝ, v'.1 ≠ 0 ∧ v'.2 ≠ 0 ∧ openSeg a' v' ⊆ {p | p ∈ I \ lattice ∧ c p.1} ∧
      openSeg a' v' ⊆ vStripe i := by
  obtain ⟨a, v, rfl, hv2, hv⟩ := hI
  obtain ⟨a', v', h1, h2, h3, h4⟩ := seg_v (k := k) a v hv2 hv hi1 hi2
  refine ⟨a', v', h1, h2, fun p hp => ⟨⟨h3 hp, DISC.notMem_lattice_of_vStripe (h4 hp)⟩,
    hc _ (h4 hp).1 (h4 hp).2⟩, h4⟩

lemma PL_sub (σ : Perm (Fin k)) : PL419 σ ⊆ D419 σ := fun _ h => by
  unfold D419; simp only [Set.mem_union]; tauto
lemma PR_sub (σ : Perm (Fin k)) : PR419 σ ⊆ D419 σ := fun _ h => by
  unfold D419; simp only [Set.mem_union]; tauto
lemma PB_sub (σ : Perm (Fin k)) : PB419 σ ⊆ D419 σ := fun _ h => by
  unfold D419; simp only [Set.mem_union]; tauto
lemma PU_sub (σ : Perm (Fin k)) : PU419 σ ⊆ D419 σ := fun _ h => by
  unfold D419; simp only [Set.mem_union]; tauto

/-- **Coverage of the horizontal stripes** (tex l.1212): if `|ℓ - r| ≥ 2`, every `H_i`,
`1 ≤ i ≤ k-1`, contains a non-axis-parallel open segment lying in the support `D` (the proof
takes it inside `P_L` or `P_R`). -/
lemma cover_H (σ : Perm (Fin k)) (hlr : 2 ≤ |(lv σ : ℤ) - rv σ|) {i : ℕ} (hi1 : 1 ≤ i)
    (hi2 : i ≤ k - 1) :
    ∃ a v : ℝ × ℝ, v.1 ≠ 0 ∧ v.2 ≠ 0 ∧ openSeg a v ⊆ D419 σ ∧ openSeg a v ⊆ hStripe i := by
  have hi : (i : ℝ) + 1 = ((i + 1 : ℕ) : ℝ) := by push_cast; ring
  rcases lt_or_ge (lv σ) (rv σ) with h | h
  · have h2 : lv σ + 2 ≤ rv σ := by
      rcases abs_cases ((lv σ : ℤ) - rv σ) with ⟨h3, _⟩ | ⟨h3, _⟩ <;> omega
    by_cases hil : lv σ + 1 ≤ i
    · -- `P_L` meets `H_i` for `i ≥ ℓ + 1`.
      have hil' : (lv σ : ℝ) + 1 ≤ i := by exact_mod_cast hil
      obtain ⟨a, v, h1, h2, h3, h4⟩ := cover_h (IL_form σ) (fun y => (lv σ : ℝ) + 1 < y) hi1 hi2
        (fun y hy _ => by linarith)
      refine ⟨a, v, h1, h2, fun p hp => PL_sub σ ?_, h4⟩
      obtain ⟨hp1, hp2⟩ := h3 hp
      exact ⟨hp1, by simpa [h] using hp2⟩
    · -- `P_R` meets `H_i` for `i ≤ r - 2`.
      have hir : i + 1 ≤ rv σ - 1 := by omega
      have hir' : (i : ℝ) + 1 ≤ (rv σ : ℝ) - 1 := by
        have : i + 2 ≤ rv σ := by omega
        have : ((i + 2 : ℕ) : ℝ) ≤ rv σ := by exact_mod_cast this
        push_cast at this; linarith
      obtain ⟨a, v, h1, h2, h3, h4⟩ := cover_h (IR_form σ) (fun y => y < (rv σ : ℝ) - 1) hi1 hi2
        (fun y _ hy => by linarith)
      refine ⟨a, v, h1, h2, fun p hp => PR_sub σ ?_, h4⟩
      obtain ⟨hp1, hp2⟩ := h3 hp
      exact ⟨hp1, by simpa [h] using hp2⟩
  · have h2 : rv σ + 2 ≤ lv σ := by
      rcases abs_cases ((lv σ : ℤ) - rv σ) with ⟨h3, _⟩ | ⟨h3, _⟩ <;> omega
    have hn : ¬ lv σ < rv σ := by omega
    by_cases hir : rv σ + 1 ≤ i
    · -- `P_R` meets `H_i` for `i ≥ r + 1`.
      have hir' : (rv σ : ℝ) + 1 ≤ i := by exact_mod_cast hir
      obtain ⟨a, v, h1, h2, h3, h4⟩ := cover_h (IR_form σ) (fun y => (rv σ : ℝ) + 1 < y) hi1 hi2
        (fun y hy _ => by linarith)
      refine ⟨a, v, h1, h2, fun p hp => PR_sub σ ?_, h4⟩
      obtain ⟨hp1, hp2⟩ := h3 hp
      exact ⟨hp1, by simpa [hn] using hp2⟩
    · -- `P_L` meets `H_i` for `i ≤ ℓ - 2`.
      have hil' : (i : ℝ) + 1 ≤ (lv σ : ℝ) - 1 := by
        have : i + 2 ≤ lv σ := by omega
        have : ((i + 2 : ℕ) : ℝ) ≤ lv σ := by exact_mod_cast this
        push_cast at this; linarith
      obtain ⟨a, v, h1, h2, h3, h4⟩ := cover_h (IL_form σ) (fun y => y < (lv σ : ℝ) - 1) hi1 hi2
        (fun y _ hy => by linarith)
      refine ⟨a, v, h1, h2, fun p hp => PL_sub σ ?_, h4⟩
      obtain ⟨hp1, hp2⟩ := h3 hp
      exact ⟨hp1, by simpa [hn] using hp2⟩

/-- **Coverage of the vertical stripes** (tex l.1212): if `|b - u| ≥ 2`, every `V_i`,
`1 ≤ i ≤ k-1`, contains a non-axis-parallel open segment lying in the support `D` (the proof
takes it inside `P_B` or `P_U`). -/
lemma cover_V (σ : Perm (Fin k)) (hbu : 2 ≤ |(bp σ : ℤ) - up σ|) {i : ℕ} (hi1 : 1 ≤ i)
    (hi2 : i ≤ k - 1) :
    ∃ a v : ℝ × ℝ, v.1 ≠ 0 ∧ v.2 ≠ 0 ∧ openSeg a v ⊆ D419 σ ∧ openSeg a v ⊆ vStripe i := by
  rcases lt_or_ge (bp σ) (up σ) with h | h
  · have h2 : bp σ + 2 ≤ up σ := by
      rcases abs_cases ((bp σ : ℤ) - up σ) with ⟨h3, _⟩ | ⟨h3, _⟩ <;> omega
    by_cases hib : bp σ + 1 ≤ i
    · have hib' : (bp σ : ℝ) + 1 ≤ i := by exact_mod_cast hib
      obtain ⟨a, v, h1, h2, h3, h4⟩ := cover_v (IB_form σ) (fun x => (bp σ : ℝ) + 1 < x) hi1 hi2
        (fun x hx _ => by linarith)
      refine ⟨a, v, h1, h2, fun p hp => PB_sub σ ?_, h4⟩
      obtain ⟨hp1, hp2⟩ := h3 hp
      exact ⟨hp1, by simpa [h] using hp2⟩
    · have hiu' : (i : ℝ) + 1 ≤ (up σ : ℝ) - 1 := by
        have : i + 2 ≤ up σ := by omega
        have : ((i + 2 : ℕ) : ℝ) ≤ up σ := by exact_mod_cast this
        push_cast at this; linarith
      obtain ⟨a, v, h1, h2, h3, h4⟩ := cover_v (IU_form σ) (fun x => x < (up σ : ℝ) - 1) hi1 hi2
        (fun x _ hx => by linarith)
      refine ⟨a, v, h1, h2, fun p hp => PU_sub σ ?_, h4⟩
      obtain ⟨hp1, hp2⟩ := h3 hp
      exact ⟨hp1, by simpa [h] using hp2⟩
  · have h2 : up σ + 2 ≤ bp σ := by
      rcases abs_cases ((bp σ : ℤ) - up σ) with ⟨h3, _⟩ | ⟨h3, _⟩ <;> omega
    have hn : ¬ bp σ < up σ := by omega
    by_cases hiu : up σ + 1 ≤ i
    · have hiu' : (up σ : ℝ) + 1 ≤ i := by exact_mod_cast hiu
      obtain ⟨a, v, h1, h2, h3, h4⟩ := cover_v (IU_form σ) (fun x => (up σ : ℝ) + 1 < x) hi1 hi2
        (fun x hx _ => by linarith)
      refine ⟨a, v, h1, h2, fun p hp => PU_sub σ ?_, h4⟩
      obtain ⟨hp1, hp2⟩ := h3 hp
      exact ⟨hp1, by simpa [hn] using hp2⟩
    · have hib' : (i : ℝ) + 1 ≤ (bp σ : ℝ) - 1 := by
        have : i + 2 ≤ bp σ := by omega
        have : ((i + 2 : ℕ) : ℝ) ≤ bp σ := by exact_mod_cast this
        push_cast at this; linarith
      obtain ⟨a, v, h1, h2, h3, h4⟩ := cover_v (IB_form σ) (fun x => x < (bp σ : ℝ) - 1) hi1 hi2
        (fun x _ hx => by linarith)
      refine ⟨a, v, h1, h2, fun p hp => PB_sub σ ?_, h4⟩
      obtain ⟨hp1, hp2⟩ := h3 hp
      exact ⟨hp1, by simpa [hn] using hp2⟩

/-- Under the standing hypotheses, `k ≥ 2` (indeed `ℓ ∉ {1, k}`). -/
lemma two_le_k {σ : Perm (Fin k)} (hσ : Standing44 σ) : 2 ≤ k := by
  rcases Nat.lt_or_ge k 1 with hk | hk
  · have : k = 0 := by omega
    subst this
    exact absurd (by simp [lv, sval]) hσ.l_ne.2
  · have := FB.sval_mem σ le_rfl hk
    have h := hσ.l_ne
    unfold lv at h
    omega

end FB27

/-- **Corollary 4.27.** Under the standing hypotheses of Subsection 4.4, Theorem 4.1 holds
whenever `|ℓ - r| ≥ 2` and `|b - u| ≥ 2`: for each length `k` there is a threshold `N₀(k)`,
depending only on `k` as in Theorem 4.1, that works for every such pattern `σ` of length `k`. The
proof does not use `Standing44.not42`; the paper states it (tex l.1018), and it is kept to match the
paper. -/
theorem cor_4_27 (k : ℕ) :
    ∃ N₀ : ℕ, ∀ σ : Perm (Fin k), Standing44 σ →
      2 ≤ |(lv σ : ℤ) - rv σ| → 2 ≤ |(bp σ : ℤ) - up σ| → GeomConclusion σ N₀ := by
  refine ⟨DISC.N0 k, fun σ hσ hlr hbu => ?_⟩
  refine DISC.geomConclusion_of_segs' σ (FB27.two_le_k hσ) (D419 σ)
    (fun p hp => by unfold D419; simp only [Set.mem_union]; tauto)
    (fun i hi1 hi2 => FB27.cover_H σ hlr hi1 hi2) (fun i hi1 hi2 => FB27.cover_V σ hbu hi1 hi2)
    (fun P hP h1 h2 => lemma_4_20 σ hσ P hP h1 h2)

end LinfPermRemoval
